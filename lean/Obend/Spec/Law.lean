module
/-
# Obend.Spec.Law — the enforced `law` fragment: syntax, parser, meaning

A package declares, at top level, `law NAME: EXPR`. The law is an admission law over the declared
state of every object created from the package: a kernel judges every write of that state by it.
This module is the fragment's abstract syntax, its parser and its MEANING (`LawExpr.denote`, read
off the declared-state data), ported from minidregg `Compiler/ObjectiveBendLaw.lean` and the
`denote` half of `Kernel/ObjectLaw.lean` (commit 092027a2). The compile to Mini's `Pred`
(`compile`, `packageLaw`, `LawRef.slot`, `compile_sound`) is NOT here: there is no `Pred` library in
this tree; it is `Obend.Law`'s, a later lane.

The fragment, exactly (G1B-ENFORCED-LAW-DESIGN; anything else refuses
`law outside the enforced fragment: …`, never a fallback to `claim`):

    EXPR  ::= EXPR implies EXPR | EXPR or EXPR | EXPR and EXPR | not EXPR | ( EXPR ) | ATOM
    ATOM  ::= REF == INT | REF <= INT | REF in [INT, …]
            | REF == REF | REF <= REF | REF <= REF + INT
            | monotone(FIELD) | writeOnce(FIELD)
    REF   ::= new.FIELD | request.subject | request.caller | request.turn | ledger.height
    INT   ::= -?[0-9]+

`implies` binds loosest and associates to the right; `or` then `and` associate to the left;
`not` applies to the atom (or parenthesised expression) after it. Edition 1 reads TOP-LEVEL
fields only: `new.a.b` refuses by name. `old.` is readable only through `monotone` and
`writeOnce` (all the kernel's predicate can say about the old state).
-/
public import Lean
public import Obend.Core.Data
public section
namespace Obend.Spec.Law
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Syntax -/

/-- A reference a law reads. `field name` is `new.name`, a top-level field of the declared
state; the others are the request facts of the write. -/
inductive LawRef where
  | field (name : String)
  | subject
  | caller
  | height
  | turn
  deriving DecidableEq, Repr, Inhabited

/-- The enforced fragment. `old.` appears only through `monotone` and `writeOnce`. -/
inductive LawExpr where
  | eqC (ref : LawRef) (value : Int)
  | leC (ref : LawRef) (value : Int)
  | inC (ref : LawRef) (values : List Int)
  | eqR (left right : LawRef)
  | leR (left right : LawRef)
  | leROff (left right : LawRef) (offset : Int)
  | monotone (field : String)
  | writeOnce (field : String)
  | not (body : LawExpr)
  | and (left right : LawExpr)
  | or (left right : LawExpr)
  | implies (premise conclusion : LawExpr)
  deriving DecidableEq, Repr, Inhabited

/-- The fields a law reads, in source order (with repetition). -/
@[expose] def LawRef.fields : LawRef → List String
  | .field name => [name]
  | _ => []

@[expose] def LawExpr.fields : LawExpr → List String
  | .eqC ref _ | .leC ref _ | .inC ref _ => ref.fields
  | .eqR left right | .leR left right | .leROff left right _ => left.fields ++ right.fields
  | .monotone field | .writeOnce field => [field]
  | .not body => body.fields
  | .and left right | .or left right | .implies left right => left.fields ++ right.fields

/-- A field or variant name that cannot alias another path. Stated over `toList`, so the kernel
evaluates it (`String.all` does not reduce in the kernel) and proofs read its characters. -/
def plainName (name : String) : Bool :=
  !name.toList.isEmpty && name.toList.all (fun c => c != '.' && c != '@' && c != '/')

/-- Every field a law reads is a plain name. -/
def LawRef.plain : LawRef → Bool
  | .field name => plainName name
  | _ => true

/-- Every field a law names is a law field name. -/
def LawExpr.fieldsPlain : LawExpr → Bool
  | .eqC ref _ | .leC ref _ | .inC ref _ => ref.plain
  | .eqR left right | .leR left right | .leROff left right _ => left.plain && right.plain
  | .monotone field | .writeOnce field => plainName field
  | .not body => body.fieldsPlain
  | .and left right | .or left right | .implies left right => left.fieldsPlain && right.fieldsPlain

/-! ## Meaning, over the declared-state data (minidregg `Kernel/ObjectLaw.lean`) -/

/-- The kernel facts a law may read: the subject whose authority the write carries (`none` in
a frame no grant covers, so every atom reading it fails closed), the calling object and the kernel
turn; and the LEDGER's height (consensus time: `ledger.height`, supplied by the ledger the act
commits to, never by the request; `Obend.Law.Consensus`). The kernel's `Facts` carries more (the
target, the patience); a law reads these four. -/
structure Facts where
  subject : Option Nat
  caller : Option Nat
  height : Nat
  turn : Nat
  deriving Repr, DecidableEq

/-- The scalar a value projects to, if it is a scalar: a natural is itself, a boolean 0 or 1. -/
@[expose] def scalarOf : Data → Option Int
  | .natural value => some (Int.ofNat value)
  | .boolean value => some (if value then 1 else 0)
  | _ => none

/-- The first scalar field called `name` of a record's fields. -/
@[expose] def firstScalarField (name : String) : List (String × Data) → Option Int
  | [] => none
  | (field, value) :: rest =>
      if field = name then
        match scalarOf value with
        | some scalar => some scalar
        | none => firstScalarField name rest
      else firstScalarField name rest

/-- The field `name` of a declared state: only a record has fields. -/
@[expose] def fieldOf (name : String) : Data → Option Int
  | .record fields => firstScalarField name fields
  | _ => none

/-- What a reference reads on the new state of a write under `facts`. -/
@[expose] def LawRef.read (facts : Facts) (new : Data) : LawRef → Option Int
  | .field name => fieldOf name new
  | .subject => facts.subject.map Int.ofNat
  | .caller => facts.caller.map Int.ofNat
  | .height => some (Int.ofNat facts.height)
  | .turn => some (Int.ofNat facts.turn)

/-- **The meaning of a law**: does the write from `old` (absent at a first write) to `new`,
under `facts`, satisfy it? A comparison with an absent reading is false; `monotone` needs both
readings; `writeOnce` holds when the old reading is absent or 0, else the new one must equal it. -/
@[expose] def LawExpr.denote (facts : Facts) (old : Option Data) (new : Data) : LawExpr → Bool
  | .eqC ref value => decide (ref.read facts new = some value)
  | .leC ref value =>
      match ref.read facts new with
      | some x => decide (x ≤ value)
      | none => false
  | .inC ref values =>
      match ref.read facts new with
      | some x => values.contains x
      | none => false
  | .eqR left right =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x = y)
      | _, _ => false
  | .leR left right =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x ≤ y)
      | _, _ => false
  | .leROff left right offset =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x ≤ y + offset)
      | _, _ => false
  | .monotone field =>
      match old.bind (fieldOf field), fieldOf field new with
      | some before, some after => decide (before ≤ after)
      | _, _ => false
  | .writeOnce field =>
      match old.bind (fieldOf field) with
      | none => true
      | some before => before == 0 || decide (fieldOf field new = some before)
  | .not body => !body.denote facts old new
  | .and left right => left.denote facts old new && right.denote facts old new
  | .or left right => left.denote facts old new || right.denote facts old new
  | .implies premise conclusion => !premise.denote facts old new || conclusion.denote facts old new

/-! ## Rendering (diagnostics and documents) -/

def LawRef.render : LawRef → String
  | .field name => "new." ++ name
  | .subject => "request.subject"
  | .caller => "request.caller"
  | .height => "ledger.height"
  | .turn => "request.turn"

def LawExpr.render : LawExpr → String
  | .eqC ref value => s!"{ref.render} == {value}"
  | .leC ref value => s!"{ref.render} <= {value}"
  | .inC ref values => s!"{ref.render} in [{", ".intercalate (values.map toString)}]"
  | .eqR left right => s!"{left.render} == {right.render}"
  | .leR left right => s!"{left.render} <= {right.render}"
  | .leROff left right offset => s!"{left.render} <= {right.render} + {offset}"
  | .monotone field => s!"monotone({field})"
  | .writeOnce field => s!"writeOnce({field})"
  | .not body => s!"not ({body.render})"
  | .and left right => s!"({left.render}) and ({right.render})"
  | .or left right => s!"({left.render}) or ({right.render})"
  | .implies premise conclusion => s!"({premise.render}) implies ({conclusion.render})"

/-! ## Tokens -/

inductive Tok where
  | ident (name : String)
  | int (value : Nat)
  | sym (text : String)
  deriving DecidableEq, Repr, Inhabited

def Tok.render : Tok → String
  | .ident name => "`" ++ name ++ "`"
  | .int value => "`" ++ toString value ++ "`"
  | .sym text => "`" ++ text ++ "`"

def refusalPrefix : String := "law outside the enforced fragment: "

def refuse {α : Type} (what : String) : Except String α := .error (refusalPrefix ++ what)

def identStart (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
def identChar (c : Char) : Bool := identStart c || ('0' ≤ c && c ≤ '9')
def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

def tokenize : Nat → List Char → Except String (List Tok)
  | _, [] => .ok []
  | 0, _ => refuse "token capacity"
  | fuel + 1, c :: rest => do
    if c == ' ' then tokenize fuel rest
    else if identStart c then
      let name := (c :: rest).takeWhile identChar
      return Tok.ident (String.ofList name) :: (← tokenize fuel ((c :: rest).dropWhile identChar))
    else if digit c then
      let digits := (c :: rest).takeWhile digit
      return Tok.int (digitsValue digits) :: (← tokenize fuel ((c :: rest).dropWhile digit))
    else match c, rest with
      | '=', '=' :: more => return Tok.sym "==" :: (← tokenize fuel more)
      | '<', '=' :: more => return Tok.sym "<=" :: (← tokenize fuel more)
      | _, _ =>
        if "()[],.+-".toList.contains c then return Tok.sym (String.singleton c) :: (← tokenize fuel rest)
        else refuse ("the character `" ++ String.singleton c ++ "` (the fragment compares with == and <=, \
          and combines with and, or, not, implies)")

/-! ## The parser -/

def expectSym (text : String) : List Tok → Except String (List Tok)
  | .sym t :: rest => if t == text then .ok rest else refuse ("expected `" ++ text ++ "`, found `" ++ t ++ "`")
  | t :: _ => refuse ("expected `" ++ text ++ "`, found " ++ t.render)
  | [] => refuse ("expected `" ++ text ++ "` at the end of the law")

def parseInt : List Tok → Except String (Int × List Tok)
  | .sym "-" :: .int n :: rest => .ok (-(Int.ofNat n), rest)
  | .int n :: rest => .ok (Int.ofNat n, rest)
  | t :: _ => refuse ("expected an integer literal, found " ++ t.render)
  | [] => refuse "expected an integer literal at the end of the law"

def startsInt : List Tok → Bool
  | .int _ :: _ => true
  | .sym "-" :: _ => true
  | _ => false

def requestFact : String → Option LawRef
  | "subject" => some .subject
  | "caller" => some .caller
  | "turn" => some .turn
  | _ => none

def parseRef : List Tok → Except String (LawRef × List Tok)
  | .ident "new" :: .sym "." :: .ident field :: rest =>
    match rest with
    | .sym "." :: _ => refuse ("the nested field path new." ++ field ++ ".… (edition 1 reads top-level fields of the \
        declared state only)")
    | _ => .ok (.field field, rest)
  | .ident "ledger" :: .sym "." :: .ident "height" :: rest => .ok (.height, rest)
  | .ident "ledger" :: .sym "." :: .ident fact :: _ =>
    refuse ("ledger." ++ fact ++ " (a law reads the ledger's height, ledger.height)")
  | .ident "request" :: .sym "." :: .ident "height" :: _ =>
    refuse "request.height: the height is a ledger fact, never a request field (write ledger.height)"
  | .ident "request" :: .sym "." :: .ident fact :: rest =>
    match requestFact fact with
    | some ref => .ok (ref, rest)
    | none => refuse ("request." ++ fact ++ " (a law reads request.subject, request.caller and request.turn, \
        and ledger.height)")
  | .ident "old" :: _ => refuse "old.FIELD outside monotone(FIELD) and writeOnce(FIELD)"
  | t :: _ => refuse (t.render ++ " where a reference new.FIELD, request.FACT or ledger.height was expected")
  | [] => refuse "a comparison missing its reference"

def parseIntList : Nat → List Tok → Except String (List Int × List Tok)
  | 0, _ => refuse "list capacity"
  | fuel + 1, toks => do
    let (value, rest) ← parseInt toks
    match rest with
    | .sym "," :: more =>
      let (values, after) ← parseIntList fuel more
      return (value :: values, after)
    | _ => return ([value], ← expectSym "]" rest)

def parseComparison (fuel : Nat) (toks : List Tok) : Except String (LawExpr × List Tok) := do
  let (left, rest) ← parseRef toks
  match rest with
  | .sym "==" :: more =>
    if startsInt more then
      let (value, after) ← parseInt more
      return (.eqC left value, after)
    else
      let (right, after) ← parseRef more
      return (.eqR left right, after)
  | .sym "<=" :: more =>
    if startsInt more then
      let (value, after) ← parseInt more
      return (.leC left value, after)
    else
      let (right, after) ← parseRef more
      match after with
      | .sym "+" :: offset =>
        let (k, after') ← parseInt offset
        return (.leROff left right k, after')
      | _ => return (.leR left right, after)
  | .ident "in" :: .sym "[" :: .sym "]" :: after => return (.inC left [], after)
  | .ident "in" :: .sym "[" :: more =>
    let (values, after) ← parseIntList fuel more
    return (.inC left values, after)
  | t :: _ => refuse ("the operator " ++ t.render ++ " (an atom is REF == …, REF <= …, or REF in [INT, …])")
  | [] => refuse ("the reference " ++ left.render ++ " compared with nothing")

mutual
def parseImplies : Nat → List Tok → Except String (LawExpr × List Tok)
  | 0, _ => refuse "nesting capacity"
  | fuel + 1, toks => do
    let (premise, rest) ← parseOr fuel toks
    match rest with
    | .ident "implies" :: more =>
      let (conclusion, after) ← parseImplies fuel more
      return (.implies premise conclusion, after)
    | _ => return (premise, rest)
def parseOr : Nat → List Tok → Except String (LawExpr × List Tok)
  | 0, _ => refuse "nesting capacity"
  | fuel + 1, toks => do
    let (first, rest) ← parseAnd fuel toks
    parseOrRest fuel first rest
def parseOrRest : Nat → LawExpr → List Tok → Except String (LawExpr × List Tok)
  | 0, _, _ => refuse "nesting capacity"
  | fuel + 1, acc, toks =>
    match toks with
    | .ident "or" :: more => do
      let (next, after) ← parseAnd fuel more
      parseOrRest fuel (.or acc next) after
    | _ => .ok (acc, toks)
def parseAnd : Nat → List Tok → Except String (LawExpr × List Tok)
  | 0, _ => refuse "nesting capacity"
  | fuel + 1, toks => do
    let (first, rest) ← parseUnary fuel toks
    parseAndRest fuel first rest
def parseAndRest : Nat → LawExpr → List Tok → Except String (LawExpr × List Tok)
  | 0, _, _ => refuse "nesting capacity"
  | fuel + 1, acc, toks =>
    match toks with
    | .ident "and" :: more => do
      let (next, after) ← parseUnary fuel more
      parseAndRest fuel (.and acc next) after
    | _ => .ok (acc, toks)
def parseUnary : Nat → List Tok → Except String (LawExpr × List Tok)
  | 0, _ => refuse "nesting capacity"
  | fuel + 1, toks =>
    match toks with
    | .ident "not" :: more => do
      let (body, after) ← parseUnary fuel more
      return (.not body, after)
    | .sym "(" :: more => do
      let (inner, after) ← parseImplies fuel more
      return (inner, ← expectSym ")" after)
    | .ident "monotone" :: .sym "(" :: .ident field :: .sym ")" :: after => .ok (.monotone field, after)
    | .ident "writeOnce" :: .sym "(" :: .ident field :: .sym ")" :: after => .ok (.writeOnce field, after)
    | .ident "monotone" :: _ => refuse "monotone takes one top-level field name: monotone(FIELD)"
    | .ident "writeOnce" :: _ => refuse "writeOnce takes one top-level field name: writeOnce(FIELD)"
    | _ => parseComparison fuel toks
end

/-- Parse the text after `law NAME:`. -/
def parse (text : String) : Except String LawExpr := do
  let toks ← tokenize (text.length + 1) text.toList
  if toks.isEmpty then refuse "an empty law"
  let (law, rest) ← parseImplies (8 * (toks.length + 2)) toks
  match rest with
  | [] => return law
  | t :: _ => refuse ("unexpected " ++ t.render ++ " after a complete law")

/-- Every law of a package, by name: names are unique. -/
def checkNames (laws : List (String × LawExpr)) : Except String Unit := do
  let names := laws.map (·.1)
  if names.eraseDups.length != names.length then
    throw "duplicate law name in a package"

end Obend.Spec.Law

end
