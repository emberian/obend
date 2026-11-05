module
/-
# Obend.Hardware.Hvm — a Leaf book lowered to an HVM2 interaction net, with its soundness theorem

Rung 2 of `HARDWARE.md`. HVM2 (HigherOrderCO, `github.com/HigherOrderCO/HVM2`, crate `hvm` 2.0.22,
paper `paper/HVM2.typst`) is a parallel evaluator for interaction combinators with a Rust, C and
CUDA runtime. Its input is a textual book of named nets. This module holds

* **a model of HVM2's net language** (§1): the eight node kinds of the paper's syntax (`ERA REF NUM
  CON DUP OPR SWI` and variables), nets as a root tree and a redex bag, the U24 numbers and the
  `operate` function of `src/hvm.rs`, and the interaction rules as a relation `Step` (LINK, CALL,
  VOID, ERAS, ANNI, COMM, OPER, SWIT, and the REF copy of a safe definition);
* **the emitter** `emitHvm` (§2): the model printed in the syntax `hvm run` parses (`src/ast.rs`);
* **a first-order expression IR** `FExp` and its compilation to nets `comp` (§3), with the net
  theorem `comp_reduces` (§4): a compiled expression's redexes reduce, under `Step`, to a single redex
  carrying the expression's value (`evalW`, HVM2's wrapping U24 arithmetic) at its continuation;
* **the lowering** `toF : Term → FExp` from the Leaf fragment, with `toF_sound` (§5): when the exact
  evaluation `evalE` of the lowered expression returns `w`, the source term reaches the literal `w`
  under Core4's reference reduction `Steps`;
* **the book** `lowerBookToHvm` and the theorem `lowerBookToHvm_sound` (§6).

## What `lowerBookToHvm_sound` says

For a book `B` that `lowerBookToHvm` accepts, a member `m` it lowered to `d`, and an argument
`x < 2^24` on which the lowered expression's exact evaluation stays below `2^24` everywhere
(`evalE … = some w`): the model reduces `@main = r & @m ~ (#x r)` to the normal form whose root is the
number `w` and whose bag is empty, and `evalBookAt B m (.nat x)` is a term that halts, under Core4's
reference semantics, with the ground observation `w` decodes to (`HSort.observe`): a natural number,
or a Boolean when the member's sort is `bool` (`0` false, `1` true). When `evalBookAt` is already a
literal, it is that literal (`lowerBookToHvm_sound_literal`).

## The fragment

`lowerMember` lowers `dataPinSpecialize (evalBook B m)`, the code `evalBookAt` folds, when it has the
shape `λself. λx. body`; `toF` accepts in `body`: natural literals below `2^24`, Booleans, variables in
scope (`x`, and those `ifZero` and β-redexes bind), `ifZero`, `ifBool`, `app (lam b) a` (a strict
`let`), and the primitives `add multiply subtract divide modulo equal less lessEqual conjunction` at
their Core4 sorts. Truncated subtraction, floor division and Lean's `%` are derived forms over
HVM2's wrapping operators (`subF`, `divF`, `remF`): a guard on `<`, and a divisor that is never zero,
because HVM2's Rust runtime panics on a zero divisor and eager evaluation runs a guarded quotient's
untaken branch anyway. Everything else is refused by name (`toF`): `self` reads the folder did not
resolve, `fix` (recursion would need λ-lifted `REF`s with their closures; not in this rung's first
fragment), λ-abstractions as values, records and `get`, sums and `case`, labels, `split`, the
object forms (`mix`, `specification`, `prototype`, `reflect`, `metadata`, `project`, `extend`),
activities (`perform`, `done`), holes, and the bitwise, shift, signed and fixed-point primitives.

## Where the model departs from HVM2, by name

* **LINK is the paper's global substitution** (`B[x ← A]`, `HVM2.typst` §Interactions), not the
  atomic substitution map of `src/hvm.rs`; the paper argues the two agree (§Substitution Map).
* **Schedules.** `Step` lets any redex fire, in either orientation (the rules are symmetric). The
  theorem exhibits one reduction to the normal form; that HVM2's own schedule reaches the same normal
  form is the strong confluence the paper claims for its interaction table, not proved here.
* **Numbers.** Only U24 and the operators are modelled; I24, F24 and the casts `[u24] [i24] [f24]`
  are not (`operate` returns `0` where the source would cast or use another type). A zero divisor is
  `0` for `/` and the dividend for `%` (the C runtime on arm64); the Rust runtime panics. `SWI` reads
  the 24-bit payload of whatever number it meets, as `get_u24` does.
* **CALL** takes any renaming of the definition's variables that is injective and avoids the
  configuration's variables (HVM2 allocates fresh locations); `REF ~ DUP` copies the reference when
  the definition holds no `DUP` (`def.safe`) and is stuck otherwise (HVM2 exits with an error).
  The `REF ~ ROOT` start is not modelled: a run starts from `@main`'s net with its own names.
* The paper's `CON ~ SWI` commutation (flagged as problematic in the paper) is the implementation's
  COMM; the lowering never builds it.
-/
public import Obend.Leaf.Static
@[expose] public section
namespace Obend.Hardware.Hvm
open Obend.Core.Term
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Equiv
set_option autoImplicit false

/-! ## 1. HVM2's net language -/

/-- `2^24`: HVM2's numbers are 24-bit (`NUM` nodes carry a 24-bit payload and a 5-bit tag). -/
abbrev u24Mod : Nat := 16777216

/-- HVM2's numeric operators (`src/hvm.rs`, `OP_ADD` … `FP_SHR`; `FP_*` are the flipped ones). -/
inductive HOp where
  | add | sub | fpSub | mul | div | fpDiv | rem | fpRem | eq | ne | lt | gt
  | and | or | xor | shl | fpShl | shr | fpShr
  deriving DecidableEq, Repr, Inhabited

/-- The operator's tag in `src/hvm.rs` (`OP_ADD = 0x04` …), the payload `SWI` reads from a bare operator. -/
def HOp.tag : HOp → Nat
  | .add => 4 | .sub => 5 | .fpSub => 6 | .mul => 7 | .div => 8 | .fpDiv => 9 | .rem => 10
  | .fpRem => 11 | .eq => 12 | .ne => 13 | .lt => 14 | .gt => 15 | .and => 16 | .or => 17
  | .xor => 18 | .shl => 19 | .fpShl => 20 | .shr => 21 | .fpShr => 22

/-- The operator's text in HVM2's syntax (`src/ast.rs`, `parse_numb_sym`). -/
def HOp.text : HOp → String
  | .add => "+" | .sub => "-" | .fpSub => ":-" | .mul => "*" | .div => "/" | .fpDiv => ":/"
  | .rem => "%" | .fpRem => ":%" | .eq => "=" | .ne => "!" | .lt => "<" | .gt => ">"
  | .and => "&" | .or => "|" | .xor => "^" | .shl => "<<" | .fpShl => ":<<" | .shr => ">>"
  | .fpShr => ":>>"

/-- The native U24 operation of `Numb::operate` (`src/hvm.rs`), the operator-tagged operand on the
left: `u32` wrapping arithmetic truncated to 24 bits. A zero divisor follows the C runtime on arm64
(`/` gives `0`, `%` the dividend); the Rust runtime panics there. -/
def HOp.u24 : HOp → Nat → Nat → Nat
  | .add, a, b => (a + b) % u24Mod
  | .sub, a, b => (a + u24Mod - b % u24Mod) % u24Mod
  | .fpSub, a, b => (b + u24Mod - a % u24Mod) % u24Mod
  | .mul, a, b => (a * b) % u24Mod
  | .div, a, b => if b = 0 then 0 else (a / b) % u24Mod
  | .fpDiv, a, b => if a = 0 then 0 else (b / a) % u24Mod
  | .rem, a, b => if b = 0 then a % u24Mod else (a % b) % u24Mod
  | .fpRem, a, b => if a = 0 then b % u24Mod else (b % a) % u24Mod
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .lt, a, b => if a < b then 1 else 0
  | .gt, a, b => if b < a then 1 else 0
  | .and, a, b => (a &&& b) % u24Mod
  | .or, a, b => (a ||| b) % u24Mod
  | .xor, a, b => (a ^^^ b) % u24Mod
  | .shl, a, b => (a <<< (b % 32)) % u24Mod
  | .fpShl, a, b => (b <<< (a % 32)) % u24Mod
  | .shr, a, b => (a >>> (b % 32)) % u24Mod
  | .fpShr, a, b => (b >>> (a % 32)) % u24Mod

/-- A `NUM` node's value: a U24 number, a bare operator `[+]`, or a partially applied one `[+3]`. -/
inductive Numb where
  | u24 (v : Nat)
  | sym (o : HOp)
  | part (o : HOp) (v : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `Numb::operate` restricted to U24 and the operators. -/
def Numb.operate : Numb → Numb → Numb
  | .sym _, .sym _ => .u24 0
  | .sym o, .u24 v => .part o v
  | .u24 v, .sym o => .part o v
  | .sym o, .part _ v => .part o v
  | .part _ v, .sym o => .part o v
  | .part _ _, .part _ _ => .u24 0
  | .u24 _, .u24 _ => .u24 0
  | .part o a, .u24 b => .u24 (o.u24 a b)
  | .u24 b, .part o a => .u24 (o.u24 a b)

/-- The 24-bit payload `SWI` reads (`get_u24`). -/
def Numb.payload : Numb → Nat
  | .u24 v => v
  | .sym o => o.tag
  | .part _ v => v

/-- A tree: a variable or a node. `ref` names a definition of the book. -/
inductive HTree where
  | var (n : Nat)
  | era
  | ref (name : String)
  | num (v : Numb)
  | con (a b : HTree)
  | dup (a b : HTree)
  | opr (a b : HTree)
  | swi (a b : HTree)
  deriving DecidableEq, Repr, Inhabited

/-- A redex `a ~ b`. -/
abbrev Redex := HTree × HTree

/-- A configuration: the root tree and the redex bag. -/
structure Cfg where
  root : HTree
  bag : List Redex
  deriving DecidableEq, Repr

/-- A named net of the book. -/
structure HDef where
  name : String
  root : HTree
  bag : List Redex
  deriving DecidableEq, Repr

/-- The variables of a tree, with repetition. -/
def HTree.vars : HTree → List Nat
  | .var n => [n]
  | .era | .ref _ | .num _ => []
  | .con a b | .dup a b | .opr a b | .swi a b => a.vars ++ b.vars

def redexVars (r : Redex) : List Nat := r.1.vars ++ r.2.vars

def bagVars (bag : List Redex) : List Nat := (bag.map redexVars).flatten

def Cfg.vars (c : Cfg) : List Nat := c.root.vars ++ bagVars c.bag

def HDef.vars (d : HDef) : List Nat := d.root.vars ++ bagVars d.bag

/-- Substitution of trees for variables (`none`: the variable stays). -/
def HTree.subst (S : Nat → Option HTree) : HTree → HTree
  | .var n => (S n).getD (.var n)
  | .era => .era
  | .ref f => .ref f
  | .num v => .num v
  | .con a b => .con (a.subst S) (b.subst S)
  | .dup a b => .dup (a.subst S) (b.subst S)
  | .opr a b => .opr (a.subst S) (b.subst S)
  | .swi a b => .swi (a.subst S) (b.subst S)

def Redex.subst (S : Nat → Option HTree) (r : Redex) : Redex := (r.1.subst S, r.2.subst S)

/-- The substitution of one variable. -/
def one (x : Nat) (t : HTree) : Nat → Option HTree := fun m => if m = x then some t else none

def HTree.rename (f : Nat → Nat) : HTree → HTree
  | .var n => .var (f n)
  | .era => .era
  | .ref g => .ref g
  | .num v => .num v
  | .con a b => .con (a.rename f) (b.rename f)
  | .dup a b => .dup (a.rename f) (b.rename f)
  | .opr a b => .opr (a.rename f) (b.rename f)
  | .swi a b => .swi (a.rename f) (b.rename f)

def Redex.rename (f : Nat → Nat) (r : Redex) : Redex := (r.1.rename f, r.2.rename f)

/-- A definition is `safe` when it holds no `DUP` node (`def.safe` in `src/hvm.rs`). -/
def HTree.hasDup : HTree → Bool
  | .dup _ _ => true
  | .con a b | .opr a b | .swi a b => a.hasDup || b.hasDup
  | _ => false

def HDef.safe (d : HDef) : Bool := !(d.root.hasDup || d.bag.any fun r => r.1.hasDup || r.2.hasDup)

/-- The binary node kinds. -/
inductive BinKind where
  | con | dup | opr | swi
  deriving DecidableEq, Repr

def HTree.bin? : HTree → Option (BinKind × HTree × HTree)
  | .con a b => some (.con, a, b)
  | .dup a b => some (.dup, a, b)
  | .opr a b => some (.opr, a, b)
  | .swi a b => some (.swi, a, b)
  | _ => none

def mkBin : BinKind → HTree → HTree → HTree
  | .con => .con | .dup => .dup | .opr => .opr | .swi => .swi

/-- The local rules: those that touch only the two nodes of the redex, with the nullary node on the
left (`Step.swap` gives the other orientation). VOID, ERAS (a number meeting `CON` or `DUP` is
copied), ANNI, OPER and SWIT, as in `interact_*` of `src/hvm.rs`; `none` for the redexes the
non-local rules (LINK, CALL, COMM, the `REF` copy) or no rule handle. -/
def localRule : HTree → HTree → Option (List Redex)
  -- VOID
  | .era, .era | .era, .num _ | .era, .ref _ | .num _, .era | .num _, .num _ | .num _, .ref _
  | .ref _, .era | .ref _, .num _ | .ref _, .ref _ => some []
  -- ERAS
  | .era, .con a b | .era, .dup a b | .era, .opr a b | .era, .swi a b => some [(.era, a), (.era, b)]
  | .num n, .con a b | .num n, .dup a b => some [(.num n, a), (.num n, b)]
  -- OPER
  | .num n, .opr a b => some (match a with
      | .num m => [(.num (n.operate m), b)]
      | _ => [(a, .opr (.num n) b)])
  -- SWIT
  | .num n, .swi a b => some (if n.payload = 0 then [(.con b .era, a)]
      else [(.con .era (.con (.num (.u24 (n.payload - 1))) b), a)])
  -- ANNI
  | .con a1 a2, .con b1 b2 | .dup a1 a2, .dup b1 b2 | .opr a1 a2, .opr b1 b2
  | .swi a1 a2, .swi b1 b2 => some [(a1, b1), (a2, b2)]
  | _, _ => none

/-- The interaction relation of a book, any redex of the bag, in either orientation. -/
inductive Step (book : List HDef) : Cfg → Cfg → Prop where
  /-- VOID, ERAS, ANNI, OPER, SWIT. -/
  | rule {root : HTree} {pre post : List Redex} {a b : HTree} {ns : List Redex} :
      localRule a b = some ns → Step book ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ ns ++ post⟩
  /-- The rules are symmetric: `a ~ b` is `b ~ a`. -/
  | swap {root : HTree} {pre post : List Redex} {a b : HTree} :
      Step book ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ (b, a) :: post⟩
  /-- LINK: the other occurrence of `x`, wherever it is, becomes `t`. -/
  | link {root : HTree} {pre post : List Redex} {x : Nat} {t : HTree} :
      Step book ⟨root, pre ++ (.var x, t) :: post⟩
        ⟨root.subst (one x t), (pre ++ post).map (Redex.subst (one x t))⟩
  /-- CALL: a reference meeting `CON`, `OPR` or `SWI` is replaced by its definition, under a renaming
  of the definition's variables that is injective and fresh for the configuration. -/
  | call {root : HTree} {pre post : List Redex} {f : String} {t : HTree} {d : HDef} (r : Nat → Nat) :
      book.find? (·.name == f) = some d →
      (∃ k a b, t.bin? = some (k, a, b) ∧ k ≠ .dup) →
      (∀ u ∈ d.vars, ∀ v ∈ d.vars, r u = r v → u = v) →
      (∀ u ∈ d.vars, r u ∉ (Cfg.vars ⟨root, pre ++ (.ref f, t) :: post⟩)) →
      Step book ⟨root, pre ++ (.ref f, t) :: post⟩
        ⟨root, pre ++ (d.root.rename r, t) :: d.bag.map (Redex.rename r) ++ post⟩
  /-- The copy of a reference to a safe definition meeting `DUP`. -/
  | copyRef {root : HTree} {pre post : List Redex} {f : String} {a b : HTree} {d : HDef} :
      book.find? (·.name == f) = some d → d.safe = true →
      Step book ⟨root, pre ++ (.ref f, .dup a b) :: post⟩
        ⟨root, pre ++ [(.ref f, a), (.ref f, b)] ++ post⟩
  /-- COMM: binary nodes of different kinds pass through each other, on four fresh variables. -/
  | comm {root : HTree} {pre post : List Redex} {a b a1 a2 b1 b2 : HTree} {ka kb : BinKind}
      {v0 v1 v2 v3 : Nat} :
      a.bin? = some (ka, a1, a2) → b.bin? = some (kb, b1, b2) → ka ≠ kb →
      [v0, v1, v2, v3].Nodup →
      (∀ v ∈ [v0, v1, v2, v3], v ∉ (Cfg.vars ⟨root, pre ++ (a, b) :: post⟩)) →
      Step book ⟨root, pre ++ (a, b) :: post⟩
        ⟨root, pre ++ [(mkBin kb (.var v0) (.var v1), a1), (mkBin kb (.var v2) (.var v3), a2),
          (mkBin ka (.var v0) (.var v2), b1), (mkBin ka (.var v1) (.var v3), b2)] ++ post⟩

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (book : List HDef) : Cfg → Cfg → Prop where
  | refl (c : Cfg) : Steps book c c
  | next {a b c : Cfg} : Step book a b → Steps book b c → Steps book a c

theorem Steps.trans {book : List HDef} {a b c : Cfg} (h₁ : Steps book a b) (h₂ : Steps book b c) :
    Steps book a c := by
  induction h₁ with
  | refl => exact h₂
  | next s _ ih => exact .next s (ih h₂)

theorem Steps.single {book : List HDef} {a b : Cfg} (s : Step book a b) : Steps book a b :=
  .next s (.refl _)

/-! ### An executable reducer of the model

`run` fires the head redex of the bag until the bag is empty, LINK by global substitution, CALL and
COMM on variables numbered from one past the configuration's largest. It is one schedule of `Step`
(not proved: it is the model's own run, printed beside `hvm run` and `evalBookAt` by the verify
script, so a divergence between the model and the artifact is seen). -/

def HTree.maxVar (t : HTree) : Nat := t.vars.foldl max 0

def Cfg.maxVar (c : Cfg) : Nat := c.vars.foldl max 0

/-- One step of the head-redex schedule; `none` when the bag is empty or the head redex is stuck. -/
def stepHead (book : List HDef) (c : Cfg) : Option Cfg :=
  match c.bag with
  | [] => none
  | (a, b) :: post =>
    match a, b with
    | .var x, t => some ⟨c.root.subst (one x t), post.map (Redex.subst (one x t))⟩
    | t, .var x => some ⟨c.root.subst (one x t), post.map (Redex.subst (one x t))⟩
    | .ref f, t =>
      match t.bin?, book.find? (·.name == f) with
      | some (.dup, x, y), some d => if d.safe then some ⟨c.root, [(.ref f, x), (.ref f, y)] ++ post⟩ else none
      | some _, some d =>
        let base := c.maxVar + 1
        some ⟨c.root, (d.root.rename (· + base), t) :: d.bag.map (Redex.rename (· + base)) ++ post⟩
      | _, _ => match localRule (.ref f) t with
        | some ns => some ⟨c.root, ns ++ post⟩
        | none => none
    | t, .ref f => some ⟨c.root, (.ref f, t) :: post⟩
    | a, b =>
      match localRule a b, localRule b a with
      | some ns, _ => some ⟨c.root, ns ++ post⟩
      | none, some ns => some ⟨c.root, ns ++ post⟩
      | none, none =>
        match a.bin?, b.bin? with
        | some (ka, a1, a2), some (kb, b1, b2) =>
          let v := c.maxVar + 1
          some ⟨c.root, [(mkBin kb (.var v) (.var (v + 1)), a1), (mkBin kb (.var (v + 2)) (.var (v + 3)), a2),
            (mkBin ka (.var v) (.var (v + 2)), b1), (mkBin ka (.var (v + 1)) (.var (v + 3)), b2)] ++ post⟩
        | _, _ => none

/-- Run the head-redex schedule for at most `fuel` interactions. -/
def run (book : List HDef) : Nat → Cfg → Cfg
  | 0, c => c
  | fuel + 1, c => match stepHead book c with
    | some c' => run book fuel c'
    | none => c

/-! ## 2. The emitter: HVM2's textual syntax -/

def Numb.text : Numb → String
  | .u24 v => toString v
  | .sym o => s!"[{o.text}]"
  | .part o v => s!"[{o.text}{v}]"

/-- A rule planted in the emitter, for the verify script's tooth: `swapSwitch` prints a switch's
two cases in the wrong order; `addAsSub` prints `[+]` as `[-]`. The model and the theorem never see a
plant; only the text changes. -/
inductive Plant where
  | none | swapSwitch | addAsSub
  deriving DecidableEq, Repr

def Plant.ofString? : String → Option Plant
  | "none" => some .none | "swapSwitch" => some .swapSwitch | "addAsSub" => some .addAsSub
  | _ => Option.none

def numbText (p : Plant) : Numb → String
  | .sym .add => if p == .addAsSub then "[-]" else "[+]"
  | .part .add v => if p == .addAsSub then s!"[-{v}]" else s!"[+{v}]"
  | n => n.text

def treeText (p : Plant) : HTree → String
  | .var n => s!"v{n}"
  | .era => "*"
  | .ref f => s!"@{f}"
  | .num v => numbText p v
  | .con a b => s!"({treeText p a} {treeText p b})"
  | .dup a b => s!"\{{treeText p a} {treeText p b}}"
  | .opr a b => s!"$({treeText p a} {treeText p b})"
  | .swi (.con z s) k => if p == .swapSwitch then s!"?(({treeText p s} {treeText p z}) {treeText p k})"
      else s!"?(({treeText p z} {treeText p s}) {treeText p k})"
  | .swi a b => s!"?({treeText p a} {treeText p b})"

def defText (p : Plant) (d : HDef) : String :=
  s!"@{d.name} = {treeText p d.root}" ++
    String.join (d.bag.map fun r => s!"\n  & {treeText p r.1} ~ {treeText p r.2}")

/-- **The emitter**: a book in the syntax `hvm run` reads, one definition per line group. -/
def emitHvmWith (p : Plant) (defs : List HDef) : String :=
  String.join (defs.map fun d => defText p d ++ "\n\n")

def emitHvm (defs : List HDef) : String := emitHvmWith .none defs

/-! ## 3. First-order expressions and their nets -/

/-- The expression language the lowering targets: U24 literals, de Bruijn variables, HVM2's native
operators, a strict `let` (its body binds index 0) and a switch on zero (`ifz v z s`: `z` when `v` is
`0`, else `s` with the predecessor at index 0). -/
inductive FExp where
  | lit (v : Nat)
  | var (i : Nat)
  | op (o : HOp) (a b : FExp)
  | let_ (a b : FExp)
  | ifz (v z s : FExp)
  deriving DecidableEq, Repr, Inhabited

/-- Extend an environment at index 0. -/
def cons {α : Type} (x : α) (ρ : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero {α : Type} (x : α) (ρ : Nat → α) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ {α : Type} (x : α) (ρ : Nat → α) (i : Nat) : cons x ρ (i + 1) = ρ i := rfl

/-- **The net's value**: HVM2's wrapping U24 semantics, `none` for an erased value (the eraser
`*` reaching the expression's continuation). The switch takes one branch; the other is erased. -/
def evalW : (Nat → Option Nat) → FExp → Option Nat
  | _, .lit v => some v
  | ρ, .var i => ρ i
  | ρ, .op o a b => match evalW ρ a, evalW ρ b with
    | some x, some y => some (o.u24 x y)
    | _, _ => none
  | ρ, .let_ a b => evalW (cons (evalW ρ a) ρ) b
  | ρ, .ifz v z s => match evalW ρ v with
    | some 0 => evalW ρ z
    | some (k + 1) => evalW (cons (some k) ρ) s
    | none => none

/-- The nullary node a value is: a number, or the eraser. -/
def nul : Option Nat → HTree
  | some v => .num (.u24 v)
  | none => .era

/-- The duplicator tree that hands one value to each of its occurrences: `*` for none, the
variable for one, a right-nested `DUP` chain otherwise. -/
def dupTree : List Nat → HTree
  | [] => .era
  | [o] => .var o
  | o :: o' :: os => .dup (.var o) (dupTree (o' :: os))

/-- What `comp` produces: the redexes, the variable occurrences `(de Bruijn index, net variable)`,
and the next free net variable. -/
structure Out where
  bag : List Redex
  occ : List (Nat × Nat)
  next : Nat

/-- The occurrences of index 0. -/
def occ0 (occ : List (Nat × Nat)) : List Nat := (occ.filter (fun p => p.1 == 0)).map (·.2)

/-- The occurrences of the other indices, seen from outside one binder. -/
def shiftOcc (occ : List (Nat × Nat)) : List (Nat × Nat) :=
  occ.filterMap fun p => if p.1 = 0 then none else some (p.1 - 1, p.2)

/-- **The compilation of an expression to redexes**, its value delivered to the main port of `K`
(the continuation), on net variables from `n`. A binary operation is `a ~ $([op] $(y K))` with `b`
delivered to `y`; a `let` hands `a`'s value to the occurrences of index 0 through `dupTree`; a
switch is `v ~ ?((zr (P sr)) K)` with the zero case delivered to `zr`, the successor case to `sr`,
and its predecessor handed out by `P`. -/
def comp : FExp → HTree → Nat → Out
  | .lit v, K, n => ⟨[(.num (.u24 v), K)], [], n⟩
  | .var i, K, n => ⟨[(.var n, K)], [(i, n)], n + 1⟩
  | .op o a b, K, n =>
    let rb := comp b (.var n) (n + 1)
    let ra := comp a (.opr (.num (.sym o)) (.opr (.var n) K)) rb.next
    ⟨rb.bag ++ ra.bag, rb.occ ++ ra.occ, ra.next⟩
  | .let_ a b, K, n =>
    let rb := comp b K n
    let ra := comp a (dupTree (occ0 rb.occ)) rb.next
    ⟨ra.bag ++ rb.bag, ra.occ ++ shiftOcc rb.occ, ra.next⟩
  | .ifz v z s, K, n =>
    let rz := comp z (.var n) (n + 2)
    let rs := comp s (.var (n + 1)) rz.next
    let rv := comp v (.swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K) rs.next
    ⟨rv.bag ++ rz.bag ++ rs.bag, rv.occ ++ rz.occ ++ shiftOcc rs.occ, rv.next⟩

/-! ### Substitution facts -/

/-- Every tree a substitution puts in has no variables. -/
def ClosedImg (S : Nat → Option HTree) : Prop := ∀ m T, S m = some T → T.vars = []

/-- The substitution handing `N` to every variable of `os`. -/
def many (os : List Nat) (N : HTree) : Nat → Option HTree := fun m => if m ∈ os then some N else none

/-- Two substitutions, the first one first. -/
def merge (S T : Nat → Option HTree) : Nat → Option HTree := fun m => (S m).or (T m)

@[simp] theorem bagVars_nil : bagVars [] = [] := rfl
@[simp] theorem bagVars_cons (r : Redex) (l : List Redex) :
    bagVars (r :: l) = r.1.vars ++ r.2.vars ++ bagVars l := by
  simp [bagVars, redexVars]
@[simp] theorem bagVars_append (l₁ l₂ : List Redex) : bagVars (l₁ ++ l₂) = bagVars l₁ ++ bagVars l₂ := by
  simp [bagVars]

@[simp] theorem nul_vars (x : Option Nat) : (nul x).vars = [] := by cases x <;> rfl

@[simp] theorem dupTree_vars : ∀ os : List Nat, (dupTree os).vars = os
  | [] => rfl
  | [_] => rfl
  | o :: o' :: os => by simp [dupTree, HTree.vars, dupTree_vars (o' :: os)]

theorem HTree.subst_id_of {S : Nat → Option HTree} :
    ∀ (t : HTree), (∀ v ∈ t.vars, S v = none) → t.subst S = t
  | .var n, h => by simp [HTree.subst, h n (by simp [HTree.vars])]
  | .era, _ => rfl
  | .ref _, _ => rfl
  | .num _, _ => rfl
  | .con a b, h | .dup a b, h | .opr a b, h | .swi a b, h => by
    simp only [HTree.vars, List.mem_append] at h
    simp only [HTree.subst, HTree.subst_id_of a (fun v hv => h v (.inl hv)),
      HTree.subst_id_of b (fun v hv => h v (.inr hv))]

theorem HTree.subst_closed {S : Nat → Option HTree} (t : HTree) (h : t.vars = []) : t.subst S = t :=
  t.subst_id_of (by simp [h])

@[simp] theorem nul_subst (S : Nat → Option HTree) (x : Option Nat) : (nul x).subst S = nul x :=
  HTree.subst_closed _ (nul_vars x)

theorem HTree.vars_subst {S : Nat → Option HTree} (hS : ClosedImg S) :
    ∀ (t : HTree) (v : Nat), v ∈ (t.subst S).vars → v ∈ t.vars
  | .var n, v, h => by
    simp only [HTree.subst] at h
    cases hn : S n with
    | none => simpa [hn, HTree.vars] using h
    | some T => simp [hn, hS n T hn] at h
  | .era, _, h | .ref _, _, h | .num _, _, h => by simp [HTree.subst, HTree.vars] at h
  | .con a b, v, h | .dup a b, v, h | .opr a b, v, h | .swi a b, v, h => by
    simp only [HTree.subst, HTree.vars, List.mem_append] at h ⊢
    exact h.imp (HTree.vars_subst hS a v) (HTree.vars_subst hS b v)

theorem bagVars_map_subst {S : Nat → Option HTree} (hS : ClosedImg S) (l : List Redex) (v : Nat)
    (h : v ∈ bagVars (l.map (Redex.subst S))) : v ∈ bagVars l := by
  induction l with
  | nil => simp at h
  | cons r l ih =>
    simp only [List.map_cons, bagVars_cons, Redex.subst, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (HTree.vars_subst hS _ v h))
    · exact .inl (.inr (HTree.vars_subst hS _ v h))
    · exact .inr (ih h)

theorem bag_subst_id {S : Nat → Option HTree} (l : List Redex) (h : ∀ v ∈ bagVars l, S v = none) :
    l.map (Redex.subst S) = l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [bagVars_cons, List.mem_append] at h
    simp only [List.map_cons, Redex.subst, List.cons.injEq]
    refine ⟨?_, ih (fun v hv => h v (.inr hv))⟩
    rw [HTree.subst_id_of r.1 (fun v hv => h v (.inl (.inl hv))),
      HTree.subst_id_of r.2 (fun v hv => h v (.inl (.inr hv)))]

theorem HTree.subst_merge {S : Nat → Option HTree} (T : Nat → Option HTree) (hS : ClosedImg S) :
    ∀ (t : HTree), (t.subst S).subst T = t.subst (merge S T)
  | .var n => by
    simp only [HTree.subst, merge]
    cases hn : S n with
    | none => simp [HTree.subst]
    | some A => simp [HTree.subst_closed A (hS n A hn)]
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b | .dup a b | .opr a b | .swi a b => by
    simp only [HTree.subst, HTree.subst_merge T hS a, HTree.subst_merge T hS b]

theorem bag_subst_merge {S : Nat → Option HTree} (T : Nat → Option HTree) (hS : ClosedImg S)
    (l : List Redex) : (l.map (Redex.subst S)).map (Redex.subst T) = l.map (Redex.subst (merge S T)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simp [Redex.subst, HTree.subst_merge T hS]

theorem HTree.subst_comm_one {S : Nat → Option HTree} {x : Nat} {A : HTree} (hS : ClosedImg S)
    (hx : S x = none) (hA : A.subst S = A) :
    ∀ (t : HTree), (t.subst S).subst (one x A) = (t.subst (one x A)).subst S
  | .var n => by
    by_cases h : n = x
    · subst h; simp [HTree.subst, hx, one, hA]
    · cases hn : S n with
      | none => simp [HTree.subst, hn, one, h]
      | some B => simp [HTree.subst, hn, one, h, HTree.subst_closed B (hS n B hn)]
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b | .dup a b | .opr a b | .swi a b => by
    simp only [HTree.subst, HTree.subst_comm_one hS hx hA a, HTree.subst_comm_one hS hx hA b]

theorem bag_subst_comm_one {S : Nat → Option HTree} {x : Nat} {A : HTree} (hS : ClosedImg S)
    (hx : S x = none) (hA : A.subst S = A) (l : List Redex) :
    (l.map (Redex.subst S)).map (Redex.subst (one x A)) =
      (l.map (Redex.subst (one x A))).map (Redex.subst S) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simp [Redex.subst, HTree.subst_comm_one hS hx hA]

theorem closedImg_merge {S T : Nat → Option HTree} (hS : ClosedImg S) (hT : ClosedImg T) :
    ClosedImg (merge S T) := by
  intro m U h
  simp only [merge] at h
  cases hm : S m with
  | none => rw [hm] at h; exact hT m U h
  | some B => rw [hm] at h; cases h; exact hS m _ hm

theorem closedImg_many {os : List Nat} {N : HTree} (hN : N.vars = []) : ClosedImg (many os N) := by
  intro m U h
  simp only [many] at h
  split at h
  · cases h; exact hN
  · cases h

theorem closedImg_one {x : Nat} {N : HTree} (hN : N.vars = []) : ClosedImg (one x N) := by
  intro m U h
  simp only [one] at h
  split at h
  · cases h; exact hN
  · cases h

/-! ### Facts about `comp` -/

theorem mem_occ0 {occ : List (Nat × Nat)} {o : Nat} : o ∈ occ0 occ ↔ (0, o) ∈ occ := by
  simp only [occ0, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨i, o'⟩, ⟨h, hi⟩, rfl⟩; simp only at hi; subst hi; exact h
  · intro h; exact ⟨(0, o), ⟨h, rfl⟩, rfl⟩

theorem mem_shiftOcc {occ : List (Nat × Nat)} {p : Nat × Nat} : p ∈ shiftOcc occ ↔ (p.1 + 1, p.2) ∈ occ := by
  simp only [shiftOcc, List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, o⟩, h, he⟩
    split at he
    · cases he
    · cases he; rename_i hi
      have : i - 1 + 1 = i := by omega
      simpa [this] using h
  · intro h
    exact ⟨(p.1 + 1, p.2), h, by simp⟩

theorem shiftOcc_names_sublist (occ : List (Nat × Nat)) :
    ((shiftOcc occ).map Prod.snd).Sublist (occ.map Prod.snd) := by
  induction occ with
  | nil => simp [shiftOcc]
  | cons p occ ih =>
    simp only [shiftOcc] at ih ⊢
    by_cases h : p.1 = 0
    · simp only [List.filterMap_cons, h, ite_true]; exact ih.cons _
    · simp only [List.filterMap_cons, h, ite_false, List.map_cons]; exact ih.cons_cons _

theorem occ0_sublist (occ : List (Nat × Nat)) : (occ0 occ).Sublist (occ.map Prod.snd) :=
  (List.filter_sublist).map _

theorem comp_indep : ∀ (e : FExp) (K K' : HTree) (n : Nat),
    (comp e K n).occ = (comp e K' n).occ ∧ (comp e K n).next = (comp e K' n).next
  | .lit _, _, _, _ => ⟨rfl, rfl⟩
  | .var _, _, _, _ => ⟨rfl, rfl⟩
  | .op o a b, K, K', n => by
    simp only [comp]
    obtain ⟨h1, h2⟩ := comp_indep a (.opr (.num (.sym o)) (.opr (.var n) K))
      (.opr (.num (.sym o)) (.opr (.var n) K')) (comp b (.var n) (n + 1)).next
    exact ⟨by rw [h1], h2⟩
  | .let_ a b, K, K', n => by
    simp only [comp]
    obtain ⟨hb1, hb2⟩ := comp_indep b K K' n
    rw [hb1, hb2]
    exact ⟨rfl, rfl⟩
  | .ifz v z s, K, K', n => by
    simp only [comp]
    obtain ⟨h1, h2⟩ := comp_indep v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K)
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K')
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    exact ⟨by rw [h1], h2⟩

/-- `comp`'s variables: fresh ones in `[n, next)`, and those of the continuation. -/
theorem comp_facts : ∀ (e : FExp) (K : HTree) (n : Nat),
    n ≤ (comp e K n).next ∧
    (∀ p ∈ (comp e K n).occ, n ≤ p.2 ∧ p.2 < (comp e K n).next) ∧
    ((comp e K n).occ.map Prod.snd).Nodup ∧
    (∀ v ∈ bagVars (comp e K n).bag, (n ≤ v ∧ v < (comp e K n).next) ∨ v ∈ K.vars)
  | .lit _, K, n => by
    refine ⟨Nat.le_refl _, by simp [comp], by simp [comp], ?_⟩
    intro v hv; simp [comp, HTree.vars] at hv; exact .inr hv
  | .var _, K, n => by
    refine ⟨Nat.le_succ _, by simp [comp], by simp [comp], ?_⟩
    intro v hv
    simp only [comp, bagVars_cons, HTree.vars, bagVars_nil, List.append_nil, List.mem_append,
      List.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact .inl ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact .inr hv
  | .op o a b, K, n => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · have := a2 p hp; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨b3, a3, ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := b2 p hp; have := a2 q hq; omega
    · intro v hv
      rcases List.mem_append.1 (by simpa using hv) with hv | hv
      · rcases b4 v hv with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)
      · rcases a4 v hv with h | h
        · exact .inl (by omega)
        · simp only [HTree.vars, List.nil_append, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact .inl (by omega)
          · exact .inr h
  | .let_ a b, K, n => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b K n
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := a2 p hp; omega
      · have := b2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨a3, b3.sublist (shiftOcc_names_sublist _), ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := a2 p hp; have := b2 _ (mem_shiftOcc.1 hq); simp only at this; omega
    · intro v hv
      rcases List.mem_append.1 (by simpa using hv) with hv | hv
      · rcases a4 v hv with h | h
        · exact .inl (by omega)
        · rw [dupTree_vars] at h
          have := b2 _ (mem_occ0.1 h); simp only at this; exact .inl (by omega)
      · rcases b4 v hv with h | h
        · exact .inl (by omega)
        · exact .inr h
  | .ifz v z s, K, n => by
    obtain ⟨z1, z2, z3, z4⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, s3, s4⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K) (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · have := v2 p hp; omega
      · have := z2 p hp; omega
      · have := s2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
      refine ⟨⟨v3, z3, ?_⟩, s3.sublist (shiftOcc_names_sublist _), ?_⟩
      · intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have := v2 p hp; have := z2 q hq; omega
      · intro x hx y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have hq' := s2 _ (mem_shiftOcc.1 hq); simp only at hq'
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := v2 p hp; omega
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := z2 p hp; omega
    · intro w hw
      simp only [bagVars_append, List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · rcases v4 w hw with h | h
        · exact .inl (by omega)
        · simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton, or_assoc] at h
          rcases h with h | h | h | h
          · exact .inl (by omega)
          · have := s2 _ (mem_occ0.1 h); simp only at this; exact .inl (by omega)
          · exact .inl (by omega)
          · exact .inr h
      · rcases z4 w hw with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)
      · rcases s4 w hw with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)

/-- Substituting for variables outside `comp`'s fresh range is substituting into the continuation. -/
theorem comp_subst_K : ∀ (e : FExp) (K : HTree) (n : Nat) (S : Nat → Option HTree),
    (∀ v, n ≤ v → v < (comp e K n).next → S v = none) →
    (comp e K n).bag.map (Redex.subst S) = (comp e (K.subst S) n).bag
  | .lit _, K, n, S, _ => by simp [comp, Redex.subst, HTree.subst]
  | .var _, K, n, S, h => by
    have := h n (Nat.le_refl _) (by simp [comp])
    simp [comp, Redex.subst, HTree.subst, this]
  | .op o a b, K, n, S, h => by
    obtain ⟨b1, -, -, -⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, -, -, -⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    simp only [comp] at h ⊢
    have hn : S n = none := h n (Nat.le_refl _) (by omega)
    rw [List.map_append, comp_subst_K b _ (n + 1) S (fun v h1 h2 => h v (by omega) (by omega)),
      comp_subst_K a _ _ S (fun v h1 h2 => h v (by omega) (by omega))]
    simp [HTree.subst, hn]
  | .let_ a b, K, n, S, h => by
    obtain ⟨b1, b2, -, -⟩ := comp_facts b K n
    obtain ⟨a1, -, -, -⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    simp only [comp] at h ⊢
    have hd : (dupTree (occ0 (comp b K n).occ)).subst S = dupTree (occ0 (comp b K n).occ) := by
      apply HTree.subst_id_of
      intro v hv
      rw [dupTree_vars] at hv
      have := b2 _ (mem_occ0.1 hv); simp only at this
      exact h v (by omega) (by omega)
    obtain ⟨hi1, hi2⟩ := comp_indep b K (K.subst S) n
    rw [List.map_append, comp_subst_K a _ _ S (fun v h1 h2 => h v (by omega) (by omega)),
      comp_subst_K b _ n S (fun v h1 h2 => h v (by omega) (by omega)), hd, hi1, hi2]
  | .ifz v z s, K, n, S, h => by
    obtain ⟨z1, -, -, -⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, -, -⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, -, -, -⟩ := comp_facts v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K) (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    simp only [comp] at h ⊢
    have hn : S n = none := h n (Nat.le_refl _) (by omega)
    have hn1 : S (n + 1) = none := h (n + 1) (by omega) (by omega)
    have hd : (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)).subst S =
        dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ) := by
      apply HTree.subst_id_of
      intro w hw
      rw [dupTree_vars] at hw
      have := s2 _ (mem_occ0.1 hw); simp only at this
      exact h w (by omega) (by omega)
    rw [List.map_append, List.map_append, comp_subst_K v _ _ S (fun w h1 h2 => h w (by omega) (by omega)),
      comp_subst_K z _ (n + 2) S (fun w h1 h2 => h w (by omega) (by omega)),
      comp_subst_K s _ _ S (fun w h1 h2 => h w (by omega) (by omega))]
    simp [HTree.subst, hn, hn1, hd]

/-! ### Steps in context -/

theorem steps_eq {book : List HDef} {c c' : Cfg} (h : c = c') : Steps book c c' := h ▸ .refl c

theorem sRule {book : List HDef} {root : HTree} {l l' : List Redex} (pre post : List Redex) {a b : HTree}
    {ns : List Redex} (h : localRule a b = some ns) (hl : l = pre ++ (a, b) :: post)
    (hl' : l' = pre ++ (ns ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'; rw [← List.append_assoc]; exact .single (.rule h)

theorem sSwap {book : List HDef} {root : HTree} {l l' : List Redex} (pre post : List Redex) {a b : HTree}
    (hl : l = pre ++ (a, b) :: post) (hl' : l' = pre ++ (b, a) :: post) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'; exact .single .swap

theorem one_none {x v : Nat} {t : HTree} (h : v ≠ x) : one x t v = none := by simp [one, h]

theorem sLink {book : List HDef} {root : HTree} {l l' : List Redex} (pre mid post : List Redex) (x : Nat)
    (t : HTree) (hr : x ∉ root.vars) (hp : x ∉ bagVars pre) (hq : x ∉ bagVars post)
    (hl : l = pre ++ (.var x, t) :: (mid ++ post))
    (hl' : l' = pre ++ (mid.map (Redex.subst (one x t)) ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'
  have h1 := Step.link (book := book) (root := root) (pre := pre) (post := mid ++ post) (x := x) (t := t)
  have er : root.subst (one x t) = root :=
    HTree.subst_id_of _ (fun v hv => one_none (fun h => hr (h ▸ hv)))
  have ep : pre.map (Redex.subst (one x t)) = pre :=
    bag_subst_id _ (fun v hv => one_none (fun h => hp (h ▸ hv)))
  have eq : post.map (Redex.subst (one x t)) = post :=
    bag_subst_id _ (fun v hv => one_none (fun h => hq (h ▸ hv)))
  rw [er, List.map_append, List.map_append, ep, eq] at h1
  exact .single h1

theorem sLinkR {book : List HDef} {root : HTree} {l l' : List Redex} (pre mid post : List Redex) (x : Nat)
    (t : HTree) (hr : x ∉ root.vars) (hp : x ∉ bagVars pre) (hq : x ∉ bagVars post)
    (hl : l = pre ++ (t, .var x) :: (mid ++ post))
    (hl' : l' = pre ++ (mid.map (Redex.subst (one x t)) ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ :=
  (sSwap pre (mid ++ post) hl rfl).trans (sLink pre mid post x t hr hp hq rfl hl')

/-- A nullary value meets the duplicator tree: every occurrence receives it. -/
def Nullary (N : HTree) : Prop := N = .era ∨ ∃ v, N = .num (.u24 v)

theorem nullary_nul (x : Option Nat) : Nullary (nul x) := by
  cases x
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

theorem Nullary.vars {N : HTree} (h : Nullary N) : N.vars = [] := by
  rcases h with rfl | ⟨v, rfl⟩ <;> rfl

theorem localRule_void {N M : HTree} (hN : Nullary N) (hM : Nullary M) : localRule N M = some [] := by
  rcases hN with rfl | ⟨_, rfl⟩ <;> rcases hM with rfl | ⟨_, rfl⟩ <;> rfl

theorem sSpread {book : List HDef} (N : HTree) (hN : Nullary N) : ∀ (os : List Nat) {root : HTree}
    {l l' : List Redex} (pre mid post : List Redex), os.Nodup →
    (∀ o ∈ os, o ∉ root.vars ∧ o ∉ bagVars pre ∧ o ∉ bagVars post) →
    l = pre ++ (N, dupTree os) :: (mid ++ post) →
    l' = pre ++ (mid.map (Redex.subst (many os N)) ++ post) →
    Steps book ⟨root, l⟩ ⟨root, l'⟩
  | [], root, l, l', pre, mid, post, _, _, hl, hl' => by
    refine sRule pre (mid ++ post) (localRule_void hN (.inl rfl)) hl ?_
    rw [hl', bag_subst_id mid (fun v _ => by simp [many])]
    simp
  | [o], root, l, l', pre, mid, post, _, ho, hl, hl' => by
    obtain ⟨h1, h2, h3⟩ := ho o (by simp)
    refine sLinkR pre mid post o N h1 h2 h3 hl ?_
    rw [hl']
    have : many [o] N = one o N := by funext m; simp [many, one]
    rw [this]
  | o :: o' :: os, root, l, l', pre, mid, post, hnd, ho, hl, hl' => by
    obtain ⟨h1, h2, h3⟩ := ho o (by simp)
    have hr : localRule N (.dup (.var o) (dupTree (o' :: os))) =
        some [(N, .var o), (N, dupTree (o' :: os))] := by
      rcases hN with rfl | ⟨_, rfl⟩ <;> rfl
    have hno : o ∉ o' :: os := (List.nodup_cons.1 hnd).1
    have hnd' : (o' :: os).Nodup := (List.nodup_cons.1 hnd).2
    refine (sRule pre (mid ++ post) hr hl rfl).trans ?_
    refine (sLinkR pre ((N, dupTree (o' :: os)) :: mid) post o N h1 h2 h3 (by simp) rfl).trans ?_
    have e1 : ((N, dupTree (o' :: os)) :: mid).map (Redex.subst (one o N)) =
        (N, dupTree (o' :: os)) :: mid.map (Redex.subst (one o N)) := by
      simp only [List.map_cons, Redex.subst, List.cons.injEq, Prod.mk.injEq, and_true]
      refine ⟨HTree.subst_closed _ hN.vars, HTree.subst_id_of _ ?_⟩
      intro v hv; rw [dupTree_vars] at hv
      exact one_none (fun h => hno (h ▸ hv))
    rw [e1]
    refine sSpread N hN (o' :: os) pre (mid.map (Redex.subst (one o N))) post hnd'
      (fun o'' h => ho o'' (List.mem_cons_of_mem _ h)) (by simp) ?_
    rw [hl', bag_subst_merge _ (closedImg_one hN.vars)]
    have : merge (one o N) (many (o' :: os) N) = many (o :: o' :: os) N := by
      funext m; by_cases hm : m = o
      · subst hm; simp [merge, one, many]
      · simp [merge, one, many, hm]
    rw [this]

theorem fresh4 {root K : HTree} {pre post : List Redex} {P : Nat → Prop}
    (h : ∀ v ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, P v) :
    (∀ v ∈ root.vars, P v) ∧ (∀ v ∈ bagVars pre, P v) ∧ (∀ v ∈ bagVars post, P v) ∧ (∀ v ∈ K.vars, P v) :=
  ⟨fun v hv => h v (by simp [hv]), fun v hv => h v (by simp [hv]), fun v hv => h v (by simp [hv]),
    fun v hv => h v (by simp [hv])⟩

theorem fresh4_mk {root K : HTree} {pre post : List Redex} {P : Nat → Prop}
    (hr : ∀ v ∈ root.vars, P v) (hp : ∀ v ∈ bagVars pre, P v) (hq : ∀ v ∈ bagVars post, P v)
    (hk : ∀ v ∈ K.vars, P v) : ∀ v ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, P v := by
  intro v hv
  simp only [List.mem_append] at hv
  rcases hv with ((h | h) | h) | h
  · exact hr v h
  · exact hp v h
  · exact hq v h
  · exact hk v h

theorem nodup_name {l : List (Nat × Nat)} (h : (l.map Prod.snd).Nodup) {x y : Nat × Nat} (hx : x ∈ l)
    (hy : y ∈ l) (he : x.2 = y.2) : x = y := by
  induction l with
  | nil => cases hx
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 hx with ex | lx <;> rcases List.mem_cons.1 hy with ey | ly
    · rw [ex, ey]
    · subst ex; exact absurd ⟨y, ly, he.symm⟩ h.1
    · subst ey; exact absurd ⟨x, lx, he⟩ h.1
    · exact ih h.2 lx ly

/-- **The net theorem.** The redexes `comp e K n` produces, with every variable occurrence of index
`i` already holding the nullary value `nul (ρ i)` (the substitution `S`), reduce under `Step` to the
single redex `nul (evalW ρ e) ~ K`, whatever redexes `pre` and `post` sit beside them, provided the
fresh variables `[n, next)` occur nowhere else. -/
theorem comp_reduces (book : List HDef) : ∀ (e : FExp) (K : HTree) (n : Nat) (ρ : Nat → Option Nat)
    (S : Nat → Option HTree) (root : HTree) (pre post : List Redex),
    (∀ p ∈ (comp e K n).occ, S p.2 = some (nul (ρ p.1))) →
    (∀ o, n ≤ o → o < (comp e K n).next → (∀ p ∈ (comp e K n).occ, p.2 ≠ o) → S o = none) →
    ClosedImg S → K.subst S = K →
    (∀ v ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, v < n ∨ (comp e K n).next ≤ v) →
    Steps book ⟨root, pre ++ ((comp e K n).bag.map (Redex.subst S) ++ post)⟩
      ⟨root, pre ++ (nul (evalW ρ e), K) :: post⟩
  | .lit v, K, n, ρ, S, root, pre, post, _, _, _, hK, _ => by
    simp only [comp, List.map_cons, List.map_nil, Redex.subst, HTree.subst, hK, evalW, nul,
      List.cons_append, List.nil_append]
    exact .refl _
  | .var i, K, n, ρ, S, root, pre, post, h1, _, _, hK, _ => by
    have := h1 (i, n) (by simp [comp])
    simp only [comp, List.map_cons, List.map_nil, Redex.subst, HTree.subst, hK, evalW, this,
      Option.getD_some, List.cons_append, List.nil_append]
    exact .refl _
  | .op o a b, K, n, ρ, S, root, pre, post, h1, h2, hS, hK, hF => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    obtain ⟨i1, i2⟩ := comp_indep a (.opr (.num (.sym o)) (.opr (nul (evalW ρ b)) K))
      (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    have hsub := comp_subst_K a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
      (one n (nul (evalW ρ b))) (fun v hv _ => one_none (by omega))
    have IHb := comp_reduces book b (.var n) (n + 1) ρ S root pre
      ((comp a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next).bag.map
        (Redex.subst S) ++ post)
    have IHa := comp_reduces book a (.opr (.num (.sym o)) (.opr (nul (evalW ρ b)) K))
      (comp b (.var n) (n + 1)).next ρ S root pre post
    simp only [comp] at h1 h2 hF ⊢
    rw [i1, i2] at IHa
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    have hKn : K.subst (one n (nul (evalW ρ b))) = K :=
      HTree.subst_id_of _ (fun v hv => one_none (by have := Fk v hv; omega))
    rw [show (HTree.opr (.num (.sym o)) (.opr (.var n) K)).subst (one n (nul (evalW ρ b))) =
      .opr (.num (.sym o)) (.opr (nul (evalW ρ b)) K) by simp [HTree.subst, one, hKn]] at hsub
    generalize comp b (.var n) (n + 1) = rb at *
    generalize comp a (.opr (.num (.sym o)) (.opr (.var n) K)) rb.next = ra at *
    have hSn : S n = none := h2 n (Nat.le_refl _) (by omega) (by
      intro p hp; rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · have := a2 p hp; omega)
    -- b, then its value linked into a's continuation, then a
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHb (fun p hp => h1 p (List.mem_append_left _ hp)) ?_ hS (by simp [HTree.subst, hSn]) ?_).trans ?_)
    · intro o' ho1 ho2 hno
      refine h2 o' (by omega) (by omega) (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · exact hno p hp
      · have := a2 p hp; omega
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · simp only [bagVars_append, List.mem_append] at hv
        rcases hv with hv | hv
        · rcases a4 v (bagVars_map_subst hS _ v hv) with h | h
          · omega
          · simp only [HTree.vars, List.nil_append, List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · omega
            · have := Fk v h; omega
        · have := Fq v hv; omega
      · simp only [HTree.vars, List.mem_singleton] at hv; omega
    refine (sLinkR pre (ra.bag.map (Redex.subst S)) post n (nul (evalW ρ b))
      (fun h => by have := Fr n h; omega) (fun h => by have := Fp n h; omega)
      (fun h => by have := Fq n h; omega) rfl rfl).trans ?_
    rw [bag_subst_comm_one hS hSn (nul_subst S _), hsub]
    refine (IHa (fun p hp => h1 p (List.mem_append_right _ hp)) ?_ hS
      (by simp [HTree.subst, hK]) ?_).trans ?_
    · intro o' ho1 ho2 hno
      refine h2 o' (by omega) ho2 (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · exact hno p hp
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · have := Fq v hv; omega
      · simp only [HTree.vars, nul_vars, List.nil_append] at hv
        have := Fk v hv; omega
    -- the operator node meets the two values
    cases ha : evalW ρ a with
    | none =>
      simp only [evalW, ha]
      refine (sRule pre post (a := .era) (b := .opr (.num (.sym o)) (.opr (nul (evalW ρ b)) K))
        (ns := [(.era, .num (.sym o)), (.era, .opr (nul (evalW ρ b)) K)]) rfl (by simp [nul]) rfl).trans ?_
      refine (sRule pre ((.era, .opr (nul (evalW ρ b)) K) :: post) (a := .era) (b := .num (.sym o))
        (ns := []) rfl (by simp) rfl).trans ?_
      refine (sRule pre post (a := .era) (b := .opr (nul (evalW ρ b)) K)
        (ns := [(.era, nul (evalW ρ b)), (.era, K)]) rfl (by simp) rfl).trans ?_
      exact sRule pre ((.era, K) :: post) (localRule_void (.inl rfl) (nullary_nul (evalW ρ b))) (by simp)
        (by simp [nul])
    | some x =>
      cases hb : evalW ρ b with
      | none =>
        simp only [evalW, ha, hb]
        refine (sRule pre post (a := .num (.u24 x)) (b := .opr (.num (.sym o)) (.opr .era K))
          (ns := [(.num (.part o x), .opr .era K)]) rfl (by simp [nul]) rfl).trans ?_
        refine (sRule pre post (a := .num (.part o x)) (b := .opr .era K)
          (ns := [(.era, .opr (.num (.part o x)) K)]) rfl (by simp) rfl).trans ?_
        refine (sRule pre post (a := .era) (b := .opr (.num (.part o x)) K)
          (ns := [(.era, .num (.part o x)), (.era, K)]) rfl (by simp) rfl).trans ?_
        exact sRule pre ((.era, K) :: post) (a := .era) (b := .num (.part o x)) (ns := []) rfl (by simp)
          (by simp [nul])
      | some y =>
        simp only [evalW, ha, hb]
        refine (sRule pre post (a := .num (.u24 x)) (b := .opr (.num (.sym o)) (.opr (.num (.u24 y)) K))
          (ns := [(.num (.part o x), .opr (.num (.u24 y)) K)]) rfl (by simp [nul]) rfl).trans ?_
        exact sRule pre post (a := .num (.part o x)) (b := .opr (.num (.u24 y)) K)
          (ns := [(.num (.u24 (o.u24 x y)), K)]) rfl (by simp) (by simp [nul])
  | .let_ a b, K, n, ρ, S, root, pre, post, h1, h2, hS, hK, hF => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b K n
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    have IHa := comp_reduces book a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next ρ S root pre
      ((comp b K n).bag.map (Redex.subst S) ++ post)
    have IHb := comp_reduces book b K n (cons (evalW ρ a) ρ)
      (merge S (many (occ0 (comp b K n).occ) (nul (evalW ρ a)))) root pre post
    simp only [comp, evalW] at h1 h2 hF ⊢
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    generalize comp b K n = rb at *
    generalize comp a (dupTree (occ0 rb.occ)) rb.next = ra at *
    have hos : ∀ o ∈ occ0 rb.occ, n ≤ o ∧ o < rb.next := fun o ho => b2 _ (mem_occ0.1 ho)
    have hshift : ∀ p ∈ shiftOcc rb.occ, ∀ o ∈ occ0 rb.occ, p.2 ≠ o := by
      intro p hp o ho heq
      have := nodup_name b3 (mem_shiftOcc.1 hp) (mem_occ0.1 ho) heq
      simp at this
    have hSos : ∀ o ∈ occ0 rb.occ, S o = none := by
      intro o ho
      have hr := hos o ho
      refine h2 o hr.1 (by omega) (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · have := a2 p hp; omega
      · exact hshift p hp o ho
    have hnd : (occ0 rb.occ).Nodup := b3.sublist (occ0_sublist _)
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHa (fun p hp => h1 p (List.mem_append_left _ hp)) ?_ hS
        (HTree.subst_id_of _ (fun v hv => hSos v (by rwa [dupTree_vars] at hv))) ?_).trans ?_)
    · intro o ho1 ho2 hno
      refine h2 o (by omega) ho2 (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · exact hno p hp
      · have := b2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · simp only [bagVars_append, List.mem_append] at hv
        rcases hv with hv | hv
        · rcases b4 v (bagVars_map_subst hS _ v hv) with h | h
          · omega
          · have := Fk v h; omega
        · have := Fq v hv; omega
      · rw [dupTree_vars] at hv; have := hos v hv; omega
    refine (sSpread (nul (evalW ρ a)) (nullary_nul _) (occ0 rb.occ) pre (rb.bag.map (Redex.subst S)) post
      hnd (fun o ho => ?_) rfl rfl).trans ?_
    · have := hos o ho
      exact ⟨fun h => by have := Fr o h; omega, fun h => by have := Fp o h; omega,
        fun h => by have := Fq o h; omega⟩
    rw [bag_subst_merge _ hS]
    refine IHb ?_ ?_ (closedImg_merge hS (closedImg_many (nul_vars _))) ?_ ?_
    · rintro ⟨i, o⟩ hp
      cases i with
      | zero =>
        have ho : o ∈ occ0 rb.occ := mem_occ0.2 hp
        simp [merge, hSos o ho, many, ho]
      | succ k =>
        have := h1 (k, o) (List.mem_append_right _ (mem_shiftOcc.2 hp))
        simp [merge, this]
    · intro o ho1 ho2 hno
      have hSo : S o = none := by
        refine h2 o ho1 (by omega) (fun p hp => ?_)
        rcases List.mem_append.1 hp with hp | hp
        · have := a2 p hp; omega
        · exact hno (p.1 + 1, p.2) (mem_shiftOcc.1 hp)
      have hmo : o ∉ occ0 rb.occ := fun h => hno _ (mem_occ0.1 h) rfl
      simp [merge, hSo, many, hmo]
    · rw [← HTree.subst_merge _ hS, hK]
      refine HTree.subst_id_of _ (fun v hv => ?_)
      have hv' : v ∉ occ0 rb.occ := fun h => by have := hos v h; have := Fk v hv; omega
      simp [many, hv']
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · have := Fq v hv; omega
      · have := Fk v hv; omega
  | .ifz v z s, K, n, ρ, S, root, pre, post, h1, h2, hS, hK, hF => by
    obtain ⟨z1, z2, z3, z4⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, s3, s4⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v (.swi (.con (.var n) (.con (dupTree (occ0
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)) (.var (n + 1)))) K)
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    have IHv := comp_reduces book v (.swi (.con (.var n) (.con (dupTree (occ0
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)) (.var (n + 1)))) K)
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next ρ S root pre
      ((comp z (.var n) (n + 2)).bag.map (Redex.subst S) ++
        ((comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).bag.map (Redex.subst S) ++ post))
    have hz : ∀ T, (comp z (.var n) (n + 2)).bag.map (Redex.subst (one n T)) = (comp z T (n + 2)).bag := by
      intro T
      rw [comp_subst_K z _ _ _ (fun w h _ => one_none (by omega))]
      simp [HTree.subst, one]
    have hs : ∀ T, (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).bag.map
        (Redex.subst (one (n + 1) T)) = (comp s T (comp z (.var n) (n + 2)).next).bag := by
      intro T
      rw [comp_subst_K s _ _ _ (fun w h _ => one_none (by omega))]
      simp [HTree.subst, one]
    have iz : ∀ T, (comp z T (n + 2)).occ = (comp z (.var n) (n + 2)).occ ∧
        (comp z T (n + 2)).next = (comp z (.var n) (n + 2)).next := fun T => comp_indep z T _ _
    have is' : ∀ T, (comp s T (comp z (.var n) (n + 2)).next).occ =
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ ∧
        (comp s T (comp z (.var n) (n + 2)).next).next =
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next := fun T => comp_indep s T _ _
    have fz : ∀ T, ∀ w ∈ bagVars (comp z T (n + 2)).bag, (n + 2 ≤ w ∧ w < (comp z (.var n) (n + 2)).next) ∨
        w ∈ T.vars := by
      intro T w hw
      obtain ⟨-, -, -, h4⟩ := comp_facts z T (n + 2)
      rw [(iz T).2] at h4; exact h4 w hw
    have fs : ∀ T, ∀ w ∈ bagVars (comp s T (comp z (.var n) (n + 2)).next).bag,
        ((comp z (.var n) (n + 2)).next ≤ w ∧ w < (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next) ∨
        w ∈ T.vars := by
      intro T w hw
      obtain ⟨-, -, -, h4⟩ := comp_facts s T (comp z (.var n) (n + 2)).next
      rw [(is' T).2] at h4; exact h4 w hw
    have IHz : ∀ (T : HTree) (ρ' : Nat → Option Nat) (S' : Nat → Option HTree) (root' : HTree)
        (pre' post' : List Redex),
        (∀ p ∈ (comp z (.var n) (n + 2)).occ, S' p.2 = some (nul (ρ' p.1))) →
        (∀ o, n + 2 ≤ o → o < (comp z (.var n) (n + 2)).next → (∀ p ∈ (comp z (.var n) (n + 2)).occ, p.2 ≠ o) →
          S' o = none) →
        ClosedImg S' → T.subst S' = T →
        (∀ w ∈ root'.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < n + 2 ∨ (comp z (.var n) (n + 2)).next ≤ w) →
        Steps book ⟨root', pre' ++ ((comp z T (n + 2)).bag.map (Redex.subst S') ++ post')⟩
          ⟨root', pre' ++ (nul (evalW ρ' z), T) :: post'⟩ := by
      intro T ρ' S' root' pre' post'
      rw [← (iz T).1, ← (iz T).2]
      exact comp_reduces book z T (n + 2) ρ' S' root' pre' post'
    have IHs : ∀ (T : HTree) (ρ' : Nat → Option Nat) (S' : Nat → Option HTree) (root' : HTree)
        (pre' post' : List Redex),
        (∀ p ∈ (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ, S' p.2 = some (nul (ρ' p.1))) →
        (∀ o, (comp z (.var n) (n + 2)).next ≤ o → o < (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next →
          (∀ p ∈ (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ, p.2 ≠ o) → S' o = none) →
        ClosedImg S' → T.subst S' = T →
        (∀ w ∈ root'.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < (comp z (.var n) (n + 2)).next ∨
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next ≤ w) →
        Steps book ⟨root', pre' ++ ((comp s T (comp z (.var n) (n + 2)).next).bag.map (Redex.subst S') ++ post')⟩
          ⟨root', pre' ++ (nul (evalW ρ' s), T) :: post'⟩ := by
      intro T ρ' S' root' pre' post'
      rw [← (is' T).1, ← (is' T).2]
      exact comp_reduces book s T _ ρ' S' root' pre' post'
    simp only [comp] at h1 h2 hF ⊢
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    generalize comp z (.var n) (n + 2) = rz at *
    generalize comp s (.var (n + 1)) rz.next = rs at *
    generalize comp v (.swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K) rs.next = rv at *
    -- facts
    have hos : ∀ o ∈ occ0 rs.occ, rz.next ≤ o ∧ o < rs.next := fun o ho => s2 _ (mem_occ0.1 ho)
    have hnd : (occ0 rs.occ).Nodup := s3.sublist (occ0_sublist _)
    have notOcc : ∀ o, n ≤ o → o < rv.next → (∀ p ∈ rv.occ, p.2 ≠ o) → (∀ p ∈ rz.occ, p.2 ≠ o) →
        (∀ p ∈ rs.occ, p.2 ≠ o) → S o = none := by
      intro o h1o h2o hv hz' hs'
      refine h2 o h1o h2o (fun p hp => ?_)
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hv p hp
      · exact hz' p hp
      · exact hs' (p.1 + 1, p.2) (mem_shiftOcc.1 hp)
    have hSn : S n = none := notOcc n (Nat.le_refl _) (by omega)
      (fun p hp => by have := v2 p hp; omega) (fun p hp => by have := z2 p hp; omega)
      (fun p hp => by have := s2 p hp; omega)
    have hSn1 : S (n + 1) = none := notOcc (n + 1) (by omega) (by omega)
      (fun p hp => by have := v2 p hp; omega) (fun p hp => by have := z2 p hp; omega)
      (fun p hp => by have := s2 p hp; omega)
    have hSos : ∀ o ∈ occ0 rs.occ, S o = none := by
      intro o ho
      have := hos o ho
      refine h2 o (by omega) (by omega) (fun p hp => ?_)
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · have := v2 p hp; omega
      · have := z2 p hp; omega
      · intro heq
        have := nodup_name s3 (mem_shiftOcc.1 hp) (mem_occ0.1 ho) heq
        simp at this
    have sH1 : ∀ x : Option Nat, ∀ p ∈ rs.occ,
        merge S (many (occ0 rs.occ) (nul x)) p.2 = some (nul (cons x ρ p.1)) := by
      rintro x ⟨i, o⟩ hp
      cases i with
      | zero =>
        have ho : o ∈ occ0 rs.occ := mem_occ0.2 hp
        simp [merge, hSos o ho, many, ho]
      | succ k =>
        have := h1 (k, o) (List.mem_append_right _ (mem_shiftOcc.2 hp))
        simp [merge, this]
    have sH2 : ∀ N, ∀ o, rz.next ≤ o → o < rs.next → (∀ p ∈ rs.occ, p.2 ≠ o) →
        merge S (many (occ0 rs.occ) N) o = none := by
      intro N o ho1 ho2 hno
      have hSo : S o = none := notOcc o (by omega) (by omega) (fun p hp => by have := v2 p hp; omega)
        (fun p hp => by have := z2 p hp; omega) hno
      have hmo : o ∉ occ0 rs.occ := fun h => hno _ (mem_occ0.1 h) rfl
      simp [merge, hSo, many, hmo]
    have zH2 : ∀ o, n + 2 ≤ o → o < rz.next → (∀ p ∈ rz.occ, p.2 ≠ o) → S o = none := by
      intro o ho1 ho2 hno
      exact notOcc o (by omega) (by omega) (fun p hp => by have := v2 p hp; omega) hno
        (fun p hp => by have := s2 p hp; omega)
    have hKos : ∀ N, K.subst (many (occ0 rs.occ) N) = K := fun N => HTree.subst_id_of _ (fun w hw => by
      have hw' : w ∉ occ0 rs.occ := fun h => by have := hos w h; have := Fk w hw; omega
      simp [many, hw'])
    have hKS1 : ∀ N, K.subst (merge S (many (occ0 rs.occ) N)) = K := fun N => by
      rw [← HTree.subst_merge _ hS, hK, hKos]
    have hS1 : ∀ x : Option Nat, ClosedImg (merge S (many (occ0 rs.occ) (nul x))) :=
      fun x => closedImg_merge hS (closedImg_many (nul_vars _))
    have hS1n1 : ∀ N, merge S (many (occ0 rs.occ) N) (n + 1) = none := fun N => by
      have : n + 1 ∉ occ0 rs.occ := fun h => by have := hos _ h; omega
      simp [merge, hSn1, many, this]
    -- unchanged pieces
    have keepZ : ∀ T (U : Nat → Option HTree), (∀ w, (n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ T.vars → U w = none) →
        ((comp z T (n + 2)).bag.map (Redex.subst S)).map (Redex.subst U) =
          (comp z T (n + 2)).bag.map (Redex.subst S) := fun T U hU =>
      bag_subst_id _ (fun w hw => hU w (fz T w (bagVars_map_subst hS _ w hw)))
    have keepS : ∀ U : Nat → Option HTree, (∀ w, (rz.next ≤ w ∧ w < rs.next) ∨ w = n + 1 → U w = none) →
        (rs.bag.map (Redex.subst S)).map (Redex.subst U) = rs.bag.map (Redex.subst S) := by
      intro U hU
      refine bag_subst_id _ (fun w hw => hU w ?_)
      rcases s4 w (bagVars_map_subst hS _ w hw) with h | h
      · exact .inl h
      · simp only [HTree.vars, List.mem_singleton] at h; exact .inr h
    have many_none : ∀ N w, w ∉ occ0 rs.occ → many (occ0 rs.occ) N w = none := fun N w h => by
      simp [many, h]
    have nFr : ∀ w, n ≤ w → w < rv.next → w ∉ root.vars := fun w h1 h2 h => by have := Fr w h; omega
    have nFp : ∀ w, n ≤ w → w < rv.next → w ∉ bagVars pre := fun w h1 h2 h => by have := Fp w h; omega
    have nFq : ∀ w, n ≤ w → w < rv.next → w ∉ bagVars post := fun w h1 h2 h => by have := Fq w h; omega
    have nFk : ∀ w, n ≤ w → w < rv.next → w ∉ K.vars := fun w h1 h2 h => by have := Fk w h; omega
    have spreadFresh : ∀ o ∈ occ0 rs.occ, o ∉ root.vars ∧ o ∉ bagVars pre ∧ o ∉ bagVars post := fun o ho => by
      have := hos o ho
      exact ⟨nFr o (by omega) (by omega), nFp o (by omega) (by omega), nFq o (by omega) (by omega)⟩
    have Pfix : (HTree.con (dupTree (occ0 rs.occ)) (.var (n + 1))).subst (one n K) =
        .con (dupTree (occ0 rs.occ)) (.var (n + 1)) := by
      refine HTree.subst_id_of _ (fun w hw => one_none ?_)
      simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have := hos w hw; omega
      · omega
    have Pfix' : ∀ T, (HTree.con (dupTree (occ0 rs.occ)) (.var (n + 1))).subst (one n T) =
        .con (dupTree (occ0 rs.occ)) (.var (n + 1)) := by
      intro T
      refine HTree.subst_id_of _ (fun w hw => one_none ?_)
      simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have := hos w hw; omega
      · omega
    have Rfix : ∀ T, Redex.subst (one n T) (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) =
        (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) := fun T => by
      simp only [Redex.subst, Pfix' T]; rfl
    have KfixN : ∀ T, K.subst (one n T) = K := fun T =>
      HTree.subst_id_of _ (fun w hw => one_none (fun h => nFk w (by omega) (by omega) (h ▸ hw)))
    have Kfix1 : ∀ T, K.subst (one (n + 1) T) = K := fun T =>
      HTree.subst_id_of _ (fun w hw => one_none (fun h => nFk w (by omega) (by omega) (h ▸ hw)))
    have zfresh : ∀ T, T.vars = [] ∨ T = K → ∀ (pre' post' : List Redex),
        (∀ w ∈ bagVars pre', w < n + 2 ∨ rz.next ≤ w) → (∀ w ∈ bagVars post', w < n + 2 ∨ rz.next ≤ w) →
        ∀ w ∈ root.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < n + 2 ∨ rz.next ≤ w := by
      intro T hT pre' post' hp hq
      refine fresh4_mk (fun w hw => ?_) hp hq (fun w hw => ?_)
      · have := Fr w hw; omega
      · rcases hT with hT | rfl
        · simp [hT] at hw
        · have := Fk w hw; omega
    -- the condition first
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHv (fun p hp => h1 p (List.mem_append_left _ (List.mem_append_left _ hp))) ?_ hS ?_ ?_).trans ?_)
    · intro o ho1 ho2 hno
      exact notOcc o (by omega) ho2 hno (fun p hp => by have := z2 p hp; omega)
        (fun p hp => by have := s2 p hp; omega)
    · have hd : (dupTree (occ0 rs.occ)).subst S = dupTree (occ0 rs.occ) :=
        HTree.subst_id_of _ (fun w hw => hSos w (by rwa [dupTree_vars] at hw))
      simp [HTree.subst, hSn, hSn1, hd, hK]
    · refine fresh4_mk (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_)
      · have := Fr w hw; omega
      · have := Fp w hw; omega
      · simp only [bagVars_append, List.mem_append] at hw
        rcases hw with hw | hw | hw
        · rcases z4 w (bagVars_map_subst hS _ w hw) with h | h
          · omega
          · simp [HTree.vars] at h; omega
        · rcases s4 w (bagVars_map_subst hS _ w hw) with h | h
          · omega
          · simp [HTree.vars] at h; omega
        · have := Fq w hw; omega
      · simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton, or_assoc] at hw
        rcases hw with hw | hw | hw | hw
        · omega
        · have := hos w hw; omega
        · omega
        · have := Fk w hw; omega
    have zH1 : ∀ p ∈ rz.occ, S p.2 = some (nul (ρ p.1)) :=
      fun p hp => h1 p (List.mem_append_left _ (List.mem_append_right _ hp))
    have sFresh : ∀ (T : HTree) (pre' : List Redex), (∀ w ∈ T.vars, w < rz.next ∨ rs.next ≤ w) →
        (∀ w ∈ bagVars pre', w < rz.next ∨ rs.next ≤ w) →
        ∀ w ∈ root.vars ++ bagVars pre' ++ bagVars post ++ T.vars, w < rz.next ∨ rs.next ≤ w := by
      intro T pre' hT hp
      refine fresh4_mk (fun w hw => ?_) hp (fun w hw => ?_) hT
      · have := Fr w hw; omega
      · have := Fq w hw; omega
    have preK : ∀ (N : HTree), N.vars = [] → ∀ w ∈ bagVars (pre ++ [(N, K)]), w < rz.next ∨ rs.next ≤ w := by
      intro N hN w hw
      simp only [bagVars_append, bagVars_cons, hN, bagVars_nil, List.append_nil, List.nil_append,
        List.mem_append] at hw
      rcases hw with hw | hw
      · have := Fp w hw; omega
      · have := Fk w hw; omega
    have seFresh : ∀ (T : HTree) (S' : Nat → Option HTree), ClosedImg S' → T.vars = [] →
        ∀ w ∈ bagVars ((comp s T rz.next).bag.map (Redex.subst S') ++ post), w < n + 2 ∨ rz.next ≤ w := by
      intro T S' hS' hT w hw
      simp only [bagVars_append, List.mem_append] at hw
      rcases hw with hw | hw
      · rcases fs T w (bagVars_map_subst hS' _ w hw) with h | h
        · omega
        · simp [hT] at h
      · have := Fq w hw; omega
    have pFresh : ∀ w ∈ bagVars pre, w < n + 2 ∨ rz.next ≤ w := fun w hw => by have := Fp w hw; omega
    have osNot : ∀ w, ((n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ K.vars) → w ∉ occ0 rs.occ := by
      intro w hw ho
      have := hos w ho
      rcases hw with hw | hw
      · omega
      · exact nFk w (by omega) (by omega) hw
    have osNot' : ∀ w, ((n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ (nul none).vars) → w ∉ occ0 rs.occ := by
      intro w hw ho
      have := hos w ho
      rcases hw with hw | hw
      · omega
      · simp [nul, HTree.vars] at hw
    have n1os : n + 1 ∉ occ0 rs.occ := fun h => by have := hos _ h; omega
    cases hv : evalW ρ v with
    | some k =>
      cases k with
      | zero =>
        simp only [evalW, hv]
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .num (.u24 0)) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
          (ns := [(.con K .era, .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))])
          rfl (by simp [nul]) rfl).trans ?_
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con K .era) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
          (ns := [(K, .var n), (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))]) rfl (by simp) rfl).trans ?_
        refine (sLinkR pre ((.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) ::
          (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n K
          (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
          (by simp) rfl).trans ?_
        rw [List.map_cons, List.map_append, bag_subst_comm_one hS hSn hK, hz,
          keepS _ (fun w hw => one_none (by omega)), Rfix]
        refine (sRule pre ((comp z K (n + 2)).bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .era) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
          (ns := [(.era, dupTree (occ0 rs.occ)), (.era, .var (n + 1))]) rfl (by simp) rfl).trans ?_
        refine (sSpread (nul none) (nullary_nul none) (occ0 rs.occ) pre ((.era, .var (n + 1)) ::
          ((comp z K (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
          (by simp [nul]) rfl).trans ?_
        rw [List.map_cons, List.map_append, keepZ K _ (fun w hw => many_none _ _ (osNot w hw)),
          bag_subst_merge _ hS]
        simp only [Redex.subst, HTree.subst, many_none _ _ n1os, Option.getD_none]
        refine (sLinkR pre ((comp z K (n + 2)).bag.map (Redex.subst S) ++
          rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul none))))) post (n + 1) (nul none)
          (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
          (by simp [nul]) rfl).trans ?_
        rw [List.map_append, keepZ K _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · exact fun h => nFk w (by omega) (by omega) (h ▸ hw))),
          bag_subst_comm_one (hS1 none) (hS1n1 _) (nul_subst _ _), hs]
        rw [List.append_assoc]
        refine (IHz K ρ S root pre _ zH1 zH2 hS hK
          (zfresh K (.inr rfl) pre _ pFresh (seFresh _ _ (hS1 none) (nul_vars none)))).trans ?_
        refine (steps_eq (by simp)).trans ((IHs (nul none) (cons none ρ) _ root (pre ++ [(nul (evalW ρ z), K)]) post
          (sH1 none) (sH2 _) (hS1 none) (nul_subst _ _)
          (sFresh _ _ (by simp) (preK _ (nul_vars _)))).trans ?_)
        exact sRule (pre ++ [(nul (evalW ρ z), K)]) post
          (localRule_void (nullary_nul (evalW (cons none ρ) s)) (nullary_nul none)) rfl (by simp)
      | succ k =>
        simp only [evalW, hv]
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .num (.u24 (k + 1))) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
          (ns := [(.con .era (.con (.num (.u24 k)) K), .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))])
          (by simp [localRule, Numb.payload]) (by simp [nul]) rfl).trans ?_
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con .era (.con (.num (.u24 k)) K)) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
          (ns := [(.era, .var n), (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))])
          rfl (by simp) rfl).trans ?_
        refine (sLinkR pre ((.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) ::
          (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n (nul none)
          (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
          (by simp [nul]) rfl).trans ?_
        have R2 : Redex.subst (one n (nul none)) (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) =
            (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) := by
          simp only [Redex.subst, Pfix' (nul none)]
          simp only [HTree.subst, KfixN]
        rw [List.map_cons, List.map_append, bag_subst_comm_one hS hSn (nul_subst _ _), hz,
          keepS _ (fun w hw => one_none (by omega)), R2]
        refine (sRule pre ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con (.num (.u24 k)) K) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
          (ns := [(.num (.u24 k), dupTree (occ0 rs.occ)), (K, .var (n + 1))]) rfl (by simp) rfl).trans ?_
        refine (sSpread (nul (some k)) (nullary_nul _) (occ0 rs.occ) pre ((K, .var (n + 1)) ::
          ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
          (by simp [nul]) rfl).trans ?_
        have R3 : Redex.subst (many (occ0 rs.occ) (nul (some k))) (K, .var (n + 1)) = (K, .var (n + 1)) := by
          simp only [Redex.subst, hKos]
          simp [HTree.subst, many_none _ _ n1os]
        rw [List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => many_none _ _ (osNot' w hw)),
          bag_subst_merge _ hS, R3]
        refine (sLinkR pre ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
          rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul (some k)))))) post (n + 1) K
          (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
          (by simp) rfl).trans ?_
        rw [List.map_append, keepZ (nul none) _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · simp [nul, HTree.vars] at hw)),
          bag_subst_comm_one (hS1 (some k)) (hS1n1 _) (hKS1 _), hs]
        rw [List.append_assoc]
        refine (IHz (nul none) ρ S root pre _ zH1 zH2 hS (nul_subst _ _)
          (zfresh (nul none) (.inl (nul_vars _)) pre _ pFresh ?_)).trans ?_
        · intro w hw
          simp only [bagVars_append, List.mem_append] at hw
          rcases hw with hw | hw
          · rcases fs K w (bagVars_map_subst (hS1 (some k)) _ w hw) with h | h
            · omega
            · have := Fk w h; omega
          · have := Fq w hw; omega
        refine (sRule pre ((comp s K rz.next).bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul (some k))))) ++ post)
          (localRule_void (nullary_nul (evalW ρ z)) (nullary_nul none)) rfl rfl).trans ?_
        refine (steps_eq (by simp)).trans (IHs K (cons (some k) ρ) _ root pre post
          (sH1 (some k)) (sH2 _) (hS1 (some k)) (hKS1 _) (sFresh _ _ (fun w hw => by have := Fk w hw; omega)
            (fun w hw => by have := Fp w hw; omega)))
    | none =>
      simp only [evalW, hv]
      refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
        (a := .era) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
        (ns := [(.era, .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))), (.era, K)])
        rfl (by simp [nul]) rfl).trans ?_
      refine (sRule pre ((.era, K) :: (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post)))
        (a := .era) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
        (ns := [(.era, .var n), (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))]) rfl (by simp) rfl).trans ?_
      refine (sLinkR pre ((.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) :: (.era, K) ::
        (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n (nul none)
        (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
        (by simp [nul]) rfl).trans ?_
      have R4 : Redex.subst (one n (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, KfixN]; rfl
      rw [List.map_cons, List.map_cons, List.map_append, bag_subst_comm_one hS hSn (nul_subst _ _), hz,
        keepS _ (fun w hw => one_none (by omega)), Rfix, R4]
      refine (sRule pre ((.era, K) :: ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
          (rs.bag.map (Redex.subst S) ++ post)))
        (a := .era) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
        (ns := [(.era, dupTree (occ0 rs.occ)), (.era, .var (n + 1))]) rfl (by simp) rfl).trans ?_
      refine (sSpread (nul none) (nullary_nul none) (occ0 rs.occ) pre ((.era, .var (n + 1)) :: (.era, K) ::
        ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
        (by simp [nul]) rfl).trans ?_
      have R5 : Redex.subst (many (occ0 rs.occ) (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, hKos]; rfl
      have R6 : Redex.subst (many (occ0 rs.occ) (nul none)) (.era, .var (n + 1)) = (.era, .var (n + 1)) := by
        simp [Redex.subst, HTree.subst, many_none _ _ n1os]
      rw [List.map_cons, List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => many_none _ _ (osNot' w hw)),
        bag_subst_merge _ hS, R5, R6]
      refine (sLinkR pre ((.era, K) :: ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
        rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul none)))))) post (n + 1) (nul none)
        (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
        (by simp [nul]) rfl).trans ?_
      have R7 : Redex.subst (one (n + 1) (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, Kfix1]; rfl
      rw [List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · simp [nul, HTree.vars] at hw)),
        bag_subst_comm_one (hS1 none) (hS1n1 _) (nul_subst _ _), hs, R7]
      refine (steps_eq (by simp)).trans ((IHz (nul none) ρ S root (pre ++ [(.era, K)]) _ zH1 zH2 hS (nul_subst _ _)
          (zfresh (nul none) (.inl (nul_vars _)) _ _ ?_ (seFresh _ _ (hS1 none) (nul_vars none)))).trans ?_)
      · intro w hw
        simp only [bagVars_append, bagVars_cons, HTree.vars, bagVars_nil, List.append_nil, List.nil_append,
          List.mem_append] at hw
        rcases hw with hw | hw
        · have := Fp w hw; omega
        · have := Fk w hw; omega
      refine (sRule (pre ++ [(.era, K)]) ((comp s (nul none) rz.next).bag.map
          (Redex.subst (merge S (many (occ0 rs.occ) (nul none)))) ++ post)
        (localRule_void (nullary_nul (evalW ρ z)) (nullary_nul none)) rfl rfl).trans ?_
      refine (steps_eq (by simp)).trans ((IHs (nul none) (cons none ρ) _ root (pre ++ [(.era, K)]) post
        (sH1 none) (sH2 _) (hS1 none) (nul_subst _ _) (sFresh _ _ (by simp) (preK .era rfl))).trans ?_)
      exact sRule (pre ++ [(.era, K)]) post
        (localRule_void (nullary_nul (evalW (cons none ρ) s)) (nullary_nul none)) rfl (by simp [nul])


/-! ## 5. The lowering from the Leaf fragment, and its soundness against Core4 -/

/-- The sort of a lowered expression: a natural, or a Boolean carried as `0`/`1`. -/
inductive HSort where
  | nat | bool
  deriving DecidableEq, Repr

/-- The Core4 literal a U24 result decodes to. -/
def HSort.lit : HSort → Nat → Term
  | .nat, w => .nat w
  | .bool, w => .boolean (w != 0)

/-- A Boolean is carried as `0` or `1`. -/
def HSort.valid : HSort → Nat → Prop
  | .nat, _ => True
  | .bool, w => w ≤ 1

/-- The ground observation a U24 result decodes to. -/
def HSort.observe : HSort → Nat → Observation
  | .nat, w => .natural w
  | .bool, w => .boolean (w != 0)

theorem HSort.observes (s : HSort) (w : Nat) : Observes (s.lit w) (s.observe w) := by
  cases s
  · exact .natural w
  · exact .boolean _

theorem HSort.lit_value (s : HSort) (w : Nat) : Value (s.lit w) := by
  cases s
  · exact .natural w
  · exact .boolean _

/-- A value below `2^24`, or nothing. -/
def ck (v : Nat) : Option Nat := if v < u24Mod then some v else none

/-- The exact operation on naturals, where it agrees with Core4 (`none`: underflow, a zero divisor,
or an operator the lowering does not use). -/
def exactOp : HOp → Nat → Nat → Option Nat
  | .add, a, b => some (a + b)
  | .mul, a, b => some (a * b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .div, a, b => if b = 0 then none else some (a / b)
  | .rem, a, b => if b = 0 then none else some (a % b)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .gt, a, b => some (if b < a then 1 else 0)
  | .and, a, b => some (a &&& b)
  | .xor, a, b => some (a ^^^ b)
  | _, _, _ => none

/-- **The exact evaluation**: every value it computes is the Core4 value and lies below `2^24`;
`none` when one would not (or a variable is out of scope). Where it answers, the net's wrapping
evaluation `evalW` answers the same (`evalE_evalW`). -/
def evalE : (Nat → Option Nat) → FExp → Option Nat
  | _, .lit v => ck v
  | η, .var i => (η i).bind ck
  | η, .op o a b => match evalE η a, evalE η b with
    | some x, some y => (exactOp o x y).bind ck
    | _, _ => none
  | η, .let_ a b => match evalE η a with
    | some x => evalE (cons (some x) η) b
    | none => none
  | η, .ifz v z s => match evalE η v with
    | some 0 => evalE η z
    | some (k + 1) => evalE (cons (some k) η) s
    | none => none

theorem ck_some {v w : Nat} (h : ck v = some w) : v = w ∧ w < u24Mod := by
  unfold ck at h; split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem exactOp_u24 {o : HOp} {x y r : Nat} (h : exactOp o x y = some r) (hy : y < u24Mod)
    (hr : r < u24Mod) : o.u24 x y = r := by
  cases o
  case sub =>
    simp only [exactOp] at h
    by_cases hle : y ≤ x
    · simp only [hle, ite_true, Option.some.injEq] at h
      subst h
      simp only [HOp.u24]
      rw [Nat.mod_eq_of_lt hy, show x + u24Mod - y = (x - y) + u24Mod by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hr]
    · simp [hle] at h
  case div =>
    simp only [exactOp] at h
    by_cases hy0 : y = 0
    · simp [hy0] at h
    · simp only [hy0, ite_false, Option.some.injEq] at h
      subst h; simp [HOp.u24, hy0, Nat.mod_eq_of_lt hr]
  case rem =>
    simp only [exactOp] at h
    by_cases hy0 : y = 0
    · simp [hy0] at h
    · simp only [hy0, ite_false, Option.some.injEq] at h
      subst h; simp [HOp.u24, hy0, Nat.mod_eq_of_lt hr]
  all_goals simp only [exactOp] at h
  all_goals first
    | (cases h; done)
    | (cases h; simp only [HOp.u24]; exact Nat.mod_eq_of_lt hr)
    | (cases h; rfl)

/-- **Exact is wrapping where exact answers.** -/
theorem evalE_evalW : ∀ (f : FExp) (η : Nat → Option Nat) (w : Nat), evalE η f = some w →
    evalW η f = some w ∧ w < u24Mod
  | .lit v, η, w, h => by
    obtain ⟨rfl, hw⟩ := ck_some h; exact ⟨rfl, hw⟩
  | .var i, η, w, h => by
    simp only [evalE] at h
    cases hi : η i with
    | none => simp [hi] at h
    | some u =>
      simp only [hi, Option.bind_some] at h
      obtain ⟨rfl, hw⟩ := ck_some h; exact ⟨by simp [evalW, hi], hw⟩
  | .op o a b, η, w, h => by
    simp only [evalE] at h
    cases ha : evalE η a with
    | none => simp [ha] at h
    | some x =>
      cases hb : evalE η b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        cases hr : exactOp o x y with
        | none => simp [hr] at h
        | some r =>
          simp only [hr, Option.bind_some] at h
          obtain ⟨rfl, hw⟩ := ck_some h
          obtain ⟨wa, -⟩ := evalE_evalW a η x ha
          obtain ⟨wb, hyb⟩ := evalE_evalW b η y hb
          exact ⟨by simp [evalW, wa, wb, exactOp_u24 hr hyb hw], hw⟩
  | .let_ a b, η, w, h => by
    simp only [evalE] at h
    cases ha : evalE η a with
    | none => simp [ha] at h
    | some x =>
      simp only [ha] at h
      obtain ⟨wa, -⟩ := evalE_evalW a η x ha
      obtain ⟨wb, hw⟩ := evalE_evalW b _ w h
      exact ⟨by simp [evalW, wa, wb], hw⟩
  | .ifz v z s, η, w, h => by
    simp only [evalE] at h
    cases hv : evalE η v with
    | none => simp [hv] at h
    | some k =>
      obtain ⟨wv, -⟩ := evalE_evalW v η k hv
      cases k with
      | zero =>
        simp only [hv] at h
        obtain ⟨wz, hw⟩ := evalE_evalW z η w h
        exact ⟨by simp [evalW, wv, wz], hw⟩
      | succ k =>
        simp only [hv] at h
        obtain ⟨ws, hw⟩ := evalE_evalW s _ w h
        exact ⟨by simp [evalW, wv, ws], hw⟩

theorem evalE_lt {f : FExp} {η : Nat → Option Nat} {w : Nat} (h : evalE η f = some w) : w < u24Mod :=
  (evalE_evalW f η w h).2

/-- Lift the variables at or above `c` (a binder inserted at `c`). -/
def FExp.lift (c : Nat) : FExp → FExp
  | .lit v => .lit v
  | .var i => .var (if i < c then i else i + 1)
  | .op o a b => .op o (a.lift c) (b.lift c)
  | .let_ a b => .let_ (a.lift c) (b.lift (c + 1))
  | .ifz v z s => .ifz (v.lift c) (z.lift c) (s.lift (c + 1))

/-- The environment with `x` inserted at `c`. -/
def ins (c : Nat) (x : Option Nat) (η : Nat → Option Nat) : Nat → Option Nat :=
  fun i => if i < c then η i else if i = c then x else η (i - 1)

theorem ins_cons (c : Nat) (x y : Option Nat) (η : Nat → Option Nat) :
    ins (c + 1) x (cons y η) = cons y (ins c x η) := by
  funext i
  cases i with
  | zero => simp [ins]
  | succ i =>
    simp only [ins, cons_succ]
    by_cases h1 : i < c
    · simp [h1]
    · by_cases h2 : i = c
      · subst h2; simp
      · have h3 : ¬ i + 1 < c + 1 := by omega
        have h4 : ¬ i + 1 = c + 1 := by omega
        simp only [h3, h4, h1, h2, ite_false]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp

theorem evalE_lift : ∀ (f : FExp) (c : Nat) (x : Option Nat) (η : Nat → Option Nat),
    evalE (ins c x η) (f.lift c) = evalE η f
  | .lit _, _, _, _ => rfl
  | .var i, c, x, η => by
    simp only [FExp.lift, evalE, ins]
    by_cases h : i < c
    · simp [h]
    · have h1 : ¬ i + 1 < c := by omega
      have h2 : ¬ i + 1 = c := by omega
      simp [h, h1, h2]
  | .op o a b, c, x, η => by simp only [FExp.lift, evalE, evalE_lift a, evalE_lift b]
  | .let_ a b, c, x, η => by
    simp only [FExp.lift, evalE, evalE_lift a]
    cases evalE η a with
    | none => rfl
    | some y => simp only; rw [← ins_cons, evalE_lift b]
  | .ifz v z s, c, x, η => by
    simp only [FExp.lift, evalE, evalE_lift v, evalE_lift z]
    cases evalE η v with
    | none => rfl
    | some k =>
      cases k with
      | zero => rfl
      | succ k => simp only; rw [← ins_cons, evalE_lift s]

theorem evalE_lift0 (f : FExp) (x : Nat) (η : Nat → Option Nat) :
    evalE (cons (some x) η) (f.lift 0) = evalE η f := by
  have : ins 0 (some x) η = cons (some x) η := by
    funext i; cases i <;> simp [ins]
  rw [← this, evalE_lift]

/-- Truncated subtraction over the wrapping one: `x < y` selects `0`. -/
def subF (l r : FExp) : FExp :=
  .let_ l (.let_ (r.lift 0) (.ifz (.op .lt (.var 1) (.var 0)) (.op .sub (.var 1) (.var 0)) (.lit 0)))

/-- The divisor `y + (y = 0)`: never zero, and `y` itself in the branch where `y ≠ 0` is used. HVM2's
Rust runtime panics on a zero divisor, and eager evaluation runs the untaken branch too. -/
def safeDivisor : FExp := .op .add (.var 1) (.op .eq (.var 1) (.lit 0))

/-- Floor division with `x / 0 = 0`. -/
def divF (l r : FExp) : FExp :=
  .let_ l (.let_ (r.lift 0) (.ifz (.var 0) (.lit 0) (.op .div (.var 2) safeDivisor)))

/-- Lean's `%`, with `x % 0 = x`. -/
def remF (l r : FExp) : FExp :=
  .let_ l (.let_ (r.lift 0) (.ifz (.var 0) (.var 1) (.op .rem (.var 2) safeDivisor)))

/-- `x ≤ y` as `(x > y) xor 1`. -/
def leF (l r : FExp) : FExp := .op .xor (.op .gt l r) (.lit 1)

/-- The primitives the lowering accepts, at their Core4 sorts. -/
def binF : Primitive → HSort → HSort → Option ((FExp → FExp → FExp) × HSort)
  | .add, .nat, .nat => some (.op .add, .nat)
  | .multiply, .nat, .nat => some (.op .mul, .nat)
  | .subtract, .nat, .nat => some (subF, .nat)
  | .divide, .nat, .nat => some (divF, .nat)
  | .modulo, .nat, .nat => some (remF, .nat)
  | .equal, .nat, .nat => some (.op .eq, .bool)
  | .less, .nat, .nat => some (.op .lt, .bool)
  | .lessEqual, .nat, .nat => some (leF, .bool)
  | .conjunction, .bool, .bool => some (.op .and, .bool)
  | _, _, _ => none

theorem evalE_op {η : Nat → Option Nat} {o : HOp} {a b : FExp} {w : Nat} (h : evalE η (.op o a b) = some w) :
    ∃ x y r, evalE η a = some x ∧ evalE η b = some y ∧ exactOp o x y = some r ∧ r = w := by
  simp only [evalE] at h
  cases ha : evalE η a with
  | none => simp [ha] at h
  | some x =>
    cases hb : evalE η b with
    | none => simp [ha, hb] at h
    | some y =>
      simp only [ha, hb] at h
      cases hr : exactOp o x y with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.bind_some] at h
        exact ⟨x, y, r, rfl, rfl, hr, (ck_some h).1⟩

theorem evalE_let2 {η : Nat → Option Nat} {l r body : FExp} {w : Nat}
    (h : evalE η (.let_ l (.let_ (r.lift 0) body)) = some w) :
    ∃ x y, evalE η l = some x ∧ evalE η r = some y ∧ evalE (cons (some y) (cons (some x) η)) body = some w := by
  simp only [evalE] at h
  cases hl : evalE η l with
  | none => simp [hl] at h
  | some x =>
    simp only [hl, evalE_lift0] at h
    cases hr : evalE η r with
    | none => simp [hr] at h
    | some y => simp only [hr] at h; exact ⟨x, y, rfl, rfl, h⟩

theorem ck_of_lt {v : Nat} (h : v < u24Mod) : ck v = some v := by simp [ck, h]

/-- **The primitives are sound**: where the lowered form evaluates exactly, Core4's primitive gives
the decoded result. -/
theorem binF_sound {op : Primitive} {sl sr s : HSort} {mk : FExp → FExp → FExp}
    (hb : binF op sl sr = some (mk, s)) {η : Nat → Option Nat} {fl fr : FExp} {w : Nat}
    (h : evalE η (mk fl fr) = some w) :
    ∃ x y, evalE η fl = some x ∧ evalE η fr = some y ∧
      (sl.valid x → sr.valid y → primitiveResult op (sl.lit x) (sr.lit y) = some (s.lit w) ∧ s.valid w) := by
  cases op <;> cases sl <;> cases sr <;> simp only [binF, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
  all_goals obtain ⟨rfl, rfl⟩ := hb
  -- add
  · obtain ⟨x, y, r, hx, hy, hr, rfl⟩ := evalE_op h
    simp only [exactOp, Option.some.injEq] at hr
    exact ⟨x, y, hx, hy, fun _ _ => ⟨by simp [primitiveResult, HSort.lit, hr], trivial⟩⟩
  -- multiply
  · obtain ⟨x, y, r, hx, hy, hr, rfl⟩ := evalE_op h
    simp only [exactOp, Option.some.injEq] at hr
    exact ⟨x, y, hx, hy, fun _ _ => ⟨by simp [primitiveResult, HSort.lit, hr], trivial⟩⟩
  -- equal
  · obtain ⟨x, y, r, hx, hy, hr, rfl⟩ := evalE_op h
    simp only [exactOp, Option.some.injEq] at hr
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, ?_⟩⟩
    · subst hr; by_cases hxy : x = y <;> simp [primitiveResult, HSort.lit, hxy]
    · subst hr; simp only [HSort.valid]; split <;> omega
  -- conjunction
  · obtain ⟨x, y, r, hx, hy, hr, rfl⟩ := evalE_op h
    simp only [exactOp, Option.some.injEq] at hr
    refine ⟨x, y, hx, hy, fun vx vy => ?_⟩
    simp only [HSort.valid] at vx vy
    subst hr
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;>
      simp [primitiveResult, HSort.lit, HSort.valid]
  -- subtract
  · obtain ⟨x, y, hx, hy, hb⟩ := evalE_let2 h
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, trivial⟩⟩
    have lx := evalE_lt hx; have ly := evalE_lt hy
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt lx, ck_of_lt ly, exactOp] at hb
    by_cases hxy : x < y
    · simp only [hxy, ite_true, ck_of_lt (show 1 < u24Mod by decide)] at hb
      simp only [ck_of_lt (show 0 < u24Mod by decide)] at hb
      cases hb
      simp [primitiveResult, HSort.lit, Nat.sub_eq_zero_of_le (Nat.le_of_lt hxy)]
    · simp only [hxy, ite_false, ck_of_lt (show 0 < u24Mod by decide)] at hb
      have hle : y ≤ x := by omega
      simp only [hle, ite_true, Option.bind_some] at hb
      first | (obtain ⟨rfl, -⟩ := ck_some hb) | (simp only [Option.some.injEq] at hb; subst hb) | cases hb
      simp [primitiveResult, HSort.lit]
  -- divide
  · obtain ⟨x, y, hx, hy, hb⟩ := evalE_let2 h
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, trivial⟩⟩
    have lx := evalE_lt hx; have ly := evalE_lt hy
    cases y with
    | zero =>
      simp only [evalE, cons_zero, Option.bind_some, ck_of_lt ly] at hb
      first | (obtain ⟨rfl, -⟩ := ck_some hb) | (simp only [Option.some.injEq] at hb; subst hb) | cases hb
      simp [primitiveResult, HSort.lit]
    | succ k =>
      simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt ly, ck_of_lt lx, safeDivisor,
        exactOp, ck_of_lt (show 0 < u24Mod by decide), Nat.add_one_ne_zero, ite_false, Nat.add_zero] at hb
      try simp only [ck_of_lt (show 0 < u24Mod by decide), Option.bind_some, ck_of_lt ly, Nat.add_zero,
        Nat.add_one_ne_zero, ite_false] at hb
      first | (obtain ⟨rfl, -⟩ := ck_some hb) | (simp only [Option.some.injEq] at hb; subst hb) | cases hb
      simp [primitiveResult, HSort.lit]
  -- less
  · obtain ⟨x, y, r, hx, hy, hr, rfl⟩ := evalE_op h
    simp only [exactOp, Option.some.injEq] at hr
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, ?_⟩⟩
    · subst hr; by_cases hxy : x < y <;> simp [primitiveResult, HSort.lit, hxy]
    · subst hr; simp only [HSort.valid]; split <;> omega
  -- lessEqual
  · simp only [leF] at h
    obtain ⟨g, one, r, hg, hone, hr, rfl⟩ := evalE_op h
    obtain ⟨x, y, r', hx, hy, hr', rfl⟩ := evalE_op hg
    simp only [evalE, ck_of_lt (show 1 < u24Mod by decide), Option.some.injEq] at hone
    subst hone
    simp only [exactOp, Option.some.injEq] at hr hr'
    subst hr hr'
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, ?_⟩⟩
    · by_cases hxy : y < x
      · have : ¬ x ≤ y := by omega
        simp [primitiveResult, HSort.lit, hxy, this]
      · have : x ≤ y := by omega
        simp [primitiveResult, HSort.lit, hxy, this]
    · simp only [HSort.valid]; split <;> decide
  -- modulo
  · obtain ⟨x, y, hx, hy, hb⟩ := evalE_let2 h
    refine ⟨x, y, hx, hy, fun _ _ => ⟨?_, trivial⟩⟩
    have lx := evalE_lt hx; have ly := evalE_lt hy
    cases y with
    | zero =>
      simp only [evalE, cons_zero, cons_succ, Option.bind_some, ck_of_lt ly, ck_of_lt lx] at hb
      cases hb
      simp [primitiveResult, HSort.lit]
    | succ k =>
      simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt ly, ck_of_lt lx, safeDivisor,
        exactOp, ck_of_lt (show 0 < u24Mod by decide), Nat.add_one_ne_zero, ite_false, Nat.add_zero] at hb
      try simp only [ck_of_lt (show 0 < u24Mod by decide), Option.bind_some, ck_of_lt ly, Nat.add_zero,
        Nat.add_one_ne_zero, ite_false] at hb
      first | (obtain ⟨rfl, -⟩ := ck_some hb) | (simp only [Option.some.injEq] at hb; subst hb) | cases hb
      simp [primitiveResult, HSort.lit]

/-- **The lowering of a term** at the sorts `Γ` of its variables, or the reason it is refused. -/
def toF (Γ : List HSort) : Term → Except String (FExp × HSort)
  | .nat v => if v < u24Mod then .ok (.lit v, .nat)
      else .error s!"literal {v} is not below 2^24 (HVM2's U24)"
  | .boolean b => .ok (.lit (if b then 1 else 0), .bool)
  | .bound i => match Γ[i]? with
    | some s => .ok (.var i, s)
    | none => .error s!"variable {i} is out of scope: a `self` read the folder did not resolve, or a free variable"
  | .binary op l r => match toF Γ l, toF Γ r with
    | .ok (fl, sl), .ok (fr, sr) => match binF op sl sr with
      | some (mk, s) => .ok (mk fl fr, s)
      | none => .error s!"primitive {repr op} at sorts {repr sl}, {repr sr}: outside the fragment"
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ifZero v z s => match toF Γ v, toF Γ z, toF (.nat :: Γ) s with
    | .ok (fv, .nat), .ok (fz, sz), .ok (fs, ss) =>
      if sz = ss then .ok (.ifz fv fz fs, sz) else .error "ifZero: branches of different sorts"
    | .ok (_, .bool), _, _ => .error "ifZero on a Boolean"
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | .ifBool c t f => match toF Γ c, toF Γ t, toF Γ f with
    | .ok (fc, .bool), .ok (ft, st), .ok (ff, sf) =>
      if st = sf then .ok (.ifz fc ff (ft.lift 0), st) else .error "ifBool: branches of different sorts"
    | .ok (_, .nat), _, _ => .error "ifBool on a natural"
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | .app (.lam b) a => match toF Γ a with
    | .ok (fa, sa) => match toF (sa :: Γ) b with
      | .ok (fb, sb) => .ok (.let_ fa fb, sb)
      | .error e => .error e
    | .error e => .error e
  | .app (.fix _ _) _ => .error "fix: recursion needs λ-lifted REFs carrying their closures; not in this rung's fragment"
  | .app _ _ => .error "application of a non-literal function: higher-order, not in the first-order fragment"
  | .lam _ => .error "a λ-abstraction as a value: higher-order, not in the first-order fragment"
  | .fix _ _ => .error "fix: recursion needs λ-lifted REFs carrying their closures; not in this rung's fragment"
  | .hole _ _ => .error "a hole"
  | .mix _ _ => .error "mix: an object form"
  | .specification _ _ => .error "specification: an object form"
  | .prototype _ _ => .error "prototype: an object form"
  | .reflect _ => .error "reflect: an object form"
  | .metadata _ => .error "metadata: an object form"
  | .project _ => .error "project: an object form"
  | .extend _ _ => .error "extend: an object form"
  | .label l => .error s!"label {l}: labels are not in the fragment"
  | .record _ => .error "a record value: not in the fragment"
  | .get _ m => .error s!"get {m}: a field selection the folder did not resolve"
  | .inject l _ => .error s!"inject {l}: sums are not in the fragment"
  | .case _ _ => .error "case: sums are not in the fragment"
  | .perform _ => .error "perform: an activity"
  | .done _ => .error "done: an activity"
  | .split _ _ _ => .error "split: a record destructor, not in the fragment"

/-- Extend a Core4 substitution at index 0. -/
theorem inst_lift (s u : Term) (σ : Nat → Term) :
    instantiate (s.substitute (liftSubstitution σ)) u = s.substitute (cons u σ) := by
  rw [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1; funext i
  cases i with
  | zero => simp [liftSubstitution, single]
  | succ i => simp only [liftSubstitution, cons_succ]; exact shift_one_cancel _ _

/-- The environment invariant: each variable in scope holds a term that reaches the literal its exact
value decodes to. -/
def EnvOk (Γ : List HSort) (η : Nat → Option Nat) (σ : Nat → Term) : Prop :=
  ∀ i s, Γ[i]? = some s → ∃ w, η i = some w ∧ Obend.Core.Term.Steps (σ i) (s.lit w) ∧ s.valid w

theorem EnvOk.cons {Γ : List HSort} {η : Nat → Option Nat} {σ : Nat → Term} (h : EnvOk Γ η σ)
    (s : HSort) (x : Nat) (u : Term) (hu : Obend.Core.Term.Steps u (s.lit x)) (hv : s.valid x) :
    EnvOk (s :: Γ) (cons (some x) η) (cons u σ) := by
  intro i s' hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨x, rfl, hu, hv⟩
  | succ i => simp only [List.getElem?_cons_succ] at hi; exact h i s' hi

/-- **The lowering is sound against Core4's reference reduction**: where the lowered expression
evaluates exactly to `w`, the source term (under any substitution meeting the invariant) reaches the
literal `w` decodes to. -/
theorem toF_sound : ∀ (t : Term) (Γ : List HSort) (f : FExp) (s : HSort), toF Γ t = .ok (f, s) →
    ∀ (η : Nat → Option Nat) (σ : Nat → Term), EnvOk Γ η σ →
    ∀ w, evalE η f = some w → Obend.Core.Term.Steps (t.substitute σ) (s.lit w) ∧ s.valid w
  | .nat v, Γ, f, s, h, η, σ, _, w, hw => by
    simp only [toF] at h
    split at h
    · cases h
      obtain ⟨rfl, -⟩ := ck_some hw
      exact ⟨by simp only [Term.substitute, HSort.lit]; exact .refl _, trivial⟩
    · cases h
  | .boolean b, Γ, f, s, h, η, σ, _, w, hw => by
    simp only [toF, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := ck_some hw
    refine ⟨?_, ?_⟩
    · cases b <;> simp only [Term.substitute, HSort.lit] <;> exact .refl _
    · cases b <;> simp [HSort.valid]
  | .bound i, Γ, f, s, h, η, σ, hσ, w, hw => by
    simp only [toF] at h
    split at h
    · rename_i s' hs
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨u, hu, hst, hv⟩ := hσ i _ hs
      simp only [evalE, hu, Option.bind_some] at hw
      obtain ⟨rfl, -⟩ := ck_some hw
      exact ⟨by simp only [Term.substitute]; exact hst, hv⟩
    · cases h
  | .binary op l r, Γ, f, s, h, η, σ, hσ, w, hw => by
    simp only [toF] at h
    cases hl : toF Γ l with
    | error e => simp [hl] at h
    | ok pl =>
      obtain ⟨fl, sl⟩ := pl
      cases hr : toF Γ r with
      | error e => simp [hl, hr] at h
      | ok pr =>
        obtain ⟨fr, sr⟩ := pr
        simp only [hl, hr] at h
        cases hb : binF op sl sr with
        | none => simp [hb] at h
        | some q =>
          obtain ⟨mk, s'⟩ := q
          simp only [hb, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨x, y, hx, hy, hprim⟩ := binF_sound hb hw
          obtain ⟨sl', vl⟩ := toF_sound l Γ fl sl hl η σ hσ x hx
          obtain ⟨sr', vr⟩ := toF_sound r Γ fr sr hr η σ hσ y hy
          obtain ⟨hp, hv⟩ := hprim vl vr
          refine ⟨?_, hv⟩
          simp only [Term.substitute]
          exact steps_trans (steps_binaryLeft op _ sl')
            (steps_trans (steps_binaryRight op (sl.lit_value x) sr')
              (steps_one (.primitive op _ _ _ (sl.lit_value x) (sr.lit_value y) hp)))
  | .ifZero v z s', Γ, f, s, h, η, σ, hσ, w, hw => by
    simp only [toF] at h
    cases hv : toF Γ v with
    | error e => simp [hv] at h
    | ok pv =>
      obtain ⟨fv, sv⟩ := pv
      cases hz : toF Γ z with
      | error e => cases sv <;> simp [hv, hz] at h
      | ok pz =>
        obtain ⟨fz, sz⟩ := pz
        cases hs : toF (.nat :: Γ) s' with
        | error e => cases sv <;> simp [hv, hz, hs] at h
        | ok ps =>
          obtain ⟨fs, ss⟩ := ps
          cases sv
          · simp only [hv, hz, hs] at h
            split at h
            · rename_i heq
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [evalE] at hw
              cases hk : evalE η fv with
              | none => simp [hk] at hw
              | some k =>
                obtain ⟨sv', -⟩ := toF_sound v Γ fv .nat hv η σ hσ k hk
                simp only [Term.substitute]
                cases k with
                | zero =>
                  simp only [hk] at hw
                  obtain ⟨sz', vz⟩ := toF_sound z Γ fz sz hz η σ hσ w hw
                  exact ⟨steps_trans (steps_ifZero _ _ sv') (.next (.zero _ _) sz'), vz⟩
                | succ k =>
                  simp only [hk] at hw
                  obtain ⟨ss', vs⟩ := toF_sound s' (.nat :: Γ) fs ss hs _ _
                    (hσ.cons .nat k (.nat k) (.refl _) trivial) w hw
                  refine ⟨steps_trans (steps_ifZero _ _ sv') (.next (.successor _ _ _) ?_), heq ▸ vs⟩
                  rw [inst_lift]; exact heq ▸ ss'
            · cases h
          · simp [hv] at h
  | .ifBool c t e, Γ, f, s, h, η, σ, hσ, w, hw => by
    simp only [toF] at h
    cases hc : toF Γ c with
    | error x => simp [hc] at h
    | ok pc =>
      obtain ⟨fc, sc⟩ := pc
      cases ht : toF Γ t with
      | error x => cases sc <;> simp [hc, ht] at h
      | ok pt =>
        obtain ⟨ft, st⟩ := pt
        cases he : toF Γ e with
        | error x => cases sc <;> simp [hc, ht, he] at h
        | ok pe =>
          obtain ⟨fe, se⟩ := pe
          cases sc
          · simp [hc] at h
          · simp only [hc, ht, he] at h
            split at h
            · rename_i heq
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [evalE] at hw
              cases hk : evalE η fc with
              | none => simp [hk] at hw
              | some k =>
                obtain ⟨sc', vc⟩ := toF_sound c Γ fc .bool hc η σ hσ k hk
                simp only [Term.substitute]
                simp only [HSort.valid] at vc
                cases k with
                | zero =>
                  simp only [hk] at hw
                  obtain ⟨se', ve⟩ := toF_sound e Γ fe se he η σ hσ w hw
                  refine ⟨steps_trans (steps_ifBool _ _ sc') (.next (.ifFalse _ _) ?_), heq ▸ ve⟩
                  exact heq ▸ se'
                | succ k =>
                  simp only [hk, evalE_lift0] at hw
                  obtain ⟨st', vt⟩ := toF_sound t Γ ft st ht η σ hσ w hw
                  have : (k + 1 != 0) = true := by simp
                  refine ⟨steps_trans (steps_ifBool _ _ ?_) (.next (.ifTrue _ _) st'), vt⟩
                  simpa [HSort.lit] using sc'
            · cases h
  | .app (.lam b) a, Γ, f, s, h, η, σ, hσ, w, hw => by
    simp only [toF] at h
    cases ha : toF Γ a with
    | error e => simp [ha] at h
    | ok pa =>
      obtain ⟨fa, sa⟩ := pa
      cases hb : toF (sa :: Γ) b with
      | error e => simp [ha, hb] at h
      | ok pb =>
        obtain ⟨fb, sb⟩ := pb
        simp only [ha, hb, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [evalE] at hw
        cases hx : evalE η fa with
        | none => simp [hx] at hw
        | some x =>
          simp only [hx] at hw
          obtain ⟨sa', va⟩ := toF_sound a Γ fa sa ha η σ hσ x hx
          obtain ⟨sb', vb⟩ := toF_sound b (sa :: Γ) fb sb hb _ _ (hσ.cons sa x _ sa' va) w hw
          refine ⟨?_, vb⟩
          simp only [Term.substitute]
          exact .next (.beta _ _) (by rw [inst_lift]; exact sb')
  | .app (.bound _) _, _, _, _, h, _, _, _, _, _ | .app (.app _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.hole _ _) _, _, _, _, h, _, _, _, _, _ | .app (.mix _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.fix _ _) _, _, _, _, h, _, _, _, _, _ | .app (.specification _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.prototype _ _) _, _, _, _, h, _, _, _, _, _ | .app (.reflect _) _, _, _, _, h, _, _, _, _, _
  | .app (.metadata _) _, _, _, _, h, _, _, _, _, _ | .app (.project _) _, _, _, _, h, _, _, _, _, _
  | .app (.nat _) _, _, _, _, h, _, _, _, _, _ | .app (.boolean _) _, _, _, _, h, _, _, _, _, _
  | .app (.label _) _, _, _, _, h, _, _, _, _, _ | .app (.binary _ _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.extend _ _) _, _, _, _, h, _, _, _, _, _ | .app (.record _) _, _, _, _, h, _, _, _, _, _
  | .app (.get _ _) _, _, _, _, h, _, _, _, _, _ | .app (.ifZero _ _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.inject _ _) _, _, _, _, h, _, _, _, _, _ | .app (.case _ _) _, _, _, _, h, _, _, _, _, _
  | .app (.ifBool _ _ _) _, _, _, _, h, _, _, _, _, _ | .app (.perform _) _, _, _, _, h, _, _, _, _, _
  | .app (.done _) _, _, _, _, h, _, _, _, _, _ | .app (.split _ _ _) _, _, _, _, h, _, _, _, _, _
  | .lam _, _, _, _, h, _, _, _, _, _ | .fix _ _, _, _, _, h, _, _, _, _, _
  | .hole _ _, _, _, _, h, _, _, _, _, _ | .mix _ _, _, _, _, h, _, _, _, _, _
  | .specification _ _, _, _, _, h, _, _, _, _, _ | .prototype _ _, _, _, _, h, _, _, _, _, _
  | .reflect _, _, _, _, h, _, _, _, _, _ | .metadata _, _, _, _, h, _, _, _, _, _
  | .project _, _, _, _, h, _, _, _, _, _ | .extend _ _, _, _, _, h, _, _, _, _, _
  | .label _, _, _, _, h, _, _, _, _, _ | .record _, _, _, _, h, _, _, _, _, _
  | .get _ _, _, _, _, h, _, _, _, _, _ | .inject _ _, _, _, _, h, _, _, _, _, _
  | .case _ _, _, _, _, h, _, _, _, _, _ | .perform _, _, _, _, h, _, _, _, _, _
  | .done _, _, _, _, h, _, _, _, _, _ | .split _ _ _, _, _, _, h, _, _, _, _, _ => by
    simp [toF] at h

/-! ## 6. The book, and `lowerBookToHvm_sound` -/

/-- A lowered member: its name, the sort its result decodes at, its expression, and its HVM2 net. -/
structure HvmMember where
  member : String
  sort : HSort
  fexp : FExp
  hdef : HDef

/-- HVM2's names are letters, digits and the characters `_`, `.`, `-` and `/`; the lowering keeps
member names as they are, so it takes those of letters, digits and `_`, and leaves `main` to the entry
point. -/
def nameOk (m : String) : Bool := !m.isEmpty && m != "main" && m.all (fun c => c.isAlphanum || c == '_')

/-- A member's net: `@m = (X r) & …`, the argument handed to its occurrences by `X`, the result
delivered to `r`. -/
def memberDef (name : String) (f : FExp) : HDef :=
  ⟨name, .con (dupTree (occ0 (comp f (.var 0) 1).occ)) (.var 0), (comp f (.var 0) 1).bag⟩

/-- **The lowering of a member**: the code `evalBookAt` folds, `dataPinSpecialize (evalBook B m)`,
when it is `λself. λx. body` and `body` is in the fragment; the refusal, by name, otherwise. -/
def lowerMember (B : Book) (m : String) : Except String HvmMember :=
  if nameOk m then
    match evalBook B m with
    | none => .error s!"{m}: no such member"
    | some c => match dataPinSpecialize c with
      | .lam (.lam body) => match toF [.nat] body with
        | .ok (f, s) =>
          if (comp f (.var 0) 1).occ.all (fun p => p.1 == 0) then .ok ⟨m, s, f, memberDef m f⟩
          else .error s!"{m}: a variable beyond the argument"
        | .error e => .error s!"{m}: {e}"
      | _ => .error s!"{m}: the folded code is not `λself. λx. body` (a static member, or not a method)"
  else .error s!"{m}: a member name outside [A-Za-z0-9_], or `main`"

def lowerAll (B : Book) : List String → Except String (List HvmMember)
  | [] => .ok []
  | m :: ms => match lowerMember B m, lowerAll B ms with
    | .ok d, .ok ds => .ok (d :: ds)
    | .error e, _ => .error e
    | _, .error e => .error e

/-- An HVM2 book lowered from a Leaf book: one net per slot. -/
structure HvmBook where
  members : List HvmMember

def HvmBook.defs (H : HvmBook) : List HDef := H.members.map (·.hdef)

def HvmBook.member? (H : HvmBook) (m : String) : Option HvmMember := H.members.find? (·.member == m)

/-- The lowering of a book, with the first refusal by name. -/
def lowerBookToHvmE (B : Book) : Except String HvmBook :=
  match lowerAll B B.slots with
  | .ok ms => .ok ⟨ms⟩
  | .error e => .error e

/-- **The lowering of a book**: every slot lowered, or `none`. -/
def lowerBookToHvm (B : Book) : Option HvmBook :=
  match lowerBookToHvmE B with
  | .ok H => some H
  | .error _ => none

/-- The first net variable past a member's own. -/
def HvmMember.top (d : HvmMember) : Nat := (comp d.fexp (.var 0) 1).next

/-- `@main = r & @m ~ (#x r)`. -/
def mainDef (d : HvmMember) (x : Nat) : HDef :=
  ⟨"main", .var d.top, [(.ref d.member, .con (.num (.u24 x)) (.var d.top))]⟩

/-- The configuration `hvm run` starts from: `@main`'s net. -/
def mainCfg (d : HvmMember) (x : Nat) : Cfg := ⟨(mainDef d x).root, (mainDef d x).bag⟩

/-- The file `hvm run` reads for member `d` at argument `x`. -/
def emitMain (H : HvmBook) (d : HvmMember) (x : Nat) (p : Plant := .none) : String :=
  emitHvmWith p (mainDef d x :: H.defs)

theorem lowerMember_ok {B : Book} {m : String} {d : HvmMember} (h : lowerMember B m = .ok d) :
    d.member = m ∧ d.hdef = memberDef m d.fexp ∧ (∀ p ∈ (comp d.fexp (.var 0) 1).occ, p.1 = 0) ∧
    ∃ c body, evalBook B m = some c ∧ dataPinSpecialize c = .lam (.lam body) ∧
      toF [.nat] body = .ok (d.fexp, d.sort) := by
  unfold lowerMember at h
  split at h
  · split at h
    · cases h
    · rename_i c hc
      split at h
      · rename_i body hbody
        split at h
        · rename_i f s hf
          split at h
          · rename_i hall
            cases h
            refine ⟨rfl, rfl, ?_, c, body, hc, hbody, hf⟩
            intro p hp
            simpa using List.all_eq_true.1 hall p hp
          · cases h
        · cases h
      · cases h
  · cases h

theorem lowerAll_ok {B : Book} : ∀ {ms : List String} {ds : List HvmMember}, lowerAll B ms = .ok ds →
    ∀ d ∈ ds, lowerMember B d.member = .ok d
  | [], ds, h, d, hd => by simp only [lowerAll, Except.ok.injEq] at h; subst h; cases hd
  | m :: ms, ds, h, d, hd => by
    simp only [lowerAll] at h
    cases h1 : lowerMember B m with
    | error e => simp [h1] at h
    | ok d' =>
      cases h2 : lowerAll B ms with
      | error e => simp [h1, h2] at h
      | ok ds' =>
        simp only [h1, h2, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.1 hd with rfl | hd
        · rw [(lowerMember_ok h1).1]; exact h1
        · exact lowerAll_ok h2 d hd

theorem HTree.rename_id : ∀ t : HTree, t.rename (fun x => x) = t
  | .var _ | .era | .ref _ | .num _ => rfl
  | .con a b | .dup a b | .opr a b | .swi a b => by simp only [HTree.rename, HTree.rename_id a, HTree.rename_id b]

theorem find?_congr {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (by simp)]
    split
    · rfl
    · exact find?_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **The net half**: `@main`'s net reduces, under the model's `Step`, to the number `w` with an
empty bag, where `w` is the expression's wrapping value at `x`. -/
theorem member_net_sound (book : List HDef) (d : HvmMember) (hdef : d.hdef = memberDef d.member d.fexp)
    (hocc : ∀ p ∈ (comp d.fexp (.var 0) 1).occ, p.1 = 0)
    (hb : book.find? (·.name == d.member) = some d.hdef) (x w : Nat)
    (hw : evalW (cons (some x) (fun _ => none)) d.fexp = some w) :
    Steps book (mainCfg d x) ⟨.num (.u24 w), []⟩ := by
  obtain ⟨f1, f2, f3, f4⟩ := comp_facts d.fexp (.var 0) 1
  obtain ⟨i1, i2⟩ := comp_indep d.fexp (.var d.top) (.var 0) 1
  show Steps book ⟨.var d.top, [(.ref d.member, .con (.num (.u24 x)) (.var d.top))]⟩ _
  have IH := comp_reduces book d.fexp (.var d.top) 1 (cons (some x) (fun _ => none))
    (many (occ0 (comp d.fexp (.var 0) 1).occ) (nul (some x))) (.var d.top) [] []
  rw [i1, i2] at IH
  have hsub := comp_subst_K d.fexp (.var 0) 1 (one 0 (.var d.top)) (fun v hv _ => one_none (by omega))
  simp only [HTree.subst, one, ite_true, Option.getD_some] at hsub
  rw [hdef] at hb
  simp only [memberDef] at hb
  unfold HvmMember.top at *
  generalize hM : (comp d.fexp (.var 0) 1).next = M at *
  generalize (comp d.fexp (.var 0) 1).occ = occ at *
  generalize hr : (comp d.fexp (.var 0) 1).bag = rbag at *
  have hos : ∀ o ∈ occ0 occ, 1 ≤ o ∧ o < M := fun o ho => f2 _ (mem_occ0.1 ho)
  -- CALL
  have hcall : Step book ⟨.var M, [(.ref d.member, .con (.num (.u24 x)) (.var M))]⟩
      ⟨.var M, [] ++ ((HTree.con (dupTree (occ0 occ)) (.var 0)).rename (fun v => v),
      .con (.num (.u24 x)) (.var M)) :: rbag.map (Redex.rename (fun v => v)) ++ []⟩ := by
    refine Step.call (root := .var M) (pre := []) (post := []) (d := ⟨d.member, .con (dupTree (occ0 occ)) (.var 0), rbag⟩) (t := .con (.num (.u24 x)) (.var M)) (fun v => v) hb
      ⟨.con, .num (.u24 x), .var M, rfl, by decide⟩
      (fun u _ v _ h => h) ?_
    intro u hu
    simp only [Cfg.vars, HTree.vars, bagVars_cons, bagVars_nil,
      List.nil_append, List.append_nil, List.mem_append, List.mem_singleton, or_self]
    simp only [HDef.vars, HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton] at hu
    intro hu'
    subst hu'
    rcases hu with (hu | hu) | hu
    · have := hos _ hu; omega
    · omega
    · rcases f4 _ hu with h | h
      · omega
      · simp [HTree.vars] at h; omega
  refine Steps.next hcall ?_
  simp only [HTree.rename_id, HTree.rename, List.nil_append, List.append_nil]
  have hmap : rbag.map (Redex.rename (fun v => v)) = rbag := by
    rw [show Redex.rename (fun v => v) = id from by funext r; simp [Redex.rename, HTree.rename_id]]
    simp
  rw [hmap]
  -- ANNI
  refine (sRule [] rbag (a := .con (dupTree (occ0 occ)) (.var 0)) (b := .con (.num (.u24 x)) (.var M))
    (ns := [(dupTree (occ0 occ), .num (.u24 x)), (.var 0, .var M)]) rfl (by simp) rfl).trans ?_
  -- LINK the result variable to `main`'s
  refine (sLink [(dupTree (occ0 occ), .num (.u24 x))] rbag [] 0 (.var M) (by simp [HTree.vars]; omega)
    ?_ (by simp) (by simp) rfl).trans ?_
  · intro h
    simp only [bagVars_cons, dupTree_vars, HTree.vars, bagVars_nil, List.append_nil] at h
    have := hos 0 h; omega
  rw [hsub]
  -- the argument reaches its occurrences
  refine (sSwap [] ((comp d.fexp (.var M) 1).bag ++ []) (a := dupTree (occ0 occ)) (b := .num (.u24 x))
    (by simp) rfl).trans ?_
  refine (sSpread (nul (some x)) (nullary_nul _) (occ0 occ) [] (comp d.fexp (.var M) 1).bag [] (f3.sublist (occ0_sublist _))
    (fun o ho => by have := hos o ho; exact ⟨by simp [HTree.vars]; omega, by simp, by simp⟩) (by simp [nul]) rfl).trans ?_
  -- the body
  refine (steps_eq (by simp)).trans ((IH ?_ ?_ (closedImg_many (nul_vars _)) ?_ ?_).trans ?_)
  · rintro ⟨i, o⟩ hp
    have hi : i = 0 := hocc _ hp
    subst hi
    have ho : o ∈ occ0 occ := mem_occ0.2 hp
    simp [many, ho]
  · intro o _ _ hno
    have : o ∉ occ0 occ := fun h => hno _ (mem_occ0.1 h) rfl
    simp [many, this]
  · have : M ∉ occ0 occ := fun h => by have := hos _ h; omega
    simp [HTree.subst, many, this]
  · intro v hv
    simp only [HTree.vars, bagVars_nil, List.append_nil, List.mem_append, List.mem_singleton, or_self] at hv
    omega
  -- the value reaches `main`'s root
  rw [hw]
  refine (sSwap [] [] (a := nul (some w)) (b := .var M) rfl rfl).trans ?_
  have := Step.link (book := book) (root := .var M) (pre := []) (post := []) (x := M) (t := nul (some w))
  simp only [List.nil_append, List.map_nil, HTree.subst, one, ite_true, Option.getD_some] at this
  exact Steps.single this

/-- The Core4 term `evalBookAt` folds, applied: `dataPinSpecialize (c {} x)`. -/
theorem evalBookAt_eq {B : Book} {m : String} {c : Term} (h : evalBook B m = some c) (x : Term) :
    evalBookAt B m x = some (dataPinSpecialize (.app (.app c (.record [])) x)) := by
  simp [evalBookAt, h]

/-- **The Core4 half**: `evalBookAt B m (.nat x)` halts with the observation the result decodes to. -/
theorem member_core_sound {B : Book} {m : String} {d : HvmMember} (h : lowerMember B m = .ok d)
    (x w : Nat) (hw : evalE (cons (some x) (fun _ => none)) d.fexp = some w) :
    ∃ r, evalBookAt B m (.nat x) = some r ∧ Halts r (d.sort.observe w) := by
  obtain ⟨-, -, -, c, body, hc, hfold, hf⟩ := lowerMember_ok h
  refine ⟨_, evalBookAt_eq hc _, ?_⟩
  rw [← halts_dataPinSpecialize_iff]
  -- the folded code `λself. λx. body` reaches the literal
  have hσ : EnvOk [.nat] (cons (some x) (fun _ => none)) (cons (.nat x) (single (.record []))) := by
    intro i s hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      exact ⟨x, rfl, .refl _, trivial⟩
    | succ i => simp at hi
  obtain ⟨hst, -⟩ := toF_sound body [.nat] d.fexp d.sort hf _ _ hσ w hw
  have run : Obend.Core.Term.Steps (.app (.app (dataPinSpecialize c) (.record [])) (.nat x)) (d.sort.lit w) := by
    rw [hfold]
    refine .next (.application _ (.beta _ _)) ?_
    have e : instantiate (.lam body) (.record []) = .lam (body.substitute (liftSubstitution (single (.record [])))) := by
      rw [instantiate_eq]; simp only [Term.substitute]
    rw [e]
    refine .next (.beta _ _) ?_
    rw [inst_lift]
    exact hst
  have halts' : Halts (.app (.app (dataPinSpecialize c) (.record [])) (.nat x)) (d.sort.observe w) :=
    ⟨_, ⟨run, d.sort.lit_value w⟩, d.sort.observes w⟩
  -- `c ≈b dataPinSpecialize c`, in the context `□ {} x`
  have hsame := (bequiv_dataPinSpecialize c) Term.bound (.app (.app (.bound 0) (.record [])) (.nat x))
  have ctx : ∀ t : Term, instantiate (.app (.app (.bound 0) (.record [])) (.nat x)) (t.substitute Term.bound) =
      .app (.app t (.record [])) (.nat x) := by
    intro t
    rw [substitute_bound]
    simp [instantiate, Term.substitute]
  rw [ctx, ctx] at hsame
  exact (hsame.halts _).2 halts'

/-- **`lowerBookToHvm_sound`.** For a book the lowering accepts, a member `m` it lowered to `d`, and
an argument `x < 2^24` on which the lowered expression's exact evaluation stays below `2^24`
(`evalE … = some w`):

1. the model of HVM2 reduces `@main = r & @m ~ (#x r)` (`mainCfg`), against the lowered book, to the
   normal form `⟨#w, []⟩`: the root is the number `w`, no redex is left;
2. `evalBookAt B m (.nat x)` is a term that halts, under Core4's reference reduction, with the ground
   observation `w` decodes to at the member's sort (`d.sort.observe w`: `w`, or `w ≠ 0` for a
   Boolean member).

So the net's normal form decodes to what `evalBookAt` evaluates to. -/
theorem lowerBookToHvm_sound {B : Book} {H : HvmBook} (hH : lowerBookToHvm B = some H) {m : String}
    {d : HvmMember} (hd : H.member? m = some d) (x : Nat) {w : Nat}
    (hw : evalE (cons (some x) (fun _ => none)) d.fexp = some w) :
    Steps H.defs (mainCfg d x) ⟨.num (.u24 w), []⟩ ∧
    ∃ r, evalBookAt B m (.nat x) = some r ∧ Halts r (d.sort.observe w) := by
  unfold lowerBookToHvm lowerBookToHvmE at hH
  cases hall : lowerAll B B.slots with
  | error e => simp [hall] at hH
  | ok ms =>
    simp only [hall, Option.some.injEq] at hH
    subst hH
    have hmem : d ∈ ms := List.mem_of_find?_eq_some hd
    have hm : d.member = m := by simpa using List.find?_some hd
    have hlow := lowerAll_ok hall d hmem
    obtain ⟨-, hdef, hocc, -⟩ := lowerMember_ok hlow
    have names : ∀ e ∈ ms, e.hdef.name = e.member := fun e he => by
      rw [(lowerMember_ok (lowerAll_ok hall e he)).2.1]; rfl
    have hb : (HvmBook.defs ⟨ms⟩).find? (·.name == d.member) = some d.hdef := by
      simp only [HvmBook.defs, List.find?_map]
      have : ms.find? ((fun e : HDef => e.name == d.member) ∘ (·.hdef)) = ms.find? (·.member == m) := by
        apply find?_congr
        intro e he
        simp [names e he, hm]
      rw [this]
      simp only [HvmBook.member?] at hd
      rw [hd]; rfl
    refine ⟨member_net_sound _ d hdef hocc hb x w (evalE_evalW _ _ _ hw).1, ?_⟩
    rw [← hm]
    exact member_core_sound (hm ▸ hlow) x w hw

/-- When `evalBookAt` is already a literal, it is the literal the net's number decodes to. -/
theorem lowerBookToHvm_sound_literal {B : Book} {H : HvmBook} (hH : lowerBookToHvm B = some H) {m : String}
    {d : HvmMember} (hd : H.member? m = some d) (x : Nat) {w : Nat}
    (hw : evalE (cons (some x) (fun _ => none)) d.fexp = some w) {r : Term}
    (hr : evalBookAt B m (.nat x) = some r) (hlit : Literal r) : r = d.sort.lit w := by
  obtain ⟨-, r', hr', ⟨v, ⟨hs, _⟩, hobs⟩⟩ := lowerBookToHvm_sound hH hd x hw
  rw [hr] at hr'; cases hr'
  have := value_steps_eq hlit.value hs
  subst this
  revert hobs
  cases d.sort <;> intro hobs <;> simp only [HSort.observe] at hobs <;> cases hobs <;> rfl
