module
/-
# Obend.Lower.Inductive — Recursive Algebraic AST Inductives & LCNF Lowering to `Core4`

Implements Stage 1 (`WS 23` / `SILICON-ELABORATOR.md` §3.2) of the Silicon Lean Kernel & Elaborator:

1. **Recursive Algebraic AST Inductives (`KName`, `KLevel`, `KLiteral`, `KExpr`, `KSyntax`)**:
   - Models the core self-hosted Lean 4 kernel (`Lean4Lean`) and elaborator (`Lean.Elab`) AST
     inductives: hierarchical names (`KName`), universe levels (`KLevel`), kernel expressions
     (`KExpr`), and elaborator syntax trees (`KSyntax`).
   - Lowers arbitrary recursive AST values into `Obend.Lower.LExpr` (`nameToLExpr`, `levelToLExpr`,
     `exprToLExpr`, `syntaxToLExpr`) and `Obend.Core.Term.Term` (`lowerName`, `lowerLevel`,
     `lowerExpr`, `lowerSyntax`), with lossless `Core4` decoders (`decodeNameTerm`,
     `decodeLevelTerm`, `decodeExprTerm`, `decodeSyntaxTerm`).

2. **Structural Pattern-Matching & Fuel-Bounded / `recConst` Recursion over Recursive ASTs (`lower_inductive_sound`)**:
   - Lowers constructor pattern-matching (`LExpr.cases`) and recursive AST traversals
     (`LExpr.recConst`) over `KLevel` and `KExpr` into `Core4` (`Term.case`, `Term.split`, `Term.fix`).
   - Proves **`lower_inductive_sound`**:
     * Every lowered `KName`, `KLevel`, `KExpr`, and `KSyntax` is a canonical `Core4` `Value`
       and round-trips identically through its `Core4` decoder, and
     * Multi-step `SSteps` reductions over recursive ASTs (including `recConst` unfolding and
       constructor `cases` elimination) evaluate in `Core4` (`Evaluates`) to the lowered result.

3. **LCNF (Lean Compiler Normal Form) Lowering Bridge (`LCNFCode`, `lcnfToLExpr`, `lowerLCNF`, `lcnf_to_core4_sound`)**:
   - Models the ANF-flattened compiler IR (`LCNFArg`, `LCNFLetValue`, `LCNFAlt`, `LCNFCode`) where
     `.zero`-quantity type and proof parameters are erased (`LCNFArg.erased`), monadic `do`-blocks
     are flattened into `.letDecl` / `.cases` / `.returnArg`, and constructor allocations and
     projections are explicit.
   - Proves **`lcnf_to_core4_sound`**: LCNF programs lower directly through `LExpr` into `Core4`,
     preserving multi-step evaluation (`SSteps` → `Evaluates`) while erasing `.zero`-quantity arguments
     to `box` (`.record []`).
-/
public import Obend.Lower.Fragment
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Proofs.Book
public import Obend.Lower.LCNF
@[expose] public section

namespace Obend.Lower.Inductive
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Lower
open Obend.Lower.LCNF
set_option autoImplicit false

/-! ## 1. Recursive Algebraic AST Datatypes (`KName`, `KLevel`, `KLiteral`, `KExpr`, `KSyntax`) -/

/-- Self-hosted kernel hierarchical name (`Lean.Name`). -/
inductive KName where
  | anonymous
  | str (parent : KName) (s : String)
  | num (parent : KName) (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Construct a simple single-component `KName`. -/
def KName.mkSimple (s : String) : KName := .str .anonymous s

/-- Structural height of a `KName`. -/
def KName.height : KName → Nat
  | .anonymous => 0
  | .str p _   => p.height + 1
  | .num p _   => p.height + 1

/-- Self-hosted kernel universe level (`Lean.Level`). -/
inductive KLevel where
  | zero
  | succ (l : KLevel)
  | max (l1 l2 : KLevel)
  | imax (l1 l2 : KLevel)
  | param (name : KName)
  deriving DecidableEq, Repr, Inhabited

/-- Structural depth of a `KLevel`. -/
def KLevel.depth : KLevel → Nat
  | .zero       => 0
  | .succ l     => l.depth + 1
  | .max l1 l2  => Nat.max l1.depth l2.depth + 1
  | .imax l1 l2 => Nat.max l1.depth l2.depth + 1
  | .param _    => 0

/-- Self-hosted kernel literal (`Lean.Literal`). -/
inductive KLiteral where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- Self-hosted kernel expression (`Lean.Expr` / `Lean4Lean.VExpr`). -/
inductive KExpr where
  | bvar (idx : Nat)
  | fvar (id : Nat)
  | sort (u : KLevel)
  | const (name : KName) (us : List KLevel)
  | app (fn arg : KExpr)
  | lam (dom body : KExpr)
  | forallE (dom body : KExpr)
  | letE (ty val body : KExpr)
  | lit (l : KLiteral)
  | proj (structName : KName) (idx : Nat) (structExpr : KExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Self-hosted elaborator syntax tree (`Lean.Syntax`). -/
inductive KSyntax where
  | missing
  | node (kind : KName) (args : List KSyntax)
  | atom (val : String)
  | ident (val : KName)
  deriving Repr, Inhabited

/-! ## 2. Lowering Recursive AST Datatypes to `LExpr` and `Core4.Term` -/

/-- Embed a `String` into `LExpr` as a 0-field constructor injection carrying `s` as its tag. -/
def stringToLExpr (s : String) : LExpr :=
  .inject s []

/-- Decode a `String` from its lowered `Core4` `Term`. -/
def decodeStringTerm : Term → Option String
  | .inject s (.record []) => some s
  | _ => none

@[simp] theorem decodeStringTerm_lowerT (s : String) :
    decodeStringTerm (lowerT (stringToLExpr s)) = some s := by
  simp [stringToLExpr, lowerT, decodeStringTerm]

/-- Lower a `KName` into `LExpr`. -/
def nameToLExpr : KName → LExpr
  | .anonymous => .inject "anonymous" []
  | .str p s   => .inject "str" [("parent", nameToLExpr p), ("str", stringToLExpr s)]
  | .num p i   => .inject "num" [("parent", nameToLExpr p), ("idx", .lit i)]

/-- Lower a `KName` directly to a `Core4` `Term`. -/
def lowerName (n : KName) : Term := lowerT (nameToLExpr n)

/-- Decode a `KName` from a lowered `Core4` `Term`. -/
def decodeNameTerm : Term → Option KName
  | .inject "anonymous" (.record []) => some .anonymous
  | .inject "str" (.record [("parent", p), ("str", .inject s (.record []))]) => do
    let parent ← decodeNameTerm p
    pure (.str parent s)
  | .inject "num" (.record [("parent", p), ("idx", .nat i)]) => do
    let parent ← decodeNameTerm p
    pure (.num parent i)
  | _ => none

theorem decodeNameTerm_lowerT : ∀ (n : KName),
    decodeNameTerm (lowerT (nameToLExpr n)) = some n
  | .anonymous => by
    simp [nameToLExpr, lowerT, decodeNameTerm]
  | .str p s => by
    simp [nameToLExpr, stringToLExpr, lowerT, decodeNameTerm, decodeNameTerm_lowerT p]
  | .num p i => by
    simp [nameToLExpr, lowerT, decodeNameTerm, decodeNameTerm_lowerT p]

theorem canonical_nameToLExpr (n : KName) : Canonical (nameToLExpr n) := by
  cases n <;> exact .inject _ _

/-- Lower a `KLevel` into `LExpr`. -/
def levelToLExpr : KLevel → LExpr
  | .zero       => .inject "zero" []
  | .succ l     => .inject "succ" [("pred", levelToLExpr l)]
  | .max l1 l2  => .inject "max" [("lhs", levelToLExpr l1), ("rhs", levelToLExpr l2)]
  | .imax l1 l2 => .inject "imax" [("lhs", levelToLExpr l1), ("rhs", levelToLExpr l2)]
  | .param n    => .inject "param" [("name", nameToLExpr n)]

/-- Lower a `KLevel` directly to a `Core4` `Term`. -/
def lowerLevel (l : KLevel) : Term := lowerT (levelToLExpr l)

/-- Decode a `KLevel` from a lowered `Core4` `Term`. -/
def decodeLevelTerm : Term → Option KLevel
  | .inject "zero" (.record []) => some .zero
  | .inject "succ" (.record [("pred", l)]) => do
    return .succ (← decodeLevelTerm l)
  | .inject "max" (.record [("lhs", l1), ("rhs", l2)]) => do
    return .max (← decodeLevelTerm l1) (← decodeLevelTerm l2)
  | .inject "imax" (.record [("lhs", l1), ("rhs", l2)]) => do
    return .imax (← decodeLevelTerm l1) (← decodeLevelTerm l2)
  | .inject "param" (.record [("name", n)]) => do
    return .param (← decodeNameTerm n)
  | _ => none

theorem decodeLevelTerm_lowerT : ∀ (l : KLevel),
    decodeLevelTerm (lowerT (levelToLExpr l)) = some l
  | .zero => by
    simp [levelToLExpr, lowerT, decodeLevelTerm]
  | .succ l => by
    simp [levelToLExpr, lowerT, decodeLevelTerm, decodeLevelTerm_lowerT l]
  | .max l1 l2 => by
    simp [levelToLExpr, lowerT, decodeLevelTerm, decodeLevelTerm_lowerT l1, decodeLevelTerm_lowerT l2]
  | .imax l1 l2 => by
    simp [levelToLExpr, lowerT, decodeLevelTerm, decodeLevelTerm_lowerT l1, decodeLevelTerm_lowerT l2]
  | .param n => by
    simp [levelToLExpr, lowerT, decodeLevelTerm, decodeNameTerm_lowerT n]

theorem canonical_levelToLExpr (l : KLevel) : Canonical (levelToLExpr l) := by
  cases l <;> exact .inject _ _

/-- Lower a `List KLevel` into `LExpr`. -/
def levelListToLExpr : List KLevel → LExpr
  | []      => .inject "nil" []
  | u :: us => .inject "cons" [("head", levelToLExpr u), ("tail", levelListToLExpr us)]

/-- Decode a `List KLevel` from a `Core4` `Term`. -/
def decodeLevelListTerm : Term → Option (List KLevel)
  | .inject "nil" (.record []) => some []
  | .inject "cons" (.record [("head", h), ("tail", t)]) => do
    return (← decodeLevelTerm h) :: (← decodeLevelListTerm t)
  | _ => none

theorem decodeLevelListTerm_lowerT : ∀ (us : List KLevel),
    decodeLevelListTerm (lowerT (levelListToLExpr us)) = some us
  | [] => by
    simp [levelListToLExpr, lowerT, decodeLevelListTerm]
  | u :: us => by
    simp [levelListToLExpr, lowerT, decodeLevelListTerm, decodeLevelTerm_lowerT u,
      decodeLevelListTerm_lowerT us]

/-- Lower a `KLiteral` into `LExpr`. -/
def literalToLExpr : KLiteral → LExpr
  | .natVal n => .inject "natVal" [("val", .lit n)]
  | .strVal s => .inject "strVal" [("val", stringToLExpr s)]

/-- Decode a `KLiteral` from a `Core4` `Term`. -/
def decodeLiteralTerm : Term → Option KLiteral
  | .inject "natVal" (.record [("val", .nat n)]) => some (.natVal n)
  | .inject "strVal" (.record [("val", .inject s (.record []))]) => some (.strVal s)
  | _ => none

theorem decodeLiteralTerm_lowerT : ∀ (lit : KLiteral),
    decodeLiteralTerm (lowerT (literalToLExpr lit)) = some lit
  | .natVal _ => by
    simp [literalToLExpr, lowerT, decodeLiteralTerm]
  | .strVal _ => by
    simp [literalToLExpr, stringToLExpr, lowerT, decodeLiteralTerm]

/-- Lower a recursive `KExpr` AST into `LExpr`. -/
def exprToLExpr : KExpr → LExpr
  | .bvar i        => .inject "bvar" [("idx", .lit i)]
  | .fvar id       => .inject "fvar" [("id", .lit id)]
  | .sort u        => .inject "sort" [("u", levelToLExpr u)]
  | .const n us    => .inject "const" [("name", nameToLExpr n), ("us", levelListToLExpr us)]
  | .app f a       => .inject "app" [("fn", exprToLExpr f), ("arg", exprToLExpr a)]
  | .lam d b       => .inject "lam" [("dom", exprToLExpr d), ("body", exprToLExpr b)]
  | .forallE d b   => .inject "forallE" [("dom", exprToLExpr d), ("body", exprToLExpr b)]
  | .letE t v b    => .inject "letE" [("ty", exprToLExpr t), ("val", exprToLExpr v), ("body", exprToLExpr b)]
  | .lit l         => .inject "lit" [("lit", literalToLExpr l)]
  | .proj s idx e  => .inject "proj" [("struct", nameToLExpr s), ("idx", .lit idx), ("expr", exprToLExpr e)]

/-- Lower a `KExpr` directly to a `Core4` `Term`. -/
def lowerExpr (e : KExpr) : Term := lowerT (exprToLExpr e)

/-- Decode a `KExpr` from a lowered `Core4` `Term`. -/
def decodeExprTerm : Term → Option KExpr
  | .inject "bvar" (.record [("idx", .nat i)]) => some (.bvar i)
  | .inject "fvar" (.record [("id", .nat id)]) => some (.fvar id)
  | .inject "sort" (.record [("u", u)]) => do
    return .sort (← decodeLevelTerm u)
  | .inject "const" (.record [("name", n), ("us", us)]) => do
    return .const (← decodeNameTerm n) (← decodeLevelListTerm us)
  | .inject "app" (.record [("fn", f), ("arg", a)]) => do
    return .app (← decodeExprTerm f) (← decodeExprTerm a)
  | .inject "lam" (.record [("dom", d), ("body", b)]) => do
    return .lam (← decodeExprTerm d) (← decodeExprTerm b)
  | .inject "forallE" (.record [("dom", d), ("body", b)]) => do
    return .forallE (← decodeExprTerm d) (← decodeExprTerm b)
  | .inject "letE" (.record [("ty", t), ("val", v), ("body", b)]) => do
    return .letE (← decodeExprTerm t) (← decodeExprTerm v) (← decodeExprTerm b)
  | .inject "lit" (.record [("lit", l)]) => do
    return .lit (← decodeLiteralTerm l)
  | .inject "proj" (.record [("struct", s), ("idx", .nat idx), ("expr", e)]) => do
    return .proj (← decodeNameTerm s) idx (← decodeExprTerm e)
  | _ => none

theorem decodeExprTerm_lowerT : ∀ (e : KExpr),
    decodeExprTerm (lowerT (exprToLExpr e)) = some e
  | .bvar _ => by
    simp [exprToLExpr, lowerT, decodeExprTerm]
  | .fvar _ => by
    simp [exprToLExpr, lowerT, decodeExprTerm]
  | .sort u => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeLevelTerm_lowerT u]
  | .const n us => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeNameTerm_lowerT n, decodeLevelListTerm_lowerT us]
  | .app f a => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeExprTerm_lowerT f, decodeExprTerm_lowerT a]
  | .lam d b => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeExprTerm_lowerT d, decodeExprTerm_lowerT b]
  | .forallE d b => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeExprTerm_lowerT d, decodeExprTerm_lowerT b]
  | .letE t v b => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeExprTerm_lowerT t, decodeExprTerm_lowerT v,
      decodeExprTerm_lowerT b]
  | .lit l => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeLiteralTerm_lowerT l]
  | .proj s idx e => by
    simp [exprToLExpr, lowerT, decodeExprTerm, decodeNameTerm_lowerT s, decodeExprTerm_lowerT e]

theorem canonical_exprToLExpr (e : KExpr) : Canonical (exprToLExpr e) := by
  cases e <;> exact .inject _ _

mutual
/-- Lower a `KSyntax` tree into `LExpr`. -/
def syntaxToLExpr : KSyntax → LExpr
  | .missing    => .inject "missing" []
  | .node k as  => .inject "node" [("kind", nameToLExpr k), ("args", syntaxListToLExpr as)]
  | .atom v     => .inject "atom" [("val", stringToLExpr v)]
  | .ident n    => .inject "ident" [("name", nameToLExpr n)]

/-- Lower a `List KSyntax` into `LExpr`. -/
def syntaxListToLExpr : List KSyntax → LExpr
  | []      => .inject "nil" []
  | s :: ss => .inject "cons" [("head", syntaxToLExpr s), ("tail", syntaxListToLExpr ss)]
end

/-- Lower a `KSyntax` directly to a `Core4` `Term`. -/
def lowerSyntax (s : KSyntax) : Term := lowerT (syntaxToLExpr s)

mutual
/-- Decode a `KSyntax` from a lowered `Core4` `Term`. -/
def decodeSyntaxTerm : Term → Option KSyntax
  | .inject "missing" (.record []) => some .missing
  | .inject "node" (.record [("kind", k), ("args", as)]) => do
    return .node (← decodeNameTerm k) (← decodeSyntaxListTerm as)
  | .inject "atom" (.record [("val", .inject v (.record []))]) => some (.atom v)
  | .inject "ident" (.record [("name", n)]) => do
    return .ident (← decodeNameTerm n)
  | _ => none

/-- Decode a `List KSyntax` from a lowered `Core4` `Term`. -/
def decodeSyntaxListTerm : Term → Option (List KSyntax)
  | .inject "nil" (.record []) => some []
  | .inject "cons" (.record [("head", h), ("tail", t)]) => do
    return (← decodeSyntaxTerm h) :: (← decodeSyntaxListTerm t)
  | _ => none
end

mutual
theorem decodeSyntaxTerm_lowerT : ∀ (s : KSyntax),
    decodeSyntaxTerm (lowerT (syntaxToLExpr s)) = some s
  | .missing => by
    simp [syntaxToLExpr, lowerT, decodeSyntaxTerm]
  | .node k as => by
    simp [syntaxToLExpr, lowerT, decodeSyntaxTerm, decodeNameTerm_lowerT k,
      decodeSyntaxListTerm_lowerT as]
  | .atom _ => by
    simp [syntaxToLExpr, stringToLExpr, lowerT, decodeSyntaxTerm]
  | .ident n => by
    simp [syntaxToLExpr, lowerT, decodeSyntaxTerm, decodeNameTerm_lowerT n]

theorem decodeSyntaxListTerm_lowerT : ∀ (ss : List KSyntax),
    decodeSyntaxListTerm (lowerT (syntaxListToLExpr ss)) = some ss
  | [] => by
    simp [syntaxListToLExpr, lowerT, decodeSyntaxListTerm]
  | s :: ss => by
    simp [syntaxListToLExpr, lowerT, decodeSyntaxListTerm, decodeSyntaxTerm_lowerT s,
      decodeSyntaxListTerm_lowerT ss]
end

theorem canonical_syntaxToLExpr (s : KSyntax) : Canonical (syntaxToLExpr s) := by
  cases s <;> exact .inject _ _

/-! ## 2b. Lowering `Obend.Core.Term` (`Primitive`, `Term`) as a Recursive AST Datatype & `Lean.*` Bridges -/

/-- Convert a host `Lean.Name` into `KName`. -/
def fromLeanName : Lean.Name → KName
  | .anonymous => .anonymous
  | .str p s   => .str (fromLeanName p) s
  | .num p i   => .num (fromLeanName p) i

/-- Convert a `KName` back to a host `Lean.Name`. -/
def toLeanName : KName → Lean.Name
  | .anonymous => .anonymous
  | .str p s   => Lean.Name.mkStr (toLeanName p) s
  | .num p i   => Lean.Name.mkNum (toLeanName p) i

@[simp] theorem fromLeanName_toLeanName : ∀ (n : KName), fromLeanName (toLeanName n) = n
  | .anonymous => rfl
  | .str p s   => by simp [toLeanName, fromLeanName, fromLeanName_toLeanName p]
  | .num p i   => by simp [toLeanName, fromLeanName, fromLeanName_toLeanName p]

/-- Helper for `KName.toCleanId` preserving `.num` indices for `Lean.FVarId` / `Lean.MVarId` names
such as `_uniq.42` while hashing string components. -/
def KName.toCleanIdAux : KName → Nat
  | .anonymous => 0
  | .num .anonymous i => i
  | .num (.str .anonymous "_uniq") i => i
  | .num p i => p.toCleanIdAux * 31 + i + 1
  | .str p s =>
    let hStr := s.toList.foldl (fun acc c => (acc * 131 + c.toNat) % 999983) 0
    p.toCleanIdAux * 31 + hStr + 1

/-- Extract a clean numeric identifier `< 1000000` from a `KName`. -/
def KName.toCleanId (n : KName) : Nat :=
  n.toCleanIdAux % 1000000

theorem KName.toCleanId_lt_offset (n : KName) : n.toCleanId < 1000000 := by
  unfold KName.toCleanId
  omega

/-- Convert a `KLevel` back to a host `Lean.Level`. -/
def toLeanLevel : KLevel → Lean.Level
  | .zero       => .zero
  | .succ l     => .succ (toLeanLevel l)
  | .max l1 l2  => .max (toLeanLevel l1) (toLeanLevel l2)
  | .imax l1 l2 => .imax (toLeanLevel l1) (toLeanLevel l2)
  | .param n    => .param (toLeanName n)

/-- Convert a host `Lean.Level` into `Option KLevel` (handling `.zero`, `.succ`, `.max`, `.imax`, `.param`, and `.mvar`). -/
def fromLeanLevel : Lean.Level → Option KLevel
  | .zero       => some .zero
  | .succ l     => do return .succ (← fromLeanLevel l)
  | .max l1 l2  => do return .max (← fromLeanLevel l1) (← fromLeanLevel l2)
  | .imax l1 l2 => do return .imax (← fromLeanLevel l1) (← fromLeanLevel l2)
  | .param n    => some (.param (fromLeanName n))
  | .mvar id    => some (.param (.str (fromLeanName id.name) "_lmvar"))

@[simp] theorem fromLeanLevel_toLeanLevel : ∀ (l : KLevel), fromLeanLevel (toLeanLevel l) = some l
  | .zero       => rfl
  | .succ l     => by simp [toLeanLevel, fromLeanLevel, fromLeanLevel_toLeanLevel l]
  | .max l1 l2  => by simp [toLeanLevel, fromLeanLevel, fromLeanLevel_toLeanLevel l1, fromLeanLevel_toLeanLevel l2]
  | .imax l1 l2 => by simp [toLeanLevel, fromLeanLevel, fromLeanLevel_toLeanLevel l1, fromLeanLevel_toLeanLevel l2]
  | .param n    => by simp [toLeanLevel, fromLeanLevel, fromLeanName_toLeanName n]

/-- Convert a host `Lean.Literal` into `KLiteral`. -/
def fromLeanLiteral : Lean.Literal → KLiteral
  | .natVal n => .natVal n
  | .strVal s => .strVal s

/-- Convert a `KLiteral` back to a host `Lean.Literal`. -/
def toLeanLiteral : KLiteral → Lean.Literal
  | .natVal n => .natVal n
  | .strVal s => .strVal s

@[simp] theorem fromLeanLiteral_toLeanLiteral (l : KLiteral) :
    fromLeanLiteral (toLeanLiteral l) = l := by
  cases l <;> rfl

/-- Convert a host `Lean.Expr` into `Option KExpr` (stripping `.mdata` annotations transparently
and mapping `.fvar` to `< 1000000` and `.mvar` to `1000000 + id` matching `mvarIdOffset` / `hwCamMVarOffset`). -/
def fromLeanExpr : Lean.Expr → Option KExpr
  | .bvar i          => some (.bvar i)
  | .fvar id         => some (.fvar (fromLeanName id.name).toCleanId)
  | .mvar id         => some (.fvar (1000000 + (fromLeanName id.name).toCleanId))
  | .sort u          => do return .sort (← fromLeanLevel u)
  | .const n us      => do return .const (fromLeanName n) (← us.mapM fromLeanLevel)
  | .app f a         => do return .app (← fromLeanExpr f) (← fromLeanExpr a)
  | .lam _ d b _     => do return .lam (← fromLeanExpr d) (← fromLeanExpr b)
  | .forallE _ d b _ => do return .forallE (← fromLeanExpr d) (← fromLeanExpr b)
  | .letE _ t v b _  => do return .letE (← fromLeanExpr t) (← fromLeanExpr v) (← fromLeanExpr b)
  | .lit l           => some (.lit (fromLeanLiteral l))
  | .mdata _ e       => fromLeanExpr e
  | .proj s i e      => do return .proj (fromLeanName s) i (← fromLeanExpr e)

@[simp] theorem fromLeanExpr_mdata (md : Lean.MData) (e : Lean.Expr) :
    fromLeanExpr (.mdata md e) = fromLeanExpr e := rfl

/-- Convert a `KExpr` back to a host `Lean.Expr` (mapping `.fvar id` with `id >= 1000000` to `.mvar`
and `id < 1000000` to `.fvar`). -/
def toLeanExpr : KExpr → Lean.Expr
  | .bvar i      => .bvar i
  | .fvar id     =>
    if id >= 1000000 then
      .mvar ⟨Lean.Name.mkNum .anonymous (id - 1000000)⟩
    else
      .fvar ⟨Lean.Name.mkNum .anonymous id⟩
  | .sort u      => .sort (toLeanLevel u)
  | .const n us  => .const (toLeanName n) (us.map toLeanLevel)
  | .app f a     => .app (toLeanExpr f) (toLeanExpr a)
  | .lam d b     => .lam (.str .anonymous "x") (toLeanExpr d) (toLeanExpr b) .default
  | .forallE d b => .forallE (.str .anonymous "x") (toLeanExpr d) (toLeanExpr b) .default
  | .letE t v b  => .letE (.str .anonymous "x") (toLeanExpr t) (toLeanExpr v) (toLeanExpr b) false
  | .lit l       => .lit (toLeanLiteral l)
  | .proj s i e  => .proj (toLeanName s) i (toLeanExpr e)

/-- Well-formed variable ID bound (`< 2000000`: `< 1000000` for `.fvar` and `1000000..1999999` for `.mvar`). -/
def KExpr.validVarIds : KExpr → Bool
  | .bvar _      => true
  | .fvar id     => decide (id < 2000000)
  | .sort _      => true
  | .const _ _   => true
  | .app f a     => f.validVarIds && a.validVarIds
  | .lam d b     => d.validVarIds && b.validVarIds
  | .forallE d b => d.validVarIds && b.validVarIds
  | .letE t v b  => t.validVarIds && v.validVarIds && b.validVarIds
  | .lit _       => true
  | .proj _ _ e  => e.validVarIds

theorem mapM_fromLeanLevel_toLeanLevel :
    ∀ (us : List KLevel), (us.map toLeanLevel).mapM fromLeanLevel = some us
  | []      => rfl
  | u :: us => by
    simp [fromLeanLevel_toLeanLevel, mapM_fromLeanLevel_toLeanLevel us]

theorem fromLeanExpr_toLeanExpr :
    ∀ (e : KExpr), e.validVarIds = true → fromLeanExpr (toLeanExpr e) = some e
  | .bvar _, _ => rfl
  | .fvar id, h => by
    simp only [KExpr.validVarIds, decide_eq_true_eq] at h
    unfold toLeanExpr
    by_cases hGe : id >= 1000000
    · simp only [hGe, ↓reduceIte, fromLeanExpr, Lean.Name.mkNum, fromLeanName,
        KName.toCleanId, KName.toCleanIdAux]
      have hMod : (id - 1000000) % 1000000 = id - 1000000 := by omega
      have hAdd : 1000000 + (id - 1000000) = id := by omega
      rw [hMod, hAdd]
    · simp only [hGe, ↓reduceIte, fromLeanExpr, Lean.Name.mkNum, fromLeanName,
        KName.toCleanId, KName.toCleanIdAux]
      have hMod : id % 1000000 = id := by omega
      rw [hMod]
  | .sort u, _ => by simp [toLeanExpr, fromLeanExpr, fromLeanLevel_toLeanLevel]
  | .const n us, _ => by
    unfold toLeanExpr fromLeanExpr
    rw [fromLeanName_toLeanName, mapM_fromLeanLevel_toLeanLevel]
    rfl
  | .app f a, h => by
    simp only [KExpr.validVarIds, Bool.and_eq_true] at h
    simp [toLeanExpr, fromLeanExpr, fromLeanExpr_toLeanExpr f h.1, fromLeanExpr_toLeanExpr a h.2]
  | .lam d b, h => by
    simp only [KExpr.validVarIds, Bool.and_eq_true] at h
    simp [toLeanExpr, fromLeanExpr, fromLeanExpr_toLeanExpr d h.1, fromLeanExpr_toLeanExpr b h.2]
  | .forallE d b, h => by
    simp only [KExpr.validVarIds, Bool.and_eq_true] at h
    simp [toLeanExpr, fromLeanExpr, fromLeanExpr_toLeanExpr d h.1, fromLeanExpr_toLeanExpr b h.2]
  | .letE t v b, h => by
    simp only [KExpr.validVarIds, Bool.and_eq_true] at h
    simp [toLeanExpr, fromLeanExpr, fromLeanExpr_toLeanExpr t h.1.1,
      fromLeanExpr_toLeanExpr v h.1.2, fromLeanExpr_toLeanExpr b h.2]
  | .lit l, _ => by simp [toLeanExpr, fromLeanExpr]
  | .proj s i e, h => by
    simp only [KExpr.validVarIds] at h
    simp [toLeanExpr, fromLeanExpr, fromLeanName_toLeanName, fromLeanExpr_toLeanExpr e h]

/-- Lower an `Obend.Core.Term.Primitive` into `LExpr`. -/
def primToLExpr : Primitive → LExpr
  | .add         => .inject "add" []
  | .multiply    => .inject "multiply" []
  | .equal       => .inject "equal" []
  | .conjunction => .inject "conjunction" []
  | .labelEqual  => .inject "labelEqual" []
  | .subtract    => .inject "subtract" []
  | .divide      => .inject "divide" []
  | .less        => .inject "less" []
  | .lessEqual   => .inject "lessEqual" []
  | .modulo      => .inject "modulo" []
  | .bitAnd      => .inject "bitAnd" []
  | .bitOr       => .inject "bitOr" []
  | .bitXor      => .inject "bitXor" []
  | .shl         => .inject "shl" []
  | .lshr        => .inject "lshr" []
  | .ashr        => .inject "ashr" []
  | .slt         => .inject "slt" []
  | .qmul32      => .inject "qmul32" []

/-- Decode an `Obend.Core.Term.Primitive` from its lowered `Core4` `Term`. -/
def decodePrimTerm : Term → Option Primitive
  | .inject "add" (.record [])         => some .add
  | .inject "multiply" (.record [])    => some .multiply
  | .inject "equal" (.record [])       => some .equal
  | .inject "conjunction" (.record []) => some .conjunction
  | .inject "labelEqual" (.record [])  => some .labelEqual
  | .inject "subtract" (.record [])    => some .subtract
  | .inject "divide" (.record [])      => some .divide
  | .inject "less" (.record [])        => some .less
  | .inject "lessEqual" (.record [])   => some .lessEqual
  | .inject "modulo" (.record [])      => some .modulo
  | .inject "bitAnd" (.record [])      => some .bitAnd
  | .inject "bitOr" (.record [])       => some .bitOr
  | .inject "bitXor" (.record [])      => some .bitXor
  | .inject "shl" (.record [])         => some .shl
  | .inject "lshr" (.record [])        => some .lshr
  | .inject "ashr" (.record [])        => some .ashr
  | .inject "slt" (.record [])         => some .slt
  | .inject "qmul32" (.record [])      => some .qmul32
  | _                                  => none

@[simp] theorem decodePrimTerm_lowerT (p : Primitive) :
    decodePrimTerm (lowerT (primToLExpr p)) = some p := by
  cases p <;> simp [primToLExpr, lowerT, decodePrimTerm]

/-- Lower a `List String` into `LExpr`. -/
def stringListToLExpr : List String → LExpr
  | []      => .inject "nil" []
  | s :: ss => .inject "cons" [("head", stringToLExpr s), ("tail", stringListToLExpr ss)]

/-- Decode a `List String` from its lowered `Core4` `Term`. -/
def decodeStringListTerm : Term → Option (List String)
  | .inject "nil" (.record []) => some []
  | .inject "cons" (.record [("head", h), ("tail", t)]) => do
    return (← decodeStringTerm h) :: (← decodeStringListTerm t)
  | _ => none

@[simp] theorem decodeStringListTerm_lowerT : ∀ (ss : List String),
    decodeStringListTerm (lowerT (stringListToLExpr ss)) = some ss
  | []      => by simp [stringListToLExpr, lowerT, decodeStringListTerm]
  | s :: ss => by
    simp [stringListToLExpr, lowerT, decodeStringListTerm, decodeStringListTerm_lowerT ss]

mutual
/-- Lower an `Obend.Core.Term.Term` AST into `LExpr` (enabling self-lowering of `Core4` metaprograms
and specializers). Each constructor is tagged with a 2-bit group `(g1, g0 : Bool)` and local index
`k ∈ 0..6` so pattern-matching in `decodeCoreTerm` has unary `Nat` depth at most 6. -/
def coreTermToLExpr : Term → LExpr
  -- Group (false, false): 0..6
  | .hole n σ          => .inject "hole" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 0), ("n", .lit n), ("subst", coreTermListToLExpr σ)]
  | .bound i           => .inject "bound" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 1), ("idx", .lit i)]
  | .lam b             => .inject "lam" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 2), ("body", coreTermToLExpr b)]
  | .app f a           => .inject "app" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 3), ("fn", coreTermToLExpr f), ("arg", coreTermToLExpr a)]
  | .mix l u           => .inject "mix" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 4), ("lhs", coreTermToLExpr l), ("rhs", coreTermToLExpr u)]
  | .fix s i           => .inject "fix" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 5), ("spec", coreTermToLExpr s), ("init", coreTermToLExpr i)]
  | .specification m e => .inject "specification" [("g1", .boolLit false), ("g0", .boolLit false), ("k", .lit 6), ("meta", coreTermToLExpr m), ("ext", coreTermToLExpr e)]
  -- Group (false, true): 0..5
  | .prototype s g     => .inject "prototype" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 0), ("spec", coreTermToLExpr s), ("tgt", coreTermToLExpr g)]
  | .reflect p         => .inject "reflect" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 1), ("proto", coreTermToLExpr p)]
  | .metadata p        => .inject "metadata" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 2), ("spec", coreTermToLExpr p)]
  | .project p         => .inject "project" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 3), ("proto", coreTermToLExpr p)]
  | .nat n             => .inject "nat" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 4), ("val", .lit n)]
  | .boolean b         => .inject "boolean" [("g1", .boolLit false), ("g0", .boolLit true), ("k", .lit 5), ("val", .boolLit b)]
  -- Group (true, false): 0..5
  | .label l           => .inject "label" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 0), ("val", stringToLExpr l)]
  | .binary op l r     => .inject "binary" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 1), ("op", primToLExpr op), ("lhs", coreTermToLExpr l), ("rhs", coreTermToLExpr r)]
  | .extend i fs       => .inject "extend" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 2), ("init", coreTermToLExpr i), ("fields", coreFieldListToLExpr fs)]
  | .record fs         => .inject "record" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 3), ("fields", coreFieldListToLExpr fs)]
  | .get g p           => .inject "get" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 4), ("tgt", coreTermToLExpr g), ("name", stringToLExpr p)]
  | .ifZero v z s      => .inject "ifZero" [("g1", .boolLit true), ("g0", .boolLit false), ("k", .lit 5), ("val", coreTermToLExpr v), ("zero", coreTermToLExpr z), ("succ", coreTermToLExpr s)]
  -- Group (true, true): 0..5
  | .inject l p        => .inject "inject" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 0), ("label", stringToLExpr l), ("payload", coreTermToLExpr p)]
  | .case sc arms      => .inject "case" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 1), ("scrut", coreTermToLExpr sc), ("arms", coreFieldListToLExpr arms)]
  | .ifBool c t f      => .inject "ifBool" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 2), ("cond", coreTermToLExpr c), ("then", coreTermToLExpr t), ("else", coreTermToLExpr f)]
  | .perform p         => .inject "perform" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 3), ("plan", coreTermToLExpr p)]
  | .done v            => .inject "done" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 4), ("val", coreTermToLExpr v)]
  | .split t ns f      => .inject "split" [("g1", .boolLit true), ("g0", .boolLit true), ("k", .lit 5), ("tgt", coreTermToLExpr t), ("names", stringListToLExpr ns), ("fn", coreTermToLExpr f)]

/-- Lower a `List Term` into `LExpr`. -/
def coreTermListToLExpr : List Term → LExpr
  | []      => .inject "nil" []
  | t :: ts => .inject "cons" [("head", coreTermToLExpr t), ("tail", coreTermListToLExpr ts)]

/-- Lower a `List (String × Term)` into `LExpr`. -/
def coreFieldListToLExpr : List (String × Term) → LExpr
  | []            => .inject "nil" []
  | (k, v) :: fss => .inject "cons" [("key", stringToLExpr k), ("val", coreTermToLExpr v), ("tail", coreFieldListToLExpr fss)]
end

/-- Lower a `Core4` `Term` AST directly into its quoted `Core4` `Term` representation. -/
def lowerCoreTerm (t : Term) : Term := lowerT (coreTermToLExpr t)

mutual
/-- Decode an `Obend.Core.Term.Term` from its lowered `Core4` `Term` representation by dispatching
on the 2-bit constructor group `(g1, g0)` to `decodeCoreGroup00..11`. -/
def decodeCoreTerm : Term → Option Term
  | .inject _ (.record ((_, .boolean false) :: (_, .boolean false) :: rest)) => decodeCoreGroup00 rest
  | .inject _ (.record ((_, .boolean false) :: (_, .boolean true)  :: rest)) => decodeCoreGroup01 rest
  | .inject _ (.record ((_, .boolean true)  :: (_, .boolean false) :: rest)) => decodeCoreGroup10 rest
  | .inject _ (.record ((_, .boolean true)  :: (_, .boolean true)  :: rest)) => decodeCoreGroup11 rest
  | _ => none

def decodeCoreGroup00 : List (String × Term) → Option Term
  | [(_, .nat 0), (_, .nat n), (_, σ)] => do return .hole n (← decodeCoreTermList σ)
  | [(_, .nat 1), (_, .nat i)]         => some (.bound i)
  | [(_, .nat 2), (_, b)]              => do return .lam (← decodeCoreTerm b)
  | [(_, .nat 3), (_, f), (_, a)]      => do return .app (← decodeCoreTerm f) (← decodeCoreTerm a)
  | [(_, .nat 4), (_, l), (_, u)]      => do return .mix (← decodeCoreTerm l) (← decodeCoreTerm u)
  | [(_, .nat 5), (_, s), (_, i)]      => do return .fix (← decodeCoreTerm s) (← decodeCoreTerm i)
  | [(_, .nat 6), (_, m), (_, e)]      => do return .specification (← decodeCoreTerm m) (← decodeCoreTerm e)
  | _ => none

def decodeCoreGroup01 : List (String × Term) → Option Term
  | [(_, .nat 0), (_, s), (_, g)]      => do return .prototype (← decodeCoreTerm s) (← decodeCoreTerm g)
  | [(_, .nat 1), (_, p)]              => do return .reflect (← decodeCoreTerm p)
  | [(_, .nat 2), (_, p)]              => do return .metadata (← decodeCoreTerm p)
  | [(_, .nat 3), (_, p)]              => do return .project (← decodeCoreTerm p)
  | [(_, .nat 4), (_, .nat n)]         => some (.nat n)
  | [(_, .nat 5), (_, .boolean b)]     => some (.boolean b)
  | _ => none

def decodeCoreGroup10 : List (String × Term) → Option Term
  | [(_, .nat 0), (_, l)]              => do return .label (← decodeStringTerm l)
  | [(_, .nat 1), (_, op), (_, l), (_, r)] => do
    return .binary (← decodePrimTerm op) (← decodeCoreTerm l) (← decodeCoreTerm r)
  | [(_, .nat 2), (_, i), (_, fs)]     => do return .extend (← decodeCoreTerm i) (← decodeCoreFieldList fs)
  | [(_, .nat 3), (_, fs)]             => do return .record (← decodeCoreFieldList fs)
  | [(_, .nat 4), (_, g), (_, p)]      => do return .get (← decodeCoreTerm g) (← decodeStringTerm p)
  | [(_, .nat 5), (_, v), (_, z), (_, s)] => do
    return .ifZero (← decodeCoreTerm v) (← decodeCoreTerm z) (← decodeCoreTerm s)
  | _ => none

def decodeCoreGroup11 : List (String × Term) → Option Term
  | [(_, .nat 0), (_, l), (_, p)]      => do return .inject (← decodeStringTerm l) (← decodeCoreTerm p)
  | [(_, .nat 1), (_, sc), (_, arms)]  => do return .case (← decodeCoreTerm sc) (← decodeCoreFieldList arms)
  | [(_, .nat 2), (_, c), (_, t), (_, f)] => do
    return .ifBool (← decodeCoreTerm c) (← decodeCoreTerm t) (← decodeCoreTerm f)
  | [(_, .nat 3), (_, p)]              => do return .perform (← decodeCoreTerm p)
  | [(_, .nat 4), (_, v)]              => do return .done (← decodeCoreTerm v)
  | [(_, .nat 5), (_, t), (_, ns), (_, f)] => do
    return .split (← decodeCoreTerm t) (← decodeStringListTerm ns) (← decodeCoreTerm f)
  | _ => none

/-- Decode a `List Term` from its lowered `Core4` `Term`. -/
def decodeCoreTermList : Term → Option (List Term)
  | .inject _ (.record []) => some []
  | .inject _ (.record [(_, h), (_, t)]) => do
    return (← decodeCoreTerm h) :: (← decodeCoreTermList t)
  | _ => none

/-- Decode a `List (String × Term)` from its lowered `Core4` `Term`. -/
def decodeCoreFieldList : Term → Option (List (String × Term))
  | .inject _ (.record []) => some []
  | .inject _ (.record [(_, k), (_, v), (_, t)]) => do
    return ((← decodeStringTerm k), (← decodeCoreTerm v)) :: (← decodeCoreFieldList t)
  | _ => none
end

@[simp] theorem lowerT_inject (l : String) (fs : List (String × LExpr)) :
    lowerT (.inject l fs) = .inject l (.record (fs.map fun x => (x.1, lowerT x.2))) := by
  simp [lowerT]

@[simp] theorem lowerT_lit (n : Nat) : lowerT (.lit n) = .nat n := by
  simp [lowerT]

@[simp] theorem Term.substitute_nat (σ : Nat → Term) (n : Nat) :
    Term.substitute σ (.nat n) = .nat n := by
  simp [Term.substitute]

@[simp] theorem lowerT_boolLit (b : Bool) : lowerT (.boolLit b) = .boolean b := by
  simp [lowerT]

mutual
theorem decodeCoreTerm_lowerT : ∀ (t : Term),
    decodeCoreTerm (lowerT (coreTermToLExpr t)) = some t
  | .hole n σ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTermList_lowerT σ]
  | .bound _ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00]
  | .lam b => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTerm_lowerT b]
  | .app f a => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTerm_lowerT f, decodeCoreTerm_lowerT a]
  | .mix l u => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTerm_lowerT l, decodeCoreTerm_lowerT u]
  | .fix s i => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTerm_lowerT s, decodeCoreTerm_lowerT i]
  | .specification m e => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup00, decodeCoreTerm_lowerT m, decodeCoreTerm_lowerT e]
  | .prototype s g => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01, decodeCoreTerm_lowerT s, decodeCoreTerm_lowerT g]
  | .reflect p => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01, decodeCoreTerm_lowerT p]
  | .metadata p => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01, decodeCoreTerm_lowerT p]
  | .project p => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01, decodeCoreTerm_lowerT p]
  | .nat _ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01]
  | .boolean _ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup01]
  | .label _ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10]
  | .binary op l r => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10, decodeCoreTerm_lowerT l, decodeCoreTerm_lowerT r]
  | .extend i fs => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10, decodeCoreTerm_lowerT i, decodeCoreFieldList_lowerT fs]
  | .record fs => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10, decodeCoreFieldList_lowerT fs]
  | .get g _ => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10, decodeCoreTerm_lowerT g]
  | .ifZero v z s => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup10, decodeCoreTerm_lowerT v, decodeCoreTerm_lowerT z, decodeCoreTerm_lowerT s]
  | .inject _ p => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT p]
  | .case sc arms => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT sc, decodeCoreFieldList_lowerT arms]
  | .ifBool c t f => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT c, decodeCoreTerm_lowerT t, decodeCoreTerm_lowerT f]
  | .perform p => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT p]
  | .done v => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT v]
  | .split t ns f => by
    simp [coreTermToLExpr, decodeCoreTerm, decodeCoreGroup11, decodeCoreTerm_lowerT t, decodeStringListTerm_lowerT ns, decodeCoreTerm_lowerT f]

theorem decodeCoreTermList_lowerT : ∀ (ts : List Term),
    decodeCoreTermList (lowerT (coreTermListToLExpr ts)) = some ts
  | [] => by
    simp [coreTermListToLExpr, decodeCoreTermList]
  | t :: ts => by
    simp [coreTermListToLExpr, decodeCoreTermList, decodeCoreTerm_lowerT t, decodeCoreTermList_lowerT ts]

theorem decodeCoreFieldList_lowerT : ∀ (fs : List (String × Term)),
    decodeCoreFieldList (lowerT (coreFieldListToLExpr fs)) = some fs
  | [] => by
    simp [coreFieldListToLExpr, decodeCoreFieldList]
  | (_, v) :: fs => by
    simp [coreFieldListToLExpr, decodeCoreFieldList, decodeCoreTerm_lowerT v, decodeCoreFieldList_lowerT fs]
end

theorem canonical_coreTermToLExpr (t : Term) : Canonical (coreTermToLExpr t) := by
  cases t <;> exact .inject _ _

/-! ## 3. Structural Pattern-Matching & Recursive AST Functions in `LExpr` (`lower_inductive_sound`) -/

/-- `LExpr` pattern matcher over `KLevel` deciding whether a universe level is `.zero` (`Prop`). -/
def isZeroLevelLExpr : LExpr :=
  .lam .emptyRow
    (.cases .boolean
      [ ("zero", [], .boolLit true)
      , ("succ", ["pred"], .lam .emptyRow (.boolLit false))
      , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
      , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
      , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
      (.bvar 0))

/-- Body of `levelSuccDepthLExpr` under the recursive self-binder. -/
def levelSuccDepthBody : LExpr :=
  .lam .emptyRow
    (.cases .natural
      [ ("zero", [], .lit 0)
      , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.bvar 2) (.bvar 0))))
      , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
      , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
      , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
      (.bvar 0))

/-- `LExpr` recursive function (`recConst`) over `KLevel` computing the `.succ`-chain depth:
`levelDepth (.zero) = 0`, `levelDepth (.succ l) = levelDepth l + 1`. -/
def levelSuccDepthLExpr : LExpr :=
  .recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody

/-- `LExpr` pattern matcher extracting the constructor tag code (`0..9`) of a lowered `KExpr`. -/
def exprCtorTagLExpr : LExpr :=
  .lam .emptyRow
    (.cases .natural
      [ ("bvar", ["idx"], .lam .natural (.lit 0))
      , ("fvar", ["id"], .lam .natural (.lit 1))
      , ("sort", ["u"], .lam .emptyRow (.lit 2))
      , ("const", ["name", "us"], .lam .emptyRow (.lam .emptyRow (.lit 3)))
      , ("app", ["fn", "arg"], .lam .emptyRow (.lam .emptyRow (.lit 4)))
      , ("lam", ["dom", "body"], .lam .emptyRow (.lam .emptyRow (.lit 5)))
      , ("forallE", ["dom", "body"], .lam .emptyRow (.lam .emptyRow (.lit 6)))
      , ("letE", ["ty", "val", "body"], .lam .emptyRow (.lam .emptyRow (.lam .emptyRow (.lit 7))))
      , ("lit", ["lit"], .lam .emptyRow (.lit 8))
      , ("proj", ["struct", "idx", "expr"], .lam .emptyRow (.lam .natural (.lam .emptyRow (.lit 9)))) ]
      (.bvar 0))

theorem isZeroLevel_runs_zero :
    SSteps (.app isZeroLevelLExpr (levelToLExpr .zero)) (.boolLit true) := by
  unfold isZeroLevelLExpr
  refine .next (.beta .emptyRow _ (levelToLExpr .zero)) ?_
  have hinst :
      (LExpr.cases .boolean
        [ ("zero", [], .boolLit true)
        , ("succ", ["pred"], .lam .emptyRow (.boolLit false))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
        (.bvar 0)).inst (levelToLExpr .zero) =
      .cases .boolean
        [ ("zero", [], .boolLit true)
        , ("succ", ["pred"], .lam .emptyRow (.boolLit false))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
        (.inject "zero" []) := by
    simp [levelToLExpr, LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  exact .next (.casesInject .boolean _ "zero" [] [] (.boolLit true) [] rfl rfl) (.refl _)

theorem isZeroLevel_runs_succ (l : KLevel) :
    SSteps (.app isZeroLevelLExpr (levelToLExpr (.succ l))) (.boolLit false) := by
  unfold isZeroLevelLExpr
  refine .next (.beta .emptyRow _ (levelToLExpr (.succ l))) ?_
  have hinst :
      (LExpr.cases .boolean
        [ ("zero", [], .boolLit true)
        , ("succ", ["pred"], .lam .emptyRow (.boolLit false))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
        (.bvar 0)).inst (levelToLExpr (.succ l)) =
      .cases .boolean
        [ ("zero", [], .boolLit true)
        , ("succ", ["pred"], .lam .emptyRow (.boolLit false))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.boolLit false)))
        , ("param", ["name"], .lam .emptyRow (.boolLit false)) ]
        (.inject "succ" [("pred", levelToLExpr l)]) := by
    simp [levelToLExpr, LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.casesInject .boolean _ "succ" [("pred", levelToLExpr l)] ["pred"]
    (.lam .emptyRow (.boolLit false)) [levelToLExpr l] rfl rfl) ?_
  refine .next (.beta .emptyRow (.boolLit false) (levelToLExpr l)) ?_
  have hinst2 : (LExpr.boolLit false).inst (levelToLExpr l) = .boolLit false := by
    simp [LExpr.inst, LExpr.subst]
  rw [hinst2]
  exact .refl _

theorem ssteps_trans {a b c : LExpr} (h1 : SSteps a b) (h2 : SSteps b c) : SSteps a c := by
  induction h1 with
  | refl => exact h2
  | next s _ ih => exact .next s (ih h2)

theorem ssteps_succArg {a b : LExpr} (h : SSteps a b) : SSteps (.natSucc a) (.natSucc b) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.succArg s) ih

theorem levelSuccDepth_runs_zero :
    SSteps (.app levelSuccDepthLExpr (levelToLExpr .zero)) (.lit 0) := by
  unfold levelSuccDepthLExpr
  refine .next (.appFun _ (.unfold _ _ _)) ?_
  have hinst1 :
      levelSuccDepthBody.inst (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) =
      .lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
          , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
          , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
          , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
          (.bvar 0)) := by
    simp [levelSuccDepthBody, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (levelToLExpr .zero)) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
        (.bvar 0)).inst (levelToLExpr .zero) =
      .cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
        (.inject "zero" []) := by
    simp [levelToLExpr, levelSuccDepthBody, LExpr.inst, LExpr.subst,
      LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  exact .next (.casesInject .natural _ "zero" [] [] (.lit 0) [] rfl rfl) (.refl _)

theorem levelSuccDepth_runs_succ (l : KLevel) {n : Nat}
    (ih : SSteps (.app levelSuccDepthLExpr (levelToLExpr l)) (.lit n)) :
    SSteps (.app levelSuccDepthLExpr (levelToLExpr (.succ l))) (.lit (n + 1)) := by
  unfold levelSuccDepthLExpr at ih ⊢
  refine .next (.appFun _ (.unfold _ _ _)) ?_
  have hinst1 :
      levelSuccDepthBody.inst (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) =
      .lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
          , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
          , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
          , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
          (.bvar 0)) := by
    simp [levelSuccDepthBody, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (levelToLExpr (.succ l))) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
        (.bvar 0)).inst (levelToLExpr (.succ l)) =
      .cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
        , ("max", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("imax", ["lhs", "rhs"], .lam .emptyRow (.lam .emptyRow (.lit 0)))
        , ("param", ["name"], .lam .emptyRow (.lit 0)) ]
        (.inject "succ" [("pred", levelToLExpr l)]) := by
    simp [levelToLExpr, levelSuccDepthBody, LExpr.inst, LExpr.subst,
      LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.casesInject .natural _ "succ" [("pred", levelToLExpr l)] ["pred"]
    (.lam .emptyRow (.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))))
    [levelToLExpr l] rfl rfl) ?_
  refine .next (.beta .emptyRow _ (levelToLExpr l)) ?_
  have hinst3 :
      (LExpr.natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (.bvar 0))).inst (levelToLExpr l) =
      .natSucc (.app (.recConst "levelSuccDepth" (fn .emptyRow .natural) levelSuccDepthBody) (levelToLExpr l)) := by
    simp [levelSuccDepthBody, LExpr.inst, LExpr.subst, LExpr.liftSubst,
      LExpr.single, LExpr.rename]
  rw [hinst3]
  exact ssteps_trans (ssteps_succArg ih) (.next (.succFold n) (.refl _))

theorem levelSuccDepth_runs_two :
    SSteps (.app levelSuccDepthLExpr (levelToLExpr (.succ (.succ .zero)))) (.lit 2) :=
  levelSuccDepth_runs_succ (.succ .zero) (levelSuccDepth_runs_succ .zero levelSuccDepth_runs_zero)

/-- **Theorem (`lower_inductive_sound`)**:
1. Every recursive AST datatype (`KName`, `KLevel`, `KExpr`, `KSyntax`, and `Obend.Core.Term.Term`)
   lowers through `LExpr` into a canonical `Core4` `Value` (`Value (lowerName n)`, `Value (lowerLevel l)`,
   `Value (lowerExpr e)`, `Value (lowerSyntax s)`, `Value (lowerCoreTerm t)`) and round-trips losslessly
   through its `Core4` decoder (`decodeNameTerm`, `decodeLevelTerm`, `decodeExprTerm`, `decodeSyntaxTerm`,
   `decodeCoreTerm`), and
2. Pattern matching (`isZeroLevelLExpr`) and recursive traversal (`levelSuccDepthLExpr` via `recConst`)
   over lowered recursive ASTs preserve multi-step reduction in `Core4` (`Evaluates`). -/
theorem lower_inductive_sound
    (n : KName) (l : KLevel) (e : KExpr) (s : KSyntax) :
    Value (lowerName n) ∧
    Value (lowerLevel l) ∧
    Value (lowerExpr e) ∧
    Value (lowerSyntax s) ∧
    decodeNameTerm (lowerName n) = some n ∧
    decodeLevelTerm (lowerLevel l) = some l ∧
    decodeExprTerm (lowerExpr e) = some e ∧
    decodeSyntaxTerm (lowerSyntax s) = some s ∧
    Evaluates (lowerT (.app isZeroLevelLExpr (levelToLExpr .zero))) (.boolean true) ∧
    Evaluates (lowerT (.app isZeroLevelLExpr (levelToLExpr (.succ l)))) (.boolean false) ∧
    Evaluates (lowerT (.app levelSuccDepthLExpr (levelToLExpr (.succ (.succ .zero))))) (.nat 2) ∧
    (∀ t : Term, Value (lowerCoreTerm t) ∧ decodeCoreTerm (lowerCoreTerm t) = some t) := by
  refine ⟨lower_value (canonical_nameToLExpr n),
          lower_value (canonical_levelToLExpr l),
          lower_value (canonical_exprToLExpr e),
          lower_value (canonical_syntaxToLExpr s),
          decodeNameTerm_lowerT n,
          decodeLevelTerm_lowerT l,
          decodeExprTerm_lowerT e,
          decodeSyntaxTerm_lowerT s,
          ?_, ?_, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_bool isZeroLevel_runs_zero
  · simpa [lowerT] using lower_sound_bool (isZeroLevel_runs_succ l)
  · simpa [lowerT] using lower_sound_nat levelSuccDepth_runs_two
  · intro t
    exact ⟨lower_value (canonical_coreTermToLExpr t), decodeCoreTerm_lowerT t⟩

/-! ## 4. LCNF (Lean Compiler Normal Form) Lowering Bridge (Delegated to `Obend.Lower.LCNF`) -/

export Obend.Lower.LCNF (
  LcnfQuantity LcnfParam LcnfArg LCNFArg LcnfLetValue LCNFLetValue LcnfAlt LcnfCode LCNFCode
  LcnfFunDecl LCNFFunDecl LcnfModule
  eraseZeroQtyArgs evalLcnfArgNat readLinearStore writeLinearStore evalLcnfLetValue evalLcnfCode
  checkLinearLetValue checkLinearStateToken checkLinearArms
  lcnfArgToLExpr lcnfLetValueToLExpr wrapMinorBvars applyLcnfArgs
  compileLcnfToLExpr lcnfToLExpr lcnfArmsToLExpr compileLcnfToCore4 lowerLCNF
  lcnfFunDeclToLExpr lowerLCNFFunDecl compileLcnfToBook compileLcnfFunDeclToBook
  sampleLcnfRecDecl sampleLcnfRecBody sampleLcnfRecDecl_runs_zero
  sampleLcnfAstMatch sampleLcnfAstMatch_runs_42
  sampleLcnfJpCode sampleLcnfJpCode_runs_42 sampleLinearStateCode sampleDuplicatedStateTokCode
  lcnf_zero_erasure_sound lcnf_linear_state_conserved lcnf_elab_pass_to_book_sound
)

theorem lcnf_to_core4_sound :
    lowerLCNF (.returnArg .erased) = box ∧
    (∀ (c : LCNFCode) (n : Nat),
      SSteps (lcnfToLExpr c) (.lit n) → Evaluates (lowerLCNF c) (.nat n)) ∧
    (∀ (c : LCNFCode) (b : Bool),
      SSteps (lcnfToLExpr c) (.boolLit b) → Evaluates (lowerLCNF c) (.boolean b)) ∧
    SSteps (lcnfToLExpr sampleLcnfAstMatch) (.lit 42) ∧
    Evaluates (lowerLCNF sampleLcnfAstMatch) (.nat 42) ∧
    Evaluates (.app (lowerLCNFFunDecl sampleLcnfRecDecl) (.nat 0)) (.nat 42) :=
  Obend.Lower.LCNF.lcnf_to_core4_sound

/-! ## 5. Multi-Constructor & Nested Recursor Lowering (`CtorIotaRule`, `compileMultiCtorIota`, `compileMultiCtorIota_sound`) -/

/-- A constructor minor-premise rule for a multi-constructor inductive recursor (`compileMultiCtorIota`):
* `ctorTag`: constructor tag name (e.g., `"zero"`, `"succ"`, `"none"`, `"some"`, `"nil"`, `"cons"`),
* `fieldNames`: record field names of the constructor injection,
* `minorBody`: minor premise body (wrapped in `wrapMinorBvars fieldNames.length` under the recursive self-binder). -/
structure CtorIotaRule where
  ctorTag    : String
  fieldNames : List String
  minorBody  : LExpr
  deriving Repr, Inhabited

/-- Compile a general multi-constructor inductive recursor (`recName`, `resTy`, `rules`) into
an `LExpr.recConst` eliminator whose body dispatches on the major premise `.bvar 0` via
`LExpr.cases resTy`. -/
def compileMultiCtorIota (recName : String) (resTy : Ty) (rules : List CtorIotaRule) : LExpr :=
  let arms := rules.map fun r => (r.ctorTag, r.fieldNames, wrapMinorBvars r.fieldNames.length r.minorBody)
  .recConst recName (fn .emptyRow resTy) (.lam .emptyRow (.cases resTy arms (.bvar 0)))

/-- Lower a Peano `Nat` into 2-constructor algebraic `LExpr` (`"zero"` / `"succ"`). -/
def peanoNatToLExpr : Nat → LExpr
  | 0     => .inject "zero" []
  | n + 1 => .inject "succ" [("pred", peanoNatToLExpr n)]

/-- Multi-constructor ι-rules for `Nat` (`zero ↦ 0`, `succ pred ↦ succ (self pred)`). -/
def natIotaRules : List CtorIotaRule :=
  [ { ctorTag := "zero", fieldNames := [],       minorBody := .lit 0 }
  , { ctorTag := "succ", fieldNames := ["pred"], minorBody := .natSucc (.app (.bvar 2) (.bvar 0)) } ]

/-- Lowered multi-constructor recursor for `Nat`. -/
def natRecIotaLExpr : LExpr :=
  compileMultiCtorIota "natRecIota" .natural natIotaRules

/-- Lower an `Option Nat` into 2-constructor algebraic `LExpr` (`"none"` / `"some"`). -/
def optionNatToLExpr : Option Nat → LExpr
  | none   => .inject "none" []
  | some v => .inject "some" [("val", .lit v)]

/-- Multi-constructor ι-rules for `Option Nat` (`none ↦ defaultVal`, `some val ↦ val`). -/
def optionIotaRules (defaultVal : Nat) : List CtorIotaRule :=
  [ { ctorTag := "none", fieldNames := [],      minorBody := .lit defaultVal }
  , { ctorTag := "some", fieldNames := ["val"], minorBody := .bvar 0 } ]

/-- Lowered multi-constructor recursor for `Option Nat`. -/
def optionRecIotaLExpr (defaultVal : Nat) : LExpr :=
  compileMultiCtorIota "optionRecIota" .natural (optionIotaRules defaultVal)

/-- Lower a `List Nat` into 2-constructor algebraic `LExpr` (`"nil"` / `"cons"`). -/
def natListToLExpr : List Nat → LExpr
  | []      => .inject "nil" []
  | x :: xs => .inject "cons" [("head", .lit x), ("tail", natListToLExpr xs)]

/-- Multi-constructor ι-rules for `List Nat` length (`nil ↦ 0`, `cons head tail ↦ succ (self tail)`). -/
def listLenIotaRules : List CtorIotaRule :=
  [ { ctorTag := "nil",  fieldNames := [],               minorBody := .lit 0 }
  , { ctorTag := "cons", fieldNames := ["head", "tail"], minorBody := .natSucc (.app (.bvar 3) (.bvar 0)) } ]

/-- Lowered multi-constructor recursor for `List Nat`. -/
def listLenIotaLExpr : LExpr :=
  compileMultiCtorIota "listLenIota" .natural listLenIotaRules

/-- Lower a nested `Option (List Nat)` into algebraic `LExpr`. -/
def optionListToLExpr : Option (List Nat) → LExpr
  | none    => .inject "none" []
  | some xs => .inject "some" [("val", natListToLExpr xs)]

/-- Nested multi-constructor ι-rules for `Option (List Nat)` (`none ↦ 0`, `some xs ↦ listLenIota xs`). -/
def nestedOptionListIotaRules : List CtorIotaRule :=
  [ { ctorTag := "none", fieldNames := [],      minorBody := .lit 0 }
  , { ctorTag := "some", fieldNames := ["val"], minorBody := .app listLenIotaLExpr (.bvar 0) } ]

/-- Lowered nested multi-constructor recursor for `Option (List Nat)`. -/
def nestedOptionListIotaLExpr : LExpr :=
  compileMultiCtorIota "nestedOptionListIota" .natural nestedOptionListIotaRules

theorem natRecIota_runs_zero :
    SSteps (.app natRecIotaLExpr (peanoNatToLExpr 0)) (.lit 0) := by
  have hunf : SStep (.app natRecIotaLExpr (peanoNatToLExpr 0))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("zero", [], .lit 0)
            , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.bvar 2) (.bvar 0)))) ]
            (.bvar 0))).inst natRecIotaLExpr)
        (peanoNatToLExpr 0)) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.bvar 2) (.bvar 0)))) ]
          (.bvar 0))).inst natRecIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
          (.bvar 0)) := by
    simp [natRecIotaLExpr, compileMultiCtorIota, natIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (peanoNatToLExpr 0)) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
        (.bvar 0)).inst (peanoNatToLExpr 0) =
      .cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
        (.inject "zero" []) := by
    simp [peanoNatToLExpr, natRecIotaLExpr, compileMultiCtorIota, natIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  exact .next (.casesInject .natural _ "zero" [] [] (.lit 0) [] rfl rfl) (.refl _)

theorem natRecIota_runs_succ (n : Nat)
    (ih : SSteps (.app natRecIotaLExpr (peanoNatToLExpr n)) (.lit n)) :
    SSteps (.app natRecIotaLExpr (peanoNatToLExpr (n + 1))) (.lit (n + 1)) := by
  have hunf : SStep (.app natRecIotaLExpr (peanoNatToLExpr (n + 1)))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("zero", [], .lit 0)
            , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.bvar 2) (.bvar 0)))) ]
            (.bvar 0))).inst natRecIotaLExpr)
        (peanoNatToLExpr (n + 1))) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app (.bvar 2) (.bvar 0)))) ]
          (.bvar 0))).inst natRecIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("zero", [], .lit 0)
          , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
          (.bvar 0)) := by
    simp [natRecIotaLExpr, compileMultiCtorIota, natIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (peanoNatToLExpr (n + 1))) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
        (.bvar 0)).inst (peanoNatToLExpr (n + 1)) =
      .cases .natural
        [ ("zero", [], .lit 0)
        , ("succ", ["pred"], .lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0)))) ]
        (.inject "succ" [("pred", peanoNatToLExpr n)]) := by
    simp [peanoNatToLExpr, natRecIotaLExpr, compileMultiCtorIota, natIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.casesInject .natural _ "succ" [("pred", peanoNatToLExpr n)] ["pred"]
    (.lam .emptyRow (.natSucc (.app natRecIotaLExpr (.bvar 0))))
    [peanoNatToLExpr n] rfl rfl) ?_
  refine .next (.beta .emptyRow _ (peanoNatToLExpr n)) ?_
  have hinst3 :
      (LExpr.natSucc (.app natRecIotaLExpr (.bvar 0))).inst (peanoNatToLExpr n) =
      .natSucc (.app natRecIotaLExpr (peanoNatToLExpr n)) := by
    simp [natRecIotaLExpr, compileMultiCtorIota, natIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst3]
  exact ssteps_trans (ssteps_succArg ih) (.next (.succFold n) (.refl _))

theorem natRecIota_runs : ∀ (n : Nat),
    SSteps (.app natRecIotaLExpr (peanoNatToLExpr n)) (.lit n)
  | 0     => natRecIota_runs_zero
  | n + 1 => natRecIota_runs_succ n (natRecIota_runs n)

theorem optionRecIota_runs_none (defaultVal : Nat) :
    SSteps (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr none)) (.lit defaultVal) := by
  have hunf : SStep (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr none))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("none", [], .lit defaultVal)
            , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
            (.bvar 0))).inst (optionRecIotaLExpr defaultVal))
        (optionNatToLExpr none)) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit defaultVal)
          , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
          (.bvar 0))).inst (optionRecIotaLExpr defaultVal) =
      .lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit defaultVal)
          , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
          (.bvar 0)) := by
    simp [optionRecIotaLExpr, compileMultiCtorIota, optionIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (optionNatToLExpr none)) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("none", [], .lit defaultVal)
        , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
        (.bvar 0)).inst (optionNatToLExpr none) =
      .cases .natural
        [ ("none", [], .lit defaultVal)
        , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
        (.inject "none" []) := by
    simp [optionNatToLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [hinst2]
  exact .next (.casesInject .natural _ "none" [] [] (.lit defaultVal) [] rfl rfl) (.refl _)

theorem optionRecIota_runs_some (defaultVal v : Nat) :
    SSteps (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr (some v))) (.lit v) := by
  have hunf : SStep (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr (some v)))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("none", [], .lit defaultVal)
            , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
            (.bvar 0))).inst (optionRecIotaLExpr defaultVal))
        (optionNatToLExpr (some v))) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit defaultVal)
          , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
          (.bvar 0))).inst (optionRecIotaLExpr defaultVal) =
      .lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit defaultVal)
          , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
          (.bvar 0)) := by
    simp [optionRecIotaLExpr, compileMultiCtorIota, optionIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (optionNatToLExpr (some v))) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("none", [], .lit defaultVal)
        , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
        (.bvar 0)).inst (optionNatToLExpr (some v)) =
      .cases .natural
        [ ("none", [], .lit defaultVal)
        , ("some", ["val"], .lam .emptyRow (.bvar 0)) ]
        (.inject "some" [("val", .lit v)]) := by
    simp [optionNatToLExpr, LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single]
  rw [hinst2]
  refine .next (.casesInject .natural _ "some" [("val", .lit v)] ["val"]
    (.lam .emptyRow (.bvar 0)) [.lit v] rfl rfl) ?_
  refine .next (.beta .emptyRow (.bvar 0) (.lit v)) ?_
  have hinst3 : (LExpr.bvar 0).inst (.lit v) = .lit v := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst3]
  exact .refl _

theorem listLenIota_runs_nil :
    SSteps (.app listLenIotaLExpr (natListToLExpr [])) (.lit 0) := by
  have hunf : SStep (.app listLenIotaLExpr (natListToLExpr []))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("nil", [], .lit 0)
            , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app (.bvar 3) (.bvar 0))))) ]
            (.bvar 0))).inst listLenIotaLExpr)
        (natListToLExpr [])) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("nil", [], .lit 0)
          , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app (.bvar 3) (.bvar 0))))) ]
          (.bvar 0))).inst listLenIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("nil", [], .lit 0)
          , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
          (.bvar 0)) := by
    simp [listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (natListToLExpr [])) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("nil", [], .lit 0)
        , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
        (.bvar 0)).inst (natListToLExpr []) =
      .cases .natural
        [ ("nil", [], .lit 0)
        , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
        (.inject "nil" []) := by
    simp [natListToLExpr, listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  exact .next (.casesInject .natural _ "nil" [] [] (.lit 0) [] rfl rfl) (.refl _)

theorem listLenIota_runs_cons (x : Nat) (xs : List Nat)
    (ih : SSteps (.app listLenIotaLExpr (natListToLExpr xs)) (.lit xs.length)) :
    SSteps (.app listLenIotaLExpr (natListToLExpr (x :: xs))) (.lit (x :: xs).length) := by
  have hunf : SStep (.app listLenIotaLExpr (natListToLExpr (x :: xs)))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("nil", [], .lit 0)
            , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app (.bvar 3) (.bvar 0))))) ]
            (.bvar 0))).inst listLenIotaLExpr)
        (natListToLExpr (x :: xs))) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("nil", [], .lit 0)
          , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app (.bvar 3) (.bvar 0))))) ]
          (.bvar 0))).inst listLenIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("nil", [], .lit 0)
          , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
          (.bvar 0)) := by
    simp [listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename, liftRename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (natListToLExpr (x :: xs))) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("nil", [], .lit 0)
        , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
        (.bvar 0)).inst (natListToLExpr (x :: xs)) =
      .cases .natural
        [ ("nil", [], .lit 0)
        , ("cons", ["head", "tail"], .lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))))) ]
        (.inject "cons" [("head", .lit x), ("tail", natListToLExpr xs)]) := by
    simp [natListToLExpr, listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.casesInject .natural _ "cons"
    [("head", .lit x), ("tail", natListToLExpr xs)] ["head", "tail"]
    (.lam .emptyRow (.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0)))))
    [.lit x, natListToLExpr xs] rfl rfl) ?_
  refine .next (.appFun (natListToLExpr xs) (.beta .emptyRow _ (.lit x))) ?_
  have hinst3 :
      (LExpr.lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0)))).inst (.lit x) =
      .lam .emptyRow (.natSucc (.app listLenIotaLExpr (.bvar 0))) := by
    simp [listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.rename]
  rw [hinst3]
  refine .next (.beta .emptyRow _ (natListToLExpr xs)) ?_
  have hinst4 :
      (LExpr.natSucc (.app listLenIotaLExpr (.bvar 0))).inst (natListToLExpr xs) =
      .natSucc (.app listLenIotaLExpr (natListToLExpr xs)) := by
    simp [listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst4]
  exact ssteps_trans (ssteps_succArg ih) (.next (.succFold xs.length) (.refl _))

theorem listLenIota_runs : ∀ (xs : List Nat),
    SSteps (.app listLenIotaLExpr (natListToLExpr xs)) (.lit xs.length)
  | []      => listLenIota_runs_nil
  | x :: xs => listLenIota_runs_cons x xs (listLenIota_runs xs)

theorem nestedOptionListIota_runs_some (xs : List Nat) :
    SSteps (.app nestedOptionListIotaLExpr (optionListToLExpr (some xs))) (.lit xs.length) := by
  have hunf : SStep (.app nestedOptionListIotaLExpr (optionListToLExpr (some xs)))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("none", [], .lit 0)
            , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
            (.bvar 0))).inst nestedOptionListIotaLExpr)
        (optionListToLExpr (some xs))) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit 0)
          , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
          (.bvar 0))).inst nestedOptionListIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit 0)
          , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
          (.bvar 0)) := by
    simp [nestedOptionListIotaLExpr, compileMultiCtorIota, nestedOptionListIotaRules,
      listLenIotaLExpr, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.rename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (optionListToLExpr (some xs))) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("none", [], .lit 0)
        , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
        (.bvar 0)).inst (optionListToLExpr (some xs)) =
      .cases .natural
        [ ("none", [], .lit 0)
        , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
        (.inject "some" [("val", natListToLExpr xs)]) := by
    simp [optionListToLExpr, listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  refine .next (.casesInject .natural _ "some" [("val", natListToLExpr xs)] ["val"]
    (.lam .emptyRow (.app listLenIotaLExpr (.bvar 0)))
    [natListToLExpr xs] rfl rfl) ?_
  refine .next (.beta .emptyRow _ (natListToLExpr xs)) ?_
  have hinst3 :
      (LExpr.app listLenIotaLExpr (.bvar 0)).inst (natListToLExpr xs) =
      .app listLenIotaLExpr (natListToLExpr xs) := by
    simp [listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst3]
  exact listLenIota_runs xs

theorem nestedOptionListIota_runs_none :
    SSteps (.app nestedOptionListIotaLExpr (optionListToLExpr none)) (.lit 0) := by
  have hunf : SStep (.app nestedOptionListIotaLExpr (optionListToLExpr none))
      (.app
        ((LExpr.lam .emptyRow
          (.cases .natural
            [ ("none", [], .lit 0)
            , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
            (.bvar 0))).inst nestedOptionListIotaLExpr)
        (optionListToLExpr none)) :=
    .appFun _ (.unfold _ _ _)
  refine .next hunf ?_
  have hinst1 :
      (LExpr.lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit 0)
          , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
          (.bvar 0))).inst nestedOptionListIotaLExpr =
      .lam .emptyRow
        (.cases .natural
          [ ("none", [], .lit 0)
          , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
          (.bvar 0)) := by
    simp [nestedOptionListIotaLExpr, compileMultiCtorIota, nestedOptionListIotaRules,
      listLenIotaLExpr, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.rename]
  rw [hinst1]
  refine .next (.beta .emptyRow _ (optionListToLExpr none)) ?_
  have hinst2 :
      (LExpr.cases .natural
        [ ("none", [], .lit 0)
        , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
        (.bvar 0)).inst (optionListToLExpr none) =
      .cases .natural
        [ ("none", [], .lit 0)
        , ("some", ["val"], .lam .emptyRow (.app listLenIotaLExpr (.bvar 0))) ]
        (.inject "none" []) := by
    simp [optionListToLExpr, listLenIotaLExpr, compileMultiCtorIota, listLenIotaRules, wrapMinorBvars,
      LExpr.inst, LExpr.subst, LExpr.liftSubst, LExpr.single, LExpr.rename]
  rw [hinst2]
  exact .next (.casesInject .natural _ "none" [] [] (.lit 0) [] rfl rfl) (.refl _)

theorem nestedOptionListIota_runs : ∀ (opt : Option (List Nat)),
    SSteps (.app nestedOptionListIotaLExpr (optionListToLExpr opt)) (.lit ((opt.map List.length).getD 0))
  | none    => nestedOptionListIota_runs_none
  | some xs => nestedOptionListIota_runs_some xs

theorem nestedOptionListIota_eval (opt : Option (List Nat)) :
    Evaluates (lowerT (.app nestedOptionListIotaLExpr (optionListToLExpr opt)))
      (.nat ((opt.map List.length).getD 0)) := by
  simpa [lowerT] using lower_sound_nat (nestedOptionListIota_runs opt)

/-- **Theorem (`compileMultiCtorIota_sound`)**:
`compileMultiCtorIota` soundly lowers 2-constructor and nested inductive eliminators (`Nat`, `Option`,
`List`, and nested `Option (List Nat)`) into `LExpr` and `Core4` (`Evaluates`):
1. `Nat` (`natRecIotaLExpr`): evaluates `peanoNatToLExpr n` to `.nat n` for every `n : Nat`,
2. `Option` (`optionRecIotaLExpr`): evaluates `none` to `.nat defaultVal` and `some v` to `.nat v`,
3. `List` (`listLenIotaLExpr`): evaluates `natListToLExpr xs` to `.nat xs.length` for every `xs : List Nat`,
4. Nested `Option (List Nat)` (`nestedOptionListIotaLExpr`): evaluates `none` to `.nat 0` and
   `some xs` to `.nat xs.length` (`nestedOptionListIota_eval`). -/
theorem compileMultiCtorIota_sound (n defaultVal v : Nat) (xs : List Nat) :
    SSteps (.app natRecIotaLExpr (peanoNatToLExpr n)) (.lit n) ∧
    Evaluates (lowerT (.app natRecIotaLExpr (peanoNatToLExpr n))) (.nat n) ∧
    Evaluates (lowerT (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr none))) (.nat defaultVal) ∧
    Evaluates (lowerT (.app (optionRecIotaLExpr defaultVal) (optionNatToLExpr (some v)))) (.nat v) ∧
    SSteps (.app listLenIotaLExpr (natListToLExpr xs)) (.lit xs.length) ∧
    Evaluates (lowerT (.app listLenIotaLExpr (natListToLExpr xs))) (.nat xs.length) ∧
    Evaluates (lowerT (.app nestedOptionListIotaLExpr (optionListToLExpr (some xs)))) (.nat xs.length) := by
  refine ⟨natRecIota_runs n, ?_, ?_, ?_, listLenIota_runs xs, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_nat (natRecIota_runs n)
  · simpa [lowerT] using lower_sound_nat (optionRecIota_runs_none defaultVal)
  · simpa [lowerT] using lower_sound_nat (optionRecIota_runs_some defaultVal v)
  · simpa [lowerT] using lower_sound_nat (listLenIota_runs xs)
  · exact nestedOptionListIota_eval (some xs)

end Obend.Lower.Inductive
end

