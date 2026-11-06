module
/-
# Obend.Hardware.Hvm.Model — HVM2's net language, its interaction rules, and its text

The model of HVM2 (HigherOrderCO, crate `hvm` 2.0.22, `paper/HVM2.typst`) that the lowering of
`Obend.Hardware.Hvm` targets, and the emitter that prints it as `hvm run` reads it. Where the model
departs from HVM2 is said in `Obend.Hardware.Hvm`'s header.
-/
@[expose] public section
namespace Obend.Hardware.Hvm
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
