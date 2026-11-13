module
/-
# Data refinement, derived polynomial signatures and lens renewal: the test suite

1. `SortedArraySet`: the fast operations run (`#guard`), agree with their specification, and their
   algebra is one `refine_exec` each, for packed sets, for raw arrays under their invariants, and
   for an operation defined here and registered with `@[refine_exec_simp]`.
2. `u64BytesRefinement`: byte order, round trip, indexing.
3. `FaceIdeal3`: lattice laws, the boundary, and the truth-table reading that loses it.
4. `#derive_poly_alg` / `#derive_alg_config` on lists, expression trees and numerals; functions and
   an inductive proof carried across.
5. `DeltaLens`: composition, disjointness, step framing; a claim certificate (the `ReviewMember`
   composition of `Obend.Teeth.Logic.FrameTeeth`, restated here) and an intention renewed across a
   richer state record.
6. `#tooth` mutations and the axiom audit.
-/
public import Obend.Tactic.DataRefinement
public import Obend.Elab.DeriveRepair
public import Obend.Repair.DeltaLensRenew
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Tactic.DataRefinement
import all Obend.Repair.AlgConfig
import all Obend.Elab.DeriveRepair
import all Obend.Repair.DeltaLensRenew
public section
namespace Obend.Tests.Metasystem.DataRefinementAndDeriveTest
open Obend Obend.Repair Obend.Logic Obend.Tactic.DataRefinement
set_option autoImplicit false

universe u

/-! ## 1. Sorted array sets -/

def evens : SortedArraySet Nat := ⟨#[0, 2, 4, 6, 8], (by decide : SortedArray #[0, 2, 4, 6, 8])⟩
def small : SortedArraySet Nat := ⟨#[1, 2, 3, 4], (by decide : SortedArray #[1, 2, 3, 4])⟩

#guard (evens.union small).val == #[0, 1, 2, 3, 4, 6, 8]
#guard (evens.inter small).val == #[2, 4]
#guard (evens.diff small).val == #[0, 6, 8]
#guard evens.contains 6 && !evens.contains 5 && !evens.contains 9
-- Without the invariant the search is wrong: 5 is in the array and is not found.
#guard containsFast #[5, 1, 3] 5 == false

example : evens.contains 4 = true := by refine_exec
example : (evens.inter small).contains 2 = true := by refine_exec
example : (evens.diff small).contains 4 = false := by refine_exec
example : (evens.union small).toSpec.mem 7 = false := by refine_exec

section Laws
variable {α : Type u} [StrictLinearOrder α]

theorem diff_inter (p q r : SortedArraySet α) : p.diff (q.inter r) = (p.diff q).union (p.diff r) := by
  refine_exec

theorem union_absorb (p q : SortedArraySet α) : p.union (p.inter q) = p := by refine_exec

theorem inter_diff_empty (p q : SortedArraySet α) : (p.inter q).inter (p.diff q) = .empty := by refine_exec

theorem contains_inter_union (p q r : SortedArraySet α) (z : α) :
    (p.inter (q.union r)).contains z = ((p.contains z && q.contains z) || (p.contains z && r.contains z)) := by
  refine_exec

/-- Raw arrays: the invariants in scope discharge the side conditions. -/
theorem raw_union_comm {a b : Array α} (ha : SortedArray a) (hb : SortedArray b) (z : α) :
    containsFast (unionFast a b) z = containsFast (unionFast b a) z := by refine_exec

theorem raw_inter_union {a b c : Array α} (ha : SortedArray a) (hb : SortedArray b) (hc : SortedArray c)
    (z : α) :
    containsFast (interFast a (unionFast b c)) z =
      (containsFast a z && (containsFast b z || containsFast c z)) := by refine_exec

/-- An operation of this module, built from the fast ones. -/
def symDiff (p q : SortedArraySet α) : SortedArraySet α := (p.diff q).union (q.diff p)

@[refine_exec_simp] theorem symDiff_toSpec (p q : SortedArraySet α) :
    (symDiff p q).toSpec = (p.toSpec.diff q.toSpec).union (q.toSpec.diff p.toSpec) := by
  rw [symDiff, SortedArraySet.unionFast_toSpec, SortedArraySet.diffFast_toSpec, SortedArraySet.diffFast_toSpec]

theorem symDiff_comm (p q : SortedArraySet α) : symDiff p q = symDiff q p := by refine_exec
theorem symDiff_self (p : SortedArraySet α) : symDiff p p = .empty := by refine_exec
theorem symDiff_assoc (p q r : SortedArraySet α) : symDiff (symDiff p q) r = symDiff p (symDiff q r) := by
  refine_exec
theorem contains_symDiff (p q : SortedArraySet α) (z : α) :
    (symDiff p q).contains z = xor (p.contains z) (q.contains z) := by refine_exec

end Laws

/-! ## 2. Words as little-endian bytes -/

#guard (packU64LE [0x0102030405060708]).data == #[8, 7, 6, 5, 4, 3, 2, 1]
#guard (packU64LE [1, 2, 3]).size == 24
#guard readU64LE (packU64LE [0x0102030405060708, 0xdeadbeef, 7]) 1 == 0xdeadbeef
#guard readU64LE (packU64LE [1, 2, 3]) 3 == 0
#guard unpackU64LE (packU64LE [18446744073709551615, 0, 42]) == [18446744073709551615, 0, 42]

example : readU64LE (packU64LE [0x0102030405060708, 0xdeadbeef, 7]) 1 = 0xdeadbeef := by refine_exec

theorem read_pack_head (w : UInt64) (l : List UInt64) : readU64LE (packU64LE (w :: l)) 0 = w := by refine_exec

theorem read_pack_tail (w : UInt64) (l : List UInt64) (i : Nat) :
    readU64LE (packU64LE (w :: l)) (i + 1) = readU64LE (packU64LE l) i := by refine_exec

theorem ofList_toSpec (l : List UInt64) : (U64Bytes.ofList l).toSpec = l := by refine_exec

/-- Indexing any well-formed byte string is indexing the list it stands for. -/
theorem read_is_index (b : ByteArray) (hb : b.size % 8 = 0) (i : Nat) :
    readU64LE b i = (unpackU64LE b).getD i 0 :=
  readU64LE_eq_spec i _ b ⟨hb, rfl⟩

/-! ## 3. Face ideals of the 3-cube -/

theorem face_modular (a b c : FaceIdeal3) :
    (a.meet b).join (a.meet c) = a.meet (b.join (a.meet c)) := by refine_exec

theorem face_median (a b c : FaceIdeal3) :
    ((a.meet b).join (b.meet c)).join (c.meet a) = ((a.join b).meet (b.join c)).meet (c.join a) := by
  refine_exec

/-- On raw words the same laws, bit by bit. -/
theorem word_distrib (a b c : BitVec 27) : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by refine_exec

attribute [refine_exec_simp] Trit.isZero_and_isOne

/-- The endpoints are disjoint, with the one fact about a coordinate registered above. -/
theorem endpoints_disjoint (v : Fin 3) : (FaceIdeal3.varEq0 v).meet (FaceIdeal3.varEq1 v) = .bot := by
  refine_exec

theorem boundary_below_top (v : Fin 3) (a : FaceIdeal3) :
    ((FaceIdeal3.varEq0 v).join (FaceIdeal3.varEq1 v)).meet a =
      ((FaceIdeal3.varEq0 v).meet a).join ((FaceIdeal3.varEq1 v).meet a) := by refine_exec

/-- `∂𝕀 ≠ 𝕀`, at every variable. -/
theorem boundary_ne_top_all : ∀ v : Fin 3, (FaceIdeal3.varEq0 v).join (FaceIdeal3.varEq1 v) ≠ .top :=
  FaceIdeal3.boundary_ne_top

example : Trit3.index Trit3.generic = 26 := rfl
example : (varEq0Mask 0 ||| varEq1Mask 0).getLsbD 26 = false := by decide +kernel
example : (BitVec.allOnes 27).getLsbD 26 = true := by decide +kernel

/-- `(i_v = 0)` as a truth table over the 8 vertices of the cube. -/
def cubeEq0 (v : Fin 3) : BitVec 8 := BitVec.ofNat 8 (maskNat (fun i => (i / 2 ^ v.val) % 2 == 0) 8)
/-- `(i_v = 1)` as a truth table over the 8 vertices. -/
def cubeEq1 (v : Fin 3) : BitVec 8 := BitVec.ofNat 8 (maskNat (fun i => (i / 2 ^ v.val) % 2 == 1) 8)

/-- **The collapse**: on truth tables the boundary is everything, `∂𝕀 = 𝕀`. -/
theorem truthTable_boundary_eq_top : ∀ v : Fin 3, cubeEq0 v ||| cubeEq1 v = BitVec.allOnes 8 := by
  decide +kernel

/-! ## 4. Derived polynomial signatures -/

inductive ConsList : Type where
  | nil : ConsList
  | cons (head : Nat) (tail : ConsList) : ConsList

inductive SnocList : Type where
  | empty : SnocList
  | snoc (init : SnocList) (last : Nat) : SnocList

inductive AExp : Type where
  | lit (n : Nat)
  | var (x : String)
  | add (l r : AExp)
  | neg (e : AExp)

inductive Rpn : Type where
  | push (n : Nat)
  | load (x : String)
  | plus (a b : Rpn)
  | minus (a : Rpn)

inductive Peano : Type where
  | zero
  | succ (n : Peano)

inductive Tally : Type where
  | none
  | more (t : Tally)

inductive Rose : Type where
  | node (kids : List Rose)

#derive_poly_alg AExp
#derive_alg_config listCfg : ConsList ≃ SnocList
#derive_alg_config exprCfg : AExp ≃ Rpn
#derive_alg_config peanoCfg : Peano ≃ Tally

/--
info: scar-free bridge Obend.Tests.Metasystem.DataRefinementAndDeriveTest.listCfg :
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.ConsList ≃ Obend.Tests.Metasystem.DataRefinementAndDeriveTest.SnocList
  over Obend.Tests.Metasystem.DataRefinementAndDeriveTest.ConsList.PolyShape:
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.listCfg.dInit does not mention Obend.Tests.Metasystem.DataRefinementAndDeriveTest.ConsList,
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.ConsList.polyInit does not mention Obend.Tests.Metasystem.DataRefinementAndDeriveTest.SnocList
-/
#guard_msgs (whitespace := lax) in
#check_scar_free_bridge listCfg

/--
info: scar-free bridge Obend.Tests.Metasystem.DataRefinementAndDeriveTest.exprCfg :
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.AExp ≃ Obend.Tests.Metasystem.DataRefinementAndDeriveTest.Rpn
  over Obend.Tests.Metasystem.DataRefinementAndDeriveTest.AExp.PolyShape:
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.exprCfg.dInit does not mention Obend.Tests.Metasystem.DataRefinementAndDeriveTest.AExp,
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.AExp.polyInit does not mention Obend.Tests.Metasystem.DataRefinementAndDeriveTest.Rpn
-/
#guard_msgs (whitespace := lax) in
#check_scar_free_bridge exprCfg

/--
error: #derive_alg_config: Obend.Tests.Metasystem.DataRefinementAndDeriveTest.ConsList.cons has 1 payload fields and
  Obend.Tests.Metasystem.DataRefinementAndDeriveTest.Peano.succ has 0
-/
#guard_msgs (whitespace := lax) in
#derive_alg_config badCfg : ConsList ≃ Peano

/-- error: #derive_poly_alg: Obend.Tests.Metasystem.DataRefinementAndDeriveTest.Rose is a nested inductive -/
#guard_msgs (whitespace := lax) in
#derive_poly_alg Rose

example : listCfg.forward (.cons 1 (.cons 2 (.cons 3 .nil))) = .snoc (.snoc (.snoc .empty 3) 2) 1 := rfl
example : listCfg.backward (.snoc (.snoc .empty 2) 1) = .cons 1 (.cons 2 .nil) := rfl
example : exprCfg.forward (.add (.lit 1) (.neg (.var "x"))) = .plus (.push 1) (.minus (.load "x")) := rfl
example : peanoCfg.forward (.succ (.succ .zero)) = .more (.more .none) := rfl
example (e : AExp) : AExp.polyAlg.op (AExp.polyUnpack e) = e := AExp.polyPack_unpack e

theorem list_round_trip (l : ConsList) : listCfg.backward (listCfg.forward l) = l := listCfg.backward_forward l
theorem expr_round_trip (r : Rpn) : exprCfg.forward (exprCfg.backward r) = r := exprCfg.forward_backward r

/-- The sum of a list, written once against the signature. -/
def sumAlg : PAlg ConsList.PolyShape ConsList.PolyArity Nat :=
  ⟨fun t => match t with
    | ⟨.nil, _⟩ => 0
    | ⟨.cons x, k⟩ => x + k 0⟩

def consSum : ConsList → Nat := ConsList.polyFold sumAlg
def snocSum : SnocList → Nat := listCfg.dFold sumAlg

example : snocSum (.snoc (.snoc (.snoc .empty 3) 2) 1) = 6 := rfl

/-- **A function carried across** (`repair_by_instantiation`): the same algebra, on the other list. -/
theorem sum_transport (l : ConsList) : consSum l = snocSum (listCfg.forward l) :=
  listCfg.repair_by_instantiation sumAlg l

/-- An evaluator, written once against the signature of `AExp`. -/
def evalAlg (env : String → Int) : PAlg AExp.PolyShape AExp.PolyArity Int :=
  ⟨fun t => match t with
    | ⟨.lit n, _⟩ => n
    | ⟨.var x, _⟩ => env x
    | ⟨.add, k⟩ => k 0 + k 1
    | ⟨.neg, k⟩ => -k 0⟩

theorem eval_transport (env : String → Int) (e : AExp) :
    AExp.polyFold (evalAlg env) e = exprCfg.dFold (evalAlg env) (exprCfg.forward e) :=
  exprCfg.repair_by_instantiation (evalAlg env) e

example : exprCfg.dFold (evalAlg fun _ => 5) (.plus (.push 1) (.minus (.load "x"))) = -4 := rfl

/-- Length and "add one to every element", for any initial algebra of the list signature. -/
def lenAlg : PAlg ConsList.PolyShape ConsList.PolyArity Nat :=
  ⟨fun t => match t with
    | ⟨.nil, _⟩ => 0
    | ⟨.cons _, k⟩ => k 0 + 1⟩

def bumpAlg {X : Type} (I : InitPAlg ConsList.PolyShape ConsList.PolyArity X) :
    PAlg ConsList.PolyShape ConsList.PolyArity X :=
  ⟨fun t => match t with
    | ⟨.nil, k⟩ => I.alg.op ⟨.nil, k⟩
    | ⟨.cons x, k⟩ => I.alg.op ⟨.cons (x + 1), k⟩⟩

/-- **A proof written once**, by the induction principle of an initial algebra. -/
theorem len_bump {X : Type} (I : InitPAlg ConsList.PolyShape ConsList.PolyArity X) (x : X) :
    I.fold lenAlg (I.fold (bumpAlg I) x) = I.fold lenAlg x := by
  apply I.elimProp (fun c => I.fold lenAlg (I.fold (bumpAlg I) c) = I.fold lenAlg c)
  intro a k ih
  cases a with
  | nil =>
    rw [I.fold_beta (bumpAlg I)]
    change I.fold lenAlg (I.alg.op ⟨.nil, _⟩) = _
    rw [I.fold_beta lenAlg, I.fold_beta lenAlg]
    rfl
  | cons x =>
    rw [I.fold_beta (bumpAlg I)]
    change I.fold lenAlg (I.alg.op ⟨.cons (x + 1), _⟩) = _
    rw [I.fold_beta lenAlg, I.fold_beta lenAlg]
    exact congrArg (· + 1) (ih 0)

/-- **The proof carried across**: instantiated at `SnocList`, with no mention of `ConsList`. -/
theorem snoc_len_bump (s : SnocList) :
    listCfg.dFold lenAlg (listCfg.dFold (bumpAlg listCfg.dInit) s) = listCfg.dFold lenAlg s :=
  len_bump listCfg.dInit s

theorem cons_len_bump (l : ConsList) :
    ConsList.polyFold lenAlg (ConsList.polyFold (bumpAlg ConsList.polyInit) l) = ConsList.polyFold lenAlg l :=
  len_bump ConsList.polyInit l

/-! ## 5. Lenses and renewal -/

/-- The old state. -/
structure Registry where
  version : Nat

/-- The richer state: the registry, with a clock and a log beside it. -/
structure Node where
  registry : Registry
  clock : Nat
  log : List String

@[expose] def Node.getRegistry (n : Node) : Registry := n.registry
@[expose] def Node.setRegistry (n : Node) (r : Registry) : Node := { n with registry := r }

theorem Node.registry_get_put (n : Node) : n.setRegistry n.getRegistry = n := rfl
theorem Node.registry_put_get (n : Node) (r : Registry) : (n.setRegistry r).getRegistry = r := rfl
theorem Node.registry_put_put (n : Node) (r₁ r₂ : Registry) :
    (n.setRegistry r₁).setRegistry r₂ = n.setRegistry r₂ := rfl

def registryLens : DeltaLens Node Registry :=
  ⟨Node.getRegistry, Node.setRegistry, Node.registry_get_put, Node.registry_put_get, Node.registry_put_put⟩

def clockLens : DeltaLens Node Nat :=
  ⟨fun n => n.clock, fun n c => { n with clock := c }, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

def versionLens : DeltaLens Registry Nat :=
  ⟨fun r => r.version, fun _ v => ⟨v⟩, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem registry_clock_disjoint : DisjointLenses registryLens clockLens := ⟨fun _ _ _ => rfl⟩

def node₀ : Node := ⟨⟨3⟩, 100, ["boot"]⟩

/-- A nested view: the version inside the registry inside the node. -/
def nodeVersionLens : DeltaLens Node Nat := registryLens.comp versionLens

example : nodeVersionLens.get node₀ = 3 := rfl
example : (nodeVersionLens.put node₀ 4).registry.version = 4 ∧ (nodeVersionLens.put node₀ 4).clock = 100 :=
  ⟨rfl, rfl⟩

theorem nodeVersion_clock_disjoint : DisjointLenses nodeVersionLens clockLens :=
  registry_clock_disjoint.comp_left versionLens

/-- Both views at once. -/
def registryClockLens : DeltaLens Node (Registry × Nat) := registry_clock_disjoint.pair

example : (registryClockLens.put node₀ (⟨9⟩, 0)).log = ["boot"] := rfl

/-- **A tick frames the registry**, along any run of ticks. -/
theorem ticks_frame_registry (n : Node) (k : Nat) :
    registryLens.get ((List.replicate k (· + 1)).foldl (fun s f => clockLens.modify f s) n) =
      registryLens.get n :=
  registry_clock_disjoint.frame_run _ n

theorem tick_bump_commute (n : Node) :
    clockLens.modify (· + 1) (nodeVersionLens.modify (· + 1) n) =
      nodeVersionLens.modify (· + 1) (clockLens.modify (· + 1) n) :=
  nodeVersion_clock_disjoint.symm.modify_comm _ _ n

/-- "The registry is at this version": a reference resolved against a registry. -/
def versionIntention : Intention Registry Unit Nat Nat String where
  ref _ := ()
  supports p := [p]
  holds w f := w.version == f
  resolve w _ := .ok w.version
  resolve_ref _ _ _ _ := rfl
  resolve_holds w _ p h f hf := by
    have e : w.version = p := Except.ok.inj h
    rw [List.mem_singleton] at hf
    rw [hf, ← e]
    exact beq_self_eq_true _

/-- The same intention over the richer state, with nothing proved again. -/
def nodeIntention : Intention Node Unit Nat Nat String := registryLens.liftIntention versionIntention

example : nodeIntention.current node₀ 3 = true := rfl
-- A registry step makes the pin stale; a tick does not.
example : nodeIntention.current (registryLens.modify (fun r => ⟨r.version + 1⟩) node₀) 3 = false := rfl
example : nodeIntention.current (clockLens.modify (· + 1) node₀) 3 = true := rfl

/-- **Renewal across the evolution** `Registry ⟶ Node`: a renewal made at a registry is the renewal
at every node holding it, and is current there. -/
theorem node_renew (n : Node) (r : Registry) (p : Nat) :
    nodeIntention.renew (registryLens.put n r) p = .ok r.version ∧
      nodeIntention.current (registryLens.put n r) r.version = true :=
  have h := renewIntentionAcrossLens registryLens versionIntention (v := r) (p := p) (p' := r.version) rfl n
  ⟨h.1, h.2.2.2⟩

/-- **The pin is framed** by every write to the clock. -/
theorem node_pin_framed (n : Node) (c p : Nat) :
    nodeIntention.current (clockLens.put n c) p = nodeIntention.current n p :=
  DeltaLens.liftIntention_frame registry_clock_disjoint versionIntention n c p

/-- A workspace: a composition with bookkeeping beside it. -/
structure Workspace where
  comp : Composition
  epoch : Nat
  notes : List String

@[expose] def Workspace.getComp (ws : Workspace) : Composition := ws.comp
@[expose] def Workspace.setComp (ws : Workspace) (C : Composition) : Workspace := { ws with comp := C }

theorem Workspace.comp_get_put (ws : Workspace) : ws.setComp ws.getComp = ws := rfl
theorem Workspace.comp_put_get (ws : Workspace) (C : Composition) : (ws.setComp C).getComp = C := rfl
theorem Workspace.comp_put_put (ws : Workspace) (C₁ C₂ : Composition) :
    (ws.setComp C₁).setComp C₂ = ws.setComp C₂ := rfl

def compLens : DeltaLens Workspace Composition :=
  ⟨Workspace.getComp, Workspace.setComp, Workspace.comp_get_put, Workspace.comp_put_get,
    Workspace.comp_put_put⟩

def epochLens : DeltaLens Workspace Nat :=
  ⟨fun ws => ws.epoch, fun ws e => { ws with epoch := e }, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem comp_epoch_disjoint : DisjointLenses compLens epochLens := ⟨fun _ _ _ => rfl⟩

section Review
open Obend.Core.Term

def layer (name : String) (fields : List (String × Term)) : Layer :=
  { name, metadata := .inject "declared" (.record [("name", .label name)]), fields }

/-- `def review(value): value + 1`. -/
def base : Layer := layer "ReviewBase.Base" [("review", .lam (.binary .add (.bound 0) (.nat 1)))]
/-- `def twice(value): self.review(self.review(value))`. -/
def twice : Layer :=
  layer "ReviewMember.Twice"
    [("twice", .lam (.app (.get (.bound 2) "review") (.app (.get (.bound 2) "review") (.bound 0))))]
/-- `def review(value): super.review(value) + 1`. -/
def augmented : Layer :=
  layer "ReviewMember.Augmented"
    [("review", .lam (.binary .add (.app (.get (.bound 1) "review") (.bound 0)) (.nat 1)))]
/-- A layer that adds a member nobody reads. -/
def unrelated : Layer := layer "ReviewMember.Unrelated" [("note", .nat 0)]

def seed : List (String × Term) := [("review", .lam (.bound 0)), ("twice", .lam (.bound 0))]

/-- `claim repeated(value: Nat): self.twice(value) == self.review(self.review(value))`. -/
def repeated : Term :=
  .lam (.lam (.lam (.binary .equal (.app (.get (.bound 2) "twice") (.bound 0))
    (.app (.get (.bound 2) "review") (.app (.get (.bound 2) "review") (.bound 0))))))

def reviewObject : ClaimObj := ⟨⟨augmented, [twice, base], seed⟩, 1, repeated, 1⟩

/-- The composition with one more layer on top. -/
def extended : Composition := ⟨unrelated, [augmented, twice, base], seed⟩

def derivation : List RStep :=
  [.congr (.app (.bound 0) (.bound 1)) (.get (.bound 2) "twice") [.lateBinding "twice" "ReviewMember.Twice"],
   .run 1]

end Review

/-- The derivation is accepted once, for the composition alone. -/
theorem review_accepted : claimCheck 4 reviewObject derivation = .ok := by decide +kernel

/-- **The certificate of `ReviewMember.repeated` renews into any workspace**: the derivation checked
once for the composition (`review_accepted`) is accepted for the composition a workspace holds. -/
theorem workspace_claim_renewed (ws : Workspace) :
    claimCheck 4 { reviewObject with comp := compLens.get (compLens.put ws reviewObject.comp) } derivation = .ok ∧
      claimMeaning { reviewObject with comp := compLens.get (compLens.put ws reviewObject.comp) } :=
  renewClaimAcrossLens compLens review_accepted ws

/-- **And is framed by the epoch.** -/
theorem workspace_claim_framed (ws : Workspace)
    (h : claimCheck 4 { reviewObject with comp := compLens.get ws } derivation = .ok) (e : Nat) :
    claimCheck 4 { reviewObject with comp := compLens.get (epochLens.put ws e) } derivation = .ok :=
  (renewClaimAcrossLens_frame comp_epoch_disjoint h e).1

/-- **And survives the composition growing a layer** that leaves its support `twice` alone. -/
theorem workspace_claim_evolved (ws : Workspace) :
    claimCheck 4 { reviewObject with comp := compLens.get (compLens.put ws extended), layer := 2 }
      derivation = .ok :=
  (renewClaimAcrossLens_evolve compLens review_accepted ws (C' := extended) (layer' := 2)
    (by intro m hm; simp [derivation, membersList, RStep.members] at hm; subst hm; rfl)
    (by decide +kernel)).1

/-! ## 6. Teeth and the axiom audit -/

-- 1. Without strict sortedness as the invariant, `containsFast` and `interFast` are not sound.
#tooth Obend.Tactic.DataRefinement.containsFast_eq_spec by
  mutation Obend.Tactic.DataRefinement.sortedArraySetRefinement := fun {α} [StrictLinearOrder α] =>
    { WF := fun _ => True, alpha := fun a _ => FinSetSpec.ofList a.toList }

#tooth Obend.Tactic.DataRefinement.interFast_eq_spec by
  mutation Obend.Tactic.DataRefinement.sortedArraySetRefinement := fun {α} [StrictLinearOrder α] =>
    { WF := fun _ => True, alpha := fun a _ => FinSetSpec.ofList a.toList }

-- 2. Read the 27 bits as vertices of a Boolean cube (no free coordinate) and the boundary is `⊤`.
#tooth Obend.Tactic.DataRefinement.boundaryMask_ne_allOnes by
  mutation Obend.Tactic.DataRefinement.tritAt := fun (i : Nat) (v : Fin 3) =>
    if (i / 2 ^ v.val) % 2 = 0 then Trit.zero else Trit.one

-- 3. A `put` that drops the write (no `put_get`), and one that also resets the clock (no `get_put`).
#tooth node_renew by
  mutation Node.setRegistry := fun (n : Node) (_ : Registry) => n

#tooth node_renew by
  mutation Node.setRegistry := fun (n : Node) (r : Registry) => { registry := r, clock := 0, log := n.log }

#tooth workspace_claim_renewed by
  mutation Workspace.setComp := fun (ws : Workspace) (_ : Composition) => ws

-- 4. A constructor packager that drops its payload is not an algebra the transport can use.
#tooth sum_transport by
  mutation listCfg.dAlg := ⟨fun t => match t with
    | ⟨.nil, _⟩ => SnocList.empty
    | ⟨.cons _, k⟩ => SnocList.snoc (k 0) 0⟩

open Lean Elab Command in
/-- No theorem of the three modules or of this suite rests on `sorryAx`, on compiler trust, or on an
axiom outside Lean's three. -/
elab "#audit_data_refinement_axioms" : command => do
  let targets : List Name := [
    ``Obend.Tactic.DataRefinement.containsFast_eq_spec,
    ``Obend.Tactic.DataRefinement.unionFast_eq_spec,
    ``Obend.Tactic.DataRefinement.interFast_eq_spec,
    ``Obend.Tactic.DataRefinement.diffFast_eq_spec,
    ``Obend.Tactic.DataRefinement.SortedArraySet.unionFast_toSpec,
    ``Obend.Tactic.DataRefinement.SortedArraySet.toSpec_injective,
    ``Obend.Tactic.DataRefinement.SortedArraySet.union_inter_distrib,
    ``Obend.Tactic.DataRefinement.readU64LE_packU64LE,
    ``Obend.Tactic.DataRefinement.packU64LE_refines,
    ``Obend.Tactic.DataRefinement.readU64LE_eq_spec,
    ``Obend.Tactic.DataRefinement.faceJoin_refines,
    ``Obend.Tactic.DataRefinement.faceMeet_refines,
    ``Obend.Tactic.DataRefinement.boundaryMask_ne_allOnes,
    ``Obend.Tactic.DataRefinement.FaceIdeal3.boundary_ne_top,
    ``Obend.Tactic.DataRefinement.FaceIdeal3.toSpec_injective,
    ``Obend.Tactic.DataRefinement.FaceIdeal3.meet_join_distrib,
    ``Obend.Tactic.DataRefinement.FaceIdeal3.join_meet_distrib,
    ``Obend.Repair.DeltaLens.duplicate_coalg,
    ``Obend.Repair.DisjointLenses.get_left_put_right,
    ``Obend.Repair.DisjointLenses.frame_run,
    ``Obend.Repair.renewClaimAcrossLens,
    ``Obend.Repair.renewClaimAcrossLens_frame,
    ``Obend.Repair.renewClaimAcrossLens_evolve,
    ``Obend.Repair.renewIntentionAcrossLens,
    ``Obend.Repair.DeltaLens.liftIntention_stays,
    ``symDiff_assoc, ``raw_inter_union, ``face_median, ``endpoints_disjoint, ``truthTable_boundary_eq_top,
    ``AExp.polyFold_beta, ``AExp.polyFold_eta, ``AExp.polyUnpack_pack, ``AExp.polyInit,
    ``listCfg, ``exprCfg, ``peanoCfg, ``sum_transport, ``eval_transport, ``snoc_len_bump,
    ``node_renew, ``node_pin_framed, ``workspace_claim_renewed, ``workspace_claim_framed,
    ``workspace_claim_evolved]
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for t in targets do
    for a in ← liftCoreM <| collectAxioms t do
      if a == ``sorryAx then throwError "{t} depends on sorryAx"
      if Obend.AssertAxioms.isCompilerTrust a then throwError "{t} depends on compiler trust {a}"
      unless standard.contains a do throwError "{t} depends on the axiom {a}"
  logInfo m!"axiom audit passed: {targets.length} declarations rest on no sorryAx, no compiler trust and no axiom outside propext, Classical.choice, Quot.sound"

/--
info: axiom audit passed: 45 declarations rest on no sorryAx, no compiler trust and no axiom outside
  propext, Classical.choice, Quot.sound
-/
#guard_msgs (whitespace := lax) in
#audit_data_refinement_axioms

/--
info: 'Obend.Tactic.DataRefinement.FaceIdeal3.boundary_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Obend.Tactic.DataRefinement.FaceIdeal3.boundary_ne_top

/-- info: 'Obend.Repair.renewIntentionAcrossLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Obend.Repair.renewIntentionAcrossLens

end Obend.Tests.Metasystem.DataRefinementAndDeriveTest
end
