module
/-
# Obend.Lower.Transport — Proposition Lowering (`lowerProp`), Unconditional `LTyped` Transport, `transport@1`, and Open-Recursion `Slot` Binding

Connects Lean propositions and proofs over the `Obend.Lower` fragment to `Obend.Logic.Holds`,
`Obend.Judge.Format`, and `Obend.Slot`:

1. **Refutation-Freedom vs. Total `Holds` (`stuckAxiomTheory_consistent_yet_not_holds`,
   `transport_refutation_free`, `transport_holds`, `transport_data_holds`)**:
   - `Consistent th` (`¬ th.Provable (.boolLit false)`) + `lower_complete_bool` proves that a provable
     decidable claim never evaluates to `.boolean false` (`transport_refutation_free`).
   - A consistent theory with an unreduced axiom (`stuckAxiomTheory`) shows `Consistent th` alone does
     not imply `Holds` without `CanonicalBool` (`stuckAxiomTheory_consistent_yet_not_holds`).
   - General `Data` lowering (`dataLExpr`, `DataInFragment`, `lowerT_dataLExpr`) extends transport from
     `List Nat` to arbitrary first-order `Data` (`transport_data_refutation_free`, `transport_data_holds`).

2. **Unconditional `LTyped` Transport via Tait–Girard Reducibility (`transport_ltyped_holds`,
   `transport_ltyped_nat_holds`, `checkL_transport_nat_holds`)**:
   - Using `ltyped_red` and `red_lapps` from `Obend.Lower.Proofs.Complete`, any well-typed decision
     procedure `LTyped [] decideExpr (curry argTys .boolean)` with `nonEmptySplits decideExpr = true`
     automatically reduces on reducible arguments to a canonical boolean, eliminating the external
     `CanonicalBool` hypothesis completely.

3. **Beyond `∀ x, P (f x)` (`transport_given`, `transport_keeps`, `transport_subtype_witness`)**:
   - Conditional claims (`Q x → P x`), invariant preservation (`inv s → inv (step s)`), and
     constructively witnessed `Subtype` claims (`(x : Nat) → { y : Nat // P x y }`) all transport
     through `lowerT`.

4. **Registered Certificate Format `transport@1` and `transportSlot` (`transportJudge`,
   `transportFormat`, `transportSlot_usable_meaning`, `transportSlot_blocked_exact`,
   `transportSlot_blocked_on_override`)**:
   - Packages transported claims into a first-class `Obend.Judge.Format` (`transport@1`) backed by the
     verified bidirectional typechecker `checkL` and an `Obend.Slot.Slot Support TransportCert` whose
     reads satisfy T3 inheritance when supports hold and exact invalidation when a supported method is
     overridden.
-/
public import Obend.Lower.Proofs.Complete
public import Obend.Lower.Judge
public import Obend.Logic.Obligation
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Core.Data (Data)
open Obend.Logic
set_option autoImplicit false

/-! ## 1. Spine Application and General `Data` Lowering -/

theorem lowerT_lapps (f : LExpr) : ∀ (args : List LExpr),
    lowerT (lapps f args) = apps (lowerT f) (args.map lowerT)
  | [] => rfl
  | a :: rest => by
    simp only [lapps, List.foldl_cons, List.map_cons, apps]
    have := lowerT_lapps (.app f a) rest
    simpa [lapps, apps, lowerT] using this

theorem map_lowerT_lit : ∀ (ns : List Nat),
    (ns.map LExpr.lit).map lowerT = (ns.map Data.natural).map Data.term
  | [] => rfl
  | n :: ns => by
    simp only [List.map_cons, lowerT, Data.term, map_lowerT_lit ns]

mutual
/-- First-order `Data` values representable in the Lean-lite (`LExpr`) fragment: naturals, booleans,
records of fragment values, and variants whose payload is a record of constructor fields. -/
def DataInFragment : Data → Bool
  | .natural _ => true
  | .boolean _ => true
  | .label _ => false
  | .record fields => FieldsInFragment fields
  | .variant _ payload => PayloadInFragment payload

def PayloadInFragment : Data → Bool
  | .record fields => FieldsInFragment fields
  | _ => false

def FieldsInFragment : List (String × Data) → Bool
  | [] => true
  | (_, v) :: rest => DataInFragment v && FieldsInFragment rest
end

mutual
/-- Embed a `Data` value into `LExpr`. -/
def dataLExpr : Data → LExpr
  | .natural n => .lit n
  | .boolean b => .boolLit b
  | .label _ => .erased
  | .record fields => .record (fieldsLExpr fields)
  | .variant label payload => .inject label (payloadFieldsLExpr payload)

def payloadFieldsLExpr : Data → List (String × LExpr)
  | .record fields => fieldsLExpr fields
  | _ => []

def fieldsLExpr : List (String × Data) → List (String × LExpr)
  | [] => []
  | (name, v) :: rest => (name, dataLExpr v) :: fieldsLExpr rest
end

mutual
/-- Lowering `dataLExpr d` reproduces `d.term` on all fragment `Data`. -/
theorem lowerT_dataLExpr : ∀ (d : Data), DataInFragment d = true → lowerT (dataLExpr d) = d.term
  | .natural n, _ => by simp [dataLExpr, lowerT, Data.term]
  | .boolean b, _ => by simp [dataLExpr, lowerT, Data.term]
  | .label _, h => by simp [DataInFragment] at h
  | .record fields, h => by
    simp only [DataInFragment] at h
    simp only [dataLExpr, lowerT, Data.term, lowerT_fieldsLExpr fields h]
  | .variant label payload, h => by
    simp only [DataInFragment] at h
    simp only [dataLExpr, lowerT, Data.term, lowerT_payloadFieldsLExpr payload h]

theorem lowerT_payloadFieldsLExpr : ∀ (d : Data), PayloadInFragment d = true →
    .record ((payloadFieldsLExpr d).map fun x => (x.1, lowerT x.2)) = d.term
  | .natural _, h => by simp [PayloadInFragment] at h
  | .boolean _, h => by simp [PayloadInFragment] at h
  | .label _, h => by simp [PayloadInFragment] at h
  | .record fields, h => by
    simp only [PayloadInFragment] at h
    simp only [payloadFieldsLExpr, Data.term, lowerT_fieldsLExpr fields h]
  | .variant _ _, h => by simp [PayloadInFragment] at h

theorem lowerT_fieldsLExpr : ∀ (fs : List (String × Data)), FieldsInFragment fs = true →
    (fieldsLExpr fs).map (fun x => (x.1, lowerT x.2)) = Obend.Core.Data.fieldsTerm fs
  | [], _ => rfl
  | (name, v) :: rest, h => by
    simp only [FieldsInFragment, Bool.and_eq_true] at h
    simp only [fieldsLExpr, List.map_cons, Obend.Core.Data.fieldsTerm,
      lowerT_dataLExpr v h.1, lowerT_fieldsLExpr rest h.2]
end

theorem map_lowerT_dataLExpr : ∀ (ds : List Data),
    (∀ d ∈ ds, DataInFragment d = true) →
    (ds.map dataLExpr).map lowerT = ds.map Data.term
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.map_cons, lowerT_dataLExpr d (h d List.mem_cons_self),
      map_lowerT_dataLExpr ds (fun x hx => h x (List.mem_cons_of_mem _ hx))]

mutual
theorem nonEmptySplits_dataLExpr : ∀ (d : Data), nonEmptySplits (dataLExpr d) = true
  | .natural _ => by simp [dataLExpr, nonEmptySplits]
  | .boolean _ => by simp [dataLExpr, nonEmptySplits]
  | .label _ => by simp [dataLExpr, nonEmptySplits]
  | .record fields => by
    simp [dataLExpr, nonEmptySplits]
    intro a b hf
    exact nonEmptySplits_fieldsLExpr fields a b hf
  | .variant label payload => by
    simp [dataLExpr, nonEmptySplits]
    intro a b hf
    exact nonEmptySplits_payloadFieldsLExpr payload a b hf

theorem nonEmptySplits_payloadFieldsLExpr : ∀ (d : Data) (a : String) (b : LExpr),
    (a, b) ∈ payloadFieldsLExpr d → nonEmptySplits b = true
  | .natural _, _, _, h | .boolean _, _, _, h | .label _, _, _, h | .variant _ _, _, _, h => by
    simp [payloadFieldsLExpr] at h
  | .record fields, a, b, h => by
    simp only [payloadFieldsLExpr] at h
    exact nonEmptySplits_fieldsLExpr fields a b h

theorem nonEmptySplits_fieldsLExpr : ∀ (fs : List (String × Data)) (a : String) (b : LExpr),
    (a, b) ∈ fieldsLExpr fs → nonEmptySplits b = true
  | [], _, _, h => by simp [fieldsLExpr] at h
  | (name, v) :: rest, a, b, h => by
    simp only [fieldsLExpr, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | hrest
    · exact nonEmptySplits_dataLExpr v
    · exact nonEmptySplits_fieldsLExpr rest a b hrest
end

/-- Lower a decidable proposition's boolean decision procedure `decideExpr : LExpr` into a `Core4`
claim term. -/
def lowerProp (decideExpr : LExpr) : Term := lowerT decideExpr

/-! ## 2. Source Theory Consistency, the Stuck-Axiom Countermodel, and `transport` -/

/-- Abstract interface for provability of boolean decision terms in a Lean environment `Σ`. -/
structure SourceTheory where
  /-- `Provable e` holds when `Σ ⊢ e = true` (i.e. the proposition decided by `e` is provable in `Σ`). -/
  Provable : LExpr → Prop
  /-- Soundness of `Decidable`: if `e` reduces in the kernel (`SSteps`) to `.boolLit false`, then any
  proof of `e = true` yields a proof of `false = true` (`False`). -/
  decide_refutes : ∀ e : LExpr, SSteps e (.boolLit false) → Provable e → Provable (.boolLit false)

/-- `Σ` is consistent when `False` (`.boolLit false = true`) is not provable. -/
def Consistent (th : SourceTheory) : Prop := ¬ th.Provable (.boolLit false)

/-- **Countermodel (`stuckAxiomTheory`)**: an environment with an unreduced boolean axiom `.const "ax" (.bvar 0)`
can be consistent and prove `.const "ax" (.bvar 0) = true`, yet its lowering does not evaluate to
`.boolean true` because `.const "ax" (.bvar 0)` is not `CanonicalBool`. -/
def stuckAxiomExpr : LExpr := .const "ax" (.bvar 0)

def stuckAxiomTheory : SourceTheory where
  Provable e := e = stuckAxiomExpr
  decide_refutes e hrun hprov := by
    subst hprov
    cases hrun with
    | next s r =>
      cases s with
      | delta _ _ =>
        cases r with
        | next s' _ => cases s'

theorem stuckAxiomTheory_consistent_yet_not_holds :
    stuckAxiomTheory.Provable stuckAxiomExpr ∧
    Consistent stuckAxiomTheory ∧
    ¬ Evaluates (lowerProp stuckAxiomExpr) (.boolean true) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro hev
    simp only [lowerProp, stuckAxiomExpr, lowerT] at hev
    obtain ⟨steps, _⟩ := hev
    cases steps with
    | next s _ => cases s

/-- **`transport_refutation_free`**: for any canonical boolean decision term `decideExpr`, if `Σ` is
consistent and proves `lapps decideExpr (ns.map .lit)`, the lowered claim never evaluates to `false`
(proved via `lower_complete_bool`). -/
theorem transport_refutation_free
    (th : SourceTheory) (decideExpr : LExpr) (ns : List Nat)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ns.map .lit)))
    (hcan : CanonicalBool (lapps decideExpr (ns.map .lit))) :
    ¬ Evaluates (apps (lowerProp decideExpr) ((ns.map Data.natural).map Data.term)) (.boolean false) := by
  intro hev
  simp only [lowerProp, ← map_lowerT_lit, ← lowerT_lapps] at hev
  have hfalse : SSteps (lapps decideExpr (ns.map .lit)) (.boolLit false) :=
    lower_complete_bool hcan hev
  exact hcons (th.decide_refutes _ hfalse hprov)

/-- **`transport` (`transport_holds`)**: if `Σ` is consistent, proves `lapps decideExpr (ns.map .lit)`,
and the applied decision term is in the canonical boolean fragment (`CanonicalBool`), then the lowered
`Core4` claim satisfies `Obend.Logic.Holds` at `ns.map Data.natural`. -/
theorem transport_holds
    (th : SourceTheory) (decideExpr : LExpr) (ns : List Nat)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ns.map .lit)))
    (hcan : CanonicalBool (lapps decideExpr (ns.map .lit))) :
    Holds (lowerProp decideExpr) (ns.map Data.natural) := by
  obtain ⟨b, hb⟩ := hcan
  cases b with
  | true =>
    have hev : Evaluates (lowerT (lapps decideExpr (ns.map .lit))) (.boolean true) := by
      simpa [lowerT] using lower_sound_bool hb
    rw [lowerT_lapps, map_lowerT_lit] at hev
    exact hev
  | false =>
    exact False.elim (hcons (th.decide_refutes _ hb hprov))

/-- **`transport_data_refutation_free`**: refutation-freedom of `lowerProp decideExpr` at arbitrary
fragment `Data` arguments `ds : List Data`. -/
theorem transport_data_refutation_free
    (th : SourceTheory) (decideExpr : LExpr) (ds : List Data)
    (hfrag : ∀ d ∈ ds, DataInFragment d = true)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ds.map dataLExpr)))
    (hcan : CanonicalBool (lapps decideExpr (ds.map dataLExpr))) :
    ¬ Evaluates (apps (lowerProp decideExpr) (ds.map Data.term)) (.boolean false) := by
  intro hev
  simp only [lowerProp, ← map_lowerT_dataLExpr ds hfrag, ← lowerT_lapps] at hev
  have hfalse : SSteps (lapps decideExpr (ds.map dataLExpr)) (.boolLit false) :=
    lower_complete_bool hcan hev
  exact hcons (th.decide_refutes _ hfalse hprov)

/-- **`transport_data_holds`**: `Obend.Logic.Holds` at arbitrary fragment `Data` arguments `ds`. -/
theorem transport_data_holds
    (th : SourceTheory) (decideExpr : LExpr) (ds : List Data)
    (hfrag : ∀ d ∈ ds, DataInFragment d = true)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ds.map dataLExpr)))
    (hcan : CanonicalBool (lapps decideExpr (ds.map dataLExpr))) :
    Holds (lowerProp decideExpr) ds := by
  obtain ⟨b, hb⟩ := hcan
  cases b with
  | true =>
    have hev : Evaluates (lowerT (lapps decideExpr (ds.map dataLExpr))) (.boolean true) := by
      simpa [lowerT] using lower_sound_bool hb
    rw [lowerT_lapps, map_lowerT_dataLExpr ds hfrag] at hev
    exact hev
  | false =>
    exact False.elim (hcons (th.decide_refutes _ hb hprov))

/-! ## 2B. Unconditional `LTyped` Transport (via Tait–Girard Reducibility) -/

/-- **`transport_ltyped_holds`**: for ANY well-typed boolean decision procedure
`LTyped [] decideExpr (curry argTys .boolean)` with `nonEmptySplits decideExpr = true`, and ANY
fragment arguments `ds : List Data` whose `dataLExpr`s are reducible (`Red`), provability in a
consistent `SourceTheory` implies `Obend.Logic.Holds (lowerProp decideExpr) ds` — with NO external
`CanonicalBool` assumption. -/
theorem transport_ltyped_holds
    (th : SourceTheory) {decideExpr : LExpr} {argTys : List Ty} {ds : List Data}
    (htyped : LTyped [] decideExpr (curry argTys .boolean))
    (hsplit : nonEmptySplits decideExpr = true)
    (hlen : ds.length = argTys.length)
    (hfrag : ∀ d ∈ ds, DataInFragment d = true)
    (hred : ∀ p ∈ (ds.map dataLExpr).zip argTys, Red p.2 p.1)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ds.map dataLExpr))) :
    Holds (lowerProp decideExpr) ds := by
  have hf_red : Red (curry argTys .boolean) decideExpr := ltyped_red htyped hsplit
  have hlen' : (ds.map dataLExpr).length = argTys.length := by simpa using hlen
  have hcan : CanonicalBool (lapps decideExpr (ds.map dataLExpr)) :=
    red_lapps (ds.map dataLExpr) argTys .boolean decideExpr hlen' hred hf_red
  exact transport_data_holds th decideExpr ds hfrag hcons hprov hcan

theorem zip_lit_replicate_red : ∀ (ns : List Nat) (p : LExpr × Ty),
    p ∈ (ns.map LExpr.lit).zip (List.replicate ns.length .natural) → Red p.2 p.1
  | [], _, h => by simp at h
  | n :: ns, p, h => by
    simp only [List.map_cons, List.length_cons, List.replicate_succ, List.zip_cons_cons,
      List.mem_cons] at h
    rcases h with rfl | hmem
    · exact ⟨n, .refl _⟩
    · exact zip_lit_replicate_red ns p hmem

/-- **`transport_ltyped_nat_holds`**: unconditional transport for `Nat`-quantified propositions.
Requires only `LTyped [] decideExpr (curry (List.replicate ns.length .natural) .boolean)` and
`nonEmptySplits decideExpr = true` — `CanonicalBool` is discharged automatically by `ltyped_red` +
`red_lapps`. -/
theorem transport_ltyped_nat_holds
    (th : SourceTheory) {decideExpr : LExpr} (ns : List Nat)
    (htyped : LTyped [] decideExpr (curry (List.replicate ns.length .natural) .boolean))
    (hsplit : nonEmptySplits decideExpr = true)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ns.map .lit))) :
    Holds (lowerProp decideExpr) (ns.map Data.natural) := by
  have hf_red : Red (curry (List.replicate ns.length .natural) .boolean) decideExpr :=
    ltyped_red htyped hsplit
  have hlen : (ns.map LExpr.lit).length = (List.replicate ns.length Ty.natural).length := by simp
  have hcan : CanonicalBool (lapps decideExpr (ns.map .lit)) :=
    red_lapps (ns.map LExpr.lit) (List.replicate ns.length Ty.natural) .boolean decideExpr
      hlen (zip_lit_replicate_red ns) hf_red
  exact transport_holds th decideExpr ns hcons hprov hcan

/-- **`checkL_transport_nat_holds`**: executable bidirectional typechecking (`checkL`) +
`nonEmptySplits` suffices to transport provability to `Obend.Logic.Holds`. -/
theorem checkL_transport_nat_holds
    (th : SourceTheory) {decideExpr : LExpr} (ns : List Nat)
    (hcheck : checkL [] decideExpr (curry (List.replicate ns.length .natural) .boolean) = true)
    (hsplit : nonEmptySplits decideExpr = true)
    (hcons : Consistent th)
    (hprov : th.Provable (lapps decideExpr (ns.map .lit))) :
    Holds (lowerProp decideExpr) (ns.map Data.natural) :=
  transport_ltyped_nat_holds th ns (checkL_sound hcheck) hsplit hcons hprov

/-! ## 3. Transport of Conditional (`given`), Invariant (`keeps`), and Witnessed `Subtype` Claims -/

/-- Source-level conditional decision expression (`pre → body`, i.e., `if pre then body else true`). -/
def givenLExpr (pre body : LExpr) : LExpr :=
  .boolRec .boolean (.boolLit true) body pre

/-- Source-level invariant-preservation decision expression (`inv s → inv (step s)`). -/
def keepsLExpr (inv step state : LExpr) : LExpr :=
  givenLExpr (.app inv state) (.app inv (.app step state))

theorem canonicalBool_given {pre body : LExpr}
    (hpre : CanonicalBool pre) (hbody : CanonicalBool body) :
    CanonicalBool (givenLExpr pre body) := by
  obtain ⟨bp, hbp⟩ := hpre
  have s1 := ssteps_congr (fun m => .boolRec .boolean (.boolLit true) body m) (fun s => .boolRecMajor .boolean _ _ s) hbp
  cases bp with
  | false =>
    exact ⟨true, ssteps_trans s1 (.next (.boolRecFalse .boolean (.boolLit true) body) (.refl _))⟩
  | true =>
    obtain ⟨bb, hbb⟩ := hbody
    exact ⟨bb, ssteps_trans s1 (ssteps_trans (.next (.boolRecTrue .boolean (.boolLit true) body) (.refl _)) hbb)⟩

/-- **`transport_given`**: conditional claims `givenLExpr pre body` with canonical boolean parts
evaluate in `Core4` to `.boolean true` whenever `Consistent th` and `th.Provable (givenLExpr pre body)` hold. -/
theorem transport_given
    (th : SourceTheory) {pre body : LExpr}
    (hcons : Consistent th)
    (hprov : th.Provable (givenLExpr pre body))
    (hpre : CanonicalBool pre)
    (hbody : CanonicalBool body) :
    Evaluates (lowerProp (givenLExpr pre body)) (.boolean true) := by
  have hcan := canonicalBool_given hpre hbody
  have h := transport_holds th (givenLExpr pre body) [] hcons (by simpa [lapps] using hprov) (by simpa [lapps] using hcan)
  simpa [Holds, apps] using h

/-- **`transport_keeps`**: invariant preservation `keepsLExpr inv step state` transports to `Evaluates _ (.boolean true)`. -/
theorem transport_keeps
    (th : SourceTheory) {inv step state : LExpr}
    (hcons : Consistent th)
    (hprov : th.Provable (keepsLExpr inv step state))
    (hpre : CanonicalBool (.app inv state))
    (hpost : CanonicalBool (.app inv (.app step state))) :
    Evaluates (lowerProp (keepsLExpr inv step state)) (.boolean true) :=
  transport_given th hcons hprov hpre hpost

/-- **`transport_subtype_witness`**: for a constructively witnessed `Subtype` function `w : Nat → { val : Nat // P x val }`,
if projecting `"val"` from `w n` reduces to `.lit m` and `decideP n m` is provable in a consistent `th`,
then in `Core4` both:
1. `.get (.app (lowerT w) (.nat n)) "val"` evaluates to `.nat m`, and
2. `Holds (lowerProp decideP) [.natural n, .natural m]`. -/
theorem transport_subtype_witness
    (th : SourceTheory) (w decideP : LExpr) (n m : Nat)
    (hcons : Consistent th)
    (hwit : SSteps (.proj "val" (.app w (.lit n))) (.lit m))
    (hprov : th.Provable (lapps decideP [.lit n, .lit m]))
    (hcan : CanonicalBool (lapps decideP [.lit n, .lit m])) :
    Evaluates (.get (.app (lowerT w) (.nat n)) "val") (.nat m) ∧
    Holds (lowerProp decideP) [.natural n, .natural m] := by
  refine ⟨?_, ?_⟩
  · have h := lower_sound_nat hwit
    simpa [lowerT] using h
  · exact transport_holds th decideP [n, m] hcons hprov hcan

/-! ## 4. Open-Recursion Artifact Binding (`methodSupport` & T3 Override Invalidation) -/

/-- Bind a lowered Lean definition `f_lean : LExpr` to member `m` provided by `providerLayer` in a
composition `C`. -/
def methodSupport (m providerLayer : String) (f_lean : LExpr) : Support :=
  ⟨m, some (providerLayer, lowerT f_lean)⟩

/-- When `symUnfold C s m` resolves to `(providerLayer, lowerT f_lean)`, the support holds at `C`. -/
theorem methodSupport_holds
    (C : Composition) (s : Nat) (m providerLayer : String) (f_lean : LExpr)
    (hunf : symUnfold C s m = some (providerLayer, lowerT f_lean)) :
    (methodSupport m providerLayer f_lean).holds C s = true := by
  simp [Support.holds, methodSupport, hunf, optEq, Obend.Logic.termEq_refl']

/-- If a modified composition `C'` overrides member `m` with a body `u` that is not `termEq` to
`lowerT f_lean`, `Support.holds` returns `false`, blocking the Lean-backed certificate at `C'`. -/
theorem methodSupport_blocked_on_override
    (C' : Composition) (s : Nat) (m providerLayer newLayer : String) (f_lean : LExpr) (u : Term)
    (hunf : symUnfold C' s m = some (newLayer, u))
    (hdiff : Obend.Law.termEq u (lowerT f_lean) = false) :
    (methodSupport m providerLayer f_lean).holds C' s = false := by
  simp [Support.holds, methodSupport, hunf, optEq, hdiff]

/-! ## 5. Registered Certificate Format `transport@1` (`transportJudge`, `transportFormat`) and `transportSlot` -/

/-- A transport statement (`TransportObj`): a Lean-lite decision procedure `decideExpr` together
with the types `argTys` of its universally quantified arguments. -/
structure TransportObj where
  decideExpr : LExpr
  argTys : List Ty

/-- A transport certificate (`TransportCert`): the digest of `decideExpr`, the lowered `Core4`
claim term, the argument types `argTys`, and the open-recursion composition `Support`s cited by the
certificate. -/
structure TransportCert where
  digest : Nat
  claim : Term
  argTys : List Ty
  supports : List Support := []

inductive TransportClause where
  /-- the certificate's claim term is not `lowerProp o.decideExpr` -/
  | notTheLowering
  /-- the certificate's digest does not match `sourceDigest o.decideExpr` -/
  | otherSource
  /-- the certificate's argument types do not match `o.argTys` -/
  | wrongArgTys
  /-- `o.decideExpr` contains a 0-field `.split []` elimination -/
  | emptySplit
  /-- `o.decideExpr` does not typecheck at `curry o.argTys .boolean` -/
  | illTyped
  deriving DecidableEq, Repr

def transportCheck (_ : Nat) (o : TransportObj) (c : TransportCert) :
    Obend.Judge.Verdict TransportClause :=
  if Obend.Law.termEq (lowerProp o.decideExpr) c.claim then
    if c.digest == sourceDigest o.decideExpr then
      if c.argTys == o.argTys then
        if nonEmptySplits o.decideExpr then
          if checkL [] o.decideExpr (curry o.argTys .boolean) then
            .ok
          else .refused .illTyped []
        else .refused .emptySplit []
      else .refused .wrongArgTys []
    else .refused .otherSource []
  else .refused .notTheLowering []

/-- What an accepted `transport@1` certificate means: its claim is `lowerProp o.decideExpr`,
`o.decideExpr` is well-typed (`LTyped [] o.decideExpr (curry o.argTys .boolean)`) with non-empty
splits, and every provable instance in any consistent `SourceTheory` satisfies `Obend.Logic.Holds`. -/
def TransportMeaning (o : TransportObj) (c : TransportCert) : Prop :=
  c.digest = sourceDigest o.decideExpr ∧
  c.claim = lowerProp o.decideExpr ∧
  c.argTys = o.argTys ∧
  LTyped [] o.decideExpr (curry o.argTys .boolean) ∧
  nonEmptySplits o.decideExpr = true ∧
  (∀ (th : SourceTheory) (ds : List Data),
    Consistent th →
    ds.length = o.argTys.length →
    (∀ d ∈ ds, DataInFragment d = true) →
    (∀ p ∈ (ds.map dataLExpr).zip o.argTys, Red p.2 p.1) →
    th.Provable (lapps o.decideExpr (ds.map dataLExpr)) →
    Holds c.claim ds)

theorem transportCheck_ok {r : Nat} {o : TransportObj} {c : TransportCert}
    (h : transportCheck r o c = .ok) :
    c.digest = sourceDigest o.decideExpr ∧
    c.claim = lowerProp o.decideExpr ∧
    c.argTys = o.argTys ∧
    nonEmptySplits o.decideExpr = true ∧
    checkL [] o.decideExpr (curry o.argTys .boolean) = true := by
  unfold transportCheck at h
  split at h
  · rename_i ht
    split at h
    · rename_i hd
      split at h
      · rename_i ha
        split at h
        · rename_i hs
          split at h
          · rename_i hc
            exact ⟨by simpa using hd, (Obend.Law.termEq_sound ht).symm, by simpa using ha, hs, hc⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

instance transportJudge : Obend.Judge TransportObj TransportCert where
  Clause := TransportClause
  Meaning := TransportMeaning
  check := transportCheck
  sound := by
    intro r o c h
    obtain ⟨hd, ht, ha, hs, hc⟩ := transportCheck_ok h
    have htyped : LTyped [] o.decideExpr (curry o.argTys .boolean) := checkL_sound hc
    refine ⟨hd, ht, ha, htyped, hs, ?_⟩
    intro th ds hcons hlen hfrag hred hprov
    rw [ht]
    exact transport_ltyped_holds th htyped hs hlen hfrag hred hcons hprov
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := nonEmptySplits o.decideExpr = true ∧ checkL [] o.decideExpr (curry o.argTys .boolean) = true
  complete := by
    intro o ⟨hs, hc⟩ _
    refine ⟨⟨sourceDigest o.decideExpr, lowerProp o.decideExpr, o.argTys, []⟩, 0, ?_⟩
    simp [transportCheck, lowerProp, Obend.Logic.termEq_refl', hs, hc]
  mono := by intros; rfl

/-- The planted bad transport certificate: a natural literal `.lit 5` claimed as a boolean decision
procedure, refused `illTyped` when `claim` and `digest` match, or refused `notTheLowering` when the
claim term is tampered with. -/
def badTransportObj : TransportObj := ⟨.natBin .beq (.lit 5) (.lit 3), []⟩
def badTransportCert : TransportCert := ⟨0, lowerProp (.boolLit true), [], []⟩

theorem badTransport_refused :
    transportCheck 0 badTransportObj badTransportCert = .refused .notTheLowering [] := by
  have h : Obend.Law.termEq (lowerProp badTransportObj.decideExpr) badTransportCert.claim = false := by
    cases e : Obend.Law.termEq (lowerProp badTransportObj.decideExpr) badTransportCert.claim
    · rfl
    · have := Obend.Law.termEq_sound e
      simp [badTransportObj, badTransportCert, lowerProp, lowerT, NatOp.prim] at this
  simp only [transportCheck, h]; rfl

open Obend.Core.Code (tyData tyOf listData listOf) in
def transportObjJson (o : TransportObj) : Lean.Json :=
  Lean.Json.mkObj [
    ("decideExpr", sourceJson o.decideExpr),
    ("argTys", Obend.Spec.DataWire.dataJson (listData (o.argTys.map tyData)))
  ]

open Obend.Core.Code (tyData tyOf listData listOf) in
def transportObjOf (s : String) : Except String TransportObj := do
  let j ← Lean.Json.parse s
  let decJson ← j.getObjVal? "decideExpr"
  let decData ← Obend.Spec.DataWire.decodeData Obend.Logic.wireDepth decJson
  let some decExpr := lexprOf decData | throw "not the wire form of a Lean-lite decision expression"
  let tysJson ← j.getObjVal? "argTys"
  let tysData ← Obend.Spec.DataWire.decodeData Obend.Logic.wireDepth tysJson
  let some tysList := (do (← listOf tysData).mapM tyOf) | throw "not a list of Core4 types"
  pure ⟨decExpr, tysList⟩

open Obend.Core.Code (tyData tyOf listData listOf) in
def transportCertJson (c : TransportCert) : Lean.Json :=
  Lean.Json.mkObj [
    ("format", "transport@1"),
    ("digest", Lean.toJson (toString c.digest)),
    ("claim", Obend.Logic.termJson c.claim),
    ("argTys", Obend.Spec.DataWire.dataJson (listData (c.argTys.map tyData)))
  ]

open Obend.Core.Code (tyData tyOf listData listOf) in
def transportCertOf (s : String) : Except String TransportCert := do
  let j ← Lean.Json.parse s
  let dStr ← j.getObjValAs? String "digest"
  let some d := dStr.toNat? | throw "the digest is not a natural"
  let claim ← Obend.Logic.termOf (← j.getObjVal? "claim")
  let tysJson ← j.getObjVal? "argTys"
  let tysData ← Obend.Spec.DataWire.decodeData Obend.Logic.wireDepth tysJson
  let some tysList := (do (← listOf tysData).mapM tyOf) | throw "not a list of Core4 types"
  pure ⟨d, claim, tysList, []⟩

/-- **The registered format `transport@1`.** -/
def transportFormat : Obend.Judge.Format where
  name := "transport"
  version := "1"
  Obj := TransportObj
  Cert := TransportCert
  judge := transportJudge
  decodeObj := transportObjOf
  decodeCert := transportCertOf
  trust := .compiled
  regime := .decidable
  bad := (badTransportObj, badTransportCert)
  badGrade := 0
  bad_refused := ⟨_, _, badTransport_refused⟩

/-- An `Obend.Slot.Slot` over `TransportCert` candidates whose supports are open-recursion
composition `Support`s. -/
def transportSlot (o : TransportObj) : Obend.Slot.Slot Support TransportCert where
  supports c := c.supports
  judge c := transportCheck 0 o c == .ok

/-- **T3 Inheritance for `transportSlot` (`transportSlot_usable_meaning`)**: if a selected
`TransportCert` reads `.usable` at composition `C'` (self-arity `s`), then `TransportMeaning o c`
holds AND every open-recursion method support in `c.supports` unfolds at `C'` as required. -/
theorem transportSlot_usable_meaning
    {o : TransportObj} {c : TransportCert} {C' : Composition} {s : Nat}
    {ev : List (Support × Bool)}
    (h : (transportSlot o).read (Support.holds C' s) (some c) = .usable c ev) :
    TransportMeaning o c ∧ ∀ sp ∈ c.supports, symUnfold C' s sp.member = sp.unfolded := by
  have ⟨hj, hall⟩ := (Obend.Slot.read_usable_supports (transportSlot o) (Support.holds C' s) c).1 ⟨ev, h⟩
  have hok : transportCheck 0 o c = .ok := by simpa [transportSlot] using hj
  refine ⟨transportJudge.sound hok, fun sp hsp => ?_⟩
  exact optEq_sound (hall sp hsp)

/-- **Exact Override Invalidation (`transportSlot_blocked_exact`)**: if a selected `TransportCert`
reads `.blocked c' dead` at composition `C'`, `dead` is non-empty and names every support in
`c.supports` that does not hold at `C'`. -/
theorem transportSlot_blocked_exact
    {o : TransportObj} {c c' : TransportCert} {C' : Composition} {s : Nat}
    {dead : List Support}
    (h : (transportSlot o).read (Support.holds C' s) (some c) = .blocked c' dead) :
    c' = c ∧ dead ≠ [] ∧ ∀ sp, sp ∈ dead ↔ sp ∈ c.supports ∧ sp.holds C' s = false :=
  Obend.Slot.read_blocked_names (transportSlot o) (Support.holds C' s) h

/-- **End-to-End Override Blocking (`transportSlot_blocked_on_override`)**: if `c` passes
`transportCheck` and cites `methodSupport m providerLayer f_lean ∈ c.supports`, and a subclass
composition `C'` overrides `m` with a body `u` where `termEq u (lowerT f_lean) = false`, then
`(transportSlot o).read (Support.holds C' s) (some c)` is guaranteed to return `.blocked c dead`
with `methodSupport m providerLayer f_lean ∈ dead`. -/
theorem transportSlot_blocked_on_override
    {o : TransportObj} {c : TransportCert} (C' : Composition) (s : Nat)
    (m providerLayer newLayer : String) (f_lean : LExpr) (u : Term)
    (hok : transportCheck 0 o c = .ok)
    (hmem : methodSupport m providerLayer f_lean ∈ c.supports)
    (hunf : symUnfold C' s m = some (newLayer, u))
    (hdiff : Obend.Law.termEq u (lowerT f_lean) = false) :
    ∃ dead, (transportSlot o).read (Support.holds C' s) (some c) = .blocked c dead ∧
      methodSupport m providerLayer f_lean ∈ dead := by
  have hfalse : (methodSupport m providerLayer f_lean).holds C' s = false :=
    methodSupport_blocked_on_override C' s m providerLayer newLayer f_lean u hunf hdiff
  have hdead_mem : methodSupport m providerLayer f_lean ∈ (transportSlot o).dead (Support.holds C' s) c := by
    rw [Obend.Slot.mem_dead_iff]
    exact ⟨hmem, hfalse⟩
  unfold Obend.Slot.Slot.read
  have hj : (transportSlot o).judge c = true := by simp [transportSlot, hok]
  simp only [hj, ite_true]
  cases hd : (transportSlot o).dead (Support.holds C' s) c with
  | nil => rw [hd] at hdead_mem; cases hdead_mem
  | cons g t => exact ⟨g :: t, rfl, hd ▸ hdead_mem⟩

/-- **Cross-Package Disjoint Overlay Preserves `transportSlot` Usable Status (`transportSlot_usable_of_disjoint_overlay`)**:
Whenever `c` is usable at base composition `C` (`(transportSlot o).usable (Support.holds C s) c = true`)
and an overlay composition `C'` preserves `symUnfold` on every supported member `sp ∈ c.supports`
(because the overlay modifies only fields disjoint from `c.supports`), `c` remains `.usable` at `C'`
and `TransportMeaning o c` is preserved without re-running `checkL` or the theorem prover. -/
theorem transportSlot_usable_of_disjoint_overlay
    {o : TransportObj} {c : TransportCert} {C C' : Composition} {s : Nat}
    (hus : (transportSlot o).usable (Support.holds C s) c = true)
    (hdisj : ∀ sp ∈ c.supports, symUnfold C' s sp.member = symUnfold C s sp.member) :
    (transportSlot o).usable (Support.holds C' s) c = true ∧
    TransportMeaning o c ∧
    (∀ sp ∈ c.supports, symUnfold C' s sp.member = sp.unfolded) := by
  obtain ⟨hj, hall⟩ := (Obend.Slot.usable_iff (transportSlot o) (Support.holds C s) c).1 hus
  have hall' : ∀ sp ∈ (transportSlot o).supports c, Support.holds C' s sp = true := by
    intro sp hsp
    have h1 := hall sp hsp
    have heq := hdisj sp hsp
    simpa only [Support.holds, heq] using h1
  have hus' : (transportSlot o).usable (Support.holds C' s) c = true :=
    (Obend.Slot.usable_iff (transportSlot o) (Support.holds C' s) c).2 ⟨hj, hall'⟩
  have hok : transportCheck 0 o c = .ok := by simpa [transportSlot] using hj
  refine ⟨hus', transportJudge.sound hok, fun sp hsp => ?_⟩
  exact optEq_sound (hall' sp hsp)

end Obend.Lower
end
