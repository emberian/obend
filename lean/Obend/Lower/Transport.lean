module
/-
# Obend.Lower.Transport — Proposition Lowering (`lowerProp`), `transport`, and Open-Recursion Support Binding

Connects Lean propositions and proofs over the `Obend.Lower` fragment to `Obend.Logic.Holds` and
`Obend.Logic.Support`:

1. **Refutation-Freedom vs. Total `Holds` (`stuckAxiomTheory_consistent_yet_not_holds`,
   `transport_refutation_free`, `transport_holds`)**:
   - `Consistent th` (`¬ th.Provable (.boolLit false)`) + `lower_complete_bool` proves that a provable
     decidable claim never evaluates to `.boolean false` (`transport_refutation_free`).
   - A consistent theory with an unreduced axiom (`stuckAxiomTheory`) shows `Consistent th` alone does
     not imply `Holds` without `CanonicalBool` (`stuckAxiomTheory_consistent_yet_not_holds`).
   - Adding `CanonicalBool` of the fragment's `Decidable` decision term bridges `th.Provable` +
     `Consistent th` to `Obend.Logic.Holds (lowerProp decideExpr) (ns.map Data.natural)` (`transport_holds`).

2. **Beyond `∀ x, P (f x)` (`transport_given`, `transport_keeps`, `transport_subtype_witness`)**:
   - Conditional claims (`Q x → P x`), invariant preservation (`inv s → inv (step s)`), and
     constructively witnessed `Subtype` claims (`(x : Nat) → { y : Nat // P x y }`) all transport
     through `lowerT`.

3. **Open-Recursion Artifact Binding (`methodSupport`, `methodSupport_holds`,
   `methodSupport_blocked_on_override`)**:
   - Binds a Lean fragment definition `f_lean` to a composition member `m` via `Obend.Logic.Support`
     (`⟨m, some (provider, lowerT f_lean)⟩`), so overriding `m` in a subclass layer automatically
     blocks the transported certificate (`Support.holds = false`).
-/
public import Obend.Lower.Proofs.Complete
public import Obend.Logic.Obligation
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Logic
set_option autoImplicit false

/-! ## 1. Spine Application in `LExpr` vs. `Obend.Logic.apps` -/

/-- Apply a source expression `f` to a list of argument expressions `args`. -/
def lapps (f : LExpr) (args : List LExpr) : LExpr := args.foldl .app f

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

end Obend.Lower
end
