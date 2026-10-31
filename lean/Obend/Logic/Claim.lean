module
/-
# Obend.Logic.Claim — what a claim means of an object

`review/PROGRAM-LOGIC-20261101.md` §2.7, §5.2. A `claim` in a spec is elaborated
(`Obend.Spec.Elaborate` `finishSpecification`) to closed Core4 code `λself. λsuper. λp₁ … λpₖ. body`
of type `Bool`, kept in the hidden knot field `KEY#claim#NAME`. Its judgment is

    Holds c d⃗ := Evaluates (c d⃗) (boolean true)

for closed `c` and data `d⃗` (data, not terms: a binder of a claim is a value, which is Vazou's
lesson for lazy refinement without stratified types). A claim of layer `j` of a composition `C` is
an obligation about the object: `self := C.object`, `super := C.superAt j`
(`instantiateClaim`), so it is about the *final* self (open recursion), and the super it reads is
the row beneath its own layer.

Two regimes, two judgments (Gemini's checkpoint review 20261101b §1). `Holds` is total: a ground
run or a Lean proof establishes it. An equational certificate establishes only the partial
`HoldsEq l r := ∀ o, Halts l o ↔ Halts r o` of the claim's two sides: if `review` diverged, both
sides of `repeated` would, and `Holds` would be false while the derivation stands. `Holds` follows
from `HoldsEq` with a ground observation of the left side (`holds_of_holdsEq`), which a certificate
of that regime never manufactures. The receipt names which judgment was established.

`equationSides` recognizes the three shapes Elaborate gives `==`: `binary equal` (Nat),
`binary labelEqual` (String), and the Bool β-redex `(λ$right. ifBool l' $right (not $right)) r`
with `l'` the left side shifted past `$right`.

`betaAll_lams`: a closed abstraction over `n` binders applied to `n` closed arguments reduces to its
body under the substitution `argSubst` placing the last argument at index 0. `holds_equal_of_bequiv`
reads an equation of the logic as a `Holds` fact: when `l ≈[b] r` and `l` has a natural observation,
the `==`-claim holds.
-/
public import Obend.Logic.LateBinding
public import Obend.Equiv.Quote
public import Obend.Law.Proofs.Claim
public import Obend.Law.Proofs.Machine
public import Obend.Core.Data
public import Obend.Judge.Cost
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
set_option autoImplicit false

/-! ## Application to a list of arguments -/

/-- `c a₁ … aₙ`. -/
def apps (c : Term) (args : List Term) : Term := args.foldl .app c

/-- **The judgment.** The closed claim `c`, applied to the data `ds`, evaluates to `true`. -/
def Holds (c : Term) (ds : List Data) : Prop :=
  Evaluates (apps c (ds.map Data.term)) (.boolean true)

/-- `n` binders around a body. -/
def lams : Nat → Term → Term
  | 0, b => b
  | n + 1, b => .lam (lams n b)

/-- Strip `n` binders. -/
def unlams : Nat → Term → Option Term
  | 0, b => some b
  | n + 1, .lam b => unlams n b
  | _ + 1, _ => none

theorem unlams_some : ∀ {n : Nat} {t b : Term}, unlams n t = some b → t = lams n b
  | 0, t, b, h => by simp only [unlams, Option.some.injEq] at h; subst h; rfl
  | n + 1, .lam t, b, h => by simp only [unlams] at h; simp only [lams, unlams_some h]
  | _ + 1, .bound _, _, h | _ + 1, .hole _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .mix _ _, _, h
  | _ + 1, .fix _ _, _, h | _ + 1, .specification _ _, _, h | _ + 1, .prototype _ _, _, h
  | _ + 1, .reflect _, _, h | _ + 1, .metadata _, _, h | _ + 1, .project _, _, h
  | _ + 1, .nat _, _, h | _ + 1, .boolean _, _, h | _ + 1, .label _, _, h
  | _ + 1, .binary _ _ _, _, h | _ + 1, .extend _ _, _, h | _ + 1, .record _, _, h
  | _ + 1, .get _ _, _, h | _ + 1, .ifZero _ _ _, _, h | _ + 1, .inject _ _, _, h
  | _ + 1, .case _ _, _, h | _ + 1, .ifBool _ _ _, _, h | _ + 1, .perform _, _, h
  | _ + 1, .done _, _, h => by simp [unlams] at h

/-- The substitution `n` β steps leave: the last argument at index 0, the first at `n - 1`. -/
def argSubst (args : List Term) (i : Nat) : Term :=
  if i < args.length then args.getD (args.length - 1 - i) (.bound 0) else .bound (i - args.length)

/-- `n` lifts of a substitution. -/
def liftN : Nat → (Nat → Term) → Nat → Term
  | 0, σ => σ
  | n + 1, σ => liftN n (liftSubstitution σ)

theorem lams_substitute : ∀ (n : Nat) (b : Term) (σ : Nat → Term),
    (lams n b).substitute σ = lams n (b.substitute (liftN n σ))
  | 0, _, _ => rfl
  | n + 1, b, σ => by
    simp only [lams, Term.substitute, liftN]
    rw [lams_substitute n b]

theorem liftN_apply : ∀ (n : Nat) (σ : Nat → Term) (i : Nat),
    liftN n σ i = if i < n then .bound i else (σ (i - n)).rename (· + n)
  | 0, σ, i => by
    simp only [liftN, Nat.not_lt_zero, ite_false, Nat.sub_zero, Nat.add_zero]
    rw [rename_eq_substitute]
    exact (substitute_bound _).symm
  | n + 1, σ, i => by
    rw [liftN, liftN_apply n]
    by_cases hi : i < n
    · simp [hi, Nat.lt_succ_of_lt hi]
    · by_cases he : i = n
      · subst he; simp [liftSubstitution, Term.rename]
      · have hgt : n < i := by omega
        have hn : ¬ i < n + 1 := by omega
        simp only [hi, hn, ite_false]
        obtain ⟨k, hk⟩ : ∃ k, i - n = k + 1 := ⟨i - n - 1, by omega⟩
        rw [hk]
        simp only [liftSubstitution, Obend.Core.TermTraverse.rename_comp]
        have : i - (n + 1) = k := by omega
        rw [this]
        congr 1; funext x; omega

/-- No free index. -/
abbrev Closed (t : Term) : Prop := Obend.Core.TermTraverse.Scoped 0 t

theorem closed_of_closedB {t : Term} (h : Obend.Law.closedB t = true) : Closed t := Obend.Law.scopedB_sound h

/-- A closed term is fixed by every renaming. -/
theorem closed_rename {t : Term} (h : Closed t) (f : Nat → Nat) : t.rename f = t :=
  Obend.Core.TermTraverse.scoped_rename_identity t 0 h f (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-- A closed term is fixed by every substitution. -/
theorem closed_subst {t : Term} (h : Closed t) (σ : Nat → Term) : t.substitute σ = t :=
  Obend.Core.TermTraverse.scoped_substitute_identity t 0 h σ (fun _ hi => absurd hi (Nat.not_lt_zero _))

theorem data_closed (d : Data) : Closed d.term :=
  (Obend.Core.Invariant.scoped_encode_iff 0 _).1 (Obend.Law.data_scoped d)

theorem steps_apps {f f' : Term} (h : Steps f f') : ∀ (args : List Term), Steps (apps f args) (apps f' args)
  | [] => h
  | a :: as => steps_apps (steps_app_fn a h) as

/-- **β for a closed application.** `n` binders applied to `n` closed arguments reduce to the body
under `argSubst`. -/
theorem betaAll_lams : ∀ (args : List Term) (b : Term), (∀ a ∈ args, Closed a) →
    Steps (apps (lams args.length b) args) (b.substitute (argSubst args))
  | [], b, _ => by
    simp only [apps, List.foldl_nil, List.length_nil, lams]
    rw [show argSubst [] = Term.bound from funext fun i => by simp [argSubst]]
    rw [substitute_bound]; exact .refl _
  | a :: as, b, hc => by
    have hc1 : Closed a := hc a List.mem_cons_self
    have hc2 : ∀ x ∈ as, Closed x := fun x hx => hc x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, lams, apps, List.foldl_cons]
    refine steps_trans (steps_apps (steps_one (.beta _ a)) as) ?_
    rw [instantiate_eq, lams_substitute]
    refine steps_trans (betaAll_lams as _ hc2) ?_
    rw [Obend.Core.TermTraverse.substitute_comp]
    refine (show _ = _ from congrArg (b.substitute ·) (funext fun i => ?_)) ▸ .refl _
    rw [liftN_apply]
    simp only [argSubst, List.length_cons]
    by_cases hi : i < as.length
    · simp only [hi, ite_true, Term.substitute, argSubst, Nat.lt_succ_of_lt hi]
      rw [show as.length + 1 - 1 - i = (as.length - 1 - i) + 1 by omega]
      simp
    · by_cases he : i = as.length
      · subst he
        simp only [Nat.lt_irrefl, ite_false, Nat.sub_self, single, Nat.lt_succ_self, ite_true]
        rw [closed_rename hc1, closed_subst hc1]
        simp
      · have hgt : as.length + 1 ≤ i := by omega
        simp only [hi, ite_false, show ¬ i < as.length + 1 by omega]
        obtain ⟨k, hk⟩ : ∃ k, i - as.length = k + 1 := ⟨i - as.length - 1, by omega⟩
        rw [hk]
        simp only [single, Term.rename, Term.substitute, argSubst, show ¬ k + as.length < as.length by omega,
          ite_false]
        congr 1; omega

/-! ## Data are closed and ask no metadata -/

mutual
theorem data_observes : (d : Data) → observes d.term = false
  | .natural _ | .boolean _ | .label _ => by simp [Data.term, observes]
  | .record fs => by simp only [Data.term, observes]; exact fields_observes fs
  | .variant _ p => by simp only [Data.term, observes]; exact data_observes p
theorem fields_observes : (fs : List (String × Data)) →
    ((Obend.Core.Data.fieldsTerm fs).map fun f => observes f.2).any id = false
  | [] => by simp [Obend.Core.Data.fieldsTerm]
  | (_, v) :: rest => by
    simp only [Obend.Core.Data.fieldsTerm, List.map_cons, List.any_cons, id, data_observes v, Bool.false_or]
    exact fields_observes rest
end

theorem data_obsFree (d : Data) : ObsFree d.term := obsFree_of_observes _ (data_observes d)

/-! ## Obligations -/

/-- A claim of a layer instantiated at an object: `c O (superAt j)`. -/
def instantiateClaim (c : Term) (C : Composition) (j : Nat) : Term := .app (.app c C.object) (C.superAt j)

/-- An obligation: the claim's code, the object it is about, the `super` its layer sees there, and
the types of its data parameters. -/
structure Obligation where
  claim : Term
  object : Term
  superAt : Term
  params : List Obend.Core.Ty.Ty

/-- The claim's code at the object. -/
def Obligation.term (o : Obligation) : Term := .app (.app o.claim o.object) o.superAt

/-- The obligation of claim `c` of layer `j` of `C`. -/
def Obligation.ofLayer (c : Term) (C : Composition) (j : Nat) (params : List Obend.Core.Ty.Ty) : Obligation :=
  ⟨c, C.object, C.superAt j, params⟩

theorem Obligation.ofLayer_term (c : Term) (C : Composition) (j : Nat) (params : List Obend.Core.Ty.Ty) :
    (Obligation.ofLayer c C j params).term = instantiateClaim c C j := rfl

/-- The obligation is met: at every data instance of its arity, the claim holds. -/
def Obligation.Met (o : Obligation) : Prop := ∀ ds : List Data, ds.length = o.params.length → Holds o.term ds

/-! ## The partial judgment of an equation -/

/-- The trivial observer: `≈[b]` gives the same completed runs. -/
theorem observed_sameRuns {l r : Term} (h : l ≈[.b] r) : SameRuns l r := by
  have := h Term.bound (.bound 0) ⟨fun n => .bound n, .bound 0⟩
  simpa [instantiate, Term.substitute, substitute_bound] using this


/-- **The equation judgment**: the two sides have the same completed runs. -/
def HoldsEq (l r : Term) : Prop := ∀ o, Halts l o ↔ Halts r o

theorem holdsEq_of_observed {l r : Term} (h : l ≈[.b] r) : HoldsEq l r :=
  (observed_sameRuns h).halts

/-- Which `==` the elaborator emitted. -/
inductive EqKind where
  | nat | label | bool
  deriving DecidableEq, Repr

/-- The ground observations the `==` of this kind compares. -/
def EqKind.accepts : EqKind → Observation → Bool
  | .nat, .natural _ => true
  | .label, .label _ => true
  | .bool, .boolean _ => true
  | _, _ => false

/-- `not x` as Elaborate lowers it. -/
def notTerm (x : Term) : Term := .ifBool x (.boolean false) (.boolean true)

/-- Undo the shift past one binder: `some l` when `l'` is `l` renamed past it. -/
def unshift (l' : Term) : Option Term :=
  if Obend.Judge.Cost.termBeq ((l'.substitute fun | 0 => .bound 0 | k + 1 => .bound k).rename Nat.succ) l'
  then some (l'.substitute fun | 0 => .bound 0 | k + 1 => .bound k) else none

theorem unshift_some {l' l : Term} (h : unshift l' = some l) : l' = l.rename Nat.succ := by
  unfold unshift at h
  split at h
  · rename_i hb; cases h; exact (Obend.Judge.Cost.termBeq_sound hb).symm
  · cases h

/-- The sides of an elaborated `==`, and its kind. -/
def equationSides : Term → Option (EqKind × Term × Term)
  | .binary .equal l r => some (.nat, l, r)
  | .binary .labelEqual l r => some (.label, l, r)
  | .app (.lam (.ifBool l' (.bound 0) (.ifBool (.bound 0) (.boolean false) (.boolean true)))) r =>
    (unshift l').map fun l => (.bool, l, r)
  | _ => none

/-! ## Reading an equation as a `Holds` fact -/

theorem halts_natural {t : Term} {n : Nat} (h : Halts t (.natural n)) : Steps t (.nat n) := by
  obtain ⟨v, ⟨s, _⟩, obs⟩ := h
  cases obs
  exact s

/-- `l == r` runs to `true` once `l` and `r` both run to `n`. -/
theorem equal_true {l r : Term} {n : Nat} (hl : Steps l (.nat n)) (hr : Steps r (.nat n)) :
    Evaluates (.binary .equal l r) (.boolean true) := by
  refine ⟨?_, .boolean _⟩
  refine steps_trans (steps_congr (fun x => .binary .equal x r) (fun s => .binaryLeft _ _ s) hl) ?_
  refine steps_trans (steps_congr (fun x => .binary .equal (.nat n) x) (fun s => .binaryRight _ _ (.natural n) s) hr) ?_
  exact steps_one (.primitive _ _ _ _ (.natural n) (.natural n) (by simp [primitiveResult]))

theorem halts_literal {t : Term} {o : Observation} (h : Halts t o) : ∃ v, Steps t v ∧ Observes v o := by
  obtain ⟨v, ⟨s, _⟩, obs⟩ := h
  exact ⟨v, s, obs⟩

/-- An elaborated `==` whose two sides run to one ground observation of its kind runs to `true`. -/
theorem equation_true {e l r : Term} {k : EqKind} (he : equationSides e = some (k, l, r)) {o : Observation}
    (hk : k.accepts o = true) (hl : Halts l o) (hr : Halts r o) : Evaluates e (.boolean true) := by
  obtain ⟨v, sl, ol⟩ := halts_literal hl
  obtain ⟨w, sr, orr⟩ := halts_literal hr
  unfold equationSides at he
  split at he
  · cases he
    cases ol <;> simp [EqKind.accepts] at hk
    cases orr
    exact equal_true sl sr
  · cases he
    cases ol <;> simp [EqKind.accepts] at hk
    cases orr
    refine ⟨?_, .boolean _⟩
    refine steps_trans (steps_congr (fun x => .binary .labelEqual x r) (fun s => .binaryLeft _ _ s) sl) ?_
    refine steps_trans (steps_congr (fun x => .binary .labelEqual (.label _) x) (fun s => .binaryRight _ _ (.label _) s) sr) ?_
    exact steps_one (.primitive _ _ _ _ (.label _) (.label _) (by simp [primitiveResult]))
  · rename_i l' r'
    obtain ⟨l0, hu, e'⟩ := Option.map_eq_some_iff.1 he
    cases e'
    have hs := unshift_some hu
    subst hs
    cases ol <;> simp [EqKind.accepts] at hk
    cases orr
    rename_i b
    refine ⟨.next (.beta _ _) ?_, .boolean _⟩
    rw [instantiate_eq]
    simp only [Term.substitute, single, shift_one_cancel]
    refine steps_trans (steps_congr (fun x => .ifBool x r (.ifBool r (.boolean false) (.boolean true)))
      (fun s => .ifCondition _ _ s) sl) ?_
    cases b
    · refine .next (.ifFalse _ _) ?_
      refine steps_trans (steps_congr (fun x => .ifBool x (.boolean false) (.boolean true))
        (fun s => .ifCondition _ _ s) sr) ?_
      exact steps_one (.ifFalse _ _)
    · exact .next (.ifTrue _ _) sr
  · cases he

/-- **`holds_of_holdsEq`.** A claim that reduces to an elaborated `==` whose sides are `HoldsEq`
holds once its left side has a ground observation of the equation's kind. -/
theorem holds_of_holdsEq {c e l r : Term} {ds : List Data} {k : EqKind}
    (hs : Steps (apps c (ds.map Data.term)) e) (he : equationSides e = some (k, l, r)) (hq : HoldsEq l r)
    {o : Observation} (hk : k.accepts o = true) (hl : Halts l o) : Holds c ds := by
  have ev := equation_true he hk hl ((hq o).1 hl)
  exact ⟨steps_trans hs ev.1, ev.2⟩

/-- **`holds_equal_of_bequiv`.** If `c d⃗` reduces to `l == r`, `l ≈[b] r`, and `l` has a natural
observation, the claim holds at `d⃗`. -/
theorem holds_equal_of_bequiv {c l r : Term} {ds : List Data}
    (hs : Steps (apps c (ds.map Data.term)) (.binary .equal l r)) (he : l ≈[.b] r) {n : Nat}
    (hl : Halts l (.natural n)) : Holds c ds := by
  have hr : Halts r (.natural n) := ((observed_sameRuns he).halts _).1 hl
  have e := equal_true (halts_natural hl) (halts_natural hr)
  exact ⟨steps_trans hs e.1, e.2⟩

end Obend.Logic
end
