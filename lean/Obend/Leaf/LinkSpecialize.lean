module
/-
# Obend.Leaf.LinkSpecialize — Whole-Book `link` Specialization & `GPaco` Up-To Bridge

Closes the open semantic whole-book `link` specialization gap noted in `Obend.Leaf.Static`:

1. **`GPaco` ↔ `Leaf.UpTo` Coinductive Bridge (`upToStepF`, `gpaco_upToStep_sound`)**:
   - Proves `joins_mono` (`Joins` is monotone in its base relation) and packages `Obend.Leaf.Base`
     as post-fixpoints of the monotone relational endofunctor `upToStepF : MonoRel Term`.
   - Proves that parameterized coinduction (`gpaco upToStepF ⊥ ⊥`, `paco`, and `gpaco_clo` up-to
     any compatible closure including `companion upToStepF`) implies full reflective contextual
     equivalence `≈b` (`gpaco_upToStep_sound`, `gpaco_clo_upToStep_sound`).

2. **Non-Redundant Semantic `WellPinnedBook` & Closedness Preservation (`closed_bindBookPins_link`)**:
   - Eliminates `Obend.Leaf.Served`'s redundant `Closed (bindBookPins B pins).link` premise by
     proving `all_substMemberEnvAt` and `closed_bindBookPins_link : Closed B.link →
     (∀ p ∈ pins, Closed p.code) → Closed (bindBookPins B pins).link`.
   - Defines the fuel-free semantic invariant `WellPinnedBook B pins` (`Closed B.link`,
     `LamCodes B`, and `Served B pins`) together with the single-pass boolean decider
     `wellPinnedBookB`.

3. **Whole-Book Link Equivalence & Canonical Self-Pinning (`specializeBook_link_sound`)**:
   - Proves `(specializeBook B pins).link ≈b B.link` (`specializeBook_link_sound`), contextual
     `Ahead` for the folding phase (`ahead_bind_to_specializeBook_link`), multi-argument method
     call equivalence across mutually recursive slot calls through the `fix` dispatcher knot
     (`specializeBook_call_bequiv`, `specializeBook_call_halts_iff`,
     `specializeBook_call_evaluates_obs_iff`), and canonical self-pinning soundness
     (`bookCanonicalPins_wellPinned`, `specializeBook_canonicalPins_link_sound`).

4. **Concrete Multi-Method Mutually Recursive Witness & Lying-Pin Refutation**:
   - `mutualCountdownBook`: 4-slot book (`stepSize`, `baseBonus`, mutually-recursive `evenAcc` and
     `oddAcc`) whose specialization folds `3 * 2 → 6` inside the recursive loop while preserving
     `.link ≈b` and `.evenAcc 4 ⇓ .nat 14`.
   - `lyingMutualPins`: refutes both `WellPinnedBook` and `(specializeBook ...).link ≈b B.link`.
-/

public import Obend.Paco.GPaco
public import Obend.Leaf.Static
public import Obend.Leaf.Served
public import Obend.Law.Proofs.Run

public section

namespace Obend.Leaf.LinkSpecialize

open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag encode)
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Served
open Obend.Leaf.Static
open Obend.Paco

set_option autoImplicit false

/-! ## 1. Connecting `Obend.Paco.GPaco` to `Obend.Leaf.UpTo` (`joins_mono`, `upToStepF`) -/

/-- `Joins` is monotone in its base relation `R`. -/
theorem joins_mono {R S : Rel Term} (hRS : R ≤ S) {t t' : Term} (h : Joins R t t') :
    Joins S t t' := by
  induction h with
  | base hb => exact .base (hRS _ _ hb)
  | run s _ ih => exact .run s ih
  | back s _ ih => exact .back s ih
  | hole n len _ ih => exact .hole n len ih
  | bound i => exact .bound i
  | lam _ ih => exact .lam ih
  | app _ _ i1 i2 => exact .app i1 i2
  | mix _ _ i1 i2 => exact .mix i1 i2
  | fix _ _ i1 i2 => exact .fix i1 i2
  | specification _ _ i1 i2 => exact .specification i1 i2
  | prototype _ _ i1 i2 => exact .prototype i1 i2
  | reflect _ ih => exact .reflect ih
  | metadata _ ih => exact .metadata ih
  | project _ ih => exact .project ih
  | nat n => exact .nat n
  | boolean b => exact .boolean b
  | label l => exact .label l
  | binary op _ _ i1 i2 => exact .binary op i1 i2
  | extend _ names _ i1 i2 => exact .extend i1 names i2
  | record names _ ih => exact .record names ih
  | get name _ ih => exact .get name ih
  | ifZero _ _ _ i1 i2 i3 => exact .ifZero i1 i2 i3
  | inject l _ ih => exact .inject l ih
  | case _ names _ i1 i2 => exact .case i1 names i2
  | ifBool _ _ _ i1 i2 i3 => exact .ifBool i1 i2 i3
  | perform _ ih => exact .perform ih
  | done _ ih => exact .done ih
  | split names _ _ i1 i2 => exact .split names i1 i2

/-- Monotone relational endofunctor whose post-fixpoints are `Obend.Leaf.Base`:
closed pairs `(o, f)` where each side takes at least one step to `Joins R`-related terms. -/
def upToStepF : MonoRel Term where
  F R o f :=
    Closed o ∧ Closed f ∧
      ∃ o₁ o' f₁ f', Step o o₁ ∧ Steps o₁ o' ∧ Step f f₁ ∧ Steps f₁ f' ∧ Joins R o' f'
  mono _ _ hRS _ _ h := by
    obtain ⟨ho, hf, o₁, o', f₁, f', so, sso, sf, ssf, hj⟩ := h
    exact ⟨ho, hf, o₁, o', f₁, f', so, sso, sf, ssf, joins_mono hRS hj⟩

/-- Every `Obend.Leaf.Base` relation is a post-fixpoint of `upToStepF`. -/
theorem post_of_base {R : Rel Term} (hB : Base R) : R ≤ upToStepF R := by
  intro o f hR
  exact ⟨(hB.closed hR).1, (hB.closed hR).2, hB.unfold hR⟩

/-- The greatest fixed point `upToStepF.gfp` is itself a valid `Obend.Leaf.Base`. -/
theorem base_upToStep_gfp : Base upToStepF.gfp where
  closed h := by
    have hunf := upToStepF.gfp_unfold _ _ h
    exact ⟨hunf.1, hunf.2.1⟩
  unfold h := (upToStepF.gfp_unfold _ _ h).2.2

/-- **Coinductive `GPaco` Bridge (`gpaco_upToStep_sound`)**:
Any pair established by `gpaco upToStepF ⊥ ⊥` is contextually equivalent (`≈b`). -/
theorem gpaco_upToStep_sound {o f : Term} (h : gpaco upToStepF ⊥ ⊥ o f) : o ≈b f := by
  rw [gpaco_init] at h
  exact bequiv_of_joins base_upToStep_gfp (.base h)

/-- **Up-To Closure `GPaco` Bridge (`gpaco_clo_upToStep_sound`)**:
Any pair established by `gpaco_clo upToStepF clo ⊥ ⊥` for a monotone compatible closure `clo`
is contextually equivalent (`≈b`). -/
theorem gpaco_clo_upToStep_sound {clo : Rel Term → Rel Term}
    (h_mono : CloMono clo) (h_compat : Compatible upToStepF clo) {o f : Term}
    (h : gpaco_clo upToStepF clo ⊥ ⊥ o f) : o ≈b f :=
  bequiv_of_joins base_upToStep_gfp (.base (gpaco_clo_sound upToStepF clo h_mono h_compat h))

/-! ## 2. Closedness Preservation Under `bindBookPins` (`closed_bindBookPins_link`) -/

/-- Lift a variable predicate under one de Bruijn binder (matching `Tree.All` on `.bind`). -/
abbrev liftPred (p : Nat → Prop) : Nat → Prop :=
  fun i => match i with | 0 => True | j + 1 => p j

theorem all_of_closed {v : Term} (hv : Closed v) (p : Nat → Prop) :
    Obend.Core.TermTraverse.All p v := by
  have h := Tree.all_rename (encode v) (· < 0) p hv id
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  rwa [Tree.rename_id] at h

theorem tree_all_rename_iff (tr : Tree Tag) :
    ∀ (p : Nat → Prop) (f : Nat → Nat),
      Tree.All p (Tree.rename f tr) ↔ Tree.All (fun i => p (f i)) tr := by
  induction tr using Tree.inductionOn with
  | var i =>
    intro p f
    simp only [Tree.rename, Tree.traverse, Tree.All]
  | bind body ih =>
    intro p f
    simp only [Tree.rename, Tree.traverse, Tree.All, ih]
    apply Tree.all_congr
    intro i
    cases i <;> simp [liftRename]
  | node tag children ih =>
    intro p f
    simp only [Tree.rename, Tree.traverse, Tree.All, List.mem_map]
    constructor
    · intro h c hc
      exact (ih c hc p f).1 (h (Tree.rename f c) ⟨c, hc, rfl⟩)
    · rintro h _ ⟨c, hc, rfl⟩
      exact (ih c hc p f).2 (h c hc)

theorem all_rename_add_two_iff (t : Term) :
    Obend.Core.TermTraverse.All (liftPred (liftPred (· < 0))) (t.rename (· + 2)) ↔ Closed t := by
  unfold Obend.Core.TermTraverse.All Closed Obend.Core.TermTraverse.Scoped Tree.Scoped
  rw [Obend.Core.TermTraverse.encode_rename, tree_all_rename_iff]

/-- Substituting closed member terms via `substMemberEnvAt` preserves every free-variable
predicate `Obend.Core.TermTraverse.All p` at arbitrary binder depth `d`. -/
theorem all_substMemberEnvAt {env : String → Option Term}
    (henv : ∀ m v, env m = some v → Closed v) :
    (t : Term) → (d : Nat) → (p : Nat → Prop) →
      Obend.Core.TermTraverse.All p t →
      Obend.Core.TermTraverse.All p (substMemberEnvAt d env t)
  | .hole n σ, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All, List.mem_map] at h ⊢
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact all_substMemberEnvAt henv x d p (h (encode x) ⟨x, hx, rfl⟩)
  | .bound _, _, _, h | .nat _, _, _, h | .boolean _, _, _, h | .label _, _, _, h => by
    simpa only [substMemberEnvAt] using h
  | .lam b, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All] at h ⊢
    exact all_substMemberEnvAt henv b (d + 1) (liftPred p) h
  | .app a b, d, p, h | .mix a b, d, p, h | .fix a b, d, p, h
  | .specification a b, d, p, h | .prototype a b, d, p, h
  | .binary _ a b, d, p, h | .split a _ b, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rintro _ (rfl | rfl)
    · exact all_substMemberEnvAt henv a d p (h _ (.inl rfl))
    · exact all_substMemberEnvAt henv b d p (h _ (.inr rfl))
  | .reflect a, d, p, h | .metadata a, d, p, h | .project a, d, p, h
  | .inject _ a, d, p, h | .perform a, d, p, h | .done a, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rintro _ rfl
    exact all_substMemberEnvAt henv a d p (h _ rfl)
  | .ifBool a b c, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rintro _ (rfl | rfl | rfl)
    · exact all_substMemberEnvAt henv a d p (h _ (.inl rfl))
    · exact all_substMemberEnvAt henv b d p (h _ (.inr (.inl rfl)))
    · exact all_substMemberEnvAt henv c d p (h _ (.inr (.inr rfl)))
  | .ifZero a b c, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rintro _ (rfl | rfl | rfl)
    · exact all_substMemberEnvAt henv a d p (h _ (.inl rfl))
    · exact all_substMemberEnvAt henv b d p (h _ (.inr (.inl rfl)))
    · have hbind := h (.bind (encode c)) (.inr (.inr rfl))
      simp only [Tree.All] at hbind ⊢
      exact all_substMemberEnvAt henv c (d + 1) (liftPred p) hbind
  | .extend a fs, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.mem_map] at h ⊢
    rintro _ (rfl | ⟨_, ⟨f, hf, rfl⟩, rfl⟩)
    · exact all_substMemberEnvAt henv a d p (h _ (.inl rfl))
    · simp only [Tree.All, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl
      have hfield := h (.node (.field f.1) [encode f.2]) (.inr ⟨f, hf, rfl⟩)
      simp only [Tree.All] at hfield
      exact all_substMemberEnvAt henv f.2 d p (hfield (encode f.2) (by simp))
  | .record fs, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_map] at h ⊢
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    simp only [Tree.All, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ rfl
    have hfield := h (.node (.field f.1) [encode f.2]) ⟨f, hf, rfl⟩
    simp only [Tree.All] at hfield
    exact all_substMemberEnvAt henv f.2 d p (hfield (encode f.2) (by simp))
  | .case a arms, d, p, h => by
    simp only [substMemberEnvAt, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.mem_map] at h ⊢
    rintro _ (rfl | ⟨_, ⟨arm, harm, rfl⟩, rfl⟩)
    · exact all_substMemberEnvAt henv a d p (h _ (.inl rfl))
    · simp only [Tree.All, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl
      have harm' := h (.node (.field arm.1) [.bind (encode arm.2)]) (.inr ⟨arm, harm, rfl⟩)
      simp only [Tree.All] at harm'
      have hbind := harm' (.bind (encode arm.2)) (by simp)
      simp only [Tree.All] at hbind ⊢
      exact all_substMemberEnvAt henv arm.2 (d + 1) (liftPred p) hbind
  | .get g m, d, p, h => by
    have hg : Obend.Core.TermTraverse.All p g := by
      simp only [Obend.Core.TermTraverse.All, encode, Tree.All,
        List.mem_cons, List.not_mem_nil, or_false] at h
      exact h (encode g) rfl
    have ihg := all_substMemberEnvAt henv g d p hg
    simp only [substMemberEnvAt]
    cases g with
    | bound i =>
      simp only [resolveMemberGet]
      by_cases hid : (i == d) = true
      · simp only [hid, ite_true]
        cases hm : env m with
        | some v => exact all_of_closed (henv m v hm) p
        | none => exact h
      · simp only [hid, Bool.false_eq_true, ite_false]
        exact h
    | _ =>
      simp only [resolveMemberGet, Obend.Core.TermTraverse.All, encode, Tree.All,
        List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl
      exact ihg
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hf; omega)
    | (have := sizeOf_snd_lt_of_mem harm; omega)

theorem closed_substPinsInCode {pins : List LeafPin} (hpins : ∀ p ∈ pins, Closed p.code)
    {code : Term} (hc : Closed code) : Closed (substPinsInCode pins code) := by
  have henv : ∀ m v, pinListEnv pins m = some v → Closed v := by
    intro m v hv
    obtain ⟨p, hp, _, rfl⟩ := pinListEnv_some hv
    exact hpins p hp
  cases code with
  | lam inner =>
    simp only [substPinsInCode, Closed, Obend.Core.TermTraverse.Scoped, Tree.Scoped,
      encode, Tree.All] at hc ⊢
    exact all_substMemberEnvAt henv inner 0 (liftPred (· < 0)) hc
  | _ =>
    simpa only [substPinsInCode] using all_substMemberEnvAt henv _ 0 (· < 0) hc

theorem all_call_iff_closed (d : LeafDef) :
    Obend.Core.TermTraverse.All (liftPred (liftPred (· < 0))) d.call ↔ Closed d.code := by
  cases hk : d.kind
  · simp only [LeafDef.call, hk, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      exact (all_rename_add_two_iff d.code).1 (h (encode (d.code.rename (· + 2))) (.inl rfl))
    · intro hc c hc_mem
      rcases hc_mem with rfl | rfl
      · exact (all_rename_add_two_iff d.code).2 hc
      · simp [Tree.All, liftPred]
  · simp only [LeafDef.call, hk, Obend.Core.TermTraverse.All, encode, Tree.All,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      have happ := h (.node .app [encode (d.code.rename (· + 2)), .var 1]) (.inl rfl)
      simp only [Tree.All] at happ
      exact (all_rename_add_two_iff d.code).1 (happ (encode (d.code.rename (· + 2))) (by simp))
    · intro hc c hc_mem
      rcases hc_mem with rfl | rfl
      · simp only [Tree.All, List.mem_cons, List.not_mem_nil, or_false]
        intro c' hc'_mem
        rcases hc'_mem with rfl | rfl
        · exact (all_rename_add_two_iff d.code).2 hc
        · simp [Tree.All, liftPred]
      · simp [Tree.All]

/-- **Closedness Preservation (`closed_bindBookPins_link`)**:
If `B.link` is closed and every pin's code is closed, then `(bindBookPins B pins).link` is
automatically closed — eliminating the redundant closedness premise in `Obend.Leaf.Served`. -/
theorem closed_bindBookPins_link {B : Book} {pins : List LeafPin}
    (hc : Closed B.link) (hpins : ∀ p ∈ pins, Closed p.code) :
    Closed (bindBookPins B pins).link := by
  simp only [Book.link, bindBookPins, Closed, Obend.Core.TermTraverse.Scoped, Tree.Scoped,
    encode, Tree.All, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
  have hrec := hc (.bind (.bind (.node .record
    (List.map (fun f => .node (.field f.1) [encode f.2]) (List.map BookItem.entry B.items))))) (.inl rfl)
  simp only [Tree.All, List.mem_map] at hrec
  rintro _ (rfl | rfl)
  · simp only [Tree.All, List.mem_map]
    rintro _ ⟨_, ⟨_, ⟨item, hitem, rfl⟩, rfl⟩, rfl⟩
    have holdField := hrec (.node (.field item.entry.1) [encode item.entry.2])
      ⟨item.entry, ⟨item, hitem, rfl⟩, rfl⟩
    simp only [Tree.All] at holdField
    have holdEntry : Obend.Core.TermTraverse.All (liftPred (liftPred (· < 0))) item.entry.2 :=
      holdField (encode item.entry.2) (by simp)
    cases item with
    | static m v =>
      simp only [bindBookItem, BookItem.entry, Tree.All, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl
      exact holdEntry
    | slot d =>
      simp only [bindBookItem, BookItem.entry, Tree.All, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ rfl
      have hcd : Closed d.code := (all_call_iff_closed d).1 holdEntry
      have hcd' : Closed (substPinsInCode pins d.code) := closed_substPinsInCode hpins hcd
      exact (all_call_iff_closed (bindLeafDef B.slots pins d)).2 hcd'
  · simp [Tree.All]

/-! ## 3. Clean Semantic Well-Pinnedness (`WellPinnedBook`) & Whole-Book `link` Soundness -/

/-- **Semantic Well-Pinnedness (`WellPinnedBook`)**:
A book `B` is well-pinned by `pins` when:
1. `B.link` is closed (`closedLink`),
2. Every slot definition in `B` is a lambda (`lamCodes`), and
3. Every pin in `pins` is closed and meets what `B.link` serves for its key (`served`). -/
structure WellPinnedBook (B : Book) (pins : List LeafPin) : Prop where
  closedLink : Closed B.link
  lamCodes   : LamCodes B
  served     : Served B pins

/-- Single-pass boolean decider for `WellPinnedBook` within `fuel` evaluation steps
(avoiding `specializedJudgeB`'s redundant closedness scan of `(bindBookPins B pins).link`). -/
def wellPinnedBookB (fuel : Nat) (B : Book) (pins : List LeafPin) : Bool :=
  Obend.Law.closedB B.link && B.lamCodesB && pins.all (B.servesB fuel)

theorem wellPinnedBook_of_bool {fuel : Nat} {B : Book} {pins : List LeafPin}
    (h : wellPinnedBookB fuel B pins = true) : WellPinnedBook B pins := by
  simp only [wellPinnedBookB, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hl⟩, hs⟩ := h
  refine ⟨closed_of_closedB hc, lamCodes_of_lamCodesB hl, ?_⟩
  intro p hp
  have hp' := (List.all_eq_true.1 hs) p hp
  simp only [Book.servesB, Bool.and_eq_true] at hp'
  exact ⟨closed_of_closedB hp'.1, meets_of_meetsB hp'.2⟩

theorem wellPinnedBook_of_specializedJudgeB {B : Book} {pins : List LeafPin}
    (h : specializedJudgeB B pins = true) : WellPinnedBook B pins := by
  obtain ⟨hc, _, hl, hs⟩ := served_of_judgeB h
  exact ⟨hc, hl, hs⟩

theorem wellPinnedBook_nil {B : Book} (hc : Closed B.link) (hl : LamCodes B) :
    WellPinnedBook B [] where
  closedLink := hc
  lamCodes := hl
  served := fun _ hp => nomatch hp

/-- `gpaco` proof of the unfolding-knot equivalence between `B.link` and `(bindBookPins B pins).link`. -/
theorem gpaco_bindBookPins_link {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) :
    gpaco upToStepF ⊥ ⊥ B.link (bindBookPins B pins).link := by
  have hc' : Closed (bindBookPins B pins).link :=
    closed_bindBookPins_link hw.closedLink (fun p hp => (hw.served p hp).1)
  have hbase : Base (Pair B pins) := pair_base hw.closedLink hc' hw.lamCodes hw.served
  refine gpaco_coind upToStepF (Pair B pins) ⊥ ⊥ (fun a b hab => ?_) ⟨rfl, rfl⟩
  left
  exact upToStepF.mono' Rel.le_sup_left a b (post_of_base hbase a b hab)

/-- Contextual `Ahead` reduction for the four-pass constant-folding phase on the bound book's link. -/
theorem ahead_Once_foldBook (B : Book) : Ahead B.link (foldBookOnce B).link :=
  link_ahead_mapBookCode dataPinPass ahead_dataPinPass B

/-- **Main Theorem (`specializeBook_link_sound`)**:
For any `WellPinnedBook B pins` (semantic, fuel-free), the linked specialized book is
reflectively contextually equivalent (`≈b`) to the original book's link:
`(specializeBook B pins).link ≈b B.link`. -/
theorem specializeBook_link_sound {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) :
    (specializeBook B pins).link ≈b B.link := by
  have hbind : B.link ≈b (bindBookPins B pins).link :=
    gpaco_upToStep_sound (gpaco_bindBookPins_link hw)
  have hfold : (bindBookPins B pins).link ≈b (specializeBook B pins).link := by
    rw [specializeBook_eq_foldBook_bindBookPins]
    exact link_bequiv_foldBook (bindBookPins B pins)
  exact (hbind.trans hfold).symm

/-- Decidable corollary of `specializeBook_link_sound` via `wellPinnedBookB`. -/
theorem specializeBook_link_of_bool_sound {fuel : Nat} {B : Book} {pins : List LeafPin}
    (h : wellPinnedBookB fuel B pins = true) :
    (specializeBook B pins).link ≈b B.link :=
  specializeBook_link_sound (wellPinnedBook_of_bool h)

/-- Compositional chaining: specializing sequentially under `pins₁` and `pins₂` preserves `.link ≈b`. -/
theorem specializeBook_link_trans_sound {B : Book} {pins₁ pins₂ : List LeafPin}
    (hw₁ : WellPinnedBook B pins₁)
    (hw₂ : WellPinnedBook (specializeBook B pins₁) pins₂) :
    (specializeBook (specializeBook B pins₁) pins₂).link ≈b B.link :=
  (specializeBook_link_sound hw₂).trans (specializeBook_link_sound hw₁)

/-! ## 4. Ground Observations & Multi-Argument Method Calls Across the `fix` Knot -/

/-- Context hole placing a function in `.app hole a`. -/
def appFnHole (a : Term) : Nat → Term
  | 0 => .app (.bound 0) (a.rename Nat.succ)
  | n + 1 => .bound (n + 1)

theorem instantiate_appFnHole (C x a : Term) :
    instantiate (C.substitute (appFnHole a)) x = instantiate C (.app x a) := by
  rw [instantiate_eq, instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1
  funext i
  cases i with
  | zero => simp only [appFnHole, Term.substitute, single, shift_one_cancel]
  | succ n => simp only [appFnHole, Term.substitute, single]

/-- `≈b` is a congruence in the function position of `.app`. -/
theorem bequiv_app_fn {f f' : Term} (h : f ≈b f') (a : Term) :
    .app f a ≈b .app f' a := by
  intro ρ C
  have hctx := h ρ (C.substitute (appFnHole (a.substitute ρ)))
  rw [instantiate_appFnHole, instantiate_appFnHole] at hctx
  simpa only [Term.substitute] using hctx

/-- `≈b` is a congruence across multi-argument applications `apps f args`. -/
theorem bequiv_apps_fn {f f' : Term} (h : f ≈b f') :
    ∀ (args : List Term), apps f args ≈b apps f' args
  | [] => h
  | a :: as => bequiv_apps_fn (bequiv_app_fn h a) as

/-- Observable values are uniquely determined by their ground `Observation`. -/
theorem observes_inj_term {v₁ v₂ : Term} {obs : Observation}
    (h₁ : Observes v₁ obs) (h₂ : Observes v₂ obs) : v₁ = v₂ := by
  cases h₁ <;> cases h₂ <;> rfl

/-- Member-projection contextual equivalence for `WellPinnedBook`. -/
theorem specializeBook_member_bequiv {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) :
    .get (specializeBook B pins).link m ≈b .get B.link m :=
  bequiv_get (specializeBook_link_sound hw) m

/-- Multi-argument method call contextual equivalence across the `fix` dispatcher knot. -/
theorem specializeBook_call_bequiv {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) (args : List Term) :
    apps (.get (specializeBook B pins).link m) args ≈b apps (.get B.link m) args :=
  bequiv_apps_fn (specializeBook_member_bequiv hw m) args

/-- Ground observation (`Halts`) agreement for any method call on `(specializeBook B pins).link`. -/
theorem specializeBook_call_halts_iff {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) (args : List Term) (obs : Observation) :
    Halts (apps (.get (specializeBook B pins).link m) args) obs ↔
      Halts (apps (.get B.link m) args) obs :=
  ((specializeBook_call_bequiv hw m args).sameRuns).halts obs

/-- Convergence agreement for any method call on `(specializeBook B pins).link`. -/
theorem specializeBook_call_converges_iff {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) (args : List Term) :
    Converges (apps (.get (specializeBook B pins).link m) args) ↔
      Converges (apps (.get B.link m) args) :=
  ((specializeBook_call_bequiv hw m args).sameRuns).converges

/-- Ground `Evaluates` agreement for any observable result `v` (`Observes v obs`) across
mutually recursive slot calls through the `fix` dispatcher knot. -/
theorem specializeBook_call_evaluates_obs_iff {B : Book} {pins : List LeafPin}
    (hw : WellPinnedBook B pins) (m : String) (args : List Term) {v : Term} {obs : Observation}
    (hobs : Observes v obs) :
    Evaluates (apps (.get (specializeBook B pins).link m) args) v ↔
      Evaluates (apps (.get B.link m) args) v := by
  have hhalts := specializeBook_call_halts_iff hw m args obs
  constructor
  · intro heval
    obtain ⟨v', heval', hobs'⟩ := hhalts.1 ⟨v, heval, hobs⟩
    rwa [observes_inj_term hobs' hobs] at heval'
  · intro heval
    obtain ⟨v', heval', hobs'⟩ := hhalts.2 ⟨v, heval, hobs⟩
    rwa [observes_inj_term hobs' hobs] at heval'

/-! ## 5. Canonical Self-Pinning Soundness (`bookCanonicalPins_wellPinned`) -/

theorem itemPinEntry_fst {item : BookItem} {m : String} {v : Term}
    (h : itemPinEntry item = some (m, v)) : item.entry.1 = m := by
  cases item with
  | static name val =>
    simp only [itemPinEntry, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1
  | slot d =>
    cases hk : d.kind <;> cases hc : d.code <;> simp [itemPinEntry, hk, hc] at h
    · exact h.2.1
    · cases hc' : ‹Term› <;> simp [hc'] at h
      exact h.2.1

theorem find?_nodup_of_mem {α : Type} {entries : List (String × α)} {e : String × α}
    (hnodup : (entries.map Prod.fst).Nodup) (hmem : e ∈ entries) :
    entries.find? (·.1 == e.1) = some e := by
  induction entries with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.1 hmem with rfl | htl
    · simp
    · have hne : (hd.1 == e.1) = false := by
        cases hbeq : hd.1 == e.1 with
        | false => rfl
        | true =>
          have heq : hd.1 = e.1 := beq_iff_eq.1 hbeq
          exact absurd (heq ▸ List.mem_map_of_mem (f := Prod.fst) htl) hnodup.1
      simp only [List.find?_cons, hne]
      exact ih hnodup.2 htl

theorem find?_mapFields {g : Term → Term} {entries : List (String × Term)} {m : String} :
    (mapFields g entries).find? (·.1 == m) =
      (entries.find? (·.1 == m)).map (fun f => (f.1, g f.2)) := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [mapFields, List.map_cons, List.find?_cons]
    cases h : hd.1 == m
    · exact ih
    · rfl

theorem itemPinEntry_steps {B : Book} {item : BookItem} {m : String} {v : Term}
    (h : itemPinEntry item = some (m, v)) (hv : Closed v) :
    Steps (openTerm item.entry.2 B.link (.record [])) v := by
  cases item with
  | static name val =>
    simp only [itemPinEntry, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [BookItem.entry, openTerm_succ, instantiate_eq, closed_subst hv]
    exact .refl _
  | slot d =>
    cases hk : d.kind with
    | method =>
      cases hc : d.code with
      | lam body =>
        simp only [itemPinEntry, hk, hc] at h
        split at h <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        have hlam : Closed (.lam body) := by
          simp only [Closed, Obend.Core.TermTraverse.Scoped, Tree.Scoped, encode, Tree.All]
          exact all_of_closed hv (liftPred (· < 0))
        simp only [BookItem.entry, LeafDef.call, hk, hc]
        rw [closed_rename hlam]
        simp only [openTerm, Term.substitute, selfSuper, closed_subst hlam]
        refine .next (.beta body B.link) ?_
        rw [instantiate_eq, closed_subst hv]
        exact .refl _
      | _ => simp [itemPinEntry, hk, hc] at h
    | cell =>
      cases hc : d.code with
      | lam inner =>
        cases hc' : inner with
        | lam body =>
          simp only [itemPinEntry, hk, hc, hc'] at h
          split at h <;> simp at h
          rcases h with ⟨rfl, rfl⟩
          have hlam2 : Closed (.lam (.lam body)) := by
            simp only [Closed, Obend.Core.TermTraverse.Scoped, Tree.Scoped, encode, Tree.All]
            exact all_of_closed hv (liftPred (liftPred (· < 0)))
          have hlam1 : Closed (.lam body) := by
            simp only [Closed, Obend.Core.TermTraverse.Scoped, Tree.Scoped, encode, Tree.All]
            exact all_of_closed hv (liftPred (· < 0))
          simp only [BookItem.entry, LeafDef.call, hk, hc, hc']
          rw [closed_rename hlam2]
          simp only [openTerm, Term.substitute, selfSuper, List.map_nil, closed_subst hlam2]
          refine .next (.application (.record []) (.beta (.lam body) B.link)) ?_
          rw [instantiate_eq, closed_subst hlam1]
          refine .next (.beta body (.record [])) ?_
          rw [instantiate_eq, closed_subst hv]
          exact .refl _
        | _ => simp [itemPinEntry, hk, hc, hc'] at h
      | _ => simp [itemPinEntry, hk, hc] at h

/-- **Canonical Self-Pinning Theorem (`bookCanonicalPins_wellPinned`)**:
For any book `B` with closed link, lambda slot codes, unique entry names, and closed canonical
pins, `B` semantically serves its own `bookCanonicalPins B` (`WellPinnedBook B (bookCanonicalPins B)`). -/
theorem bookCanonicalPins_wellPinned {B : Book}
    (hc : Closed B.link) (hl : LamCodes B)
    (hnodup : ((B.items.map BookItem.entry).map Prod.fst).Nodup)
    (hcp : ∀ p ∈ bookCanonicalPins B, Closed p.code) :
    WellPinnedBook B (bookCanonicalPins B) where
  closedLink := hc
  lamCodes := hl
  served := by
    intro p hp
    have hv : Closed p.code := hcp p hp
    simp only [bookCanonicalPins, List.mem_map, List.mem_filterMap] at hp
    obtain ⟨⟨m, v⟩, ⟨item, hitem, hpin⟩, rfl⟩ := hp
    refine ⟨hv, v, ?_, .refl v⟩
    have hunf : Steps B.link
        (.record (mapFields (openTerm · B.link (.record [])) (B.items.map BookItem.entry))) := by
      rw [← openTerm_record]
      exact .next (.fix _ _) (fix_unfold _ _)
    have hname : item.entry.1 = m := itemPinEntry_fst hpin
    have hfind0 : (B.items.map BookItem.entry).find? (·.1 == m) = some item.entry := by
      rw [← hname]
      exact find?_nodup_of_mem hnodup (List.mem_map_of_mem hitem)
    have hfind : (mapFields (openTerm · B.link (.record [])) (B.items.map BookItem.entry)).find?
        (·.1 == m) = some (m, openTerm item.entry.2 B.link (.record [])) := by
      rw [find?_mapFields, hfind0, Option.map_some, hname]
    exact steps_trans (Obend.Logic.steps_get m hunf)
      (steps_trans (.next (.field _ _ _ hfind) (.refl _)) (itemPinEntry_steps hpin hv))

/-- Specializing a well-formed book under its own `bookCanonicalPins B` preserves `.link ≈b`. -/
theorem specializeBook_canonicalPins_link_sound {B : Book}
    (hc : Closed B.link) (hl : LamCodes B)
    (hnodup : ((B.items.map BookItem.entry).map Prod.fst).Nodup)
    (hcp : ∀ p ∈ bookCanonicalPins B, Closed p.code) :
    (specializeBook B (bookCanonicalPins B)).link ≈b B.link :=
  specializeBook_link_sound (bookCanonicalPins_wellPinned hc hl hnodup hcp)

/-! ## 6. Multi-Method Mutually Recursive Witness & Lying-Pin Refutation -/

/-- Four-slot book with two mutually recursive methods (`evenAcc` and `oddAcc`) calling each other
across the `fix` dispatcher knot while reading `stepSize` (`3`) and `baseBonus` (`2`):
- `evenAcc n := ifZero n self.baseBonus (λpred. self.oddAcc pred)`
- `oddAcc  n := ifZero n 0 (λpred. (self.stepSize * 2) + self.evenAcc pred)` -/
def mutualCountdownBook : Book where
  items :=
    [ .slot { member := "stepSize", slot := 0, kind := .cell,
              code := .lam (.lam (.nat 3)), reads := [] }
    , .slot { member := "baseBonus", slot := 1, kind := .cell,
              code := .lam (.lam (.nat 2)), reads := [] }
    , .slot { member := "evenAcc", slot := 2, kind := .method,
              code := .lam (.lam
                (.ifZero (.bound 0)
                  (.get (.bound 1) "baseBonus")
                  (.app (.get (.bound 2) "oddAcc") (.bound 0)))),
              reads := [1, 3] }
    , .slot { member := "oddAcc", slot := 3, kind := .method,
              code := .lam (.lam
                (.ifZero (.bound 0)
                  (.nat 0)
                  (.binary .add
                    (.binary .multiply (.get (.bound 2) "stepSize") (.nat 2))
                    (.app (.get (.bound 2) "evenAcc") (.bound 0))))),
              reads := [0, 2] } ]

/-- Honest pins served by `mutualCountdownBook`: `stepSize ↦ 3`, `baseBonus ↦ 2`. -/
def honestMutualPins : List LeafPin :=
  [ ⟨.layer "stepSize", .nat 3⟩
  , ⟨.layer "baseBonus", .nat 2⟩ ]

/-- Lying pins NOT served by `mutualCountdownBook`: `stepSize ↦ 10` (dispatcher serves `3`). -/
def lyingMutualPins : List LeafPin :=
  [ ⟨.layer "stepSize", .nat 10⟩
  , ⟨.layer "baseBonus", .nat 2⟩ ]

theorem mutualCountdown_wellPinnedB_true :
    wellPinnedBookB 500 mutualCountdownBook honestMutualPins = true := by
  decide +kernel

/-- **Inhabited Witness (`WellPinnedBook`)**: `mutualCountdownBook` with `honestMutualPins`
inhabits `WellPinnedBook`. -/
theorem mutualCountdown_wellPinned_inhabited :
    WellPinnedBook mutualCountdownBook honestMutualPins :=
  wellPinnedBook_of_bool mutualCountdown_wellPinnedB_true

/-- **Inhabited Witness (`gpaco upToStepF`)**: `gpaco upToStepF ⊥ ⊥` relates `mutualCountdownBook.link`
and `(bindBookPins mutualCountdownBook honestMutualPins).link`. -/
theorem mutualCountdown_gpaco_inhabited :
    gpaco upToStepF ⊥ ⊥ mutualCountdownBook.link
      (bindBookPins mutualCountdownBook honestMutualPins).link :=
  gpaco_bindBookPins_link mutualCountdown_wellPinned_inhabited

/-- **Inhabited Witness (`gpaco_clo upToStepF`)**: `gpaco_clo upToStepF id ⊥ ⊥` is inhabited on
`mutualCountdownBook.link`. -/
theorem mutualCountdown_gpaco_clo_inhabited :
    gpaco_clo upToStepF id ⊥ ⊥ mutualCountdownBook.link
      (bindBookPins mutualCountdownBook honestMutualPins).link := by
  unfold gpaco_clo
  rw [rclo.rclo_id, composeRclo_id, Rel.sup_bot, Rel.sup_bot]
  have h := mutualCountdown_gpaco_inhabited
  simpa [gpaco] using h

/-- **Whole-Book Link Equivalence Witness**: specializing `mutualCountdownBook` under
`honestMutualPins`:
1. folds `self.stepSize * 2` to `.nat 6` inside `oddAcc` and drops `stepSize` from `oddAcc.reads` (`[2]`),
2. preserves full `.link ≈b` equivalence, and
3. evaluates `.evenAcc 4` across the mutually recursive `fix` knot to `.nat 14` (`6 + 6 + 2`). -/
theorem mutualCountdown_specialized_witness :
    (specializeBook mutualCountdownBook honestMutualPins).link ≈b mutualCountdownBook.link ∧
    ((specializeBook mutualCountdownBook honestMutualPins).defs.find? (·.member == "oddAcc")).map (·.reads) =
      some [2] ∧
    lookupBookCode (specializeBook mutualCountdownBook honestMutualPins) "oddAcc" =
      some (.lam (.lam (.ifZero (.bound 0) (.nat 0)
        (.binary .add (.nat 6) (.app (.get (.bound 2) "evenAcc") (.bound 0)))))) ∧
    Evaluates (.app (.get (specializeBook mutualCountdownBook honestMutualPins).link "evenAcc") (.nat 4))
      (.nat 14) := by
  have hequiv := specializeBook_link_sound mutualCountdown_wellPinned_inhabited
  have hrunOrig : Obend.Law.run 500 (.app (.get mutualCountdownBook.link "evenAcc") (.nat 4)) =
      some (.nat 14) := optTermEq_sound (by decide +kernel)
  have hevalOrig : Evaluates (.app (.get mutualCountdownBook.link "evenAcc") (.nat 4)) (.nat 14) :=
    Obend.Law.run_sound 500 hrunOrig
  have hevalSpec : Evaluates
      (.app (.get (specializeBook mutualCountdownBook honestMutualPins).link "evenAcc") (.nat 4))
      (.nat 14) :=
    (specializeBook_call_evaluates_obs_iff mutualCountdown_wellPinned_inhabited
      "evenAcc" [.nat 4] (.natural 14)).2 hevalOrig
  exact ⟨hequiv, by decide +kernel, optTermEq_sound (by decide +kernel), hevalSpec⟩

/-- **Semantic Refutation 1 (Lying Pin Breaks `.link ≈b`)**:
Specializing `mutualCountdownBook` under `lyingMutualPins` (`stepSize := 10` instead of `3`)
breaks behavioural equivalence `.link ≈b` (`evenAcc 4` evaluates to `42` instead of `14`). -/
theorem lyingMutualPins_breaks_link_bequiv :
    ¬ ((specializeBook mutualCountdownBook lyingMutualPins).link ≈b mutualCountdownBook.link) := by
  intro heq
  have hrunOrig : Obend.Law.run 500 (.app (.get mutualCountdownBook.link "evenAcc") (.nat 4)) =
      some (.nat 14) := optTermEq_sound (by decide +kernel)
  have hrunLying : Obend.Law.run 500
      (.app (.get (specializeBook mutualCountdownBook lyingMutualPins).link "evenAcc") (.nat 4)) =
      some (.nat 42) := optTermEq_sound (by decide +kernel)
  have hevalOrig := Obend.Law.run_sound 500 hrunOrig
  have hevalLying := Obend.Law.run_sound 500 hrunLying
  have hcall : .app (.get (specializeBook mutualCountdownBook lyingMutualPins).link "evenAcc") (.nat 4) ≈b
      .app (.get mutualCountdownBook.link "evenAcc") (.nat 4) :=
    bequiv_app_fn (bequiv_get heq "evenAcc") (.nat 4)
  obtain ⟨v, hvEval, hvObs⟩ :=
    (hcall.sameRuns.halts (.natural 42)).1 ⟨.nat 42, hevalLying, .natural 42⟩
  have hvEq : v = .nat 42 := observes_inj_term hvObs (.natural 42)
  rw [hvEq] at hvEval
  have h14_eq_42 : (Term.nat 14) = (Term.nat 42) := Obend.Law.evaluates_unique hevalOrig hvEval
  cases h14_eq_42

/-- **Semantic Refutation 2 (Lying Pin Refutes `WellPinnedBook` & `wellPinnedBookB`)**:
`lyingMutualPins` is rejected by `wellPinnedBookB` and cannot satisfy `WellPinnedBook`. -/
theorem lyingMutualPins_not_wellPinned :
    wellPinnedBookB 500 mutualCountdownBook lyingMutualPins = false ∧
    ¬ WellPinnedBook mutualCountdownBook lyingMutualPins := by
  refine ⟨by decide +kernel, fun hw => ?_⟩
  exact lyingMutualPins_breaks_link_bequiv (specializeBook_link_sound hw)

end Obend.Leaf.LinkSpecialize

end
