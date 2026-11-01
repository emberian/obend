module
/-
# Obend.Lower.Proofs.Complete — Tait–Girard Reducibility, Canonicity of `LTyped`, and Converse Simulation (`lower_complete`)

1. **Refutation of untyped `lower_complete` (`raw_lower_complete_refuted`) and the `nonEmptySplits` boundary**:
   - Because `lowerT .erased = box = .record []`, eliminating `.erased` as a 0-field structure
     (`erasedElim := .split [] (.lit 42) .erased`, corresponding to `@True.rec (fun _ => Nat) 42 h`)
     evaluates in 1 step to `.nat 42` in `Core4` (`erasedElim_evaluates_in_core4`), whereas it is
     stuck in the source semantics `SStep` (`erasedElim_stuck_in_source`).
   - Moreover, because `LTyped` assigns `.emptyRow` to both `.erased` and `fieldRow []`, `erasedElim`
     is derivable in raw `LTyped` (`erasedElim_ltyped`), proving that `nonEmptySplits` (requiring
     structure `.split` eliminations to have at least one field, matching Lean structures with fields)
     is the exact syntactic condition needed to prevent `.erased` from being eliminated as a record.

2. **Tait–Girard Reducibility (`Red`) and Unconditional Canonicity of `LTyped` (`ltyped_reducible`,
   `ltyped_canonical_nat`, `ltyped_canonical_bool`)**:
   - Defines `RedBundle` (packaging `Red`, `RedRow`, and `RedVariant`) by pure structural recursion on `Ty`
     so all reducibility clauses hold by definitional equality (`rfl`).
   - Proves backward closure under `SStep` (`red_sstep`, `red_ssteps`), parallel de Bruijn substitution
     identities (`rename_comp`, `rename_subst`, `subst_rename`, `subst_comp`, `subst_bvar`,
     `subst_liftSubst_inst`), and the **Fundamental Theorem of Logical Relations** (`ltyped_reducible`):
     every `LTyped Γ e T` term with `nonEmptySplits e = true` is reducible under any reducible
     closing substitution.
   - Specializing to `Γ = []` yields unconditional source canonicity (`ltyped_canonical_nat`,
     `ltyped_canonical_bool`) and unconditional converse simulation (`lower_complete_ltyped_nat`,
     `lower_complete_ltyped_bool`, `lower_iff_ltyped_nat`, `lower_iff_ltyped_bool`).
-/
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Typing
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.Ty
set_option autoImplicit false

/-! ## 1. The `.erased` / `box` Boundary: Why Untyped `lower_complete` is Refuted -/

/-- Eliminating `.erased` as a 0-field record (`@True.rec (fun _ => Nat) 42 h`). -/
def erasedElim : LExpr := .split [] (.lit 42) .erased

/-- In `Core4`, `lowerT erasedElim = .split (.record []) [] (.nat 42)` steps to `.nat 42`. -/
theorem erasedElim_evaluates_in_core4 : Evaluates (lowerT erasedElim) (.nat 42) := by
  simp only [erasedElim, lowerT, box]
  exact ⟨.next (.splitRecord [] [] (.nat 42) [] rfl) (.refl _), .natural 42⟩

/-- In the source semantics `SStep`, `erasedElim` is stuck because `.erased` is not `.record []`. -/
theorem erasedElim_stuck_in_source : ¬ SSteps erasedElim (.lit 42) := by
  intro h
  cases h with
  | next s _ =>
    cases s with
    | splitMajor _ _ sm => cases sm

/-- **Refutation of raw untyped `lower_complete`**: without excluding `.erased` from computational
record/inductive elimination, `Evaluates (lowerT e) (.nat n)` does not imply `SSteps e (.lit n)`. -/
theorem raw_lower_complete_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), Evaluates (lowerT e) (.nat n) → SSteps e (.lit n) := by
  intro h
  exact erasedElim_stuck_in_source (h erasedElim 42 erasedElim_evaluates_in_core4)

/-- `erasedElim` is typable in raw `LTyped` when 0-field `.split []` is permitted, because both
`.erased` and `fieldRow []` have type `.emptyRow`. -/
theorem erasedElim_ltyped : LTyped [] erasedElim .natural :=
  .split (Ts := []) rfl List.nodup_nil (by simp) (.erased []) (.lit [] 42)

/-- `Witness.rec 5 Witness.mk`, read: the destructor of a field-less structure on an erased proof. -/
def erasedRec : LExpr := .split [] (.lit 5) .erased

theorem erasedRec_typed : LTyped [] erasedRec .natural :=
  .split (Ts := []) rfl List.nodup_nil (by simp) (.erased _) (.lit _ _)

theorem erasedRec_lowered : Evaluates (lowerT erasedRec) (.nat 5) := by
  simp only [erasedRec, lowerT, box]
  exact ⟨.next (.splitRecord _ _ _ [] rfl) (.refl _), .natural 5⟩

theorem erasedRec_stuck : ∀ e', ¬ SStep erasedRec e' := by
  intro e' h
  cases h with
  | splitMajor _ _ s => cases s

/-- **The converse fails on the typed fragment without `nonEmptySplits`, at an erasure.** -/
theorem lower_complete_fails :
    ¬ ∀ (e : LExpr) (n : Nat), LTyped [] e .natural → Evaluates (lowerT e) (.nat n) → SSteps e (.lit n) := by
  intro claim
  have run := claim erasedRec 5 erasedRec_typed erasedRec_lowered
  cases run with
  | next s _ => exact erasedRec_stuck _ s

/-! ## 2. `lower_complete` and Exact Bi-Simulation under Source Canonicity -/

/-- A closed source term of type `Nat` reduces to some canonical `Nat` literal. -/
def CanonicalNat (e : LExpr) : Prop := ∃ m : Nat, SSteps e (.lit m)

/-- A closed source term of type `Bool` reduces to some canonical `Bool` literal. -/
def CanonicalBool (e : LExpr) : Prop := ∃ b : Bool, SSteps e (.boolLit b)

theorem erasedElim_not_canonical : ¬ CanonicalNat erasedElim := by
  rintro ⟨m, hm⟩
  cases hm with
  | next s _ =>
    cases s with
    | splitMajor _ _ sm => cases sm

/-- **`lower_complete` at `Nat`**: if `e` is a canonical `Nat` term in the source fragment and
`lowerT e` evaluates to `.nat n` in `Core4`, then `e` reduces to `.lit n` in `SSteps`. -/
theorem lower_complete_nat {e : LExpr} {n : Nat}
    (hcan : CanonicalNat e) (hev : Evaluates (lowerT e) (.nat n)) :
    SSteps e (.lit n) := by
  obtain ⟨m, hm⟩ := hcan
  have hevm : Evaluates (lowerT e) (.nat m) := by simpa [lowerT] using lower_sound_nat hm
  have heq := evaluates_unique hevm hev
  cases heq
  exact hm

/-- **`lower_complete` at `Bool`**: if `e` is a canonical `Bool` term in the source fragment and
`lowerT e` evaluates to `.boolean b` in `Core4`, then `e` reduces to `.boolLit b` in `SSteps`. -/
theorem lower_complete_bool {e : LExpr} {b : Bool}
    (hcan : CanonicalBool e) (hev : Evaluates (lowerT e) (.boolean b)) :
    SSteps e (.boolLit b) := by
  obtain ⟨b', hb'⟩ := hcan
  have hevb' : Evaluates (lowerT e) (.boolean b') := by simpa [lowerT] using lower_sound_bool hb'
  have heq := evaluates_unique hevb' hev
  cases heq
  exact hb'

/-- **Exact `Nat` Bi-Simulation (`lower_iff_nat`)**: on canonical source terms, `Core4` evaluation
to `.nat n` and source reduction to `.lit n` coincide. -/
theorem lower_iff_nat {e : LExpr} {n : Nat} (hcan : CanonicalNat e) :
    Evaluates (lowerT e) (.nat n) ↔ SSteps e (.lit n) :=
  ⟨lower_complete_nat hcan, fun h => by simpa [lowerT] using lower_sound_nat h⟩

/-- **Exact `Bool` Bi-Simulation (`lower_iff_bool`)**: on canonical source terms, `Core4` evaluation
to `.boolean b` and source reduction to `.boolLit b` coincide. -/
theorem lower_iff_bool {e : LExpr} {b : Bool} (hcan : CanonicalBool e) :
    Evaluates (lowerT e) (.boolean b) ↔ SSteps e (.boolLit b) :=
  ⟨lower_complete_bool hcan, fun h => by simpa [lowerT] using lower_sound_bool h⟩

/-! ## 3. Structural Closure of `CanonicalNat` and `CanonicalBool` -/

theorem ssteps_trans {a b c : LExpr} (h1 : SSteps a b) (h2 : SSteps b c) : SSteps a c := by
  induction h1 with
  | refl => exact h2
  | next s _ ih => exact .next s (ih h2)

theorem ssteps_congr {a b : LExpr} (f : LExpr → LExpr)
    (hf : ∀ {x y : LExpr}, SStep x y → SStep (f x) (f y)) (h : SSteps a b) :
    SSteps (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (hf s) ih

theorem canonicalNat_lit (n : Nat) : CanonicalNat (.lit n) := ⟨n, .refl _⟩

theorem canonicalBool_lit (b : Bool) : CanonicalBool (.boolLit b) := ⟨b, .refl _⟩

theorem canonicalNat_const (name : String) {b : LExpr} (hb : CanonicalNat b) :
    CanonicalNat (.const name b) := by
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, .next (.delta name b) hn⟩

theorem canonicalBool_const (name : String) {b : LExpr} (hb : CanonicalBool b) :
    CanonicalBool (.const name b) := by
  obtain ⟨v, hv⟩ := hb
  exact ⟨v, .next (.delta name b) hv⟩

theorem canonicalNat_succ {a : LExpr} (ha : CanonicalNat a) : CanonicalNat (.natSucc a) := by
  obtain ⟨n, hn⟩ := ha
  exact ⟨n + 1, ssteps_trans (ssteps_congr .natSucc .succArg hn) (.next (.succFold n) (.refl _))⟩

theorem canonicalNat_bin (op : NatOp) (hop : op.resultTy = .natural)
    {l r : LExpr} (hl : CanonicalNat l) (hr : CanonicalNat r) :
    CanonicalNat (.natBin op l r) := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  have s1 := ssteps_congr (fun x => .natBin op x r) (fun s => .binLeft op r s) ha
  have s2 := ssteps_congr (fun y => .natBin op (.lit a) y) (fun s => .binRight op a s) hb
  cases op <;> simp [NatOp.resultTy] at hop
  · exact ⟨a + b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .add a b) (.refl _)))⟩
  · exact ⟨a - b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .sub a b) (.refl _)))⟩
  · exact ⟨a * b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .mul a b) (.refl _)))⟩
  · exact ⟨a / b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .div a b) (.refl _)))⟩
  · exact ⟨a % b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .mod a b) (.refl _)))⟩

theorem canonicalBool_bin (op : NatOp) (hop : op.resultTy = .boolean)
    {l r : LExpr} (hl : CanonicalNat l) (hr : CanonicalNat r) :
    CanonicalBool (.natBin op l r) := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  have s1 := ssteps_congr (fun x => .natBin op x r) (fun s => .binLeft op r s) ha
  have s2 := ssteps_congr (fun y => .natBin op (.lit a) y) (fun s => .binRight op a s) hb
  cases op <;> simp [NatOp.resultTy] at hop
  · exact ⟨a == b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .beq a b) (.refl _)))⟩
  · exact ⟨decide (a ≤ b), ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .ble a b) (.refl _)))⟩

/-! ## 4. De Bruijn Renaming and Substitution Algebra on `LExpr` -/

theorem liftRename_comp (f g : Nat → Nat) :
    (fun i => liftRename g (liftRename f i)) = liftRename (fun i => g (f i)) := by
  funext i; cases i <;> rfl

theorem LExpr.rename_comp : ∀ (e : LExpr) (f g : Nat → Nat),
    (e.rename f).rename g = e.rename (fun i => g (f i))
  | .bvar i, f, g => by simp [LExpr.rename]
  | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ => by simp [LExpr.rename]
  | .const n b, f, g => by simp only [LExpr.rename, LExpr.rename_comp b f g]
  | .app a b, f, g => by simp only [LExpr.rename, LExpr.rename_comp a f g, LExpr.rename_comp b f g]
  | .lam T b, f, g => by
    simp only [LExpr.rename, LExpr.rename_comp b (liftRename f) (liftRename g), liftRename_comp]
  | .letE T v b, f, g => by
    simp only [LExpr.rename, LExpr.rename_comp v f g,
      LExpr.rename_comp b (liftRename f) (liftRename g), liftRename_comp]
  | .natSucc a, f, g => by simp only [LExpr.rename, LExpr.rename_comp a f g]
  | .natBin op a b, f, g => by simp only [LExpr.rename, LExpr.rename_comp a f g, LExpr.rename_comp b f g]
  | .natRec T z s m, f, g => by
    simp only [LExpr.rename, LExpr.rename_comp z f g, LExpr.rename_comp s f g, LExpr.rename_comp m f g]
  | .boolRec T x y m, f, g => by
    simp only [LExpr.rename, LExpr.rename_comp x f g, LExpr.rename_comp y f g, LExpr.rename_comp m f g]
  | .record fs, f, g => by
    simp only [LExpr.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_comp x.2 f g]
  | .split ns F m, f, g => by simp only [LExpr.rename, LExpr.rename_comp F f g, LExpr.rename_comp m f g]
  | .proj n t, f, g => by simp only [LExpr.rename, LExpr.rename_comp t f g]
  | .inject l fs, f, g => by
    simp only [LExpr.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_comp x.2 f g]
  | .cases T arms m, f, g => by
    simp only [LExpr.rename, List.map_map, LExpr.rename_comp m f g]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_comp x.2.2 f g]
  | .recConst n T b, f, g => by
    simp only [LExpr.rename, LExpr.rename_comp b (liftRename f) (liftRename g), liftRename_comp]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem liftSubst_liftRename (f : Nat → Nat) (σ : Nat → LExpr) :
    (fun i => LExpr.liftSubst σ (liftRename f i)) = LExpr.liftSubst (fun i => σ (f i)) := by
  funext i; cases i <;> rfl

theorem LExpr.rename_subst : ∀ (e : LExpr) (f : Nat → Nat) (σ : Nat → LExpr),
    (e.rename f).subst σ = e.subst (fun i => σ (f i))
  | .bvar i, f, σ => by simp [LExpr.rename, LExpr.subst]
  | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ => by simp [LExpr.rename, LExpr.subst]
  | .const n b, f, σ => by simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst b f σ]
  | .app a b, f, σ => by simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst a f σ, LExpr.rename_subst b f σ]
  | .lam T b, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst b (liftRename f) (LExpr.liftSubst σ),
      liftSubst_liftRename]
  | .letE T v b, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst v f σ,
      LExpr.rename_subst b (liftRename f) (LExpr.liftSubst σ), liftSubst_liftRename]
  | .natSucc a, f, σ => by simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst a f σ]
  | .natBin op a b, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst a f σ, LExpr.rename_subst b f σ]
  | .natRec T z s m, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst z f σ, LExpr.rename_subst s f σ,
      LExpr.rename_subst m f σ]
  | .boolRec T x y m, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst x f σ, LExpr.rename_subst y f σ,
      LExpr.rename_subst m f σ]
  | .record fs, f, σ => by
    simp only [LExpr.rename, LExpr.subst, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_subst x.2 f σ]
  | .split ns F m, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst F f σ, LExpr.rename_subst m f σ]
  | .proj n t, f, σ => by simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst t f σ]
  | .inject l fs, f, σ => by
    simp only [LExpr.rename, LExpr.subst, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_subst x.2 f σ]
  | .cases T arms m, f, σ => by
    simp only [LExpr.rename, LExpr.subst, List.map_map, LExpr.rename_subst m f σ]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.rename_subst x.2.2 f σ]
  | .recConst n T b, f, σ => by
    simp only [LExpr.rename, LExpr.subst, LExpr.rename_subst b (liftRename f) (LExpr.liftSubst σ),
      liftSubst_liftRename]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem liftSubst_rename (σ : Nat → LExpr) (f : Nat → Nat) :
    (fun i => (LExpr.liftSubst σ i).rename (liftRename f)) =
      LExpr.liftSubst (fun i => (σ i).rename f) := by
  funext i; cases i with
  | zero => simp [LExpr.liftSubst, LExpr.rename, liftRename]
  | succ n => simp only [LExpr.liftSubst, LExpr.rename_comp]; rfl

theorem LExpr.subst_rename : ∀ (e : LExpr) (σ : Nat → LExpr) (f : Nat → Nat),
    (e.subst σ).rename f = e.subst (fun i => (σ i).rename f)
  | .bvar i, σ, f => by simp [LExpr.subst]
  | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ => by simp [LExpr.subst, LExpr.rename]
  | .const n b, σ, f => by simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename b σ f]
  | .app a b, σ, f => by simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename a σ f, LExpr.subst_rename b σ f]
  | .lam T b, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename b (LExpr.liftSubst σ) (liftRename f),
      liftSubst_rename]
  | .letE T v b, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename v σ f,
      LExpr.subst_rename b (LExpr.liftSubst σ) (liftRename f), liftSubst_rename]
  | .natSucc a, σ, f => by simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename a σ f]
  | .natBin op a b, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename a σ f, LExpr.subst_rename b σ f]
  | .natRec T z s m, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename z σ f, LExpr.subst_rename s σ f,
      LExpr.subst_rename m σ f]
  | .boolRec T x y m, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename x σ f, LExpr.subst_rename y σ f,
      LExpr.subst_rename m σ f]
  | .record fs, σ, f => by
    simp only [LExpr.subst, LExpr.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_rename x.2 σ f]
  | .split ns F m, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename F σ f, LExpr.subst_rename m σ f]
  | .proj n t, σ, f => by simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename t σ f]
  | .inject l fs, σ, f => by
    simp only [LExpr.subst, LExpr.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_rename x.2 σ f]
  | .cases T arms m, σ, f => by
    simp only [LExpr.subst, LExpr.rename, List.map_map, LExpr.subst_rename m σ f]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_rename x.2.2 σ f]
  | .recConst n T b, σ, f => by
    simp only [LExpr.subst, LExpr.rename, LExpr.subst_rename b (LExpr.liftSubst σ) (liftRename f),
      liftSubst_rename]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem liftSubst_comp (σ τ : Nat → LExpr) :
    (fun i => (LExpr.liftSubst σ i).subst (LExpr.liftSubst τ)) =
      LExpr.liftSubst (fun i => (σ i).subst τ) := by
  funext i; cases i with
  | zero => simp [LExpr.liftSubst, LExpr.subst]
  | succ n => simp only [LExpr.liftSubst, LExpr.rename_subst, LExpr.subst_rename]

theorem LExpr.subst_comp : ∀ (e : LExpr) (σ τ : Nat → LExpr),
    (e.subst σ).subst τ = e.subst (fun i => (σ i).subst τ)
  | .bvar i, σ, τ => by simp [LExpr.subst]
  | .erased, _, _ | .lit _, _, _ | .boolLit _, _, _ => by simp [LExpr.subst]
  | .const n b, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp b σ τ]
  | .app a b, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp a σ τ, LExpr.subst_comp b σ τ]
  | .lam T b, σ, τ => by
    simp only [LExpr.subst, LExpr.subst_comp b (LExpr.liftSubst σ) (LExpr.liftSubst τ), liftSubst_comp]
  | .letE T v b, σ, τ => by
    simp only [LExpr.subst, LExpr.subst_comp v σ τ,
      LExpr.subst_comp b (LExpr.liftSubst σ) (LExpr.liftSubst τ), liftSubst_comp]
  | .natSucc a, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp a σ τ]
  | .natBin op a b, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp a σ τ, LExpr.subst_comp b σ τ]
  | .natRec T z s m, σ, τ => by
    simp only [LExpr.subst, LExpr.subst_comp z σ τ, LExpr.subst_comp s σ τ, LExpr.subst_comp m σ τ]
  | .boolRec T x y m, σ, τ => by
    simp only [LExpr.subst, LExpr.subst_comp x σ τ, LExpr.subst_comp y σ τ, LExpr.subst_comp m σ τ]
  | .record fs, σ, τ => by
    simp only [LExpr.subst, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_comp x.2 σ τ]
  | .split ns F m, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp F σ τ, LExpr.subst_comp m σ τ]
  | .proj n t, σ, τ => by simp only [LExpr.subst, LExpr.subst_comp t σ τ]
  | .inject l fs, σ, τ => by
    simp only [LExpr.subst, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_comp x.2 σ τ]
  | .cases T arms m, σ, τ => by
    simp only [LExpr.subst, List.map_map, LExpr.subst_comp m σ τ]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, LExpr.subst_comp x.2.2 σ τ]
  | .recConst n T b, σ, τ => by
    simp only [LExpr.subst, LExpr.subst_comp b (LExpr.liftSubst σ) (LExpr.liftSubst τ), liftSubst_comp]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem liftSubst_bvar : LExpr.liftSubst LExpr.bvar = LExpr.bvar := by
  funext i; cases i <;> simp [LExpr.liftSubst, LExpr.rename]

theorem LExpr.subst_bvar : ∀ (e : LExpr), e.subst LExpr.bvar = e
  | .bvar _ | .erased | .lit _ | .boolLit _ => by simp [LExpr.subst]
  | .const n b => by simp only [LExpr.subst, LExpr.subst_bvar b]
  | .app a b => by simp only [LExpr.subst, LExpr.subst_bvar a, LExpr.subst_bvar b]
  | .lam T b => by simp only [LExpr.subst, liftSubst_bvar, LExpr.subst_bvar b]
  | .letE T v b => by simp only [LExpr.subst, liftSubst_bvar, LExpr.subst_bvar v, LExpr.subst_bvar b]
  | .natSucc a => by simp only [LExpr.subst, LExpr.subst_bvar a]
  | .natBin op a b => by simp only [LExpr.subst, LExpr.subst_bvar a, LExpr.subst_bvar b]
  | .natRec T z s m => by
    simp only [LExpr.subst, LExpr.subst_bvar z, LExpr.subst_bvar s, LExpr.subst_bvar m]
  | .boolRec T x y m => by
    simp only [LExpr.subst, LExpr.subst_bvar x, LExpr.subst_bvar y, LExpr.subst_bvar m]
  | .record fs => by
    simp only [LExpr.subst]
    congr 1
    have hmap : fs.map (fun x => (x.1, x.2.subst LExpr.bvar)) = fs.map id := by
      apply List.map_congr_left; intro x hx
      simp only [id, LExpr.subst_bvar x.2]
    simpa using hmap
  | .split ns F m => by simp only [LExpr.subst, LExpr.subst_bvar F, LExpr.subst_bvar m]
  | .proj n t => by simp only [LExpr.subst, LExpr.subst_bvar t]
  | .inject l fs => by
    simp only [LExpr.subst]
    congr 1
    have hmap : fs.map (fun x => (x.1, x.2.subst LExpr.bvar)) = fs.map id := by
      apply List.map_congr_left; intro x hx
      simp only [id, LExpr.subst_bvar x.2]
    simpa using hmap
  | .cases T arms m => by
    simp only [LExpr.subst, LExpr.subst_bvar m]
    congr 1
    have hmap : arms.map (fun x => (x.1, x.2.1, x.2.2.subst LExpr.bvar)) = arms.map id := by
      apply List.map_congr_left; intro x hx
      simp only [id, LExpr.subst_bvar x.2.2]
    simpa using hmap
  | .recConst n T b => by simp only [LExpr.subst, liftSubst_bvar, LExpr.subst_bvar b]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

/-- Extend a substitution `σ` with `a` at index `0`. -/
def consSubst (a : LExpr) (σ : Nat → LExpr) : Nat → LExpr
  | 0 => a
  | n + 1 => σ n

theorem subst_liftSubst_inst (body a : LExpr) (σ : Nat → LExpr) :
    (body.subst (LExpr.liftSubst σ)).inst a = body.subst (consSubst a σ) := by
  simp only [LExpr.inst, LExpr.subst_comp]
  congr 1; funext i; cases i with
  | zero => simp [LExpr.liftSubst, LExpr.subst, LExpr.single, consSubst]
  | succ n =>
    simp only [LExpr.liftSubst, LExpr.rename_subst, consSubst]
    exact LExpr.subst_bvar (σ n)

/-! ## 5. Tait–Girard Reducibility (`Red`) and Unconditional Canonicity of `LTyped` -/

/-- Every `.split` in `e` eliminates a non-empty list of structure fields (`!names.isEmpty`),
ruling out `.split [] _ .erased` (`erasedElim`). -/
def nonEmptySplits : LExpr → Bool
  | .bvar _ | .erased | .lit _ | .boolLit _ => true
  | .const _ b | .lam _ b | .natSucc b | .proj _ b => nonEmptySplits b
  | .app a b | .letE _ a b | .natBin _ a b => nonEmptySplits a && nonEmptySplits b
  | .natRec _ z s m | .boolRec _ z s m => nonEmptySplits z && nonEmptySplits s && nonEmptySplits m
  | .record fs | .inject _ fs => fs.attach.all fun ⟨f, _⟩ => nonEmptySplits f.2
  | .split names F m => !names.isEmpty && nonEmptySplits F && nonEmptySplits m
  | .cases _ arms m => nonEmptySplits m && arms.attach.all fun ⟨a, _⟩ => nonEmptySplits a.2.2
  | .recConst _ _ _ => false
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i h; have := LExpr.sizeOf_snd_lt h; omega)
    | (rename_i h; have := LExpr.sizeOf_arm_lt h; omega)

/-- Structural Tait–Girard reducibility bundle on `Ty`: packages term reducibility (`Red`),
field-row reducibility (`RedRow`), and sum-variant reducibility (`RedVariant`) in a single
structural recursion on `Ty` so that all three reduce definitionally (`rfl`). -/
def RedBundle : Ty → (LExpr → Prop) × (List (String × LExpr) → Prop) × (String → List (String × LExpr) → Prop)
  | .natural => (CanonicalNat, fun _ => False, fun _ _ => False)
  | .boolean => (CanonicalBool, fun _ => False, fun _ _ => False)
  | .emptyRow => (fun _ => True, fun fs => fs = [], fun _ _ => False)
  | .arrow .reusable .unrestricted A B =>
    let rA := (RedBundle A).1
    let rB := (RedBundle B).1
    (fun e => ∀ a, rA a → rB (.app e a), fun _ => False, fun _ _ => False)
  | .field name A tail =>
    let rA := (RedBundle A).1
    let rowA := (RedBundle A).2.1
    let rTail := (RedBundle tail).2.1
    let vTail := (RedBundle tail).2.2
    (fun e => ∃ v rest, SSteps e (.record ((name, v) :: rest)) ∧ rA v ∧ rTail rest,
     fun fs => ∃ v rest, fs = (name, v) :: rest ∧ rA v ∧ rTail rest,
     fun label fs => if name = label then rowA fs else vTail label fs)
  | .variant row =>
    let vRow := (RedBundle row).2.2
    (fun e => ∃ label fs, SSteps e (.inject label fs) ∧ vRow label fs,
     fun _ => False,
     fun _ _ => False)
  | _ => (fun _ => False, fun _ => False, fun _ _ => False)

/-- Tait–Girard reducibility predicate for the `Obend.Lower` type discipline. -/
abbrev Red (T : Ty) : LExpr → Prop := (RedBundle T).1

/-- Reducibility of a field list `fs` against a closed field row `row`. -/
abbrev RedRow (T : Ty) : List (String × LExpr) → Prop := (RedBundle T).2.1

/-- Reducibility of a variant payload `(label, fs)` against a sum row `row`. -/
abbrev RedVariant (T : Ty) : String → List (String × LExpr) → Prop := (RedBundle T).2.2

/-- Backward closure of `Red T` under a single head reduction step `SStep e e'`. -/
theorem red_sstep : ∀ (T : Ty) {e e' : LExpr}, SStep e e' → Red T e' → Red T e
  | .natural, _, _, s, ⟨n, hn⟩ => ⟨n, .next s hn⟩
  | .boolean, _, _, s, ⟨b, hb⟩ => ⟨b, .next s hb⟩
  | .emptyRow, _, _, _, _ => trivial
  | .arrow .reusable .unrestricted _ B, _, _, s, h =>
    fun a ha => red_sstep B (.appFun a s) (h a ha)
  | .field _ _ _, _, _, s, ⟨v, rest, hr, hv, hrest⟩ =>
    ⟨v, rest, .next s hr, hv, hrest⟩
  | .variant _, _, _, s, ⟨label, fs, hr, hvar⟩ =>
    ⟨label, fs, .next s hr, hvar⟩
  | .label, _, _, _, h | .variable _, _, _, _, h | .specification _ _, _, _, _, h
  | .prototype _ _, _, _, _, h | .custody _, _, _, _, h | .computation _ _ _, _, _, _, h
  | .arrow .once _ _ _, _, _, _, h | .arrow .reusable .erased _ _, _, _, _, h
  | .arrow .reusable .affine _ _, _, _, _, h | .arrow .reusable .linear _ _, _, _, _, h =>
    False.elim h

/-- Backward closure of `Red T` under multi-step reduction `SSteps e e'`. -/
theorem red_ssteps (T : Ty) {e e' : LExpr} (h : SSteps e e') (he' : Red T e') : Red T e := by
  induction h with
  | refl => exact he'
  | next s _ ih => exact red_sstep T s (ih he')

/-- A closing substitution `σ` is reducible for context `Γ` when every bound variable in `Γ`
maps to a reducible term of its type. -/
def SubstRed (Γ : List Ty) (σ : Nat → LExpr) : Prop :=
  ∀ i T, Γ[i]? = some T → Red T (σ i)

theorem substRed_nil : SubstRed [] LExpr.bvar := by
  intro i T hi; simp at hi

theorem substRed_cons {Γ : List Ty} {A : Ty} {a : LExpr} {σ : Nat → LExpr}
    (ha : Red A a) (hσ : SubstRed Γ σ) : SubstRed (A :: Γ) (consSubst a σ) := by
  intro i T hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi; exact ha
  | succ n =>
    simp only [List.getElem?_cons_succ] at hi
    exact hσ n T hi

/-- Constructing `RedRow` from a typed list of fields. -/
theorem redRow_of_fields (σ : Nat → LExpr) :
    ∀ (fs : List (String × LExpr)) (Ts : List Ty),
      fs.length = Ts.length →
      (∀ p ∈ fs.zip Ts, Red p.2 (p.1.2.subst σ)) →
      RedRow (fieldRow ((fs.map Prod.fst).zip Ts)) (fs.map fun x => (x.1, x.2.subst σ))
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h
  | (name, e) :: fs, T :: Ts, hl, hred => by
    refine ⟨e.subst σ, fs.map fun x => (x.1, x.2.subst σ), rfl, ?_, ?_⟩
    · exact hred ((name, e), T) (by simp)
    · exact redRow_of_fields σ fs Ts (by simpa using hl) (fun p hp => hred p (by simp [hp]))

/-- Looking up a field in `row.lookup [] fuel name` extracts a reducible value from `RedRow row fs`. -/
theorem redRow_lookup :
    ∀ (fuel : Nat) (row : Ty) (fs : List (String × LExpr)) (name : String) (T : Ty),
      row.lookup [] fuel name = some T →
      RedRow row fs →
      ∃ v, fs.find? (fun f => f.1 == name) = some (name, v) ∧ Red T v
  | 0, _, _, _, _, hk, _ => by simp [Ty.lookup] at hk
  | fuel + 1, .field prior member tail, fs, name, T, hk, hrow => by
    obtain ⟨v, rest, rfl, hv, hrest⟩ := hrow
    simp only [Ty.lookup] at hk
    by_cases h : prior = name
    · subst h
      simp only [ite_true, Option.some.injEq] at hk
      subst hk
      simp only [List.find?, beq_self_eq_true]
      exact ⟨v, rfl, hv⟩
    · simp only [h, ite_false] at hk
      have hne : (prior == name) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.find?, hne]
      exact redRow_lookup fuel tail rest name T hk hrest
  | fuel + 1, .natural, _, _, _, hk, _ | fuel + 1, .label, _, _, _, hk, _
  | fuel + 1, .boolean, _, _, _, hk, _ | fuel + 1, .variable _, _, _, _, hk, _
  | fuel + 1, .arrow _ _ _ _, _, _, _, hk, _ | fuel + 1, .emptyRow, _, _, _, hk, _
  | fuel + 1, .specification _ _, _, _, _, hk, _ | fuel + 1, .prototype _ _, _, _, _, hk, _
  | fuel + 1, .custody _, _, _, _, hk, _ | fuel + 1, .variant _, _, _, _, hk, _
  | fuel + 1, .computation _ _ _, _, _, _, hk, _ => by simp [Ty.lookup] at hk

theorem splitValues_cons_of_not_mem {α : Type} (n : String) (v : α) (rest : List (String × α)) :
    ∀ (ns : List String), n ∉ ns → splitValues ((n, v) :: rest) ns = splitValues rest ns
  | [], _ => rfl
  | k :: ns, hn => by
    have hnk : n ≠ k := fun h => hn (by simp [h])
    have hne : (n == k) = false := beq_eq_false_iff_ne.mpr hnk
    have hn' : n ∉ ns := fun h => hn (by simp [h])
    simp only [splitValues, List.find?, hne, splitValues_cons_of_not_mem n v rest ns hn']

/-- `splitValues` on `RedRow (fieldRow (names.zip Ts)) fs` with `names.Nodup` extracts reducible
arguments and preserves `Red R` when applied along `F.spine`. -/
theorem redRow_split_spine {R : Ty} :
    ∀ (names : List String) (Ts : List Ty) (fs : List (String × LExpr)) (F : LExpr),
      names.length = Ts.length →
      names.Nodup →
      RedRow (fieldRow (names.zip Ts)) fs →
      Red (curry Ts R) F →
      ∃ values, splitValues fs names = some values ∧ Red R (F.spine values)
  | [], [], _, F, _, _, _, hF => ⟨[], rfl, hF⟩
  | [], _ :: _, _, _, h, _, _, _ | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | n :: ns, T :: Ts, _, F, hl, hnd, ⟨v, rest, rfl, hv, hrest⟩, hF => by
    simp only [List.nodup_cons] at hnd
    have hFv : Red (curry Ts R) (.app F v) := hF v hv
    obtain ⟨vs, hvs, hspine⟩ := redRow_split_spine ns Ts rest (.app F v) (by simpa using hl) hnd.2 hrest hFv
    refine ⟨v :: vs, ?_, hspine⟩
    simp only [splitValues, List.find?, beq_self_eq_true,
      splitValues_cons_of_not_mem n v rest ns hnd.1, hvs]; rfl

/-- Looking up `label` in `row` lifts `RedRow` to `RedVariant row label fs`. -/
theorem redVariant_of_lookup :
    ∀ (fuel : Nat) (row member : Ty) (label : String) (fs : List (String × LExpr)),
      row.lookup [] fuel label = some member →
      RedRow member fs →
      RedVariant row label fs
  | 0, _, _, _, _, hk, _ => by simp [Ty.lookup] at hk
  | fuel + 1, .field prior m tail, member, label, fs, hk, hrow => by
    simp only [Ty.lookup] at hk
    simp only [RedVariant, RedBundle]
    by_cases h : prior = label
    · subst h
      simp only [ite_true, Option.some.injEq] at hk ⊢
      subst hk; exact hrow
    · simp only [h, ite_false] at hk ⊢
      exact redVariant_of_lookup fuel tail member label fs hk hrow
  | fuel + 1, .natural, _, _, _, hk, _ | fuel + 1, .label, _, _, _, hk, _
  | fuel + 1, .boolean, _, _, _, hk, _ | fuel + 1, .variable _, _, _, _, hk, _
  | fuel + 1, .arrow _ _ _ _, _, _, _, hk, _ | fuel + 1, .emptyRow, _, _, _, hk, _
  | fuel + 1, .specification _ _, _, _, _, hk, _ | fuel + 1, .prototype _ _, _, _, _, hk, _
  | fuel + 1, .custody _, _, _, _, hk, _ | fuel + 1, .variant _, _, _, _, hk, _
  | fuel + 1, .computation _ _ _, _, _, _, hk, _ => by simp [Ty.lookup] at hk

/-- Eliminating `RedVariant (armsRow arms sig) label fs` finds the matching arm and produces a
reducible spine application. -/
theorem redVariant_cases {R : Ty} (σ : Nat → LExpr) :
    ∀ (arms : List (String × List String × LExpr)) (sig : List (List Ty))
      (label : String) (fs : List (String × LExpr)),
      arms.length = sig.length →
      (∀ p ∈ arms.zip sig, p.1.2.1.length = p.2.length) →
      (∀ p ∈ arms.zip sig, p.1.2.1.Nodup) →
      (∀ p ∈ arms.zip sig, Red (curry p.2 R) (p.1.2.2.subst σ)) →
      RedVariant (armsRow arms sig) label fs →
      ∃ names minor values,
        (arms.map fun x => (x.1, x.2.1, x.2.2.subst σ)).find? (fun arm => arm.1 == label) =
          some (label, names, minor) ∧
        splitValues fs names = some values ∧
        Red R (minor.spine values)
  | [], [], _, _, _, _, _, _, hvar => False.elim hvar
  | [], _ :: _, _, _, h, _, _, _, _ | _ :: _, [], _, _, h, _, _, _, _ => by simp at h
  | (armLabel, names, M) :: arms, Ts :: sig, label, fs, hl, hlen, hnd, harms, hvar => by
    simp only [armsRow, RedVariant, RedBundle] at hvar
    by_cases h : armLabel = label
    · subst h
      simp only [ite_true] at hvar
      have hlen0 := hlen ((armLabel, names, M), Ts) (by simp)
      have hnd0 := hnd ((armLabel, names, M), Ts) (by simp)
      have hM0 := harms ((armLabel, names, M), Ts) (by simp)
      obtain ⟨values, hvs, hspine⟩ := redRow_split_spine names Ts fs (M.subst σ) hlen0 hnd0 hvar hM0
      refine ⟨names, M.subst σ, values, ?_, hvs, hspine⟩
      simp
    · simp only [h, ite_false] at hvar
      have hne : (armLabel == label) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.map_cons, List.find?, hne]
      exact redVariant_cases σ arms sig label fs (by simpa using hl)
        (fun p hp => hlen p (by simp [hp]))
        (fun p hp => hnd p (by simp [hp]))
        (fun p hp => harms p (by simp [hp]))
        hvar

/-- **Fundamental Theorem of Logical Relations (`ltyped_reducible`)**: every `LTyped Γ e T` term
with `nonEmptySplits e = true` is Tait–Girard reducible under any reducible substitution `σ` for `Γ`. -/
theorem ltyped_reducible {Γ : List Ty} {e : LExpr} {T : Ty}
    (h : LTyped Γ e T) (hne : nonEmptySplits e = true)
    {σ : Nat → LExpr} (hσ : SubstRed Γ σ) :
    Red T (e.subst σ) := by
  induction h generalizing σ with
  | bvar hi =>
    simp only [LExpr.subst]
    exact hσ _ _ hi
  | erased _ =>
    trivial
  | const _ ih =>
    simp only [nonEmptySplits] at hne
    simp only [LExpr.subst]
    exact red_sstep _ (.delta _ _) (ih hne hσ)
  | app _ _ _ ihf iha =>
    simp only [nonEmptySplits, Bool.and_eq_true] at hne
    simp only [LExpr.subst]
    exact (ihf hne.1 hσ) _ (iha hne.2 hσ)
  | @lam Γ A B body _ _ ih =>
    simp only [nonEmptySplits] at hne
    simp only [LExpr.subst]
    intro a ha
    have hstep : SStep (.app (.lam A (body.subst (LExpr.liftSubst σ))) a)
        ((body.subst (LExpr.liftSubst σ)).inst a) := .beta _ _ _
    refine red_sstep B hstep ?_
    rw [subst_liftSubst_inst]
    exact ih hne (substRed_cons ha hσ)
  | @letE Γ A B v body _ _ _ ihv ihb =>
    simp only [nonEmptySplits, Bool.and_eq_true] at hne
    simp only [LExpr.subst]
    have hv := ihv hne.1 hσ
    have hstep : SStep (.letE A (v.subst σ) (body.subst (LExpr.liftSubst σ)))
        ((body.subst (LExpr.liftSubst σ)).inst (v.subst σ)) := .zeta _ _ _
    refine red_sstep B hstep ?_
    rw [subst_liftSubst_inst]
    exact ihb hne.2 (substRed_cons hv hσ)
  | lit _ n =>
    simp only [LExpr.subst]
    exact canonicalNat_lit n
  | natSucc _ ih =>
    simp only [nonEmptySplits] at hne
    simp only [LExpr.subst]
    exact canonicalNat_succ (ih hne hσ)
  | natBin op _ _ ihl ihr =>
    simp only [nonEmptySplits, Bool.and_eq_true] at hne
    simp only [LExpr.subst]
    have hl := ihl hne.1 hσ
    have hr := ihr hne.2 hσ
    cases op
    · exact canonicalNat_bin .add rfl hl hr
    · exact canonicalNat_bin .sub rfl hl hr
    · exact canonicalNat_bin .mul rfl hl hr
    · exact canonicalNat_bin .div rfl hl hr
    · exact canonicalNat_bin .mod rfl hl hr
    · exact canonicalBool_bin .beq rfl hl hr
    · exact canonicalBool_bin .ble rfl hl hr
  | boolLit _ b =>
    simp only [LExpr.subst]
    exact canonicalBool_lit b
  | @natRec Γ T z s m _ _ _ _ ihz ihs ihm =>
    simp only [nonEmptySplits, Bool.and_eq_true] at hne
    simp only [LExpr.subst]
    have hz := ihz hne.1.1 hσ
    have hs := ihs hne.1.2 hσ
    obtain ⟨n, hn⟩ := ihm hne.2 hσ
    have smaj := ssteps_congr (fun x => .natRec T (z.subst σ) (s.subst σ) x)
      (fun st => .natRecMajor T (z.subst σ) (s.subst σ) st) hn
    refine red_ssteps T smaj ?_
    clear hn smaj
    induction n with
    | zero =>
      exact red_sstep T (.natRecZero T (z.subst σ) (s.subst σ)) hz
    | succ k ihk =>
      exact red_sstep T (.natRecSucc T (z.subst σ) (s.subst σ) k)
        (hs (.lit k) (canonicalNat_lit k) _ ihk)
  | @boolRec Γ T x y m _ _ _ ihx ihy ihm =>
    simp only [nonEmptySplits, Bool.and_eq_true] at hne
    simp only [LExpr.subst]
    have hx := ihx hne.1.1 hσ
    have hy := ihy hne.1.2 hσ
    obtain ⟨b, hb⟩ := ihm hne.2 hσ
    have smaj := ssteps_congr (fun c => .boolRec T (x.subst σ) (y.subst σ) c)
      (fun st => .boolRecMajor T (x.subst σ) (y.subst σ) st) hb
    refine red_ssteps T smaj ?_
    cases b with
    | false => exact red_sstep T (.boolRecFalse T (x.subst σ) (y.subst σ)) hx
    | true => exact red_sstep T (.boolRecTrue T (x.subst σ) (y.subst σ)) hy
  | @record Γ fs Ts hl _ _ _ ih =>
    simp only [nonEmptySplits, List.all_eq_true] at hne
    simp only [LExpr.subst]
    have hrow : RedRow (fieldRow ((fs.map Prod.fst).zip Ts)) (fs.map fun x => (x.1, x.2.subst σ)) :=
      redRow_of_fields σ fs Ts hl (fun p hp =>
        ih p hp (hne ⟨p.1, (List.of_mem_zip hp).1⟩ (List.mem_attach _ _)) hσ)
    cases fs with
    | nil =>
      cases Ts with
      | nil => trivial
      | cons _ _ => simp at hl
    | cons f rest =>
      cases Ts with
      | nil => simp at hl
      | cons T0 Ts' =>
        obtain ⟨v, r, heq, hv, hr⟩ := hrow
        exact ⟨v, r, heq ▸ .refl _, hv, hr⟩
  | @split Γ names F m Ts R hl nd _ _ _ ihm ihF =>
    simp only [nonEmptySplits, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hne
    simp only [LExpr.subst]
    have hm := ihm hne.2 hσ
    have hF := ihF hne.1.2 hσ
    cases names with
    | nil => exact False.elim (hne.1.1 rfl)
    | cons n0 ns =>
      cases Ts with
      | nil => simp at hl
      | cons T0 Ts' =>
        obtain ⟨v0, rest0, smaj, hv0, hrest0⟩ := hm
        have hrow : RedRow (fieldRow ((n0 :: ns).zip (T0 :: Ts'))) ((n0, v0) :: rest0) :=
          ⟨v0, rest0, rfl, hv0, hrest0⟩
        obtain ⟨values, hvs, hspine⟩ := redRow_split_spine (n0 :: ns) (T0 :: Ts') ((n0, v0) :: rest0)
          (F.subst σ) hl nd hrow hF
        have s1 := ssteps_congr (fun x => .split (n0 :: ns) (F.subst σ) x)
          (fun st => .splitMajor (n0 :: ns) (F.subst σ) st) smaj
        exact red_ssteps R s1 (red_sstep R (.splitRecord (n0 :: ns) (F.subst σ) ((n0, v0) :: rest0) values hvs) hspine)
  | @proj Γ t row T name fuel _ hk ih =>
    simp only [nonEmptySplits] at hne
    simp only [LExpr.subst]
    have ht := ih hne hσ
    cases fuel with
    | zero => simp [Ty.lookup] at hk
    | succ fuel' =>
      cases row with
      | field prior member tail =>
        obtain ⟨v0, rest0, starget, hv0, hrest0⟩ := ht
        have hrow : RedRow (.field prior member tail) ((prior, v0) :: rest0) :=
          ⟨v0, rest0, rfl, hv0, hrest0⟩
        obtain ⟨v, hfind, hv⟩ := redRow_lookup (fuel' + 1) (.field prior member tail)
          ((prior, v0) :: rest0) name T hk hrow
        have s1 := ssteps_congr (fun x => .proj name x) (fun st => .projTarget name st) starget
        exact red_ssteps T s1 (red_sstep T (.projRecord name ((prior, v0) :: rest0) v hfind) hv)
      | _ => simp [Ty.lookup] at hk
  | @inject Γ label fs Ts row fuel hl _ _ _ hk ih =>
    simp only [nonEmptySplits, List.all_eq_true] at hne
    simp only [LExpr.subst]
    have hrow := redRow_of_fields σ fs Ts hl (fun p hp =>
      ih p hp (hne ⟨p.1, (List.of_mem_zip hp).1⟩ (List.mem_attach _ _)) hσ)
    exact ⟨label, fs.map fun x => (x.1, x.2.subst σ), .refl _,
      redVariant_of_lookup fuel row _ label _ hk hrow⟩
  | @cases Γ R arms sig m hl _ _ hlen hnd _ _ _ ihm iharms =>
    simp only [nonEmptySplits, Bool.and_eq_true, List.all_eq_true] at hne
    simp only [LExpr.subst]
    obtain ⟨label, fs, smaj, hvar⟩ := ihm hne.1 hσ
    obtain ⟨names, minor, values, hfind, hvs, hspine⟩ :=
      redVariant_cases σ arms sig label fs hl hlen hnd
        (fun p hp => iharms p hp (hne.2 ⟨p.1, (List.of_mem_zip hp).1⟩ (List.mem_attach _ _)) hσ) hvar
    have s1 := ssteps_congr
      (fun x => .cases R (arms.map fun a => (a.1, a.2.1, a.2.2.subst σ)) x)
      (fun st => .casesMajor R (arms.map fun a => (a.1, a.2.1, a.2.2.subst σ)) st) smaj
    exact red_ssteps R s1 (red_sstep R (.casesInject R _ label fs names minor values hfind hvs) hspine)
  | recConst _ _ _ =>
    simp [nonEmptySplits] at hne

/-- Every closed `LTyped [] e T` term with `nonEmptySplits e = true` is reducible (`Red T e`). -/
theorem ltyped_red {e : LExpr} {T : Ty}
    (h : LTyped [] e T) (hne : nonEmptySplits e = true) : Red T e := by
  have hsub := ltyped_reducible h hne substRed_nil
  rwa [LExpr.subst_bvar] at hsub

/-- **Unconditional `Nat` Canonicity of `LTyped` (`ltyped_canonical_nat`)**: every closed
`LTyped [] e .natural` term with `nonEmptySplits e = true` reduces to a `Nat` literal in `SSteps`. -/
theorem ltyped_canonical_nat {e : LExpr}
    (h : LTyped [] e .natural) (hne : nonEmptySplits e = true) : CanonicalNat e :=
  ltyped_red h hne

/-- **Unconditional `Bool` Canonicity of `LTyped` (`ltyped_canonical_bool`)**: every closed
`LTyped [] e .boolean` term with `nonEmptySplits e = true` reduces to a `Bool` literal in `SSteps`. -/
theorem ltyped_canonical_bool {e : LExpr}
    (h : LTyped [] e .boolean) (hne : nonEmptySplits e = true) : CanonicalBool e :=
  ltyped_red h hne

/-- **Unconditional `lower_complete` at `Nat` for `LTyped` (`lower_complete_ltyped_nat`)**:
no external `CanonicalNat` hypothesis is required! -/
theorem lower_complete_ltyped_nat {e : LExpr} {n : Nat}
    (h : LTyped [] e .natural) (hne : nonEmptySplits e = true)
    (hev : Evaluates (lowerT e) (.nat n)) :
    SSteps e (.lit n) :=
  lower_complete_nat (ltyped_canonical_nat h hne) hev

/-- **Unconditional `lower_complete` at `Bool` for `LTyped` (`lower_complete_ltyped_bool`)**:
no external `CanonicalBool` hypothesis is required! -/
theorem lower_complete_ltyped_bool {e : LExpr} {b : Bool}
    (h : LTyped [] e .boolean) (hne : nonEmptySplits e = true)
    (hev : Evaluates (lowerT e) (.boolean b)) :
    SSteps e (.boolLit b) :=
  lower_complete_bool (ltyped_canonical_bool h hne) hev

/-- **Unconditional `Nat` Bi-Simulation for `LTyped` (`lower_iff_ltyped_nat`)**. -/
theorem lower_iff_ltyped_nat {e : LExpr} {n : Nat}
    (h : LTyped [] e .natural) (hne : nonEmptySplits e = true) :
    Evaluates (lowerT e) (.nat n) ↔ SSteps e (.lit n) :=
  lower_iff_nat (ltyped_canonical_nat h hne)

/-- **Unconditional `Bool` Bi-Simulation for `LTyped` (`lower_iff_ltyped_bool`)**. -/
theorem lower_iff_ltyped_bool {e : LExpr} {b : Bool}
    (h : LTyped [] e .boolean) (hne : nonEmptySplits e = true) :
    Evaluates (lowerT e) (.boolean b) ↔ SSteps e (.boolLit b) :=
  lower_iff_bool (ltyped_canonical_bool h hne)

/-! ## 6. Verified Bidirectional Type Synthesis & Checking for `LTyped` (`inferL`, `checkL`) -/

/-- Decidable `List.Nodup` check for `List String`. -/
def nodupStrings : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && nodupStrings ns

theorem nodupStrings_sound : ∀ {ns : List String}, nodupStrings ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [nodupStrings, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupStrings_sound h.2⟩

/-- Peel `k` reusable unrestricted arrows `fn A B` from a type `TF`. -/
def peelArrows : Nat → Ty → Option (List Ty × Ty)
  | 0, R => some ([], R)
  | k + 1, .arrow .reusable .unrestricted A B => do
    let (Ts, R) ← peelArrows k B
    pure (A :: Ts, R)
  | _ + 1, _ => none

theorem peelArrows_sound : ∀ (k : Nat) (TF : Ty) (Ts : List Ty) (R : Ty),
    peelArrows k TF = some (Ts, R) → k = Ts.length ∧ curry Ts R = TF
  | 0, R, _, _, h => by
    simp only [peelArrows, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | k + 1, .arrow .reusable .unrestricted A B, _, _, h => by
    simp only [peelArrows, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨Ts', R'⟩, hp, hmk⟩ := h
    cases hmk
    obtain ⟨hl, hc⟩ := peelArrows_sound k B Ts' R' hp
    exact ⟨by simp [← hl], by simp [curry, fn, hc]⟩
  | k + 1, .natural, _, _, h | k + 1, .label, _, _, h | k + 1, .boolean, _, _, h
  | k + 1, .variable _, _, _, h | k + 1, .emptyRow, _, _, h | k + 1, .field _ _ _, _, _, h
  | k + 1, .specification _ _, _, _, h | k + 1, .prototype _ _, _, _, h | k + 1, .custody _, _, _, h
  | k + 1, .variant _, _, _, h | k + 1, .computation _ _ _, _, _, h
  | k + 1, .arrow .once _ _ _, _, _, h | k + 1, .arrow .reusable .erased _ _, _, _, h
  | k + 1, .arrow .reusable .affine _ _, _, _, h | k + 1, .arrow .reusable .linear _ _, _, _, h => by
    simp [peelArrows] at h

/-- Sufficient lookup fuel for any closed field row. -/
def rowFuel : Ty → Nat
  | .field _ _ tail => rowFuel tail + 1
  | _ => 1

mutual
/-- Verified bidirectional type inference for `LExpr`, using `expected?` to resolve `.inject` sum types. -/
def inferL (Γ : List Ty) (expected? : Option Ty) : LExpr → Option Ty
  | .bvar i => Γ[i]?
  | .erased => some .emptyRow
  | .const _ b => inferL Γ expected? b
  | .app f a =>
    match inferL Γ none f with
    | some (.arrow .reusable .unrestricted A B) =>
      if good A && inferL Γ (some A) a == some A then some B else none
    | _ => none
  | .lam A b =>
    if good A then
      let expB := match expected? with
        | some (.arrow .reusable .unrestricted _ B) => some B
        | _ => none
      (inferL (A :: Γ) expB b).map (fn A)
    else none
  | .letE A v b =>
    if good A && inferL Γ (some A) v == some A then
      inferL (A :: Γ) expected? b
    else none
  | .lit _ => some .natural
  | .natSucc a =>
    if inferL Γ (some .natural) a == some .natural then some .natural else none
  | .natBin op l r =>
    if inferL Γ (some .natural) l == some .natural && inferL Γ (some .natural) r == some .natural then
      some op.resultTy
    else none
  | .boolLit _ => some .boolean
  | .natRec T z s m =>
    if good T && inferL Γ (some T) z == some T &&
       inferL Γ (some (fn .natural (fn T T))) s == some (fn .natural (fn T T)) &&
       inferL Γ (some .natural) m == some .natural then
      some T
    else none
  | .boolRec T x y m =>
    if inferL Γ (some T) x == some T && inferL Γ (some T) y == some T &&
       inferL Γ (some .boolean) m == some .boolean then
      some T
    else none
  | .record fs =>
    match inferFields Γ fs with
    | some Ts =>
      if nodupStrings (fs.map Prod.fst) && Ts.all good then
        some (fieldRow ((fs.map Prod.fst).zip Ts))
      else none
    | none => none
  | .split names F m =>
    match inferL Γ none F with
    | some TF =>
      match peelArrows names.length TF with
      | some (Ts, R) =>
        if nodupStrings names && Ts.all good &&
           inferL Γ (some (fieldRow (names.zip Ts))) m == some (fieldRow (names.zip Ts)) then
          some R
        else none
      | none => none
    | none => none
  | .proj name t =>
    match inferL Γ none t with
    | some row => row.lookup [] (rowFuel row) name
    | none => none
  | .inject label fs =>
    match expected? with
    | some (.variant row) =>
      match inferFields Γ fs with
      | some Ts =>
        if nodupStrings (fs.map Prod.fst) && Ts.all good &&
           row.lookup [] (rowFuel row) label == some (fieldRow ((fs.map Prod.fst).zip Ts)) then
          some (.variant row)
        else none
      | none => none
    | _ => none
  | .cases R arms m =>
    match inferArms Γ R arms with
    | some sig =>
      if nodupStrings (arms.map Prod.fst) && good R &&
         inferL Γ (some (.variant (armsRow arms sig))) m == some (.variant (armsRow arms sig)) then
        some R
      else none
    | none => none
  | .recConst _ T b =>
    if good T && inferL (T :: Γ) (some T) b == some T then
      some T
    else none

def inferFields (Γ : List Ty) : List (String × LExpr) → Option (List Ty)
  | [] => some []
  | (_, e) :: rest =>
    match inferL Γ none e, inferFields Γ rest with
    | some T, some Ts => some (T :: Ts)
    | _, _ => none

def inferArms (Γ : List Ty) (R : Ty) : List (String × List String × LExpr) → Option (List (List Ty))
  | [] => some []
  | (_, names, M) :: rest =>
    match inferL Γ none M with
    | some TM =>
      match peelArrows names.length TM with
      | some (Ts, R') =>
        if R' == R && nodupStrings names && Ts.all good then
          match inferArms Γ R rest with
          | some sig => some (Ts :: sig)
          | none => none
        else none
      | none => none
    | none => none
end

/-- Decidable typechecker for `LTyped Γ e T`. -/
def checkL (Γ : List Ty) (e : LExpr) (T : Ty) : Bool :=
  inferL Γ (some T) e == some T

mutual
/-- Soundness of `inferL`: whenever `inferL Γ expected? e = some T`, `LTyped Γ e T` holds. -/
theorem inferL_sound (Γ : List Ty) :
    ∀ (e : LExpr) (expected? : Option Ty) (T : Ty),
      inferL Γ expected? e = some T → LTyped Γ e T
  | .bvar _, _, _, h => .bvar h
  | .erased, _, _, h => by
    simp only [inferL, Option.some.injEq] at h
    subst h; exact .erased Γ
  | .const _ b, exp?, T, h =>
    .const (inferL_sound Γ b exp? T h)
  | .app f a, _, _, h => by
    simp only [inferL] at h
    cases hf : inferL Γ none f with
    | none => simp [hf] at h
    | some TF =>
      cases TF with
      | arrow r q A B =>
        cases r <;> cases q <;> simp [hf] at h
        obtain ⟨⟨hA, ha⟩, rfl⟩ := h
        exact .app (inferL_sound Γ f none (fn A B) hf)
          (inferL_sound Γ a (some A) A ha) hA
      | _ => simp [hf] at h
  | .lam A b, _, _, h => by
    simp only [inferL] at h
    split at h <;> rename_i hA
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨B, hb, rfl⟩ := h
      exact .lam hA (inferL_sound (A :: Γ) b _ B hb)
    · cases h
  | .letE A v b, exp?, T, h => by
    simp only [inferL, Bool.and_eq_true, beq_iff_eq] at h
    split at h <;> rename_i hcond
    · exact .letE hcond.1 (inferL_sound Γ v (some A) A hcond.2) (inferL_sound (A :: Γ) b exp? T h)
    · cases h
  | .lit n, _, _, h => by
    simp only [inferL, Option.some.injEq] at h
    subst h; exact .lit Γ n
  | .natSucc a, _, _, h => by
    simp only [inferL, beq_iff_eq] at h
    split at h <;> rename_i ha
    · simp only [Option.some.injEq] at h
      subst h; exact .natSucc (inferL_sound Γ a (some .natural) .natural ha)
    · cases h
  | .natBin op l r, _, _, h => by
    simp only [inferL, Bool.and_eq_true, beq_iff_eq] at h
    split at h <;> rename_i hcond
    · simp only [Option.some.injEq] at h
      subst h
      exact .natBin op (inferL_sound Γ l (some .natural) .natural hcond.1)
        (inferL_sound Γ r (some .natural) .natural hcond.2)
    · cases h
  | .boolLit b, _, _, h => by
    simp only [inferL, Option.some.injEq] at h
    subst h; exact .boolLit Γ b
  | .natRec R z s m, _, _, h => by
    simp only [inferL, Bool.and_eq_true, beq_iff_eq] at h
    split at h <;> rename_i hcond
    · simp only [Option.some.injEq] at h
      subst h
      exact .natRec hcond.1.1.1
        (inferL_sound Γ z (some R) R hcond.1.1.2)
        (inferL_sound Γ s (some (fn .natural (fn R R))) (fn .natural (fn R R)) hcond.1.2)
        (inferL_sound Γ m (some .natural) .natural hcond.2)
    · cases h
  | .boolRec R x y m, _, _, h => by
    simp only [inferL, Bool.and_eq_true, beq_iff_eq] at h
    split at h <;> rename_i hcond
    · simp only [Option.some.injEq] at h
      subst h
      exact .boolRec
        (inferL_sound Γ x (some R) R hcond.1.1)
        (inferL_sound Γ y (some R) R hcond.1.2)
        (inferL_sound Γ m (some .boolean) .boolean hcond.2)
    · cases h
  | .record fs, _, _, h => by
    simp only [inferL] at h
    cases hfs : inferFields Γ fs with
    | none => simp [hfs] at h
    | some Ts =>
      simp only [hfs, Bool.and_eq_true, List.all_eq_true] at h
      split at h <;> rename_i hcond
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hlen, htyped⟩ := inferFields_sound Γ fs Ts hfs
        exact .record hlen (nodupStrings_sound hcond.1) hcond.2 htyped
      · cases h
  | .split names F m, _, _, h => by
    simp only [inferL] at h
    cases hF : inferL Γ none F with
    | none => simp [hF] at h
    | some TF =>
      simp only [hF] at h
      cases hp : peelArrows names.length TF with
      | none => simp [hp] at h
      | some p =>
        obtain ⟨Ts, R⟩ := p
        simp only [hp, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
        split at h <;> rename_i hcond
        · simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hlen, hcurry⟩ := peelArrows_sound names.length TF Ts R hp
          have hFT : LTyped Γ F (curry Ts R) := hcurry ▸ inferL_sound Γ F none TF hF
          exact .split hlen (nodupStrings_sound hcond.1.1) hcond.1.2
            (inferL_sound Γ m (some (fieldRow (names.zip Ts))) (fieldRow (names.zip Ts)) hcond.2) hFT
        · cases h
  | .proj name t, _, _, h => by
    simp only [inferL] at h
    cases ht : inferL Γ none t with
    | none => simp [ht] at h
    | some row =>
      simp only [ht] at h
      exact .proj (inferL_sound Γ t none row ht) h
  | .inject label fs, exp?, _, h => by
    simp only [inferL] at h
    cases exp? with
    | none => simp at h
    | some expT =>
      cases expT with
      | variant row =>
        simp only at h
        cases hfs : inferFields Γ fs with
        | none => simp [hfs] at h
        | some Ts =>
          simp only [hfs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
          split at h <;> rename_i hcond
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hlen, htyped⟩ := inferFields_sound Γ fs Ts hfs
            exact .inject hlen (nodupStrings_sound hcond.1.1) hcond.1.2 htyped hcond.2
          · cases h
      | _ => simp at h
  | .cases R arms m, _, _, h => by
    simp only [inferL] at h
    cases harms : inferArms Γ R arms with
    | none => simp [harms] at h
    | some sig =>
      simp only [harms, Bool.and_eq_true, beq_iff_eq] at h
      split at h <;> rename_i hcond
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hl, hlen, hnd, hg, htyped⟩ := inferArms_sound Γ R arms sig harms
        exact .cases hl (nodupStrings_sound hcond.1.1)
          (inferL_sound Γ m (some (.variant (armsRow arms sig))) (.variant (armsRow arms sig)) hcond.2)
          hlen hnd hg hcond.1.2 htyped
      · cases h
  | .recConst _ T b, _, _, h => by
    simp only [inferL, Bool.and_eq_true, beq_iff_eq] at h
    split at h <;> rename_i hcond
    · simp only [Option.some.injEq] at h
      subst h
      exact .recConst hcond.1 (inferL_sound (T :: Γ) b (some T) T hcond.2)
    · cases h

theorem inferFields_sound (Γ : List Ty) :
    ∀ (fs : List (String × LExpr)) (Ts : List Ty),
      inferFields Γ fs = some Ts →
      fs.length = Ts.length ∧ (∀ p ∈ fs.zip Ts, LTyped Γ p.1.2 p.2)
  | [], _, h => by
    simp only [inferFields, Option.some.injEq] at h
    subst h; exact ⟨rfl, by simp⟩
  | (_, e) :: rest, _, h => by
    simp only [inferFields] at h
    cases he : inferL Γ none e with
    | none => simp [he] at h
    | some T =>
      cases hrest : inferFields Γ rest with
      | none => simp [he, hrest] at h
      | some Ts' =>
        simp only [he, hrest, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, htyped⟩ := inferFields_sound Γ rest Ts' hrest
        refine ⟨by simp [hlen], ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact inferL_sound Γ e none T he
        · exact htyped p hp'

theorem inferArms_sound (Γ : List Ty) (R : Ty) :
    ∀ (arms : List (String × List String × LExpr)) (sig : List (List Ty)),
      inferArms Γ R arms = some sig →
      arms.length = sig.length ∧
      (∀ p ∈ arms.zip sig, p.1.2.1.length = p.2.length) ∧
      (∀ p ∈ arms.zip sig, p.1.2.1.Nodup) ∧
      (∀ p ∈ arms.zip sig, ∀ T ∈ p.2, good T = true) ∧
      (∀ p ∈ arms.zip sig, LTyped Γ p.1.2.2 (curry p.2 R))
  | [], _, h => by
    simp only [inferArms, Option.some.injEq] at h
    subst h; exact ⟨rfl, by simp, by simp, by simp, by simp⟩
  | (_, names, M) :: rest, _, h => by
    simp only [inferArms] at h
    cases hM : inferL Γ none M with
    | none => simp [hM] at h
    | some TM =>
      simp only [hM] at h
      cases hp : peelArrows names.length TM with
      | none => simp [hp] at h
      | some p =>
        obtain ⟨Ts, R'⟩ := p
        simp only [hp, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
        split at h <;> rename_i hcond
        · cases hsig' : inferArms Γ R rest with
          | none => simp [hsig'] at h
          | some sig' =>
            simp only [hsig', Option.some.injEq] at h
            subst h
            obtain ⟨⟨rfl, hnd0⟩, hg0⟩ := hcond
            obtain ⟨hlen0, hcurry0⟩ := peelArrows_sound names.length TM Ts R' hp
            have hMT : LTyped Γ M (curry Ts R') := hcurry0 ▸ inferL_sound Γ M none TM hM
            obtain ⟨hl, hlen, hnd, hg, htyped⟩ := inferArms_sound Γ R' rest sig' hsig'
            refine ⟨by simp [hl], ?_, ?_, ?_, ?_⟩
            · intro p hp'; rcases List.mem_cons.mp hp' with rfl | hp'
              · exact hlen0
              · exact hlen p hp'
            · intro p hp'; rcases List.mem_cons.mp hp' with rfl | hp'
              · exact nodupStrings_sound hnd0
              · exact hnd p hp'
            · intro p hp'; rcases List.mem_cons.mp hp' with rfl | hp'
              · exact hg0
              · exact hg p hp'
            · intro p hp'; rcases List.mem_cons.mp hp' with rfl | hp'
              · exact hMT
              · exact htyped p hp'
        · cases h
end

/-- **Soundness of `checkL`**: if `checkL Γ e T = true`, then `LTyped Γ e T` holds. -/
theorem checkL_sound {Γ : List Ty} {e : LExpr} {T : Ty} (h : checkL Γ e T = true) :
    LTyped Γ e T := by
  simp only [checkL, beq_iff_eq] at h
  exact inferL_sound Γ e (some T) T h

/-! ### Completeness of `inferL` and `checkL` (`ltyped_iff_checkL`) -/

theorem nodupStrings_complete : ∀ {xs : List String}, xs.Nodup → nodupStrings xs = true
  | [], _ => rfl
  | x :: xs, h => by
    have ⟨hx, hxs⟩ := List.nodup_cons.mp h
    simp [nodupStrings, hx, nodupStrings_complete hxs]

theorem peelArrows_curry : ∀ (Ts : List Ty) (R : Ty),
    peelArrows Ts.length (curry Ts R) = some (Ts, R)
  | [], R => rfl
  | A :: Ts, R => by
    simp [List.length_cons, curry, fn, peelArrows, peelArrows_curry Ts R]

theorem lookup_empty_rowFuel : ∀ (row : Ty) (fuel : Nat) (name : String) (T : Ty),
    row.lookup [] fuel name = some T → row.lookup [] (rowFuel row) name = some T
  | .field prior member tail, 0, _, _, h => by simp [Ty.lookup] at h
  | .field prior member tail, f + 1, name, T, h => by
    simp only [Ty.lookup, rowFuel] at h ⊢
    split at h <;> rename_i heq
    · simp [heq, h]
    · simp [heq, lookup_empty_rowFuel tail f name T h]
  | .variable _, 0, _, _, h | .variable _, _ + 1, _, _, h => by simp [Ty.lookup, List.lookup] at h
  | .natural, 0, _, _, h | .natural, _ + 1, _, _, h
  | .label, 0, _, _, h | .label, _ + 1, _, _, h
  | .boolean, 0, _, _, h | .boolean, _ + 1, _, _, h
  | .emptyRow, 0, _, _, h | .emptyRow, _ + 1, _, _, h
  | .arrow _ _ _ _, 0, _, _, h | .arrow _ _ _ _, _ + 1, _, _, h
  | .specification _ _, 0, _, _, h | .specification _ _, _ + 1, _, _, h
  | .prototype _ _, 0, _, _, h | .prototype _ _, _ + 1, _, _, h
  | .custody _, 0, _, _, h | .custody _, _ + 1, _, _, h
  | .variant _, 0, _, _, h | .variant _, _ + 1, _, _, h
  | .computation _ _ _, 0, _, _, h | .computation _ _ _, _ + 1, _, _, h => by
    simp [Ty.lookup] at h

mutual
/-- Syntactic bidirectional checkability predicate: every `.inject` occurs in a checking position
(`hasExp = true`) where the expected `.variant row` is known, and synthesis positions (`hasExp = false`)
do not contain unannotated `.inject`s. -/
def synthClean (hasExp : Bool) : LExpr → Bool
  | .bvar _ | .erased | .lit _ | .boolLit _ => true
  | .const _ b => synthClean hasExp b
  | .app f a => synthClean false f && synthClean true a
  | .lam _ b => synthClean hasExp b
  | .letE _ v b => synthClean true v && synthClean hasExp b
  | .natSucc a => synthClean true a
  | .natBin _ l r => synthClean true l && synthClean true r
  | .natRec _ z s m => synthClean true z && synthClean true s && synthClean true m
  | .boolRec _ x y m => synthClean true x && synthClean true y && synthClean true m
  | .record fs => synthCleanFields fs
  | .split _ F m => synthClean false F && synthClean true m
  | .proj _ t => synthClean false t
  | .inject _ fs => hasExp && synthCleanFields fs
  | .cases _ arms m => synthCleanArms arms && synthClean true m
  | .recConst _ _ b => synthClean true b

def synthCleanFields : List (String × LExpr) → Bool
  | [] => true
  | (_, e) :: rest => synthClean false e && synthCleanFields rest

def synthCleanArms : List (String × List String × LExpr) → Bool
  | [] => true
  | (_, _, M) :: rest => synthClean false M && synthCleanArms rest
end

theorem inferFields_complete {Γ : List Ty} :
    ∀ {fs : List (String × LExpr)} {Ts : List Ty},
      fs.length = Ts.length →
      (∀ p ∈ fs.zip Ts, inferL Γ none p.1.2 = some p.2) →
      inferFields Γ fs = some Ts
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h
  | (n, e) :: fs, T :: Ts, hlen, hrec => by
    have he : inferL Γ none e = some T := hrec ((n, e), T) (by simp)
    have hrest : inferFields Γ fs = some Ts :=
      inferFields_complete (by simpa using hlen) (fun p hp => hrec p (by simp [hp]))
    simp [inferFields, he, hrest]

theorem inferArms_complete {Γ : List Ty} {R : Ty} :
    ∀ {arms : List (String × List String × LExpr)} {sig : List (List Ty)},
      arms.length = sig.length →
      (∀ p ∈ arms.zip sig, p.1.2.1.length = p.2.length) →
      (∀ p ∈ arms.zip sig, p.1.2.1.Nodup) →
      (∀ p ∈ arms.zip sig, ∀ T ∈ p.2, good T = true) →
      (∀ p ∈ arms.zip sig, inferL Γ none p.1.2.2 = some (curry p.2 R)) →
      inferArms Γ R arms = some sig
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => by simp at h
  | (lbl, names, M) :: arms, Ts :: sig, hlen, hnames, hnd, hg, hM => by
    have hM0 : inferL Γ none M = some (curry Ts R) := hM ((lbl, names, M), Ts) (by simp)
    have hn0 : names.length = Ts.length := hnames ((lbl, names, M), Ts) (by simp)
    have hnd0 : nodupStrings names = true := nodupStrings_complete (hnd ((lbl, names, M), Ts) (by simp))
    have hg0 : Ts.all good = true := List.all_eq_true.mpr (hg ((lbl, names, M), Ts) (by simp))
    have hrest : inferArms Γ R arms = some sig :=
      inferArms_complete (by simpa using hlen)
        (fun p hp => hnames p (by simp [hp]))
        (fun p hp => hnd p (by simp [hp]))
        (fun p hp => hg p (by simp [hp]))
        (fun p hp => hM p (by simp [hp]))
    simp [inferArms, hM0, hn0, peelArrows_curry, hnd0, hg0, hrest]

theorem synthCleanFields_mem :
    ∀ {fs : List (String × LExpr)} {Ts : List Ty},
      synthCleanFields fs = true →
      ∀ p ∈ fs.zip Ts, synthClean false p.1.2 = true
  | [], _, _, p, hp => by simp at hp
  | (_, _) :: _, [], _, p, hp => by simp at hp
  | (_, e) :: fs, _ :: Ts, hc, p, hp => by
    simp only [synthCleanFields, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hc.1
    · exact synthCleanFields_mem hc.2 p hp'

theorem synthCleanArms_mem :
    ∀ {arms : List (String × List String × LExpr)} {sig : List (List Ty)},
      synthCleanArms arms = true →
      ∀ p ∈ arms.zip sig, synthClean false p.1.2.2 = true
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | (_, _, M) :: arms, _ :: sig, hc, p, hp => by
    simp only [synthCleanArms, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hc.1
    · exact synthCleanArms_mem hc.2 p hp'

/-- **Completeness of `inferL` (`ltyped_inferL_complete`)**: every `LTyped Γ e T` derivation on a
`synthClean hasExp e` term is inferred as `some T` by `inferL Γ (cond hasExp (some T) none) e`. -/
theorem ltyped_inferL_complete {Γ : List Ty} {e : LExpr} {T : Ty}
    (h : LTyped Γ e T) :
    ∀ (hasExp : Bool), synthClean hasExp e = true →
      inferL Γ (cond hasExp (some T) none) e = some T := by
  induction h with
  | bvar hb => intro _ _; exact hb
  | erased _ => intro _ _; rfl
  | const _ ih => intro hasExp hc; exact ih hasExp hc
  | app _ _ hA ihf iha =>
    intro hasExp hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hf' := ihf false hc.1
    have ha' := iha true hc.2
    simp only [cond] at hf' ha'
    simp [inferL, hf', ha', hA]
  | lam hA _ ihb =>
    intro hasExp hc
    have hb' := ihb hasExp hc
    cases hasExp <;> simp_all [inferL, cond]
  | letE hA _ _ ihv ihb =>
    intro hasExp hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hv' := ihv true hc.1
    have hb' := ihb hasExp hc.2
    simp only [cond] at hv'
    simp only [inferL, hA, hv', beq_self_eq_true, Bool.and_self, ↓reduceIte]
    exact hb'
  | lit _ _ => intro _ _; rfl
  | natSucc _ iha =>
    intro _ hc
    have ha' := iha true hc
    simp only [cond] at ha'
    simp [inferL, ha']
  | natBin op _ _ ihl ihr =>
    intro _ hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hl' := ihl true hc.1
    have hr' := ihr true hc.2
    simp only [cond] at hl' hr'
    simp [inferL, hl', hr']
  | boolLit _ _ => intro _ _; rfl
  | natRec hT _ _ _ ihz ihs ihm =>
    intro _ hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hz' := ihz true hc.1.1
    have hs' := ihs true hc.1.2
    have hm' := ihm true hc.2
    simp only [cond] at hz' hs' hm'
    simp [inferL, hT, hz', hs', hm']
  | boolRec _ _ _ ihx ihy ihm =>
    intro _ hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hx' := ihx true hc.1.1
    have hy' := ihy true hc.1.2
    have hm' := ihm true hc.2
    simp only [cond] at hx' hy' hm'
    simp [inferL, hx', hy', hm']
  | @record Γ' fs' Ts' hlen hnd hg _ ihfs =>
    intro _ hc
    have hfields : inferFields Γ' fs' = some Ts' :=
      inferFields_complete hlen (fun p hp => ihfs p hp false (synthCleanFields_mem hc p hp))
    have hnd' := nodupStrings_complete hnd
    simp [inferL, hfields, hnd']
    exact hg
  | @split Γ' names' F' m' Ts' R' hlen hnd hg _ _ ihm ihF =>
    intro _ hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have hF' := ihF false hc.1
    have hm' := ihm true hc.2
    simp only [cond] at hF' hm'
    have hnd' := nodupStrings_complete hnd
    simp [inferL, hF', hlen, peelArrows_curry, hnd', hm']
    exact hg
  | proj _ hlook iht =>
    intro _ hc
    have ht' := iht false hc
    simp only [cond] at ht'
    simp [inferL, ht', lookup_empty_rowFuel _ _ _ _ hlook]
  | @inject Γ' label' fs' Ts' row' fuel' hlen hnd hg _ hlook ihfs =>
    intro hasExp hc
    simp only [synthClean, Bool.and_eq_true] at hc
    rcases hc with ⟨rfl, hcfs⟩
    have hfields : inferFields Γ' fs' = some Ts' :=
      inferFields_complete hlen (fun p hp => ihfs p hp false (synthCleanFields_mem hcfs p hp))
    have hnd' := nodupStrings_complete hnd
    have hlook' := lookup_empty_rowFuel _ _ _ _ hlook
    simp [inferL, cond, hfields, hnd', hlook']
    exact hg
  | @cases Γ' R' arms' sig' m' hlen hnd _ hnames hnd_arms hg hR _ ihm iharms =>
    intro _ hc
    simp only [synthClean, Bool.and_eq_true] at hc
    have harms' : inferArms Γ' R' arms' = some sig' :=
      inferArms_complete hlen hnames hnd_arms hg
        (fun p hp => iharms p hp false (synthCleanArms_mem hc.1 p hp))
    have hm' := ihm true hc.2
    simp only [cond] at hm'
    have hnd' := nodupStrings_complete hnd
    simp [inferL, harms', hnd', hR, hm']
  | recConst hT _ ihb =>
    intro _ hc
    have hb' := ihb true hc
    simp only [cond] at hb'
    simp [inferL, hT, hb']

/-- **Completeness of `checkL`**: for any `synthClean true e = true`, `LTyped Γ e T` implies
`checkL Γ e T = true`. -/
theorem checkL_complete {Γ : List Ty} {e : LExpr} {T : Ty}
    (hc : synthClean true e = true) (h : LTyped Γ e T) :
    checkL Γ e T = true := by
  simp only [checkL, beq_iff_eq]
  exact ltyped_inferL_complete h true hc

/-- **Exact Characterization / Decidability of `LTyped` (`ltyped_iff_checkL`)**:
On any `synthClean true e = true` term, `LTyped Γ e T` holds if and only if `checkL Γ e T = true`. -/
theorem ltyped_iff_checkL {Γ : List Ty} {e : LExpr} {T : Ty}
    (hc : synthClean true e = true) :
    LTyped Γ e T ↔ checkL Γ e T = true :=
  ⟨checkL_complete hc, checkL_sound⟩

/-- Apply a source expression `f` to a list of argument expressions `args`. -/
def lapps (f : LExpr) (args : List LExpr) : LExpr := args.foldl .app f

/-- Applying a reducible curried function `f` of type `curry argTys R` to reducible arguments `args`
produces a reducible result `Red R (lapps f args)`. -/
theorem red_lapps :
    ∀ (args : List LExpr) (argTys : List Ty) (R : Ty) (f : LExpr),
      args.length = argTys.length →
      (∀ p ∈ args.zip argTys, Red p.2 p.1) →
      Red (curry argTys R) f →
      Red R (lapps f args)
  | [], [], _, f, _, _, hf => hf
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp at h
  | a :: args, A :: argTys, R, f, hl, hargs, hf =>
    red_lapps args argTys R (.app f a) (by simpa using hl)
      (fun p hp => hargs p (by simp [hp]))
      (hf a (hargs (a, A) (by simp)))

end Obend.Lower
end
