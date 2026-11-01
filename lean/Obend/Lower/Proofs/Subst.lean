module
/- The lowering commutes with renaming and substitution, so a source β (or ζ) step is one Core4 β
step on the lowered terms. -/
public import Obend.Lower.Lower
public import Obend.Equiv.Reduction
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_comp rename_substitute substitute_rename substitute_comp)
open Obend.Equiv (instantiate_eq single)
set_option autoImplicit false

theorem rename_shift1 (t : Term) (f : Nat → Nat) :
    (t.rename Nat.succ).rename (liftRename f) = (t.rename f).rename Nat.succ := by
  rw [rename_comp, rename_comp]; rfl

theorem rename_shift3 (t : Term) (f : Nat → Nat) :
    (t.rename (· + 3)).rename (liftRename (liftRename (liftRename f))) = (t.rename f).rename (· + 3) := by
  rw [rename_comp, rename_comp]; rfl

theorem rename_shift4 (t : Term) (f : Nat → Nat) :
    (t.rename (· + 4)).rename (liftRename (liftRename (liftRename (liftRename f)))) =
      (t.rename f).rename (· + 4) := by
  rw [rename_comp, rename_comp]; rfl

theorem subst_shift1 (t : Term) (τ : Nat → Term) :
    (t.rename Nat.succ).substitute (liftSubstitution τ) = (t.substitute τ).rename Nat.succ := by
  rw [rename_substitute, substitute_rename]; rfl

theorem subst_shift3 (t : Term) (τ : Nat → Term) :
    (t.rename (· + 3)).substitute (liftSubstitution (liftSubstitution (liftSubstitution τ))) =
      (t.substitute τ).rename (· + 3) := by
  rw [rename_substitute, substitute_rename]
  congr 1; funext i
  simp only [liftSubstitution, rename_comp]

theorem subst_shift4 (t : Term) (τ : Nat → Term) :
    (t.rename (· + 4)).substitute
        (liftSubstitution (liftSubstitution (liftSubstitution (liftSubstitution τ)))) =
      (t.substitute τ).rename (· + 4) := by
  rw [rename_substitute, substitute_rename]
  congr 1; funext i
  simp only [liftSubstitution, rename_comp]

theorem natRecSpec_rename (Z S : Term) (f : Nat → Nat) :
    (natRecSpec Z S).rename f = natRecSpec (Z.rename f) (S.rename f) := by
  simp only [natRecSpec, Term.rename, rename_shift3, rename_shift4]
  rfl

theorem natRecSpec_substitute (Z S : Term) (τ : Nat → Term) :
    (natRecSpec Z S).substitute τ = natRecSpec (Z.substitute τ) (S.substitute τ) := by
  simp only [natRecSpec, Term.substitute, subst_shift3, subst_shift4]
  simp [liftSubstitution, Term.rename]

theorem caseArm_rename (names : List String) (M : Term) (f : Nat → Nat) :
    (caseArm names M).rename (liftRename f) = caseArm names (M.rename f) := by
  simp only [caseArm, Term.rename, rename_shift1]; rfl

theorem caseArm_substitute (names : List String) (M : Term) (τ : Nat → Term) :
    (caseArm names M).substitute (liftSubstitution τ) = caseArm names (M.substitute τ) := by
  simp only [caseArm, Term.substitute, subst_shift1]; rfl

theorem lowerT_rename : ∀ (e : LExpr) (f : Nat → Nat), lowerT (e.rename f) = (lowerT e).rename f
  | .bvar i, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .erased, f => by simp [LExpr.rename, lowerT, Term.rename, box]
  | .const n b, f => by simp only [LExpr.rename, lowerT]; exact lowerT_rename b f
  | .app a b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f, lowerT_rename b f]
  | .lam T b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b]
  | .letE T v b, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b, lowerT_rename v]
  | .lit n, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .natSucc a, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f]
  | .natBin op a b, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename a f, lowerT_rename b f]
  | .boolLit b, f => by simp [LExpr.rename, lowerT, Term.rename]
  | .natRec T z s m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename z f, lowerT_rename s f, lowerT_rename m f,
      natRecSpec_rename, box]
    rfl
  | .boolRec T x y m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename x f, lowerT_rename y f, lowerT_rename m f]
  | .record fs, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2 f]
  | .split ns F m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename F f, lowerT_rename m f]
  | .proj n t, f => by simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename t f]
  | .inject l fs, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map]
    congr 2; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2 f]
  | .cases T arms m, f => by
    simp only [LExpr.rename, lowerT, Term.rename, List.map_map, lowerT_rename m f]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_rename x.2.2 f, caseArm_rename]
  | .recConst n T b, f => by
    simp only [LExpr.rename, lowerT, Term.rename, lowerT_rename b, recSpec, box, rename_shift1]
    rfl
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

theorem lowerT_liftSubst (σ : Nat → LExpr) :
    (fun i => lowerT (LExpr.liftSubst σ i)) = liftSubstitution (fun i => lowerT (σ i)) := by
  funext i; cases i with
  | zero => simp [LExpr.liftSubst, lowerT, liftSubstitution]
  | succ n => simp [LExpr.liftSubst, liftSubstitution, lowerT_rename]

theorem lowerT_subst : ∀ (e : LExpr) (σ : Nat → LExpr),
    lowerT (e.subst σ) = (lowerT e).substitute (fun i => lowerT (σ i))
  | .bvar i, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .erased, σ => by simp [LExpr.subst, lowerT, Term.substitute, box]
  | .const n b, σ => by simp only [LExpr.subst, lowerT]; exact lowerT_subst b σ
  | .app a b, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ, lowerT_subst b σ]
  | .lam T b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_liftSubst]
  | .letE T v b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_subst v, lowerT_liftSubst]
  | .lit n, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .natSucc a, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ]
  | .natBin op a b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst a σ, lowerT_subst b σ]
  | .boolLit b, σ => by simp [LExpr.subst, lowerT, Term.substitute]
  | .natRec T z s m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst z σ, lowerT_subst s σ, lowerT_subst m σ,
      natRecSpec_substitute, box]
    rfl
  | .boolRec T x y m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst x σ, lowerT_subst y σ, lowerT_subst m σ]
  | .record fs, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2 σ]
  | .split ns F m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst F σ, lowerT_subst m σ]
  | .proj n t, σ => by simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst t σ]
  | .inject l fs, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map]
    congr 2; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2 σ]
  | .cases T arms m, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, List.map_map, lowerT_subst m σ]
    congr 1; apply List.map_congr_left; intro x hx
    simp only [Function.comp_apply, lowerT_subst x.2.2 σ, caseArm_substitute]
  | .recConst n T b, σ => by
    simp only [LExpr.subst, lowerT, Term.substitute, lowerT_subst b, lowerT_liftSubst, recSpec, box,
      subst_shift1]
    rfl
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := LExpr.sizeOf_snd_lt hx; omega)
    | (have := LExpr.sizeOf_arm_lt hx; omega)

/-- **A source β step is a Core4 β step**: lowering commutes with instantiation. -/
theorem lowerT_inst (b a : LExpr) : lowerT (b.inst a) = instantiate (lowerT b) (lowerT a) := by
  rw [LExpr.inst, lowerT_subst, instantiate_eq]
  congr 1; funext i; cases i <;> simp [LExpr.single, single, lowerT]

theorem lowerT_spine : ∀ (F : LExpr) (vs : List LExpr), lowerT (F.spine vs) = applyAll (lowerT F) (vs.map lowerT)
  | F, [] => rfl
  | F, v :: vs => by
    simp only [LExpr.spine, List.map_cons, applyAll]
    rw [lowerT_spine]; simp only [lowerT]

end Obend.Lower
end
