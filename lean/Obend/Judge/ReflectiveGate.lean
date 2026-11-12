module
public import Obend.Judge.CertifierRatchet
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.SvenvsCorrigibility

public section
namespace Obend.Judge.ReflectiveGate
open SvenvsCorrigibility CertifierRatchet

inductive EmbTy where
  | boolTy | bv4Ty
  deriving DecidableEq, Repr
inductive Val where
  | bool (b : Bool) | bv4 (v : BitVec 4)
  deriving DecidableEq, Repr

def Val.asBool : Val → Bool | .bool b => b | .bv4 _ => false
def Val.asBv4 : Val → BitVec 4 | .bv4 v => v | .bool _ => 0

/-- Finite binders store their sixteen syntactic instances, in numerical order.
Quotation substitutes constants before constructing the binder. No Lean
proposition or semantic proof occurs in the embedded syntax. -/
inductive EmbTerm where
  | var (name : String) (ty : EmbTy)
  | bconst (b : Bool)
  | bv4 (v : BitVec 4)
  | notE (a : EmbTerm)
  | andE (a b : EmbTerm)
  | orE (a b : EmbTerm)
  | impE (a b : EmbTerm)
  | eqE (a b : EmbTerm)
  | iteE (c a b : EmbTerm)
  | bitE (i : Fin 4) (a : EmbTerm)
  | lut4E (table : BitVec 16) (a b c d : EmbTerm)
  | forallBv4 (name : String) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : EmbTerm)
  deriving DecidableEq, Repr

abbrev Env := String → EmbTy → Val

def inferEmbTy : EmbTerm → Option EmbTy
  | .var _ t => some t
  | .bconst _ => some .boolTy
  | .bv4 _ => some .bv4Ty
  | .notE a => if inferEmbTy a = some .boolTy then some .boolTy else none
  | .andE a b | .orE a b | .impE a b =>
      if inferEmbTy a = some .boolTy ∧ inferEmbTy b = some .boolTy then some .boolTy else none
  | .eqE a b => if inferEmbTy a = inferEmbTy b ∧ (inferEmbTy a).isSome then some .boolTy else none
  | .iteE c a b => if inferEmbTy c = some .boolTy ∧ inferEmbTy a = inferEmbTy b then inferEmbTy a else none
  | .bitE _ a => if inferEmbTy a = some .bv4Ty then some .boolTy else none
  | .lut4E _ a b c d => if (inferEmbTy a == some .boolTy) && (inferEmbTy b == some .boolTy) && (inferEmbTy c == some .boolTy) && (inferEmbTy d == some .boolTy) then some .boolTy else none
  | .forallBv4 _ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 =>
      if (inferEmbTy t0 == some .boolTy) && (inferEmbTy t1 == some .boolTy) && (inferEmbTy t2 == some .boolTy) && (inferEmbTy t3 == some .boolTy) && (inferEmbTy t4 == some .boolTy) && (inferEmbTy t5 == some .boolTy) && (inferEmbTy t6 == some .boolTy) && (inferEmbTy t7 == some .boolTy) && (inferEmbTy t8 == some .boolTy) && (inferEmbTy t9 == some .boolTy) && (inferEmbTy t10 == some .boolTy) && (inferEmbTy t11 == some .boolTy) && (inferEmbTy t12 == some .boolTy) && (inferEmbTy t13 == some .boolTy) && (inferEmbTy t14 == some .boolTy) && (inferEmbTy t15 == some .boolTy) then some .boolTy else none

def WellTypedFormula (t : EmbTerm) : Bool := inferEmbTy t == some .boolTy

/-- Tarskian evaluation; finite universal quantification checks all sixteen
explicit substitution instances. Variables retain both their name and sort. -/
def evalEmbTerm (env : Env) : EmbTerm → Val
  | .var n .boolTy => .bool (env n .boolTy).asBool
  | .var n .bv4Ty => .bv4 (env n .bv4Ty).asBv4
  | .bconst b => .bool b
  | .bv4 v => .bv4 v
  | .notE a => .bool (!(evalEmbTerm env a).asBool)
  | .andE a b => .bool ((evalEmbTerm env a).asBool && (evalEmbTerm env b).asBool)
  | .orE a b => .bool ((evalEmbTerm env a).asBool || (evalEmbTerm env b).asBool)
  | .impE a b => .bool (!(evalEmbTerm env a).asBool || (evalEmbTerm env b).asBool)
  | .eqE a b => .bool (decide (evalEmbTerm env a = evalEmbTerm env b))
  | .iteE c a b => if (evalEmbTerm env c).asBool then evalEmbTerm env a else evalEmbTerm env b
  | .bitE i a => .bool ((evalEmbTerm env a).asBv4.getLsbD i)
  | .lut4E table a b c d => .bool (table.getLsbD
      ((evalEmbTerm env a).asBool.toNat + 2*(evalEmbTerm env b).asBool.toNat +
       4*(evalEmbTerm env c).asBool.toNat + 8*(evalEmbTerm env d).asBool.toNat))
  | .forallBv4 _ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 =>
      .bool ((evalEmbTerm env t0).asBool && (evalEmbTerm env t1).asBool && (evalEmbTerm env t2).asBool && (evalEmbTerm env t3).asBool && (evalEmbTerm env t4).asBool && (evalEmbTerm env t5).asBool && (evalEmbTerm env t6).asBool && (evalEmbTerm env t7).asBool && (evalEmbTerm env t8).asBool && (evalEmbTerm env t9).asBool && (evalEmbTerm env t10).asBool && (evalEmbTerm env t11).asBool && (evalEmbTerm env t12).asBool && (evalEmbTerm env t13).asBool && (evalEmbTerm env t14).asBool && (evalEmbTerm env t15).asBool)

def evalTerm (env : Env) (t : EmbTerm) : Option Val :=
  if (inferEmbTy t).isSome then some (evalEmbTerm env t) else none

structure Sequent where
  hyps : List EmbTerm
  concl : EmbTerm
  deriving DecidableEq, Repr

def sequentTyped (s : Sequent) : Bool := s.hyps.all WellTypedFormula && WellTypedFormula s.concl
def Holds (env : Env) (t : EmbTerm) : Prop := (evalEmbTerm env t).asBool = true

def SemValid (s : Sequent) : Prop := sequentTyped s = true ∧
  ∀ env, (∀ h ∈ s.hyps, Holds env h) → Holds env s.concl

theorem holds_evalTerm_iff (env : Env) (t : EmbTerm) (wt : WellTypedFormula t = true) :
    Holds env t ↔ evalTerm env t = some (.bool true) := by
  have ht : inferEmbTy t = some .boolTy := by simpa [WellTypedFormula] using wt
  simp only [evalTerm, ht, Option.isSome_some, ↓reduceIte, Option.some.injEq]
  unfold Holds
  cases evalEmbTerm env t <;> simp [Val.asBool]

theorem semValid_tarskian (seq : Sequent) : SemValid seq ↔
    (∀ h ∈ seq.hyps, WellTypedFormula h = true) ∧ WellTypedFormula seq.concl = true ∧
      ∀ env, (∀ h ∈ seq.hyps, evalTerm env h = some (.bool true)) →
        evalTerm env seq.concl = some (.bool true) := by
  constructor
  · rintro ⟨wt,h⟩
    simp only [sequentTyped, Bool.and_eq_true, List.all_eq_true] at wt
    exact ⟨wt.1, wt.2, fun env hh => (holds_evalTerm_iff env _ wt.2).1
      (h env (fun t ht => (holds_evalTerm_iff env t (wt.1 t ht)).2 (hh t ht)))⟩
  · rintro ⟨wh,wc,h⟩
    refine ⟨by simpa only [sequentTyped, Bool.and_eq_true, List.all_eq_true] using And.intro wh wc, ?_⟩
    intro env hh
    exact (holds_evalTerm_iff env _ wc).2 (h env
      (fun t ht => (holds_evalTerm_iff env t (wh t ht)).1 (hh t ht)))

/-- These are local primitive reductions, not arbitrary formula evaluation. -/
def primitiveTruth : EmbTerm → Bool
  | .bconst b => b
  | .impE (.bconst a) (.bconst b) => !a || b
  | .eqE (.bconst a) (.bconst b) => a == b
  | .eqE (.bv4 a) (.bv4 b) => a == b
  | .eqE (.notE (.bconst a)) (.bconst b) => (!a) == b
  | .eqE (.andE (.bconst a) (.bconst b)) (.bconst c) => (a && b) == c
  | .eqE (.orE (.bconst a) (.bconst b)) (.bconst c) => (a || b) == c
  | .eqE (.bitE i (.bv4 a)) (.bconst b) => a.getLsbD i == b
  | .eqE (.lut4E table (.bconst a) (.bconst b) (.bconst c) (.bconst d)) (.bconst r) =>
      table.getLsbD (a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat) == r
  | _ => false

theorem primitiveTruth_correct (t : EmbTerm) (h : primitiveTruth t = true) (env : Env) : Holds env t := by
  unfold primitiveTruth at h
  split at h <;> simp_all [Holds, evalEmbTerm, Val.asBool, Val.asBv4]

/-- Single-hole, sort-checked contexts for equational congruence. -/
inductive EqContext where
  | notE
  | andLeft (b : EmbTerm) | andRight (a : EmbTerm)
  | orLeft (b : EmbTerm) | orRight (a : EmbTerm)
  | impLeft (b : EmbTerm) | impRight (a : EmbTerm)
  | eqLeft (b : EmbTerm) | eqRight (a : EmbTerm)
  | iteCond (a b : EmbTerm) | iteThen (c b : EmbTerm) | iteElse (c a : EmbTerm)
  | bitE (i : Fin 4)
  | lutA (table : BitVec 16) (b c d : EmbTerm)
  | lutB (table : BitVec 16) (a c d : EmbTerm)
  | lutC (table : BitVec 16) (a b d : EmbTerm)
  | lutD (table : BitVec 16) (a b c : EmbTerm)
  deriving Repr

def plugContext (ctx : EqContext) (x : EmbTerm) : EmbTerm := match ctx with
  | .notE => .notE x
  | .andLeft b => .andE x b
  | .andRight a => .andE a x
  | .orLeft b => .orE x b
  | .orRight a => .orE a x
  | .impLeft b => .impE x b
  | .impRight a => .impE a x
  | .eqLeft b => .eqE x b
  | .eqRight a => .eqE a x
  | .iteCond a b => .iteE x a b
  | .iteThen c b => .iteE c x b
  | .iteElse c a => .iteE c a x
  | .bitE i => .bitE i x
  | .lutA table b c d => .lut4E table x b c d
  | .lutB table a c d => .lut4E table a x c d
  | .lutC table a b d => .lut4E table a b x d
  | .lutD table a b c => .lut4E table a b c x

theorem plugContext_eval (ctx : EqContext) (env : Env) (a b : EmbTerm)
    (h : evalEmbTerm env a = evalEmbTerm env b) :
    evalEmbTerm env (plugContext ctx a) = evalEmbTerm env (plugContext ctx b) := by
  cases ctx <;> simp only [plugContext, evalEmbTerm, h]

/-- Equality congruence is an implication schema. Symmetry is deliberately
absent: it is derived by applying this schema to reflexivity. -/
inductive Derivable : Sequent → Prop where
  | axHyp {hs t} : sequentTyped ⟨hs,t⟩ = true → t ∈ hs → Derivable ⟨hs,t⟩
  | primitive {s} : sequentTyped s = true → primitiveTruth s.concl = true → Derivable s
  | eqRefl {hs a} : sequentTyped ⟨hs,.eqE a a⟩ = true → Derivable ⟨hs,.eqE a a⟩
  | eqCongr {hs a b c} : sequentTyped ⟨hs,.impE (.eqE a b) (.impE (.eqE a c) (.eqE b c))⟩ = true →
      Derivable ⟨hs,.impE (.eqE a b) (.impE (.eqE a c) (.eqE b c))⟩
  | impIntro {hs a b} : sequentTyped ⟨hs,.impE a b⟩ = true → Derivable ⟨a::hs,b⟩ → Derivable ⟨hs,.impE a b⟩
  | impElim {hs a b} : sequentTyped ⟨hs,b⟩ = true → Derivable ⟨hs,.impE a b⟩ → Derivable ⟨hs,a⟩ → Derivable ⟨hs,b⟩
  | andIntro {hs a b} : sequentTyped ⟨hs,.andE a b⟩ = true → Derivable ⟨hs,a⟩ → Derivable ⟨hs,b⟩ → Derivable ⟨hs,.andE a b⟩
  | andElimL {hs a b} : sequentTyped ⟨hs,a⟩ = true → Derivable ⟨hs,.andE a b⟩ → Derivable ⟨hs,a⟩
  | andElimR {hs a b} : sequentTyped ⟨hs,b⟩ = true → Derivable ⟨hs,.andE a b⟩ → Derivable ⟨hs,b⟩
  | eqTrans {hs a b c} : sequentTyped ⟨hs,.eqE a c⟩ = true → Derivable ⟨hs,.eqE a b⟩ → Derivable ⟨hs,.eqE b c⟩ → Derivable ⟨hs,.eqE a c⟩
  | eqContext {hs ctx a b} : sequentTyped ⟨hs,.eqE (plugContext ctx a) (plugContext ctx b)⟩ = true →
      Derivable ⟨hs,.eqE a b⟩ → Derivable ⟨hs,.eqE (plugContext ctx a) (plugContext ctx b)⟩
  | forallBv4Intro {hs name t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15} : sequentTyped ⟨hs,.forallBv4 name t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15⟩ = true →
      Derivable ⟨hs,t0⟩ → Derivable ⟨hs,t1⟩ → Derivable ⟨hs,t2⟩ → Derivable ⟨hs,t3⟩ → Derivable ⟨hs,t4⟩ → Derivable ⟨hs,t5⟩ → Derivable ⟨hs,t6⟩ → Derivable ⟨hs,t7⟩ → Derivable ⟨hs,t8⟩ → Derivable ⟨hs,t9⟩ → Derivable ⟨hs,t10⟩ → Derivable ⟨hs,t11⟩ → Derivable ⟨hs,t12⟩ → Derivable ⟨hs,t13⟩ → Derivable ⟨hs,t14⟩ → Derivable ⟨hs,t15⟩ →
      Derivable ⟨hs,.forallBv4 name t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15⟩

theorem derivable_sound {s : Sequent} (h : Derivable s) : SemValid s := by
  induction h with
  | axHyp wt mem => exact ⟨wt, fun _ hh => hh _ mem⟩
  | primitive wt hp => exact ⟨wt, fun env _ => primitiveTruth_correct _ hp env⟩
  | eqRefl wt => exact ⟨wt, fun _ _ => by simp [Holds, evalEmbTerm, Val.asBool]⟩
  | @eqCongr hs a b c wt =>
    refine ⟨wt, fun env _ => ?_⟩
    simp only [Holds, evalEmbTerm, Val.asBool, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases hab : evalEmbTerm env a = evalEmbTerm env b
    · apply Or.inr
      by_cases hac : evalEmbTerm env a = evalEmbTerm env c
      · exact .inr (hab.symm.trans hac)
      · exact .inl hac
    · exact .inl hab
  | @impIntro hs a b wt _ ih =>
    refine ⟨wt, fun env hh => ?_⟩
    simp only [Holds, evalEmbTerm, Val.asBool, Bool.or_eq_true, Bool.not_eq_true']
    cases ha : (evalEmbTerm env a).asBool with
    | false => exact .inl ha
    | true => exact .inr (ih.2 env (by intro t ht; rcases List.mem_cons.mp ht with rfl | ht; exact ha; exact hh t ht))
  | @impElim hs a b wt _ _ ih1 ih2 =>
    refine ⟨wt, fun env hh => ?_⟩
    have h1 := ih1.2 env hh
    have h2 := ih2.2 env hh
    change (evalEmbTerm env a).asBool = true at h2
    change (!(evalEmbTerm env a).asBool || (evalEmbTerm env b).asBool) = true at h1
    change (evalEmbTerm env b).asBool = true
    simpa only [h2, Bool.not_true, Bool.false_or] using h1
  | andIntro wt _ _ ih1 ih2 =>
    exact ⟨wt, fun env hh => by simpa [Holds, evalEmbTerm, Val.asBool] using And.intro (ih1.2 env hh) (ih2.2 env hh)⟩
  | andElimL wt _ ih =>
    exact ⟨wt, fun env hh => (show Holds env _ ∧ Holds env _ from by simpa [Holds, evalEmbTerm, Val.asBool] using ih.2 env hh).1⟩
  | andElimR wt _ ih =>
    exact ⟨wt, fun env hh => (show Holds env _ ∧ Holds env _ from by simpa [Holds, evalEmbTerm, Val.asBool] using ih.2 env hh).2⟩
  | eqTrans wt _ _ ih1 ih2 =>
    refine ⟨wt, fun env hh => ?_⟩
    have h1 := ih1.2 env hh
    have h2 := ih2.2 env hh
    simp only [Holds, evalEmbTerm, Val.asBool, decide_eq_true_eq] at h1 h2 ⊢
    exact h1.trans h2
  | @eqContext hs ctx a b wt _ ih =>
    refine ⟨wt, fun env hh => ?_⟩
    have he := ih.2 env hh
    simp only [Holds, evalEmbTerm, Val.asBool, decide_eq_true_eq] at he ⊢
    exact plugContext_eval ctx env a b he
  | forallBv4Intro wt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 ih10 ih11 ih12 ih13 ih14 ih15 =>
    refine ⟨wt, fun env hh => ?_⟩
    simp only [Holds, evalEmbTerm, Val.asBool, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ih0.2 env hh, ih1.2 env hh⟩, ih2.2 env hh⟩, ih3.2 env hh⟩, ih4.2 env hh⟩, ih5.2 env hh⟩, ih6.2 env hh⟩, ih7.2 env hh⟩, ih8.2 env hh⟩, ih9.2 env hh⟩, ih10.2 env hh⟩, ih11.2 env hh⟩, ih12.2 env hh⟩, ih13.2 env hh⟩, ih14.2 env hh⟩, ih15.2 env hh⟩

inductive ProofCert where
  | axHyp | primitive | eqRefl | eqCongr
  | impIntro (p : ProofCert)
  | impElim (a : EmbTerm) (p q : ProofCert)
  | andIntro (p q : ProofCert)
  | andElimL (b : EmbTerm) (p : ProofCert)
  | andElimR (a : EmbTerm) (p : ProofCert)
  | eqTrans (b : EmbTerm) (p q : ProofCert)
  | eqContext (ctx : EqContext) (a b : EmbTerm) (p : ProofCert)
  | forallBv4Intro (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : ProofCert)
  deriving Repr

def congruenceShape : EmbTerm → Bool
  | .impE (.eqE a b) (.impE (.eqE c d) (.eqE e f)) => a == c && b == e && d == f
  | _ => false

theorem congruenceShape_derivable (s : Sequent) (wt : sequentTyped s = true)
    (h : congruenceShape s.concl = true) : Derivable s := by
  obtain ⟨hs,t⟩ := s
  unfold congruenceShape at h
  split at h
  next a b c d e f ht =>
    dsimp only at ht
    subst t
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := h
    exact .eqCongr wt
  next => cases h

/-- Pairwise checking also rejects missing and excess finite cases. -/
def checkProof (p : ProofCert) (s : Sequent) : Bool := sequentTyped s &&
  match p, s.concl with
  | .axHyp, t => s.hyps.contains t
  | .primitive, t => primitiveTruth t
  | .eqRefl, .eqE a b => a == b
  | .eqCongr, t => congruenceShape t
  | .impIntro p, .impE a b => checkProof p ⟨a::s.hyps,b⟩
  | .impElim a p q, b => checkProof p ⟨s.hyps,.impE a b⟩ && checkProof q ⟨s.hyps,a⟩
  | .andIntro p q, .andE a b => checkProof p ⟨s.hyps,a⟩ && checkProof q ⟨s.hyps,b⟩
  | .andElimL b p, a => checkProof p ⟨s.hyps,.andE a b⟩
  | .andElimR a p, b => checkProof p ⟨s.hyps,.andE a b⟩
  | .eqTrans b p q, .eqE a c => checkProof p ⟨s.hyps,.eqE a b⟩ && checkProof q ⟨s.hyps,.eqE b c⟩
  | .eqContext ctx a b p, t =>
      t == .eqE (plugContext ctx a) (plugContext ctx b) && checkProof p ⟨s.hyps,.eqE a b⟩
  | .forallBv4Intro p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15, .forallBv4 _ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 =>
      checkProof p0 ⟨s.hyps,t0⟩ && checkProof p1 ⟨s.hyps,t1⟩ && checkProof p2 ⟨s.hyps,t2⟩ && checkProof p3 ⟨s.hyps,t3⟩ && checkProof p4 ⟨s.hyps,t4⟩ && checkProof p5 ⟨s.hyps,t5⟩ && checkProof p6 ⟨s.hyps,t6⟩ && checkProof p7 ⟨s.hyps,t7⟩ && checkProof p8 ⟨s.hyps,t8⟩ && checkProof p9 ⟨s.hyps,t9⟩ && checkProof p10 ⟨s.hyps,t10⟩ && checkProof p11 ⟨s.hyps,t11⟩ && checkProof p12 ⟨s.hyps,t12⟩ && checkProof p13 ⟨s.hyps,t13⟩ && checkProof p14 ⟨s.hyps,t14⟩ && checkProof p15 ⟨s.hyps,t15⟩
  | _, _ => false
termination_by structural p

theorem checkProof_sound (p : ProofCert) (s : Sequent) (h : checkProof p s = true) : Derivable s := by
  induction p generalizing s with
  | axHyp =>
    simp only [checkProof, Bool.and_eq_true, List.contains_iff_mem] at h
    exact .axHyp h.1 h.2
  | primitive =>
    simp only [checkProof, Bool.and_eq_true] at h
    exact .primitive h.1 h.2
  | eqRefl =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkProof, Bool.and_eq_true, Bool.false_eq_true, and_false, beq_iff_eq] at h
    next a b => obtain ⟨wt,rfl⟩ := h; exact .eqRefl wt
  | eqCongr =>
    simp only [checkProof, Bool.and_eq_true] at h
    exact congruenceShape_derivable s h.1 h.2
  | impIntro p ih =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkProof, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
    next a b => exact .impIntro h.1 (ih _ h.2)
  | impElim a p q ihp ihq =>
    simp only [checkProof, Bool.and_eq_true] at h
    exact .impElim h.1 (ihp _ h.2.1) (ihq _ h.2.2)
  | andIntro p q ihp ihq =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkProof, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
    next a b => exact .andIntro h.1 (ihp _ h.2.1) (ihq _ h.2.2)
  | andElimL b p ih =>
    simp only [checkProof, Bool.and_eq_true] at h
    exact .andElimL h.1 (ih _ h.2)
  | andElimR a p ih =>
    simp only [checkProof, Bool.and_eq_true] at h
    exact .andElimR h.1 (ih _ h.2)
  | eqTrans b p q ihp ihq =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkProof, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
    next a c => exact .eqTrans h.1 (ihp _ h.2.1) (ihq _ h.2.2)
  | eqContext ctx a b p ih =>
    obtain ⟨hs,t⟩ := s
    simp only [checkProof, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨wt, rfl, hp⟩ := h
    exact .eqContext wt (ih _ hp)
  | forallBv4Intro p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ih0 ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 ih10 ih11 ih12 ih13 ih14 ih15 =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkProof, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
    next name t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 =>
      obtain ⟨wt, h⟩ := h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
      exact .forallBv4Intro wt (ih0 _ h0) (ih1 _ h1) (ih2 _ h2) (ih3 _ h3) (ih4 _ h4) (ih5 _ h5) (ih6 _ h6) (ih7 _ h7) (ih8 _ h8) (ih9 _ h9) (ih10 _ h10) (ih11 _ h11) (ih12 _ h12) (ih13 _ h13) (ih14 _ h14) (ih15 _ h15)

theorem checkProof_complete {s : Sequent} (h : Derivable s) : ∃ p, checkProof p s = true := by
  induction h with
  | axHyp wt hm => exact ⟨.axHyp, by simp [checkProof, wt, hm]⟩
  | primitive wt hp => exact ⟨.primitive, by simp [checkProof, wt, hp]⟩
  | eqRefl wt => exact ⟨.eqRefl, by simp [checkProof, wt]⟩
  | eqCongr wt => exact ⟨.eqCongr, by simp [checkProof, congruenceShape, wt]⟩
  | @impIntro hs a b wt _ ih0 =>
    obtain ⟨p0,h0⟩ := ih0
    exact ⟨.impIntro p0, by simp [checkProof, wt, h0]⟩
  | @impElim hs a b wt _ _ ih0 ih1 =>
    obtain ⟨p0,h0⟩ := ih0
    obtain ⟨p1,h1⟩ := ih1
    exact ⟨.impElim a p0 p1, by simp [checkProof, wt, h0, h1]⟩
  | @andIntro hs a b wt _ _ ih0 ih1 =>
    obtain ⟨p0,h0⟩ := ih0
    obtain ⟨p1,h1⟩ := ih1
    exact ⟨.andIntro p0 p1, by simp [checkProof, wt, h0, h1]⟩
  | @andElimL hs a b wt _ ih0 =>
    obtain ⟨p0,h0⟩ := ih0
    exact ⟨.andElimL b p0, by simp [checkProof, wt, h0]⟩
  | @andElimR hs a b wt _ ih0 =>
    obtain ⟨p0,h0⟩ := ih0
    exact ⟨.andElimR a p0, by simp [checkProof, wt, h0]⟩
  | @eqTrans hs a b c wt _ _ ih0 ih1 =>
    obtain ⟨p0,h0⟩ := ih0
    obtain ⟨p1,h1⟩ := ih1
    exact ⟨.eqTrans b p0 p1, by simp [checkProof, wt, h0, h1]⟩
  | @eqContext hs ctx a b wt _ ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨.eqContext ctx a b p, by simp [checkProof, wt, hp]⟩
  | forallBv4Intro wt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 ih10 ih11 ih12 ih13 ih14 ih15 =>
    obtain ⟨p0,h0⟩ := ih0
    obtain ⟨p1,h1⟩ := ih1
    obtain ⟨p2,h2⟩ := ih2
    obtain ⟨p3,h3⟩ := ih3
    obtain ⟨p4,h4⟩ := ih4
    obtain ⟨p5,h5⟩ := ih5
    obtain ⟨p6,h6⟩ := ih6
    obtain ⟨p7,h7⟩ := ih7
    obtain ⟨p8,h8⟩ := ih8
    obtain ⟨p9,h9⟩ := ih9
    obtain ⟨p10,h10⟩ := ih10
    obtain ⟨p11,h11⟩ := ih11
    obtain ⟨p12,h12⟩ := ih12
    obtain ⟨p13,h13⟩ := ih13
    obtain ⟨p14,h14⟩ := ih14
    obtain ⟨p15,h15⟩ := ih15
    exact ⟨.forallBv4Intro p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15, by simp [checkProof, wt, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]⟩

theorem checkProof_sem_sound (p : ProofCert) (s : Sequent) (h : checkProof p s = true) : SemValid s :=
  derivable_sound (checkProof_sound p s h)

def forall16 (name : String) (body : BitVec 4 → EmbTerm) : EmbTerm :=
  .forallBv4 name (body 0#4) (body 1#4) (body 2#4) (body 3#4) (body 4#4) (body 5#4) (body 6#4) (body 7#4) (body 8#4) (body 9#4) (body 10#4) (body 11#4) (body 12#4) (body 13#4) (body 14#4) (body 15#4)

def forallCert (body : BitVec 4 → ProofCert) : ProofCert :=
  .forallBv4Intro (body 0#4) (body 1#4) (body 2#4) (body 3#4) (body 4#4) (body 5#4) (body 6#4) (body 7#4) (body 8#4) (body 9#4) (body 10#4) (body 11#4) (body 12#4) (body 13#4) (body 14#4) (body 15#4)

theorem bv4_cases (v : BitVec 4) : v = 0#4 ∨ v = 1#4 ∨ v = 2#4 ∨ v = 3#4 ∨ v = 4#4 ∨ v = 5#4 ∨ v = 6#4 ∨ v = 7#4 ∨ v = 8#4 ∨ v = 9#4 ∨ v = 10#4 ∨ v = 11#4 ∨ v = 12#4 ∨ v = 13#4 ∨ v = 14#4 ∨ v = 15#4 := by
  have hv := v.isLt
  simp only [← BitVec.toNat_inj]
  change v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3 ∨ v.toNat = 4 ∨ v.toNat = 5 ∨ v.toNat = 6 ∨ v.toNat = 7 ∨ v.toNat = 8 ∨ v.toNat = 9 ∨ v.toNat = 10 ∨ v.toNat = 11 ∨ v.toNat = 12 ∨ v.toNat = 13 ∨ v.toNat = 14 ∨ v.toNat = 15
  omega

theorem forall16_holds (name : String) (body : BitVec 4 → EmbTerm) (env : Env) :
    Holds env (forall16 name body) ↔ ∀ v, Holds env (body v) := by
  simp only [forall16, Holds, evalEmbTerm, Val.asBool, Bool.and_eq_true]
  constructor
  · intro h v
    rcases bv4_cases v with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 <;> subst v <;> simp_all
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h 0#4, h 1#4⟩, h 2#4⟩, h 3#4⟩, h 4#4⟩, h 5#4⟩, h 6#4⟩, h 7#4⟩, h 8#4⟩, h 9#4⟩, h 10#4⟩, h 11#4⟩, h 12#4⟩, h 13#4⟩, h 14#4⟩, h 15#4⟩

@[simp] theorem holds_and (env : Env) (a b : EmbTerm) :
    Holds env (.andE a b) ↔ Holds env a ∧ Holds env b := by simp [Holds, evalEmbTerm, Val.asBool]
@[simp] theorem holds_imp (env : Env) (a b : EmbTerm) :
    Holds env (.impE a b) ↔ (Holds env a → Holds env b) := by
  change (!_ || _) = true ↔ (_ = true → _ = true)
  cases (evalEmbTerm env a).asBool <;> cases (evalEmbTerm env b).asBool <;> decide

/-- Extensional quotation of a finite plant and its two policy tables. Each
entry is a real implication in the object logic, beneath two finite binders. -/
def admissibleCase (step : BitVec 4 → BitVec 4 → BitVec 4) (safe : BitVec 4 → Bool)
    (oldp newp : Policy (BitVec 4) (BitVec 4)) (s a : BitVec 4) : EmbTerm :=
  .andE (.impE (.bconst (safe s && newp s a)) (.bconst (safe (step s a))))
    (.impE (.bconst (oldp s a)) (.bconst (newp s a)))

def reflectAdmissibleSequent (step : BitVec 4 → BitVec 4 → BitVec 4) (safe : BitVec 4 → Bool)
    (oldp newp : Policy (BitVec 4) (BitVec 4)) : Sequent :=
  ⟨[], forall16 "s" (fun s => forall16 "a" (admissibleCase step safe oldp newp s))⟩

theorem reflectAdmissible_typed (step : BitVec 4 → BitVec 4 → BitVec 4) (safe : BitVec 4 → Bool)
    (oldp newp : Policy (BitVec 4) (BitVec 4)) :
    sequentTyped (reflectAdmissibleSequent step safe oldp newp) = true := by
  simp [sequentTyped, reflectAdmissibleSequent, forall16, admissibleCase, WellTypedFormula, inferEmbTy]

theorem reflectAdmissible_holds (step : BitVec 4 → BitVec 4 → BitVec 4) (safe : BitVec 4 → Bool)
    (oldp newp : Policy (BitVec 4) (BitVec 4)) (env : Env) :
    Holds env (reflectAdmissibleSequent step safe oldp newp).concl ↔
      AdmissibleUpgrade step (fun s => safe s = true) oldp newp := by
  simp only [reflectAdmissibleSequent, forall16_holds, admissibleCase, holds_and, holds_imp]
  change (∀ s a, ((safe s && newp s a) = true → safe (step s a) = true) ∧
    (oldp s a = true → newp s a = true)) ↔ _
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨fun s a hs hp => (h s a).1 ⟨hs,hp⟩, fun s a hp => (h s a).2 hp⟩
  · intro h s a
    exact ⟨fun ⟨hs,hp⟩ => h.1 s a hs hp, fun hp => h.2 s a hp⟩

theorem reflectAdmissible_iff (step : BitVec 4 → BitVec 4 → BitVec 4) (safe : BitVec 4 → Bool)
    (oldp newp : Policy (BitVec 4) (BitVec 4)) :
    SemValid (reflectAdmissibleSequent step safe oldp newp) ↔
      AdmissibleUpgrade step (fun s => safe s = true) oldp newp := by
  constructor
  · intro h
    exact (reflectAdmissible_holds step safe oldp newp (fun _ _ => .bool false)).1
      (h.2 _ (fun _ h => False.elim (List.not_mem_nil h)))
  · intro h
    exact ⟨reflectAdmissible_typed step safe oldp newp,
      fun env _ => (reflectAdmissible_holds step safe oldp newp env).2 h⟩

def wdStep (s a : BitVec 4) : BitVec 4 := if a = 1 then 0 else s+1
def wdSafe (s : BitVec 4) : Bool := decide (s.toNat ≤ 3)
def wdShield (_ : BitVec 4) : BitVec 4 := 1
def wdOldPol (_ : BitVec 4) (a : BitVec 4) : Bool := a == 1
def wdNewPol (s a : BitVec 4) : Bool := (a == 0 || a == 1) && wdSafe (wdStep s a)
def wdBadPol (_ _ : BitVec 4) : Bool := true

def wdSequent : Sequent := reflectAdmissibleSequent wdStep wdSafe wdOldPol wdNewPol
def wdProofCert : ProofCert := forallCert fun _ => forallCert fun _ => .andIntro .primitive .primitive

theorem forallCert_checkProof (hs : List EmbTerm) (name : String) (cert : BitVec 4 → ProofCert)
    (body : BitVec 4 → EmbTerm) (wt : sequentTyped ⟨hs, forall16 name body⟩ = true)
    (h : ∀ v, checkProof (cert v) ⟨hs, body v⟩ = true) :
    checkProof (forallCert cert) ⟨hs, forall16 name body⟩ = true := by
  unfold forallCert forall16 at *
  simp [checkProof, wt, h]

theorem reflectAdmissible_checkProof (step : BitVec 4 → BitVec 4 → BitVec 4)
    (safe : BitVec 4 → Bool) (oldp newp : Policy (BitVec 4) (BitVec 4))
    (h : AdmissibleUpgrade step (fun s => safe s = true) oldp newp) :
    checkProof wdProofCert (reflectAdmissibleSequent step safe oldp newp) = true := by
  unfold wdProofCert reflectAdmissibleSequent
  apply forallCert_checkProof _ _ _ _ (reflectAdmissible_typed step safe oldp newp)
  intro s
  apply forallCert_checkProof
  · simp [sequentTyped, forall16, admissibleCase, WellTypedFormula, inferEmbTy]
  · intro a
    simp [admissibleCase, checkProof, sequentTyped, WellTypedFormula, inferEmbTy, primitiveTruth]
    refine ⟨?_, ?_⟩
    · cases hs : safe s <;> cases hp : newp s a
      · exact .inl (.inl rfl)
      · exact .inl (.inl rfl)
      · exact .inl (.inr rfl)
      · exact .inr (h.1 s a hs hp)
    · cases ho : oldp s a
      · exact .inl rfl
      · exact .inr (h.2 s a ho)

theorem wd_admissible (s : BitVec 4) :
    AdmissibleUpgrade wdStep (fun x => wdSafe x = true) wdOldPol wdNewPol ∧
    wdSafe (wdStep s (wdShield s)) = true := by
  constructor
  · constructor
    · intro x a _ h; exact (Bool.and_eq_true_iff.mp h).2
    · intro x a h
      have ha : a = 1 := by simpa [wdOldPol] using h
      simp [wdNewPol, wdStep, ha, wdSafe]
  · simp [wdStep, wdShield, wdSafe]

example : checkProof wdProofCert wdSequent = true :=
  reflectAdmissible_checkProof _ _ _ _ (wd_admissible 0).1

theorem wd_encodes_obligation (seq : Sequent) :
    EncodesObligation SemValid seq (AdmissibleUpgrade wdStep (fun s => wdSafe s = true) wdOldPol wdNewPol) :=
  fun _ => (wd_admissible 0).1

theorem wd_encodes_obligation_iff (oldp newp : Policy (BitVec 4) (BitVec 4)) :
    EncodesObligationIff SemValid (reflectAdmissibleSequent wdStep wdSafe oldp newp)
      (AdmissibleUpgrade wdStep (fun s => wdSafe s = true) oldp newp) :=
  reflectAdmissible_iff _ _ _ _

theorem wd_badPol_rejected_under_iff (p : ProofCert) :
    checkProof p (reflectAdmissibleSequent wdStep wdSafe wdNewPol wdBadPol) = false := by
  cases h : checkProof p (reflectAdmissibleSequent wdStep wdSafe wdNewPol wdBadPol) with
  | false => rfl
  | true =>
    have hs := (reflectAdmissible_iff _ _ _ _).1 (checkProof_sem_sound _ _ h)
    have hf := hs.1 3 0 (by decide) rfl
    exact Bool.noConfusion hf

example : ¬ Weaker wdOldPol wdNewPol := fun h => Bool.noConfusion (h 0 0 (by decide))

@[expose] def reflectiveGate {S A : Type} (p : ProofCert) (seq : Sequent)
    (oldp newp : Policy S A) : Policy S A := CertifierRatchet.cgate (checkProof p seq) oldp newp

theorem reflectiveGate_safe {S A : Type} (step : S → A → S) (safe init : S → Prop)
    (oldp newp : Policy S A) (sh ctrl : S → A) (p : ProofCert) (seq : Sequent)
    (he : EncodesObligation SemValid seq (SoundPolicy step safe newp))
    (ho : SoundPolicy step safe oldp) (hi : InitSafe init safe) (hs : SafeShield step safe sh) :
    Invariant step init (enveloped (reflectiveGate p seq oldp newp) sh ctrl) safe := by
  apply safety_preservation hi _ hs
  exact cgate_keeps _ _ _ _ (fun h => he (checkProof_sem_sound p seq h)) ho

theorem watchdog_install_preserves_invariant (oldp : Policy (BitVec 4) (BitVec 4)) :
    reflectiveGate wdProofCert wdSequent oldp wdNewPol = wdNewPol ∧
    ∀ ctrl, Invariant wdStep (fun s => s = 0)
      (enveloped (reflectiveGate wdProofCert wdSequent oldp wdNewPol) wdShield ctrl)
      (fun s => wdSafe s = true) := by
  have accepted : checkProof wdProofCert wdSequent = true :=
    reflectAdmissible_checkProof _ _ _ _ (wd_admissible 0).1
  have installed : reflectiveGate wdProofCert wdSequent oldp wdNewPol = wdNewPol :=
    cgate_installs _ _ _ accepted
  refine ⟨installed, ?_⟩
  rw [installed]
  apply safety_preservation
  · intro s hs; subst s; decide
  · exact (wd_admissible 0).1.1
  · intro s _; exact (wd_admissible s).2

theorem ill_typed_never_semValid (seq : Sequent) (h : WellTypedFormula seq.concl = false) : ¬ SemValid seq := by
  intro hv
  have ht := hv.1
  simp [sequentTyped, h] at ht

def closed : EmbTerm → Bool
  | .var _ _ => false
  | .bconst _ | .bv4 _ => true
  | .notE a | .bitE _ a => closed a
  | .andE a b | .orE a b | .impE a b | .eqE a b => closed a && closed b
  | .iteE c a b => closed c && closed a && closed b
  | .lut4E _ a b c d => closed a && closed b && closed c && closed d
  | .forallBv4 _ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 => closed t0 && closed t1 && closed t2 && closed t3 && closed t4 && closed t5 && closed t6 && closed t7 && closed t8 && closed t9 && closed t10 && closed t11 && closed t12 && closed t13 && closed t14 && closed t15

theorem closed_eval (t : EmbTerm) (h : closed t = true) (env env' : Env) :
    evalEmbTerm env t = evalEmbTerm env' t := by
  induction t <;> simp_all [closed, evalEmbTerm]

/-- Capture-free substitution on the expanded finite syntax. Binder labels
are annotations: their bound occurrences have already been instantiated. -/
def substValue (name : String) (v : Val) : EmbTerm → EmbTerm
  | .var n .boolTy => match v with
      | .bool b => if n = name then .bconst b else .var n .boolTy
      | .bv4 _ => .var n .boolTy
  | .var n .bv4Ty => match v with
      | .bv4 b => if n = name then .bv4 b else .var n .bv4Ty
      | .bool _ => .var n .bv4Ty
  | .bconst b => .bconst b
  | .bv4 b => .bv4 b
  | .notE a => .notE (substValue name v a)
  | .andE a b => .andE (substValue name v a) (substValue name v b)
  | .orE a b => .orE (substValue name v a) (substValue name v b)
  | .impE a b => .impE (substValue name v a) (substValue name v b)
  | .eqE a b => .eqE (substValue name v a) (substValue name v b)
  | .iteE c a b => .iteE (substValue name v c) (substValue name v a) (substValue name v b)
  | .bitE i a => .bitE i (substValue name v a)
  | .lut4E table a b c d => .lut4E table (substValue name v a) (substValue name v b) (substValue name v c) (substValue name v d)
  | .forallBv4 label t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 => .forallBv4 label (substValue name v t0) (substValue name v t1) (substValue name v t2) (substValue name v t3) (substValue name v t4) (substValue name v t5) (substValue name v t6) (substValue name v t7) (substValue name v t8) (substValue name v t9) (substValue name v t10) (substValue name v t11) (substValue name v t12) (substValue name v t13) (substValue name v t14) (substValue name v t15)

def substBv4 (name : String) (v : BitVec 4) (body : EmbTerm) : EmbTerm := substValue name (.bv4 v) body

def freeVars : EmbTerm → List (String × EmbTy)
  | .var n ty => [(n,ty)]
  | .bconst _ | .bv4 _ => []
  | .notE a => freeVars a
  | .andE a b => freeVars a ++ freeVars b
  | .orE a b => freeVars a ++ freeVars b
  | .impE a b => freeVars a ++ freeVars b
  | .eqE a b => freeVars a ++ freeVars b
  | .iteE c a b => freeVars c ++ freeVars a ++ freeVars b
  | .bitE _ a => freeVars a
  | .lut4E _ a b c d => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d
  | .forallBv4 _ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 => freeVars t0 ++ freeVars t1 ++ freeVars t2 ++ freeVars t3 ++ freeVars t4 ++ freeVars t5 ++ freeVars t6 ++ freeVars t7 ++ freeVars t8 ++ freeVars t9 ++ freeVars t10 ++ freeVars t11 ++ freeVars t12 ++ freeVars t13 ++ freeVars t14 ++ freeVars t15

def envValue (env : Env) (n : String) : EmbTy → Val
  | .boolTy => .bool (env n .boolTy).asBool
  | .bv4Ty => .bv4 (env n .bv4Ty).asBv4

theorem substValue_same (env : Env) (name : String) (ty : EmbTy) (t : EmbTerm) :
    evalEmbTerm env (substValue name (envValue env name ty) t) = evalEmbTerm env t := by
  induction t with
  | var n t =>
    cases t <;> cases ty <;> by_cases h : n = name <;>
      simp [substValue, envValue, evalEmbTerm, h]
  | _ => simp_all [substValue, evalEmbTerm]

def closeFor (var : String × EmbTy) (t : EmbTerm) : EmbTerm :=
  match var.2 with
  | .boolTy => .andE (substValue var.1 (.bool false) t) (substValue var.1 (.bool true) t)
  | .bv4Ty => forall16 var.1 (fun v => substBv4 var.1 v t)

theorem closeFor_elim (env : Env) (var : String × EmbTy) (t : EmbTerm)
    (h : Holds env (closeFor var t)) : Holds env t := by
  obtain ⟨name,ty⟩ := var
  cases ty with
  | boolTy =>
    have hh := (holds_and _ _ _).1 h
    have he := substValue_same env name .boolTy t
    cases hv : (env name .boolTy).asBool with
    | false =>
      simp only [envValue, hv] at he
      simpa only [Holds, he] using hh.1
    | true =>
      simp only [envValue, hv] at he
      simpa only [Holds, he] using hh.2
  | bv4Ty =>
    change Holds env (forall16 name (fun v => substBv4 name v t)) at h
    have hh := (forall16_holds _ _ _).1 h ((env name .bv4Ty).asBv4)
    have he := substValue_same env name .bv4Ty t
    dsimp only [envValue] at he
    simpa only [Holds, substBv4, he] using hh

def closeAll (vars : List (String × EmbTy)) (t : EmbTerm) : EmbTerm :=
  vars.foldl (fun body var => closeFor var body) t

theorem closeAll_elim (env : Env) (vars : List (String × EmbTy)) (t : EmbTerm)
    (h : Holds env (closeAll vars t)) : Holds env t := by
  induction vars generalizing t with
  | nil => exact h
  | cons v vs ih => exact closeFor_elim env v t (ih _ h)

def closeFormula (t : EmbTerm) : EmbTerm :=
  if closed t then t else closeAll (freeVars t).eraseDups t

theorem closeFormula_elim (env : Env) (t : EmbTerm) (h : Holds env (closeFormula t)) : Holds env t := by
  unfold closeFormula at h
  split at h
  · exact h
  · exact closeAll_elim env _ t h

inductive FastProofCert where
  | embedBaseProof (p : ProofCert)
  | fastSym
  | fastDecideClosed
  deriving Repr

/-- The fast rule closes free Boolean and BV4 variables by exhaustive finite
instantiation. It checks that closure succeeded before evaluating the result. -/
def checkFastProof (p : FastProofCert) (s : Sequent) : Bool :=
  match p with
  | .embedBaseProof p => checkProof p s
  | .fastSym => sequentTyped s && match s.concl with
      | .eqE b a => s.hyps.contains (.eqE a b)
      | _ => false
  | .fastDecideClosed => sequentTyped s && closed (closeFormula s.concl) &&
      (evalEmbTerm (fun _ _ => .bool false) (closeFormula s.concl)).asBool

theorem fastKernel_sound (p : FastProofCert) (s : Sequent)
    (h : checkFastProof p s = true) : SemValid s := by
  cases p with
  | embedBaseProof p => exact checkProof_sem_sound p s h
  | fastSym =>
    obtain ⟨hs,t⟩ := s
    cases t <;> simp only [checkFastProof, Bool.and_eq_true, Bool.false_eq_true, and_false,
      List.contains_iff_mem] at h
    next b a =>
      refine ⟨h.1, fun env hh => ?_⟩
      have he := hh _ h.2
      simp only [Holds, evalEmbTerm, Val.asBool, decide_eq_true_eq] at he ⊢
      exact he.symm
  | fastDecideClosed =>
    simp only [checkFastProof, Bool.and_eq_true] at h
    refine ⟨h.1.1, fun env _ => ?_⟩
    apply closeFormula_elim env s.concl
    unfold Holds
    rw [closed_eval (closeFormula s.concl) h.1.2 env (fun _ _ => .bool false)]
    exact h.2

theorem fastKernel_inhabited (b : Bool) :
    checkFastProof (.embedBaseProof .eqRefl) ⟨[],.eqE (.bconst b) (.bconst b)⟩ = true := by
  cases b <;> rfl

theorem fastKernel_extends_base (p : ProofCert) (s : Sequent) :
    checkFastProof (.embedBaseProof p) s = checkProof p s := by simp [checkFastProof]


def baseCertSize : ProofCert → Nat
  | .axHyp | .primitive | .eqRefl | .eqCongr => 1
  | .impIntro p | .andElimL _ p | .andElimR _ p | .eqContext _ _ _ p => 1 + baseCertSize p
  | .impElim _ p q | .andIntro p q | .eqTrans _ p q => 1 + baseCertSize p + baseCertSize q
  | .forallBv4Intro p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 => 1 + baseCertSize p0 + baseCertSize p1 + baseCertSize p2 + baseCertSize p3 + baseCertSize p4 + baseCertSize p5 + baseCertSize p6 + baseCertSize p7 + baseCertSize p8 + baseCertSize p9 + baseCertSize p10 + baseCertSize p11 + baseCertSize p12 + baseCertSize p13 + baseCertSize p14 + baseCertSize p15

def fastCertSize : FastProofCert → Nat
  | .embedBaseProof p => baseCertSize p
  | .fastSym | .fastDecideClosed => 1

def symBaseProof (a b : EmbTerm) : ProofCert :=
  .impElim (.eqE a a)
    (.impElim (.eqE a b) .eqCongr .axHyp) .eqRefl

theorem sym_certificate_reduction (b : Bool) :
    let a := EmbTerm.bconst b
    let t := EmbTerm.notE (.notE a)
    let seq : Sequent := ⟨[.eqE a t], .eqE t a⟩
    checkProof (symBaseProof a t) seq = true ∧ checkFastProof .fastSym seq = true ∧
      fastCertSize .fastSym < baseCertSize (symBaseProof a t) := by
  cases b <;> decide

theorem fastSym_conservative (s : Sequent) (h : checkFastProof .fastSym s = true) :
    ∃ p, checkProof p s = true := by
  obtain ⟨hs, t⟩ := s
  cases t <;> simp only [checkFastProof, Bool.and_eq_true, Bool.false_eq_true, and_false,
    List.contains_iff_mem] at h
  next b a =>
    obtain ⟨wt, hmem⟩ := h
    have whs : hs.all WellTypedFormula = true := (Bool.and_eq_true_iff.mp wt).1
    have wab : WellTypedFormula (.eqE a b) = true := (List.all_eq_true.mp whs) _ hmem
    have heqty : ∃ ty, inferEmbTy a = some ty ∧ inferEmbTy b = some ty := by
      simp only [WellTypedFormula, inferEmbTy] at wab
      cases ha : inferEmbTy a <;> cases hb : inferEmbTy b <;> simp_all [beq_iff_eq]
    obtain ⟨ty, ha, hb⟩ := heqty
    refine ⟨symBaseProof a b, ?_⟩
    simp [symBaseProof, checkProof, congruenceShape, sequentTyped, whs,
      WellTypedFormula, inferEmbTy, ha, hb, hmem]

theorem fastKernel_conservative_over_base (step : BitVec 4 → BitVec 4 → BitVec 4)
    (safe : BitVec 4 → Bool) (oldp newp : Policy (BitVec 4) (BitVec 4)) (p : FastProofCert)
    (h : checkFastProof p (reflectAdmissibleSequent step safe oldp newp) = true) :
    Derivable (reflectAdmissibleSequent step safe oldp newp) ∧
      checkProof wdProofCert (reflectAdmissibleSequent step safe oldp newp) = true := by
  have hadm : AdmissibleUpgrade step (fun s => safe s = true) oldp newp :=
    (reflectAdmissible_iff step safe oldp newp).1 (fastKernel_sound p _ h)
  have hbase : checkProof wdProofCert (reflectAdmissibleSequent step safe oldp newp) = true :=
    reflectAdmissible_checkProof step safe oldp newp hadm
  exact ⟨checkProof_sound _ _ hbase, hbase⟩

/-- A kernel value includes its certificate protocol, so changing implementations
never smuggles an unverified proof parser into the gate. -/
abbrev KernelChecker := FastProofCert → Sequent → Bool
def SoundKernel (K : KernelChecker) : Prop := ∀ p seq, K p seq = true → SemValid seq

def BaseKernel : KernelChecker
  | .embedBaseProof p, seq => checkProof p seq
  | _, _ => false
abbrev FastKernel : KernelChecker := checkFastProof

def SoundExtension (old new : KernelChecker) : Prop :=
  SoundKernel new ∧ ∀ p seq, old p seq = true → new p seq = true

theorem baseKernel_sound (p : FastProofCert) (seq : Sequent)
    (h : BaseKernel p seq = true) : SemValid seq := by
  cases p with
  | embedBaseProof p => exact checkProof_sem_sound p seq h
  | fastSym => cases h
  | fastDecideClosed => cases h

theorem baseKernel_inhabited (b : Bool) :
    BaseKernel (.embedBaseProof .eqRefl) ⟨[],.eqE (.bconst b) (.bconst b)⟩ = true := by cases b <;> rfl

theorem fastKernel_is_sound_extension (K : KernelChecker) (h : K = BaseKernel) : SoundExtension K FastKernel := by
  subst K
  refine ⟨fastKernel_sound, ?_⟩
  intro p seq hp
  cases p with
  | embedBaseProof p => exact hp
  | fastSym => cases hp
  | fastDecideClosed => cases hp

theorem kernel_hot_swap_safe {S A : Type} (line : Nat → KernelChecker)
    (h0 : SoundKernel (line 0)) (hs : ratchetStream SoundExtension line)
    (step : S → A → S) (safe init : S → Prop) (oldp newp : Policy S A)
    (sh ctrl : S → A) (hi : InitSafe init safe) (hsh : SafeShield step safe sh)
    (ho : SoundPolicy step safe oldp) (n : Nat) (p : FastProofCert) (seq : Sequent)
    (he : EncodesObligation SemValid seq (SoundPolicy step safe newp)) :
    SoundKernel (line n) ∧ Invariant step init
      (enveloped (CertifierRatchet.cgate (line n p seq) oldp newp) sh ctrl) safe := by
  have hn : SoundKernel (line n) := ratchet_stream_safe line (fun _ _ _ h => h.1) h0 hs n
  exact ⟨hn, safety_preservation hi (cgate_keeps _ _ _ _ (fun hp => he (hn p seq hp)) ho) hsh ctrl⟩

/-- Mathematical admission of the whole base calculus. The executable APIs
remain checkProof and BaseKernel; this existential census is not an algorithm. -/
noncomputable def baseKernelAdmits (seq : Sequent) : Bool :=
  @decide (Derivable seq) (Classical.propDecidable _)

theorem baseKernelAdmits_iff (seq : Sequent) : baseKernelAdmits seq = true ↔ ∃ p, checkProof p seq = true := by
  simp only [baseKernelAdmits, decide_eq_true_eq]
  exact ⟨checkProof_complete, fun ⟨p,h⟩ => checkProof_sound p seq h⟩

theorem baseKernelAdmits_sem_sound (seq : Sequent) (h : baseKernelAdmits seq = true) : SemValid seq :=
  by
    classical
    exact derivable_sound (of_decide_eq_true h)

theorem baseKernelAdmits_inhabited (name : String) :
    baseKernelAdmits ⟨[],.eqE (.var name .boolTy) (.var name .boolTy)⟩ = true := by
  classical
  apply decide_eq_true
  apply Derivable.eqRefl
  simp [sequentTyped, WellTypedFormula, inferEmbTy]

def EncodesKernelSoundness (seq : Sequent) (K : KernelChecker) : Prop := SemValid seq → SoundKernel K
def LoebReflection (old new : KernelChecker) (p : FastProofCert) (seq : Sequent) : Prop :=
  old p seq = true → SoundKernel new
def KernelSoundnessWitness (K : KernelChecker) : Prop := ∃ seq, SemValid seq ∧ EncodesKernelSoundness seq K

def acceptAllKernel : KernelChecker := fun _ _ => true

theorem accept_all_kernel_unsound (name : String) : ¬ SoundKernel acceptAllKernel := by
  intro h
  exact ill_typed_never_semValid ⟨[],.var name .bv4Ty⟩ rfl (h .fastSym ⟨[],.var name .bv4Ty⟩ rfl)

/-- A diagonal falsehood cannot be both certified and truth-preserving. This
uses only the displayed fixed-point equivalence, not a hidden reflection rule. -/
theorem diagonal_self_reference_obstruction {O : Type} (K : O → Bool) (sem : O → Prop)
    (d : O) (fixed : sem d ↔ K d ≠ true) (sound : SoundCertifier K sem) :
    K d = false ∧ sem d := by
  have hn : K d ≠ true := fun h => (fixed.1 (sound d h)) h
  exact ⟨Bool.eq_false_iff.mpr hn, fixed.2 hn⟩

theorem diagonal_reflection_forces_truth {O : Type} (K : O → Bool) (sem : O → Prop)
    (diag : (O → Prop) → O) (fixed : ∀ P, sem (diag P) ↔ (K (diag P) = true → P (diag P)))
    (sound : SoundCertifier K sem) (P : O → Prop) (certified : K (diag P) = true) : P (diag P) :=
  (fixed P).1 (sound _ certified) certified

/-- Finiteness of the habitat establishes its policy facts, but supplies no
soundness evidence for a checker admitting an ill-typed formula. -/
theorem loeb_finite_obstruction (name : String) :
    AdmissibleUpgrade wdStep (fun s => wdSafe s = true) wdOldPol wdNewPol ∧
    (∀ seq, EncodesObligation SemValid seq
      (AdmissibleUpgrade wdStep (fun s => wdSafe s = true) wdOldPol wdNewPol)) ∧
    (∀ p seq, BaseKernel p seq = true → acceptAllKernel p seq = true) ∧
    (∃ p seq, acceptAllKernel p seq = true ∧ BaseKernel p seq = false) ∧
    (∃ p seq, BaseKernel p seq = true ∧ ¬ EncodesKernelSoundness seq acceptAllKernel ∧
      ¬ LoebReflection BaseKernel acceptAllKernel p seq) ∧
    ¬ SoundKernel acceptAllKernel ∧ ¬ KernelSoundnessWitness acceptAllKernel := by
  have hn := accept_all_kernel_unsound name
  refine ⟨(wd_admissible 0).1, wd_encodes_obligation, fun _ _ _ => rfl,
    ⟨.fastSym, ⟨[],.var name .bv4Ty⟩, rfl, rfl⟩, ?_, hn, ?_⟩
  · let seq : Sequent := ⟨[],.eqE (.bconst true) (.bconst true)⟩
    have hc : BaseKernel (.embedBaseProof .eqRefl) seq = true := rfl
    exact ⟨.embedBaseProof .eqRefl, seq, hc, fun h => hn (h (baseKernel_sound _ _ hc)), fun h => hn (h hc)⟩
  · rintro ⟨seq, hv, he⟩; exact hn (he hv)

theorem loeb_finite_obstruction_admission (name : String) :
    ∃ K' : Sequent → Bool,
      (∀ seq, baseKernelAdmits seq = true → K' seq = true) ∧
      (∃ seq, K' seq = true ∧ baseKernelAdmits seq = false) ∧
      ¬ SoundCertifier K' SemValid := by
  let seq : Sequent := ⟨[],.var name .bv4Ty⟩
  have invalid : ¬ SemValid seq := ill_typed_never_semValid seq rfl
  have rejected : baseKernelAdmits seq = false := by
    cases h : baseKernelAdmits seq with
    | false => rfl
    | true => exact (invalid (baseKernelAdmits_sem_sound seq h)).elim
  exact ⟨fun _ => true, fun _ _ => rfl, ⟨seq,rfl,rejected⟩, fun h => invalid (h seq rfl)⟩

theorem unfaithful_encoding_can_breach (name : String) :
    ∃ seq, SemValid seq ∧ ¬ EncodesObligation SemValid seq
      (SoundPolicy wdStep (fun s => wdSafe s = true) wdBadPol) := by
  let seq : Sequent := ⟨[], .eqE (.var name .boolTy) (.var name .boolTy)⟩
  have hv : SemValid seq := checkProof_sem_sound .eqRefl seq (by
    simp [seq, checkProof, sequentTyped, WellTypedFormula, inferEmbTy])
  refine ⟨seq, hv, ?_⟩
  intro h
  exact Bool.noConfusion (h hv 3 0 (by decide) rfl)

end Obend.Judge.ReflectiveGate
