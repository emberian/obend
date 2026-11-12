module
/-
# `Obend.Leaf.SelfApplicableMix` — Genuine 1st/2nd/3rd Futamura Projections & `Core4` Lowering

Builds on `Obend.Leaf.SelfApplicableMixCore` to prove all three genuine Jones–Gomard–Sestoft
Futamura projections returning residual `MixProg` ASTs (`futamura1_target_sound`,
`futamura2_self_application_compiler_sound`, `futamura3_self_self_cogen_sound`), inhabit all three
projections (`futamura1_target_inhabited` + `#guard` witnesses for Futamura 2 and 3), and lower
`MixProg` with simulation and machine-completeness proofs to `Obend.Core.Term`
(`lowerMixToCore4_sound`, `lowerMixToCore4_machine_complete`).
-/
public import Obend.Leaf.SelfApplicableMixCore
public import Obend.Core.Term
public import Obend.Core.TermTraverse
public import Obend.Core.Machine
public import Obend.Core.MachineFast
public import Obend.Core.Invariant
public import Obend.Core.Proofs.Adequacy.Scoped
public import Obend.Core.Proofs.Completeness
import all Obend.Leaf.SelfApplicableMixCore
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Machine
import all Obend.Core.Invariant
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Completeness

public section
namespace Obend.Leaf.SelfApplicableMix

open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
open Obend.Core.Proofs.Adequacy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## 1. Genuine 1st, 2nd & 3rd Futamura Projection Theorems -/

/-- **1st Futamura Projection (`futamura1_target_sound`)**:
    Specializing an object interpreter `interp` at `srcVal` via `mixProg` yields residual target code
    `target : MixProg` (`evalMix fuelMix mixProg (quoteProg interp) srcVal = some (quoteProg target)`)
    with zero static AST dispatch (`hasStaticConstruct target = false`) agreeing with `interp` on all `d`. -/
theorem futamura1_target_sound
    (fuelMix kd : Nat) (interp : MixProg) (srcVal : MixVal) (target : MixProg)
    (hMix : runMixSpecialize fuelMix interp srcVal = some target)
    (hCert : checkSpecializesProg kd interp srcVal target = true) :
    evalMix fuelMix mixProg (quoteProg interp) srcVal = some (quoteProg target) ∧
    hasStaticConstruct target = false ∧
    (∀ (d v : MixVal),
      (∃ fuel, evalMix fuel interp srcVal d = some v) ↔
      (∃ targetFuel, evalMix targetFuel target .nil d = some v)) := by
  unfold runMixSpecialize at hMix
  cases hEval : evalMix fuelMix mixProg (quoteProg interp) srcVal with
  | none => simp [hEval] at hMix
  | some qRes =>
    simp only [hEval] at hMix
    obtain ⟨hStrip, hSem⟩ := checkSpecializesProg_sound hCert
    exact ⟨congrArg some (quote_of_unquoteProg hMix), hStrip, hSem⟩

/-- **2nd Futamura Projection (`futamura2_self_application_compiler_sound`)**:
    Self-applying `mixProg` to `(quoteProg mixProg, quoteProg interp)` inside `evalMix` produces a
    standalone 1-level **compiler** `compilerProg : MixProg` (`hasStaticConstruct compilerProg = false`)
    turning any `srcVal` into `quoteProg target`, whose execution on any `d` matches `interp`. -/
theorem futamura2_self_application_compiler_sound
    (fuelSelf kdComp : Nat) (interp compilerProg : MixProg)
    (hSelf : runMixSpecialize fuelSelf mixProg (quoteProg interp) = some compilerProg)
    (hCompCert : checkSpecializesProg kdComp mixProg (quoteProg interp) compilerProg = true) :
    evalMix fuelSelf mixProg (quoteProg mixProg) (quoteProg interp) = some (quoteProg compilerProg) ∧
    hasStaticConstruct compilerProg = false ∧
    (∀ (srcVal qTarget : MixVal),
      (∃ fuelComp, evalMix fuelComp compilerProg .nil srcVal = some qTarget) ↔
      (∃ fuelMix, evalMix fuelMix mixProg (quoteProg interp) srcVal = some qTarget)) ∧
    (∀ (fuelComp kdTarget : Nat) (srcVal : MixVal) (target : MixProg),
      evalMix fuelComp compilerProg .nil srcVal = some (quoteProg target) →
      checkSpecializesProg kdTarget interp srcVal target = true →
      ∀ (d v : MixVal),
        (∃ fuel, evalMix fuel interp srcVal d = some v) ↔
        (∃ targetFuel, evalMix targetFuel target .nil d = some v)) := by
  unfold runMixSpecialize at hSelf
  cases hEval : evalMix fuelSelf mixProg (quoteProg mixProg) (quoteProg interp) with
  | none => simp [hEval] at hSelf
  | some qRes =>
    simp only [hEval] at hSelf
    obtain ⟨hStrip, hSem⟩ := checkSpecializesProg_sound hCompCert
    refine ⟨congrArg some (quote_of_unquoteProg hSelf), hStrip, ?_, ?_⟩
    · intro srcVal qTarget; exact (hSem srcVal qTarget).symm
    · intro _ _ _ _ _ hTargetCert d v; exact (checkSpecializesProg_sound hTargetCert).2 d v

/-- **3rd Futamura Projection (`futamura3_self_self_cogen_sound`)**:
    Self-applying `mixProg` to `(quoteProg mixProg, quoteProg mixProg)` inside `evalMix` produces a
    standalone 1-level **compiler-generator (`cogen`)** `cogenProg : MixProg`
    (`hasStaticConstruct cogenProg = false`) turning any `quoteProg interp` into a standalone compiler. -/
theorem futamura3_self_self_cogen_sound
    (fuelCogenGen kdCogen : Nat) (cogenProg : MixProg)
    (hCogen : runMixSpecialize fuelCogenGen mixProg (quoteProg mixProg) = some cogenProg)
    (hCogenCert : checkSpecializesProg kdCogen mixProg (quoteProg mixProg) cogenProg = true) :
    evalMix fuelCogenGen mixProg (quoteProg mixProg) (quoteProg mixProg) = some (quoteProg cogenProg) ∧
    hasStaticConstruct cogenProg = false ∧
    (∀ (interp : MixProg) (qCompiler : MixVal),
      (∃ fuelRunCogen, evalMix fuelRunCogen cogenProg .nil (quoteProg interp) = some qCompiler) ↔
      (∃ fuelSelf, evalMix fuelSelf mixProg (quoteProg mixProg) (quoteProg interp) = some qCompiler)) ∧
    (∀ (fuelRunCogen kdComp : Nat) (interp compilerProg : MixProg),
      evalMix fuelRunCogen cogenProg .nil (quoteProg interp) = some (quoteProg compilerProg) →
      checkSpecializesProg kdComp mixProg (quoteProg interp) compilerProg = true →
      ∀ (srcVal qTarget : MixVal),
        (∃ fuelComp, evalMix fuelComp compilerProg .nil srcVal = some qTarget) ↔
        (∃ fuelMix, evalMix fuelMix mixProg (quoteProg interp) srcVal = some qTarget)) := by
  unfold runMixSpecialize at hCogen
  cases hEval : evalMix fuelCogenGen mixProg (quoteProg mixProg) (quoteProg mixProg) with
  | none => simp [hEval] at hCogen
  | some qRes =>
    simp only [hEval] at hCogen
    obtain ⟨hStrip, hSem⟩ := checkSpecializesProg_sound hCogenCert
    refine ⟨congrArg some (quote_of_unquoteProg hCogen), hStrip, ?_, ?_⟩
    · intro interp qCompiler; exact (hSem (quoteProg interp) qCompiler).symm
    · intro _ _ _ _ _ hCompCert srcVal qTarget; exact ((checkSpecializesProg_sound hCompCert).2 srcVal qTarget).symm

/-- **Full End-to-End 3rd Futamura Object-Semantic Chain (`futamura3_end_to_end_object_sound`)**:
    Chains `cogenProg = mix(⌜mix⌝, ⌜mix⌝)` → `compilerProg = cogen(⌜interp⌝)` →
    `target = compiler(srcVal)` all the way down to object-program dynamic evaluation `evalMix`. -/
theorem futamura3_end_to_end_object_sound
    (fuelCogenGen kdCogen fuelRunCogen kdComp fuelComp kdTarget : Nat)
    (cogenProg interp compilerProg target : MixProg) (srcVal : MixVal)
    (hCogen : runMixSpecialize fuelCogenGen mixProg (quoteProg mixProg) = some cogenProg)
    (hCogenCert : checkSpecializesProg kdCogen mixProg (quoteProg mixProg) cogenProg = true)
    (hGenComp : evalMix fuelRunCogen cogenProg .nil (quoteProg interp) = some (quoteProg compilerProg))
    (hCompCert : checkSpecializesProg kdComp mixProg (quoteProg interp) compilerProg = true)
    (hGenTarget : evalMix fuelComp compilerProg .nil srcVal = some (quoteProg target))
    (hTargetCert : checkSpecializesProg kdTarget interp srcVal target = true) :
    evalMix fuelCogenGen mixProg (quoteProg mixProg) (quoteProg mixProg) = some (quoteProg cogenProg) ∧
    hasStaticConstruct cogenProg = false ∧
    hasStaticConstruct compilerProg = false ∧
    hasStaticConstruct target = false ∧
    (∃ fuelMix, evalMix fuelMix mixProg (quoteProg interp) srcVal = some (quoteProg target)) ∧
    (∀ (d v : MixVal),
      (∃ fuel, evalMix fuel interp srcVal d = some v) ↔
      (∃ targetFuel, evalMix targetFuel target .nil d = some v)) := by
  obtain ⟨hCgEv, hCgStrip, _, hCgComp⟩ := futamura3_self_self_cogen_sound fuelCogenGen kdCogen cogenProg hCogen hCogenCert
  obtain ⟨hCpStrip, _⟩ := checkSpecializesProg_sound hCompCert
  obtain ⟨hTgStrip, hTgSem⟩ := checkSpecializesProg_sound hTargetCert
  exact ⟨hCgEv, hCgStrip, hCpStrip, hTgStrip,
    (hCgComp fuelRunCogen kdComp interp compilerProg hGenComp hCompCert srcVal (quoteProg target)).mp ⟨fuelComp, hGenTarget⟩,
    hTgSem⟩

/-! ## 2. Object Source Language (`ObjSrc`), `objInterp`, & Inhabitedness of Futamura 1/2/3 -/

inductive ObjSrc where
  | lit (n : Nat) | var0 | var1
  | add (a b : ObjSrc) | sub (a b : ObjSrc) | mul (a b : ObjSrc) | lt (a b : ObjSrc)
  | ifPos (cond eThen eElse : ObjSrc) | let1 (bound body : ObjSrc)
  | whilePos (cond stepBody resultExpr : ObjSrc)
  deriving DecidableEq, Repr

def quoteObjSrc : ObjSrc → MixVal
  | .lit n => .pair (.sym .lit) (.num n)
  | .var0 => .pair (.sym .var0) .nil
  | .var1 => .pair (.sym .var1) .nil
  | .add a b => .pair (.sym .add) (.pair (quoteObjSrc a) (quoteObjSrc b))
  | .sub a b => .pair (.sym .sub) (.pair (quoteObjSrc a) (quoteObjSrc b))
  | .mul a b => .pair (.sym .mul) (.pair (quoteObjSrc a) (quoteObjSrc b))
  | .lt a b => .pair (.sym .lt) (.pair (quoteObjSrc a) (quoteObjSrc b))
  | .ifPos c t f => .pair (.sym .ifPos) (.pair (quoteObjSrc c) (.pair (quoteObjSrc t) (quoteObjSrc f)))
  | .let1 b body => .pair (.sym .let1) (.pair (quoteObjSrc b) (quoteObjSrc body))
  | .whilePos c step res =>
    .pair (.sym .whilePos) (.pair (quoteObjSrc c) (.pair (quoteObjSrc step) (quoteObjSrc res)))

def objInterp : MixProg :=
  let tag := sFst .var; let pay := sSnd .var; let e1 := sFst pay; let e2 := sSnd pay
  let evalSub (sub : SExpr) : MixExpr := .sCall (.sym .eval) sub .dVar
  { entry := .sym .entry
  , procs :=
      [ { name := .sym .entry, body := .sCall (.sym .eval) .var (dCons .dVar (.dLit .nil)) }
      , { name := .sym .eval
        , body :=
            .sIf (sEqSym tag .lit) (.dLift pay)
            (.sIf (sEqSym tag .var0) (dFst .dVar)
            (.sIf (sEqSym tag .var1) (dFst (dSnd .dVar))
            (.sIf (sEqSym tag .add) (.dBin .add (evalSub e1) (evalSub e2))
            (.sIf (sEqSym tag .sub) (.dBin .sub (evalSub e1) (evalSub e2))
            (.sIf (sEqSym tag .mul) (.dBin .mul (evalSub e1) (evalSub e2))
            (.sIf (sEqSym tag .lt) (.dBin .lt (evalSub e1) (evalSub e2))
            (.sIf (sEqSym tag .ifPos) (.dIf (evalSub e1) (evalSub (sFst e2)) (evalSub (sSnd e2)))
            (.sIf (sEqSym tag .let1) (.dWithEnv (dCons (evalSub e1) .dVar) (evalSub e2))
              (.dWithEnv (.dWhile (evalSub e1) (dCons (evalSub (sFst e2)) (dSnd .dVar)))
                (evalSub (sSnd e2))))))))))) } ] }

/-- Quadratic polynomial `x * x + 3 * x + 5` in `ObjSrc`. -/
def quadPolyObjSrc : ObjSrc :=
  .add (.add (.mul .var0 .var0) (.mul (.lit 3) .var0)) (.lit 5)

set_option maxRecDepth 200000 in
/-- Universal inhabitedness witness for `futamura1_target_sound` across all dynamic inputs `x`. -/
theorem futamura1_target_inhabited (x : Nat) :
    ∃ target : MixProg,
      runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) = some target ∧
      checkSpecializesProg 40 objInterp (quoteObjSrc quadPolyObjSrc) target = true ∧
      progSize target < progSize objInterp ∧
      evalMix 40 target .nil (.num x) = some (.num (x * x + 3 * x + 5)) := by
  have h1 : (match runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) with
      | some t => checkSpecializesProg 40 objInterp (quoteObjSrc quadPolyObjSrc) t &&
                  decide (progSize t < progSize objInterp)
      | none => false) = true := by decide
  cases hr1 : runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) with
  | none => rw [hr1] at h1; cases h1
  | some target =>
    rw [hr1] at h1; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨target, rfl, h1.1, h1.2, ?_⟩
    have hDec : runMixSpecialize 400 objInterp (quoteObjSrc quadPolyObjSrc) =
        some { entry := .sym .entry
             , procs := [{ name := .sym .entry
                         , body := .dWithEnv (.dBin .cons .dVar (.dLit .nil))
                             (.dBin .add
                               (.dBin .add
                                 (.dBin .mul (.dUnary .fst .dVar) (.dUnary .fst .dVar))
                                 (.dBin .mul (.dLit (.num 3)) (.dUnary .fst .dVar)))
                               (.dLit (.num 5))) }] } := by decide
    rw [hr1] at hDec; injection hDec with hTargetEq; subst hTargetEq; rfl

-- Inhabitedness witnesses confirming all premises of `futamura2` (standalone 6-proc compiler) and `futamura3` (standalone 13-proc cogen):
#guard match runMixSpecialize 3000 mixProg (quoteProg objInterp) with
  | some c => checkSpecializesProg 300 mixProg (quoteProg objInterp) c && !hasStaticConstruct c && c.procs.length == 6
  | none => false

#guard match runMixSpecialize 4000 mixProg (quoteProg mixProg) with
  | some cg => checkSpecializesProg 280 mixProg (quoteProg mixProg) cg && !hasStaticConstruct cg && cg.procs.length == 13
  | none => false

/-! ## 3. Verified `Core4` Lowering (`lowerMixToCore4`, `lowerMixToCore4_sound`, `lowerMixToCore4_machine_complete`) -/

/-- Canonical `Core4` representation of a `MixVal` datum. -/
@[expose] def encodeMixVal : MixVal → Term
  | .nil => .inject "nil" (.nat 0)
  | .num n => .inject "num" (.nat n)
  | .sym s => .inject "sym" (.nat s.toCode)
  | .pair a b => .inject "pair" (.record [("fst", encodeMixVal a), ("snd", encodeMixVal b)])

/-- Canonical `Core4` representation of an `Option MixVal` result. -/
@[expose] def encodeOptMixVal : Option MixVal → Term
  | none => .inject "none" (.nat 0)
  | some v => .inject "some" (encodeMixVal v)

@[simp] private theorem scoped_nat_true (n v : Nat) : Scoped n (.nat v) := .natural v
@[simp] private theorem scoped_bool_true (n : Nat) (b : Bool) : Scoped n (.boolean b) := .boolean b

private theorem scoped0_sub {t : Term} (h : Scoped 0 t) (σ : Nat → Term) : t.substitute σ = t :=
  scoped_substitute_identity h σ (fun _ hi => absurd hi (Nat.not_lt_zero _))

private theorem scoped0_ren {t : Term} (h : Scoped 0 t) (f : Nat → Nat) : t.rename f = t :=
  Obend.Core.TermTraverse.scoped_rename_identity t 0 ((scoped_encode_iff 0 t).1 h) f
    (fun _ hi => absurd hi (Nat.not_lt_zero _))

private theorem scoped0_any {t : Term} (h : Scoped 0 t) (n : Nat) : Scoped n t := by
  have hr := Obend.Core.TermTraverse.scoped_rename t 0 n ((scoped_encode_iff 0 t).1 h) id
    (fun _ hi => absurd hi (Nat.not_lt_zero _))
  rwa [scoped0_ren h id, ← scoped_encode_iff n t] at hr

theorem encodeMixVal_scoped (v : MixVal) : Scoped 0 (encodeMixVal v) := by
  induction v with
  | nil | num _ | sym _ => simp [encodeMixVal]
  | pair a b iha ihb => simp [encodeMixVal, iha, ihb]

theorem encodeOptMixVal_scoped (ov : Option MixVal) : Scoped 0 (encodeOptMixVal ov) := by
  cases ov <;> simp [encodeOptMixVal, encodeMixVal_scoped]

private theorem steps_trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with | refl _ => exact h2 | next s _ ih => exact .next s (ih h2)
private theorem steps_app_fn {f f' : Term} (a : Term) (h : Steps f f') : Steps (.app f a) (.app f' a) := by
  induction h with | refl _ => exact .refl _ | next s _ ih => exact .next (.application a s) ih
private theorem steps_case_scrut {s s' : Term} (arms : List (String × Term)) (h : Steps s s') : Steps (.case s arms) (.case s' arms) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.caseTarget arms st) ih
private theorem steps_get_tgt {g g' : Term} (nm : String) (h : Steps g g') : Steps (.get g nm) (.get g' nm) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.target nm st) ih
private theorem steps_ifBool_cond {c c' : Term} (t f : Term) (h : Steps c c') : Steps (.ifBool c t f) (.ifBool c' t f) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.ifCondition t f st) ih
private theorem steps_ifZero_cond {v v' : Term} (z s : Term) (h : Steps v v') : Steps (.ifZero v z s) (.ifZero v' z s) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.condition z s st) ih
private theorem steps_bin_left {op : Primitive} {l l' : Term} (r : Term) (h : Steps l l') : Steps (.binary op l r) (.binary op l' r) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.binaryLeft op r st) ih
private theorem steps_bin_right {op : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') : Steps (.binary op l r) (.binary op l r') := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.binaryRight op l hl st) ih

private theorem steps_beta_eq {body arg target res : Term}
    (heq : instantiate body arg = target) (hs : Steps target res) : Steps (.app (.lam body) arg) res := by
  rw [← heq] at hs; exact .next (.beta body arg) hs

private theorem steps_caseInject_eq {tag : String} {pay : Term} {arms : List (String × Term)}
    {arm target res : Term} (hf : arms.find? (fun f => f.1 == tag) = some (tag, arm))
    (heq : instantiate arm pay = target) (hs : Steps target res) : Steps (.case (.inject tag pay) arms) res := by
  rw [← heq] at hs; exact .next (.caseInject tag pay arms arm hf) hs

private theorem steps_succ_eq {k : Nat} {z s target res : Term}
    (heq : instantiate s (.nat k) = target) (hs : Steps target res) : Steps (.ifZero (.nat (k + 1)) z s) res := by
  rw [← heq] at hs; exact .next (.successor k z s) hs

/-- Call-by-name logical realizability relating lazy `Core4` terms to `MixVal` trees. -/
@[expose] def RealizesMixVal : Term → MixVal → Prop
  | t, .nil => ∃ p, Evaluates t (.inject "nil" p)
  | t, .num n => ∃ p, Evaluates t (.inject "num" p) ∧ Evaluates p (.nat n)
  | t, .sym s => ∃ p, Evaluates t (.inject "sym" p) ∧ Evaluates p (.nat s.toCode)
  | t, .pair a b =>
    ∃ r fa fb,
      Evaluates t (.inject "pair" r) ∧
      Evaluates r (.record [("fst", fa), ("snd", fb)]) ∧
      RealizesMixVal fa a ∧ RealizesMixVal fb b

/-- Call-by-name logical realizability for `Option MixVal`. -/
@[expose] def RealizesOptMixVal : Term → Option MixVal → Prop
  | t, none => ∃ p, Evaluates t (.inject "none" p)
  | t, some v => ∃ p, Evaluates t (.inject "some" p) ∧ RealizesMixVal p v

theorem encodeMixVal_realizes (v : MixVal) : RealizesMixVal (encodeMixVal v) v := by
  induction v with
  | nil => exact ⟨.nat 0, .refl _, .inject _ _⟩
  | num n => exact ⟨.nat n, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .natural n⟩⟩
  | sym s => exact ⟨.nat s.toCode, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .natural _⟩⟩
  | pair a b iha ihb =>
    exact ⟨_, _, _, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .record _⟩, iha, ihb⟩

private theorem realizesMixVal_of_steps {t t' : Term} {v : MixVal}
    (hs : Steps t t') (hr : RealizesMixVal t' v) : RealizesMixVal t v := by
  cases v with
  | nil => obtain ⟨p, he⟩ := hr; exact ⟨p, steps_trans hs he.1, he.2⟩
  | num n => obtain ⟨p, he, hn⟩ := hr; exact ⟨p, ⟨steps_trans hs he.1, he.2⟩, hn⟩
  | sym s => obtain ⟨p, he, hn⟩ := hr; exact ⟨p, ⟨steps_trans hs he.1, he.2⟩, hn⟩
  | pair a b =>
    obtain ⟨r, fa, fb, he, hrec, ha, hb⟩ := hr
    exact ⟨r, fa, fb, ⟨steps_trans hs he.1, he.2⟩, hrec, ha, hb⟩

private theorem realizesOptMixVal_of_steps {t t' : Term} {ov : Option MixVal}
    (hs : Steps t t') (hr : RealizesOptMixVal t' ov) : RealizesOptMixVal t ov := by
  cases ov with
  | none => obtain ⟨p, he⟩ := hr; exact ⟨p, steps_trans hs he.1, he.2⟩
  | some v => obtain ⟨p, he, hv⟩ := hr; exact ⟨p, ⟨steps_trans hs he.1, he.2⟩, hv⟩

/-- Ground `Nat` extractor projecting `some (.num n)` to `.nat n` for `Core4` machine execution. -/
def extractNumCore : Term :=
  .lam (.case (.bound 0)
    [ ("some", .case (.bound 0)
        [ ("num", .bound 0), ("nil", .nat 0), ("sym", .nat 0), ("pair", .nat 0) ])
    , ("none", .nat 0) ])

private theorem extractNumCore_scoped : Scoped 0 extractNumCore := by simp [extractNumCore]

theorem extractNumCore_evaluates {t : Term} {n : Nat}
    (hr : RealizesOptMixVal t (some (.num n))) :
    Evaluates (.app extractNumCore t) (.nat n) := by
  obtain ⟨p, hp, ⟨pn, hpn, hnat⟩⟩ := hr
  refine ⟨.next (.beta _ _) ?_, .natural n⟩
  simp only [instantiate, Term.substitute, List.map, liftSubstitution]
  refine steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute, liftSubstitution]; rfl) ?_)
  exact steps_trans (steps_case_scrut _ hpn.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) hnat.1)

private def isTrueCore : Term :=
  .lam (.case (.bound 0)
    [ ("nil", .boolean false)
    , ("num", .ifZero (.bound 0) (.boolean false) (.boolean true))
    , ("sym", .boolean true)
    , ("pair", .boolean true) ])

private theorem isTrueCore_scoped : Scoped 0 isTrueCore := by simp [isTrueCore]

private theorem isTrueCore_eval {t : Term} {v : MixVal} (hv : RealizesMixVal t v) :
    Evaluates (.app isTrueCore t) (.boolean v.isTrue) := by
  refine ⟨.next (.beta _ _) ?_, .boolean _⟩
  simp only [instantiate, Term.substitute, List.map, liftSubstitution]
  cases v with
  | nil =>
    obtain ⟨p, hp⟩ := hv
    exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.boolean false)))
  | num n =>
    obtain ⟨p, hp, hn⟩ := hv
    refine steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]; rfl) ?_)
    refine steps_trans (steps_ifZero_cond _ _ hn.1) ?_
    cases n with
    | zero => exact .next (.zero _ _) (.refl (.boolean false))
    | succ k => exact steps_succ_eq (by simp [instantiate, Term.substitute]) (.refl (.boolean true))
  | sym _ =>
    obtain ⟨p, hp, _⟩ := hv
    exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.boolean true)))
  | pair _ _ =>
    obtain ⟨r, _, _, hp, _, _, _⟩ := hv
    exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.boolean true)))

private def lowerUnaryCore : MixUnaryOp → Term
  | .fst => .lam (.case (.bound 0)
      [ ("pair", .get (.bound 0) "fst"), ("nil", encodeMixVal .nil)
      , ("num", encodeMixVal .nil), ("sym", encodeMixVal .nil) ])
  | .snd => .lam (.case (.bound 0)
      [ ("pair", .get (.bound 0) "snd"), ("nil", encodeMixVal .nil)
      , ("num", encodeMixVal .nil), ("sym", encodeMixVal .nil) ])
  | .isPair => .lam (.case (.bound 0)
      [ ("pair", encodeMixVal (.num 1)), ("nil", encodeMixVal (.num 0))
      , ("num", encodeMixVal (.num 0)), ("sym", encodeMixVal (.num 0)) ])
  | .isZero => .lam (.case (.bound 0)
      [ ("num", .ifZero (.bound 0) (encodeMixVal (.num 1)) (encodeMixVal (.num 0)))
      , ("nil", encodeMixVal (.num 0)), ("sym", encodeMixVal (.num 0)), ("pair", encodeMixVal (.num 0)) ])
  | .notB => .lam (.ifBool (.app isTrueCore (.bound 0)) (encodeMixVal (.num 0)) (encodeMixVal (.num 1)))

private theorem lowerUnaryCore_scoped (op : MixUnaryOp) : Scoped 0 (lowerUnaryCore op) := by
  cases op <;> simp [lowerUnaryCore, scoped0_any (encodeMixVal_scoped _), scoped0_any isTrueCore_scoped]

private theorem lowerUnaryCore_realizes (op : MixUnaryOp) {t : Term} {v : MixVal}
    (hv : RealizesMixVal t v) : RealizesMixVal (.app (lowerUnaryCore op) t) (evalUnary op v) := by
  have hNil := encodeMixVal_scoped .nil
  have hZ := encodeMixVal_scoped (.num 0)
  have hO := encodeMixVal_scoped (.num 1)
  cases op with
  | fst =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, List.map, scoped0_sub hNil, liftSubstitution]
    cases v with
    | pair a b =>
      obtain ⟨r, fa, fb, hp, hr, ha, _⟩ := hv
      refine realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1)
        (steps_caseInject_eq (target := .get r "fst") rfl (by simp [instantiate, Term.substitute])
          (steps_trans (steps_get_tgt "fst" hr.1) (.next (.field _ "fst" fa rfl) (.refl fa))))) ha
    | nil => obtain ⟨p, hp⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
    | num _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
    | sym _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
  | snd =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, List.map, scoped0_sub hNil, liftSubstitution]
    cases v with
    | pair a b =>
      obtain ⟨r, fa, fb, hp, hr, _, hb⟩ := hv
      refine realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1)
        (steps_caseInject_eq (target := .get r "snd") rfl (by simp [instantiate, Term.substitute])
          (steps_trans (steps_get_tgt "snd" hr.1) (.next (.field _ "snd" fb rfl) (.refl fb))))) hb
    | nil => obtain ⟨p, hp⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
    | num _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
    | sym _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hNil]) (.refl _))) (encodeMixVal_realizes .nil)
  | isPair =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, List.map, scoped0_sub hZ, scoped0_sub hO]
    cases v with
    | pair _ _ => obtain ⟨r, _, _, hp, _, _, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hO]) (.refl _))) (encodeMixVal_realizes (.num 1))
    | nil => obtain ⟨p, hp⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
    | num _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
    | sym _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
  | isZero =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, List.map, scoped0_sub hZ, scoped0_sub hO, liftSubstitution]
    cases v with
    | num n =>
      obtain ⟨p, hp, hn⟩ := hv
      refine realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1)
        (steps_caseInject_eq (target := .ifZero p (encodeMixVal (.num 1)) (encodeMixVal (.num 0))) rfl
          (by simp [instantiate, Term.substitute, scoped0_sub hZ, scoped0_sub hO])
          (steps_ifZero_cond _ _ hn.1))) ?_
      cases n with
      | zero => exact realizesMixVal_of_steps (.next (.zero _ _) (.refl _)) (encodeMixVal_realizes (.num 1))
      | succ k => exact realizesMixVal_of_steps (steps_succ_eq (target := encodeMixVal (.num 0)) (by simp [instantiate, scoped0_sub hZ]) (.refl _)) (encodeMixVal_realizes (.num 0))
    | nil => obtain ⟨p, hp⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
    | sym _ => obtain ⟨p, hp, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
    | pair _ _ => obtain ⟨r, _, _, hp, _, _, _⟩ := hv; exact realizesMixVal_of_steps (steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, scoped0_sub hZ]) (.refl _))) (encodeMixVal_realizes (.num 0))
  | notB =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub isTrueCore_scoped, scoped0_sub hZ, scoped0_sub hO]
    have hc := isTrueCore_eval hv
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hc.1) ?_
    simp only [evalUnary]
    cases v.isTrue <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 1))
    · exact realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) (encodeMixVal_realizes (.num 0))

private def tagCodeCore : Term :=
  .lam (.case (.bound 0)
    [ ("nil", .nat 0), ("num", .nat 1), ("sym", .nat 2), ("pair", .nat 3) ])

private theorem tagCodeCore_scoped : Scoped 0 tagCodeCore := by simp [tagCodeCore]

private def mixValTag : MixVal → Nat
  | .nil => 0 | .num _ => 1 | .sym _ => 2 | .pair _ _ => 3

private theorem tagCodeCore_eval {t : Term} {v : MixVal} (hv : RealizesMixVal t v) :
    Evaluates (.app tagCodeCore t) (.nat (mixValTag v)) := by
  refine ⟨.next (.beta _ _) ?_, .natural _⟩
  simp only [instantiate, Term.substitute, List.map]
  cases v with
  | nil => obtain ⟨p, hp⟩ := hv; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.nat 0)))
  | num _ => obtain ⟨p, hp, _⟩ := hv; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.nat 1)))
  | sym _ => obtain ⟨p, hp, _⟩ := hv; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.nat 2)))
  | pair _ _ => obtain ⟨r, _, _, hp, _, _, _⟩ := hv; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.nat 3)))

private def unboxNatCore : Term :=
  .lam (.case (.bound 0)
    [ ("num", .bound 0), ("sym", .bound 0), ("nil", .nat 0), ("pair", .nat 0) ])

private theorem unboxNatCore_scoped : Scoped 0 unboxNatCore := by simp [unboxNatCore]

private theorem unboxNatCore_num {t : Term} {n : Nat} (hv : RealizesMixVal t (.num n)) :
    Evaluates (.app unboxNatCore t) (.nat n) := by
  obtain ⟨p, hp, hn⟩ := hv
  refine ⟨.next (.beta _ _) ?_, .natural n⟩
  simp only [instantiate, Term.substitute, List.map, liftSubstitution]
  exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) hn.1)

private theorem unboxNatCore_sym {t : Term} {s : MixSym} (hv : RealizesMixVal t (.sym s)) :
    Evaluates (.app unboxNatCore t) (.nat s.toCode) := by
  obtain ⟨p, hp, hn⟩ := hv
  refine ⟨.next (.beta _ _) ?_, .natural s.toCode⟩
  simp only [instantiate, Term.substitute, List.map, liftSubstitution]
  exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) hn.1)

private def eqMixSpec : Term :=
  let a := Term.get (.bound 0) "a"
  let b := Term.get (.bound 0) "b"
  let self := Term.bound 2
  .lam (.lam (.lam
    (.ifBool (.binary .equal (.app tagCodeCore a) (.app tagCodeCore b))
      (.ifBool (.binary .equal (.app tagCodeCore a) (.nat 0))
        (.boolean true)
        (.ifBool (.binary .less (.app tagCodeCore a) (.nat 3))
          (.binary .equal (.app unboxNatCore a) (.app unboxNatCore b))
          (.ifBool
            (.app self (.record [("a", .app (lowerUnaryCore .fst) a), ("b", .app (lowerUnaryCore .fst) b)]))
            (.app self (.record [("a", .app (lowerUnaryCore .snd) a), ("b", .app (lowerUnaryCore .snd) b)]))
            (.boolean false))))
      (.boolean false))))

private def eqMixCore : Term := .fix eqMixSpec (.nat 0)

private theorem eqMixCore_scoped : Scoped 0 eqMixCore := by
  simp [eqMixCore, eqMixSpec, scoped0_any tagCodeCore_scoped, scoped0_any unboxNatCore_scoped,
    scoped0_any (lowerUnaryCore_scoped .fst), scoped0_any (lowerUnaryCore_scoped .snd)]

private theorem eval_bin_nat {op : Primitive} {l r : Term} {nl nr : Nat} {out : Term}
    (hl : Evaluates l (.nat nl)) (hr : Evaluates r (.nat nr))
    (hp : primitiveResult op (.nat nl) (.nat nr) = some out) (hv : Value out) :
    Evaluates (.binary op l r) out :=
  ⟨steps_trans (steps_bin_left _ hl.1) (steps_trans (steps_bin_right (.natural nl) hr.1)
    (.next (.primitive op _ _ out (.natural nl) (.natural nr) hp) (.refl _))), hv⟩

private theorem eval_ifBool_true {c : Term} (t f : Term) {out : Term}
    (hc : Evaluates c (.boolean true)) (ht : Evaluates t out) : Evaluates (.ifBool c t f) out :=
  ⟨steps_trans (steps_ifBool_cond t f hc.1) (.next (.ifTrue t f) ht.1), ht.2⟩

private theorem eval_ifBool_false {c : Term} (t f : Term) {out : Term}
    (hc : Evaluates c (.boolean false)) (hf : Evaluates f out) : Evaluates (.ifBool c t f) out :=
  ⟨steps_trans (steps_ifBool_cond t f hc.1) (.next (.ifFalse t f) hf.1), hf.2⟩

private theorem eval_ifBool_step {c : Term} (t f : Term) {out : Term} {b : Bool}
    (hc : Evaluates c (.boolean b)) (hBr : Evaluates (if b then t else f) out) :
    Evaluates (.ifBool c t f) out := by
  cases b
  · exact eval_ifBool_false t f hc hBr
  · exact eval_ifBool_true t f hc hBr

private theorem eqMixCore_unfold (p : Term) :
    Steps (.app eqMixCore p)
      (.ifBool (.binary .equal (.app tagCodeCore (.get p "a")) (.app tagCodeCore (.get p "b")))
        (.ifBool (.binary .equal (.app tagCodeCore (.get p "a")) (.nat 0))
          (.boolean true)
          (.ifBool (.binary .less (.app tagCodeCore (.get p "a")) (.nat 3))
            (.binary .equal (.app unboxNatCore (.get p "a")) (.app unboxNatCore (.get p "b")))
            (.ifBool
              (.app eqMixCore (.record [("a", .app (lowerUnaryCore .fst) (.get p "a")), ("b", .app (lowerUnaryCore .fst) (.get p "b"))]))
              (.app eqMixCore (.record [("a", .app (lowerUnaryCore .snd) (.get p "a")), ("b", .app (lowerUnaryCore .snd) (.get p "b"))]))
              (.boolean false))))
        (.boolean false)) := by
  refine steps_trans (steps_app_fn p (.next (.fix eqMixSpec (.nat 0)) (.refl _))) ?_
  change Steps (.app (.app (.app eqMixSpec eqMixCore) (.nat 0)) p) _
  dsimp only [eqMixSpec]
  refine .next (.application p (.application (.nat 0) (.beta _ _))) ?_
  simp only [instantiate, Term.substitute, liftSubstitution, List.map,
    scoped0_ren eqMixCore_scoped, scoped0_sub eqMixCore_scoped,
    scoped0_ren tagCodeCore_scoped, scoped0_sub tagCodeCore_scoped,
    scoped0_ren unboxNatCore_scoped, scoped0_sub unboxNatCore_scoped,
    scoped0_ren (lowerUnaryCore_scoped .fst), scoped0_sub (lowerUnaryCore_scoped .fst),
    scoped0_ren (lowerUnaryCore_scoped .snd), scoped0_sub (lowerUnaryCore_scoped .snd)]
  refine .next (.application p (.beta _ _)) ?_
  simp only [instantiate, Term.substitute, liftSubstitution, List.map,
    scoped0_ren eqMixCore_scoped, scoped0_sub eqMixCore_scoped,
    scoped0_ren tagCodeCore_scoped, scoped0_sub tagCodeCore_scoped,
    scoped0_ren unboxNatCore_scoped, scoped0_sub unboxNatCore_scoped,
    scoped0_ren (lowerUnaryCore_scoped .fst), scoped0_sub (lowerUnaryCore_scoped .fst),
    scoped0_ren (lowerUnaryCore_scoped .snd), scoped0_sub (lowerUnaryCore_scoped .snd)]
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, List.map,
    scoped0_sub eqMixCore_scoped, scoped0_sub tagCodeCore_scoped, scoped0_sub unboxNatCore_scoped,
    scoped0_sub (lowerUnaryCore_scoped .fst), scoped0_sub (lowerUnaryCore_scoped .snd)]
  exact .refl _

private theorem eqMixCore_eval {va vb : MixVal} :
    ∀ {ta tb : Term}, RealizesMixVal ta va → RealizesMixVal tb vb →
      Evaluates (.app eqMixCore (.record [("a", ta), ("b", tb)])) (.boolean (va == vb)) := by
  induction va generalizing vb with
  | nil =>
    intro ta tb ha hb
    let p := Term.record [("a", ta), ("b", tb)]
    have hpA : Steps (.get p "a") ta := .next (.field _ "a" ta rfl) (.refl _)
    have hpB : Steps (.get p "b") tb := .next (.field _ "b" tb rfl) (.refl _)
    have hTagA := tagCodeCore_eval (realizesMixVal_of_steps hpA ha)
    have hTagB := tagCodeCore_eval (realizesMixVal_of_steps hpB hb)
    have hEqTag := eval_bin_nat (op := .equal) hTagA hTagB rfl (.boolean _)
    cases vb with
    | nil =>
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean true⟩
      exact (eval_ifBool_true _ _ hEqTag
        (eval_ifBool_true _ _ (eval_bin_nat (op := .equal) hTagA ⟨.refl _, .natural 0⟩ rfl (.boolean true)) ⟨.refl _, .boolean true⟩)).1
    | num _ | sym _ | pair _ _ =>
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean false⟩
      exact (eval_ifBool_false _ _ hEqTag ⟨.refl _, .boolean false⟩).1
  | num na =>
    intro ta tb ha hb
    let p := Term.record [("a", ta), ("b", tb)]
    have hpA : Steps (.get p "a") ta := .next (.field _ "a" ta rfl) (.refl _)
    have hpB : Steps (.get p "b") tb := .next (.field _ "b" tb rfl) (.refl _)
    have hTagA := tagCodeCore_eval (realizesMixVal_of_steps hpA ha)
    have hTagB := tagCodeCore_eval (realizesMixVal_of_steps hpB hb)
    have hEqTag := eval_bin_nat (op := .equal) hTagA hTagB rfl (.boolean _)
    cases vb with
    | num nb =>
      have hCmp := eval_bin_nat (op := .equal) (unboxNatCore_num (realizesMixVal_of_steps hpA ha))
        (unboxNatCore_num (realizesMixVal_of_steps hpB hb)) rfl (.boolean (na == nb))
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean _⟩
      exact (eval_ifBool_true _ _ hEqTag
        (eval_ifBool_false _ _ (eval_bin_nat (op := .equal) hTagA ⟨.refl _, .natural 0⟩ rfl (.boolean false))
          (eval_ifBool_true _ _ (eval_bin_nat (op := .less) hTagA ⟨.refl _, .natural 3⟩ rfl (.boolean true)) hCmp))).1
    | nil | sym _ | pair _ _ =>
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean false⟩
      exact (eval_ifBool_false _ _ hEqTag ⟨.refl _, .boolean false⟩).1
  | sym sa =>
    intro ta tb ha hb
    let p := Term.record [("a", ta), ("b", tb)]
    have hpA : Steps (.get p "a") ta := .next (.field _ "a" ta rfl) (.refl _)
    have hpB : Steps (.get p "b") tb := .next (.field _ "b" tb rfl) (.refl _)
    have hTagA := tagCodeCore_eval (realizesMixVal_of_steps hpA ha)
    have hTagB := tagCodeCore_eval (realizesMixVal_of_steps hpB hb)
    have hEqTag := eval_bin_nat (op := .equal) hTagA hTagB rfl (.boolean _)
    cases vb with
    | sym sb =>
      have hCmp := eval_bin_nat (op := .equal) (unboxNatCore_sym (realizesMixVal_of_steps hpA ha))
        (unboxNatCore_sym (realizesMixVal_of_steps hpB hb)) rfl (.boolean (sa.toCode == sb.toCode))
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean _⟩
      exact (eval_ifBool_true _ _ hEqTag
        (eval_ifBool_false _ _ (eval_bin_nat (op := .equal) hTagA ⟨.refl _, .natural 0⟩ rfl (.boolean false))
          (eval_ifBool_true _ _ (eval_bin_nat (op := .less) hTagA ⟨.refl _, .natural 3⟩ rfl (.boolean true)) hCmp))).1
    | nil | num _ | pair _ _ =>
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean false⟩
      exact (eval_ifBool_false _ _ hEqTag ⟨.refl _, .boolean false⟩).1
  | pair a1 a2 iha1 iha2 =>
    intro ta tb ha hb
    let p := Term.record [("a", ta), ("b", tb)]
    have hpA : Steps (.get p "a") ta := .next (.field _ "a" ta rfl) (.refl _)
    have hpB : Steps (.get p "b") tb := .next (.field _ "b" tb rfl) (.refl _)
    have hTagA := tagCodeCore_eval (realizesMixVal_of_steps hpA ha)
    have hTagB := tagCodeCore_eval (realizesMixVal_of_steps hpB hb)
    have hEqTag := eval_bin_nat (op := .equal) hTagA hTagB rfl (.boolean _)
    cases vb with
    | pair b1 b2 =>
      have hFst := iha1 (lowerUnaryCore_realizes .fst (realizesMixVal_of_steps hpA ha))
        (lowerUnaryCore_realizes .fst (realizesMixVal_of_steps hpB hb))
      have hPairBr : Evaluates
          (if (a1 == b1) then
            .app eqMixCore (.record [("a", .app (lowerUnaryCore .snd) (.get p "a")),
              ("b", .app (lowerUnaryCore .snd) (.get p "b"))])
           else .boolean false)
          (.boolean ((a1 == b1) && (a2 == b2))) := by
        cases (a1 == b1) <;> simp only [Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true]
        · exact ⟨.refl _, .boolean false⟩
        · exact iha2 (lowerUnaryCore_realizes .snd (realizesMixVal_of_steps hpA ha))
            (lowerUnaryCore_realizes .snd (realizesMixVal_of_steps hpB hb))
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean _⟩
      exact (eval_ifBool_true _ _ hEqTag
        (eval_ifBool_false _ _ (eval_bin_nat (op := .equal) hTagA ⟨.refl _, .natural 0⟩ rfl (.boolean false))
          (eval_ifBool_false _ _ (eval_bin_nat (op := .less) hTagA ⟨.refl _, .natural 3⟩ rfl (.boolean false))
            (eval_ifBool_step _ _ hFst hPairBr)))).1
    | nil | num _ | sym _ =>
      refine ⟨steps_trans (eqMixCore_unfold p) ?_, .boolean false⟩
      exact (eval_ifBool_false _ _ hEqTag ⟨.refl _, .boolean false⟩).1

private def lowerBinCore (op : MixBinOp) : Term :=
  let a := Term.get (.bound 0) "a"
  let b := Term.get (.bound 0) "b"
  let bothNum := Term.binary .conjunction
    (.binary .equal (.app tagCodeCore a) (.nat 1))
    (.binary .equal (.app tagCodeCore b) (.nat 1))
  match op with
  | .cons => .lam (.inject "pair" (.record [("fst", a), ("snd", b)]))
  | .eq => .lam (.ifBool (.app eqMixCore (.bound 0)) (encodeMixVal (.num 1)) (encodeMixVal (.num 0)))
  | .add => .lam (.ifBool bothNum (.inject "num" (.binary .add (.app unboxNatCore a) (.app unboxNatCore b))) (encodeMixVal (.num 0)))
  | .sub => .lam (.ifBool bothNum (.inject "num" (.binary .subtract (.app unboxNatCore a) (.app unboxNatCore b))) (encodeMixVal (.num 0)))
  | .mul => .lam (.ifBool bothNum (.inject "num" (.binary .multiply (.app unboxNatCore a) (.app unboxNatCore b))) (encodeMixVal (.num 0)))
  | .lt => .lam (.ifBool bothNum
      (.ifBool (.binary .less (.app unboxNatCore a) (.app unboxNatCore b)) (encodeMixVal (.num 1)) (encodeMixVal (.num 0)))
      (encodeMixVal (.num 0)))

private theorem lowerBinCore_scoped (op : MixBinOp) : Scoped 0 (lowerBinCore op) := by
  cases op <;> simp [lowerBinCore, scoped0_any tagCodeCore_scoped, scoped0_any unboxNatCore_scoped,
    scoped0_any eqMixCore_scoped, scoped0_any (encodeMixVal_scoped _)]

private theorem lowerBinCore_realizes (op : MixBinOp) {ta tb : Term} {va vb : MixVal}
    (ha : RealizesMixVal ta va) (hb : RealizesMixVal tb vb) :
    RealizesMixVal (.app (lowerBinCore op) (.record [("a", ta), ("b", tb)])) (evalBin op va vb) := by
  let p := Term.record [("a", ta), ("b", tb)]
  have hpA : Steps (.get p "a") ta := .next (.field _ "a" ta rfl) (.refl _)
  have hpB : Steps (.get p "b") tb := .next (.field _ "b" tb rfl) (.refl _)
  have hZ := encodeMixVal_scoped (.num 0)
  have hO := encodeMixVal_scoped (.num 1)
  have hBothEval : Evaluates
      (.binary .conjunction
        (.binary .equal (.app tagCodeCore (.get p "a")) (.nat 1))
        (.binary .equal (.app tagCodeCore (.get p "b")) (.nat 1)))
      (.boolean ((mixValTag va == 1) && (mixValTag vb == 1))) := by
    have e1 := eval_bin_nat (op := .equal) (tagCodeCore_eval (realizesMixVal_of_steps hpA ha)) ⟨.refl _, .natural 1⟩ rfl (.boolean _)
    have e2 := eval_bin_nat (op := .equal) (tagCodeCore_eval (realizesMixVal_of_steps hpB hb)) ⟨.refl _, .natural 1⟩ rfl (.boolean _)
    exact ⟨steps_trans (steps_bin_left _ e1.1) (steps_trans (steps_bin_right (.boolean _) e2.1)
      (.next (.primitive .conjunction _ _ _ (.boolean _) (.boolean _) rfl) (.refl _))), .boolean _⟩
  cases op with
  | cons =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, List.map]
    exact ⟨_, _, _, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .record _⟩,
      realizesMixVal_of_steps hpA ha, realizesMixVal_of_steps hpB hb⟩
  | eq =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub eqMixCore_scoped, scoped0_sub hO, scoped0_sub hZ]
    have hEq := eqMixCore_eval ha hb
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hEq.1) ?_
    simp only [evalBin]
    cases (va == vb) <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
    · exact realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) (encodeMixVal_realizes (.num 1))
  | add =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub tagCodeCore_scoped, scoped0_sub unboxNatCore_scoped, scoped0_sub hZ]
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hBothEval.1) ?_
    cases va with
    | num na =>
      cases vb with
      | num nb =>
        refine realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) ⟨_, ⟨.refl _, .inject _ _⟩, ?_⟩
        exact eval_bin_nat (op := .add) (unboxNatCore_num (realizesMixVal_of_steps hpA ha))
          (unboxNatCore_num (realizesMixVal_of_steps hpB hb)) rfl (.natural (na + nb))
      | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
    | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
  | sub =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub tagCodeCore_scoped, scoped0_sub unboxNatCore_scoped, scoped0_sub hZ]
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hBothEval.1) ?_
    cases va with
    | num na =>
      cases vb with
      | num nb =>
        refine realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) ⟨_, ⟨.refl _, .inject _ _⟩, ?_⟩
        exact eval_bin_nat (op := .subtract) (unboxNatCore_num (realizesMixVal_of_steps hpA ha))
          (unboxNatCore_num (realizesMixVal_of_steps hpB hb)) rfl (.natural (na - nb))
      | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
    | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
  | mul =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub tagCodeCore_scoped, scoped0_sub unboxNatCore_scoped, scoped0_sub hZ]
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hBothEval.1) ?_
    cases va with
    | num na =>
      cases vb with
      | num nb =>
        refine realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) ⟨_, ⟨.refl _, .inject _ _⟩, ?_⟩
        exact eval_bin_nat (op := .multiply) (unboxNatCore_num (realizesMixVal_of_steps hpA ha))
          (unboxNatCore_num (realizesMixVal_of_steps hpB hb)) rfl (.natural (na * nb))
      | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
    | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
  | lt =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub tagCodeCore_scoped, scoped0_sub unboxNatCore_scoped, scoped0_sub hZ, scoped0_sub hO]
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hBothEval.1) ?_
    cases va with
    | num na =>
      cases vb with
      | num nb =>
        refine realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) ?_
        have hLt := eval_bin_nat (op := .less) (unboxNatCore_num (realizesMixVal_of_steps hpA ha))
          (unboxNatCore_num (realizesMixVal_of_steps hpB hb)) rfl (.boolean (decide (na < nb)))
        refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hLt.1) ?_
        simp only [evalBin]
        by_cases h : na < nb <;> simp only [h, decide_true, decide_false, ↓reduceIte]
        · exact realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) (encodeMixVal_realizes (.num 1))
        · exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
      | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))
    | nil | sym _ | pair _ _ => exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (encodeMixVal_realizes (.num 0))

private def lowerSExprCore : SExpr → Term
  | .var => .lam (.bound 0)
  | .lit v => .lam (encodeMixVal v)
  | .unary op e => .lam (.app (lowerUnaryCore op) (.app (lowerSExprCore e) (.bound 0)))
  | .bin op e1 e2 =>
    .lam (.app (lowerBinCore op)
      (.record [("a", .app (lowerSExprCore e1) (.bound 0)), ("b", .app (lowerSExprCore e2) (.bound 0))]))
  | .ifS c t f =>
    .lam (.ifBool (.app isTrueCore (.app (lowerSExprCore c) (.bound 0)))
      (.app (lowerSExprCore t) (.bound 0)) (.app (lowerSExprCore f) (.bound 0)))
  | .letS b body =>
    .lam (.app (lowerSExprCore body)
      (.inject "pair" (.record [("fst", .app (lowerSExprCore b) (.bound 0)), ("snd", .bound 0)])))

private theorem lowerSExprCore_scoped (se : SExpr) : Scoped 0 (lowerSExprCore se) := by
  induction se with
  | var => simp [lowerSExprCore]
  | lit v => simp [lowerSExprCore, scoped0_any (encodeMixVal_scoped v)]
  | unary op e ih => simp [lowerSExprCore, scoped0_any (lowerUnaryCore_scoped op), scoped0_any ih]
  | bin op e1 e2 ih1 ih2 =>
    simp [lowerSExprCore, scoped0_any (lowerBinCore_scoped op), scoped0_any ih1, scoped0_any ih2]
  | ifS c t f ihc iht ihf =>
    simp [lowerSExprCore, scoped0_any isTrueCore_scoped, scoped0_any ihc, scoped0_any iht, scoped0_any ihf]
  | letS b body ihb ihbody =>
    simp [lowerSExprCore, scoped0_any ihb, scoped0_any ihbody]

private theorem lowerSExprCore_realizes (se : SExpr) {ts : Term} {s : MixVal}
    (hs : RealizesMixVal ts s) : RealizesMixVal (.app (lowerSExprCore se) ts) (evalSExpr se s) := by
  induction se generalizing ts s with
  | var => exact realizesMixVal_of_steps (steps_beta_eq (by simp [instantiate, Term.substitute]) (.refl ts)) hs
  | lit v =>
    refine realizesMixVal_of_steps (.next (.beta _ _) ?_) (encodeMixVal_realizes v)
    simp only [instantiate, scoped0_sub (encodeMixVal_scoped v)]; exact .refl _
  | unary op e ih =>
    refine realizesMixVal_of_steps (.next (.beta _ _) ?_) (lowerUnaryCore_realizes op (ih hs))
    simp only [instantiate, Term.substitute, scoped0_sub (lowerUnaryCore_scoped op), scoped0_sub (lowerSExprCore_scoped e)]
    exact .refl _
  | bin op e1 e2 ih1 ih2 =>
    refine realizesMixVal_of_steps (.next (.beta _ _) ?_) (lowerBinCore_realizes op (ih1 hs) (ih2 hs))
    simp only [instantiate, Term.substitute, List.map, scoped0_sub (lowerBinCore_scoped op),
      scoped0_sub (lowerSExprCore_scoped e1), scoped0_sub (lowerSExprCore_scoped e2)]
    exact .refl _
  | ifS c t f ihc iht ihf =>
    refine realizesMixVal_of_steps (.next (.beta _ _) (.refl _)) ?_
    simp only [instantiate, Term.substitute, scoped0_sub isTrueCore_scoped,
      scoped0_sub (lowerSExprCore_scoped c), scoped0_sub (lowerSExprCore_scoped t), scoped0_sub (lowerSExprCore_scoped f)]
    have hc := isTrueCore_eval (ihc hs)
    refine realizesMixVal_of_steps (steps_ifBool_cond _ _ hc.1) ?_
    simp only [evalSExpr]
    cases (evalSExpr c s).isTrue <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact realizesMixVal_of_steps (.next (.ifFalse _ _) (.refl _)) (ihf hs)
    · exact realizesMixVal_of_steps (.next (.ifTrue _ _) (.refl _)) (iht hs)
  | letS b body ihb ihbody =>
    refine realizesMixVal_of_steps (.next (.beta _ _) ?_)
      (ihbody ⟨_, _, _, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .record _⟩, ihb hs, hs⟩)
    simp only [instantiate, Term.substitute, List.map, scoped0_sub (lowerSExprCore_scoped body),
      scoped0_sub (lowerSExprCore_scoped b)]
    exact .refl _

private def isSomeCore : Term :=
  .lam (.case (.bound 0) [ ("none", .boolean false), ("some", .boolean true) ])

private theorem isSomeCore_scoped : Scoped 0 isSomeCore := by simp [isSomeCore]

private theorem isSomeCore_eval {t : Term} {ov : Option MixVal} (ho : RealizesOptMixVal t ov) :
    Evaluates (.app isSomeCore t) (.boolean ov.isSome) := by
  refine ⟨.next (.beta _ _) ?_, .boolean _⟩
  simp only [instantiate, Term.substitute, List.map]
  cases ov with
  | none => obtain ⟨p, hp⟩ := ho; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.boolean false)))
  | some _ => obtain ⟨p, hp, _⟩ := ho; exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl (.boolean true)))

private def unboxSomeCore : Term :=
  .lam (.case (.bound 0) [ ("some", .bound 0), ("none", encodeMixVal .nil) ])

private theorem unboxSomeCore_scoped : Scoped 0 unboxSomeCore := by
  simp [unboxSomeCore, scoped0_any (encodeMixVal_scoped .nil)]

private theorem unboxSomeCore_realizes {t : Term} {v : MixVal} (ho : RealizesOptMixVal t (some v)) :
    RealizesMixVal (.app unboxSomeCore t) v := by
  obtain ⟨p, hp, hv⟩ := ho
  refine realizesMixVal_of_steps (.next (.beta _ _) ?_) hv
  simp only [instantiate, Term.substitute, List.map, liftSubstitution, scoped0_sub (encodeMixVal_scoped .nil)]
  exact steps_trans (steps_case_scrut _ hp.1) (steps_caseInject_eq rfl (by simp [instantiate, Term.substitute]) (.refl p))

private def exprSubtrees : MixExpr → List MixExpr
  | .dVar => [.dVar] | .dLit v => [.dLit v] | .dLift se => [.dLift se]
  | .dUnary op e1 => .dUnary op e1 :: exprSubtrees e1
  | .dCall c e1 => .dCall c e1 :: exprSubtrees e1
  | .sLet b e1 => .sLet b e1 :: exprSubtrees e1
  | .sCall c s e1 => .sCall c s e1 :: exprSubtrees e1
  | .spCall c s e1 => .spCall c s e1 :: exprSubtrees e1
  | .dBin op e1 e2 => .dBin op e1 e2 :: (exprSubtrees e1 ++ exprSubtrees e2)
  | .dWhile e1 e2 => .dWhile e1 e2 :: (exprSubtrees e1 ++ exprSubtrees e2)
  | .dWithEnv e1 e2 => .dWithEnv e1 e2 :: (exprSubtrees e1 ++ exprSubtrees e2)
  | .sIf c e1 e2 => .sIf c e1 e2 :: (exprSubtrees e1 ++ exprSubtrees e2)
  | .dIf c t f => .dIf c t f :: (exprSubtrees c ++ exprSubtrees t ++ exprSubtrees f)

private theorem mem_exprSubtrees_self (e : MixExpr) : e ∈ exprSubtrees e := by
  cases e <;> simp [exprSubtrees]

private def exprChildren : MixExpr → List MixExpr
  | .dVar | .dLit _ | .dLift _ => []
  | .dUnary _ e1 | .dCall _ e1 | .sLet _ e1 | .sCall _ _ e1 | .spCall _ _ e1 => [e1]
  | .dBin _ e1 e2 | .dWhile e1 e2 | .dWithEnv e1 e2 | .sIf _ e1 e2 => [e1, e2]
  | .dIf c t f => [c, t, f]

private theorem child_mem_exprSubtrees (root : MixExpr) :
    ∀ {e sub : MixExpr}, e ∈ exprSubtrees root → sub ∈ exprChildren e → sub ∈ exprSubtrees root := by
  induction root with
  | dVar | dLit _ | dLift _ =>
    intro e sub he hsub; simp [exprSubtrees] at he; subst he; simp [exprChildren] at hsub
  | dUnary _ e1 ih | dCall _ e1 ih | sLet _ e1 ih | sCall _ _ e1 ih | spCall _ _ e1 ih =>
    intro e sub he hsub; simp only [exprSubtrees, List.mem_cons] at he
    rcases he with rfl | he1
    · simp only [exprChildren, List.mem_singleton] at hsub; subst hsub
      exact List.Mem.tail _ (mem_exprSubtrees_self _)
    · exact List.Mem.tail _ (ih he1 hsub)
  | dBin _ e1 e2 ih1 ih2 | dWhile e1 e2 ih1 ih2 | dWithEnv e1 e2 ih1 ih2 | sIf _ e1 e2 ih1 ih2 =>
    intro e sub he hsub; simp only [exprSubtrees, List.mem_cons, List.mem_append] at he ⊢
    rcases he with rfl | he1 | he2
    · simp only [exprChildren, List.mem_cons, List.not_mem_nil, or_false] at hsub
      rcases hsub with rfl | rfl
      · exact Or.inr (Or.inl (mem_exprSubtrees_self _))
      · exact Or.inr (Or.inr (mem_exprSubtrees_self _))
    · exact Or.inr (Or.inl (ih1 he1 hsub))
    · exact Or.inr (Or.inr (ih2 he2 hsub))
  | dIf c t f ihc iht ihf =>
    intro e sub he hsub; simp only [exprSubtrees, List.mem_cons, List.mem_append] at he ⊢
    rcases he with rfl | (hc | ht) | hf
    · simp only [exprChildren, List.mem_cons, List.not_mem_nil, or_false] at hsub
      rcases hsub with rfl | rfl | rfl
      · exact Or.inr (Or.inl (Or.inl (mem_exprSubtrees_self _)))
      · exact Or.inr (Or.inl (Or.inr (mem_exprSubtrees_self _)))
      · exact Or.inr (Or.inr (mem_exprSubtrees_self _))
    · exact Or.inr (Or.inl (Or.inl (ihc hc hsub)))
    · exact Or.inr (Or.inl (Or.inr (iht ht hsub)))
    · exact Or.inr (Or.inr (ihf hf hsub))

private def progSubtrees : List MixProc → List MixExpr
  | [] => []
  | pr :: rest => exprSubtrees pr.body ++ progSubtrees rest

private theorem lookup_mem_progSubtrees {procs : List MixProc} {c : MixVal} {body : MixExpr}
    (h : lookupProc procs c = some body) : body ∈ progSubtrees procs := by
  induction procs with
  | nil => simp [lookupProc] at h
  | cons pr rest ih =>
    simp only [lookupProc] at h; simp only [progSubtrees, List.mem_append]
    by_cases hEq : pr.name == c
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at h; subst h; exact Or.inl (mem_exprSubtrees_self _)
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inr (ih h)

private theorem child_mem_progSubtrees {procs : List MixProc} {e sub : MixExpr}
    (he : e ∈ progSubtrees procs) (hsub : sub ∈ exprChildren e) : sub ∈ progSubtrees procs := by
  induction procs with
  | nil => simp [progSubtrees] at he
  | cons pr rest ih =>
    simp only [progSubtrees, List.mem_append] at he ⊢
    rcases he with h1 | h2
    · exact Or.inl (child_mem_exprSubtrees pr.body h1 hsub)
    · exact Or.inr (ih h2)

private def findExprIdx : List MixExpr → MixExpr → Nat
  | [], _ => 0
  | x :: xs, e => if x == e then 0 else findExprIdx xs e + 1

private def buildDispatch : List Term → Term
  | [] => .lam (encodeOptMixVal none)
  | arm :: rest => .lam (.ifZero (.bound 0) arm (.app (buildDispatch rest) (.bound 0)))

private theorem buildDispatch_scoped {arms : List Term} (h : ∀ a ∈ arms, Scoped 0 a) :
    Scoped 0 (buildDispatch arms) := by
  induction arms with
  | nil => simp [buildDispatch, scoped0_any (encodeOptMixVal_scoped none)]
  | cons arm rest ih =>
    have ha := h arm (List.Mem.head _)
    have hr := ih (fun a hm => h a (List.Mem.tail _ hm))
    simp [buildDispatch, scoped0_any ha, scoped0_any hr]

private theorem buildDispatch_steps {cs : List MixExpr} (f : MixExpr → Term)
    (hf : ∀ x ∈ cs, Scoped 0 (f x)) {e : MixExpr} (he : e ∈ cs) :
    Steps (.app (buildDispatch (cs.map f)) (.nat (findExprIdx cs e))) (f e) := by
  induction cs with
  | nil => cases he
  | cons x xs ih =>
    have hx := hf x (List.Mem.head _)
    have hRest := buildDispatch_scoped (arms := xs.map f) (by
      intro a ha; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha; exact hf y (List.Mem.tail _ hy))
    simp only [List.map, buildDispatch, findExprIdx]
    by_cases hEq : x == e
    · have hxe : x = e := eq_of_beq hEq; subst hxe
      simp only [beq_self_eq_true, ↓reduceIte]
      refine .next (.beta _ _) ?_
      simp only [instantiate, Term.substitute, liftSubstitution, scoped0_sub hx, scoped0_sub hRest]
      exact .next (.zero _ _) (.refl _)
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
      have heXs : e ∈ xs := by
        cases List.mem_cons.mp he with
        | inl h => exact absurd (h ▸ beq_self_eq_true x) hEq
        | inr h => exact h
      refine .next (.beta _ _) ?_
      simp only [instantiate, Term.substitute, liftSubstitution, scoped0_sub hx, scoped0_sub hRest]
      refine .next (.successor (findExprIdx xs e) _ _) ?_
      simp only [instantiate, Term.substitute, scoped0_sub hRest]
      exact ih (fun y hy => hf y (List.Mem.tail _ hy)) heXs

private def mkSubCall (r : Term) (cs : List MixExpr) (sub : MixExpr) (ts td : Term) : Term :=
  .app (.app r (.nat (findExprIdx cs sub))) (.record [("s", ts), ("d", td)])

private def lowerExprArm (procs : List MixProc) (cs : List MixExpr) (e : MixExpr) : Term :=
  let r := Term.get (.bound 0) "r"
  let ts := Term.get (.bound 0) "s"
  let td := Term.get (.bound 0) "d"
  let call (sub : MixExpr) (sArg dArg : Term) : Term := mkSubCall r cs sub sArg dArg
  let noneT := encodeOptMixVal none
  .lam <| match e with
  | .dVar => .inject "some" td
  | .dLit v => .inject "some" (encodeMixVal v)
  | .dLift se => .inject "some" (.app (lowerSExprCore se) ts)
  | .dUnary op e1 =>
    let r1 := call e1 ts td
    .ifBool (.app isSomeCore r1) (.inject "some" (.app (lowerUnaryCore op) (.app unboxSomeCore r1))) noneT
  | .dBin op e1 e2 =>
    let r1 := call e1 ts td; let r2 := call e2 ts td
    .ifBool (.app isSomeCore r1)
      (.ifBool (.app isSomeCore r2)
        (.inject "some" (.app (lowerBinCore op) (.record [("a", .app unboxSomeCore r1), ("b", .app unboxSomeCore r2)])))
        noneT) noneT
  | .dIf c t f =>
    let rc := call c ts td
    .ifBool (.app isSomeCore rc)
      (.ifBool (.app isTrueCore (.app unboxSomeCore rc)) (call t ts td) (call f ts td)) noneT
  | .dWhile c body =>
    let rc := call c ts td
    let rb := call body ts td
    .ifBool (.app isSomeCore rc)
      (.ifBool (.app isTrueCore (.app unboxSomeCore rc))
        (.ifBool (.app isSomeCore rb) (call (.dWhile c body) ts (.app unboxSomeCore rb)) noneT)
        (.inject "some" td)) noneT
  | .dWithEnv e1 e2 =>
    let r1 := call e1 ts td
    .ifBool (.app isSomeCore r1) (call e2 ts (.app unboxSomeCore r1)) noneT
  | .dCall callee dArg =>
    match lookupProc procs callee with
    | none => noneT
    | some pBody =>
      let rd := call dArg ts td
      .ifBool (.app isSomeCore rd) (call pBody (encodeMixVal .nil) (.app unboxSomeCore rd)) noneT
  | .sIf c t f =>
    .ifBool (.app isTrueCore (.app (lowerSExprCore c) ts)) (call t ts td) (call f ts td)
  | .sLet b body =>
    call body (.inject "pair" (.record [("fst", .app (lowerSExprCore b) ts), ("snd", ts)])) td
  | .sCall callee sArg dArg =>
    match lookupProc procs callee with
    | none => noneT
    | some pBody =>
      let rd := call dArg ts td
      .ifBool (.app isSomeCore rd) (call pBody (.app (lowerSExprCore sArg) ts) (.app unboxSomeCore rd)) noneT
  | .spCall callee sKey dArg =>
    match lookupProc procs callee with
    | none => noneT
    | some pBody =>
      let rd := call dArg ts td
      .ifBool (.app isSomeCore rd) (call pBody (.app (lowerSExprCore sKey) ts) (.app unboxSomeCore rd)) noneT

private theorem lowerExprArm_scoped (procs : List MixProc) (cs : List MixExpr) (e : MixExpr) :
    Scoped 0 (lowerExprArm procs cs e) := by
  cases e with
  | dCall callee dArg | sCall callee _ dArg | spCall callee _ dArg =>
    dsimp only [lowerExprArm]; cases lookupProc procs callee <;>
      simp [mkSubCall, scoped0_any isSomeCore_scoped, scoped0_any unboxSomeCore_scoped,
        scoped0_any (encodeMixVal_scoped _), scoped0_any (encodeOptMixVal_scoped none),
        scoped0_any (lowerSExprCore_scoped _)]
  | _ =>
    dsimp only [lowerExprArm]
    simp [mkSubCall, scoped0_any isSomeCore_scoped, scoped0_any unboxSomeCore_scoped,
      scoped0_any isTrueCore_scoped, scoped0_any (encodeMixVal_scoped _),
      scoped0_any (encodeOptMixVal_scoped none), scoped0_any (lowerUnaryCore_scoped _),
      scoped0_any (lowerBinCore_scoped _), scoped0_any (lowerSExprCore_scoped _)]

private def lowerProgRunnerSpec (p : MixProg) : Term :=
  let cs := progSubtrees p.procs
  let disp := buildDispatch (cs.map (lowerExprArm p.procs cs))
  let stepAdapter : Term :=
    .lam (.lam (.lam
      (.app (.app disp (.bound 1))
        (.record [("r", .bound 2), ("s", .get (.bound 0) "s"), ("d", .get (.bound 0) "d")]))))
  let noneRunner : Term := .lam (.lam (encodeOptMixVal none))
  .lam (.lam (.lam (.ifZero (.bound 0) noneRunner (.app stepAdapter (.app (.bound 3) (.bound 0))))))

private def lowerProgRunner (p : MixProg) : Term := .fix (lowerProgRunnerSpec p) (.nat 0)

private theorem lowerProgRunner_scoped (p : MixProg) : Scoped 0 (lowerProgRunner p) := by
  have hDisp : Scoped 0 (buildDispatch ((progSubtrees p.procs).map (lowerExprArm p.procs (progSubtrees p.procs)))) :=
    buildDispatch_scoped fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact lowerExprArm_scoped _ _ x
  simp [lowerProgRunner, lowerProgRunnerSpec, scoped0_any hDisp, scoped0_any (encodeOptMixVal_scoped none)]

/-- **Verified `MixProg` → `Core4` Compiler (`lowerMixToCore4`)**:
    Compiles any `MixProg` into a closed `Core4` combinator (`Scoped 0`). -/
def lowerMixToCore4 (p : MixProg) : Term :=
  match lookupProc p.procs p.entry with
  | none => .lam (encodeOptMixVal none)
  | some entryBody =>
    let cs := progSubtrees p.procs
    let runner := lowerProgRunner p
    let entryIdx := findExprIdx cs entryBody
    .lam (.app (.app (.app runner (.get (.bound 0) "fuel")) (.nat entryIdx))
      (.record [("s", .get (.bound 0) "s"), ("d", .get (.bound 0) "d")]))

/-- Apply a lowered `MixProg` term to `(fuel, staticIn, dynamicIn)` as a closed `Core4` expression. -/
def applyLoweredMix (compiled : Term) (fuel : Nat) (s d : MixVal) : Term :=
  .app compiled (.record [("fuel", .nat fuel), ("s", encodeMixVal s), ("d", encodeMixVal d)])

theorem lowerMixToCore4_scoped (p : MixProg) : Scoped 0 (lowerMixToCore4 p) := by
  unfold lowerMixToCore4
  cases lookupProc p.procs p.entry <;>
    simp [scoped0_any (encodeOptMixVal_scoped none), scoped0_any (lowerProgRunner_scoped p)]

theorem applyLoweredMix_scoped (p : MixProg) (fuel : Nat) (s d : MixVal) :
    Scoped 0 (applyLoweredMix (lowerMixToCore4 p) fuel s d) := by
  simp [applyLoweredMix, lowerMixToCore4_scoped p, encodeMixVal_scoped]

private theorem realizesOpt_ifBool {c t f : Term} {b : Bool} {ov : Option MixVal}
    (hc : Evaluates c (.boolean b)) (hBr : RealizesOptMixVal (if b then t else f) ov) :
    RealizesOptMixVal (.ifBool c t f) ov := by
  refine realizesOptMixVal_of_steps (steps_ifBool_cond t f hc.1) ?_
  cases b
  · exact realizesOptMixVal_of_steps (.next (.ifFalse t f) (.refl _)) hBr
  · exact realizesOptMixVal_of_steps (.next (.ifTrue t f) (.refl _)) hBr

private theorem lowerProgRunner_unfold (p : MixProg) (tf idx sd : Term) :
    let cs := progSubtrees p.procs
    let disp := buildDispatch (cs.map (lowerExprArm p.procs cs))
    let stepAdapter := Term.lam (.lam (.lam
      (.app (.app disp (.bound 1))
        (.record [("r", .bound 2), ("s", .get (.bound 0) "s"), ("d", .get (.bound 0) "d")]))))
    Steps (.app (.app (.app (lowerProgRunner p) tf) idx) sd)
      (.app (.app (.ifZero tf (.lam (.lam (encodeOptMixVal none)))
        (.app stepAdapter (.app (lowerProgRunner p) (.bound 0)))) idx) sd) := by
  intro cs disp stepAdapter
  have hRunSc := lowerProgRunner_scoped p
  have hDispSc : Scoped 0 disp := buildDispatch_scoped fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact lowerExprArm_scoped _ _ x
  have hStepSc : Scoped 0 stepAdapter := by simp [stepAdapter, scoped0_any hDispSc]
  have hNoneR : Scoped 0 (.lam (.lam (encodeOptMixVal none))) := by
    simp [scoped0_any (encodeOptMixVal_scoped none)]
  refine steps_trans (steps_app_fn sd (steps_app_fn idx (steps_app_fn tf
    (.next (.fix (lowerProgRunnerSpec p) (.nat 0)) (.refl _))))) ?_
  change Steps (.app (.app (.app (.app (.app (lowerProgRunnerSpec p) (lowerProgRunner p)) (.nat 0)) tf) idx) sd) _
  dsimp only [lowerProgRunnerSpec]
  change Steps (.app (.app (.app (.app (.app (.lam (.lam (.lam (.ifZero (.bound 0)
    (.lam (.lam (encodeOptMixVal none))) (.app stepAdapter (.app (.bound 3) (.bound 0)))))))
    (lowerProgRunner p)) (.nat 0)) tf) idx) sd) _
  refine .next (.application sd (.application idx (.application tf (.application (.nat 0) (.beta _ _))))) ?_
  simp only [instantiate, Term.substitute, liftSubstitution,
    scoped0_ren hRunSc, scoped0_sub hRunSc, scoped0_ren hNoneR, scoped0_sub hNoneR,
    scoped0_ren hStepSc, scoped0_sub hStepSc]
  refine .next (.application sd (.application idx (.application tf (.beta _ _)))) ?_
  simp only [instantiate, Term.substitute, liftSubstitution,
    scoped0_ren hRunSc, scoped0_sub hRunSc, scoped0_ren hNoneR, scoped0_sub hNoneR,
    scoped0_ren hStepSc, scoped0_sub hStepSc]
  refine .next (.application sd (.application idx (.beta _ _))) ?_
  simp only [instantiate, Term.substitute, liftSubstitution,
    scoped0_ren hRunSc, scoped0_sub hRunSc, scoped0_ren hNoneR, scoped0_sub hNoneR,
    scoped0_ren hStepSc, scoped0_sub hStepSc]
  exact .refl _

private theorem lowerProgRunner_eval (p : MixProg) (fuel : Nat) :
    ∀ {e : MixExpr} (_he : e ∈ progSubtrees p.procs) {tf ts td : Term} {s d : MixVal},
      Evaluates tf (.nat fuel) →
      RealizesMixVal ts s → RealizesMixVal td d →
      RealizesOptMixVal
        (.app (.app (.app (lowerProgRunner p) tf) (.nat (findExprIdx (progSubtrees p.procs) e)))
          (.record [("s", ts), ("d", td)]))
        (evalExpr fuel p.procs e s d) := by
  induction fuel with
  | zero =>
    intro e _ tf ts td s d htf _ _
    let idx := Term.nat (findExprIdx (progSubtrees p.procs) e)
    let sd := Term.record [("s", ts), ("d", td)]
    have s3 : Steps (.app (.app (.lam (.lam (encodeOptMixVal none))) idx) sd) (encodeOptMixVal none) := by
      refine .next (.application sd (.beta _ _)) ?_
      simp only [instantiate, Term.substitute, liftSubstitution, scoped0_sub (encodeOptMixVal_scoped none)]
      refine .next (.beta _ _) ?_
      simp only [instantiate, scoped0_sub (encodeOptMixVal_scoped none)]; exact .refl _
    refine realizesOptMixVal_of_steps (steps_trans (lowerProgRunner_unfold p tf idx sd) (steps_trans ?_ s3))
      ⟨.nat 0, .refl _, .inject _ _⟩
    exact steps_app_fn sd (steps_app_fn idx (steps_trans (steps_ifZero_cond _ _ htf.1) (.next (.zero _ _) (.refl _))))
  | succ k ih =>
    intro e he tf ts td s d htf hs hd
    let cs := progSubtrees p.procs
    let disp := buildDispatch (cs.map (lowerExprArm p.procs cs))
    let idx := Term.nat (findExprIdx cs e)
    let sd := Term.record [("s", ts), ("d", td)]
    let rNext := Term.app (lowerProgRunner p) (.nat k)
    let stepAdapter := Term.lam (.lam (.lam (.app (.app disp (.bound 1))
      (.record [("r", .bound 2), ("s", .get (.bound 0) "s"), ("d", .get (.bound 0) "d")]))))
    have hRunSc := lowerProgRunner_scoped p
    have hRNextSc : Scoped 0 rNext := .app hRunSc (.natural k)
    have hIdxSc : Scoped 0 idx := .natural _
    have hDispSc : Scoped 0 disp := buildDispatch_scoped fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact lowerExprArm_scoped _ _ x
    have hStepSc : Scoped 0 stepAdapter := by simp [stepAdapter, scoped0_any hDispSc]
    have s1 : Steps (.app (.app (.app (lowerProgRunner p) tf) idx) sd)
        (.app (lowerExprArm p.procs cs e)
          (.record [("r", rNext), ("s", .get sd "s"), ("d", .get sd "d")])) := by
      refine steps_trans (lowerProgRunner_unfold p tf idx sd) ?_
      refine steps_trans (steps_app_fn sd (steps_app_fn idx (steps_trans (steps_ifZero_cond _ _ htf.1)
        (steps_succ_eq (target := .app stepAdapter rNext)
          (by change instantiate (.app stepAdapter (.app (lowerProgRunner p) (.bound 0))) (.nat k) = .app stepAdapter rNext
              simp only [instantiate, Term.substitute, scoped0_sub hStepSc, scoped0_sub hRunSc, rNext])
          (.refl _))))) ?_
      dsimp only [stepAdapter]
      refine .next (.application sd (.application idx (.beta _ _))) ?_
      simp only [instantiate, Term.substitute, Term.rename, liftSubstitution, List.map,
        scoped0_ren hDispSc, scoped0_sub hDispSc, scoped0_ren hRNextSc, scoped0_sub hRNextSc]
      refine .next (.application sd (.beta _ _)) ?_
      simp only [instantiate, Term.substitute, Term.rename, liftSubstitution, List.map,
        scoped0_ren hDispSc, scoped0_sub hDispSc, scoped0_ren hRNextSc, scoped0_sub hRNextSc,
        scoped0_ren hIdxSc, scoped0_sub hIdxSc]
      refine .next (.beta _ _) ?_
      simp only [instantiate, Term.substitute, List.map,
        scoped0_sub hDispSc, scoped0_sub hRNextSc, scoped0_sub hIdxSc]
      exact steps_app_fn _ (buildDispatch_steps (lowerExprArm p.procs cs) (fun x _ => lowerExprArm_scoped _ _ x) he)
    let env := Term.record [("r", rNext), ("s", .get sd "s"), ("d", .get sd "d")]
    have hEnvR : Steps (.get env "r") rNext := .next (.field _ "r" _ rfl) (.refl _)
    have hEnvS : RealizesMixVal (.get env "s") s :=
      realizesMixVal_of_steps (.next (.field _ "s" _ rfl) (.next (.field _ "s" _ rfl) (.refl _))) hs
    have hEnvD : RealizesMixVal (.get env "d") d :=
      realizesMixVal_of_steps (.next (.field _ "d" _ rfl) (.next (.field _ "d" _ rfl) (.refl _))) hd
    have callSub : ∀ {sub : MixExpr} (hSub : sub ∈ cs) {ts' td' : Term} {s' d' : MixVal},
        RealizesMixVal ts' s' → RealizesMixVal td' d' →
        RealizesOptMixVal (mkSubCall (.get env "r") cs sub ts' td') (evalExpr k p.procs sub s' d') := by
      intro sub hSub ts' td' s' d' hs' hd'
      exact realizesOptMixVal_of_steps (steps_app_fn _ (steps_app_fn _ hEnvR))
        (ih hSub ⟨.refl _, .natural k⟩ hs' hd')
    refine realizesOptMixVal_of_steps s1 ?_
    have hBeta : ∀ {body : Term} {ov : Option MixVal},
        RealizesOptMixVal (instantiate body env) ov → RealizesOptMixVal (.app (.lam body) env) ov :=
      fun hr => realizesOptMixVal_of_steps (.next (.beta _ env) (.refl _)) hr
    have hNoneOpt : RealizesOptMixVal (encodeOptMixVal none) none := ⟨.nat 0, .refl _, .inject _ _⟩
    cases e with
    | dVar =>
      dsimp only [lowerExprArm]; refine hBeta ?_; simp only [instantiate, Term.substitute]
      exact ⟨_, ⟨.refl _, .inject _ _⟩, hEnvD⟩
    | dLit v =>
      dsimp only [lowerExprArm]; refine hBeta ?_; simp only [instantiate, Term.substitute, scoped0_sub (encodeMixVal_scoped v)]
      exact ⟨_, ⟨.refl _, .inject _ _⟩, encodeMixVal_realizes v⟩
    | dLift se =>
      dsimp only [lowerExprArm]; refine hBeta ?_; simp only [instantiate, Term.substitute, scoped0_sub (lowerSExprCore_scoped se)]
      exact ⟨_, ⟨.refl _, .inject _ _⟩, lowerSExprCore_realizes se hEnvS⟩
    | dUnary op e1 =>
      have hr1 := callSub (child_mem_progSubtrees he (List.Mem.head _)) hEnvS hEnvD
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
        scoped0_sub (lowerUnaryCore_scoped op), scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeOptMixVal_scoped none)]
      refine realizesOpt_ifBool (isSomeCore_eval hr1) ?_
      simp only [evalExpr]
      cases h1 : evalExpr k p.procs e1 s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
      · exact hNoneOpt
      · rename_i v1; rw [h1] at hr1
        exact ⟨_, ⟨.refl _, .inject _ _⟩, lowerUnaryCore_realizes op (unboxSomeCore_realizes hr1)⟩
    | dBin op e1 e2 =>
      have hr1 := callSub (child_mem_progSubtrees he (List.Mem.head _)) hEnvS hEnvD
      have hr2 := callSub (child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.head _))) hEnvS hEnvD
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
        scoped0_sub (lowerBinCore_scoped op), scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeOptMixVal_scoped none)]
      refine realizesOpt_ifBool (isSomeCore_eval hr1) ?_
      simp only [evalExpr]
      cases h1 : evalExpr k p.procs e1 s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
      · exact hNoneOpt
      · rename_i v1; rw [h1] at hr1
        refine realizesOpt_ifBool (isSomeCore_eval hr2) ?_
        cases h2 : evalExpr k p.procs e2 s d <;> simp only [h2, Option.isSome, ↓reduceIte, Bool.false_eq_true]
        · exact hNoneOpt
        · rename_i v2; rw [h2] at hr2
          exact ⟨_, ⟨.refl _, .inject _ _⟩,
            lowerBinCore_realizes op (unboxSomeCore_realizes hr1) (unboxSomeCore_realizes hr2)⟩
    | dIf c t f =>
      have hc : c ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      have ht : t ∈ cs := child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.head _))
      have hf : f ∈ cs := child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hrc := callSub hc hEnvS hEnvD
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
        scoped0_sub isTrueCore_scoped, scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeOptMixVal_scoped none)]
      refine realizesOpt_ifBool (isSomeCore_eval hrc) ?_
      simp only [evalExpr]
      cases h1 : evalExpr k p.procs c s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
      · exact hNoneOpt
      · rename_i vc; rw [h1] at hrc
        refine realizesOpt_ifBool (isTrueCore_eval (unboxSomeCore_realizes hrc)) ?_
        cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true]
        · exact callSub hf hEnvS hEnvD
        · exact callSub ht hEnvS hEnvD
    | dWhile c body =>
      have hrc := callSub (child_mem_progSubtrees he (List.Mem.head _)) hEnvS hEnvD
      have hrb := callSub (child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.head _))) hEnvS hEnvD
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
        scoped0_sub isTrueCore_scoped, scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeOptMixVal_scoped none)]
      refine realizesOpt_ifBool (isSomeCore_eval hrc) ?_
      simp only [evalExpr]
      cases h1 : evalExpr k p.procs c s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
      · exact hNoneOpt
      · rename_i vc; rw [h1] at hrc
        refine realizesOpt_ifBool (isTrueCore_eval (unboxSomeCore_realizes hrc)) ?_
        cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true]
        · exact ⟨_, ⟨.refl _, .inject _ _⟩, hEnvD⟩
        · refine realizesOpt_ifBool (isSomeCore_eval hrb) ?_
          cases h2 : evalExpr k p.procs body s d <;> simp only [h2, Option.isSome, ↓reduceIte, Bool.false_eq_true]
          · exact hNoneOpt
          · rename_i d'; rw [h2] at hrb
            exact callSub he hEnvS (unboxSomeCore_realizes hrb)
    | dWithEnv e1 e2 =>
      have hr1 := callSub (child_mem_progSubtrees he (List.Mem.head _)) hEnvS hEnvD
      have he2 : e2 ∈ cs := child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.head _))
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
        scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeOptMixVal_scoped none)]
      refine realizesOpt_ifBool (isSomeCore_eval hr1) ?_
      simp only [evalExpr]
      cases h1 : evalExpr k p.procs e1 s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
      · exact hNoneOpt
      · rename_i d'; rw [h1] at hr1
        exact callSub he2 hEnvS (unboxSomeCore_realizes hr1)
    | dCall callee dArg =>
      have hdArg : dArg ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      dsimp only [lowerExprArm]; simp only [evalExpr]
      cases hLook : lookupProc p.procs callee with
      | none =>
        refine hBeta ?_; simp only [instantiate, scoped0_sub (encodeOptMixVal_scoped none)]
        cases evalExpr k p.procs dArg s d <;> exact hNoneOpt
      | some pBody =>
        have hrd := callSub hdArg hEnvS hEnvD
        refine hBeta ?_
        simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
          scoped0_sub unboxSomeCore_scoped, scoped0_sub (encodeMixVal_scoped .nil), scoped0_sub (encodeOptMixVal_scoped none)]
        refine realizesOpt_ifBool (isSomeCore_eval hrd) ?_
        cases h1 : evalExpr k p.procs dArg s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
        · exact hNoneOpt
        · rename_i dv; rw [h1] at hrd
          exact callSub (lookup_mem_progSubtrees hLook) (encodeMixVal_realizes .nil) (unboxSomeCore_realizes hrd)
    | sIf c t f =>
      have ht : t ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      have hf : f ∈ cs := child_mem_progSubtrees he (List.Mem.tail _ (List.Mem.head _))
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isTrueCore_scoped, scoped0_sub (lowerSExprCore_scoped c)]
      refine realizesOpt_ifBool (isTrueCore_eval (lowerSExprCore_realizes c hEnvS)) ?_
      simp only [evalExpr]
      cases hct : (evalSExpr c s).isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true]
      · exact callSub hf hEnvS hEnvD
      · exact callSub ht hEnvS hEnvD
    | sLet b body =>
      have hb : body ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      dsimp only [lowerExprArm]; refine hBeta ?_
      simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub (lowerSExprCore_scoped b)]
      exact callSub hb ⟨_, _, _, ⟨.refl _, .inject _ _⟩, ⟨.refl _, .record _⟩,
        lowerSExprCore_realizes b hEnvS, hEnvS⟩ hEnvD
    | sCall callee sArg dArg =>
      have hdArg : dArg ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      dsimp only [lowerExprArm]; simp only [evalExpr]
      cases hLook : lookupProc p.procs callee with
      | none =>
        refine hBeta ?_; simp only [instantiate, scoped0_sub (encodeOptMixVal_scoped none)]
        cases evalExpr k p.procs dArg s d <;> exact hNoneOpt
      | some pBody =>
        have hrd := callSub hdArg hEnvS hEnvD
        refine hBeta ?_
        simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
          scoped0_sub unboxSomeCore_scoped, scoped0_sub (lowerSExprCore_scoped sArg), scoped0_sub (encodeOptMixVal_scoped none)]
        refine realizesOpt_ifBool (isSomeCore_eval hrd) ?_
        cases h1 : evalExpr k p.procs dArg s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
        · exact hNoneOpt
        · rename_i dv; rw [h1] at hrd
          exact callSub (lookup_mem_progSubtrees hLook) (lowerSExprCore_realizes sArg hEnvS) (unboxSomeCore_realizes hrd)
    | spCall callee sKey dArg =>
      have hdArg : dArg ∈ cs := child_mem_progSubtrees he (List.Mem.head _)
      dsimp only [lowerExprArm]; simp only [evalExpr]
      cases hLook : lookupProc p.procs callee with
      | none =>
        refine hBeta ?_; simp only [instantiate, scoped0_sub (encodeOptMixVal_scoped none)]
        cases evalExpr k p.procs dArg s d <;> exact hNoneOpt
      | some pBody =>
        have hrd := callSub hdArg hEnvS hEnvD
        refine hBeta ?_
        simp only [mkSubCall, instantiate, Term.substitute, List.map, scoped0_sub isSomeCore_scoped,
          scoped0_sub unboxSomeCore_scoped, scoped0_sub (lowerSExprCore_scoped sKey), scoped0_sub (encodeOptMixVal_scoped none)]
        refine realizesOpt_ifBool (isSomeCore_eval hrd) ?_
        cases h1 : evalExpr k p.procs dArg s d <;> simp only [h1, Option.isSome, ↓reduceIte, Bool.false_eq_true]
        · exact hNoneOpt
        · rename_i dv; rw [h1] at hrd
          exact callSub (lookup_mem_progSubtrees hLook) (lowerSExprCore_realizes sKey hEnvS) (unboxSomeCore_realizes hrd)

/-- **Simulation Theorem (`lowerMixToCore4_sound`)**:
    For every `p : MixProg`, `fuel : Nat`, and `s d : MixVal`, the lowered `Core4` combinator
    evaluates under `Core.Term.Evaluates` to a lazy `Core4` value realizing `evalMix fuel p s d`. -/
theorem lowerMixToCore4_sound (p : MixProg) (fuel : Nat) (s d : MixVal) :
    RealizesOptMixVal (applyLoweredMix (lowerMixToCore4 p) fuel s d) (evalMix fuel p s d) := by
  unfold applyLoweredMix lowerMixToCore4 evalMix
  cases hLook : lookupProc p.procs p.entry with
  | none =>
    dsimp only
    refine realizesOptMixVal_of_steps
      (steps_beta_eq (target := encodeOptMixVal none) (by simp [instantiate, scoped0_sub (encodeOptMixVal_scoped none)]) (.refl (encodeOptMixVal none)))
      ⟨.nat 0, .refl _, .inject _ _⟩
  | some entryBody =>
    dsimp only
    let inp := Term.record [("fuel", .nat fuel), ("s", encodeMixVal s), ("d", encodeMixVal d)]
    have hEval := lowerProgRunner_eval p fuel (lookup_mem_progSubtrees hLook)
      (tf := .get inp "fuel") (ts := .get inp "s") (td := .get inp "d")
      ⟨.next (.field _ "fuel" _ rfl) (.refl _), .natural fuel⟩
      (realizesMixVal_of_steps (.next (.field _ "s" _ rfl) (.refl _)) (encodeMixVal_realizes s))
      (realizesMixVal_of_steps (.next (.field _ "d" _ rfl) (.refl _)) (encodeMixVal_realizes d))
    refine realizesOptMixVal_of_steps (steps_beta_eq ?_ (.refl _)) hEval
    simp [inp, instantiate, Term.substitute, List.map, scoped0_sub (lowerProgRunner_scoped p)]

private theorem runBounded_mono {l1 l2 : Limits} (hh : l1.heap ≤ l2.heap) (hs : l1.stack ≤ l2.stack) :
    ∀ {ticks : Nat} {st final : State} {val : RuntimeValue},
      runBounded l1 ticks st = .finished val final →
      runBounded l2 ticks st = .finished val final
  | 0, st, final, val, h => by
    cases hc : st.control <;> simp [runBounded, hc] at h ⊢; exact h
  | ticks + 1, st, final, val, h => by
    cases hStep : step l1 st with
    | finished v nxt =>
      simp only [runBounded, hStep] at h
      have hStep2 : step l2 st = .finished v nxt := by
        cases hc : st.control <;> simp [step, hc] at hStep ⊢
        all_goals try (split at hStep <;> contradiction)
        exact hStep
      simp [runBounded, hStep2, h]
    | suspended rsn nxt =>
      cases rsn with
      | capacity => simp [runBounded, hStep] at h
      | ticks =>
        simp only [runBounded, hStep] at h
        have hStep2 : step l2 st = .suspended .ticks nxt := by
          cases hc : st.control <;> simp only [step, hc] at hStep ⊢
          all_goals try contradiction
          all_goals
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hStep ⊢
            split at hStep
            · rename_i hFit
              have hFit2 : (stepRaw st).heap.size ≤ l2.heap ∧ (stepRaw st).stack.length ≤ l2.stack :=
                ⟨Nat.le_trans hFit.1 hh, Nat.le_trans hFit.2 hs⟩
              simp only [hFit2, and_self, ↓reduceIte]
              injection hStep with _ hEq; rw [hEq]
            · cases hStep
        simp only [runBounded, hStep2]
        exact runBounded_mono hh hs h
    | divergent _ _ | refused _ _ | yielded _ _ => simp [runBounded, hStep] at h

/-- **End-to-End `Core4` Demand-Machine Execution (`lowerMixToCore4_machine_complete`)**:
    Whenever `evalMix fuel p s d = some (.num n)`, the closed `Core4` term
    `.app extractNumCore (applyLoweredMix (lowerMixToCore4 p) fuel s d)` evaluates to `.nat n`
    AND executes to `.finished (.natural n)` on `Machine.runBounded` / `MachineFast`. -/
theorem lowerMixToCore4_machine_complete
    (p : MixProg) (fuel : Nat) (s d : MixVal) (n : Nat)
    (hEval : evalMix fuel p s d = some (.num n)) :
    let term := Term.app extractNumCore (applyLoweredMix (lowerMixToCore4 p) fuel s d)
    Scoped 0 term ∧
    Evaluates term (.nat n) ∧
    ∃ (limits : Limits) (ticks : Nat) (final : State),
      runBounded limits ticks (initial term) = .finished (.natural n) final := by
  intro term
  have hClosed : Scoped 0 term := .app extractNumCore_scoped (applyLoweredMix_scoped p fuel s d)
  have hSim := lowerMixToCore4_sound p fuel s d
  rw [hEval] at hSim
  have hEv : Evaluates term (.nat n) := extractNumCore_evaluates hSim
  obtain ⟨initSt, final, hStart, hSteps, hFin⟩ :=
    Obend.Core.Proofs.Completeness.machine_evaluation_complete hClosed hEv (.natural n)
  have hInit : initSt = initial term := by
    simp [Obend.Core.Proofs.Completeness.startSource, hClosed] at hStart; exact hStart.symm
  refine ⟨hClosed, hEv, ?_⟩
  rw [← hInit]
  clear hStart hInit
  induction hSteps with
  | refl s0 =>
    obtain ⟨rv, hc, hg⟩ := Obend.Core.Proofs.Completeness.machineTransition_finished hFin
    cases rv <;> simp [Obend.Core.Proofs.Completeness.groundObservation] at hg
    subst hg
    exact ⟨{ heap := s0.heap.size, stack := s0.stack.length }, 0, s0, by simp [runBounded, hc]⟩
  | @next sCur sNext _ hAdv _ ih =>
    obtain ⟨lim, ticks, fin, hRun⟩ := ih hFin
    obtain ⟨rfl, _, running⟩ := Obend.Core.Proofs.Completeness.machineTransition_advanced hAdv
    let lim' : Limits :=
      { heap := max lim.heap (stepRaw sCur).heap.size
      , stack := max lim.stack (stepRaw sCur).stack.length }
    have hRun' := runBounded_mono (l2 := lim') (Nat.le_max_left _ _) (Nat.le_max_left _ _) hRun
    have hStepCur : step lim' sCur = .suspended .ticks (stepRaw sCur) := by
      cases hc : sCur.control with
      | complete rv => exact False.elim (running rv hc)
      | refused _ | blackhole _ | yielded _ =>
        simp [Obend.Core.Proofs.Completeness.machineTransition, step, hc,
          Obend.Core.Proofs.Completeness.outcomeTransition] at hAdv
      | evaluate _ _ | enter _ | returned _ =>
        have hFitLim : (stepRaw sCur).heap.size ≤ lim'.heap ∧ (stepRaw sCur).stack.length ≤ lim'.stack :=
          ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
        simp [step, hc, hFitLim]
    exact ⟨lim', ticks + 1, fin, by rw [runBounded, hStepCur]; exact hRun'⟩

end Obend.Leaf.SelfApplicableMix
end
