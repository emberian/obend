module
/-
# `Obend.Lower.Pancake.LcnfEmit` — First-Order `LcnfCode` Range/Shape Checker, Emitter & `evalFoBlock`

Defines the collision-free constructor tag table, disjoint `'v'`/`'h'`/`'a'` local slot supply,
64-bit range-and-shape checker `checkFoLcnf`, path-sensitive `synthLcnfClk`, `PStmt` emitter
`compileLcnfToPancake`, and fuel-free block evaluator `evalFoBlock` + equivalence with
`Obend.Lower.LCNF.evalLcnfCodeVal` (`G6`).
-/
public import Obend.Lower.LCNF
public import Obend.Lower.Pancake.PanSem
public import Obend.Lower.Pancake.CondSClk
import all Obend.Core.Term
import all Obend.Lower.LCNF
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.CondSClk

public section

namespace Obend.Lower.Pancake

open Obend.Core.Term (splitValues)
open Obend.Lower (NatOp)
open Obend.Lower.LCNF

set_option autoImplicit false

/-! ## 1. Collision-Free Constructor Tag Table & Disjoint Local Slot Supply -/

mutual
/-- Collect all constructor tag strings appearing in `.ctor` or `.cases` across `c`. -/
def collectTags : LcnfCode → List String
  | .return _ => []
  | .unreach => []
  | .jmp _ _ => []
  | .letValue (.ctor tag _) body => tag :: collectTags body
  | .letValue _ body => collectTags body
  | .jpDecl _ _ jpBody body => collectTags body ++ collectTags jpBody
  | .ifBool _ t f => collectTags t ++ collectTags f
  | .cases _ arms => collectArmsTags arms
termination_by structural c => c

def collectArmsTags : List (String × List String × LcnfCode) → List String
  | [] => []
  | (tag, _, body) :: rest => tag :: (collectTags body ++ collectArmsTags rest)
termination_by structural arms => arms
end

/-- First-occurrence index of `tag` in `tags`. -/
def lookupTagIdx : List String → String → Option Nat
  | [], _ => none
  | hd :: tl, t => if hd == t then some 0 else (lookupTagIdx tl t).map (· + 1)
termination_by structural tags => tags

theorem lookupTagIdx_lt {tags : List String} {t : String} {i : Nat}
    (h : lookupTagIdx tags t = some i) : i < tags.length := by
  induction tags generalizing i with
  | nil => simp [lookupTagIdx] at h
  | cons hd tl ih =>
    simp only [lookupTagIdx] at h
    if heq : hd == t then
      simp [heq] at h; subst h; simp
    else
      simp [heq] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih hj
      simp; omega

theorem lookupTagIdx_inj {tags : List String} {t1 t2 : String} {i : Nat}
    (h1 : lookupTagIdx tags t1 = some i) (h2 : lookupTagIdx tags t2 = some i) :
    t1 = t2 := by
  induction tags generalizing i with
  | nil => simp [lookupTagIdx] at h1
  | cons hd tl ih =>
    simp only [lookupTagIdx] at h1 h2
    cases e1 : (hd == t1) <;> cases e2 : (hd == t2) <;> simp [e1, e2] at h1 h2
    · obtain ⟨j1, hj1, heq1⟩ := h1
      obtain ⟨j2, hj2, heq2⟩ := h2
      have hjeq : j1 = j2 := by omega
      subst hjeq
      exact ih hj1 hj2
    · omega
    · omega
    · have ht1 : hd = t1 := beq_iff_eq.mp e1
      have ht2 : hd = t2 := beq_iff_eq.mp e2
      exact ht1.symm.trans ht2

/-- Kind-tagged local variable name generator (`'v'` = computational var, `'h'` = join hit flag,
    `'a'` = join argument slot). Injective on `(kind, id)` by length/head inspection. -/
def mkSlot (kind : Char) (id : Nat) : String :=
  String.ofList (kind :: List.replicate id '_')

theorem mkSlot_inj {k1 k2 : Char} {i1 i2 : Nat} (h : mkSlot k1 i1 = mkSlot k2 i2) :
    k1 = k2 ∧ i1 = i2 := by
  have hl : (mkSlot k1 i1).toList = (mkSlot k2 i2).toList := congrArg String.toList h
  simp only [mkSlot, String.toList_ofList, List.cons.injEq] at hl
  refine ⟨hl.1, ?_⟩
  have hlen := congrArg List.length hl.2
  simpa [List.length_replicate] using hlen

theorem mkSlot_ne_of_kind {k1 k2 : Char} (hk : k1 ≠ k2) (i1 i2 : Nat) :
    mkSlot k1 i1 ≠ mkSlot k2 i2 :=
  fun h => hk (mkSlot_inj h).1

theorem mkSlot_ne_of_lt {k1 k2 : Char} {i1 i2 : Nat} (hlt : i1 < i2) :
    mkSlot k1 i1 ≠ mkSlot k2 i2 :=
  fun h => by have := (mkSlot_inj h).2; omega

/-! ## 2. First-Order LCNF Range- & Shape-Safe Type System (`FoScalarTy`, `FoTy`, `checkFoLcnf`) -/

/-- Pure syntactic first-order RHS check (excludes closures and linear state tokens). -/
def foPureLetVal : LcnfLetValue → Bool
  | .arg _ | .natOp _ _ _ | .ctor _ _ => true
  | _ => false

mutual
/-- Pure syntactic first-order code predicate (every nested branch/arm/join body uses `foPureLetVal`). -/
def foPureCode : LcnfCode → Bool
  | .return _ | .unreach | .jmp _ _ => true
  | .letValue lv body => foPureLetVal lv && foPureCode body
  | .ifBool _ t f => foPureCode t && foPureCode f
  | .cases _ arms => foPureArms arms
  | .jpDecl _ _ jpBody body => foPureCode jpBody && foPureCode body
termination_by structural c => c

def foPureArms : List (String × List String × LcnfCode) → Bool
  | [] => true
  | (_, _, body) :: rest => foPureCode body && foPureArms rest
termination_by structural arms => arms
end

/-- First-order 1-word (`Shape.One`) types admitted across join-point parameters and scalars. -/
inductive FoScalarTy where
  | scalar (maxVal : Nat)
  | bool
  | erased
  deriving DecidableEq, Repr, Inhabited

/-- First-order LCNF value types (1-word scalars/bools/erased + tagged scalar-field ADTs). -/
inductive FoTy where
  | one (st : FoScalarTy)
  | ctor (tag : String) (fieldNames : List String) (fieldBounds : List Nat)
  deriving DecidableEq, Repr, Inhabited

def FoTy.toShape : FoTy → Shape
  | .one _ => .One
  | .ctor _ fieldNames _ => .Comb (List.replicate (fieldNames.length + 1) .One)

def FoScalarTy.wf : FoScalarTy → Bool
  | .scalar hi => decide (hi < 2 ^ 64)
  | .bool      => true
  | .erased    => true

def FoScalarTy.subTy : FoScalarTy → FoScalarTy → Bool
  | .scalar a, .scalar b => decide (a ≤ b) && decide (b < 2 ^ 64)
  | .bool,     .bool     => true
  | .erased,   .erased   => true
  | _,         _         => false

def FoScalarTy.join : FoScalarTy → FoScalarTy → Option FoScalarTy
  | .scalar a, .scalar b =>
    let m := max a b
    if decide (m < 2 ^ 64) then some (.scalar m) else none
  | .bool,   .bool   => some .bool
  | .erased, .erased => some .erased
  | _,       _       => none

def joinScalarList : List FoScalarTy → List FoScalarTy → Option (List FoScalarTy)
  | [], [] => some []
  | x :: xs, y :: ys =>
    match x.join y, joinScalarList xs ys with
    | some z, some zs => some (z :: zs)
    | _, _ => none
  | _, _ => none
termination_by structural xs => xs

/-- Join-point typing signature (`jpId` + 1-word parameter bounds). -/
structure JpSig where
  jpId   : Nat
  params : List FoScalarTy
  deriving DecidableEq, Repr, Inhabited

def inferArgFoTy (envTys : List FoTy) : LcnfArg → Option FoTy
  | .bvar idx   => envTys[idx]?
  | .lit n      => if decide (n < 2 ^ 64) then some (.one (.scalar n)) else none
  | .boolLit _  => some (.one .bool)
  | .erased     => some (.one .erased)
  | .stateTok _ => none

def inferArgScalarTy (envTys : List FoTy) (a : LcnfArg) : Option FoScalarTy :=
  match inferArgFoTy envTys a with
  | some (.one st) => if st.wf then some st else none
  | _ => none

def inferCtorFields (envTys : List FoTy) :
    List (String × LcnfArg) → Option (List String × List Nat)
  | [] => some ([], [])
  | (nm, a) :: rest =>
    match inferArgFoTy envTys a, inferCtorFields envTys rest with
    | some (.one (.scalar b)), some (nms, bs) =>
      if decide (b < 2 ^ 64) && !(nms.contains nm) then
        some (nm :: nms, b :: bs)
      else
        none
    | _, _ => none
termination_by structural fs => fs

def inferLetValFoTy (tags : List String) (envTys : List FoTy) : LcnfLetValue → Option FoTy
  | .arg a => inferArgFoTy envTys a
  | .natOp op l r =>
    match inferArgFoTy envTys l, inferArgFoTy envTys r with
    | some (.one (.scalar b1)), some (.one (.scalar b2)) =>
      if decide (b1 < 2 ^ 64) && decide (b2 < 2 ^ 64) then
        match op with
        | .add =>
          if decide (b1 + b2 < 2 ^ 64) then some (.one (.scalar (b1 + b2))) else none
        | .sub => some (.one (.scalar b1))
        | .mul =>
          if decide (b1 * b2 < 2 ^ 64) then some (.one (.scalar (b1 * b2))) else none
        | .beq => some (.one .bool)
        | .ble => some (.one .bool)
        | .div | .mod => none
      else
        none
    | _, _ => none
  | .ctor tag fields =>
    match lookupTagIdx tags tag, inferCtorFields envTys fields with
    | some idx, some (nms, bs) =>
      if decide (idx < 2 ^ 64) then some (.ctor tag nms bs) else none
    | _, _ => none
  | .record _ | .proj _ _ | .app _ _ | .stateRead _ _ | .stateWrite _ _ _ => none

def mergeOptParams : Option (List FoScalarTy) → Option (List FoScalarTy) → Option (Option (List FoScalarTy))
  | none, y => some y
  | x, none => some x
  | some xs, some ys => (joinScalarList xs ys).map some

mutual
/-- Untrusted parameter-type inference helper scanning `jmp targetJpId` sites inside `body`.
    Soundness does NOT rely on this helper: `checkFoCode` independently verifies every jump. -/
def inferJpParams (tags : List String) (targetJpId numParams : Nat) (envTys : List FoTy) :
    LcnfCode → Option (Option (List FoScalarTy))
  | .return _ => some none
  | .unreach  => some none
  | .jmp id args =>
    if id == targetJpId then
      if args.length == numParams then
        (args.mapM (inferArgScalarTy envTys)).map some
      else
        none
    else
      some none
  | .letValue v body =>
    match inferLetValFoTy tags envTys v with
    | some ty => inferJpParams tags targetJpId numParams (ty :: envTys) body
    | none => none
  | .ifBool _ t f =>
    match inferJpParams tags targetJpId numParams envTys t,
          inferJpParams tags targetJpId numParams envTys f with
    | some p1, some p2 => mergeOptParams p1 p2
    | _, _ => none
  | .cases scrut arms =>
    match inferArgFoTy envTys scrut with
    | some (.ctor cTag cNames cBounds) =>
      let armEnv := (cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys
      inferJpParamsArm tags targetJpId numParams armEnv cTag cNames arms
    | _ => none
  | .jpDecl innerId innerN innerJpBody innerBody =>
    if innerId == targetJpId then none
    else
      match inferJpParams tags innerId innerN envTys innerBody with
      | some innerOpt =>
        let innerParams := innerOpt.getD (List.replicate innerN (.scalar 0))
        match inferJpParams tags targetJpId numParams envTys innerBody,
              inferJpParams tags targetJpId numParams (innerParams.map FoTy.one ++ envTys) innerJpBody with
        | some p1, some p2 => mergeOptParams p1 p2
        | _, _ => none
      | none => none
termination_by structural c => c

def inferJpParamsArm (tags : List String) (targetJpId numParams : Nat) (armEnv : List FoTy)
    (cTag : String) (cNames : List String) :
    List (String × List String × LcnfCode) → Option (Option (List FoScalarTy))
  | [] => none
  | (aTag, armNames, armBody) :: rest =>
    if aTag == cTag then
      if armNames == cNames then inferJpParams tags targetJpId numParams armEnv armBody else none
    else
      inferJpParamsArm tags targetJpId numParams armEnv cTag cNames rest
termination_by structural arms => arms
end

def checkArgsSubTy (envTys : List FoTy) : List LcnfArg → List FoScalarTy → Bool
  | [], [] => true
  | a :: as, expected :: es =>
    match inferArgScalarTy envTys a with
    | some actual => actual.subTy expected && checkArgsSubTy envTys as es
    | none => false
  | _, _ => false
termination_by structural as => as

def checkArmTagsValid (tags : List String) : List (String × List String × LcnfCode) → Bool
  | [] => true
  | (atag, _, _) :: rest =>
    (match lookupTagIdx tags atag with
     | some idx => decide (idx < 2 ^ 64)
     | none => false) && checkArmTagsValid tags rest
termination_by structural arms => arms

mutual
/-- Check whether `c` is a well-typed first-order LCNF block returning a scalar `≤ retBound < 2^64`
    (or jumping to an active `JpSig` in `jpSigs`). -/
def checkFoCode (tags : List String) (envTys : List FoTy) (jpSigs : List JpSig) :
    LcnfCode → Option Nat
  | .return a =>
    match inferArgFoTy envTys a with
    | some (.one (.scalar b)) => if decide (b < 2 ^ 64) then some b else none
    | _ => none
  | .unreach => none
  | .jmp id args =>
    match jpSigs.find? (fun s => s.jpId == id) with
    | some sig =>
      if args.length == sig.params.length && checkArgsSubTy envTys args sig.params then
        some 0
      else
        none
    | none => none
  | .letValue v body =>
    match inferLetValFoTy tags envTys v with
    | some ty => checkFoCode tags (ty :: envTys) jpSigs body
    | none => none
  | .ifBool cond t f =>
    match inferArgFoTy envTys cond with
    | some (.one .bool) =>
      match checkFoCode tags envTys jpSigs t, checkFoCode tags envTys jpSigs f with
      | some b1, some b2 => some (max b1 b2)
      | _, _ => none
    | _ => none
  | .cases scrut arms =>
    match scrut, inferArgFoTy envTys scrut with
    | .bvar _, some (.ctor cTag cNames cBounds) =>
      if checkArmTagsValid tags arms && foPureArms arms then
        let armEnv := (cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys
        checkFoArm tags armEnv jpSigs cTag cNames arms
      else
        none
    | _, _ => none
  | .jpDecl jpId numParams jpBody body =>
    if jpSigs.any (fun s => s.jpId == jpId) then none
    else
      match inferJpParams tags jpId numParams envTys body with
      | some optParams =>
        let paramTys := optParams.getD (List.replicate numParams (.scalar 0))
        if paramTys.length == numParams && paramTys.all FoScalarTy.wf then
          match checkFoCode tags envTys (⟨jpId, paramTys⟩ :: jpSigs) body,
                checkFoCode tags (paramTys.map FoTy.one ++ envTys) jpSigs jpBody with
          | some b1, some b2 => some (max b1 b2)
          | _, _ => none
        else
          none
      | none => none
termination_by structural c => c

def checkFoArm (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    List (String × List String × LcnfCode) → Option Nat
  | [] => none
  | (aTag, armNames, armBody) :: rest =>
    if aTag == cTag then
      if armNames == cNames then checkFoCode tags armEnv jpSigs armBody else none
    else
      checkFoArm tags armEnv jpSigs cTag cNames rest
termination_by structural arms => arms
end

theorem checkFoArm_eq_find (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    ∀ arms, checkFoArm tags armEnv jpSigs cTag cNames arms =
      match arms.find? (fun a => a.1 == cTag) with
      | some (_, armNames, armBody) =>
        if armNames == cNames then checkFoCode tags armEnv jpSigs armBody else none
      | none => none
  | [] => by exact Eq.trans rfl rfl
  | (aTag, armNames, armBody) :: rest => by
    simp only [checkFoArm, List.find?]
    cases aTag == cTag <;> simp [checkFoArm_eq_find]

/-- Top-level first-order closed scalar `LcnfCode` checker (`some maxRetVal` when well-typed). -/
@[expose] def checkFoLcnf (c : LcnfCode) : Option Nat :=
  let tags := collectTags c
  if decide (tags.length < 2 ^ 64) then
    checkFoCode tags [] [] c
  else
    none

mutual
theorem checkFoCode_bound_lt (tags : List String) :
    ∀ (c : LcnfCode) (envTys : List FoTy) (jpSigs : List JpSig) (b : Nat),
      checkFoCode tags envTys jpSigs c = some b →
      b < 2 ^ 64 ∧ foPureCode c = true
  | .return a, envTys, _, b, h => by
    simp only [checkFoCode] at h
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at h
    | some ty =>
      rw [ha] at h
      cases ty with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st with
        | bool | erased => simp at h
        | scalar hi =>
          dsimp only at h
          by_cases hlt : hi < 2 ^ 64 <;> simp [hlt] at h
          subst h; exact ⟨hlt, rfl⟩
  | .unreach, _, _, _, h => by simp [checkFoCode] at h
  | .jmp id _, _, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hf : jpSigs.find? (fun s => s.jpId == id) with
    | none => simp [hf] at h
    | some sig =>
      rw [hf] at h
      dsimp only at h
      split at h <;> simp at h
      subst h; exact ⟨by decide, rfl⟩
  | .letValue v body, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hty : inferLetValFoTy tags envTys v with
    | none => simp [hty] at h
    | some ty =>
      rw [hty] at h
      have hlv : foPureLetVal v = true := by
        cases v <;> simp [inferLetValFoTy, foPureLetVal] at hty ⊢
      obtain ⟨hlt, hp⟩ := checkFoCode_bound_lt tags body (ty :: envTys) jpSigs b h
      exact ⟨hlt, by simp [foPureCode, hlv, hp]⟩
  | .ifBool cond t f, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hc : inferArgFoTy envTys cond with
    | none => simp [hc] at h
    | some ty =>
      rw [hc] at h
      cases ty with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st <;> simp at h
        cases ht : checkFoCode tags envTys jpSigs t <;>
          cases hf : checkFoCode tags envTys jpSigs f <;> simp [ht, hf] at h
        obtain ⟨hlt1, hp1⟩ := checkFoCode_bound_lt tags t envTys jpSigs _ ht
        obtain ⟨hlt2, hp2⟩ := checkFoCode_bound_lt tags f envTys jpSigs _ hf
        subst h
        exact ⟨by omega, by simp [foPureCode, hp1, hp2]⟩
  | .cases scrut arms, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases scrut with
    | lit _ | boolLit _ | erased | stateTok _ => simp at h
    | bvar idx =>
      cases hs : inferArgFoTy envTys (.bvar idx) with
      | none => simp [hs] at h
      | some sty =>
        rw [hs] at h
        cases sty with
        | one _ => simp at h
        | ctor cTag cNames cBounds =>
          dsimp only at h
          cases hcond : (checkArmTagsValid tags arms && foPureArms arms) with
          | false => rw [hcond] at h; simp at h
          | true =>
            simp only [hcond, ↓reduceIte] at h
            simp only [Bool.and_eq_true] at hcond
            exact ⟨checkFoArm_bound_lt tags _ jpSigs cTag cNames arms b h,
              by simp [foPureCode, hcond.2]⟩
  | .jpDecl jpId numParams jpBody body, envTys, jpSigs, b, h => by
    simp only [checkFoCode] at h
    cases hany : jpSigs.any (fun s => s.jpId == jpId) with
    | true => simp [hany] at h
    | false =>
      simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
      cases hinf : inferJpParams tags jpId numParams envTys body with
      | none => simp [hinf] at h
      | some optP =>
        rw [hinf] at h
        dsimp only at h
        split at h <;> try simp at h
        cases hb1 : checkFoCode tags envTys (⟨jpId, optP.getD (List.replicate numParams (.scalar 0))⟩ :: jpSigs) body with
        | none => rw [hb1] at h; cases h
        | some b1 =>
          cases hb2 : checkFoCode tags ((optP.getD (List.replicate numParams (.scalar 0))).map FoTy.one ++ envTys) jpSigs jpBody with
          | none => rw [hb1, hb2] at h; cases h
          | some b2 =>
            rw [hb1, hb2] at h
            injection h with h
            obtain ⟨hlt1, hp1⟩ := checkFoCode_bound_lt tags body _ _ _ hb1
            obtain ⟨hlt2, hp2⟩ := checkFoCode_bound_lt tags jpBody _ _ _ hb2
            subst h
            exact ⟨by omega, by simp [foPureCode, hp2, hp1]⟩
termination_by structural c => c

theorem checkFoArm_bound_lt (tags : List String) (armEnv : List FoTy) (jpSigs : List JpSig)
    (cTag : String) (cNames : List String) :
    ∀ (arms : List (String × List String × LcnfCode)) (b : Nat),
      checkFoArm tags armEnv jpSigs cTag cNames arms = some b →
      b < 2 ^ 64
  | [], _, h => by simp [checkFoArm] at h
  | (aTag, armNames, armBody) :: rest, b, h => by
    simp only [checkFoArm] at h
    cases heq : (aTag == cTag) with
    | true =>
      simp only [heq, ↓reduceIte] at h
      cases hnm : (armNames == cNames) with
      | false => simp [hnm] at h
      | true =>
        simp only [hnm, ↓reduceIte] at h
        exact (checkFoCode_bound_lt tags armBody armEnv jpSigs b h).1
    | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      exact checkFoArm_bound_lt tags armEnv jpSigs cTag cNames rest b h
termination_by structural arms => arms
end

/-! ## 3. Path-Sensitive Clock Synthesis (`synthLcnfClk`), Fuel Bound (`minLcnfFuel`) & Emitter -/

mutual
/-- Path-sensitive `CondSClk` fuel bound synthesized for an `LcnfCode` block. -/
@[expose] def synthLcnfClk : LcnfCode → Nat
  | .return _               => 0
  | .unreach                => 0
  | .jmp _ _                => 1
  | .letValue _ body        => synthLcnfClk body
  | .ifBool _ t f           => max (synthLcnfClk t) (synthLcnfClk f)
  | .cases _ arms           => synthArmsClk arms
  | .jpDecl _ _ jpBody body => synthLcnfClk body + synthLcnfClk jpBody
termination_by structural c => c

def synthArmsClk : List (String × List String × LcnfCode) → Nat
  | [] => 0
  | (_, _, body) :: rest => max (synthLcnfClk body) (synthArmsClk rest)
termination_by structural arms => arms
end

mutual
/-- Guaranteed step-fuel upper bound for `Obend.Lower.LCNF.evalLcnfCodeVal`. -/
@[expose] def minLcnfFuel : LcnfCode → Nat
  | .return _               => 1
  | .unreach                => 1
  | .jmp _ _                => 1
  | .letValue _ body        => 1 + minLcnfFuel body
  | .ifBool _ t f           => 1 + max (minLcnfFuel t) (minLcnfFuel f)
  | .cases _ arms           => 1 + minArmsFuel arms
  | .jpDecl _ _ jpBody body => 1 + minLcnfFuel body + minLcnfFuel jpBody
termination_by structural c => c

def minArmsFuel : List (String × List String × LcnfCode) → Nat
  | [] => 0
  | (_, _, body) :: rest => max (minLcnfFuel body) (minArmsFuel rest)
termination_by structural arms => arms
end

theorem minLcnfFuel_pos : ∀ c : LcnfCode, 1 ≤ minLcnfFuel c
  | .return _ | .unreach | .jmp _ _ => Nat.le_refl 1
  | .letValue _ _ | .ifBool _ _ _ | .cases _ _ | .jpDecl _ _ _ _ => by
    simp only [minLcnfFuel]; omega

/-- Compiled join-point descriptor carrying its fresh `'h'` flag slot and `'a'` parameter slots. -/
structure CompiledJp where
  jpId      : Nat
  numParams : Nat
  hitSlot   : String
  argSlots  : List String
  deriving Repr, Inhabited

def argShape (varSlots : List (String × Shape)) : LcnfArg → Shape
  | .bvar idx => match varSlots[idx]? with | some (_, sh) => sh | none => .One
  | _         => .One

def compileArg (varSlots : List (String × Shape)) : LcnfArg → PExp
  | .bvar idx     => match varSlots[idx]? with | some (nm, _) => .lvar nm | none => .const 0#64
  | .lit n        => .const (BitVec.ofNat 64 n)
  | .boolLit b    => .const (if b then 1#64 else 0#64)
  | .erased       => .const 0#64
  | .stateTok tid => .const (BitVec.ofNat 64 tid)

def compileFastNatOp (op : NatOp) (e1 e2 : PExp) : PExp :=
  match op with
  | .add => .binop .Add [e1, e2]
  | .mul => .panop .Mul [e1, e2]
  | .beq => .cmp .Equal e1 e2
  | .ble => .cmp .NotLower e2 e1
  | _    => .const 0#64

def wrapDecZeros : List String → PStmt → PStmt
  | [], inner => inner
  | s :: ss, inner => .dec s .One (.const 0#64) (wrapDecZeros ss inner)
termination_by structural ss => ss

def assignJpArgs (varSlots : List (String × Shape)) : List String → List LcnfArg → PStmt
  | [], [] => .skip
  | dst :: dsts, a :: as =>
    .seq (.lassign dst (compileArg varSlots a)) (assignJpArgs varSlots dsts as)
  | _, _ => .skip
termination_by structural dsts => dsts

def bindJpParams : List String → List String → PStmt → PStmt
  | [], [], inner => inner
  | p :: ps, a :: as, inner => .dec p .One (.lvar a) (bindJpParams ps as inner)
  | _, _, inner => inner
termination_by structural ps => ps

def bindCtorFields (eScrut : PExp) (fieldIdx : Nat) : List String → PStmt → PStmt
  | [], inner => inner
  | fSlot :: fSlots, inner =>
    .dec fSlot .One (.rfield fieldIdx eScrut) (bindCtorFields eScrut (fieldIdx + 1) fSlots inner)
termination_by structural fSlots => fSlots

def mkFreshSlots (kind : Char) (start : Nat) : Nat → List String
  | 0 => []
  | k + 1 => mkSlot kind start :: mkFreshSlots kind (start + 1) k
termination_by structural k => k

theorem mkFreshSlots_length (kind : Char) : ∀ (start k : Nat), (mkFreshSlots kind start k).length = k
  | _, 0 => by exact Eq.trans rfl rfl
  | start, k + 1 => by simp [mkFreshSlots, mkFreshSlots_length kind (start + 1) k]

theorem mem_mkFreshSlots {kind : Char} {x : String} :
    ∀ {start k : Nat}, x ∈ mkFreshSlots kind start k → ∃ j, start ≤ j ∧ j < start + k ∧ x = mkSlot kind j
  | _, 0, h => by cases h
  | start, k + 1, h => by
    simp only [mkFreshSlots, List.mem_cons] at h
    rcases h with rfl | htl
    · exact ⟨start, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots htl
      exact ⟨j, by omega, by omega, rfl⟩

mutual
/-- Syntax-directed lowering of `Obend.Lower.LCNF.LcnfCode` to `PanSem.PStmt`, threading a
    strictly monotone slot counter `nextId` so every `Dec` binder is globally fresh. -/
def compileCode (tags : List String) (varSlots : List (String × Shape))
    (jpSlots : List CompiledJp) (nextId : Nat) : LcnfCode → PStmt × Nat
  | .return a => (.ret (compileArg varSlots a), nextId)
  | .unreach  => (.skip, nextId)
  | .jmp id args =>
    match jpSlots.find? (fun cj => cj.jpId == id) with
    | some cj =>
      let assigns := assignJpArgs varSlots cj.argSlots args
      (.seq assigns (.seq (.lassign cj.hitSlot (.const 1#64)) .tick), nextId)
    | none => (.tick, nextId)
  | .letValue (.arg a) body =>
    let sh := argShape varSlots a
    let vSlot := mkSlot 'v' nextId
    let (cBody, nextId') := compileCode tags ((vSlot, sh) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot sh (compileArg varSlots a) cBody, nextId')
  | .letValue (.natOp .sub l r) body =>
    let vSlot := mkSlot 'v' nextId
    let eL := compileArg varSlots l
    let eR := compileArg varSlots r
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    let satSub := .ite (.cmp .Lower eL eR) .skip (.lassign vSlot (.binop .Sub [eL, eR]))
    (.dec vSlot .One (.const 0#64) (.seq satSub cBody), nextId')
  | .letValue (.natOp op l r) body =>
    let vSlot := mkSlot 'v' nextId
    let eOp := compileFastNatOp op (compileArg varSlots l) (compileArg varSlots r)
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot .One eOp cBody, nextId')
  | .letValue (.ctor tag fields) body =>
    let tIdx := (lookupTagIdx tags tag).getD 0
    let sh := Shape.Comb (List.replicate (fields.length + 1) .One)
    let vSlot := mkSlot 'v' nextId
    let eCtor := PExp.rstruct (.const (BitVec.ofNat 64 tIdx) :: fields.map (fun f => compileArg varSlots f.2))
    let (cBody, nextId') := compileCode tags ((vSlot, sh) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot sh eCtor cBody, nextId')
  | .letValue _ body =>
    let vSlot := mkSlot 'v' nextId
    let (cBody, nextId') := compileCode tags ((vSlot, .One) :: varSlots) jpSlots (nextId + 1) body
    (.dec vSlot .One (.const 0#64) cBody, nextId')
  | .ifBool cond t f =>
    let (cT, id1) := compileCode tags varSlots jpSlots nextId t
    let (cF, id2) := compileCode tags varSlots jpSlots id1 f
    (.ite (compileArg varSlots cond) cT cF, id2)
  | .cases scrut arms =>
    compileArms tags (compileArg varSlots scrut) varSlots jpSlots nextId arms
  | .jpDecl jpId numParams jpBody body =>
    let hitSlot := mkSlot 'h' nextId
    let argSlots := mkFreshSlots 'a' (nextId + 1) numParams
    let nextId1 := nextId + 1 + numParams
    let cj : CompiledJp := ⟨jpId, numParams, hitSlot, argSlots⟩
    let (cBody, nextId2) := compileCode tags varSlots (cj :: jpSlots) nextId1 body
    let pSlots := mkFreshSlots 'v' nextId2 numParams
    let jpVarSlots := (pSlots.map (fun s => (s, Shape.One))) ++ varSlots
    let (cJpBody, nextId3) := compileCode tags jpVarSlots jpSlots (nextId2 + numParams) jpBody
    let tailIf := PStmt.ite (.lvar hitSlot) (bindJpParams pSlots argSlots cJpBody) .skip
    (.dec hitSlot .One (.const 0#64) (wrapDecZeros argSlots (.seq cBody tailIf)), nextId3)
termination_by structural c => c

def compileArms (tags : List String) (eScrut : PExp) (varSlots : List (String × Shape))
    (jpSlots : List CompiledJp) (nextId : Nat) :
    List (String × List String × LcnfCode) → PStmt × Nat
  | [] => (.skip, nextId)
  | (armTag, fieldNames, armBody) :: rest =>
    let k := fieldNames.length
    let fSlots := mkFreshSlots 'v' nextId k
    let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
    let (cArm, id1) := compileCode tags armVarSlots jpSlots (nextId + k) armBody
    let (cRest, id2) := compileArms tags eScrut varSlots jpSlots id1 rest
    let tIdx := (lookupTagIdx tags armTag).getD 0
    let guard := PExp.cmp .Equal (.rfield 0 eScrut) (.const (BitVec.ofNat 64 tIdx))
    (.ite guard (bindCtorFields eScrut 1 fSlots cArm) cRest, id2)
termination_by structural arms => arms
end

/-- **Top-Level Verified `LcnfCode → PStmt` Compiler (`compileLcnfToPancake`)**. -/
@[expose] def compileLcnfToPancake (c : LcnfCode) : PStmt :=
  (compileCode (collectTags c) [] [] 0 c).1


/-! ### 3.1 Decidable Join-Free `PureBlock` Bridge for `compileLcnfToCore4` Agreement -/

mutual
/-- Decidable syntactic check for the join-free `Obend.Lower.LCNF.PureBlock` fragment. -/
@[expose] def isJoinFreePureBlock : LcnfCode → Bool
  | .return _        => true
  | .unreach         => true
  | .letValue v body => isPureLetValue v && isJoinFreePureBlock body
  | .ifBool _ t f    => isJoinFreePureBlock t && isJoinFreePureBlock f
  | .cases _ arms    => isJoinFreePureArms arms
  | .jpDecl _ _ _ _  => false
  | .jmp _ _         => false
termination_by structural c => c

def isJoinFreePureArms : List (String × List String × LcnfCode) → Bool
  | [] => true
  | (_, _, body) :: rest => isJoinFreePureBlock body && isJoinFreePureArms rest
termination_by structural arms => arms
end

theorem isJoinFreePureBlock_inhabited : ∃ c : LcnfCode, isJoinFreePureBlock c = true :=
  ⟨.return (.lit 0), by exact Eq.trans rfl rfl⟩

theorem isJoinFreePureArms_inhabited :
    ∃ arms : List (String × List String × LcnfCode), isJoinFreePureArms arms = true :=
  ⟨[("k", [], .return (.lit 0))], by exact Eq.trans rfl rfl⟩

theorem checkFoLcnf_inhabited : ∃ (c : LcnfCode) (b : Nat), checkFoLcnf c = some b :=
  ⟨.return (.lit 0), 0, by exact Eq.trans rfl rfl⟩

mutual
theorem isJoinFreePureBlock_sound :
    (c : LcnfCode) → isJoinFreePureBlock c = true → PureBlock c
  | .return a => fun _ => .ret a
  | .unreach => fun _ => .unreach
  | .letValue v body => fun h => by
    simp only [isJoinFreePureBlock, Bool.and_eq_true] at h
    exact .letValue h.1 (isJoinFreePureBlock_sound body h.2)
  | .ifBool _ t f => fun h => by
    simp only [isJoinFreePureBlock, Bool.and_eq_true] at h
    exact .ifBool (isJoinFreePureBlock_sound t h.1) (isJoinFreePureBlock_sound f h.2)
  | .cases _ arms => fun h => by
    simp only [isJoinFreePureBlock] at h
    exact .cases (isJoinFreePureArms_sound arms h)
  | .jpDecl _ _ _ _ => fun h => by simp [isJoinFreePureBlock] at h
  | .jmp _ _ => fun h => by simp [isJoinFreePureBlock] at h
termination_by structural c => c

theorem isJoinFreePureArms_sound :
    (arms : List (String × List String × LcnfCode)) →
    isJoinFreePureArms arms = true →
    ∀ arm ∈ arms, PureBlock arm.2.2
  | [] => fun _ _ hm => by cases hm
  | (_, _, body) :: rest => fun h arm hm => by
    simp only [isJoinFreePureArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | htl
    · exact isJoinFreePureBlock_sound body h.1
    · exact isJoinFreePureArms_sound rest h.2 arm htl
termination_by structural arms => arms
end

/-! ## 5. Compositional Block Semantics (`evalFoBlock`) & Equivalence with `evalLcnfCodeVal` -/

/-- Intra-block LCNF outcome before enclosing `jpDecl` handlers catch outgoing tail jumps. -/
inductive FoOutcome where
  | returned (v : LcnfVal)
  | jumped   (jpId : Nat) (args : List LcnfVal)

def evalFoLetVal (env : List LcnfVal) : LcnfLetValue → Option LcnfVal
  | .arg a => evalLcnfArgVal env a
  | .natOp op l r =>
    match evalLcnfArgVal env l, evalLcnfArgVal env r with
    | some (.scalar lv), some (.scalar rv) =>
      match op with
      | .add => some (.scalar (lv + rv))
      | .sub => some (.scalar (lv - rv))
      | .mul => some (.scalar (lv * rv))
      | .div => some (.scalar (lv / rv))
      | .mod => some (.scalar (lv % rv))
      | .beq => some (.bool (lv == rv))
      | .ble => some (.bool (lv <= rv))
    | _, _ => none
  | .ctor tag fs =>
    (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)).map (.ctor tag)
  | _ => none

mutual
/-- Fuel-free structural evaluator for first-order `LcnfCode` blocks. -/
def evalFoBlock (env : List LcnfVal) : LcnfCode → Option FoOutcome
  | .return a => (evalLcnfArgVal env a).map .returned
  | .unreach  => none
  | .jmp id args => (args.mapM (evalLcnfArgVal env)).map (.jumped id)
  | .letValue v body =>
    match evalFoLetVal env v with
    | some val => evalFoBlock (val :: env) body
    | none => none
  | .ifBool cond t f =>
    match evalLcnfArgVal env cond with
    | some (.bool b) => if b then evalFoBlock env t else evalFoBlock env f
    | _ => none
  | .cases scrut arms =>
    match evalLcnfArgVal env scrut with
    | some (.ctor tag fs) => evalFoArm env tag fs arms
    | _ => none
  | .jpDecl jpId numParams jpBody body =>
    match evalFoBlock env body with
    | none => none
    | some (.returned v) => some (.returned v)
    | some (.jumped tid argVals) =>
      if tid == jpId then
        if argVals.length == numParams then
          evalFoBlock (argVals ++ env) jpBody
        else
          none
      else
        some (.jumped tid argVals)
termination_by structural c => c

def evalFoArm (env : List LcnfVal) (tag : String) (fs : List (String × LcnfVal)) :
    List (String × List String × LcnfCode) → Option FoOutcome
  | [] => none
  | (armTag, names, body) :: rest =>
    if armTag == tag then
      match splitValues fs names with
      | some vals => evalFoBlock (vals.reverse ++ env) body
      | none => none
    else
      evalFoArm env tag fs rest
termination_by structural arms => arms
end

theorem evalFoArm_eq_find (env : List LcnfVal) (tag : String) (fs : List (String × LcnfVal)) :
    ∀ arms, evalFoArm env tag fs arms =
      match arms.find? (fun (armTag, _, _) => armTag == tag) with
      | some (_, names, body) =>
        match splitValues fs names with
        | some vals => evalFoBlock (vals.reverse ++ env) body
        | none => none
      | none => none
  | [] => by exact Eq.trans rfl rfl
  | (armTag, names, body) :: rest => by
    cases h : (armTag == tag) <;> simp only [evalFoArm, List.find?, h, ↓reduceIte, Bool.false_eq_true, evalFoArm_eq_find] <;> cases splitValues fs names <;> rfl

/-- Dispatch an `FoOutcome` through a well-nested stack of `LcnfJpClosure` frames. -/
def applyJps : List LcnfJpClosure → FoOutcome → Option LcnfVal
  | _, .returned v => some v
  | [], .jumped _ _ => none
  | jp :: rest, .jumped tid args =>
    if jp.jpId == tid then
      if args.length == jp.numParams then
        match evalFoBlock (args ++ jp.declEnv) jp.jpBody with
        | some out => applyJps rest out
        | none => none
      else
        none
    else
      applyJps rest (.jumped tid args)
termination_by structural jps => jps

def jpsFuel : List LcnfJpClosure → Nat
  | [] => 0
  | jp :: rest => minLcnfFuel jp.jpBody + jpsFuel rest
termination_by structural jps => jps

@[simp] theorem applyJps_returned (jps : List LcnfJpClosure) (v : LcnfVal) :
    applyJps jps (.returned v) = some v := by
  cases jps <;> rfl

/-- Predicate characterizing lexical join-closure stacks built by `evalLcnfCodeVal`. -/
inductive SavedDepthWF : List LcnfJpClosure → Prop where
  | nil : SavedDepthWF []
  | cons {jp : LcnfJpClosure} {rest : List LcnfJpClosure} :
      jp.savedJpsDepth = rest.length →
      foPureCode jp.jpBody = true →
      SavedDepthWF rest →
      SavedDepthWF (jp :: rest)

private theorem option_mapM_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x <;> simp [hx] at h
    cases hxs : xs.mapM f <;> simp [hxs] at h
    subst h
    simp [option_mapM_length f xs _ hxs]

private theorem foPureArms_mem :
    ∀ {arms : List (String × List String × LcnfCode)} {atag : String}
      {anms : List String} {abody : LcnfCode},
      foPureArms arms = true →
      (atag, anms, abody) ∈ arms →
      foPureCode abody = true ∧ minLcnfFuel abody ≤ minArmsFuel arms
  | [], _, _, _, _, hm => by cases hm
  | (_, _, _) :: rest, _, _, _, hp, hm => by
    simp only [foPureArms, minArmsFuel, Bool.and_eq_true] at hp ⊢
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq; exact ⟨hp.1, by omega⟩
    · obtain ⟨h1, h2⟩ := foPureArms_mem hp.2 htl
      exact ⟨h1, by omega⟩

private theorem evalFoLetVal_iff {fuel : Nat} (hpos : 1 ≤ fuel)
    {env : List LcnfVal} {jps : List LcnfJpClosure} {st : List (Nat × Nat)}
    {v : LcnfLetValue} (hp : foPureLetVal v = true) :
    ∀ {val : LcnfVal} {st' : List (Nat × Nat)},
      (evalLcnfLetValueVal fuel env jps st v = some (val, st') ↔
        st' = st ∧ evalFoLetVal env v = some val) := by
  intro val st'
  cases fuel with
  | zero => omega
  | succ _ =>
    cases v with
    | arg a =>
      simp only [evalLcnfLetValueVal, evalFoLetVal]
      cases evalLcnfArgVal env a <;> simp [and_comm, eq_comm]
    | natOp op l r =>
      simp only [evalLcnfLetValueVal, evalFoLetVal, Bind.bind, Option.bind, pure]
      cases hl : evalLcnfArgVal env l with
      | none => simp
      | some vl =>
        cases vl <;> try simp
        cases hr : evalLcnfArgVal env r with
        | none => simp
        | some vr =>
          cases vr <;> try simp
          cases op <;> simp [and_comm, eq_comm]
    | ctor tag fs =>
      simp only [evalLcnfLetValueVal, evalFoLetVal]
      have hmapEq : (fs.mapM fun (name, a) => do return (name, ← evalLcnfArgVal env a)) =
          (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) := rfl
      rw [hmapEq]
      cases (fs.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) <;>
        simp [and_comm, eq_comm]
    | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
      simp [foPureLetVal] at hp

private theorem savedDepth_le_of_find {jps : List LcnfJpClosure}
    (hwf : SavedDepthWF jps) :
    ∀ {id : Nat} {jp : LcnfJpClosure},
      jps.find? (fun e => e.jpId == id) = some jp →
      jp.savedJpsDepth ≤ jps.length := by
  induction hwf with
  | nil => intro _ _ h; simp at h
  | @cons hd rest hdepth _ _ ih =>
    intro id jp h
    simp only [List.find?] at h
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, Option.some.injEq] at h
      subst h
      simp [hdepth]
    | false =>
      simp only [heq] at h
      have h1 := ih h
      simp; omega

private theorem applyJps_find {jps : List LcnfJpClosure}
    (hwf : SavedDepthWF jps) {id : Nat} {jp : LcnfJpClosure}
    (hfind : jps.find? (fun e => e.jpId == id) = some jp) :
    foPureCode jp.jpBody = true ∧
    SavedDepthWF (jps.drop (jps.length - jp.savedJpsDepth)) ∧
    minLcnfFuel jp.jpBody + jpsFuel (jps.drop (jps.length - jp.savedJpsDepth)) ≤ jpsFuel jps ∧
    ∀ (vals : List LcnfVal),
      vals.length = jp.numParams →
      applyJps jps (.jumped id vals) =
        match evalFoBlock (vals ++ jp.declEnv) jp.jpBody with
        | some out => applyJps (jps.drop (jps.length - jp.savedJpsDepth)) out
        | none => none := by
  induction hwf with
  | nil => simp at hfind
  | @cons hd rest hdepth hbody hrest ih =>
    simp only [List.find?] at hfind
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, Option.some.injEq] at hfind
      subst hfind
      have hsub1 : (hd :: rest).length - hd.savedJpsDepth = 1 := by simp [hdepth]
      have hdrop : (hd :: rest).drop ((hd :: rest).length - hd.savedJpsDepth) = rest := by
        rw [hsub1]; rfl
      refine ⟨hbody, hdrop.symm ▸ hrest, ?_, fun vals hlen => ?_⟩
      · rw [hdrop]; simp [jpsFuel]
      · rw [hdrop]; simp [applyJps, heq, hlen]
    | false =>
      simp only [heq] at hfind
      obtain ⟨hb, hrd, hfuel, hfn⟩ := ih hfind
      have hle : jp.savedJpsDepth ≤ rest.length := savedDepth_le_of_find hrest hfind
      have hdropEq : (hd :: rest).drop ((hd :: rest).length - jp.savedJpsDepth) =
          rest.drop (rest.length - jp.savedJpsDepth) := by
        have hsub : (rest.length + 1) - jp.savedJpsDepth = (rest.length - jp.savedJpsDepth) + 1 := by
          omega
        simp only [List.length_cons, hsub, List.drop_succ_cons]
      refine ⟨hb, hdropEq.symm ▸ hrd, ?_, fun vals hlen => ?_⟩
      · rw [hdropEq]; simp only [jpsFuel]; omega
      · simp only [applyJps, heq, Bool.false_eq_true, ↓reduceIte]
        rw [hfn vals hlen, hdropEq]

private theorem applyJps_jumped_some {jps : List LcnfJpClosure} (hwf : SavedDepthWF jps)
    {id : Nat} {vals : List LcnfVal} {v : LcnfVal}
    (happ : applyJps jps (.jumped id vals) = some v) :
    ∃ jp outJ,
      jps.find? (fun e => e.jpId == id) = some jp ∧
      vals.length = jp.numParams ∧
      evalFoBlock (vals ++ jp.declEnv) jp.jpBody = some outJ ∧
      applyJps (jps.drop (jps.length - jp.savedJpsDepth)) outJ = some v := by
  induction hwf with
  | nil => simp [applyJps] at happ
  | @cons hd rest hdepth _ hrest ih =>
    simp only [applyJps] at happ
    cases heq : (hd.jpId == id) with
    | true =>
      simp only [heq, ↓reduceIte] at happ
      cases hlen : (vals.length == hd.numParams) with
      | false => simp [hlen] at happ
      | true =>
        simp only [hlen, ↓reduceIte] at happ
        cases hout : evalFoBlock (vals ++ hd.declEnv) hd.jpBody with
        | none => simp [hout] at happ
        | some outJ =>
          rw [hout] at happ
          have hsub1 : (hd :: rest).length - hd.savedJpsDepth = 1 := by simp [hdepth]
          have hdrop : (hd :: rest).drop ((hd :: rest).length - hd.savedJpsDepth) = rest := by
            rw [hsub1]; rfl
          exact ⟨hd, outJ, by simp [List.find?, heq], beq_iff_eq.mp hlen, hout, hdrop.symm ▸ happ⟩
    | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at happ
      obtain ⟨jp, outJ, hf, hl, hout, happ'⟩ := ih happ
      have hle : jp.savedJpsDepth ≤ rest.length := savedDepth_le_of_find hrest hf
      have hdropEq : (hd :: rest).drop ((hd :: rest).length - jp.savedJpsDepth) =
          rest.drop (rest.length - jp.savedJpsDepth) := by
        have hsub : (rest.length + 1) - jp.savedJpsDepth = (rest.length - jp.savedJpsDepth) + 1 := by
          omega
        simp only [List.length_cons, hsub, List.drop_succ_cons]
      exact ⟨jp, outJ, by simp [List.find?, heq, hf], hl, hout, hdropEq.symm ▸ happ'⟩

/-- Forward equivalence: any `evalLcnfCodeVal` success on `foPureCode` agrees with `evalFoBlock` + `applyJps`. -/
private theorem evalLcnfCodeVal_eq_applyJps :
    ∀ (fuel : Nat) (c : LcnfCode) (env : List LcnfVal) (jps : List LcnfJpClosure)
      (st st' : List (Nat × Nat)) (v : LcnfVal),
      foPureCode c = true →
      SavedDepthWF jps →
      evalLcnfCodeVal fuel env jps st c = some (v, st') →
      st' = st ∧ ∃ out, evalFoBlock env c = some out ∧ applyJps jps out = some v := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [evalLcnfCodeVal] at h
  | succ f ih =>
    intro c env jps st st' v hp hjps hev
    cases c with
    | «return» a =>
      simp only [evalLcnfCodeVal, Bind.bind, Option.bind, pure] at hev
      cases ha : evalLcnfArgVal env a with
      | none => simp [ha] at hev
      | some valA =>
        simp only [ha, Option.some.injEq, Prod.mk.injEq] at hev
        rcases hev with ⟨rfl, rfl⟩
        exact ⟨rfl, .returned valA, by simp [evalFoBlock, ha], applyJps_returned jps valA⟩
    | unreach => simp [evalLcnfCodeVal] at hev
    | letValue lv body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hlv : evalLcnfLetValueVal f env jps st lv with
      | none => simp [hlv] at hev
      | some p =>
        obtain ⟨val, stMid⟩ := p
        have hfpos : 1 ≤ f := by
          cases f with
          | zero => simp [evalLcnfLetValueVal] at hlv
          | succ _ => omega
        obtain ⟨hstMid, hfoLv⟩ := (evalFoLetVal_iff hfpos hp.1).mp hlv
        subst stMid
        simp only [hlv, Bind.bind, Option.bind] at hev
        obtain ⟨hst, out, hfoB, happ⟩ := ih body (val :: env) jps st st' v hp.2 hjps hev
        exact ⟨hst, out, by simp [evalFoBlock, hfoLv, hfoB], happ⟩
    | ifBool cond t fls =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hc : evalLcnfArgVal env cond with
      | none => simp [hc] at hev
      | some cv =>
        cases cv <;> simp [hc] at hev
        rename_i bv
        cases bv with
        | true =>
          obtain ⟨hst, out, hfo, happ⟩ := ih t env jps st st' v hp.1 hjps hev
          exact ⟨hst, out, by simp [evalFoBlock, hc, hfo], happ⟩
        | false =>
          obtain ⟨hst, out, hfo, happ⟩ := ih fls env jps st st' v hp.2 hjps hev
          exact ⟨hst, out, by simp [evalFoBlock, hc, hfo], happ⟩
    | cases scrut arms =>
      simp only [foPureCode] at hp
      simp only [evalLcnfCodeVal] at hev
      cases hs : evalLcnfArgVal env scrut with
      | none => simp [hs] at hev
      | some sv =>
        cases sv <;> simp [hs] at hev
        rename_i tag fs
        cases hf : arms.find? (fun (armTag, _, _) => armTag == tag) with
        | none => simp [hf] at hev
        | some arm =>
          obtain ⟨atag, names, armBody⟩ := arm
          cases hsp : splitValues fs names with
          | none => simp [hf, hsp] at hev
          | some vals =>
            simp only [hf, hsp, Option.bind_some] at hev
            have hpArm := (foPureArms_mem hp (List.mem_of_find?_eq_some hf)).1
            obtain ⟨hst, out, hfo, happ⟩ := ih armBody (vals.reverse ++ env) jps st st' v hpArm hjps hev
            exact ⟨hst, out, by simp [evalFoBlock, hs, evalFoArm_eq_find, hf, hsp, hfo], happ⟩
    | jpDecl id n jpBody body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalLcnfCodeVal] at hev
      have hjps' : SavedDepthWF (⟨id, n, env, jps.length, jpBody⟩ :: jps) :=
        .cons rfl hp.1 hjps
      obtain ⟨hst, outB, hfoB, happB⟩ := ih body env _ st st' v hp.2 hjps' hev
      refine ⟨hst, ?_⟩
      cases outB with
      | returned rv =>
        simp only [applyJps_returned] at happB
        exact ⟨.returned rv, by simp [evalFoBlock, hfoB], by simpa using happB⟩
      | jumped tid argVals =>
        simp only [applyJps] at happB
        have hcomm : (id == tid) = (tid == id) := by
          cases h1 : (id == tid) <;> cases h2 : (tid == id) <;> simp_all [beq_iff_eq]
        rw [hcomm] at happB
        cases htid : (tid == id) with
        | true =>
          simp only [htid, ↓reduceIte] at happB
          cases hlen : (argVals.length == n) with
          | false => simp [hlen] at happB
          | true =>
            simp only [hlen, ↓reduceIte] at happB
            cases houtJ : evalFoBlock (argVals ++ env) jpBody with
            | none => simp [houtJ] at happB
            | some outJ =>
              rw [houtJ] at happB
              exact ⟨outJ, by simp [evalFoBlock, hfoB, htid, hlen, houtJ], happB⟩
        | false =>
          simp only [htid, Bool.false_eq_true, ↓reduceIte] at happB
          exact ⟨.jumped tid argVals, by simp [evalFoBlock, hfoB, htid], happB⟩
    | jmp id args =>
      simp only [evalLcnfCodeVal] at hev
      cases hfind : jps.find? (fun entry => entry.jpId == id) with
      | none => simp [hfind] at hev
      | some jp =>
        rw [hfind] at hev
        dsimp only [Bind.bind, Option.bind] at hev
        cases hne : (args.length != jp.numParams) with
        | true => simp [hne] at hev
        | false =>
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at hev
          cases hvals : args.mapM (evalLcnfArgVal env) with
          | none => simp [hvals] at hev
          | some vals =>
            rw [hvals] at hev
            dsimp only [Bind.bind, Option.bind] at hev
            obtain ⟨hpBody, hjpsDrop, _, hfn⟩ := applyJps_find hjps hfind
            have hlenEq : vals.length = jp.numParams := by
              have h1 := option_mapM_length (evalLcnfArgVal env) args vals hvals
              have h2 : args.length = jp.numParams := by simpa [bne_eq_false_iff_eq] using hne
              omega
            obtain ⟨hst, outJ, hfoJ, happJ⟩ :=
              ih jp.jpBody (vals ++ jp.declEnv) _ st st' v hpBody hjpsDrop hev
            refine ⟨hst, .jumped id vals, by simp [evalFoBlock, hvals], ?_⟩
            rw [hfn vals hlenEq, hfoJ]
            exact happJ

/-- Converse fuel adequacy: `evalFoBlock` + `applyJps` implies `evalLcnfCodeVal` succeeds for all `fuel ≥ minLcnfFuel c + jpsFuel jps`. -/
theorem evalFoBlock_implies_evalLcnfCodeVal :
    ∀ (fuel : Nat) (c : LcnfCode) (env : List LcnfVal) (jps : List LcnfJpClosure)
      (st : List (Nat × Nat)) (out : FoOutcome) (v : LcnfVal),
      foPureCode c = true →
      SavedDepthWF jps →
      evalFoBlock env c = some out →
      applyJps jps out = some v →
      minLcnfFuel c + jpsFuel jps ≤ fuel →
      evalLcnfCodeVal fuel env jps st c = some (v, st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c _ _ _ _ _ _ _ _ _ hle
    have := minLcnfFuel_pos c
    omega
  | succ f ih =>
    intro c env jps st out v hp hjps hfo happ hfuel
    cases c with
    | «return» a =>
      simp only [evalFoBlock] at hfo
      cases ha : evalLcnfArgVal env a <;> simp [ha] at hfo
      subst hfo
      simp only [applyJps_returned, Option.some.injEq] at happ
      subst happ
      simp [evalLcnfCodeVal, ha]
    | unreach => simp [evalFoBlock] at hfo
    | letValue lv body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases hlv : evalFoLetVal env lv with
      | none => simp [hlv] at hfo
      | some val =>
        rw [hlv] at hfo
        simp only [minLcnfFuel] at hfuel
        have hbpos := minLcnfFuel_pos body
        have hfpos : 1 ≤ f := by omega
        have hevLv : evalLcnfLetValueVal f env jps st lv = some (val, st) :=
          (evalFoLetVal_iff hfpos hp.1).mpr ⟨rfl, hlv⟩
        simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hevLv]
        exact ih body (val :: env) jps st out v hp.2 hjps hfo happ (by omega)
    | ifBool cond t fls =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases hc : evalLcnfArgVal env cond with
      | none => simp [hc] at hfo
      | some cv =>
        cases cv <;> simp [hc] at hfo
        rename_i bv
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hc]
        cases bv with
        | true =>
          simp only [↓reduceIte] at hfo ⊢
          exact ih t env jps st out v hp.1 hjps hfo happ (by omega)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hfo ⊢
          exact ih fls env jps st out v hp.2 hjps hfo happ (by omega)
    | cases scrut arms =>
      simp only [foPureCode] at hp
      simp only [evalFoBlock] at hfo
      cases hs : evalLcnfArgVal env scrut with
      | none => simp [hs] at hfo
      | some sv =>
        cases sv <;> simp [hs] at hfo
        rename_i tag fs
        rw [evalFoArm_eq_find] at hfo
        cases hf : arms.find? (fun (armTag, _, _) => armTag == tag) with
        | none => simp [hf] at hfo
        | some arm =>
          obtain ⟨atag, names, armBody⟩ := arm
          rw [hf] at hfo
          dsimp only at hfo
          cases hsp : splitValues fs names with
          | none => simp [hsp] at hfo
          | some vals =>
            rw [hsp] at hfo
            obtain ⟨hpArm, hfuelArm⟩ := foPureArms_mem hp (List.mem_of_find?_eq_some hf)
            simp only [minLcnfFuel] at hfuel
            simp only [evalLcnfCodeVal, Bind.bind, Option.bind, hs, hf, hsp]
            exact ih armBody (vals.reverse ++ env) jps st out v hpArm hjps hfo happ (by omega)
    | jpDecl id n jpBody body =>
      simp only [foPureCode, Bool.and_eq_true] at hp
      simp only [evalFoBlock] at hfo
      cases houtB : evalFoBlock env body with
      | none => simp [houtB] at hfo
      | some outB =>
        rw [houtB] at hfo
        let jpNew : LcnfJpClosure := ⟨id, n, env, jps.length, jpBody⟩
        have hjps' : SavedDepthWF (jpNew :: jps) := .cons rfl hp.1 hjps
        have happB : applyJps (jpNew :: jps) outB = some v := by
          cases outB with
          | returned rv =>
            dsimp only at hfo
            injection hfo with hEq; subst hEq
            simpa using happ
          | jumped tid argVals =>
            dsimp only at hfo
            have hcomm : (id == tid) = (tid == id) := by
              cases h1 : (id == tid) <;> cases h2 : (tid == id) <;> simp_all [beq_iff_eq]
            simp only [applyJps, jpNew, hcomm]
            cases htid : (tid == id) with
            | true =>
              simp only [htid, ↓reduceIte] at hfo ⊢
              cases hlen : (argVals.length == n) with
              | false => simp [hlen] at hfo
              | true =>
                simp only [hlen, ↓reduceIte] at hfo ⊢
                rw [hfo]; exact happ
            | false =>
              simp only [htid, Bool.false_eq_true, ↓reduceIte] at hfo ⊢
              injection hfo with hEq; subst hEq
              exact happ
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal]
        exact ih body env (jpNew :: jps) st outB v hp.2 hjps' houtB happB
          (by simp only [jpsFuel, jpNew]; omega)
    | jmp id args =>
      simp only [evalFoBlock] at hfo
      cases hvals : args.mapM (evalLcnfArgVal env) with
      | none => simp [hvals] at hfo
      | some vals =>
        rw [hvals] at hfo
        simp only [Option.map_some, Option.some.injEq] at hfo
        subst hfo
        obtain ⟨jp, outJ, hfind, hlenV, houtJ, happJ⟩ := applyJps_jumped_some hjps happ
        obtain ⟨hpBody, hjpsDrop, hfuelDrop, _⟩ := applyJps_find hjps hfind
        have hlenArgs : args.length = jp.numParams :=
          (option_mapM_length (evalLcnfArgVal env) args vals hvals).trans hlenV
        have hneFalse : (args.length != jp.numParams) = false := by
          simp [hlenArgs]
        simp only [minLcnfFuel] at hfuel
        simp only [evalLcnfCodeVal, hfind, Bind.bind, Option.bind, hneFalse, Bool.false_eq_true, ↓reduceIte, hvals]
        exact ih jp.jpBody (vals ++ jp.declEnv) _ st outJ v hpBody hjpsDrop houtJ happJ (by omega)


end Obend.Lower.Pancake
end
