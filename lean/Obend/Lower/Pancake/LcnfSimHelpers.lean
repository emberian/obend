module
/-
# `Obend.Lower.Pancake.LcnfSimHelpers` — Clock-Synthesis Agreement & Frame Simulation Lemmas (`G6`)

Proves `compileCode_clk_and_mono` (`synthStmtClk` agreement + slot-counter monotonicity),
64-bit `BitVec` non-wrapping arithmetic lemmas, constructor field representation `CtorFieldsRel`,
join-point stack invariants (`JpStackWF`, `JpsIdle`, `JpTriggered`), and local-frame setup/teardown
lemmas (`evaluate_wrapDecZeros`, `evaluate_assignJpArgs`, `evaluate_jmp_stack`,
`evaluate_bindJpParams_raw`, `evaluate_bindCtorFields`) consumed by `Obend.Lower.Pancake`.
-/
public import Obend.Lower.Pancake.LcnfEmit
import all Obend.Core.Term
import all Obend.Lower.LCNF
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.CondSClk
import all Obend.Lower.Pancake.LcnfEmit

public section

namespace Obend.Lower.Pancake

open Obend.Core.Term (splitValues)
open Obend.Lower (NatOp)
open Obend.Lower.LCNF

set_option autoImplicit false

/-! ## 4. Exact Agreement with Generic `CondSClk.synthStmtClk` -/

theorem synthStmtClk_wrapDecZeros (ss : List String) (inner : PStmt) :
    synthStmtClk (wrapDecZeros ss inner) = synthStmtClk inner := by
  induction ss with
  | nil => rfl
  | cons _ tl ih => simp [wrapDecZeros, ih]

theorem synthStmtClk_assignJpArgs (vs : List (String × Shape)) :
    ∀ (dsts : List String) (args : List LcnfArg),
      synthStmtClk (assignJpArgs vs dsts args) = some 0
  | [], [] => by exact Eq.trans rfl rfl
  | _ :: dsts, _ :: args => by
    simp [assignJpArgs, synthStmtClk_assignJpArgs vs dsts args]
  | [], _ :: _ => by exact Eq.trans rfl rfl
  | _ :: _, [] => by exact Eq.trans rfl rfl

theorem synthStmtClk_bindJpParams :
    ∀ (ps as : List String) (inner : PStmt),
      synthStmtClk (bindJpParams ps as inner) = synthStmtClk inner
  | [], [], _ => by exact Eq.trans rfl rfl
  | _ :: ps, _ :: as, inner => by simp [bindJpParams, synthStmtClk_bindJpParams ps as inner]
  | [], _ :: _, _ => by exact Eq.trans rfl rfl
  | _ :: _, [], _ => by exact Eq.trans rfl rfl

theorem synthStmtClk_bindCtorFields (e : PExp) :
    ∀ (idx : Nat) (fs : List String) (inner : PStmt),
      synthStmtClk (bindCtorFields e idx fs inner) = synthStmtClk inner
  | _, [], _ => by exact Eq.trans rfl rfl
  | idx, _ :: fs, inner => by simp [bindCtorFields, synthStmtClk_bindCtorFields e (idx + 1) fs inner]

mutual
theorem compileCode_clk_and_mono (tags : List String) :
    (c : LcnfCode) →
    ∀ (varSlots : List (String × Shape)) (jpSlots : List CompiledJp) (nextId : Nat),
      synthStmtClk (compileCode tags varSlots jpSlots nextId c).1 = some (synthLcnfClk c) ∧
      nextId ≤ (compileCode tags varSlots jpSlots nextId c).2
  | .return _, _, _, nextId => by exact ⟨rfl, Nat.le_refl _⟩
  | .unreach,  _, _, nextId => by exact ⟨rfl, Nat.le_refl _⟩
  | .jmp id args, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    cases jpSlots.find? (fun cj => cj.jpId == id) with
    | none => exact ⟨rfl, Nat.le_refl _⟩
    | some cj =>
      refine ⟨?_, Nat.le_refl _⟩
      have ha := synthStmtClk_assignJpArgs varSlots cj.argSlots args
      simp [synthStmtClk, ha]
  | .letValue v body, varSlots, jpSlots, nextId => by
    cases v with
    | arg a =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, argShape varSlots a) :: varSlots) jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
    | natOp op l r =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, .One) :: varSlots) jpSlots (nextId + 1)
      cases op <;>
        exact ⟨by simp [compileCode, synthLcnfClk, synthStmtClk, h.1],
               by simp only [compileCode]; omega⟩
    | ctor tag fields =>
      have h := compileCode_clk_and_mono tags body
        ((mkSlot 'v' nextId, Shape.Comb (List.replicate (fields.length + 1) .One)) :: varSlots)
        jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
    | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
      have h := compileCode_clk_and_mono tags body ((mkSlot 'v' nextId, .One) :: varSlots) jpSlots (nextId + 1)
      exact ⟨by simpa [compileCode, synthLcnfClk] using h.1, by simp only [compileCode]; omega⟩
  | .ifBool cond t f, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    have ht := compileCode_clk_and_mono tags t varSlots jpSlots nextId
    have hf := compileCode_clk_and_mono tags f varSlots jpSlots (compileCode tags varSlots jpSlots nextId t).2
    exact ⟨by simp [synthStmtClk, ht.1, hf.1], Nat.le_trans ht.2 hf.2⟩
  | .cases scrut arms, varSlots, jpSlots, nextId =>
    compileArms_clk_and_mono tags arms (compileArg varSlots scrut) varSlots jpSlots nextId
  | .jpDecl jpId numParams jpBody body, varSlots, jpSlots, nextId => by
    simp only [compileCode, synthLcnfClk]
    have hb := compileCode_clk_and_mono tags body varSlots
      (⟨jpId, numParams, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) numParams⟩ :: jpSlots)
      (nextId + 1 + numParams)
    let nextId2 := (compileCode tags varSlots
      (⟨jpId, numParams, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) numParams⟩ :: jpSlots)
      (nextId + 1 + numParams) body).2
    have hj := compileCode_clk_and_mono tags jpBody
      (((mkFreshSlots 'v' nextId2 numParams).map (fun s => (s, Shape.One))) ++ varSlots)
      jpSlots (nextId2 + numParams)
    dsimp only [nextId2] at hj
    refine ⟨?_, ?_⟩
    · simp only [synthStmtClk, synthStmtClk_wrapDecZeros, synthStmtClk_bindJpParams, hb.1, hj.1, Nat.max_zero]
    · have h1 := hb.2
      have h2 := hj.2
      omega
termination_by structural c => c

theorem compileArms_clk_and_mono (tags : List String) :
    (arms : List (String × List String × LcnfCode)) →
    ∀ (eScrut : PExp) (varSlots : List (String × Shape)) (jpSlots : List CompiledJp) (nextId : Nat),
      synthStmtClk (compileArms tags eScrut varSlots jpSlots nextId arms).1 = some (synthArmsClk arms) ∧
      nextId ≤ (compileArms tags eScrut varSlots jpSlots nextId arms).2
  | [], _, _, _, nextId => by exact ⟨rfl, Nat.le_refl _⟩
  | (armTag, fieldNames, armBody) :: rest, eScrut, varSlots, jpSlots, nextId => by
    simp only [compileArms, synthArmsClk]
    have ha := compileCode_clk_and_mono tags armBody
      (((mkFreshSlots 'v' nextId fieldNames.length).reverse.map (fun s => (s, Shape.One))) ++ varSlots)
      jpSlots (nextId + fieldNames.length)
    have hr := compileArms_clk_and_mono tags rest eScrut varSlots jpSlots
      (compileCode tags
        (((mkFreshSlots 'v' nextId fieldNames.length).reverse.map (fun s => (s, Shape.One))) ++ varSlots)
        jpSlots (nextId + fieldNames.length) armBody).2
    refine ⟨?_, ?_⟩
    · simp only [synthStmtClk, synthStmtClk_bindCtorFields, ha.1, hr.1]
    · have h1 := ha.2
      have h2 := hr.2
      omega
termination_by structural arms => arms
end


/-! ## 6. Compiler Simulation Proof (`compileCode_sound`) -/

theorem bv64_add_ofNat {a b : Nat} (hab : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

theorem bv64_add_right_cancel {u w v : Word} (h : u + v = w + v) : u = w := by
  apply BitVec.eq_of_toNat_eq
  have hu := u.isLt
  have hw := w.isLt
  have hv := v.isLt
  have ht : (u + v).toNat = (w + v).toNat := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add] at ht
  omega

theorem bv64_sub_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply bv64_add_right_cancel (v := BitVec.ofNat 64 b)
  rw [BitVec.sub_add_cancel, bv64_add_ofNat (by omega)]
  have hsub : a - b + b = a := by omega
  rw [hsub]

theorem bv64_mul_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a * b < 2 ^ 64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]

theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv64_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = (a == b) := by
  cases heq : (a == b) with
  | true =>
    have hab : a = b := beq_iff_eq.mp heq
    subst hab; simp
  | false =>
    cases hbv : (BitVec.ofNat 64 a == BitVec.ofNat 64 b) with
    | false => rfl
    | true =>
      have hw : BitVec.ofNat 64 a = BitVec.ofNat 64 b := beq_iff_eq.mp hbv
      have ht := congrArg BitVec.toNat hw
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
      exact absurd (beq_iff_eq.mpr ht) (by simp [heq])

theorem word10_ne_zero_sim (b : Bool) :
    ((if b then (1#64 : Word) else 0#64) != 0#64) = b := by
  cases b <;> decide

theorem res_var_self (lc : FMap String PanVal) (v : String) (old : Option PanVal) :
    res_var lc (v, old) v = old := by
  cases old <;> simp [res_var, DOMSUB, FUPDATE]

theorem res_var_ne (lc : FMap String PanVal) (v x : String) (old : Option PanVal)
    (hne : x ≠ v) :
    res_var lc (v, old) x = lc x := by
  cases old <;> simp [res_var, DOMSUB, FUPDATE, hne]

/-- Encoding relation for 1-word scalar/boolean/erased LCNF values. -/
def encodeScalar : LcnfVal → FoScalarTy → Word → Prop
  | .scalar n, .scalar hi, w => n ≤ hi ∧ hi < 2 ^ 64 ∧ w = BitVec.ofNat 64 n
  | .bool b,   .bool,      w => w = (if b then 1#64 else 0#64)
  | .erased,   .erased,    w => w = 0#64
  | _,         _,          _ => False

theorem encodeScalar_subTy {v : LcnfVal} {actual expected : FoScalarTy} {w : Word}
    (henc : encodeScalar v actual w) (hsub : actual.subTy expected = true) :
    encodeScalar v expected w := by
  cases actual <;> cases expected <;> simp [FoScalarTy.subTy] at hsub
  · rename_i a b
    cases v <;> simp [encodeScalar] at henc ⊢
    exact ⟨by omega, hsub.2, henc.2.2⟩
  · exact henc
  · exact henc

/-- Relational representation of distinct-name scalar constructor fields in `PanVal.rstruct`. -/
inductive CtorFieldsRel : List (String × LcnfVal) → List String → List Nat → List PanVal → Prop where
  | nil : CtorFieldsRel [] [] [] []
  | cons {nm : String} {n b : Nat} {fs : List (String × LcnfVal)}
      {nms : List String} {bs : List Nat} {pvs : List PanVal} :
      n ≤ b → b < 2 ^ 64 → nm ∉ nms →
      CtorFieldsRel fs nms bs pvs →
      CtorFieldsRel ((nm, .scalar n) :: fs) (nm :: nms) (b :: bs) (.word (BitVec.ofNat 64 n) :: pvs)

theorem ctorFieldsRel_shapes {fs : List (String × LcnfVal)} {nms : List String}
    {bs : List Nat} {pvs : List PanVal} (h : CtorFieldsRel fs nms bs pvs) :
    shapes_of pvs = List.replicate nms.length Shape.One ∧ fs.length = nms.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ ih => simp [shapes_of, List.replicate_succ, ih.1, ih.2]

theorem find_skip_of_not_mem {nm : String} {v : LcnfVal}
    {fs : List (String × LcnfVal)} {nms : List String} (hnot : nm ∉ nms) :
    splitValues ((nm, v) :: fs) nms = splitValues fs nms := by
  induction nms with
  | nil => rfl
  | cons m ms ih =>
    have hne : (nm == m) = false :=
      beq_eq_false_iff_ne.mpr (fun heq => hnot (heq ▸ List.Mem.head _))
    have hnot' : nm ∉ ms := fun hm => hnot (List.Mem.tail _ hm)
    simp only [splitValues, List.find?, hne, Bind.bind, Option.bind, pure, ih hnot']

theorem ctorFieldsRel_splitValues {fs : List (String × LcnfVal)} {nms : List String}
    {bs : List Nat} {pvs : List PanVal} (h : CtorFieldsRel fs nms bs pvs) :
    splitValues fs nms = some (fs.map Prod.snd) := by
  induction h with
  | nil => rfl
  | @cons nm n _ fs' nms' _ _ _ _ hnot _ ih =>
    simp only [splitValues, List.find?, beq_self_eq_true, Bind.bind, Option.bind, pure, find_skip_of_not_mem hnot, ih, List.map]

/-- Full first-order value representation in `PanVal`. -/
def encodeFoVal (tags : List String) : LcnfVal → FoTy → PanVal → Prop
  | v, .one st, .word w => encodeScalar v st w
  | .ctor tag fs, .ctor cTag cNames cBounds, .rstruct (.word wTag :: pvs) =>
    tag = cTag ∧
    ∃ idx, lookupTagIdx tags tag = some idx ∧ idx < 2 ^ 64 ∧
      wTag = BitVec.ofNat 64 idx ∧
      CtorFieldsRel fs cNames cBounds pvs
  | _, _, _ => False

theorem encodeFoVal_shape {tags : List String} {v : LcnfVal} {ty : FoTy} {pv : PanVal}
    (h : encodeFoVal tags v ty pv) : shape_of pv = ty.toShape := by
  cases ty with
  | one _ =>
    cases pv with
    | word _ => rfl
    | rstruct _ => cases h
  | ctor cTag cNames cBounds =>
    cases v <;> try cases h
    cases pv with
    | word _ => cases h
    | rstruct vs =>
      cases vs with
      | nil => cases h
      | cons v0 pvs =>
        cases v0 with
        | rstruct _ => cases h
        | word wTag =>
          obtain ⟨_, _, _, _, _, hrel⟩ := h
          have hsh := (ctorFieldsRel_shapes hrel).1
          simp [shape_of, shapes_of, FoTy.toShape, List.replicate_succ, hsh]

/-- Environment invariant linking `env`, `envTys`, `varSlots`, and `s.locals`. -/
inductive EnvMatches (tags : List String) :
    List LcnfVal → List FoTy → List (String × Shape) → FMap String PanVal → Prop where
  | nil (lc : FMap String PanVal) : EnvMatches tags [] [] [] lc
  | cons {v : LcnfVal} {ty : FoTy} {slot : String} {vs : List LcnfVal}
      {tys : List FoTy} {slots : List (String × Shape)} {lc : FMap String PanVal}
      {pv : PanVal} :
      lc slot = some pv →
      encodeFoVal tags v ty pv →
      EnvMatches tags vs tys slots lc →
      EnvMatches tags (v :: vs) (ty :: tys) ((slot, ty.toShape) :: slots) lc

theorem EnvMatches.congr {tags : List String} {env : List LcnfVal} {envTys : List FoTy}
    {varSlots : List (String × Shape)} {lc lc' : FMap String PanVal}
    (h : EnvMatches tags env envTys varSlots lc)
    (heq : ∀ p ∈ varSlots, lc' p.1 = lc p.1) :
    EnvMatches tags env envTys varSlots lc' := by
  induction h with
  | nil _ => exact .nil lc'
  | @cons v ty slot vs tys slots _ pv hlc henc _ ih =>
    have hhead : lc' slot = some pv := (heq (slot, ty.toShape) (List.Mem.head _)).trans hlc
    exact .cons hhead henc (ih (fun p hp => heq p (List.Mem.tail _ hp)))

theorem EnvMatches.lookup {tags : List String} {env : List LcnfVal} {envTys : List FoTy}
    {varSlots : List (String × Shape)} {lc : FMap String PanVal}
    (h : EnvMatches tags env envTys varSlots lc) :
    ∀ (idx : Nat) {ty : FoTy}, envTys[idx]? = some ty →
      ∃ v slot pv,
        env[idx]? = some v ∧
        varSlots[idx]? = some (slot, ty.toShape) ∧
        lc slot = some pv ∧
        encodeFoVal tags v ty pv := by
  induction h with
  | nil _ => intro idx _ hget; simp at hget
  | @cons v ty0 slot vs tys slots _ pv hlc henc _ ih =>
    intro idx ty hget
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      exact ⟨v, slot, pv, rfl, rfl, hlc, henc⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget ⊢
      exact ih k hget

/-- Slot-index upper bound for computational `'v'` slots. -/
def VarSlotsWF (nextId : Nat) (varSlots : List (String × Shape)) : Prop :=
  ∀ p ∈ varSlots, ∃ i, i < nextId ∧ p.1 = mkSlot 'v' i

theorem VarSlotsWF.mono {n1 n2 : Nat} {vs : List (String × Shape)}
    (hle : n1 ≤ n2) (h : VarSlotsWF n1 vs) : VarSlotsWF n2 vs :=
  fun p hp => let ⟨i, hi, heq⟩ := h p hp; ⟨i, by omega, heq⟩

theorem VarSlotsWF.lookup {nextId : Nat} {vs : List (String × Shape)}
    (h : VarSlotsWF nextId vs) {idx : Nat} {slot : String} {sh : Shape}
    (hget : vs[idx]? = some (slot, sh)) : ∃ i, i < nextId ∧ slot = mkSlot 'v' i :=
  h (slot, sh) (List.mem_of_getElem? hget)

/-- Well-formedness and index-disjointness of the active `CompiledJp` stack. -/
inductive JpStackWF : Nat → List JpSig → List CompiledJp → Prop where
  | nil (n : Nat) : JpStackWF n [] []
  | cons {n0 n1 : Nat} {sig : JpSig} {sigs : List JpSig} {cjs : List CompiledJp} :
      JpStackWF n0 sigs cjs →
      sig.jpId ∉ sigs.map JpSig.jpId →
      n0 + 1 + sig.params.length ≤ n1 →
      JpStackWF n1 (sig :: sigs)
        (⟨sig.jpId, sig.params.length, mkSlot 'h' n0, mkFreshSlots 'a' (n0 + 1) sig.params.length⟩ :: cjs)

theorem JpStackWF.mono {n1 n2 : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    (hle : n1 ≤ n2) (h : JpStackWF n1 sigs cjs) : JpStackWF n2 sigs cjs := by
  cases h with
  | nil _ => exact .nil n2
  | cons hsub hnot hbound => exact .cons hsub hnot (by omega)

def ArgSlotsBound (argSlots : List String) (lc : FMap String PanVal) : Prop :=
  ∀ a ∈ argSlots, ∃ w : Word, lc a = some (.word w)

def JpsIdle (jpSlots : List CompiledJp) (lc : FMap String PanVal) : Prop :=
  ∀ cj ∈ jpSlots, lc cj.hitSlot = some (.word 0#64) ∧ ArgSlotsBound cj.argSlots lc

/-- Pointwise relation between jump argument values and staged `'a'` local slots. -/
inductive ScalarSlotsRel :
    List LcnfVal → List FoScalarTy → List String → FMap String PanVal → Prop where
  | nil (lc : FMap String PanVal) : ScalarSlotsRel [] [] [] lc
  | cons {v : LcnfVal} {st : FoScalarTy} {slot : String} {vs : List LcnfVal}
      {sts : List FoScalarTy} {slots : List String} {lc : FMap String PanVal} {w : Word} :
      lc slot = some (.word w) →
      encodeScalar v st w →
      ScalarSlotsRel vs sts slots lc →
      ScalarSlotsRel (v :: vs) (st :: sts) (slot :: slots) lc

theorem ScalarSlotsRel.congr {vs : List LcnfVal} {sts : List FoScalarTy}
    {slots : List String} {lc lc' : FMap String PanVal}
    (h : ScalarSlotsRel vs sts slots lc) (heq : ∀ a ∈ slots, lc' a = lc a) :
    ScalarSlotsRel vs sts slots lc' := by
  induction h with
  | nil _ => exact .nil lc'
  | @cons v st slot vs' sts' slots' _ w hlc henc _ ih =>
    exact .cons ((heq slot (List.Mem.head _)).trans hlc) henc
      (ih (fun a ha => heq a (List.Mem.tail _ ha)))

theorem ScalarSlotsRel.length_eq {vs : List LcnfVal} {sts : List FoScalarTy}
    {slots : List String} {lc : FMap String PanVal}
    (h : ScalarSlotsRel vs sts slots lc) : vs.length = sts.length := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp [ih]

/-- Post-jump stack state: exactly the target join point has `hitSlot = 1#64` and populated `argSlots`;
    all other active join points remain idle (`hitSlot = 0#64`). -/
inductive JpTriggered (tid : Nat) (argVals : List LcnfVal) (lc : FMap String PanVal) :
    List JpSig → List CompiledJp → Prop where
  | here {sig : JpSig} {cj : CompiledJp} {sigs : List JpSig} {cjs : List CompiledJp} :
      sig.jpId = tid →
      lc cj.hitSlot = some (.word 1#64) →
      ScalarSlotsRel argVals sig.params cj.argSlots lc →
      JpsIdle cjs lc →
      JpTriggered tid argVals lc (sig :: sigs) (cj :: cjs)
  | there {sig : JpSig} {cj : CompiledJp} {sigs : List JpSig} {cjs : List CompiledJp} :
      sig.jpId ≠ tid →
      lc cj.hitSlot = some (.word 0#64) →
      ArgSlotsBound cj.argSlots lc →
      JpTriggered tid argVals lc sigs cjs →
      JpTriggered tid argVals lc (sig :: sigs) (cj :: cjs)

theorem jpStack_slots_lt {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    (h : JpStackWF n sigs cjs) :
    ∀ cj ∈ cjs,
      (∃ i < n, cj.hitSlot = mkSlot 'h' i) ∧
      (∀ a ∈ cj.argSlots, ∃ j < n, a = mkSlot 'a' j) := by
  induction h with
  | nil _ => intro _ hm; cases hm
  | @cons n0 n1 sig sigs' cjs' hsub _ hbound ih =>
    intro cj hm
    rcases List.mem_cons.mp hm with rfl | htl
    · refine ⟨⟨n0, by omega, rfl⟩, fun a ha => ?_⟩
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      exact ⟨j, by omega, rfl⟩
    · obtain ⟨⟨i, hi, hh⟩, hargs⟩ := ih cj htl
      exact ⟨⟨i, by omega, hh⟩, fun a ha => let ⟨j, hj, eq⟩ := hargs a ha; ⟨j, by omega, eq⟩⟩

theorem JpsIdle.congr_of_wf {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    {lc lc' : FMap String PanVal} (hwf : JpStackWF n sigs cjs) (hidle : JpsIdle cjs lc)
    (heq : ∀ i < n, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i)) :
    JpsIdle cjs lc' := by
  intro cj hcj
  obtain ⟨⟨i, hi, hh⟩, hargs⟩ := jpStack_slots_lt hwf cj hcj
  obtain ⟨hhit, hbnd⟩ := hidle cj hcj
  refine ⟨by rw [hh, (heq i hi).1, ← hh, hhit], fun a ha => ?_⟩
  obtain ⟨j, hj, rfl⟩ := hargs a ha
  obtain ⟨w, hw⟩ := hbnd (mkSlot 'a' j) ha
  exact ⟨w, (heq j hj).2.trans hw⟩

theorem JpTriggered.congr_of_wf {n : Nat} {sigs : List JpSig} {cjs : List CompiledJp}
    {tid : Nat} {argVals : List LcnfVal} {lc lc' : FMap String PanVal}
    (hwf : JpStackWF n sigs cjs)
    (htrig : JpTriggered tid argVals lc sigs cjs)
    (heq : ∀ i < n, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i)) :
    JpTriggered tid argVals lc' sigs cjs := by
  induction hwf with
  | nil _ => cases htrig
  | @cons n0 n1 sig sigs' cjs' hsub _ hbound ih =>
    have heqSub : ∀ i < n0, lc' (mkSlot 'h' i) = lc (mkSlot 'h' i) ∧ lc' (mkSlot 'a' i) = lc (mkSlot 'a' i) :=
      fun i hi => heq i (by omega)
    cases htrig with
    | here hid hhit hrel hidle =>
      refine .here hid ((heq n0 (by omega)).1.trans hhit) ?_ (JpsIdle.congr_of_wf hsub hidle heqSub)
      refine hrel.congr (fun a ha => ?_)
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      exact (heq j (by omega)).2
    | there hne hhit hbnd hrest =>
      refine .there hne ((heq n0 (by omega)).1.trans hhit) ?_ (ih hrest heqSub)
      intro a ha
      obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots ha
      obtain ⟨w, hw⟩ := hbnd (mkSlot 'a' j) ha
      exact ⟨w, (heq j (by omega)).2.trans hw⟩

/-- Argument compilation simulation (`compileArg` vs `evalLcnfArgVal` + `inferArgFoTy`). -/
theorem compileArg_sim {θ : Type} {tags : List String}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    {s : PanState θ} (henv : EnvMatches tags env envTys varSlots s.locals)
    {a : LcnfArg} {ty : FoTy} (hty : inferArgFoTy envTys a = some ty) :
    ∃ v pv,
      evalLcnfArgVal env a = some v ∧
      eval s (compileArg varSlots a) = some pv ∧
      argShape varSlots a = ty.toShape ∧
      encodeFoVal tags v ty pv := by
  cases a with
  | bvar idx =>
    simp only [inferArgFoTy] at hty
    obtain ⟨v, slot, pv, henvGet, hslotsGet, hlc, henc⟩ := henv.lookup idx hty
    exact ⟨v, pv, henvGet, by simp [compileArg, hslotsGet, hlc],
      by simp [argShape, hslotsGet], henc⟩
  | lit n =>
    simp only [inferArgFoTy] at hty
    by_cases hlt : n < 2 ^ 64 <;> simp [hlt] at hty
    subst hty
    exact ⟨.scalar n, .word (BitVec.ofNat 64 n), rfl, rfl, rfl, ⟨Nat.le_refl n, hlt, rfl⟩⟩
  | boolLit b =>
    simp only [inferArgFoTy, Option.some.injEq] at hty
    subst hty
    exact ⟨.bool b, .word (if b then 1#64 else 0#64), rfl, rfl, rfl, rfl⟩
  | erased =>
    simp only [inferArgFoTy, Option.some.injEq] at hty
    subst hty
    exact ⟨.erased, .word 0#64, rfl, rfl, rfl, rfl⟩
  | stateTok _ => simp [inferArgFoTy] at hty

theorem inferCtorFields_sim {θ : Type} {tags : List String}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    {s : PanState θ} (henv : EnvMatches tags env envTys varSlots s.locals) :
    ∀ (fields : List (String × LcnfArg)) {nms : List String} {bs : List Nat},
      inferCtorFields envTys fields = some (nms, bs) →
      ∃ fs pvs,
        (fields.mapM fun (p : String × LcnfArg) => do return (p.1, ← evalLcnfArgVal env p.2)) = some fs ∧
        evalList s (fields.map (fun f => compileArg varSlots f.2)) = some pvs ∧
        fields.length = nms.length ∧
        CtorFieldsRel fs nms bs pvs
  | [], _, _, h => by
    simp only [inferCtorFields, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨[], [], rfl, rfl, rfl, .nil⟩
  | (nm, a) :: rest, nms, bs, h => by
    simp only [inferCtorFields] at h
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at h
    | some tyA =>
      rw [ha] at h
      cases tyA with
      | ctor _ _ _ => simp at h
      | one st =>
        cases st with
        | bool | erased => simp at h
        | scalar b =>
          cases hrest : inferCtorFields envTys rest with
          | none => simp [hrest] at h
          | some p =>
            obtain ⟨nms', bs'⟩ := p
            rw [hrest] at h
            dsimp only at h
            cases hcond : (decide (b < 2 ^ 64) && !(nms'.contains nm)) with
            | false => rw [hcond] at h; simp at h
            | true =>
              simp only [hcond, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
                decide_eq_false_iff_not, decide_eq_true_eq] at hcond
              obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sim henv ha
              cases pva with
              | rstruct _ => cases henca
              | word wa =>
                cases va <;> simp [encodeFoVal, encodeScalar] at henca
                rename_i na
                rcases henca with ⟨hle, _, rfl⟩
                obtain ⟨fs', pvs', hfs', hpvs', hlen', hrel'⟩ := inferCtorFields_sim henv rest hrest
                refine ⟨(nm, .scalar na) :: fs', .word (BitVec.ofNat 64 na) :: pvs', ?_, ?_, by simp [hlen'],
                  .cons hle hcond.1 hcond.2 hrel'⟩
                · rw [List.mapM_cons]
                  dsimp only [Bind.bind, Option.bind, pure] at hfs' ⊢
                  rw [heva]
                  dsimp only
                  rw [hfs']
                · simp [hpva, hpvs']

/-- State-setup / state-teardown characterization of `wrapDecZeros`. -/
theorem evaluate_wrapDecZeros {θ : Type} :
    ∀ (start k : Nat) (inner : PStmt) (s : PanState θ),
      ∃ sInner : PanState θ,
        sInner.clock = s.clock ∧
        (StateWF s → StateWF sInner) ∧
        (∀ a ∈ mkFreshSlots 'a' start k, sInner.locals a = some (.word 0#64)) ∧
        (∀ x, (∀ j, start ≤ j → j < start + k → x ≠ mkSlot 'a' j) → sInner.locals x = s.locals x) ∧
        ∃ sOut : PanState θ,
          let rMid := evaluate inner sInner
          evaluate (wrapDecZeros (mkFreshSlots 'a' start k) inner) s = (rMid.1, sOut) ∧
          sOut.clock = rMid.2.clock ∧
          (StateWF rMid.2 → StateWF sOut) ∧
          (∀ x, (∀ j, start ≤ j → j < start + k → x ≠ mkSlot 'a' j) → sOut.locals x = rMid.2.locals x)
  | _, 0, inner, s => by
    refine ⟨s, rfl, id, ?_, fun _ _ => rfl, (evaluate inner s).2, rfl, rfl, id, fun _ _ => rfl⟩
    intro _ hm; cases hm
  | start, k + 1, inner, s => by
    let a0 := mkSlot 'a' start
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (a0, .word 0#64) }
    obtain ⟨sInner, hclkIn, hwfIn, hbndIn, hpresIn, sOut1, hev1, hclkOut1, hwfOut1, hpresOut1⟩ :=
      evaluate_wrapDecZeros (start + 1) k inner s1
    refine ⟨sInner, hclkIn, fun h => hwfIn ⟨h.1, h.2⟩, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (a0, s.locals a0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_⟩
    · intro a ha
      simp only [mkFreshSlots, List.mem_cons] at ha
      rcases ha with rfl | htl
      · rw [hpresIn a0 (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
        simp [s1, FUPDATE]
      · exact hbndIn a htl
    · intro x hx
      rw [hpresIn x (fun j hj1 hj2 => hx j (by omega) (by omega))]
      have hne0 : x ≠ a0 := hx start (Nat.le_refl _) (by omega)
      simp [s1, FUPDATE, hne0]
    · simp only [mkFreshSlots, wrapDecZeros]
      rw [evaluate_dec, eval_const]
      dsimp only
      have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro x hx
      have hne0 : x ≠ a0 := hx start (Nat.le_refl _) (by omega)
      dsimp only
      rw [res_var_ne _ _ _ _ hne0]
      exact hpresOut1 x (fun j hj1 hj2 => hx j (by omega) (by omega))

/-- Execution of `assignJpArgs` populates `argSlots` with `ScalarSlotsRel` while preserving all non-target slots. -/
theorem evaluate_assignJpArgs {θ : Type} {tags : List String} {vBound : Nat}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    (vswf : VarSlotsWF vBound varSlots) :
    ∀ (aStart : Nat) (args : List LcnfArg) (paramTys : List FoScalarTy) (s : PanState θ),
      StateWF s →
      EnvMatches tags env envTys varSlots s.locals →
      args.length = paramTys.length →
      checkArgsSubTy envTys args paramTys = true →
      ArgSlotsBound (mkFreshSlots 'a' aStart paramTys.length) s.locals →
      ∃ argVals sOut,
        args.mapM (evalLcnfArgVal env) = some argVals ∧
        evaluate (assignJpArgs varSlots (mkFreshSlots 'a' aStart paramTys.length) args) s = (.normal, sOut) ∧
        sOut.clock = s.clock ∧
        StateWF sOut ∧
        ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' aStart paramTys.length) sOut.locals ∧
        (∀ x, (∀ j, aStart ≤ j → j < aStart + paramTys.length → x ≠ mkSlot 'a' j) →
          sOut.locals x = s.locals x)
  | _, [], [], s, hwf, _, _, _, _ => by
    exact ⟨[], s, rfl, evaluate_skip s, rfl, hwf, .nil _, fun _ _ => rfl⟩
  | _, _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | _, [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | aStart, a :: as, expected :: es, s, hwf, henv, hlen, hsub, hbnd => by
    simp only [checkArgsSubTy] at hsub
    cases hact : inferArgScalarTy envTys a with
    | none => simp [hact] at hsub
    | some actual =>
      rw [hact] at hsub
      simp only [Bool.and_eq_true] at hsub
      simp only [inferArgScalarTy] at hact
      cases haTy : inferArgFoTy envTys a with
      | none => simp [haTy] at hact
      | some tyA =>
        rw [haTy] at hact
        cases tyA with
        | ctor _ _ _ => simp at hact
        | one stA =>
          dsimp only at hact
          split at hact <;> simp at hact
          subst hact
          obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sim henv haTy
          cases pva with
          | rstruct _ => cases henca
          | word wa =>
            have hencExp : encodeScalar va expected wa := encodeScalar_subTy henca hsub.1
            let dst := mkSlot 'a' aStart
            obtain ⟨wOld, hwOld⟩ := hbnd dst (by simp [List.length_cons, mkFreshSlots, dst])
            have hvalid : is_valid_value s .Local dst (.word wa) = true := by
              simp [is_valid_value, lookup_kvar, hwOld]
            let s1 := set_kvar .Local dst (.word wa) s
            have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
            have henv1 : EnvMatches tags env envTys varSlots s1.locals :=
              henv.congr (fun p hp => by
                obtain ⟨i, _, hiEq⟩ := vswf p hp
                have hne : p.1 ≠ dst := hiEq ▸ mkSlot_ne_of_kind (by decide) i aStart
                simp [s1, set_kvar, set_var, FUPDATE, hne])
            have hbnd1 : ArgSlotsBound (mkFreshSlots 'a' (aStart + 1) es.length) s1.locals := by
              intro a' ha'
              obtain ⟨j, hj1, _, rfl⟩ := mem_mkFreshSlots ha'
              have hne : mkSlot 'a' j ≠ dst := (mkSlot_ne_of_lt (by omega : aStart < j)).symm
              obtain ⟨w', hw'⟩ := hbnd (mkSlot 'a' j) (by simp [List.length_cons, mkFreshSlots, ha'])
              exact ⟨w', by simp [s1, set_kvar, set_var, FUPDATE, hne, hw']⟩
            obtain ⟨valsRest, sOut, hmapRest, hevRest, hclkRest, hwfOut, hrelRest, hpresRest⟩ :=
              evaluate_assignJpArgs vswf (aStart + 1) as es s1 hwf1 henv1 (by simpa using hlen) hsub.2 hbnd1
            refine ⟨va :: valsRest, sOut, by simp [List.mapM_cons, heva, hmapRest], ?_, hclkRest, hwfOut, ?_, ?_⟩
            · simp only [List.length_cons, mkFreshSlots, assignJpArgs]
              rw [evaluate_seq, evaluate_assign, hpva]
              dsimp only
              rw [hvalid]
              exact hevRest
            · simp only [List.length_cons, mkFreshSlots]
              have hdstOut : sOut.locals dst = some (.word wa) := by
                rw [hpresRest dst (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                simp [s1, set_kvar, set_var, FUPDATE]
              exact .cons hdstOut hencExp hrelRest
            · intro x hx
              simp only [List.length_cons] at hx
              rw [hpresRest x (fun j hj1 hj2 => hx j (by omega) (by omega))]
              have hne0 : x ≠ dst := hx aStart (Nat.le_refl _) (by omega)
              simp [s1, set_kvar, set_var, FUPDATE, hne0]

/-- Jump-dispatch across `JpStackWF`: executes `assignJpArgs ;; lassign hitSlot 1 ;; tick` and produces `JpTriggered`. -/
theorem evaluate_jmp_stack {θ : Type} {tags : List String} {vBound n : Nat}
    {env : List LcnfVal} {envTys : List FoTy} {varSlots : List (String × Shape)}
    (vswf : VarSlotsWF vBound varSlots)
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    (jpswf : JpStackWF n jpSigs jpSlots)
    {id : Nat} {args : List LcnfArg} {sig : JpSig}
    (hfind : jpSigs.find? (fun s => s.jpId == id) = some sig)
    (hlen : args.length = sig.params.length)
    (hsub : checkArgsSubTy envTys args sig.params = true)
    {s : PanState θ} (hwf : StateWF s) (hclk : 1 ≤ s.clock)
    (henv : EnvMatches tags env envTys varSlots s.locals)
    (hidle : JpsIdle jpSlots s.locals) :
    ∃ cj argVals s1,
      jpSlots.find? (fun c => c.jpId == id) = some cj ∧
      args.mapM (evalLcnfArgVal env) = some argVals ∧
      evaluate (.seq (assignJpArgs varSlots cj.argSlots args)
        (.seq (.lassign cj.hitSlot (.const 1#64)) .tick)) s = (.normal, s1) ∧
      s.clock ≤ s1.clock + 1 ∧
      StateWF s1 ∧
      JpTriggered id argVals s1.locals jpSigs jpSlots ∧
      (∀ idx, s1.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
      (∀ k idx, n ≤ idx → (k = 'h' ∨ k = 'a') → s1.locals (mkSlot k idx) = s.locals (mkSlot k idx)) := by
  induction jpswf with
  | nil _ => simp at hfind
  | @cons n0 n1 sigHd sigsTl cjsTl hsubWf _ hbound ih =>
    let cjHd : CompiledJp := ⟨sigHd.jpId, sigHd.params.length, mkSlot 'h' n0,
      mkFreshSlots 'a' (n0 + 1) sigHd.params.length⟩
    simp only [List.find?] at hfind
    cases heq : (sigHd.jpId == id) with
    | true =>
      rw [heq] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      obtain ⟨hhit0, hbnd0⟩ := hidle cjHd (List.Mem.head _)
      have hidleTl : JpsIdle cjsTl s.locals := fun c hc => hidle c (List.Mem.tail _ hc)
      obtain ⟨argVals, sArgs, hmap, hevArgs, hclkArgs, hwfArgs, hrelArgs, hpresArgs⟩ :=
        evaluate_assignJpArgs vswf (n0 + 1) args sigHd.params s hwf henv hlen hsub hbnd0
      have hhitArgs : sArgs.locals (mkSlot 'h' n0) = some (.word 0#64) :=
        (hpresArgs _ (fun j _ _ => mkSlot_ne_of_kind (by decide) n0 j)).trans hhit0
      have hvalidHit : is_valid_value sArgs .Local (mkSlot 'h' n0) (.word 1#64) = true := by
        simp [is_valid_value, lookup_kvar, hhitArgs]
      let sHit := set_kvar .Local (mkSlot 'h' n0) (.word 1#64) sArgs
      have hclkHit : (sHit.clock == 0) = false := by
        have hpos : 0 < sHit.clock := by simp [sHit, set_kvar, set_var, hclkArgs]; omega
        cases hsc : sHit.clock with
        | zero => omega
        | succ _ => rfl
      let s1 := dec_clock sHit
      refine ⟨cjHd, argVals, s1, by simp [cjHd, List.find?, heq], hmap, ?_, ?_, ⟨hwfArgs.1, hwfArgs.2⟩, ?_, ?_, ?_⟩
      · dsimp only [cjHd]
        rw [evaluate_seq, hevArgs]
        dsimp only
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [evaluate_seq, evaluate_assign, eval_const]
        dsimp only
        rw [hvalidHit]
        simp only [↓reduceIte, beq_self_eq_true]
        rw [evaluate_tick, hclkHit]
        rfl
      · simp only [s1, dec_clock_clock, sHit, set_kvar, set_var, hclkArgs]; omega
      · refine .here (beq_iff_eq.mp heq) (by simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE]) ?_ ?_
        · exact hrelArgs.congr (fun a ha => by
            obtain ⟨j, _, _, rfl⟩ := mem_mkFreshSlots ha
            have hne : mkSlot 'a' j ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) j n0
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hne])
        · refine JpsIdle.congr_of_wf hsubWf hidleTl (fun i hi => ⟨?_, ?_⟩)
          · have hneH : mkSlot 'h' i ≠ mkSlot 'h' n0 := mkSlot_ne_of_lt hi
            have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'h' i ≠ mkSlot 'a' j :=
              fun j _ _ => mkSlot_ne_of_kind (by decide) i j
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
          · have hneH : mkSlot 'a' i ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) i n0
            have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'a' i ≠ mkSlot 'a' j :=
              fun j hj1 _ => mkSlot_ne_of_lt (by omega)
            simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
      · intro idx
        have hneH : mkSlot 'v' idx ≠ mkSlot 'h' n0 := mkSlot_ne_of_kind (by decide) idx n0
        have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot 'v' idx ≠ mkSlot 'a' j :=
          fun j _ _ => mkSlot_ne_of_kind (by decide) idx j
        simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
      · intro k idx hge _
        have hneH : mkSlot k idx ≠ mkSlot 'h' n0 := (mkSlot_ne_of_lt (by omega : n0 < idx)).symm
        have hneA : ∀ j, n0 + 1 ≤ j → j < n0 + 1 + sigHd.params.length → mkSlot k idx ≠ mkSlot 'a' j :=
          fun j _ hj2 => (mkSlot_ne_of_lt (by omega : j < idx)).symm
        simp [s1, dec_clock, sHit, set_kvar, set_var, FUPDATE, hneH, hpresArgs _ hneA]
    | false =>
      rw [heq] at hfind
      obtain ⟨hhit0, hbnd0⟩ := hidle cjHd (List.Mem.head _)
      have hidleTl : JpsIdle cjsTl s.locals := fun c hc => hidle c (List.Mem.tail _ hc)
      obtain ⟨cj, argVals, s1, hcjFind, hmap, hev1, hclk1, hwf1, htrig1, hvPres, hhaPres⟩ :=
        ih hfind hidleTl
      refine ⟨cj, argVals, s1, by simp [List.find?, heq, hcjFind], hmap, hev1, hclk1, hwf1, ?_, hvPres, ?_⟩
      · refine .there (beq_eq_false_iff_ne.mp heq) ?_ ?_ htrig1
        · exact (hhaPres 'h' n0 (Nat.le_refl _) (Or.inl rfl)).trans hhit0
        · intro a ha
          obtain ⟨j, hj1, _, rfl⟩ := mem_mkFreshSlots ha
          obtain ⟨w, hw⟩ := hbnd0 (mkSlot 'a' j) ha
          exact ⟨w, (hhaPres 'a' j (by omega) (Or.inr rfl)).trans hw⟩
      · intro k idx hge hk
        exact hhaPres k idx (by omega) hk

/-- State-setup / state-teardown characterization of `bindJpParams`. -/
theorem evaluate_bindJpParams_raw {θ : Type} (tags : List String) :
    ∀ (pStart aStart : Nat) (argVals : List LcnfVal) (paramTys : List FoScalarTy)
      (inner : PStmt) (s : PanState θ),
      StateWF s →
      ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' aStart paramTys.length) s.locals →
      ∃ sInner : PanState θ,
        let k := paramTys.length
        let pSlots := mkFreshSlots 'v' pStart k
        sInner.clock = s.clock ∧
        StateWF sInner ∧
        (∀ x, (∀ j, pStart ≤ j → j < pStart + k → x ≠ mkSlot 'v' j) → sInner.locals x = s.locals x) ∧
        (∀ env envTys varSlots,
          EnvMatches tags env envTys varSlots sInner.locals →
          EnvMatches tags (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
            ((pSlots.map (fun nm => (nm, Shape.One))) ++ varSlots) sInner.locals) ∧
        ∃ sOut : PanState θ,
          let rMid := evaluate inner sInner
          evaluate (bindJpParams pSlots (mkFreshSlots 'a' aStart k) inner) s = (rMid.1, sOut) ∧
          sOut.clock = rMid.2.clock ∧
          (StateWF rMid.2 → StateWF sOut) ∧
          ((∀ idx, rMid.2.locals (mkSlot 'v' idx) = sInner.locals (mkSlot 'v' idx)) →
            ∀ idx, sOut.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
          (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sOut.locals x = rMid.2.locals x)
  | _, _, [], [], inner, s, hwf, .nil _ => by
    exact ⟨s, rfl, hwf, fun _ _ => rfl, fun _ _ _ h => h,
      (evaluate inner s).2, rfl, rfl, id, fun h => h, fun _ _ => rfl⟩
  | pStart, aStart, v :: vs, st :: sts, inner, s, hwf, .cons (w := w) hlcA hencA hrelRest => by
    let p0 := mkSlot 'v' pStart
    let a0 := mkSlot 'a' aStart
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (p0, .word w) }
    have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
    have hrel1 : ScalarSlotsRel vs sts (mkFreshSlots 'a' (aStart + 1) sts.length) s1.locals :=
      hrelRest.congr (fun a ha => by
        obtain ⟨j, _, _, rfl⟩ := mem_mkFreshSlots ha
        have hne : mkSlot 'a' j ≠ p0 := mkSlot_ne_of_kind (by decide) j pStart
        simp [s1, FUPDATE, hne])
    obtain ⟨sInner, hclkIn, hwfIn, hpresIn, hliftEnv, sOut1, hev1, hclkOut1, hwfOut1, hvOut1, hnonVOut1⟩ :=
      evaluate_bindJpParams_raw tags (pStart + 1) (aStart + 1) vs sts inner s1 hwf1 hrel1
    refine ⟨sInner, hclkIn, hwfIn, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (p0, s.locals p0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_, ?_⟩
    · intro x hx
      simp only [List.length_cons] at hx
      rw [hpresIn x (fun j hj1 hj2 => hx j (by omega) (by omega))]
      have hne0 : x ≠ p0 := hx pStart (Nat.le_refl _) (by omega)
      simp [s1, FUPDATE, hne0]
    · intro env envTys varSlots henv
      have hp0In : sInner.locals p0 = some (.word w) := by
        rw [hpresIn p0 (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
        simp [s1, FUPDATE]
      simp only [List.length_cons, List.cons_append, List.map_cons, mkFreshSlots]
      exact .cons (ty := .one st) hp0In hencA (hliftEnv env envTys varSlots henv)
    · simp only [List.length_cons, mkFreshSlots, bindJpParams]
      rw [evaluate_dec, eval_lvar, hlcA]
      dsimp only
      have hsh : (Shape.One == shape_of (.word w)) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro hmidV idx
      have hv1 := hvOut1 hmidV
      dsimp only
      if heq : idx = pStart then
        subst heq
        exact res_var_self sOut1.locals p0 (s.locals p0)
      else
        have hne : mkSlot 'v' idx ≠ p0 := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hv1 idx]
        simp [s1, FUPDATE, hne]
    · intro x hx
      dsimp only
      rw [res_var_ne _ _ _ _ (hx pStart)]
      exact hnonVOut1 x hx

/-- State-setup / state-teardown characterization of `bindCtorFields` for `.cases` arms. -/
theorem evaluate_bindCtorFields {θ : Type} (tags : List String)
    {scrutSlot : String} {si : Nat} (hsiSlot : scrutSlot = mkSlot 'v' si)
    {rvs : List PanVal} :
    ∀ (vStart fieldIdx : Nat)
      {fs : List (String × LcnfVal)} {nms : List String} {bs : List Nat} {pvs : List PanVal},
      CtorFieldsRel fs nms bs pvs →
      ∀ (accVals : List LcnfVal) (accTys : List FoTy) (accSlots : List (String × Shape))
        (inner : PStmt) (s : PanState θ),
        si < vStart →
        StateWF s →
        s.locals scrutSlot = some (.rstruct rvs) →
        (∀ j, j < pvs.length → rvs[fieldIdx + j]? = pvs[j]?) →
        VarSlotsWF vStart accSlots →
        EnvMatches tags accVals accTys accSlots s.locals →
        ∃ sInner : PanState θ,
          let k := nms.length
          let fSlots := mkFreshSlots 'v' vStart k
          sInner.clock = s.clock ∧
          StateWF sInner ∧
          VarSlotsWF (vStart + k) ((fSlots.reverse.map (fun nm => (nm, Shape.One))) ++ accSlots) ∧
          EnvMatches tags ((fs.map Prod.snd).reverse ++ accVals)
            ((bs.reverse.map (fun b => FoTy.one (.scalar b))) ++ accTys)
            ((fSlots.reverse.map (fun nm => (nm, Shape.One))) ++ accSlots) sInner.locals ∧
          (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sInner.locals x = s.locals x) ∧
          ∃ sOut : PanState θ,
            let rMid := evaluate inner sInner
            evaluate (bindCtorFields (.lvar scrutSlot) fieldIdx fSlots inner) s = (rMid.1, sOut) ∧
            sOut.clock = rMid.2.clock ∧
            (StateWF rMid.2 → StateWF sOut) ∧
            ((∀ idx, rMid.2.locals (mkSlot 'v' idx) = sInner.locals (mkSlot 'v' idx)) →
              ∀ idx, sOut.locals (mkSlot 'v' idx) = s.locals (mkSlot 'v' idx)) ∧
            (∀ x, (∀ c, x ≠ mkSlot 'v' c) → sOut.locals x = rMid.2.locals x)
  | vStart, _, _, _, _, _, .nil, accVals, accTys, accSlots, inner, s, _, hwf, _, _, hvswf, henv => by
    exact ⟨s, rfl, hwf, by simpa [mkFreshSlots] using hvswf, henv, fun _ _ => rfl,
      (evaluate inner s).2, rfl, rfl, id, fun h => h, fun _ _ => rfl⟩
  | vStart, fieldIdx, _, _, _, _, @CtorFieldsRel.cons nm n b fs' nms' bs' pvs' hnb hbLt _ hrelRest,
      accVals, accTys, accSlots, inner, s, hsiLt, hwf, hscrut, hrvsGet, hvswf, henv => by
    let f0 := mkSlot 'v' vStart
    have hget0 : rvs[fieldIdx]? = some (.word (BitVec.ofNat 64 n)) := by
      have h0 := hrvsGet 0 (by simp)
      simpa using h0
    let s1 : PanState θ := { s with locals := FUPDATE s.locals (f0, .word (BitVec.ofNat 64 n)) }
    have hwf1 : StateWF s1 := ⟨hwf.1, hwf.2⟩
    have hscrutNe : scrutSlot ≠ f0 := hsiSlot ▸ mkSlot_ne_of_lt hsiLt
    have hscrut1 : s1.locals scrutSlot = some (.rstruct rvs) := by
      simp [s1, FUPDATE, hscrutNe, hscrut]
    have hvswf1 : VarSlotsWF (vStart + 1) ((f0, Shape.One) :: accSlots) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | htl
      · exact ⟨vStart, by omega, rfl⟩
      · obtain ⟨i, hi, heq⟩ := hvswf p htl
        exact ⟨i, by omega, heq⟩
    have henv1 : EnvMatches tags (.scalar n :: accVals) (FoTy.one (.scalar b) :: accTys)
        ((f0, Shape.One) :: accSlots) s1.locals := by
      refine EnvMatches.cons (pv := .word (BitVec.ofNat 64 n)) (ty := .one (.scalar b))
        (by simp [s1, FUPDATE]) ⟨hnb, hbLt, rfl⟩ ?_
      exact henv.congr (fun p hp => by
        obtain ⟨i, hi, hpEq⟩ := hvswf p hp
        have hne : p.1 ≠ f0 := hpEq ▸ mkSlot_ne_of_lt hi
        simp [s1, FUPDATE, hne])
    have hrvsGet1 : ∀ j, j < pvs'.length → rvs[(fieldIdx + 1) + j]? = pvs'[j]? := by
      intro j hj
      have h1 := hrvsGet (j + 1) (by simp; omega)
      have hidx : fieldIdx + (j + 1) = (fieldIdx + 1) + j := by omega
      rw [← hidx, h1]; rfl
    obtain ⟨sInner, hclkIn, hwfIn, hvswfIn, henvIn, hnonVIn, sOut1, hev1, hclkOut1, hwfOut1, hvOut1, hnonVOut1⟩ :=
      evaluate_bindCtorFields tags hsiSlot (vStart + 1) (fieldIdx + 1) hrelRest
        (.scalar n :: accVals) (FoTy.one (.scalar b) :: accTys) ((f0, Shape.One) :: accSlots)
        inner s1 (by omega) hwf1 hscrut1 hrvsGet1 hvswf1 henv1
    have haddEq : vStart + 1 + nms'.length = vStart + (nms'.length + 1) := by omega
    have hslotsEq :
        ((mkFreshSlots 'v' vStart (nms'.length + 1)).reverse.map (fun nm => (nm, Shape.One))) ++ accSlots =
        ((mkFreshSlots 'v' (vStart + 1) nms'.length).reverse.map (fun nm => (nm, Shape.One))) ++
          ((f0, Shape.One) :: accSlots) := by
      simp [mkFreshSlots, f0, List.reverse_cons, List.map_append, List.append_assoc]
    have hvalsEq :
        (((nm, LcnfVal.scalar n) :: fs').map Prod.snd).reverse ++ accVals =
        (fs'.map Prod.snd).reverse ++ (LcnfVal.scalar n :: accVals) := by
      simp [List.reverse_cons, List.append_assoc]
    have htysEq :
        ((b :: bs').reverse.map (fun x => FoTy.one (.scalar x))) ++ accTys =
        (bs'.reverse.map (fun x => FoTy.one (.scalar x))) ++ (FoTy.one (.scalar b) :: accTys) := by
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    refine ⟨sInner, hclkIn, hwfIn, ?_, ?_, ?_,
      { sOut1 with locals := res_var sOut1.locals (f0, s.locals f0) }, ?_, hclkOut1,
      fun h => let h1 := hwfOut1 h; ⟨h1.1, h1.2⟩, ?_, ?_⟩
    · simp only [List.length_cons]; rw [hslotsEq, ← haddEq]; exact hvswfIn
    · simp only [List.length_cons]; rw [hvalsEq, htysEq, hslotsEq]; exact henvIn
    · intro x hx
      rw [hnonVIn x hx]
      simp [s1, f0, FUPDATE, hx vStart]
    · simp only [List.length_cons, mkFreshSlots, bindCtorFields]
      rw [evaluate_dec, eval_rfield, eval_lvar, hscrut]
      dsimp only
      rw [hget0]
      dsimp only
      have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 n))) = true := rfl
      simp only [hsh, ↓reduceIte]
      rw [hev1]
    · intro hmidV idx
      have hv1 := hvOut1 hmidV
      dsimp only
      if heq : idx = vStart then
        subst heq
        exact res_var_self sOut1.locals f0 (s.locals f0)
      else
        have hne : mkSlot 'v' idx ≠ f0 := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hv1 idx]
        simp [s1, FUPDATE, hne]
    · intro x hx
      dsimp only
      rw [res_var_ne _ _ _ _ (hx vStart)]
      exact hnonVOut1 x hx

/-- Unified outcome postcondition for `compileCode_sound`. -/
def BlockPost {θ : Type} (retBound : Nat) (jpSigs : List JpSig) (jpSlots : List CompiledJp)
    (s0 : PanState θ) (out : FoOutcome) (r : PanResult) (s1 : PanState θ) : Prop :=
  match out with
  | .returned v =>
    ∃ n, v = .scalar n ∧ n ≤ retBound ∧ retBound < 2 ^ 64 ∧
      r = .ret (.word (BitVec.ofNat 64 n))
  | .jumped tid argVals =>
    r = .normal ∧
    JpTriggered tid argVals s1.locals jpSigs jpSlots ∧
    (∀ idx, s1.locals (mkSlot 'v' idx) = s0.locals (mkSlot 'v' idx))

theorem BlockPost.widen_bound {θ : Type} {b1 b2 : Nat} (hle : b1 ≤ b2) (hlt : b2 < 2 ^ 64)
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    {s0 : PanState θ} {out : FoOutcome} {r : PanResult} {s1 : PanState θ}
    (h : BlockPost b1 jpSigs jpSlots s0 out r s1) :
    BlockPost b2 jpSigs jpSlots s0 out r s1 := by
  cases out with
  | returned v =>
    obtain ⟨n, rfl, hn, _, hr⟩ := h
    exact ⟨n, rfl, by omega, hlt, hr⟩
  | jumped _ _ => exact h

theorem mkSlot_h_ne_v (i j : Nat) : mkSlot 'h' i ≠ mkSlot 'v' j :=
  mkSlot_ne_of_kind (by decide) i j

theorem mkSlot_a_ne_v (i j : Nat) : mkSlot 'a' i ≠ mkSlot 'v' j :=
  mkSlot_ne_of_kind (by decide) i j

theorem BlockPost.after_dec_v {θ : Type} {retBound nextId : Nat}
    {jpSigs : List JpSig} {jpSlots : List CompiledJp}
    (jpswf : JpStackWF nextId jpSigs jpSlots)
    {s0 sIn smid : PanState θ} {vIdx : Nat} {out : FoOutcome} {r : PanResult}
    (hsInV : ∀ idx, idx ≠ vIdx → sIn.locals (mkSlot 'v' idx) = s0.locals (mkSlot 'v' idx))
    (hpost : BlockPost retBound jpSigs jpSlots sIn out r smid) :
    BlockPost retBound jpSigs jpSlots s0 out r
      { smid with locals := res_var smid.locals (mkSlot 'v' vIdx, s0.locals (mkSlot 'v' vIdx)) } := by
  cases out with
  | returned v => exact hpost
  | jumped tid argVals =>
    obtain ⟨hr, htrig, hvPres⟩ := hpost
    refine ⟨hr, ?_, ?_⟩
    · refine JpTriggered.congr_of_wf jpswf htrig (fun i _ => ⟨?_, ?_⟩)
      · dsimp only; exact res_var_ne _ _ _ _ (mkSlot_h_ne_v i vIdx)
      · dsimp only; exact res_var_ne _ _ _ _ (mkSlot_a_ne_v i vIdx)
    · intro idx
      dsimp only
      if heq : idx = vIdx then
        subst heq
        exact res_var_self smid.locals _ _
      else
        have hne : mkSlot 'v' idx ≠ mkSlot 'v' vIdx := fun h => heq (mkSlot_inj h).2
        rw [res_var_ne _ _ _ _ hne, hvPres idx, hsInV idx heq]


end Obend.Lower.Pancake
end
