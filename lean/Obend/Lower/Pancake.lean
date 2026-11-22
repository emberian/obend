module
/-
# `Obend.Lower.Pancake` — Verified First-Order `LcnfCode → PStmt` Compiler & `Core4` Weld (`G6`)

Closes Cross-Tree Gate `G6` (`MASTER_REVIVAL_ALIGNMENT.md` §2.1.4 & §4.1):
1. **`synthStmtClk_compileLcnfToPancake`**: Generic `CondSClk.synthStmtClk` recovers `synthLcnfClk c`
   identically on every compiled `LcnfCode`.
2. **`compileLcnfToPancake_correct` & `compileLcnfToPancake_premises_inhabited`**: Every well-typed
   first-order `LcnfCode` term (`letValue`, `.natOp` with saturating `.sub`, `.ctor`/`.cases`,
   `ifBool`, lexical `jpDecl`/`jmp`, `return`) evaluates in `evalLcnfCode` to `n < 2^64` AND executes
   in `PanSem.evaluate` under synthesized `CondSClk` fuel `synthLcnfClk c` with `0` `TimeOut`/`Error`
   to `.ret (.word (BitVec.ofNat 64 n))`.
3. **`compileLcnfToPancake_agrees_with_core4`**: Welds `compileLcnfToPancake` directly to
   `Obend.Lower.LCNF.compileLcnfToCore4` (`LCNF.lean:584`) on join-free pure blocks.
4. **`runCompiledLcnfBatch_sound`**: Multi-turn batch execution preserving `StateWF` and cumulative
   remaining `CondSClk` fuel across persistent `PanState` turns.
-/
public import Obend.Lower.LCNF
public import Obend.Lower.Pancake.PanSem
public import Obend.Lower.Pancake.CondSClk
public import Obend.Lower.Pancake.RefinesClkPan
public import Obend.Lower.Pancake.LcnfEmit
public import Obend.Lower.Pancake.LcnfSimHelpers
import all Obend.Core.Term
import all Obend.Lower.LCNF
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.CondSClk
import all Obend.Lower.Pancake.RefinesClkPan
import all Obend.Lower.Pancake.LcnfEmit
import all Obend.Lower.Pancake.LcnfSimHelpers

public section

namespace Obend.Lower.Pancake

open Obend.Core.Term (Evaluates splitValues)
open Obend.Lower (NatOp)
open Obend.Lower.LCNF

set_option autoImplicit false

/-- Generic `CondSClk.synthStmtClk` recovers `synthLcnfClk c` identically on every compiled `LcnfCode`. -/
theorem synthStmtClk_compileLcnfToPancake (c : LcnfCode) :
    synthStmtClk (compileLcnfToPancake c) = some (synthLcnfClk c) :=
  (compileCode_clk_and_mono (collectTags c) c [] [] 0).1

mutual
/-- **Core Structural Compiler Simulation Theorem (`compileCode_sim`)**:
    Every `LcnfCode` block passing `checkFoCode` evaluates in `evalFoBlock` to some `out` and
    executes in `PanSem.evaluate` under `synthLcnfClk c` fuel with `0` `TimeOut`/`Error`,
    consuming at most `synthLcnfClk c` ticks and satisfying `BlockPost`. -/
private theorem compileCode_sim {θ : Type} (tags : List String) :
    ∀ (c : LcnfCode) (env : List LcnfVal) (envTys : List FoTy)
      (varSlots : List (String × Shape)) (jpSigs : List JpSig) (jpSlots : List CompiledJp)
      (nextId retBound : Nat) (s0 : PanState θ),
      checkFoCode tags envTys jpSigs c = some retBound →
      StateWF s0 →
      synthLcnfClk c ≤ s0.clock →
      VarSlotsWF nextId varSlots →
      JpStackWF nextId jpSigs jpSlots →
      EnvMatches tags env envTys varSlots s0.locals →
      JpsIdle jpSlots s0.locals →
      ∃ out r s1,
        evalFoBlock env c = some out ∧
        evaluate (compileCode tags varSlots jpSlots nextId c).1 s0 = (r, s1) ∧
        s0.clock ≤ s1.clock + synthLcnfClk c ∧
        StateWF s1 ∧
        BlockPost retBound jpSigs jpSlots s0 out r s1
  | .return a, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, _, _, _, henv, _ => by
    simp only [checkFoCode] at hchk
    cases ha : inferArgFoTy envTys a with
    | none => simp [ha] at hchk
    | some tyA =>
      rw [ha] at hchk
      cases tyA with
      | ctor _ _ _ => simp at hchk
      | one stA =>
        cases stA with
        | bool | erased => simp at hchk
        | scalar hi =>
          simp only at hchk
          split at hchk <;> simp at hchk
          subst hchk
          obtain ⟨va, pva, heva, hpva, _, henca⟩ := compileArg_sim henv ha
          cases pva with
          | rstruct _ => simp [encodeFoVal] at henca
          | word wa =>
            cases va <;> simp [encodeFoVal, encodeScalar] at henca
            rename_i n
            rcases henca with ⟨hn, hlt, rfl⟩
            refine ⟨.returned (.scalar n), .ret (.word (BitVec.ofNat 64 n)), empty_locals s0,
              by simp [evalFoBlock, heva], ?_, by simp [empty_locals, synthLcnfClk],
              ⟨hwf.1, hwf.2⟩, ⟨n, rfl, hn, hlt, rfl⟩⟩
            simp only [compileCode]
            rw [evaluate_ret, hpva]
            rfl
  | .unreach, _, _, _, _, _, _, _, _, hchk, _, _, _, _, _, _ => by
    simp [checkFoCode] at hchk
  | .jmp id args, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hfind : jpSigs.find? (fun s => s.jpId == id) with
    | none => simp [hfind] at hchk
    | some sig =>
      rw [hfind] at hchk
      dsimp only at hchk
      cases hcond : (args.length == sig.params.length && checkArgsSubTy envTys args sig.params) with
      | false => simp [hcond] at hchk
      | true =>
        simp only [hcond, ↓reduceIte, Option.some.injEq] at hchk
        subst hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        simp only [synthLcnfClk] at hclk
        obtain ⟨cj, argVals, s1, hcjFind, hmap, hev1, hclk1, hwf1, htrig1, hvPres, _⟩ :=
          evaluate_jmp_stack hvswf hjpswf hfind hcond.1 hcond.2 hwf hclk henv hidle
        refine ⟨.jumped id argVals, .normal, s1, by simp [evalFoBlock, hmap], ?_, hclk1, hwf1,
          ⟨rfl, htrig1, hvPres⟩⟩
        simp only [compileCode, hcjFind]
        exact hev1
  | .letValue lv body, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hty : inferLetValFoTy tags envTys lv with
    | none => simp [hty] at hchk
    | some ty =>
      rw [hty] at hchk
      dsimp only at hchk
      simp only [synthLcnfClk] at hclk
      let vSlot := mkSlot 'v' nextId
      have hvswf' : VarSlotsWF (nextId + 1) ((vSlot, ty.toShape) :: varSlots) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | htl
        · exact ⟨nextId, by omega, rfl⟩
        · exact (hvswf.mono (by omega)) p htl
      have hjpswf' : JpStackWF (nextId + 1) jpSigs jpSlots := hjpswf.mono (by omega)
      cases lv with
      | record _ | proj _ _ | app _ _ | stateRead _ _ | stateWrite _ _ _ =>
        simp [inferLetValFoTy] at hty
      | arg a =>
        simp only [inferLetValFoTy] at hty
        obtain ⟨va, pva, heva, hpva, hshEq, henca⟩ := compileArg_sim henv hty
        let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, pva) }
        have henvIn : EnvMatches tags (va :: env) (ty :: envTys) ((vSlot, ty.toShape) :: varSlots) sIn.locals := by
          refine .cons (by simp [sIn, FUPDATE]) henca ?_
          exact henv.congr (fun p hp => by
            obtain ⟨i, hi, hpEq⟩ := hvswf p hp
            have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
            simp [sIn, FUPDATE, hne])
        have hidleIn : JpsIdle jpSlots sIn.locals :=
          JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
            ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
             by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
        obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
          compileCode_sim tags body (va :: env) (ty :: envTys) ((vSlot, ty.toShape) :: varSlots)
            jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
        have hshVal : (ty.toShape == shape_of pva) = true := beq_iff_eq.mpr (encodeFoVal_shape henca).symm
        refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
          by simp [evalFoBlock, evalFoLetVal, heva, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
          hpostB.after_dec_v hjpswf (fun idx hne => by
            have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
            simp [sIn, FUPDATE, hneS])⟩
        simp only [compileCode, hshEq]
        rw [evaluate_dec, hpva]
        dsimp only [sIn] at hevB
        dsimp only
        simp only [hshVal, ↓reduceIte]
        rw [hevB]
      | ctor tag fields =>
        simp only [inferLetValFoTy] at hty
        cases htIdx : lookupTagIdx tags tag with
        | none => simp [htIdx] at hty
        | some tIdx =>
          cases hflds : inferCtorFields envTys fields with
          | none => simp [htIdx, hflds] at hty
          | some p =>
            obtain ⟨nms, bs⟩ := p
            rw [htIdx, hflds] at hty
            dsimp only at hty
            by_cases htIdxLt : tIdx < 2 ^ 64 <;> simp [htIdxLt] at hty
            subst hty
            obtain ⟨fs, pvs, hfs, hpvs, hlenEq, hrel⟩ := inferCtorFields_sim henv fields hflds
            let pv := PanVal.rstruct (.word (BitVec.ofNat 64 tIdx) :: pvs)
            have hencPv : encodeFoVal tags (.ctor tag fs) (.ctor tag nms bs) pv :=
              ⟨rfl, tIdx, htIdx, htIdxLt, rfl, hrel⟩
            have hshCtor : Shape.Comb (List.replicate (fields.length + 1) .One) = (FoTy.ctor tag nms bs).toShape := by
              simp [FoTy.toShape, hlenEq]
            let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, pv) }
            have henvIn : EnvMatches tags (.ctor tag fs :: env) (.ctor tag nms bs :: envTys)
                ((vSlot, (FoTy.ctor tag nms bs).toShape) :: varSlots) sIn.locals := by
              refine .cons (by simp [sIn, FUPDATE]) hencPv ?_
              exact henv.congr (fun q hq => by
                obtain ⟨i, hi, hqEq⟩ := hvswf q hq
                have hne : q.1 ≠ vSlot := hqEq ▸ mkSlot_ne_of_lt hi
                simp [sIn, FUPDATE, hne])
            have hidleIn : JpsIdle jpSlots sIn.locals :=
              JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                 by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
            obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
              compileCode_sim tags body (.ctor tag fs :: env) (.ctor tag nms bs :: envTys)
                ((vSlot, (FoTy.ctor tag nms bs).toShape) :: varSlots)
                jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
            have hshVal : ((FoTy.ctor tag nms bs).toShape == shape_of pv) = true :=
              beq_iff_eq.mpr (encodeFoVal_shape hencPv).symm
            refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
              by simp only [evalFoBlock, evalFoLetVal]; rw [hfs]; simp [hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
              hpostB.after_dec_v hjpswf (fun idx hne => by
                have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                simp [sIn, FUPDATE, hneS])⟩
            simp only [compileCode, htIdx, Option.getD_some, hshCtor]
            rw [evaluate_dec, eval_rstruct, evalList_cons, eval_const, hpvs]
            dsimp only [sIn, pv, Option.map] at hevB ⊢
            rw [hshVal]
            simp only [↓reduceIte]
            rw [hevB]
      | natOp op l rArg =>
        simp only [inferLetValFoTy] at hty
        cases hlTy : inferArgFoTy envTys l with
        | none => simp [hlTy] at hty
        | some tyL =>
          rw [hlTy] at hty
          cases tyL with
          | ctor _ _ _ => simp at hty
          | one stL =>
            cases stL with
            | bool | erased => simp at hty
            | scalar b1 =>
              cases hrTy : inferArgFoTy envTys rArg with
              | none => simp [hrTy] at hty
              | some tyR =>
                rw [hrTy] at hty
                cases tyR with
                | ctor _ _ _ => simp at hty
                | one stR =>
                  cases stR with
                  | bool | erased => simp at hty
                  | scalar b2 =>
                    dsimp only at hty
                    cases hb12 : (decide (b1 < 2 ^ 64) && decide (b2 < 2 ^ 64)) with
        | false => simp [hb12] at hty
        | true =>
          simp only [hb12, ↓reduceIte] at hty
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb12
          obtain ⟨vl, pvl, hevl, hpvl, _, hencl⟩ := compileArg_sim henv hlTy
          obtain ⟨vr, pvr, hevr, hpvr, _, hencr⟩ := compileArg_sim henv hrTy
          cases pvl with
          | rstruct _ => simp [encodeFoVal] at hencl
          | word wl =>
            cases vl <;> simp [encodeFoVal, encodeScalar] at hencl
            rename_i nl
            rcases hencl with ⟨hnl, _, rfl⟩
            cases pvr with
            | rstruct _ => simp [encodeFoVal] at hencr
            | word wr =>
              cases vr <;> simp [encodeFoVal, encodeScalar] at hencr
              rename_i nr
              rcases hencr with ⟨hnr, _, rfl⟩
              have hnl64 : nl < 2 ^ 64 := by omega
              have hnr64 : nr < 2 ^ 64 := by omega
              cases op with
              | div | mod => simp at hty
              | sub =>
                simp only [Option.some.injEq] at hty
                subst hty
                let sZ := { s0 with locals := FUPDATE s0.locals (vSlot, .word 0#64) }
                have hlNe : eval sZ (compileArg varSlots l) = some (.word (BitVec.ofNat 64 nl)) := by
                  cases l with
                  | bvar idx =>
                    simp only [inferArgFoTy] at hlTy
                    obtain ⟨_, slot, _, _, hslotsGet, hlc, _⟩ := henv.lookup idx hlTy
                    obtain ⟨i, hi, hslotEq⟩ := hvswf.lookup hslotsGet
                    have hne : slot ≠ vSlot := hslotEq ▸ mkSlot_ne_of_lt hi
                    simpa [compileArg, hslotsGet, sZ, FUPDATE, hne, hlc] using hpvl
                  | _ => exact hpvl
                have hrNe : eval sZ (compileArg varSlots rArg) = some (.word (BitVec.ofNat 64 nr)) := by
                  cases rArg with
                  | bvar idx =>
                    simp only [inferArgFoTy] at hrTy
                    obtain ⟨_, slot, _, _, hslotsGet, hlc, _⟩ := henv.lookup idx hrTy
                    obtain ⟨i, hi, hslotEq⟩ := hvswf.lookup hslotsGet
                    have hne : slot ≠ vSlot := hslotEq ▸ mkSlot_ne_of_lt hi
                    simpa [compileArg, hslotsGet, sZ, FUPDATE, hne, hlc] using hpvr
                  | _ => exact hpvr
                let satSub := PStmt.ite (.cmp .Lower (compileArg varSlots l) (compileArg varSlots rArg))
                  .skip (.lassign vSlot (.binop .Sub [compileArg varSlots l, compileArg varSlots rArg]))
                have hSat : ∃ sSat : PanState θ,
                    evaluate satSub sZ = (.normal, sSat) ∧
                    sSat.clock = s0.clock ∧
                    StateWF sSat ∧
                    sSat.locals vSlot = some (.word (BitVec.ofNat 64 (nl - nr))) ∧
                    (∀ x, x ≠ vSlot → sSat.locals x = s0.locals x) := by
                  by_cases hltSub : nl < nr
                  · have hsub0 : nl - nr = 0 := by omega
                    have hcmp : word_cmp .Lower (BitVec.ofNat 64 nl) (BitVec.ofNat 64 nr) = true := by
                      simp [word_cmp, bv64_ult_ofNat hnl64 hnr64, hltSub]
                    refine ⟨sZ, ?_, rfl, ⟨hwf.1, hwf.2⟩, by simp [sZ, FUPDATE, hsub0],
                      fun x hne => by simp [sZ, FUPDATE, hne]⟩
                    simp only [satSub]
                    rw [evaluate_ite, eval_cmp, hlNe, hrNe]
                    dsimp only
                    rw [hcmp]
                    have ho : ((1#64 : Word) != 0#64) = true := by decide
                    simp only [ho, ↓reduceIte]
                    exact evaluate_skip sZ
                  · have hleSub : nr ≤ nl := by omega
                    have hcmp : word_cmp .Lower (BitVec.ofNat 64 nl) (BitVec.ofNat 64 nr) = false := by
                      simp [word_cmp, bv64_ult_ofNat hnl64 hnr64, hltSub]
                    have hvalidZ : is_valid_value sZ .Local vSlot (.word (BitVec.ofNat 64 nl - BitVec.ofNat 64 nr)) = true := by
                      simp [is_valid_value, lookup_kvar, sZ, FUPDATE]
                    let sSet := set_kvar .Local vSlot (.word (BitVec.ofNat 64 nl - BitVec.ofNat 64 nr)) sZ
                    refine ⟨sSet, ?_, rfl, ⟨hwf.1, hwf.2⟩,
                      by simp [sSet, set_kvar, set_var, FUPDATE, bv64_sub_ofNat hnl64 hleSub],
                      fun x hne => by simp [sSet, set_kvar, set_var, sZ, FUPDATE, hne]⟩
                    simp only [satSub]
                    rw [evaluate_ite, eval_cmp, hlNe, hrNe]
                    dsimp only
                    rw [hcmp]
                    have hz : ((0#64 : Word) != 0#64) = false := by decide
                    simp only [Bool.false_eq_true, ↓reduceIte, hz]
                    rw [evaluate_assign, eval_binop2, hlNe, hrNe]
                    dsimp only [word_op, Option.map]
                    rw [hvalidZ]
                    rfl
                obtain ⟨sSat, hevSat, hclkSat, hwfSat, hvSat, hotherSat⟩ := hSat
                have henvSat : EnvMatches tags (.scalar (nl - nr) :: env)
                    (FoTy.one (.scalar b1) :: envTys) ((vSlot, .One) :: varSlots) sSat.locals := by
                  refine .cons (ty := .one (.scalar b1)) hvSat ⟨by omega, hb12.1, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    exact hotherSat p.1 (hpEq ▸ mkSlot_ne_of_lt hi))
                have hidleSat : JpsIdle jpSlots sSat.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨hotherSat _ (mkSlot_h_ne_v i nextId),
                     hotherSat _ (mkSlot_a_ne_v i nextId)⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sim tags body (.scalar (nl - nr) :: env)
                    (FoTy.one (.scalar b1) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sSat hchk hwfSat
                    (by rw [hclkSat]; exact hclk) hvswf' hjpswf' henvSat hidleSat
                rw [hclkSat] at hclkB
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne =>
                    hotherSat _ (fun h => hne (mkSlot_inj h).2))⟩
                simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [evaluate_seq]
                dsimp only [sZ] at hevSat
                rw [hevSat]
                dsimp only
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [hevB]
              | add =>
                dsimp only at hty
                by_cases hbAdd : b1 + b2 < 2 ^ 64 <;> simp [hbAdd] at hty
                subst hty
                have haddLt : nl + nr < 2 ^ 64 := by omega
                let wOut := BitVec.ofNat 64 (nl + nr)
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.scalar (nl + nr) :: env)
                    (FoTy.one (.scalar (b1 + b2)) :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one (.scalar (b1 + b2)))
                    (by simp [sIn, FUPDATE]) ⟨by omega, hbAdd, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sim tags body (.scalar (nl + nr) :: env)
                    (FoTy.one (.scalar (b1 + b2)) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                have hwAdd : BitVec.ofNat 64 nl + (BitVec.ofNat 64 nr + 0#64) = wOut := by
                  rw [BitVec.add_zero, bv64_add_ofNat haddLt]
                rw [evaluate_dec, eval_binop2, hpvl, hpvr]
                dsimp only [sIn, wOut, word_op, List.foldr, Option.map] at hevB hwAdd ⊢
                rw [hwAdd]
                have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 (nl + nr)))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | mul =>
                dsimp only at hty
                by_cases hbMul : b1 * b2 < 2 ^ 64 <;> simp [hbMul] at hty
                subst hty
                have hmulLe : nl * nr ≤ b1 * b2 := Nat.mul_le_mul hnl hnr
                have hmulLt : nl * nr < 2 ^ 64 := by omega
                let wOut := BitVec.ofNat 64 (nl * nr)
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.scalar (nl * nr) :: env)
                    (FoTy.one (.scalar (b1 * b2)) :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one (.scalar (b1 * b2)))
                    (by simp [sIn, FUPDATE]) ⟨hmulLe, hbMul, rfl⟩ ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sim tags body (.scalar (nl * nr) :: env)
                    (FoTy.one (.scalar (b1 * b2)) :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_panop2, hpvl, hpvr]
                dsimp only [sIn, wOut, pan_op, Option.map] at hevB ⊢
                rw [bv64_mul_ofNat hnl64 hnr64 hmulLt]
                have hsh : (Shape.One == shape_of (.word (BitVec.ofNat 64 (nl * nr)))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | beq =>
                simp only [Option.some.injEq] at hty
                subst hty
                let bOut := (nl == nr)
                let wOut : Word := if bOut then 1#64 else 0#64
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one .bool)
                    (by simp [sIn, FUPDATE]) rfl ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sim tags body (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, bOut, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_cmp, hpvl, hpvr]
                dsimp only [sIn, wOut, bOut, word_cmp] at hevB ⊢
                simp only [bv64_beq_ofNat hnl64 hnr64]
                have hsh : (Shape.One == shape_of (.word (if (nl == nr) = true then 1#64 else 0#64))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
              | ble =>
                simp only [Option.some.injEq] at hty
                subst hty
                let bOut : Bool := (nl <= nr)
                let wOut : Word := if bOut then 1#64 else 0#64
                let sIn := { s0 with locals := FUPDATE s0.locals (vSlot, .word wOut) }
                have henvIn : EnvMatches tags (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots) sIn.locals := by
                  refine EnvMatches.cons (pv := .word wOut) (ty := .one .bool)
                    (by simp [sIn, FUPDATE]) rfl ?_
                  exact henv.congr (fun p hp => by
                    obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                    have hne : p.1 ≠ vSlot := hpEq ▸ mkSlot_ne_of_lt hi
                    simp [sIn, FUPDATE, hne])
                have hidleIn : JpsIdle jpSlots sIn.locals :=
                  JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
                    ⟨by simp [sIn, FUPDATE, vSlot, mkSlot_h_ne_v i nextId],
                     by simp [sIn, FUPDATE, vSlot, mkSlot_a_ne_v i nextId]⟩)
                obtain ⟨out, r, smid, hfoB, hevB, hclkB, hwfMid, hpostB⟩ :=
                  compileCode_sim tags body (.bool bOut :: env)
                    (FoTy.one .bool :: envTys) ((vSlot, .One) :: varSlots)
                    jpSigs jpSlots (nextId + 1) retBound sIn hchk ⟨hwf.1, hwf.2⟩ hclk hvswf' hjpswf' henvIn hidleIn
                have hbleEq : word_cmp .NotLower (BitVec.ofNat 64 nr) (BitVec.ofNat 64 nl) = bOut := by
                  simp only [word_cmp, bv64_ult_ofNat hnr64 hnl64, bOut]
                  by_cases h1 : nr < nl <;> by_cases h2 : nl ≤ nr <;> simp [h1, h2] <;> omega
                refine ⟨out, r, { smid with locals := res_var smid.locals (vSlot, s0.locals vSlot) },
                  by simp [evalFoBlock, evalFoLetVal, hevl, hevr, bOut, hfoB], ?_, hclkB, ⟨hwfMid.1, hwfMid.2⟩,
                  hpostB.after_dec_v hjpswf (fun idx hne => by
                    have hneS : mkSlot 'v' idx ≠ vSlot := fun h => hne (mkSlot_inj h).2
                    simp [sIn, FUPDATE, hneS])⟩
                simp only [compileCode, compileFastNatOp]
                rw [evaluate_dec, eval_cmp, hpvr, hpvl]
                dsimp only [sIn, wOut] at hevB ⊢
                simp only [hbleEq]
                have hsh : (Shape.One == shape_of (.word (if bOut = true then 1#64 else 0#64))) = true := rfl
                simp only [hsh, ↓reduceIte]
                rw [hevB]
  | .ifBool cond t fls, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hcTy : inferArgFoTy envTys cond with
    | none => simp [hcTy] at hchk
    | some tyC =>
      rw [hcTy] at hchk
      cases tyC with
      | ctor _ _ _ => simp at hchk
      | one stC =>
        cases stC <;> simp at hchk
        cases ht : checkFoCode tags envTys jpSigs t <;>
          cases hf : checkFoCode tags envTys jpSigs fls <;> simp [ht, hf] at hchk
        rename_i bt bf
        subst hchk
        have hbtLt := (checkFoCode_bound_lt tags t envTys jpSigs bt ht).1
        have hbfLt := (checkFoCode_bound_lt tags fls envTys jpSigs bf hf).1
        have hmaxLt : max bt bf < 2 ^ 64 := by omega
        obtain ⟨vc, pvc, hevc, hpvc, _, hencc⟩ := compileArg_sim henv hcTy
        cases pvc with
        | rstruct _ => simp [encodeFoVal] at hencc
        | word wc =>
          cases vc <;> simp [encodeFoVal, encodeScalar] at hencc
          rename_i bv
          subst hencc
          simp only [synthLcnfClk] at hclk
          cases bv with
          | true =>
            obtain ⟨out, r, s1, hfoT, hevT, hclkT, hwf1, hpostT⟩ :=
              compileCode_sim tags t env envTys varSlots jpSigs jpSlots nextId bt s0
                ht hwf (by omega) hvswf hjpswf henv hidle
            refine ⟨out, r, s1, by simp [evalFoBlock, hevc, hfoT], ?_,
              by simp only [synthLcnfClk]; omega, hwf1,
              hpostT.widen_bound (by omega) hmaxLt⟩
            simp only [compileCode]
            rw [evaluate_ite, hpvc]
            dsimp only
            have ho : ((1#64 : Word) != 0#64) = true := by decide
            simp only [ho, ↓reduceIte]
            exact hevT
          | false =>
            let id1 := (compileCode tags varSlots jpSlots nextId t).2
            have hid1 : nextId ≤ id1 := (compileCode_clk_and_mono tags t varSlots jpSlots nextId).2
            obtain ⟨out, r, s1, hfoF, hevF, hclkF, hwf1, hpostF⟩ :=
              compileCode_sim tags fls env envTys varSlots jpSigs jpSlots id1 bf s0
                hf hwf (by omega) (hvswf.mono hid1) (hjpswf.mono hid1) henv hidle
            refine ⟨out, r, s1, by simp [evalFoBlock, hevc, hfoF], ?_,
              by simp only [synthLcnfClk]; omega, hwf1,
              hpostF.widen_bound (by omega) hmaxLt⟩
            simp only [compileCode]
            rw [evaluate_ite, hpvc]
            dsimp only
            have hz : ((0#64 : Word) != 0#64) = false := by decide
            simp only [hz, Bool.false_eq_true, ↓reduceIte]
            exact hevF
  | .cases scrut arms, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases scrut with
    | lit _ | boolLit _ | erased | stateTok _ => simp at hchk
    | bvar idx =>
      cases hsTy : inferArgFoTy envTys (.bvar idx) with
      | none => simp [hsTy] at hchk
      | some tyS =>
        rw [hsTy] at hchk
        cases tyS with
        | one _ => simp at hchk
        | ctor cTag cNames cBounds =>
          dsimp only at hchk
          cases hcond : (checkArmTagsValid tags arms && foPureArms arms) with
          | false => simp [hcond] at hchk
          | true =>
            simp only [hcond, ↓reduceIte] at hchk
            simp only [Bool.and_eq_true] at hcond
            rw [checkFoArm_eq_find] at hchk
            cases hfind : arms.find? (fun a => a.1 == cTag) with
            | none => simp [hfind] at hchk
            | some arm =>
              rw [hfind] at hchk
              obtain ⟨mTag, armNames, mBody⟩ := arm
              dsimp only at hchk
              cases hnames : (armNames == cNames) with
              | false => simp [hnames] at hchk
              | true =>
                simp only [hnames, ↓reduceIte] at hchk
                have hnamesEq : armNames = cNames := beq_iff_eq.mp hnames
                subst armNames
                simp only [inferArgFoTy] at hsTy
                obtain ⟨vScrut, scrutSlot, pvScrut, henvGet, hslotsGet, hlcScrut, hencScrut⟩ :=
                  henv.lookup idx hsTy
                obtain ⟨si, hsiLt, hsiSlot⟩ := hvswf.lookup hslotsGet
                cases vScrut <;> try cases hencScrut
                rename_i rTag fs
                cases pvScrut with
                | word _ => cases hencScrut
                | rstruct rvs =>
                  cases rvs with
                  | nil => cases hencScrut
                  | cons rv0 pvs =>
                    cases rv0 with
                    | rstruct _ => cases hencScrut
                    | word wTag =>
                      obtain ⟨htagEq, cIdx, hcIdx, hcIdxLt, rfl, hrel⟩ := hencScrut
                      subst rTag
                      have heScrut : compileArg varSlots (.bvar idx) = .lvar scrutSlot := by
                        simp [compileArg, hslotsGet]
                      have hspEq : splitValues fs cNames = some (fs.map Prod.snd) :=
                        ctorFieldsRel_splitValues hrel
                      simp only [synthLcnfClk] at hclk
                      obtain ⟨out, r, s1, hfoM, hevArms, hclkArms, hwf1, hpostArms⟩ :=
                        compileArms_sim tags arms scrutSlot si hsiSlot cTag cIdx cNames cBounds
                          fs pvs mTag mBody env envTys varSlots jpSigs jpSlots nextId retBound s0
                          hsiLt hcIdx hcIdxLt hrel hcond.1 hfind hchk hwf hclk hvswf hjpswf henv hidle hlcScrut
                      refine ⟨out, r, s1, ?_, ?_, hclkArms, hwf1, hpostArms⟩
                      · simp [evalFoBlock, evalLcnfArgVal, henvGet, evalFoArm_eq_find, hfind, hspEq, hfoM]
                      · simp only [compileCode, heScrut]
                        exact hevArms
  | .jpDecl jpId numParams jpBody body, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hchk, hwf, hclk, hvswf, hjpswf, henv, hidle => by
    simp only [checkFoCode] at hchk
    cases hany : jpSigs.any (fun s => s.jpId == jpId) with
    | true => simp [hany] at hchk
    | false =>
      simp only [hany, Bool.false_eq_true, ↓reduceIte] at hchk
      cases hinf : inferJpParams tags jpId numParams envTys body with
      | none => simp [hinf] at hchk
      | some optParams =>
        rw [hinf] at hchk
        dsimp only at hchk
        let paramTys := optParams.getD (List.replicate numParams (.scalar 0))
        cases hpcond : (paramTys.length == numParams && paramTys.all FoScalarTy.wf) with
        | false => simp [paramTys, hpcond] at hchk
        | true =>
          change (if (paramTys.length == numParams && paramTys.all FoScalarTy.wf) = true then _ else none) = some retBound at hchk
          simp only [hpcond, ↓reduceIte] at hchk
          simp only [Bool.and_eq_true, beq_iff_eq] at hpcond
          have hboth : ∃ bBody bJp,
              checkFoCode tags envTys (⟨jpId, paramTys⟩ :: jpSigs) body = some bBody ∧
              checkFoCode tags (paramTys.map FoTy.one ++ envTys) jpSigs jpBody = some bJp ∧
              max bBody bJp = retBound := by
            dsimp only [paramTys]
            cases h1 : checkFoCode tags envTys (⟨jpId, optParams.getD (List.replicate numParams (.scalar 0))⟩ :: jpSigs) body with
            | none => rw [h1] at hchk; cases hchk
            | some bBody =>
              cases h2 : checkFoCode tags ((optParams.getD (List.replicate numParams (.scalar 0))).map FoTy.one ++ envTys) jpSigs jpBody with
              | none => rw [h1, h2] at hchk; cases hchk
              | some bJp =>
                rw [h1, h2] at hchk
                exact ⟨bBody, bJp, rfl, rfl, Option.some.inj hchk⟩
          obtain ⟨bBody, bJp, hb1, hb2, hretEq⟩ := hboth
          subst hretEq
          have hbBodyLt := (checkFoCode_bound_lt tags body _ _ bBody hb1).1
          have hbJpLt := (checkFoCode_bound_lt tags jpBody _ _ bJp hb2).1
          have hmaxLt : max bBody bJp < 2 ^ 64 := by omega
          simp only [synthLcnfClk] at hclk
          let hitSlot := mkSlot 'h' nextId
          let argSlots := mkFreshSlots 'a' (nextId + 1) numParams
          let nextId1 := nextId + 1 + numParams
          let cj : CompiledJp := ⟨jpId, numParams, hitSlot, argSlots⟩
          have hnotMem : jpId ∉ jpSigs.map JpSig.jpId := by
            intro hm
            rcases List.mem_map.mp hm with ⟨s, hs, rfl⟩
            have : jpSigs.any (fun x => x.jpId == s.jpId) = true :=
              List.any_eq_true.mpr ⟨s, hs, beq_self_eq_true _⟩
            rw [hany] at this; cases this
          have hjpswfBody : JpStackWF nextId1 (⟨jpId, paramTys⟩ :: jpSigs) (cj :: jpSlots) := by
            have hcjEq : cj = ⟨jpId, paramTys.length, mkSlot 'h' nextId, mkFreshSlots 'a' (nextId + 1) paramTys.length⟩ := by
              simp [cj, hitSlot, argSlots, hpcond.1]
            rw [hcjEq]
            exact .cons hjpswf hnotMem (by simp [nextId1, hpcond.1])
          let sHit0 : PanState θ := { s0 with locals := FUPDATE s0.locals (hitSlot, .word 0#64) }
          let cBody := (compileCode tags varSlots (cj :: jpSlots) nextId1 body).1
          let nextId2 := (compileCode tags varSlots (cj :: jpSlots) nextId1 body).2
          have hmonoBody : nextId1 ≤ nextId2 :=
            (compileCode_clk_and_mono tags body varSlots (cj :: jpSlots) nextId1).2
          let pSlots := mkFreshSlots 'v' nextId2 numParams
          let jpVarSlots := (pSlots.map (fun s => (s, Shape.One))) ++ varSlots
          let cJpBody := (compileCode tags jpVarSlots jpSlots (nextId2 + numParams) jpBody).1
          let tailIf := PStmt.ite (.lvar hitSlot) (bindJpParams pSlots argSlots cJpBody) .skip
          obtain ⟨sInner, hclkIn0, hwfInFn, hbndArgsIn, hpresArgsIn, sOutWrap, hevWrap, hclkWrap, hwfWrapFn, hpresArgsOut⟩ :=
            evaluate_wrapDecZeros (nextId + 1) numParams (.seq cBody tailIf) sHit0
          have hclkIn : sInner.clock = s0.clock := hclkIn0
          have hwfIn : StateWF sInner := hwfInFn ⟨hwf.1, hwf.2⟩
          have hsInnerNonFrame : ∀ x, x ≠ hitSlot →
              (∀ j, nextId + 1 ≤ j → j < nextId + 1 + numParams → x ≠ mkSlot 'a' j) →
              sInner.locals x = s0.locals x := by
            intro x hneH hneA
            rw [hpresArgsIn x hneA]
            simp [sHit0, FUPDATE, hneH]
          have henvIn : EnvMatches tags env envTys varSlots sInner.locals :=
            henv.congr (fun p hp => by
              obtain ⟨i, _, hpEq⟩ := hvswf p hp
              exact hsInnerNonFrame p.1
                (hpEq ▸ mkSlot_ne_of_kind (by decide) i nextId)
                (fun j _ _ => hpEq ▸ mkSlot_ne_of_kind (by decide) i j))
          have hidleIn : JpsIdle (cj :: jpSlots) sInner.locals := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | htl
            · refine ⟨?_, fun a ha => ⟨0#64, hbndArgsIn a ha⟩⟩
              rw [hpresArgsIn hitSlot (fun j _ _ => mkSlot_ne_of_kind (by decide) nextId j)]
              simp [sHit0, FUPDATE]
            · refine JpsIdle.congr_of_wf hjpswf hidle (fun i hi => ⟨?_, ?_⟩) c htl
              · exact hsInnerNonFrame _ (mkSlot_ne_of_lt hi) (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)
              · exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) i nextId) (fun j hj1 _ => mkSlot_ne_of_lt (by omega))
          obtain ⟨outB, rB, sMidB, hfoB, hevB, hclkB, hwfMidB, hpostB⟩ :=
            compileCode_sim tags body env envTys varSlots (⟨jpId, paramTys⟩ :: jpSigs) (cj :: jpSlots)
              nextId1 bBody sInner hb1 hwfIn (by rw [hclkIn]; omega)
              (hvswf.mono (by omega)) hjpswfBody henvIn hidleIn
          rw [hclkIn] at hclkB
          -- Case-analyze `outB` (`returned` vs `jumped`)
          cases outB with
          | returned rv =>
            obtain ⟨n, rfl, hnLe, _, hrB⟩ := hpostB
            subst hrB
            have hevSeq : evaluate (.seq cBody tailIf) sInner = (.ret (.word (BitVec.ofNat 64 n)), sMidB) := by
              rw [evaluate_seq, hevB]; rfl
            let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
            refine ⟨.returned (.scalar n), .ret (.word (BitVec.ofNat 64 n)), sFinal,
              by simp [evalFoBlock, hfoB], ?_, ?_, ?_, ⟨n, rfl, by omega, hmaxLt, rfl⟩⟩
            · simp only [compileCode]
              rw [evaluate_dec, eval_const]
              dsimp only
              have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
              simp only [hsh, ↓reduceIte]
              dsimp only [argSlots, sHit0, hitSlot] at hevWrap
              rw [hevWrap, hevSeq]
            · simp only [sFinal, synthLcnfClk]; rw [hclkWrap, hevSeq]; dsimp only; omega
            · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfMidB)
              exact ⟨hw1.1, hw1.2⟩
          | jumped tid argVals =>
            obtain ⟨hrB, htrigB, hvPresB⟩ := hpostB
            subst hrB
            cases htrigB with
            | here hidEq hhitMid hrelMid hidleMid =>
              dsimp only at hidEq
              subst hidEq
              have hlenArgs : argVals.length = numParams :=
                hrelMid.length_eq.trans hpcond.1
              have hrelMid' : ScalarSlotsRel argVals paramTys (mkFreshSlots 'a' (nextId + 1) paramTys.length) sMidB.locals := by
                simpa [cj, argSlots, hpcond.1] using hrelMid
              obtain ⟨sJpIn, hclkJpIn, hwfJpIn, hpresJpIn, hliftJpEnv, sOutBind, hevBind, hclkBind, hwfBindFn, hvBindOut, hnonVBindOut⟩ :=
                evaluate_bindJpParams_raw tags nextId2 (nextId + 1) argVals paramTys cJpBody sMidB hwfMidB hrelMid'
              have henvMid : EnvMatches tags env envTys varSlots sJpIn.locals :=
                henv.congr (fun p hp => by
                  obtain ⟨i, hi, hpEq⟩ := hvswf p hp
                  have h1 : sJpIn.locals p.1 = sMidB.locals p.1 :=
                    hpresJpIn p.1 (fun j hj1 _ => hpEq ▸ mkSlot_ne_of_lt (by omega))
                  have h2 : sMidB.locals p.1 = sInner.locals p.1 := hpEq ▸ hvPresB i
                  have h3 : sInner.locals p.1 = s0.locals p.1 :=
                    hsInnerNonFrame p.1
                      (hpEq ▸ mkSlot_ne_of_kind (by decide) i nextId)
                      (fun j _ _ => hpEq ▸ mkSlot_ne_of_kind (by decide) i j)
                  exact h1.trans (h2.trans h3))
              have henvJp : EnvMatches tags (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
                  jpVarSlots sJpIn.locals := by
                have hpEq : pSlots = mkFreshSlots 'v' nextId2 paramTys.length := by simp [pSlots, hpcond.1]
                simpa [jpVarSlots, hpEq] using hliftJpEnv env envTys varSlots henvMid
              have hvswfJp : VarSlotsWF (nextId2 + numParams) jpVarSlots := by
                intro p hp
                rcases List.mem_append.mp hp with hp1 | hp2
                · rcases List.mem_map.mp hp1 with ⟨nm, hnm, rfl⟩
                  obtain ⟨j, _, hj2, rfl⟩ := mem_mkFreshSlots hnm
                  exact ⟨j, hj2, rfl⟩
                · exact (hvswf.mono (by omega)) p hp2
              have hidleJp : JpsIdle jpSlots sJpIn.locals :=
                JpsIdle.congr_of_wf hjpswf hidleMid (fun i _ =>
                  ⟨hpresJpIn _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j),
                   hpresJpIn _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)⟩)
              obtain ⟨outJ, rJ, sMidJ, hfoJ, hevJ, hclkJ, hwfMidJ, hpostJ⟩ :=
                compileCode_sim tags jpBody (argVals ++ env) (paramTys.map FoTy.one ++ envTys)
                  jpVarSlots jpSigs jpSlots (nextId2 + numParams) bJp sJpIn
                  hb2 hwfJpIn (by rw [hclkJpIn]; omega) hvswfJp (hjpswf.mono (by omega)) henvJp hidleJp
              rw [hclkJpIn] at hclkJ
              have hevBind' : evaluate (bindJpParams pSlots argSlots cJpBody) sMidB = (rJ, sOutBind) := by
                have hpEq : pSlots = mkFreshSlots 'v' nextId2 paramTys.length := by simp [pSlots, hpcond.1]
                have haEq : argSlots = mkFreshSlots 'a' (nextId + 1) paramTys.length := by simp [argSlots, hpcond.1]
                rw [hpEq, haEq, hevBind, hevJ]
              have hevSeq : evaluate (.seq cBody tailIf) sInner = (rJ, sOutBind) := by
                rw [evaluate_seq, hevB]
                dsimp only [tailIf]
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [evaluate_ite, eval_lvar]
                have hh1 : sMidB.locals hitSlot = some (.word 1#64) := hhitMid
                rw [hh1]
                dsimp only
                have hnz : ((1#64 : Word) != 0#64) = true := by decide
                simp only [hnz, ↓reduceIte]
                exact hevBind'
              let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
              refine ⟨outJ, rJ, sFinal,
                by simp [evalFoBlock, hfoB, hlenArgs, hfoJ], ?_, ?_, ?_, ?_⟩
              · simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                dsimp only [argSlots, sHit0, hitSlot] at hevWrap
                rw [hevWrap, hevSeq]
              · simp only [sFinal, synthLcnfClk]
                rw [hclkWrap, hevSeq]; dsimp only
                rw [hclkBind, hevJ]; dsimp only at hclkJ ⊢
                omega
              · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfBindFn (by rw [hevJ]; exact hwfMidJ))
                exact ⟨hw1.1, hw1.2⟩
              · cases outJ with
                | returned rv =>
                  obtain ⟨n, rfl, hnLe, _, hrJ⟩ := hpostJ
                  exact ⟨n, rfl, by omega, hmaxLt, hrJ⟩
                | jumped tid2 argVals2 =>
                  obtain ⟨hrJ, htrigJ, hvPresJ⟩ := hpostJ
                  refine ⟨hrJ, ?_, ?_⟩
                  · refine JpTriggered.congr_of_wf hjpswf htrigJ (fun i hi => ⟨?_, ?_⟩)
                    · simp only [sFinal]
                      rw [res_var_ne _ _ _ _ (mkSlot_ne_of_lt hi)]
                      rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)]
                      rw [hevSeq]; dsimp only
                      rw [hnonVBindOut _ (fun c => mkSlot_ne_of_kind (by decide) i c)]
                      rw [hevJ]
                    · simp only [sFinal]
                      rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) i nextId)]
                      rw [hpresArgsOut _ (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                      rw [hevSeq]; dsimp only
                      rw [hnonVBindOut _ (fun c => mkSlot_ne_of_kind (by decide) i c)]
                      rw [hevJ]
                  · intro idx
                    simp only [sFinal]
                    rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) idx nextId)]
                    rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)]
                    rw [hevSeq]; dsimp only
                    have hvMid : sOutBind.locals (mkSlot 'v' idx) = sMidB.locals (mkSlot 'v' idx) :=
                      hvBindOut (by rw [hevJ]; exact hvPresJ) idx
                    rw [hvMid, hvPresB idx]
                    exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) idx nextId)
                      (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)
            | there hneId hhitMid _ htrigOuter =>
              dsimp only at hneId
              have htidFalse : (tid == jpId) = false :=
                beq_eq_false_iff_ne.mpr (fun h => hneId h.symm)
              have hevSeq : evaluate (.seq cBody tailIf) sInner = (.normal, sMidB) := by
                rw [evaluate_seq, hevB]
                dsimp only [tailIf]
                simp only [beq_self_eq_true, ↓reduceIte]
                rw [evaluate_ite, eval_lvar]
                have hh0 : sMidB.locals hitSlot = some (.word 0#64) := hhitMid
                rw [hh0]
                dsimp only
                have hz : ((0#64 : Word) != 0#64) = false := by decide
                simp only [hz, Bool.false_eq_true, ↓reduceIte]
                exact evaluate_skip sMidB
              let sFinal := { sOutWrap with locals := res_var sOutWrap.locals (hitSlot, s0.locals hitSlot) }
              refine ⟨.jumped tid argVals, .normal, sFinal,
                by simp [evalFoBlock, hfoB, htidFalse], ?_, ?_, ?_, ⟨rfl, ?_, ?_⟩⟩
              · simp only [compileCode]
                rw [evaluate_dec, eval_const]
                dsimp only
                have hsh : (Shape.One == shape_of (.word 0#64)) = true := rfl
                simp only [hsh, ↓reduceIte]
                dsimp only [argSlots, sHit0, hitSlot] at hevWrap
                rw [hevWrap, hevSeq]
              · simp only [sFinal, synthLcnfClk]
                rw [hclkWrap, hevSeq]; dsimp only
                omega
              · have hw1 := hwfWrapFn (by rw [hevSeq]; exact hwfMidB)
                exact ⟨hw1.1, hw1.2⟩
              · refine JpTriggered.congr_of_wf hjpswf htrigOuter (fun i hi => ⟨?_, ?_⟩)
                · simp only [sFinal]
                  rw [res_var_ne _ _ _ _ (mkSlot_ne_of_lt hi)]
                  rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) i j)]
                  rw [hevSeq]
                · simp only [sFinal]
                  rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) i nextId)]
                  rw [hpresArgsOut _ (fun j hj1 _ => mkSlot_ne_of_lt (by omega))]
                  rw [hevSeq]
              · intro idx
                simp only [sFinal]
                rw [res_var_ne _ _ _ _ (mkSlot_ne_of_kind (by decide) idx nextId)]
                rw [hpresArgsOut _ (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)]
                rw [hevSeq]; dsimp only
                rw [hvPresB idx]
                exact hsInnerNonFrame _ (mkSlot_ne_of_kind (by decide) idx nextId)
                  (fun j _ _ => mkSlot_ne_of_kind (by decide) idx j)
termination_by structural c => c

private theorem compileArms_sim {θ : Type} (tags : List String) :
    ∀ (arms : List (String × List String × LcnfCode))
      (scrutSlot : String) (si : Nat) (_ : scrutSlot = mkSlot 'v' si)
      (cTag : String) (cIdx : Nat) (cNames : List String) (cBounds : List Nat)
      (fs : List (String × LcnfVal)) (pvs : List PanVal)
      (mTag : String) (mBody : LcnfCode)
      (env : List LcnfVal) (envTys : List FoTy) (varSlots : List (String × Shape))
      (jpSigs : List JpSig) (jpSlots : List CompiledJp) (nextId retBound : Nat) (s0 : PanState θ),
      si < nextId →
      lookupTagIdx tags cTag = some cIdx →
      cIdx < 2 ^ 64 →
      CtorFieldsRel fs cNames cBounds pvs →
      checkArmTagsValid tags arms = true →
      arms.find? (fun a => a.1 == cTag) = some (mTag, cNames, mBody) →
      checkFoCode tags ((cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys) jpSigs mBody = some retBound →
      StateWF s0 →
      synthArmsClk arms ≤ s0.clock →
      VarSlotsWF nextId varSlots →
      JpStackWF nextId jpSigs jpSlots →
      EnvMatches tags env envTys varSlots s0.locals →
      JpsIdle jpSlots s0.locals →
      s0.locals scrutSlot = some (.rstruct (.word (BitVec.ofNat 64 cIdx) :: pvs)) →
      ∃ out r s1,
        evalFoBlock ((fs.map Prod.snd).reverse ++ env) mBody = some out ∧
        evaluate (compileArms tags (.lvar scrutSlot) varSlots jpSlots nextId arms).1 s0 = (r, s1) ∧
        s0.clock ≤ s1.clock + synthArmsClk arms ∧
        StateWF s1 ∧
        BlockPost retBound jpSigs jpSlots s0 out r s1
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfind, _, _, _, _, _, _, _, _ => by
    simp at hfind
  | (armTag, fieldNames, armBody) :: rest, scrutSlot, si, hsiSlot, cTag, cIdx, cNames, cBounds,
      fs, pvs, mTag, mBody, env, envTys, varSlots, jpSigs, jpSlots, nextId, retBound, s0,
      hsiLt, hcIdx, hcIdxLt, hrel, htagsValid, hfind, hchkM, hwf, hclk, hvswf, hjpswf, henv, hidle, hscrut => by
    simp only [checkArmTagsValid, Bool.and_eq_true] at htagsValid
    cases htIdx : lookupTagIdx tags armTag with
    | none => simp [htIdx] at htagsValid
    | some tIdx =>
      rw [htIdx] at htagsValid
      simp only [decide_eq_true_eq] at htagsValid
      simp only [List.find?] at hfind
      simp only [synthArmsClk] at hclk
      cases heqTag : (armTag == cTag) with
      | true =>
        rw [heqTag] at hfind
        simp only [Option.some.injEq, Prod.mk.injEq] at hfind
        rcases hfind with ⟨hmTagEq, hfnEq, hmEq⟩
        subst mTag
        subst fieldNames
        subst mBody
        have htagEq : armTag = cTag := beq_iff_eq.mp heqTag
        subst armTag
        have htEq : tIdx = cIdx := by
          rw [hcIdx] at htIdx; exact Option.some.inj htIdx.symm
        subst tIdx
        let k := cNames.length
        let fSlots := mkFreshSlots 'v' nextId k
        let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
        let cArm := (compileCode tags armVarSlots jpSlots (nextId + k) armBody).1
        obtain ⟨sInner, hclkIn, hwfIn, hvswfIn, henvIn, hnonVIn, sOut, hevBind, hclkOut, hwfOutFn, hvOut, hnonVOut⟩ :=
          evaluate_bindCtorFields tags hsiSlot nextId 1 hrel env envTys varSlots cArm s0
            hsiLt hwf hscrut (fun j _ => by simp [Nat.add_comm 1 j]) hvswf henv
        have hidleIn : JpsIdle jpSlots sInner.locals :=
          JpsIdle.congr_of_wf hjpswf hidle (fun i _ =>
            ⟨hnonVIn _ (fun c => mkSlot_h_ne_v i c),
             hnonVIn _ (fun c => mkSlot_a_ne_v i c)⟩)
        obtain ⟨out, r, smid, hfoM, hevM, hclkM, hwfMid, hpostM⟩ :=
          compileCode_sim tags armBody ((fs.map Prod.snd).reverse ++ env)
            ((cBounds.reverse.map (fun b => FoTy.one (.scalar b))) ++ envTys)
            armVarSlots jpSigs jpSlots (nextId + k) retBound sInner
            hchkM hwfIn (by rw [hclkIn]; omega) hvswfIn (hjpswf.mono (by omega)) henvIn hidleIn
        rw [hclkIn] at hclkM
        refine ⟨out, r, sOut, hfoM, ?_, ?_, hwfOutFn (by rw [hevM]; exact hwfMid), ?_⟩
        · simp only [compileArms, htIdx, Option.getD_some]
          rw [evaluate_ite, eval_cmp, eval_rfield, eval_lvar, eval_const, hscrut]
          dsimp only
          simp only [List.getElem?_cons_zero, word_cmp, beq_self_eq_true, ↓reduceIte]
          have hnz : ((1#64 : Word) != 0#64) = true := by decide
          simp only [hnz, ↓reduceIte]
          dsimp only [fSlots, k, cArm] at hevBind ⊢
          rw [hevBind, hevM]
        · simp only [synthArmsClk]; rw [hclkOut, hevM]; dsimp only; omega
        · cases out with
          | returned rv =>
            rw [hevM] at hevBind
            exact hpostM
          | jumped tid argVals =>
            obtain ⟨hrM, htrigM, hvPresM⟩ := hpostM
            refine ⟨hrM, ?_, ?_⟩
            · refine JpTriggered.congr_of_wf hjpswf htrigM (fun i _ => ⟨?_, ?_⟩)
              · rw [hnonVOut _ (fun c => mkSlot_h_ne_v i c), hevM]
              · rw [hnonVOut _ (fun c => mkSlot_a_ne_v i c), hevM]
            · exact hvOut (by rw [hevM]; exact hvPresM)
      | false =>
        rw [heqTag] at hfind
        have hidxNe : cIdx ≠ tIdx := fun h => by
          subst h
          have := lookupTagIdx_inj htIdx hcIdx
          exact absurd (beq_iff_eq.mpr this) (by simp [heqTag])
        have hbvFalse : (BitVec.ofNat 64 cIdx == BitVec.ofNat 64 tIdx) = false := by
          rw [bv64_beq_ofNat hcIdxLt htagsValid.1]
          exact beq_eq_false_iff_ne.mpr hidxNe
        let k := fieldNames.length
        let fSlots := mkFreshSlots 'v' nextId k
        let armVarSlots := (fSlots.reverse.map (fun s => (s, Shape.One))) ++ varSlots
        let id1 := (compileCode tags armVarSlots jpSlots (nextId + k) armBody).2
        have hid1 : nextId + k ≤ id1 :=
          (compileCode_clk_and_mono tags armBody armVarSlots jpSlots (nextId + k)).2
        obtain ⟨out, r, s1, hfoM, hevRest, hclkRest, hwf1, hpostRest⟩ :=
          compileArms_sim tags rest scrutSlot si hsiSlot cTag cIdx cNames cBounds
            fs pvs mTag mBody env envTys varSlots jpSigs jpSlots id1 retBound s0
            (by omega) hcIdx hcIdxLt hrel htagsValid.2 hfind hchkM hwf (by omega)
            (hvswf.mono (by omega)) (hjpswf.mono (by omega)) henv hidle hscrut
        refine ⟨out, r, s1, hfoM, ?_, by simp only [synthArmsClk]; omega, hwf1, hpostRest⟩
        simp only [compileArms, htIdx, Option.getD_some]
        rw [evaluate_ite, eval_cmp, eval_rfield, eval_lvar, eval_const, hscrut]
        dsimp only
        simp only [List.getElem?_cons_zero, word_cmp, hbvFalse, Bool.false_eq_true, ↓reduceIte]
        have hz : ((0#64 : Word) != 0#64) = false := by decide
        simp only [hz, Bool.false_eq_true, ↓reduceIte]
        exact hevRest
termination_by structural arms => arms
end

/-! ## 7. Exported End-to-End Correctness, `Core4` Weld & Multi-Turn Batch Theorems -/

/-- Closed-program totality + tight `RefinesClkTight` theorem for `compileLcnfToPancake`. -/
theorem compileLcnfToPancake_tight {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      n ≤ retBound ∧
      retBound < 2 ^ 64 ∧
      (∀ fuel, minLcnfFuel c ≤ fuel → evalLcnfCode fuel [] [] [] c = some (n, [])) ∧
      RefinesClkTight (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun _ r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  simp only [checkFoLcnf] at hchk
  split at hchk <;> try simp at hchk
  obtain ⟨hboundLt, hpure⟩ := checkFoCode_bound_lt (collectTags c) c [] [] retBound hchk
  -- Extract canonical `n` by running `compileCode_sim` on `emptyPanState () (synthLcnfClk c)`
  let sDummy := emptyPanState () (synthLcnfClk c)
  have hvswf0 : VarSlotsWF 0 [] := fun _ h => by cases h
  have hidle0 : JpsIdle [] sDummy.locals := fun _ h => by cases h
  obtain ⟨out0, r0, _, hfo0, _, _, _, hpost0⟩ :=
    compileCode_sim (collectTags c) c [] [] [] [] [] 0 retBound sDummy
      hchk (emptyPanState_wf () _) (Nat.le_refl _) hvswf0 (.nil 0) (.nil _) hidle0
  cases out0 with
  | jumped _ _ => cases hpost0.2.1
  | returned rv =>
    obtain ⟨n, rfl, hnLe, _, _⟩ := hpost0
    refine ⟨n, hnLe, hboundLt, ?_, ?_⟩
    · intro fuel hfuel
      have hevVal := evalFoBlock_implies_evalLcnfCodeVal fuel c [] [] [] (.returned (.scalar n))
        (.scalar n) hpure .nil hfo0 rfl (by simpa [jpsFuel] using hfuel)
      simp [evalLcnfCode, hevVal, LcnfVal.toNat?]
    · intro s0 ⟨hwf0, _⟩ hclk0
      have hidleS0 : JpsIdle [] s0.locals := fun _ h => by cases h
      obtain ⟨out, r, s1, hfo, hev, hclk1, hwf1, hpost⟩ :=
        compileCode_sim (collectTags c) c [] [] [] [] [] 0 retBound s0
          hchk hwf0 hclk0 hvswf0 (.nil 0) (.nil _) hidleS0
      rw [hfo0] at hfo
      injection hfo with houtEq
      subst houtEq
      obtain ⟨n', hscEq, _, _, hrEq⟩ := hpost
      injection hscEq with hnEq
      subst hnEq
      subst hrEq
      exact ⟨.ret (.word (BitVec.ofNat 64 n)), s1, hev, PanResult.noConfusion, PanResult.noConfusion, hclk1, ⟨hwf1, rfl⟩⟩

/-- **Primary `G6` Theorem (`compileLcnfToPancake_correct`)**:
    Every well-typed first-order `LcnfCode` term `c` evaluates in `evalLcnfCode` to a `< 2^64`
    scalar `n` AND executes in `PanSem.evaluate` under synthesized `CondSClk` fuel `synthLcnfClk c`
    with `0` `TimeOut` and `0` `Error` (`RefinesClkPan`) to `.ret (.word (BitVec.ofNat 64 n))`. -/
theorem compileLcnfToPancake_correct {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      n ≤ retBound ∧
      retBound < 2 ^ 64 ∧
      evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) ∧
      synthStmtClk (compileLcnfToPancake c) = some (synthLcnfClk c) ∧
      RefinesClkPan (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  obtain ⟨n, hn, hlt, hfuel, htight⟩ := compileLcnfToPancake_tight (θ := θ) c retBound hchk
  exact ⟨n, hn, hlt, hfuel (minLcnfFuel c) (Nat.le_refl _),
    synthStmtClk_compileLcnfToPancake c, htight.toRefinesClkPan⟩

/-- **Joint Premise Inhabitation for `compileLcnfToPancake_correct`**:
    For every `ffiInit : θ` and `c : LcnfCode`, there exists a concrete `s0 : PanState θ`
    satisfying both `EntryWF (fun _ => True) s0` and `s0.clock ≥ synthLcnfClk c`. -/
theorem compileLcnfToPancake_premises_inhabited {θ : Type} (ffiInit : θ) (c : LcnfCode) :
    ∃ s0 : PanState θ, EntryWF (fun _ => True) s0 ∧ s0.clock ≥ synthLcnfClk c :=
  ⟨emptyPanState ffiInit (synthLcnfClk c), ⟨emptyPanState_wf ffiInit _, trivial⟩, Nat.le_refl _⟩

/-- **Cross-Backend `Pancake ↔ Core4` Weld (`compileLcnfToPancake_agrees_with_core4`)**:
    For every join-free first-order `LcnfCode` term (`isJoinFreePureBlock c = true`) accepted by
    `checkFoLcnf`, `compileLcnfToCore4 c` (`Obend.Lower.LCNF:584`) evaluates in `Core4` to `.nat n`
    AND `compileLcnfToPancake c` refines `PanSem.evaluate` under `synthLcnfClk c` fuel with `0`
    `TimeOut`/`Error` to `.ret (.word (BitVec.ofNat 64 n))` for the identical `n < 2^64`. -/
theorem compileLcnfToPancake_agrees_with_core4 {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound)
    (hpure : isJoinFreePureBlock c = true) :
    ∃ n : Nat,
      n ≤ retBound ∧
      retBound < 2 ^ 64 ∧
      Evaluates (compileLcnfToCore4 c) (.nat n) ∧
      RefinesClkPan (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  obtain ⟨n, hn, hlt, hev, _, href⟩ := compileLcnfToPancake_correct (θ := θ) c retBound hchk
  have hcore4 : Evaluates (compileLcnfToCore4 c) (.nat n) :=
    evalLcnfCode_simulates_core4 (minLcnfFuel c) c n (isJoinFreePureBlock_sound c hpure) hev
  exact ⟨n, hn, hlt, hcore4, href⟩

/-- Multi-turn batch checker over a sequence of first-order `LcnfCode` request handlers. -/
@[expose] def checkFoLcnfBatch : List LcnfCode → Option (List Nat)
  | [] => some []
  | c :: cs => do
    let b ← checkFoLcnf c
    let bs ← checkFoLcnfBatch cs
    return b :: bs
termination_by structural cs => cs

theorem checkFoLcnfBatch_inhabited :
    ∃ (cs : List LcnfCode) (bs : List Nat), checkFoLcnfBatch cs = some bs :=
  ⟨[.return (.lit 0)], [0], by exact Eq.trans rfl rfl⟩

/-- Cumulative path-sensitive clock bound across a multi-turn batch `List LcnfCode`. -/
@[expose] def synthBatchClk : List LcnfCode → Nat
  | [] => 0
  | c :: cs => synthLcnfClk c + synthBatchClk cs
termination_by structural cs => cs

/-- Multi-turn batch execution of compiled `LcnfCode` handlers threading persistent `PanState`
    (`memory`, `globals`, `ffi`, and remaining `clock`) across turns. -/
@[expose] def runCompiledLcnfBatch {θ : Type} : List LcnfCode → PanState θ → Option (List Word × PanState θ)
  | [], s => some ([], s)
  | c :: cs, s =>
    match evaluate (compileLcnfToPancake c) s with
    | (.ret (.word w), s1) =>
      match runCompiledLcnfBatch cs s1 with
      | some (ws, sFinal) => some (w :: ws, sFinal)
      | none => none
    | _ => none
termination_by structural cs => cs

/-- Turn-by-turn evaluation & `Core4` agreement relation across a batch `List LcnfCode`. -/
inductive BatchEvalRel : List LcnfCode → List Nat → Prop where
  | nil : BatchEvalRel [] []
  | cons {c : LcnfCode} {n : Nat} {cs : List LcnfCode} {ns : List Nat} :
      evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) →
      (isJoinFreePureBlock c = true → Evaluates (compileLcnfToCore4 c) (.nat n)) →
      BatchEvalRel cs ns →
      BatchEvalRel (c :: cs) (n :: ns)

/-- **Apex Multi-Turn Batch Trace Theorem (`runCompiledLcnfBatch_sound`)**:
    Every checked batch `cs : List LcnfCode` executes end-to-end across `runCompiledLcnfBatch`
    from any `StateWF s0` with `s0.clock ≥ synthBatchClk cs` with `0` `TimeOut`/`Error`,
    preserving `StateWF` and cumulative clock bounds while agreeing turn-by-turn with
    `Obend.Lower.LCNF.evalLcnfCode` and `compileLcnfToCore4`. -/
theorem runCompiledLcnfBatch_sound {θ : Type}
    (cs : List LcnfCode) (bounds : List Nat) (s0 : PanState θ)
    (hchk : checkFoLcnfBatch cs = some bounds)
    (hwf0 : StateWF s0)
    (hclk0 : synthBatchClk cs ≤ s0.clock) :
    ∃ (ns : List Nat) (sFinal : PanState θ),
      runCompiledLcnfBatch cs s0 = some (ns.map (BitVec.ofNat 64), sFinal) ∧
      s0.clock ≤ sFinal.clock + synthBatchClk cs ∧
      StateWF sFinal ∧
      BatchEvalRel cs ns := by
  induction cs generalizing bounds s0 with
  | nil =>
    exact ⟨[], s0, rfl, by simp [synthBatchClk], hwf0, .nil⟩
  | cons c cs ih =>
    simp only [checkFoLcnfBatch] at hchk
    cases hc : checkFoLcnf c with
    | none => simp [hc] at hchk
    | some b =>
      rw [hc] at hchk
      cases hcs : checkFoLcnfBatch cs with
      | none => simp [hcs] at hchk
      | some bs =>
        simp only [synthBatchClk] at hclk0
        obtain ⟨n, _, _, hfuelC, htightC⟩ := compileLcnfToPancake_tight (θ := θ) c b hc
        obtain ⟨r1, s1, hev1, _, _, hclk1, hwf1, hr1⟩ :=
          htightC s0 ⟨hwf0, trivial⟩ (by omega)
        subst hr1
        obtain ⟨nsRest, sFinal, hrunRest, hclkRest, hwfFinal, hrelRest⟩ :=
          ih bs s1 hcs hwf1 (by omega)
        have hevC : evalLcnfCode (minLcnfFuel c) [] [] [] c = some (n, []) :=
          hfuelC (minLcnfFuel c) (Nat.le_refl _)
        have hcoreC : isJoinFreePureBlock c = true → Evaluates (compileLcnfToCore4 c) (.nat n) :=
          fun hp => evalLcnfCode_simulates_core4 (minLcnfFuel c) c n (isJoinFreePureBlock_sound c hp) hevC
        refine ⟨n :: nsRest, sFinal, ?_, by simp only [synthBatchClk]; omega, hwfFinal,
          .cons hevC hcoreC hrelRest⟩
        simp only [runCompiledLcnfBatch, hev1, hrunRest, List.map_cons]

/-- Canonical fuel-complete scalar evaluator `evalLcnf`. -/
@[expose] def evalLcnf (c : LcnfCode) : Option Nat :=
  (evalLcnfCode (minLcnfFuel c) [] [] [] c).map Prod.fst

/-- Direct `evalLcnf` corollary of `compileLcnfToPancake_correct`. -/
theorem compileLcnfToPancake_evalLcnf_correct {θ : Type} (c : LcnfCode) (retBound : Nat)
    (hchk : checkFoLcnf c = some retBound) :
    ∃ n : Nat,
      evalLcnf c = some n ∧
      n ≤ retBound ∧
      RefinesClkPan (θ := θ) (fun _ => True) (compileLcnfToPancake c) (synthLcnfClk c)
        (fun r _ => r = .ret (.word (BitVec.ofNat 64 n))) := by
  obtain ⟨n, hn, _, hev, _, href⟩ := compileLcnfToPancake_correct (θ := θ) c retBound hchk
  exact ⟨n, by simp [evalLcnf, hev], hn, href⟩

end Obend.Lower.Pancake
end
