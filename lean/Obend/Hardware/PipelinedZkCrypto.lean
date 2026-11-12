module
/-
# Obend.Hardware.PipelinedZkCrypto — 4-Stage Pipelined Goldilocks Butterfly & Wiedemann Binary-Tower RTL

1. **4-Stage Register-Pipelined Goldilocks Radix-2 Butterfly (`pipelinedGlButterflyRtlModule`)**:
   1 new `(u_t, v_t, w_t)` butterfly/cycle, universal 4-cycle stream non-interference
   (`pipelinedGlButterfly_latency4_sound`), and Leiserson–Saxe retiming closure at $>300\text{ MHz}$.
2. **Wiedemann Binary-Tower Field $\mathcal{T}_0 \subset \dots \subset \mathcal{T}_6 = \mathbb{F}_{2^{64}} \subset \mathcal{T}_7 = \mathbb{F}_{2^{128}}$**:
   3-submultiplication Karatsuba `towerMul` and norm-reduction `towerInv` over `BitVec (2^k)` with
   all commutative field laws proved for all $k \in \mathbb{N}$ (`towerMul_assoc`, `towerMul_inv`).
3. **Carry-Free SWAR-Karatsuba + 2-Stage Pipelined `gf2_64TowerMulRtlModule`**:
   Bit-exact equivalence to `towerMul 6` (`gf2_64TowerMulRtl_eq_towerMul`, `gf2_64TowerMulRtl_pipe2_sound`).
-/
public import Obend.Apps.ZkNtt.Goldilocks
public import Obend.Hardware.HDL
public import Obend.Hardware.Process
public import Obend.Hardware.Retiming

public section

namespace Obend.Hardware.PipelinedZkCrypto

open Obend.Apps.ZkNtt Obend.Hardware.HDL Obend.Hardware.Process Obend.Hardware.Retiming

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## 1. Pure Topological Wire Builder & Linear DAG Evaluation Lemma -/

private structure WireB where
  rev  : List WireAssign := []
  next : Nat := 0

private def pushW (s : WireB) (name : String) (e : RtlExpr) (w : Nat := 64) : RtlExpr × WireB :=
  (.wireRef s.next,
    { rev := { wireIdx := s.next, name := name, expr := e, width := w } :: s.rev, next := s.next + 1 })

private theorem foldWires_other (inputs regs : Nat → BitVec 64) (k : Nat) :
    ∀ (rest : List WireAssign) (env : Nat → BitVec 64), (∀ a ∈ rest, a.wireIdx ≠ k) →
      rest.foldl (fun (env : Nat → BitVec 64) a =>
        let v := evalRtlExpr inputs env regs a.expr
        fun i => if i == a.wireIdx then v else env i) env k = env k := by
  intro rest; induction rest with
  | nil => intro _ _; rfl
  | cons a tail ih =>
    intro env hNe; simp only [List.foldl_cons]
    rw [ih _ (fun x hx => hNe x (List.mem_cons_of_mem _ hx))]
    simp [beq_false_of_ne (Ne.symm (hNe a List.mem_cons_self))]

private theorem go_wireIdx_ge :
    ∀ (assigns : List WireAssign) (nIn nReg idx : Nat),
      checkWireTableDAG.go nIn nReg idx assigns = true → ∀ a ∈ assigns, idx ≤ a.wireIdx := by
  intro assigns; induction assigns with
  | nil => intro _ _ _ _ _ h; cases h
  | cons hd tl ih =>
    intro nIn nReg idx hGo a ha
    simp only [checkWireTableDAG.go, Bool.and_eq_true, beq_iff_eq] at hGo
    rcases List.mem_cons.mp ha with rfl | hMem
    · omega
    · have := ih nIn nReg (idx + 1) hGo.2 a hMem; omega

/-- **Linear DAG Wire Evaluation Lemma**: in any module passing `checkWireTableDAG`, wire `a.wireIdx`
in `evalWireTable` evaluates `a.expr` directly against the final `evalWireTable` environment. -/
theorem evalWireTable_at_dag (nIn nReg : Nat) (inputs regs : Nat → BitVec 64)
    (assigns : List WireAssign) (hDag : checkWireTableDAG nIn nReg assigns = true)
    (a : WireAssign) (ha : a ∈ assigns) :
    evalWireTable inputs regs assigns a.wireIdx =
      evalRtlExpr inputs (evalWireTable inputs regs assigns) regs a.expr := by
  unfold checkWireTableDAG at hDag; unfold evalWireTable
  suffices ∀ (l : List WireAssign) (idx : Nat) (env : Nat → BitVec 64),
      checkWireTableDAG.go nIn nReg idx l = true → a ∈ l →
      let fin := l.foldl (fun (e : Nat → BitVec 64) w =>
        let v := evalRtlExpr inputs e regs w.expr
        fun i => if i == w.wireIdx then v else e i) env
      fin a.wireIdx = evalRtlExpr inputs fin regs a.expr from
    this assigns 0 (fun _ => 0#64) hDag ha
  intro l; induction l with
  | nil => intro _ _ _ h; cases h
  | cons w rest ih =>
    intro idx env hGo hMem
    simp only [checkWireTableDAG.go, Bool.and_eq_true, beq_iff_eq] at hGo
    rcases List.mem_cons.mp hMem with rfl | hTail
    · dsimp only; simp only [List.foldl_cons]
      have hRestGt : ∀ x ∈ rest, x.wireIdx ≠ a.wireIdx := fun x hx => by
        have := go_wireIdx_ge rest nIn nReg (idx + 1) hGo.2 x hx; omega
      rw [foldWires_other inputs regs a.wireIdx rest _ hRestGt]
      simp only [beq_self_eq_true, ite_true]
      apply evalRtlExpr_dag_locality nIn nReg idx inputs regs env _ a.expr hGo.1.2
      intro i hi
      have hRestGtI : ∀ x ∈ rest, x.wireIdx ≠ i := fun x hx => by
        have := go_wireIdx_ge rest nIn nReg (idx + 1) hGo.2 x hx; omega
      rw [foldWires_other inputs regs i rest _ hRestGtI]
      simp [beq_false_of_ne (by omega : i ≠ a.wireIdx)]
    · exact ih (idx + 1) _ hGo.2 hTail

private theorem pushW_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr)
    (s : WireB) (name : String) (e : RtlExpr) (w : Nat := 64) :
    let r := pushW s name e w
    (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧
    ((∀ wa ∈ r.2.rev, wa ∈ finalRev) → evalRtlExpr ins fin regs r.1 = evalRtlExpr ins fin regs e) :=
  ⟨fun _ h => List.mem_cons_of_mem _ h, fun hSub => hFin _ (hSub _ List.mem_cons_self)⟩

private theorem stepModuleRegs_false_at (m : RtlModule) (ins st : Nat → BitVec 64)
    (hNodup : (m.regs.map (·.regIdx)).Nodup) (r : RegSpec) (hMem : r ∈ m.regs) :
    stepModuleRegs m false ins st r.regIdx = evalRtlExpr ins (evalWireTable ins st m.wires) st r.nextExpr := by
  unfold stepModuleRegs; let wEnv := evalWireTable ins st m.wires
  let stepFn (nextSt : Nat → BitVec 64) (reg : RegSpec) : Nat → BitVec 64 :=
    let v := match reg.resetKind with
      | .resetFree => evalRtlExpr ins wEnv st reg.nextExpr
      | .syncReset iv => if false then iv else evalRtlExpr ins wEnv st reg.nextExpr
    fun i => if i == reg.regIdx then v else nextSt i
  have hOther : ∀ (ts : List RegSpec) (e : Nat → BitVec 64), r.regIdx ∉ ts.map (·.regIdx) →
      ts.foldl stepFn e r.regIdx = e r.regIdx := by
    intro ts; induction ts with
    | nil => intro _ _; rfl
    | cons x xs ih =>
      intro e hni; simp only [List.map_cons, List.mem_cons, not_or] at hni
      rw [List.foldl_cons, ih _ hni.2]; simp [stepFn, hni.1]
  suffices ∀ (rs : List RegSpec) (e : Nat → BitVec 64), (rs.map (·.regIdx)).Nodup → r ∈ rs →
      rs.foldl stepFn e r.regIdx = evalRtlExpr ins wEnv st r.nextExpr from this m.regs st hNodup hMem
  intro rs; induction rs with
  | nil => intro _ _ h; cases h
  | cons hd tl ih =>
    intro e hNd hm; rw [List.map_cons, List.nodup_cons] at hNd; rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hTail
    · rw [hOther tl _ hNd.1]; dsimp only [stepFn]; cases r.resetKind <;> simp
    · exact ih _ hNd.2 hTail

/-! ## 2. 4-Stage Deeply Pipelined Goldilocks Radix-2 Butterfly `RtlModule` -/
private def glPExpr : RtlExpr := .const 0xFFFFFFFF00000001#64
private def glMask32Expr : RtlExpr := .const 0xFFFFFFFF#64
private def glShift32Expr : RtlExpr := .const 32#64
private def pushGlCanon (s : WireB) (x : RtlExpr) : RtlExpr × WireB :=
  pushW s "gl_canon" (.mux (.alu .ult x glPExpr) x (.alu .sub x glPExpr))
private def pushGlAdd (s : WireB) (a b : RtlExpr) : RtlExpr × WireB :=
  let (remP, s1) := pushW s "gl_remp" (.alu .sub glPExpr b)
  pushW s1 "gl_add" (.mux (.alu .ult a remP) (.alu .add a b) (.alu .sub a remP))
private def pushGlSub (s : WireB) (a b : RtlExpr) : RtlExpr × WireB :=
  pushW s "gl_sub" (.mux (.alu .ult a b) (.alu .add (.alu .sub glPExpr b) a) (.alu .sub a b))

private def buildPipelinedGlButterfly : List OutputPort × List RegSpec × WireB :=
  let (uCanon, s1) := pushGlCanon {} (.inputPort 0)
  let (vLo, s2) := pushW s1 "s1_vlo" (.alu .bitAnd (.inputPort 1) glMask32Expr)
  let (vHi, s3) := pushW s2 "s1_vhi" (.alu .lshr (.inputPort 1) glShift32Expr)
  let (wLo, s4) := pushW s3 "s1_wlo" (.alu .bitAnd (.inputPort 2) glMask32Expr)
  let (wHi, s5) := pushW s4 "s1_whi" (.alu .lshr (.inputPort 2) glShift32Expr)
  let (p00, s6) := pushW s5 "s1_p00" (.alu .mul vLo wLo)
  let (p01, s7) := pushW s6 "s1_p01" (.alu .mul vLo wHi)
  let (p10, s8) := pushW s7 "s1_p10" (.alu .mul vHi wLo)
  let (p11, s9) := pushW s8 "s1_p11" (.alu .mul vHi wHi)
  let (valIn, s10) := pushW s9 "s1_val" (.resize (.trunc 1) (.inputPort 3)) 1
  let (mid32, s11) := pushW s10 "s2_mid32"
    (.alu .add (.alu .add (.alu .lshr (.regRead 0) glShift32Expr)
      (.alu .bitAnd (.regRead 1) glMask32Expr)) (.alu .bitAnd (.regRead 2) glMask32Expr))
  let (prodLo, s12) := pushW s11 "s2_lo"
    (.alu .bitOr (.alu .bitAnd (.regRead 0) glMask32Expr)
      (.alu .shl (.alu .bitAnd mid32 glMask32Expr) glShift32Expr))
  let (prodHi, s13) := pushW s12 "s2_hi"
    (.alu .add (.alu .add (.alu .add (.regRead 3) (.alu .lshr (.regRead 1) glShift32Expr))
      (.alu .lshr (.regRead 2) glShift32Expr)) (.alu .lshr mid32 glShift32Expr))
  let (hiLo, s14) := pushW s13 "s3_hilo" (.alu .bitAnd (.regRead 7) glMask32Expr)
  let (hiHi, s15) := pushW s14 "s3_hihi" (.alu .lshr (.regRead 7) glShift32Expr)
  let (mid, s16)  := pushW s15 "s3_mid"  (.alu .sub (.alu .shl hiLo glShift32Expr) hiLo)
  let (loC, s17)  := pushGlCanon s16 (.regRead 6)
  let (t1, s18)   := pushGlAdd s17 loC mid
  let (vw, s19)   := pushGlSub s18 t1 hiHi
  let (evenNext, s20) := pushGlAdd s19 (.regRead 11) (.regRead 10)
  let (oddNext, s21)  := pushGlSub s20 (.regRead 11) (.regRead 10)
  let mkReg (idx : Nat) (name : String) (nx : RtlExpr) (w : Nat := 64) : RegSpec :=
    { regIdx := idx, name := name, domain := .coreClk, resetKind := .syncReset 0#64
      isSynchronizer := false, nextExpr := nx, width := w }
  let regs : List RegSpec :=
    [ mkReg 0 "s1_p00" p00, mkReg 1 "s1_p01" p01, mkReg 2 "s1_p10" p10, mkReg 3 "s1_p11" p11
    , mkReg 4 "s1_u" uCanon, mkReg 5 "s1_valid" valIn 1
    , mkReg 6 "s2_prod_lo" prodLo, mkReg 7 "s2_prod_hi" prodHi
    , mkReg 8 "s2_u" (.regRead 4), mkReg 9 "s2_valid" (.regRead 5) 1
    , mkReg 10 "s3_vw" vw, mkReg 11 "s3_u" (.regRead 8), mkReg 12 "s3_valid" (.regRead 9) 1
    , mkReg 13 "s4_out_even" evenNext, mkReg 14 "s4_out_odd" oddNext
    , mkReg 15 "s4_out_valid" (.regRead 12) 1 ]
  let outs : List OutputPort :=
    [ { name := "out_even",  expr := .regRead 13, width := 64 }
    , { name := "out_odd",   expr := .regRead 14, width := 64 }
    , { name := "out_valid", expr := .regRead 15, width := 1 } ]
  (outs, regs, s21)

private def glBuilt : List OutputPort × List RegSpec × WireB := buildPipelinedGlButterfly
private def glWires : List WireAssign := glBuilt.2.2.rev.reverse
private def glRegs  : List RegSpec    := glBuilt.2.1

/-- **4-Stage Deeply Pipelined Goldilocks Radix-2 Butterfly `RtlModule`**. -/
def pipelinedGlButterflyRtlModule : RtlModule :=
  { name := "pipelined_gl_butterfly_4stage"
    inputNames := ["u_in", "v_in", "w_in", "in_valid"], inputWidths := [64, 64, 64, 1]
    wires := glWires, regs := glRegs, outputs := glBuilt.1 }

@[expose] def glButterflyInputs (u v w : BitVec 64) (valid : BitVec 64 := 1#64) : Nat → BitVec 64
  | 0 => u | 1 => v | 2 => w | 3 => valid | _ => 0#64

theorem pipelinedGlButterfly_wellFormed (u : Unit) (_ : u = ()) :
    checkRtlModuleW pipelinedGlButterflyRtlModule = true := by decide +kernel

/-! ### 2a. Leiserson–Saxe Retiming Timing Closure (0-Stage Fails 300 MHz, 4-Stage Closes >300 MHz) -/

def glButterflySyncGraph : SyncGraph where
  name := "gl_butterfly_4stage_sync"
  primaryInputs := [0]; primaryOutputs := [5]
  edges :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 1900 }
    , { src := 1, dst := 2, origRegs := 0, combDelayPs := 1600 }
    , { src := 2, dst := 3, origRegs := 0, combDelayPs := 2100 }
    , { src := 3, dst := 4, origRegs := 0, combDelayPs := 1500 }
    , { src := 4, dst := 5, origRegs := 4, combDelayPs := 0 } ]
def glButterflyUnpipelinedCert : RetimingCert :=
  { vertexLags := [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)], ioLatencyShift := 0 }
def glButterfly4StageCert : RetimingCert :=
  { vertexLags := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 0)], ioLatencyShift := 0 }

theorem glButterfly_retiming_closes_333MHz (c : ProcessCorner) (hc : c = corner7nm_SS) :
    checkRetimingCert glButterflySyncGraph glButterflyUnpipelinedCert c 3000 = false ∧
    checkRetimingCert glButterflySyncGraph glButterfly4StageCert c 3000 = true := by
  subst hc; exact ⟨by decide, by decide⟩

/-! ### 2b. Exact 4-Cycle Non-Interfering Stream Equivalence (`pipelinedGlButterfly_latency4_sound`) -/

private theorem bv_add_toNat (x y : BitVec 64) : (evalAluOp .add x y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_add]
private theorem bv_sub_toNat (x y : BitVec 64) :
    (evalAluOp .sub x y).toNat = (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_sub]
private theorem bv_mul_toNat (x y : BitVec 64) : (evalAluOp .mul x y).toNat = (x.toNat * y.toNat) % 18446744073709551616 := by
  simp only [evalAluOp, BitVec.toNat_mul]
private theorem bv_or_toNat (x y : BitVec 64) : (evalAluOp .bitOr x y).toNat = x.toNat ||| y.toNat := by
  simp only [evalAluOp, BitVec.toNat_or]
private theorem bv_and_mask32_toNat (x : BitVec 64) : (evalAluOp .bitAnd x 0xFFFFFFFF#64).toNat = x.toNat % 4294967296 := by
  have hm : (0xFFFFFFFF#64).toNat = 2 ^ 32 - 1 := rfl
  simp only [evalAluOp, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
private theorem bv_lshr_32_toNat (x : BitVec 64) : (evalAluOp .lshr x 32#64).toNat = x.toNat / 4294967296 := by
  have hs : (32#64).toNat % 64 = 32 := rfl; simp only [evalAluOp, BitVec.toNat_ushiftRight, hs, Nat.shiftRight_eq_div_pow]
private theorem bv_shl_32_toNat (x : BitVec 64) : (evalAluOp .shl x 32#64).toNat = (x.toNat * 4294967296) % 18446744073709551616 := by
  have hs : (32#64).toNat % 64 = 32 := rfl; simp only [evalAluOp, BitVec.toNat_shiftLeft, hs, Nat.shiftLeft_eq]
private theorem mux_ult_eq (x y t f : BitVec 64) :
    (if (evalAluOp .ult x y != 0#64) = true then t else f) = (if x.toNat < y.toNat then t else f) := by
  have h10 : (1#64 != 0#64) = true := by simp
  unfold evalAluOp BitVec.ult; by_cases h : x.toNat < y.toNat <;> simp [h, h10]
private theorem lt_two_pow_64_of_lt_prime {x : Nat} (hx : x < goldilocksPrime) : x < 2 ^ 64 := by
  have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl; unfold goldilocksPrime at hx; omega
private theorem goldilocksCanon64_of_lt {x : Nat} (hx : x < goldilocksPrime) : goldilocksCanon64 x = x := by
  unfold goldilocksCanon64; have hge : ¬ goldilocksPrime ≤ x := by omega
  simp only [hge, ite_false]

private def glCanonBV (vx : BitVec 64) : BitVec 64 :=
  if evalAluOp .ult vx 0xFFFFFFFF00000001#64 != 0#64 then vx else evalAluOp .sub vx 0xFFFFFFFF00000001#64
private def glAddBV (va vb : BitVec 64) : BitVec 64 :=
  let remP := evalAluOp .sub 0xFFFFFFFF00000001#64 vb
  if evalAluOp .ult va remP != 0#64 then evalAluOp .add va vb else evalAluOp .sub va remP
private def glSubBV (va vb : BitVec 64) : BitVec 64 :=
  if evalAluOp .ult va vb != 0#64 then evalAluOp .add (evalAluOp .sub 0xFFFFFFFF00000001#64 vb) va
  else evalAluOp .sub va vb

private theorem glCanonBV_eq (vx : BitVec 64) :
    glCanonBV vx = BitVec.ofNat 64 (goldilocksCanon64 vx.toNat) ∧ (glCanonBV vx).toNat < goldilocksPrime := by
  have hEq : glCanonBV vx = BitVec.ofNat 64 (goldilocksCanon64 vx.toNat) := by
    unfold glCanonBV; rw [mux_ult_eq]; apply BitVec.eq_of_toNat_eq
    have hvx := vx.isLt; have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
    have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl; rw [hp]; unfold goldilocksCanon64
    by_cases hlt : vx.toNat < goldilocksPrime
    · have hge : ¬ goldilocksPrime ≤ vx.toNat := by omega
      simp only [hlt, ite_true, hge, ite_false, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt hvx).symm
    · have hge : goldilocksPrime ≤ vx.toNat := by omega
      simp only [hlt, ite_false, hge, ite_true, bv_sub_toNat, hp, BitVec.toNat_ofNat, hw]
      rw [hw] at hvx; unfold goldilocksPrime at hge ⊢; omega
  have hspec := (goldilocksCanon64_spec vx.isLt).1
  refine ⟨hEq, ?_⟩; rw [hEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]; exact hspec

private theorem glAddBV_eq (va vb : BitVec 64)
    (ha : va.toNat < goldilocksPrime) (hb : vb.toNat < goldilocksPrime) :
    glAddBV va vb = BitVec.ofNat 64 (goldilocksAddSpec va.toNat vb.toNat) ∧ (glAddBV va vb).toNat < goldilocksPrime := by
  have hEq : glAddBV va vb = BitVec.ofNat 64 (goldilocksAddSpec va.toNat vb.toNat) := by
    unfold glAddBV; dsimp only; rw [mux_ult_eq]; apply BitVec.eq_of_toNat_eq
    have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
    have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have hrem : (evalAluOp .sub 0xFFFFFFFF00000001#64 vb).toNat = goldilocksPrime - vb.toNat := by
      simp only [bv_sub_toNat, hp]; unfold goldilocksPrime at hb ⊢; omega
    rw [hrem]; unfold goldilocksAddSpec; rw [goldilocksCanon64_of_lt ha, goldilocksCanon64_of_lt hb]; dsimp only
    by_cases hlt : va.toNat < goldilocksPrime - vb.toNat
    · have hge : ¬ goldilocksPrime ≤ va.toNat + vb.toNat := by omega
      simp only [hlt, ite_true, hge, ite_false, bv_add_toNat, BitVec.toNat_ofNat, hw]
    · have hge : goldilocksPrime ≤ va.toNat + vb.toNat := by omega
      simp only [hlt, ite_false, hge, ite_true, bv_sub_toNat, hrem, BitVec.toNat_ofNat, hw]
      unfold goldilocksPrime at ha hb hlt hge ⊢; omega
  have hspec := (goldilocksAddSpec_spec va.isLt vb.isLt).1
  refine ⟨hEq, ?_⟩; rw [hEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]; exact hspec

private theorem glSubBV_eq (va vb : BitVec 64)
    (ha : va.toNat < goldilocksPrime) (hb : vb.toNat < goldilocksPrime) :
    glSubBV va vb = BitVec.ofNat 64 (goldilocksSubSpec va.toNat vb.toNat) ∧ (glSubBV va vb).toNat < goldilocksPrime := by
  have hEq : glSubBV va vb = BitVec.ofNat 64 (goldilocksSubSpec va.toNat vb.toNat) := by
    unfold glSubBV; rw [mux_ult_eq]; apply BitVec.eq_of_toNat_eq
    have hp : (0xFFFFFFFF00000001#64).toNat = goldilocksPrime := rfl
    have hw : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    unfold goldilocksSubSpec; rw [goldilocksCanon64_of_lt ha, goldilocksCanon64_of_lt hb]; dsimp only
    by_cases hlt : va.toNat < vb.toNat
    · have hle : ¬ vb.toNat ≤ va.toNat := by omega
      simp only [hlt, ite_true, hle, ite_false, bv_add_toNat, bv_sub_toNat, hp, BitVec.toNat_ofNat, hw]
      unfold goldilocksPrime at ha hb hlt ⊢; omega
    · have hle : vb.toNat ≤ va.toNat := by omega
      simp only [hlt, ite_false, hle, ite_true, bv_sub_toNat, BitVec.toNat_ofNat, hw]
      unfold goldilocksPrime at ha hb; omega
  have hspec := (goldilocksSubSpec_spec va.isLt vb.isLt).1
  refine ⟨hEq, ?_⟩; rw [hEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hspec)]; exact hspec

private def stage1P00 (v w : BitVec 64) : BitVec 64 := evalAluOp .mul (evalAluOp .bitAnd v 0xFFFFFFFF#64) (evalAluOp .bitAnd w 0xFFFFFFFF#64)
private def stage1P01 (v w : BitVec 64) : BitVec 64 := evalAluOp .mul (evalAluOp .bitAnd v 0xFFFFFFFF#64) (evalAluOp .lshr w 32#64)
private def stage1P10 (v w : BitVec 64) : BitVec 64 := evalAluOp .mul (evalAluOp .lshr v 32#64) (evalAluOp .bitAnd w 0xFFFFFFFF#64)
private def stage1P11 (v w : BitVec 64) : BitVec 64 := evalAluOp .mul (evalAluOp .lshr v 32#64) (evalAluOp .lshr w 32#64)
private def stage2Lo (p00 p01 p10 : BitVec 64) : BitVec 64 :=
  let mid32 := evalAluOp .add (evalAluOp .add (evalAluOp .lshr p00 32#64) (evalAluOp .bitAnd p01 0xFFFFFFFF#64)) (evalAluOp .bitAnd p10 0xFFFFFFFF#64)
  evalAluOp .bitOr (evalAluOp .bitAnd p00 0xFFFFFFFF#64) (evalAluOp .shl (evalAluOp .bitAnd mid32 0xFFFFFFFF#64) 32#64)
private def stage2Hi (p00 p01 p10 p11 : BitVec 64) : BitVec 64 :=
  let mid32 := evalAluOp .add (evalAluOp .add (evalAluOp .lshr p00 32#64) (evalAluOp .bitAnd p01 0xFFFFFFFF#64)) (evalAluOp .bitAnd p10 0xFFFFFFFF#64)
  evalAluOp .add (evalAluOp .add (evalAluOp .add p11 (evalAluOp .lshr p01 32#64)) (evalAluOp .lshr p10 32#64)) (evalAluOp .lshr mid32 32#64)
private def stage3Reduce (lo hi : BitVec 64) : BitVec 64 :=
  let hiLo := evalAluOp .bitAnd hi 0xFFFFFFFF#64; let hiHi := evalAluOp .lshr hi 32#64
  glSubBV (glAddBV (glCanonBV lo) (evalAluOp .sub (evalAluOp .shl hiLo 32#64) hiLo)) hiHi

private theorem stage123_mul_sound (v w : BitVec 64) :
    let p00 := stage1P00 v w; let p01 := stage1P01 v w
    let p10 := stage1P10 v w; let p11 := stage1P11 v w
    let vw  := stage3Reduce (stage2Lo p00 p01 p10) (stage2Hi p00 p01 p10 p11)
    vw = BitVec.ofNat 64 ((v.toNat * w.toNat) % goldilocksPrime) ∧ vw.toNat < goldilocksPrime := by
  dsimp only [stage1P00, stage1P01, stage1P10, stage1P11, stage2Lo, stage2Hi, stage3Reduce]
  let vLo := evalAluOp .bitAnd v 0xFFFFFFFF#64; let vHi := evalAluOp .lshr v 32#64
  let wLo := evalAluOp .bitAnd w 0xFFFFFFFF#64; let wHi := evalAluOp .lshr w 32#64
  let p00 := evalAluOp .mul vLo wLo; let p01 := evalAluOp .mul vLo wHi
  let p10 := evalAluOp .mul vHi wLo; let p11 := evalAluOp .mul vHi wHi
  let mid32 := evalAluOp .add (evalAluOp .add (evalAluOp .lshr p00 32#64)
    (evalAluOp .bitAnd p01 0xFFFFFFFF#64)) (evalAluOp .bitAnd p10 0xFFFFFFFF#64)
  let lo := evalAluOp .bitOr (evalAluOp .bitAnd p00 0xFFFFFFFF#64)
    (evalAluOp .shl (evalAluOp .bitAnd mid32 0xFFFFFFFF#64) 32#64)
  let hi := evalAluOp .add (evalAluOp .add (evalAluOp .add p11 (evalAluOp .lshr p01 32#64))
    (evalAluOp .lshr p10 32#64)) (evalAluOp .lshr mid32 32#64)
  let hiLo := evalAluOp .bitAnd hi 0xFFFFFFFF#64; let hiHi := evalAluOp .lshr hi 32#64
  let mid  := evalAluOp .sub (evalAluOp .shl hiLo 32#64) hiLo
  change glSubBV (glAddBV (glCanonBV lo) mid) hiHi = _ ∧
    (glSubBV (glAddBV (glCanonBV lo) mid) hiHi).toNat < _
  have hv := v.isLt; have hw0 := w.isLt
  have h2_64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl; have h2_32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have hv0 := bv_and_mask32_toNat v; have hv1 := bv_lshr_32_toNat v
  have hwLo := bv_and_mask32_toNat w; have hwHi := bv_lshr_32_toNat w
  have hv0Lt : vLo.toNat < 4294967296 := by rw [hv0]; exact Nat.mod_lt _ (by omega)
  have hv1Lt : vHi.toNat < 4294967296 := by rw [hv1]; rw [h2_64] at hv; omega
  have hw0Lt : wLo.toNat < 4294967296 := by rw [hwLo]; exact Nat.mod_lt _ (by omega)
  have hw1Lt : wHi.toNat < 4294967296 := by rw [hwHi]; rw [h2_64] at hw0; omega
  have mul32_lt : ∀ x y, x < 4294967296 → y < 4294967296 → x * y < 18446744073709551616 := fun x y hx hy => by
    have := Nat.mul_le_mul (show x ≤ 4294967295 by omega) (show y ≤ 4294967295 by omega); omega
  have hp00 : p00.toNat = vLo.toNat * wLo.toNat := by simp only [p00, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ hv0Lt hw0Lt)]
  have hp01 : p01.toNat = vLo.toNat * wHi.toNat := by simp only [p01, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ hv0Lt hw1Lt)]
  have hp10 : p10.toNat = vHi.toNat * wLo.toNat := by simp only [p10, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ hv1Lt hw0Lt)]
  have hp11 : p11.toNat = vHi.toNat * wHi.toNat := by simp only [p11, bv_mul_toNat, Nat.mod_eq_of_lt (mul32_lt _ _ hv1Lt hw1Lt)]
  have hp00HiLt : p00.toNat / 4294967296 < 4294967296 := by have := mul32_lt _ _ hv0Lt hw0Lt; omega
  have hmid32 : mid32.toNat = p00.toNat / 4294967296 + p01.toNat % 4294967296 + p10.toNat % 4294967296 := by
    have := Nat.mod_lt p01.toNat (by omega : 0 < 4294967296)
    have := Nat.mod_lt p10.toNat (by omega : 0 < 4294967296)
    simp only [mid32, bv_add_toNat, bv_lshr_32_toNat, bv_and_mask32_toNat]; omega
  have hlo : lo.toNat = p00.toNat % 4294967296 + 4294967296 * (mid32.toNat % 4294967296) := by
    have hm1 : p00.toNat % 4294967296 < 2 ^ 32 := by rw [h2_32]; exact Nat.mod_lt _ (by omega)
    have hm2 : mid32.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
    have hm2Mul : mid32.toNat % 4294967296 * 4294967296 < 18446744073709551616 := by
      have := Nat.mul_le_mul_right 4294967296 (show mid32.toNat % 4294967296 ≤ 4294967295 by omega); omega
    have hshEq : mid32.toNat % 4294967296 * 4294967296 = (mid32.toNat % 4294967296) <<< 32 := by rw [Nat.shiftLeft_eq, h2_32]
    simp only [lo, bv_or_toNat, bv_and_mask32_toNat, bv_shl_32_toNat]
    rw [Nat.mod_eq_of_lt hm2Mul, hshEq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hm1, ← hshEq,
      Nat.add_comm, Nat.mul_comm _ 4294967296]
  let H : Nat := p11.toNat + p01.toNat / 4294967296 + p10.toNat / 4294967296 + mid32.toNat / 4294967296
  have hProd : lo.toNat + 18446744073709551616 * H = v.toNat * w.toNat := by
    have := Nat.mod_add_div p00.toNat 4294967296; have := Nat.mod_add_div p01.toNat 4294967296
    have := Nat.mod_add_div p10.toNat 4294967296; have := Nat.mod_add_div mid32.toNat 4294967296
    have hLin : lo.toNat + 18446744073709551616 * H =
        p00.toNat + 4294967296 * (p01.toNat + p10.toNat) + 18446744073709551616 * p11.toNat := by dsimp only [H]; omega
    rw [hLin, hp00, hp01, hp10, hp11, hv0, hv1, hwLo, hwHi]
    have := Nat.mod_add_div v.toNat 4294967296; have := Nat.mod_add_div w.toNat 4294967296; grind
  have hProdLt : v.toNat * w.toNat < 18446744073709551616 * 18446744073709551616 := by
    rw [h2_64] at hv hw0
    have := Nat.mul_le_mul (show v.toNat ≤ 18446744073709551615 by omega) (show w.toNat ≤ 18446744073709551615 by omega); omega
  have hHLt : H < 18446744073709551616 := by omega
  have hhi : hi.toNat = H := by simp only [hi, bv_add_toNat, bv_lshr_32_toNat]; dsimp only [H] at hHLt ⊢; omega
  have hhiLo := bv_and_mask32_toNat hi; have hhiHi := bv_lshr_32_toNat hi
  have hhiLoLt : hiLo.toNat < 4294967296 := by rw [hhiLo]; exact Nat.mod_lt _ (by omega)
  have hhiHiLt : hiHi.toNat < 4294967296 := by rw [hhiHi, hhi]; omega
  have hmid : mid.toNat = hiLo.toNat * 4294967296 - hiLo.toNat := by simp only [mid, bv_sub_toNat, bv_shl_32_toNat]; omega
  have hmidLtP : mid.toNat < goldilocksPrime := by unfold goldilocksPrime; omega
  have hhiHiLtP : hiHi.toNat < goldilocksPrime := by unfold goldilocksPrime; omega
  obtain ⟨hLoCEq, hLoCLt⟩ := glCanonBV_eq lo
  obtain ⟨hT1Eq, hT1Lt⟩ := glAddBV_eq (glCanonBV lo) mid hLoCLt hmidLtP
  obtain ⟨hSubEq, hSubLt⟩ := glSubBV_eq (glAddBV (glCanonBV lo) mid) hiHi hT1Lt hhiHiLtP
  refine ⟨?_, hSubLt⟩; rw [hSubEq, hT1Eq, hLoCEq]
  have hLoCLt64 := lt_two_pow_64_of_lt_prime (goldilocksCanon64_spec lo.isLt).1
  have hT1Lt64 := lt_two_pow_64_of_lt_prime (goldilocksAddSpec_spec hLoCLt64 mid.isLt).1
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLoCLt64, Nat.mod_eq_of_lt hT1Lt64]
  have hCanonIdemp : goldilocksAddSpec (goldilocksCanon64 lo.toNat) mid.toNat =
      goldilocksAddSpec lo.toNat mid.toNat := by
    unfold goldilocksAddSpec; rw [goldilocksCanon64_of_lt (goldilocksCanon64_spec lo.isLt).1]
  rw [hCanonIdemp, hmid, hhiLo, hhiHi]
  change BitVec.ofNat 64 (goldilocksReduce128Spec lo.toNat hi.toNat) = _
  rw [(goldilocksReduce128Spec_sound lo.isLt hi.isLt).2, h2_64, hhi, hProd]

private theorem pushGlCanon_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr) (s : WireB) (x : RtlExpr) :
    let r := pushGlCanon s x
    (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧ ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
      evalRtlExpr ins fin regs r.1 = glCanonBV (evalRtlExpr ins fin regs x)) :=
  pushW_spec ins regs fin finalRev hFin s "gl_canon" (.mux (.alu .ult x glPExpr) x (.alu .sub x glPExpr))

private theorem pushGlSub_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr) (s : WireB) (a b : RtlExpr) :
    let r := pushGlSub s a b
    (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧ ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
      evalRtlExpr ins fin regs r.1 = glSubBV (evalRtlExpr ins fin regs a) (evalRtlExpr ins fin regs b)) :=
  pushW_spec ins regs fin finalRev hFin s "gl_sub"
    (.mux (.alu .ult a b) (.alu .add (.alu .sub glPExpr b) a) (.alu .sub a b))

private theorem pushGlAdd_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr) (s : WireB) (a b : RtlExpr) :
    let r := pushGlAdd s a b
    (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧ ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
      evalRtlExpr ins fin regs r.1 = glAddBV (evalRtlExpr ins fin regs a) (evalRtlExpr ins fin regs b)) := by
  unfold pushGlAdd; dsimp only
  let r1 := pushW s "gl_remp" (.alu .sub glPExpr b)
  obtain ⟨m1, e1⟩ := pushW_spec ins regs fin finalRev hFin s "gl_remp" (.alu .sub glPExpr b)
  obtain ⟨m2, e2⟩ := pushW_spec ins regs fin finalRev hFin r1.2 "gl_add"
    (.mux (.alu .ult a r1.1) (.alu .add a b) (.alu .sub a r1.1))
  refine ⟨fun wa h => m2 wa (m1 wa h), fun hSub => (e2 hSub).trans ?_⟩
  exact congrArg (fun z => if evalAluOp .ult (evalRtlExpr ins fin regs a) z != 0#64
    then evalAluOp .add (evalRtlExpr ins fin regs a) (evalRtlExpr ins fin regs b)
    else evalAluOp .sub (evalRtlExpr ins fin regs a) z) (e1 (fun wa h => hSub wa (m2 wa h)))

private theorem pipelinedGlButterfly_step_regs (ins st : Nat → BitVec 64) :
    let st' := stepModuleRegs pipelinedGlButterflyRtlModule false ins st
    st' 0 = stage1P00 (ins 1) (ins 2) ∧ st' 1 = stage1P01 (ins 1) (ins 2) ∧
    st' 2 = stage1P10 (ins 1) (ins 2) ∧ st' 3 = stage1P11 (ins 1) (ins 2) ∧
    st' 4 = glCanonBV (ins 0) ∧ st' 5 = truncToWidth 1 (ins 3) ∧
    st' 6 = stage2Lo (st 0) (st 1) (st 2) ∧ st' 7 = stage2Hi (st 0) (st 1) (st 2) (st 3) ∧
    st' 8 = st 4 ∧ st' 9 = st 5 ∧
    st' 10 = stage3Reduce (st 6) (st 7) ∧ st' 11 = st 8 ∧ st' 12 = st 9 ∧
    st' 13 = glAddBV (st 11) (st 10) ∧ st' 14 = glSubBV (st 11) (st 10) ∧ st' 15 = st 12 := by
  have hDag : checkWireTableDAG 4 16 pipelinedGlButterflyRtlModule.wires = true := by decide +kernel
  have hNodup : (pipelinedGlButterflyRtlModule.regs.map (·.regIdx)).Nodup := by decide +kernel
  let fin := evalWireTable ins st pipelinedGlButterflyRtlModule.wires
  let finalRev := glBuilt.2.2.rev
  have hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin st wa.expr :=
    fun wa hwa => evalWireTable_at_dag 4 16 ins st _ hDag wa (List.mem_reverse.mpr hwa)
  have hr (k : Nat) (r : RegSpec) (hMem : r ∈ pipelinedGlButterflyRtlModule.regs) (hk : r.regIdx = k) :
      stepModuleRegs pipelinedGlButterflyRtlModule false ins st k = evalRtlExpr ins fin st r.nextExpr := by
    rw [← hk, stepModuleRegs_false_at pipelinedGlButterflyRtlModule ins st hNodup r hMem]
  let r1  := pushGlCanon {} (.inputPort 0)
  let r2  := pushW r1.2 "s1_vlo" (.alu .bitAnd (.inputPort 1) glMask32Expr)
  let r3  := pushW r2.2 "s1_vhi" (.alu .lshr (.inputPort 1) glShift32Expr)
  let r4  := pushW r3.2 "s1_wlo" (.alu .bitAnd (.inputPort 2) glMask32Expr)
  let r5  := pushW r4.2 "s1_whi" (.alu .lshr (.inputPort 2) glShift32Expr)
  let r6  := pushW r5.2 "s1_p00" (.alu .mul r2.1 r4.1); let r7 := pushW r6.2 "s1_p01" (.alu .mul r2.1 r5.1)
  let r8  := pushW r7.2 "s1_p10" (.alu .mul r3.1 r4.1); let r9 := pushW r8.2 "s1_p11" (.alu .mul r3.1 r5.1)
  let r10 := pushW r9.2 "s1_val" (.resize (.trunc 1) (.inputPort 3)) 1
  let r11 := pushW r10.2 "s2_mid32" (.alu .add (.alu .add (.alu .lshr (.regRead 0) glShift32Expr)
    (.alu .bitAnd (.regRead 1) glMask32Expr)) (.alu .bitAnd (.regRead 2) glMask32Expr))
  let r12 := pushW r11.2 "s2_lo" (.alu .bitOr (.alu .bitAnd (.regRead 0) glMask32Expr)
    (.alu .shl (.alu .bitAnd r11.1 glMask32Expr) glShift32Expr))
  let r13 := pushW r12.2 "s2_hi" (.alu .add (.alu .add (.alu .add (.regRead 3)
    (.alu .lshr (.regRead 1) glShift32Expr)) (.alu .lshr (.regRead 2) glShift32Expr)) (.alu .lshr r11.1 glShift32Expr))
  let r14 := pushW r13.2 "s3_hilo" (.alu .bitAnd (.regRead 7) glMask32Expr)
  let r15 := pushW r14.2 "s3_hihi" (.alu .lshr (.regRead 7) glShift32Expr)
  let r16 := pushW r15.2 "s3_mid"  (.alu .sub (.alu .shl r14.1 glShift32Expr) r14.1)
  let r17 := pushGlCanon r16.2 (.regRead 6); let r18 := pushGlAdd r17.2 r17.1 r16.1
  let r19 := pushGlSub r18.2 r18.1 r15.1; let r20 := pushGlAdd r19.2 (.regRead 11) (.regRead 10)
  obtain ⟨m1, e1⟩ := pushGlCanon_spec ins st fin finalRev hFin {} (.inputPort 0)
  obtain ⟨m2, e2⟩ := pushW_spec ins st fin finalRev hFin r1.2 "s1_vlo" (.alu .bitAnd (.inputPort 1) glMask32Expr)
  obtain ⟨m3, e3⟩ := pushW_spec ins st fin finalRev hFin r2.2 "s1_vhi" (.alu .lshr (.inputPort 1) glShift32Expr)
  obtain ⟨m4, e4⟩ := pushW_spec ins st fin finalRev hFin r3.2 "s1_wlo" (.alu .bitAnd (.inputPort 2) glMask32Expr)
  obtain ⟨m5, e5⟩ := pushW_spec ins st fin finalRev hFin r4.2 "s1_whi" (.alu .lshr (.inputPort 2) glShift32Expr)
  obtain ⟨m6, e6⟩ := pushW_spec ins st fin finalRev hFin r5.2 "s1_p00" (.alu .mul r2.1 r4.1)
  obtain ⟨m7, e7⟩ := pushW_spec ins st fin finalRev hFin r6.2 "s1_p01" (.alu .mul r2.1 r5.1)
  obtain ⟨m8, e8⟩ := pushW_spec ins st fin finalRev hFin r7.2 "s1_p10" (.alu .mul r3.1 r4.1)
  obtain ⟨m9, e9⟩ := pushW_spec ins st fin finalRev hFin r8.2 "s1_p11" (.alu .mul r3.1 r5.1)
  obtain ⟨m10, e10⟩ := pushW_spec ins st fin finalRev hFin r9.2 "s1_val" (.resize (.trunc 1) (.inputPort 3)) 1
  obtain ⟨m11, e11⟩ := pushW_spec ins st fin finalRev hFin r10.2 "s2_mid32" (.alu .add (.alu .add (.alu .lshr (.regRead 0) glShift32Expr)
    (.alu .bitAnd (.regRead 1) glMask32Expr)) (.alu .bitAnd (.regRead 2) glMask32Expr))
  obtain ⟨m12, e12⟩ := pushW_spec ins st fin finalRev hFin r11.2 "s2_lo" (.alu .bitOr (.alu .bitAnd (.regRead 0) glMask32Expr)
    (.alu .shl (.alu .bitAnd r11.1 glMask32Expr) glShift32Expr))
  obtain ⟨m13, e13⟩ := pushW_spec ins st fin finalRev hFin r12.2 "s2_hi" (.alu .add (.alu .add (.alu .add (.regRead 3)
    (.alu .lshr (.regRead 1) glShift32Expr)) (.alu .lshr (.regRead 2) glShift32Expr)) (.alu .lshr r11.1 glShift32Expr))
  obtain ⟨m14, e14⟩ := pushW_spec ins st fin finalRev hFin r13.2 "s3_hilo" (.alu .bitAnd (.regRead 7) glMask32Expr)
  obtain ⟨m15, e15⟩ := pushW_spec ins st fin finalRev hFin r14.2 "s3_hihi" (.alu .lshr (.regRead 7) glShift32Expr)
  obtain ⟨m16, e16⟩ := pushW_spec ins st fin finalRev hFin r15.2 "s3_mid"  (.alu .sub (.alu .shl r14.1 glShift32Expr) r14.1)
  obtain ⟨m17, e17⟩ := pushGlCanon_spec ins st fin finalRev hFin r16.2 (.regRead 6)
  obtain ⟨m18, e18⟩ := pushGlAdd_spec ins st fin finalRev hFin r17.2 r17.1 r16.1
  obtain ⟨m19, e19⟩ := pushGlSub_spec ins st fin finalRev hFin r18.2 r18.1 r15.1
  obtain ⟨m20, e20⟩ := pushGlAdd_spec ins st fin finalRev hFin r19.2 (.regRead 11) (.regRead 10)
  obtain ⟨m21, e21⟩ := pushGlSub_spec ins st fin finalRev hFin r20.2 (.regRead 11) (.regRead 10)
  have s20 : ∀ wa ∈ r20.2.rev, wa ∈ finalRev := m21
  have s19 : ∀ wa ∈ r19.2.rev, wa ∈ finalRev := fun w h => s20 w (m20 w h)
  have s18 := fun w h => s19 w (m19 w h); have s17 := fun w h => s18 w (m18 w h)
  have s16 := fun w h => s17 w (m17 w h); have s15 := fun w h => s16 w (m16 w h)
  have s14 := fun w h => s15 w (m15 w h); have s13 := fun w h => s14 w (m14 w h)
  have s12 := fun w h => s13 w (m13 w h); have s11 := fun w h => s12 w (m12 w h)
  have s10 := fun w h => s11 w (m11 w h); have s9  := fun w h => s10 w (m10 w h)
  have s8  := fun w h => s9  w (m9  w h); have s7  := fun w h => s8  w (m8  w h)
  have s6  := fun w h => s7  w (m7  w h); have s5  := fun w h => s6  w (m6  w h)
  have s4  := fun w h => s5  w (m5  w h); have s3  := fun w h => s4  w (m4  w h)
  have s2  := fun w h => s3  w (m3  w h); have s1  := fun w h => s2  w (m2  w h)
  dsimp only; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hr 8 glRegs[8] (by decide +kernel) rfl, hr 9 glRegs[9] (by decide +kernel) rfl, ?_,
    hr 11 glRegs[11] (by decide +kernel) rfl, hr 12 glRegs[12] (by decide +kernel) rfl, ?_, ?_,
    hr 15 glRegs[15] (by decide +kernel) rfl⟩
  · rw [hr 0 glRegs[0] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r6.1 = _
    rw [e6 s6]; simp only [evalRtlExpr]; rw [e2 s2, e4 s4]; rfl
  · rw [hr 1 glRegs[1] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r7.1 = _
    rw [e7 s7]; simp only [evalRtlExpr]; rw [e2 s2, e5 s5]; rfl
  · rw [hr 2 glRegs[2] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r8.1 = _
    rw [e8 s8]; simp only [evalRtlExpr]; rw [e3 s3, e4 s4]; rfl
  · rw [hr 3 glRegs[3] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r9.1 = _
    rw [e9 s9]; simp only [evalRtlExpr]; rw [e3 s3, e5 s5]; rfl
  · rw [hr 4 glRegs[4] (by decide +kernel) rfl]; exact e1 s1
  · rw [hr 5 glRegs[5] (by decide +kernel) rfl]; exact e10 s10
  · rw [hr 6 glRegs[6] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r12.1 = _
    rw [e12 s12]; simp only [evalRtlExpr]; rw [e11 s11]; rfl
  · rw [hr 7 glRegs[7] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r13.1 = _
    rw [e13 s13]; simp only [evalRtlExpr]; rw [e11 s11]; rfl
  · rw [hr 10 glRegs[10] (by decide +kernel) rfl]; change evalRtlExpr ins fin st r19.1 = _
    rw [e19 s19, e18 s18, e17 s17, e16 s16]; simp only [evalRtlExpr]; rw [e14 s14, e15 s15]; rfl
  · rw [hr 13 glRegs[13] (by decide +kernel) rfl]; exact e20 s20
  · rw [hr 14 glRegs[14] (by decide +kernel) rfl]; exact e21 (fun _ h => h)

/-- **4-Step Non-Interference Theorem**: starting from ANY state `st0` and clocking ANY 4 inputs
`ins0..ins3`, Stage-4 outputs equal the canonical Goldilocks butterfly of `ins0` alone. -/
theorem pipelinedGlButterfly_four_steps_sound
    (st0 ins0 ins1 ins2 ins3 anyIns : Nat → BitVec 64) :
    let st1 := stepModuleRegs pipelinedGlButterflyRtlModule false ins0 st0
    let st2 := stepModuleRegs pipelinedGlButterflyRtlModule false ins1 st1
    let st3 := stepModuleRegs pipelinedGlButterflyRtlModule false ins2 st2
    let st4 := stepModuleRegs pipelinedGlButterflyRtlModule false ins3 st3
    let u0  := (ins0 0).toNat; let v0 := (ins0 1).toNat; let w0 := (ins0 2).toNat
    let outs := evalModuleOutputs pipelinedGlButterflyRtlModule anyIns st4
    outs.lookup "out_even" = some (BitVec.ofNat 64 ((u0 + v0 * w0) % goldilocksPrime)) ∧
    outs.lookup "out_odd" = some (BitVec.ofNat 64 ((u0 % goldilocksPrime + goldilocksPrime -
      (v0 * w0) % goldilocksPrime) % goldilocksPrime)) ∧
    outs.lookup "out_valid" = some (truncToWidth 1 (ins0 3)) ∧
    (st4 13).toNat < goldilocksPrime ∧ (st4 14).toNat < goldilocksPrime := by
  intro st1 st2 st3 st4 u0 v0 w0 outs
  obtain ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, _, _, _, _, _, _, _, _, _, _⟩ := pipelinedGlButterfly_step_regs ins0 st0
  obtain ⟨_, _, _, _, _, _, s2_6, s2_7, s2_8, s2_9, _, _, _, _, _, _⟩ := pipelinedGlButterfly_step_regs ins1 st1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, s3_10, s3_11, s3_12, _, _, _⟩ := pipelinedGlButterfly_step_regs ins2 st2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, s4_13, s4_14, s4_15⟩ := pipelinedGlButterfly_step_regs ins3 st3
  let vwBV := stage3Reduce (stage2Lo (stage1P00 (ins0 1) (ins0 2)) (stage1P01 (ins0 1) (ins0 2)) (stage1P10 (ins0 1) (ins0 2)))
    (stage2Hi (stage1P00 (ins0 1) (ins0 2)) (stage1P01 (ins0 1) (ins0 2)) (stage1P10 (ins0 1) (ins0 2)) (stage1P11 (ins0 1) (ins0 2)))
  dsimp only [st4, st3, st2, st1] at *
  have h13 : stepModuleRegs pipelinedGlButterflyRtlModule false ins3 (stepModuleRegs pipelinedGlButterflyRtlModule false ins2
      (stepModuleRegs pipelinedGlButterflyRtlModule false ins1 (stepModuleRegs pipelinedGlButterflyRtlModule false ins0 st0))) 13 =
      glAddBV (glCanonBV (ins0 0)) vwBV := by rw [s4_13, s3_11, s3_10, s2_8, s2_6, s2_7, s1_0, s1_1, s1_2, s1_3, s1_4]
  have h14 : stepModuleRegs pipelinedGlButterflyRtlModule false ins3 (stepModuleRegs pipelinedGlButterflyRtlModule false ins2
      (stepModuleRegs pipelinedGlButterflyRtlModule false ins1 (stepModuleRegs pipelinedGlButterflyRtlModule false ins0 st0))) 14 =
      glSubBV (glCanonBV (ins0 0)) vwBV := by rw [s4_14, s3_11, s3_10, s2_8, s2_6, s2_7, s1_0, s1_1, s1_2, s1_3, s1_4]
  have h15 : stepModuleRegs pipelinedGlButterflyRtlModule false ins3 (stepModuleRegs pipelinedGlButterflyRtlModule false ins2
      (stepModuleRegs pipelinedGlButterflyRtlModule false ins1 (stepModuleRegs pipelinedGlButterflyRtlModule false ins0 st0))) 15 =
      truncToWidth 1 (ins0 3) := by rw [s4_15, s3_12, s2_9, s1_5]
  obtain ⟨hMulEq, hMulLt⟩ := stage123_mul_sound (ins0 1) (ins0 2)
  obtain ⟨hUC, hULt⟩ := glCanonBV_eq (ins0 0)
  obtain ⟨hEvenEq, hEvenLt⟩ := glAddBV_eq _ vwBV hULt hMulLt
  obtain ⟨hOddEq, hOddLt⟩ := glSubBV_eq _ vwBV hULt hMulLt
  have hUC_spec := goldilocksCanon64_spec (ins0 0).isLt
  have hUCLt64 := lt_two_pow_64_of_lt_prime hUC_spec.1
  have hpPos : 0 < goldilocksPrime := by unfold goldilocksPrime; omega
  have hProdModLtP : (v0 * w0) % goldilocksPrime < goldilocksPrime := Nat.mod_lt _ hpPos
  have hProdModLt64 := lt_two_pow_64_of_lt_prime hProdModLtP
  have hUToNat : (glCanonBV (ins0 0)).toNat = goldilocksCanon64 u0 := by
    rw [hUC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hUCLt64]
  have hVWToNat : vwBV.toNat = (v0 * w0) % goldilocksPrime := by
    dsimp only [vwBV]; rw [hMulEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hProdModLt64]
  have hEvenArith : goldilocksAddSpec (goldilocksCanon64 u0) ((v0 * w0) % goldilocksPrime) =
      (u0 + v0 * w0) % goldilocksPrime := by
    rw [(goldilocksAddSpec_spec hUCLt64 hProdModLt64).2, Nat.add_mod, hUC_spec.2,
      Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
  have hOddArith : goldilocksSubSpec (goldilocksCanon64 u0) ((v0 * w0) % goldilocksPrime) =
      (u0 % goldilocksPrime + goldilocksPrime - (v0 * w0) % goldilocksPrime) % goldilocksPrime := by
    rw [(goldilocksSubSpec_spec hUCLt64 hProdModLt64).2,
      goldilocksCanon64_of_lt hUC_spec.1, goldilocksCanon64_of_lt hProdModLtP, hUC_spec.2]
  have hOutE : outs.lookup "out_even" = some (st4 13) := rfl
  have hOutO : outs.lookup "out_odd"  = some (st4 14) := rfl
  have hOutV : outs.lookup "out_valid" = some (st4 15) := rfl
  rw [hOutE, hOutO, hOutV]; dsimp only [st4, st3, st2, st1]; rw [h13, h14, h15]
  exact ⟨congrArg some (by rw [hEvenEq, hUToNat, hVWToNat, hEvenArith]),
    congrArg some (by rw [hOddEq, hUToNat, hVWToNat, hOddArith]), rfl, hEvenLt, hOddLt⟩

private theorem list_take_add_four {α : Type} :
    ∀ (t : Nat) (xs : List α) (h : t + 4 ≤ xs.length),
      xs.take (t + 4) =
        xs.take t ++ [xs[t]'(by omega), xs[t + 1]'(by omega), xs[t + 2]'(by omega), xs[t + 3]'(by omega)]
  | 0, [], h | 0, [_], h | 0, [_, _], h | 0, [_, _, _], h => by simp at h
  | 0, _ :: _ :: _ :: _ :: _, _ => rfl
  | _ + 1, [], h => by simp at h
  | t + 1, x :: xs, h => by
    simp only [List.length_cons] at h
    have ih := list_take_add_four t xs (by omega)
    have h1 : (x :: xs).take (t + 1 + 4) = x :: xs.take (t + 4) := rfl
    have h0 : (x :: xs).take (t + 1) = x :: xs.take t := rfl
    rw [h1, h0, ih]; rfl

/-- **`pipelinedGlButterfly_latency4_sound`**: Exact 4-cycle pipeline stream equivalence! -/
theorem pipelinedGlButterfly_latency4_sound
    (initRegs anyIns : Nat → BitVec 64) (stream : List (Nat → BitVec 64))
    (t : Nat) (ht : t + 4 ≤ stream.length) :
    let trace := (stream.take (t + 4)).map (fun ins => (false, ins))
    let st    := runModuleTrace pipelinedGlButterflyRtlModule initRegs trace
    let ins_t := stream[t]'(by omega)
    let u_t   := (ins_t 0).toNat; let v_t := (ins_t 1).toNat; let w_t := (ins_t 2).toNat
    let outs  := evalModuleOutputs pipelinedGlButterflyRtlModule anyIns st
    outs.lookup "out_even" = some (BitVec.ofNat 64 ((u_t + v_t * w_t) % goldilocksPrime)) ∧
    outs.lookup "out_odd" = some (BitVec.ofNat 64 ((u_t % goldilocksPrime + goldilocksPrime -
      (v_t * w_t) % goldilocksPrime) % goldilocksPrime)) ∧
    outs.lookup "out_valid" = some (truncToWidth 1 (ins_t 3)) ∧
    (st 13).toNat < goldilocksPrime ∧ (st 14).toNat < goldilocksPrime ∧
    ((st 14).toNat : Int) = ((u_t : Int) - (v_t : Int) * (w_t : Int)) % (goldilocksPrime : Int) := by
  intro trace st ins_t u_t v_t w_t outs
  have hRun : st =
      stepModuleRegs pipelinedGlButterflyRtlModule false (stream[t + 3]'(by omega))
        (stepModuleRegs pipelinedGlButterflyRtlModule false (stream[t + 2]'(by omega))
          (stepModuleRegs pipelinedGlButterflyRtlModule false (stream[t + 1]'(by omega))
            (stepModuleRegs pipelinedGlButterflyRtlModule false (stream[t]'(by omega))
              (runModuleTrace pipelinedGlButterflyRtlModule initRegs ((stream.take t).map (false, ·)))))) := by
    dsimp only [st, trace]; rw [list_take_add_four t stream ht, List.map_append]; unfold runModuleTrace
    rw [List.foldl_append]; rfl
  obtain ⟨hEven, hOdd, hVal, h13Lt, h14Lt⟩ := pipelinedGlButterfly_four_steps_sound
    (runModuleTrace pipelinedGlButterflyRtlModule initRegs ((stream.take t).map (false, ·)))
    (stream[t]'(by omega)) (stream[t + 1]'(by omega)) (stream[t + 2]'(by omega)) (stream[t + 3]'(by omega)) anyIns
  rw [← hRun] at hEven hOdd hVal h13Lt h14Lt
  refine ⟨hEven, hOdd, hVal, h13Lt, h14Lt, ?_⟩
  have hOuts14 : outs.lookup "out_odd" = some (st 14) := rfl
  rw [hOuts14] at hOdd; injection hOdd with hSt14
  have hpPos : (0 : Nat) < goldilocksPrime := by unfold goldilocksPrime; omega
  have hSubLtP := Nat.mod_lt (u_t % goldilocksPrime + goldilocksPrime - (v_t * w_t) % goldilocksPrime) hpPos
  have hvwLt := Nat.mod_lt (v_t * w_t) hpPos
  rw [show (st 14).toNat = (u_t % goldilocksPrime + goldilocksPrime - (v_t * w_t) % goldilocksPrime) % goldilocksPrime
    from by rw [hSt14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_two_pow_64_of_lt_prime hSubLtP)]]
  have hIntMod : (((u_t % goldilocksPrime + goldilocksPrime - (v_t * w_t) % goldilocksPrime) %
      goldilocksPrime : Nat) : Int) = (((u_t % goldilocksPrime : Nat) : Int) + (goldilocksPrime : Int) -
      (((v_t * w_t) % goldilocksPrime : Nat) : Int)) % (goldilocksPrime : Int) := by
    rw [Int.natCast_emod]; congr 1; omega
  rw [hIntMod, Int.natCast_emod, Int.natCast_emod, Int.natCast_mul]
  have hShift : (u_t : Int) % (goldilocksPrime : Int) + (goldilocksPrime : Int) -
      ((v_t : Int) * (w_t : Int)) % (goldilocksPrime : Int) =
      ((u_t : Int) % (goldilocksPrime : Int) - ((v_t : Int) * (w_t : Int)) % (goldilocksPrime : Int)) +
        (goldilocksPrime : Int) * 1 := by omega
  rw [hShift, Int.add_mul_emod_self_left, ← Int.sub_emod]

/-! ## 3. Wiedemann (1988) Binary-Tower Field $\mathcal{T}_0 \subset \dots \subset \mathcal{T}_6 = \mathbb{F}_{2^{64}} \subset \mathcal{T}_7 = \mathbb{F}_{2^{128}}$ -/

abbrev TowerElem (k : Nat) : Type := BitVec (2 ^ k)
abbrev Tower64 : Type := BitVec 64
abbrev Tower128 : Type := BitVec 64 × BitVec 64

def towerLo {k : Nat} (a : BitVec (2 ^ (k + 1))) : BitVec (2 ^ k) := a.setWidth (2 ^ k)
def towerHi {k : Nat} (a : BitVec (2 ^ (k + 1))) : BitVec (2 ^ k) := (a >>> (2 ^ k)).setWidth (2 ^ k)
def towerJoin {k : Nat} (lo hi : BitVec (2 ^ k)) : BitVec (2 ^ (k + 1)) :=
  (hi.append lo).cast (by rw [Nat.pow_succ]; omega)

@[expose] def towerZero (k : Nat) : BitVec (2 ^ k) := 0#(2 ^ k)
@[expose] def towerOne (k : Nat) : BitVec (2 ^ k) := 1#(2 ^ k)
@[expose] def towerOmega : (k : Nat) → BitVec (2 ^ k)
  | 0 => 1#1 | k + 1 => towerJoin (towerZero k) (towerOne k)
@[expose] def towerAdd (k : Nat) (a b : BitVec (2 ^ k)) : BitVec (2 ^ k) := a ^^^ b

def towerMulOmega : (k : Nat) → BitVec (2 ^ k) → BitVec (2 ^ k)
  | 0, u => u
  | k + 1, u => towerJoin (towerHi u) (towerLo u ^^^ towerMulOmega k (towerHi u))

/-- **Recursive 3-Submultiplication Karatsuba-Wiedemann Binary-Tower Multiplier**. -/
@[expose] def towerMul : (k : Nat) → BitVec (2 ^ k) → BitVec (2 ^ k) → BitVec (2 ^ k)
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let a0 := towerLo a; let a1 := towerHi a; let b0 := towerLo b; let b1 := towerHi b
    let p0 := towerMul k a0 b0; let p1 := towerMul k a1 b1
    let p01 := towerMul k (a0 ^^^ a1) (b0 ^^^ b1)
    let lo := p0 ^^^ p1
    towerJoin lo ((p01 ^^^ lo) ^^^ towerMulOmega k p1)

/-- **Recursive Norm-Reduction Wiedemann Tower Multiplicative Inverse (`towerInv`)**. -/
@[expose] def towerInv : (k : Nat) → BitVec (2 ^ k) → BitVec (2 ^ k)
  | 0, a => a
  | k + 1, a =>
    let a0 := towerLo a; let a1 := towerHi a
    let a0Shift := a0 ^^^ towerMulOmega k a1
    let d := towerInv k (towerMul k a0 a0Shift ^^^ towerMul k a1 a1)
    towerJoin (towerMul k d a0Shift) (towerMul k d a1)

def tower128Mul (a b : Tower128) : Tower128 :=
  let prod := towerMul 7 (towerJoin (k := 6) a.1 a.2) (towerJoin (k := 6) b.1 b.2)
  (towerLo (k := 6) prod, towerHi (k := 6) prod)

def tower128Inv (a : Tower128) : Tower128 :=
  let inv := towerInv 7 (towerJoin (k := 6) a.1 a.2)
  (towerLo (k := 6) inv, towerHi (k := 6) inv)

/-! ### 3a. Split/Join Bijection & Characteristic-2 Commutative Ring Algebra -/

private theorem getLsbD_towerJoin {k : Nat} (lo hi : BitVec (2 ^ k)) (i : Nat) :
    (towerJoin lo hi).getLsbD i = if i < 2 ^ k then lo.getLsbD i else hi.getLsbD (i - 2 ^ k) := by
  simp [towerJoin, BitVec.getLsbD_cast, BitVec.getLsbD_append]

theorem towerLo_join {k : Nat} (lo hi : BitVec (2 ^ k)) : towerLo (towerJoin lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hiLt; simp [towerLo, getLsbD_towerJoin, hiLt]

theorem towerHi_join {k : Nat} (lo hi : BitVec (2 ^ k)) : towerHi (towerJoin lo hi) = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hiLt
  rw [towerHi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, getLsbD_towerJoin]
  have hnot : ¬ (2 ^ k + i < 2 ^ k) := by omega
  have hsub : 2 ^ k + i - 2 ^ k = i := by omega
  simp [hiLt, hnot, hsub]

theorem towerJoin_lo_hi {k : Nat} (x : BitVec (2 ^ (k + 1))) : towerJoin (towerLo x) (towerHi x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hiLt
  rw [getLsbD_towerJoin]; split
  · rename_i hlt; simp [towerLo, hlt]
  · rename_i hge
    have hlt2 : i - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hiLt; omega
    have hadd : 2 ^ k + (i - 2 ^ k) = i := by omega
    simp [towerHi, BitVec.getLsbD_ushiftRight, hlt2, hadd]

private theorem towerLo_xor {k : Nat} (a b : BitVec (2 ^ (k + 1))) :
    towerLo (a ^^^ b) = towerLo a ^^^ towerLo b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [towerLo, hi]
private theorem towerHi_xor {k : Nat} (a b : BitVec (2 ^ (k + 1))) :
    towerHi (a ^^^ b) = towerHi a ^^^ towerHi b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [towerHi, hi]
private theorem towerJoin_xor {k : Nat} (a0 a1 b0 b1 : BitVec (2 ^ k)) :
    towerJoin (a0 ^^^ b0) (a1 ^^^ b1) = towerJoin a0 a1 ^^^ towerJoin b0 b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor, getLsbD_towerJoin]; split <;> simp
private theorem towerZero_succ (k : Nat) : towerZero (k + 1) = towerJoin (towerZero k) (towerZero k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [towerZero, getLsbD_towerJoin]
private theorem towerOne_succ (k : Nat) : towerOne (k + 1) = towerJoin (towerOne k) (towerZero k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hiLt
  simp only [towerOne, towerZero, getLsbD_towerJoin, BitVec.getLsbD_one, BitVec.getLsbD_zero]
  by_cases h0 : i = 0
  · subst h0; simp [Nat.two_pow_pos k, hiLt]
  · simp [h0]
private theorem xor_towerZero {k : Nat} (a : BitVec (2 ^ k)) : a ^^^ towerZero k = a := by simp [towerZero]
private theorem towerZero_xor {k : Nat} (a : BitVec (2 ^ k)) : towerZero k ^^^ a = a := by simp [towerZero]
private theorem xor_self_towerZero {k : Nat} (a : BitVec (2 ^ k)) : a ^^^ a = towerZero k := by simp [towerZero]
private theorem bv_xor_cancel_left {w : Nat} (x y : BitVec w) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem towerAdd_comm (k : Nat) (a b : BitVec (2 ^ k)) : towerAdd k a b = towerAdd k b a := BitVec.xor_comm a b
theorem towerAdd_assoc (k : Nat) (a b c : BitVec (2 ^ k)) :
    towerAdd k (towerAdd k a b) c = towerAdd k a (towerAdd k b c) := BitVec.xor_assoc a b c
theorem towerAdd_zero_right (k : Nat) (a : BitVec (2 ^ k)) : towerAdd k a (towerZero k) = a := xor_towerZero a
theorem towerAdd_zero_left (k : Nat) (a : BitVec (2 ^ k)) : towerAdd k (towerZero k) a = a := towerZero_xor a
theorem towerAdd_self_zero (k : Nat) (a : BitVec (2 ^ k)) : towerAdd k a a = towerZero k := xor_self_towerZero a

theorem towerMulOmega_zero (k : Nat) : towerMulOmega k (towerZero k) = towerZero k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [towerZero_succ]; unfold towerMulOmega; rw [towerLo_join, towerHi_join, ih, xor_self_towerZero]

theorem towerMulOmega_add (k : Nat) (a b : BitVec (2 ^ k)) :
    towerMulOmega k (a ^^^ b) = towerMulOmega k a ^^^ towerMulOmega k b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold towerMulOmega; rw [towerLo_xor, towerHi_xor, ih, ← towerJoin_xor]; congr 1
    rw [BitVec.xor_assoc, ← BitVec.xor_assoc (towerLo b), BitVec.xor_comm (towerLo b),
      BitVec.xor_assoc, BitVec.xor_assoc]

theorem towerMul_comm (k : Nat) (a b : BitVec (2 ^ k)) : towerMul k a b = towerMul k b a := by
  induction k with
  | zero => exact BitVec.and_comm a b
  | succ k ih =>
    unfold towerMul; dsimp only
    rw [ih (towerLo a) (towerLo b), ih (towerHi a) (towerHi b),
      BitVec.xor_comm (towerLo a) (towerHi a), BitVec.xor_comm (towerLo b) (towerHi b),
      ih (towerHi a ^^^ towerLo a) (towerHi b ^^^ towerLo b)]

theorem towerMul_zero (k : Nat) (a : BitVec (2 ^ k)) : towerMul k a (towerZero k) = towerZero k := by
  induction k with
  | zero => simp [towerMul, towerZero]
  | succ k ih =>
    rw [towerZero_succ]; unfold towerMul; dsimp only
    rw [towerLo_join, towerHi_join, xor_self_towerZero, ih, ih, ih,
      xor_self_towerZero, xor_self_towerZero, towerMulOmega_zero, xor_self_towerZero]

theorem towerZero_mul (k : Nat) (a : BitVec (2 ^ k)) : towerMul k (towerZero k) a = towerZero k := by
  rw [towerMul_comm, towerMul_zero]

theorem towerMul_distrib_left (k : Nat) (a b c : BitVec (2 ^ k)) :
    towerMul k a (towerAdd k b c) = towerAdd k (towerMul k a b) (towerMul k a c) := by
  induction k with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [towerMul, towerAdd, BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl
  | succ k ih =>
    unfold towerAdd at *; unfold towerMul; dsimp only; rw [towerLo_xor, towerHi_xor]
    have hSum : (towerLo b ^^^ towerLo c) ^^^ (towerHi b ^^^ towerHi c) =
        (towerLo b ^^^ towerHi b) ^^^ (towerLo c ^^^ towerHi c) := by
      rw [BitVec.xor_assoc, ← BitVec.xor_assoc (towerLo c), BitVec.xor_comm (towerLo c),
        BitVec.xor_assoc, BitVec.xor_assoc]
    rw [hSum, ih, ih, ih, towerMulOmega_add, ← towerJoin_xor]; congr 1
    · rw [BitVec.xor_assoc, ← BitVec.xor_assoc (towerMul k (towerLo a) (towerLo c)),
        BitVec.xor_comm (towerMul k (towerLo a) (towerLo c)), BitVec.xor_assoc, BitVec.xor_assoc]
    · generalize towerMul k (towerLo a) (towerLo b) = x0; generalize towerMul k (towerLo a) (towerLo c) = y0
      generalize towerMul k (towerHi a) (towerHi b) = x1; generalize towerMul k (towerHi a) (towerHi c) = y1
      generalize towerMul k (towerLo a ^^^ towerHi a) (towerLo b ^^^ towerHi b) = x2
      generalize towerMul k (towerLo a ^^^ towerHi a) (towerLo c ^^^ towerHi c) = y2
      generalize towerMulOmega k x1 = xt; generalize towerMulOmega k y1 = yt
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
      cases x0.getLsbD i <;> cases y0.getLsbD i <;> cases x1.getLsbD i <;> cases y1.getLsbD i <;>
        cases x2.getLsbD i <;> cases y2.getLsbD i <;> cases xt.getLsbD i <;> cases yt.getLsbD i <;> rfl

theorem towerMul_distrib_right (k : Nat) (a b c : BitVec (2 ^ k)) :
    towerMul k (towerAdd k a b) c = towerAdd k (towerMul k a c) (towerMul k b c) := by
  rw [towerMul_comm, towerMul_distrib_left, towerMul_comm k c a, towerMul_comm k c b]

theorem towerMul_succ_bilinear (k : Nat) (a b : BitVec (2 ^ (k + 1))) :
    towerMul (k + 1) a b =
      towerJoin (towerMul k (towerLo a) (towerLo b) ^^^ towerMul k (towerHi a) (towerHi b))
        ((towerMul k (towerLo a) (towerHi b) ^^^ towerMul k (towerHi a) (towerLo b)) ^^^
          towerMulOmega k (towerMul k (towerHi a) (towerHi b))) := by
  conv => lhs; unfold towerMul
  dsimp only; apply congrArg (towerJoin _)
  have d1 := towerMul_distrib_right k (towerLo a) (towerHi a) (towerLo b ^^^ towerHi b)
  have d2 := towerMul_distrib_left k (towerLo a) (towerLo b) (towerHi b)
  have d3 := towerMul_distrib_left k (towerHi a) (towerLo b) (towerHi b)
  unfold towerAdd at d1 d2 d3; rw [d1, d2, d3]
  generalize towerMul k (towerLo a) (towerLo b) = p00; generalize towerMul k (towerLo a) (towerHi b) = p01
  generalize towerMul k (towerHi a) (towerLo b) = p10; generalize towerMul k (towerHi a) (towerHi b) = p11
  generalize towerMulOmega k p11 = pt
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
  cases p00.getLsbD i <;> cases p01.getLsbD i <;> cases p10.getLsbD i <;>
    cases p11.getLsbD i <;> cases pt.getLsbD i <;> rfl

theorem towerMul_one (k : Nat) (a : BitVec (2 ^ k)) : towerMul k a (towerOne k) = a := by
  induction k with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hi0 : i = 0 := by omega
    subst hi0; simp [towerMul, towerOne]
  | succ k ih =>
    rw [towerOne_succ, towerMul_succ_bilinear, towerLo_join, towerHi_join,
      ih, towerMul_zero, towerMul_zero, ih,
      xor_towerZero, towerZero_xor, towerMulOmega_zero, xor_towerZero, towerJoin_lo_hi]

theorem towerOne_mul (k : Nat) (a : BitVec (2 ^ k)) : towerMul k (towerOne k) a = a := by
  rw [towerMul_comm, towerMul_one]

theorem towerMulOmega_eq_mul_omega (k : Nat) (u : BitVec (2 ^ k)) :
    towerMulOmega k u = towerMul k u (towerOmega k) := by
  induction k with
  | zero => exact (towerMul_one 0 u).symm
  | succ k ih =>
    change towerJoin (towerHi u) (towerLo u ^^^ towerMulOmega k (towerHi u)) =
      towerMul (k + 1) u (towerJoin (towerZero k) (towerOne k))
    rw [towerMul_succ_bilinear, towerLo_join, towerHi_join,
      towerMul_zero, towerMul_one, towerMul_one, towerMul_zero, towerZero_xor, xor_towerZero, ih]

/-- **Universal Associativity of Wiedemann Binary-Tower Multiplication (`towerMul_assoc`)**. -/
theorem towerMul_assoc (k : Nat) (a b c : BitVec (2 ^ k)) :
    towerMul k (towerMul k a b) c = towerMul k a (towerMul k b c) := by
  induction k with
  | zero => exact BitVec.and_assoc a b c
  | succ k ih =>
    have mulOmega_assoc : ∀ x y : BitVec (2 ^ k),
        towerMul k (towerMulOmega k x) y = towerMulOmega k (towerMul k x y) := fun x y => by
      rw [towerMulOmega_eq_mul_omega, towerMulOmega_eq_mul_omega,
        ih x (towerOmega k) y, towerMul_comm k (towerOmega k) y, ← ih]
    have mulOmega_right : ∀ x y : BitVec (2 ^ k),
        towerMul k x (towerMulOmega k y) = towerMulOmega k (towerMul k x y) := fun x y => by
      rw [towerMul_comm, mulOmega_assoc, towerMul_comm]
    rw [towerMul_succ_bilinear k a b, towerMul_succ_bilinear k _ c,
      towerMul_succ_bilinear k b c, towerMul_succ_bilinear k a _,
      towerLo_join, towerHi_join, towerLo_join, towerHi_join]
    let a0 := towerLo a; let a1 := towerHi a; let b0 := towerLo b; let b1 := towerHi b
    let c0 := towerLo c; let c1 := towerHi c
    have dL := fun x y z => towerMul_distrib_left k x y z
    have dR := fun x y z => towerMul_distrib_right k x y z
    unfold towerAdd at dL dR; congr 1
    · rw [dR, dR, dR, dL, dL, dL, mulOmega_assoc, mulOmega_right,
        ih a0 b0 c0, ih a1 b1 c0, ih a0 b1 c1, ih a1 b0 c1, ih a1 b1 c1]
      generalize towerMul k a0 (towerMul k b0 c0) = t1; generalize towerMul k a1 (towerMul k b1 c0) = t2
      generalize towerMul k a0 (towerMul k b1 c1) = t3; generalize towerMul k a1 (towerMul k b0 c1) = t4
      generalize towerMulOmega k (towerMul k a1 (towerMul k b1 c1)) = t5
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
      cases t1.getLsbD i <;> cases t2.getLsbD i <;> cases t3.getLsbD i <;>
        cases t4.getLsbD i <;> cases t5.getLsbD i <;> rfl
    · simp only [dR, dL, mulOmega_assoc, mulOmega_right, towerMulOmega_add, ih]
      generalize towerMul k a0 (towerMul k b0 c1) = u1; generalize towerMul k a0 (towerMul k b1 c0) = u2
      generalize towerMul k a1 (towerMul k b0 c0) = u3; generalize towerMul k a1 (towerMul k b1 c1) = u4
      generalize towerMulOmega k (towerMul k a1 (towerMul k b1 c0)) = v1
      generalize towerMulOmega k (towerMul k a0 (towerMul k b1 c1)) = v2
      generalize towerMulOmega k (towerMul k a1 (towerMul k b0 c1)) = v3
      generalize towerMulOmega k (towerMulOmega k u4) = w1
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
      cases u1.getLsbD i <;> cases u2.getLsbD i <;> cases u3.getLsbD i <;> cases u4.getLsbD i <;>
        cases v1.getLsbD i <;> cases v2.getLsbD i <;> cases v3.getLsbD i <;> cases w1.getLsbD i <;> rfl

/-- Explicit Wiedemann defining polynomial identity $X_k^2 \oplus \omega_{k-1} X_k \oplus 1 = 0$. -/
theorem tower_defining_relation (k : Nat) :
    let xk := towerOmega (k + 1); let omega := towerJoin (towerOmega k) (towerZero k)
    towerAdd (k + 1) (towerAdd (k + 1) (towerMul (k + 1) xk xk) (towerMul (k + 1) omega xk))
      (towerOne (k + 1)) = towerZero (k + 1) := by
  intro xk omega
  have hxk : xk = towerJoin (towerZero k) (towerOne k) := rfl
  have hSq : towerMul (k + 1) xk xk = towerJoin (towerOne k) (towerOmega k) := by
    rw [hxk, towerMul_succ_bilinear, towerLo_join, towerHi_join]
    simp only [towerMul_zero, towerMul_one, towerOne_mul, towerZero_xor, xor_self_towerZero,
      towerMulOmega_eq_mul_omega]
  have hLin : towerMul (k + 1) omega xk = towerJoin (towerZero k) (towerOmega k) := by
    dsimp only [omega]
    rw [hxk, towerMul_succ_bilinear, towerLo_join, towerHi_join, towerLo_join, towerHi_join]
    simp only [towerMul_zero, towerMul_one, xor_towerZero, xor_self_towerZero, towerMulOmega_zero]
  unfold towerAdd
  rw [hSq, hLin, towerOne_succ, ← towerJoin_xor, ← towerJoin_xor,
    xor_towerZero, xor_self_towerZero, xor_self_towerZero, xor_towerZero, towerZero_succ]

/-! ### 3b. Wiedemann Artin–Schreier Trace Theorem & Universal Field Inversion (`towerMul_inv`) -/

private def towerTrace : (k : Nat) → BitVec (2 ^ k) → BitVec 1
  | 0, x => x | k + 1, x => towerTrace k (towerMulOmega k (towerHi x))
private def towerOmegaInv : (k : Nat) → BitVec (2 ^ k)
  | 0 => 1#1 | k + 1 => towerJoin (towerOmega k) (towerOne k)
private theorem towerTrace_zero (k : Nat) : towerTrace k (towerZero k) = 0#1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [towerZero_succ]; unfold towerTrace; rw [towerHi_join, towerMulOmega_zero, ih]
private theorem towerTrace_add (k : Nat) (a b : BitVec (2 ^ k)) :
    towerTrace k (a ^^^ b) = towerTrace k a ^^^ towerTrace k b := by
  induction k with
  | zero => rfl
  | succ k ih => unfold towerTrace; rw [towerHi_xor, towerMulOmega_add, ih]

private theorem towerTrace_sq (k : Nat) (x : BitVec (2 ^ k)) :
    towerTrace k (towerMul k x x) = towerTrace k x := by
  induction k with
  | zero => simp [towerTrace, towerMul]
  | succ k ih =>
    rw [towerMul_succ_bilinear]; unfold towerTrace
    rw [towerHi_join, towerMul_comm k (towerHi x) (towerLo x), xor_self_towerZero, towerZero_xor]
    have hSqOmega : towerMulOmega k (towerMulOmega k (towerMul k (towerHi x) (towerHi x))) =
        towerMul k (towerMulOmega k (towerHi x)) (towerMulOmega k (towerHi x)) := by
      rw [towerMulOmega_eq_mul_omega, towerMulOmega_eq_mul_omega, towerMulOmega_eq_mul_omega]
      let u := towerHi x; let w := towerOmega k
      rw [towerMul_assoc k (towerMul k u u) w w, towerMul_assoc k u u (towerMul k w w),
        ← towerMul_assoc k u w w, towerMul_comm k (towerMul k u w) w,
        ← towerMul_assoc k u w (towerMul k u w)]
    rw [hSqOmega, ih]

theorem towerOne_ne_zero (k : Nat) : towerOne k ≠ towerZero k := by
  intro h; have h0 := congrArg (fun v => v.getLsbD 0) h
  simp [towerOne, towerZero, Nat.two_pow_pos k] at h0
private theorem towerMul_four (k : Nat) (x y z v : BitVec (2 ^ k)) :
    towerMul k (towerMul k x y) (towerMul k z v) = towerMul k (towerMul k x z) (towerMul k y v) := by
  rw [towerMul_assoc k x y (towerMul k z v), ← towerMul_assoc k y z v,
    towerMul_comm k y z, towerMul_assoc k z y v, ← towerMul_assoc k x z (towerMul k y v)]
private theorem towerMul_omega_omegaInv (k : Nat) :
    towerMul k (towerOmega k) (towerOmegaInv k) = towerOne k := by
  cases k with
  | zero => rfl
  | succ k =>
    change towerMul (k + 1) (towerJoin (towerZero k) (towerOne k))
      (towerJoin (towerOmega k) (towerOne k)) = towerOne (k + 1)
    rw [towerMul_succ_bilinear, towerLo_join, towerHi_join, towerLo_join, towerHi_join]
    simp only [towerZero_mul, towerMul_one, towerOne_mul, towerZero_xor,
      towerMulOmega_eq_mul_omega, xor_self_towerZero, ← towerOne_succ]
private theorem towerTrace_omega (k : Nat) : towerTrace k (towerOmega k) = 1#1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change towerTrace k (towerMulOmega k (towerHi (towerJoin (towerZero k) (towerOne k)))) = 1#1
    rw [towerHi_join, towerMulOmega_eq_mul_omega, towerOne_mul, ih]
private theorem towerTrace_omegaInv (k : Nat) : towerTrace k (towerOmegaInv k) = 1#1 := by
  cases k with
  | zero => rfl
  | succ k =>
    change towerTrace k (towerMulOmega k (towerHi (towerJoin (towerOmega k) (towerOne k)))) = 1#1
    rw [towerHi_join, towerMulOmega_eq_mul_omega, towerOne_mul, towerTrace_omega]

/-- **Universal Multiplicative Inverse in the Wiedemann Binary Tower (`towerMul_inv`)**. -/
theorem towerMul_inv (k : Nat) (a : BitVec (2 ^ k)) (ha : a ≠ towerZero k) :
    towerMul k a (towerInv k a) = towerOne k := by
  induction k with
  | zero =>
    have hlt : a.toNat < 2 := a.isLt
    by_cases h0 : a.toNat = 0
    · exact absurd (BitVec.eq_of_toNat_eq h0) ha
    · have ha1 : a = 1#1 := BitVec.eq_of_toNat_eq (by change a.toNat = 1; omega)
      subst ha1; rfl
  | succ k ih =>
    let a0 := towerLo a; let a1 := towerHi a; let w := towerOmega k
    let a0s := a0 ^^^ towerMulOmega k a1
    let norm := towerMul k a0 a0s ^^^ towerMul k a1 a1
    have hNormNe : norm ≠ towerZero k := by
      intro hNorm0
      by_cases ha1 : a1 = towerZero k
      · have ha0 : a0 ≠ towerZero k := fun ha0 => ha (by
          rw [← towerJoin_lo_hi a]; change towerJoin a0 a1 = _
          rw [ha0, ha1, ← towerZero_succ])
        have hSq0 : towerMul k a0 a0 = towerZero k := by
          dsimp only [norm, a0s] at hNorm0
          rw [ha1, towerMulOmega_zero, xor_towerZero, towerMul_zero, xor_towerZero] at hNorm0
          exact hNorm0
        have hInv0 := ih a0 ha0
        have : a0 = towerZero k := calc
          a0 = towerMul k a0 (towerOne k) := (towerMul_one k a0).symm
          _  = towerMul k a0 (towerMul k a0 (towerInv k a0)) := by rw [hInv0]
          _  = towerMul k (towerMul k a0 a0) (towerInv k a0) := (towerMul_assoc k _ _ _).symm
          _  = towerZero k := by rw [hSq0, towerZero_mul]
        exact ha0 this
      · let a1i := towerInv k a1; have h1 : towerMul k a1 a1i = towerOne k := ih a1 ha1
        let wi := towerOmegaInv k; have hw : towerMul k w wi = towerOne k := towerMul_omega_omegaInv k
        let u := towerMul k a1i wi; let q := towerMul k a0 u
        have hdL := fun x y z => towerMul_distrib_left k x y z
        have hdR := fun x y z => towerMul_distrib_right k x y z
        unfold towerAdd at hdL hdR
        have ha1u : towerMul k a1 u = wi := by dsimp only [u]; rw [← towerMul_assoc, h1, towerOne_mul]
        have ha1wu : towerMul k (towerMul k a1 w) u = towerOne k := by
          dsimp only [u]; rw [towerMul_four, h1, hw, towerOne_mul]
        have hScaled : (towerMul k q q ^^^ q) ^^^ towerMul k wi wi =
            towerMul k norm (towerMul k u u) := by
          dsimp only [norm, a0s, q]
          rw [towerMulOmega_eq_mul_omega, hdL a0 a0 (towerMul k a1 w), hdR, hdR,
            towerMul_four k a0 a0 u u, towerMul_four k a0 (towerMul k a1 w) u u,
            ha1wu, towerMul_one, towerMul_four k a1 a1 u u, ha1u]
        have hAS : (towerMul k q q ^^^ q) ^^^ towerMul k wi wi = towerZero k := by
          rw [hScaled, hNorm0, towerZero_mul]
        have hTr := congrArg (towerTrace k) hAS
        rw [towerTrace_add, towerTrace_add, towerTrace_sq, BitVec.xor_self, BitVec.zero_xor,
          towerTrace_sq, towerTrace_omegaInv, towerTrace_zero] at hTr
        exact absurd hTr (by decide)
    let d := towerInv k norm
    have hd : towerMul k d norm = towerOne k := by rw [towerMul_comm, ih norm hNormNe]
    have hdL := fun x y z => towerMul_distrib_left k x y z
    unfold towerAdd at hdL
    have hPull : ∀ x y : BitVec (2 ^ k),
        towerMul k x (towerMul k d y) = towerMul k d (towerMul k x y) := fun x y => by
      rw [← towerMul_assoc, towerMul_comm k x d, towerMul_assoc]
    change towerMul (k + 1) a (towerJoin (towerMul k d a0s) (towerMul k d a1)) = towerOne (k + 1)
    rw [towerMul_succ_bilinear, towerLo_join, towerHi_join]
    have hLo : towerMul k a0 (towerMul k d a0s) ^^^ towerMul k a1 (towerMul k d a1) = towerOne k := by
      rw [hPull, hPull, ← hdL, hd]
    have hHi : (towerMul k a0 (towerMul k d a1) ^^^ towerMul k a1 (towerMul k d a0s)) ^^^
        towerMulOmega k (towerMul k a1 (towerMul k d a1)) = towerZero k := by
      rw [hPull a0 a1, hPull a1 a0s, hPull a1 a1]; dsimp only [a0s]
      rw [hdL a1 a0 (towerMulOmega k a1), hdL d (towerMul k a1 a0) _, towerMul_comm k a1 a0,
        bv_xor_cancel_left]
      have hOmPull : towerMulOmega k (towerMul k d (towerMul k a1 a1)) =
          towerMul k d (towerMul k a1 (towerMulOmega k a1)) := by
        rw [towerMulOmega_eq_mul_omega, towerMulOmega_eq_mul_omega,
          towerMul_assoc k d (towerMul k a1 a1) w, towerMul_assoc k a1 a1 w]
      rw [hOmPull, xor_self_towerZero]
    rw [hLo, hHi, ← towerOne_succ]

theorem towerInv_mul (k : Nat) (a : BitVec (2 ^ k)) (ha : a ≠ towerZero k) :
    towerMul k (towerInv k a) a = towerOne k := by rw [towerMul_comm, towerMul_inv k a ha]

theorem tower128Mul_inv (a : Tower128) (ha : a ≠ (0#64, 0#64)) :
    tower128Mul a (tower128Inv a) = (1#64, 0#64) := by
  unfold tower128Mul tower128Inv; dsimp only; rw [towerJoin_lo_hi]
  have hNe : towerJoin (k := 6) a.1 a.2 ≠ towerZero 7 := fun h0 => ha (by
    have hLo := congrArg (towerLo (k := 6)) h0; have hHi := congrArg (towerHi (k := 6)) h0
    rw [towerZero_succ, towerLo_join, towerLo_join] at hLo
    rw [towerZero_succ, towerHi_join, towerHi_join] at hHi
    exact Prod.ext hLo hHi)
  rw [towerMul_inv 7 _ hNe, towerOne_succ, towerLo_join, towerHi_join]; rfl

/-! ## 4. Carry-Free SWAR-Karatsuba + 2-Stage Pipelined `GF(2^{64})` `RtlModule` -/
private def swarMask : Nat → BitVec 64
  | 0 => 0x5555555555555555#64 | 1 => 0x3333333333333333#64 | 2 => 0x0F0F0F0F0F0F0F0F#64
  | 3 => 0x00FF00FF00FF00FF#64 | 4 => 0x0000FFFF0000FFFF#64 | _ => 0x00000000FFFFFFFF#64
private def swarMulOmegaBV : Nat → BitVec 64 → BitVec 64
  | 0, u => u
  | k + 1, u =>
    let m := swarMask k; let sh := BitVec.ofNat 64 (2 ^ k)
    let u0 := evalAluOp .bitAnd u m; let u1 := evalAluOp .bitAnd (evalAluOp .lshr u sh) m
    evalAluOp .bitOr u1 (evalAluOp .shl (evalAluOp .bitXor u0 (swarMulOmegaBV k u1)) sh)
private def swarCombineBV (k : Nat) (p q : BitVec 64) : BitVec 64 :=
  let m := swarMask k; let sh := BitVec.ofNat 64 (2 ^ k)
  let p0 := evalAluOp .bitAnd p m; let p1 := evalAluOp .bitAnd (evalAluOp .lshr p sh) m
  let lo := evalAluOp .bitXor p0 p1
  evalAluOp .bitOr lo (evalAluOp .shl (evalAluOp .bitXor (evalAluOp .bitXor q lo) (swarMulOmegaBV k p1)) sh)
private def swarMulBV : Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, x, y => evalAluOp .bitAnd x y
  | k + 1, x, y =>
    let sh := BitVec.ofNat 64 (2 ^ k)
    let xf := evalAluOp .bitXor x (evalAluOp .lshr x sh)
    let yf := evalAluOp .bitXor y (evalAluOp .lshr y sh)
    swarCombineBV k (swarMulBV k x y) (evalAluOp .bitAnd (swarMulBV k xf yf) (swarMask k))
private def pushSwarMulOmega : Nat → WireB → RtlExpr → RtlExpr × WireB
  | 0, s, u => (u, s)
  | k + 1, s, u =>
    let m := RtlExpr.const (swarMask k); let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
    let (u1, s1) := pushW s "sw_u1" (.alu .bitAnd (.alu .lshr u sh) m)
    let (om, s2) := pushSwarMulOmega k s1 u1
    (.alu .bitOr u1 (.alu .shl (.alu .bitXor (.alu .bitAnd u m) om) sh), s2)
private def pushSwarCombine (k : Nat) (s : WireB) (p q : RtlExpr) : RtlExpr × WireB :=
  let m := RtlExpr.const (swarMask k); let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
  let (p1, s1) := pushW s  "sw_p1" (.alu .bitAnd (.alu .lshr p sh) m)
  let (lo, s2) := pushW s1 "sw_lo" (.alu .bitXor (.alu .bitAnd p m) p1)
  let (om, s3) := pushSwarMulOmega k s2 p1
  pushW s3 "sw_out" (.alu .bitOr lo (.alu .shl (.alu .bitXor (.alu .bitXor q lo) om) sh))
private def pushSwarMul : Nat → WireB → RtlExpr → RtlExpr → RtlExpr × WireB
  | 0, s, x, y => pushW s "sw_and" (.alu .bitAnd x y)
  | k + 1, s, x, y =>
    let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
    let (p, s1)  := pushSwarMul k s x y
    let (xf, s2) := pushW s1 "sw_xf" (.alu .bitXor x (.alu .lshr x sh))
    let (yf, s3) := pushW s2 "sw_yf" (.alu .bitXor y (.alu .lshr y sh))
    let (qr, s4) := pushSwarMul k s3 xf yf
    pushSwarCombine k s4 p (.alu .bitAnd qr (.const (swarMask k)))
private def buildGf2_64TowerMul : List OutputPort × List RegSpec × WireB :=
  let aIn := RtlExpr.inputPort 0; let bIn := RtlExpr.inputPort 1
  let sh5 := RtlExpr.const (BitVec.ofNat 64 (2 ^ 5))
  let (p5, s1)      := pushSwarMul 5 {} aIn bIn
  let (xf5, s2)     := pushW s1 "t64_xf" (.alu .bitXor aIn (.alu .lshr aIn sh5))
  let (yf5, s3)     := pushW s2 "t64_yf" (.alu .bitXor bIn (.alu .lshr bIn sh5))
  let (q5r, s4)     := pushSwarMul 5 s3 xf5 yf5
  let (q5, s5)      := pushW s4 "t64_q" (.alu .bitAnd q5r (.const (swarMask 5)))
  let (combOut, s6) := pushSwarCombine 5 s5 p5 q5
  let (pipeNx, s7)  := pushSwarCombine 5 s6 (.regRead 0) (.regRead 1)
  let (valIn, s8)   := pushW s7 "t64_val" (.resize (.trunc 1) (.inputPort 2)) 1
  let mkReg (idx : Nat) (name : String) (nx : RtlExpr) (w : Nat := 64) : RegSpec :=
    { regIdx := idx, name := name, domain := .coreClk, resetKind := .syncReset 0#64
      isSynchronizer := false, nextExpr := nx, width := w }
  let regs : List RegSpec :=
    [ mkReg 0 "s1_p32" p5, mkReg 1 "s1_q32" q5, mkReg 2 "s1_valid" valIn 1
    , mkReg 3 "s2_pipe_out" pipeNx, mkReg 4 "s2_pipe_valid" (.regRead 2) 1 ]
  let outs : List OutputPort :=
    [ { name := "tower64_mul_out",    expr := combOut,    width := 64 }
    , { name := "tower64_pipe_out",   expr := .regRead 3, width := 64 }
    , { name := "tower64_pipe_valid", expr := .regRead 4, width := 1 } ]
  (outs, regs, s8)
private def t64Built : List OutputPort × List RegSpec × WireB := buildGf2_64TowerMul
private def t64Regs  : List RegSpec := t64Built.2.1
/-- **Carry-Free SWAR-Karatsuba + 2-Stage Pipelined `GF(2^{64})` Binary-Tower Multiplier `RtlModule`**. -/
def gf2_64TowerMulRtlModule : RtlModule :=
  { name := "gf2_64_wiedemann_tower_mul"
    inputNames := ["a_in", "b_in", "in_valid"], inputWidths := [64, 64, 1]
    wires := t64Built.2.2.rev.reverse, regs := t64Regs, outputs := t64Built.1 }
@[expose] def gf2_64Inputs (a b : BitVec 64) (valid : BitVec 64 := 1#64) : Nat → BitVec 64
  | 0 => a | 1 => b | 2 => valid | _ => 0#64
def checkCarryFreeExpr : RtlExpr → Bool
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => true
  | .bitNot a | .resize _ a => checkCarryFreeExpr a
  | .mux c t f => checkCarryFreeExpr c && checkCarryFreeExpr t && checkCarryFreeExpr f
  | .alu op l r =>
    (match op with | .bitAnd | .bitOr | .bitXor | .shl | .lshr => true | _ => false) &&
    checkCarryFreeExpr l && checkCarryFreeExpr r
def checkModuleCarryFree (m : RtlModule) : Bool :=
  m.wires.all (fun w => checkCarryFreeExpr w.expr) &&
  m.regs.all (fun r => checkCarryFreeExpr r.nextExpr) &&
  m.outputs.all (fun o => checkCarryFreeExpr o.expr)
theorem gf2_64TowerMulRtl_wellFormed (u : Unit) (_ : u = ()) :
    checkRtlModuleW gf2_64TowerMulRtlModule = true ∧
    checkModuleCarryFree gf2_64TowerMulRtlModule = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ### 4a. DAG Evaluation & Bit-Exact Equivalence (`gf2_64TowerMulRtl_eq_towerMul`) -/

private theorem pushSwarMulOmega_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr) :
    ∀ (k : Nat) (s : WireB) (u : RtlExpr),
      let r := pushSwarMulOmega k s u
      (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧
      ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
        evalRtlExpr ins fin regs r.1 = swarMulOmegaBV k (evalRtlExpr ins fin regs u)) := by
  intro k; induction k with
  | zero => intro _ _; exact ⟨fun _ h => h, fun _ => rfl⟩
  | succ k ih =>
    intro s u; unfold pushSwarMulOmega; dsimp only
    let m := RtlExpr.const (swarMask k); let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
    obtain ⟨m1, e1⟩ := pushW_spec ins regs fin finalRev hFin s "sw_u1" (.alu .bitAnd (.alu .lshr u sh) m)
    let r1 := pushW s "sw_u1" (.alu .bitAnd (.alu .lshr u sh) m)
    obtain ⟨m2, e2⟩ := ih r1.2 r1.1
    refine ⟨fun wa h => m2 wa (m1 wa h), fun hSub => ?_⟩
    have hSub1 : ∀ wa ∈ r1.2.rev, wa ∈ finalRev := fun wa h => hSub wa (m2 wa h)
    simp only [evalRtlExpr]; rw [e2 hSub, e1 hSub1]; rfl

private theorem pushSwarCombine_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr)
    (k : Nat) (s : WireB) (p q : RtlExpr) :
    let r := pushSwarCombine k s p q
    (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧
    ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
      evalRtlExpr ins fin regs r.1 = swarCombineBV k (evalRtlExpr ins fin regs p) (evalRtlExpr ins fin regs q)) := by
  unfold pushSwarCombine; dsimp only
  let m := RtlExpr.const (swarMask k); let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
  obtain ⟨m1, e1⟩ := pushW_spec ins regs fin finalRev hFin s "sw_p1" (.alu .bitAnd (.alu .lshr p sh) m)
  let r1 := pushW s "sw_p1" (.alu .bitAnd (.alu .lshr p sh) m)
  obtain ⟨m2, e2⟩ := pushW_spec ins regs fin finalRev hFin r1.2 "sw_lo" (.alu .bitXor (.alu .bitAnd p m) r1.1)
  let r2 := pushW r1.2 "sw_lo" (.alu .bitXor (.alu .bitAnd p m) r1.1)
  obtain ⟨m3, e3⟩ := pushSwarMulOmega_spec ins regs fin finalRev hFin k r2.2 r1.1
  let r3 := pushSwarMulOmega k r2.2 r1.1
  obtain ⟨m4, e4⟩ := pushW_spec ins regs fin finalRev hFin r3.2 "sw_out"
    (.alu .bitOr r2.1 (.alu .shl (.alu .bitXor (.alu .bitXor q r2.1) r3.1) sh))
  refine ⟨fun wa h => m4 wa (m3 wa (m2 wa (m1 wa h))), fun hSub => ?_⟩
  have hSub3 : ∀ wa ∈ r3.2.rev, wa ∈ finalRev := fun wa h => hSub wa (m4 wa h)
  have hSub2 : ∀ wa ∈ r2.2.rev, wa ∈ finalRev := fun wa h => hSub3 wa (m3 wa h)
  have hSub1 : ∀ wa ∈ r1.2.rev, wa ∈ finalRev := fun wa h => hSub2 wa (m2 wa h)
  rw [e4 hSub]; simp only [evalRtlExpr]; rw [e3 hSub3, e2 hSub2]; simp only [evalRtlExpr]; rw [e1 hSub1]; rfl

private theorem pushSwarMul_spec (ins regs fin : Nat → BitVec 64) (finalRev : List WireAssign)
    (hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr) :
    ∀ (k : Nat) (s : WireB) (x y : RtlExpr),
      let r := pushSwarMul k s x y
      (∀ wa ∈ s.rev, wa ∈ r.2.rev) ∧
      ((∀ wa ∈ r.2.rev, wa ∈ finalRev) →
        evalRtlExpr ins fin regs r.1 = swarMulBV k (evalRtlExpr ins fin regs x) (evalRtlExpr ins fin regs y)) := by
  intro k; induction k with
  | zero => intro s x y; exact pushW_spec ins regs fin finalRev hFin s "sw_and" (.alu .bitAnd x y)
  | succ k ih =>
    intro s x y; unfold pushSwarMul; dsimp only
    let sh := RtlExpr.const (BitVec.ofNat 64 (2 ^ k))
    obtain ⟨m1, e1⟩ := ih s x y; let r1 := pushSwarMul k s x y
    obtain ⟨m2, e2⟩ := pushW_spec ins regs fin finalRev hFin r1.2 "sw_xf" (.alu .bitXor x (.alu .lshr x sh))
    let r2 := pushW r1.2 "sw_xf" (.alu .bitXor x (.alu .lshr x sh))
    obtain ⟨m3, e3⟩ := pushW_spec ins regs fin finalRev hFin r2.2 "sw_yf" (.alu .bitXor y (.alu .lshr y sh))
    let r3 := pushW r2.2 "sw_yf" (.alu .bitXor y (.alu .lshr y sh))
    obtain ⟨m4, e4⟩ := ih r3.2 r2.1 r3.1; let r4 := pushSwarMul k r3.2 r2.1 r3.1
    obtain ⟨m5, e5⟩ := pushSwarCombine_spec ins regs fin finalRev hFin k r4.2 r1.1
      (.alu .bitAnd r4.1 (.const (swarMask k)))
    refine ⟨fun wa h => m5 wa (m4 wa (m3 wa (m2 wa (m1 wa h)))), fun hSub => ?_⟩
    have hSub4 : ∀ wa ∈ r4.2.rev, wa ∈ finalRev := fun wa h => hSub wa (m5 wa h)
    have hSub3 : ∀ wa ∈ r3.2.rev, wa ∈ finalRev := fun wa h => hSub4 wa (m4 wa h)
    have hSub2 : ∀ wa ∈ r2.2.rev, wa ∈ finalRev := fun wa h => hSub3 wa (m3 wa h)
    have hSub1 : ∀ wa ∈ r1.2.rev, wa ∈ finalRev := fun wa h => hSub2 wa (m2 wa h)
    rw [e5 hSub, e1 hSub1]; simp only [evalRtlExpr]; rw [e4 hSub4, e2 hSub2, e3 hSub3]; rfl

private def swarLane (k j : Nat) (x : BitVec 64) : BitVec (2 ^ k) :=
  (x >>> (j * 2 ^ k)).setWidth (2 ^ k)
private theorem swarMask_fin :
    ∀ (k : Fin 6) (i : Fin 64),
      (swarMask k.val).getLsbD i.val = decide (i.val % (2 ^ (k.val + 1)) < 2 ^ k.val) := by decide
private theorem swarLane_lo {k : Nat} (j : Nat) (x : BitVec 64) :
    towerLo (swarLane (k + 1) j x) = swarLane k (2 * j) x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi2 : i < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  simp only [towerLo, swarLane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, hi2,
    decide_true, Bool.true_and]
  congr 1; rw [Nat.pow_succ]; grind
private theorem swarLane_hi {k : Nat} (j : Nat) (x : BitVec 64) :
    towerHi (swarLane (k + 1) j x) = swarLane k (2 * j + 1) x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hSumLt : 2 ^ k + i < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  simp only [towerHi, swarLane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, hSumLt,
    decide_true, Bool.true_and]
  congr 1; rw [Nat.pow_succ]; grind
private theorem lt6_cases {k : Nat} (hk : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
private theorem swarLane_mask_even {k : Nat} (hk : k < 6) (j : Nat) (hj : j < 2 ^ (6 - (k + 1))) (x : BitVec 64) :
    swarLane k (2 * j) (evalAluOp .bitAnd x (swarMask k)) = swarLane k (2 * j) x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [swarLane, evalAluOp, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  have hBound : 2 * j * 2 ^ k + i < 64 := by rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [swarMask_fin ⟨k, hk⟩ ⟨_, hBound⟩]
  have hMod : (2 * j * 2 ^ k + i) % 2 ^ (k + 1) = i := by
    rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  simp [hMod, hi]
private theorem swarLane_mask_odd {k : Nat} (hk : k < 6) (j : Nat) (hj : j < 2 ^ (6 - (k + 1))) (x : BitVec 64) :
    swarLane k (2 * j + 1) (evalAluOp .bitAnd x (swarMask k)) = towerZero k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [swarLane, towerZero, evalAluOp, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
  have hBound : (2 * j + 1) * 2 ^ k + i < 64 := by
    rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [swarMask_fin ⟨k, hk⟩ ⟨_, hBound⟩]
  have hMod : ¬ (((2 * j + 1) * 2 ^ k + i) % 2 ^ (k + 1) < 2 ^ k) := by
    rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  simp [hMod]

private theorem shift_mod64_of_lt6 {k : Nat} (hk : k < 6) : (BitVec.ofNat 64 (2 ^ k)).toNat % 64 = 2 ^ k := by
  rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem swarLane_shr_even {k : Nat} (hk : k < 6) (j : Nat) (x : BitVec 64) :
    swarLane k (2 * j) (evalAluOp .lshr x (BitVec.ofNat 64 (2 ^ k))) = swarLane k (2 * j + 1) x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [swarLane, evalAluOp, shift_mod64_of_lt6 hk, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]; congr 1; grind
private theorem swarLane_xor (k j : Nat) (x y : BitVec 64) :
    swarLane k j (evalAluOp .bitXor x y) = swarLane k j x ^^^ swarLane k j y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [swarLane, evalAluOp, hi]

private theorem swarLane_combine {k : Nat} (hk : k < 6) (lo hi : BitVec 64)
    (hLoOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) lo = towerZero k)
    (hHiOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) hi = towerZero k)
    (j : Nat) (hj : j < 2 ^ (6 - (k + 1))) :
    swarLane (k + 1) j (evalAluOp .bitOr lo (evalAluOp .shl hi (BitVec.ofNat 64 (2 ^ k)))) =
      towerJoin (swarLane k (2 * j) lo) (swarLane k (2 * j) hi) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hiLt
  have hBound : j * 2 ^ (k + 1) + i < 64 := by rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [getLsbD_towerJoin]
  simp only [swarLane, evalAluOp, shift_mod64_of_lt6 hk, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hiLt, hBound,
    decide_true, Bool.true_and]
  by_cases hHalf : i < 2 ^ k
  · have hLoIdx : j * 2 ^ (k + 1) + i = 2 * j * 2 ^ k + i := by
      rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    by_cases hj0 : j = 0
    · subst hj0; simp [hHalf]
    · have hNotLt : ¬ (2 * j * 2 ^ k + i < 2 ^ k) := by
        rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hPrev := congrArg (fun v => v.getLsbD i) (hHiOdd (j - 1) (by omega))
      simp only [swarLane, towerZero, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_zero, hHalf, decide_true, Bool.true_and] at hPrev
      have hPrevIdx : 2 * j * 2 ^ k + i - 2 ^ k = (2 * (j - 1) + 1) * 2 ^ k + i := by
        rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp [hHalf, hLoIdx, hNotLt, hPrevIdx, hPrev]
  · have hSubLt : i - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hiLt; omega
    have hLoZero := congrArg (fun v => v.getLsbD (i - 2 ^ k)) (hLoOdd j hj)
    simp only [swarLane, towerZero, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_zero, hSubLt, decide_true, Bool.true_and] at hLoZero
    have hOddIdx : j * 2 ^ (k + 1) + i = (2 * j + 1) * 2 ^ k + (i - 2 ^ k) := by
      rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hNotLt : ¬ ((2 * j + 1) * 2 ^ k + (i - 2 ^ k) < 2 ^ k) := by
      rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hHiIdx : (2 * j + 1) * 2 ^ k + (i - 2 ^ k) - 2 ^ k = 2 * j * 2 ^ k + (i - 2 ^ k) := by
      rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simp [hHalf, hSubLt, hOddIdx, hLoZero, hNotLt, hHiIdx]

private theorem pow_6_sub {k : Nat} (hk : k < 6) : 2 ^ (6 - k) = 2 * 2 ^ (6 - (k + 1)) := by
  rcases lt6_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem swarMulOmegaBV_lane :
    ∀ (k : Nat), k ≤ 6 → ∀ (j : Nat), j < 2 ^ (6 - k) → ∀ (u : BitVec 64),
      swarLane k j (swarMulOmegaBV k u) = towerMulOmega k (swarLane k j u) := by
  intro k; induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro hk j hj u; have hkLt : k < 6 := by omega
    have hPow := pow_6_sub hkLt; unfold swarMulOmegaBV towerMulOmega; dsimp only
    let u0 := evalAluOp .bitAnd u (swarMask k)
    let u1 := evalAluOp .bitAnd (evalAluOp .lshr u (BitVec.ofNat 64 (2 ^ k))) (swarMask k)
    let om := swarMulOmegaBV k u1
    have hu1Odd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) u1 = towerZero k :=
      fun m hm => swarLane_mask_odd hkLt m hm _
    have hHiOdd : ∀ m, m < 2 ^ (6 - (k + 1)) →
        swarLane k (2 * m + 1) (evalAluOp .bitXor u0 om) = towerZero k := fun m hm => by
      rw [swarLane_xor, swarLane_mask_odd hkLt m hm,
        ih (by omega) (2 * m + 1) (by omega) u1, hu1Odd m hm, towerMulOmega_zero, xor_self_towerZero]
    rw [swarLane_combine hkLt u1 (evalAluOp .bitXor u0 om) hu1Odd hHiOdd j hj,
      swarLane_lo, swarLane_hi, swarLane_mask_even hkLt j hj, swarLane_shr_even hkLt j,
      swarLane_xor, swarLane_mask_even hkLt j hj,
      ih (by omega) (2 * j) (by omega) u1, swarLane_mask_even hkLt j hj, swarLane_shr_even hkLt j]

private theorem swarCombineBV_lane {k : Nat} (hk : k < 6) (p q : BitVec 64)
    (hqOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) q = towerZero k)
    (j : Nat) (hj : j < 2 ^ (6 - (k + 1))) :
    let p0 := swarLane k (2 * j) p; let p1 := swarLane k (2 * j + 1) p; let p01 := swarLane k (2 * j) q
    swarLane (k + 1) j (swarCombineBV k p q) =
      towerJoin (p0 ^^^ p1) ((p01 ^^^ (p0 ^^^ p1)) ^^^ towerMulOmega k p1) := by
  have hPow := pow_6_sub hk; unfold swarCombineBV; dsimp only
  let p0w := evalAluOp .bitAnd p (swarMask k)
  let p1w := evalAluOp .bitAnd (evalAluOp .lshr p (BitVec.ofNat 64 (2 ^ k))) (swarMask k)
  let low := evalAluOp .bitXor p0w p1w; let omw := swarMulOmegaBV k p1w
  let hiw := evalAluOp .bitXor (evalAluOp .bitXor q low) omw
  have hp1Odd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) p1w = towerZero k :=
    fun m hm => swarLane_mask_odd hk m hm _
  have hLoOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) low = towerZero k := fun m hm => by
    rw [swarLane_xor, swarLane_mask_odd hk m hm, hp1Odd m hm, xor_self_towerZero]
  have hHiOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) hiw = towerZero k := fun m hm => by
    rw [swarLane_xor, swarLane_xor, hqOdd m hm, hLoOdd m hm, xor_self_towerZero,
      swarMulOmegaBV_lane k (by omega) (2 * m + 1) (by omega) p1w, hp1Odd m hm,
      towerMulOmega_zero, xor_self_towerZero]
  change swarLane (k + 1) j (evalAluOp .bitOr low (evalAluOp .shl hiw (BitVec.ofNat 64 (2 ^ k)))) = _
  rw [swarLane_combine hk low hiw hLoOdd hHiOdd j hj]
  have hp0j : swarLane k (2 * j) p0w = swarLane k (2 * j) p := swarLane_mask_even hk j hj p
  have hp1j : swarLane k (2 * j) p1w = swarLane k (2 * j + 1) p := by
    rw [swarLane_mask_even hk j hj, swarLane_shr_even hk j]
  have hloj : swarLane k (2 * j) low = swarLane k (2 * j) p ^^^ swarLane k (2 * j + 1) p := by
    rw [swarLane_xor, hp0j, hp1j]
  have homj : swarLane k (2 * j) omw = towerMulOmega k (swarLane k (2 * j + 1) p) := by
    rw [swarMulOmegaBV_lane k (by omega) (2 * j) (by omega) p1w, hp1j]
  rw [hloj, swarLane_xor, swarLane_xor, hloj, homj]

private theorem swarMulBV_lane :
    ∀ (k : Nat), k ≤ 6 → ∀ (j : Nat), j < 2 ^ (6 - k) → ∀ (x y : BitVec 64),
      swarLane k j (swarMulBV k x y) = towerMul k (swarLane k j x) (swarLane k j y) := by
  intro k; induction k with
  | zero =>
    intro _ j _ x y; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [swarLane, swarMulBV, towerMul, evalAluOp, hi]
  | succ k ih =>
    intro hk j hj x y; have hkLt : k < 6 := by omega
    have hPow := pow_6_sub hkLt; unfold swarMulBV towerMul; dsimp only
    let xf := evalAluOp .bitXor x (evalAluOp .lshr x (BitVec.ofNat 64 (2 ^ k)))
    let yf := evalAluOp .bitXor y (evalAluOp .lshr y (BitVec.ofNat 64 (2 ^ k)))
    let q  := evalAluOp .bitAnd (swarMulBV k xf yf) (swarMask k)
    have hqOdd : ∀ m, m < 2 ^ (6 - (k + 1)) → swarLane k (2 * m + 1) q = towerZero k :=
      fun m hm => swarLane_mask_odd hkLt m hm _
    change swarLane (k + 1) j (swarCombineBV k (swarMulBV k x y) q) = _
    rw [swarCombineBV_lane hkLt (swarMulBV k x y) q hqOdd j hj,
      ih (by omega) (2 * j) (by omega), ih (by omega) (2 * j + 1) (by omega),
      swarLane_mask_even hkLt j hj, ih (by omega) (2 * j) (by omega),
      swarLane_xor, swarLane_xor, swarLane_shr_even hkLt j, swarLane_shr_even hkLt j,
      swarLane_lo, swarLane_hi, swarLane_lo, swarLane_hi]

private theorem swarMulBV_6_eq_towerMul (a b : BitVec 64) : swarMulBV 6 a b = towerMul 6 a b := by
  have h := swarMulBV_lane 6 (by omega) 0 (by decide) a b
  have hId : ∀ z : BitVec 64, swarLane 6 0 z = z := fun z => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [swarLane, hi]
  simpa only [hId] using h

private def swarQ5BV (a b : BitVec 64) : BitVec 64 :=
  evalAluOp .bitAnd (swarMulBV 5
    (evalAluOp .bitXor a (evalAluOp .lshr a (BitVec.ofNat 64 (2 ^ 5))))
    (evalAluOp .bitXor b (evalAluOp .lshr b (BitVec.ofNat 64 (2 ^ 5))))) (swarMask 5)

private theorem gf2_64_wire_eval (ins regs : Nat → BitVec 64) :
    let fin := evalWireTable ins regs gf2_64TowerMulRtlModule.wires
    let aIn := RtlExpr.inputPort 0; let bIn := RtlExpr.inputPort 1
    let sh5 := RtlExpr.const (BitVec.ofNat 64 (2 ^ 5))
    let r1  := pushSwarMul 5 {} aIn bIn
    let r2  := pushW r1.2 "t64_xf" (.alu .bitXor aIn (.alu .lshr aIn sh5))
    let r3  := pushW r2.2 "t64_yf" (.alu .bitXor bIn (.alu .lshr bIn sh5))
    let r4  := pushSwarMul 5 r3.2 r2.1 r3.1
    let r5  := pushW r4.2 "t64_q" (.alu .bitAnd r4.1 (.const (swarMask 5)))
    let r6  := pushSwarCombine 5 r5.2 r1.1 r5.1
    let r7  := pushSwarCombine 5 r6.2 (.regRead 0) (.regRead 1)
    let r8  := pushW r7.2 "t64_val" (.resize (.trunc 1) (.inputPort 2)) 1
    evalRtlExpr ins fin regs r6.1 = towerMul 6 (ins 0) (ins 1) ∧
    evalRtlExpr ins fin regs r1.1 = swarMulBV 5 (ins 0) (ins 1) ∧
    evalRtlExpr ins fin regs r5.1 = swarQ5BV (ins 0) (ins 1) ∧
    evalRtlExpr ins fin regs r7.1 = swarCombineBV 5 (regs 0) (regs 1) ∧
    evalRtlExpr ins fin regs r8.1 = truncToWidth 1 (ins 2) := by
  have hDag : checkWireTableDAG 3 5 gf2_64TowerMulRtlModule.wires = true := by decide +kernel
  let fin := evalWireTable ins regs gf2_64TowerMulRtlModule.wires
  let finalRev := t64Built.2.2.rev
  have hFin : ∀ wa ∈ finalRev, fin wa.wireIdx = evalRtlExpr ins fin regs wa.expr :=
    fun wa hwa => evalWireTable_at_dag 3 5 ins regs _ hDag wa (List.mem_reverse.mpr hwa)
  let aIn := RtlExpr.inputPort 0; let bIn := RtlExpr.inputPort 1; let sh5 := RtlExpr.const (BitVec.ofNat 64 (2 ^ 5))
  let r1 := pushSwarMul 5 {} aIn bIn
  let r2 := pushW r1.2 "t64_xf" (.alu .bitXor aIn (.alu .lshr aIn sh5))
  let r3 := pushW r2.2 "t64_yf" (.alu .bitXor bIn (.alu .lshr bIn sh5))
  let r4 := pushSwarMul 5 r3.2 r2.1 r3.1
  let r5 := pushW r4.2 "t64_q" (.alu .bitAnd r4.1 (.const (swarMask 5)))
  let r6 := pushSwarCombine 5 r5.2 r1.1 r5.1
  let r7 := pushSwarCombine 5 r6.2 (.regRead 0) (.regRead 1)
  obtain ⟨m1, e1⟩ := pushSwarMul_spec ins regs fin finalRev hFin 5 {} aIn bIn
  obtain ⟨m2, e2⟩ := pushW_spec ins regs fin finalRev hFin r1.2 "t64_xf" (.alu .bitXor aIn (.alu .lshr aIn sh5))
  obtain ⟨m3, e3⟩ := pushW_spec ins regs fin finalRev hFin r2.2 "t64_yf" (.alu .bitXor bIn (.alu .lshr bIn sh5))
  obtain ⟨m4, e4⟩ := pushSwarMul_spec ins regs fin finalRev hFin 5 r3.2 r2.1 r3.1
  obtain ⟨m5, e5⟩ := pushW_spec ins regs fin finalRev hFin r4.2 "t64_q" (.alu .bitAnd r4.1 (.const (swarMask 5)))
  obtain ⟨m6, e6⟩ := pushSwarCombine_spec ins regs fin finalRev hFin 5 r5.2 r1.1 r5.1
  obtain ⟨m7, e7⟩ := pushSwarCombine_spec ins regs fin finalRev hFin 5 r6.2 (.regRead 0) (.regRead 1)
  obtain ⟨m8, e8⟩ := pushW_spec ins regs fin finalRev hFin r7.2 "t64_val" (.resize (.trunc 1) (.inputPort 2)) 1
  have hSub7 : ∀ wa ∈ r7.2.rev, wa ∈ finalRev := m8
  have hSub6 := fun wa h => hSub7 wa (m7 wa h); have hSub5 := fun wa h => hSub6 wa (m6 wa h)
  have hSub4 := fun wa h => hSub5 wa (m5 wa h); have hSub3 := fun wa h => hSub4 wa (m4 wa h)
  have hSub2 := fun wa h => hSub3 wa (m3 wa h); have hSub1 := fun wa h => hSub2 wa (m2 wa h)
  have hp : evalRtlExpr ins fin regs r1.1 = swarMulBV 5 (ins 0) (ins 1) := e1 hSub1
  have hq : evalRtlExpr ins fin regs r5.1 = swarQ5BV (ins 0) (ins 1) := by
    rw [e5 hSub5]; simp only [evalRtlExpr]; rw [e4 hSub4, e2 hSub2, e3 hSub3]; rfl
  refine ⟨?_, hp, hq, e7 hSub7, e8 (fun _ h => h)⟩
  rw [e6 hSub6, hp, hq]; exact swarMulBV_6_eq_towerMul (ins 0) (ins 1)

/-- **Universal Bit-Exact Hardware-Software Equivalence (`gf2_64TowerMulRtl_eq_towerMul`)**. -/
theorem gf2_64TowerMulRtl_eq_towerMul (a b valid : BitVec 64) (regs : Nat → BitVec 64) :
    (evalModuleOutputs gf2_64TowerMulRtlModule (gf2_64Inputs a b valid) regs).lookup
      "tower64_mul_out" = some (towerMul 6 a b) :=
  congrArg some (gf2_64_wire_eval (gf2_64Inputs a b valid) regs).1

/-- **2-Stage Registered Pipeline Equivalence (`gf2_64TowerMulRtl_pipe2_sound`)**. -/
theorem gf2_64TowerMulRtl_pipe2_sound (st0 ins0 ins1 anyIns : Nat → BitVec 64) :
    let st1  := stepModuleRegs gf2_64TowerMulRtlModule false ins0 st0
    let st2  := stepModuleRegs gf2_64TowerMulRtlModule false ins1 st1
    let outs := evalModuleOutputs gf2_64TowerMulRtlModule anyIns st2
    outs.lookup "tower64_pipe_out" = some (towerMul 6 (ins0 0) (ins0 1)) ∧
    outs.lookup "tower64_pipe_valid" = some (truncToWidth 1 (ins0 2)) := by
  intro st1 st2 outs
  have hNodup : (gf2_64TowerMulRtlModule.regs.map (·.regIdx)).Nodup := by decide +kernel
  have hr (k : Nat) (r : RegSpec) (hMem : r ∈ gf2_64TowerMulRtlModule.regs)
      (hk : r.regIdx = k) (ins st : Nat → BitVec 64) :
      stepModuleRegs gf2_64TowerMulRtlModule false ins st k =
        evalRtlExpr ins (evalWireTable ins st gf2_64TowerMulRtlModule.wires) st r.nextExpr := by
    rw [← hk, stepModuleRegs_false_at gf2_64TowerMulRtlModule ins st hNodup r hMem]
  obtain ⟨_, hp0, hq0, _, hv0⟩ := gf2_64_wire_eval ins0 st0
  obtain ⟨_, _, _, hpipe1, _⟩ := gf2_64_wire_eval ins1 st1
  have hs1_0 : st1 0 = swarMulBV 5 (ins0 0) (ins0 1) :=
    (hr 0 t64Regs[0] (by decide +kernel) rfl ins0 st0).trans hp0
  have hs1_1 : st1 1 = swarQ5BV (ins0 0) (ins0 1) :=
    (hr 1 t64Regs[1] (by decide +kernel) rfl ins0 st0).trans hq0
  have hs1_2 : st1 2 = truncToWidth 1 (ins0 2) :=
    (hr 2 t64Regs[2] (by decide +kernel) rfl ins0 st0).trans hv0
  have hs2_3 : st2 3 = swarCombineBV 5 (st1 0) (st1 1) :=
    (hr 3 t64Regs[3] (by decide +kernel) rfl ins1 st1).trans hpipe1
  have hs2_4 : st2 4 = st1 2 := hr 4 t64Regs[4] (by decide +kernel) rfl ins1 st1
  have hLookup : outs.lookup "tower64_pipe_out" = some (st2 3) ∧
      outs.lookup "tower64_pipe_valid" = some (st2 4) := ⟨rfl, rfl⟩
  rw [hLookup.1, hLookup.2, hs2_3, hs2_4, hs1_0, hs1_1, hs1_2]
  exact ⟨congrArg some (swarMulBV_6_eq_towerMul (ins0 0) (ins0 1)), rfl⟩

end Obend.Hardware.PipelinedZkCrypto
end
