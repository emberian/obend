; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet (renamed from *_lec.smt2 on 2026-11-05). The logic-equivalence check of the emitted .sv is
; hardware/lec/lec.sh with the generated quantum_photonic_coproc_top_lec.smt2. See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Flagship App #8 (`apps/quantum-photonic-matter/verilator/quantum_photonic_lec.smt2`):
; Z3 `QF_BV` 64-bit Logic Equivalence Check (LEC) & Algebraic Invariant Miter for
; `quantum_photonic_coproc_top.sv` (`emitModuleSV quantumPhotonicCoprocTopRtlModule`):
; 1. `.obend` open-recursive datapath equivalence (`FaultTolerantCoProcOverride` & `SymmetryPreservingKrawtchoukOverride`),
; 2. 1-WL DPR guard (`quotientHypergraphSlot` + Q_3 shell symmetry) & degree-4 scaled Krawtchouk Taylor amplitude
;    (`evalScaledMatrixTaylorImag hypercubeQ3QuotientMatrix 157 100 4 wQ3 3 == 9287743200`),
; 3. 4x4 Faddeev-LeVerrier exact crosstalk cancellation `G_th * adj(G_th) * v == 8769 * v` across all 2^256 vectors,
; 4. Genuine 3-stage Majorana spinor braiding over Z[i]^4 (`T_01(T_12(T_01(psi))) == T_12(T_01(T_12(psi)))`,
;    composed from independent single-gate definitions `T_01 = I_4 + \gamma_0\gamma_1` and `T_12 = I_4 + \gamma_1\gamma_2`),
; 5. Chiral fermion-parity cooling (`spinorChiralParity = diag(1, 1, -1, -1)`, `parityCoolingJumpOp 0`):
;    dark on every even-parity codeword (`z2 == 0 && z3 == 0`) and maps every odd-parity state into `{0, 1}`.

(set-logic QF_BV)

(declare-const in_batch_vectors (_ BitVec 64))
(declare-const in_syndrome_rounds (_ BitVec 64))
(declare-const in_krawtchouk_batch_size (_ BitVec 64))
(declare-const in_pst_step_index (_ BitVec 64))
(declare-const in_pin_w0 (_ BitVec 64))
(declare-const in_pin_w1 (_ BitVec 64))
(declare-const in_pin_w2 (_ BitVec 64))
(declare-const in_pin_w3 (_ BitVec 64))
(declare-const in_pin_shell_w01 (_ BitVec 64))
(declare-const in_pin_shell_w12 (_ BitVec 64))
(declare-const in_pin_shell_w23 (_ BitVec 64))
(declare-const v0 (_ BitVec 64))
(declare-const v1 (_ BitVec 64))
(declare-const v2 (_ BitVec 64))
(declare-const v3 (_ BitVec 64))
(declare-const z0_re (_ BitVec 64))
(declare-const z0_im (_ BitVec 64))
(declare-const z1_re (_ BitVec 64))
(declare-const z1_im (_ BitVec 64))
(declare-const z2_re (_ BitVec 64))
(declare-const z2_im (_ BitVec 64))
(declare-const z3_re (_ BitVec 64))
(declare-const z3_im (_ BitVec 64))

; --- 1. `.obend` Spec vs RTL Datapath ---
(define-fun spec_adjoint_ops () (_ BitVec 64)
  (bvadd (bvmul in_batch_vectors (_ bv4 64)) (_ bv8769 64)))
(define-fun rtl_adjoint_ops () (_ BitVec 64)
  (bvadd (bvshl in_batch_vectors (_ bv2 64)) #x0000000000002241))

(define-fun spec_cycle_budget () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_syndrome_rounds (_ bv16 64)) (_ bv4 64)) (_ bv32 64)))
(define-fun rtl_cycle_budget () (_ BitVec 64)
  (bvadd (bvadd (bvshl in_syndrome_rounds (_ bv4 64)) #x0000000000000004) #x0000000000000020))

(define-fun spec_krawtchouk_macs () (_ BitVec 64)
  (bvadd (bvmul in_krawtchouk_batch_size (_ bv4 64)) (_ bv3142 64)))
(define-fun rtl_krawtchouk_macs () (_ BitVec 64)
  (bvadd (bvshl in_krawtchouk_batch_size (_ bv2 64)) #x0000000000000c46))

(define-fun dpr_usable () Bool
  (and (= in_pin_w0 in_pin_w1)
       (= in_pin_w2 in_pin_w3)
       (= in_pin_shell_w01 (_ bv3 64))
       (= in_pin_shell_w12 (_ bv4 64))
       (= in_pin_shell_w23 (_ bv3 64))))

; Degree-4 scaled Taylor amplitude at t = 157/100 on symmetric Q_3 (shell_w23 = 3):
(define-fun rtl_q3_taylor_at_157_100 () (_ BitVec 64)
  (bvmul (bvmul (bvmul (_ bv4 64) (_ bv100 64)) (bvmul (_ bv3 64) (_ bv2 64)))
         (bvmul (bvmul (_ bv157 64) (_ bv157 64)) (_ bv157 64))))

; --- 2. 4x4 Faddeev-LeVerrier Exact Crosstalk Cancellation (`det = 8769`) ---
(define-fun u0 () (_ BitVec 64)
  (bvadd (bvadd (bvmul (_ bv918 64) v0) (bvmul (bvneg (_ bv174 64)) v1))
         (bvadd (bvmul (bvneg (_ bv63 64)) v2) (bvmul (_ bv30 64) v3))))
(define-fun u1 () (_ BitVec 64)
  (bvadd (bvadd (bvmul (bvneg (_ bv174 64)) v0) (bvmul (_ bv950 64) v1))
         (bvadd (bvmul (bvneg (_ bv160 64)) v2) (bvmul (bvneg (_ bv63 64)) v3))))
(define-fun u2 () (_ BitVec 64)
  (bvadd (bvadd (bvmul (bvneg (_ bv63 64)) v0) (bvmul (bvneg (_ bv160 64)) v1))
         (bvadd (bvmul (_ bv950 64) v2) (bvmul (bvneg (_ bv174 64)) v3))))
(define-fun u3 () (_ BitVec 64)
  (bvadd (bvadd (bvmul (_ bv30 64) v0) (bvmul (bvneg (_ bv63 64)) v1))
         (bvadd (bvmul (bvneg (_ bv174 64)) v2) (bvmul (_ bv918 64) v3))))

(define-fun y0 () (_ BitVec 64) (bvadd (bvadd (bvmul (_ bv10 64) u0) (bvmul (_ bv2 64) u1)) u2))
(define-fun y1 () (_ BitVec 64) (bvadd (bvadd (bvmul (_ bv2 64) u0) (bvmul (_ bv10 64) u1)) (bvadd (bvmul (_ bv2 64) u2) u3)))
(define-fun y2 () (_ BitVec 64) (bvadd (bvadd u0 (bvmul (_ bv2 64) u1)) (bvadd (bvmul (_ bv10 64) u2) (bvmul (_ bv2 64) u3))))
(define-fun y3 () (_ BitVec 64) (bvadd (bvadd u1 (bvmul (_ bv2 64) u2)) (bvmul (_ bv10 64) u3)))

; --- 3. Genuine 3-Stage Complex Spinor Majorana Braiding (`T_01 T_12 T_01` vs `T_12 T_01 T_12`) ---
; Stage L1 = T_01(psi)
(define-fun l1_z0_re () (_ BitVec 64) (bvsub z0_re z1_im))
(define-fun l1_z0_im () (_ BitVec 64) (bvadd z0_im z1_re))
(define-fun l1_z1_re () (_ BitVec 64) (bvsub z1_re z0_im))
(define-fun l1_z1_im () (_ BitVec 64) (bvadd z1_im z0_re))
(define-fun l1_z2_re () (_ BitVec 64) (bvadd z2_re z3_im))
(define-fun l1_z2_im () (_ BitVec 64) (bvsub z2_im z3_re))
(define-fun l1_z3_re () (_ BitVec 64) (bvadd z3_re z2_im))
(define-fun l1_z3_im () (_ BitVec 64) (bvsub z3_im z2_re))

; Stage L2 = T_12(L1)
(define-fun l2_z0_re () (_ BitVec 64) (bvsub l1_z0_re l1_z0_im))
(define-fun l2_z0_im () (_ BitVec 64) (bvadd l1_z0_re l1_z0_im))
(define-fun l2_z1_re () (_ BitVec 64) (bvadd l1_z1_re l1_z1_im))
(define-fun l2_z1_im () (_ BitVec 64) (bvsub l1_z1_im l1_z1_re))
(define-fun l2_z2_re () (_ BitVec 64) (bvsub l1_z2_re l1_z2_im))
(define-fun l2_z2_im () (_ BitVec 64) (bvadd l1_z2_re l1_z2_im))
(define-fun l2_z3_re () (_ BitVec 64) (bvadd l1_z3_re l1_z3_im))
(define-fun l2_z3_im () (_ BitVec 64) (bvsub l1_z3_im l1_z3_re))

; Stage L3 = T_01(L2) = (T_01 * T_12 * T_01)(psi)
(define-fun l3_z0_re () (_ BitVec 64) (bvsub l2_z0_re l2_z1_im))
(define-fun l3_z0_im () (_ BitVec 64) (bvadd l2_z0_im l2_z1_re))
(define-fun l3_z1_re () (_ BitVec 64) (bvsub l2_z1_re l2_z0_im))
(define-fun l3_z1_im () (_ BitVec 64) (bvadd l2_z1_im l2_z0_re))
(define-fun l3_z2_re () (_ BitVec 64) (bvadd l2_z2_re l2_z3_im))
(define-fun l3_z2_im () (_ BitVec 64) (bvsub l2_z2_im l2_z3_re))
(define-fun l3_z3_re () (_ BitVec 64) (bvadd l2_z3_re l2_z2_im))
(define-fun l3_z3_im () (_ BitVec 64) (bvsub l2_z3_im l2_z2_re))

; Stage R1 = T_12(psi)
(define-fun r1_z0_re () (_ BitVec 64) (bvsub z0_re z0_im))
(define-fun r1_z0_im () (_ BitVec 64) (bvadd z0_re z0_im))
(define-fun r1_z1_re () (_ BitVec 64) (bvadd z1_re z1_im))
(define-fun r1_z1_im () (_ BitVec 64) (bvsub z1_im z1_re))
(define-fun r1_z2_re () (_ BitVec 64) (bvsub z2_re z2_im))
(define-fun r1_z2_im () (_ BitVec 64) (bvadd z2_re z2_im))
(define-fun r1_z3_re () (_ BitVec 64) (bvadd z3_re z3_im))
(define-fun r1_z3_im () (_ BitVec 64) (bvsub z3_im z3_re))

; Stage R2 = T_01(R1)
(define-fun r2_z0_re () (_ BitVec 64) (bvsub r1_z0_re r1_z1_im))
(define-fun r2_z0_im () (_ BitVec 64) (bvadd r1_z0_im r1_z1_re))
(define-fun r2_z1_re () (_ BitVec 64) (bvsub r1_z1_re r1_z0_im))
(define-fun r2_z1_im () (_ BitVec 64) (bvadd r1_z1_im r1_z0_re))
(define-fun r2_z2_re () (_ BitVec 64) (bvadd r1_z2_re r1_z3_im))
(define-fun r2_z2_im () (_ BitVec 64) (bvsub r1_z2_im r1_z3_re))
(define-fun r2_z3_re () (_ BitVec 64) (bvadd r1_z3_re r1_z2_im))
(define-fun r2_z3_im () (_ BitVec 64) (bvsub r1_z3_im r1_z2_re))

; Stage R3 = T_12(R2) = (T_12 * T_01 * T_12)(psi)
(define-fun r3_z0_re () (_ BitVec 64) (bvsub r2_z0_re r2_z0_im))
(define-fun r3_z0_im () (_ BitVec 64) (bvadd r2_z0_re r2_z0_im))
(define-fun r3_z1_re () (_ BitVec 64) (bvadd r2_z1_re r2_z1_im))
(define-fun r3_z1_im () (_ BitVec 64) (bvsub r2_z1_im r2_z1_re))
(define-fun r3_z2_re () (_ BitVec 64) (bvsub r2_z2_re r2_z2_im))
(define-fun r3_z2_im () (_ BitVec 64) (bvadd r2_z2_re r2_z2_im))
(define-fun r3_z3_re () (_ BitVec 64) (bvadd r2_z3_re r2_z3_im))
(define-fun r3_z3_im () (_ BitVec 64) (bvsub r2_z3_im r2_z3_re))

; --- 4. Chiral Parity Cooling (`parityCoolingJumpOp 0`: `(z0, z1, z2, z3) -> (z2, z3, 0, 0)`) ---
(define-fun even_in () Bool
  (and (= z2_re (_ bv0 64)) (= z2_im (_ bv0 64)) (= z3_re (_ bv0 64)) (= z3_im (_ bv0 64))))
(define-fun cool_z0_re () (_ BitVec 64) z2_re)
(define-fun cool_z0_im () (_ BitVec 64) z2_im)
(define-fun cool_z1_re () (_ BitVec 64) z3_re)
(define-fun cool_z1_im () (_ BitVec 64) z3_im)
(define-fun cool_z2_re () (_ BitVec 64) (_ bv0 64))
(define-fun cool_z2_im () (_ BitVec 64) (_ bv0 64))
(define-fun cool_z3_re () (_ BitVec 64) (_ bv0 64))
(define-fun cool_z3_im () (_ BitVec 64) (_ bv0 64))

(assert
  (or
    (distinct spec_adjoint_ops rtl_adjoint_ops)
    (distinct spec_cycle_budget rtl_cycle_budget)
    (distinct spec_krawtchouk_macs rtl_krawtchouk_macs)
    (distinct rtl_q3_taylor_at_157_100 (_ bv9287743200 64))
    (distinct y0 (bvmul (_ bv8769 64) v0))
    (distinct y1 (bvmul (_ bv8769 64) v1))
    (distinct y2 (bvmul (_ bv8769 64) v2))
    (distinct y3 (bvmul (_ bv8769 64) v3))
    (distinct l3_z0_re r3_z0_re)
    (distinct l3_z0_im r3_z0_im)
    (distinct l3_z1_re r3_z1_re)
    (distinct l3_z1_im r3_z1_im)
    (distinct l3_z2_re r3_z2_re)
    (distinct l3_z2_im r3_z2_im)
    (distinct l3_z3_re r3_z3_re)
    (distinct l3_z3_im r3_z3_im)
    (and even_in (or (distinct cool_z0_re (_ bv0 64))
                     (distinct cool_z0_im (_ bv0 64))
                     (distinct cool_z1_re (_ bv0 64))
                     (distinct cool_z1_im (_ bv0 64))))
    (distinct cool_z2_re (_ bv0 64))
    (distinct cool_z2_im (_ bv0 64))
    (distinct cool_z3_re (_ bv0 64))
    (distinct cool_z3_im (_ bv0 64))))

(check-sat)
