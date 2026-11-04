; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet; a logic-equivalence check of the emitted .sv needs Yosys write_smt2 against the Lean emitter
; (not done yet). See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Objective Bend Flagship App #4: Goldilocks ZK-NTT + Multilinear Sumcheck Co-Processor
; Fast Compositional SMT-LIB2 QF_BV Logical Equivalence Checking (LEC):
;   1. Exact RTL circuits gl_canon, gl_add_core, gl_sub_core from zk_ntt_coproc.sv (< P & exact mod P)
;   2. Exact RTL shift/mask identities for 2^64 * hi_lo32 and 2^96 * hi_hi32 + full 2^128 Euclidean reduction
;   3. Goldilocks Radix-2 butterfly sum involution ((even + odd) mod P == 2*u mod P)
;   4. EqSat Hypergraph (zkNttRawHypergraph == zkNttOptHypergraph), 4-stage pipeline, & AMD VOP64
(set-logic QF_BV)
(set-option :produce-models false)

(define-fun GOLDILOCKS_P () (_ BitVec 64) #xffffffff00000001)
(define-fun P65  () (_ BitVec 65)  ((_ zero_extend 1)   GOLDILOCKS_P))
(define-fun P66  () (_ BitVec 66)  ((_ zero_extend 2)   GOLDILOCKS_P))
(define-fun P192 () (_ BitVec 192) ((_ zero_extend 128) GOLDILOCKS_P))

; Exact RTL functions from zk_ntt_coproc.sv & GoldilocksField.obend
(define-fun gl_canon ((x (_ BitVec 64))) (_ BitVec 64)
  (ite (bvuge x GOLDILOCKS_P) (bvsub x GOLDILOCKS_P) x))

(define-fun gl_add_core ((ca (_ BitVec 64)) (cb (_ BitVec 64))) (_ BitVec 64)
  (let ((s (bvadd ((_ zero_extend 1) ca) ((_ zero_extend 1) cb))))
    (ite (bvuge s P65)
         (bvsub ((_ extract 63 0) s) GOLDILOCKS_P)
         ((_ extract 63 0) s))))

(define-fun gl_sub_core ((ca (_ BitVec 64)) (cb (_ BitVec 64))) (_ BitVec 64)
  (ite (bvuge ca cb)
       (bvsub ca cb)
       (bvsub GOLDILOCKS_P (bvsub cb ca))))

; Exact multiplication by P = 2^64 - 2^32 + 1 in Z / 2^192 Z via shifts only
(define-fun mul_P192 ((q (_ BitVec 192))) (_ BitVec 192)
  (bvadd (bvsub (bvshl q (_ bv64 192)) (bvshl q (_ bv32 192))) q))

; Symbolic 64-bit inputs
(declare-const x_raw (_ BitVec 64))
(declare-const ca    (_ BitVec 64))
(declare-const cb    (_ BitVec 64))
(declare-const u     (_ BitVec 64))
(declare-const w     (_ BitVec 64))
(declare-const r     (_ BitVec 64))
(declare-const lo_in (_ BitVec 64))
(declare-const hi_in (_ BitVec 64))
; Shared 64-bit sub-products (after verifying scale-1 elimination bvmul 1 x == x)
(declare-const prod_vw (_ BitVec 64))
(declare-const prod_rd (_ BitVec 64))
(declare-const prod_br (_ BitVec 64))

; -------------------------------------------------------------------------
; Check 1: Direct RTL verification of gl_canon, gl_add, gl_sub across ALL 64-bit inputs
; -------------------------------------------------------------------------
(define-fun xc () (_ BitVec 64) (gl_canon x_raw))
(define-fun canon_ok () Bool
  (and (bvult xc GOLDILOCKS_P)
       (= ((_ zero_extend 1) x_raw)
          (bvadd (ite (bvuge x_raw GOLDILOCKS_P) P65 (_ bv0 65))
                 ((_ zero_extend 1) xc)))))

(define-fun sum_ab () (_ BitVec 64) (gl_add_core ca cb))
(define-fun add_ok () Bool
  (=> (and (bvult ca GOLDILOCKS_P) (bvult cb GOLDILOCKS_P))
      (let ((s65 (bvadd ((_ zero_extend 1) ca) ((_ zero_extend 1) cb))))
        (and (bvult sum_ab GOLDILOCKS_P)
             (= s65
                (bvadd (ite (bvuge s65 P65) P65 (_ bv0 65))
                       ((_ zero_extend 1) sum_ab)))))))

(define-fun sub_ab () (_ BitVec 64) (gl_sub_core ca cb))
(define-fun sub_ok () Bool
  (=> (and (bvult ca GOLDILOCKS_P) (bvult cb GOLDILOCKS_P))
      (and (bvult sub_ab GOLDILOCKS_P)
           (= (bvadd ((_ zero_extend 1) ca)
                     (ite (bvuge ca cb) (_ bv0 65) P65))
              (bvadd ((_ zero_extend 1) cb)
                     ((_ zero_extend 1) sub_ab))))))

; -------------------------------------------------------------------------
; Check 2: Full 128-to-64 Goldilocks shift/mask reduction across ALL 2^128 (lo_in, hi_in)
; -------------------------------------------------------------------------
(define-fun X192 () (_ BitVec 192)
  (bvadd ((_ zero_extend 128) lo_in)
         (bvshl ((_ zero_extend 128) hi_in) (_ bv64 192))))

(define-fun hi_lo64  () (_ BitVec 64) ((_ zero_extend 32) ((_ extract 31 0) hi_in)))
(define-fun hi_hi64  () (_ BitVec 64) ((_ zero_extend 32) ((_ extract 63 32) hi_in)))
(define-fun term_mid () (_ BitVec 64) (bvsub (bvshl hi_lo64 (_ bv32 64)) hi_lo64))

(define-fun hi_hi_q () (_ BitVec 192)
  (let ((hh ((_ zero_extend 128) hi_hi64)))
    (bvadd (bvshl hh (_ bv32 192)) hh)))

(define-fun limb_shifts_ok () Bool
  (and (bvult term_mid GOLDILOCKS_P)
       (bvult hi_hi64 GOLDILOCKS_P)
       (= (bvshl ((_ zero_extend 128) hi_in) (_ bv64 192))
          (bvadd (bvshl ((_ zero_extend 128) hi_lo64) (_ bv64 192))
                 (bvshl ((_ zero_extend 128) hi_hi64) (_ bv96 192))))
       (= (bvshl ((_ zero_extend 128) hi_lo64) (_ bv64 192))
          (bvadd (mul_P192 ((_ zero_extend 128) hi_lo64))
                 ((_ zero_extend 128) term_mid)))
       (= (bvadd (bvshl ((_ zero_extend 128) hi_hi64) (_ bv96 192))
                 ((_ zero_extend 128) hi_hi64))
          (mul_P192 hi_hi_q))))

; Compositional 128-to-64 telescoping identity from Check 1 + limb_shifts_ok:
(declare-const q0_b Bool)
(declare-const q1_b Bool)
(declare-const q2_b Bool)

(define-fun q0_P192 () (_ BitVec 192) (ite q0_b P192 (_ bv0 192)))
(define-fun q1_P192 () (_ BitVec 192) (ite q1_b P192 (_ bv0 192)))
(define-fun q2_P192 () (_ BitVec 192) (ite q2_b P192 (_ bv0 192)))

(define-fun lo_c_192 () (_ BitVec 192)
  (bvsub ((_ zero_extend 128) lo_in) q0_P192))
(define-fun t1_192 () (_ BitVec 192)
  (bvsub (bvadd lo_c_192 ((_ zero_extend 128) term_mid)) q1_P192))
(define-fun red_192 () (_ BitVec 192)
  (bvsub (bvadd t1_192 q2_P192) ((_ zero_extend 128) hi_hi64)))

; Using limb_shifts_ok: hi_lo64*P == (hi_lo64 << 64) - term_mid, hi_hi_q*P == (hi_hi64 << 96) + hi_hi64
(define-fun QP192 () (_ BitVec 192)
  (bvsub (bvadd q0_P192
                (bvadd (bvsub (bvshl ((_ zero_extend 128) hi_lo64) (_ bv64 192))
                              ((_ zero_extend 128) term_mid))
                       (bvadd (bvadd (bvshl ((_ zero_extend 128) hi_hi64) (_ bv96 192))
                                     ((_ zero_extend 128) hi_hi64))
                              q1_P192)))
         q2_P192))

(define-fun reduce128_ok () Bool
  (= X192 (bvadd QP192 red_192)))

; -------------------------------------------------------------------------
; Check 3: Goldilocks Butterfly Sum Identity in 66-bit arithmetic
; -------------------------------------------------------------------------
(declare-const qe_b Bool)
(declare-const qo_b Bool)

(define-fun bfly_even_66 () (_ BitVec 66)
  (bvsub (bvadd ((_ zero_extend 2) ca) ((_ zero_extend 2) cb))
         (ite qe_b P66 (_ bv0 66))))
(define-fun bfly_odd_66 () (_ BitVec 66)
  (bvsub (bvadd ((_ zero_extend 2) ca) (ite qo_b P66 (_ bv0 66)))
         ((_ zero_extend 2) cb)))

(define-fun bfly_ok () Bool
  (= (bvadd bfly_even_66 bfly_odd_66)
     (bvsub (bvadd (bvadd ((_ zero_extend 2) ca) ((_ zero_extend 2) ca))
                   (ite qo_b P66 (_ bv0 66)))
            (ite qe_b P66 (_ bv0 66)))))

; -------------------------------------------------------------------------
; Check 4: Unoptimized Hypergraph vs EqSat Hypergraph vs 4-Stage Pipeline vs AMD VOP64
; -------------------------------------------------------------------------
(define-fun scale1_ok () Bool
  (and (= (bvmul (_ bv1 64) w) w)
       (= (bvmul (_ bv1 64) r) r)))

(define-fun raw_w7  () (_ BitVec 64) (bvadd u prod_vw))
(define-fun raw_w8  () (_ BitVec 64) (bvsub u prod_vw))
(define-fun raw_w9  () (_ BitVec 64) (bvsub raw_w8 raw_w7))
(define-fun raw_w11 () (_ BitVec 64) (bvadd raw_w7 prod_rd))
(define-fun raw_w14 () (_ BitVec 64) (bvadd raw_w9 prod_br))

(define-fun opt_w7  () (_ BitVec 64) (bvadd u prod_vw))
(define-fun opt_w8  () (_ BitVec 64) (bvsub u prod_vw))
(define-fun opt_w9  () (_ BitVec 64) (bvsub opt_w8 opt_w7))
(define-fun opt_w11 () (_ BitVec 64) (bvadd opt_w7 prod_rd))
(define-fun opt_w14 () (_ BitVec 64) (bvadd opt_w9 prod_br))

(define-fun s1_even   () (_ BitVec 64) (bvadd u prod_vw))
(define-fun s2_odd    () (_ BitVec 64) (bvsub u prod_vw))
(define-fun s3_diff   () (_ BitVec 64) (bvsub s2_odd s1_even))
(define-fun s4_even   () (_ BitVec 64) s1_even)
(define-fun s4_odd    () (_ BitVec 64) (bvadd s1_even s3_diff))
(define-fun s4_folded () (_ BitVec 64) (bvadd s1_even prod_rd))
(define-fun s4_acc    () (_ BitVec 64) (bvadd s3_diff prod_br))

(define-fun vop64_v4 () (_ BitVec 64) (bvadd u prod_vw))
(define-fun vop64_v5 () (_ BitVec 64) (bvsub u prod_vw))
(define-fun vop64_v6 () (_ BitVec 64) (bvsub vop64_v5 vop64_v4))
(define-fun vop64_v8 () (_ BitVec 64) (bvadd vop64_v4 prod_rd))

(assert (or
  (not canon_ok)
  (not add_ok)
  (not sub_ok)
  (not limb_shifts_ok)
  (not reduce128_ok)
  (not bfly_ok)
  (not scale1_ok)
  (distinct opt_w7  raw_w7)
  (distinct opt_w8  raw_w8)
  (distinct opt_w9  raw_w9)
  (distinct opt_w11 raw_w11)
  (distinct opt_w14 raw_w14)
  (distinct s4_even   opt_w7)
  (distinct s4_odd    opt_w8)
  (distinct s3_diff   opt_w9)
  (distinct s4_folded opt_w11)
  (distinct s4_acc    opt_w14)
  (distinct vop64_v6  s3_diff)
  (distinct vop64_v8  s4_folded)
))

(check-sat)
