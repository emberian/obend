; Objective Bend Flagship App #4: Goldilocks ZK-NTT + Multilinear Sumcheck Co-Processor
; SMT-LIB2 QF_BV Logical Equivalence Checking (LEC) across EqSat RTL, 4-Stage Pipeline & AMD VOP64
(set-logic QF_BV)
(set-option :produce-models false)

(declare-const u    (_ BitVec 64))
(declare-const v    (_ BitVec 64))
(declare-const w    (_ BitVec 64))
(declare-const r    (_ BitVec 64))
(declare-const bias (_ BitVec 64))

; 1. Unoptimized Hypergraph (zkNttRawHypergraph: 10 edges, 3 discrete multipliers)
(define-fun raw_w5  () (_ BitVec 64) (bvmul (_ bv1 64) w))
(define-fun raw_w6  () (_ BitVec 64) (bvmul v raw_w5))
(define-fun raw_w7  () (_ BitVec 64) (bvadd u raw_w6))
(define-fun raw_w8  () (_ BitVec 64) (bvsub u raw_w6))
(define-fun raw_w9  () (_ BitVec 64) (bvsub raw_w8 raw_w7))
(define-fun raw_w10 () (_ BitVec 64) (bvmul r raw_w9))
(define-fun raw_w11 () (_ BitVec 64) (bvadd raw_w7 raw_w10))
(define-fun raw_w12 () (_ BitVec 64) (bvmul (_ bv1 64) r))
(define-fun raw_w13 () (_ BitVec 64) (bvmul bias raw_w12))
(define-fun raw_w14 () (_ BitVec 64) (bvadd raw_w9 raw_w13))

; 2. E-Graph Equality-Saturated Hypergraph (zkNttOptHypergraph: 6 edges, 3 fused .mac, 1 .mul)
(define-fun opt_w6  () (_ BitVec 64) (bvmul v w))
(define-fun opt_w7  () (_ BitVec 64) (bvadd u (bvmul v w)))
(define-fun opt_w8  () (_ BitVec 64) (bvsub u opt_w6))
(define-fun opt_w9  () (_ BitVec 64) (bvsub opt_w8 opt_w7))
(define-fun opt_w11 () (_ BitVec 64) (bvadd opt_w7 (bvmul r opt_w9)))
(define-fun opt_w14 () (_ BitVec 64) (bvadd opt_w9 (bvmul bias r)))

; 3. 64-bit AMD VOP64 GPU Instruction Sequence (compileRtlExprToAmdGpu zkNttButterflyFoldRtlExpr)
(define-fun vop64_v3 () (_ BitVec 64) (bvmul v w))
(define-fun vop64_v4 () (_ BitVec 64) (bvadd u vop64_v3))
(define-fun vop64_v5 () (_ BitVec 64) (bvsub u vop64_v3))
(define-fun vop64_v6 () (_ BitVec 64) (bvsub vop64_v5 vop64_v4))
(define-fun vop64_v8 () (_ BitVec 64) (bvadd vop64_v4 (bvmul r vop64_v6)))

; 4. Goldilocks shift/mask mid-term identity: (hi_lo32 << 32) - hi_lo32 == hi_lo32 * 0xFFFFFFFF
(declare-const hi_lo32 (_ BitVec 32))
(define-fun hi_lo64 () (_ BitVec 64) ((_ zero_extend 32) hi_lo32))
(define-fun gl_shift_sub () (_ BitVec 64) (bvsub (bvshl hi_lo64 (_ bv32 64)) hi_lo64))
(define-fun gl_mul_eps   () (_ BitVec 64) (bvmul hi_lo64 #x00000000ffffffff))

; Assert negation of conjunction of all equivalence obligations (must be UNSAT)
(assert (or
  (distinct opt_w7  raw_w7)
  (distinct opt_w8  raw_w8)
  (distinct opt_w11 raw_w11)
  (distinct opt_w14 raw_w14)
  (distinct vop64_v8 opt_w11)
  (distinct gl_shift_sub gl_mul_eps)
))

(check-sat)
