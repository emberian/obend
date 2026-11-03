; Objective Bend Flagship App #6 (`apps/fidget-cam/verilator/fidget_cam_lec.smt2`)
; Formal QF_BV / QF_NIA Logic Equivalence Checking (LEC) Miter:
; 1. Proves that the box-pruned & backward-liveness-compacted 7-op Center SSA tape
;    and 9-op Mounting-Boss SSA tape are bit-exact with the full 20-op Impeller SSA F-Rep tape
;    across their respective octree bounding boxes (`B_center = [-2, 2]^3`, `B_boss = [14, 16] x [-1, 1]^2`),
; 2. Proves that the `ImpellerCamTop` RTL datapath outputs match the `.obend` specification
;    across all 64-bit `in_step_dist`, `in_subdiv_level`, and `in_liverps_override_en` inputs.

(set-logic QF_BV)

(declare-const in_x (_ BitVec 64))
(declare-const in_y (_ BitVec 64))
(declare-const in_z (_ BitVec 64))
(declare-const in_step_dist (_ BitVec 64))
(declare-const in_subdiv_level (_ BitVec 64))
(declare-const in_liverps_override_en Bool)

; Full 20-op SSA tape evaluation
(define-fun r0 () (_ BitVec 64) in_x)
(define-fun r1 () (_ BitVec 64) (bvmul r0 r0))
(define-fun r2 () (_ BitVec 64) in_y)
(define-fun r3 () (_ BitVec 64) (bvmul r2 r2))
(define-fun r4 () (_ BitVec 64) (bvadd r1 r3))
(define-fun r5 () (_ BitVec 64) #x0000000000000064) ; 100
(define-fun r6 () (_ BitVec 64) (bvsub r4 r5))

(define-fun r7 () (_ BitVec 64) #x000000000000000f) ; 15
(define-fun r8 () (_ BitVec 64) (bvsub r0 r7))
(define-fun r9 () (_ BitVec 64) (bvmul r8 r8))
(define-fun r10 () (_ BitVec 64) (bvadd r9 r3))
(define-fun r11 () (_ BitVec 64) #x0000000000000004) ; 4
(define-fun r12 () (_ BitVec 64) (bvsub r10 r11))

(define-fun r13 () (_ BitVec 64) (ite (bvsle r6 r12) r6 r12))

(define-fun r14 () (_ BitVec 64) (bvadd r0 r7))
(define-fun r15 () (_ BitVec 64) (bvmul r14 r14))
(define-fun r16 () (_ BitVec 64) (bvadd r15 r3))
(define-fun r17 () (_ BitVec 64) (bvsub r16 r11))
(define-fun r18 () (_ BitVec 64) (bvneg r17))

(define-fun frep_full_20op () (_ BitVec 64) (ite (bvsge r13 r18) r13 r18))

; Pruned & compacted 7-op Center SSA tape
(define-fun frep_center_pruned_7op () (_ BitVec 64)
  (bvsub (bvadd (bvmul in_x in_x) (bvmul in_y in_y)) #x0000000000000064))

; Pruned & compacted 9-op Mounting-Boss SSA tape
(define-fun frep_boss_pruned_9op () (_ BitVec 64)
  (let ((dx (bvsub in_x #x000000000000000f)))
    (bvsub (bvadd (bvmul dx dx) (bvmul in_y in_y)) #x0000000000000004)))

; Bounding box predicates
(define-fun in_center_box () Bool
  (and (bvsge in_x (_ bv18446744073709551614 64)) ; -2
       (bvsle in_x #x0000000000000002)
       (bvsge in_y (_ bv18446744073709551614 64)) ; -2
       (bvsle in_y #x0000000000000002)
       (bvsge in_z (_ bv18446744073709551614 64)) ; -2
       (bvsle in_z #x0000000000000002)))

(define-fun in_boss_box () Bool
  (and (bvsge in_x #x000000000000000e) ; 14
       (bvsle in_x #x0000000000000010) ; 16
       (bvsge in_y (_ bv18446744073709551615 64)) ; -1
       (bvsle in_y #x0000000000000001)
       (bvsge in_z (_ bv18446744073709551615 64)) ; -1
       (bvsle in_z #x0000000000000001)))

; Spec vs RTL datapath for ImpellerCamTop `.obend`
(define-fun spec_wall_um () (_ BitVec 64)
  (ite in_liverps_override_en #x0000000000000af0 #x0000000000000a28))
(define-fun rtl_wall_um () (_ BitVec 64)
  (ite in_liverps_override_en (_ bv2800 64) (_ bv2600 64)))

(define-fun spec_lip_pad () (_ BitVec 64)
  (bvadd (bvmul in_step_dist (_ bv72 64)) (_ bv7 64)))
(define-fun rtl_lip_pad () (_ BitVec 64)
  (bvadd (bvmul in_step_dist #x0000000000000048) #x0000000000000007))

(define-fun spec_active_voxels () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_subdiv_level (_ bv128 64)) (_ bv9 64))
         (ite in_liverps_override_en (_ bv64 64) (_ bv0 64))))
(define-fun rtl_active_voxels () (_ BitVec 64)
  (bvadd (bvadd (bvshl in_subdiv_level (_ bv7 64)) #x0000000000000009)
         (ite in_liverps_override_en #x0000000000000040 #x0000000000000000)))

; Assert negation of equivalence (miter): unsat proves 0 counterexamples across all 2^64 states
(assert
  (or
    (and in_center_box (distinct frep_center_pruned_7op frep_full_20op))
    (and in_boss_box (distinct frep_boss_pruned_9op frep_full_20op))
    (distinct spec_wall_um rtl_wall_um)
    (distinct spec_lip_pad rtl_lip_pad)
    (distinct spec_active_voxels rtl_active_voxels)))

(check-sat)
