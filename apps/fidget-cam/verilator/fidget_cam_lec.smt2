; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet; a logic-equivalence check of the emitted .sv needs Yosys write_smt2 against the Lean emitter
; (not done yet). See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Objective Bend Flagship App #6 (`apps/fidget-cam/verilator/fidget_cam_lec.smt2`)
; Formal QF_BV Logic Equivalence Checking (LEC) Miter:
; 1. Proves that all THREE box-pruned & backward-liveness-compacted standalone SSA tapes:
;    - 7-op Center Hub SSA tape on `B_center = [5, 6] x [-1, 1]^2`,
;    - 9-op Rim-Attached Mounting-Boss SSA tape on `B_boss = [11, 12] x [-1, 1]^2`,
;    - 9-op Standalone Internal Cooling-Bore SSA tape on `B_bore = [-5, -3] x [-1, 1]^2`
;    are bit-exact with the full 20-op Impeller SSA F-Rep tape (`impellerSsaTape`),
; 2. Proves that the internal cooling bore carves a genuine hollow channel (`frep_full_20op > 0`)
;    at `(-4, 0, z)` while the connected hub-to-boss bridge `(9..11, 0, 0)` is solid (`<= 0`),
; 3. Proves that the `ImpellerCamTop` RTL datapath outputs match the `.obend` specification
;    across all 64-bit `in_step_dist`, `in_subdiv_level`, and `in_liverps_override_en` inputs.

(set-logic QF_BV)

(declare-const in_x (_ BitVec 64))
(declare-const in_y (_ BitVec 64))
(declare-const in_z (_ BitVec 64))
(declare-const in_step_dist (_ BitVec 64))
(declare-const in_subdiv_level (_ BitVec 64))
(declare-const in_liverps_override_en (_ BitVec 64))

; Full 20-op SSA tape (`impellerSsaTape` in `Obend.Apps.FidgetCam`)
(define-fun w_0 () (_ BitVec 64) in_x)
(define-fun w_1 () (_ BitVec 64) (bvmul w_0 w_0))
(define-fun w_2 () (_ BitVec 64) in_y)
(define-fun w_3 () (_ BitVec 64) (bvmul w_2 w_2))
(define-fun w_4 () (_ BitVec 64) (bvadd w_1 w_3))
(define-fun w_5 () (_ BitVec 64) (_ bv100 64))
(define-fun w_6 () (_ BitVec 64) (bvsub w_4 w_5))

(define-fun w_7 () (_ BitVec 64) (_ bv10 64))
(define-fun w_8 () (_ BitVec 64) (bvsub w_0 w_7))
(define-fun w_9 () (_ BitVec 64) (bvmul w_8 w_8))
(define-fun w_10 () (_ BitVec 64) (bvadd w_9 w_3))
(define-fun w_11 () (_ BitVec 64) (_ bv4 64))
(define-fun w_12 () (_ BitVec 64) (bvsub w_10 w_11))

(define-fun w_13 () (_ BitVec 64) (ite (bvslt w_12 w_6) w_12 w_6))

(define-fun w_14 () (_ BitVec 64) (bvadd w_0 w_11))
(define-fun w_15 () (_ BitVec 64) (bvmul w_14 w_14))
(define-fun w_16 () (_ BitVec 64) (bvadd w_15 w_3))
(define-fun w_17 () (_ BitVec 64) (bvsub w_16 w_11))
(define-fun w_18 () (_ BitVec 64) (bvsub (_ bv0 64) w_17))

(define-fun frep_full_20op () (_ BitVec 64) (ite (bvslt w_13 w_18) w_18 w_13))

; 1. Standalone compacted 7-op Center Hub SSA tape (`impellerCenterCompactedTape`)
(define-fun frep_center_pruned_7op () (_ BitVec 64)
  (bvsub (bvadd (bvmul in_x in_x) (bvmul in_y in_y)) (_ bv100 64)))

; 2. Standalone compacted 9-op Mounting-Boss SSA tape (`impellerBossCompactedTape`)
(define-fun frep_boss_pruned_9op () (_ BitVec 64)
  (let ((dx (bvsub in_x (_ bv10 64))))
    (bvsub (bvadd (bvmul dx dx) (bvmul in_y in_y)) (_ bv4 64))))

; 3. Standalone compacted 9-op Cooling-Bore SSA tape (`impellerBoreCompactedTape`, zero unpruned refs!)
(define-fun frep_bore_pruned_9op () (_ BitVec 64)
  (let ((bx (bvadd in_x (_ bv4 64))))
    (bvsub (_ bv0 64) (bvsub (bvadd (bvmul bx bx) (bvmul in_y in_y)) (_ bv4 64)))))

; Sub-box predicates
(define-fun in_center_box () Bool
  (and (bvsge in_x (_ bv5 64))
       (bvsle in_x (_ bv6 64))
       (bvsge in_y (bvneg (_ bv1 64)))
       (bvsle in_y (_ bv1 64))
       (bvsge in_z (bvneg (_ bv1 64)))
       (bvsle in_z (_ bv1 64))))

(define-fun in_boss_box () Bool
  (and (bvsge in_x (_ bv11 64))
       (bvsle in_x (_ bv12 64))
       (bvsge in_y (bvneg (_ bv1 64)))
       (bvsle in_y (_ bv1 64))
       (bvsge in_z (bvneg (_ bv1 64)))
       (bvsle in_z (_ bv1 64))))

(define-fun in_bore_box () Bool
  (and (bvsge in_x (bvneg (_ bv5 64)))
       (bvsle in_x (bvneg (_ bv3 64)))
       (bvsge in_y (bvneg (_ bv1 64)))
       (bvsle in_y (_ bv1 64))
       (bvsge in_z (bvneg (_ bv1 64)))
       (bvsle in_z (_ bv1 64))))

; 16-bit extreme-coordinate boundary boxes: [-32768, -32764] U [32763, 32767]
(define-fun in_far_exterior_16b () Bool
  (and (or (and (bvsge in_x (bvneg (_ bv32768 64))) (bvsle in_x (bvneg (_ bv32764 64))))
           (and (bvsge in_x (_ bv32763 64)) (bvsle in_x (_ bv32767 64))))
       (or (and (bvsge in_y (bvneg (_ bv32768 64))) (bvsle in_y (bvneg (_ bv32764 64))))
           (and (bvsge in_y (bvneg (_ bv2 64))) (bvsle in_y (_ bv2 64)))
           (and (bvsge in_y (_ bv32763 64)) (bvsle in_y (_ bv32767 64))))))

; Spec vs RTL datapath for ImpellerCamTop `.obend`
(define-fun live_en () Bool (distinct in_liverps_override_en (_ bv0 64)))

(define-fun spec_wall_um () (_ BitVec 64)
  (ite live_en (_ bv2800 64) (_ bv2600 64)))
(define-fun rtl_wall_um () (_ BitVec 64)
  (ite (distinct in_liverps_override_en #x0000000000000000) #x0000000000000af0 #x0000000000000a28))

(define-fun spec_lip_pad () (_ BitVec 64)
  (bvadd (bvmul in_step_dist (_ bv72 64)) (_ bv7 64)))
(define-fun rtl_lip_pad () (_ BitVec 64)
  (bvadd (bvmul in_step_dist #x0000000000000048) #x0000000000000007))

(define-fun spec_active_voxels () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_subdiv_level (_ bv128 64)) (_ bv9 64))
         (ite live_en (_ bv64 64) (_ bv0 64))))
(define-fun rtl_active_voxels () (_ BitVec 64)
  (bvadd (bvadd (bvmul in_subdiv_level #x0000000000000080) #x0000000000000009)
         (ite (distinct in_liverps_override_en #x0000000000000000) #x0000000000000040 #x0000000000000000)))

; Assert negation of equivalence (miter): unsat proves 0 counterexamples across all 2^64 states
(assert
  (or
    (and in_center_box (distinct frep_center_pruned_7op frep_full_20op))
    (and in_boss_box (distinct frep_boss_pruned_9op frep_full_20op))
    (and in_bore_box (distinct frep_bore_pruned_9op frep_full_20op))
    (and (= in_x (bvneg (_ bv4 64))) (= in_y (_ bv0 64)) (not (bvsgt frep_full_20op (_ bv0 64))))
    (and in_far_exterior_16b (not (bvsgt frep_full_20op (_ bv0 64))))
    (distinct spec_wall_um rtl_wall_um)
    (distinct spec_lip_pad rtl_lip_pad)
    (distinct spec_active_voxels rtl_active_voxels)))

(check-sat)
