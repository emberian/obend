; Z3 SMT-LIB2 Formal Equivalence & Cleanroom Safety Check for:
; 1. Obend.Hardware.Compiler (`compileBookToRtl` on `emit (comp 1)` from ReviewMember.obend)
; 2. Obend.Hardware.Synth (`LUT3` 0xCA 2:1 mux + `CARRY8` two's-complement subtractor `a + ~b + 1`)
; 3. Obend.Hardware.FabuBlox (`checkFacilityStep` FEOL Cu/Au contamination & >150C photoresist safety)
(set-logic QF_BV)

(declare-const arg (_ BitVec 64))
(declare-const b   (_ BitVec 64))
(declare-const sel (_ BitVec 1))

; 1. Compiled `emit (comp 1)` RTL wire expressions:
;    w_0 (review) = ((arg + 1) + 1)
;    w_1 (twice)  = ((((arg + 1) + 1) + 1) + 1)
(define-fun w_0_review () (_ BitVec 64)
  (bvadd (bvadd arg #x0000000000000001) #x0000000000000001))
(define-fun w_1_twice () (_ BitVec 64)
  (bvadd (bvadd (bvadd (bvadd arg #x0000000000000001) #x0000000000000001) #x0000000000000001) #x0000000000000001))

; Specification of ReviewMember.obend (`review(x) = x + 2`, `twice(x) = review(review(x)) = x + 4`):
(define-fun spec_review () (_ BitVec 64) (bvadd arg #x0000000000000002))
(define-fun spec_twice  () (_ BitVec 64) (bvadd arg #x0000000000000004))

; 2. Two's complement CARRY8 subtractor (`arg + ~b + 1` == `arg - b`):
(define-fun carry8_sub () (_ BitVec 64)
  (bvadd (bvadd arg (bvnot b)) #x0000000000000001))
(define-fun spec_sub () (_ BitVec 64)
  (bvsub arg b))

; 3. FabuBlox Facility OS safety check:
(declare-const is_feol_furnace Bool)
(declare-const has_cu_or_au    Bool)
(declare-const temp_gt_150     Bool)
(declare-const has_photoresist Bool)

(define-fun facility_admits () Bool
  (and (not (and is_feol_furnace has_cu_or_au))
       (not (and temp_gt_150 has_photoresist))))

; Assert that EITHER:
; (a) compiled ReviewMember RTL disagrees with spec, OR
; (b) CARRY8 two's-complement subtractor disagrees with `bvsub`, OR
; (c) an admitted FabuBlox cleanroom step contaminates an FEOL furnace or scorches photoresist.
(assert
  (or (distinct w_0_review spec_review)
      (distinct w_1_twice  spec_twice)
      (distinct carry8_sub spec_sub)
      (and facility_admits is_feol_furnace has_cu_or_au)
      (and facility_admits temp_gt_150 has_photoresist)))

(check-sat)
