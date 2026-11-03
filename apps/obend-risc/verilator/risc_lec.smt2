; Objective Bend Flagship App #1: 3-Layer Open-Recursive RISC Softcore
; SMT-LIB2 QF_BV Logical Equivalence Checking (LEC), Non-Interference & Trap Preemption
(set-logic QF_BV)
(set-option :produce-models false)

(declare-const imem_rdata (_ BitVec 64))
(declare-const dmem_rdata (_ BitVec 64))
(declare-const pc         (_ BitVec 64))
(declare-const mstatus    (_ BitVec 64))
(declare-const mepc       (_ BitVec 64))
(declare-const mcause     (_ BitVec 64))
(declare-const rs1_val    (_ BitVec 64))
(declare-const rs2_val    (_ BitVec 64))

; 1. Spec bit-slice decoders (div/mod) vs RTL shift/mask decoders
(define-fun spec_opcode () (_ BitVec 64) (bvurem imem_rdata (_ bv128 64)))
(define-fun spec_rd     () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv128 64)) (_ bv32 64)))
(define-fun spec_funct3 () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv4096 64)) (_ bv8 64)))
(define-fun spec_rs1    () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv32768 64)) (_ bv32 64)))
(define-fun spec_rs2    () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv1048576 64)) (_ bv32 64)))
(define-fun spec_imm12  () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv1048576 64)) (_ bv4096 64)))
(define-fun spec_funct7 () (_ BitVec 64) (bvurem (bvudiv imem_rdata (_ bv33554432 64)) (_ bv128 64)))

(define-fun rtl_opcode () (_ BitVec 64) (bvand imem_rdata (_ bv127 64)))
(define-fun rtl_rd     () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv7 64)) (_ bv31 64)))
(define-fun rtl_funct3 () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv12 64)) (_ bv7 64)))
(define-fun rtl_rs1    () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv15 64)) (_ bv31 64)))
(define-fun rtl_rs2    () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv20 64)) (_ bv31 64)))
(define-fun rtl_imm12  () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv20 64)) (_ bv4095 64)))
(define-fun rtl_funct7 () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv25 64)) (_ bv127 64)))

; 2. Layer 1 (BaseRiscCore), Layer 2 (PrivilegeCsrOverride), Layer 3 (CustomSimdZkExt) RTL datapaths
(define-fun is_trap () Bool (and (= rtl_opcode (_ bv115 64)) (= rtl_imm12 (_ bv0 64))))
(define-fun is_mret () Bool (and (= rtl_opcode (_ bv115 64)) (= rtl_imm12 (_ bv770 64))))
(define-fun is_custom_ext () Bool (= rtl_opcode (_ bv43 64)))

(define-fun base_alu_rhs () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv19 64)) rtl_imm12 rs2_val))

(define-fun base_alu_out () (_ BitVec 64)
  (ite (= rtl_funct3 (_ bv0 64)) (bvadd rs1_val base_alu_rhs)
  (ite (= rtl_funct3 (_ bv1 64)) (bvsub rs1_val base_alu_rhs)
  (ite (= rtl_funct3 (_ bv2 64)) (bvmul rs1_val base_alu_rhs)
                                 (bvadd rs1_val base_alu_rhs)))))

(define-fun custom_ext_out () (_ BitVec 64)
  (ite (= rtl_funct3 (_ bv0 64)) (bvadd (bvmul rs1_val rs2_val) rtl_funct7)
  (ite (= rtl_funct3 (_ bv1 64)) (bvadd (bvmul rs1_val (_ bv4294967295 64)) rs2_val)
                                 (bvadd rs1_val (bvshl rs2_val (_ bv1 64))))))

(define-fun base_wb_val () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv3 64)) dmem_rdata
  (ite (= rtl_opcode (_ bv111 64)) (bvadd pc (_ bv4 64))
  base_alu_out)))

(define-fun priv_wb_val () (_ BitVec 64)
  (ite is_trap (bvadd pc (_ bv4 64)) base_wb_val))

(define-fun composed_wb_val () (_ BitVec 64)
  (ite is_trap (bvadd pc (_ bv4 64))
  (ite is_custom_ext custom_ext_out base_wb_val)))

(define-fun base_next_pc () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv99 64))
    (ite (= rs1_val rs2_val) (bvadd pc (bvshl rtl_funct7 (_ bv2 64))) (bvadd pc (_ bv4 64)))
  (ite (= rtl_opcode (_ bv111 64))
    (bvadd pc (bvshl rtl_imm12 (_ bv2 64)))
    (bvadd pc (_ bv4 64)))))

(define-fun composed_next_pc () (_ BitVec 64)
  (ite is_trap (_ bv64 64)
  (ite is_mret mepc base_next_pc)))

(define-fun composed_next_mstatus () (_ BitVec 64)
  (ite is_trap (_ bv24 64) (ite is_mret (_ bv8 64) mstatus)))

(define-fun composed_next_mepc () (_ BitVec 64)
  (ite is_trap (bvadd pc (_ bv4 64)) mepc))

(define-fun composed_next_mcause () (_ BitVec 64)
  (ite is_trap (_ bv11 64) mcause))

(define-fun composed_dmem_we () (_ BitVec 64)
  (ite is_trap (_ bv0 64) (ite (= rtl_opcode (_ bv35 64)) (_ bv1 64) (_ bv0 64))))

; Assert negation of conjunction of all 3 LEC obligations (must be UNSAT)
(assert (or
  ; Obligation A: In-core bit-slice decoder equivalence
  (distinct spec_opcode rtl_opcode)
  (distinct spec_rd     rtl_rd)
  (distinct spec_funct3 rtl_funct3)
  (distinct spec_rs1    rtl_rs1)
  (distinct spec_rs2    rtl_rs2)
  (distinct spec_imm12  rtl_imm12)
  (distinct spec_funct7 rtl_funct7)

  ; Obligation B: Base opcode non-interference (when opcode != 43 and opcode != 115)
  (and (not (= rtl_opcode (_ bv43 64)))
       (not (= rtl_opcode (_ bv115 64)))
       (or (distinct composed_wb_val base_wb_val)
           (distinct composed_next_pc base_next_pc)))

  ; Obligation C: Privilege trap preemption over base and extension layers
  (and is_trap
       (or (distinct composed_next_pc (_ bv64 64))
           (distinct composed_next_mepc (bvadd pc (_ bv4 64)))
           (distinct composed_next_mcause (_ bv11 64))
           (distinct composed_next_mstatus (_ bv24 64))
           (distinct composed_dmem_we (_ bv0 64))))
))

(check-sat)
