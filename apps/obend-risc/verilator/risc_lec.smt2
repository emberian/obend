; HAND-WRITTEN property check (relabelled 2026-11-04). This file was typed by hand: it is not derived
; from the .sv beside it nor from the Lean RtlModule, so z3 `unsat` establishes properties of the
; formulas written here, not equivalence of the RTL with anything. It is kept as a worked property
; sheet; a logic-equivalence check of the emitted .sv needs Yosys write_smt2 against the Lean emitter
; (not done yet). See review/EXPERT-fpga-silicon-20261103.md §3.2.
; Objective Bend Flagship App #1: 3-Layer Open-Recursive RISC Softcore
; SMT-LIB2 QF_BV Logical Equivalence Checking (LEC), Sign-Extended Decoders, Non-Interference & Trap Preemption
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

; 1. Spec bit-slice & sign-extend decoders (extract / sign_extend) vs RTL shift/mask decoders
(define-fun spec_opcode  () (_ BitVec 64) ((_ zero_extend 57) ((_ extract 6 0)   imem_rdata)))
(define-fun spec_rd      () (_ BitVec 64) ((_ zero_extend 59) ((_ extract 11 7)  imem_rdata)))
(define-fun spec_funct3  () (_ BitVec 64) ((_ zero_extend 61) ((_ extract 14 12) imem_rdata)))
(define-fun spec_rs1     () (_ BitVec 64) ((_ zero_extend 59) ((_ extract 19 15) imem_rdata)))
(define-fun spec_rs2     () (_ BitVec 64) ((_ zero_extend 59) ((_ extract 24 20) imem_rdata)))
(define-fun spec_imm_u12 () (_ BitVec 64) ((_ zero_extend 52) ((_ extract 31 20) imem_rdata)))
(define-fun spec_funct7  () (_ BitVec 64) ((_ zero_extend 57) ((_ extract 31 25) imem_rdata)))
(define-fun spec_imm_i   () (_ BitVec 64) ((_ sign_extend 52) ((_ extract 31 20) imem_rdata)))
(define-fun spec_imm_s   () (_ BitVec 64)
  ((_ sign_extend 52) (concat ((_ extract 31 25) imem_rdata) ((_ extract 11 7) imem_rdata))))
(define-fun spec_imm_b   () (_ BitVec 64)
  ((_ sign_extend 51)
    (concat ((_ extract 31 31) imem_rdata)
            ((_ extract 7 7)   imem_rdata)
            ((_ extract 30 25) imem_rdata)
            ((_ extract 11 8)  imem_rdata)
            #b0)))

(define-fun rtl_opcode  () (_ BitVec 64) (bvand imem_rdata (_ bv127 64)))
(define-fun rtl_rd      () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv7 64)) (_ bv31 64)))
(define-fun rtl_funct3  () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv12 64)) (_ bv7 64)))
(define-fun rtl_rs1     () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv15 64)) (_ bv31 64)))
(define-fun rtl_rs2     () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv20 64)) (_ bv31 64)))
(define-fun rtl_imm_u12 () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv20 64)) (_ bv4095 64)))
(define-fun rtl_funct7  () (_ BitVec 64) (bvand (bvlshr imem_rdata (_ bv25 64)) (_ bv127 64)))
(define-fun rtl_imm_i   () (_ BitVec 64) (bvashr (bvshl imem_rdata (_ bv32 64)) (_ bv52 64)))
(define-fun rtl_imm_s   () (_ BitVec 64)
  (bvashr (bvshl (bvor (bvshl rtl_funct7 (_ bv5 64)) rtl_rd) (_ bv52 64)) (_ bv52 64)))
(define-fun rtl_imm_b   () (_ BitVec 64)
  (bvashr
    (bvshl
      (bvor
        (bvor
          (bvshl (bvand (bvlshr imem_rdata (_ bv31 64)) (_ bv1 64)) (_ bv12 64))
          (bvshl (bvand (bvlshr imem_rdata (_ bv7 64))  (_ bv1 64)) (_ bv11 64)))
        (bvor
          (bvshl (bvand (bvlshr imem_rdata (_ bv25 64)) (_ bv63 64)) (_ bv5 64))
          (bvshl (bvand (bvlshr imem_rdata (_ bv8 64))  (_ bv15 64)) (_ bv1 64))))
      (_ bv51 64))
    (_ bv51 64)))

; 2. Layer 1 (BaseRiscCore), Layer 2 (PrivilegeCsrOverride), Layer 3 (CustomSimdZkExt) RTL datapaths
(define-fun is_trap () Bool
  (and (= rtl_opcode (_ bv115 64)) (= rtl_funct3 (_ bv0 64)) (= rtl_imm_u12 (_ bv0 64))))
(define-fun is_mret () Bool
  (and (= rtl_opcode (_ bv115 64)) (= rtl_funct3 (_ bv0 64)) (= rtl_imm_u12 (_ bv770 64))))
(define-fun is_csrrs () Bool
  (and (= rtl_opcode (_ bv115 64)) (= rtl_funct3 (_ bv2 64))))
(define-fun is_custom_ext () Bool (= rtl_opcode (_ bv43 64)))

(define-fun csr_rdata () (_ BitVec 64)
  (ite (= rtl_imm_u12 (_ bv768 64)) mstatus
  (ite (= rtl_imm_u12 (_ bv833 64)) mepc
  (ite (= rtl_imm_u12 (_ bv834 64)) mcause (_ bv80 64)))))

(define-fun base_alu_rhs () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv19 64)) rtl_imm_i rs2_val))

(define-fun shamt () (_ BitVec 64) (bvand base_alu_rhs (_ bv63 64)))

(define-fun base_alu_out () (_ BitVec 64)
  (ite (= rtl_funct3 (_ bv0 64))
    (ite (and (= rtl_opcode (_ bv51 64)) (= rtl_funct7 (_ bv32 64)))
      (bvsub rs1_val base_alu_rhs)
      (ite (and (= rtl_opcode (_ bv51 64)) (= rtl_funct7 (_ bv1 64)))
        (bvmul rs1_val base_alu_rhs)
        (bvadd rs1_val base_alu_rhs)))
  (ite (= rtl_funct3 (_ bv1 64)) (bvshl rs1_val shamt)
  (ite (= rtl_funct3 (_ bv2 64)) (ite (bvslt rs1_val base_alu_rhs) (_ bv1 64) (_ bv0 64))
  (ite (= rtl_funct3 (_ bv3 64)) (ite (bvult rs1_val base_alu_rhs) (_ bv1 64) (_ bv0 64))
  (ite (= rtl_funct3 (_ bv4 64)) (bvxor rs1_val base_alu_rhs)
  (ite (= rtl_funct3 (_ bv5 64))
    (ite (= (bvlshr rtl_funct7 (_ bv1 64)) (_ bv16 64))
      (bvashr rs1_val shamt)
      (bvlshr rs1_val shamt))
  (ite (= rtl_funct3 (_ bv6 64)) (bvor rs1_val base_alu_rhs)
                                 (bvand rs1_val base_alu_rhs)))))))))

(define-fun custom_ext_out () (_ BitVec 64)
  (ite (= rtl_funct3 (_ bv0 64)) (bvadd (bvmul rs1_val rs2_val) rtl_funct7)
  (ite (= rtl_funct3 (_ bv1 64))
    (bvadd (bvsub (bvshl (bvand rs1_val #x00000000ffffffff) (_ bv32 64))
                  (bvand rs1_val #x00000000ffffffff))
           rs2_val)
    (bvadd rs1_val (bvshl rs2_val (_ bv1 64))))))

(define-fun base_wb_val () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv3 64)) dmem_rdata
  (ite (= rtl_opcode (_ bv111 64)) (bvadd pc (_ bv4 64))
  base_alu_out)))

(define-fun composed_wb_val () (_ BitVec 64)
  (ite is_csrrs csr_rdata
  (ite is_custom_ext custom_ext_out base_wb_val)))

(define-fun base_wb_en () (_ BitVec 64)
  (ite (or (= rtl_opcode (_ bv19 64))
           (= rtl_opcode (_ bv51 64))
           (= rtl_opcode (_ bv3 64))
           (= rtl_opcode (_ bv111 64)))
       (_ bv1 64) (_ bv0 64)))

(define-fun composed_wb_en () (_ BitVec 64)
  (ite is_trap (_ bv0 64)
    (ite (or is_csrrs is_custom_ext (= base_wb_en (_ bv1 64))) (_ bv1 64) (_ bv0 64))))

(define-fun branch_taken () Bool
  (ite (= rtl_funct3 (_ bv0 64)) (= rs1_val rs2_val)
  (ite (= rtl_funct3 (_ bv1 64)) (not (= rs1_val rs2_val))
  (ite (= rtl_funct3 (_ bv4 64)) (bvslt rs1_val rs2_val)
                                 (not (bvslt rs1_val rs2_val))))))

(define-fun base_next_pc () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv99 64))
    (ite branch_taken (bvadd pc rtl_imm_b) (bvadd pc (_ bv4 64)))
  (ite (= rtl_opcode (_ bv111 64))
    (bvadd pc (bvshl rtl_imm_i (_ bv1 64)))
    (bvadd pc (_ bv4 64)))))

(define-fun composed_next_pc () (_ BitVec 64)
  (ite is_trap (_ bv80 64)
  (ite is_mret mepc base_next_pc)))

(define-fun composed_next_mstatus () (_ BitVec 64)
  (ite is_trap (_ bv24 64) (ite is_mret (_ bv8 64) mstatus)))

(define-fun composed_next_mepc () (_ BitVec 64)
  (ite is_trap (bvadd pc (_ bv4 64)) mepc))

(define-fun composed_next_mcause () (_ BitVec 64)
  (ite is_trap (_ bv11 64) mcause))

(define-fun base_dmem_we () (_ BitVec 64)
  (ite (= rtl_opcode (_ bv35 64)) (_ bv1 64) (_ bv0 64)))

(define-fun composed_dmem_we () (_ BitVec 64)
  (ite is_trap (_ bv0 64) base_dmem_we))

; Assert negation of conjunction of all 4 LEC obligations (must be UNSAT)
(assert (or
  ; Obligation A: In-core bit-slice & sign-extended immediate decoder equivalence
  (distinct spec_opcode  rtl_opcode)
  (distinct spec_rd      rtl_rd)
  (distinct spec_funct3  rtl_funct3)
  (distinct spec_rs1     rtl_rs1)
  (distinct spec_rs2     rtl_rs2)
  (distinct spec_imm_u12 rtl_imm_u12)
  (distinct spec_funct7  rtl_funct7)
  (distinct spec_imm_i   rtl_imm_i)
  (distinct spec_imm_s   rtl_imm_s)
  (distinct spec_imm_b   rtl_imm_b)

  ; Obligation B: Base opcode non-interference (when opcode != 43 and opcode != 115)
  (and (not (= rtl_opcode (_ bv43 64)))
       (not (= rtl_opcode (_ bv115 64)))
       (or (distinct composed_wb_val  base_wb_val)
           (distinct composed_wb_en   base_wb_en)
           (distinct composed_next_pc base_next_pc)
           (distinct composed_dmem_we base_dmem_we)
           (distinct composed_next_mstatus mstatus)
           (distinct composed_next_mepc    mepc)
           (distinct composed_next_mcause  mcause)))

  ; Obligation C: Privilege ECALL trap preemption over base and extension layers (including GPR writeback preemption)
  (and is_trap
       (or (distinct composed_next_pc      (_ bv80 64))
           (distinct composed_next_mepc    (bvadd pc (_ bv4 64)))
           (distinct composed_next_mcause  (_ bv11 64))
           (distinct composed_next_mstatus (_ bv24 64))
           (distinct composed_wb_en        (_ bv0 64))
           (distinct composed_dmem_we      (_ bv0 64))))

  ; Obligation D: Privilege MRET restoration without GPR or memory side effects
  (and is_mret
       (or (distinct composed_next_pc      mepc)
           (distinct composed_next_mstatus (_ bv8 64))
           (distinct composed_wb_en        (_ bv0 64))
           (distinct composed_dmem_we      (_ bv0 64))))
))

(check-sat)
