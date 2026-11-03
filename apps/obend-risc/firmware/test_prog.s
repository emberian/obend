# Objective Bend 3-Layer Open-Recursive RISC Softcore Firmware Test
# Layers exercised:
#   Layer 1 (BaseRiscCore):         8-element Fibonacci sequence in x1..x8 (1, 1, 2, 3, 5, 8, 13, 21)
#   Layer 2 (PrivilegeCsrOverride): Synchronous ECALL trap at PC=0x20 -> mtvec=0x40 & MRET to mepc=0x24
#   Layer 3 (CustomSimdZkExt):      4 custom opcode 0x2B ZK_MAC instructions accumulating into x11..x14
#   Final Verification:             Store combined checksum x15 = x8 + x10 + x14 = 1345 to dmem[0]

.section .text
.globl _start

_start:
    # Phase 1: 8-element Fibonacci sequence (x1..x8)
    addi    x1, x0, 1               # 0x00: 0x00100093  x1 = 1
    addi    x2, x0, 1               # 0x04: 0x00100113  x2 = 1
    add     x3, x1, x2              # 0x08: 0x002081B3  x3 = 2
    add     x4, x2, x3              # 0x0C: 0x00310233  x4 = 3
    add     x5, x3, x4              # 0x10: 0x004182B3  x5 = 5
    add     x6, x4, x5              # 0x14: 0x00520333  x6 = 8
    add     x7, x5, x6              # 0x18: 0x006283B3  x7 = 13
    add     x8, x6, x7              # 0x1C: 0x00730433  x8 = 21

    # Phase 2: Trigger synchronous CSR trap (PrivilegeCsrOverride layer)
    ecall   x9                      # 0x20: 0x000004F3  mepc<=0x24, mcause<=11, mstatus<=24, pc<=0x40

    # Phase 3: 4 CustomSimdZkExt (opcode 0x2B) MAC instructions after MRET
    zk.mac  x11, x6, x7, 1          # 0x24: 0x027305AB  x11 = 8 * 13 + 1 = 105
    zk.mac  x12, x11, x3, 2         # 0x28: 0x0435862B  x12 = 105 * 2 + 2 = 212
    zk.mac  x13, x12, x4, 3         # 0x2C: 0x064606AB  x13 = 212 * 3 + 3 = 639
    zk.mac  x14, x13, x3, 4         # 0x30: 0x0836872B  x14 = 639 * 2 + 4 = 1282

    # Phase 4: Combine Fibonacci + CSR Trap + CustomSimdZkExt checksum and store to dmem[0]
    add     x15, x8, x10            # 0x34: 0x00A407B3  x15 = 21 + 42 = 63
    add     x15, x15, x14           # 0x38: 0x00E787B3  x15 = 63 + 1282 = 1345
    sw      x15, 0(x0)              # 0x3C: 0x00F02023  dmem[0] <= 1345

    # MTVEC Trap Handler at PC = 0x40 (word index 16)
_mtvec_handler:
    addi    x10, x0, 42             # 0x40: 0x02A00513  x10 = 42 (trap handler marker)
    mret                            # 0x44: 0x30200073  pc <= mepc (0x24), mstatus <= 8
