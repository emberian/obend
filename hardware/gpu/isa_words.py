#!/usr/bin/env python3
"""The machine code of a hardware/gpu/isa/<graph>.txt dump as llvm-mc's byte list: one line per instruction,
little-endian bytes of its dwords (`isa_check.sh` stage 2)."""
import sys

for ln in open(sys.argv[1]):
    if not ln.startswith("\t") or "\t; " not in ln:
        continue
    words = ln.rstrip("\n").split("\t; ", 1)[1].split()
    out = []
    for w in words:
        v = int(w, 16)
        out += [f"0x{(v >> (8 * i)) & 0xFF:02x}" for i in range(4)]
    print(" ".join(out))
