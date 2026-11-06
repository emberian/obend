#!/usr/bin/env python3
"""Plant a removed s_waitcnt in the machine code the device will run, through Mesa's shader cache.

    python3 -I waitcnt_plant.py CACHE_DIR ISA.txt STAGE INSTR

RADV compiles our WGSL to the machine code in ISA.txt (hardware/gpu/isa/<graph>.txt) and, when the
device runs with MESA_DISK_CACHE_MULTI_FILE=1 MESA_SHADER_CACHE_DIR=CACHE_DIR, keeps each compiled
pipeline in CACHE_DIR/mesa_shader_cache/xx/<sha> as (Mesa 24.2.8 src/util/disk_cache_os.c,
`create_cache_item_file`): the driver keys blob, a u32 item type, a `cache_entry_file_data` (u32 `util_hash_crc32`,
zlib's crc32 inverted, of the compressed bytes; u32 uncompressed size), then the zstd frame of the pipeline blob, which holds
the shader's code verbatim. This script finds the entry whose blob contains STAGE's dwords, replaces
instruction INSTR (one dword, an s_waitcnt) by `s_nop 0` (0xbf800000, the same width, so nothing moves),
recompresses, rewrites the crc, and the next run of obend-gpu-run with the same cache executes the
planted program on the card. That run is the measurement rung G2's waitcnt check is named after:
whether the card, without the wait, computes something else.
"""
import glob
import os
import struct
import subprocess
import sys
import zlib

ZSTD_MAGIC = b"\x28\xb5\x2f\xfd"


def mesa_crc32(data):
    """util_hash_crc32 (src/util/crc32.c): `~crc32(0, data, size)` with zlib's crc32."""
    return (~zlib.crc32(data)) & 0xFFFFFFFF


def stage_words(isa, stage):
    out, cur, k = [], None, -1
    for ln in open(isa):
        if ln.startswith("## stage"):
            k += 1
            cur = out if k == stage else None
            continue
        if cur is not None and ln.startswith("\t") and "\t; " in ln:
            cur.append([int(w, 16) for w in ln.rstrip("\n").split("\t; ", 1)[1].split()])
    return out


def main():
    cache_dir, isa, stage, instr = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    insts = stage_words(isa, stage)
    code = b"".join(struct.pack("<I", w) for ws in insts for w in ws)
    off = sum(4 * len(ws) for ws in insts[:instr])
    assert len(insts[instr]) == 1, "the planted instruction must be one dword"
    hits = 0
    for path in glob.glob(os.path.join(cache_dir, "mesa_shader_cache", "??", "*")):
        raw = open(path, "rb").read()
        z = raw.find(ZSTD_MAGIC)
        if z < 8:
            continue
        crc, usize = struct.unpack("<II", raw[z - 8:z])
        comp = raw[z:]
        if mesa_crc32(comp) != crc:
            continue
        blob = subprocess.run(["zstd", "-d", "-q", "-c"], input=comp, capture_output=True, check=True).stdout
        assert len(blob) == usize
        at = blob.find(code)
        if at < 0:
            continue
        patched = blob[:at + off] + struct.pack("<I", 0xBF800000) + blob[at + off + 4:]
        comp2 = subprocess.run(["zstd", "-q", "-c", "-19"], input=patched, capture_output=True, check=True).stdout
        new = raw[:z - 8] + struct.pack("<II", mesa_crc32(comp2), len(patched)) + comp2
        open(path, "wb").write(new)
        print(f"patched {path}: stage {stage} instruction {instr} ({insts[instr][0]:08x}) -> s_nop 0 at blob offset {at + off}")
        hits += 1
    if hits != 1:
        print(f"[FAIL] {hits} cache entries hold stage {stage}'s code (expected 1)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
