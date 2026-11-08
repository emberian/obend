# Resource observations and an occupancy model

`grade.py PLAN_JSON ISA_TXT --wave-size 64` consumes the dispatch plan and the
real `isa_extract.py` output. It requires a matching stage number, file and thread
count. It records VGPR, SGPR, LDS bytes/workgroup, scratch bytes/wave and code size
reported by RADV, then computes the **static Mesa occupancy estimate** for gfx1031.
Wave size must come from the compiler dump, not the workgroup size. The gate reads
the allocated ACO VCC mask class (`s2` for wave64, `s1` for wave32), and independently
requires its occupancy estimate to equal RADV's reported `Subgroups per SIMD`.

The model follows Mesa 24.2.8's
[`radv_get_max_waves`](https://github.com/chaotic-cx/mesa-mirror/blob/mesa-24.2.8/src/amd/vulkan/radv_shader.c#L2414)
and [`ac_gpu_info`](https://github.com/chaotic-cx/mesa-mirror/blob/mesa-24.2.8/src/amd/common/ac_gpu_info.c):
512 physical wave64 VGPRs/SIMD, allocation rounded to 8 (wave64) or 16 (wave32),
16 wave slots/SIMD, 128 KiB LDS/WGP, four SIMD/WGP, 1024-byte LDS allocation
rounding. SGPR usage is recorded but does not constrain this gfx10+ occupancy
formula. `mesa_max_waves` uses Mesa's final wave32-normalized reporting convention;
`mesa_waves_per_simd` is the intermediate estimate in waves of the selected size.
These are a transcription of that compiler's model, not measured hardware residency.
The [RADV statistics definitions](https://github.com/chaotic-cx/mesa-mirror/blob/mesa-24.2.8/src/amd/vulkan/radv_pipeline.c#L912)
fix the units. AMD's [occupancy guide](https://gpuopen.com/learn/occupancy-explained/)
explains why resource limits alone do not determine achieved occupancy.

Dispatch count and total code size compose by summation; allocated wire bytes
come from the dispatch plan. When the emitter provides `logicalReadBytes` and
`logicalWriteBytes`, the grade retains and sums those logical access counts.
For acyclic ISA the model also sums the byte widths of all vector buffer/global
loads and stores, multiplied by active invocations. This is a conservative
requested-byte bound: divergent paths overcount, cache effects are absent, scalar
descriptor loads/LDS/scratch are excluded. It is **not measured DRAM traffic**.
Backward branches or unsupported memory operations produce an unavailable bound,
not a guessed number. Scratch and code size do not turn into invented time costs.

`gate.py --runner /path/to/obend-gpu-run --work /new/output/directory` runs two
real shaders on RADV. The ordinary shader computes `y[i] = x[i] + 1`. The plant
stores repeated copies in a 32 KiB workgroup array and reads a data-dependent slot
from the next lane after a barrier; it computes the same output. The gate requires
both output checks to pass, actual compiled machine code to change, reported LDS
to increase, and predicted residency to decrease. It preserves source, raw compiler
dump, extracted ISA, output and grade in the new directory. It never alters a
statistics file to manufacture the change. The small plant is intentionally a
resource-pressure experiment, not an alternative NTT implementation.
The changed-code comparison hashes only instruction dwords; differing graph-name
headers or resource metadata cannot satisfy it.

This delivers an empirical resource-model gate. It does **not** predict VGPR/LDS
allocation from source, prove a lax-monoidal grading theorem, or claim the full G5
rung from `review/GPU-PROGRAM-20261105.md` is complete. Those stronger claims remain
open; compiler allocations are explicitly observations supplied to the model.

Remeasured gate result on hbox RX 6750 XT, RADV Mesa 24.2.8, 2026-11-06:

| Resource | Ordinary | LDS pressure |
|---|---:|---:|
| VGPR / SGPR | 8 / 128 | 8 / 128 |
| LDS bytes/workgroup | 0 | 32768 |
| Scratch bytes/wave | 0 | 0 |
| Machine code bytes | 56 | 332 |
| Predicted Mesa wave64 waves/SIMD | 16 | 1 |
| RADV normalized Subgroups/SIMD | 32 | 2 |

Both exact output vectors passed, including a 32-bit carry. `resume-results/`
preserves the fresh run; `results/` retains the predecessor’s run. The planted shader contains a real loop, so its static global traffic
bound is unavailable, as intended. The real repeated-NOP shorthand in its compiler
dump also exercises `isa_extract.py`'s expansion and code-byte count check.

## Final packed NTT resource grades

The fresh `resume-ntt-{1024,65536,1048576}-grade.json` files refer to the same packed
source as the resumed 1024-sample benchmarks in `../baseline/`. They were graded
from new RADV dumps on 2026-11-06. Fresh artifact-only emission matched the
committed plans and shader bytes; the retained expected outputs matched the
committed manifests. Fresh extracted ISA matched the committed ISA byte for byte,
and every allocation, code-size and logical-traffic number below reproduced.
The predecessor’s `ntt-*-grade.json` files remain historical evidence. Every stage uses wave64, confirmed from
its own ACO `s2` VCC allocation in the matching raw dump. The predicted normalized
occupancy equals RADV's `Subgroups per SIMD` for every stage, not only for the
pressure-test shader above.

Every measured NTT stage reports **64 VGPRs, 128 SGPRs, 4096 LDS bytes/workgroup and
zero scratch**. Both the register and LDS formulas give an upper limit of
**8 wave64 waves/SIMD**, reported by RADV as **16 normalized subgroups/SIMD**.
This is a static resource ceiling; small dispatches need not supply enough work
to attain it.

| N | Dispatches | Wire buffer bytes | Total code bytes | Logical global access bytes | Logical workgroup access bytes |
|---:|---:|---:|---:|---:|---:|
| 1,024 | 3 | 16,384 | 13,864 | 92,160 | 49,152 |
| 65,536 | 2 | 1,048,576 | 20,840 | 6,029,312 | 6,291,456 |
| 1,048,576 | 3 | 16,777,216 | 26,912 | 136,314,880 | 134,217,728 |

Logical access bytes sum the emitter's dispatch-level read/write annotations;
workgroup accesses are reported separately from global-buffer accesses. These
are source-model counts, **not measured DRAM or LDS transactions**. All three
real ISA programs contain loops, so the independent acyclic-ISA traffic bound
is unavailable rather than substituted for those counts.

`plans/ntt-N.json` retains just the cost-relevant fields from each full emitted
plan, plus that full file's SHA-256. Constants and wire layout are omitted from
these small excerpts. Each grade includes the full plan, final extracted ISA and
raw RADV dump hashes, the source annotations, and the observed subgroup value
per stage. The final ISA itself is in `../isa/ntt-N.txt`; the full generated plan
is regenerated by the emitter. To reproduce the basic grade from the excerpt:

```
python3 grade.py plans/ntt-1024.json ../isa/ntt-1024.txt --wave-size 64
```

The fresh grades additionally retain the raw-dump occupancy cross-check and
workgroup-access annotations. No resource allocation is inferred from the timing
results, and the source-to-register-allocation proof remains open.

The fresh compiler dumps are `../evidence/resume-ntt-N-radv.txt`; the gate log
is `../evidence/resume-measurements.log`. The replay script used for this run is
`../evidence/resume-measurements.py` (hbox paths recorded explicitly).
The tightened machine-code comparison was rerun successfully in
`../evidence/resume-resource-machine-gate.log`; `resume-results/` contains that run.
