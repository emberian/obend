# GPU kernels: lane integration, 2026-11-06

Branch `lane-gpu-kernels`, recovered from uncommitted work based on `dev` at `0b90f5b`. Fresh recovery measurements use hbox's
RX 6750 XT (gfx1031), RADV Mesa 24.2.8. Dev at `402378a` (including square integration `2af7cf7`) is integrated by hand.
This is an integration report, not a claim
that the ISA-model gate is green. The model lane must extend its instruction and
wait-counter coverage before the new kernels can pass G2.

## Landed pieces

- `523aa7c`: shared Goldilocks specifications, limb refinements and builder.
- `55b39ec`: live layout, general workgroup source, lowering and whole-dispatch race proof.
- `81ab441`: regenerated kernels/ISA, batch runner, fresh CPU/GPU measurements and resource gate.
- `9e2cd8b`: recovery evidence and precise proof boundaries.
- `d6fa57b`: hand-resolved merge of dev `402378a`, shared square/kernel sources,
  regenerated integration artifacts and final gate evidence.

## What changed

The ordinary graph lowering now uses last-use storage allocation with a checked
live-value invariant. Dead fused wires do not allocate storage, nonoverlapping
lifetimes reuse it, and eligible last-use maps overwrite their input. Gather and
concatenation cannot take over a source they still read; another same-stage reader
also prevents takeover. The old every-wire prefix allocation is removed.

`ArrayKernel` is a general source language for indexed multi-output maps, register
programs, shared buffers, uniform phases and dispatches. `BlockLower` defines a
separate physical-memory target and proves lowering sound. `BlockEmit` emits that
source directly, including strided per-lane loops and the two address-space-correct
barriers. It contains no NTT shader template. Admission checks bounds and u32
intermediates, initialization, register closure, scatter ownership and the G4
access protocol. Even inactive code must have valid literals and nonzero divisors.

The NTT source constructor builds register radix-4 networks and multiple shared
phases per upload, using ec-gpu's Stockham organization. The chosen upload degrees
are 4+3+3, 8+8 and 7+7+6 at the three required sizes. Small tiles are packed into
physical workgroups. Canonicalization occurs in the input registers. The old
per-layer NTT builder and superseded generated stages are deleted; the new source
constructor is the only NTT path.

All shader values use two u32 limbs. Carry, shift, product assembly and
special-prime reduction are proved against the existing bitvector and Goldilocks
specifications. The emitted 32×32 widening primitive uses Naga's SHADER_INT64
extension to expose low/high multiplication; RADV's actual code uses native
`v_mul_lo_u32` and `v_mul_hi_u32`. This is **not standard u32-only WGSL syntax**.
The former general emulated 64×64 multiply path is gone. The representation and
arithmetic proof boundaries are detailed in [GPU-LIMBS-20261106](GPU-LIMBS-20261106.md).

At 65,536 points, the working device buffer is 131,072 words (1 MiB), plus a
separate 65,536-word root table and 4 KiB LDS per workgroup. At 1,048,576 points, the working device buffer is 16 MiB,
with a separate 8 MiB root table. These are allocations, not measured memory traffic.

## Universal statements

The core compiler theorem now has a checked allocation and a live-only entry
representation. This is its actual statement, omitting only the proof body:

```lean
theorem lowerArrayToGpu_sound (g : ArrayGraph) (hWf : g.wf = true)
    (hLayout : layoutOk g = true)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good g.lengths env)
    (hFlat : Flat g.lengths (gpuLayout g).base
      (liveAt (layerGraph (fuseGraph g)) g.outputs) env flat) :
    runProgram (lowerArrayToGpu g) flat = evalGraph g env
```

The block source has an independently defined physical lowering. Its bounds
hypothesis is obtained from the exact executable source admission check:

```lean
theorem checkedProgram_sound (p : Program) (mem : Memory) (flat : FlatMemory)
    (hg : Good p mem) (hf : Represents p mem flat) (hc : p.check = .ok ()) :
    Represents p (evalProgram p mem) (lowerProgram p flat)
```

The field theorem is universal over arbitrary, potentially noncanonical limbs:

```lean
theorem mul_sound (a b : Word) :
    (mul a b).val = goldilocksMulSpec a.val b.val
```

It composes exact 32-bit operations, 128-bit product assembly and
`goldilocksReduce128Spec_sound`, rather than assuming a carry or an intermediate
bound. `mul32_widen_limbs` identifies low/high extraction of the bounded widening
primitive with the proved extended-u32 multiplication.

The admitted protocol is translated into the existing Vulkan G4 model. Recovery
completed its whole-dispatch composition:

```lean
theorem checkProgram_not_racy (p : Program) (hc : p.check = .ok ()) (width : Nat)
    (hp : SourceProtocol.checkProgram p width = true)
    (d : Dispatch) (hd : d ∈ p.dispatches) (mem : Nat → ArrayKernel.Memory) :
    (dispatchTrace p d mem width).static.racy = false
```

`DispatchProtocol.checkProgram_not_racy` combines per-workgroup phase ordering
with checked cross-group device ownership and private shared storage.
`SourceProtocol.checkProgram_read_sequential` additionally proves that every ordinary read in a
well-formed Vulkan-consistent execution equals `phaseReadValue`: the latest
preceding phase's write, or initial zero. The writer is derived by the theorem;
no latest-write or happens-before certificate is a premise. The concrete protocol
checker performs finite access/ownership checks without evaluating field arithmetic
or enumerating possible Vulkan outcomes.

This visibility statement is about evaluator-labelled traces. It does not model
host uploads (G4 initializes locations to zero), enforce register instruction
semantics by itself, or certify textual WGSL/compiler translation. Those interfaces
must not be inferred from race freedom alone.

## Integration with the RTL square

Both emitters now share `SquareGraphs` and its vectors. The monadic builder and
field construction come from `ArrayBuild` and `GoldilocksSource`; the block NTT
constructor and mathematical reference implementations live in `Gpu.Ntt`.
`EmitGpu` contains IO and admission/reference checks. The obsolete per-layer
`nttGraph` is gone. The square uses `array-route` to retain constant, gather and
concatenation coverage on the same source graph through both devices; its old
NTT SystemVerilog artifacts are removed. The block NTT is not claimed to have
an RTL commuting-square theorem.

The square's array equality now composes with checked liveness allocation:

```lean
theorem rtl_eq_gpu_array (name : String) (g : ArrayGraph) (hwf : g.wf = true)
    (hLayout : layoutOk g = true) (ins regs : Nat → Word)
    (flat : Nat → Word) (hFlat : Flat g.lengths (gpuLayout g).base
      (liveAt (layerGraph (fuseGraph g)) g.outputs) (inputEnvOf g ins) flat) :
    (runProgram (lowerArrayToGpu g) flat).flatten =
      (evalModuleOutputs (compileArrayGraphToRtl name g) ins regs).map Prod.snd
```

The corresponding scalar statement carries the same checked-layout/live-entry
premises. The RTL soundness theorem itself still requires only graph well-formedness.

Fresh merged square checks passed all byte/model stages, the complete `array-route`
external gate (Yosys/z3, Verilator, device and planted faults), and `glmul-4`
Verilator simulation. The logs contain:

```text
LEC sq_array_route: unsat, bit-precise
mutation `out_w4_0 = 64'd1 ^ (w_16);`: sat
[4] Verilator: vectors=12, mismatches=0 against evalModuleOutputs
[6] swapped `w_11 = (w_3 - w_7);`: Verilator mismatches=24, LEC z3 says sat
[PASS] hardware/gpu/square (array-route)
[PASS] hardware/gpu/square (stage 4) (glmul-4)
```

This is scoped integration validation, not a fresh full-square run over every
external stage. EQY remains opt-in and was not run. The working hbox Verilator
v5.024 build and shim are documented in `hardware/README.md`.

## Measurements against a named baseline

Microseconds per transform. GPU device times use 3 warmups and 1,024 measured
transforms in a pre-recorded batch; immutable reset copies occur outside timestamp
intervals. CPU values are medians of 31 samples of **Plonky3 p3-dft 0.8.0**,
`Radix2DitParallel<Goldilocks>`, width one, on hbox's i9-12900. Both CPU configurations
are shown. The host and device were shared with another validation lane; these are measured
comparisons, not quiet-host best-performance claims. Fresh CPU measurements were
substantially faster than the predecessor's run; its ratios are superseded.

| Points | Dispatches | Ours median | Ours p90 | P3 1 thread median | P3 8 threads median | Faster measured CPU / ours |
|---:|---:|---:|---:|---:|---:|---:|
| 1,024 | 3 | 13.360 | 51.440 | 23.752 | 23.848 | 1.778× |
| 65,536 | 2 | 50.200 | 68.760 | 1,513.712 | 399.185 | 7.952× |
| 1,048,576 | 3 | 584.080 | 586.160 | 36,640.157 | 13,016.353 | 22.285× |

The ratios compare computation intervals. GPU host-batch amortized times are
77.897 / 128.176 / 680.985 µs; these include warmups, reset copies, query/output
copies and final mappings, but exclude command recording and pipeline creation.
They are neither per-sample medians nor application end-to-end latency.
The 1,024-point p90 is substantially above its median. Short intermediate batches
also ran slower; they are retained and labelled in the
[baseline evidence](../hardware/gpu/baseline/README.md).

VkFFT supports Vulkan/AMD but does not provide exact Goldilocks arithmetic, so a
floating-point FFT is not substituted as the baseline. The ec-gpu OpenCL candidate
could not run: direct `clGetPlatformIDs` returned -1001 and zero platforms, with no
installed ICD. Its field representation also needs the documented high-bit
precondition checked. The mandatory exact CPU baseline ran at all requested sizes.

## Resource model and gate

Every final timed NTT stage reports 64 VGPRs, 128 SGPRs, 4096 bytes LDS and zero
scratch. The model predicts eight wave64 waves/SIMD, matching RADV's normalized
16 subgroups/SIMD. Logical source global access totals are 92,160 / 6,029,312 /
136,314,880 bytes; these include repeated root-table reads and do not claim DRAM
traffic. Code sizes are 13,864 / 20,840 / 26,912 bytes across each transform's stages.

The planted resource change is a real shader: it preserves exact outputs while
raising LDS from 0 to 32,768 bytes. Predicted wave64 residency changes 16→1, while
RADV's normalized report changes 32→2. The gate also requires changed machine code
and exact output. Raw compiler dumps and grades are retained under
[`hardware/gpu/cost`](../hardware/gpu/cost/README.md). Allocation is observed from
the compiler; occupancy is predicted by the Mesa formula. Formal source resource
grading and a lax-monoidal G5 theorem remain open.

## Gate evidence and routing

Recovery fixed unbuilt proofs in `DispatchProtocol` and `GoldilocksSource`,
connected the shared builders to emission, and imported the dispatch proof from
the emitter so it cannot silently fall out of the named build.

Named Lean builds on hbox passed for the emitter, RDNA2 tool, layout/workgroup
checks, limb proofs and ZK application. Source admission regressions passed,
including inactive invalid literals, zero divisors and overflowing address sums.
Raw logs are in [`hardware/gpu/evidence`](../hardware/gpu/evidence/).
The separately run `Obend.Teeth.Hardware.Rdna2Runs` target fails its old pinned
ISA executions for the same missing instruction semantics (`resume-merged-isa-fixtures.log`);
it is not included among the successful targets and was not weakened.

The final merged `verify_gpu.sh` run passed and is recorded in
`resume-merged-verify.log`:

```text
addAsSub: caught
swapMux: caught
mulHighZero: caught
[PASS] hardware/gpu
```

The final NTT instruction streams and compiler resource statistics are identical
to the freshly timed version (`resume-merged-ntt-isa-identity.log`); only the generated
adapter header changed.
The first recovery attempt overlapped synchronization of dev's changed scalar
fixtures and was superseded by this clean merged run.
It regenerates the million-point source evaluation, checks committed SHA manifests,
runs exact device comparisons, plants add/sub, mux and high-product faults, then
extracts ISA. Benchmark correctness is a separate exact-output check, not a
replacement for this gate.

The full ISA gate ran stages 1–2; stages 3–6 were then run individually so the
decoder refusal did not hide later results:

| ISA stage | Result |
|---|---|
| 1, generated decoder data | PASS |
| 2, decoder vs LLVM | FAIL: signed branch text (`s_branch -15` vs LLVM `65521`) and unrendered DS format |
| 3, machine-code bit-flip teeth | PASS |
| 4, wave-model execution | FAIL: first `V_CMP_LT_U32` in adjoint-mul-add has no semantics |
| 5, gem5 instruction replay | PASS |
| 6, waitcnt analysis | FAIL: `DS_WRITE_B128` counters are not modelled |

Per-graph execution also refuses `S_MULK_I32` in field multiplication,
`S_ADD_U32` in the smallest NTT, and `V_MBCNT_LO_U32_B32` in the workgroup NTTs.
The full static mnemonic inventory absent from `Semantics.execInst` is
[`unsupported-isa.tsv`](../hardware/gpu/evidence/unsupported-isa.tsv), with graph
names. Shared-memory additions are `DS_READ_B64`, `DS_WRITE_B64`, `DS_WRITE_B128`;
lane IDs need `V_MBCNT_LO_U32_B32` and `V_MBCNT_HI_U32_B32`. Scalar loop/control,
32-bit compare/shift/subtract and SDWA variants also occur. The inventory is a
static coverage scan, not a claim that each instruction was independently executed.
The model lane must also handle barrier/shared visibility, not only decode opcodes.
No refusal was converted to a no-op and no ISA gate was relaxed.

## References and remaining scope

The workgroup argument follows [GPUVerify (Betts et al., OOPSLA 2012)](https://nchong.github.io/papers/oopsla12.pdf)
and [Faial (Cogumbreiro et al., CAV 2021)](https://cogumbreiro.github.io/assets/faial-cav21.pdf):
uniform barriers and ownership between synchronization points. Its actual memory
relations are the existing Dartagnan-checked G4 Vulkan model, not a new sequential
memory model. The NTT organization follows
[ec-gpu radix_fft](https://github.com/filecoin-project/ec-gpu/blob/master/ec-gpu-gen/src/cl/fft.cl)
and [Govindaraju et al., SC 2008](https://doi.org/10.1109/SC.2008.5213922).
[VkFFT](https://github.com/DTolm/VkFFT) and
[cuFFT's design documentation](https://docs.nvidia.com/cuda/cufft/) inform the
register/shared/global hierarchy, with no claim of equivalent field support.
Arithmetic and occupancy references are cited in their linked implementation notes.

Proved: compiler/refinement and protocol statements quoted above, universally over
their admitted language. Checked: generated bytes, source NTT against independent
mathematical implementations, device outputs, and planted faults. Measured:
timings and compiler allocations. The NTT constructor's equality to the mathematical
DFT is checked on emitted inputs, not universally proved. Textual WGSL and shader
compiler correctness remain an external gate boundary. Full G2 is blocked on the
ISA-model lane's extensions; full formal G5 is not claimed. The complete monadic
`glMul` builder-to-field theorem also remains open: the arithmetic schedule is
proved, while its construction/emission interfaces still rely on separate checks.
