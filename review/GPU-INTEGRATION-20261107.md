# GPU frontend/kernel integration, 2026-11-07

Integration of `gpu-integrate` (`9de8eea`, including kernels `74a5ac8` and dev `bdb267d`)
into `lane-gpu-frontend` at `d4ddd55`. All new commits belong to the frontend branch.
The earlier frontend and kernel reports are historical evidence, not this run's results.

## Fragment and referents

The lexical fragment retains immutable bindings, static shapes, pointwise word maps,
gathers, concatenation, literals, reductions and inclusive/exclusive segmented scans.
It retains the Accelerate/Futhark/Lift distinction between source operators and schedules
recorded in [the frontend report](GPU-FRONTEND-20261106.md). Its current fold schedule
is linear within a segment; integration does not add parallelism within a long segment.

The only NTT construction is `Gpu.Ntt.nttBlockProgram`, the kernels lane's register
radix-4 Stockham construction in the general `ArrayKernel` language. Its ec-gpu and
Govindaraju design references, workgroup ownership checks and G4 phase checks are
retained. The recursive NTT and direct DFT are independent reference evaluators, not
alternative emitted NTT builders.

The lexical fragment cannot yet express group/lane-indexed multi-output register
networks with workgroup-local buffers and uniform barrier-separated phases. Arithmetic
expressions alone are insufficient to express that execution structure. Block NTTs
therefore use `ArrayKernel` admission and lowering, not the lexical encoded-source
theorem. There is no retained per-layer frontend NTT alongside them.

## Typing and arithmetic

`GoldilocksSource` and `ArrayBuild` are the sole field construction used by both ordinary
field programs and block kernels. `ArrayPrograms.glMulSource` reifies that shared
construction into lexical source. `ArrayReify.reify` checks scope, fresh destinations,
primitive operations and exact round-trip graph equality, normalizing only diagnostic
`opIdx` labels. It checks lengths, boundary wires and all operation/source/destination
structure; it does not decide a sampled semantic equation. `Reified.eval_sound` proves
accepted reification preserves the shared graph's denotation for every represented input.
Admission failure is returned, with no direct-graph fallback.

That lexical source becomes an actual closed Core4 member through the existing
`ArrayMember.checkMember`. `TypedGraph` and `Plan` now retain the executable `layoutOk`
receipt as well as the shape/element derivation. The untrusted last-use allocator may
reuse dead storage or a map's final input; the checked layout proves live-value
preservation and excludes cross-invocation read/write aliases. Fold invocations are
not eligible for map-only in-place reuse.

Map and fold shaders now share `vec2<u32>` arithmetic. The limb carry, multiplication,
shift and Goldilocks reduction theorems remain. Bounded 32×32 widening still uses
Naga/wgpu's `SHADER_INT64` extension; this is not standard-u32-only WGSL. The full
monadic `GoldilocksSource.glMul` builder-to-field theorem remains open, as does a
universal theorem equating the NTT construction with the DFT. Exact modular field
checks and independent NTT/DFT checks remain external finite checks.

## Catgrad boundary

The integer-adapted external catgrad MLP still imports through the typed array path,
uses the shared live layout and limb emitter, and is checked against catgrad's own
interpreter. Its theorem begins at the admitted typed graph, not arbitrary catgrad
semantics. Float support, upstream neural-network accuracy, and a general catgrad
compiler correctness theorem are not claimed. Its add/sub and mux mutations remain;
the global field/NTT gate checks the high-product-limb mutation that U32 masking can hide.

## The composed theorem

`ArrayMember.Plan.source_to_gpu_encoded` remains the frontend result. For an accepted
plan `p`, ordinary word arrays `inputs`, a source/graph boundary representation, correct
shapes and a good graph environment, its buffer premise is now:

```lean
Flat p.graph.lengths (gpuLayout p.graph).base
  (liveAt (layerGraph (fuseGraph p.graph)) p.graph.outputs) target flat
```

The exact declaration (with its namespace opens from `ArrayMember.lean`) is:

```lean
theorem Plan.source_to_gpu_encoded {C : Obend.Logic.Composition} {m : String} (p : Plan C m)
    (inputs : List Vec) (target : Env) (flat : Nat → Word)
    (count : p.inputLengths.length = inputs.length)
    (shape : ∀ i, lexicalLens p.inputLengths i = (inputValues inputs i).length)
    (boundary : Represents p.inputLengths.length (inputValues inputs) target)
    (good : Good p.graph.lengths target)
    (hflat : Flat p.graph.lengths (gpuLayout p.graph).base
      (liveAt (layerGraph (fuseGraph p.graph)) p.graph.outputs) target flat) :
    runProgram p.lower flat = p.program.eval (inputValues inputs) ∧
    ∀ output, output < (p.program.eval (inputValues inputs)).length → ∀ index,
      Halts (.app (nth (.app (.get C.object m) (encodeInputs inputs)) output) (.nat index))
        (.natural (((p.program.eval (inputValues inputs)).getD output []).getD index 0#64).toNat)
```

The conclusion remains `runProgram p.lower flat = p.program.eval (inputValues inputs)`
and Core4 halting observations of every source output element with the same word.
`Plan` carries checked typing and layout proofs; callers do not supply an output
correctness certificate. The composition retains `book_sound`, source term semantics,
source compilation, typing-derived graph validity, and general GPU lowering.

`BlockLower.checkedProgram_sound` separately proves that an accepted block program's
flat-memory target represents its source evaluation, for every good represented input.
`DispatchProtocol.checkProgram_not_racy` and `SourceProtocol.checkProgram_read_sequential`
retain the phase race/visibility statements. Their existing host-initialization and
evaluator-labelled-trace boundaries remain. Neither lowering theorem proves the WGSL
text emitter or Vulkan implementation; those are exercised by the external gates.

The square consumes the same admitted ordinary graph on both legs. `rtl_eq_gpu_array`
now requires graph validity, checked layout, and the live-entry buffer relation.
`array-route` covers routing/constants/shared producers; `soac-boundaries` retains
fold coverage. Block NTT has no array-RTL square theorem.

## Validation and measured limits

All runs use `/home/hbox/obend/frontend` under `swarm-build`. The named build passed:

```sh
swarm-build lake build obend-emit-gpu obend-emit-sv obend obend-rdna2 \
  Obend.Apps.ZkNtt Obend.Hardware.Gpu.LimbsGoldilocks \
  Obend.Hardware.Gpu.LimbsShift Obend.Hardware.Gpu.DispatchProtocol \
  Obend.Hardware.Square Obend.Teeth.Hardware.GpuLayout \
  Obend.Teeth.Hardware.Workgroup Obend.Teeth.Hardware.ArrayTyping \
  Obend.Teeth.Hardware.GpuArrayMember Obend.Teeth.Hardware.GpuArrayEncoding \
  Obend.Teeth.Hardware.GpuSourcePrograms
```

The block admission/refusal file passed via
`swarm-build lake env lean tests/gpu/ArrayKernelCheck.lean`. Both emitters regenerated
all registered GPU artifacts and square SystemVerilog/LEC artifacts; catgrad hashes
were refreshed through the merged emitter. A private-helper module visibility error
was fixed before the successful build. The SOAC gate's obsolete mismatch diagnostic
was fixed after its planted execution produced real wrong outputs; the rerun passed.

| Gate | Fresh result |
|---|---|
| `verify_source.sh --adapter radv` | PASS: exported book and ordinary surface-source workflow, independent word oracle, named refusals and wrong-answer mutations |
| catgrad replay | PASS: pinned upstream interpreter, refreshed hashes, exact MLP/scalar values, both mutations and named refusals |
| `verify_soac.sh` with NumPy | PASS: regenerated artifacts, device values, independent NumPy pipeline, concrete planted mismatch |
| full `square/verify_square.sh` | PASS: includes array-route, field and SOAC; bytes, HDL/array agreement, LEC, Verilator, card and real faults; EQY remains opt-in and was not run |
| resource-pressure gate | PASS: actual compiled LDS grows from 0 to 32768 bytes, normalized Mesa waves/SIMD falls from 16 to 1, both exact vectors pass |
| batch-reset gate | PASS: reset-sensitive final output and sample/stage/dispatch/memory bounds |
| `verify_gpu.sh` | PASS: regenerated bytes/digests, every device result, all three actual wrong-answer mutations, fresh RADV ISA extraction |
| `isa_check.sh`, stages 1 / 3 / 5 | PASS: generated modules, decoding bit flips, gem5 replay |
| stage 2 | FAIL on ntt-1024: `DS_WRITE_B128` and `DS_WRITE_B64` are unrendered against LLVM |
| stage 4 | FAIL on adjoint-mul-add, vector 0 / stage 0 / pc 24: `V_CMP_LT_U32` has no semantics; later execution and store mutations are not reached |
| stage 6 | FAIL on ntt-1024, stage 0 / dword 26: `DS_WRITE_B128` counters are not modeled; wait-removal mutations are not reached |
| fresh `Rdna2Runs.lean` elaboration | FAIL: pinned `checkGraph = true` equations evaluate false; no claims or checks were weakened |

The ISA stages ran separately so the decoder failure did not hide execution or wait
analysis. `lake build Obend.Teeth.Hardware.Rdna2Runs` returned a cached success even
though its `include_str` artifacts had changed. That is not fresh validation. Direct
`swarm-build lake env lean Obend/Teeth/Hardware/Rdna2Runs.lean` re-elaboration fails on
the new dumps; both outputs are retained. The model lane still owns the missing ISA
semantics. The model directory is byte-for-byte unchanged from `d4ddd55`.

Fresh sustained NTT measurements on RX 6750 XT / RADV Mesa 24.2.8, in **microseconds
per transform**. Device columns are timestamps around dispatches; host is amortized
batch wall time. Three warmups precede 1024 measured transforms, each restored from
the original input; the reset copy is outside the device interval. Correctness vectors
and the final batch output match. Plonky3 is the pinned `p3-dft 0.8.0`
`Radix2DitParallel<Goldilocks>` baseline, median of 31 warm samples, natural-order output,
cloning outside the timer and API allocation/conversion inside.

| N | dispatches | GPU median | GPU p10–p90 | host batch | CPU 1 thread median | CPU 8 threads median |
|---:|---:|---:|---:|---:|---:|---:|
| 1024 | 3 | 13.360 | 12.160–15.400 | 76.962 | 39.759 | 23.661 |
| 65536 | 2 | 50.200 | 48.840–70.040 | 130.380 | 2147.830 | 502.095 |
| 1048576 | 3 | 584.280 | 582.760–586.360 | 681.933 | 34657.178 | 9553.214 |

CPU and GPU runs were on the shared hbox, with no exclusive-host claim; this lane's
source evaluation was running during measurement. Observed host load at GPU measurement
was 5.44 / 4.92 / 4.91. Device compute and host/API timings have different scopes and
are not an end-to-end GPU speedup claim. The efficient block schedule survives integration.

The remaining frontend performance limit is visible in fresh results: the single
65536-element segment takes **93.031 ms** on the GPU versus **2.413 ms** for NumPy's
full pipeline; 64 segments of 1024 take **19.025 ms** versus **2.168 ms**. NumPy 2.5.4
uses a median of 101 warm repetitions including allocation and Python dispatch; GPU
numbers run from submission to completion, excluding shader compilation and transfers.
The integer catgrad MLP takes **2.145 ms** per GPU vector versus **0.166220 ms** for the
adapted upstream interpreter's forward pass (clone/lowering/shape/scheduling/evaluation
included, input construction excluded). Neither is a competitive neural-network claim.

## Replacement and integration

Removed the frontend's duplicate Goldilocks builder and complete per-layer NTT builder.
The shared registry selects ordinary typed sources or the sole block NTT lazily; both
emitters share ordinary graph selection and vectors. All three GPU mutations require
actual wrong outputs. ISA extraction retains limb stores, repeated instructions and
embedded constant-pool offsets. The missing-wait detector now also recognizes DS,
global and flat loads. No file under `lean/Obend/Hardware/Gpu/Rdna2/` was changed.

The primary hardware/source docs describe the merged boundary. The old frontend
report is explicitly marked historical. The integration does not claim the lexical
fragment produces the efficient block NTT; adding its missing workgroup constructs
and a corresponding Core4/source theorem remains work, rather than retaining two NTTs.

## Commits

`5a1ea56` — merge typed array sources with shared field and block GPU kernels.

The follow-up commit, “Record merged GPU artifacts and integration gates”, contains the fresh ISA, raw evidence and this report.

## Final gate output

```text
PASS named Lean build and ArrayKernel admission/refusal file
PASS hardware/gpu
PASS source book GPU gate
PASS catgrad MLP gate
PASS SOAC arrays: artifacts, independent expected values, device, wrong-answer tooth
PASS hardware/gpu/square (full registry, including array-route)
PASS resource-pressure and batch-reset gates
PASS ISA stages 1, 3, 5
FAIL ISA stage 2: unrendered DS writes
FAIL ISA stage 4: V_CMP_LT_U32 has no semantics
FAIL ISA stage 6: DS_WRITE_B128 counters not modeled
FAIL fresh Rdna2Runs elaboration: pinned checkGraph equations are false
```

Committed raw gate/timing evidence is in [`gpu-integration-20261107/`](gpu-integration-20261107/).
Full build logs and regenerated large artifacts live under
`/home/hbox/obend/frontend-integration/`; no sibling worktree was used or modified.
