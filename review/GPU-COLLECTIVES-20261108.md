# GPU collectives, block sources and NTT value proofs, 2026-11-08

All three requested gaps are closed: work-efficient segmented collectives, a
general Core4 block-source path for the sole NTT, and a universal theorem that
the actual NTT source is the Goldilocks DFT. Branch `lane-gpu-collectives` starts
at integrated `d021939`. All builds and device runs use hbox under `swarm-build`;
no sibling worktree or Rdna2 model is changed.

## Fragment and referents

The lexical typed fragment and `ArrayMember.Plan.source_to_gpu_encoded` remain
the ordinary frontend. Every reduce/scan now goes through one admitted
`ArrayKernel` schedule: ordered compact Blelloch trees in LDS and a hierarchical
reduce-then-scan between workgroups. Static segment descriptors preserve empty
segments. Short segments finish at their current level; only long segments
enter the next summary level. This pruning is necessary for linear work with
mixed short and long segments. The GPU has no retained sequential scan path.

The design follows CUB's shared/register block decomposition, Merrill and
Garland's distinction between roughly 3N-transfer hierarchical scan and
2N-transfer decoupled look-back, and Sengupta's segmented scan semantics.
Current Thrust CUDA delegates scan to CUB. The block language currently has
ordered dispatches, shared phases and barriers, but no inter-workgroup atomic
publication or fallback protocol. The choice of a hierarchy is a limitation of
this language, not a claim that portable single-pass scan is impossible:
Smith, Levien and Owens' 2025 decoupled fallback explicitly addresses that case.
Primary sources and the WGSL memory boundary are collected in
[the collective design notes](../hardware/gpu/collectives/README.md).

For the NTT, `ArrayKernel` is now the block-level source fragment of Core4.
`BlockCoreProgram` interprets real group/lane index expressions, immutable
phase snapshots, lexical register code and bounded maps as Core4 terms. It does
not construct a Core4 term from evaluated answers. This reuses the existing AST;
there is no second NTT source language or transform-specific Core primitive.
[Lift's low-level primitives](https://lift-project.readthedocs.io/en/latest/lift-overview/)
(`mapWrg`/`mapLcl`, `toLocal`/`toGlobal`/`toPrivate`, and symbolic split/join views),
together with [Futhark's intra-group parallelism](https://futhark-lang.org/publications/ppopp19.pdf),
motivate this interface.
The sole NTT emitter calls `NttSource.compile` and the general checked block plan.

## Typing and arithmetic

Ordinary source typing, live layout checks and source reification remain.
Collective source admission checks the actual descriptor addresses and phase
ownership; the existing G4 model checks the actual physical workgroup protocol.
The array action scheduler also checks live arena boundaries and cross-kernel
read/write separation before composing map and collective actions.

`GoldilocksSource` remains the sole arithmetic construction for both ordinary
field programs and block registers. Its multiply was factored at the existing
wide-product/reduction boundary, preserving the original instructions by the
`glMul_expansion` definitional-equality theorem. The actual builder now has
universal canon/add/sub/multiply contracts. Multiplication accepts arbitrary
64-bit operands and returns a canonical residue. Two inherited native mask/pack
proof steps were replaced at their `LimbsShift` source with kernel bitvector
lemmas; the public arithmetic axiom audit contains only `propext`,
`Classical.choice` and `Quot.sound`.

```lean
theorem glMul_sound (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glMul n k a b).run st
    (evalBuild out.2 env out.1).toNat < goldilocksPrime ∧
      (evalBuild out.2 env out.1).toNat =
        ((evalBuild st env a).toNat*(evalBuild st env b).toNat) % goldilocksPrime
```
## The composed theorems

The collective theorem quantifies over every input and every successful
source construction/admission, for all four associative word monoids in the
fragment: modular add/multiply and bitwise AND/OR. Operand order is preserved;
commutativity is not used by the tree argument. Empty reductions use the identity.

```lean
theorem build_initialMemory_value (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) (hcheck : p.check = .ok ())
    (input : Array Word) (hsize : input.size = shape.inputLen) :
    (List.range shape.outLen).map (valueAt (evalProgram p (initialMemory p [input])) 1) =
      evalFold op shape (fun i => input.getD i (0#64))
```
The work bound counts lane reads, register-code instructions and writes in the
actual constructed source program. It excludes index-expression evaluation,
metadata/admission costs, dispatch overhead and expansion into machine
instructions; it is not a hardware instruction-count or elapsed-time bound.

```lean
theorem build_work (op : ReduceOp) (shape : FoldShape) (depth : Nat) (p : Program)
    (hbuild : build op shape depth = .ok p) :
    programWork p ≤ match shape.mode with
      | none => 36*(shape.inputLen+shape.segments.length)
      | some _ => 114*shape.inputLen
```
The ordinary array consumer composes those scheduled actions with the existing GPU value semantics:

```lean
theorem compile_runProgram (p : GpuProgram) (compiled : Schedule)
    (hc : compile p = .ok compiled) (flat : BlockLower.FlatMemory) :
    compiledOutputs p compiled flat = runProgram p (fun a => flat (.device,a))
```
The block fragment has the corresponding encoded-input Core4 result:

```lean
theorem Plan.source_to_gpu_encoded (p : Plan) (mem : Memory) (flat : FlatMemory)
    (hg : BlockLower.Good p.source mem) (hf : Represents p.source mem flat)
    (array index : Nat) (hv : Valid p.source array index) :
    Steps (observe p.term (BlockCoreEncoding.memory mem) array index)
      (.nat ((lowerProgram p.source flat) (address p.source array index)).toNat)
```
`Plan.not_racy` uses the same source protocol receipt. These are source/Core4
and flat GPU semantic theorems. They do not prove the WGSL text emitter, Vulkan
driver or physical device; the external gates exercise those boundaries.

The NTT proof includes a kernel-checked primitive-root certificate, exact root
order for every power-of-two size through 2^32, DIF/DFT factorization, Stockham
indexing, the actual linear-time twiddle table, and radix-4/final-radix-2
register networks. It follows the actual register loads and instructions,
shared phases, packed workgroups and dispatch stores; group-frame proofs keep
other tiles intact. These compose into equality at the program's declared
output port, for arbitrary 64-bit input words, including noncanonical residues.

`NttSource.Supported n` means exactly `n = 2^bits` with `1 ≤ bits ≤ 25`.
The source theorem has no admission, computed-answer or finite-certificate premise:

```lean
theorem nttBlockProgram_dft (n : Nat) (hn : NttSource.Supported n)
    (input : Array Word) (hinput : input.size = n) (i : Nat) (hi : i < n) :
    (valueAt (evalProgram (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i).toNat =
      dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i
```

The same result composes with the actual encoded Core4 source and general GPU
lowering:

```lean
theorem source_to_gpu_dft_encoded (n : Nat) (plan : BlockPlan.Plan) (hc : compile n = .ok plan)
    (input : Array Word) (hinput : input.size = n) (flat : FlatMemory)
    (hf : Represents (nttBlockProgram n) (initialMemory (nttBlockProgram n) [input]) flat)
    (i : Nat) (hi : i < n) :
    let value := dft n (rootOfUnity n) (fun j => (input.getD j 0#64).toNat) i
    Steps (BlockPlan.observe (program n)
      (BlockCoreEncoding.memory (initialMemory (nttBlockProgram n) [input]))
      ((nttBlockProgram n).outputs.getD 0 0) i) (.nat value) ∧
    ((lowerProgram (nttBlockProgram n) flat)
      (address (nttBlockProgram n) ((nttBlockProgram n).outputs.getD 0 0) i)).toNat = value
```

The composed theorem explicitly requires successful source admission and a
flat memory representing the encoded input. Admission completeness for every
supported size is not proved; actual emission still runs all checks. The
source DFT theorem itself covers every supported size without that premise.
The final public axiom audit for these results, the field builder, the generic
block source/race-freedom result and the collective value/work/action theorems
contains only `propext`, `Classical.choice` and `Quot.sound` (the work bound
needs only `propext` and `Quot.sound`). The emitter imports `NttCorrect`; the
finite direct-DFT checks and their naive evaluator have been removed.

## Validation and measured limits

The named convergence Lean build passed 902 jobs, including both emitters,
`obend`, `obend-rdna2`, the previously named source/square/layout targets, the
collective value/work/action proofs, and the new block-source/NTT algebra modules.
The final proof/emitter build passed 814 jobs, including `NttCorrect` and both
emitters. Fresh `tests/gpu/ArrayKernelCheck.lean` admission/refusal checks passed.
The complete artifact/device gates also passed on the rebuilt source emitter,
with identical registered artifacts. The collective checkpoint and source
convergence both passed `verify_gpu.sh` (all positives and three real wrong-answer
mutations), `verify_source.sh`, SOAC/NumPy, catgrad
replay, and both `soac-boundaries` and `array-route` square gates. After the final
proof import and finite-DFT removal, `verify_gpu.sh --stage 1` regenerated all
29 registered graphs again: every plan, shader and expected-output artifact
remains byte-identical. All 78 changed Lean files match the sources built on
hbox. No device algorithm changed after the full source-convergence gate run.

The catgrad replay preserved the independent interpreter's expected words.
Its new parallel fold plan changes 10 stages to 12 and 639,896 live words to
476,996; the digest was refreshed only after the candidate and official full
gates passed, including both plants and named refusals. The source-convergence
run records a 1.676 ms mean GPU runner interval over four vectors versus
0.496906 ms per adapted-interpreter forward pass. The latter includes source
clone, lang-to-core lowering, shape evaluation, loads, scheduling and evaluation,
excluding input-tensor construction. The GPU interval includes command encoding,
submission and completion, and may include the queued input upload; compilation
and output readback are outside. This is a small replay on a shared host, not a
sustained throughput or competitive neural-network benchmark.

Primitive timings below are medians in **microseconds**, uint64 add, on
RX 6750 XT / RADV Mesa 24.2.8 and i9-12900 / NumPy 2.5.4. GPU timestamps span
all dispatches and barriers; reset copies, compilation, transfers and readback
are outside. NumPy uses warm inputs and preallocated output, including Python
dispatch. Both have 3 warmups and 31 samples. The host is shared, with no
exclusive-load claim. Every measured final output is exact. A further 72 cases
(144 vectors) cover all four monoids, inclusive/exclusive/reduce, irregular and
empty segments, and mixed short/long pruning. All 18 measured source cases
regenerated identically (61 plan/shader files) with the final pruned emitter.

| Elements | Layout | Operation | Dispatches | GPU µs | NumPy µs |
|---:|---|---|---:|---:|---:|
| 65,536 | one segment | inclusive | 3 | 78.84 | 101.314 |
| 65,536 | one segment | exclusive | 3 | 78.64 | 402.812 |
| 65,536 | one segment | reduce | 2 | 44.96 | 6.575 |
| 65,536 | length 32 segments | inclusive | 1 | 68.20 | 115.831 |
| 65,536 | length 32 segments | exclusive | 1 | 68.24 | 143.185 |
| 65,536 | length 32 segments | reduce | 1 | 48.28 | 33.564 |
| 1,048,576 | one segment | inclusive | 5 | 122.36 | 1875.226 |
| 1,048,576 | one segment | exclusive | 5 | 120.68 | 1514.050 |
| 1,048,576 | one segment | reduce | 3 | 183.24 | 121.305 |
| 1,048,576 | length 32 segments | inclusive | 1 | 240.56 | 2075.765 |
| 1,048,576 | length 32 segments | exclusive | 1 | 242.88 | 1885.872 |
| 1,048,576 | length 32 segments | reduce | 1 | 175.92 | 488.521 |
| 16,777,216 | one segment | inclusive | 5 | 1606.00 | 25957.919 |
| 16,777,216 | one segment | exclusive | 5 | 1603.56 | 26091.876 |
| 16,777,216 | one segment | reduce | 3 | 652.52 | 4970.378 |
| 16,777,216 | length 32 segments | inclusive | 1 | 3344.40 | 30241.424 |
| 16,777,216 | length 32 segments | exclusive | 1 | 3335.04 | 35001.343 |
| 16,777,216 | length 32 segments | reduce | 1 | 2657.12 | 11763.579 |

The same-run handwritten WGSL device-copy baseline is 4.72 / 50.76 / 774.52 µs
at the three sizes; it uses the same runner and adapter, but is not a source
compiler correctness result.
At 2^24, single-segment scan is about 48% of copy's input-word throughput;
length-32 segmented scan is about 23%. Small reductions remain slower than
NumPy, including the measured 2^20 single reduction. No favorable subset is
substituted for the complete matrix.

The published CUB reference is [Merrill and Garland's 2016 paper, figures 7–9](https://research.nvidia.com/sites/default/files/pubs/2016-03_Single-pass-Parallel-Prefix/nvr-2016-002.pdf), showing CUB 1.5.2 saturated
32-bit scan: roughly 30.8 billion items/s on M40, 26.7 on K40 and 14.4 on C2050,
with ECC off. Those correspond to minimal read+write traffic of approximately
246 / 214 / 115 GB/s and a near-copy throughput class. Those byte rates are
derived minimum traffic, not measured memory traffic. The paper does not specify
a timer, warmup or sample-count protocol. These are historical NVIDIA 32-bit
prefix-sum results, not a measured same-card u64 or short-segment baseline.
The same-card copy gap above is the direct normalized comparison available here.
The long-segment hierarchy rereads input and incurs extra dispatches; it does
not match CUB's single-pass traffic class. Length-32 segments fit in one local
phase sequence and already read and write each input/output word once.

The user's 93 ms baseline was the **whole SOAC pipeline**, not one scan.
The matching source-convergence pipeline takes 9.566 ms GPU versus 2.218559 ms
NumPy for one 65,536-element segment, and 9.719 ms versus 2.135112 ms for 64×1,024.
Both have 66 dispatches. Compared with the recorded preceding GPU baselines
93.031 / 19.025 ms, measured with the same runner timing code, these are
9.73× / 1.96× shorter; the new GPU pipeline still
trails NumPy by 4.31× / 4.55×. These GPU figures are means over two fixture
vectors, including command encoding, submission and completion, and potentially
the queued input upload; compilation and output readback are outside. NumPy's
101-sample median follows 10 warmups and includes allocations and Python
dispatch. The primitive 79 µs scan has a different measurement scope from that
93 ms pipeline baseline.

Admission remains costly: the recorded 2^24 single inclusive-add scan spent
73.767 seconds in source checks and 524.478 seconds total including exact G4
trace checking (about 8.7 minutes). The [retained admission log](../hardware/gpu/collectives/results/admission-single-24-add-inclusive.log) identifies the five-dispatch,
33,686,016-device-word program. These admission costs are outside the device
timing table. The checks were retained; compact symbolic admission is still
open performance work.

Fresh ISA stages 1/3/5 pass. Stage 2 fails on DS_WRITE_B128/B64 rendering,
stage 4 on missing V_CMP_LT_U32 semantics, and stage 6 on DS_WRITE_B128 counter
modeling. A fresh `Obend/Teeth/Hardware/Rdna2Runs.lean` run also fails its pinned
`checkGraph` checks; a cached build is not reported as passing that gate. The
separate ISA lane owns that work. No Rdna2 file was changed.

## Replacement and integration

Purged the sequential fold WGSL emitter and its obsolete invocation-schedule
claim. All ordinary/book/catgrad fold consumers use the admitted block hierarchy.
Purged the first hierarchy's repeated propagation of finished short segments.
The sole NTT construction remains; only its static builder loops were made
explicit for proofs, retaining balanced uploads, register radix-4 arithmetic,
shared phases, packing and live device buffers. Its source/Core4 path is now
connected through the general block counterpart and its value theorem is the
universal DFT result. Removed the finite direct-DFT evaluator and checks. The
independent O(N log N) recursive CPU NTT remains a regression oracle for emitted
fixtures, not a second GPU construction.

## Open work

Single-pass atomic look-back/fallback, faster compact admission, better short-
segment packing and lower full-pipeline dispatch overhead remain performance
gaps. The checked frontend supports four associative word monoids; it does not
provide arbitrary user-defined monoids. Admission completeness over the entire
supported NTT size domain remains unproved; per-program admission stays checked.
The ISA model gaps are owned by its lane. No RTL square theorem for block NTT,
WGSL text-emitter theorem, arbitrary floating-point monoid, or general catgrad
compiler theorem is claimed.

## Commits and evidence

- `577ff4c`, `39360fc`, `5a35af6`, `5ca4bbc`: checked collective construction,
  segmented values, consumer integration and actual linear work bound.
- `cf7e6fd`: general block-source Core4 composition.
- `09261c6`: exact device/baseline evidence and refreshed consumers.
- `75b70b0`: universal shared field builder bridge and kernel-only projection proofs.
- `1ec6afb`: sole NTT through the block-source plan and universal transform algebra.
- `721daa7`: actual phase/group/dispatch execution equals the DFT universally,
  composed with Core4/GPU; finite direct-DFT evaluator and checks purged.
- `7a343a4`: final convergence evidence, closed theorem audits, and corrected
  full-pipeline timing scope.

Raw measurements, artifact revalidation and checkpoint gates are under
[`hardware/gpu/collectives/results`](../hardware/gpu/collectives/results).
Full new logs live in `/home/hbox/obend/frontend-collectives/` and field proof
logs in `/home/hbox/obend/frontend-field/`. The retained `proofs/FinalAxioms.lean`
reproduces the final public audit; `source-convergence/status.json` records each
full regression command and its status.
