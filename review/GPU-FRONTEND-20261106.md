# GPU frontend, 2026-11-06

This lane connects source programs and serialized catgrad models to the array GPU backend.
The source frontend, typing derivation, collective operations and catgrad importer are implemented.
The validation section distinguishes the proved compiler path, external checks and measured limits.

## Fragment and referents

The source separates scalar word expressions from collective array expressions, following
[Accelerate's `Exp`/`Acc` distinction](https://www.acceleratehs.org/documentation/users-guide/language.html).
Immutable lexical bindings compose maps, gathers, concatenations, literal arrays, reductions and
scans. Shapes are static for this fragment. There is no arbitrary recursion, dynamic allocation,
scatter with conflicting writes, or floating-point operator hidden behind an integer encoding.

[Futhark, PLDI 2017](https://elsman.com/pdf/pldi17.pdf), §§2–5, supplies the SOAC meaning and the
separation between mathematical operators, fusion, and flattening. Associative word monoids admit
exact reduction reassociation. Inclusive and exclusive scans are distinguished explicitly;
segment lengths retain empty segments. This is a restricted flat fragment, not Futhark's entire
nested-parallel language or its full fusion system.

[Lift, ICFP 2015](https://michel-steuwer.github.io/files/publications/2015/ICFP-2015.pdf) motivates
separating a pattern from its schedule. The initial fold backend assigns one invocation to each
segment and scans that segment sequentially, with linear work and parallelism across segments.
It has no parallelism within a single segment. This is not a substitute for the work-efficient
parallel up-sweep/down-sweep in [Blelloch's prefix-sums chapter](https://www.cs.cmu.edu/~guyb/papers/Ble93.pdf),
or a claim to reproduce [NESL's flattening and work/depth guarantees](https://www.cs.cmu.edu/~scandal/nesl.html).
The missing intra-segment parallel schedule remains engineering work.

[Dex's typed index sets](https://arxiv.org/html/2104.05372), §§2.1 and 3.3–3.4, motivate the compact
Core4 representation: an array is observed by applying its index function. Array source bindings
must retain sharing; expanding every element's complete arithmetic expression into Core4 would
undo the backend's efficient representation.

## Typing and arithmetic

`ArrayTyping.TensorType` records the full row-major shape and element interpretation. Pointwise
maps require equal shapes, so `[2,3]` and `[6]` are distinct even though both occupy six words.
Gather reindexing preserves elements and changes shape explicitly; its contravariant identity
and composition laws are `reindex_id` and `reindex_comp`.

`GraphTyping` exposes local shape, arity, element-signature and wire-scope premises, and global
single-assignment and definition-before-use premises. `GraphTyping.wf` derives the backend's
`ArrayGraph.wf`. `checkTypedGraph` returns the graph with its derivation; `TypedGraph.lower_sound`
consumes that proof. The checker additionally rejects reads from uninitialized scratch, which
legacy `ArrayGraph.wf` alone allowed. The static rejection checks are in
`Obend.Teeth.Hardware.ArrayTyping` and are examples, not workload correctness theorems.

The storage semantics is `BitVec 64`. Scalar Core4 addition, multiplication and subtraction encode
wrapping explicitly; plain unbounded natural arithmetic is not silently accepted. Shifts distinguish
Core4's masked counts from the array model's zero result for counts at least 64. The WGSL emitter
must test the complete unsigned count before returning a shifted value, including counts with
nonzero upper 32 bits.

`fixed q` is a binary-scale annotation on word storage. A product of scales `q` and `r` has scale
`q+r`; addition requires equal scales. There is no implicit rescaling, saturation or promise that
word overflow preserves an exact rational value. A no-overflow precondition is needed for that
interpretation. Predicate constants are restricted to zero or one. Floating point is refused.

## Catgrad boundary

See [the importer and oracle contract](../hardware/gpu/catgrad/README.md). The Rust oracle uses the
actual upstream `hidden.rs` example with explicit integer adaptations. The serializer exports its
original floating-point term, adapted source term, and concrete tensor specialization. Catgrad's
own interpreter compares the adapted source and specialization on identical inputs before the
Lean importer or GPU runs.

The importer is not a proved catgrad compiler. The universal GPU theorem starts at its typed
`ArrayGraph`. Equality to catgrad is checked externally, on the supplied vectors, with planted
faults. The distinction matters especially for future float support: exact IEEE operation semantics,
rounding and exceptional values, compiler permissions, reduction ordering, and a specification of
acceptable error must be supplied; replacing the word carrier by real numbers proves a different
program. The float papers and concrete remaining requirements are documented in the catgrad README.

## The composed theorem

The following statement is in `Obend.Hardware.Gpu.ArrayMember`; its namespace imports supply
`Program`, `Env`, `Good`, `Flat` and `Represents`. The `Plan` contains the closed composition,
lexical scope, exact selected-member syntax equality and graph typing derivation. Its checker
decides those premises, rather than requesting a semantic certificate for the desired result.

```lean
theorem Plan.source_to_gpu_encoded {C : Obend.Logic.Composition} {m : String} (p : Plan C m)
    (inputs : List Vec) (target : Env) (flat : Nat → Word)
    (count : p.inputLengths.length = inputs.length)
    (shape : ∀ i, lexicalLens p.inputLengths i = (inputValues inputs i).length)
    (boundary : Represents p.inputLengths.length (inputValues inputs) target)
    (good : Good p.graph.lengths target) (hflat : Flat p.graph.lengths target flat) :
    runProgram p.lower flat = p.program.eval (inputValues inputs) ∧
    ∀ output, output < (p.program.eval (inputValues inputs)).length → ∀ index,
      Halts (.app (nth (.app (.get C.object m) (encodeInputs inputs)) output) (.nat index))
        (.natural (((p.program.eval (inputValues inputs)).getD output []).getD index 0#64).toNat)
```

The first conjunct identifies GPU program semantics with source evaluation. The second identifies
every observed output element of the actual Core4 member with that same result, using `book_sound`.
The remaining hypotheses describe only input counts, shapes and buffer loading. This is a theorem
about the fragment, including segmented folds; it is not an NTT-instance theorem. The source arrays
are compact indexed functions, and lexical bindings preserve sharing. Executable graph evaluation
uses arrays and the proved cached-prefix fold implementation rather than the list-based reference.

The shape erasure theorem, in `Obend.Hardware.ArrayTyping`, is:

```lean
theorem GraphTyping.wf {types : List TensorType} {g : ArrayGraph}
    (h : GraphTyping types g) : g.wf = true
```

`ArrayPrograms` now constructs lexical field/NTT programs and actual composition members. The
emitter's previous graph-wire builder and hand-built field/NTT graphs were removed. The selected
source member is checked before its graph reaches emission. See [the source workflow](../hardware/gpu/SOURCE.md)
for the API and file-format boundary. The whole-array API currently requires the source syntax
witness; arbitrary Core4 SOAC recovery from a book file is not implemented.

## Validation and measured limits

The named hbox builds for the frontend, core fold proofs, typing and admission/refusal tests pass.
The large literal test exercises compact encoding and equality at the NTT's input scale. Actual
field emission is checked against exact natural multiplication modulo the Goldilocks prime; the
NTT emission is checked against recursive radix-2 arithmetic and, at smaller sizes, the naive DFT.
The Stockham schedule follows ec-gpu's radix-2 specialization; a throughput comparison against
ec-gpu's production implementation has not been run, so no competitive NTT performance is claimed.

`verify_source.sh` passed both the exported-book workflow and literal `Affine.obend` → ordinary
`obend emit` → GPU workflow on RADV. Normal source evaluation gives `7 → 26` and `2^64−1 → 2`;
the same inputs are included in the GPU vectors. An independent Python word oracle, shifts at and
beyond the word boundary, fixed-point numerators, named refusals, and actual wrong-value planted
shaders passed. The final catgrad replay passed artifact digests, its own interpreter,
both planted arithmetic/mux defects and operation/type/shape/linear-use refusals.

Measured baselines, with full timing scope and versions in the linked reports:

| Workload | RX 6750 XT / RADV, ms | CPU baseline, ms | Interpretation |
|---|---:|---:|---|
| Adapted upstream MLP forward pass | 3.107 | 0.421578, catgrad interpreter | GPU submission/completion is about 7.37× longer |
| SOAC full pipeline, 65,536-element single segment | 95.125 | 2.881, NumPy | about 33.0× longer |
| SOAC full pipeline, 64×1,024 segmentation | 19.224 | 3.060, NumPy | about 6.28× longer; pipeline also contains unsegmented operators |

These are measurements, not correctness theorems or gated performance claims. The GPU timings
exclude compilation and transfer; CPU timings include allocations and host dispatch. See
[SOAC results](../hardware/gpu/SOAC.md) and [catgrad results](../hardware/gpu/catgrad/README.md).
These figures replace the predecessor's draft measurements and come from recovery runs.
The catgrad CPU timer includes source-term cloning and lang-to-core lowering on every pass;
the GPU timer excludes compilation. The host was shared with other work. These differing scopes
and shared-host conditions preclude treating the ratios as stable speedup bounds.
The catgrad log is [`recovery-radv-20261106.txt`](../hardware/gpu/catgrad/results/recovery-radv-20261106.txt).
An added interpreter-generated probe also checks U32 predicate values consumed by arithmetic,
nonzero U32 mux conditions and wrapping Add/Sub/Mul, with both shader faults caught.

`verify_gpu.sh` stages 1–4 passed: final artifacts reproduce, device outputs agree, both shader
mutations cause wrong values, and final RDNA2 assembly is extracted. Its retained output is
[`frontend-gpu-gate.log`](../hardware/gpu/frontend-gpu-gate.log). The source gate's output is
[`source-gate.log`](../hardware/gpu/source-gate.log).

Final integration still running: ISA stages 1–6 with the new segmented-loop instructions and
PC-relative constant pools. Its final log must be attached before this lane is described as passing G2.

Open engineering work: work-efficient parallel intra-segment schedules; a production ec-gpu
throughput comparison; broader source syntax recovery; a proof for catgrad specialization/import;
fixed-point rescaling and a no-overflow rational interpretation; and a specified floating-point
backend. The new source/GPU theorem and shape discipline do not imply those additional results.
