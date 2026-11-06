# Catgrad OpenHypergraph → ArrayGraph → GPU

`verify_catgrad.sh` regenerates `mlp.json` using the actual Rust catgrad interpreter,
imports it in Lean, compares the independent outputs before emission, checks the
committed shader/plan/vector digests in `SHA256SUMS`, then runs the WGSL on a selected GPU. Both `addAsSub` and `swapMux` must cause value disagreements;
a runner startup failure does not count. Unknown operations (`Tensor.Map.Exp`), F32,
a corrupted interpreter result, an incompatible shape with the same storage size,
and a repeated linear read must be refused before a plan is written.

```
CATGRAD=$HOME/hellas/catgrad OPEN_HYPERGRAPHS=$HOME/hellas/open-hypergraphs \
  hardware/gpu/catgrad/verify_catgrad.sh --adapter radv
```

`EMIT`, `RUN`, `CATGRAD_ORACLE_BUILD` (persistent Rust build directory), and
`CATGRAD_GATE_OUT` can select existing executables and retained run directories.
The gate compiles Rust only; build `obend-emit-gpu` on the designated Lean host first.
The fixture is deterministic, timings are printed independently and never gated.
The generated source adaptation asserts that exactly two Sigmoid calls exist.
The original example remains available in the serialized provenance. The importer
refuses F32 input types rather than coercing them to words.

## The example and its lineage

The workload is **`catgrad/examples/hidden.rs::SimpleMNISTModel`**, the upstream
MNIST example: batch 2, input 28×28, flatten to 784, dense 784→100, activation,
dense 100→10, activation. The example itself uses demonstration parameters, not
trained weights. The gate compiles that actual upstream Rust source using
`include!`; it does not replace its model definition with a similar graph.

The integer-first adaptation is explicit: its F32 type annotations become U32,
and its two `nn::Sigmoid.call` expressions become `min(x,600)` (clipped ReLU on
U32). Integer test parameters replace its float demonstration parameters. This
**does not claim to implement the original floating sigmoid model**. Four vectors
cover zero, sparse positive weights, a second positive pattern, and U32 overflow.
The overflow vector makes both `MAX_U32 + 2` and `MAX_U32 * MAX_U32` produce 1
before activation, so clipping cannot hide a missing U32 mask.

The oracle executes the adapted upstream term through
`Interpreter<NdArrayBackend>::run`, including its actual shape computation,
parameter loads and both layers. `mlp.json` retains the original floating
`originalFloatTerm` and adapted `sourceTerm`. For the GPU importer, the exporter
specializes the known input reshape and parameter loads into explicit tensor
boundaries in `term`; cap tensors are explicit inputs. It separately runs that
specialized core term through catgrad's own `Interpreter::eval` and requires it
to match the upstream example on every vector before serializing.

The serialized `term` uses catgrad/open-hypergraphs' own serde derives. The Lean
importer performs independent shape inference and compares its evaluator with
the upstream interpreter outputs before producing shaders. Specialization and
import currently have finite gates rather than semantic-preservation proofs.

Read against these local source revisions on 2026-11-06 (the imported catgrad
library and example files are unchanged; the existing local workspace adds an
unrelated graphplay member):

* catgrad `7629a506680fdd9380706bd31b43017d1bf153fc`: `catgrad/src/category/core.rs`,
  `catgrad/examples/hidden.rs`, `catgrad/src/definition/types.rs`, `interpreter/interpreter.rs`, `interpreter/tensor_op.rs`,
  `interpreter/backend/ndarray.rs`, and `abstract_interpreter/eval.rs`.
* open-hypergraphs `d746affdc347b9a6137f34feeaf4bd97c4a8334b`:
  `src/lax/open_hypergraph.rs` and `src/lax/hypergraph.rs`.

The envelope `catgrad-core-u32-v1` adds concrete `inputTypes`, source provenance
and test vectors to the unmodified serde representation of specialized `term`.
Its graph has `sources`, `targets`, and a `hypergraph`
with `nodes`, `edges`, `adjacency` and `quotient`. Node labels are `Tensor`, not
shape annotations; shape inference starts at `inputTypes`. A nonempty quotient
must be resolved upstream before import. Only topological single-assignment terms
with explicit Copy and one-use wires are admitted.

Supported core operations are `Copy`, rank-2 `Tensor.MatMul`, and
`Tensor.Map.{Add,Sub,Mul,LT,Where}`. All tensors must be U32, all pointwise operand
shapes must agree, and matrix inner dimensions must agree. Other operations,
control flow, definitions, dtype conversions, higher-rank matmuls and implicit
broadcasting are refused by name. Each U32 arithmetic boundary is explicitly
masked with `0xffffffff`; these are not float operations renamed to integers.

The parser/importer currently has no catgrad semantic-preservation theorem.
`checkTypedGraph` constructs a typing derivation whose erasure establishes the
premise of the existing ArrayGraph-to-GPU theorem. Boundary tensor shapes are
retained, with explicit identity gathers flattening/restoring their representation.
Internal elements are typed `.word`; the U32 masking correspondence is tested,
not a proved refinement of this element type. The
comparison with the external interpreter is finite evidence for the import step.
The named refusal tests and planted device faults guard different boundaries.

## Device run, 2026-11-06

`results/recovery-radv-20261106.txt` records the recovery gate on hbox's Radeon RX 6750 XT
(RADV Mesa 24.2.8): four vectors agreed across upstream catgrad, the Lean evaluator
and the GPU; both planted shader mutations and all five named refusal cases passed.
The additional scalar oracle probe checks wrapping Add/Sub/Mul, LT results consumed by Add,
and Where conditions 0, 1, 2 and U32_MAX. This catgrad revision uses U32 predicates;
Where selects its first value for every nonzero condition. Both planted faults are caught
on that probe as well.

The same-host baseline was **0.421578 ms** per upstream catgrad interpreter forward
pass and **3.107 ms** per GPU vector. The GPU path is slower for this workload and
schedule. CPU timing includes source-term cloning and lang-to-core lowering on every pass,
shape evaluation, parameter loads, term scheduling and arithmetic, but excludes input
tensor construction. GPU timing excludes compiler work, so this is not an equal-scope
throughput comparison. GPU timing includes command
submission and device completion, excluding pipeline creation, buffer upload and
readback. These are observations on a shared host, not a performance guarantee. The earlier
`radv-20261106.txt` and `final-radv-20261106.txt` logs are retained as historical runs;
the recovery figures above supersede their timing claims.

The runner used was the already-built `isa/hardware/gpu/runner/target/release/obend-gpu-run`
on hbox, which requests `SHADER_INT64` and reports dispatch timing.

## Floating point remains a separate obligation

[Browne, Lee & Salvi (2610.24548)](https://arxiv.org/html/2610.24548), §§3 and 5,
reason over Float32, retaining NaNs and signed zero. Their opaque transcendental
symbols require pointwise agreement between the reference and device routines;
`expf` and `__expf` cannot be identified. Velvet's SMT results remain trusted in
the reported setup. This is not an end-to-end bitcode/device proof.

[LARK (2611.02028)](https://arxiv.org/html/2611.02028), §§4.1–4.3 and Appendix A.7,
uses exact arithmetic, including exact integer payloads under width tags. It
explicitly leaves rounding, overflow and quantization outside its equivalence
claim; numerical GPU tests provide separate tolerance evidence. Its reusable
operation semantics and explicit trust report are useful architecture, not a
proof that our U32 model implements IEEE arithmetic.

Our future float path requires all of the following, beyond either paper's title:

1. A separate IEEE scalar interpretation with explicit format, rounding, NaN,
   infinity, signed-zero and subnormal/flush behavior; conversions must carry
   their actual rounding and saturation rules.
2. Reduction semantics specifying accumulation format and tree/order, and whether
   multiply-add contracts to FMA. Associativity of modular words cannot justify
   reordering float reductions.
3. A source-to-array semantic-preservation theorem and either bit-exact device
   agreement under pinned compiler modes or a proved error relation with input
   hypotheses. An empirical tolerance must remain labelled empirical.
4. Transcendentals with a documented shared implementation assumption, or proved
   device approximation/error bounds. Unsupported functions remain named errors.
5. Backend-specific numerical probes and planted rounding/order/NaN faults,
   alongside the existing race/memory and actual-device gates. Fast-math settings
   and driver/compiler versions belong in the run evidence.
