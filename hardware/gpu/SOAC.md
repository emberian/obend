# Reduction and scan baseline

`ArrayOp.fold op shape` adds reductions, inclusive and exclusive scans, and their
segmented forms to the existing array graph and GPU lowering. Convenience constructors
are `ArrayOp.reduce`, `scan`, `segReduce`, and `segScan`. `ReduceOp` contains addition,
multiplication, bitwise AND and bitwise OR over words modulo 2^64. Each operation has
proved associativity and left/right identity laws in `ArrayFold.lean`.

Both scans preserve the input length. Inclusive scans include the current element;
exclusive scans start with the identity and omit the final total. Segment descriptors
are lengths whose sum must equal the input length. Empty reduction segments produce
identities, including all-ones for AND; empty scan segments produce no elements.
The shape check rejects source arity or length mismatches.

The conventions follow Futhark's length-preserving inclusive scan, with the exclusive
variant named explicitly; Accelerate and NESL supply the segment-length representation.
The schedule remains separate from the operator, as in Lift:

- [Futhark, PLDI 2017](https://futhark-lang.org/publications/pldi17.pdf), §2.
- [Accelerate language interface](https://hackage-content.haskell.org/package/accelerate-1.1.0.0/docs/src/Data.Array.Accelerate.Language.html), `foldSeg` and scan operations.
- [NESL](https://www.cs.cmu.edu/~scandal/nesl.html), nested arrays and work/depth.
- [Lift, CGO 2017](https://eprints.gla.ac.uk/146596/1/146596.pdf), pattern/schedule separation and `reduceSeq`.
- [Strategies for Regular Segmented Reductions on GPU, FHPC 2017](https://futhark-lang.org/publications/fhpc17.pdf), the sequential-segment strategy and alternatives for larger segments.

## Execution and proofs

The reference semantics maps each output to a fold of its input interval. The CPU
executor caches the previous prefix and extends it, resetting at segment boundaries.
It reads the source Array in constant time and accumulates outputs with tail-recursive
`Array.push`; a 65,536-element scan does not require a chain of recursive list outputs.
`foldRangesCachedArr_toList` and `evalFoldExec_toList` establish equality with the reference
semantics. `evalGraphArr_eq` includes the new operator through the existing graph evaluator.
The execution strategy has linear arithmetic work for the generated scan/reduction
intervals; this complexity assessment is not a mechanized cost theorem.

The GPU baseline assigns one invocation to each segment. A reduction invocation writes
one value; a scan invocation writes its entire contiguous output segment. The invocation
count (`Kernel.threads`) is therefore separate from the output span (`Kernel.count`).
`scanRange_eq` proves the indexed accumulator loop, `foldThreadValues_flatten` proves the
segment schedule, `kernelInvocationValues_flatten` connects it to the output-address
model, and `lowerEdge_invocations_sound` connects those actual loops to every valid edge
input. The existing universal `lowerArrayToGpu_sound` continues through fusion and layering.

This schedule has linear work and parallelism **between** segments. It has no parallelism
within a segment. It is a correctness baseline, not a competitive large-segment scan:
Blelloch-style workgroup trees or multi-dispatch chunk totals and offsets remain needed.
The current schedule does not implement Futhark's adaptive strategy selection.

## Gate and measurements

`verify_soac.sh` regenerates and compares the committed artifacts, runs all five graphs
on the selected GPU, and requires `addAsSub` to produce an actual output mismatch. Shader
validation errors and crashes do not count as the negative tooth. `SoacPrograms.lean`
also checks each emission against an independent list `foldl`/`scanl` reference. The suite
covers all monoids, both scan modes, leading/interior/trailing empty segments, an empty
segment list, overflow, and map → fold/scan → gather composition. The large cases contain
65,536 elements and are stored by digest instead of committing their expected vectors.

With `SOAC_PYTHON` set to a Python interpreter containing NumPy, the gate additionally
checks every output against NumPy uint64 operations and records CPU timing. `soac_numpy.py`
uses vectorized row reductions/scans for the regular segmented case. Its full pipeline
computes the same 25 output vectors as the GPU graph. A separate sum/cumsum timing is a
primitive baseline and does not represent the full pipeline.

CPU timings include allocations and Python dispatch over warm inputs. GPU runner timings
cover submission through device completion, excluding shader compilation and transfers.
They have different timing scopes and are not reported as an end-to-end speedup. The
recorded run and exact versions are in `soac-results.json` and the accompanying gate log.

Rerun after the dev merge on 2026-11-06: RX 6750 XT, RADV Mesa 24.2.8; Core i9-12900, Python 3.12.7,
NumPy 2.5.4 (101 CPU repetitions). The boundary, empty-segment, overflow and composed-operation
cases matched both references and the device; the planted arithmetic defect caused wrong output.

| Input / segmentation | GPU full pipeline, ms/vector | NumPy full pipeline, ms | NumPy sum+cumsum, ms |
|---|---:|---:|---:|
| 8 elements, empty and nonempty segments | 0.333 | 0.178 | 0.003 |
| 65,536 elements, one segment | 92.492 | 2.936 | 0.136 |
| 65,536 elements, 64 segments of 1,024 | 19.518 | 2.939 | 0.137 |

The full pipeline includes both unsegmented and segmented operations, so the final row
still executes long single-segment reductions/scans. This experiment exposes the
large-segment schedule's poor GPU utilization; it does not establish competitive GPU
performance. The next optimization should use parallel chunk reductions/scans, prove
chunk-total propagation from the monoid laws, and retain the sequential schedule for
segments small enough that synchronization would cost more than it saves.
