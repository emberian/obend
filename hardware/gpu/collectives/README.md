# Collective measurements

`benchmark.py` obtains scan/reduction artifacts from the source emitter, generates
independent NumPy `uint64` expected outputs, and sends every output element through
the ordinary GPU runner's exact comparison. Add/multiply wrap modulo 2^64;
AND/OR are bitwise word monoids. Reduction returns one word per segment, including
the identity for an empty segment. Scans preserve the concatenated input shape.

The default timing matrix covers addition at 2^16, 2^20 and 2^24 words, both one
long segment and many segments of length 32, for inclusive/exclusive/reduction.
All four monoids get correctness checks at 2^16 and on small fixtures. Before
timing, an irregular fixture crosses tile boundaries and includes empty
segments; all-empty and no-segment fixtures check boundary behavior. Small cases
have two input patterns, including high bits and arithmetic overflow. Large
multiply inputs stay odd; AND/OR events span the input instead of saturating in
its first few words. A standalone handwritten `vec2<u32>` copy shader measures
the same adapter through the same runner; it is labeled as a bandwidth baseline,
not as a source compiler correctness result.

Run on the designated host, coordinating exclusive GPU access with other lanes:

```sh
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json \
/home/hbox/obend/soac-benchmark-venv/bin/python hardware/gpu/collectives/benchmark.py \
  --emitter lean/.lake/build/bin/obend-emit-gpu \
  --runner hardware/gpu/runner/target/release/obend-gpu-run \
  --adapter radv --out /home/hbox/obend/collectives-measurement
```

That ICD path and Python environment are the existing hbox configuration. On
another host select its actual GPU driver and a Python environment with NumPy.
Driver-selection environment variables are recorded in the results.

The output directory must be new. `--suite correctness` runs the small and 2^16 cases;
`--suite benchmark --sizes 16 --ops add --modes inclusive` is a bounded timing
probe. Defaults are declared before execution: 31 measured repetitions after three
warmups for GPU and NumPy. `--gpu-repeats` and `--cpu-repeats` are recorded in the
report. No subprocess timeout kills are used. Builds belong under `swarm-build`.
`--ops` selects timed monoids; `--correctness-ops` selects the independent
correctness matrix. `--suite copy --sizes 16` runs just the copy baseline and
does not invoke the source emitter.

GPU times in microseconds span first-pass beginning to last-pass end, including
every dispatch and intervening barrier. Compilation, initial upload, reset copies
and final readback are excluded. The runner resets the whole device workbuffer
before every interval, so results describe warm, device-resident execution. Its
separate host batch number includes reset copies, warmups and final mapping.
NumPy uses preallocated outputs and warm inputs; `perf_counter_ns` includes Python
dispatch and the same operation, excluding allocation and fixture IO. NumPy is
not run concurrently with GPU samples. Median, p10 and p90 use the sorted sample
at floor((count−1)*percentile/100), consistently on both sides.

`results.json` records environment, scopes, samples, adapter, every case result,
logical traffic, metadata size and fixture hashes. Per-case directories retain
specs, emitted WGSL/plan, emitter/GPU logs and results. Raw fixture files are
removed only after successful exact validation, bounding active binary data;
`--keep-fixtures` retains them for direct runner replay. Regenerating a run uses
the same fixed seed and documented input pattern. Failed cases keep their binary
files. Writes stop with less than 20 GiB free, without deleting another run's data.

The runner optionally reads `vectors.json` instead of `expected.tsv`:

```json
{"format":"u64le","vectors":[{"index":"case","inputs":["input.u64le"],"expected":["expected.u64le"]}]}
```

Each listed file contains raw little-endian words and must have exactly eight
bytes per corresponding plan boundary element. Every input and every output must
be listed, including zero-byte files for empty wires. High bits are preserved;
the runner's internal `i64` storage does not change word semantics. TSV gates
continue to work, with the same complete boundary shape checks. A malformed JSON
manifest is an error, not permission to fall back to TSV. Device buffer limits
are checked before GPU allocation. The runner still enforces its 512 MiB reset
image and 65,536 batched dispatch limits.

Focused oracle/fixture checks:

```sh
python3 -m unittest discover -s hardware/gpu/collectives -p 'test_benchmark.py'
cd hardware/gpu/runner
swarm-build cargo test --release --bin obend-gpu-run binary_fixture_tests
```

# Algorithm references and comparison limits

Merrill and Garland's 2016 decoupled lookback uses aggregate/prefix tile states
and overlaps redundant metadata work with prefix propagation, approaching two
global item transfers per element. Their figures 7–9 report CUB 1.5.2 saturated
**32-bit device-wide prefix sum** at approximately **30.8 billion items/s on Tesla
M40, 26.7 on K40, and 14.4 on C2050**, all with ECC disabled. The corresponding
minimum read-plus-write rates are 246.4, 213.6 and 115.2 GB/s, derived from eight
bytes per item, not measured memory traffic. The paper does not give an explicit
timer/warmup/sample protocol. These are historical published GPU results, not
measurements of this repository's u64 code or its AMD adapter.
[Primary paper](https://research.nvidia.com/sites/default/files/pubs/2016-03_Single-pass-Parallel-Prefix/nvr-2016-002.pdf).

The initial portable implementation uses hierarchical reduce-then-scan: reduce
tiles, scan their totals recursively, reread and scan each input tile seeded by
its prefix. This has linear work and about three global word transfers per
element plus the small hierarchy. A shared tree upsweep/downsweep keeps local
work linear. CUB's block implementations also combine sequential register work,
shared raking and warp scans. Current Thrust's CUDA scan calls CUB dispatch; the
2016 paper's slower Thrust 1.8.2 result is not a current Thrust comparison.
[CUB block source](https://raw.githubusercontent.com/NVIDIA/cccl/main/cub/cub/block/block_scan.cuh),
[current Thrust CUDA source](https://raw.githubusercontent.com/NVIDIA/cccl/main/thrust/thrust/system/cuda/detail/scan.h).

Sengupta et al. extend the work-efficient scan tree to segment boundaries. A
useful formulation lifts a monoid to value/head pairs:
`(a, ha) combine (b, hb) = (hb ? b : a combine b, ha OR hb)`.
Segment lengths must additionally preserve empty segment reduction outputs;
head flags alone cannot represent empty segments.
[2007 primary paper](https://doi.org/10.2312/eggh/eggh07/097-106).

Levien's 2020 Vulkan prototype reported 2.05 ms GPU time for 64 Mi 32-bit unsigned
integers on GTX 1080, explicitly as preliminary measurements. Its published
derived rate/bandwidth units are inconsistent, so this is not used as a numeric
baseline here. The 2021 follow-up explains the distinct publication and forward
progress problems of cross-workgroup lookback.
[2020 post](https://raphlinus.github.io/gpu/2020/04/30/prefix-sum.html),
[2021 post](https://raphlinus.github.io/gpu/2021/11/17/prefix-sum-portable.html).

The 2021 limitation is **not a claim that portable single-pass scan is impossible**.
Smith, Levien and Owens (SPAA 2025) present decoupled fallback, which recomputes
blocking tiles after bounded spinning. Their atomic splitting packs state into
each payload chunk, accepts matching states and uses monotone atomic maximum to
prevent state regression; it supports 64-bit payloads without 64-bit atomics.
This is a concrete future design, requiring semantics for atomics and fallback
that the current ArrayKernel language does not express.
[2025 primary paper](https://escholarship.org/content/qt0bk9z4bt/qt0bk9z4bt.pdf?v=lg).

Ordinary separate-payload message passing cannot be inferred from WGSL relaxed
atomics: current WGSL barriers have workgroup scope, and different atomic
locations do not supply acquire/release publication. The current hierarchy uses
ordered dispatches for global communication.
[WGSL memory semantics](https://gpuweb.github.io/gpuweb/wgsl/#memory-semantics).
