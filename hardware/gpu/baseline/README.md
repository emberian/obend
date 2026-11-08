# Named Goldilocks NTT baseline

The executable uses **Plonky3 p3-dft 0.8.0**, `Radix2DitParallel<Goldilocks>`,
with exact Goldilocks arithmetic and one transform per call (matrix width one).
`Cargo.lock` pins dependencies. Run `./run.sh`; it builds with two compiler jobs
and `-C target-cpu=native`, and refuses writes/building below 20 GiB available.
Set `RAYON_NUM_THREADS=1` or `8` to reproduce the recorded runs.

The public `dft` API returns natural-order output. Plonky3's roots at these
three sizes equal the emitter's `7^((p-1)/N)` roots (hex values
`9d8f2ad78bfed972`, `54df9630bf79450e`, `30ba2ecd5e93e76d` respectively). Each size checks an inverse
roundtrip and four direct DFT frequencies before measuring. Three warmups populate
cached twiddles. Thirty-one separate samples exclude input construction/cloning
but include all work performed by `dft`, including its output conversion and
allocation. Every result reaches `black_box` and contributes to a checksum.
The upstream [DFT trait](https://docs.rs/p3-dft/0.8.0/p3_dft/trait.TwoAdicSubgroupDft.html)
and [Plonky3 benchmark](https://github.com/Plonky3/Plonky3/blob/main/dft/benches/fft.rs)
are the API and methodology references. This is our harness around their
implementation, not a reproduction of their width-256 benchmark.

Remeasured 2026-11-06 at 22:52 UTC on hbox's Intel Core i9-12900, Rust
`1.100.0-nightly (0dfb098f3 2026-08-31)`. CPU times below are microseconds; median and p90 of 31 samples:

| N | CPU 1 thread median | CPU 1 thread p90 | CPU 8 threads median | CPU 8 threads p90 |
|---:|---:|---:|---:|---:|
| 1,024 | 23.752 | 25.126 | 23.848 | 27.696 |
| 65,536 | 1,513.712 | 1,553.699 | 399.185 | 420.275 |
| 1,048,576 | 36,640.157 | 39,308.671 | 13,016.353 | 19,670.786 |

Raw min/median/p90 and checksums are in `resume-p3-1thread.tsv` and
`resume-p3-8threads.tsv`. The host was shared, with load average
1.17 / 0.61 / 2.11 just after the CPU runs (`resume-host-load.txt`). These
are observed conditions, not claims about best attainable CPU performance.
The predecessor's more heavily loaded runs remain in `hbox-p3-*.tsv`; the
fresh CPU measurements are substantially faster and replace their comparison ratios.
CPU and GPU measurements were separate runs on a shared host; a sibling lane was
also running GPU gates, so exclusive GPU use is not claimed. Compare GPU device
timestamps with CPU computation time only with that distinction visible; the
separate GPU host batch time is retained below.

## Final sustained GPU comparison

The final generated, packed NTT shaders ran on hbox's **RX 6750 XT**, RADV
Mesa 24.2.8, on 2026-11-06. Each `--bench 1024` run records **3 warmups and 1024
measured transforms** in advance, submits all command buffers together, and uses
a distinct GPU timestamp pair for every transform. Before each transform a GPU
copy restores the original input/workspace; that copy lies outside its timestamp
interval. There are no per-sample CPU waits or output readbacks. Query results and
the final output are read back once after the batch. All normal correctness vectors
and the final batch output matched exactly at all three sizes.

GPU times, in microseconds:

| N | Dispatches/transform | Device median | Device p10 | Device p90 | Host batch amortized |
|---:|---:|---:|---:|---:|---:|
| 1,024 | 3 | 13.360 | 12.120 | 51.440 | 77.897 |
| 65,536 | 2 | 50.200 | 48.800 | 68.760 | 128.176 |
| 1,048,576 | 3 | 584.080 | 582.240 | 586.160 | 680.985 |

`host_batch_amortized_us` is wall time from the single batch submission through
both final buffer mappings, divided by **1027 total repetitions**, including warmups.
It includes reset copies and final query/output copies, but excludes command
recording, pipeline creation and the initial reset-image upload. It is not a
per-sample median or an application end-to-end latency. Device timestamps cover
the transform dispatch interval, excluding the reset and final readback. The wide
1,024-point p10–p90 interval is retained rather than hidden by its median.

Measured CPU median divided by measured GPU device median:

| N | CPU 1 thread / GPU | CPU 8 threads / GPU | Faster measured CPU configuration |
|---:|---:|---:|---|
| 1,024 | 1.778× | 1.785× | 1 thread |
| 65,536 | 30.154× | 7.952× | 8 threads |
| 1,048,576 | 62.731× | 22.285× | 8 threads |

These are **compute-time ratios**, not end-to-end speedups. Against the faster
of the two measured CPU configurations, the ratios are 1.778×, 7.952× and 22.285×.
The CPU baseline has 31 samples; the GPU sustained run has 1024. Neither measurement
claims the best implementation/configuration available in the library or a quiet host.

Fresh logs are `resume-gpu-ntt-{1024,65536,1048576}-sustained.txt`.
The predecessor’s `hbox-gpu-ntt-*-sustained.txt` logs remain as historical measurements.
Matching compiler resource grades and full emitted-plan hashes are in
`../cost/resume-ntt-{1024,65536,1048576}-grade.json`.
`comparison-1thread.tsv` and `comparison-8threads.tsv` are produced by `compare.py`.
The earlier `hbox-gpu-ntt-{1024,65536}-batched.txt` files are **intermediate 31-sample
experiments on the earlier source**, retained as history; they are not the final
packed-source performance measurements and should not be mixed into this table.

## GPU library applicability

[VkFFT's upstream feature list](https://github.com/DTolm/VkFFT#currently-supported-features)
and [configuration](https://github.com/DTolm/VkFFT/tree/master/documentation)
provide Vulkan on AMD, but the transform domains are floating-point complex/real
FFT and DCT. The supported precision modes do not supply exact modular
Goldilocks arithmetic or finite-field roots. A VkFFT complex FFT timing is not an
NTT comparison, and no such substituted number is reported. Adding a Goldilocks
arithmetic backend would be substantive new implementation work.

[`ec-gpu`/`ec-gpu-gen`](https://github.com/filecoin-project/ec-gpu) generates
finite-field CUDA/OpenCL kernels and provides `radix_fft_many`, making it a
semantically relevant candidate. Two concrete obstacles remain on this host:

* hbox has `libOpenCL.so.1` (the loader), but a direct `clGetPlatformIDs` call on
  2026-11-06 returned `-1001` (`CL_PLATFORM_NOT_FOUND_KHR`) and zero platforms;
  `/etc/OpenCL/vendors` has no installed ICD and `clinfo` is absent. Vulkan RADV
  availability does not imply OpenCL availability.
* Its upstream README assumes the most significant bit of the prime field is
  unset. Goldilocks fills the top bit of a 64-bit limb. Using it directly with a
  single 64-bit limb violates that arithmetic precondition; a wider representation
  and compatible field trait implementation would need to be checked.

No ec-gpu timing is invented or substituted from another field/device. Installing
an OpenCL runtime and implementing/checking the field representation are named
remaining work for that optional GPU baseline. The mandatory exact named CPU
baseline above has actually run at all three requested sizes.

To join actual GPU measurements, run
`python3 compare.py --cpu resume-p3-8threads.tsv GPU_BENCH_LOG...`.
The output preserves GPU device medians and host batch amortized times separately and labels the CPU/device
ratio as a compute-only ratio. Missing measurements fail instead of appearing as zero.

`batch-reset-check/` is a small correctness fixture, not a performance baseline:
an in-place increment, including a low-limb carry, must still yield exactly one
increment after `--bench 129` (132 repetitions including warmups). This crosses
the runner's 128-pass command-buffer boundary and detects a missing reset copy.

Run `python3 verify_batch.py --runner ../runner/target/release/obend-gpu-run`
to repeat the reset-sensitive test and rejection checks for invalid sample counts,
empty stage lists, too many batched dispatches, and oversized reset buffers.

The resumed run repeated `verify_batch.py` successfully; its output and the
resource-pressure gate output are in `../evidence/resume-measurements.log`.
The fresh OpenCL probe is `../evidence/resume-opencl-probe.txt`.
