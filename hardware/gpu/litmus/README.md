# hardware/gpu/litmus: the memory model of our GPUs, measured

Rung G4 of `review/GPU-PROGRAM-20261105.md`. The model is `lean/Obend/Hardware/Gpu/Memory.lean`
(read its header first: the referent, the specialization of the Vulkan model to WGSL, what is proved
and what is a checked table); the gate is `../verify_litmus.sh`; this directory is the suite and its
measurements.

## The tests

The kernels under `wgsl/` are GPUHarbor's (Levine, Guo, Huang, Ma, Chau, Sorensen, "GPUHarbor:
Testing GPU Memory Consistency at Large", ISCA 2023; `github.com/reeselevine/webgpu-litmus`,
Apache-2.0), copied unmodified below a header naming the source file and commit. `suite.tsv` names
which kernel and which result kernel make a test, the scope of the thread pair and the address space
of the test locations. The test shapes are the field's, not ours: MP, SB, LB, IRIW, 2+2W (the weak
behaviours of Alglave et al., "GPU Concurrency: Weak Behaviours and Programming Assumptions",
ASPLOS 2015), CoRR, CoWW, CoWR, CoRW1, CoRW2 and read-modify-write atomicity (the coherence tests),
each at device scope (the two threads of an instance in different workgroups, atomics in a storage
buffer: WGSL gives them QueueFamily scope) and, for the first family and the coherence of reads and
writes, at workgroup scope (both threads in one workgroup, atomics in `workgroup` memory or in the
storage buffer), with and without the WGSL barriers between the accesses; and GPUHarbor's barrier
tests on non-atomic `workgroup` memory (store-load, load-store, store-store across a
`workgroupBarrier`). Scopes exercised: workgroup (barriers, `workgroup`-space atomics) and device
(storage atomics; WebGPU's one queue makes QueueFamily and Device the same here). Subgroup scope is
not exercised: WGSL's subgroup built-ins are not used by any kernel.

Every kernel thread plays role 0 of its own instance and role 1 of another instance in the same
dispatch, so a barrier between the two roles of the kernel body is in both threads' program order.
The shapes in `lean/tools/litmuscheck/LitmusCheck.lean` are the kernels' per-thread programs
projected to one instance's locations with every barrier kept in place, which is what the device
ran, not the two-line pseudo-code GPUHarbor displays. The difference shows: with that reading the
model forbids the `seq0` class of `mp-workgroup-barrier`, `mp-storage-workgroup-barrier`,
`sb-workgroup-rmw-barrier` and `lb-workgroup-barrier` as well as their `weak` class, and no device
showed `seq0` for any of them.

## The runner and the stress

`../runner/src/bin/obend-gpu-litmus.rs` is a port of GPUHarbor's host side (`litmus-setup.js`) and
of the parameter space of its tuning page (`randomConfig`: the number of testing and total
workgroups, the workgroup size, the memory stride, the stress line size and target lines, the
stress iterations and patterns, the shuffle, barrier, pre-stress and memory-stress percentages), the
tuned-stress method of Kirkham, Sorensen, Tureci and Martonosi ("Foundations of Empirical Memory
Consistency Testing", OOPSLA 2020). The PRNG is GPUHarbor's `prng.js` seeded from the run's seed and
the test's name, so a seed names the parameter sequence. Each test runs a number of configurations
and, per configuration, a number of iterations (one dispatch each); the committed tables use
GPUHarbor's deployed budget (its production `.env`: fifty configurations of fifty iterations). The
outcome classes are counted by GPUHarbor's own result kernels; the runner only sums them.

    cd ../runner && cargo build --release
    ./target/release/obend-gpu-litmus ../litmus --adapter radv --configs 50 --iterations 50 \
        --seed obend-20261106 --out ../litmus/results/rx6750xt-radv.tsv

On hbox, `VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json` selects Mesa's RADV for
the RX 6750 XT, the loader's default is AMDVLK (`--adapter "AMD open-source"`), and `--adapter Intel`
is the UHD 770 under Mesa's ANV; on the Mac the one adapter is the M2 Max under Metal.

## The tables

`results/<device>-<driver>.tsv`: one line per test with the seed, the budget, the number of
classified instances, the count of every outcome class, the largest single-configuration count of
the `weak` class and the configuration that produced it. `results/STRONGER.tsv` records the tests
whose weak class the model allows and no device showed: the device is stronger than its model there,
and the gate holds the record to the tables (a recorded test that a device later shows fails the
gate, as does an allowed weak class that is neither shown nor recorded).

What the devices showed, in words (the tables have the counts):

* The relaxed weak behaviours at device scope, MP, SB, LB and 2+2W, appear on the M2 Max under
  Metal and on the RX 6750 XT under both RADV and AMDVLK; IRIW's weak outcome appears only on the
  M2 Max. The UHD 770 under ANV showed no weak behaviour at all at this budget (a first run with a
  mis-sized result buffer, discarded, had shown one SB instance): the Intel integrated part reads as
  sequential on these tests.
* A `storageBarrier` between the accesses of threads in different workgroups does not remove the
  weak behaviours on the M2 Max (MP and SB with a read-modify-write), as the model says: WGSL's
  barriers have Workgroup scope. The AMD and Intel parts never showed them with the barrier, and
  nobody showed LB's: those are recorded in `STRONGER.tsv`.
* No device showed any coherence violation (CoRR, CoWW, CoWR, CoRW1, CoRW2, atomicity), at either
  scope, and none showed a weak outcome of a workgroup-scope test with barriers or of the non-atomic
  barrier tests.
* The weak behaviours at workgroup scope without barriers (MP, SB, LB in `workgroup` memory) did not
  appear on any device; MP in the storage buffer within one workgroup appeared on RADV. The ones not
  shown are recorded in `STRONGER.tsv`.

## The referent

`dartagnan/` holds every shape and outcome as a Dartagnan Vulkan litmus test (`obend-litmus-check
dartagnan`), one `exists` assertion per outcome, and `verdicts.tsv`, Dartagnan's `Result` on each under
`cat/vulkan.cat` (`PASS`: the outcome is reachable). The gate requires the checker's verdict to equal
Dartagnan's on every file, regenerating the verdicts when Dartagnan is installed (`DAT3M_HOME` or
`~/tools/dartagnan`) and reading the committed table otherwise.

## The gate

`../verify_litmus.sh`: Dartagnan agreement on every shape and outcome; every class a device showed
is allowed; every allowed weak class is shown or recorded; each planted change to the checker's
axioms (drop coherence, drop barrier synchronization, make it sequential) makes the device stage
fail; and the section functor restricts along scope inclusion on every shape.
