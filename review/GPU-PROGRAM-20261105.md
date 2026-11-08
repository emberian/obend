# GPU as a theory, device as a model: a program (2026-11-05)

> 2026-11-06 kernel-lane update: The live layout, general workgroup source, limb arithmetic, Stockham uploads, measured resource model and named CPU comparison are implemented in the lane. See [GPU-KERNELS-20261106](GPU-KERNELS-20261106.md) for universal theorem statements, final gate results and remaining boundaries. This dated design document is not evidence that the new ISA model gate passes.

Prompted by Noah Chrein's question ("is categorical semantics on a GPU as easy as replacing the topos
Set by a category GPU, then GPU by GTX5060Ti?") and by the council's finding that our previous GPU
work (`Hardware/Accelerators.lean`'s nine-instruction interpreter, the six-stage self-acceleration
theorems) modelled a device nobody ran. The flaw was ours. This note is the program that makes the
idea honest, in the rung grammar of `HARDWARE.md`: external artifact, theorem over our model of it,
gate a planted fault must fail.

## Ingredients found

- **Abraham & Okoli, "Toward a Universal GPU ISA" (arXiv 2603.28793, March 2026).** Cross-vendor
  analysis of PTX, RDNA 1-4, CDNA 1-4, Intel Xe, Apple G13. Ten hardware-invariant primitives plus
  intra-wave shuffle (lockstep group, mask divergence, register/occupancy tradeoff with
  O = floor(F/(R*W*w)), managed scratchpad, zero-cost switch, 3-level memory, atomic RMW, workgroup
  barrier, identity registers, async memory + sync); six parameterizable dialects (W, R, S, max
  workgroup, named barriers, FP64); six true divergences (divergence mechanism, SALU/VALU split,
  hierarchy depth, matrix units, memory ordering mechanism, fixed function). Thin abstraction
  principle: query W, R, S; structured control flow hides divergence; scoped acq/rel hides caches.
  Validation is thin (three kernels, T4 and M1, weak baselines; AMD and Intel "in progress"; the formal
  ISA spec is a promised companion report). The taxonomy is what we take, not the numbers.
- **AMD machine-readable ISA (GPUOpen).** XML per RDNA and CDNA generation (CDNA5 added August 2026)
  with instructions, encodings, bit fields, operand types, data formats, and a C++ `IsaDecoder`.
  Operation semantics is prose. So the instruction inventory and decoder are generated, never typed.
- **hbox has an AMD Radeon RX 6750 XT (Navi 22, gfx1031, RDNA2)** on the `amdgpu` kernel driver, with
  both Vulkan ICDs installed (Mesa RADV `radeon_icd.x86_64.json`; AMDVLK/LLPC 2025.Q2.1), Mesa
  24.2.8, LLVM 19 with the `amdgcn` target (`llc`, `llvm-mc`, `llvm-objdump`), `clang`, `glslangValidator`
  14.3, `spirv-tools` 2024.3, `cargo`. No ROCm compute runtime (no `hipcc`, no `rocminfo`); `rocm-smi`
  only. The RDNA2 ISA reference manual is public. `RADV_DEBUG=shaders` dumps the final gfx1031
  assembly and resource usage (VGPRs, LDS) of every pipeline RADV compiles.
- **The Mac's Apple GPU** with Dougall Johnson's `applegpu` (G13 docs, disassembler, assembler,
  emulator) and Asahi's AGX notes: an executable third-party oracle for the ISA stratum.
- **Memory models.** PTX (Lustig et al., ASPLOS 2019, Alloy) and Vulkan/SPIR-V are formal and
  litmus-validated; AMD's is HSA scoped release consistency (HRF-Relaxed, TACO 2015) and the Relaxed
  Memory Model Zoo records that no cat model of it is published. Litmus methodology: Alglave et al.
  ASPLOS 2015; Kirkham et al. OOPSLA 2020; GPUHarbor ISCA 2023.
- **Execution model theorems.** Habermaier & Knapp (ESOP 2012): SIMT lockstep is observationally
  equal to interleaved execution for barrier-uniform kernels. GPUVerify (OOPSLA 2012) and Faial
  (CAV 2021) discharge race and divergence freedom.
- **Kernels verified in Lean already.** Browne, Lee & Salvi (arXiv 2610.24548, October 2026): Velvet,
  an imperative verifier embedded in Lean, proves spec-to-CUDA-kernel equivalence over floats, race
  freedom in VerCors.
- **Sheaf-of-views floors.** Gibson (arXiv 2605.08609, May 2026): Lean 4 + Mathlib proof that a design
  presheaf over views is a sheaf and pairwise overlap compatibility gives global consistency. Van
  Starkenburg, Basold & Ford (arXiv 2508.01866): separation logic as categorical logic internal to
  sheaf categories ("sheafeology"). Goguen 1992 is the ancestor. Nobody has aimed this at memory models.
- **Ours.** `Hardware/OpenHypergraph.lean` (Wilson-Zanasi data-parallel string diagrams,
  `layerHypergraph_sound`, `evalHypergraph_pipelined_eq_comb`, per-op catgrad optics); `Hardware/Hvm.lean`
  rung 2 (`lowerBookToHvm_sound`, one schedule exhibited, confluence not proved); `Apps/ZkNtt.lean`
  (Goldilocks field, `goldilocksMulSpec`, `goldilocksReduce128Spec_sound`, the radix-2 butterfly, the
  Verilator-gated RTL). breadstuffs: `Dregg2/Distributed/Fibration.lean` (one fibration over deployment
  conditions, apex fibre = single-machine ideal, `lift` adds measured slack), `Apps/EpistemicSheaf.lean`
  (consensus = global section, fork = witnessed non-gluing), `Metatheory/IndexedMonoidal.lean`
  (Shulman monoidal fibrations), `Market/ZKOpenRel.lean` (strong monoidal grading functor,
  conservation = zero-defect subcategory), `Authority/Epistemic.lean` (Lawvere triple over a fibration).

## The organizing idea

Set does two jobs in categorical semantics: the carrier of values and the ambient logic. A device can
do the first and not the second. So "replace Set by GPU" is replaced by:

- **GPU is a theory, not a category of values.** `T_GPU` is Abraham-Okoli's eleven primitives with
  the six dialect parameters, a Lawvere-style theory with structured control and scoped acq/rel.
- **A device is a model of it.** RDNA2-on-hbox, G13-on-the-Mac, T4, are interpretations
  `M : Syn(T_GPU) → Set` (relations, where atomics and float reductions make outcomes a set).
- **A program is a morphism in the syntactic category**, concretely a `StrictOpenHypergraph` over
  the theory's signature, whose semantics on a device is `M` applied.
- **The memory model is a sheaf condition on the scope site.** Scopes wave ⊂ workgroup ⊂ device ⊂
  system form a coverage on places; per-thread observed histories form a presheaf; a consistent run
  is a global section; a weak behaviour exhibited by a litmus test is a witnessed non-gluing.
- **The devices form the base of a fibration.** Base points are (W, R, S, memory-model variant,
  numeric mode); the apex fibre is `evalHypergraphComb`, sequential and exact; reindexing to a device
  point adds measured slack (permitted reorderings, error interval, latency window). A GTX 5060 Ti is
  a point in the base. The AMD model we have no hardware for is a point with a named open.

## Rungs

| rung | from → to | external artifact | theorem | gate |
|---|---|---|---|---|
| G0 | A-O model → `Obend.Hardware.Gpu.Theory` | the paper's Tables II-IV | none (a signature); a study until G1 lands | `#docs_census` names only |
| G1 (landed 2026-11-05: `Obend.Hardware.Gpu`, `hardware/gpu/`) | `StrictOpenHypergraph` → abstract GPU program | emitted WGSL/GLSL and SPIR-V | `lowerHypergraphToGpu_sound`: one dispatch (or one barrier) per wavefront layer; barrier-uniform by construction, so Habermaier-Knapp's hypothesis holds structurally; uses `layerHypergraph_sound` | runs on hbox (RADV) and the Mac (Metal) equal `evalHypergraphComb` on a vector set; a planted wrong op fails on both |
| G2 | abstract program → RDNA2 ISA | AMD's RDNA2 XML; RADV's `RADV_DEBUG=shaders` dump | decoder generated from the XML; semantics for the instruction subset RADV emits for our kernels (demand-driven, refused by name like `Hvm.lean`); `radv_output_denotes`: the dumped ISA, read by our model, computes the abstract program. Translation validation of an untrusted compiler, per kernel, as a `Judge` format | our decoder agrees with AMD's `IsaDecoder` on the dump bytes; model's run equals the 6750 XT's run; a flipped bit in the dump fails |
| G3 | abstract program → Apple G13 | Metal binary; `applegpu` disassembly and emulator | same shape as G2 with a third oracle | Lean model, emulator and silicon agree; planted fault splits them |
| G4 | scoped memory model → sheaf on the scope site | litmus suite (MP, SB, LB, IRIW with scopes) run at stress on hbox and the Mac | `allowed_iff_glues` for the finite litmus shapes; the first machine-checked model of AMD's HSA-scoped ordering, validated on silicon | forbidden outcome refused by the checker and never observed; model-allowed weak outcome observed on a device or recorded as the device being stronger |
| G5 | program → resource grade | RADV's reported VGPR and LDS usage | `grade` lax monoidal into a cost semiring over (W, R, S); occupancy by the paper's equation | predicted VGPR/LDS equals RADV's report; a planted spill moves both |
| G6 | everything → one fibration | none | the breadstuffs `Fibration` pattern: apex `evalHypergraphComb`, fibres G1-G5 with measured slack, `lift` between device points; `Accelerators.lean`'s interpreter and the six-stage theorems were deleted 2026-11-05 with `Lower/Proofs/SelfAccelerate.lean` and the apps' GPU co-execution certificates (nothing lands beside) | non-vacuity (a device point with positive slack) and a negative tooth, as in breadstuffs |
| G7 | HVM2 net → GPU | `hvm run-cu` | schedule independence (Lafont's strong confluence, ported) | needs a CUDA device; hbox is AMD and HVM2 has no HIP backend. Named open until a card or a port exists |

**Landed the same day:** G1, in `Obend.Hardware.Gpu` with `hardware/gpu/verify_gpu.sh`; the gate passed on
hbox's RX 6750 XT under both RADV and AMDVLK and on the Mac's M2 Max, and RADV's final ISA of every stage
is under `hardware/gpu/isa/`. hbox's card was the missing device: the AMDVLK ICD is the loader's default
there, `VK_ICD_FILENAMES` selects Mesa's RADV, whose `RADV_DEBUG=shaders` is the dump G2 reads.

**Landed later the same day:** the array generalization. `Obend.Hardware.ArrayHypergraph` (wires carry
vectors; map, gather, concat, const; the scalar graphs as the one-element instance) and the lowering
restated over it with `lowerArrayToGpu_sound`; the Goldilocks NTT of 64 points, built from gathers and the
`glMul` limb network, runs on both cards and the Mac and agrees with the naive DFT. The device as the site
and the shape-indexed wires as presheaves on finite index sets are now the same code.

**Landed 2026-11-06:** the lowering's structure. `fuseGraph` (Halide/TVM elementwise inlining with a
soundness theorem at the graph level, since a wavefront level never contains a chain) and the frontier
layering of Wilson–Zanasi's `kahn` replace the greedy layering; the NTT is Stockham radix-2 over whole
wires as ec-gpu's `radix_fft` kernel. The 64-point NTT went from 1670 dispatches to 19, and NTTs of 1024
and 65536 points (31 and 49 dispatches, `3 log₂ n + 1`) run on both cards and the Mac. The 65536-point
plan is kept as a digest. Dispatch times are printed by the runner and not gated.

**First workload:** the Goldilocks radix-2 butterfly from `Apps/ZkNtt.lean` as an open hypergraph. Exact
arithmetic, so atomic and reduction order is irrelevant by associativity; the spec already exists; the
RTL path is already Verilator-gated. One spec through two devices (Verilator/EQY and RDNA2) is the
six-stage diagram done honestly: a commuting square with every leg an external run.

## What this does for our own agenda

- The hardware tier gets a device we own, can run daily, with a vendor-documented ISA.
- The Houyhnhnm "verify others" slice gets its sharpest instance: the GPU compiler is an untrusted
  producer, the ISA dump is its witness, a small `Judge` format checks it.
- One fibration replaces per-device modules: FPGA tile, GPU, HVM2 are base points of one structure.
- `OpenHypergraph.lean` gets the reason to exist the council asked for (P6: functorial adjoint,
  pipelining) because catgrad-shaped models become real workloads with a gate.
- The ZK prover acceleration path (Goldilocks NTT on GPU; hellas `ec-gpu` adjacency) opens.
- Publishable gaps we would fill: a machine-checked AMD scoped memory model validated on RDNA2; the
  sheaf-on-scopes reading of weak memory; a mechanization of Abraham-Okoli's model with mapping
  theorems to two real devices.

## Draft reply to Noah

See the chat of 2026-11-05; the text is reproduced below for sending.

---

Not as easy as swapping toposes, and the reason is worth more than the answer. Set does two jobs in
categorical semantics: it is the carrier of values and it is the ambient logic (exponentials,
subobject classifier, colimits). A device can play the carrier but not the logic: kernels have no
function spaces of kernels and no truth values. So "presheaves C^op → GPU" is a legitimate definition
of C-indexed families of buffers with kernel restriction maps, and every theorem you want from
presheaf toposes is gone with the exponentials.

Here is the replacement that I think is actually right, in your terms.

GPU is a theory, not a category of values. Abraham and Okoli (arXiv 2603.28793, this March) extracted
from PTX, RDNA, CDNA, Xe and Apple G13 eleven hardware-invariant primitives, six parameters and six
genuine divergences. Call the primitives with their parameters T_GPU, a Lawvere-style theory with
structured control flow and scoped acquire/release. A device is a model M : Syn(T_GPU) → Set, or into
Rel once atomics make outcomes a set. A GTX 5060 Ti is a model, not a theory; "Set ⇒ GPU ⇒ GTX" is
theory ⇒ model, and the second arrow is where all the content lives. Programs are morphisms in the
syntactic category, concretely open hypergraphs over the signature (Wilson and Zanasi, who also made
the syntax itself a data-parallel array structure, which is the real sense in which categorical
semantics runs "on" a GPU).

Your presheaves do appear, with Set as codomain and the device as the site. A GPU is places and
nested scopes, wave ⊂ workgroup ⊂ device ⊂ system; the scopes are a coverage; what each place can
observe is a presheaf; the memory model is the sheaf condition; a consistent execution is a global
section; a weak memory behaviour caught by a litmus test is a witnessed non-gluing, exactly
Abramsky-Brandenburger contextuality with scopes as contexts. Nobody has written this down for memory
models as far as I can find, and the Lean floor exists (Gibson, arXiv 2605.08609). For you
specifically: scoped visibility is a family of modalities graded by the scope lattice, and the sheaf
condition over the site is what makes them compose. And the empirical method of the field is Yoneda:
Kirkham, Sorensen and company identify a device's memory model by its outcome table on a finite
family of litmus probes, which is the model determined by its restriction to a dense subcategory.

The devices themselves assemble into a fibration over execution conditions (W, R, S, memory model
variant, numeric mode). The apex fibre is the sequential exact semantics in Set. Reindexing to a
device point adds measured slack: permitted reorderings, an error interval, a latency window. Changes
of device are vertical arrows in a Shulman-style equipment whose horizontal arrows are programs and
whose 2-cells are refinement proofs; compiler correctness is a 2-cell, and an equivalence check with a
planted fault is checking one.

What makes this honest rather than decorative is the gate: at every stratum, an external run of the
real device that a planted fault must fail. We have an RDNA2 card and a documented ISA to start on;
your card would be the CUDA point in the base.
