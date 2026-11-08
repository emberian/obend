# AMD's machine-readable RDNA2 ISA, and the generator that reads it (rung G2)

`amdgpu_isa_rdna2.xml` is AMD's machine-readable specification of the RDNA 2 instruction set, taken
unchanged from the bundle GPUOpen publishes at <https://gpuopen.com/machine-readable-isa/>
(download link `/download/machine-readable-isa/latest/`, which resolved to
`AMD_GPU_MR_ISA_XML_2026_08_06.zip`, sha256
`82404f1126761b7877595b622afa7e1f311f2f41e89a3abe9aaf8ad045c082e2`), fetched 2026-11-06. The file's own
header says schema 1.1.1, release date 2026-02-20, license MIT, "AMD Public Use"; its sha256 is
`d671ecbc36543674ab59e9b2feffd56718fd2137e7ad913c314f2e2508b9f4f7`. The schema is documented in
<https://github.com/GPUOpen-Tools/isa_spec_manager> (`documentation/spec_documentation.md`), whose
`IsaDecoder` (`source/isa_decoder/isa_decoder.cpp`) is the reference reading of it: an encoding is found
by masking the first dword with the encoding's identifier mask and looking the result up among its
identifiers, in `Order`; the instruction is the one whose encoding and opcode bits form that identifier;
the encoding *condition* (`default`, `has_lit_0`, `has_dpp16`, ...) is an expression over the fields of the
base encoding that selects the variant and its width.

`gen_encodings.py` (run as `python3 -I gen_encodings.py amdgpu_isa_rdna2.xml ../../../lean/Obend/Hardware/Gpu/Rdna2/`)
writes the Lean data modules `Obend.Hardware.Gpu.Rdna2.Encodings` and `Obend.Hardware.Gpu.Rdna2.Insts.*`
from the XML: every encoding with its bit count, identifier mask, identifiers, condition names and fields;
every instruction with its flags and every one of its encodings (encoding name, condition, opcode,
operands with field, operand type, data format, size, direction); the operand types with their
predefined values (register runs kept as runs, which the generator verifies against the XML, special
values one by one). Nothing in those modules is typed by hand; `isa_check.sh` regenerates them and
compares bytes. `Obend.Hardware.Gpu.Rdna2.Decode` is the hand-written decoder over that data, and the
gate `isa_check.sh` holds it to LLVM 19's disassembler on every instruction of `../isa/*.txt`.

`gem5_ref.cpp` ports, case by case with file and line, the lane arithmetic of gem5's executable Vega
model (github.com/gem5/gem5, `src/arch/amdgpu/vega/insts/*.cc`, revision
9d368896ce119c17e1289dcbb18f33624724b843) for every instruction of the model's subset that exists in
Vega; `gem5_ref.py` assembles each twin with llvm-mc in a fixed register assignment, runs the port on
random register states and writes `gem5_vectors.tsv`, the state before and after each; `obend-rdna2
gem5` replays every row through `Obend.Hardware.Gpu.Rdna2.Semantics.step` and compares every register
(`isa_check.sh` stage 5, pinned in `Obend.Teeth.Hardware.Rdna2Runs`). The row's last column names the
registers in which RDNA2 is documented to differ from Vega (`V_CMPX` writes EXEC only, manual 12.9).

`waitcnt_plant.py` is the device side of `Obend.Hardware.Gpu.Rdna2.Waitcnt`: it replaces one `s_waitcnt`
by `s_nop 0` in the machine code RADV keeps in Mesa's multi-file shader cache (entry format and crc per
`src/util/disk_cache_os.c`, `util_hash_crc32`), so that the next `obend-gpu-run` executes the planted
program on the card. Measured 2026-11-06 on hbox's RX 6750 XT (RADV, Mesa 24.2.8), on the unfused
three-stage diamond of dev cf2de1b (`git show cf2de1b:hardware/gpu/isa/diamond.txt`): stage 0,
instruction 11 (`s_waitcnt vmcnt(0)`, the wait between the two `buffer_load_dwordx2` and the
`v_add_co_u32` that consumes them) planted; five runs, all 12 vectors disagree on each, with different
values every run (the add read whatever the VGPRs held before the loads landed); the same graph
recompiled into a fresh cache: 0 disagree. The static check refuses the planted dump at exactly that
instruction (`V_ADD_CO_U32 reads v2 while a vector load to it is outstanding`).

The segmented reduction and scan kernels add the scalar loop/control-flow subset (`s_add_u32`,
`s_addc_u32`, `s_sub_i32`, `s_max_u32`, `s_xor_b32`, `s_mul_i32`, `s_mul_hi_u32`, `s_or_b64`,
`s_andn2_b64`, `s_cselect_b64`, `s_bfm_b64`, `s_and_saveexec_b64`, `s_cmp_eq_i32`, `s_branch`,
`s_cbranch_scc0`, `s_cbranch_scc1`, `s_cmp_lg_i32`, `s_cmp_ge_u32`, `s_getpc_b64`,
`s_or_b32`, `s_nop`) and `v_readfirstlane_b32`, `v_min_u32`, `v_lshrrev_b32`,
`v_add_lshl_u32`, `v_cmp_ge_u32`. These follow the same pinned gem5 bodies, with new differential
vectors exercising zero/all-active EXEC, lane 32 and lane 63 alone, scalar carry-in/out, and signed
subtraction overflow. `s_mul_i32`'s reference widens its signed operands before multiplying to avoid
C++ signed-overflow undefined behavior while preserving the low product bits. The shared `addCi`,
`mulLo` and `mulHi` functions also serve the scalar operations; their existing arithmetic theorems
therefore apply to these results.

`S_INST_PREFETCH` has no Vega twin. The [AMD RDNA2 manual, section 12.5](https://www.amd.com/content/dam/amd/en/documents/radeon-tech-docs/instruction-set-architectures/rdna2-shader-instruction-set-architecture.pdf)
defines it as changing instruction-cache prefetch distance: modes 1–3, with all other bits zero.
Those modes leave the functional state unchanged; reserved modes are refused. `V_READFIRSTLANE_B32`
(section 12.8) writes its scalar destination even with EXEC zero, selecting lane zero in that case;
otherwise it reads the lowest active lane. LDS-direct sources remain refused. The XML already
classifies its destination as scalar, so the wait checker follows the vector-load dependency into
the scalar consumer without an instruction-specific exception.

The large folds additionally emit `S_LSHL3_ADD_U32`, following manual section 12.1's shifted sum
and unsigned overflow flag; the pinned Vega model has no twin. `S_GETPC_B64` returns the byte address
of the next instruction (manual 12.3, checked against gem5); the checker relocates a stage's code
origin to zero. Mesa's embedded constant pool is preserved as `.data BYTE_OFFSET DWORD...` records,
with exact offsets including the compiler's end-of-code marker padding. The checker loads those
bytes into read-only memory for that stage, refuses unaligned/overlapping records or records reaching
the host buffers, and removes the pool before the next stage. Dropping a pool therefore cannot fall
back to an earlier stage's data. Stage 4 also flips descriptor words' low bits until an executed value or address mismatch
is observed for each workload that reads the pool, reporting its stage and byte offset. Empty
segments can leave individual words unobserved. If all mutations survive, complete removal of the
pool must still replay correctly before the gate reports it unread on this vector suite; that is
an inapplicable negative, not a successful mutation or a universal unreachability claim. Mesa
retains such an unused pool after unrolling `soac-boundaries`, whose twelve vectors still replay
with all `.data` removed. Parse failures never count as successful mutations.

Serial compiler loops need a runtime allowance proportional to their inputs. The checker budgets
`16 * code_dwords + 64 * plan_words + 64` steps per wave; reaching that limit is still a refusal,
not a termination claim. The instruction, gem5, and output checks keep their existing meanings.
The wait-mutation gate searches every stage, using a scalar wait for empty folds whose only loads
are descriptors; a truly load-free dump is reported as having no applicable load-wait mutation.

The source-language fixtures also require `V_CMP_GT_U64` and `V_SUBREV_CO_U32`, following manual
sections 12.9/12.11 and their pinned gem5 VOPC/VOP3 bodies. Reversed subtraction reuses `subCo`
with exchanged operands, including the borrow bit, rather than adding a second arithmetic definition.

For repeat gate runs, `OBEND_GPU_ARTIFACTS` can point to an existing emission directory. Only graphs
kept as digests use it, and each use runs `sha256sum -c` against the committed digest before replay.
Committed small graph directories keep their existing path; an unset cache variable still emits
freshly, and an explicitly selected cache with missing or changed artifacts fails.
