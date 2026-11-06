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
program on the card. Measured 2026-11-06 on hbox's RX 6750 XT (RADV, Mesa 24.2.8): diamond, stage 0,
instruction 11 (`s_waitcnt vmcnt(0)`, the wait between the two `buffer_load_dwordx2` and the
`v_add_co_u32` that consumes them) planted; five runs, all 12 vectors disagree on each, with different
values every run (the add read whatever the VGPRs held before the loads landed); the same graph
recompiled into a fresh cache: 0 disagree. The static check refuses the planted dump at exactly that
instruction (`V_ADD_CO_U32 reads v2 while a vector load to it is outstanding`).
