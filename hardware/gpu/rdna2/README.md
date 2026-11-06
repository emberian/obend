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
