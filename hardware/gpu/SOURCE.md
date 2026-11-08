# Source programs on the GPU

The array frontend accepts immutable, lexically scoped programs with pointwise maps,
gathers, concatenation, literals, reductions, and inclusive/exclusive scans, including
segmented forms. The scalar carrier is a 64-bit wrapping word. The design and literature
references are in [the frontend review](../../review/GPU-FRONTEND-20261106.md).

## From a surface program

[`source/Affine.obend`](source/Affine.obend) is an ordinary Objective Bend record/spec
composition. Its `run` method spells out word arithmetic:

```text
(((x * 3n) % 18446744073709551616n) + 5n) % 18446744073709551616n
```

Build the named `obend` and `obend-emit-gpu` executables, then run these commands from
the repository root (with the binaries on `PATH`):

```sh
obend check hardware/gpu/source/Affine.obend
obend run hardware/gpu/source/Affine.obend small       # result: 26
obend run hardware/gpu/source/Affine.obend boundary    # result: 2 at x = 2^64 - 1
obend emit hardware/gpu/source/Affine.obend --object affine \
  --out /tmp/affine.book.json --call run 7
obend-emit-gpu leaf /tmp/affine.book.json run \
  hardware/gpu/source/Affine.inputs.json --out /tmp/affine-gpu
obend-gpu-run /tmp/affine-gpu
```

The signed input `-1` stores the same word as the source natural `2^64 - 1`.
`verify_source.sh` requires this full source-file path, including original source
execution, ordinary book emission, independent integer reference results and a planted
GPU output mismatch. Set `OBEND_BIN`, `OBEND_EMIT_GPU`, and `OBEND_GPU_RUN` to select
built executables; the source driver is required, not silently skipped.

## A book file

For a small generated book in the same wire format, the separate
`obend-emit-gpu leaf-example --out /tmp/gpu-book-example` command writes
`example.book.json` and `inputs.json`. The gate also tests this lower-level file boundary.

`leaf BOOK MEMBER INPUTS --out DIR` reads the existing JSON book format emitted by
`obend emit` or `obend lower --emit`. It decodes the pinned `composition`, checks closure,
and re-emits it; independently printed book definitions cannot override that composition.
The selected unary scalar member is mapped over each input array. `INPUTS` is a JSON
list of equally sized arrays of signed integers; each row is a separate test vector.
Storage is modulo 2^64, with signed decimal notation at the file boundary.

This CLI recognizes the scalar Core4 fragment implemented by `Source.compileMember`.
Wrapping arithmetic must be explicit in the term; unbounded natural addition is refused.
Unknown members, unsupported operators, open terms and incompatible input shapes fail
before a plan is written. `leaf-example` exports a wrapping `3*x+5` member in the book
wire format; the surface fixture above exercises the ordinary source parser and emitter too.

## Whole-array members

The reusable Lean API is `ArrayMember.checkMember C member program inputLengths`.
`program` is lexical source syntax, not a graph. The checker verifies that the selected
member of the closed composition `C` is exactly the compact Core4 encoding of that
syntax, verifies lexical scope, and returns a `Plan` containing a shape/type derivation.
This is translation validation with a source syntax witness. There is not yet a parser
that recovers arbitrary array SOAC syntax from an exported Core4 book file.

`ArrayPrograms` constructs lexical array programs. Field multiplication reuses the sole
`GoldilocksSource`/`ArrayBuild` construction: `ArrayReify.reify` recovers source bindings and
checks exact structural round-trip equality (ignoring diagnostic operation labels).
`Reified.eval_sound` proves accepted reification preserves that builder's semantics.
These programs become actual composition members and pass `checkMember` before emission;
there is no graph fallback. `SoacPrograms` uses the same checked source route. The typed
receipt also retains `layoutOk`, the executable check of live-buffer reuse and aliasing.

The sole NTT construction is `Gpu.Ntt.nttBlockProgram` in `ArrayKernel`. The lexical
fragment lacks indexed workgroup lanes, shared-memory phases and barriers. It therefore
does not produce this block NTT, and the theorem below does not cover the NTT. Block
programs have separate admission, lowering and phase-protocol theorems and device gates.
The shared limb arithmetic is proved; a full theorem connecting the monadic `glMul`
builder to field multiplication and a universal NTT-to-DFT theorem remain open.

The universal result is `ArrayMember.Plan.source_to_gpu_encoded`. For every accepted
plan and ordinary input arrays, under the stated shape and input-buffer relations,
`runProgram` returns the source evaluator's outputs, and observing each output element
of the actual Core4 composition member halts with that same word. The proof composes
`book_sound`, `Program.term_sound`, `compile_sound`, `GraphTyping.wf`, and
`lowerArrayToGpu_sound`. It does not assume an output correctness certificate or decide
a fixture. See the exact theorem in
[`ArrayMember.lean`](../../lean/Obend/Hardware/Gpu/ArrayMember.lean).

The theorem ends at `runProgram`. WGSL execution and decoded device instructions are
separate external gates; they are not claimed as a mechanized Vulkan compiler theorem.
`verify_source.sh` checks the file workflow with an independent modular-integer oracle,
requires a planted shader defect to cause a value mismatch, checks shift boundaries and
signed fixed-point numerators, and checks named refusals. `verify_gpu.sh` and
`isa_check.sh` cover the emitted programs and machine-code model.

`fixed q` records a binary scale; multiplication adds scales. There is no implicit
rounding, saturation or rescaling. The fixed-square gate interprets signed Q8 inputs and
Q16 results where those samples do not overflow; arbitrary words retain modular semantics.
