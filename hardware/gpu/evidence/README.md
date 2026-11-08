# GPU kernel recovery evidence

The recovery runs have `resume-` prefixes. Unprefixed logs and `isa-final-stage-*`
are predecessor history and are not the basis for the final recovery result.

- `resume-merge-build.log`: named emitter, RDNA2, square and proof-check builds
  after integrating dev at `402378a` (including `2af7cf7`).
- `resume-merged-verify.log`: final merged GPU gate, including source-oracle
  regeneration, device comparison, planted shader faults and RADV extraction.
- `resume-merged-isa-*.log`: final ISA gate outcomes. Missing model instructions
  remain refusals, including the pinned Lean execution fixtures.
- `resume-square-*.log`: square byte/model checks and scoped external integration
  checks for the replacement array-routing fixture and shared field graph.
- `resume-source-checks.log`: source admission mutations.
- `resume-measurements.py` and `resume-measurements.log`: fresh artifact/hash,
  exact-output, timestamp, resource and batch-reset runs. Timing tables and raw
  CPU results are in `../baseline`; grades and resource-pressure outputs are in
  `../cost`. Fresh resource gate dword-hash check is
  `resume-resource-machine-gate.log`.
- `unsupported-isa.tsv`: static mnemonic inventory absent from the model,
  with graph names; it is not a claim each opcode was executed independently.

The report in `review/GPU-KERNELS-20261106.md` distinguishes proved refinements,
checked artifact/device agreement and measured timing/allocation observations.
