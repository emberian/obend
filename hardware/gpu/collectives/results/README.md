# Collective measurements and regression evidence

Runs made on hbox's RX 6750 XT / RADV under `swarm-build`, 2026-11-07–08.
These are the collective checkpoint runs, before the subsequent NTT proof refactor.
The revalidation manifest identifies the exact emitter binary and confirms all 18
measured source cases (61 plan/shader files) against the final pruned hierarchy.

- `timing-radv.json`: 18 uint64 add collective cases at 2^16, 2^20 and 2^24,
  with one segment or segments of length32, plus three device-copy baselines.
  GPU timestamps cover all dispatches, after three warmups, with31 samples;
  reset copies are outside the interval. NumPy2.5.4 uses warm inputs and
  preallocated outputs. Upload, shader compilation and readback are excluded.
- `correctness-radv.json`:72 cases, two vectors each, every output word checked;
  all four admitted word monoids, both scan modes, reductions, empty/irregular
  segments, and mixed short/long segments that exercise hierarchy pruning.
- `gates/soac.json`: the full SOAC pipeline's independent NumPy comparison.
  This has a different scope from the primitive timing matrix: GPU submission
  through completion and CPU computation including allocations/Python dispatch.
- `gates/final-status.json` and logs: full GPU/source/SOAC/catgrad gates, both
  square routes, and each ISA stage. The original stale catgrad digest failure
  is retained alongside the successful complete rerun after regeneration.

ISA stages1/3/5 pass;2/4/6 fail on the pre-existing DS rendering, V_CMP_LT_U32
semantics and DS counter gaps. No Rdna2 model files were changed. Timing was on a
shared host, without an exclusive-device or end-to-end application speedup claim.
