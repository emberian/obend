# Collective measurements and regression evidence

Runs made on hbox's RX 6750 XT / RADV under `swarm-build`, 2026-11-07–08.
These are the collective checkpoint runs, before the subsequent NTT proof refactor.
The revalidation manifest identifies the exact emitter binary and confirms all 18
measured source cases (61 plan/shader files) against the final pruned hierarchy.

- `timing-radv.json`: 18 uint64 add collective cases at 2^16, 2^20 and 2^24,
  with one segment or segments of length 32, plus three device-copy baselines.
  GPU timestamps cover all dispatches, after three warmups, with 31 samples;
  reset copies are outside the interval. NumPy 2.5.4 uses warm inputs and
  preallocated outputs. Upload, shader compilation and readback are excluded.
- `admission-single-24-add-inclusive.log`: source admission took 73.767 seconds;
  source plus G4 admission took 524.478 seconds for the timed 2^24 single scan.
  These costs are outside the device timestamp interval.
- `correctness-radv.json`: 72 cases, two vectors each, every output word checked;
  all four admitted word monoids, both scan modes, reductions, empty/irregular
  segments, and mixed short/long segments that exercise hierarchy pruning.
- `gates/soac.json`: the full SOAC pipeline's independent NumPy comparison.
  This has a different scope from the primitive timing matrix: GPU wall time
  from command encoding through completion (including any queued input copy) and
  CPU computation including allocations/Python dispatch. The JSON records the
  timing-scope correction; numerical measurements are unchanged.
- `gates/final-status.json` and logs: full GPU/source/SOAC/catgrad gates, both
  square routes, and each ISA stage. The original stale catgrad digest failure
  is retained alongside the successful complete rerun after regeneration.

ISA stages 1/3/5 pass; 2/4/6 fail on the pre-existing DS rendering, V_CMP_LT_U32
semantics and DS counter gaps. No Rdna2 model files were changed. Timing was on a
shared host, without an exclusive-device or end-to-end application speedup claim.

`source-convergence/` retains the complete second gate run after the block-source
emitter integration and static NTT refactor: all non-ISA gates pass, registered
artifacts remain identical, and the same three ISA model stages remain red.

`proofs/final-axioms.log` and `proofs/FinalAxioms.lean` retain the closed public
NTT, Core4/GPU, field, collective and race-freedom axiom audit. Build summaries
include hashes and paths for the full hbox logs. Fresh source-admission checks
pass; the fresh Rdna2 compiled pins remain red with the model gaps above.
