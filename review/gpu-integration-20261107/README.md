# Integration evidence

Fresh outputs from `/home/hbox/obend/frontend` on 2026-11-07 Pacific / 2026-11-08 UTC.
The report is [GPU-INTEGRATION-20261107.md](../GPU-INTEGRATION-20261107.md).
All builds and gates ran under `swarm-build`; no RDNA2 model files changed.

`build-summary.log` is the tail of the successful named build; the full output is
`/home/hbox/obend/frontend-integration/build-fixed.log`. Other files are raw gate or
measurement outputs. `soac-numpy.json` is the independent NumPy report.
`rdna2-runs.log` records Lake's cached success; `rdna2-runs-fresh.log` records the
required fresh elaboration failure against the new embedded artifacts. Only the
latter is evidence about the current pinned executions.

NTT benchmarks use the reset-sensitive batch runner, three warmups and 1024 timed
transforms. The separate Plonky3 logs include methodology and CPU thread counts.
Host and device timings have different scopes; the shared host was not isolated.
