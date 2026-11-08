# Vault performance measurements

Running ledger, 2026-11-08. These measurements do **not** establish the requested
`O(change · log(vault))` bound. Whole checkpoints are still read and written, and
the complete 10,000-record curves remain unfinished.

## Binaries and location

All measurements below ran on **hbox**, under `swarm-build`. The evidence directory is
`/othersys/home/hbox/obend-vaultperf-measure` (abbreviated `M` below).
Generated vaults are retained there, not committed.

| Binary | Source | SHA-256 |
|---|---|---|
| `M/obend-before-4ad39c7` | Exact `4ad39c7`, archived before edits; baseline build exited 0 | `549061d5d796ad1bfdfb708991d8ee7c87a63787f80e999f3982f4b643daedcf` |
| `M/obend-after-build3` | Integrated first implementation, build3 exited 0 | `7a702e62b4040c21d6a575ed5e7caaea6910fc93b87f6d6e76ca2f049449257a` |
| `M/obend-after-build4` | Adds demand context and shared rendered worlds, build4 exited 0 | `fff4533f76509b1bd89e732c041506ac300f59066ece73f754c873b8468d044f` |
| `M/obend-after-build5` | Maintains the name index through multiwrite admission, build5 exited 0 | `0726bb5c6cf8e6c92e3ea8c557e3bfa129dac77a52b4e88a2db744f92195b098` |

Build commands were `SWARM_MEM_MAX=16G LEAN_NUM_THREADS=4 swarm-build lake build obend`
for the baseline, and the root's integrated builds. Build logs and exit files are in
`/othersys/home/hbox/obend-vaultperf-build/`, named `baseline-build.*`,
`integrated-build3.*`, `integrated-build4.*`, and `integrated-build5.*`.

Every new runner records binary identity and parameters in `run.json`, and every
completed command in `measurements.tsv`. Newer revisions also record output byte
counts and the harness hash. Earlier TSV schemas are retained when resumed; missing
columns must not be interpreted as measured zero. Each detached job has an adjacent
`.pid`, `.log`, and `.exit` (the exit file appears upon completion).

## What the Git baseline means

The runner creates a Git repository in the **same markdown directory**. After each
vault command it measures:

```sh
git status --porcelain --untracked-files=all -- '*.md'
git add -- '*.md'
git commit -q -m 'Markdown change'
```

`add` and `commit` run only if markdown changed. Git signing and hooks are disabled
for these generated repositories; `.obend` is excluded. A fork's Git snapshot is
seeded before its measured edits. Git numbers below include status plus add plus
commit when applicable. This measures persistence of the resulting markdown;
Git does not judge laws, preserve refused proposals, or explain a rejoin.

`ms` is the vault's `OBEND_COST` elapsed time. `wall` includes CLI process startup.
The Git gap uses **wall / Git elapsed**, not the smaller internal cost. All listed
large-vault samples replayed **0 records**, although the old runner's separate
`log` audit replays history.

## Scale samples: before and build3

The 2,000-page generator has 20 additional index pages; 20,000 has 200. Seed is 7.
Times are milliseconds. Genesis and unchanged rows use `before-2000`,
`before-20000`, `after-bursts-2000`, and `after-20000`. The 20k one-page before row
uses the identical initial snapshot in `before-bursts-20000`.

| Pages | Command | Before ms | Build3 ms | Build3 read bytes | Build3 wrote bytes | Build3 wall | Git | Gap |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 2,000 | Genesis | 17,603 | 17,615 | 185,755 | 1,784,714 | 17,895.14 | 214.86 | 83.3× |
| 2,000 | Unchanged open | 872 | 1,291 | 1,970,470 | 1,548,223 | 1,462.80 | 5.00 | 292.7× |
| 20,000 | Genesis | 1,410,888 | 512,880 | 1,906,938 | 18,013,397 | 513,209.18 | 1,977.71 | 259.5× |
| 20,000 | Unchanged open | 21,524 | 14,190 | 19,916,517 | 15,588,204 | 14,459.60 | 17.66 | 818.9× |
| 20,000 | One-page edit, record 3 | 96,761 | 18,884 | 17,557,453 | 15,588,501 | 19,086.17 | 76.68 | 248.9× |

For the 20k changed-page sample the judging phase falls from 76,051 ms to 3,466 ms.
The remaining cost includes hashing/encoding the world and reading/writing the
checkpoint; the write still emits about 15.6 MB. The change is useful, but its cost
is not independent of vault size.

## Rejoin curve: short history, 2,000 pages

These runs start at **2 records**, not 10,000. `before-bursts-2000` and
`after-bursts-2000` use the same seed, burst order, and batch size 10. A burst writes
across `min(B, 500)` pages while the tip tightens its laws and changes three pages.
Exit 1 is an expected partial refusal, recorded explicitly.

| Burst writes | Before merge ms | Build3 merge ms | Before read bytes | Build3 read bytes | Build3 wrote bytes | Build3 wall | Git | Gap |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 34,178 | 41,823 | 4,262,371 | 3,923,836 | 6,214,895 | 42,159.71 | 27.36 | 1,541× |
| 100 | 57,917 | 43,787 | 9,208,542 | 3,965,850 | 6,348,252 | 43,975.54 | 33.40 | 1,317× |
| 1,000 | 188,702 | 70,396 | 14,648,733 | 4,267,727 | 7,246,347 | 70,657.65 | 81.94 | 862× |
| 5,000 | Pending | Pending | — | — | — | — | — | — |

The 1,000-write results include the identical interrupted workload described below:
both binaries recorded a refused tip turn, then resumed after the same repair.
They are not clean fresh runs of the revised generator. The successful merges and
their Git comparisons are measured, not extrapolated.

## Build4 matched 20k probe

`stable-before-20000` was copied while holding the baseline vault's actual `FLOCK`
on `.obend/lock`, immediately after genesis. Its markdown had no subsequent external
edit. Both probes copy this same snapshot, measure an unchanged open, make the same
one-page edit, and measure another unchanged open (`steady`).

The build4 first open includes migration from the legacy log. The subsequent rows
measure its current format. Evidence: `probe-before-20000.{log,exit}` and
`probe-after4-20000.{log,exit}`, and each directory's `measurements.tsv`.

Both probes exited 0. Times are milliseconds; all replayed zero records.

| Operation | Before ms | Build4 ms | Before read bytes | Build4 read bytes | Build4 wrote bytes | Build4 wall | Git | Gap |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| First unchanged open, including build4 migration | 33,517 | 16,366 | 19,915,937 | 22,338,211 | 18,009,454 | 16,806.24 | 40.68 | 413.2× |
| Same one-page edit | 102,151 | 19,337 | 19,916,169 | 17,557,453 | 15,588,501 | 19,782.83 | 182.62 | 108.3× |
| Steady unchanged open | 29,668 | 15,524 | 19,916,683 | 17,557,967 | 15,588,387 | 15,823.75 | 34.00 | 465.4× |

The changed-page judging phase is 76,034 → 2,336 ms. The steady unchanged judging
phase is 7,744 → 101 ms. Whole-world work remains visible in the other phases.
These are build4 data, retained separately from the final build5 probes.

## Final build5: matched 2k and 20k probes

These fresh probes use `taskset -c 0` inside `swarm-build`, with an 8G cap. They run
sequentially: before and after at 2k, then before and after at 20k. Each pair copies
the same stable initial snapshot. The 2k snapshot has two records, so its edited
sample is record 4; the 20k snapshot has one record, so its edited sample is record
3. The first open migrates the old log on the new binary; the rows below are the
subsequent edit and steady unchanged open. All four probes exited 0.

| Pages | Operation | Before ms | Build5 ms | Build5 read bytes | Build5 wrote bytes | Build5 wall | Git | Gap |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 2,000 | One-page edit | 1,589 | 1,346 | 1,774,309 | 1,548,515 | 1,596.30 | 35.07 | 45.5× |
| 2,000 | Steady unchanged | 840 | 908 | 1,774,817 | 1,548,406 | 1,098.75 | 6.85 | 160.5× |
| 20,000 | One-page edit | 121,410 | 9,636 | 17,557,453 | 15,588,501 | 9,819.89 | 151.83 | 64.7× |
| 20,000 | Steady unchanged | 19,404 | 8,431 | 17,557,967 | 15,588,387 | 8,660.61 | 102.31 | 84.6× |

The edit's judging phase is 747 → 161 ms at 2k, and 97,500 → 1,408 ms at 20k.
Steady unchanged judging is 35 → 4 ms and 5,663 → 50 ms respectively. Every row
replays zero records. Bytes read and written still grow almost tenfold when the
number of pages grows tenfold, even for an unchanged open: the requested bound is
not met.

Evidence: `M/probe5-{before,after}-{2000,20000}.{log,exit}` and their fixture
directories' `measurements.tsv` and `run.json`. The latter now records inherited
CPU affinity. `M/scale5-probes.sh` is the exact sequential driver.

## Final build5: short-history 2k rejoin curve

These fresh runs copy `stable-before-2000/vault`, use the corrected workload,
start the burst sequence at three records, and run sequentially on CPU 0 with
an 8G cap. Both complete with exit 0. They are not the requested 10,000-record
curve. B10 merges 10 writes with zero refusals; B100 merges 98 writes with two
refusals. Both have three candidate sections.

| Burst writes | Before merge ms | Build5 merge ms | Before read bytes | Build5 read bytes | Build5 wrote bytes | Build5 wall | Git | Gap |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 38,705 | 8,105 | 4,263,024 | 3,924,296 | 6,214,892 | 8,251.04 | 21.09 | 391.3× |
| 100 | 64,382 | 19,424 | 9,209,194 | 3,966,285 | 6,348,252 | 19,781.76 | 64.22 | 308.1× |

Judging falls from 36,213 to 6,324 ms for B10 and from 62,311 to 16,485 ms
for B100. The measured improvement still leaves a large gap against Git and
whole-checkpoint work. Evidence: `M/short5-{before,after}-2000.{log,exit}` and
`measurements.tsv` in those directories. The shared driver is
`M/scale5-probes.sh`; its `scale5-probes.exit` is 0.

## The workload correction and resumption gate

The original generator restored cap 100 after each burst. This legitimately woke
previously refused balance-100 writes. At the next burst, cap 95 could not land
against those now-current balances. Both 2k runs therefore stopped at
`burst/1000/tip`, naming accounts P0130 and P1254. Treating that exit as success
would have measured a different law than the one the workload claimed.

The generator now brings current balances above 95 within that cap in the **same
judged turn** as the tightening. It changes only the numeric frontmatter field,
preserving bodies and candidates. The two stopped runs resumed at that phase;
their original failed attempts remain in the TSVs and original logs. Resume logs
are `before-bursts-2000-resume.log` and `after-bursts-2000-resume.log`.

`--resume` verifies binary identity, restores the recorded workload parameters,
reconstructs the deterministic RNG stream for completed phases, and skips their
effects. Its narrow runtime gate deliberately exited 17 before the second fork of
a 20-page, 4-record, two-burst run. After resume, `cmp` found its final log and
checkpoint byte-identical, and `diff` found all markdown identical, to the
uninterrupted run. Evidence: `resume-{reference,interrupted}.log` and
`resume-equivalence.exit` = 0. This is a runtime regression test, not a theorem.

Fifteen Python harness tests pass with `python3 lean/tests/vault/cost_harness.py`.
They cover missing/stale baseline coverage, an actual Git change and no-op,
retained measurements, segment byte counts, checkpoint counts, and preserving
body text during balance adjustment.
The additional sampling tests cover odd sample counts, retained samples, exact
coverage agreement, median elapsed time, conservative maxima for other metrics,
and refusing to replace a baseline after any functional failure.

## Walkthrough gates

The old runner silently excluded changed command sequences. In the original
24-step WORKSHOP run it excluded 13 steps. The new runner fails missing or changed
baseline rows and refuses to replace a baseline after a functional failure. A
successful comparison explicitly reports that **all** steps were compared.

SWARM also needed a real fixture repair: its retention example stopped at an
unrelated refused birth before creating its fork. Its expected output blessed
missing files. The revised scenario seeds the relevant admitted base, requires
the intended refusal, compares the pending file byte for byte after rejoin, and
checks status at the unchanged admitted version. Unicode character prefixes
replace GNU `cut -c`, which split UTF-8 and crashed the old runner. All 28 revised
steps pass on the unchanged baseline binary.

The same-host before totals were: WALKTHROUGH 1,611 ms (44 steps), TRANSPORT 435 ms
(24), REASONS 74 ms (15), SWARM 58,294 ms (28), FORMS 304 ms (23), and WORKSHOP
45,841 ms (24). The FORMS/WORKSHOP worker also recorded a contemporaneous baseline
repeat because the host load moved substantially; use its paired report for those
comparisons.

Build3 functional outputs pass for all of this worker's four documents. W/T/R
ordinary cost comparisons pass. SWARM's ordinary comparison is **red** at step 2:
status 143 → 444 ms. Its output still matches. The red is retained in
`SWARM-after-compare.log`; it was not overwritten or declared a pass.

Build5 W44/T24/R15 single-sample record and independent strict comparisons pass.
Its first single-sample SWARM comparison is red on five timing rows (7, 8, 9, 17,
18), with identical outputs and no byte/record regressions. Those logs remain
`SWARM-after5-{record,compare}.log`; they are not reported as passes.

The 2G cap was investigated rather than presumed responsible. The journal reports
120.7 MB peak memory for the recording scope (`run-u141028`) and 117.1 MB for the
comparison (`run-u141037`), far below 2G. Their CPU times were 18.938 and 31.028
seconds. The host's default `swarm-build` affinity spans P and E cores, but four
copied-vault status probes did not establish that as the cause: CPU 0 gave 855/819
ms and CPU 16 gave 726/773 ms, with identical bytes. Another CPU-0 probe took 470
ms, with zero major faults, 26,495 minor faults and substantial kernel CPU time.
Evidence is in `affinity-{p1,e1,e2,p2}.{cost,time}`, `affinity-perf.log` and
`affinity-strace.log`. The cause is not claimed to be isolated.

The final SWARM gate uses a predetermined **three fresh complete samples** for
recording, followed by an independent three fresh complete samples for comparison.
All 28 steps pass functionally in every sample. Step/command coverage must be
identical; elapsed milliseconds use the median, all other measures use the
maximum. The aggregate comparison passes all 28 steps. This is explicitly a
statistical gate, not a claim that the earlier single-sample comparison passed.
Both batches use CPU 0 and a 2G cap. Default runner behavior remains one sample.

Final recording/comparison is in `M/after5-tests/lean`. For W/T/R the commands were:

```sh
for doc in vault/WALKTHROUGH vault/TRANSPORT reasons/REASONS; do
  SWARM_MEM_MAX=2G swarm-build python3 -u tests/vault/walkthrough.py \
    --doc tests/$doc.md --cost-baseline
  # A separate ordinary run checks the recorded baseline:
  SWARM_MEM_MAX=2G swarm-build python3 -u tests/vault/walkthrough.py --doc tests/$doc.md
done
```

Actual runs serialize all record passes before all comparison passes. Each command
has `M/NAME-after5-{record,compare}.{log,exit}`. The root merges only these four
documents' rows from `after5-tests/lean/tests/vault/COST.baseline.tsv`, with
FORMS/WORKSHOP and CRASH/RETAIN from their owners. Independent workers never write
the same baseline file concurrently.

For SWARM, the final commands add `taskset -c 0` and `--cost-samples 3`, with
`--work M/swarm5-record-samples` and `--work M/swarm5-compare-samples` respectively.
Logs are `SWARM-after5-samples-{record,compare}.{log,exit}` (both exits 0).
Each sample retains its fixture, output, raw per-command costs and TSV; each batch
retains `aggregate.tsv`. Recorded/compared total milliseconds are W 1,666/1,636,
T 357/564, R 158/193, and SWARM 12,638/12,439 (the last sums step medians).

## Reproduction and unfinished work

From `M`, the full baseline jobs were launched as:

```sh
SWARM_MEM_MAX=16G swarm-build python3 -u large.py --work before-2000 \
  --binary ./obend-before-4ad39c7 --pages 2000 --records 10000 \
  --bursts 10,100,1000,5000 --every 100
SWARM_MEM_MAX=16G swarm-build python3 -u large.py --work before-20000 \
  --binary ./obend-before-4ad39c7 --pages 20000 --records 10000 \
  --bursts 10,100,1000,5000 --every 100
```

Their original harness includes a full `obend log` replay just to count records.
The new harness reads the successful command's checkpoint header instead;
full-log replay remains a separate acceptance gate. Both long-running original
jobs retain their original executable harness. Their completed open/write costs
are valid; neither full curve is finished.

Earlier short curves used `--records 2` at 2k or `--records 3` at 20k.
Final build5 short curves use the current `large-final.py` (a copy of repository
`large.py`) with `--records 3`, the stable 2k snapshot and `--bursts 10,100`. Snapshot probes use
`--from-vault stable-before-20000 --pages 20000 --records 3 --bursts ''`.
`probe.py` invokes that runner and appends one measured `steady` open. Both binary
paths and the snapshot path are recorded in each run's metadata.

At the pause, full-before-2k had completed `history/1152`;
full-before-20k was still auditing its initial history. Both have since resumed. At the sampled 96.8 seconds
per baseline 20k write, 10,000 writes would take about 11 days **if that rate held**.
This is an extrapolation, not a measurement or a completed gate.

The host was shared with other builds and benchmark jobs. During the later probes,
memory pressure reported about 8% full stall time over a minute, and Git latencies
also rose. Isolated small timing differences are not strong evidence of a speedup
or regression. Large structural changes in bytes read and judging time are stated
with their actual measurements; no uncontrolled timing result establishes an
asymptotic bound.

For final build5 cost gates, the six owned long-running benchmark runners and their
current CLI children were paused with `SIGSTOP`, each selected from its own PID
file and revalidated by argv, process start time and cgroup. No other jobs were
touched. `M/quiet-window-1794169821.json` records the identities and resumption
state; `python3 M/pause-benchmarks.py M/quiet-window-1794169821.json` validates those
same identities before `SIGCONT`.

The next measurement in each paused dataset includes waiting time and is excluded
from timing claims (data rows are one-based, excluding the header):

| Dataset | Excluded timing row |
|---|---:|
| `before-2000` | 1154 |
| `before-20000` | 3 |
| `before-bursts-2000` | 206 |
| `after-bursts-2000` | 328 |
| `before-bursts-20000` | 5 |
| `after-20000` | 7 |

The rows explicitly excluded above are not used in the reported tables. The
originally paused CLI children were released at 2026-11-08T20:44:43Z while their
Python parents remained stopped, allowing the current command to finish and
release its heap. Some commands continued through the final probe window; this
was not a host-wide idle benchmark. `M/release-children.py` and the manifest retain
those timestamps. All six runners resumed at **2026-11-08T21:04:48Z**. A subsequent
inspection of their recorded runner PIDs and each current `obend.pid` found **no
stopped owned process**; all twelve were in state S, with child worker threads
free to run.

The final binary's requested full curves were launched immediately after resuming
the old jobs. `M/full-after5.sh` serializes 2k then 20k, using CPU 0, a 16G cap,
the same seed and stable initial snapshots. Its detached driver PID is **877845**,
recorded in `M/full-after5.pid`; its transcript and eventual exit are
`M/full-after5.log` and `M/full-after5.exit`. The 2k stage is active and the 20k
stage is queued. `M/full-after5-plan.json` records both stages and the frozen
build5 SHA. Each stage keeps its own `.log`, eventual `.exit`, `run.json`,
`measurements.tsv`, and current `obend.pid`. There were 43 GB free on `/othersys`
at launch. These runs share the host with the resumed jobs; their eventual timing
interpretation must account for that contention.

The stage command, run by the serialized driver from `M`, is:

```sh
SWARM_MEM_MAX=16G swarm-build taskset -c 0 python3 -u large-final.py \
  --work full-after5-2000 --binary ./obend-after-build5 \
  --from-vault stable-before-2000/vault --pages 2000 --records 10000 \
  --bursts 10,100,1000,5000 --every 100
# The second stage substitutes full-after5-20000, stable-before-20000 and 20000.
```

The detached launch command was:

```sh
nohup sh -c 'bash full-after5.sh > full-after5.log 2>&1; echo $? > full-after5.exit' \
  </dev/null >/dev/null 2>&1 & echo $! > full-after5.pid
```

For continuation, inspect the driver/stage logs and exit files. Do not launch a
second copy while its recorded runner or command is active. If a stage ends after
a completed-command failure, `large-final.py --resume --work DATASET` restores the
recorded binary and parameters and continues the deterministic workload. The old
full-before jobs retain the old generator and may require this corrected runner
if they reach the cap-tightening failure described above. No full 10,000-record
before/after result is claimed here.

