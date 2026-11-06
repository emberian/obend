# Machines

Reach everything by the ssh alias in ~/.ssh/config (on the Mac). Keys live in ~/.ssh; never copy a private key
anywhere. Facts dated 2026-10-31.

## Ember's own machines

### The Mac (where you are)
- Apple silicon laptop; ember's working machine. Edit, `cargo check`, filtered macOS-runnable tests, single-file
  Lean (`lake env lean <file>`) on a warm `.lake`, Playwright (~/tools/playwright), cv.
- Not for: whole-tree Lean builds of big projects, long CPU jobs, anything that needs Linux.
- Travels: it may be on hotel or phone networks. Tailscale routes come and go; a box that "is down" may just be
  unreachable from here. Check from a second box before calling a machine down.
- Claude's hooks run this machine's binaries; a stale `~/.cargo/bin/cv` once blocked every lane (see RULES.md,
  Continuity).

### hbox (`ssh hbox` on the home LAN; `ssh hbox-saas` or `ssh hbox-remote` from anywhere)
- Home server: i9-12900 (24 threads: P-cores 0-15, E-cores 16-23), 123 GB RAM, ZFS.
  Disks: nvme root `/` (455 GB, usually 85-93% full: watch it), `/tank` HDD mirror (slow; old warm bases,
  candidates, evidence; put no new data there), `/othersys` SSD.
- For: Lean and Rust builds through `swarm-build`, journey and test worlds, long jobs. Shared with other projects
  (nanodregg, fn, codex lanes); everything there runs in parallel, so size memory caps so the sum stays under ~100 GB.
- `free` lies there: the ZFS ARC counts as used. Look at /proc/spl/kstat/zfs/arcstats and summed RSS before calling
  it busy.
- minidregg's unattended builder runs here (/home/hbox/lanes/integ, PID file builder.pid, start with builder-run.sh;
  see minidregg board/seats/build-loop.md). Its read-write deploy key for emberian/minidregg is ~/.ssh/minidregg-deploy
  (2026-10-15), used only to publish board/REDS.md, `green` and fixture rerecords. Lane pool: /home/hbox/pool, t1..t11.
- Its network drops sometimes (2026-10-31: unreachable for hours, then down around midday, back by 14:00). When it
  is unreachable, route nothing there: a seat told to certify on hbox lost its run when the box went. Check it
  answers before you point a job at it, and keep PID files there so a run survives the Mac roaming.

### persvati (`ssh persvati-lan` at home; `ssh persvati-remote` from anywhere, via the workhorse; slow hop)
- Ember's personal workstation: 24 cores, 83 GB RAM, nvme.
- For: quiet measurement (low background load), and overflow Lean/Rust builds under `/home/ember/mdpool`
  (minidregg's pool; budget ~80 GB, a `swarm.slice` memory cap). Approved for fn2 certifies too (ember,
  2026-10-31 evening): fn2 seats use a clone under their own directory in `/home/ember/mdpool`, PID files, the
  same memory discipline. `/tank/fn` there already holds an fn toolchain (acl2-8.7, sbcl, toolchains, images,
  scratch): qualify it before use (certify one known book and compare its .cert.out with forge's) and say so in
  the first READY from the box. From the Mac it answers only as `persvati-remote` (via the workhorse, a slow hop);
  `persvati-lan` works on the home LAN.
- Not for: system-wide changes, root setup, or anything outside your pool directory without ember's word. It's
  her personal machine.

### pug (`ssh pug` / `pug-p14s`, tailscale)
- Ember's homelab laptop; the future home of minidregg's re-genesis. Ask before using it.

### storagebox (`ssh storagebox`, port 23)
- Hetzner storage box: backups. Never write to it unless a task is explicitly about backups.

## Hetzner cloud (hcloud context `dregg`; every server costs money; see RULES.md)

### dregg-build2 (`ssh bb2` as user `build`; `ssh dregg-build2` as root)
- ccx53: 32 dedicated cores, 122 GB RAM, 564 GB nvme, Debian 13, fsn1. About EUR 1/hour, created 2026-10-31.
- Since 2026-10-31 evening it belongs to obend: minidregg moved back to hbox. The minidregg setup stays in place
  (unused) unless ember says otherwise: lane pool at /srv/pool (`. /srv/pool/pool.env; lane-tree acquire SEAT REF`),
  the unattended builder under /srv/integ, `swarm-build` with a 100 GB slice and a box-wide cap of 20 Lean
  compilers. Use the `build` user; root only for setup.
- The `build` user has a read-write deploy key for emberian/minidregg only (~/.ssh/minidregg_deploy, 2026-10-31),
  used by the builder to publish board/REDS.md and move `green`. Lanes still push their work from the Mac.
- obend: a clone at `~/obend/repo` as user `build` (branch `dev`), logs under `~/obend/logs`; shares the
  20-compiler cap with minidregg, so prefer hbox for obend when hbox is up.

### dregg-forge (`ssh dregg-forge`, root)
- cpx62: 16 vCPU, 32 GB, 534 GB. Shared:
  - minidregg's public demo (systemd-nspawn machine `demo`, demo.dregg.online; holds a deliberate bounty key:
    never touch it), `nano`, and `composed` (the gate's container). Reach containers via `ssh demo-dry`,
    `ssh nano-box`, `ssh composed-box` (jump through forge).
  - fn2's quiet measurement and nightly box (user `fn`): seat clones under `/build/lanes/<seat>`, PID files in each
    clone's `build/*.pid`, the nightly at `/build/nightly.sh` (cron 10:00 UTC = 03:00 Pacific; results under
    `/build/nightly/<date>-<sha>/`, `latest` a symlink). Its clock is UTC.
  - One shared certify lock: closures run one at a time, so a seat's long certify queues every other seat.
  - Container notes (infra, 2026-10-31): `demo` is user-namespaced (nspawn -U) with a host-side volume custodian
    (`demo-volume-custodian`, ROOT /var/lib/demo-grains prjquota ext4); `composed` is NOT user-namespaced (Stage A:
    host-mounted prjquota worlds volume /var/lib/composed-grains-host, no loop devices). Forge has no /dev/kvm (no
    microVM possible). Snapshots: `world-snap` in /var/lib/machines/pool. Recipes: dregg-infra edge/demo (board/seats/infra.md).
- Not for: builds. Heavy jobs there disturb fn2's measurements and the demo.

### dregg-workhorse (`ssh dregg-workhorse`, root)
- cx33, 4 vCPU, 7 GB: the LIVE EDGE. DelveTalk, the dregg edge node, headscale (it routes `*-remote` aliases),
  grafana/prometheus, the RustDesk relay, the Discord bot. Never a build or lane box; never restart services there
  without ember.

### dregg-anchor (`ssh dregg-anchor`, root)
- cx23: small anchor box. Holds the canonical dregg-infra git remote. Not for compute.

### Gone (aliases may still exist in ~/.ssh/config; don't use them)
- dregg-build (its address now belongs to forge), dregg-ref, dregg-demo: destroyed 2026-10-29.

## Other hosts in ~/.ssh/config
`vast`, `elidel`, `xprt-bench`, the `*.fg-goose.online` boxes, `hbox.lunar.town`, and git forges belong to other
projects or people. Don't use them without ember's explicit word for your task.
