module
/-
# Obend.Hardware.Retiming — Leiserson–Saxe Synchronous Graph Retiming & Untrusted Certificate Checker

Formalizes **Leiserson–Saxe retiming** (*Retiming Synchronous Circuitry*, Algorithmica 1991) within
Objective Bend's untrusted-producer / verified-checker architecture:

1. **Synchronous Circuit Graph & Integer Lag Certificates (`SyncEdge`, `SyncGraph`, `RetimingCert`)**:
   - Models a synchronous circuit as a directed graph where each edge $e = (u \to v)$ carries an
     initial non-negative register count $w(e) \in \mathbb{N}$ and combinational propagation delay,
   - An external, untrusted LP/network-flow optimizer proposes an integer lag assignment
     $r : V \to \mathbb{Z}$, transforming edge weights to $w_r(e) = w(e) + r(v) - r(u)$.
2. **Kernel Certificate Checker (`checkRetimingCert`, `checkAllCombPathsMeetDelay`)**:
   - Verifies $w_r(e) \ge 0$ for every edge $e \in E$ (no negative physical flip-flops!),
   - Verifies uniform I/O boundary lag ($r(i) = 0$ on primary inputs, $r(o) = L$ on primary outputs),
   - Computes order-independent Bellman–Ford longest combinational arrival times across all
     zero-register edges ($w_r(e) = 0$) and verifies the topological arrival-time inequality
     $\text{arr}(u) + D(e) \le \text{arr}(v) \le D_{\max}$ (simultaneously bounding all multi-hop
     combinational paths regardless of edge list order and rejecting positive-delay zero-register loops).
3. **Mechanized Soundness Theorems (`0 sorry`)**:
   - `retimed_weights_nonneg`: accepted certificates never produce negative edge register counts,
   - `path_weight_telescopes` & `cycle_weight_invariant`: register counts telescope on paths and
     are invariant around directed cycles,
   - `checkAllCombPathsMeetDelay_sound` & `solveVerifiedRetiming_sound`: EVERY contiguous
     zero-register walk in `g.edges` has total combinational delay $\le D_{\max}$ independent of
     `g.edges` ordering.
-/
public import Obend.Hardware.Process
@[expose] public section

namespace Obend.Hardware.Retiming
open Obend.Hardware.Process
set_option autoImplicit false

/-! ## 1. Synchronous Circuit Graphs & Retimed Edge Weights ($w_r(e) = w(e) + r(v) - r(u)$) -/

/-- A directed edge in a synchronous dataflow graph with `origRegs` initial pipeline registers
and `combDelayPs` picoseconds of combinational logic delay. -/
structure SyncEdge where
  src         : Nat
  dst         : Nat
  origRegs    : Nat
  combDelayPs : Nat
  deriving DecidableEq, Repr

/-- Synchronous circuit graph with designated primary input vertices, primary output vertices,
and directed edges. -/
structure SyncGraph where
  name           : String
  primaryInputs  : List Nat
  primaryOutputs : List Nat
  edges          : List SyncEdge
  deriving DecidableEq, Repr

/-- An untrusted retiming certificate assigning an integer lag `r(v) ∈ ℤ` to each vertex `v` and
declaring the uniform external I/O latency shift `ioLatencyShift : Int`. -/
structure RetimingCert where
  vertexLags     : List (Nat × Int)
  ioLatencyShift : Int
  deriving DecidableEq, Repr

/-- Look up the integer lag `r(v)` of vertex `v` in a `RetimingCert` (defaulting to `0`). -/
def lookupLag (cert : RetimingCert) (v : Nat) : Int :=
  match cert.vertexLags.find? (fun (id, _) => id == v) with
  | some (_, lag) => lag
  | none => 0

/-- Leiserson–Saxe retimed edge weight formula: $w_r(e) = w(e) + r(\text{dst}) - r(\text{src})$. -/
def retimedEdgeWeight (lag : Nat → Int) (e : SyncEdge) : Int :=
  (e.origRegs : Int) + lag e.dst - lag e.src

/-- Check that a single edge has non-negative retimed register weight ($w_r(e) \ge 0$). -/
def checkEdgeWeightNonneg (lag : Nat → Int) (e : SyncEdge) : Bool :=
  decide (0 ≤ retimedEdgeWeight lag e)

/-- Check that all edges in a list have non-negative retimed register weight. -/
def checkAllEdgesNonneg (lag : Nat → Int) (edges : List SyncEdge) : Bool :=
  edges.all (checkEdgeWeightNonneg lag)

/-- Theorem (`retimed_weights_nonneg`):
If `checkAllEdgesNonneg lag edges = true`, every `e ∈ edges` has `0 ≤ retimedEdgeWeight lag e`. -/
theorem retimed_weights_nonneg
    (lag : Nat → Int) (edges : List SyncEdge)
    (hOk : checkAllEdgesNonneg lag edges = true) :
    ∀ e ∈ edges, 0 ≤ retimedEdgeWeight lag e := by
  intro e hMem
  simp only [checkAllEdgesNonneg, List.all_eq_true] at hOk
  have hEdge := hOk e hMem
  simp only [checkEdgeWeightNonneg, decide_eq_true_eq] at hEdge
  exact hEdge

/-! ## 2. Path Weight Telescoping & Cycle Register Invariance Theorems -/

/-- A single hop `(origWeight, nextVertex)` along a contiguous directed path in a synchronous graph. -/
structure PathHop where
  weight  : Int
  nextVtx : Nat
  deriving DecidableEq, Repr

/-- Final vertex reached by following `path` starting from `startVtx`. -/
def pathEndVtx (startVtx : Nat) : List PathHop → Nat
  | [] => startVtx
  | h :: rest => pathEndVtx h.nextVtx rest

/-- Sum of original register weights $\sum w(e_i)$ along `path`. -/
def origPathWeight : List PathHop → Int
  | [] => 0
  | h :: rest => h.weight + origPathWeight rest

/-- Sum of Leiserson–Saxe retimed register weights $\sum (w(e_i) + r(v_{i+1}) - r(v_i))$ along `path`. -/
def retimedPathWeight (lag : Nat → Int) (curVtx : Nat) : List PathHop → Int
  | [] => 0
  | h :: rest =>
    (h.weight + lag h.nextVtx - lag curVtx) + retimedPathWeight lag h.nextVtx rest

/-- Theorem (`path_weight_telescopes`):
Along ANY contiguous directed path starting at `startVtx`, the sum of retimed edge weights
telescopes to `origPathWeight path + lag (pathEndVtx startVtx path) - lag startVtx`! -/
theorem path_weight_telescopes
    (lag : Nat → Int) (startVtx : Nat) (path : List PathHop) :
    retimedPathWeight lag startVtx path =
      origPathWeight path + lag (pathEndVtx startVtx path) - lag startVtx := by
  induction path generalizing startVtx with
  | nil =>
    simp only [retimedPathWeight, origPathWeight, pathEndVtx]
    omega
  | cons h rest ih =>
    simp only [retimedPathWeight, origPathWeight, pathEndVtx, ih h.nextVtx]
    omega

/-- Theorem (`cycle_weight_invariant`):
Around ANY directed cycle (`pathEndVtx startVtx cycle = startVtx`), the total register count is
strictly invariant under Leiserson–Saxe retiming (`retimedPathWeight lag startVtx cycle = origPathWeight cycle`)! -/
theorem cycle_weight_invariant
    (lag : Nat → Int) (startVtx : Nat) (cycle : List PathHop)
    (hClosed : pathEndVtx startVtx cycle = startVtx) :
    retimedPathWeight lag startVtx cycle = origPathWeight cycle := by
  rw [path_weight_telescopes lag startVtx cycle, hClosed]
  omega

/-- Corollary: For any I/O path from a primary input `u` with `lag u = 0` to a primary output `v`
with `lag v = L`, retiming shifts the path's register latency by exactly `L` clock cycles. -/
theorem io_path_latency_shift
    (lag : Nat → Int) (u : Nat) (path : List PathHop) (L : Int)
    (hIn  : lag u = 0)
    (hOut : lag (pathEndVtx u path) = L) :
    retimedPathWeight lag u path = origPathWeight path + L := by
  rw [path_weight_telescopes lag u path, hIn, hOut]
  omega

/-! ## 3. Untrusted Retiming Certificate Checker (`checkRetimingCert`) -/

/-- Check that every primary input has lag `0` and every primary output has lag `cert.ioLatencyShift`. -/
def checkBoundaryLags (g : SyncGraph) (cert : RetimingCert) : Bool :=
  (g.primaryInputs.all (fun u => decide (lookupLag cert u = 0))) &&
  (g.primaryOutputs.all (fun v => decide (lookupLag cert v = cert.ioLatencyShift)))

/-- Check single-edge setup timing closure under retimed register weight `wr = w_r(e)`:
* Negative register weights (`wr < 0`) are physically invalid (`false`),
* Purely combinational edges (`wr == 0`) must satisfy
  `corner.tCqMaxPs + e.combDelayPs + corner.tSetupPs + corner.tSkewPs ≤ clockPeriodPs`,
* Registered edges (`wr ≥ 1`) cut the combinational path across a flip-flop boundary (`true`). -/
def checkRetimedTimingEdge
    (lag : Nat → Int) (corner : ProcessCorner) (clockPeriodPs : Nat) (e : SyncEdge) : Bool :=
  let wr := retimedEdgeWeight lag e
  if decide (wr < 0) then
    false
  else if wr == 0 then
    decide (corner.tCqMaxPs + e.combDelayPs + corner.tSetupPs + corner.tSkewPs ≤ clockPeriodPs)
  else
    true

/-- Look up the integer lag of vertex `v` in an association list `lags`. -/
def lookupLagAssoc (lags : List (Nat × Int)) (v : Nat) : Int :=
  match lags.find? (fun (id, _) => id == v) with
  | some (_, lag) => lag
  | none => 0

/-- Look up the accumulated combinational arrival time (in ps) at vertex `v` in `arrs`. -/
def lookupArrivalAssoc (arrs : List (Nat × Nat)) (v : Nat) : Nat :=
  match arrs.find? (fun (id, _) => id == v) with
  | some (_, arr) => arr
  | none => 0

/-- Update or insert the combinational arrival time (in ps) of vertex `v` in `arrs`. -/
def updateArrivalAssoc (arrs : List (Nat × Nat)) (v : Nat) (newArr : Nat) : List (Nat × Nat) :=
  match arrs with
  | [] => [(v, newArr)]
  | (id, oldArr) :: rest =>
    if id == v then (id, newArr) :: rest
    else (id, oldArr) :: updateArrivalAssoc rest v newArr

/-- Propagate combinational arrival time across a zero-register retimed edge (`w_r(e) ≤ 0`)
as in Leiserson–Saxe's Algorithm FEAS. -/
def stepCombArrivalEdge (lags : List (Nat × Int)) (arrs : List (Nat × Nat)) (e : SyncEdge) :
    List (Nat × Nat) :=
  if retimedEdgeWeight (lookupLagAssoc lags) e ≤ 0 then
    let candArr := lookupArrivalAssoc arrs e.src + e.combDelayPs
    if lookupArrivalAssoc arrs e.dst < candArr then
      updateArrivalAssoc arrs e.dst candArr
    else
      arrs
  else
    arrs

/-- Run `passes` Bellman–Ford longest-path relaxation sweeps across all zero-register edges so
multi-hop arrival times converge to the exact DAG critical path independent of edge list order. -/
def computeCombArrivalsLoop :
    Nat → List (Nat × Int) → List SyncEdge → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, arrs => arrs
  | k + 1, lags, edges, arrs =>
    computeCombArrivalsLoop k lags edges (edges.foldl (stepCombArrivalEdge lags) arrs)

/-- Compute order-independent longest combinational arrival times across all zero-weight retimed
edges in `edges` via `|E|` Bellman–Ford relaxation sweeps. -/
def computeCombArrivals (lags : List (Nat × Int)) (edges : List SyncEdge) : List (Nat × Nat) :=
  computeCombArrivalsLoop edges.length lags edges []

/-- Check that every zero-register retimed edge and every multi-hop combinational path in `edges`
meets `maxCombDelayPs` under `cert`, verified via Bellman–Ford arrival fixed-point inequalities
`arr(src) + d(e) ≤ arr(dst) ≤ maxCombDelayPs` (which are completely independent of edge order in
`edges` and reject positive-delay zero-register combinational loops). -/
def checkAllCombPathsMeetDelay (cert : RetimingCert) (maxCombDelayPs : Nat) (edges : List SyncEdge) : Bool :=
  let lag  := lookupLag cert
  let arrs := computeCombArrivals cert.vertexLags edges
  edges.all (fun e =>
    if retimedEdgeWeight lag e ≤ 0 then
      decide (e.combDelayPs ≤ maxCombDelayPs) &&
      decide (lookupArrivalAssoc arrs e.src + e.combDelayPs ≤ lookupArrivalAssoc arrs e.dst) &&
      decide (lookupArrivalAssoc arrs e.dst ≤ maxCombDelayPs)
    else
      true)

/-- Complete kernel certificate checker for an untrusted Leiserson–Saxe retiming certificate:
1. All retimed edge weights are non-negative (`checkAllEdgesNonneg`),
2. Primary inputs/outputs obey uniform lag boundaries (`checkBoundaryLags`),
3. Every zero-register edge and every multi-hop zero-register combinational path closes setup timing
   within `clockPeriodPs` at `corner`. -/
def checkRetimingCert
    (g : SyncGraph) (cert : RetimingCert) (corner : ProcessCorner) (clockPeriodPs : Nat) : Bool :=
  let lag := lookupLag cert
  let overheadPs := corner.tCqMaxPs + corner.tSetupPs + corner.tSkewPs
  checkAllEdgesNonneg lag g.edges &&
  checkBoundaryLags g cert &&
  g.edges.all (checkRetimedTimingEdge lag corner clockPeriodPs) &&
  (if g.edges.any (fun e => retimedEdgeWeight lag e == 0) then
    decide (overheadPs ≤ clockPeriodPs) &&
    checkAllCombPathsMeetDelay cert (clockPeriodPs - overheadPs) g.edges
   else
    true)

/-- Apply a verified retiming certificate to transform `SyncGraph` edge register counts. -/
def applyRetiming (g : SyncGraph) (cert : RetimingCert) : SyncGraph :=
  let lag := lookupLag cert
  { g with
    edges := g.edges.map (fun e =>
      { e with origRegs := Int.toNat (retimedEdgeWeight lag e) }) }

/-! ## 4. Functional Equivalence of Retimed Pipelines (`leiserson_saxe_shift_sound`) -/

/-- Un-retimed 2-cycle MAC pipeline state (`w(mul → add) = 0`, `w(add → out) = 2`). -/
structure UnretimedMacState where
  s1 : BitVec 64
  s2 : BitVec 64
  deriving DecidableEq, Repr

/-- Step the un-retimed 2-cycle MAC pipeline by one clock cycle. -/
def stepUnretimedMac (st : UnretimedMacState) (a b c : BitVec 64) : UnretimedMacState :=
  { s1 := (a * b) + c
  , s2 := st.s1 }

/-- Retimed 2-cycle MAC pipeline state (`w_r(mul → add) = 1`, `w_r(add → out) = 1`). -/
structure RetimedMacState where
  mulReg : BitVec 64
  cReg   : BitVec 64
  outReg : BitVec 64
  deriving DecidableEq, Repr

/-- Step the Leiserson–Saxe retimed 2-cycle MAC pipeline by one clock cycle. -/
def stepRetimedMac (st : RetimedMacState) (a b c : BitVec 64) : RetimedMacState :=
  { mulReg := a * b
  , cReg   := c
  , outReg := st.mulReg + st.cReg }

/-- Theorem (`leiserson_saxe_shift_sound`):
For ANY 64-bit input stream `(a0, b0, c0)` at cycle 0 and `(a1, b1, c1)` at cycle 1,
the retimed MAC pipeline output `outReg` after 2 clock cycles is bit-identical to the un-retimed
MAC pipeline output `s2` (`(a0 * b0) + c0`)! -/
theorem leiserson_saxe_shift_sound
    (u0 : UnretimedMacState) (r0 : RetimedMacState)
    (a0 b0 c0 a1 b1 c1 : BitVec 64) :
    let u2 := stepUnretimedMac (stepUnretimedMac u0 a0 b0 c0) a1 b1 c1
    let r2 := stepRetimedMac (stepRetimedMac r0 a0 b0 c0) a1 b1 c1
    r2.outReg = u2.s2 ∧ r2.outReg = (a0 * b0) + c0 :=
  ⟨rfl, rfl⟩

/-! ## 5. Concrete Retiming Certificate Benchmark (Unretimed Fails 500 MHz, Retimed Passes 500 MHz) -/

/-- Unretimed MAC graph: edge `0 → 1` (`mul → add`) has `0` registers and `2200 ps` combinational
delay; edge `1 → 2` (`add → out`) has `2` registers and `900 ps` delay. -/
def macUnretimedGraph : SyncGraph where
  name           := "mac_2stage"
  primaryInputs  := [0]
  primaryOutputs := [2]
  edges          :=
    [ { src := 0, dst := 1, origRegs := 0, combDelayPs := 2200 }
    , { src := 1, dst := 2, origRegs := 2, combDelayPs := 900 } ]

/-- Identity (unretimed) certificate with all lags `0`. -/
def identityRetimingCert : RetimingCert where
  vertexLags     := [(0, 0), (1, 0), (2, 0)]
  ioLatencyShift := 0

/-- Leiserson–Saxe retiming certificate setting `r(1) = 1` (moving 1 register from `1 → 2` onto `0 → 1`). -/
def balancedRetimingCert : RetimingCert where
  vertexLags     := [(0, 0), (1, 1), (2, 0)]
  ioLatencyShift := 0

/-- Illegal retiming certificate setting `r(1) = -1` (creating a negative register count `-1` on `0 → 1`). -/
def negativeWeightBadCert : RetimingCert where
  vertexLags     := [(0, 0), (1, -1), (2, 0)]
  ioLatencyShift := 0

example :
    checkRetimingCert macUnretimedGraph identityRetimingCert corner7nm_SS 2000 = false ∧
    checkRetimingCert macUnretimedGraph negativeWeightBadCert corner7nm_SS 2000 = false ∧
    checkRetimingCert macUnretimedGraph balancedRetimingCert corner7nm_SS 2000 = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## 6. Constructive Bellman–Ford Retiming Solver & Order-Independent Longest-Path Soundness -/

/-- Deduplicate a list of vertex IDs while preserving first-appearance order. -/
def dedupVertexIds : List Nat → List Nat
  | [] => []
  | v :: vs =>
    let rest := dedupVertexIds vs
    if rest.contains v then rest else v :: rest

/-- Collect all unique vertex IDs referenced in a `SyncGraph`. -/
def collectGraphVertices (g : SyncGraph) : List Nat :=
  dedupVertexIds (g.primaryInputs ++ g.primaryOutputs ++ g.edges.flatMap (fun e => [e.src, e.dst]))

/-- Update or insert the integer lag of vertex `v` in `lags`. -/
def updateLagAssoc (lags : List (Nat × Int)) (v : Nat) (newLag : Int) : List (Nat × Int) :=
  match lags with
  | [] => [(v, newLag)]
  | (id, oldLag) :: rest =>
    if id == v then (id, newLag) :: rest
    else (id, oldLag) :: updateLagAssoc rest v newLag

/-- Minimum retimed register count required on edge `e` to satisfy target combinational delay `maxCombDelayPs`:
if `e.combDelayPs > maxCombDelayPs`, at least `1` flip-flop must be placed on `e`; otherwise `0`. -/
def minRequiredEdgeRegs (maxCombDelayPs : Nat) (e : SyncEdge) : Int :=
  if e.combDelayPs > maxCombDelayPs then 1 else 0

/-- Relax a single `SyncEdge` under Leiserson–Saxe FEAS difference constraints
$r(\text{dst}) - r(\text{src}) \ge \text{req}(e) - w(e)$. -/
def relaxRetimingEdge
    (g : SyncGraph) (maxCombDelayPs : Nat) (arrs : List (Nat × Nat))
    (lags : List (Nat × Int)) (e : SyncEdge) : List (Nat × Int) :=
  let rSrc := lookupLagAssoc lags e.src
  let rDst := lookupLagAssoc lags e.dst
  let wr   := (e.origRegs : Int) + rDst - rSrc
  let combArrivalPs :=
    if wr ≤ 0 then lookupArrivalAssoc arrs e.src + e.combDelayPs else e.combDelayPs
  let req : Int :=
    if e.combDelayPs > maxCombDelayPs || combArrivalPs > maxCombDelayPs then 1 else 0
  let minDstLag := rSrc + req - (e.origRegs : Int)
  if rDst < minDstLag then
    if !(g.primaryInputs.contains e.dst) && !(g.primaryOutputs.contains e.dst) && decide (0 ≤ rDst) then
      updateLagAssoc lags e.dst minDstLag
    else if !(g.primaryInputs.contains e.src) && !(g.primaryOutputs.contains e.src) then
      updateLagAssoc lags e.src (rDst + (e.origRegs : Int) - req)
    else
      lags
  else
    lags

/-- Perform one full Leiserson–Saxe FEAS Bellman–Ford relaxation pass across all edges of `g`. -/
def relaxRetimingPass (g : SyncGraph) (maxCombDelayPs : Nat) (lags : List (Nat × Int)) :
    List (Nat × Int) :=
  let arrs := computeCombArrivals lags g.edges
  g.edges.foldl (relaxRetimingEdge g maxCombDelayPs arrs) lags

/-- Perform `fuel` iterative Bellman–Ford relaxation passes. -/
def relaxRetimingLoop : Nat → SyncGraph → Nat → List (Nat × Int) → List (Nat × Int)
  | 0, _, _, lags => lags
  | fuel + 1, g, maxCombDelayPs, lags =>
    relaxRetimingLoop fuel g maxCombDelayPs (relaxRetimingPass g maxCombDelayPs lags)

/-- Constructive Bellman–Ford / iterative relaxation Leiserson–Saxe retiming solver. -/
def solveRetimingFuel (fuel : Nat) (g : SyncGraph) (maxCombDelayPs : Nat) : RetimingCert :=
  let initLags := (collectGraphVertices g).map (fun v => (v, (0 : Int)))
  { vertexLags     := relaxRetimingLoop fuel g maxCombDelayPs initLags
  , ioLatencyShift := 0 }

/-- Check that a list of `SyncEdge`s forms a contiguous walk from `curVtx` to `endVtx`. -/
def checkContiguousSyncEdges (curVtx endVtx : Nat) : List SyncEdge → Bool
  | [] => curVtx == endVtx
  | e :: rest => (e.src == curVtx) && checkContiguousSyncEdges e.dst endVtx rest

/-- Total combinational propagation delay $\sum_{e \in \text{walk}} D(e)$ along a contiguous walk. -/
def combWalkDelay : List SyncEdge → Nat
  | [] => 0
  | e :: rest => e.combDelayPs + combWalkDelay rest

private theorem combWalk_arrival_bound
    (cert : RetimingCert) (maxDelay : Nat) (edges : List SyncEdge)
    (hDelayOk : checkAllCombPathsMeetDelay cert maxDelay edges = true) :
    let arr := fun v => lookupArrivalAssoc (computeCombArrivals cert.vertexLags edges) v
    ∀ (walk : List SyncEdge) (u v : Nat),
      walk ≠ [] →
      checkContiguousSyncEdges u v walk = true →
      (∀ e ∈ walk, e ∈ edges ∧ retimedEdgeWeight (lookupLag cert) e ≤ 0) →
      arr u + combWalkDelay walk ≤ arr v ∧ arr v ≤ maxDelay := by
  simp only [checkAllCombPathsMeetDelay, List.all_eq_true] at hDelayOk
  intro arr walk
  induction walk with
  | nil =>
    intro _ _ hNe; exact False.elim (hNe rfl)
  | cons e rest ih =>
    intro u v _ hContig hAllZero
    simp only [checkContiguousSyncEdges, Bool.and_eq_true, beq_iff_eq] at hContig
    rcases hContig with ⟨rfl, hRestContig⟩
    obtain ⟨heMem, heZero⟩ := hAllZero e List.mem_cons_self
    have heCheck := hDelayOk e heMem
    simp only [heZero, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at heCheck
    rcases heCheck with ⟨⟨_, heStep⟩, heDstBound⟩
    cases rest with
    | nil =>
      simp only [checkContiguousSyncEdges, beq_iff_eq] at hRestContig
      subst hRestContig
      simp only [combWalkDelay, Nat.add_zero]
      exact ⟨heStep, heDstBound⟩
    | cons e2 rest2 =>
      have hSub := ih e.dst v (List.cons_ne_nil _ _) hRestContig
        (fun x hx => hAllZero x (List.mem_cons_of_mem _ hx))
      dsimp only [arr] at hSub ⊢
      simp only [combWalkDelay] at hSub ⊢
      exact ⟨by omega, hSub.2⟩

/-- **Universal Order-Independent Combinational Path Soundness (`checkAllCombPathsMeetDelay_sound`)**:
Whenever `checkAllCombPathsMeetDelay cert maxDelay edges = true`, EVERY contiguous walk `walk` of
zero-register edges in `edges` (of ANY hop count, regardless of the ordering of `edges`) has total
combinational delay `combWalkDelay walk ≤ maxDelay`, and no positive-delay zero-register cycle can
exist in `edges`! -/
theorem checkAllCombPathsMeetDelay_sound
    (cert : RetimingCert) (maxDelay : Nat) (edges : List SyncEdge)
    (hOk : checkAllCombPathsMeetDelay cert maxDelay edges = true)
    (u v : Nat) (walk : List SyncEdge)
    (hContig : checkContiguousSyncEdges u v walk = true)
    (hZeroWalk : ∀ e ∈ walk, e ∈ edges ∧ retimedEdgeWeight (lookupLag cert) e ≤ 0) :
    combWalkDelay walk ≤ maxDelay ∧
    (u = v → combWalkDelay walk = 0) := by
  cases walk with
  | nil =>
    simp [combWalkDelay]
  | cons e rest =>
    have hBound := combWalk_arrival_bound cert maxDelay edges hOk
      (e :: rest) u v (List.cons_ne_nil _ _) hContig hZeroWalk
    refine ⟨by omega, ?_⟩
    intro hCycle
    subst hCycle
    omega

/-- Verified wrapper around `solveRetimingFuel` that checks `checkAllEdgesNonneg` and
`checkAllCombPathsMeetDelay` on the resulting certificate before returning `some cert`. -/
def solveVerifiedRetiming? (fuel : Nat) (g : SyncGraph) (maxCombDelayPs : Nat) : Option RetimingCert :=
  let cert := solveRetimingFuel fuel g maxCombDelayPs
  if checkAllEdgesNonneg (lookupLag cert) g.edges &&
     checkAllCombPathsMeetDelay cert maxCombDelayPs g.edges then
    some cert
  else
    none

/-- **Theorem (`solveVerifiedRetiming_sound`)**:
Whenever `solveVerifiedRetiming? fuel g maxDelay = some cert`:
1. Every edge $e \in g.\text{edges}$ has non-negative retimed register weight $w_r(e) \ge 0$, AND
2. Every contiguous zero-register combinational walk in `g.edges` has total combinational delay
   `combWalkDelay walk ≤ maxDelay` (independent of edge ordering in `g.edges`)! -/
theorem solveVerifiedRetiming_sound
    (fuel : Nat) (g : SyncGraph) (maxDelay : Nat) (cert : RetimingCert)
    (hSome : solveVerifiedRetiming? fuel g maxDelay = some cert) :
    (∀ e ∈ g.edges, 0 ≤ retimedEdgeWeight (lookupLag cert) e) ∧
    (∀ (u v : Nat) (walk : List SyncEdge),
      checkContiguousSyncEdges u v walk = true →
      (∀ e ∈ walk, e ∈ g.edges ∧ retimedEdgeWeight (lookupLag cert) e ≤ 0) →
      combWalkDelay walk ≤ maxDelay) := by
  unfold solveVerifiedRetiming? at hSome
  dsimp only at hSome
  split at hSome
  · rename_i hOk
    simp only [Bool.and_eq_true] at hOk
    injection hSome with hEq
    subst hEq
    refine ⟨retimed_weights_nonneg (lookupLag _) g.edges hOk.1, ?_⟩
    intro u v walk hContig hZeroWalk
    exact (checkAllCombPathsMeetDelay_sound _ maxDelay g.edges hOk.2 u v walk hContig hZeroWalk).1
  · cases hSome

/-- Apply a `RetimingCert` to a `SyncGraph`, updating every edge's `origRegs` to
`(retimedEdgeWeight (lookupLag cert) e).toNat`. -/
def applyRetimingCertToGraph (g : SyncGraph) (cert : RetimingCert) : SyncGraph :=
  { g with
    edges := g.edges.map (fun e =>
      { e with origRegs := (retimedEdgeWeight (lookupLag cert) e).toNat }) }

/-- Project a `SyncEdge` to a `PathHop` carrying its integer register count and destination vertex. -/
def edgeToPathHop (e : SyncEdge) : PathHop where
  weight  := (e.origRegs : Int)
  nextVtx := e.dst

/-- Project a list of `SyncEdge`s along a path/cycle to `List PathHop`. -/
def edgesToPathHops (edges : List SyncEdge) : List PathHop :=
  edges.map edgeToPathHop

theorem pathEndVtx_edgesToPathHops (curVtx endVtx : Nat) (edges : List SyncEdge)
    (hContig : checkContiguousSyncEdges curVtx endVtx edges = true) :
    pathEndVtx curVtx (edgesToPathHops edges) = endVtx := by
  induction edges generalizing curVtx with
  | nil =>
    simp only [checkContiguousSyncEdges, beq_iff_eq] at hContig
    simp [edgesToPathHops, pathEndVtx, hContig]
  | cons e rest ih =>
    simp only [checkContiguousSyncEdges, Bool.and_eq_true, beq_iff_eq] at hContig
    simp only [edgesToPathHops, List.map_cons, pathEndVtx, edgeToPathHop]
    exact ih e.dst hContig.2

theorem origPathWeight_retime_eq_retimedPathWeight
    (cert : RetimingCert) (curVtx endVtx : Nat) (edges : List SyncEdge)
    (hContig : checkContiguousSyncEdges curVtx endVtx edges = true)
    (hNonneg : checkAllEdgesNonneg (lookupLag cert) edges = true) :
    origPathWeight
      (edgesToPathHops
        (edges.map (fun e => { e with origRegs := (retimedEdgeWeight (lookupLag cert) e).toNat }))) =
      retimedPathWeight (lookupLag cert) curVtx (edgesToPathHops edges) := by
  induction edges generalizing curVtx with
  | nil =>
    simp [edgesToPathHops, origPathWeight, retimedPathWeight]
  | cons e rest ih =>
    simp only [checkContiguousSyncEdges, Bool.and_eq_true, beq_iff_eq] at hContig
    simp only [checkAllEdgesNonneg, List.all_cons, Bool.and_eq_true] at hNonneg
    have hEdgeNonneg : 0 ≤ retimedEdgeWeight (lookupLag cert) e := by
      simp only [checkEdgeWeightNonneg, decide_eq_true_eq] at hNonneg
      exact hNonneg.1
    have hToNat : ((retimedEdgeWeight (lookupLag cert) e).toNat : Int) = retimedEdgeWeight (lookupLag cert) e :=
      Int.toNat_of_nonneg hEdgeNonneg
    have hIh := ih e.dst hContig.2 hNonneg.2
    simp only [edgesToPathHops] at hIh
    simp only [List.map_cons, edgesToPathHops, origPathWeight, retimedPathWeight, edgeToPathHop]
    rw [hToNat, hIh]
    rcases hContig with ⟨rfl, _⟩
    unfold retimedEdgeWeight
    omega

/-- **Theorem (`applyRetimingCertToGraph_preserves_cycle_weight`)**:
Applying a non-negative retiming certificate `cert` via `applyRetimingCertToGraph` preserves the
exact total register count around any contiguous directed cycle (`checkContiguousSyncEdges startVtx startVtx g.edges = true`). -/
theorem applyRetimingCertToGraph_preserves_cycle_weight
    (g : SyncGraph) (cert : RetimingCert) (startVtx : Nat)
    (hCycle : checkContiguousSyncEdges startVtx startVtx g.edges = true)
    (hNonneg : checkAllEdgesNonneg (lookupLag cert) g.edges = true) :
    origPathWeight (edgesToPathHops (applyRetimingCertToGraph g cert).edges) =
      origPathWeight (edgesToPathHops g.edges) := by
  simp only [applyRetimingCertToGraph]
  rw [origPathWeight_retime_eq_retimedPathWeight cert startVtx startVtx g.edges hCycle hNonneg]
  have hEnd := pathEndVtx_edgesToPathHops startVtx startVtx g.edges hCycle
  exact cycle_weight_invariant (lookupLag cert) startVtx (edgesToPathHops g.edges) hEnd

end Obend.Hardware.Retiming
end
