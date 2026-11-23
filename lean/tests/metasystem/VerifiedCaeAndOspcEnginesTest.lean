import Obend.Hardware.PinoutEquiv
import Obend.Hardware.PlaneSweepDrcLvs
import Obend.Hardware.SmallSignalMna
import Obend.Hardware.DigitalFilterAndArray
import Obend.Hardware.OspcProver
import Obend.Hardware.YosysLec
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/VerifiedCaeAndOspcEnginesTest.lean`

Comprehensive verification, sharpness/completeness witnesses, planted-fault refutations,
SystemVerilog / `YosysLec` / Verilator RTL sanity checks, 12 `#tooth` kernel mutation-killing
witnesses, and `#assert_axioms_tree` whole-cone purity audit across all 5 Stage-3D greenfield
`LAW-M1` hardware & CAE engines:
1. **`Obend.Hardware.PinoutEquiv`**: IPC-7351B $D_4$-invariant pad/electrical/rail drop-in bijection
   (`checkPinoutIso_iff`), 256-bit `DetCbor` datasheet citation freshness & collision binding,
   `pinoutEquivJudge`, multi-turn digest revocation trace, and 3-way BOM co-design merge.
2. **`Obend.Hardware.PlaneSweepDrcLvs`**: $O((N+K)\log N)$ sorted X-event `.enter`-before-`.leave`
   plane-sweep DRC (`planeSweepDrcExec_eq_allPairsSpec`, exact boundary tie-breaking), rank-bounded
   `UnionFind` LVS (`checkLvsConnectivityExec_iff`), `planeSweepDrcLvsJudge`, and multi-turn layout trace.
3. **`Obend.Hardware.SmallSignalMna`**: $2n \times 2n$ block-real rational AC MNA Krawczyk/Neumann
   residual enclosure (`smallSignalMna_neumann_enclosure_sound`), `pelgrom_parallel_variance_invariance`,
   multi-frequency sweep trace, `smallSignalMnaJudge`, and preserved common-centroid + SAR ADC laws.
4. **`Obend.Hardware.DigitalFilterAndArray`**: Sharp $\ell_1$-norm FIR wordlength (`fir_l1_norm_wordlength_exact`
   tightness witness), folded symmetric FIR, cascaded `CIC → ShiftTrunc → FIR` zero-overflow,
   continuum Chebyshev Pell identity & `dolphChebyshev_sidelobe_bound`, and preserved `IqPhasor` / Rollett.
5. **`Obend.Hardware.OspcProver`**: 4-tile 2D Hypercube ($Q_2$) XOR-Butterfly `RtlMemModule` prover
   (`FaceIdeal4` `∂𝕀⁴ ≠ 𝕀⁴`, `ExprCAM`, `DiscrTreeLUT`, `DeltaNet`, `StreamLRAT`), 2-hop lockstep
   Sumcheck & canonical binary Merkle root folding, multi-cycle trace soundness, SV/SMT2/Verilator sanity.
-/

namespace Obend.Tests.Metasystem.VerifiedCaeAndOspcEnginesTest

open Obend
open Obend.Analysis
open Obend.Crypto
open Obend.Hardware.HDL
open Obend.Hardware.YosysLec
open Obend.Hardware.PinoutEquiv
open Obend.Hardware.PlaneSweepDrcLvs
open Obend.Hardware.SmallSignalMna
open Obend.Hardware.DigitalFilterAndArray
open Obend.Hardware.OspcProver

set_option autoImplicit false

-- ============================================================================
-- 1. `PinoutEquiv`: IPC-7351B D4 Bijection, 256-Bit DetCbor Cite & Judge
-- ============================================================================

def qfn4Base : FootprintPackageSpec :=
  { partNumber := "QFN4_LDO_BASE"
    courtyardWidthNm := 2000000
    courtyardLengthNm := 3000000
    pins := #[
      ⟨1, "VIN",  .powerIn 3300 3000 3600, ⟨-500000, -500000, 300000, 500000, 50000⟩⟩,
      ⟨2, "GND",  .gnd,                    ⟨ 500000, -500000, 300000, 500000, 50000⟩⟩,
      ⟨3, "CLKP", .diffPos 1,              ⟨ 500000,  500000, 300000, 500000, 50000⟩⟩,
      ⟨4, "CLKN", .diffNeg 1,              ⟨-500000,  500000, 300000, 500000, 50000⟩⟩
    ] }

/-- Second-source QFN-4 rotated by 90° (`rot = 1, mirrorX = false`) with swapped courtyard/aperture axes
    and reordered pin numbering (`[10, 11, 12, 13]`). -/
def qfn4AltRot90 : FootprintPackageSpec :=
  { partNumber := "QFN4_LDO_ALT90"
    courtyardWidthNm := 3000000
    courtyardLengthNm := 2000000
    pins := #[
      ⟨10, "CLKN_B", .diffNeg 1,              ⟨-500000, -500000, 500000, 300000, 50000⟩⟩,
      ⟨11, "VIN_B",  .powerIn 3300 2900 3700, ⟨ 500000, -500000, 500000, 300000, 50000⟩⟩,
      ⟨12, "GND_B",  .gnd,                    ⟨ 500000,  500000, 500000, 300000, 50000⟩⟩,
      ⟨13, "CLKP_B", .diffPos 1,              ⟨-500000,  500000, 500000, 300000, 50000⟩⟩
    ] }

/-- Bad swap: differential polarity swapped (`diffPos 1` vs `diffNeg 1` at rotated positions). -/
def qfn4BadPolarity : FootprintPackageSpec :=
  { qfn4AltRot90 with
    pins := (qfn4AltRot90.pins.set! 0 ⟨10, "CLKP_WRONG", .diffPos 1, ⟨-500000, -500000, 500000, 300000, 50000⟩⟩).set!
              3 ⟨13, "CLKN_WRONG", .diffNeg 1, ⟨-500000,  500000, 500000, 300000, 50000⟩⟩ }

#guard checkPinoutIso 400 10000 qfn4Base qfn4AltRot90 == true
#guard checkPinoutIso 400 10000 qfn4Base qfn4BadPolarity == false
#guard verifyPinoutBijection 400 10000 ⟨1, false⟩ qfn4Base qfn4AltRot90 #[1, 2, 3, 0] == true

theorem test_pinout_iso_completeness_and_refusal :
    PinoutDropInEquiv 400 10000 qfn4Base qfn4AltRot90 ∧
    ¬ PinoutDropInEquiv 400 10000 qfn4Base qfn4BadPolarity := by
  refine ⟨(checkPinoutIso_iff 400 10000 qfn4Base qfn4AltRot90).mp (by decide +kernel), ?_⟩
  intro hBad
  have hTrue := (checkPinoutIso_iff 400 10000 qfn4Base qfn4BadPolarity).mpr hBad
  have hFalse : checkPinoutIso 400 10000 qfn4Base qfn4BadPolarity = false := by decide +kernel
  rw [hFalse] at hTrue
  cases hTrue

/-- Universal semantic impossibility when `pinoutEquivJudge` refutes by stale 256-bit datasheet digest
    or `.obend` Vault smart-contract violation (`costCents = 320 > 250`). -/
def staleSwapObj : PinoutSwapObj :=
  { laws := defaultEdaLaws
    oldPart := baselineLdoPart
    newPart := secondSourceLdoPart
    pkgA := qfn4Base
    pkgB := qfn4AltRot90
    minMarginMv := 400
    padTolNm := 10000
    cite256 := { defaultDatasheetCite256 with currentDigest256 := 0xdeadbeef#256 }
    agentName := "procurement_scout"
    facts := defaultEdaFacts }

def overbudgetSwapObj : PinoutSwapObj :=
  { staleSwapObj with
    newPart := overbudgetSecondSourcePart
    cite256 := defaultDatasheetCite256 }

def validSwapObj : PinoutSwapObj :=
  { staleSwapObj with cite256 := defaultDatasheetCite256 }

def validSwapCert : PinoutSwapCert := ⟨⟨1, false⟩, #[1, 2, 3, 0]⟩

#guard checkPinoutSwap 0 validSwapObj validSwapCert == .ok
#guard checkPinoutSwap 0 staleSwapObj validSwapCert == .refused .staleDatasheetDigest []
#guard checkPinoutSwap 0 overbudgetSwapObj validSwapCert ==
  .refused (.vaultLawRefused "bom_budget" "bom_budget") []

theorem test_pinout_judge_refuted_impossible (c' : PinoutSwapCert) :
    ¬ PinoutSwapMeaning staleSwapObj c' ∧
    ¬ PinoutSwapMeaning overbudgetSwapObj c' :=
  ⟨pinoutEquivJudge.refuted (r := 0) (c := validSwapCert) (k := .staleDatasheetDigest) (p := [])
     (show checkPinoutSwap 0 staleSwapObj validSwapCert = .refused .staleDatasheetDigest [] by decide +kernel)
     rfl c',
   pinoutEquivJudge.refuted (r := 0) (c := validSwapCert)
     (k := .vaultLawRefused "bom_budget" "bom_budget") (p := [])
     (show checkPinoutSwap 0 overbudgetSwapObj validSwapCert =
       .refused (.vaultLawRefused "bom_budget" "bom_budget") [] by decide +kernel)
     rfl c'⟩

-- Multi-turn revision trace with digest revocation blocking rollback to revoked datasheet digest:
def revDigest1 : BitVec 256 := defaultDatasheetCite256.currentDigest256
def revDigest2 : BitVec 256 := 0xCAFE1234#256

def revInitState : PinoutRevisionState :=
  ⟨baselineLdoPart, qfn4Base, revDigest1, 0, []⟩

def revTurn1 : PinoutRevisionTurn :=
  ⟨secondSourceLdoPart, qfn4AltRot90, ⟨"TI", "v2", revDigest2, revDigest2⟩,
   400, 10000, defaultEdaLaws, "scout", defaultEdaFacts, true⟩

def revTurnRollback : PinoutRevisionTurn :=
  ⟨baselineLdoPart, qfn4Base, ⟨"TI", "v1", revDigest1, revDigest1⟩,
   400, 10000, defaultEdaLaws, "scout", defaultEdaFacts, false⟩

#guard (runPinoutRevisionTrace revInitState [revTurn1]).isSome == true
#guard runPinoutRevisionTrace revInitState [revTurn1, revTurnRollback] == none

-- ============================================================================
-- 2. `PlaneSweepDrcLvs`: Exact Tie-Breaking, O((N+K) log N) DRC & Union-Find LVS
-- ============================================================================

/-- Exact boundary sharpness check (`sep = 5`):
    `[0, 10]` vs `[15, 20]` is DRC-clean (`10 + 5 ≤ 15`),
    whereas `[0, 10]` vs `[14, 20]` violates spacing (`10 + 5 > 14`) and tests `.enter` before `.leave` at `x = 14`. -/
def drcExactTouchClean : Array LayoutBox2D :=
  #[⟨1, 0, 0, 10, 10⟩, ⟨1, 15, 0, 20, 10⟩]

def drcExactTieViolation : Array LayoutBox2D :=
  #[⟨1, 0, 0, 10, 10⟩, ⟨1, 14, 0, 20, 10⟩]

#guard planeSweepDrcExec 5 drcExactTouchClean == true
#guard allPairsDrcSpec 5 drcExactTouchClean.toList == true
#guard planeSweepDrcExec 5 drcExactTieViolation == false
#guard allPairsDrcSpec 5 drcExactTieViolation.toList == false

/-- Multi-layer Metal1 (`layer 1`) + Via1 + Metal2 (`layer 2`) LVS benchmark:
    Net 10 bridges Metal1 `[0,20]×[0,20]` through Via1 `[5,15]×[5,15]` to Metal2 `[0,20]×[0,60]`
    and back through Via1 `[5,15]×[45,55]` to Metal1 `[0,20]×[40,60]`;
    Net 20 is an isolated Metal1 island `[40,60]×[0,60]` (`sep ≥ 20`). -/
def lvsCleanShapes : Array LvsShape := #[
  ⟨⟨1,  0,  0, 20, 20⟩, 10⟩,
  ⟨⟨2,  0,  0, 20, 60⟩, 10⟩,
  ⟨⟨1,  0, 40, 20, 60⟩, 10⟩,
  ⟨⟨1, 40,  0, 60, 60⟩, 20⟩
]

def lvsCleanVias : Array LvsVia := #[
  ⟨⟨10, 5,  5, 15, 15⟩, 1, 2, 2⟩,
  ⟨⟨10, 5, 45, 15, 55⟩, 1, 2, 2⟩
]

-- LVS open fault: dropping the second via leaves shape 2 (`net 10`) physically disconnected from shape 0 (`net 10`).
#guard checkLvsConnectivityExec lvsCleanShapes lvsCleanVias == true
#guard checkLvsConnectivityExec lvsCleanShapes #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩] == false

-- Note on DRC+LVS: Metal1 shapes on Net 10 are at `y ∈ [0,20]` and `[40,60]` (`sep = 20 ≥ 10`),
-- and Metal2 is on `layer 2`, so `planeSweepDrcLvsJudge` accepts `(10, lvsCleanShapes, lvsCleanVias)`!
#guard checkDrcLvs 0 ⟨10, lvsCleanShapes, lvsCleanVias⟩ ⟨"sky130_fd_pr"⟩ == .ok
#guard checkDrcLvs 0 ⟨25, lvsCleanShapes, lvsCleanVias⟩ ⟨"sky130_fd_pr"⟩ == .refused .drcSpacingViolation []
#guard checkDrcLvs 0 ⟨10, lvsCleanShapes, #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩]⟩ ⟨"sky130_fd_pr"⟩ ==
  .refused .lvsConnectivityMismatch []

private theorem lvsOpenFault_exec_false :
    checkLvsConnectivityExec lvsCleanShapes #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩] = false := by
  cases h : checkLvsConnectivityExec lvsCleanShapes #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩] with
  | false => rfl
  | true =>
    have hBij := ((checkLvsConnectivityExec_iff lvsCleanShapes #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩]).mp h).2
    have hConn := (hBij 0 2 (by decide) (by decide)).mpr (by decide)
    have hEdges : extractPhysicalEdges lvsCleanShapes #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩] = [(0, 1)] := by
      decide +kernel
    rw [hEdges] at hConn
    have hInv : ∀ u v, GeomConnected 4 [(0, 1)] u v → (u < 2 ↔ v < 2) := by
      intro u v hc
      induction hc with
      | refl _ => exact Iff.rfl
      | edge _ _ hm => simp at hm; obtain ⟨rfl, rfl⟩ := hm; decide
      | symm _ ih => exact ih.symm
      | trans _ _ ih1 ih2 => exact ih1.trans ih2
    exact absurd ((hInv 0 2 hConn).mp (by decide)) (by decide)

theorem test_drc_lvs_judge_refuted (c' : DrcLvsCert) :
    ¬ DrcLvsMeaning ⟨25, lvsCleanShapes, lvsCleanVias⟩ c' ∧
    ¬ DrcLvsMeaning ⟨10, lvsCleanShapes, #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩]⟩ c' :=
  ⟨planeSweepDrcLvsJudge.refuted (r := 0) (c := ⟨"sky130_fd_pr"⟩) (k := .drcSpacingViolation) (p := [])
     (show checkDrcLvs 0 ⟨25, lvsCleanShapes, lvsCleanVias⟩ ⟨"sky130_fd_pr"⟩ =
       .refused .drcSpacingViolation [] by
       unfold checkDrcLvs; rw [planeSweepDrcExec_eq_allPairsSpec]; decide +kernel)
     rfl c',
   planeSweepDrcLvsJudge.refuted (r := 0) (c := ⟨"sky130_fd_pr"⟩) (k := .lvsConnectivityMismatch) (p := [])
     (show checkDrcLvs 0 ⟨10, lvsCleanShapes, #[⟨⟨10, 5, 5, 15, 15⟩, 1, 2, 2⟩]⟩ ⟨"sky130_fd_pr"⟩ =
       .refused .lvsConnectivityMismatch [] by
       unfold checkDrcLvs; rw [planeSweepDrcExec_eq_allPairsSpec, lvsOpenFault_exec_false]; decide +kernel)
     rfl c'⟩

-- ============================================================================
-- 3. `SmallSignalMna`: 2n×2n AC Neumann Enclosure, Pelgrom & SAR ADC
-- ============================================================================

/-- 2-node RC ladder AC MNA at $\omega = 1$:
    $G = \begin{bmatrix} 2 & -1 \\ -1 & 2 \end{bmatrix}$, $C = \begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}$. -/
def rc2MatG : List (List CanonicalRat) := [[2, -1], [-1, 2]]
def rc2MatC : List (List CanonicalRat) := [[1, 0], [0, 1]]
def rc2PrecondR : List (List CanonicalRat) := [
  [CanonicalRat.mk 1 2, CanonicalRat.mk 1 5, CanonicalRat.mk 1 4, 0],
  [CanonicalRat.mk 1 5, CanonicalRat.mk 1 2, 0, CanonicalRat.mk 1 4],
  [CanonicalRat.mk (-1) 4, 0, CanonicalRat.mk 1 2, CanonicalRat.mk 1 5],
  [0, CanonicalRat.mk (-1) 4, CanonicalRat.mk 1 5, CanonicalRat.mk 1 2]
]

#guard (acMatVecExec 2 #[#[2, -1], #[-1, 2]] #[#[1, 0], #[0, 1]] 1 #[1, 0, 0, 0]).toList ==
  Obend.Hardware.CircuitDae.matVecMulN 4 (buildAcBlockMatrix 2 rc2MatG rc2MatC 1) [1, 0, 0, 0]
#guard checkSmallSignalNeumannEnclosure 2 rc2MatG rc2MatC rc2PrecondR 1
  [CanonicalRat.mk 1 2, CanonicalRat.mk 1 5, CanonicalRat.mk (-1) 4, 0] [1, 0, 0, 0] 1 == true

theorem test_ac_mna_enclosure_and_pelgrom
    (vStar : List CanonicalRat)
    (hSol : ∀ i, i < 4 →
      Obend.Hardware.CircuitDae.vecEntry
        (Obend.Hardware.CircuitDae.matVecMulN 4 (buildAcBlockMatrix 2 rc2MatG rc2MatC 1) vStar) i =
      Obend.Hardware.CircuitDae.vecEntry [1, 0, 0, 0] i)
    (aVt area : CanonicalRat) (hArea : 0 < area)
    (p0 gx gy cxx cxy cyy px py : Int) :
    vecNormInf 4 (Obend.Hardware.CircuitDae.vecSubN 4 vStar
      [CanonicalRat.mk 1 2, CanonicalRat.mk 1 5, CanonicalRat.mk (-1) 4, 0]) ≤ 1 ∧
    pelgromParallelVariance aVt area 8 = pelgromVariance aVt area ∧
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 ∧
    prouhetThueMorseMismatch1D p0 gx cxx px = 0 := by
  have hEnc := smallSignalMna_neumann_enclosure_sound 2 rc2MatG rc2MatC rc2PrecondR 1
    [CanonicalRat.mk 1 2, CanonicalRat.mk 1 5, CanonicalRat.mk (-1) 4, 0] [1, 0, 0, 0] 1 (by decide +kernel)
  have hPel := pelgrom_octuple_preserves_variance_and_cancels_hessian aVt area hArea p0 gx gy cxx cxy cyy px py
  exact ⟨(hEnc.2 vStar hSol).2.1, hPel.1, hPel.2, prouhetThueMorse_cancels_linear_and_quadratic_bow p0 gx cxx px⟩

-- ============================================================================
-- 4. `DigitalFilterAndArray`: Sharp l1 FIR/CIC & Continuum Dolph–Chebyshev
-- ============================================================================

def symFirTaps : Array Int := #[3, -5, 7, -5, 3]

#guard firL1Norm symFirTaps.toList == 23
#guard firOutExec symFirTaps (firWorstSignal symFirTaps.toList 100 4) 4 == 2300
#guard firFoldedSymmetricExec symFirTaps (firWorstSignal symFirTaps.toList 100 4) 4 == 2300
#guard chebyshevTExec 6 (CanonicalRat.mk 3 5) == chebyshevT 6 (CanonicalRat.mk 3 5)
#guard checkDolphChebyshevDesign 8 (CanonicalRat.mk 6 5) 10 == true

theorem test_fir_sharpness_and_dolph_chebyshev
    (c : CanonicalRat) (hLo : -1 ≤ CanonicalRat.mk 6 5 * c) (hHi : CanonicalRat.mk 6 5 * c ≤ 1) :
    (∃ xWorst : Obend.Hardware.Cic.Signal,
      (∀ k, intAbs (xWorst k) ≤ 100) ∧
      firOut symFirTaps.toList xWorst 4 = 2300) ∧
    dolphChebyshevAF 8 (CanonicalRat.mk 6 5) c *
      dolphChebyshevAF 8 (CanonicalRat.mk 6 5) c ≤ 1 := by
  have hSharp := (fir_l1_norm_wordlength_exact symFirTaps.toList 100).2
  have hSlr := checkDolphChebyshevDesign_sound 8 (CanonicalRat.mk 6 5) 10 (by decide +kernel)
  refine ⟨?_, hSlr.2 c hLo hHi⟩
  obtain ⟨xw, hBnd, hEq⟩ := hSharp
  have hL1 : ((100 : Nat) : Int) * (firL1Norm symFirTaps.toList : Int) = 2300 := by decide +kernel
  have hLen : symFirTaps.toList.length - 1 = 4 := by decide +kernel
  rw [hLen, hL1] at hEq
  exact ⟨xw, hBnd, hEq⟩

-- ============================================================================
-- 5. `OspcProver`: 4-Tile Q2 Prover, SV/SMT2 Emission & Live Verilator/Yosys
-- ============================================================================

#guard checkRtlMemModuleW (ospcTileRtl 0) == true
#guard checkRtlMemModuleW (ospcTileRtl 1) == true
#guard checkRtlMemModuleW (ospcTileRtl 2) == true
#guard checkRtlMemModuleW (ospcTileRtl 3) == true

#guard ((emitMemModuleSV (ospcTileRtl 0)).splitOn "\n").any (·.startsWith "  (* ram_style = \"block\" *)")
#guard ((emitMemModuleSV (ospcTileRtl 3)).splitOn "\n").contains "endmodule"
#guard ((lecMemScript (ospcTileRtl 0)).print.splitOn "\n").any (·.startsWith "(define-fun |rtl_mem_cam_bank|")
#guard ((lecMemScript (ospcTileRtl 3)).print.splitOn "\n").any (·.startsWith "(define-fun |rtl_mem_clause_bank|")

/-- Host-aware live RTL tool sanity gate: when `verilator` or `yosys` is available on the build host
    (`hbox` / `bb2`), elaborate all 4 emitted SystemVerilog `OspcProver` tile modules (`tile0..tile3`)
    with `verilator --lint-only` and/or `yosys` `read_verilog -sv; hierarchy -check; proc`! -/
def findExecutable? (paths : List String) : IO (Option String) := do
  for p in paths do
    if ← (System.FilePath.mk p).pathExists then
      return some p
  return none

def verifyLiveOspcTilesRtlIfPresent : IO Unit := do
  let verilatorOpt ← findExecutable? ["/tmp/verilator-ok/bin/verilator", "/usr/bin/verilator", "/usr/local/bin/verilator"]
  let yosysOpt     ← findExecutable? ["/tmp/oss-cad-suite/bin/yosys", "/usr/bin/yosys", "/usr/local/bin/yosys"]
  if verilatorOpt.isSome || yosysOpt.isSome then
    let tmpDir := "/tmp/obend_ospc_4tile_sv_check"
    IO.FS.createDirAll tmpDir
    let tiles : List RtlMemModule := [ospcTileRtl 0, ospcTileRtl 1, ospcTileRtl 2, ospcTileRtl 3]
    for m in tiles do
      let svPath := s!"{tmpDir}/{m.core.name}.sv"
      IO.FS.writeFile svPath (emitMemModuleSV m)
      if let some vBin := verilatorOpt then
        let rV ← IO.Process.output
          { cmd := vBin, args := #["--lint-only", "-Wno-UNUSED", "-Wno-UNDRIVEN", "--top-module", m.core.name, svPath] }
        unless rV.exitCode == 0 do
          throw <| IO.userError s!"verilator --lint-only failed on {m.core.name}:\n{rV.stderr}\n{rV.stdout}"
      if let some yBin := yosysOpt then
        let yCmd := s!"read_verilog -sv {svPath}; hierarchy -check -top {m.core.name}; proc; opt_clean"
        let rY ← IO.Process.output { cmd := yBin, args := #["-q", "-p", yCmd] }
        unless rY.exitCode == 0 do
          throw <| IO.userError s!"yosys RTL elaboration failed on {m.core.name}:\n{rY.stderr}"

#eval verifyLiveOspcTilesRtlIfPresent

theorem test_ospc_prover_inhabited_and_non_collapse (v : Fin 4) (seed : BitVec 64) :
    (FaceIdeal4.varEq0 v).join (FaceIdeal4.varEq1 v) ≠ FaceIdeal4.top ∧
    ∃ (o : OspcProverObj) (c : OspcProverCert),
      ospcProverJudge.Fragment o ∧ ospcProverJudge.Meaning o c ∧ ospcProverJudge.check 1 o c = .ok :=
  ⟨faceIdeal4_boundary_ne_top v, ospcProverJudge_inhabited seed⟩

-- ============================================================================
-- 6. `#tooth` Kernel Mutation-Sensitivity Kills (`12` Kills Across All 5 Modules)
-- ============================================================================

-- Tooth 1 (`PinoutEquiv`): Ignoring courtyard dimensions breaks `checkPinoutIso_iff`:
#tooth Obend.Hardware.PinoutEquiv.checkPinoutIso_iff by mutation
  Obend.Hardware.PinoutEquiv.checkCourtyardFits := fun _ _ _ => true

-- Tooth 2 (`PinoutEquiv`): Ignoring 256-bit digest equality breaks `staleDatasheetCite256_refused`:
#tooth Obend.Hardware.PinoutEquiv.staleDatasheetCite256_refused by mutation
  Obend.Hardware.PinoutEquiv.checkDatasheetCite256Fresh := fun cite => decide (cite.currentDigest256 ≠ 0#256)

-- Tooth 3 (`PlaneSweepDrcLvs`): Reversing `.enter`-before-`.leave` tie-breaking at equal `xCoord`
-- breaks `planeSweepDrcExec_eq_allPairsSpec` (exact `scout` §5.7 mutation witness!):
def brokenSweepEventLeLeaveFirst (e1 e2 : SweepEvent) : Bool :=
  if e1.xCoord < e2.xCoord then true else if e2.xCoord < e1.xCoord then false
  else if e1.isLeave && !e2.isLeave then true else if !e1.isLeave && e2.isLeave then false
  else decide (e1.boxIdx ≤ e2.boxIdx)

#tooth Obend.Hardware.PlaneSweepDrcLvs.planeSweepDrcExec_eq_allPairsSpec by mutation
  Obend.Hardware.PlaneSweepDrcLvs.sweepEventLe := brokenSweepEventLeLeaveFirst

-- Tooth 4 (`PlaneSweepDrcLvs`): Rubber-stamping 2D spacing breaks `boxSpacing2D_disjoint`:
#tooth Obend.Hardware.PlaneSweepDrcLvs.boxSpacing2D_disjoint by mutation
  Obend.Hardware.PlaneSweepDrcLvs.checkBoxSpacing2D := fun _ _ _ => true

-- Tooth 5 (`PlaneSweepDrcLvs`): No-op union in `UnionFind` breaks `checkLvsConnectivityExec_iff`:
#tooth Obend.Hardware.PlaneSweepDrcLvs.checkLvsConnectivityExec_iff by mutation
  Obend.Hardware.PlaneSweepDrcLvs.ufUnion := fun uf _ _ => uf

-- Tooth 6 (`SmallSignalMna`): Omitting `alpha < 1` contraction check breaks `smallSignalMna_neumann_enclosure_sound`:
def brokenNeumannSkipAlpha (n : Nat) (G C R : List (List CanonicalRat))
    (omega : CanonicalRat) (vApprox iSrc : List CanonicalRat) (errBound : CanonicalRat) : Bool :=
  let alpha := acNeumannAlpha n G C R omega
  let delta := acNeumannResidual n G C R omega vApprox iSrc
  decide (0 < n) && decide (0 ≤ errBound) && decide (delta ≤ (1 - alpha) * errBound)

#tooth Obend.Hardware.SmallSignalMna.smallSignalMna_neumann_enclosure_sound by mutation
  Obend.Hardware.SmallSignalMna.checkSmallSignalNeumannEnclosure := brokenNeumannSkipAlpha

-- Tooth 7 (`SmallSignalMna`): Falling back from 8-cell octuple to 4-cell quad breaks `chiralityBalanced2D_cancels_full_hessian`:
#tooth Obend.Hardware.SmallSignalMna.chiralityBalanced2D_cancels_full_hessian by mutation
  Obend.Hardware.SmallSignalMna.chiralityBalanced2DMismatch := Obend.Hardware.SmallSignalMna.crossCoupledQuad2DMismatch

-- Tooth 8 (`DigitalFilterAndArray`): Under-reporting `firL1Norm` as `0` breaks `fir_l1_norm_wordlength_exact`:
#tooth Obend.Hardware.DigitalFilterAndArray.fir_l1_norm_wordlength_exact by mutation
  Obend.Hardware.DigitalFilterAndArray.firL1Norm := fun _ => 0

-- Tooth 9 (`DigitalFilterAndArray`): Flipping rotation sign in `chebyshevPair` breaks `chebyshev_pell_identity`:
def brokenChebyshevPairSign : Nat → CanonicalRat → CanonicalRat × CanonicalRat
  | 0, _ => (1, 0)
  | m + 1, u =>
    let p := brokenChebyshevPairSign m u
    (u * p.1 + (1 - u * u) * p.2, p.1 + u * p.2)

#tooth Obend.Hardware.DigitalFilterAndArray.chebyshev_pell_identity by mutation
  Obend.Hardware.DigitalFilterAndArray.chebyshevPair := brokenChebyshevPairSign

-- Tooth 10 (`OspcProver`): Collapsing `varEq0` to `top` breaks `faceIdeal4_boundary_ne_top`:
#tooth Obend.Hardware.OspcProver.faceIdeal4_boundary_ne_top by mutation
  Obend.Hardware.OspcProver.FaceIdeal4.varEq0 := fun _ => FaceIdeal4.top

-- Tooth 11 (`OspcProver`): Reversing `(lo, hi)` butterfly child order breaks `q2Butterfly_merkle_eq_canonical_root`:
def brokenButterflyMerkleHiLo (H : Obend.Digest.HashBytes.Hash) (leaf : Fin 4 → Nat) : Fin 4 → Nat :=
  let m0 : Fin 4 → Nat := fun t =>
    Obend.Core.Digest.digestWith H (leaf (q2OrderedHi ⟨0, by omega⟩ t)) (leaf (q2OrderedLo ⟨0, by omega⟩ t))
  fun t =>
    Obend.Core.Digest.digestWith H (m0 (q2OrderedHi ⟨1, by omega⟩ t)) (m0 (q2OrderedLo ⟨1, by omega⟩ t))

#tooth Obend.Hardware.OspcProver.q2Butterfly_merkle_eq_canonical_root by mutation
  Obend.Hardware.OspcProver.stepButterflyMerkle2Hop := brokenButterflyMerkleHiLo

-- Tooth 12 (`OspcProver`): Omitting `DeltaNet` linearity guard in `stepOspc4TileCycle` breaks `ospc_four_tile_prover_multi_cycle_sound`:
def brokenStepOspcSkipLinearity (H : Obend.Digest.HashBytes.Hash)
    (st : Ospc4TileProverState) (turn : OspcProverCycleTurn) : Except OspcRefusal Ospc4TileProverState :=
  let tiles' : Fin 4 → MemState := fun t => stepMemModule (ospcTileRtl t) turn.rst (turn.inputsFor t) (st.tiles t)
  let aggPoly := stepButterflySumcheck2Hop turn.tilePolys ⟨0, by omega⟩
  let sq := absorbAndSqueezeRound aggPoly st.transcript
  let mRoot := stepButterflyMerkle2Hop H (tileLeavesOf tiles') ⟨0, by omega⟩
  .ok ⟨tiles', sq.2, aggPoly.eval sq.1, mRoot, computeCycleReceipt256 H sq.2.state mRoot, st.cycleCount + 1⟩

#tooth Obend.Hardware.OspcProver.ospc_four_tile_prover_multi_cycle_sound by mutation
  Obend.Hardware.OspcProver.stepOspc4TileCycle := brokenStepOspcSkipLinearity

-- ============================================================================
-- 7. Imported-Tree Axiom Audit (`0 sorryAx`, `0` Custom Axioms, `0` Native)
-- ============================================================================

#assert_axioms_tree

end Obend.Tests.Metasystem.VerifiedCaeAndOspcEnginesTest
