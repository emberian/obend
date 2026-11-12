module
/-
# Obend.Crypto — Modular Dual-Track Post-Quantum PIOP, `MultilinearPCS` & `SameOpening` Spine

Umbrella module re-exporting Obend's dual-assumption cryptographic commitment and PIOP stack:
* `Obend.Crypto.Multilinear` — Polymorphic `CommRingOps` / `LawfulCommRing`, `Goldilocks`,
  `GoldilocksExt2`, `eqPoly`, `mleEval`, `foldFirstVar`, `mleEval_foldFirstVar`.
* `Obend.Crypto.Transcript` — Fenzi-safe (`ePrint 2026/1838`), full 256-bit (`state.size = 32`)
  cSHAKE256 Fiat–Shamir transcript (`TranscriptPhase`, `bindRelation`, `encodeFrame_injective`).
* `Obend.Crypto.Sumcheck` — Fenzi-bound `verifySumcheck`, `honestSumcheckProver`,
  `honestSumcheckProver_completeness`, `verifySumcheck_round_sound`, `verifySumcheck_sound_dichotomy`.
* `Obend.Crypto.PCS` — Binary RS proximity-gap guard (`ePrint 2026/2424`, `ValidProximityConfig`),
  `MultilinearPCS`, `BindingSound`, `SparseOneHotCommit`, and 32-byte `canopyMerklePCS`.
* `Obend.Crypto.DualSpine` — Lattice Ajtai / `PikkuFold` (`2026/1809`) ternary norm guard
  (`normInf_ternaryProj_le`), `ajtaiCommit_add`, `ajtaiLatticePCS`, `ajtaiSparseOneHot`, and
  cross-assumption `DualPCS` (`dualPCS_completeness`, `dualPCS_sound_of_either`).
* `Obend.Crypto.SameOpening` — `Choe–Kang–Stehlé` (`2026/2546`) `SmudgeSafe` guard, `BitZ`
  (`2026/2141`) $B$-bit range packing, `kktPrimalDualGapZero`, and `privateConvexSameOpeningJudge`.
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS
public import Obend.Crypto.DualSpine
public import Obend.Crypto.SameOpening
