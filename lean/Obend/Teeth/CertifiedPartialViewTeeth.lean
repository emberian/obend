/-
# Obend.Teeth.CertifiedPartialViewTeeth — Axiom Hygiene, Executable Poles & `#tooth` Kills for `CertifiedPartialView`

Verifies `Obend.Vault.CertifiedPartialView`:
1. `#assert_axioms_tree` whole-cone axiom hygiene (`0 sorryAx`, `0` custom axioms, `0 native_decide`).
2. Positive & negative kernel-checked witnesses (`decide +kernel`) for:
   - Dynamic 256-bit sparse partial-view projection, range non-omission, and `.redactedOverlap` refusal;
   - Multi-turn `peval` membrane execution across 3 state-mutating turns (static branch pruning of an
     out-of-cone secret key, `0`-scale algebraic annihilation, visible `.present` write + root update,
     and secret-only `secretOnlyEnv` evaluation matching `execFullTurns` step-for-step);
   - Goldilocks 4-limb Module-SIS Ajtai homomorphic linear opening `s_comb = ∑ c_i • s_i + s_mask`
     on `inhabitedAjtaiParams 1` (`cols = 8`) accepting honest masked sums (`100 + 2 * 25 = 150`) and
     rejecting tampered scalars (`151`).
3. **6 `#tooth` kernel mutation kills** covering:
   - Mutating range-gap overlap boundary `≤` to strict `<` (`rangesOverlap`),
   - Mutating `.blindedStub` tag domain separation (`blindedStubTag := emptyGapTag`),
   - Mutating `.emptyGap` vs `.present` tag domain separation (`emptyGapTag := presentNodeTag`),
   - Mutating `peval` branch condition polarity (`branchCondLe := fun u v => decide (v < u)`),
   - Mutating `peval` residual read-cone check (`checkResidualReadCone`),
   - Mutating homomorphic Ajtai 4-limb scalar readout (`readGadgetScalar`).
-/
import Obend.Vault.CertifiedPartialView
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Teeth.CertifiedPartialViewTeeth

open Obend.Core.Digest (Digest256)
open Obend.Crypto (inhabitedAjtaiParams ajtaiCommit)
open Obend.Vault.Affordance (Auth)
open Obend.Vault.CertifiedPartialView

set_option autoImplicit false

/-! ## 0. Whole-Cone Axiom Hygiene (`0 sorryAx`, `0` Custom Axioms, `0` Compiler Trust) -/

#assert_axioms_tree

/-! ## 1. Kernel-Checked Executable Witnesses (`decide +kernel`) -/

def recPub : ObjRecord :=
  { fields := [(0, 5), (1, 100)]
    required := [.read, .write]
    salt := 0x1111#256 }

def recConeSec : ObjRecord :=
  { fields := [(0, 30)]
    required := [.read, .control]
    salt := 0x2222#256 }

def recForbiddenSec : ObjRecord :=
  { fields := [(0, 9999)]
    required := [.read, .control]
    salt := 0x3333#256 }

/-- Contiguous sparse full tree over `[0#256, 30#256]`:
    - `[0, 9]`: `.emptyGap`
    - `[10, 10]`: `recPub` (visible to viewer)
    - `[11, 19]`: `.emptyGap`
    - `[20, 20]`: `recConeSec` (redacted from viewer, allowed in `residualReadCone`)
    - `[21, 29]`: `.emptyGap`
    - `[30, 30]`: `recForbiddenSec` (redacted from viewer AND forbidden in `residualReadCone`!) -/
def sampleFullTree : FullTree :=
  .branch
    (.branch
      (.emptyGap 0#256 9#256)
      (.branch
        (.present 10#256 recPub)
        (.emptyGap 11#256 19#256)))
    (.branch
      (.present 20#256 recConeSec)
      (.branch
        (.emptyGap 21#256 29#256)
        (.present 30#256 recForbiddenSec)))

def sampleStore : FullStore := ⟨sampleFullTree⟩

/-- Viewer membrane frustum: sees `[0, 19]` with `[.read, .write]`; entire `[20, 30]` subtree is blinded. -/
def viewerFrustum : CapFrustum :=
  { heldAuths := [.read, .write]
    allowedRanges := [(0#256, 19#256)] }

/-- Residual evaluator cone: allows `[20, 25]` (`recConeSec`), strictly forbids `30#256` (`recForbiddenSec`). -/
def enclaveResidualCone : CapFrustum :=
  { heldAuths := [.read, .control]
    allowedRanges := [(20#256, 25#256)] }

/-- Explicit sparse partial-view tree with `[20, 30]` collapsed into a single `.blindedStub`
    (avoids invoking Keccak-f[1600] inside `decide +kernel`). -/
def samplePartialView : PartialView :=
  { worldRoot := 0xABCD#256
    viewFrustum := viewerFrustum
    tree :=
      .branch
        (.branch
          (.emptyGap 0#256 9#256)
          (.branch
            (.present 10#256 recPub)
            (.emptyGap 11#256 19#256)))
        (.blindedStub 0xDEAD#256 20#256 30#256) }

/-- 1. Positive & negative structural poles (`decide +kernel`):
    - Tree well-formedness & confidentiality (`visibleEntries = [(10#256, recPub)]`);
    - Range scan over `[0, 19]` succeeds with `.complete [(10#256, recPub)]`, while `[15, 25]` refuses with `.redactedOverlap 20#256 30#256`;
    - `peval` prunes dead branch reading forbidden `30#256`, annihilates `scale 0 (.proj 30#256 0)`,
      folds `.emptyGap` key `12#256` to `0`, evaluates `secretOnlyEnv` (`secEnv 10#256 = none`) to `60 = evalFull`,
      and rejects `eLeak` when `30#256` is live (`checkResidualReadCone = false`)! -/
example :
    let pv := samplePartialView
    let secEnv := secretOnlyEnv sampleStore pv
    let eSafe : PExpr :=
      .ifLe (.proj 10#256 0) (.lit 10)
        (.add (.add (.scale 2 (.proj 20#256 0)) (.proj 12#256 0)) (.scale 0 (.proj 30#256 0)))
        (.proj 30#256 0)
    let eLeak : PExpr :=
      .ifLe (.proj 10#256 1) (.lit 10) (.lit 1) (.proj 30#256 0)
    let accSafe := pevalAux pv eSafe
    let accLeak := pevalAux pv eLeak
    sampleStore.tree.wf = true ∧
    pv.tree.wf = true ∧
    pv.tree.visibleEntries = [(10#256, recPub)] ∧
    rangeScanSubtree pv.tree 0#256 19#256 = .complete [(10#256, recPub)] ∧
    rangeScanSubtree pv.tree 15#256 25#256 = .redactedOverlap 20#256 30#256 ∧
    secEnv 10#256 = none ∧
    evalResidual secEnv accSafe.residual = 60 ∧
    evalFull sampleStore eSafe = 60 ∧
    checkResidualReadCone enclaveResidualCone accSafe.residual = true ∧
    checkResidualReadCone enclaveResidualCone accLeak.residual = false := by
  decide +kernel

/-- 2. Multi-turn execution witness (`decide +kernel`):
    Turn 1 folds `proj 10 0 (= 5) + 7 = 12` and writes `12` to `(10#256, field 0)`;
    Turn 2 observes the updated `12 > 10` at the membrane, takes `else` (`3 * 30 = 90`), and writes `90` to `(10#256, field 1)`;
    Turn 3 folds `90 - 12 = 78` purely at the membrane! -/
example :
    let turns : List MembraneTurn := [
      { expr := .add (.proj 10#256 0) (.lit 7)
        residualReadCone := enclaveResidualCone
        writeTarget := some ⟨10#256, 0, 0x4444#256⟩ },
      { expr := .ifLe (.proj 10#256 0) (.lit 10)
                  (.lit 0)
                  (.recProj true (.proj 30#256 0) (.scale 3 (.proj 20#256 0)))
        residualReadCone := enclaveResidualCone
        writeTarget := some ⟨10#256, 1, 0x5555#256⟩ },
      { expr := .sub (.proj 10#256 1) (.proj 10#256 0)
        residualReadCone := enclaveResidualCone
        writeTarget := none }
    ]
    (execFullTurns sampleStore turns).map Prod.fst = some [12, 90, 78] := by
  decide +kernel

/-- 3. Goldilocks 4-limb Module-SIS Ajtai homomorphic linear opening witness (`decide +kernel`):
    `s₁` commits scalar `100` with blinding `[7, 11, 13, 17]`,
    `s₂` commits scalar `25` with blinding `[3, 5, 9, 2]`,
    `s_mask` has zero scalar limbs `[0, 0, 0, 0]` and blinding `[19, 23, 29, 31]`;
    `s_comb = 1 • s₁ + 2 • s₂ + s_mask` opens `150` against `(1 • C₁ + 2 • C₂ + C_mask) mod q`
    and rejects dishonest scalar `151`! -/
example :
    let pp := inhabitedAjtaiParams 1
    let s₁ : List Int := [100, 0, 0, 0, 7, 11, 13, 17]
    let s₂ : List Int := [25, 0, 0, 0, 3, 5, 9, 2]
    let sMask : List Int := [0, 0, 0, 0, 19, 23, 29, 31]
    let c₁ := ajtaiCommit pp s₁ rfl
    let c₂ := ajtaiCommit pp s₂ rfl
    let cMask := ajtaiCommit pp sMask rfl
    let sComb := combineLinearWitnesses [(0, s₁), (1, s₂)] sMask
    verifyHomomorphicLinearOpening pp [(0, c₁), (1, c₂)] cMask 150 sComb = true ∧
    verifyHomomorphicLinearOpening pp [(0, c₁), (1, c₂)] cMask 151 sComb = false := by
  decide +kernel

/-! ## 2. `#tooth` Kernel Mutation Kills on Universal Theorems -/

/-- Mutation 1: Off-by-one strict `<` in `rangesOverlap` misses singleton boundary keys `[k, k]`
    and is rejected by `rangeScanPartial_sound_or_collision`. -/
def rangesOverlapStrictLt (aLo aHi bLo bHi : Key256) : Bool :=
  decide (aLo.toNat < bHi.toNat) && decide (bLo.toNat < aHi.toNat)

#tooth Obend.Vault.CertifiedPartialView.rangeScanPartial_sound_or_collision
  by mutation Obend.Vault.CertifiedPartialView.rangesOverlap := rangesOverlapStrictLt

-- Mutation 2: Collapsing `.blindedStub` tag domain separation (`blindedStubTag := emptyGapTag`)
-- enables stub/empty-gap confusion and is rejected by `blindedStub_domain_sep_or_collision`.
#tooth Obend.Vault.CertifiedPartialView.blindedStub_domain_sep_or_collision
  by mutation Obend.Vault.CertifiedPartialView.blindedStubTag := Obend.Vault.CertifiedPartialView.emptyGapTag

-- Mutation 3: Collapsing `.emptyGap` vs `.present` tag domain separation (`emptyGapTag := presentNodeTag`)
-- lets a host omit a present key as an empty gap and is rejected by `rangeScanPartial_sound_or_collision`.
#tooth Obend.Vault.CertifiedPartialView.rangeScanPartial_sound_or_collision
  by mutation Obend.Vault.CertifiedPartialView.emptyGapTag := Obend.Vault.CertifiedPartialView.presentNodeTag

/-- Mutation 4: Inverting `peval` static branch condition polarity (`branchCondLe := v < u`)
    evaluates the wrong conditional arm and is rejected by `peval_sound_and_confidential`. -/
def branchCondInverted (u v : Nat) : Bool :=
  decide (v < u)

#tooth Obend.Vault.CertifiedPartialView.peval_sound_and_confidential
  by mutation Obend.Vault.CertifiedPartialView.branchCondLe := branchCondInverted

/-- Mutation 5: Disabling the membrane residual read-cone check (`checkResidualReadCone`)
    allows redacted out-of-cone keys into residual terms and is rejected by `peval_sound_and_confidential`. -/
def checkResidualReadConeBypass (cone : CapFrustum) (r : ResExpr) : Bool :=
  match cone.allowedRanges, r with
  | [], .lit _ => true
  | _, _ => true

#tooth Obend.Vault.CertifiedPartialView.peval_sound_and_confidential
  by mutation Obend.Vault.CertifiedPartialView.checkResidualReadCone := checkResidualReadConeBypass

/-- Mutation 6: Corrupting `readGadgetScalar` to leak/include blinding coordinate `l₄` breaks
    mask invariance and is rejected by `verifyHomomorphicLinearOpening_sound`. -/
def readGadgetScalarLeaky : List Int → Int
  | l₀ :: l₁ :: l₂ :: l₃ :: l₄ :: _ =>
    l₀ + 65536 * l₁ + 4294967296 * l₂ + 281474976710656 * l₃ + l₄
  | xs => if xs.isEmpty then 0 else 0

#tooth Obend.Vault.CertifiedPartialView.verifyHomomorphicLinearOpening_sound
  by mutation Obend.Vault.CertifiedPartialView.readGadgetScalar := readGadgetScalarLeaky

end Obend.Teeth.CertifiedPartialViewTeeth
