module
/-
# Metasystem Test Suite — `Obend.Trailblaze.{ZkStripe, ClusterGov, CathedralApex}`

End-to-end kernel verification, positive & negative smoke fixtures, `#tooth` mutation-killing
barriers on universal soundness theorems, and zero-`Classical.choice` / zero-`sorryAx` axiom audits:

1. **Organ O5 (`ZkStripe`)**:
   - policies are `Obend.Judge.SymbolicRegex.PredRE`: complement and intersection laws,
   - 256-bit `callTreeDigest`, `callTreeDigestBytes_binding` (`0` obligations, `0` `Classical`),
   - Recursive multi-hop `allSessionNodes` / `auditNodes_all_hops_sound` (`silverZkStripeSmoke`).
2. **Organ O6 (`ClusterGov`)**:
   - `Sable` $F_O$ overflow-free `intDot` / `intDotExec` exactness over `koalaBearPrime`,
   - `Ozaki` `ozakiSliceSum` / `ozakiSliceSumExec` schedule invariance under `HyperLaw2NonInterference`,
   - `PhysicalEnergyEnvelope` authority-pinned RTT & lower-curve shadow-FLOP energy conservation
     (`silverClusterGovSmoke`).
3. **Cathedral Apex (`CathedralApex`)**:
   - Unconditional `apex_cathedral_zkstripe_to_clustergov_sound` (`0` Stage-A obligations!) +
     32-byte (`BitVec 256`) in-rack FPGA boolean verifier receipt (`silverCathedralApexSmoke`).
-/
public import Lean
public import Obend.Tactic.Tooth
public import Obend.Trailblaze.CathedralApex
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Trailblaze.CathedralApex

public section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Obend.Tests.Metasystem.TrailblazeZkStripeGovTest

open Obend.Digest.HashBytes (be)
open Obend.Trailblaze.ZkStripe
open Obend.Trailblaze.ClusterGov
open Obend.Trailblaze.CathedralApex

set_option autoImplicit false

#check @Obend.Trailblaze.ZkStripe.callTreeDigestBytes_binding
#check @Obend.Trailblaze.ZkStripe.auditNodes_all_hops_sound
#check @Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit
#check @Obend.Trailblaze.ClusterGov.intDotExec_eq_intDot
#check @Obend.Trailblaze.ClusterGov.ozakiSliceSumExec_eq_ozakiSliceSum
#check @Obend.Trailblaze.ClusterGov.energy_conservation_bounds_hidden_ops
#check @Obend.Trailblaze.ClusterGov.apex_verifiable_ai_cluster_step
#check @Obend.Trailblaze.CathedralApex.fpgaVerifierReceipt256_at_most_two_states
#check @Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_compl
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_inter
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_alt
#print axioms Obend.Trailblaze.ZkStripe.callTreeDigest_size
#print axioms Obend.Trailblaze.ZkStripe.audit_covers_callTree_hops
#print axioms Obend.Trailblaze.ZkStripe.checkView_body_framed
#print axioms Obend.Trailblaze.ZkStripe.utf8Bytes_injective
#print axioms Obend.Trailblaze.ZkStripe.callTreeDigestBytes_binding
#print axioms Obend.Trailblaze.ZkStripe.callTreeDigest_binding
#print axioms Obend.Trailblaze.ZkStripe.auditNodes_all_hops_sound
#print axioms Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit
#print axioms Obend.Trailblaze.ClusterGov.sable_dot_exact_no_wrap
#print axioms Obend.Trailblaze.ClusterGov.intDotExec_eq_intDot
#print axioms Obend.Trailblaze.ClusterGov.sable_dotExec_exact_no_wrap
#print axioms Obend.Trailblaze.ClusterGov.ozakiSliceSumExec_eq_ozakiSliceSum
#print axioms Obend.Trailblaze.ClusterGov.ozakiSliceSum_perm
#print axioms Obend.Trailblaze.ClusterGov.ozaki_tree_schedule_invariant
#print axioms Obend.Trailblaze.ClusterGov.ozaki_closes_schedule_covert_channel
#print axioms Obend.Trailblaze.ClusterGov.energy_conservation_bounds_hidden_ops
#print axioms Obend.Trailblaze.ClusterGov.upper_curve_subtraction_masks_covert_ops
#print axioms Obend.Trailblaze.ClusterGov.apex_verifiable_ai_cluster_step
#print axioms Obend.Trailblaze.CathedralApex.fpgaVerifierReceipt256_at_most_two_states
#print axioms Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound
#print axioms Obend.Trailblaze.CathedralApex.cathedralTrace_sound
#print axioms Obend.Trailblaze.CathedralApex.checkCathedralTrace_sound
#print axioms extractCallTreeCollision
#print axioms callTreeDigestBytes_binding

#tooth Obend.Trailblaze.CathedralApex.encodeReceipt256_inj by
  mutation Obend.Trailblaze.CathedralApex.encodeReceipt256 := fun _ => ByteArray.empty

#tooth Obend.Trailblaze.CathedralApex.checkInRackFpgaReceipt_zero_covert_channel by
  mutation Obend.Trailblaze.CathedralApex.checkInRackFpgaReceipt :=
    fun H treeRoot step rcpt =>
      rcpt.verdict && decide (rcpt.receiptPayloadBytes.data.size ≤ maxRackReceiptBytes) &&
      decide (rcpt.verifierReceipt256 =
        computeFpgaVerifierReceipt256 H rcpt.rackId rcpt.epoch treeRoot step true)

#tooth Obend.Trailblaze.ClusterGov.checkPhysicalEnergyEnvelope_no_underflow by
  mutation Obend.Trailblaze.ClusterGov.checkPhysicalEnergyEnvelope :=
    fun env => decide (0 < env.minHiddenOpMilliJ ∧
      env.measuredRttMicros ≤ env.authorityBudgetMicros ∧
      physicalResidualMilliJ env ≤ env.minHiddenOpMilliJ * env.hiddenOpsCap)

#tooth Obend.Trailblaze.ZkStripe.matchesBytes_compl by
  mutation Obend.Trailblaze.ZkStripe.matchesBytes := fun _ _ => true

#tooth Obend.Trailblaze.ZkStripe.callTreeDigest_binding by
  mutation Obend.Trailblaze.ZkStripe.callTreeDigest := fun _ _ => ⟨ByteArray.empty⟩

#tooth Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit by
  mutation Obend.Trailblaze.ZkStripe.auditNodes := fun _ _ => .ok ()

#tooth Obend.Trailblaze.ZkStripe.sessionNodePreimage_inj by
  mutation Obend.Trailblaze.ZkStripe.sessionNodePreimage :=
    fun key _ req resp childrenBytes =>
      (0x01 : UInt8) ::
      (be 32 key.toNat ++
       (frameBytes [] ++
        (frameBytes req ++
         (frameBytes resp ++
          childrenBytes))))

#tooth Obend.Trailblaze.ClusterGov.sable_dot_exact_no_wrap by
  mutation Obend.Trailblaze.ClusterGov.checkSableNoWrap := fun _ => true

#tooth Obend.Trailblaze.ClusterGov.energy_conservation_bounds_hidden_ops by
  mutation Obend.Trailblaze.ClusterGov.checkPhysicalEnergyEnvelope := fun _ => true

#tooth Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralTurn := fun _ => true

#tooth Obend.Trailblaze.CathedralApex.checkCathedralTrace_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralTrace := fun _ _ => true

#tooth callTreeDigestBytes_binding by
  mutation sessionNodePreimage := fun _ _ req resp kids => req ++ resp ++ kids

#tooth rdna2Wavefront_simulates_ozaki_sound by
  mutation checkRdna2DispatchEnvelope := fun _ => true

#tooth sealedVramRandomOpening_sound by
  mutation checkVramChallengeOpening := fun _ _ _ _ => true


/-! ## §1. Organ O5 (`ZkStripe`): policies over `SymbolicRegex.PredRE`, 256-bit digests -/

-- Complement and intersection, on concrete requests.
example : matchesBytes (forbidSubseq stripeLiveKeyPrefix) [71, 69, 84, 32, 47] = true := by decide
example : matchesBytes (forbidSubseq stripeLiveKeyPrefix) [71, 115, 107, 95, 49] = false := by
  decide
example :
    matchesBytes (.inter (startsWith httpGetPrefix) (forbidSubseq stripeLiveKeyPrefix))
      [71, 69, 84, 32, 47, 118, 49] = true := by decide
example :
    matchesBytes (.inter (startsWith httpGetPrefix) (forbidSubseq stripeLiveKeyPrefix))
      [80, 79, 83, 84, 32, 47, 118, 49] = false := by decide
-- The organ's expressions are the judge's: no second regular-expression type.
example : forbidSubseq stripeLiveKeyPrefix =
    Obend.Judge.SymbolicRegex.absenceOf (Obend.Judge.SymbolicRegex.lit stripeLiveKeyPrefix) := rfl
example (r : PredRE) (bs : List UInt8) :
    matchesBytes r bs = true ↔ Obend.Judge.SymbolicRegex.Matches bs r := matchesBytes_iff r bs

-- The four-hop tree: admitted, canonical, a 32-byte digest; the planted faults refused by name.
example : callTreeHopCount validFourHopCallTree = 4 := rfl
example : (allSessionNodes validFourHopCallTree).length = 4 := rfl
example : verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = true := by decide
example : checkCanonicalSessionTree fastMerkleHash validFourHopCallTree = true := by decide
example : (callTreeDigest fastMerkleHash validFourHopCallTree).bytes.size = 32 :=
  callTreeDigest_size (by decide)
example :
    auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree =
      .error (.requestRegexViolation "registry.hf.co") := rfl
example :
    auditZkStripeCallTree defaultZkStripePolicy leakedResponseCallTree =
      .error (.responseRegexViolation "cdn.dataset.org") := rfl

def untrustedNotaryTree : HttpsSessionNode :=
  .mk 0xBAD0#256 "api.stripe.com" [71, 69, 84] [123, 125] []

example :
    auditZkStripeCallTree defaultZkStripePolicy untrustedNotaryTree =
      .error (.untrustedNotary "api.stripe.com") := rfl

-- The digest reads every field: the domain of hop 1, one payload byte of hop 4, the notary key.
example :
    (callTreeDigestBytes fastMerkleHash validFourHopCallTree !=
      callTreeDigestBytes fastMerkleHash spoofedDomainCallTree) = true := by decide
example :
    (callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash spoofedDomainCallTree) = true := by decide

def mutatedHop4CallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107]
      (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk fixtureNotaryKey "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk fixtureNotaryKey "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 51, 93] []
      ]
    ]
  ]

example :
    (callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash mutatedHop4CallTree) = true := by decide
example :
    (callTreeDigest fastMerkleHash (.mk fixtureNotaryKey "a" [71] [123, 125] []) !=
      callTreeDigest fastMerkleHash (.mk (fixtureNotaryKey + 1) "a" [71] [123, 125] [])) = true := by
  decide

example : silverZkStripeSmoke = true := by decide


/-! ## §2. Organ O6 (`ClusterGov`) Kernel Checks: `Sable` $F_O$, `Ozaki` `Exec` & `PhysicalEnergyEnvelope` -/

-- Signed negative & positive exact dot-product round-trip (`intDot` & `intDotExec`) modulo `koalaBearPrime`
example : intDot [512, -256, 128, -64] [300, 400, -500, 100] = -19200 := rfl
example : intDotExec #[512, -256, 128, -64] #[300, 400, -500, 100] = -19200 := by decide
example :
    decodeSignedModP koalaBearPrime
      (embedModP koalaBearPrime (intDot [512, -256, 128, -64] [300, 400, -500, 100])) =
      -19200 := rfl

-- Universal `sable_dot_exact_no_wrap` instantiated on concrete signed vectors
example :
    decodeSignedModP defaultKoalaBound.modulusP
      (embedModP defaultKoalaBound.modulusP
        (intDot [512, -256, 128, -64] [300, 400, -500, 100])) =
      intDot [512, -256, 128, -64] [300, 400, -500, 100] :=
  (sable_dot_exact_no_wrap defaultKoalaBound [512, -256, 128, -64] [300, 400, -500, 100]
    rfl (by decide)
    (checkVecAbsBounded_sound rfl)
    (checkVecAbsBounded_sound rfl)).2

-- `Ozaki` worker permutation, `ozakiSliceSumExec`, & binary AllReduce tree re-association invariance
def gpuWorkerA : List Int := [100, -20, 3]
def gpuWorkerB : List Int := [50, 40, -1]
def gpuWorkerC : List Int := [-30, 10, 5]
def gpuWorkerD : List Int := [7, -15, 2]

example :
    ozakiSliceSum [gpuWorkerA, gpuWorkerB, gpuWorkerC, gpuWorkerD] =
      ozakiSliceSum [gpuWorkerD, gpuWorkerB, gpuWorkerA, gpuWorkerC] := rfl

example :
    (ozakiSliceSumExec #[#[100, -20, 3], #[50, 40, -1], #[-30, 10, 5], #[7, -15, 2]]).toList =
      ozakiSliceSum [gpuWorkerA, gpuWorkerB, gpuWorkerC, gpuWorkerD] := by decide

def ringTree : AllReduceTree :=
  .node (.node (.node (.leaf gpuWorkerA) (.leaf gpuWorkerB)) (.leaf gpuWorkerC)) (.leaf gpuWorkerD)

def butterflyTree : AllReduceTree :=
  .node (.node (.leaf gpuWorkerA) (.leaf gpuWorkerB))
        (.node (.leaf gpuWorkerC) (.leaf gpuWorkerD))

example : evalAllReduceTree ringTree = evalAllReduceTree butterflyTree := rfl
example : evalRadixSlices 1024 (sliceVecAdd gpuWorkerA gpuWorkerB) =
    evalRadixSlices 1024 gpuWorkerA + evalRadixSlices 1024 gpuWorkerB := rfl

-- `ClusterGov` valid step admission (`rfl` compatibility) and named refusals
example : verifyClusterStep validClusterStepCtx = true := rfl
example : auditClusterStep validClusterStepCtx = .ok [120, 30, 7] := rfl
example :
    auditClusterStep wrapOverflowClusterCtx =
      .error (.sableModulusWrap 4000000000 koalaBearPrime) := rfl
example :
    auditClusterStep flopsBreachClusterCtx =
      .error (.flopsCapExceeded 12500000 10000000) := rfl

-- Authority-pinned RTT & lower-curve energy envelope checks
example : checkPhysicalEnergyEnvelope defaultPhysicalEnvelope = true := by decide
example :
    (match auditPhysicalClusterStep ⟨validClusterStepCtx, defaultPhysicalEnvelope⟩ with
     | .ok out => out == #[120, 30, 7]
     | .error _ => false) = true := by decide
example :
    (match auditPhysicalClusterStep
        ⟨validClusterStepCtx, { defaultPhysicalEnvelope with measuredRttMicros := 52000 }⟩ with
     | .error e => e == .rttBudgetExceeded 52000 3000
     | .ok _ => false) = true := by decide
example :
    (match auditPhysicalClusterStep
        ⟨validClusterStepCtx, { defaultPhysicalEnvelope with meterEnergyMilliJ := 500 }⟩ with
     | .error e => e == .energyResidualExceeded 70 20
     | .ok _ => false) = true := by decide

example : silverClusterGovSmoke = true := by decide


/-! ## §3. Whole-Cathedral Apex (`CathedralApex`) Checks -/

-- Spoofed-domain cathedral turn: mutates hop-1 domain while leaving `committedTreeDigestBytes`
def spoofedDomainCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with batchCallTree := spoofedDomainCallTree }

example : checkCathedralTurn sampleCathedralTurn = true := by decide
example : checkCathedralTurn brokenWeldCathedralTurn = false := by decide
example : checkCathedralTurn oversizedReceiptCathedralTurn = false := by decide
example : checkCathedralTurn spoofedDomainCathedralTurn = false := by decide
example :
    checkCathedralTrace sampleInitTraceState [sampleCathedralTurn, sampleSecondCathedralTurn] =
      true := by decide
example :
    checkCathedralTrace sampleInitTraceState [sampleCathedralTurn, sampleCathedralTurn] =
      false := by decide
example : silverCathedralApexSmoke = true := by decide


/-! Regression witnesses for P1-04 and P1-07. -/

private def receiptTestHash : Obend.Digest.HashBytes.Hash := fun _ => List.replicate 32 0
private def receiptTestStep : AriadneStep := ⟨1, 2, 3, 4, 5⟩
private def canonicalTestReceipt : InRackFpgaReceipt :=
  ⟨7, 1, true, 0#256, encodeReceipt256 0#256⟩

example : checkInRackFpgaReceipt receiptTestHash 2 receiptTestStep canonicalTestReceipt = true :=
  by decide

-- Same digest, same size, different bytes: the original size-only check admitted this.
example : checkInRackFpgaReceipt receiptTestHash 2 receiptTestStep
    { canonicalTestReceipt with receiptPayloadBytes := encodeReceipt256 1#256 } = false :=
  by decide

example : (encodeReceipt256 1#256).data.toList =
    List.replicate 31 (0 : UInt8) ++ [1] := by decide

private def underMeteredEnvelope : PhysicalEnergyEnvelope := {
  measuredRttMicros := 1
  authorityBudgetMicros := 2
  meterEnergyMilliJ := 9
  lowerCurveProvenMilliJ := 8
  idleEnergyMilliJ := 2
  toleranceMilliJ := 0
  minHiddenOpMilliJ := 1
  hiddenOpsCap := 0
}

-- Truncating subtraction reports zero, but admission must still reject the envelope.
example : physicalResidualMilliJ underMeteredEnvelope = 0 := by decide
example : checkPhysicalEnergyEnvelope underMeteredEnvelope = false := by decide
example : checkPhysicalEnergyEnvelope
    { underMeteredEnvelope with meterEnergyMilliJ := 10 } = true := by decide
example : checkPhysicalEnergyEnvelope
    { underMeteredEnvelope with toleranceMilliJ := 100, hiddenOpsCap := 100 } = false := by decide
example : (match auditPhysicalClusterStep ⟨validClusterStepCtx, underMeteredEnvelope⟩ with
    | .error (.energyBaselineUnderflow 9 10) => true
    | _ => false) = true := by decide




/-! ## §4. `#tooth` Mutation-Killing Barriers on Universal Soundness Theorems -/

-- Barrier 1: a matcher that says yes breaks the complement law.

-- Barrier 2: a digest that does not read the tree breaks its binding.

-- Barrier 3: an audit that admits every hop breaks the organ's theorem.

-- Barrier 4: a preimage that drops the domain breaks its injectivity.

-- `#tooth` Barrier 5: mutating `checkSableNoWrap` to `fun _ => true` breaks `sable_dot_exact_no_wrap`

-- `#tooth` Barrier 6: mutating `checkPhysicalEnergyEnvelope` to `fun _ => true` breaks `energy_conservation_bounds_hidden_ops`

-- `#tooth` Barrier 7: mutating `checkCathedralTurn` to `fun _ => true` breaks `apex_cathedral_zkstripe_to_clustergov_sound`

-- `#tooth` Barrier 8: mutating `checkCathedralTrace` to `fun _ _ => true` breaks `checkCathedralTrace_sound`


/-! ## §5. Kernel Axiom Audit (`0 sorryAx`, `0 Classical.choice`, `0` custom `axiom`s) -/



-- Compile-time constructive axiom gate: refuses `Classical.choice`, `sorryAx`, `_native`, or custom axioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  let prefixes : List Name := [
    `Obend.Trailblaze.ZkStripe,
    `Obend.Trailblaze.ClusterGov,
    `Obend.Trailblaze.CathedralApex
  ]
  let mut bad : Array (Name × List Name) := #[]
  for (c, info) in env.constants.map₁.toList do
    let .thmInfo _ := info | continue
    if c.isInternal || c.isInternalDetail then continue
    unless prefixes.any (·.isPrefixOf c) do continue
    let axs ← liftCoreM <| collectAxioms c
    let disallowed := axs.toList.filter (!allowed.contains ·)
    unless disallowed.isEmpty do
      bad := bad.push (c, disallowed)
  -- Type-valued collision programs are audited too, not only theorem declarations.
  for c in [``extractCallTreeCollision, ``callTreeDigest_binding_aux,
      ``callTreeChildrenDigestBytes_binding_aux,
      ``Obend.Judge.DecoAndCallTree.treeRoot_binds,
      ``Obend.Judge.DecoAndCallTree.treeRoots_binds,
      ``Obend.Judge.DecoAndCallTree.mrootC_binds,
      ``Obend.Vault.Lsafe.edgesCollision] do
    let axs ← liftCoreM <| collectAxioms c
    let disallowed := axs.toList.filter (!allowed.contains ·)
    unless disallowed.isEmpty do
      bad := bad.push (c, disallowed)
  unless bad.isEmpty do
    throwError m!"Constructive axiom gate failed (Classical.choice, sorryAx, or custom axiom found): {bad.toList}"


example : ∃ t : HttpsSessionNode,
    checkCanonicalSessionTree (Obend.Digest.Cshake256.cshake256Bytes []) t = true ∧
    callTreeDigestBytes (Obend.Digest.Cshake256.cshake256Bytes []) t =
      callTreeDigestBytes (Obend.Digest.Cshake256.cshake256Bytes []) t := cshake_callTree_binding_inhabited

/-- One-worker identity reduction executes S_ENDPGM and reads the loaded VGPR. -/
def executedDispatch : Rdna2WavefrontDispatch :=
  ⟨#[0xbf810000], 32, #[#[7, 11]], #[7, 11], false⟩
example : checkRdna2DispatchEnvelope executedDispatch = true := by decide +kernel
example : checkRdna2DispatchEnvelope { executedDispatch with hwReducedOut := #[99, 11] } = false := by decide +kernel
example : checkRdna2DispatchEnvelope { executedDispatch with shaderIsaWords := #[0xffffffff] } = false := by decide +kernel


def openingHash : Obend.Digest.HashBytes.Hash := fun _ => Obend.Digest.HashBytes.be 32 1
def validOpening : SealedVramOpeningClaim :=
  ⟨1, 1, 1, Array.replicate 8 0, Array.replicate 8 1, Array.replicate 8 ⟨[]⟩, 0⟩
example : checkVramChallengeOpening openingHash 1 42 validOpening = true := by decide +kernel
example : checkVramChallengeOpening openingHash 1 42 { validOpening with sealedRoot256 := 0 } = false := by decide +kernel
example : checkVramChallengeOpening openingHash 1 42 { validOpening with challengeSeed256 := 2 } = false := by decide +kernel
example : checkVramChallengeOpening openingHash 1 42 { validOpening with openedPageDigests := Array.replicate 8 2 } = false := by decide +kernel

end Obend.Tests.Metasystem.TrailblazeZkStripeGovTest
end
