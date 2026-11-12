module
/-
# Metasystem Test Suite — `Obend.Trailblaze.{ZkStripe, ClusterGov, CathedralApex}`

End-to-end kernel verification, positive & negative smoke fixtures, `#tooth` mutation-killing
barriers on universal soundness theorems, and zero-`Classical.choice` / zero-`sorryAx` axiom audits:

1. **Organ O5 (`ZkStripe`)**:
   - `PredRE` Brzozowski complement/intersection/De Morgan laws,
   - Stateful 2-bit `(inString, escaped)` JSON VPA lexer + `ByteArray` `Exec` fast path (`Spec ↔ Exec`),
   - Unconditional domain-bound `callTreeDigestBytes_binding` (`0` obligations, `0` `Classical`),
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
public import Obend.Trailblaze.ZkStripe
public import Obend.Trailblaze.ClusterGov
public import Obend.Trailblaze.CathedralApex
import all Obend.Trailblaze.ZkStripe
import all Obend.Trailblaze.ClusterGov
import all Obend.Trailblaze.CathedralApex

public section
namespace Obend.Tests.Metasystem.TrailblazeZkStripeGovTest

open Obend.Digest.HashBytes (be)
open Obend.Trailblaze.ZkStripe
open Obend.Trailblaze.ClusterGov
open Obend.Trailblaze.CathedralApex

set_option autoImplicit false

/-! ## §1. Organ O5 (`ZkStripe`) Kernel Checks: `PredRE`, String-Aware `VpaOver` & Domain-Bound `CallTree` -/

-- `PredRE` boolean complement (`compl`) and conjunction (`inter`) concrete checks
example : matchesBytes (PredRE.forbidSubseq stripeLiveKeyPrefix) [71, 69, 84, 32, 47] = true := rfl
example : matchesBytes (PredRE.forbidSubseq stripeLiveKeyPrefix) [71, 115, 107, 95, 49] = false := rfl

example :
    matchesBytes
      (.inter (.seq (PredRE.litBytes httpGetPrefix) (.star PredRE.anyByte))
              (PredRE.forbidSubseq stripeLiveKeyPrefix))
      [71, 69, 84, 32, 47, 118, 49] = true := rfl

example :
    matchesBytes
      (.inter (.seq (PredRE.litBytes httpGetPrefix) (.star PredRE.anyByte))
              (PredRE.forbidSubseq stripeLiveKeyPrefix))
      [80, 79, 83, 84, 32, 47, 118, 49] = false := rfl

-- Stateful 2-bit `(inString, escaped)` JSON VPA lexer + `ByteArray` `Exec` fast path checks
example : runJsonFramingVpa jsonFramingVpa [123, 91, 49, 44, 50, 93, 125] = true := rfl
example : runJsonFramingVpa jsonFramingVpa [123, 91, 49, 125, 93] = false := rfl
example : runJsonFramingVpa jsonFramingVpa [125, 123, 125] = false := rfl

-- String-aware delimiter confinement: unmatched `}` inside `"..."` is accepted (`Spec` & `Exec`)
example :
    runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"msg\":\"unmatched } inside string\"}") = true := by
  decide
example :
    runJsonFramingVpaExec jsonFramingVpa ("{\"msg\":\"unmatched } inside string\"}".toByteArray) = true := by
  decide

-- Escaped-quote delimiter smuggling `{"smuggle":"\"}` is refused (`none` / `false`) (`Spec` & `Exec`)
example :
    lexJsonBytesSpec false false (utf8Bytes "{\"smuggle\":\"\\\"}") = none := by
  decide
example :
    lexJsonByteArrayExec ("{\"smuggle\":\"\\\"}".toByteArray) = none := by
  decide
example :
    runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\"}") = false := by
  decide
example :
    runJsonFramingVpaExec jsonFramingVpa ("{\"smuggle\":\"\\\"}".toByteArray) = false := by
  decide

-- Properly closed string with escaped quote + `}` (`{"smuggle":"\"}"}`) is accepted
example :
    runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\"}\"}") = true := by
  decide
example :
    runJsonFramingVpaExec jsonFramingVpa ("{\"smuggle\":\"\\\"}\"}".toByteArray) = true := by
  decide

-- Escaped backslash `\\` + closing quote + unmatched `}` (`{"smuggle":"\\"}}`) is refused
example :
    runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\\\"}}") = false := by
  decide
example :
    runJsonFramingVpaExec jsonFramingVpa ("{\"smuggle\":\"\\\\\"}}".toByteArray) = false := by
  decide

-- 4-hop `tlsn` `CallTree` full-tree audit & refusal checks
example : callTreeHopCount validFourHopCallTree = 4 := rfl
example : (allSessionNodes validFourHopCallTree).length = 4 := rfl
example : verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = true := by decide
example : checkCanonicalSessionTree fastMerkleHash validFourHopCallTree = true := by decide
example :
    auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree =
      .error (.requestRegexViolation "registry.hf.co") := rfl
example :
    (match auditZkStripeCallTree defaultZkStripePolicy unbalancedVpaCallTree with
     | .error e => e == .unbalancedFraming "cdn.dataset.org"
     | .ok () => false) = true := by decide

-- Untrusted notary refusal check
def untrustedNotaryTree : HttpsSessionNode :=
  .mk 0xBAD0 "api.stripe.com" [71, 69, 84] [123, 125] []

example :
    auditZkStripeCallTree defaultZkStripePolicy untrustedNotaryTree =
      .error (.untrustedNotary "api.stripe.com" 0xBAD0) := rfl

-- Domain sensitivity: swapping `serverDomain` on hop 1 changes `callTreeDigestBytes` & `callTreeDigest`
example :
    (callTreeDigestBytes fastMerkleHash validFourHopCallTree !=
      callTreeDigestBytes fastMerkleHash spoofedDomainCallTree) = true := by decide
example :
    (callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash spoofedDomainCallTree) = true := by decide

-- Payload sensitivity: altering 1 payload byte in hop 4 changes the root `callTreeDigest`
def mutatedHop4CallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107]
      (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 51, 93] []
      ]
    ]
  ]

example :
    (callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash mutatedHop4CallTree) = true := by decide

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


/-! ## §4. `#tooth` Mutation-Killing Barriers on Universal Soundness Theorems -/

-- `#tooth` Barrier 1: mutating `PredRE` `nullable` to `fun _ => true` breaks `matchesBytes_compl`
#tooth Obend.Trailblaze.ZkStripe.matchesBytes_compl by
  mutation Obend.Trailblaze.ZkStripe.nullable := fun _ => true

-- `#tooth` Barrier 2: mutating `stepVpa` to ignore stack pops breaks `runVpa_balanced_stack`
#tooth Obend.Trailblaze.ZkStripe.runVpa_balanced_stack by
  mutation Obend.Trailblaze.ZkStripe.stepVpa := fun _ q stk _ => some (q, stk)

-- `#tooth` Barrier 3: mutating `lexJsonStep` to ignore backslash `\` (`92`) breaks `runJsonFramingVpa_rejects_escaped_quote_smuggle`
#tooth Obend.Trailblaze.ZkStripe.runJsonFramingVpa_rejects_escaped_quote_smuggle by
  mutation Obend.Trailblaze.ZkStripe.lexJsonStep := fun inString _ b =>
    if inString then
      if b == 34 then (false, false, .internal b) else (true, false, .internal b)
    else
      if b == 34 then (true, false, .internal b)
      else if b == 123 then (false, false, .call 1 b)
      else if b == 125 then (false, false, .ret 1 b)
      else (false, false, .internal b)

-- `#tooth` Barrier 4: mutating `sessionNodePreimage` to drop `domain` breaks `sessionNodePreimage_inj`
#tooth Obend.Trailblaze.ZkStripe.sessionNodePreimage_inj by
  mutation Obend.Trailblaze.ZkStripe.sessionNodePreimage :=
    fun notaryHash _ req resp childrenBytes =>
      (0x01 : UInt8) ::
      (be 8 notaryHash ++
       (frameBytes [] ++
        (frameBytes req ++
         (frameBytes resp ++
          childrenBytes))))

-- `#tooth` Barrier 4b: mutating `frameBytes` to drop the 4-byte length prefix breaks `frameBytes_append_inj`
#tooth Obend.Trailblaze.ZkStripe.frameBytes_append_inj by
  mutation Obend.Trailblaze.ZkStripe.frameBytes := fun xs => xs

-- `#tooth` Barrier 5: mutating `checkSableNoWrap` to `fun _ => true` breaks `sable_dot_exact_no_wrap`
#tooth Obend.Trailblaze.ClusterGov.sable_dot_exact_no_wrap by
  mutation Obend.Trailblaze.ClusterGov.checkSableNoWrap := fun _ => true

-- `#tooth` Barrier 6: mutating `checkPhysicalEnergyEnvelope` to `fun _ => true` breaks `energy_conservation_bounds_hidden_ops`
#tooth Obend.Trailblaze.ClusterGov.energy_conservation_bounds_hidden_ops by
  mutation Obend.Trailblaze.ClusterGov.checkPhysicalEnergyEnvelope := fun _ => true

-- `#tooth` Barrier 7: mutating `checkCathedralTurn` to `fun _ => true` breaks `apex_cathedral_zkstripe_to_clustergov_sound`
#tooth Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralTurn := fun _ => true

-- `#tooth` Barrier 8: mutating `checkCathedralTrace` to `fun _ _ => true` breaks `checkCathedralTrace_sound`
#tooth Obend.Trailblaze.CathedralApex.checkCathedralTrace_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralTrace := fun _ _ => true


/-! ## §5. Kernel Axiom Audit (`0 sorryAx`, `0 Classical.choice`, `0` custom `axiom`s) -/

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
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_deMorgan_alt
#print axioms Obend.Trailblaze.ZkStripe.runVpa_balanced_stack
#print axioms Obend.Trailblaze.ZkStripe.lexJsonByteArrayExec_eq_spec
#print axioms Obend.Trailblaze.ZkStripe.runJsonFramingVpaExec_eq_spec
#print axioms Obend.Trailblaze.ZkStripe.runJsonFramingVpa_rejects_escaped_quote_smuggle
#print axioms Obend.Trailblaze.ZkStripe.runJsonFramingVpa_string_escape_sound
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
  unless bad.isEmpty do
    throwError m!"Constructive axiom gate failed (Classical.choice, sorryAx, or custom axiom found): {bad.toList}"

end Obend.Tests.Metasystem.TrailblazeZkStripeGovTest
end
