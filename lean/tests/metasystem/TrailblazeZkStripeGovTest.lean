module
/-
# Metasystem Test Suite — `Obend.Trailblaze.{ZkStripe, ClusterGov, CathedralApex}`

End-to-end kernel verification, positive & negative smoke fixtures, `#tooth` mutation-killing
barriers on universal soundness theorems, and `#print axioms` audits for Trailblazer T2:

1. **Organ O5 (`ZkStripe`)**: `PredRE` Brzozowski complement/intersection/De Morgan laws,
   `VpaOver`/`VpaMachine` balanced call/return stack invariant, 4-hop `tlsn` `HttpsSessionNode`
   `CallTree` Merkle digest & `Reasons.wf` policy admission/refusal (`silverZkStripeSmoke`).
2. **Organ O6 (`ClusterGov`)**: `Sable` $F_O$ overflow-free dot-product exactness over
   `koalaBearPrime`, `Ozaki` permutation & AllReduce tree-schedule invariance closing float
   covert channels under `HyperLaw2NonInterference`, `AriadneStep` `flopsCap` governance
   (`silverClusterGovSmoke`).
3. **Cathedral Apex (`CathedralApex`)**: End-to-end `ZkStripe → Reasons → HyperLaw → ClusterGov`
   digest weld & soundness (`apex_cathedral_zkstripe_to_clustergov_sound`, `silverCathedralApexSmoke`).
-/
public import Obend.Tactic.Tooth
public import Obend.Trailblaze.ZkStripe
public import Obend.Trailblaze.ClusterGov
public import Obend.Trailblaze.CathedralApex
import all Obend.Trailblaze.ZkStripe
import all Obend.Trailblaze.ClusterGov
import all Obend.Trailblaze.CathedralApex

@[expose] public section
namespace Obend.Tests.Metasystem.TrailblazeZkStripeGovTest

open Obend.Trailblaze.ZkStripe
open Obend.Trailblaze.ClusterGov
open Obend.Trailblaze.CathedralApex

set_option autoImplicit false

/-! ## §1. Organ O5 (`ZkStripe`) Kernel Checks: `PredRE`, `VpaOver` & 4-Hop `CallTree` -/

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

-- `VpaOver` / `VpaMachine` balanced JSON framing vs mismatched / underflowing returns
example : runVpa jsonFramingVpa (lexJsonVpaSymbols [123, 91, 49, 44, 50, 93, 125]) = true := rfl
example : runVpa jsonFramingVpa (lexJsonVpaSymbols [123, 91, 49, 125, 93]) = false := rfl
example : runVpa jsonFramingVpa (lexJsonVpaSymbols [125, 123, 125]) = false := rfl
example : IsBalancedVpaTrace (lexJsonVpaSymbols [123, 91, 50, 93, 125]) :=
  runVpa_balanced_stack jsonFramingVpa _ rfl

-- 4-hop `tlsn` `CallTree` audit & refusal checks
example : callTreeHopCount validFourHopCallTree = 4 := rfl
example : auditZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = .ok () := rfl
example :
    auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree =
      .error (.requestRegexViolation "registry.hf.co") := rfl
example :
    auditZkStripeCallTree defaultZkStripePolicy unbalancedVpaCallTree =
      .error (.unbalancedFraming "cdn.dataset.org") := rfl

-- Untrusted notary refusal check
def untrustedNotaryTree : HttpsSessionNode :=
  .mk 0xBAD0 "api.stripe.com" [71, 69, 84] [123, 125] []

example :
    auditZkStripeCallTree defaultZkStripePolicy untrustedNotaryTree =
      .error (.untrustedNotary "api.stripe.com" 0xBAD0) := rfl

-- Merkle digest sensitivity: altering 1 payload byte in hop 4 changes the root `callTreeDigest`
def mutatedHop4CallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 51, 93] []
      ]
    ]
  ]

example :
    (callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash mutatedHop4CallTree) = true := by decide

example : silverZkStripeSmoke = true := by decide


/-! ## §2. Organ O6 (`ClusterGov`) Kernel Checks: `Sable` $F_O$, `Ozaki` & `AriadneStep` -/

-- Signed negative & positive exact dot-product round-trip modulo `koalaBearPrime`
example : intDot [512, -256, 128, -64] [300, 400, -500, 100] = -19200 := rfl
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

-- `Ozaki` worker permutation & binary AllReduce tree re-association invariance
def gpuWorkerA : List Int := [100, -20, 3]
def gpuWorkerB : List Int := [50, 40, -1]
def gpuWorkerC : List Int := [-30, 10, 5]
def gpuWorkerD : List Int := [7, -15, 2]

example :
    ozakiSliceSum [gpuWorkerA, gpuWorkerB, gpuWorkerC, gpuWorkerD] =
      ozakiSliceSum [gpuWorkerD, gpuWorkerB, gpuWorkerA, gpuWorkerC] := rfl

def ringTree : AllReduceTree :=
  .node (.node (.node (.leaf gpuWorkerA) (.leaf gpuWorkerB)) (.leaf gpuWorkerC)) (.leaf gpuWorkerD)

def butterflyTree : AllReduceTree :=
  .node (.node (.leaf gpuWorkerA) (.leaf gpuWorkerB))
        (.node (.leaf gpuWorkerC) (.leaf gpuWorkerD))

example : evalAllReduceTree ringTree = evalAllReduceTree butterflyTree := rfl
example : evalRadixSlices 1024 (sliceVecAdd gpuWorkerA gpuWorkerB) =
    evalRadixSlices 1024 gpuWorkerA + evalRadixSlices 1024 gpuWorkerB := rfl

-- `ClusterGov` valid step admission and named refusals
example : auditClusterStep validClusterStepCtx = .ok [120, 30, 7] := rfl
example :
    auditClusterStep wrapOverflowClusterCtx =
      .error (.sableModulusWrap 4000000000 koalaBearPrime) := rfl
example :
    auditClusterStep flopsBreachClusterCtx =
      .error (.flopsCapExceeded 12500000 10000000) := rfl
example : silverClusterGovSmoke = true := rfl


/-! ## §3. Whole-Cathedral Apex (`CathedralApex`) Checks & `#tooth` Mutation Barriers -/

example : checkCathedralTurn sampleCathedralTurn = true := by decide
example : checkCathedralTurn brokenWeldCathedralTurn = false := by decide
example : silverCathedralApexSmoke = true := by decide

-- `#tooth` Barrier 1: mutating `PredRE` `nullable` to `fun _ => true` breaks `matchesBytes_compl`
#tooth Obend.Trailblaze.ZkStripe.matchesBytes_compl by
  mutation Obend.Trailblaze.ZkStripe.nullable := fun _ => true

-- `#tooth` Barrier 2: mutating `stepVpa` to ignore stack pops breaks `runVpa_balanced_stack`
#tooth Obend.Trailblaze.ZkStripe.runVpa_balanced_stack by
  mutation Obend.Trailblaze.ZkStripe.stepVpa := fun _ q stk _ => some (q, stk)

-- `#tooth` Barrier 3: mutating `checkSableNoWrap` to `fun _ => true` breaks `sable_dot_exact_no_wrap`
#tooth Obend.Trailblaze.ClusterGov.sable_dot_exact_no_wrap by
  mutation Obend.Trailblaze.ClusterGov.checkSableNoWrap := fun _ => true

-- `#tooth` Barrier 4: mutating `checkCathedralTurn` to `fun _ => true` breaks `apex_cathedral_zkstripe_to_clustergov_sound`
#tooth Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound by
  mutation Obend.Trailblaze.CathedralApex.checkCathedralTurn := fun _ => true


/-! ## §4. Kernel Axiom Audit (`0 sorryAx`, `0` custom `axiom`s) -/

#check @Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit
#check @Obend.Trailblaze.ClusterGov.apex_verifiable_ai_cluster_step
#check @Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound

#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_compl
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_inter
#print axioms Obend.Trailblaze.ZkStripe.matchesBytes_deMorgan_alt
#print axioms Obend.Trailblaze.ZkStripe.runVpa_balanced_stack
#print axioms Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit
#print axioms Obend.Trailblaze.ClusterGov.sable_dot_exact_no_wrap
#print axioms Obend.Trailblaze.ClusterGov.embedModP_injective_of_no_wrap
#print axioms Obend.Trailblaze.ClusterGov.ozakiSliceSum_perm
#print axioms Obend.Trailblaze.ClusterGov.ozaki_tree_schedule_invariant
#print axioms Obend.Trailblaze.ClusterGov.ozaki_closes_schedule_covert_channel
#print axioms Obend.Trailblaze.ClusterGov.apex_verifiable_ai_cluster_step
#print axioms Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound

end Obend.Tests.Metasystem.TrailblazeZkStripeGovTest
end
