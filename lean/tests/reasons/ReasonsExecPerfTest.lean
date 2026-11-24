module
public import Obend.Reasons
public import Obend.Vault.WorldTree.ShardedWorld
public import Obend.Vault.Merge
public import Obend.Vault.Cli
public import Obend.Tactic.Tooth
import all Obend.Codec.Hex
import all Obend.Vault.Store
import all Obend.Reasons
import all Obend.Vault.WorldTree.ShardedWorld

/-!
# `tests/reasons/ReasonsExecPerfTest.lean` — `Spec ↔ Exec` Verification & Mutation-Sensitivity Suite

Verifies the unboxed indexed `Reasons` evaluator (`gammaExec`, `wfExec`, `iterFix`) and the
`Vault` / `ChunkedWorld` hot-path `Spec ↔ Exec` refinements (`decodeShardPayloadCanonArray`,
`BucketedStore`, `freshPagesFast`, `resolveInIndexed`, `planIndexed`, `problemsIndexed`):
1. Universal theorem signatures & `#print axioms` kernel audit (`0 sorry`, `0` custom axioms).
2. Positive, cyclic, competing-defeat, odd-loop, duplicate-name, and overlong-LEB128 shard witnesses.
3. `#tooth` mutation-sensitivity guards refuting planted faults in `Reasons` and `ChunkedWorld`.
-/

public section

namespace Obend.Tests.ReasonsExecPerfTest

open Obend.Reasons
open Obend.Vault
open Obend.Vault.ChunkedWorld

-- 1. Universal `Spec ↔ Exec` Theorem Signatures & Kernel Axiom Audit
#check @gammaExec_eq
#check @wfExec_eq
#check @wfExec_same
#check @wfExec_statusIn
#check @gamma_eq_gammaExec
#check @wf_eq_wfExec
#check @iter_eq_iterFix
#check @decodeShardPayloadCanonArray_sound
#check @BucketedStore.page?_eq
#check @BucketedStore.tomb?_eq
#check @Obend.Vault.resolveIn_eq_indexed
#check @Obend.Vault.freshPages_eq_fast
#check @Obend.Vault.openAdmission_eq_fast
#check @Obend.Vault.landAll_eq_indexed
#check @Obend.Vault.landTexts_eq_indexed
#check @Obend.Vault.Merge.namesOf_eq_fast
#check @Obend.Vault.Merge.plan_eq_indexed
#check @Obend.Vault.Cli.problems_eq_indexed

#print axioms Obend.Reasons.wfExec_eq
#print axioms Obend.Reasons.wfExec_statusIn
#print axioms Obend.Vault.ChunkedWorld.decodeShardPayloadCanonArray_sound
#print axioms Obend.Vault.ChunkedWorld.BucketedStore.page?_eq
#print axioms Obend.Vault.freshPages_eq_fast
#print axioms Obend.Vault.Merge.plan_eq_indexed
#print axioms Obend.Vault.Cli.problems_eq_indexed

-- 2. Concrete `Reasons` Semantic & Edge-Case Kernel Proofs (Stratified, Positive Cycle, Even/Odd Defeat)
def posCycleProg : Program :=
  { facts := ["obs"]
    rules := [
      { name := "c1", concl := "x", pos := ["y"], neg := [] },
      { name := "c2", concl := "y", pos := ["x"], neg := [] },
      { name := "ok", concl := "grounded", pos := ["obs"], neg := ["x"] }
    ] }

#guard wfExec posCycleProg == (["obs", "grounded"], ["obs", "grounded"])
#guard statusIn (wfExec posCycleProg) "x" == .unsupported
#guard statusIn (wfExec posCycleProg) "grounded" == .supported

def selfCycleProg : Program :=
  { facts := ["o"]
    rules := [
      { name := "c1", concl := "x", pos := ["x"], neg := [] },
      { name := "ok", concl := "g", pos := ["o"], neg := ["x"] }
    ] }

example : wfExec selfCycleProg = (["o", "g"], ["o", "g"]) := by
  rw [wfExec_eq]; rfl

def evenCycleProg : Program :=
  { facts := []
    rules := [
      { name := "r1", concl := "a", pos := [], neg := ["b"] },
      { name := "r2", concl := "b", pos := [], neg := ["a"] }
    ] }

#guard wfExec evenCycleProg == ([], ["a", "b"])
#guard statusIn (wfExec evenCycleProg) "a" == .undefined
example : wfExec evenCycleProg = ([], ["a", "b"]) := by
  rw [wfExec_eq]; rfl

def oddCycleProg : Program :=
  { facts := []
    rules := [{ name := "odd", concl := "p", pos := [], neg := ["p"] }] }

#guard wfExec oddCycleProg == ([], ["p"])
#guard statusIn (wfExec oddCycleProg) "p" == .undefined
example : wfExec oddCycleProg = ([], ["p"]) := by
  rw [wfExec_eq]; rfl

-- 3. `#tooth` Mutation-Sensitivity Witnesses on `Reasons.firesBits` & `ChunkedWorld`
#tooth Obend.Reasons.firesBits_eq by mutation Obend.Reasons.firesBits :=
  fun _ _ _ => true

#tooth Obend.Vault.ChunkedWorld.BucketedStore.page?_eq by mutation Obend.Vault.ChunkedWorld.BucketedStore.page? :=
  fun _ _ => none

-- 4. Duplicate-Name First-Match Preservation & Canonical vs Overlong-LEB128 Shard Kernel Proofs
def samplePage1 : Page :=
  { name := "acct/P0001", id := 101, history := [⟨[(1, .text "first")], [], []⟩],
    seen := some "first", authors := [], note := none, kind := none }

def samplePage1Dup : Page :=
  { name := "acct/P0001", id := 999, history := [⟨[(2, .text "second")], [], []⟩],
    seen := some "second", authors := [], note := none, kind := none }

def dupStore : Store :=
  { pages := [samplePage1, samplePage1Dup], tombs := [samplePage1Dup] }

example : (buildBucketedStore dupStore).page? "acct/P0001" = some samplePage1 := by
  rw [BucketedStore.page?_eq]; rfl
example : (buildBucketedStore dupStore).page? "acct/P0002" = none := by
  rw [BucketedStore.page?_eq]; rfl
example : (buildBucketedStore dupStore).tomb? "acct/P0001" = some samplePage1Dup := by
  rw [BucketedStore.tomb?_eq]; rfl

-- Canonical shard payload `[0, 0]` decodes in 1 pass without re-serialization:
example : crShardPayload.decodeExact [0, 0] = some ([], []) := rfl

-- Overlong LEB128 `[128, 0, 0]` for `([], [])` is accepted by general `cShardPayload.decodeExact`
-- on fallback, while `crShardPayload.decodeExact` strictly rejects it so non-canonical bytes are
-- never reused as canonical shard digests:
example : cShardPayload.decodeExact [128, 0, 0] = some ([], []) := rfl
example : crShardPayload.decodeExact [128, 0, 0] = none := rfl

end Obend.Tests.ReasonsExecPerfTest
end
