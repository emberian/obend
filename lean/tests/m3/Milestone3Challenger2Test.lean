import Obend.Vault.Projection
import Obend.Vault.Mandate
import Obend.Core.Digest
import Obend.Receipt.Merkle

open Obend.Vault.Projection
open Obend.Vault.Mandate
open Obend.Core.Digest (deployed)
open Obend.Receipt.Merkle (mapRoot Small)

set_option autoImplicit false
set_option linter.unusedVariables false

def assertPass (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] ADVERSARIAL STRESS TEST FAILED: {what}")

/-! =========================================================================
    Milestone 3 Challenger 2: Formal Refutation Theorems
    ========================================================================= -/

/-- Budget escalation is strictly rejected by the attenuation preorder. -/
theorem adv_budget_escalation_impossible (p c : Mandate) (h : p.budget < c.budget) :
    ¬ attenuates c p := by
  intro hatten
  have hb := hatten.2.1
  omega

/-- Expiration term extension is strictly rejected by the attenuation preorder. -/
theorem adv_expiration_extension_impossible (p c : Mandate) (h : p.expiresAt < c.expiresAt) :
    ¬ attenuates c p := by
  intro hatten
  have he := hatten.2.2.2.1
  omega

/-- Target domain escape is strictly rejected by the attenuation preorder. -/
theorem adv_target_escape_impossible (p c : Mandate) (h : c.target ≠ p.target) :
    ¬ attenuates c p := by
  intro hatten
  have ht := hatten.2.2.2.2.1
  exact h ht

/-- Sibling oversubscription is strictly rejected by budget partitioning. -/
theorem adv_sibling_oversubscription_impossible (p : Mandate) (cs : List DelegTree)
    (h : p.budget < (cs.map (fun c => c.mandate.budget)).sum) :
    ¬ (DelegTree.node p cs).BudgetPartitioned := by
  intro hp
  have hsum := children_no_oversubscribe hp
  omega

/-! =========================================================================
    Suite 1: Blinded Merkle Multiproof & Fog-of-War Empirical Probes
    ========================================================================= -/

def runProjectionMultiproofProbes : IO Unit := do
  IO.println "=== Challenger 2 Suite 1: Blinded Merkle Multiproofs & Fog-of-War ==="

  -- Setup test vaults of varying shapes and sizes
  let c1 : VaultCell := ⟨10, [.read], 1001, 5555⟩
  let c2 : VaultCell := ⟨20, [.write], 1002, 6666⟩
  let c3 : VaultCell := ⟨30, [.read, .write], 1003, 7777⟩
  let c4 : VaultCell := ⟨40, [.call], 1004, 8888⟩
  let c5 : VaultCell := ⟨50, [.control], 1005, 9999⟩
  let c6 : VaultCell := ⟨60, [.reset], 1006, 1111⟩
  let c7 : VaultCell := ⟨70, [.notify], 1007, 2222⟩

  let vaults : List (String × List VaultCell) := [
    ("Empty Vault (size 0)", []),
    ("Singleton Vault (size 1)", [c1]),
    ("Two-Cell Vault (size 2)", [c1, c2]),
    ("Three-Cell Vault (size 3)", [c1, c2, c3]),
    ("Five-Cell Vault (size 5)", [c1, c2, c3, c4, c5]),
    ("Seven-Cell Vault (size 7)", [c1, c2, c3, c4, c5, c6, c7])
  ]

  let allCaps : List Obend.Vault.Projection.Auth :=
    [.read, .write, .grant, .call, .reply, .reset, .control, .notify]
  let readCaps : List Obend.Vault.Projection.Auth := [.read]
  let emptyCaps : List Obend.Vault.Projection.Auth := []

  -- 1. Merkle Root Invariance Probes: Redacted cells do NOT perturb the Merkle root
  for (name, v) in vaults do
    let honestRoot := mapRoot deployed (vaultCommits deployed v)
    let rootAll := mapRoot deployed (projectedCommits deployed allCaps v)
    let rootRead := mapRoot deployed (projectedCommits deployed readCaps v)
    let rootEmpty := mapRoot deployed (projectedCommits deployed emptyCaps v)

    assertPass s!"Root invariance across caps for {name}"
      (honestRoot == rootAll && honestRoot == rootRead && honestRoot == rootEmpty)

  -- 2. Stranger Verification Completeness on Honest Vaults
  let testVault := [c1, c2, c3, c4, c5, c6, c7]
  let vRoot := mapRoot deployed (vaultCommits deployed testVault)
  let testCaps := readCaps

  let honestOpenings : List BlindedOpening :=
    (List.range testVault.length).map fun j =>
      mkBlindedOpening deployed testCaps testVault j

  for j in [0:testVault.length] do
    let bo := mkBlindedOpening deployed testCaps testVault j
    assertPass s!"Stranger verification succeeds for honest cell {j}"
      (verifyBlindedOpening deployed bo vRoot == true)

  let bmp : BlindedMultiProof := ⟨vRoot, testVault.length, honestOpenings⟩
  assertPass "verifyBlindedMultiProof accepts complete honest multiproof"
    (verifyBlindedMultiProof deployed bmp == true)

  -- 3. Adversarial Stranger Verification Attacks (Must Reject with false)
  let bo0 := mkBlindedOpening deployed testCaps testVault 0 -- Revealed cell (c1 has required [.read], testCaps has [.read])
  let bo1 := mkBlindedOpening deployed testCaps testVault 1 -- Blinded cell (c2 has required [.write], testCaps lacks [.write])

  -- Attack 1: Corrupted salt in revealed cell
  let badSaltBo : BlindedOpening := { bo0 with cell := .revealed c1.id c1.required (c1.salt + 1) c1.content }
  assertPass "Corrupted salt in revealed opening rejected"
    (verifyBlindedOpening deployed badSaltBo vRoot == false)

  -- Attack 2: Tampered content in revealed cell
  let badContentBo : BlindedOpening := { bo0 with cell := .revealed c1.id c1.required c1.salt (c1.content + 100) }
  assertPass "Tampered content in revealed opening rejected"
    (verifyBlindedOpening deployed badContentBo vRoot == false)

  -- Attack 3: Tampered commitment in blinded cell
  let badCommitBo : BlindedOpening := { bo1 with cell := .blinded c2.id (cellBlind deployed c2 + 1) }
  assertPass "Tampered blinded commitment in redacted opening rejected"
    (verifyBlindedOpening deployed badCommitBo vRoot == false)

  -- Attack 4: Forged root
  assertPass "Honest opening checked against wrong root rejected"
    (verifyBlindedOpening deployed bo0 (vRoot + 1) == false)

  -- Attack 5: Truncated sibling path (path too short)
  let truncBo : BlindedOpening := { bo0 with path := bo0.path.dropLast }
  assertPass "Truncated path rejected by climb"
    (verifyBlindedOpening deployed truncBo vRoot == false)

  -- Attack 6: Extended sibling path (bogus extra sibling)
  let extBo : BlindedOpening := { bo0 with path := bo0.path ++ [42] }
  assertPass "Extended path rejected by climb"
    (verifyBlindedOpening deployed extBo vRoot == false)

  -- Attack 7: Corrupted sibling hash in path
  match bo0.path with
  | [] => pure ()
  | s :: rest =>
    let corruptBo : BlindedOpening := { bo0 with path := (s + 1) :: rest }
    assertPass "Corrupted sibling hash in path rejected"
      (verifyBlindedOpening deployed corruptBo vRoot == false)

  -- Attack 8: Swapped index attack (claiming position 1 with position 0's leaf/path)
  let swapBo : BlindedOpening := { bo0 with index := 1 }
  assertPass "Swapped index attack rejected"
    (verifyBlindedOpening deployed swapBo vRoot == false)

  -- Attack 9: Out-of-bounds size mismatch in multiproof
  let badSizeBmp : BlindedMultiProof := { bmp with size := bmp.size + 1 }
  assertPass "Multiproof size mismatch rejected"
    (verifyBlindedMultiProof deployed badSizeBmp == false)

  -- Attack 10: Index overflow (> 2^256) rejected by Small check
  let hugeIndexBo : BlindedOpening := { bo0 with index := 2^256 }
  assertPass "Index exceeding 2^256 rejected by Small gate"
    (verifyBlindedOpening deployed hugeIndexBo vRoot == false)

  -- 4. Fog-of-War Noninterference Probes
  -- Two vaults that differ ONLY on secret/hidden cells are indistinguishable to a low viewer
  let vaultA := [c1, c2, c3]
  let c2_modified : VaultCell := { c2 with content := 99999, salt := 88888 }
  let cSecret : VaultCell := ⟨999, [.control], 777, 666⟩
  let vaultB := [c1, c2_modified, c3, cSecret]

  -- Viewer holding only [.read] can only see c1
  assertPass "Fog-of-War noninterference: differing secrets produce identical visibleTo"
    (visibleTo readCaps vaultA == visibleTo readCaps vaultB)

  assertPass "Fog-of-War idempotence: rerender_idempotent holds"
    (visibleTo readCaps (visibleTo readCaps vaultA) == visibleTo readCaps vaultA)

  assertPass "Vision monotonicity: superset caps see superset of cells"
    (let subView := visibleTo readCaps vaultA
     let superView := visibleTo allCaps vaultA
     subView.all (fun c => superView.contains c))

/-! =========================================================================
    Suite 2: Mandate Attenuation Trees & Invocation Validation Probes
    ========================================================================= -/

def runMandateAttenuationProbes : IO Unit := do
  IO.println "=== Challenger 2 Suite 2: Mandate Attenuation Trees & Invocations ==="

  let parentCaveat : Caveat := ⟨fun m => m != 99⟩
  let parent : Mandate := {
    grantor   := "treasury",
    holder    := "coordinator",
    target    := "clearing-house",
    rights    := [.read, .write, .call],
    budget    := 500,
    cells     := [10, 20, 30],
    expiresAt := 1000,
    caveat    := parentCaveat
  }

  -- 1. Sub-delegation Attenuation Clamping
  -- Sub-delegation constructor automatically clamps budget, expiresAt, and filters rights & cells
  let attemptedChild := parent.subDelegate
    "worker-1"
    [.read, .control]  -- asks for .control (parent lacks .control)
    999                -- asks for budget 999 (parent has 500)
    [10, 99]           -- asks for cell 99 (parent lacks 99)
    2000               -- asks for expiration 2000 (parent has 1000)
    .any

  assertPass "subDelegate clamps budget to parent budget"
    (attemptedChild.budget == 500)
  assertPass "subDelegate clamps expiresAt to parent expiresAt"
    (attemptedChild.expiresAt == 1000)
  assertPass "subDelegate filters out unheld rights (.control dropped)"
    (attemptedChild.rights == [.read])
  assertPass "subDelegate filters out unheld cells (cell 99 dropped)"
    (attemptedChild.cells == [10])
  assertPass "subDelegate conjoins caveats: parent restriction m!=99 preserved"
    (attemptedChild.caveat.admits 99 == false)

  -- 2. Sibling Oversubscription Probes (children_no_oversubscribe)
  let child1 : Mandate := { parent with holder := "w1", budget := 200 }
  let child2 : Mandate := { parent with holder := "w2", budget := 200 }
  let child3 : Mandate := { parent with holder := "w3", budget := 100 }
  let childOversub : Mandate := { parent with holder := "w3", budget := 101 }

  let tHonest : DelegTree := .node parent [.node child1 [], .node child2 [], .node child3 []]
  let tBad : DelegTree := .node parent [.node child1 [], .node child2 [], .node childOversub []]

  assertPass "Honest partition (200 + 200 + 100 = 500) satisfies budget partition"
    (tHonest.childrenBudget <= parent.budget)

  assertPass "Oversubscribed siblings (200 + 200 + 101 = 501 > 500) detected"
    (tBad.childrenBudget > parent.budget)

  -- 3. Invocation Validation Attacks (checkInvocation & authorizedBy)
  let validInv : Invocation := {
    agent        := "coordinator",
    target       := "clearing-house",
    cell         := 20,
    method       := 1,
    requiredAuth := [.read, .write],
    cost         := 100,
    epoch        := 500
  }

  assertPass "Honest invocation within envelope succeeds"
    (checkInvocation parent validInv == true)

  -- Attack 1: Impostor agent identity
  let invImpostor : Invocation := { validInv with agent := "evil-agent" }
  assertPass "Impostor agent invocation rejected"
    (checkInvocation parent invImpostor == false)

  -- Attack 2: Target domain escape
  let invDomainEscape : Invocation := { validInv with target := "other-vault" }
  assertPass "Target domain escape rejected"
    (checkInvocation parent invDomainEscape == false)

  -- Attack 3: Unauthorized capability request (.reset not held)
  let invBadAuth : Invocation := { validInv with requiredAuth := [.read, .reset] }
  assertPass "Unauthorized capability requirement rejected"
    (checkInvocation parent invBadAuth == false)

  -- Attack 4: Budget overdraft (cost 501 > budget 500)
  let invOverdraft : Invocation := { validInv with cost := 501 }
  assertPass "Budget overdraft invocation rejected"
    (checkInvocation parent invOverdraft == false)

  -- Attack 5: Unauthorized cell access (cell 99 not in [10, 20, 30])
  let invBadCell : Invocation := { validInv with cell := 99 }
  assertPass "Access to unmasked cell rejected"
    (checkInvocation parent invBadCell == false)

  -- Attack 6: Expired mandate invocation
  let invAtExpiry : Invocation := { validInv with epoch := 1000 }
  let invExpired : Invocation := { validInv with epoch := 1001 }
  let invSeverelyExpired : Invocation := { validInv with epoch := 9999 }
  assertPass "Invocation at exact expiration limit succeeds"
    (checkInvocation parent invAtExpiry == true)
  assertPass "Invocation after expiration (+1 epoch) rejected"
    (checkInvocation parent invExpired == false)
  assertPass "Severely expired invocation rejected"
    (checkInvocation parent invSeverelyExpired == false)

  -- Attack 7: Invocation rejected by caveat filter (method 99)
  let invBadMethod : Invocation := { validInv with method := 99 }
  assertPass "Invocation rejected by runtime caveat filter"
    (checkInvocation parent invBadMethod == false)

/-! =========================================================================
    Main Runner
    ========================================================================= -/

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== [Milestone 3 Challenger 2 Empirical Test Runner] ==="
  IO.println "=========================================================="
  runProjectionMultiproofProbes
  runMandateAttenuationProbes
  IO.println "=========================================================="
  IO.println "=== [All Challenger 2 Empirical Probes PASSED Cleanly] ==="
  IO.println "=========================================================="

#print axioms adv_budget_escalation_impossible
#print axioms adv_expiration_extension_impossible
#print axioms adv_target_escape_impossible
#print axioms adv_sibling_oversubscription_impossible
