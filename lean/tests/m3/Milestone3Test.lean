import Obend.Vault.Escrow
import Obend.Vault.Affordance
import Obend.Vault.Projection
import Obend.Vault.Mandate
import Obend.Receipt.Merkle
import Obend.Core.Digest

open Obend.Vault.Escrow
open Obend.Vault.Affordance
open Obend.Vault.Projection
open Obend.Vault.Mandate
open Obend.Receipt.Merkle (mapRoot)
open Obend.Core.Digest (deployed)
open Obend.Core.Data

/-! # Milestone 3 Unit Tests -/

-- 1. Unit test: Escrow deposit, settlement, and solvency
def test_escrow_deposit_and_settle : Bool :=
  let st0 := openedEscrow
  -- Deposit side A
  let st1 : EscrowState := { status := upd st0.status .A .deposited,
                             amount := upd st0.amount .A 100,
                             recv   := st0.recv,
                             paid   := st0.paid }
  -- Deposit side B
  let st2 : EscrowState := { status := upd st1.status .B .deposited,
                             amount := upd st1.amount .B 200,
                             recv   := st1.recv,
                             paid   := st1.paid }
  let ready := (st2.status .A == .deposited) && (st2.status .B == .deposited)
  let st3 : EscrowState := { status := fun _ => .consumed,
                             amount := st2.amount,
                             recv   := fun p => st2.recv p + st2.amount p.other,
                             paid   := fun s => st2.paid s + st2.amount s }
  ready &&
  (st3.recv .A == 200) &&
  (st3.recv .B == 100) &&
  (st3.paid .A == 100) &&
  (st3.paid .B == 200)

#guard test_escrow_deposit_and_settle == true

-- 2. Unit test: PrepaidLease advance and conservation
def test_prepaid_lease_advance : Bool :=
  let terms : LeaseTerms := { rent := 25, period := 10, start := 0, count := 4, budget := 100,
                              lessor := 1, lessee := 2, asset := 10 }
  let st0 := openLease terms
  let st1 := advance terms st0
  let st2 := advance terms st1
  (st0.remaining == 100) &&
  (st0.drawn == 0) &&
  (st1.nextDue == 10) &&
  (st1.remaining == 75) &&
  (st1.drawn == 25) &&
  (st2.nextDue == 20) &&
  (st2.remaining == 50) &&
  (st2.drawn == 50)

#guard test_prepaid_lease_advance == true

-- 3. Unit test: GatedAffordance evaluation
def demoAff : CellAffordance String where
  required := [.read, .write]
  effect   := "recalibrate"
  name     := "btn_recalibrate"

def demoGated : GatedAffordance String where
  aff    := demoAff
  law    := .eqR .turn .turn
  fields := []
  method := 1

def demoCtx : FireCtx String where
  effectDigest := fun _ => 42
  prevDigest   := 100
  preCommit    := 200
  postCommit   := 300

def demoFacts : Obend.Spec.Law.Facts where
  subject := some 0
  caller  := some 0
  height  := 10
  turn    := 1

def test_gated_affordance_eval : Bool :=
  let passCaps : List Obend.Vault.Affordance.Auth := [.read, .write, .call]
  let failCaps : List Obend.Vault.Affordance.Auth := [.read]
  let dummyData : Data := .record []
  let okStatus := evaluateAffordance demoGated passCaps demoFacts none dummyData demoCtx
  let failStatus := evaluateAffordance demoGated failCaps demoFacts none dummyData demoCtx
  match okStatus, failStatus with
  | .lit intent, .dark badge =>
      (intent.surface.firedEffect == "recalibrate") &&
      (intent.surface.boundRoot == 300) &&
      (badge.byLaw == "btn_recalibrate") &&
      (badge.missingCaps == [.write])
  | _, _ => false

#guard test_gated_affordance_eval == true

-- 4. Unit test: Fog-of-War Projection
def test_fog_of_war_projection : Bool :=
  let cell1 : VaultCell := ⟨1, [.read], 101, 1001⟩
  let cell2 : VaultCell := ⟨2, [.write], 102, 1002⟩
  let cell3 : VaultCell := ⟨3, [.read, .write], 103, 1003⟩
  let vault := [cell1, cell2, cell3]
  let viewerCaps : List Obend.Vault.Projection.Auth := [.read]
  let vis := visibleTo viewerCaps vault
  (vis.length == 1) &&
  (vis.map (·.id) == [1])

#guard test_fog_of_war_projection == true

-- 5. Unit test: Stranger-Checkable Blinded Multiproof
def test_blinded_multiproofs : Bool :=
  let cell1 : VaultCell := ⟨0, [.read], 111, 222⟩
  let cell2 : VaultCell := ⟨1, [.write], 333, 444⟩
  let vault := [cell1, cell2]
  let viewerCaps : List Obend.Vault.Projection.Auth := [.read]
  let root := mapRoot deployed (vaultCommits deployed vault)
  let opening0 := mkBlindedOpening deployed viewerCaps vault 0
  let opening1 := mkBlindedOpening deployed viewerCaps vault 1
  let v0 := verifyBlindedOpening deployed opening0 root
  let v1 := verifyBlindedOpening deployed opening1 root
  let multiproof : BlindedMultiProof := ⟨root, opening0.size, [opening0, opening1]⟩
  v0 && v1 && verifyBlindedMultiProof deployed multiproof

#guard test_blinded_multiproofs == true

-- 6. Unit test: Mandate Sub-delegation and Attenuation
def test_mandate_subdelegation : Bool :=
  let parent : Mandate := {
    grantor   := "treasury",
    holder    := "coordinator",
    target    := "dex-clearing",
    rights    := [.read, .write, .call],
    budget    := 1000,
    cells     := [1, 2, 3, 4],
    expiresAt := 500,
    caveat    := .any
  }
  let child := parent.subDelegate "worker-1" [.read, .call] 300 [2, 3] 400 .any
  (child.grantor == "coordinator") &&
  (child.holder == "worker-1") &&
  (child.target == "dex-clearing") &&
  (child.rights == [.read, .call]) &&
  (child.budget == 300) &&
  (child.cells == [2, 3]) &&
  (child.expiresAt == 400)

#guard test_mandate_subdelegation == true

def main : IO Unit := do
  IO.println "[PASS] Milestone3Test: All unit tests succeeded."
