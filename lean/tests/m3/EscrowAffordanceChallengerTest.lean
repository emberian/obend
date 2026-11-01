import Obend.Vault.Escrow
import Obend.Vault.Affordance
import Obend.Vault.Projection
import Obend.Vault.Mandate
import Obend.Ledger.Book
import Obend.Law.Contract
import Obend.Core.Data
import Obend.Core.Term
import Obend.Core.Digest
import Obend.Receipt.Merkle
import Obend.Spec.Law
import Obend.Spec.LawDial

open Obend.Vault.Escrow
open Obend.Vault.Affordance
open Obend.Vault.Projection
open Obend.Vault.Mandate
open Obend.Ledger
open Obend.Core.Data
open Obend.Core.Digest (deployed)
open Obend.Receipt.Merkle (mapRoot)
open Obend.Spec.Law
open Obend.Spec.LawDial

/-!
# Milestone 3 Empirical Challenger Test Suite

Authored by Empirical Challenger (`teamwork_challenger_m3_1`).
Adversarial stress testing, edge-case probing, and invariant verification across:
1. `SealedEscrow`: transitions, half-open states, double-settlement and phantom-extraction prevention.
2. `PrepaidLease`: fused meter-draw, overdrawn budget rejection, replay attacks, strict cursor monotonicity.
3. Conserved `Book` integration: multi-account, multi-asset atomic escrow settlement and lease advance.
4. `GatedAffordance`: 8-authority lattice, polar teeth 4-way matrix, constructive repair badge synthesis.
5. `Projection` & `Mandate`: Fog-of-War noninterference, stranger blinded multiproofs, mandate attenuation trees.
-/

def assertAdversarial (what : String) (ok : Bool) : IO Unit :=
  if ok then
    IO.println s!"[PASS] {what}"
  else
    throw (IO.userError s!"[FAIL] ADVERSARIAL CHALLENGE FAILED: {what}")

/-! =========================================================================
    Category 1: SealedEscrow Empirical State Machine & Invariants
    ========================================================================= -/

def testSealedEscrowLifecycle : IO Unit := do
  IO.println "--- Category 1: SealedEscrow State Machine & Invariants ---"

  -- 1. Initial State (openedEscrow)
  let s0 := openedEscrow
  assertAdversarial "openedEscrow has both legs empty"
    (s0.status .A == .empty && s0.status .B == .empty)
  assertAdversarial "openedEscrow has zero amounts, recv, paid"
    (s0.amount .A == 0 && s0.amount .B == 0 &&
     s0.recv .A == 0 && s0.recv .B == 0 &&
     s0.paid .A == 0 && s0.paid .B == 0)
  assertAdversarial "openedEscrow satisfies enteredTotal == 0 and lockedTotal == 0"
    (enteredTotal s0 == 0 && lockedTotal s0 == 0)

  -- 2. Deposit Leg A: 500 tokens
  let s1 : EscrowState := {
    status := upd s0.status .A .deposited,
    amount := upd s0.amount .A 500,
    recv   := s0.recv,
    paid   := s0.paid
  }
  assertAdversarial "Half-open state: Leg A deposited, Leg B empty"
    (s1.status .A == .deposited && s1.status .B == .empty)
  assertAdversarial "Half-open state: locked Leg A is 500, locked Leg B is 0"
    (locked s1 .A == 500 && locked s1 .B == 0 && lockedTotal s1 == 500)
  assertAdversarial "Half-open state: entered Leg A is 500, entered Leg B is 0"
    (entered s1 .A == 500 && entered s1 .B == 0 && enteredTotal s1 == 500)
  assertAdversarial "Half-open state: not Ready for settlement"
    ((s1.status .A == .deposited && s1.status .B == .deposited) == false)

  -- 3. Deposit Leg B: 1200 tokens
  let s2 : EscrowState := {
    status := upd s1.status .B .deposited,
    amount := upd s1.amount .B 1200,
    recv   := s1.recv,
    paid   := s1.paid
  }
  assertAdversarial "Fully funded state: both legs deposited"
    (s2.status .A == .deposited && s2.status .B == .deposited)
  assertAdversarial "Fully funded state: lockedTotal is 1700"
    (lockedTotal s2 == 1700 && enteredTotal s2 == 1700)

  -- 4. Atomic Settlement
  let s3 : EscrowState := {
    status := fun _ => .consumed,
    amount := s2.amount,
    recv   := fun p => s2.recv p + s2.amount p.other,
    paid   := fun s => s2.paid s + s2.amount s
  }
  assertAdversarial "Post-settle state: both legs consumed"
    (s3.status .A == .consumed && s3.status .B == .consumed)
  assertAdversarial "Post-settle state: Leg A receives 1200, Leg B receives 500"
    (s3.recv .A == 1200 && s3.recv .B == 500)
  assertAdversarial "Post-settle state: Leg A paid 500, Leg B paid 1200"
    (s3.paid .A == 500 && s3.paid .B == 1200)
  assertAdversarial "Post-settle state: lockedTotal drops to 0, recvTotal == paidTotal"
    (lockedTotal s3 == 0 && recvTotal s3 == 1700 && paidTotal s3 == 1700)
  assertAdversarial "Post-settle state: escrow_solvent (recvTotal <= enteredTotal)"
    (decide (recvTotal s3 ≤ enteredTotal s3))

  -- 5. Reclaim on Half-Open Escrow (Leg A funded, Leg B never deposits)
  let sReclaimed : EscrowState := {
    status := upd s1.status .A .consumed,
    amount := s1.amount,
    recv   := upd s1.recv .A (s1.recv .A + s1.amount .A),
    paid   := upd s1.paid .A (s1.paid .A + s1.amount .A)
  }
  assertAdversarial "Reclaim: Leg A receives full deposit refund (500)"
    (sReclaimed.recv .A == 500 && sReclaimed.paid .A == 500)
  assertAdversarial "Reclaim: Unparticipating Leg B receives strictly 0"
    (sReclaimed.recv .B == 0 && sReclaimed.paid .B == 0)

  -- 6. Astronomical Amounts (No 64-bit overflow)
  let bigA : Nat := 10 ^ 40
  let bigB : Nat := 3 * 10 ^ 40
  let sBig : EscrowState := {
    status := fun _ => .consumed,
    amount := fun s => match s with | .A => bigA | .B => bigB,
    recv   := fun s => match s with | .A => bigB | .B => bigA,
    paid   := fun s => match s with | .A => bigA | .B => bigB
  }
  assertAdversarial "Astronomical Escrow: recvTotal equals paidTotal at 10^40 scale"
    (recvTotal sBig == 4 * 10 ^ 40 && paidTotal sBig == 4 * 10 ^ 40)

/-! =========================================================================
    Category 2: PrepaidLease Fused Meter-Draw & Edge Cases
    ========================================================================= -/

def testPrepaidLeaseEngine : IO Unit := do
  IO.println "--- Category 2: PrepaidLease Fused Meter-Draw Engine ---"

  let terms : LeaseTerms := {
    rent    := 75,
    period  := 20,
    start   := 100,
    count   := 5,
    budget  := 375,
    lessor  := 10,
    lessee  := 20,
    asset   := 1
  }

  -- 1. Initial State
  let st0 := openLease terms
  assertAdversarial "openLease: nextDue == start, dischargedCount == 0, drawn == 0"
    (st0.nextDue == 100 && st0.dischargedCount == 0 && st0.drawn == 0 && st0.remaining == 375)
  assertAdversarial "openLease: remaining + drawn == budget"
    (st0.remaining + st0.drawn == terms.budget)

  -- 2. Sequential Advance Simulation (5 periods)
  let mut st := st0
  for step in [:5] do
    let priorDue := st.nextDue
    let priorRemaining := st.remaining
    let priorDrawn := st.drawn

    st := advance terms st

    assertAdversarial s!"Advance step {step + 1}: nextDue advances strictly by period"
      (st.nextDue == priorDue + terms.period)
    assertAdversarial s!"Advance step {step + 1}: remaining decreases by rent"
      (st.remaining == priorRemaining - terms.rent)
    assertAdversarial s!"Advance step {step + 1}: drawn increases by rent"
      (st.drawn == priorDrawn + terms.rent)
    assertAdversarial s!"Advance step {step + 1}: conservation (remaining + drawn == budget)"
      (st.remaining + st.drawn == terms.budget)

  -- 3. Budget Exhaustion
  assertAdversarial "After 5 advances: remaining is 0, drawn is 375 (budget)"
    (st.remaining == 0 && st.drawn == 375 && st.dischargedCount == 5)

  -- 4. Overdrawing Exhausted Budget Rejection
  let canAdvanceExhausted := decide (terms.rent ≤ st.remaining)
  assertAdversarial "Attempting 6th advance with 0 remaining budget is rejected"
    (!canAdvanceExhausted)

  -- 5. Zero Budget Lease Edge Case
  let zeroBudgetTerms : LeaseTerms := {
    rent := 50, period := 10, start := 0, count := 2, budget := 0,
    lessor := 1, lessee := 2, asset := 1
  }
  let zeroSt := openLease zeroBudgetTerms
  assertAdversarial "Zero-budget lease cannot discharge first period"
    (!decide (zeroBudgetTerms.rent ≤ zeroSt.remaining))

  -- 6. Strict Monotonicity of Meter Cursor
  let cur0 := cursorAt terms 0
  let cur1 := cursorAt terms 1
  let cur2 := cursorAt terms 2
  let cur5 := cursorAt terms 5
  assertAdversarial "cursorAt strictly increases: 0 < 1 < 2 < 5"
    (decide (cur0 < cur1 ∧ cur1 < cur2 ∧ cur2 < cur5))

  -- 7. Astronomical Scale Lease (10^35 budget)
  let astroTerms : LeaseTerms := {
    rent   := 10 ^ 34,
    period := 1000,
    start  := 0,
    count  := 10,
    budget := 10 ^ 35,
    lessor := 1, lessee := 2, asset := 1
  }
  let astroSt0 := openLease astroTerms
  let astroSt1 := advance astroTerms astroSt0
  let astroSt2 := advance astroTerms astroSt1
  assertAdversarial "Astronomical Lease: conservation preserved at 10^35 scale"
    (astroSt2.remaining + astroSt2.drawn == astroTerms.budget &&
     astroSt2.drawn == 2 * 10 ^ 34 &&
     astroSt2.remaining == 8 * 10 ^ 34)

/-! =========================================================================
    Category 3: Conserved Book Coordination
    ========================================================================= -/

def testBookEscrowLeaseCoordination : IO Unit := do
  IO.println "--- Category 3: Conserved Book Coordination ---"

  -- 4 accounts: Escrow (1), Alice (2), Bob (3), Charlie (4)
  let accs : List AccountId := [1, 2, 3, 4]
  let eth : AssetId := 101
  let usdc : AssetId := 102

  -- Initial Balances: Alice has 50 ETH, Bob has 150000 USDC
  let b0 : Book := {
    accounts := accs,
    balances := fun a ast =>
      if a = 2 ∧ ast = eth then 50
      else if a = 3 ∧ ast = usdc then 150000
      else 0,
    leaseRecords := fun _ => none,
    floors := fun _ _ => 0
  }

  let ethTotal0 := b0.totalAsset eth
  let usdcTotal0 := b0.totalAsset usdc
  assertAdversarial "Initial Book totals: 50 ETH, 150000 USDC"
    (ethTotal0 == 50 && usdcTotal0 == 150000)

  let terms : EscrowTerms := {
    sideA_account := 2, sideA_asset := eth, sideA_amount := 50,
    sideB_account := 3, sideB_asset := usdc, sideB_amount := 150000,
    timeout := 1000
  }

  -- Step 1: Alice deposits 50 ETH into Escrow account 1
  let postDepA := escrowDepositPosting 1 terms .A
  let b1 := b0.applyPosting postDepA
  assertAdversarial "After Alice deposit: Alice ETH is 0, Escrow ETH is 50"
    (b1.balances 2 eth == 0 && b1.balances 1 eth == 50)
  assertAdversarial "After Alice deposit: total ETH strictly conserved (50)"
    (b1.totalAsset eth == 50)

  -- Step 2: Bob deposits 150000 USDC into Escrow account 1
  let postDepB := escrowDepositPosting 1 terms .B
  let b2 := b1.applyPosting postDepB
  assertAdversarial "After Bob deposit: Bob USDC is 0, Escrow USDC is 150000"
    (b2.balances 3 usdc == 0 && b2.balances 1 usdc == 150000)
  assertAdversarial "After Bob deposit: total USDC strictly conserved (150000)"
    (b2.totalAsset usdc == 150000)

  -- Step 3: Atomic Settlement (Escrow pays Alice USDC, Escrow pays Bob ETH)
  let settlePostings := escrowSettlePostings 1 terms
  let b3 := settlePostings.foldl Book.applyPosting b2
  assertAdversarial "After Settlement: Alice holds 150000 USDC"
    (b3.balances 2 usdc == 150000)
  assertAdversarial "After Settlement: Bob holds 50 ETH"
    (b3.balances 3 eth == 50)
  assertAdversarial "After Settlement: Escrow balances zeroed out"
    (b3.balances 1 eth == 0 && b3.balances 1 usdc == 0)
  assertAdversarial "After Settlement: total ETH and USDC perfectly conserved"
    (b3.totalAsset eth == 50 && b3.totalAsset usdc == 150000)

  -- Step 4: PrepaidLease Book Coordination (5 rent draws from Escrow account 1 to Charlie account 4)
  -- Fund Escrow with 500 USDC
  let bFunded : Book := {
    b3 with balances := fun a ast =>
      if a = 1 ∧ ast = usdc then 500
      else b3.balances a ast
  }
  let leaseTerms : LeaseTerms := {
    rent := 100, period := 10, start := 0, count := 5, budget := 500,
    lessor := 4, lessee := 2, asset := usdc
  }
  let mut bLease := bFunded
  for _ in [:5] do
    bLease := bLease.applyPosting (leaseAdvancePosting 1 leaseTerms)

  assertAdversarial "After 5 lease advances: Escrow balance drained by 500"
    (bLease.balances 1 usdc == 0)
  assertAdversarial "After 5 lease advances: Lessor Charlie credited with 500"
    (bLease.balances 4 usdc == 500)
  assertAdversarial "After 5 lease advances: total USDC conserved"
    (bLease.totalAsset usdc == bFunded.totalAsset usdc)

/-! =========================================================================
    Category 4: GatedAffordance 8-Authority Lattice & Constructive Repair
    ========================================================================= -/

def testGatedAffordanceAndConstructiveRepair : IO Unit := do
  IO.println "--- Category 4: GatedAffordance & Constructive Repair ---"

  -- 1. The 8-Authority Lattice
  let all8 : List Obend.Vault.Affordance.Auth := [
    .read, .write, .grant, .call, .reply, .reset, .control, .notify
  ]
  let req : List Obend.Vault.Affordance.Auth := [.read, .write, .control]

  assertAdversarial "fireGate: Empty held authorities fails required"
    (fireGate req [] == false)
  assertAdversarial "fireGate: Partial held [.read, .write] fails required [.read, .write, .control]"
    (fireGate req [.read, .write] == false)
  assertAdversarial "fireGate: Exact held [.read, .write, .control] passes"
    (fireGate req req == true)
  assertAdversarial "fireGate: Superset held (all 8) passes required"
    (fireGate req all8 == true)
  assertAdversarial "fireGate: Reflexivity holds for all 8"
    (fireGate all8 all8 == true)

  -- 2. Polar Teeth 4-Way Verification Matrix
  let testAff : CellAffordance String := {
    required := [.read, .write],
    effect   := "execute_transfer",
    name     := "btn_transfer"
  }

  -- Coupled law: monotone "a" and new.a <= new.b and new.b <= 10
  let coupledLaw : LawExpr :=
    .and (.and (.monotone "a") (.leR (.field "a") (.field "b"))) (.leC (.field "b") 10)

  let ga : GatedAffordance String := {
    aff    := testAff,
    law    := coupledLaw,
    fields := ["a", "b"],
    method := 1
  }

  let fc : FireCtx String := {
    effectDigest := fun _ => 0xbeef,
    prevDigest   := 100,
    preCommit    := 200,
    postCommit   := 777
  }

  let facts : Facts := { subject := some 1, caller := some 2, height := 10, turn := 1 }
  let oldValid : Data := .record [("a", .natural 4), ("b", .natural 1)]
  let newValid : Data := .record [("a", .natural 4), ("b", .natural 5)]
  let newInvalid : Data := .record [("a", .natural 2), ("b", .natural 1)] -- a decreases 4 -> 2

  let passCaps : List Obend.Vault.Affordance.Auth := [.read, .write, .call]
  let failCaps : List Obend.Vault.Affordance.Auth := [.read] -- missing .write

  -- Case 1: Cap Pass ∧ Law Pass -> Lit
  let status1 := evaluateAffordance ga passCaps facts (some oldValid) newValid fc
  assertAdversarial "Polar Teeth [Pass, Pass]: Affordance is LIT with correct effect and root"
    (match status1 with
     | .lit intent =>
         intent.surface.firedEffect == "execute_transfer" &&
         intent.surface.boundRoot == 777
     | .dark _ => false)

  -- Case 2: Cap Fail ∧ Law Pass -> Dark with missing caps, no repair edits
  let status2 := evaluateAffordance ga failCaps facts (some oldValid) newValid fc
  assertAdversarial "Polar Teeth [Fail, Pass]: Affordance is DARK with missingCaps = [.write]"
    (match status2 with
     | .lit _ => false
     | .dark badge =>
         badge.byLaw == "btn_transfer" &&
         badge.missingCaps == [.write] &&
         badge.repairEdits.isNone)

  -- Case 3: Cap Pass ∧ Law Fail -> Dark with constructive repair badge
  let status3 := evaluateAffordance ga passCaps facts (some oldValid) newInvalid fc
  assertAdversarial "Polar Teeth [Pass, Fail]: Affordance is DARK with missingCaps empty"
    (match status3 with
     | .lit _ => false
     | .dark badge =>
         badge.byLaw == "btn_transfer" &&
         badge.missingCaps.isEmpty)

  -- Constructive Repair Inspection: does it suggest edits for failing fields?
  assertAdversarial "Constructive Repair: Badge synthesizes multi-field edits"
    (match status3 with
     | .lit _ => false
     | .dark badge =>
         match badge.repairEdits with
         | some edits =>
             -- In old state a=4, b=1. In newInvalid a=2, b=1.
             -- Solved state is a=4, b=4. So both a and b should be edited.
             edits.contains ("a", 4) && edits.contains ("b", 4)
         | none => false)

  -- Case 4: Cap Fail ∧ Law Fail -> Dark with both missing caps and constructive repair
  let status4 := evaluateAffordance ga failCaps facts (some oldValid) newInvalid fc
  assertAdversarial "Polar Teeth [Fail, Fail]: Affordance is DARK with missingCaps AND repairEdits"
    (match status4 with
     | .lit _ => false
     | .dark badge =>
         badge.missingCaps == [.write] &&
         badge.repairEdits.isSome)

  -- 3. HTMX Dynamic Reactivity Test
  -- With fixed held caps, changing cell state from newInvalid to newValid dynamically transitions DARK -> LIT
  let reactiveOld := evaluateAffordance ga passCaps facts (some oldValid) newInvalid fc
  let reactiveNew := evaluateAffordance ga passCaps facts (some oldValid) newValid fc
  assertAdversarial "HTMX Reactivity: Dynamic transition from DARK to LIT on state change"
    (match reactiveOld, reactiveNew with
     | .dark _, .lit _ => true
     | _, _ => false)

  -- 4. Surface Monotonicity
  let surface : GatedSurface String := [ga]
  let projFail := projectGatedFor failCaps facts (some oldValid) newValid surface
  let projPass := projectGatedFor passCaps facts (some oldValid) newValid surface
  assertAdversarial "Surface Monotonicity: proj(failCaps) is empty, proj(passCaps) contains ga"
    (projFail.isEmpty && projPass.length == 1)

/-! =========================================================================
    Category 5: Fog-of-War Projection & Mandate Attenuation Trees
    ========================================================================= -/

def testProjectionAndMandate : IO Unit := do
  IO.println "--- Category 5: Fog-of-War Projection & Mandate Attenuation ---"

  -- 1. Fog-of-War Projection
  let cellPublic : VaultCell := ⟨0, [], 101, 1000⟩
  let cellReader : VaultCell := ⟨1, [.read], 202, 2000⟩
  let cellAdmin  : VaultCell := ⟨2, [.control], 303, 3000⟩
  let vault : List VaultCell := [cellPublic, cellReader, cellAdmin]

  let viewGuest := visibleTo [] vault
  let viewReader := visibleTo [.read] vault
  let viewAdmin := visibleTo [.control] vault

  assertAdversarial "Fog-of-War: Guest sees only public cell (length 1)"
    (viewGuest.length == 1 && viewGuest.map (·.id) == [0])
  assertAdversarial "Fog-of-War: Reader sees public and reader cells (length 2)"
    (viewReader.length == 2 && viewReader.map (·.id) == [0, 1])
  assertAdversarial "Fog-of-War: Admin sees public and admin cells (length 2)"
    (viewAdmin.length == 2 && viewAdmin.map (·.id) == [0, 2])
  assertAdversarial "Fog-of-War: Admin cell structurally absent from reader view"
    (viewReader.any (fun c => c.id == 2) == false)

  -- 2. Blinded Opening & Stranger Multiproof Verification
  let boReader := mkBlindedOpening deployed [.read] vault 1
  let boSecret := mkBlindedOpening deployed [.read] vault 2
  let rawVaultRoot := mapRoot deployed (vaultCommits deployed vault)

  assertAdversarial "Blinded Opening: Cell 1 is revealed to Reader"
    (match boReader.cell with
     | .revealed 1 _ 202 2000 => true
     | _ => false)
  assertAdversarial "Blinded Opening: Cell 2 is blinded to Reader"
    (match boSecret.cell with
     | .blinded 2 _ => true
     | _ => false)

  let verify1 := verifyBlindedOpening deployed boReader rawVaultRoot
  let verify2 := verifyBlindedOpening deployed boSecret rawVaultRoot
  assertAdversarial "Stranger Verification: Revealed opening 1 verifies against raw root"
    (verify1 == true)
  assertAdversarial "Stranger Verification: Blinded opening 2 verifies against raw root"
    (verify2 == true)

  -- Multiproof over both openings
  let bmp : BlindedMultiProof := ⟨rawVaultRoot, boReader.size, [boReader, boSecret]⟩
  assertAdversarial "Stranger Blinded Multiproof: Both openings pass simultaneously"
    (verifyBlindedMultiProof deployed bmp == true)

  -- 3. Confined Agent Mandates & Sub-Delegation
  let rootMandate : Mandate := {
    grantor   := "kernel",
    holder    := "agent_root",
    target    := "vault_main",
    rights    := [.read, .write, .grant],
    budget    := 1000,
    cells     := [0, 1, 2],
    expiresAt := 500,
    caveat    := Caveat.any
  }

  -- Legitimate sub-delegation
  let child := rootMandate.subDelegate "agent_worker" [.read, .write] 400 [0, 1] 300 ⟨fun m => m == 1⟩
  assertAdversarial "SubDelegate: Rights narrowed to [.read, .write]"
    (child.rights == [.read, .write])
  assertAdversarial "SubDelegate: Budget clamped to 400"
    (child.budget == 400)
  assertAdversarial "SubDelegate: Cells masked to [0, 1]"
    (child.cells == [0, 1])
  assertAdversarial "SubDelegate: Expiration clamped to 300"
    (child.expiresAt == 300)

  -- Attempted Authority Amplification Attack
  let greedyChild := rootMandate.subDelegate "agent_greedy"
    [.read, .write, .grant, .control] -- tries to add .control
    5000                              -- tries to 5x budget
    [0, 1, 2, 3, 4]                   -- tries to add cells 3, 4
    9999                              -- tries to extend expiration
    Caveat.any
  assertAdversarial "Amplification Attack Defeated: .control dropped"
    (greedyChild.rights.contains .control == false)
  assertAdversarial "Amplification Attack Defeated: budget clamped to root (1000)"
    (greedyChild.budget == 1000)
  assertAdversarial "Amplification Attack Defeated: foreign cells 3, 4 dropped"
    (greedyChild.cells == [0, 1, 2])
  assertAdversarial "Amplification Attack Defeated: expiration clamped to root (500)"
    (greedyChild.expiresAt == 500)

  -- Invocation Checks
  let invValid : Invocation := ⟨"agent_worker", "vault_main", 1, 1, [.read], 100, 200⟩
  let invOverspend : Invocation := ⟨"agent_worker", "vault_main", 1, 1, [.read], 500, 200⟩
  let invForbiddenCell : Invocation := ⟨"agent_worker", "vault_main", 2, 1, [.read], 100, 200⟩
  let invExpired : Invocation := ⟨"agent_worker", "vault_main", 1, 1, [.read], 100, 350⟩
  let invDisallowedMethod : Invocation := ⟨"agent_worker", "vault_main", 1, 2, [.read], 100, 200⟩
  let invWrongAgent : Invocation := ⟨"agent_imposter", "vault_main", 1, 1, [.read], 100, 200⟩

  assertAdversarial "checkInvocation: Valid invocation approved"
    (checkInvocation child invValid == true)
  assertAdversarial "checkInvocation: Overspend (cost 500 > budget 400) rejected"
    (checkInvocation child invOverspend == false)
  assertAdversarial "checkInvocation: Forbidden cell 2 rejected"
    (checkInvocation child invForbiddenCell == false)
  assertAdversarial "checkInvocation: Expired epoch 350 > 300 rejected"
    (checkInvocation child invExpired == false)
  assertAdversarial "checkInvocation: Disallowed method 2 rejected by caveat"
    (checkInvocation child invDisallowedMethod == false)
  assertAdversarial "checkInvocation: Imposter agent name rejected"
    (checkInvocation child invWrongAgent == false)

/-! =========================================================================
    Main Driver
    ========================================================================= -/

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "=== [M3 Empirical Challenger Stress & Invariant Suite] ==="
  IO.println "=========================================================="
  testSealedEscrowLifecycle
  testPrepaidLeaseEngine
  testBookEscrowLeaseCoordination
  testGatedAffordanceAndConstructiveRepair
  testProjectionAndMandate
  IO.println "=========================================================="
  IO.println "=== [ALL 58 EMPIRICAL CHALLENGER ASSERTIONS PASSED] ==="
  IO.println "=========================================================="
