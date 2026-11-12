module
/-
# EpistemicVouchMarketTest — attack runs, a judged slash, and mutation teeth for the vouch market

Exercises `Obend.Polis.EpistemicVouchMarket`:

1. **A ring of five pseudonyms.** An adversary with 1000 units of capacity from the root splits it
   over five pseudonyms, wires them into a ring of mutual vouches of 1000 each, and has each stake
   1000 on a claim. The capacity is 1000, exactly; the certificate checker agrees; a packing that
   tries to carry more is refused; and the bound holds for every wiring inside the region, not
   only this one.
2. **A judged slash.** A voucher on a false tally, a voucher for that voucher, and an uninvolved
   voucher on a true tally. The judge refutes the false tally and the slash pays the hunter and
   the treasury to the unit; the true tally cannot be slashed, nor can anything without a
   challenge or without a grade that covers the tally.
3. **Hit and run.** Stake that is locked cannot be unbonded, an unbond cannot be taken before its
   cooldown, a challenge holds the stake past its unlock epoch; once the challenge lapses the
   voucher leaves with everything.
4. **Teeth.** Each `#tooth` replaces one check and reports that a stored proof no longer checks.
-/
public import Obend.Polis.EpistemicVouchMarket
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
import all Obend.Polis.EpistemicVouchMarket
import all Obend.Logic.SeparationFrame
import all Obend.Judge.Class
import all Obend.Core.Term
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

public section

namespace Obend.Tests.Metasystem.EpistemicVouchMarketTest

open Obend.Polis.EpistemicVouchMarket

set_option autoImplicit false

/-! ## 1. A ring of five pseudonyms -/

def root : TrustNode := .principal 0
def auditClaim : TrustNode := .claim 0xA11CE#256
def pseudonym (i : Nat) : TrustNode := .principal (10 + i)

/-- What the root extends to the adversary: 200 to each of five pseudonyms, 1000 in all. -/
def inbound : List CapEdge :=
  [⟨root, pseudonym 0, 200⟩, ⟨root, pseudonym 1, 200⟩, ⟨root, pseudonym 2, 200⟩,
    ⟨root, pseudonym 3, 200⟩, ⟨root, pseudonym 4, 200⟩]

/-- The ring, and each pseudonym's stake on the claim: 5000 of stated capacity each way. -/
def ringAndStakes : List CapEdge :=
  [⟨pseudonym 0, pseudonym 1, 1000⟩, ⟨pseudonym 1, pseudonym 2, 1000⟩,
    ⟨pseudonym 2, pseudonym 3, 1000⟩, ⟨pseudonym 3, pseudonym 4, 1000⟩,
    ⟨pseudonym 4, pseudonym 0, 1000⟩,
    ⟨pseudonym 0, auditClaim, 1000⟩, ⟨pseudonym 1, auditClaim, 1000⟩,
    ⟨pseudonym 2, auditClaim, 1000⟩, ⟨pseudonym 3, auditClaim, 1000⟩,
    ⟨pseudonym 4, auditClaim, 1000⟩]

def ringNet : List CapEdge := inbound ++ ringAndStakes

-- The minimum cut over all 128 node sets is 1000, not 5000.
example : effectiveTrustCapacity ringNet root auditClaim = 1000 := by decide +kernel

/-- Five chains root → pseudonym → claim, 200 each. -/
def ringPacking : List (Nat × List Nat) :=
  [(200, [0, 10]), (200, [1, 11]), (200, [2, 12]), (200, [3, 13]), (200, [4, 14])]

-- The linear certificate: that packing, and the cut around the root alone.
example : certifyTrustCapacity ringNet root auditClaim ringPacking [] = some 1000 := by
  decide +kernel

example : effectiveTrustCapacity ringNet root auditClaim = 1000 :=
  certifyTrustCapacity_exact (packing := ringPacking) (S := []) (by decide +kernel)

-- A sixth chain around the ring finds the root's edge already spent.
example : packingValue root auditClaim ringNet (ringPacking ++ [(200, [0, 5, 11])]) = none := by
  decide +kernel

-- The stated 5000 does not pack: no root edge carries 1000.
example : packingValue root auditClaim ringNet
    [(1000, [0, 10]), (1000, [1, 11]), (1000, [2, 12]), (1000, [3, 13]), (1000, [4, 14])] = none := by
  decide +kernel

-- A chain that does not start at the root, and one that does not reach the claim, are no evidence.
example : packingValue root auditClaim ringNet [(100, [5, 11])] = none := by decide +kernel
example : packingValue root auditClaim ringNet [(100, [0, 5])] = none := by decide +kernel

-- The cut around the root is not the only one; the cut that isolates the claim is worth 5000.
example : cutCapacity ringNet (fun v => decide (v ≠ auditClaim)) = 5000 := by decide +kernel

/-- The adversary's region: the pseudonyms and the claim they stake on. -/
def inRegion (v : TrustNode) : Bool :=
  memB v [auditClaim, pseudonym 0, pseudonym 1, pseudonym 2, pseudonym 3, pseudonym 4]

theorem sumBy_append {α : Type} (f : α → Nat) :
    ∀ l₁ l₂ : List α, sumBy f (l₁ ++ l₂) = sumBy f l₁ + sumBy f l₂
  | [], _ => by simp [sumBy]
  | a :: l, l₂ => by simp [sumBy, sumBy_append f l l₂, Nat.add_assoc]

theorem sumBy_zero {α : Type} {f : α → Nat} : ∀ {l : List α}, (∀ a ∈ l, f a = 0) → sumBy f l = 0
  | [], _ => rfl
  | a :: l, h => by
    simp [sumBy, h a List.mem_cons_self, sumBy_zero fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The bound does not depend on the wiring. Whatever edges leave the region's nodes (any number,
any capacity, rings, self-vouches), the claim receives at most the 1000 that entered. -/
theorem any_wiring_inside_the_region_is_capped (wiring : List CapEdge)
    (hw : ∀ e ∈ wiring, inRegion e.src = true) :
    effectiveTrustCapacity (inbound ++ wiring) root auditClaim ≤ 1000 := by
  refine (sybilSplit_non_amplifying (inbound ++ wiring) inRegion 1000 (by decide +kernel)
    (by decide +kernel) ?_).1 (by decide +kernel)
  have h1 : sumBy (fun e => if !inRegion e.src && inRegion e.dst then e.cap else 0) inbound =
      1000 := by decide +kernel
  have h2 : sumBy (fun e => if !inRegion e.src && inRegion e.dst then e.cap else 0) wiring = 0 :=
    sumBy_zero fun e he => by simp [hw e he]
  unfold externalInflow
  rw [sumBy_append, h1, h2]
  exact Nat.le_refl _

example : effectiveTrustCapacity ringNet root auditClaim ≤ 1000 :=
  any_wiring_inside_the_region_is_capped ringAndStakes (by decide +kernel)

-- With the region deleted nothing reaches the claim, and the second half of the theorem says the
-- region adds at most what entered it.
example : effectiveTrustCapacity (honestSubnet ringNet inRegion) root auditClaim = 0 := by
  decide +kernel

/-! ## 2. A judged slash -/

def falseTally : TallyClaim := ⟨[1, 2], 4⟩
def trueTally : TallyClaim := ⟨[1, 2], 3⟩

-- The judge: accepts the true tally, refutes the false one, and decides neither below the grade.
example : tallyJudge.check 2 trueTally () = .ok := rfl
example : refutationHolds trueTally 2 () = false := by decide +kernel
example : refutationHolds falseTally 2 () = true := by decide +kernel
example : refutationHolds falseTally 1 () = false := by decide +kernel
example : ¬ tallyJudge.Meaning falseTally () := refutationHolds_sound (grade := 2) (cert := ())
  (by decide +kernel) ()
example : tallyDigest falseTally ≠ tallyDigest trueTally := by decide +kernel

/-- Principal 0 is the hunter; 1 stakes on the false tally; 2 stakes on principal 1; 3 stakes on
the true tally. The book is treasury, then free and bonded per principal. -/
def genesis : MarketState := ⟨0, [0, 10, 0, 100, 0, 100, 0, 100, 0], [], [], []⟩

def onFalse : VouchEdge := ⟨1, .claim (tallyDigest falseTally), 60, 5000, 4⟩
def onVoucher : VouchEdge := ⟨2, .principal 1, 40, 2500, 4⟩
def onTrue : VouchEdge := ⟨3, .claim (tallyDigest trueTally), 50, 10000, 4⟩

def opening : List (MarketTurn TallyClaim Unit) :=
  [.depositBond 1 80, .depositBond 2 50, .depositBond 3 70, .addVouch onFalse, .addVouch onVoucher,
    .addVouch onTrue, .advanceEpoch, .challengeClaim 0 (tallyDigest falseTally)]

/-- After the opening: the fee is paid, the challenge is open until epoch 3. -/
def preSlash : MarketState :=
  ⟨1, [1, 9, 0, 20, 80, 50, 50, 30, 70], [onTrue, onVoucher, onFalse],
    [⟨tallyDigest falseTally, 0, 3⟩], []⟩

/-- After the slash: 30 seized from principal 1 and 10 from principal 2; 7 + 2 to the hunter,
23 + 8 to the treasury; principal 3 and its vouch as they were. -/
def postSlash : MarketState := ⟨1, [32, 18, 0, 20, 50, 50, 40, 30, 70], [onTrue], [], []⟩

example : runMarket tallyMarket genesis opening = some preSlash := by decide +kernel

example : slashRefutedClaim tallyMarket preSlash 0 falseTally 2 () = some postSlash := by
  decide +kernel

-- The trust the false tally had before the slash: 30 from its voucher's bond.
example : effectiveTrustCapacity (trustNetwork preSlash) (.principal 1)
    (.claim (tallyDigest falseTally)) = 30 := by decide +kernel
-- From principal 2 it is the bottleneck of the two vouches, and the cap of principal 2's bond holds.
example : effectiveTrustCapacity (trustNetwork preSlash) (.principal 2)
    (.claim (tallyDigest falseTally)) = 10 := by decide +kernel
example : effectiveTrustCapacity (trustNetwork preSlash) (.principal 2)
    (.claim (tallyDigest falseTally)) ≤ bonded preSlash 2 :=
  trust_bounded_by_bond (trace_preserves_inv ((validTrace_iff_run tallyMarket).2
    (by decide +kernel : runMarket tallyMarket genesis opening = some preSlash))
    (marketInv_genesis _ _)) 2 (by decide +kernel)
-- After it, none.
example : effectiveTrustCapacity (trustNetwork postSlash) (.principal 1)
    (.claim (tallyDigest falseTally)) = 0 := by decide +kernel

-- Value is conserved over the whole trace, and the books differ by a conserved value.
example : totalValue postSlash = totalValue genesis ∧ BookDelta genesis.book postSlash.book :=
  validMarketTrace_conserves_total_value (P := tallyMarket)
    (turns := opening ++ [.slashRefuted 0 falseTally 2 ()])
    ((validTrace_iff_run tallyMarket).2 (by decide +kernel))
example : totalValue postSlash = 310 := by decide +kernel

-- The claim was false, and the hunter held an open challenge on its digest.
example : (∀ c : Unit, ¬ tallyJudge.Meaning falseTally c) ∧ ∃ ch ∈ preSlash.challenges,
    ch.claim = tallyDigest falseTally ∧ ch.challenger = 0 ∧ preSlash.epoch < ch.deadline :=
  slash_only_refuted (P := tallyMarket) (st' := postSlash) (hunter := 0) (claim := falseTally)
    (grade := 2) (cert := ()) (by decide +kernel)

-- Principal 3 is in no genealogy of the false tally: bond, free balance and vouch are untouched.
example : bonded postSlash 3 = bonded preSlash 3 ∧
    (3 ≠ 0 → freeBal postSlash 3 = freeBal preSlash 3) ∧
    ∀ e ∈ preSlash.edges, e.voucher = 3 → e ∈ postSlash.edges :=
  honest_uninvolved_vouchers_untouched (P := tallyMarket) (hunter := 0) (claim := falseTally)
    (grade := 2) (cert := ()) (by decide +kernel) 3 fun e he hv hb => by
      have hall : (preSlash.edges.all fun e => !(decide (e.voucher = 3) &&
          slashHit tallyMarket.horizon preSlash (tallyDigest falseTally) e)) = true := by
        decide +kernel
      have hhit : slashHit tallyMarket.horizon preSlash (tallyDigest falseTally) e = true :=
        slashHit_iff.2 hb
      have := List.all_eq_true.1 hall e he
      simp [hv, hhit] at this

-- The hunter and the treasury received the whole slashable capacity: 30 + 10.
example : bal postSlash.book treasuryAcct + freeBal postSlash 0 =
    bal preSlash.book treasuryAcct + freeBal preSlash 0 + 40 := by decide +kernel

-- The voucher for the voucher is in the genealogy at depth 1 and not at depth 0.
example : inGenealogy preSlash.edges (tallyDigest falseTally) 1 onVoucher = true ∧
    inGenealogy preSlash.edges (tallyDigest falseTally) 0 onVoucher = false ∧
    inGenealogy preSlash.edges (tallyDigest falseTally) 1 onTrue = false := by decide +kernel

-- What cannot be slashed: a true tally under challenge, a false one with no challenge, a false
-- one by someone who did not open the challenge, and a false one at a grade that does not cover it.
example : runMarket tallyMarket preSlash
    [.challengeClaim 0 (tallyDigest trueTally), .slashRefuted 0 trueTally 2 ()] = none := by
  decide +kernel
example : slashRefutedClaim tallyMarket { preSlash with challenges := [] } 0 falseTally 2 () =
    none := by decide +kernel
example : slashRefutedClaim tallyMarket preSlash 3 falseTally 2 () = none := by decide +kernel
example : slashRefutedClaim tallyMarket preSlash 0 falseTally 1 () = none := by decide +kernel
-- A challenge that has lapsed slashes nothing either.
example : runMarket tallyMarket preSlash
    [.advanceEpoch, .advanceEpoch, .slashRefuted 0 falseTally 2 ()] = none := by decide +kernel

-- Each refusal is a named violation.
example : MarketViolation tallyMarket preSlash (.slashRefuted 0 falseTally 1 ()) :=
  (marketStep_skip_implies_violation tallyMarket preSlash _).1 (by decide +kernel)

/-! ## 3. Hit and run -/

def soloGenesis : MarketState := ⟨0, [0, 10, 0, 100, 0], [], [], []⟩
def staked : List (MarketTurn TallyClaim Unit) := [.depositBond 1 80, .addVouch onFalse]

def after (turns : List (MarketTurn TallyClaim Unit)) : Option MarketState :=
  runMarket tallyMarket soloGenesis (staked ++ turns)

-- 60 of the 80 bonded are locked until epoch 4: only the other 20 can be asked for.
example : after [.requestUnbond 1 60] = none := by decide +kernel
example : after [.requestUnbond 1 21] = none := by decide +kernel
example : (after [.requestUnbond 1 20]).isSome = true := by decide +kernel
-- Nor can the locked stake be vouched twice.
example : after [.addVouch ⟨1, .principal 0, 21, 10000, 4⟩] = none := by decide +kernel
-- A vouch must be locked for the challenge window, must lose something, and cannot lose more
-- than it stakes.
example : after [.addVouch ⟨1, .principal 0, 5, 10000, 1⟩] = none := by decide +kernel
example : after [.addVouch ⟨1, .principal 0, 5, 0, 4⟩] = none := by decide +kernel
example : after [.addVouch ⟨1, .principal 0, 5, 10001, 4⟩] = none := by decide +kernel

-- The unbond of the free 20 has a cooldown of 3 epochs: refused at epochs 0, 1 and 2, paid at 3.
example : after [.requestUnbond 1 20, .finalizeUnbond 1] = none := by decide +kernel
example : after [.requestUnbond 1 20, .advanceEpoch, .advanceEpoch, .finalizeUnbond 1] = none := by
  decide +kernel
example : (after [.requestUnbond 1 20, .advanceEpoch, .advanceEpoch, .advanceEpoch,
    .finalizeUnbond 1]).map (fun st => (freeBal st 1, bonded st 1)) = some (40, 60) := by
  decide +kernel
-- It is paid once.
example : after [.requestUnbond 1 20, .advanceEpoch, .advanceEpoch, .advanceEpoch,
    .finalizeUnbond 1, .finalizeUnbond 1] = none := by decide +kernel

/-- Three quiet epochs, then a challenge at epoch 3: the stake that would have unlocked at 4 is
held to the challenge's deadline, 5. -/
def challengedAtThree : List (MarketTurn TallyClaim Unit) :=
  [.advanceEpoch, .advanceEpoch, .advanceEpoch, .challengeClaim 0 (tallyDigest falseTally)]

example : (after challengedAtThree).map (fun st => st.edges.map (·.unlockEpoch)) = some [5] := by
  decide +kernel
-- At epoch 4, past the original unlock, the stake is still held and still slashable.
example : after (challengedAtThree ++ [.advanceEpoch, .requestUnbond 1 60]) = none := by
  decide +kernel
example : (after (challengedAtThree ++ [.advanceEpoch, .slashRefuted 0 falseTally 2 ()])).map
    (fun st => (bonded st 1, freeBal st 0, bal st.book treasuryAcct)) = some (50, 16, 24) := by
  decide +kernel

/-- No refutation arrives. The challenge lapses at 5, the voucher asks for the whole stake, waits
out the cooldown, and leaves with all 100 units. -/
def honestExit : List (MarketTurn TallyClaim Unit) :=
  challengedAtThree ++ [.advanceEpoch, .advanceEpoch, .requestUnbond 1 80, .advanceEpoch,
    .advanceEpoch, .advanceEpoch, .finalizeUnbond 1]

example : (after honestExit).map (fun st => (st.epoch, freeBal st 1, bonded st 1)) =
    some (8, 100, 0) := by decide +kernel

-- The universal theorem on this trace: every reachable state keeps the four guarantees.
example (st' : MarketState) (h : after honestExit = some st') (p : Nat)
    (hcool : ∀ r ∈ st'.unbonds, r.principal = p → st'.epoch < r.cooldownExpiry) :
    stepEpistemicMarket tallyMarket st' (.finalizeUnbond p : MarketTurn TallyClaim Unit) = none :=
  (cooldown_prevents_hit_and_run (marketInv_genesis tallyMarket _)
    ((validTrace_iff_run tallyMarket).2 h)).2.2.2 p hcool

-- And its converse: a matured request in a reachable state is always paid.
example (st : MarketState) (turns : List (MarketTurn TallyClaim Unit))
    (h : ValidEpistemicMarketTrace tallyMarket soloGenesis turns st) (r : UnbondRequest)
    (hr : r ∈ st.unbonds) (hexp : r.cooldownExpiry ≤ st.epoch) :
    (stepEpistemicMarket tallyMarket st
      (.finalizeUnbond r.principal : MarketTurn TallyClaim Unit)).isSome = true := by
  obtain ⟨st', _, hs, _⟩ := post_cooldown_unbond_succeeds (Cert := Unit)
    (trace_preserves_inv h (marketInv_genesis tallyMarket _)) hr hexp
  rw [hs]; rfl

/-! ## 4. Teeth -/

-- Slash on any run of the judge, refuting or not.
#tooth Obend.Polis.EpistemicVouchMarket.slash_only_refuted by mutation
  Obend.Polis.EpistemicVouchMarket.refutationHolds := fun _ _ _ => true

-- Pay the hunter and let the remainder vanish instead of reaching the treasury.
#tooth Obend.Polis.EpistemicVouchMarket.slash_conserves_total_value by mutation
  Obend.Polis.EpistemicVouchMarket.seize := fun bps hunter e L =>
    debit (transfer L (bondAcct e.voucher) (freeAcct hunter) (seizable e L * bps / 10000))
      (bondAcct e.voucher) (seizable e L - seizable e L * bps / 10000)

-- Seize from every vouch, in the genealogy or not.
#tooth Obend.Polis.EpistemicVouchMarket.honest_uninvolved_vouchers_untouched by mutation
  Obend.Polis.EpistemicVouchMarket.slashStep := fun bps hunter _ e L => seize bps hunter e L

-- Pay an unbond without waiting for its cooldown.
#tooth Obend.Polis.EpistemicVouchMarket.unbond_only_after_cooldown by mutation
  Obend.Polis.EpistemicVouchMarket.matured := fun _ p r => decide (r.principal = p)

-- Accept vouches and unbond requests without looking at the bond.
#tooth Obend.Polis.EpistemicVouchMarket.step_preserves_inv by mutation
  Obend.Polis.EpistemicVouchMarket.collateralized := fun _ _ _ => true

-- Let a challenge leave the locks as they were.
#tooth Obend.Polis.EpistemicVouchMarket.step_preserves_inv by mutation
  Obend.Polis.EpistemicVouchMarket.extendLock := fun _ _ e => e

-- Count no capacity as entering a region.
#tooth Obend.Polis.EpistemicVouchMarket.sybilSplit_non_amplifying by mutation
  Obend.Polis.EpistemicVouchMarket.externalInflow := fun _ _ => 0

-- A cut that every edge crosses for free.
#tooth Obend.Polis.EpistemicVouchMarket.vouchPacking_le_cut by mutation
  Obend.Polis.EpistemicVouchMarket.crossing := fun _ _ => 0

-- A root side that may hold the target is no cut.
#tooth Obend.Polis.EpistemicVouchMarket.certifyTrustCapacity_exact by mutation
  Obend.Polis.EpistemicVouchMarket.rootSide := fun r _ S v => decide (v = r) || memB v S

-- Forget that the loss fraction is in basis points.
#tooth Obend.Polis.EpistemicVouchMarket.trust_bounded_by_bond by mutation
  Obend.Polis.EpistemicVouchMarket.slashableCapacity := fun e => e.stake * e.lossBps

-- Refuse nothing for a lock shorter than the challenge window.
#tooth Obend.Polis.EpistemicVouchMarket.marketStep_skip_implies_violation by mutation
  Obend.Polis.EpistemicVouchMarket.lockCoversWindow := fun _ _ _ => true

#assert_axioms_tree

end Obend.Tests.Metasystem.EpistemicVouchMarketTest
end
