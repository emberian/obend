module
/-
# FrustumLivingScreenshotTest — a frustum, a screenshot cut from it, its return, and a cited quote

Runs `Obend.Vault.FrustumMembrane` and `Obend.Vault.TransclusionAndMirror` on one small world.

1. **Frustum.** `alice` reaches `bob`, `carol`, `treasury`, `oracle` and `sink`; not `vault` (no
   capability names it), not `blind` (her capability carries no `read`), not `ghost` (not on the
   ledger). The hidden cell is rewritten and deleted, and a sealed slot's cleartext replaced.
2. **Screenshot.** `{alice, bob}` is cut out: the capability to `treasury` is attenuated to a
   residual, to `oracle` severed, to `sink` interposed. A form is filled offline, turns are run
   against the screenshot, and it is re-grafted; stale and unbalanced returns are refused by name.
3. **Replay and negotiation.** A confined trace under two environments; an ambient one; a
   three-party negotiation in which the third party names a cell the granter never held.
4. **Transclusion and the mirror badge.** A truthful quote, a forged one, the source advancing, and
   the badge of a render nobody checked.
5. **Teeth.** Each `#tooth` replaces one real check and requires the kernel to reject the stored
   proof of a universal theorem that rested on it.

Kernel `decide` is used wherever no hash has to be computed; runs that compute cSHAKE256 are
`#guard`s, since the kernel does not evaluate Keccak in useful time. `#assert_axioms_tree` needs the
bodies of the whole import closure, hence the `import all` block.
-/

public import Obend.Vault.FrustumMembrane
public import Obend.Vault.TransclusionAndMirror
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import Obend.Vault.FrustumMembrane
meta import Obend.Vault.TransclusionAndMirror
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Doc
import all Obend.Doc.Backlinks
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.ReactiveNotebook
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Logic.SuperRefines
import all Obend.Polis.VerkleUmem
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Core4
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.SupportSheaf
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Form
import all Obend.Vault.FrustumMembrane
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Law
import all Obend.Vault.Page
import all Obend.Vault.Rehydration
import all Obend.Vault.Store
import all Obend.Vault.TransclusionAndMirror

public section

namespace Obend.Tests.Metasystem.FrustumLivingScreenshotTest

open Obend.Core.Data (Data)
open Obend.Spec.Law (Facts)
open Obend.Vault (natAt)
open Obend.Vault.Affordance (Auth GatedAffordance)
open Obend.Vault.Rehydration (AttestedRoot Interaction InteractionLog confined Rehydration
  MembraneViewer)
open Obend.Vault.Form (NExpr PRef Known Assignment)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Digest.HashBytes (CollisionAmong)
open Obend.Vault.FrustumMembrane
open Obend.Vault.TransclusionAndMirror

set_option autoImplicit false

/-! ## 1. The frustum -/

/-- An affordance lit under the rights `need` while the cell's balance is at most `cap`. -/
def gated (name : String) (need : List Auth) (cap : Int) : GatedAffordance Unit :=
  { aff := ⟨need, (), name⟩, law := .leC (.field "balance") cap, fields := ["balance"] }

def bobRecord : CellRecord :=
  { state := .record [("balance", .natural 7)], sealed := [("pin", ⟨[1, 2, 3], [9]⟩)],
    caps := [⟨"carol", [.read]⟩],
    surface := [gated "credit" [.write] 50, gated "seize" [.grant] 50] }

/-- `alice` holds `read` over five cells, one of them absent, and `write` without `read` over
`blind`; `vault` holds a capability to `alice`, and nobody holds one to `vault`. -/
def world : World :=
  World.ofList ⟨none, none, 0, 0⟩
    [("alice", { state := .record [("balance", .natural 5)],
                 caps := [⟨"alice", [.read, .write]⟩, ⟨"bob", [.read, .write]⟩,
                          ⟨"treasury", [.read]⟩, ⟨"oracle", [.read]⟩, ⟨"sink", [.read, .write]⟩,
                          ⟨"ghost", [.read]⟩, ⟨"blind", [.write]⟩] }),
     ("bob", bobRecord),
     ("carol", { state := .record [("balance", .natural 1)] }),
     ("treasury", { state := .record [("balance", .natural 100), ("reserved", .natural 40)],
                    surface := [gated "audit" [.read] 50, gated "peek" [.read] 1000] }),
     ("oracle", { state := .record [("price", .natural 3)] }),
     ("sink", { state := .record [("balance", .natural 0)] }),
     ("blind", { state := .record [("balance", .natural 50)] }),
     ("vault", { state := .record [("balance", .natural 1000)],
                 caps := [⟨"alice", [.read, .write]⟩] })]

example : world.visible "alice" = ["alice", "bob", "treasury", "oracle", "sink", "carol"] := by
  decide

example : world.canObserve "alice" "vault" = false ∧ world.canObserve "alice" "blind" = false ∧
    world.canObserve "alice" "ghost" = false ∧ world.canObserve "vault" "alice" = true := by decide

example : (Frustum.project world "alice").cells.map (·.1) =
    ["alice", "bob", "carol", "treasury", "oracle", "sink"] := by decide

example : (Frustum.project world "alice").reflect "vault" = none :=
  frustum_unobservable_absent fun h => absurd (canObserve_iff.mpr h) (by decide)

/-- The affordances `alice` may fire: on `bob` what `write` lights (not what `grant` would), on
the treasury what its state allows. -/
example : ((Frustum.project world "alice").reflect "bob").map (·.lit) = some ["credit"] ∧
    ((Frustum.project world "alice").reflect "treasury").map (·.lit) = some ["peek"] := by decide

/-- Whatever is written to the hidden cell, and if it is deleted, `alice`'s frustum is the same. -/
example (r : CellRecord) :
    Frustum.project (world.set "vault" r) "alice" = Frustum.project world "alice" ∧
    Frustum.project (world.erase "vault") "alice" = Frustum.project world "alice" :=
  hidden_cell_mutation_invisible (fun h => absurd (canObserve_iff.mpr h) (by decide)) r

/-- Any cleartext behind `bob`'s sealed slot with the same commitment shows `alice` the same. -/
example (sealed' : List (String × SealedSlot))
    (h : sealed'.map (fun e => (e.1, sealCommit e.2)) =
      bobRecord.sealed.map (fun e => (e.1, sealCommit e.2))) :
    Frustum.project (world.set "bob" { bobRecord with sealed := sealed' }) "alice" =
      Frustum.project (world.set "bob" bobRecord) "alice" :=
  frustum_committed_field_hides_value world "alice" "bob" bobRecord sealed' h

-- The sealed slot is shown as 32 bytes, the commitment of the secret and the salt.
#guard (((Frustum.project world "alice").reflect "bob").map fun v => v.sealed.map (·.2)) ==
  some [sealCommit ⟨[1, 2, 3], [9]⟩]
#guard (sealCommit ⟨[1, 2, 3], [9]⟩).size == 32
#guard sealCommit ⟨[1, 2, 3], [9]⟩ != sealCommit ⟨[1, 2, 3], [8]⟩
#guard sealCommit ⟨[1, 2, 3], [9]⟩ != sealCommit ⟨[1, 2], [3, 9]⟩

/-! ## 2. The living screenshot -/

/-- What `alice` may draw: the treasury's balance less its reserve, less the amount drawn. -/
def available : NExpr :=
  .sub (.sub (.field (.page "treasury") "balance") (.field (.page "treasury") "reserved"))
    (.hole "draw")

def witnessed : InteractionLog := [.attested ⟨0, true, true⟩]

def policy : CellId → Cap → Disposition := fun _ cap =>
  if cap.target == "treasury" then .attenuate { held := [.read], permits := fun _ => true } available
  else if cap.target == "oracle" then .sever witnessed
  else .interpose (.record [("balance", .natural 0)])

def shot : Screenshot := (Frustum.project world "alice").snip ["alice", "bob"] policy ["balance"]

example : shot.interior.map (·.id) = ["alice", "bob"] := by decide

example : shot.pins.map (fun p => (p.holder, p.target)) =
    [("alice", "treasury"), ("alice", "oracle"), ("alice", "sink"), ("alice", "ghost"),
     ("alice", "blind"), ("bob", "carol")] := by decide

def residualAt (s : Screenshot) (target : CellId) : Option NExpr :=
  s.pins.findSome? fun p =>
    if p.target == target then
      match p.face with
      | .attenuated _ r => some r
      | _ => none
    else none

/-- The treasury's two slots are gone from the residual; their difference is what is left. -/
example : residualAt shot "treasury" = some (.sub (.lit 60) (.hole "draw")) := by decide

/-- The form filled offline: no page is read to evaluate it. -/
example : ((NExpr.sub (.lit 60) (.hole "draw")).subst { nats := [("draw", 25)] }).eval
    (fun _ => none) = some 35 := by decide

/-- The residual and the original agree under any knowledge that has the treasury as captured. -/
example (a : Assignment) (k : Known)
    (hk : Obend.Vault.Form.Agrees (backingKnown (Frustum.project world "alice") "treasury") k) :
    ((available.peval (backingKnown (Frustum.project world "alice") "treasury")).subst a).eval k =
      (available.subst a).eval k :=
  attenuate_preserves_public_semantics _ "treasury" available a k hk

example : shot.pins.map (·.face.liveness) =
    [.Live, .ReplayedDeterministic, .ReplayedDeterministic, .ReplayedDeterministic,
     .ReplayedDeterministic, .ReplayedDeterministic] := by decide

/-- A severed pin with an ambient reach in its log is a reconstruction, not a replay. -/
example (f : Frustum) (cap : Cap) :
    (makeFace f cap (.sever [.attested ⟨0, true, true⟩, .ambient])).liveness ≠
      .ReplayedDeterministic := fun h =>
  absurd ((sever_promotes_replayed_deterministic f cap _).2.2.1.mp h) (by decide)

def turns : List LocalTurn :=
  [.edit "alice" "balance" 3, .edit "bob" "balance" 9, .viaPin "alice" "sink" "balance" 99,
   .viaPin "alice" "treasury" "balance" 0, .viaPin "alice" "oracle" "price" 1]

def after : Sys := runSys ⟨world, shot⟩ turns

example : after.shot.interior.map (fun x => (x.id, natAt x.now "balance")) =
    [("alice", 3), ("bob", 9)] := by decide

/-- The write through the interposed pin landed on the stand-in. -/
example : (after.shot.pins.filterMap fun p => match p.face with
    | .interposed m => if p.target == "sink" then some (natAt m "balance") else none
    | _ => none) = [99] := by decide

/-- No pin of the screenshot is tethered, so after these turns every upstream cell is as it was. -/
example (u : CellId) : after.upstream.cell u = world.cell u :=
  (interposed_frustum_never_touches_severed_upstream turns ⟨world, shot⟩ u fun p hp _ => by
    have hall : (shot.pins.all fun p => !p.face.isTethered) = true := by decide
    simpa using List.all_eq_true.mp hall p hp).1

/-- With the same pin tethered the same turn does write upstream: the theorem's premise matters. -/
example : (runSys ⟨world, (Frustum.project world "alice").snip ["alice", "bob"]
      (fun _ _ => .tether) ["balance"]⟩ [.viaPin "alice" "sink" "balance" 99]).upstream.balance
      "balance" "sink" = 99 := by decide

def refusal (r : Except RegraftRefusal World) : Option RegraftRefusal :=
  match r with
  | .ok _ => none
  | .error e => some e

def landed (r : Except RegraftRefusal World) (cells : List CellId) : Option (List (Nat × Nat)) :=
  match r with
  | .ok w => some (cells.map fun c => (w.balance "balance" c, ((w.cell c).map (·.epoch)).getD 0))
  | .error _ => none

-- The edited interior lands whole: 5 + 7 = 3 + 9, each epoch advanced; the treasury is untouched.
#guard landed (regraftFrustum world after.shot) ["alice", "bob", "treasury"] ==
  some [(3, 1), (9, 1), (100, 0)]
-- A cell outside the cut changed while the screenshot was away: its change survives the return.
#guard landed (regraftFrustum (world.poke "vault" "balance" 7) after.shot) ["alice", "vault"] ==
  some [(3, 1), (7, 1)]
-- So does a change to the cell behind the interposed pin: its stand-in was local.
#guard landed (regraftFrustum (world.poke "sink" "balance" 4) after.shot) ["bob", "sink"] ==
  some [(9, 1), (4, 1)]
-- An interior cell moved upstream: refused, naming it.
#guard refusal (regraftFrustum (world.poke "bob" "balance" 8) after.shot) ==
  some (.staleInterior "bob")
-- The severed pin's target moved: refused, naming the pin.
#guard refusal (regraftFrustum (world.poke "oracle" "price" 4) after.shot) ==
  some (.staleBoundary "alice" "oracle")
-- An edit that does not conserve the declared field: refused, naming the field.
#guard refusal (regraftFrustum world (runSys ⟨world, shot⟩ [.edit "alice" "balance" 4]).shot) ==
  some (.unbalanced "balance")
-- A screenshot held by a viewer without `write` over its interior does not land.
#guard refusal (regraftFrustum world { after.shot with viewer := "vault" }) ==
  some (.staleInterior "bob")

/-- Without a severed pin the whole return is a kernel computation. -/
example : landed (regraftFrustum world (runSys ⟨world, (Frustum.project world "alice").snip
      ["alice", "bob"] (fun _ _ => .interpose (.record [])) ["balance"]⟩
      [.edit "alice" "balance" 12, .edit "bob" "balance" 0]).shot) ["alice", "bob"] =
    some [(12, 1), (0, 1)] := by decide

/-- Whatever world an admitted return produces, the hidden cell is in it as it was, and the
balance over the interior and the treasury is what it was. -/
example (w' : World) (h : regraftFrustum world after.shot = .ok w') :
    w'.cell "vault" = world.cell "vault" ∧
    w'.total "balance" (after.shot.interior.map (·.id) ++ ["treasury"]) =
      world.total "balance" (after.shot.interior.map (·.id) ++ ["treasury"]) := by
  have hout : ∀ c, c = "vault" ∨ c = "treasury" → ∀ x, x ∈ after.shot.interior → x.id ≠ c := by
    intro c hc x hx
    have hall : (after.shot.interior.all fun x => x.id != "vault" && x.id != "treasury") = true := by
      decide
    have hx' := List.all_eq_true.mp hall x hx
    simp only [Bool.and_eq_true, bne_iff_ne] at hx'
    rcases hc with rfl | rfl
    · exact hx'.1
    · exact hx'.2
  obtain ⟨_, hframe, hcons, _⟩ := regraftFrustum_atomic_conserving h
  exact ⟨hframe "vault" (hout "vault" (.inl rfl)),
    hcons "balance" (by decide) ["treasury"] fun c hc => by
      have hct : c = "treasury" := by simpa using hc
      exact hout c (.inr hct)⟩

/-! ## 3. Replay and negotiation -/

def addRoot : Nat → AttestedRoot → Nat := fun s ar => s + ar.root

/-- A confined trace: the fold moves, and lands on the same state under every environment. -/
example (env₁ env₂ : Nat) :
    replayState (envStep addRoot (fun _ e => e) env₁) 0
        [.attested ⟨42, true, true⟩, .attested ⟨42, true, true⟩] =
      replayState (envStep addRoot (fun _ e => e) env₂) 0
        [.attested ⟨42, true, true⟩, .attested ⟨42, true, true⟩] :=
  confined_replay_env_independent addRoot _ env₁ env₂ _ 0 (by decide)

example (env : Nat) : replayState (envStep addRoot (fun _ e => e) env) 0
    [.attested ⟨42, true, true⟩, .attested ⟨42, true, true⟩] = 84 := by
  simp [replayState, envStep, addRoot]

/-- One ambient step: two environments, two states. -/
example : replayState (envStep addRoot (fun _ e => e) 0) 0 [.ambient] ≠
    replayState (envStep addRoot (fun _ e => e) 1) 0 [.ambient] :=
  (ambient_replay_env_dependent addRoot [] 0 0 1 (by decide)).2

/-- The granter: read, write and grant over `ledger`, until height 100. -/
def heldA : NegCap := ⟨"ledger", [.read, .write, .grant], [.notAfter 100]⟩
/-- The first requester: read and write, for amounts up to 5. -/
def askB : NegCap := ⟨"ledger", [.read, .write], [.amountAtMost 5]⟩
/-- The second requester names a cell the granter's capability never named. -/
def askC : NegCap := ⟨"vault", [.read, .write], []⟩
/-- A third asks for a right the granter never held. -/
def askD : NegCap := ⟨"ledger", [.read, .call], []⟩

example : (negotiate heldA askB).confers "ledger" .write ⟨50, 3⟩ = true ∧
    (negotiate heldA askB).confers "ledger" .write ⟨50, 9⟩ = false ∧
    (negotiate heldA askB).confers "ledger" .write ⟨101, 3⟩ = false ∧
    (negotiate heldA askB).confers "ledger" .grant ⟨50, 3⟩ = false := by decide

/-- A to B to C: the third party's ask confers nothing over `vault`, whatever the right. -/
example (a : Auth) (ctx : NegCtx) :
    (negotiate (negotiate heldA askB) askC).confers "vault" a ctx = false :=
  deputy_cannot_retarget (negotiate heldA askB) askC "vault" (by decide) a ctx

/-- Nor does it keep anything over `ledger`: an ask aimed elsewhere is an empty meet. -/
example : (negotiate (negotiate heldA askB) askC).confers "ledger" .read ⟨50, 3⟩ = false := by
  decide

/-- The over-asked `call` is not conferred. -/
example (ctx : NegCtx) : (negotiate heldA askD).confers "ledger" .call ctx = false :=
  (deputy_confers_no_unheld_target heldA askD "ledger" .call ctx (by
    simp [NegCap.confers, heldA])).1

/-- The chain through B then D confers what the chain through D then B does. -/
example (t : CellId) (a : Auth) (ctx : NegCtx) :
    (negotiateChain heldA [askB, askD]).confers t a ctx =
      (negotiateChain heldA [askD, askB]).confers t a ctx :=
  (negotiation_path_independent heldA _ _ (List.Perm.swap askD askB []) t a ctx).1

/-! ## 4. Transclusion and the mirror badge -/

/-- A 256-bit salt. -/
def saltOf (b : UInt8) : List UInt8 := List.replicate 32 b

def src : SourceCell :=
  (SourceCell.mk [] []).advance
    [[("title", ⟨[7], saltOf 1⟩), ("body", ⟨[1, 2], saltOf 2⟩)], [("title", ⟨[8], saltOf 3⟩)]]

def firstDigest : ByteArray := (src.observed.head?.map receiptDigest).getD genesisDigest

/-- A truthful quote of the first receipt's title, and a forged one. -/
def truthful : Transclusion := ⟨firstDigest, 0, "title", ⟨[7], saltOf 1⟩⟩
def forged : Transclusion := { truthful with opening := ⟨[99], saltOf 1⟩ }

def quoted (r : Except TransclusionRefusal DatedQuote) : Option DatedQuote :=
  match r with
  | .ok d => some d
  | .error _ => none

def refused (r : Except TransclusionRefusal DatedQuote) : Option TransclusionRefusal :=
  match r with
  | .ok _ => none
  | .error e => some e

#guard linkedFrom genesisDigest 0 src.observed
#guard quoted (admitTransclusion src.observed truthful) == some ⟨[7], 0, 1⟩
#guard refused (admitTransclusion src.observed forged) == some .digestMismatch
-- The head's title is 8; the quote still says 7 and says how old it is.
#guard (quoted (admitTransclusion src.observed truthful)).map (·.staleness) == some 1
-- What the source has staged cannot be cited.
#guard refused (admitTransclusion (src.stage [("title", ⟨[99], saltOf 1⟩)]).observed forged) ==
  some .digestMismatch
-- The right bytes with no salt, and under another field's salt.
#guard refused (admitTransclusion src.observed { truthful with opening := ⟨[7], []⟩ }) ==
  some (.saltWidth 0)
#guard refused (admitTransclusion src.observed { truthful with opening := ⟨[7], saltOf 2⟩ }) ==
  some .digestMismatch
-- A citation of a receipt that is not in the chain, a wrong height, an absent field.
#guard refused (admitTransclusion src.observed { truthful with cited := genesisDigest }) ==
  some .uncitedReceipt
#guard refused (admitTransclusion src.observed { truthful with height := 1 }) ==
  some (.heightMismatch 0)
#guard refused (admitTransclusion src.observed { truthful with field := "footer" }) ==
  some .fieldAbsent
-- Three turns later the same citation is admitted with the same bytes, three receipts staler.
#guard quoted (admitTransclusion
    (src.advance [[("title", ⟨[9], saltOf 4⟩)], [("title", ⟨[10], saltOf 5⟩)],
      [("title", ⟨[11], saltOf 6⟩)]]).observed truthful) ==
  some ⟨[7], 0, 4⟩

/-- However the source advances, the admitted quote is admitted again, dated against the new head. -/
example (d : DatedQuote) (h : admitTransclusion src.observed truthful = .ok d)
    (more : List (List (String × SealedSlot))) :
    admitTransclusion (src.advance more).observed truthful =
      .ok { d with headHeight := d.headHeight + more.length } :=
  (transclusion_stable_under_source_advance h more).1

/-- The admitted opening, bytes and salt, is the slot any receipt with the cited digest holds, or a
collision. -/
example (d : DatedQuote) (h : admitTransclusion src.observed truthful = .ok d) (r₀ : Receipt)
    (hr₀ : r₀ ∈ src.finalized) (hcite : receiptDigest r₀.header = truthful.cited)
    (v : SealedSlot) (hv : r₀.fields.lookup "title" = some v) :
    (⟨[7], saltOf 1⟩ : SealedSlot) = v ∨
      CollisionAmong (cshake256Bytes receiptCustomization)
        (fun x => ∃ hd, hd ∈ src.observed ∧ x = receiptPreimage hd) ∨
      CollisionAmong (cshake256Bytes sealCustomization)
        (fun x => x = sealPreimage (fieldSlot "title" ⟨[7], saltOf 1⟩) ∨
          x = sealPreimage (fieldSlot "title" v)) :=
  (transclusion_provenance_faithful h hr₀ hcite hv).2

/-- The forged quote is refused, or the slots of `[99]` and `[7]` collide under the seal hash. -/
example (d : DatedQuote) (h : admitTransclusion src.observed truthful = .ok d) :
    admitTransclusion src.observed forged = .error .digestMismatch ∨
      CollisionAmong (cshake256Bytes sealCustomization)
        (fun x => x = sealPreimage (fieldSlot "title" ⟨[99], saltOf 1⟩) ∨
          x = sealPreimage (fieldSlot "title" ⟨[7], saltOf 1⟩)) :=
  (transclusion_lying_opening_refused_or_collides (forged := forged) h rfl rfl rfl
    (by decide)).elim .inl
    fun h' => h'.elim
      (fun hw => absurd (by decide : forged.opening.salt.length = 32) hw.1) .inr

/-- A reader with `read` alone: however much it quotes, the source refuses its writes. -/
example (ts : List Transclusion) (fields : List (String × SealedSlot)) :
    serveSource (Document.transcludeAll ⟨[.read], []⟩ src.observed ts) src (.write fields) = none :=
  (transclusion_no_amplify ⟨[.read], []⟩ src ts).2.2.1 (by decide) fields

/-- A server's preview: the reader's machine ran nothing. -/
def nothingRan : VerificationGate → GateOutcome := fun _ => .skipped
/-- The reader ran everything but the replay. -/
def allButReplay : VerificationGate → GateOutcome := fun g =>
  if g = .confinementReplay then .skipped else .passed

def badge (r : Except RenderRefusal MirrorRender) : Option (MirrorTier × List VerificationGate) :=
  match r with
  | .ok m => some (m.tier, m.skipped)
  | .error _ => none

example : badge (classifyMirrorRender nothingRan "page" genesisDigest) =
    some (.untrustedOriginMirror, VerificationGate.all) := by decide

example : badge (classifyMirrorRender allButReplay "page" genesisDigest) =
    some (.untrustedOriginMirror, [.confinementReplay]) := by decide

example : badge (classifyMirrorRender (fun _ => .passed) "page" genesisDigest) =
    some (.selfVerifiedLocal, []) := by decide

-- A badge claiming self-verification over a preview nobody checked does not validate; nor does an
-- untrusted badge that leaves a skipped gate out, or points at another address.
#guard !verifyMirrorBadge nothingRan "page" genesisDigest
  ⟨.selfVerifiedLocal, [], ⟨"page", genesisDigest⟩⟩
#guard !verifyMirrorBadge nothingRan "page" genesisDigest
  ⟨.untrustedOriginMirror, [.receiptChain, .proofSignature], ⟨"page", genesisDigest⟩⟩
#guard !verifyMirrorBadge nothingRan "page" genesisDigest
  ⟨.untrustedOriginMirror, VerificationGate.all, ⟨"page", firstDigest⟩⟩
#guard verifyMirrorBadge nothingRan "page" genesisDigest
  ⟨.untrustedOriginMirror, VerificationGate.all, ⟨"page", genesisDigest⟩⟩
#guard (ObendUri.render ⟨"page", genesisDigest⟩) ==
  "obend://page/" ++ String.ofList (List.replicate 64 '0')
-- The two gates this tree computes: a linked chain passes, a forged quote fails, no chain skips.
#guard chainGate (some src.observed) == .passed
#guard transclusionGate (some src.observed) truthful == .passed
#guard transclusionGate (some src.observed) forged == .failed
#guard (match classifyMirrorRender (fun g => if g = .transclusionProvenance then
    transclusionGate (some src.observed) forged else .passed) "page" genesisDigest with
  | .error (.gateFailed .transclusionProvenance) => true
  | _ => false)

/-- No badge over a preview nobody checked validates as self-verified, whatever it says. -/
example (kind : String) (address : ByteArray) (r : MirrorRender)
    (h : verifyMirrorBadge nothingRan kind address r = true) : r.tier = .untrustedOriginMirror :=
  (serverMirror_never_claims_selfVerified nothingRan kind address r .receiptChain (by decide)).1 h

/-- And the classifier's badge for it lists all five gates and the object's own address. -/
example (kind : String) (address : ByteArray) (r : MirrorRender)
    (h : classifyMirrorRender nothingRan kind address = .ok r) :
    r.skipped = VerificationGate.all ∧ r.upgrade = ⟨kind, address⟩ ∧ address.size = 32 := by
  have htier := (serverMirror_never_claims_selfVerified nothingRan kind address r .receiptChain
    (by decide)).2 h
  obtain ⟨hsk, _, hup, hsize⟩ :=
    serverMirror_reports_all_skipped_gates nothingRan kind address r (.inr h) htier
  exact ⟨hsk.trans (by decide), hup, hsize⟩

/-! ## 5. Teeth -/

-- The crawl follows every capability, read-bearing or not, on the ledger or not.
#tooth Obend.Vault.FrustumMembrane.canObserve_iff by mutation
  Obend.Vault.FrustumMembrane.World.succs := fun w c =>
    match w.pub c with
    | some p => p.caps.map (·.target)
    | none => []

-- The seal leaves the salt out of what it hashes.
#tooth Obend.Vault.FrustumMembrane.sealCommit_binds by mutation
  Obend.Vault.FrustumMembrane.sealCommit := fun s =>
    Obend.Crypto.cshake32ByteArray sealCustomization (Obend.Crypto.encodeListField s.secret)

-- The view shows something other than the commitments.
#tooth Obend.Vault.FrustumMembrane.frustum_sealed_slot_shows_commitment by mutation
  Obend.Vault.FrustumMembrane.viewCell := fun facts held p =>
    { state := p.state, sealed := [], caps := p.caps,
      lit := (Obend.Vault.Affordance.projectGatedFor held facts none p.state p.surface).map
        (·.aff.name),
      epoch := p.epoch }

-- A write through any matching pin reaches upstream, tethered or not.
#tooth Obend.Vault.FrustumMembrane.interposed_frustum_never_touches_severed_upstream by mutation
  Obend.Vault.FrustumMembrane.tetherWrites := fun pins holder target =>
    pins.any fun p => pinMatches holder target p && p.rights.contains Auth.write

-- The return does not look at the interior's epochs or the viewer's rights.
#tooth Obend.Vault.FrustumMembrane.regraftFrustum_atomic_conserving by mutation
  Obend.Vault.FrustumMembrane.interiorFresh := fun _ _ _ => true

-- The return does not check conservation.
#tooth Obend.Vault.FrustumMembrane.regraftFrustum_atomic_conserving by mutation
  Obend.Vault.FrustumMembrane.balanced := fun _ _ _ => true

-- The return does not compare a severed pin's snapshot with its target.
#tooth Obend.Vault.FrustumMembrane.regraft_boundary_fresh_or_collision by mutation
  Obend.Vault.FrustumMembrane.pinFresh := fun _ _ _ => true

-- The replay reads the environment on every step, witnessed or not.
#tooth Obend.Vault.FrustumMembrane.confined_replay_env_independent by mutation
  Obend.Vault.FrustumMembrane.envStep := fun _ amb env s _ => amb s env

-- The negotiation does not compare the ask's target with the granter's.
#tooth Obend.Vault.FrustumMembrane.deputy_confers_no_unheld_target by mutation
  Obend.Vault.FrustumMembrane.negotiate := fun held ask =>
    { target := ask.target, rights := held.rights.filter ask.rights.contains,
      caveats := held.caveats ++ ask.caveats }

-- The admission does not compare the quote's commitment with the receipt's.
#tooth Obend.Vault.TransclusionAndMirror.transclusion_provenance_faithful by mutation
  Obend.Vault.TransclusionAndMirror.admitTransclusion := fun chain t =>
    match chain.find? (fun h => decide (receiptDigest h = t.cited)) with
    | none => .error .uncitedReceipt
    | some h =>
      if h.height = t.height then
        match h.commits.lookup t.field with
        | none => .error .fieldAbsent
        | some _ => .ok ⟨t.opening.secret, t.height, chain.length - 1⟩
      else .error (.heightMismatch h.height)

-- A transclusion hands the document `write` over its source.
#tooth Obend.Vault.TransclusionAndMirror.transclusion_no_amplify by mutation
  Obend.Vault.TransclusionAndMirror.Document.transclude := fun doc chain t =>
    match admitTransclusion chain t with
    | .ok d => { held := Auth.write :: doc.held, quotes := doc.quotes ++ [d] }
    | .error _ => doc

-- The validator accepts a self-verified badge without asking which gates passed.
#tooth Obend.Vault.TransclusionAndMirror.badge_selfVerified_all_passed by mutation
  Obend.Vault.TransclusionAndMirror.verifyMirrorBadge := fun outcomes kind address r =>
    decide (address.size = 32) && decide (r.upgrade = ⟨kind, address⟩) &&
      VerificationGate.all.all (fun g => outcomes g != .failed) &&
      match r.tier with
      | .selfVerifiedLocal => true
      | .untrustedOriginMirror => decide (r.skipped = skippedGates outcomes)

-- The validator accepts an untrusted badge without reading its list of skipped gates.
#tooth Obend.Vault.TransclusionAndMirror.badge_untrusted_lists_skipped by mutation
  Obend.Vault.TransclusionAndMirror.verifyMirrorBadge := fun outcomes kind address r =>
    decide (address.size = 32) && decide (r.upgrade = ⟨kind, address⟩) &&
      VerificationGate.all.all (fun g => outcomes g != .failed) &&
      match r.tier with
      | .selfVerifiedLocal => VerificationGate.all.all fun g => outcomes g == .passed
      | .untrustedOriginMirror => true

/-! ## 6. The axiom census -/

#assert_axioms_tree

end Obend.Tests.Metasystem.FrustumLivingScreenshotTest

end
