module
public import Obend.Crypto.BinaryTower256
public import Obend.Judge.DecoAndCallTree
import all Init.Data.String.Defs
import all Obend.Crypto.BinaryTower256
import all Obend.Judge.DecoAndCallTree
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Vault.Lsafe
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
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.SameOpening
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.TranscriptPolicy
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.UpTo
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.LateBinding
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
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
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth

public section
namespace Obend.Tests.BinaryTowerDecoCallTree
open Obend.Crypto Obend.Crypto.BinaryTower256 Obend.Judge.DecoAndCallTree
open Obend.Judge.VpaJson (JState jsonAccepting)
set_option autoImplicit false
set_option Elab.async false

example (a : Tower256) : ofExec256 (toExec256 a) = a := ofExec256_toExec256 a
example (a : Tower256Exec) : ofBytes32 (toBytes32 a) = some a := ofBytes32_toBytes32 a
example (a b : TowerElem 3) (h : embedTowerChain 3 5 a = embedTowerChain 3 5 b) : a = b :=
  embedTowerChain_injective 3 5 a b h
example (a : Tower128) (ha : a ≠ towerZero 7) : towerMul 7 a (towerInv 7 a) = towerOne 7 :=
  towerMul_inv 7 a ha
example : towerMul 1 (false, true) (false, true) = (true, true) := by rfl
example : mulExec 3 0x53 0xca = packTower 3 (towerMul 3 (unpackTower 3 0x53) (unpackTower 3 0xca)) := by
  simpa only [packTower_unpackTower] using mulExec_refines 3 (unpackTower 3 0x53) (unpackTower 3 0xca)
example : Simulates 8 (towerAdd 8 (unpackTower 8 0x123456789abcdef) (unpackTower 8 0x10000000000000000))
    (0x123456789abcdef ^^^ 0x10000000000000000) :=
  Simulates.add 8 (packTower_unpackTower 8 _) (packTower_unpackTower 8 _)

example : mulExec 7 (packTower 7 (towerOne 7)) (packTower 7 (towerOne 7)) =
    packTower 7 (towerOne 7) := by rw [mulExec_refines, towerMul_one]
example : mulExec 8 (packTower 8 (towerOne 8)) (packTower 8 (towerOne 8)) =
    packTower 8 (towerOne 8) := by rw [mulExec_refines, towerMul_one]
example : ofBytes32 (toBytes32 (0x8000000000000000000000000000000000000000000000000000000000000001 : Tower256Exec)) =
    some 0x8000000000000000000000000000000000000000000000000000000000000001 := ofBytes32_toBytes32 _

example (H : Tower128) : ghashPoly H [] = ghashPoly H [towerZero 7] := ghashPoly_leading_zero H
example : ghashPoly (towerOne 7) [towerOne 7] ≠ ghashPoly (towerOne 7) [towerZero 7] := by
  simpa [ghashPoly, RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul] using towerOne_ne_zero 7

example : (1 : Nat) ≤ 1 :=
  ghashDiff_roots_bound [towerOne 7] [towerZero 7] 1 [towerZero 7]
    (by decide +kernel) (by decide +kernel) (by simp)
    ⟨towerOne 7, by simpa [ghashPoly, RoundPoly.evalCoeffs,
      CommRingOps.zero, CommRingOps.add, CommRingOps.mul] using towerOne_ne_zero 7⟩
    (by intro H h; simp only [List.mem_singleton] at h; subst H
        simp [ghashPoly, RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul])

example : decList (encList [[], [0], [255, 128, 0]]) = some [[], [0], [255, 128, 0]] := decList_encList _
example : encList [[1, 2], [3]] ≠ encList [[1], [2, 3]] := by
  intro h
  have := encList_injective _ _ h
  contradiction

/-! ## Views, masks and depth-1 members, in the kernel (no hashing) -/

def js (s : String) : ByteArray := s.toByteArray
def httpHead : ByteArray := js "HTTP/1.1 200 OK\r\n\r\n"

/-- `{"note":"x\"y","k":"` · `secret` · `"}`: the hidden span sits in a value string. -/
def bodySlots : List SpanSlot :=
  [.opened (js "{\"note\":\"x\\\"y\",\"k\":\"") [], .masked (js "****"), .opened (js "\"}") []]
def bodySpans : List ByteArray := [js "{\"note\":\"x\\\"y\",\"k\":\"", js "secret", js "\"}"]

example : checkMask JState.init bodySlots bodySpans = true := by decide +kernel
example : (bodyRun JState.init bodySlots).map jsonAccepting = some true := by decide +kernel
-- A hidden span with an escape pair inside is confined; one that ends on the backslash is not.
example : checkMask JState.init bodySlots
    [js "{\"note\":\"x\\\"y\",\"k\":\"", js "se\\\"cret", js "\"}"] = true := by decide +kernel
example : checkMask JState.init bodySlots
    [js "{\"note\":\"x\\\"y\",\"k\":\"", js "secret\\", js "\"}"] = false := by decide +kernel
-- A mask with a quote, and a mask placed in a key, are refused by the public run.
example : bodyRun JState.init
    [.opened (js "{\"k\":\"") [], .masked (js "a\"b"), .opened (js "\"}") []] = none := by
  decide +kernel
example : bodyRun JState.init [.opened (js "{\"") [], .masked (js "k"), .opened (js "\":1}") []] =
    none := by decide +kernel

/-- A 32-byte root whose hex is sixty-four zeros. -/
def zeroRoot : Hash256 := ⟨⟨(List.replicate 32 (0 : UInt8)).toArray⟩, by decide⟩
def zeros : String := "0000000000000000000000000000000000000000000000000000000000000000"
def respView (body : String) : TranscriptView := ⟨⟨2, ByteArray.empty⟩, [.opened httpHead [], .opened (js body) []]⟩

example : checkSubtreeRoot (respView ("{\"subtree_root\":\"" ++ zeros ++ "\",\"n\":1}")) zeroRoot =
    true := by decide +kernel
example : topLevelMembers [.opened (js "{\"a\":\"x\",\"b\":{\"c\":\"y\"},\"d\":\"z\"}") []] =
    [(js "d", js "z"), (js "a", js "x")] := by decide +kernel
-- Not a member: nested in an object or an array, reflected inside a string value, another root,
-- a value with an escape, a top-level array.
example : checkSubtreeRoot (respView ("{\"data\":{\"subtree_root\":\"" ++ zeros ++ "\"}}")) zeroRoot =
    false := by decide +kernel
example : checkSubtreeRoot (respView ("{\"l\":[{\"subtree_root\":\"" ++ zeros ++ "\"}]}")) zeroRoot =
    false := by decide +kernel
example : checkSubtreeRoot
    (respView ("{\"user_bio\":\"x\\\"subtree_root\\\":\\\"" ++ zeros ++ "\\\"\",\"n\":1}")) zeroRoot =
    false := by decide +kernel
example : checkSubtreeRoot (respView ("{\"subtree_root\":\"1000000000000000000000000000000000000000000000000000000000000000\"}")) zeroRoot =
    false := by decide +kernel
example : checkSubtreeRoot (respView ("[\"subtree_root\",\"" ++ zeros ++ "\"]")) zeroRoot =
    false := by decide +kernel
-- Not a member: the value is under a mask, whatever the mask spells.
example : checkSubtreeRoot ⟨⟨4, ByteArray.empty⟩,
    [.opened httpHead [], .opened (js "{\"subtree_root\":\"") [], .masked (js zeros),
      .opened (js "\"}") []]⟩ zeroRoot = false := by decide +kernel

example : checkFresh ⟨[js "n"], []⟩ plantedAttestation = false := by decide +kernel

#tooth checkDecoAttestation_iff_relation by mutation checkDecoAttestation := fun _ _ _ => true
#tooth callTreeVerify_sound_or_collision by mutation callTreeVerify := fun _ _ _ _ => true
#tooth towerScaleX_eq_mul by mutation towerScaleX := fun k _ => towerZero k
#tooth towerKaratsuba_eq by mutation towerKaratsuba := fun k a b => towerAdd k a b
#tooth towerMul_add_distrib by mutation towerMul := fun k _ _ => towerOne k
#tooth checkFresh_iff by mutation checkFresh := fun _ _ => true
#tooth checkPolicy_iff by mutation checkPolicy := fun _ _ => true
#tooth encList_injective by mutation encList := fun _ => []
-- A mask check that does not ask the hidden span to return to the machine state.
#tooth checkMask_run by mutation Obend.Judge.spanConfined := fun _ _ _ => true
-- A node preimage that drops the attestation and the children.
#tooth treeRoot_binds by mutation nodePreimage := fun h _ => encList [encInt (kindTag h.kind)]
-- A tag check that accepts every tag.
#tooth deco_ghash_forgery_keys_bound by mutation tagVerifies := fun _ _ => true

#print axioms towerMul_add_distrib
#print axioms embedTower_injective
#print axioms towerMul_inv
#print axioms ghashDiff_roots_bound
#print axioms checkDecoAttestation_iff_relation
#print axioms checkOpening_binds
#print axioms treeRoot_binds
#print axioms encList_injective
#print axioms callTreeVerify_sound_or_collision
#assert_axioms_tree

end Obend.Tests.BinaryTowerDecoCallTree
