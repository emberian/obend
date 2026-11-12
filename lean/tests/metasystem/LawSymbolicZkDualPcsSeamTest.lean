module
public import Obend.SymbolicZk.CompileToPiop
public import Obend.Law.AmendCli
public import Obend.Polis.ZkBiscuit
public import Obend.Polis.HouyhnhnmTurn
import all Obend.SymbolicZk.SkolemChaseCore
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.SymbolicZk.CompileToPiop
import all Obend.Law.AmendCli
import all Obend.Polis.ZkBiscuit
import all Obend.Polis.HouyhnhnmTurn
public import metasystem.VerifiableCredentialsAndTraceTest
import all metasystem.VerifiableCredentialsAndTraceTest
import all Obend.Polis.VerifiableCredentials
import Obend.Tactic.Tooth
public section
namespace Obend.Tests.LawSymbolicZkDualPcsSeam
open Obend.Crypto Obend.SymbolicZk.CompileToPiop
open Obend.Law.PointwiseRevise Obend.Law.AmendCli
open Obend.Polis
open Obend.Digest.Cshake256 Obend.Digest.HashBytes

def failedLookup : SymbolicZkStmt :=
  ⟨#[], #[], #[], #[], #[], #[Goldilocks.zero], #[Goldilocks.one], 0⟩
def failedWitness : SymbolicZkWitness := ⟨#[], #[1]⟩

theorem residualOverflow_refused : stmtWitnessStructValid failedLookup failedWitness = false := by decide
#guard !stmtWitnessStructValid failedLookup failedWitness
#guard (eqWeightedTable [Goldilocks.zero, Goldilocks.one] []).length == 2
#tooth residualOverflow_refused by mutation stmtWitnessStructValid := fun _ _ => true
#tooth zipMulPadded_length by mutation zipMulPadded := fun xs ws => (xs.zip ws).map (fun p => CommRingOps.mul p.1 p.2)

open Obend.SymbolicZk.SkolemChaseCore in
def atom (r : Nat) : Atom Term := ⟨r, [.const 7]⟩
#guard (lowerChaseAtoms [atom 0, atom 1] [atom 1]).lookupQueries == #[Goldilocks.one]
#guard (lowerChaseAtoms [atom 0] [atom 1]).lookupQueries == #[Goldilocks.one]
example : SymbolicSemanticsValid (lowerChaseAtoms [atom 0, atom 1] [atom 1])
    (lowerChaseWitness [atom 0, atom 1] [atom 1]) :=
  (lowerChaseAtoms_semantics _ _ (by decide)).mpr (by simp)
theorem absentChaseAtom_refused : ¬ SymbolicSemanticsValid (lowerChaseAtoms [atom 0] [atom 1])
    (lowerChaseWitness [atom 0] [atom 1]) := by
  rw [lowerChaseAtoms_semantics _ _ (by decide)]
  simp [atom]
#tooth lowerChaseAtoms_semantics by mutation lowerChaseAtoms := fun _ _ =>
  ⟨#[], #[], #[], #[], #[], #[], #[], 1⟩

open Obend.SymbolicZk.SkolemChaseCore in
def chaseRule : TgdRule := ⟨1, [0], [], [⟨0, [.var 0]⟩], [⟨1, [.var 0]⟩]⟩
open Obend.SymbolicZk.SkolemChaseCore in
def chasedModel : FactSet := runBoundedChase [chaseRule] 1 [atom 0]
#guard chasedModel == [atom 0, atom 1]
#guard Obend.SymbolicZk.SkolemChaseCore.allRulesSatisfied [chaseRule] chasedModel
#guard !Obend.SymbolicZk.SkolemChaseCore.allRulesSatisfied [chaseRule] [atom 0]
#guard (lowerChaseRuleInstance chasedModel chaseRule [(0, .const 7)]).isSome
example : SymbolicSemanticsValid (lowerChaseAtoms [atom 0, atom 1] [atom 0, atom 1])
    (lowerChaseWitness [atom 0, atom 1] [atom 0, atom 1]) :=
  (lowerChaseRuleInstance_sound [atom 0, atom 1] chaseRule [(0, .const 7)]
    [atom 0] [atom 1] (by simp [chaseRule, atom, Obend.SymbolicZk.SkolemChaseCore.evalPatAtoms,
      Obend.SymbolicZk.SkolemChaseCore.evalPatAtom, Obend.SymbolicZk.SkolemChaseCore.evalPatArgs,
      Obend.SymbolicZk.SkolemChaseCore.evalPatTerm, Obend.SymbolicZk.SkolemChaseCore.lookupSubst])
    (by simp [chaseRule, atom, Obend.SymbolicZk.SkolemChaseCore.evalPatAtoms,
      Obend.SymbolicZk.SkolemChaseCore.evalPatAtom, Obend.SymbolicZk.SkolemChaseCore.evalPatArgs,
      Obend.SymbolicZk.SkolemChaseCore.evalPatTerm, Obend.SymbolicZk.SkolemChaseCore.lookupSubst])
    (by decide)).2.mpr (by simp)
#tooth lowerChaseRuleInstance_sound by mutation lowerChaseAtoms := fun _ _ =>
  ⟨#[], #[], #[], #[], #[], #[], #[], 1⟩

def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun v =>
    [Char.ofNat (if v.toNat / 16 < 10 then 48 + v.toNat / 16 else 87 + v.toNat / 16),
     Char.ofNat (if v.toNat % 16 < 10 then 48 + v.toNat % 16 else 87 + v.toNat % 16)])
def old : SpecTheory 16 := [⟨"fee", 3, 0xaaaa⟩]
def turn : AmendmentTurn 16 := ⟨2, [⟨"recover", 1, 0x00c0⟩]⟩
def floor : Bedrock 16 := ⟨fun v => (0x00c0 : BitVec 16).getLsbD v.val, 6, by decide⟩
def receipt : AmendReceipt :=
  ⟨2, .accepted 7 old, [], ["untouched"], #[⟨42, 99⟩], turn.digest, floor.digest, supportDigest []⟩
def root : Obend.Polis.Block :=
  ⟨255, .atom 1000,
    encodeFrame ⟨Array.replicate 32 3⟩ ⟨#[0, 0, 0, 0]⟩ "golden".toUTF8,
    Native.bytesOfList (be 8 101)⟩

-- Exact strings are also asserted by Rust amend_cli::test_law_biscuit_golden_vectors.
#guard hex turn.digest == "2431ea726b7b7030421d7278cbbf3570767930d00f0a439804c825148edb6b35"
#guard hex floor.digest == "0d9cb8d846f06d8780ea40f054faef443159568f0587ef09f4c2776a6fae0f83"
#guard hex receipt.digest == "cf5a6308c19e9183faedadac9ddf72533272750ab3b64f616e421d93061d25f6"
#guard hex (rootLineage root) == "e7d43dfb65f7d2f70ed08dbf68492e1fde0bd24251a456ed4f33b25dc9e4f251"
#guard hex (Native.bytesOfList (be 32 (credNul (rootLineage root)))) ==
  "aa15ffe15196a3cce9df102d6897fa10e2d441a1a5c393d1e035b0562152c027"

open Obend.Polis.VerifiableCredentials Obend.Polis.HouyhnhnmTurn
#guard factAtom ⟨1, "s".toUTF8, "object".toUTF8⟩ != factAtom ⟨2, "s".toUTF8, "object".toUTF8⟩
#guard factAtom ⟨1, "s".toUTF8, "object".toUTF8⟩ != factAtom ⟨1, "t".toUTF8, "object".toUTF8⟩
#tooth factAtom_binds by mutation factAtomPreimage := fun e => e.obj.data.toList
#tooth committedStateRoot_revoked_binding by mutation stateRootBytes :=
  fun c s => encodeFrame (c.stateRoot s) ByteArray.empty (c.capabilityRoot s.capabilities)
#tooth nextState_refuses_replay by mutation spendInvocations := fun r _ => r
example (c : TurnCommitments) (v : InnerVerifier) : Nonempty (TurnProofSystem c v) :=
  dualPcsTurnProofSystem_inhabited c v

namespace CredentialCases
open Obend.Tests.VerifiableCredentialsAndTrace
-- A valid opening of the public zero table still cannot stand in for the relation table.
def zeroStatement : CredentialStatement :=
  { statement with tableCommitment := commitTable deployedReceiptParams (List.replicate 32 Goldilocks.zero) }
#guard !verifyExPostCredentialReceipt deployedReceiptParams policy vk zeroStatement Obend.Tests.VerifiableCredentialsAndTrace.receipt
#guard !verifyExPostCredentialReceipt deployedReceiptParams policy vk
  { statement with credentialDigest := ByteArray.empty } Obend.Tests.VerifiableCredentialsAndTrace.receipt
#tooth verifyExPostCredentialReceipt_sound by mutation verifyExPostCredentialReceipt := fun _ _ _ _ _ => true
#guard commitments.stateRoot cell0 ==
  commitments.stateRoot (nextState cell0 { turn1.structured with deltas := #[0, 0] })
#guard committedStateRoot commitments cell0 !=
  committedStateRoot commitments (nextState cell0 { turn1.structured with deltas := #[0, 0] })
#guard !execTurnSymbolic verifier (nextState cell0 turn1.structured) turn1.structured
#guard verifyDualPcsTurn commitments verifier (materializeInputs commitments cell0 turn1.structured 0)
  (squeezeChallenge256 (turnTranscript (materializeInputs commitments cell0 turn1.structured 0))).1.val
  (proveDualPcsTurn commitments cell0 turn1.structured 0)
end CredentialCases
end Obend.Tests.LawSymbolicZkDualPcsSeam
