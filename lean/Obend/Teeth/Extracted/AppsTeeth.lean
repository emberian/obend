module
/-
# `Obend.Teeth.Extracted.AppsTeeth` — Apps Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (4 mutation witnesses) extracted from
`Obend.Apps` modules so `Obend.Apps.*` elaborates definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.Hybrid
import all Obend.Analysis.QuantumWalk
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.TaylorModel
import all Obend.Apps.SovereignDrex
import all Obend.AssertCompiled
import all Obend.Consensus.Epistemic
import all Obend.Consensus.Finality
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Elab.AutoCert
import all Obend.Elab.Workbook
import all Obend.Equiv.Clairvoyant
import all Obend.Fold.Collapse
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.HDL
import all Obend.Hardware.Kinematics
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.OpenUSD
import all Obend.Hardware.Photonics
import all Obend.Hardware.Process
import all Obend.Hardware.QuantumMatter
import all Obend.Hardware.Silicon
import all Obend.Hardware.Compiler
import all Obend.Hardware.Synth
import all Obend.Hardware.Types
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Netting
import all Obend.Judge.TranscriptPolicy
import all Obend.Law
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Served
import all Obend.Leaf.Specialize
import all Obend.Leaf.Static
import all Obend.Leaf.UpTo
import all Obend.Ledger.Floors
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Rewrite
import all Obend.Lower.Fragment
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Reflect
import all Obend.Lower.Transport
import all Obend.Run.Durable
import all Obend.Spec.Capture
import all Obend.Spec.CrossPackage
import all Obend.Spec.Elaborate
import all Obend.Spec.FrontEnd
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.Parse
import all Obend.Spec.Sha256
import all Obend.Spec.Syntax
import all Obend.Teeth.Hardware.CliffordKernel
import all Obend.Vault.CheckedCarry
import all Obend.Vault.Escrow
import all Obend.Vault.Hyperedge
import all Obend.Vault.IrreversibleOutbox
import all Obend.Vault.Mandate
import all Obend.Vault.Projection
import all Obend.Vault.Replay
import all Obend.Vault.UnifiedDeos

public section
end

namespace Obend.Teeth.Extracted.AppsTeeth
/-! ## Extracted from `Obend.Apps.SovereignDrex` (2 teeth) -/
section Obend_Apps_SovereignDrex
open Obend.Apps.SovereignDrex
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Slot
open Obend.Slot.Protocol
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.Ledger
open Obend.Judge
open Obend.Vault
open Obend.Vault.CheckedCarry
open Obend.Vault.UnifiedDeos
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace
open Obend.Consensus.Finality
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler

private def brokenDrexRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames := ["in_lot_count"]
  , wires := []
  , regs := []
  , outputs := [{ name := "out_turn_admitted", expr := .const 1#64 }] }

#tooth sovereignDrexBatchTopRtlModule_epoch_replay_refused by mutation
  sovereignDrexBatchTopRtlModule := brokenDrexRtlModule

private def brokenDrexCommittee4 : List Nat := [0, 1, 2, 3, 4, 5]

#tooth sovereignDrex_engine_and_bft_finality_sound by mutation
  drexCommittee4 := brokenDrexCommittee4

end Obend_Apps_SovereignDrex
end Obend.Teeth.Extracted.AppsTeeth
