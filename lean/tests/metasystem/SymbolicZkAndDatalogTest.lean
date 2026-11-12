module
public import Obend.SymbolicZk.SemiringDatalog
public import Obend.SymbolicZk.RankedFixpointArith
public import Obend.SymbolicZk.CamUnifyArith

import all Obend.SymbolicZk.SemiringDatalog
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.SymbolicZk.CamUnifyArith
meta import Obend.SymbolicZk.SemiringDatalog
meta import Obend.SymbolicZk.RankedFixpointArith
meta import Obend.SymbolicZk.CamUnifyArith

public section
set_option autoImplicit false
namespace Obend.SymbolicZk.Tests
open Datalog Ranked Cam Obend.Reasons

/-- Independent iterative reduct evaluator, used only for finite test witness generation. -/
def gammaTrace (p : ArithProgram) (j : Array Bool) : Array Bool × Array Nat := Id.run do
  let mut m := Array.replicate p.numAtoms false
  let mut ranks := Array.replicate p.numAtoms 0
  for k in [:p.numAtoms + 1] do
    let next := (Array.range p.numAtoms).map fun a =>
      p.rules.any (fun r => r.head == a && firesFast r j m)
    ranks := (Array.range p.numAtoms).map fun a =>
      if bit next a && !bit m a then k + 1 else rankAt ranks a
    m := next
  return (m, ranks)

def candidateCert (p : ArithProgram) (t u : Array Bool) (stage rankT rankU : Array Nat) : ArrayCert := Id.run do
  let base : ArrayCert := ⟨stage, rankT, rankU, #[], #[], #[]⟩
  let st := (Array.range p.numAtoms).map fun a =>
    ((Array.range p.rules.size).find? fun i =>
      checkTrueSupport p t u {base with supportT := Array.replicate p.numAtoms i} a).getD 0
  let su := (Array.range p.numAtoms).map fun a =>
    ((Array.range p.rules.size).find? fun i =>
      checkSupport p t u rankU (Array.replicate p.numAtoms i) a).getD 0
  let blockers := p.rules.map fun r =>
    match (Array.range r.neg.size).find? (fun i => checkBlocker r t u stage (true, i)) with
    | some i => (true, i)
    | none => (false, ((Array.range r.pos.size).find? (fun i => checkBlocker r t u stage (false, i))).getD 0)
  return {base with supportT := st, supportU := su, blockers := blockers}

/-- Exhaustive stages and true-support ranks over the two-atom universe. Upper ranks
come from an independent Horn iteration, and every candidate is passed to the real checker. -/
def feasibleTwo (p : ArithProgram) (t u : Array Bool) : Bool :=
  let upper := gammaTrace p t
  if upper.1 != u || (gammaTrace p u).1 != t then false else
  (Array.range 9).any fun s => (Array.range 9).any fun r =>
    checkRankedWFS p t u (candidateCert p t u #[s % 3, s / 3] #[r % 3, r / 3] upper.2)

/-- 32 rules: 2 heads × 4 positive subsets × 4 negative subsets.
The corpus is every subset containing at most two distinct rules: 1+32+496=529. -/
def twoRules : Array ArithRule := (Array.range 32).map fun i =>
  ⟨i / 16, (Array.range 2).filter (fun a => (i / 4 / 2^a) % 2 == 1),
    (Array.range 2).filter (fun a => (i / 2^a) % 2 == 1)⟩

def twoPrograms : Array ArithProgram :=
  #[⟨2, #[]⟩] ++ twoRules.map (fun r => ⟨2, #[r]⟩) ++
    (Array.range 32).flatMap (fun i => ((Array.range 32).filter (i < ·)).map
      (fun j => ⟨2, #[twoRules[i]!, twoRules[j]!]⟩))

def statusBits (code : Nat) : Array Bool × Array Bool :=
  let status := #[code % 3, code / 3]
  (status.map (· == 2), status.map (· != 0))

def wfsDiscrepancies : Nat := Id.run do
  let mut bad := 0
  for p in twoPrograms do
    let model := wf (toReasonsProgram p)
    let tw := (Array.range 2).map fun a => model.1.contains (atomName a)
    let uw := (Array.range 2).map fun a => model.2.contains (atomName a)
    for code in [:9] do
      let (t, u) := statusBits code
      let expected := t == tw && u == uw
      if feasibleTwo p t u != expected then bad := bad + 1
  return bad

#guard twoPrograms.size == 529
#guard twoPrograms.size * 9 == 4761
#guard wfsDiscrepancies == 0

/-- Named regressions cover each nonmonotonic regime. -/
def tweety : ArithProgram := ⟨3, #[⟨0, #[], #[]⟩, ⟨1, #[0], #[2]⟩]⟩
def positiveCycle : ArithProgram := ⟨2, #[⟨0, #[1], #[]⟩, ⟨1, #[0], #[]⟩]⟩
def oddLoop : ArithProgram := ⟨2, #[⟨0, #[], #[0]⟩]⟩
def evenLoop : ArithProgram := ⟨2, #[⟨0, #[], #[1]⟩, ⟨1, #[], #[0]⟩]⟩
#guard checkRankedWFS tweety #[true, true, false] #[true, true, false]
  (candidateCert tweety #[true, true, false] #[true, true, false] #[1,1,0] #[0,1,0] #[1,2,0])
#guard feasibleTwo positiveCycle #[false,false] #[false,false]
#guard feasibleTwo oddLoop #[false,false] #[true,false]
#guard feasibleTwo evenLoop #[false,false] #[true,true]
#guard !feasibleTwo evenLoop #[true,false] #[true,false]

#guard !checkRankedGamma positiveCycle #[false,false] #[true,true] #[0,0] #[0,1]
#guard checkRankedGLStable evenLoop #[true,false] #[0,0] #[0,0]
#guard !checkRankedGLStable oddLoop #[false,false] #[0,0] #[0,0]
#guard !checkRankedGLStable oddLoop #[true,false] #[0,0] #[0,0]

open Obend.Crypto

def q (n : Nat) : GroundTuple := ⟨n, #[]⟩
def sampleNat : SortedKTable Nat := ⟨#[(q 1, 2), (q 3, 5)]⟩
def sampleBool : SortedKTable Bool := ⟨#[(q 1, true), (q 3, true)]⟩
#guard verifyGapCert (⟨#[]⟩ : SortedKTable Nat) (q 0) .emptyTable
#guard verifyGapCert sampleNat (q 0) .belowFirst
#guard verifyGapCert sampleNat (q 4) .aboveLast
#guard verifyGapCert sampleNat (q 2) (.adjacentGap 0)
#guard evalRuleFast sampleNat ⟨q 4, #[q 1, q 3]⟩ == 10
#guard evalRuleFast sampleBool ⟨q 4, #[q 1, q 3]⟩
#guard (evalRuleFast (⟨#[(q 1, ⟨some 2⟩), (q 3, ⟨some 5⟩)]⟩ : SortedKTable TropicalMinCost)
  ⟨q 4, #[q 1, q 3]⟩).cost == some 7
#guard (evalProvGoldilocks (fun n : Nat => Goldilocks.ofNat (n+2))
  (.add (.mul (.var 0) (.var 1)) (.var 0))).val == 8

def groundProgram : Array GroundRule := #[⟨q 4, #[q 1,q 3]⟩, ⟨q 4, #[q 1]⟩]
#guard lookupFast (tpFast groundProgram sampleNat) (q 4) == tpSpec groundProgram (lookupSpec sampleNat) (q 4)
#guard lookupFast (tpFast groundProgram sampleNat) (q 4) == 12
#guard lookupFast (tpFast groundProgram sampleBool) (q 4)
#guard lookupFast (mergeAddSorted sampleNat sampleNat) (q 1) == 4
#guard lookupFast (semiNaiveStepFast #[⟨q 4, #[q 1,q 3]⟩] sampleNat
  (⟨#[(q 1,3),(q 3,7)]⟩ : SortedKTable Nat)) (q 4) == 50
#guard (lookupFast (tpFast #[⟨q 4, #[q 1,q 3]⟩,⟨q 4,#[q 5]⟩]
  (⟨#[(q 1,⟨some 2⟩),(q 3,⟨some 5⟩),(q 5,⟨some 9⟩)]⟩ : SortedKTable TropicalMinCost)) (q 4)).cost == some 7
#guard (mergeAddSorted (⟨#[(q 1, Goldilocks.one)]⟩ : SortedKTable Goldilocks)
  ⟨#[(q 1, Goldilocks.neg Goldilocks.one)]⟩).entries.size == 0
#guard (lookupFast (tpFast groundProgram (⟨#[(q 1,Goldilocks.ofNat 2),(q 3,Goldilocks.ofNat 3)]⟩ : SortedKTable Goldilocks)) (q 4)).val == 8
#guard quadraticFiresGate Goldilocks.zero Goldilocks.one Goldilocks.zero Goldilocks.one
#guard !quadraticFiresGate Goldilocks.zero Goldilocks.zero Goldilocks.zero Goldilocks.one
#guard quadraticFiresGate Goldilocks.one Goldilocks.zero Goldilocks.one Goldilocks.zero
#guard quadraticFiresGate (Goldilocks.ofNat 2) Goldilocks.zero
  (Goldilocks.ofNat 9223372034707292161) Goldilocks.zero

open Obend.Lower.ExprCAM

def camWord (tag left right : Nat) : CamWord64 :=
  packCamWord64 ⟨BitVec.ofNat 4 tag, false, false, 0, BitVec.ofNat 16 left, BitVec.ofNat 16 right⟩
def acyclicCam : CamDagPool := ⟨#[camWord 10 0 0, camWord 4 2 2, camWord 3 0 0],
  #[some 1, none, none]⟩
def recursiveCam : CamDagPool := ⟨#[camWord 10 0 0, camWord 4 2 0, camWord 3 0 0],
  #[some 1, none, none]⟩
def mutualCam : CamDagPool :=
  ⟨#[camWord 10 0 0, camWord 10 1 0, camWord 4 4 1, camWord 4 4 0, camWord 3 0 0],
    #[some 2, some 3, none, none, none]⟩
#guard checkTopologicalUnifyExec acyclicCam #[1,1,0]
#guard !checkTopologicalUnifyExec recursiveCam #[1,1,0]
#guard !checkTopologicalUnifyExec mutualCam #[1,1,1,1,0]
#guard checkCanonicalCamPool #[camWord 3 0 0, camWord 4 0 0] ⟨#[0,1], #[0,1]⟩
#guard !checkCanonicalCamPool #[camWord 3 0 0, camWord 3 0 0] ⟨#[0,1], #[0,1]⟩
#guard checkLinMemExec ⟨#[⟨7,0,42⟩], #[], #[⟨⟨7,0,42⟩,1⟩], #[]⟩
#guard !checkLinMemExec ⟨#[⟨7,0,42⟩], #[], #[⟨⟨7,0,42⟩,1⟩,⟨⟨7,0,42⟩,2⟩], #[]⟩
#guard !checkLinMemExec ⟨#[], #[⟨0,2,10⟩,⟨1,1,11⟩], #[⟨⟨0,2,10⟩,1⟩,⟨⟨1,1,11⟩,2⟩], #[]⟩

/-- The ≤ mutant admits exactly the constructor cycle rejected by the theorem. -/
def weakHeightCheck (p : CamDagPool) (tau : Array Nat) : Bool :=
  (Array.range p.words.size).all fun u =>
    (childHandles p.words[u]!).all (fun v => v < p.words.size && heightAt tau v ≤ heightAt tau u) &&
    match p.sigma[u]?.getD none with
    | none => true
    | some v => v < p.words.size && heightAt tau u == heightAt tau v
#guard weakHeightCheck recursiveCam #[0,0,0]
#guard weakHeightCheck mutualCam #[0,0,0,0,0]

/-- Removing time order preserves balance but admits the two-step circulating ghost. -/
def ghostTrace : LinMem :=
  ⟨#[], #[⟨0,2,10⟩,⟨1,1,11⟩], #[⟨⟨0,2,10⟩,1⟩,⟨⟨1,1,11⟩,2⟩], #[]⟩
#guard decide (sortCells (births ghostTrace) = sortCells (exits ghostTrace)) &&
  checkStrictKeys ((sortCells (births ghostTrace)).map LinearCell.cellId)
#guard !checkLinMemExec ghostTrace
#guard checkProofForestExec #[(0,1)] ⟨#[1,1], #[1,0], #[1,1], #[0,0]⟩
#guard !checkProofForestExec #[(0,1),(1,0)] ⟨#[1,0], #[0,0], #[0,0], #[0,1]⟩

#guard checkCongruenceProofs #[camWord 3 0 0, camWord 3 1 0, camWord 4 0 0, camWord 4 1 1]
  #[(0,1)] #[⟨0,1,.seed 0⟩,⟨2,3,.node 0 0⟩]
#guard !checkCongruenceProofs #[camWord 4 0 0,camWord 4 1 1]
  #[] #[⟨0,1,.node 0 0⟩]
#guard !(mkExprCamWord64 (.lam (.sort .zero) (.bvar 0)) 0 0).getLsbD 59
#guard (mkExprCamWord64 (.bvar 0) 0 0).getLsbD 59

#tooth checkCongruenceProofs_sound by mutation checkCongruenceRow := fun _ _ _ _ _ => true
#tooth quadraticFiresGate_sound by mutation quadraticFiresGate := fun _ _ _ _ => true

#guard checkLinMemExec ⟨#[⟨1,0,7⟩], #[⟨2,1,9⟩], #[⟨⟨1,0,7⟩,1⟩], #[⟨2,1,9⟩]⟩
#guard !checkLinMemExec ⟨#[⟨1,0,7⟩], #[⟨1,1,9⟩], #[⟨⟨1,0,7⟩,1⟩], #[⟨1,1,9⟩]⟩

#tooth sumRows_merge by mutation mergeRows := fun xs _ => xs
#tooth buildSorted_sum by mutation buildSorted := fun _ => ⟨#[]⟩
#tooth checkProofForestExec_sound by mutation strictHeight := fun a b => decide (b ≤ a)

#tooth checkRankedGamma_sound by mutation earlier := fun a b => a ≤ b
#tooth checkRankedWFS_sound by mutation noLater := fun _ _ => True
#tooth topologicalHeight_forbids_cyclic_mvar by mutation strictHeight := fun a b => decide (b ≤ a)
#tooth linmem_sound by mutation bornBefore := fun _ => true

end Obend.SymbolicZk.Tests
