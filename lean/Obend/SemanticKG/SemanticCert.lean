module
/-
# Obend.SemanticKG.SemanticCert — Positive & Why-Not Receipts, Masked Ajtai Openings & `semantic-kg@1` Judge
Stage 4 of `Obend.SemanticKG`:
1. `PositiveSemanticReceipt` + `PosLineageNode` DAG + `verifyMaskedAjtaiOpening` (`semantic_positive_cert_sound`).
2. `WhyNotSemanticReceipt` + `checkSortedKTableBoolWF_iff` + Mode A (`guardedCoreGap`) & Mode B (`wfsNegationBlocker`) (`semantic_whynot_cert_sound`).
3. Non-tautological `semanticKgJudge` & `"semantic-kg@1"` `Obend.Judge.Format`.
-/
public import Obend.SemanticKG.Databank
public import Obend.SemanticKG.SpanParse
public import Obend.SemanticKG.ObjectWire
import all Obend.Judge.Class
import all Obend.SemanticKG.ObjectWire
import all Obend.SemanticKG.ColtJoin
public import Obend.Judge.Class
public import Obend.Crypto.DualSpine
public import Lean.Data.Json
import all Obend.SemanticKG.Databank
import all Obend.SemanticKG.SpanParse
import all Obend.SemanticKG.HypergraphChase
import all Obend.SymbolicZk.SemiringDatalog
import all Obend.SymbolicZk.SkolemChaseCore
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.Polis.EvidencedOcap
import all Obend.Crypto.DualSpine
public section
namespace Obend.SemanticKG
open Obend Obend.Core.Digest Obend.Digest.HashBytes Obend.Judge Obend.SymbolicZk Obend.SymbolicZk.SkolemChaseCore
open Obend.Judge.Commit (cshakeHasher)
open Obend.SymbolicZk.Datalog (ProvenanceSemiringOps LawfulProvenanceSemiring)
open Lean (Json)
set_option autoImplicit false

/-! ## §1. Positive Semantic Receipt, Acyclic `ProvVec4` Lineage DAG & Masked Ajtai Opening -/
structure EdbSpanOpening where
  chunkIdx      : Nat
  chunk         : DocChunkEntry
  merkleProof   : VpaJson.SpanProof
  redactionPol  : RedactionSlicePolicy
  disclosedSpan : Nat × Nat
  atom          : SpanBoundAtom
  baseWeight    : ProvVec4
def verifyEdbSpanOpening (chunkMerkleRoot : VpaJson.SpanRoot) (g : GrammarSpec) (op : EdbSpanOpening) : Bool :=
  (op.merkleProof.index == op.chunkIdx) &&
  verifyDatabankChunkInclusion chunkMerkleRoot op.chunk op.merkleProof &&
  checkRedactionDelimiterConfined op.chunk.rawBytes op.redactionPol &&
  op.redactionPol.disclosedSpans.toList.contains op.disclosedSpan &&
  decide (op.disclosedSpan.1 ≤ op.atom.byteStart) &&
  decide (op.atom.byteStart + op.atom.byteLen ≤ op.disclosedSpan.2) &&
  (match extractSpanBoundAtoms g op.chunk with | .ok atoms => atoms.contains op.atom | .error _ => false) &&
  (op.baseWeight != ProvenanceSemiringOps.zero)
inductive PosLineageNode where
  | edbLeaf (openingIdx : Nat) (tuple : Datalog.GroundTuple) (weight : ProvVec4)
  | ruleFire (ruleIdx : Nat) (premiseIndices : Array Nat) (headTuple : Datalog.GroundTuple) (weight : ProvVec4)
  | sumCombine (leftIdx rightIdx : Nat) (tuple : Datalog.GroundTuple) (weight : ProvVec4)
  deriving DecidableEq, Repr
def PosLineageNode.tuple : PosLineageNode → Datalog.GroundTuple
  | .edbLeaf _ t _ | .ruleFire _ _ t _ | .sumCombine _ _ t _ => t
def PosLineageNode.weight : PosLineageNode → ProvVec4
  | .edbLeaf _ _ w | .ruleFire _ _ _ w | .sumCombine _ _ _ w => w
def premiseValuation (nodes : Array PosLineageNode) (premiseIndices : Array Nat) : Datalog.KRelationSpec ProvVec4 :=
  fun q => match premiseIndices.toList.find? (fun p => match nodes[p]? with | some pn => pn.tuple == q | none => false) with
    | some p => match nodes[p]? with | some pn => pn.weight | none => ProvenanceSemiringOps.zero
    | none => ProvenanceSemiringOps.zero
def verifyPosLineageNode (openings : Array EdbSpanOpening) (rules : Array Datalog.GroundRule)
    (nodes : Array PosLineageNode) (k : Nat) (nd : PosLineageNode) : Bool :=
  match nd with
  | .edbLeaf opIdx t w => match openings[opIdx]? with
    | none => false | some op => (t == spanAtomToGroundTuple op.atom) && (w == op.baseWeight)
  | .ruleFire rIdx pidxs headTuple w => match rules[rIdx]? with
    | none => false
    | some r => (headTuple == r.head) && pidxs.all (fun p => decide (p < k)) &&
      r.body.all (fun q => pidxs.any (fun p => match nodes[p]? with | some pn => pn.tuple == q | none => false)) &&
      (w == Datalog.evalRuleSpec (premiseValuation nodes pidxs) r)
  | .sumCombine lIdx rIdx t w => decide (lIdx < k) && decide (rIdx < k) &&
    match nodes[lIdx]?, nodes[rIdx]? with
    | some nl, some nr => (nl.tuple == t) && (nr.tuple == t) && (w == ProvenanceSemiringOps.add nl.weight nr.weight)
    | _, _ => false
def verifyPosLineageDag (openings : Array EdbSpanOpening) (rules : Array Datalog.GroundRule)
    (nodes : Array PosLineageNode) (targetTuple : Datalog.GroundTuple) (claimedWeight : ProvVec4) : Bool :=
  decide (0 < nodes.size) && (claimedWeight != ProvenanceSemiringOps.zero) &&
  (Array.range nodes.size).all (fun k => match nodes[k]? with | none => false | some nd => verifyPosLineageNode openings rules nodes k nd) &&
  match nodes[nodes.size - 1]? with | none => false | some lastNd => (lastNd.tuple == targetTuple) && (lastNd.weight == claimedWeight)
inductive PosProvDerivable (edb : List (Datalog.GroundTuple × ProvVec4))
    (rules : Array Datalog.GroundRule) : Datalog.GroundTuple → ProvVec4 → Prop where
  | edb {t w} : (t, w) ∈ edb → PosProvDerivable edb rules t w
  | ruleFire {r : Datalog.GroundRule} {v : Datalog.KRelationSpec ProvVec4} :
      r ∈ rules.toList → (∀ q ∈ r.body, PosProvDerivable edb rules q (v q)) → PosProvDerivable edb rules r.head (Datalog.evalRuleSpec v r)
  | sumCombine {t w₁ w₂} : PosProvDerivable edb rules t w₁ → PosProvDerivable edb rules t w₂ → PosProvDerivable edb rules t (ProvenanceSemiringOps.add w₁ w₂)
def verifyMaskedAjtaiOpening (pp : Obend.Crypto.AjtaiParams) (beta : Nat) (comm witness maskVec : List Int) : Bool :=
  if hw : witness.length = pp.cols then if hm : maskVec.length = pp.cols then
      Obend.Crypto.checkShortNorm beta witness && Obend.Crypto.checkShortNorm beta maskVec &&
      decide (Obend.Crypto.ajtaiCommit pp (Obend.Crypto.vecAdd witness maskVec)
        ((Obend.Crypto.vecAdd_length witness maskVec (hw.trans hm.symm)).trans hw) = comm)
    else false else false
theorem verifyMaskedAjtaiOpening_sound (pp : Obend.Crypto.AjtaiParams) (beta : Nat)
    (comm witness maskVec : List Int)
    (hVer : verifyMaskedAjtaiOpening pp beta comm witness maskVec = true) :
    ∃ (hw : witness.length = pp.cols) (hm : maskVec.length = pp.cols),
      Obend.Crypto.Short pp.cols beta witness ∧ Obend.Crypto.Short pp.cols beta maskVec ∧
      Obend.Crypto.Short pp.cols (beta + beta) (Obend.Crypto.vecAdd witness maskVec) ∧
      comm = Obend.Crypto.vecAddMod (pp.modulus : Int)
        (Obend.Crypto.ajtaiCommit pp witness hw) (Obend.Crypto.ajtaiCommit pp maskVec hm) := by
  unfold verifyMaskedAjtaiOpening at hVer
  split at hVer
  · rename_i hw; split at hVer
    · rename_i hm; simp only [Bool.and_eq_true, decide_eq_true_eq] at hVer
      obtain ⟨⟨hSw, hSm⟩, hComm⟩ := hVer
      have hNW := (Obend.Crypto.checkShortNorm_iff beta witness).mp hSw
      have hNM := (Obend.Crypto.checkShortNorm_iff beta maskVec).mp hSm
      exact ⟨hw, hm, ⟨hw, hNW⟩, ⟨hm, hNM⟩,
        ⟨(Obend.Crypto.vecAdd_length witness maskVec (hw.trans hm.symm)).trans hw,
          Nat.le_trans (Obend.Crypto.normInf_vecAdd_le witness maskVec) (Nat.add_le_add hNW hNM)⟩,
        hComm.symm.trans (Obend.Crypto.ajtaiCommit_add pp hw hm)⟩
    · cases hVer
  · cases hVer
structure PositiveSemanticReceipt where
  edbOpenings   : Array EdbSpanOpening
  lineageDag    : Array PosLineageNode
  targetTuple   : Datalog.GroundTuple
  claimedWeight : ProvVec4
  ajtaiComm     : List Int
  ajtaiWitness  : List Int
  ajtaiMask     : List Int
def verifyPositiveReceipt (chunkMerkleRoot : VpaJson.SpanRoot) (g : GrammarSpec)
    (rules : Array Datalog.GroundRule) (pp : Obend.Crypto.AjtaiParams) (beta : Nat)
    (queryPol : KgQueryPolicy) (rights mask : UInt64) (ρ : Nat → Obend.Polis.KleenePred3)
    (rcpt : PositiveSemanticReceipt) : Bool :=
  checkKgQueryGuard queryPol rights mask ρ &&
  rcpt.edbOpenings.all (verifyEdbSpanOpening chunkMerkleRoot g) &&
  verifyPosLineageDag rcpt.edbOpenings rules rcpt.lineageDag rcpt.targetTuple rcpt.claimedWeight &&
  verifyMaskedAjtaiOpening pp beta rcpt.ajtaiComm rcpt.ajtaiWitness rcpt.ajtaiMask
private theorem verifyEdbSpanOpening_sound {db : SemanticDatabank} {g : GrammarSpec}
    {op : EdbSpanOpening} (hWfDb : WfDatabankBounds db = true)
    (hVer : verifyEdbSpanOpening (databankChunkMerkleRoot db) g op = true) :
    (db.chunks[op.chunkIdx]? = some op.chunk ∨
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
        cshakeHasher.hash databankChunkSpanTag m₁ = cshakeHasher.hash databankChunkSpanTag m₂) ∧
    ValidExtractedSpanAtom g op.chunk op.atom ∧
    (applyRedactionPolicy op.chunk.rawBytes op.redactionPol).extract
        op.atom.byteStart (op.atom.byteStart + op.atom.byteLen) =
      op.chunk.rawBytes.extract op.atom.byteStart (op.atom.byteStart + op.atom.byteLen) ∧
    op.baseWeight ≠ ProvenanceSemiringOps.zero := by
  simp only [verifyEdbSpanOpening, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem, bne_iff_ne] at hVer
  obtain ⟨⟨⟨⟨⟨⟨⟨hIdxEq, hMerkle⟩, hRedConf⟩, hSpMem⟩, hLo⟩, hHi⟩, hParse⟩, hWne⟩ := hVer
  have hBind := verifyDatabankChunkInclusion_binding hWfDb hMerkle; rw [hIdxEq] at hBind
  cases hEx : extractSpanBoundAtoms g op.chunk with
  | error _ => rw [hEx] at hParse; cases hParse
  | ok atoms =>
    rw [hEx] at hParse
    exact ⟨hBind, (span_parse_sound_and_unforgeable hEx hEx).2.2.2.1 op.atom (Array.contains_iff_mem.mp hParse),
      redacted_span_parse_sound hRedConf hSpMem hLo hHi, hWne⟩
private theorem verifyPosLineageDag_sound
    {openings : Array EdbSpanOpening} {rules : Array Datalog.GroundRule}
    {nodes : Array PosLineageNode} {targetTuple : Datalog.GroundTuple} {claimedWeight : ProvVec4}
    (hDag : verifyPosLineageDag openings rules nodes targetTuple claimedWeight = true) :
    PosProvDerivable (openings.toList.map fun op => (spanAtomToGroundTuple op.atom, op.baseWeight))
      rules targetTuple claimedWeight ∧ claimedWeight ≠ ProvenanceSemiringOps.zero := by
  let edb := openings.toList.map fun op => (spanAtomToGroundTuple op.atom, op.baseWeight)
  simp only [verifyPosLineageDag, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    Array.all_eq_true_iff_forall_mem] at hDag
  obtain ⟨⟨⟨hPos, hWne⟩, hNodes⟩, hLast⟩ := hDag
  have hEach : ∀ k (hk : k < nodes.size),
      PosProvDerivable edb rules (nodes[k]'hk).tuple (nodes[k]'hk).weight := by
    intro k; induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk; have hNodeOk := hNodes k (Array.mem_range.mpr hk)
      rw [Array.getElem?_eq_some_getElem nodes k hk] at hNodeOk
      cases hNd : nodes[k]'hk with
      | edbLeaf opIdx t w =>
        rw [hNd] at hNodeOk; simp only [verifyPosLineageNode] at hNodeOk
        cases hOp : openings[opIdx]? with
        | none => rw [hOp] at hNodeOk; cases hNodeOk
        | some op =>
          rw [hOp] at hNodeOk; simp only [Bool.and_eq_true, beq_iff_eq] at hNodeOk
          obtain ⟨rfl, rfl⟩ := hNodeOk
          exact .edb (List.mem_map.mpr ⟨op, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hOp), rfl⟩)
      | ruleFire rIdx pidxs headTuple w =>
        rw [hNd] at hNodeOk; simp only [verifyPosLineageNode] at hNodeOk
        cases hRule : rules[rIdx]? with
        | none => rw [hRule] at hNodeOk; cases hNodeOk
        | some r =>
          rw [hRule] at hNodeOk
          simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
            decide_eq_true_eq, Array.any_eq_true] at hNodeOk
          obtain ⟨⟨⟨rfl, hAcyc⟩, hBodyCov⟩, rfl⟩ := hNodeOk
          refine .ruleFire (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hRule)) fun q hq => ?_
          obtain ⟨j, hj, hMatch⟩ := hBodyCov q hq
          cases hFind : pidxs.toList.find? (fun p =>
              match nodes[p]? with | some pn => pn.tuple == q | none => false) with
          | none => exact False.elim (List.find?_eq_none.mp hFind (pidxs[j]'hj) (Array.getElem_mem_toList hj) hMatch)
          | some p =>
            have hpLt : p < k := hAcyc p (Array.mem_toList_iff.mp (List.mem_of_find?_eq_some hFind))
            have hpSz := Nat.lt_trans hpLt hk; have hpPred := List.find?_some hFind
            rw [Array.getElem?_eq_some_getElem nodes p hpSz, beq_iff_eq] at hpPred
            have hValEq : premiseValuation nodes pidxs q = (nodes[p]'hpSz).weight := by
              simp [premiseValuation, hFind, Array.getElem?_eq_some_getElem nodes p hpSz]
            rw [hValEq, ← hpPred]; exact ih p hpLt hpSz
      | sumCombine lIdx rIdx t w =>
        rw [hNd] at hNodeOk; simp only [verifyPosLineageNode, Bool.and_eq_true, decide_eq_true_eq] at hNodeOk
        obtain ⟨⟨hlLt, hrLt⟩, hLR⟩ := hNodeOk
        have hlSz := Nat.lt_trans hlLt hk; have hrSz := Nat.lt_trans hrLt hk
        rw [Array.getElem?_eq_some_getElem nodes lIdx hlSz, Array.getElem?_eq_some_getElem nodes rIdx hrSz] at hLR
        simp only [Bool.and_eq_true, beq_iff_eq] at hLR; obtain ⟨⟨hlT, hrT⟩, rfl⟩ := hLR
        have hL := ih lIdx hlLt hlSz; have hR := ih rIdx hrLt hrSz
        rw [hlT] at hL; rw [hrT] at hR; exact .sumCombine hL hR
  have hLastLt : nodes.size - 1 < nodes.size := by omega
  rw [Array.getElem?_eq_some_getElem nodes (nodes.size - 1) hLastLt] at hLast
  simp only [Bool.and_eq_true, beq_iff_eq] at hLast
  have hDer := hEach (nodes.size - 1) hLastLt; rw [hLast.1, hLast.2] at hDer; exact ⟨hDer, hWne⟩

/-- **Stage-4 Positive Receipt Master Soundness Theorem (`semantic_positive_cert_sound`)**. -/
theorem semantic_positive_cert_sound
    {db : SemanticDatabank} {g : GrammarSpec} {rules : Array Datalog.GroundRule}
    {pp : Obend.Crypto.AjtaiParams} {beta : Nat} {queryPol : KgQueryPolicy}
    {rights mask : UInt64} {ρ ρ' : Nat → Obend.Polis.KleenePred3} {rcpt : PositiveSemanticReceipt}
    (hWfDb : WfDatabankBounds db = true)
    (hRef : ∀ v, Obend.Polis.KleenePred3.Refines (ρ v) (ρ' v))
    (hVer : verifyPositiveReceipt (databankChunkMerkleRoot db) g rules pp beta
      queryPol rights mask ρ rcpt = true) :
    (∀ op ∈ rcpt.edbOpenings,
      (db.chunks[op.chunkIdx]? = some op.chunk ∨
        ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
          cshakeHasher.hash databankChunkSpanTag m₁ = cshakeHasher.hash databankChunkSpanTag m₂) ∧
      ValidExtractedSpanAtom g op.chunk op.atom ∧
      (applyRedactionPolicy op.chunk.rawBytes op.redactionPol).extract
          op.atom.byteStart (op.atom.byteStart + op.atom.byteLen) =
        op.chunk.rawBytes.extract op.atom.byteStart (op.atom.byteStart + op.atom.byteLen) ∧
      op.baseWeight ≠ ProvenanceSemiringOps.zero) ∧
    PosProvDerivable (rcpt.edbOpenings.toList.map fun op => (spanAtomToGroundTuple op.atom, op.baseWeight))
      rules rcpt.targetTuple rcpt.claimedWeight ∧
    rcpt.claimedWeight ≠ ProvenanceSemiringOps.zero ∧
    ((Obend.Polis.realizabilityFrame Obend.Polis.capPCA).Leads
      (Obend.Polis.holdsCap rights)
      ((Obend.Polis.realizabilityFrame Obend.Polis.capPCA).seq (.attenuate mask) (.guard queryPol.needRights))
      (fun c => c = .k) ∧
      Obend.Polis.subMask queryPol.needRights rights = true ∧
      Obend.Polis.KleenePred3.accepts (queryPol.caveat.eval ρ') = true) ∧
    (∃ (hw : rcpt.ajtaiWitness.length = pp.cols) (hm : rcpt.ajtaiMask.length = pp.cols),
      Obend.Crypto.Short pp.cols beta rcpt.ajtaiWitness ∧
      Obend.Crypto.Short pp.cols beta rcpt.ajtaiMask ∧
      Obend.Crypto.Short pp.cols (beta + beta) (Obend.Crypto.vecAdd rcpt.ajtaiWitness rcpt.ajtaiMask) ∧
      rcpt.ajtaiComm = Obend.Crypto.vecAddMod (pp.modulus : Int)
        (Obend.Crypto.ajtaiCommit pp rcpt.ajtaiWitness hw)
        (Obend.Crypto.ajtaiCommit pp rcpt.ajtaiMask hm)) := by
  simp only [verifyPositiveReceipt, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hVer
  obtain ⟨⟨⟨hGuard, hOps⟩, hDag⟩, hAjtai⟩ := hVer
  obtain ⟨hDer, hWne⟩ := verifyPosLineageDag_sound hDag
  obtain ⟨hLeads, _, hSubR, _, hAcc'⟩ := evidenced_kg_query_guard_sound queryPol rights mask ρ ρ' hGuard hRef
  exact ⟨fun op hop => verifyEdbSpanOpening_sound hWfDb (hOps op hop),
    hDer, hWne, ⟨hLeads, hSubR, hAcc'⟩,
    verifyMaskedAjtaiOpening_sound pp beta rcpt.ajtaiComm rcpt.ajtaiWitness rcpt.ajtaiMask hAjtai⟩

private theorem singleton_positive (root : VpaJson.SpanRoot) (g : GrammarSpec)
    (pp : Obend.Crypto.AjtaiParams) (pol : KgQueryPolicy) (rights : UInt64)
    (op : EdbSpanOpening) (target : Datalog.GroundTuple) (comm witness mask : List Int)
    (ho : verifyEdbSpanOpening root g op = true)
    (hd : verifyPosLineageDag #[op] #[] #[.edbLeaf 0 target ProvenanceSemiringOps.one]
      target ProvenanceSemiringOps.one = true)
    (ha : verifyMaskedAjtaiOpening pp 0 comm witness mask = true)
    (hg : checkKgQueryGuard pol rights rights (fun _ => .unbound3) = true) :
    verifyPositiveReceipt root g #[] pp 0 pol rights rights (fun _ => .unbound3)
      ⟨#[op], #[.edbLeaf 0 target ProvenanceSemiringOps.one], target, ProvenanceSemiringOps.one,
        comm, witness, mask⟩ = true := by
  simp [verifyPositiveReceipt, hg, hd, ha, ho]

/-- Non-vacuity witness for `verifyPositiveReceipt` (zero Keccak kernel evaluation). -/
theorem verifyPositiveReceipt_inhabited (predSym : UInt32) (rights : UInt64) :
    let raw := "{\"p\":\"rel\",\"a\":\"x\"}".toByteArray
    let doc := mkDocChunk 1 0 raw
    let db : SemanticDatabank := ⟨0, #[doc]⟩
    let g : GrammarSpec := ⟨wellMatchedJsonVpa, ⟨#[("x".toByteArray, 7)]⟩,
      #[⟨"rel".toByteArray, predSym, 1, Obend.Judge.SymbolicRegex.tt, .ff⟩]⟩
    let pp := Obend.Crypto.inhabitedAjtaiParams 0
    let queryPol : KgQueryPolicy := ⟨⟨[]⟩, rights, .const true⟩
    ∃ (rcpt : PositiveSemanticReceipt) (op : EdbSpanOpening),
      verifyEdbSpanOpening (databankChunkMerkleRoot db) g op = true ∧
      verifyPosLineageDag #[op] #[] rcpt.lineageDag rcpt.targetTuple rcpt.claimedWeight = true ∧
      verifyMaskedAjtaiOpening pp 0 rcpt.ajtaiComm rcpt.ajtaiWitness rcpt.ajtaiMask = true ∧
      verifyPositiveReceipt (databankChunkMerkleRoot db) g #[] pp 0 queryPol rights rights
        (fun _ => .unbound3) rcpt = true := by
  intro raw doc db g pp queryPol
  obtain ⟨_, _, ⟨atoms, hSz1, hEx⟩⟩ := extractSpanBoundAtoms_inhabited predSym
  have hPos : 0 < atoms.size := by omega
  let a := atoms[0]'hPos; have haMem : a ∈ atoms := Array.getElem_mem hPos
  have haValid := (span_parse_sound_and_unforgeable hEx hEx).2.2.2.1 a haMem
  have hMerkle : verifyDatabankChunkInclusion (databankChunkMerkleRoot db) doc
      (databankChunkMerkleProof db 0) = true :=
    verifyDatabankChunkInclusion_complete db 0 (by decide)
      (wfDocChunk_mkDocChunk (by decide) (by decide) (by decide))
  let redPol : RedactionSlicePolicy := ⟨19, #[(0, 19)]⟩
  have hRawSz : doc.rawBytes.size = 19 := by change raw.size = 19; decide
  have hRedConf : checkRedactionDelimiterConfined doc.rawBytes redPol = true := by
    have hElid : elidedGaps redPol = [] := by decide
    simp [checkRedactionDelimiterConfined, redPol, hRawSz, hElid, checkSortedDisjointSpansFrom]
  have hInBounds : a.byteStart + a.byteLen ≤ 19 := hRawSz ▸ haValid.in_bounds
  have hOneNeZero : (ProvenanceSemiringOps.one : ProvVec4) ≠ ProvenanceSemiringOps.zero := by
    intro hEq
    have h0 : (1 : Nat) = 0 := congrArg (fun v : ProvVec4 => v.limbs[0].val) hEq
    exact Nat.one_ne_zero h0
  let op : EdbSpanOpening := ⟨0, doc, databankChunkMerkleProof db 0, redPol, (0, 19), a, ProvenanceSemiringOps.one⟩
  let target := spanAtomToGroundTuple a; let wZero : List Int := [0, 0, 0, 0]
  have hwLen : wZero.length = pp.cols := by decide
  let comm := Obend.Crypto.ajtaiCommit pp (Obend.Crypto.vecAdd wZero wZero)
    ((Obend.Crypto.vecAdd_length wZero wZero rfl).trans hwLen)
  have hSpMem : redPol.disclosedSpans.toList.contains (0, 19) = true := by decide
  have hEx' : extractSpanBoundAtoms g doc = .ok atoms := hEx
  have hOpOk : verifyEdbSpanOpening (databankChunkMerkleRoot db) g op = true := by
    have hPrfIdx : (databankChunkMerkleProof db 0).index = 0 := rfl
    have hStart0 : decide (0 ≤ a.byteStart) = true := by simp
    have hEnd19 : decide (a.byteStart + a.byteLen ≤ 19) = true := decide_eq_true hInBounds
    simp only [verifyEdbSpanOpening, op, hPrfIdx, beq_self_eq_true, hMerkle, hRedConf, hSpMem,
      hStart0, hEnd19, hEx', Array.contains_iff_mem.mpr haMem, bne_iff_ne.mpr hOneNeZero, Bool.and_self]
  have hDagOk : verifyPosLineageDag #[op] #[] #[.edbLeaf 0 target ProvenanceSemiringOps.one]
      target ProvenanceSemiringOps.one = true := by
    simp [verifyPosLineageDag, verifyPosLineageNode, bne_iff_ne.mpr hOneNeZero, op, target,
      PosLineageNode.tuple, PosLineageNode.weight, Array.range_eq_range']
  have hAjtaiOk : verifyMaskedAjtaiOpening pp 0 comm wZero wZero = true := by
    unfold verifyMaskedAjtaiOpening; rw [dite_eq_left hwLen, dite_eq_left hwLen]
    have hNorm : Obend.Crypto.checkShortNorm 0 wZero = true := by decide
    simp [hNorm, comm]
  have hGuardOk : checkKgQueryGuard queryPol rights rights (fun _ => .unbound3) = true :=
    checkKgQueryGuard_inhabited ⟨[]⟩ rights
  refine ⟨⟨#[op], #[.edbLeaf 0 target ProvenanceSemiringOps.one], target, ProvenanceSemiringOps.one,
    comm, wZero, wZero⟩, op, hOpOk, hDagOk, hAjtaiOk, ?_⟩
  exact singleton_positive _ g pp queryPol rights op target comm wZero wZero hOpOk hDagOk hAjtaiOk hGuardOk

/-! ## §2. Computable `SortedKTable Bool` WF & `WhyNotSemanticReceipt` (Modes A & B) -/
private def checkSortedKTableBoolWFGo (es : Array (Datalog.GroundTuple × Bool)) (i : Nat) : Bool :=
  if h : i < es.size then
    (es[i]'h).2 &&
    (if hNext : i + 1 < es.size then
      decide (Datalog.TupleLt (es[i]'h).1 (es[i + 1]'hNext).1) && checkSortedKTableBoolWFGo es (i + 1)
    else true)
  else true
termination_by es.size - i

/-- $O(|M|)$ computable Boolean checker deciding `Datalog.SortedKTable.WF` on `SortedKTable Bool`. -/
def checkSortedKTableBoolWF (M : Datalog.SortedKTable Bool) : Bool := checkSortedKTableBoolWFGo M.entries 0
private theorem checkSortedKTableBoolWFGo_iff (es : Array (Datalog.GroundTuple × Bool)) :
    ∀ (i : Nat), checkSortedKTableBoolWFGo es i = true ↔
      (∀ k (hk : k < es.size), i ≤ k → (es[k]'hk).2 = true) ∧
      (∀ k (hk : k + 1 < es.size), i ≤ k → Datalog.TupleLt (es[k]'(by omega)).1 (es[k + 1]'hk).1) := by
  intro i; induction fuel : es.size - i using Nat.strongRecOn generalizing i with
  | ind fuel ih =>
    unfold checkSortedKTableBoolWFGo
    by_cases h : i < es.size
    · rw [dite_eq_left h]
      by_cases hNext : i + 1 < es.size
      · rw [dite_eq_left hNext, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          ih (es.size - (i + 1)) (by omega) (i + 1) rfl]
        exact ⟨fun ⟨hB, hL, hTB, hTL⟩ =>
            ⟨fun k hk hik => if he : k = i then he ▸ hB else hTB k hk (by omega),
             fun k hk hik => if he : k = i then he ▸ hL else hTL k hk (by omega)⟩,
          fun ⟨hB, hL⟩ => ⟨hB i h (Nat.le_refl _), hL i hNext (Nat.le_refl _),
            fun k hk hik => hB k hk (by omega), fun k hk hik => hL k hk (by omega)⟩⟩
      · rw [dite_eq_right hNext, Bool.and_true]
        exact ⟨fun hB => ⟨fun k hk hik => (show k = i by omega) ▸ hB, fun k hk hik => by omega⟩,
          fun ⟨hB, _⟩ => hB i h (Nat.le_refl _)⟩
    · rw [dite_eq_right h]; exact ⟨fun _ => ⟨fun k hk hik => by omega, fun k hk hik => by omega⟩, fun _ => rfl⟩
private theorem tupleLt_of_adj {es : Array (Datalog.GroundTuple × Bool)}
    (hAdj : ∀ k (hk : k + 1 < es.size), Datalog.TupleLt (es[k]'(by omega)).1 (es[k + 1]'hk).1) :
    ∀ (d i : Nat) (hi : i < es.size) (hj : i + 1 + d < es.size),
      Datalog.TupleLt (es[i]'hi).1 (es[i + 1 + d]'hj).1
  | 0, i, _, hj => hAdj i hj
  | d + 1, i, hi, hj => Datalog.lt_trans (tupleLt_of_adj hAdj d i hi (by omega)) (hAdj (i + 1 + d) (by omega))

/-- Exact reflection theorem: `checkSortedKTableBoolWF M = true ↔ M.WF`. -/
theorem checkSortedKTableBoolWF_iff (M : Datalog.SortedKTable Bool) :
    checkSortedKTableBoolWF M = true ↔ M.WF := by
  unfold checkSortedKTableBoolWF Datalog.SortedKTable.WF; rw [checkSortedKTableBoolWFGo_iff M.entries 0]
  constructor
  · rintro ⟨hB, hAdj⟩; refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hjEq : i.val + 1 + (j.val - (i.val + 1)) = j.val := by omega
      simpa only [hjEq] using tupleLt_of_adj (fun k hk => hAdj k hk (Nat.zero_le _))
        (j.val - (i.val + 1)) i.val i.isLt (by omega)
    · have ht := hB i.val i.isLt (Nat.zero_le _); change M.entries[i.val].2 ≠ false; rw [ht]; decide
  · rintro ⟨hOrd, hNz⟩
    refine ⟨fun k hk _ => ?_, fun k hk _ => hOrd ⟨k, by omega⟩ ⟨k + 1, hk⟩ (Nat.lt_succ_self k)⟩
    cases hb : M.entries[k].2; · exact False.elim (hNz ⟨k, hk⟩ hb)
    · rfl

/-- Lift `allRulesSatisfied` to declarative `ModelsRules` on any finite `FactSet`. -/
theorem modelsRules_of_allRulesSatisfied {rules : List TgdRule} {M : FactSet}
    (hWf : rules.all WfRule = true) (hSat : allRulesSatisfied rules M = true) :
    ModelsRules Term.const rules M := by
  intro r hrMem τ bodyAtoms hevBody hBodySub
  have hWfRule : WfRule r = true := (List.all_eq_true.mp hWf) r hrMem
  have hFrontInBody : ∀ x ∈ r.frontierVars, x ∈ varsOfPatAtoms r.body := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hWfRule; exact hWfRule.1.2
  obtain ⟨σ, hσMem, hextστ⟩ :=
    SkolemChaseCore.matchPatAtoms_complete Term.const [] τ (ExtendsSubst.nil τ) r.body bodyAtoms M hevBody hBodySub
  obtain ⟨_, σBodyAtoms, hevσBody, _⟩ := SkolemChaseCore.matchPatAtoms_sound Term.const [] σ r.body M hσMem
  have hσBound : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ x = some d :=
    fun x hx => SkolemChaseCore.bound_of_mem_varsOfPatAtoms Term.const σ r.body σBodyAtoms x (hFrontInBody x hx) hevσBody
  obtain ⟨tTuple, hExtract⟩ := SkolemChaseCore.extractFrontierTuple_some_of_all_bound r.frontierVars σ hσBound
  have hIsSat : isSatisfied Term.const r σ M = true := (List.all_eq_true.mp ((List.all_eq_true.mp hSat) r hrMem)) σ hσMem
  cases hHeadMatches : matchPatAtoms Term.const (frontierSubst r.frontierVars σ) r.head M with
  | nil => simp [isSatisfied, hHeadMatches] at hIsSat
  | cons τ' _ =>
    obtain ⟨hextFront, headAtoms, hevHead, hHeadSub⟩ :=
      SkolemChaseCore.matchPatAtoms_sound Term.const (frontierSubst r.frontierVars σ) τ' r.head M (hHeadMatches ▸ .head _)
    refine ⟨τ', headAtoms, fun x hx => ?_, hevHead, hHeadSub⟩
    obtain ⟨d, hdσ⟩ := hσBound x hx
    have hZip : lookupSubst (frontierSubst r.frontierVars σ) x = some d := by
      simp only [frontierSubst, hExtract]
      rw [SkolemChaseCore.lookupSubst_zip_of_extract r.frontierVars σ tTuple hExtract x hx]; exact hdσ
    rw [hextFront x d hZip, hextστ x d hdσ]
private def nodupAtomsList : List (Atom Term) → Bool
  | [] => true
  | a :: rest => (!rest.contains a) && nodupAtomsList rest

private theorem nodupAtomsList_iff : ∀ xs : List (Atom Term), nodupAtomsList xs = true ↔ xs.Nodup
  | [] => by simp [nodupAtomsList]
  | x :: xs => by
    have hnot : xs.contains x = false ↔ x ∉ xs := by cases h : xs.contains x <;> simp_all
    simp only [nodupAtomsList, Bool.and_eq_true, Bool.not_eq_true', hnot, nodupAtomsList_iff xs, List.nodup_cons]

private def groundChunkFactsGo (atoms : Array (Atom Term)) :
    List SpanBoundAtom → Array Ranked.ArithRule → Option (Array Ranked.ArithRule)
  | [], acc => some acc
  | fact :: rest, acc => do
    let head ← atoms.idxOf? (spanAtomToBaseChaseAtom fact)
    groundChunkFactsGo atoms rest (acc.push ⟨head, #[], #[]⟩)

private def groundChunksGo (g : GrammarSpec) (atoms : Array (Atom Term)) :
    List DocChunkEntry → Array Ranked.ArithRule → Option (Array Ranked.ArithRule)
  | [], acc => some acc
  | chunk :: rest, acc => do
    let facts ← (extractSpanBoundAtoms g chunk).toOption
    let acc' ← groundChunkFactsGo atoms facts.toList acc
    groundChunksGo g atoms rest acc'

private def mapIdxOf? (atoms : Array (Atom Term)) : List (Atom Term) → Array Nat → Option (Array Nat)
  | [], acc => some acc
  | a :: rest, acc => do
    let idx ← atoms.idxOf? a
    mapIdxOf? atoms rest (acc.push idx)

private def groundHeadsGo (atoms : Array (Atom Term)) (pos : Array Nat) :
    List (Atom Term) → Array Ranked.ArithRule → Option (Array Ranked.ArithRule)
  | [], acc => some acc
  | fact :: rest, acc => do
    let head ← atoms.idxOf? fact
    groundHeadsGo atoms pos rest (acc.push ⟨head, pos, #[]⟩)

private def groundRuleSubstsGo (atoms : Array (Atom Term)) (rule : TgdRule) :
    List (Subst Term) → Array Ranked.ArithRule → Option (Array Ranked.ArithRule)
  | [], acc => some acc
  | σ :: rest, acc => do
    let body ← evalPatAtoms Term.const σ rule.body
    let pos ← mapIdxOf? atoms body #[]
    let frontier ← extractFrontierTuple rule.frontierVars σ
    let heads ← instantiateRuleHead rule frontier
    let acc' ← groundHeadsGo atoms pos heads acc
    groundRuleSubstsGo atoms rule rest acc'

private def groundRulesGo (atoms : Array (Atom Term)) (probe : List Nat → Colt.Rows) :
    List TgdRule → Array Ranked.ArithRule → Option (Array Ranked.ArithRule)
  | [], acc => some acc
  | rule :: rest, acc => do
    let acc' ← groundRuleSubstsGo atoms rule (matchBodyColt atoms probe rule.body []).toList acc
    groundRulesGo atoms probe rest acc'

/-- Ground the requested TGDs over a duplicate-free finite atom dictionary using COLT body matching.
Missing EDB atoms and unrepresentable Skolem heads reject the dictionary. Atom IDs are positions
in this same dictionary. -/
def groundWhyNotProgram (g : GrammarSpec) (chunks : Array DocChunkEntry) (rules : Array TgdRule)
    (atoms : Array (Atom Term)) : Option Ranked.ArithProgram := do
  guard (WfRuleSet rules.toList)
  guard (nodupAtomsList atoms.toList)
  let acc₁ ← groundChunksGo g atoms chunks.toList #[]
  let probe := openAtomTrie atoms
  let clauses ← groundRulesGo atoms probe.probe rules.toList acc₁
  return ⟨atoms.size, clauses⟩

private def wfsModel (atoms : Array (Atom Term)) (bits : Array Bool) : Array (Atom Term) :=
  (atoms.zip bits).filterMap fun (a, b) => if b then some a else none

private theorem idxOf?_some_getElem {α : Type} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} {i : Nat} (h : xs.idxOf? a = some i) :
    ∃ hi : i < xs.size, xs[i]'hi = a := by
  have hl : xs.toList.idxOf? a = some i := by
    rw [← List.idxOf?_toArray, Array.toArray_toList]; exact h
  obtain ⟨hi, hget, _⟩ := List.idxOf?_eq_some_iff.mp hl
  exact ⟨by simpa using hi, by simpa [Array.getElem_toList] using hget⟩

private theorem idxOf?_of_nodup_getElem {α : Type} [BEq α] [LawfulBEq α]
    {xs : Array α} (hNd : xs.toList.Nodup) {i : Nat} (hi : i < xs.size) :
    xs.idxOf? (xs[i]'hi) = some i := by
  have hconv : ∀ (x : α), xs.idxOf? x = xs.toList.idxOf? x := fun x => by
    rw [← Array.toArray_toList (xs := xs), List.idxOf?_toArray]
  rw [hconv]
  have hiL : i < xs.toList.length := by simpa using hi
  refine List.idxOf?_eq_some_iff.mpr ⟨hiL, by simp, fun j hj heq => ?_⟩
  have hne := (List.pairwise_iff_getElem.mp hNd) j i (Nat.lt_trans hj hiL) hiL hj
  exact hne (by simpa [Array.getElem_toList] using heq)

private theorem mem_wfsModel_iff {atoms : Array (Atom Term)} {bits : Array Bool}
    (hSz : bits.size = atoms.size) (a : Atom Term) :
    a ∈ (wfsModel atoms bits).toList ↔
      ∃ (j : Nat) (hj : j < atoms.size), atoms[j]'hj = a ∧ Ranked.bit bits j = true := by
  unfold wfsModel
  rw [Array.toList_filterMap, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a', b⟩, hMem, hIf⟩
    cases b with
    | false => cases hIf
    | true =>
      injection hIf with ha; subst ha
      rw [Array.toList_zip] at hMem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hMem
      simp only [List.length_zip, Array.length_toList, hSz, Nat.min_self] at hj
      simp only [List.getElem_zip, Array.getElem_toList, Prod.mk.injEq] at hget
      refine ⟨j, hj, hget.1, ?_⟩
      simp [Ranked.bit, show j < bits.size by omega, hget.2]
  · rintro ⟨j, hj, hEq, hBit⟩
    have hjb : j < bits.size := by omega
    have hbTrue : bits[j]'hjb = true := by simpa [Ranked.bit, hjb] using hBit
    refine ⟨(a, true), ?_, rfl⟩
    rw [Array.toList_zip]
    refine List.mem_iff_getElem.mpr ⟨j, by simp [hSz, hj], ?_⟩
    simp [List.getElem_zip, Array.getElem_toList, hEq, hbTrue]

private theorem mem_wfsModel_of_idxOf? {atoms : Array (Atom Term)} {bits : Array Bool}
    (hSz : bits.size = atoms.size) (hNd : atoms.toList.Nodup)
    {a : Atom Term} {j : Nat} (hIdx : atoms.idxOf? a = some j) :
    a ∈ (wfsModel atoms bits).toList ↔ Ranked.bit bits j = true := by
  rw [mem_wfsModel_iff hSz]
  obtain ⟨hj, hget⟩ := idxOf?_some_getElem hIdx
  constructor
  · rintro ⟨k, hk, hka, hbit⟩
    have hkj : k = j := by
      have hkIdx := idxOf?_of_nodup_getElem hNd hk
      rw [hka, hIdx] at hkIdx
      exact (Option.some.inj hkIdx).symm
    exact hkj ▸ hbit
  · intro hbit
    exact ⟨j, hj, hget, hbit⟩

private theorem groundChunkFactsGo_sound (atoms : Array (Atom Term)) :
    ∀ (facts : List SpanBoundAtom) (acc res : Array Ranked.ArithRule),
      groundChunkFactsGo atoms facts acc = some res →
      (∀ r ∈ acc, r ∈ res) ∧
      ∀ fact ∈ facts, ∃ head, atoms.idxOf? (spanAtomToBaseChaseAtom fact) = some head ∧
        ⟨head, #[], #[]⟩ ∈ res
  | [], acc, res, h => by
    injection h with hr; subst hr; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | fact :: rest, acc, res, h => by
    unfold groundChunkFactsGo at h
    cases hIdx : atoms.idxOf? (spanAtomToBaseChaseAtom fact) with
    | none => simp [hIdx] at h
    | some head =>
      simp only [hIdx, bind, Option.bind] at h
      obtain ⟨hMono, hRest⟩ := groundChunkFactsGo_sound atoms rest _ res h
      refine ⟨fun r hr => hMono r (Array.mem_push.mpr (Or.inl hr)), fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hfRest
      · exact ⟨head, hIdx, hMono _ (Array.mem_push.mpr (Or.inr rfl))⟩
      · exact hRest f hfRest

private theorem groundChunksGo_sound (g : GrammarSpec) (atoms : Array (Atom Term)) :
    ∀ (chunks : List DocChunkEntry) (acc res : Array Ranked.ArithRule),
      groundChunksGo g atoms chunks acc = some res →
      (∀ r ∈ acc, r ∈ res) ∧
      ∀ chunk ∈ chunks, ∃ facts, extractSpanBoundAtoms g chunk = .ok facts ∧
        ∀ fact ∈ facts, ∃ head, atoms.idxOf? (spanAtomToBaseChaseAtom fact) = some head ∧
          ⟨head, #[], #[]⟩ ∈ res
  | [], acc, res, h => by
    injection h with hr; subst hr; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | chunk :: rest, acc, res, h => by
    unfold groundChunksGo at h
    cases hEx : extractSpanBoundAtoms g chunk with
    | error _ => simp [hEx, Except.toOption] at h
    | ok facts =>
      simp only [hEx, Except.toOption, bind, Option.bind] at h
      cases hF : groundChunkFactsGo atoms facts.toList acc with
      | none => simp [hF] at h
      | some acc' =>
        simp only [hF] at h
        obtain ⟨hMono1, hCur⟩ := groundChunkFactsGo_sound atoms facts.toList acc acc' hF
        obtain ⟨hMono2, hRest⟩ := groundChunksGo_sound g atoms rest acc' res h
        refine ⟨fun r hr => hMono2 r (hMono1 r hr), fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hcRest
        · refine ⟨facts, hEx, fun fact hfact => ?_⟩
          obtain ⟨head, hIdx, hMem⟩ := hCur fact (Array.mem_toList_iff.mpr hfact)
          exact ⟨head, hIdx, hMono2 _ hMem⟩
        · exact hRest c hcRest

private theorem mapIdxOf?_sound (atoms : Array (Atom Term)) :
    ∀ (bs : List (Atom Term)) (acc res : Array Nat),
      mapIdxOf? atoms bs acc = some res →
      ∀ idx ∈ res, idx ∈ acc ∨ ∃ a ∈ bs, atoms.idxOf? a = some idx
  | [], acc, res, h => by
    injection h with hr; subst hr; exact fun _ hi => Or.inl hi
  | b :: rest, acc, res, h => by
    unfold mapIdxOf? at h
    cases hIdx : atoms.idxOf? b with
    | none => simp [hIdx] at h
    | some k =>
      simp only [hIdx, bind, Option.bind] at h
      intro idx hMem
      rcases mapIdxOf?_sound atoms rest (acc.push k) res h idx hMem with hAcc | ⟨a, ha, haIdx⟩
      · rcases Array.mem_push.mp hAcc with hOld | rfl
        · exact Or.inl hOld
        · exact Or.inr ⟨b, .head _, hIdx⟩
      · exact Or.inr ⟨a, .tail _ ha, haIdx⟩

private theorem groundHeadsGo_sound (atoms : Array (Atom Term)) (pos : Array Nat) :
    ∀ (heads : List (Atom Term)) (acc res : Array Ranked.ArithRule),
      groundHeadsGo atoms pos heads acc = some res →
      (∀ r ∈ acc, r ∈ res) ∧
      ∀ fact ∈ heads, ∃ head, atoms.idxOf? fact = some head ∧ ⟨head, pos, #[]⟩ ∈ res
  | [], acc, res, h => by
    injection h with hr; subst hr; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | fact :: rest, acc, res, h => by
    unfold groundHeadsGo at h
    cases hIdx : atoms.idxOf? fact with
    | none => simp [hIdx] at h
    | some head =>
      simp only [hIdx, bind, Option.bind] at h
      obtain ⟨hMono, hRest⟩ := groundHeadsGo_sound atoms pos rest _ res h
      refine ⟨fun r hr => hMono r (Array.mem_push.mpr (Or.inl hr)), fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hfRest
      · exact ⟨head, hIdx, hMono _ (Array.mem_push.mpr (Or.inr rfl))⟩
      · exact hRest f hfRest

private theorem groundRuleSubstsGo_sound (atoms : Array (Atom Term)) (rule : TgdRule) :
    ∀ (substs : List (Subst Term)) (acc res : Array Ranked.ArithRule),
      groundRuleSubstsGo atoms rule substs acc = some res →
      (∀ r ∈ acc, r ∈ res) ∧
      ∀ σ ∈ substs,
        ∃ body pos frontier heads,
          evalPatAtoms Term.const σ rule.body = some body ∧
          (∀ idx ∈ pos, ∃ a ∈ body, atoms.idxOf? a = some idx) ∧
          extractFrontierTuple rule.frontierVars σ = some frontier ∧
          instantiateRuleHead rule frontier = some heads ∧
          ∀ fact ∈ heads, ∃ head, atoms.idxOf? fact = some head ∧ ⟨head, pos, #[]⟩ ∈ res
  | [], acc, res, h => by
    injection h with hr; subst hr; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | σ :: rest, acc, res, h => by
    unfold groundRuleSubstsGo at h
    cases hBody : evalPatAtoms Term.const σ rule.body with
    | none => simp [hBody] at h
    | some body =>
      simp only [hBody, bind, Option.bind] at h
      cases hPos : mapIdxOf? atoms body #[] with
      | none => simp [hPos] at h
      | some pos =>
        simp only [hPos] at h
        cases hFront : extractFrontierTuple rule.frontierVars σ with
        | none => simp [hFront] at h
        | some frontier =>
          simp only [hFront] at h
          cases hHeads : instantiateRuleHead rule frontier with
          | none => simp [hHeads] at h
          | some heads =>
            simp only [hHeads] at h
            cases hG : groundHeadsGo atoms pos heads acc with
            | none => simp [hG] at h
            | some acc' =>
              simp only [hG] at h
              obtain ⟨hMono1, hCur⟩ := groundHeadsGo_sound atoms pos heads acc acc' hG
              obtain ⟨hMono2, hRest⟩ := groundRuleSubstsGo_sound atoms rule rest acc' res h
              refine ⟨fun r hr => hMono2 r (hMono1 r hr), fun τ hτ => ?_⟩
              rcases List.mem_cons.mp hτ with rfl | hτRest
              · refine ⟨body, pos, frontier, heads, hBody, ?_, hFront, hHeads, ?_⟩
                · intro idx hIdx
                  rcases mapIdxOf?_sound atoms body #[] pos hPos idx hIdx with hEmp | hFound
                  · simp at hEmp
                  · exact hFound
                · intro fact hfact
                  obtain ⟨head, hHeadIdx, hMem⟩ := hCur fact hfact
                  exact ⟨head, hHeadIdx, hMono2 _ hMem⟩
              · exact hRest τ hτRest

private theorem groundRulesGo_sound (atoms : Array (Atom Term)) (probe : List Nat → Colt.Rows) :
    ∀ (rules : List TgdRule) (acc res : Array Ranked.ArithRule),
      groundRulesGo atoms probe rules acc = some res →
      (∀ r ∈ acc, r ∈ res) ∧
      ∀ rule ∈ rules, ∀ σ ∈ (matchBodyColt atoms probe rule.body []).toList,
        ∃ body pos frontier heads,
          evalPatAtoms Term.const σ rule.body = some body ∧
          (∀ idx ∈ pos, ∃ a ∈ body, atoms.idxOf? a = some idx) ∧
          extractFrontierTuple rule.frontierVars σ = some frontier ∧
          instantiateRuleHead rule frontier = some heads ∧
          ∀ fact ∈ heads, ∃ head, atoms.idxOf? fact = some head ∧ ⟨head, pos, #[]⟩ ∈ res
  | [], acc, res, h => by
    injection h with hr; subst hr; exact ⟨fun _ h => h, fun _ h => nomatch h⟩
  | rule :: rest, acc, res, h => by
    unfold groundRulesGo at h
    cases hS : groundRuleSubstsGo atoms rule (matchBodyColt atoms probe rule.body []).toList acc with
    | none => simp [hS] at h
    | some acc' =>
      simp only [hS, bind, Option.bind] at h
      obtain ⟨hMono1, hCur⟩ := groundRuleSubstsGo_sound atoms rule _ acc acc' hS
      obtain ⟨hMono2, hRest⟩ := groundRulesGo_sound atoms probe rest acc' res h
      refine ⟨fun r hr => hMono2 r (hMono1 r hr), fun r hr σ hσ => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hrRest
      · obtain ⟨body, pos, frontier, heads, hBody, hPos, hFront, hHeads, hFacts⟩ := hCur σ hσ
        exact ⟨body, pos, frontier, heads, hBody, hPos, hFront, hHeads, fun fact hfact =>
          let ⟨head, hIdx, hMem⟩ := hFacts fact hfact
          ⟨head, hIdx, hMono2 _ hMem⟩⟩
      · exact hRest r hrRest σ hσ

/-- Direct semantic bridge from `groundWhyNotProgram` to extracted EDB facts and COLT-grounded
TGD rules via `matchBodyColt_eq_matchBody`. -/
theorem groundWhyNotProgram_sound {g : GrammarSpec} {chunks : Array DocChunkEntry}
    {rules : Array TgdRule} {atoms : Array (Atom Term)} {p : Ranked.ArithProgram}
    (h : groundWhyNotProgram g chunks rules atoms = some p) :
    WfRuleSet rules.toList = true ∧
    atoms.toList.Nodup ∧
    p.numAtoms = atoms.size ∧
    (∀ chunk ∈ chunks, ∃ facts, extractSpanBoundAtoms g chunk = .ok facts ∧
      ∀ fact ∈ facts, ∃ head, atoms.idxOf? (spanAtomToBaseChaseAtom fact) = some head ∧
        ⟨head, #[], #[]⟩ ∈ p.rules) ∧
    (∀ rule ∈ rules.toList, ∀ σ ∈ matchBody atoms.toList rule.body [],
      ∃ body pos frontier heads,
        evalPatAtoms Term.const σ rule.body = some body ∧
        (∀ idx ∈ pos, ∃ a ∈ body, atoms.idxOf? a = some idx) ∧
        extractFrontierTuple rule.frontierVars σ = some frontier ∧
        instantiateRuleHead rule frontier = some heads ∧
        ∀ fact ∈ heads, ∃ head, atoms.idxOf? fact = some head ∧ ⟨head, pos, #[]⟩ ∈ p.rules) := by
  unfold groundWhyNotProgram at h
  cases hWf : WfRuleSet rules.toList with
  | false =>
    simp only [hWf, Bool.false_eq_true, guard, ↓reduceIte, failure, Alternative.failure, bind, Option.bind] at h
    cases h
  | true =>
    cases hNd : nodupAtomsList atoms.toList with
    | false =>
      simp only [hWf, hNd, Bool.false_eq_true, guard, ↓reduceIte, failure, Alternative.failure, pure, bind, Option.bind] at h
      cases h
    | true =>
      simp only [hWf, hNd, guard, ↓reduceIte, pure, bind, Option.bind] at h
      cases hC : groundChunksGo g atoms chunks.toList #[] with
      | none => simp [hC] at h
      | some acc₁ =>
        simp only [hC] at h
        cases hR : groundRulesGo atoms (openAtomTrie atoms).probe rules.toList acc₁ with
        | none => simp [hR] at h
        | some clauses =>
          simp only [hR, Option.some.injEq] at h
          subst p
          obtain ⟨_, hChunks⟩ := groundChunksGo_sound g atoms chunks.toList #[] acc₁ hC
          obtain ⟨hMono, hRules⟩ := groundRulesGo_sound atoms (openAtomTrie atoms).probe rules.toList acc₁ clauses hR
          refine ⟨rfl, (nodupAtomsList_iff _).mp hNd, rfl, ?_, ?_⟩
          · intro chunk hChunk
            obtain ⟨facts, hEx, hFacts⟩ := hChunks chunk (Array.mem_toList_iff.mpr hChunk)
            refine ⟨facts, hEx, fun fact hfact => ?_⟩
            obtain ⟨head, hIdx, hMem⟩ := hFacts fact hfact
            exact ⟨head, hIdx, hMono _ hMem⟩
          · intro rule hRule σ hσ
            rw [← matchBodyColt_eq_matchBody atoms rule.body []] at hσ
            exact hRules rule hRule σ hσ

/-- Constructive inhabitedness witnesses for `groundWhyNotProgram` and its grounding stages. -/
private example :
    groundChunkFactsGo #[] [] #[] = some #[] ∧
    groundChunksGo ⟨wellMatchedJsonVpa, ⟨#[]⟩, #[]⟩ #[] [] #[] = some #[] ∧
    mapIdxOf? #[] [] #[] = some #[] ∧
    groundHeadsGo #[] #[] [] #[] = some #[] ∧
    groundRuleSubstsGo #[] ⟨0, [], [], [], []⟩ [] #[] = some #[] ∧
    groundRulesGo #[] (openAtomTrie #[]).probe [] #[] = some #[] ∧
    groundWhyNotProgram ⟨wellMatchedJsonVpa, ⟨#[]⟩, #[]⟩ #[] #[] #[] = some ⟨0, #[]⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

inductive WhyNotMode where
  | guardedCoreGap (tbl : SymInternTable) (M : Datalog.SortedKTable Bool)
      (targetTuple : Datalog.GroundTuple) (gapCert : Datalog.GapCert)
  | wfsNegationBlocker (atoms : Array (Atom Term)) (tBits uBits : Array Bool)
      (wfsCert : Ranked.ArrayCert) (definiteFalse : Bool)
structure WhyNotSemanticReceipt where
  db   : SemanticDatabank
  mode : WhyNotMode
def checkDatabankExtractedInTable (g : GrammarSpec) (db : SemanticDatabank)
    (tbl : SymInternTable) (M : Datalog.SortedKTable Bool) : Bool :=
  db.chunks.all fun chunk =>
    match extractSpanBoundAtoms g chunk with
    | .error _ => false
    | .ok atoms => atoms.all fun a =>
        let gt := spanAtomToGroundTuple a
        Datalog.lookupFast M gt && (decodeTuple tbl gt == some (spanAtomToBaseChaseAtom a))
def verifyWhyNotReceipt (expectedDbRoot : DatabankRoot256) (g : GrammarSpec)
    (tgdRules : Array TgdRule) (targetAtom : Atom Term) (rcpt : WhyNotSemanticReceipt) : Bool :=
  WfDatabank rcpt.db && (databankCommit256 rcpt.db == expectedDbRoot) &&
  match rcpt.mode with
  | .guardedCoreGap tbl M targetTuple gapCert =>
    checkDatabankExtractedInTable g rcpt.db tbl M && tbl.WF && checkSortedKTableBoolWF M &&
    tableSymsInBounds tbl M && tgdRules.all IsGuardedRule && checkGuardedSaturationFast tbl M tgdRules &&
    (internAtom tbl targetAtom == some targetTuple) && Datalog.verifyGapCert M targetTuple gapCert
  | .wfsNegationBlocker atoms tBits uBits cert definiteFalse =>
    match groundWhyNotProgram g rcpt.db.chunks tgdRules atoms, atoms.idxOf? targetAtom with
    | some p, some i =>
      Ranked.WFProgram p && checkVgrsFixpointLinear p tBits uBits cert &&
      !Ranked.bit tBits i && (!definiteFalse || !Ranked.bit uBits i)
    | _, _ => false
def WhyNotConclusion (g : GrammarSpec) (tgdRules : Array TgdRule)
    (targetAtom : Atom Term) (rcpt : WhyNotSemanticReceipt) : Prop :=
  match rcpt.mode with
  | .guardedCoreGap tbl M _ _ =>
    (∀ chunk ∈ rcpt.db.chunks, ∃ atoms, extractSpanBoundAtoms g chunk = .ok atoms ∧
      ∀ a ∈ atoms, spanAtomToBaseChaseAtom a ∈ decodeSortedFactSet tbl M) ∧
    allRulesSatisfied tgdRules.toList (decodeSortedFactSet tbl M) = true ∧
    ModelsRules Term.const tgdRules.toList (decodeSortedFactSet tbl M) ∧
    targetAtom ∉ decodeSortedFactSet tbl M
  | .wfsNegationBlocker atoms tBits _ _ definiteFalse =>
    let model := (wfsModel atoms tBits).toList
    (∀ c ∈ rcpt.db.chunks, ∃ facts, extractSpanBoundAtoms g c = .ok facts ∧
      ∀ a ∈ facts, spanAtomToBaseChaseAtom a ∈ model) ∧
    ModelsRules Term.const tgdRules.toList model ∧ targetAtom ∉ model ∧
    ∃ p i, groundWhyNotProgram g rcpt.db.chunks tgdRules atoms = some p ∧
      atoms.idxOf? targetAtom = some i ∧
      Ranked.atomName i ∉ (Obend.Reasons.wf (Ranked.toReasonsProgram p)).1 ∧
      (definiteFalse = true → Ranked.atomName i ∉ (Obend.Reasons.wf (Ranked.toReasonsProgram p)).2)
private theorem wfDatabankBounds_of_wfDatabank {db : SemanticDatabank}
    (h : WfDatabank db = true) : WfDatabankBounds db = true := by
  simp only [WfDatabank, WfDatabankBounds, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h ⊢
  exact ⟨h.1, fun c hc => (Bool.and_eq_true_iff.mp (h.2 c hc)).1⟩

private theorem closure_head_true {p : Ranked.ArithProgram} {uBits tBits : Array Bool}
    (hClos : Ranked.checkClosure p uBits tBits = true) {head : Nat} {pos : Array Nat}
    (hRule : ⟨head, pos, #[]⟩ ∈ p.rules) (hPos : ∀ b ∈ pos, Ranked.bit tBits b = true) :
    Ranked.bit tBits head = true := by
  have hR := (Array.all_eq_true_iff_forall_mem.mp hClos) ⟨head, pos, #[]⟩ hRule
  have hFire : Ranked.firesFast ⟨head, pos, #[]⟩ uBits tBits = true := by
    simp [Ranked.firesFast, hPos]
  simpa [hFire] using hR

/-- **Stage-4 Why-Not Receipt Master Soundness Theorem (`semantic_whynot_cert_sound`)**. -/
theorem semantic_whynot_cert_sound
    {dbRef : SemanticDatabank} {expectedDbRoot : DatabankRoot256}
    {g : GrammarSpec} {tgdRules : Array TgdRule} {targetAtom : Atom Term}
    {rcpt : WhyNotSemanticReceipt}
    (hWfRef : WfDatabankBounds dbRef = true) (hRefRoot : databankCommit256 dbRef = expectedDbRoot)
    (hVer : verifyWhyNotReceipt expectedDbRoot g tgdRules targetAtom rcpt = true) :
    (rcpt.db = dbRef ∨
      CollisionAmong deployed (fun m => m = databankPreimage rcpt.db ∨ m = databankPreimage dbRef)) ∧
    WhyNotConclusion g tgdRules targetAtom rcpt := by
  unfold verifyWhyNotReceipt at hVer; simp only [Bool.and_eq_true, beq_iff_eq] at hVer
  obtain ⟨⟨hWfDb, hRootEq⟩, hMode⟩ := hVer
  refine ⟨databankCommit256_binding (wfDatabankBounds_of_wfDatabank hWfDb) hWfRef
    (hRootEq.trans hRefRoot.symm), ?_⟩
  unfold WhyNotConclusion
  cases hM : rcpt.mode with
  | guardedCoreGap tbl M targetTuple gapCert =>
    rw [hM] at hMode; simp only [Bool.and_eq_true, beq_iff_eq] at hMode
    obtain ⟨⟨⟨⟨⟨⟨⟨hEdb, hTbl⟩, hMWfB⟩, hBounds⟩, hGuarded⟩, hSatFast⟩, hIntern⟩, hGap⟩ := hMode
    have hMWf := (checkSortedKTableBoolWF_iff M).mp hMWfB
    have hSatSpec : allRulesSatisfied tgdRules.toList (decodeSortedFactSet tbl M) = true := by
      rw [← checkGuardedSaturationFast_eq_spec tbl M tgdRules hTbl hMWf hBounds hGuarded]; exact hSatFast
    have hWfRules : tgdRules.toList.all WfRule = true := List.all_eq_true.mpr fun r hr =>
      (Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp hGuarded r (Array.mem_toList_iff.mp hr))).1
    have hGapZero := Datalog.sortedGapNonMembership_sound M hMWf targetTuple gapCert hGap
    have hNotMem : targetAtom ∉ decodeSortedFactSet tbl M := fun hMem => by
      have hChk := (checkAtomInTableFast_eq_true_iff hTbl hMWf targetAtom).mpr hMem
      simp only [checkAtomInTableFast, hIntern, hGapZero, ProvenanceSemiringOps.zero] at hChk; cases hChk
    refine ⟨fun chunk hChunk => ?_, hSatSpec, modelsRules_of_allRulesSatisfied hWfRules hSatSpec, hNotMem⟩
    have hC := Array.all_eq_true_iff_forall_mem.mp hEdb chunk hChunk
    cases hEx : extractSpanBoundAtoms g chunk with
    | error _ => rw [hEx] at hC; cases hC
    | ok atoms =>
      rw [hEx] at hC; refine ⟨atoms, rfl, fun a ha => ?_⟩
      have haOk := Array.all_eq_true_iff_forall_mem.mp hC a ha
      simp only [Bool.and_eq_true, beq_iff_eq] at haOk
      refine (checkAtomInTableFast_eq_true_iff hTbl hMWf (spanAtomToBaseChaseAtom a)).mp ?_
      simp [checkAtomInTableFast, internAtom_of_decodeTuple hTbl haOk.2, haOk.1, ProvenanceSemiringOps.zero]
  | wfsNegationBlocker atoms tBits uBits cert definiteFalse =>
    rw [hM] at hMode
    cases hp : groundWhyNotProgram g rcpt.db.chunks tgdRules atoms with
    | none => simp [hp] at hMode
    | some p =>
      cases hi : atoms.idxOf? targetAtom with
      | none => simp [hp, hi] at hMode
      | some i =>
        simp only [hp, hi, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hMode
        obtain ⟨⟨⟨hWf, hFix⟩, hT⟩, hU⟩ := hMode
        have hCheck : tBits.size = p.numAtoms ∧ uBits.size = p.numAtoms ∧
            Ranked.checkClosure p uBits tBits = true := by
          unfold checkVgrsFixpointLinear Ranked.checkRankedWFS at hFix
          simp only [Bool.and_eq_true, beq_iff_eq] at hFix
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, ht⟩, hu⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hClos⟩ := hFix
          exact ⟨ht, hu, hClos⟩
        obtain ⟨hTSz, hUSz, hClos⟩ := hCheck
        have hSame := (checkVgrsFixpointLinear_iff_wfs p tBits uBits hWf hTSz hUSz).mp ⟨cert, hFix⟩
        obtain ⟨_, hNd, hNum, hChunks, hRules⟩ := groundWhyNotProgram_sound hp
        have hBitsSz : tBits.size = atoms.size := hTSz.trans hNum
        refine ⟨?_, ?_, ?_, p, i, hp, hi, ?_, ?_⟩
        · intro c hc
          obtain ⟨facts, hEx, hFacts⟩ := hChunks c hc
          refine ⟨facts, hEx, fun a ha => ?_⟩
          obtain ⟨head, hIdx, hRuleMem⟩ := hFacts a ha
          have hBit : Ranked.bit tBits head = true :=
            closure_head_true hClos hRuleMem (fun _ hb => by simp at hb)
          exact (mem_wfsModel_of_idxOf? hBitsSz hNd hIdx).mpr hBit
        · intro r hrMem τ bodyAtoms hevBody hBodySub
          have hSubAtoms : ∀ a ∈ bodyAtoms, a ∈ atoms.toList := fun a ha => by
            obtain ⟨j, hj, hget, _⟩ := (mem_wfsModel_iff hBitsSz a).mp (hBodySub a ha)
            exact hget ▸ Array.getElem_mem_toList hj
          obtain ⟨σ, hσMem, hExtστ⟩ :=
            SkolemChaseCore.matchPatAtoms_complete Term.const [] τ (ExtendsSubst.nil τ)
              r.body bodyAtoms atoms.toList hevBody hSubAtoms
          obtain ⟨body', pos, frontier, heads, hBody', hPos, hFront, hHeads, hRuleHeads⟩ :=
            hRules r hrMem σ hσMem
          have hBodyEq : body' = bodyAtoms := by
            have h1 := SkolemChaseCore.evalPatAtoms_ext Term.const hExtστ r.body body' hBody'
            rw [hevBody] at h1
            exact (Option.some.inj h1).symm
          subst hBodyEq
          have hPosTrue : ∀ b ∈ pos, Ranked.bit tBits b = true := fun b hb => by
            obtain ⟨a, haBody, haIdx⟩ := hPos b hb
            exact (mem_wfsModel_of_idxOf? hBitsSz hNd haIdx).mp (hBodySub a haBody)
          let τ' := buildHeadSubst r.frontierVars frontier r.existVars (fun y => Term.skolem r.id y frontier)
          refine ⟨τ', heads, fun x hx => ?_, hHeads, fun fact hfact => ?_⟩
          · have hZip := SkolemChaseCore.lookupSubst_zip_of_extract r.frontierVars σ frontier hFront x hx
            have hσSome : ∃ d, lookupSubst σ x = some d := by
              have hEx : ∀ (vs : List VarId) (fr : List Term),
                  extractFrontierTuple vs σ = some fr → x ∈ vs → ∃ d, lookupSubst σ x = some d := by
                intro vs
                induction vs with
                | nil => intro _ _ h; cases h
                | cons v vs ih =>
                  intro fr hF hMem
                  unfold extractFrontierTuple at hF
                  cases hv : lookupSubst σ v with
                  | none => simp [hv] at hF
                  | some dv =>
                    rw [hv] at hF
                    cases hvs : extractFrontierTuple vs σ with
                    | none => simp [hvs] at hF
                    | some dvs =>
                      rcases List.mem_cons.mp hMem with rfl | hRest
                      · exact ⟨dv, hv⟩
                      · exact ih dvs hvs hRest
              exact hEx r.frontierVars frontier hFront hx
            obtain ⟨d, hd⟩ := hσSome
            have hLeft : lookupSubst (r.frontierVars.zip frontier) x = some d := hZip.trans hd
            have hτ' : lookupSubst τ' x = some d :=
              SkolemChaseCore.lookupSubst_append_left (r.frontierVars.zip frontier) _ x d hLeft
            rw [hτ', hExtστ x d hd]
          · obtain ⟨head, hHeadIdx, hRuleMem⟩ := hRuleHeads fact hfact
            have hBit : Ranked.bit tBits head = true := closure_head_true hClos hRuleMem hPosTrue
            exact (mem_wfsModel_of_idxOf? hBitsSz hNd hHeadIdx).mpr hBit
        · intro hMem
          have hBit := (mem_wfsModel_of_idxOf? hBitsSz hNd hi).mp hMem
          simp [hT] at hBit
        · intro hm
          have ht := (Ranked.mem_decodeBits _ _).mp ((hSame.1 _).mpr hm)
          simp [hT] at ht
        · intro hd hm
          have hu := (Ranked.mem_decodeBits _ _).mp ((hSame.2 _).mpr hm)
          rcases hU with hf | hf <;> simp_all

deriving instance DecidableEq for Ranked.ArithProgram

/-- Non-vacuity witness for `verifyWhyNotReceipt` in BOTH Mode A and Mode B. -/
theorem verifyWhyNotReceipt_inhabited (worldRoot : DatabankRoot256) :
    let db : SemanticDatabank := ⟨worldRoot, #[]⟩
    let g : GrammarSpec := ⟨wellMatchedJsonVpa, ⟨#[]⟩, #[]⟩
    let r : TgdRule := ⟨1, [0], [], [⟨0, [.var 0]⟩], [⟨1, [.var 0]⟩]⟩
    let targetAtom : Atom Term := ⟨2, [.const 0]⟩
    (∃ rcptA, verifyWhyNotReceipt (databankCommit256 db) g #[r] targetAtom rcptA = true) ∧
    (∃ rcptB, verifyWhyNotReceipt (databankCommit256 db) g #[r] targetAtom rcptB = true) := by
  intro db g r targetAtom
  have hWfDb : WfDatabank db = true := by simp [WfDatabank, db]
  constructor
  · let tbl : SymInternTable := ⟨#[.const 0]⟩
    let M : Datalog.SortedKTable Bool := ⟨#[(⟨0, #[0]⟩, true), (⟨1, #[0]⟩, true)]⟩
    refine ⟨⟨db, .guardedCoreGap tbl M ⟨2, #[0]⟩ .aboveLast⟩, ?_⟩
    obtain ⟨hTbl, hMWf, hBnd, hG, hSat⟩ := checkGuardedSaturationFast_inhabited 0
    have hMWfB := (checkSortedKTableBoolWF_iff M).mpr hMWf
    have hInt : internAtom tbl targetAtom = some ⟨2, #[0]⟩ := by
      simp [internAtom, internTerms, internTerm, internTermGo, tbl, targetAtom]
    have hGap : Datalog.verifyGapCert M ⟨2, #[0]⟩ .aboveLast = true := by decide
    have hTbl' : tbl.WF = true := hTbl
    have hBnd' : tableSymsInBounds tbl M = true := hBnd
    have hG' : IsGuardedRule r = true := hG
    have hSat' : checkGuardedSaturationFast tbl M #[r] = true := hSat
    simp [verifyWhyNotReceipt, hWfDb, checkDatabankExtractedInTable, db, hTbl', hMWfB, hBnd', hG', hSat', hInt, hGap]
  · let p : Ranked.ArithProgram := ⟨1, #[]⟩
    let cert : Ranked.ArrayCert := ⟨#[0], #[0], #[0], #[0], #[0], #[]⟩
    refine ⟨⟨db, .wfsNegationBlocker #[targetAtom] #[false] #[false] cert true⟩, ?_⟩
    have hWfP : Ranked.WFProgram p = true := by simp [Ranked.WFProgram, p]
    have hVgrs : checkVgrsFixpointLinear p #[false] #[false] cert = true := by
      simp [checkVgrsFixpointLinear, Ranked.checkRankedWFS, p, cert, Ranked.WFProgram,
        Ranked.checkClosure, Ranked.bit, Array.range_eq_range']
    have hGround : groundWhyNotProgram g #[] #[r] #[targetAtom] = some p := by
      simp only [groundWhyNotProgram, openAtomTrie, funext (Colt.probe_eq_select _ _)]
      decide +kernel
    have hIdx : (#[targetAtom] : Array (Atom Term)).idxOf? targetAtom = some 0 := by decide +kernel
    simp only [verifyWhyNotReceipt, hWfDb, beq_self_eq_true, Bool.and_self, Bool.true_and,
      show db.chunks = #[] from rfl, hGround, hIdx, hWfP, hVgrs]
    decide +kernel

/-! ## §3. Non-Tautological `semanticKgJudge` & `"semantic-kg@1"` `Obend.Judge.Format` -/
def ExtractedEdbFacts (g : GrammarSpec) (db : SemanticDatabank) (I : FactSet) : Prop :=
  ∃ chunkAtomLists : List (Array SpanBoundAtom),
    chunkAtomLists.length = db.chunks.size ∧
    (∀ (i : Nat) (hi : i < db.chunks.size),
      ∃ atoms, chunkAtomLists[i]? = some atoms ∧
        extractSpanBoundAtoms g (db.chunks[i]'hi) = .ok atoms) ∧
    I = chunkAtomLists.flatMap (fun arr => arr.toList.map spanAtomToBaseChaseAtom)
inductive SemanticKgCert where
  | chaseProof (fuel : Nat)
  | countermodel (tbl : SymInternTable) (M : Datalog.SortedKTable Bool)
      (targetTuple : Datalog.GroundTuple) (gapCert : Datalog.GapCert)
inductive SemanticKgClause where
  | nonBaseTargetAtom | queryGuardDenied | invalidRuleSet | unguardedRule (ruleIdx : Nat)
  | invalidDatabank | databankRootMismatch | chunkParseFailed (chunkIdx : Nat) | saturatedCountermodel
  deriving DecidableEq, Repr

/-- **Pure Declarative Mathematical Specification (`SemanticKgMeaning`)**. -/
def SemanticKgMeaning (o : SemanticKgObj) (_c : SemanticKgCert) : Prop :=
  WfDatabank o.db = true ∧ databankCommit256 o.db = o.expectedDbRoot ∧
  Obend.Polis.subMask o.queryPolicy.needRights (o.rights &&& o.mask) = true ∧
  Obend.Polis.KleenePred3.accepts (o.queryPolicy.caveat.eval o.env) = true ∧
  WfRuleSet o.tgdRules.toList = true ∧ (∀ r ∈ o.tgdRules.toList, IsGuardedRule r = true) ∧
  isBaseAtom o.targetAtom = true ∧
  ∃ I : FactSet, ExtractedEdbFacts o.grammar o.db I ∧
    ∀ (N : FactSet) (cw : RuleId → List Term → VarId → Term),
      (∀ a ∈ I, a ∈ N) → WitnessSatisfiesRules Term.const o.tgdRules.toList N cw → o.targetAtom ∈ N

/-- Inhabited finite-chase-saturating fragment for `semanticKgJudge` completeness. -/
def SemanticKgFragment (o : SemanticKgObj) : Prop :=
  WfDatabank o.db = true ∧ databankCommit256 o.db = o.expectedDbRoot ∧
  Obend.Polis.subMask o.queryPolicy.needRights (o.rights &&& o.mask) = true ∧
  Obend.Polis.KleenePred3.accepts (o.queryPolicy.caveat.eval o.env) = true ∧
  WfRuleSet o.tgdRules.toList = true ∧ (∀ r ∈ o.tgdRules.toList, IsGuardedRule r = true) ∧
  isBaseAtom o.targetAtom = true ∧
  ∃ I : FactSet, ExtractedEdbFacts o.grammar o.db I ∧
    ∃ fuel : Nat, allRulesSatisfied o.tgdRules.toList (runBoundedChase o.tgdRules.toList fuel I) = true
def chaseWitnessOf (rules : List TgdRule) (M : FactSet) : RuleId → List Term → VarId → Term :=
  fun rid dTuple y =>
    match rules.find? (fun r => r.id == rid) with
    | none => .const 0
    | some r => match matchPatAtoms Term.const (r.frontierVars.zip dTuple) r.head M with
      | [] => .const 0 | τ' :: _ => (lookupSubst τ' y).getD (.const 0)
private theorem evalPatArgs_eq_of_agree {Dom : Type} (constOf : ConstId → Dom) {σ₁ σ₂ : Subst Dom} :
    ∀ (pts : List PatTerm),
      (∀ v ∈ pts.filterMap (fun pt => match pt with | .var u => some u | .const _ => none),
        lookupSubst σ₁ v = lookupSubst σ₂ v) →
      evalPatArgs constOf σ₁ pts = evalPatArgs constOf σ₂ pts
  | [], _ => rfl
  | pt :: rest, hAgree => by
    have h1 : evalPatTerm constOf σ₁ pt = evalPatTerm constOf σ₂ pt := by
      cases pt with | const _ => rfl | var v => exact hAgree v (by simp)
    simp only [evalPatArgs, h1, evalPatArgs_eq_of_agree constOf rest fun v hv => hAgree v (by cases pt <;> simp [hv])]
private theorem evalPatAtoms_eq_of_agree {Dom : Type} (constOf : ConstId → Dom) {σ₁ σ₂ : Subst Dom} :
    ∀ (pas : List PatAtom),
      (∀ v ∈ varsOfPatAtoms pas, lookupSubst σ₁ v = lookupSubst σ₂ v) →
      evalPatAtoms constOf σ₁ pas = evalPatAtoms constOf σ₂ pas
  | [], _ => rfl
  | pa :: rest, hAgree => by
    have h1 : evalPatAtom constOf σ₁ pa = evalPatAtom constOf σ₂ pa := by
      unfold evalPatAtom; rw [evalPatArgs_eq_of_agree constOf pa.args (fun v hv => hAgree v (List.mem_flatMap.mpr ⟨pa, .head _, hv⟩))]
    have h2 := evalPatAtoms_eq_of_agree constOf rest fun v hv => by
      obtain ⟨p, hp, hvp⟩ := List.mem_flatMap.mp hv; exact hAgree v (List.mem_flatMap.mpr ⟨p, .tail _ hp, hvp⟩)
    simp only [evalPatAtoms, h1, h2]
private theorem extractFrontierTuple_of_extends {Dom : Type} {σ τ : Subst Dom}
    (hext : ExtendsSubst σ τ) :
    ∀ (fvs : List VarId) (ts : List Dom),
      extractFrontierTuple fvs σ = some ts → extractFrontierTuple fvs τ = some ts
  | [], _, h => h
  | v :: vs, _, h => by
    simp only [extractFrontierTuple] at h ⊢
    cases h1 : lookupSubst σ v with | none => simp [h1] at h | some d =>
      cases h2 : extractFrontierTuple vs σ with | none => simp [h1, h2] at h | some ds =>
        simp only [h1, h2, Option.some.injEq] at h; subst h
        simp [hext v d h1, extractFrontierTuple_of_extends hext vs ds h2]
private theorem find?_rule_of_nodup_id {r : TgdRule} :
    ∀ (rs : List TgdRule), (rs.map (·.id)).Nodup → r ∈ rs → rs.find? (fun r' => r'.id == r.id) = some r
  | [], _, hm => nomatch hm
  | r₀ :: rest, hNd, hm => by
    rw [List.map_cons, List.nodup_cons] at hNd; simp only [List.find?]
    rcases List.mem_cons.mp hm with rfl | hRest
    · simp
    · have hNe : (r₀.id == r.id) = false := by
        cases hEq : (r₀.id == r.id) with
        | false => rfl
        | true => exact False.elim (hNd.1 (beq_iff_eq.mp hEq ▸ List.mem_map_of_mem (f := (·.id)) hRest))
      rw [hNe]; exact find?_rule_of_nodup_id rest hNd.2 hRest
private theorem witnessSatisfiesRules_of_allRulesSatisfied
    {rules : List TgdRule} {M : FactSet} (hWf : WfRuleSet rules = true)
    (hSat : allRulesSatisfied rules M = true) :
    WitnessSatisfiesRules Term.const rules M (chaseWitnessOf rules M) := by
  simp only [WfRuleSet, Bool.and_eq_true] at hWf
  have hNdIds := (SkolemChaseCore.nodupVars_iff_nodup _).mp hWf.2
  intro r hrMem σN bodyAtomsN hevBody hBodyIn dTuple hExt
  have hWfR : WfRule r = true := (List.all_eq_true.mp hWf.1) r hrMem
  have hFrontInBody : ∀ x ∈ r.frontierVars, x ∈ varsOfPatAtoms r.body := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hWfR; exact hWfR.1.2
  have hHeadVars : ∀ v ∈ varsOfPatAtoms r.head, v ∈ r.frontierVars ∨ v ∈ r.existVars := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hWfR; exact hWfR.2
  have hDisj : ∀ y ∈ r.existVars, y ∉ r.frontierVars := fun y hy hMemF => by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hWfR
    have hF := hWfR.1.1.2 y hy; rw [List.contains_iff_mem.mpr hMemF] at hF; cases hF
  obtain ⟨σ, hσMem, hextστ⟩ :=
    SkolemChaseCore.matchPatAtoms_complete Term.const [] σN (ExtendsSubst.nil σN) r.body bodyAtomsN M hevBody hBodyIn
  obtain ⟨_, σBodyAtoms, hevσBody, _⟩ := SkolemChaseCore.matchPatAtoms_sound Term.const [] σ r.body M hσMem
  have hσBound : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ x = some d :=
    fun x hx => SkolemChaseCore.bound_of_mem_varsOfPatAtoms Term.const σ r.body σBodyAtoms x (hFrontInBody x hx) hevσBody
  obtain ⟨tTuple, hExtσ⟩ := SkolemChaseCore.extractFrontierTuple_some_of_all_bound r.frontierVars σ hσBound
  have hTupleEq : tTuple = dTuple := by
    have hN2 := extractFrontierTuple_of_extends hextστ r.frontierVars tTuple hExtσ
    rw [hN2] at hExt; exact Option.some.inj hExt
  subst hTupleEq
  have hIsSat : isSatisfied Term.const r σ M = true := (List.all_eq_true.mp ((List.all_eq_true.mp hSat) r hrMem)) σ hσMem
  have hFrontZip : frontierSubst r.frontierVars σ = r.frontierVars.zip tTuple := by simp [frontierSubst, hExtσ]
  unfold isSatisfied at hIsSat; rw [hFrontZip] at hIsSat
  cases hHm : matchPatAtoms Term.const (r.frontierVars.zip tTuple) r.head M with
  | nil => simp [hHm] at hIsSat
  | cons τ' _ =>
    obtain ⟨hextFront, headAtoms, hevHead, hHeadIn⟩ :=
      SkolemChaseCore.matchPatAtoms_sound Term.const (r.frontierVars.zip tTuple) τ' r.head M (hHm ▸ .head _)
    have hFindR := find?_rule_of_nodup_id rules hNdIds hrMem
    refine ⟨headAtoms, ?_, hHeadIn⟩
    rw [evalPatAtoms_eq_of_agree Term.const r.head (σ₂ := τ'), hevHead]; intro v hv
    rcases hHeadVars v hv with hvF | hvE
    · have hLookB := SkolemChaseCore.lookupSubst_buildHeadSubst_frontier r.frontierVars tTuple r.existVars
        (chaseWitnessOf rules M r.id tTuple) σ hExtσ hvF
      obtain ⟨d, hdσ⟩ := hσBound v hvF
      have hZip : lookupSubst (r.frontierVars.zip tTuple) v = some d := by
        rw [SkolemChaseCore.lookupSubst_zip_of_extract r.frontierVars σ tTuple hExtσ v hvF]; exact hdσ
      rw [hLookB, hdσ, hextFront v d hZip]
    · have hLookB : lookupSubst (buildHeadSubst r.frontierVars tTuple r.existVars
          (chaseWitnessOf rules M r.id tTuple)) v = some (chaseWitnessOf rules M r.id tTuple v) := by
        simp only [buildHeadSubst]
        rw [SkolemChaseCore.lookupSubst_append_of_left_none _ _ v
          (SkolemChaseCore.lookupSubst_zip_none_of_not_mem r.frontierVars tTuple (hDisj v hvE))]
        exact SkolemChaseCore.lookupSubst_map_mkExist r.existVars _ hvE
      obtain ⟨d, hdτ'⟩ := SkolemChaseCore.bound_of_mem_varsOfPatAtoms Term.const τ' r.head headAtoms v hv hevHead
      rw [hLookB, hdτ']; simp [chaseWitnessOf, hFindR, hHm, hdτ']
private def extractAllChunksGo (g : GrammarSpec) (chunks : Array DocChunkEntry)
    (idx : Nat) (acc : List (Array SpanBoundAtom)) : Except Nat (List (Array SpanBoundAtom)) :=
  if h : idx < chunks.size then
    match extractSpanBoundAtoms g (chunks[idx]'h) with
    | .ok atoms => extractAllChunksGo g chunks (idx + 1) (acc ++ [atoms])
    | .error _ => .error idx
  else .ok acc
termination_by chunks.size - idx
private def findUnguardedRuleGo (rules : Array TgdRule) (idx : Nat) : Option Nat :=
  if h : idx < rules.size then
    if IsGuardedRule (rules[idx]'h) then findUnguardedRuleGo rules (idx + 1) else some idx
  else none
termination_by rules.size - idx
private theorem findUnguardedRuleGo_some (rules : Array TgdRule) :
    ∀ idx i, findUnguardedRuleGo rules idx = some i → ∃ h : i < rules.size, IsGuardedRule (rules[i]'h) = false := by
  intro idx i hEq; induction fuel : rules.size - idx using Nat.strongRecOn generalizing idx with
  | ind fuel ih =>
    unfold findUnguardedRuleGo at hEq
    by_cases h : idx < rules.size
    · rw [dite_eq_left h] at hEq; cases hG : IsGuardedRule (rules[idx]'h)
      · simp only [hG, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEq; subst hEq; exact ⟨h, hG⟩
      · simp only [hG, ↓reduceIte] at hEq; exact ih (rules.size - (idx + 1)) (by omega) (idx + 1) hEq rfl
    · rw [dite_eq_right h] at hEq; cases hEq
private theorem findUnguardedRuleGo_none (rules : Array TgdRule) :
    ∀ idx, findUnguardedRuleGo rules idx = none → ∀ j (hj : j < rules.size), idx ≤ j → IsGuardedRule (rules[j]'hj) = true := by
  intro idx hEq; induction fuel : rules.size - idx using Nat.strongRecOn generalizing idx with
  | ind fuel ih =>
    intro j hj hij; unfold findUnguardedRuleGo at hEq
    by_cases h : idx < rules.size
    · rw [dite_eq_left h] at hEq; cases hG : IsGuardedRule (rules[idx]'h)
      · simp [hG] at hEq
      · simp only [hG, ↓reduceIte] at hEq
        if hji : j = idx then subst hji; exact hG
        else exact ih (rules.size - (idx + 1)) (by omega) (idx + 1) hEq rfl j hj (by omega)
    · omega
private theorem extractAllChunksGo_ok_le (g : GrammarSpec) (chunks : Array DocChunkEntry) :
    ∀ (idx : Nat) (acc res : List (Array SpanBoundAtom)),
      idx ≤ chunks.size → acc.length = idx →
      (∀ (j : Nat), j < idx → ∀ (hjC : j < chunks.size),
        ∃ atoms, acc[j]? = some atoms ∧ extractSpanBoundAtoms g (chunks[j]'hjC) = .ok atoms) →
      extractAllChunksGo g chunks idx acc = .ok res →
      res.length = chunks.size ∧
      ∀ (j : Nat) (hj : j < chunks.size),
        ∃ atoms, res[j]? = some atoms ∧ extractSpanBoundAtoms g (chunks[j]'hj) = .ok atoms := by
  intro idx acc res hLe hAccLen hAccOk hGo
  induction fuel : chunks.size - idx using Nat.strongRecOn generalizing idx acc with
  | ind fuel ih =>
    unfold extractAllChunksGo at hGo
    by_cases h : idx < chunks.size
    · rw [dite_eq_left h] at hGo
      cases hEx : extractSpanBoundAtoms g (chunks[idx]'h) with
      | error _ => rw [hEx] at hGo; cases hGo
      | ok atoms =>
        rw [hEx] at hGo
        refine ih (chunks.size - (idx + 1)) (by omega) (idx + 1) (acc ++ [atoms])
          (by omega) (by simp [hAccLen]) ?_ hGo rfl
        intro j hj hjC
        by_cases hji : j < idx
        · obtain ⟨as, has, hex⟩ := hAccOk j hji hjC
          exact ⟨as, by rw [List.getElem?_append_left (by omega)]; exact has, hex⟩
        · have hjEq : j = idx := by omega
          subst j
          refine ⟨atoms, ?_, hEx⟩
          rw [List.getElem?_append_right (by omega)]; simp [hAccLen]
    · rw [dite_eq_right h, Except.ok.injEq] at hGo; subst hGo
      exact ⟨hAccLen.trans (by omega), fun j hj => hAccOk j (by omega) hj⟩
private theorem extractAllChunksGo_err (g : GrammarSpec) (chunks : Array DocChunkEntry) :
    ∀ (idx : Nat) (acc : List (Array SpanBoundAtom)) (badIdx : Nat),
      extractAllChunksGo g chunks idx acc = .error badIdx →
      ∃ (h : badIdx < chunks.size) (err : ParseRefusal),
        extractSpanBoundAtoms g (chunks[badIdx]'h) = .error err := by
  intro idx acc badIdx hGo; induction fuel : chunks.size - idx using Nat.strongRecOn generalizing idx acc with
  | ind fuel ih =>
    unfold extractAllChunksGo at hGo
    by_cases h : idx < chunks.size
    · rw [dite_eq_left h] at hGo
      cases hEx : extractSpanBoundAtoms g (chunks[idx]'h) with
      | error err => rw [hEx] at hGo; injection hGo with hEq; subst hEq; exact ⟨h, err, hEx⟩
      | ok atoms => rw [hEx] at hGo; exact ih (chunks.size - (idx + 1)) (by omega) (idx + 1) (acc ++ [atoms]) hGo rfl
    · rw [dite_eq_right h] at hGo; cases hGo
private theorem extractedEdbFacts_unique {g : GrammarSpec} {db : SemanticDatabank} {I₁ I₂ : FactSet}
    (h₁ : ExtractedEdbFacts g db I₁) (h₂ : ExtractedEdbFacts g db I₂) : I₁ = I₂ := by
  obtain ⟨ls₁, hLen₁, hAt₁, rfl⟩ := h₁; obtain ⟨ls₂, hLen₂, hAt₂, rfl⟩ := h₂
  congr 1; apply List.ext_getElem (hLen₁.trans hLen₂.symm)
  intro i hi₁ hi₂; have hC : i < db.chunks.size := by omega
  obtain ⟨a₁, hg₁, he₁⟩ := hAt₁ i hC; obtain ⟨a₂, hg₂, he₂⟩ := hAt₂ i hC
  rw [List.getElem?_eq_getElem hi₁, Option.some.injEq] at hg₁
  rw [List.getElem?_eq_getElem hi₂, Option.some.injEq] at hg₂
  rw [he₁] at he₂; exact hg₁.trans ((Except.ok.inj he₂).trans hg₂.symm)
private theorem extractedEdbFacts_isBase {g : GrammarSpec} {db : SemanticDatabank} {I : FactSet}
    (h : ExtractedEdbFacts g db I) : IsBaseFactSet I = true := by
  obtain ⟨_, _, _, rfl⟩ := h
  simp only [IsBaseFactSet, List.all_eq_true, List.mem_flatMap, List.mem_map]
  rintro a ⟨_, _, b, _, rfl⟩; exact spanAtomToBaseChaseAtom_isBase b
private theorem embedBaseAtom_const_eq (a : Atom Term) (hBase : isBaseAtom a = true) :
    embedBaseAtom Term.const a = a := by
  rcases a with ⟨rel, args⟩; simp only [isBaseAtom, List.all_eq_true] at hBase
  simp only [embedBaseAtom, mapAtom, Atom.mk.injEq, true_and]
  induction args with
  | nil => rfl
  | cons t rest ih =>
    have ht := hBase t (.head _)
    cases t with | skolem _ _ _ => cases ht | const c => exact congrArg (Term.const c :: ·) (ih fun x hx => hBase x (.tail _ hx))
def checkSemanticKgObjPreconditions (o : SemanticKgObj) :
    Except (SemanticKgClause × List Nat) FactSet :=
  if !isBaseAtom o.targetAtom then .error (.nonBaseTargetAtom, [])
  else if !checkKgQueryGuard o.queryPolicy o.rights o.mask o.env then .error (.queryGuardDenied, [])
  else if !WfRuleSet o.tgdRules.toList then .error (.invalidRuleSet, [])
  else match findUnguardedRuleGo o.tgdRules 0 with
  | some idx => .error (.unguardedRule idx, [idx])
  | none =>
    if !WfDatabank o.db then .error (.invalidDatabank, [])
    else if databankCommit256 o.db != o.expectedDbRoot then .error (.databankRootMismatch, [])
    else match extractAllChunksGo o.grammar o.db.chunks 0 [] with
    | .error idx => .error (.chunkParseFailed idx, [idx])
    | .ok atomLists => .ok (atomLists.flatMap fun arr => arr.toList.map spanAtomToBaseChaseAtom)
def checkSemanticKgStep (o : SemanticKgObj) (c : SemanticKgCert) (r : Nat) :
    Option (Judge.Verdict SemanticKgClause) :=
  match checkSemanticKgObjPreconditions o with
  | .error (k, p) => some (.refused k p)
  | .ok edbFacts =>
    match c with
    | .chaseProof fuel =>
      if fuel ≤ r then
        if (runBoundedChaseExec o.tgdRules fuel edbFacts.toArray).toList.contains o.targetAtom then some .ok else none
      else none
    | .countermodel tbl M targetTuple gapCert =>
      if M.entries.size ≤ r then
        if tbl.WF && checkSortedKTableBoolWF M && tableSymsInBounds tbl M &&
           edbFacts.all (checkAtomInTableFast tbl M) && checkGuardedSaturationFast tbl M o.tgdRules &&
           (internAtom tbl o.targetAtom == some targetTuple) && Datalog.verifyGapCert M targetTuple gapCert then
          some (.refused .saturatedCountermodel [])
        else none
      else none
def checkSemanticKg (r : Nat) (o : SemanticKgObj) (c : SemanticKgCert) :
    Judge.Verdict SemanticKgClause :=
  match Judge.deepen (checkSemanticKgStep o c) r with | some v => v | none => .uncovered
private theorem checkObjPreconditions_ok_props {o : SemanticKgObj} {edb : FactSet}
    (hPre : checkSemanticKgObjPreconditions o = .ok edb) :
    WfDatabank o.db = true ∧ databankCommit256 o.db = o.expectedDbRoot ∧
    Obend.Polis.subMask o.queryPolicy.needRights (o.rights &&& o.mask) = true ∧
    Obend.Polis.KleenePred3.accepts (o.queryPolicy.caveat.eval o.env) = true ∧
    WfRuleSet o.tgdRules.toList = true ∧ (∀ r ∈ o.tgdRules.toList, IsGuardedRule r = true) ∧
    isBaseAtom o.targetAtom = true ∧ ExtractedEdbFacts o.grammar o.db edb := by
  unfold checkSemanticKgObjPreconditions at hPre
  cases hBase : isBaseAtom o.targetAtom; · simp [hBase] at hPre
  simp only [hBase, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPre
  cases hGuard : checkKgQueryGuard o.queryPolicy o.rights o.mask o.env; · simp [hGuard] at hPre
  simp only [hGuard, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPre
  cases hWfR : WfRuleSet o.tgdRules.toList; · simp [hWfR] at hPre
  simp only [hWfR, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPre
  cases hUng : findUnguardedRuleGo o.tgdRules 0 with
  | some _ => rw [hUng] at hPre; cases hPre
  | none =>
    rw [hUng] at hPre; cases hDb : WfDatabank o.db; · simp [hDb] at hPre
    simp only [hDb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPre
    cases hRoot : (databankCommit256 o.db != o.expectedDbRoot)
    · simp only [hRoot, Bool.false_eq_true, ↓reduceIte] at hPre
      cases hEx : extractAllChunksGo o.grammar o.db.chunks 0 [] with
      | error _ => rw [hEx] at hPre; cases hPre
      | ok atomLists =>
        rw [hEx, Except.ok.injEq] at hPre; subst hPre
        obtain ⟨hSub, hAcc⟩ := Bool.and_eq_true_iff.mp hGuard
        obtain ⟨hLen, hAt⟩ := extractAllChunksGo_ok_le o.grammar o.db.chunks 0 [] atomLists
          (Nat.zero_le _) rfl (fun _ hj => by omega) hEx
        exact ⟨rfl, bne_eq_false_iff_eq.mp hRoot, hSub, hAcc, rfl, fun r hr => by
          obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hr)
          exact findUnguardedRuleGo_none o.tgdRules 0 hUng j hj (Nat.zero_le _),
          rfl, ⟨atomLists, hLen, hAt, rfl⟩⟩
    · simp [hRoot] at hPre
private theorem checkObjPreconditions_err_refutes {o : SemanticKgObj} {k : SemanticKgClause}
    {p : List Nat} (hErr : checkSemanticKgObjPreconditions o = .error (k, p)) :
    ∀ c', ¬ SemanticKgMeaning o c' := by
  intro c' hM
  obtain ⟨hDb, hRoot, hSub, hAcc, hWfR, hAllG, hBase, ⟨I, ⟨ls, hLen, hAt, _⟩, _⟩⟩ := hM
  have hGuard : checkKgQueryGuard o.queryPolicy o.rights o.mask o.env = true := Bool.and_eq_true_iff.mpr ⟨hSub, hAcc⟩
  unfold checkSemanticKgObjPreconditions at hErr
  simp only [hBase, hGuard, hWfR, hDb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hErr
  cases hUng : findUnguardedRuleGo o.tgdRules 0 with
  | some idx =>
    obtain ⟨hIdx, hFalse⟩ := findUnguardedRuleGo_some o.tgdRules 0 idx hUng
    rw [hAllG (o.tgdRules[idx]'hIdx) (Array.getElem_mem_toList hIdx)] at hFalse; cases hFalse
  | none =>
    rw [hUng] at hErr; simp only [bne_eq_false_iff_eq.mpr hRoot, Bool.false_eq_true, ↓reduceIte] at hErr
    cases hEx : extractAllChunksGo o.grammar o.db.chunks 0 [] with
    | ok _ => rw [hEx] at hErr; cases hErr
    | error badIdx =>
      obtain ⟨hBad, _, hFail⟩ := extractAllChunksGo_err o.grammar o.db.chunks 0 [] badIdx hEx
      obtain ⟨_, _, hOk⟩ := hAt badIdx hBad; rw [hOk] at hFail; cases hFail

/-- **Non-Tautological `Obend.Judge` Instance (`semanticKgJudge`)**. -/
instance semanticKgJudge : Obend.Judge SemanticKgObj SemanticKgCert where
  Clause := SemanticKgClause
  Meaning := SemanticKgMeaning
  check := checkSemanticKg
  refutes := fun _ => true
  Fragment := SemanticKgFragment
  sound := by
    intro r o c hOk; unfold checkSemanticKg at hOk
    cases hD : Judge.deepen (checkSemanticKgStep o c) r with
    | none => rw [hD] at hOk; cases hOk
    | some v =>
      rw [hD] at hOk; subst hOk; obtain ⟨i, _, hi⟩ := Judge.deepen_some (checkSemanticKgStep o c) hD
      unfold checkSemanticKgStep at hi
      cases hPre : checkSemanticKgObjPreconditions o with
      | error _ => rw [hPre] at hi; cases hi
      | ok edb =>
        rw [hPre] at hi; obtain ⟨hDb, hRoot, hSub, hAcc, hWfR, hAllG, hBase, hEx⟩ := checkObjPreconditions_ok_props hPre
        cases c with
        | countermodel _ _ _ _ => dsimp only at hi; split at hi <;> (try split at hi) <;> cases hi
        | chaseProof fuel =>
          dsimp only at hi; split at hi
          · split at hi
            · rename_i hCont; have hMem := List.contains_iff_mem.mp hCont
              rw [SkolemChaseCore.runBoundedChaseExec_eq_spec] at hMem
              refine ⟨hDb, hRoot, hSub, hAcc, hWfR, hAllG, hBase, ⟨edb, hEx, fun N cw hIinN hNWit => ?_⟩⟩
              have hBaseI := extractedEdbFacts_isBase hEx
              have hIinN' : ∀ a ∈ edb, embedBaseAtom Term.const a ∈ N := fun a ha =>
                (embedBaseAtom_const_eq a ((List.all_eq_true.mp hBaseI) a ha)).symm ▸ hIinN a ha
              have hMapped := SkolemChaseCore.runBoundedChase_homomorphism Term.const
                o.tgdRules.toList fuel edb N cw hBaseI hIinN' hNWit o.targetAtom hMem
              rwa [SkolemChaseCore.mapAtom_evalSkolemHom_eq_embedBase Term.const cw o.targetAtom hBase,
                  embedBaseAtom_const_eq o.targetAtom hBase] at hMapped
            · cases hi
          · cases hi
  refuted := by
    intro r o c k p hRef _ c'; unfold checkSemanticKg at hRef
    cases hD : Judge.deepen (checkSemanticKgStep o c) r with
    | none => rw [hD] at hRef; cases hRef
    | some v =>
      rw [hD] at hRef; subst hRef; obtain ⟨i, _, hi⟩ := Judge.deepen_some (checkSemanticKgStep o c) hD
      unfold checkSemanticKgStep at hi
      cases hPre : checkSemanticKgObjPreconditions o with
      | error _ => exact checkObjPreconditions_err_refutes hPre c'
      | ok edb =>
        rw [hPre] at hi; obtain ⟨_, _, _, _, hWfR, hAllG, _, hEx⟩ := checkObjPreconditions_ok_props hPre
        cases c with
        | chaseProof _ => dsimp only at hi; split at hi <;> (try split at hi) <;> cases hi
        | countermodel tbl M targetTuple gapCert =>
          dsimp only at hi; split at hi
          · split at hi
            · rename_i hCm; simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hCm
              obtain ⟨⟨⟨⟨⟨⟨hTbl, hMWfB⟩, hBounds⟩, hCov⟩, hSatFast⟩, hIntern⟩, hGap⟩ := hCm
              have hMWf := (checkSortedKTableBoolWF_iff M).mp hMWfB
              have hAllGArr : o.tgdRules.all IsGuardedRule = true :=
                Array.all_eq_true_iff_forall_mem.mpr fun r hr => hAllG r (Array.mem_toList_iff.mpr hr)
              have hSatSpec : allRulesSatisfied o.tgdRules.toList (decodeSortedFactSet tbl M) = true := by
                rw [← checkGuardedSaturationFast_eq_spec tbl M o.tgdRules hTbl hMWf hBounds hAllGArr]; exact hSatFast
              have hGapZero := Datalog.sortedGapNonMembership_sound M hMWf targetTuple gapCert hGap
              have hNotMem : o.targetAtom ∉ decodeSortedFactSet tbl M := fun hMem => by
                have hChk := (checkAtomInTableFast_eq_true_iff hTbl hMWf o.targetAtom).mpr hMem
                simp only [checkAtomInTableFast, hIntern, hGapZero, ProvenanceSemiringOps.zero] at hChk; cases hChk
              intro hMean; obtain ⟨_, _, _, _, _, _, _, ⟨I, hExI, hEntails⟩⟩ := hMean
              have hEqI := extractedEdbFacts_unique hExI hEx; subst hEqI
              exact hNotMem (hEntails (decodeSortedFactSet tbl M)
                (chaseWitnessOf o.tgdRules.toList (decodeSortedFactSet tbl M))
                (fun a ha => (checkAtomInTableFast_eq_true_iff hTbl hMWf a).mp (hCov a ha))
                (witnessSatisfiesRules_of_allRulesSatisfied hWfR hSatSpec))
            · cases hi
          · cases hi
  complete := by
    intro o hFrag ⟨c0, hMean⟩
    obtain ⟨_, _, _, _, hWfR, _, _, ⟨I, hExI, ⟨fuel, hSat⟩⟩⟩ := hFrag
    cases hPre : checkSemanticKgObjPreconditions o with
    | error _ => exact False.elim (checkObjPreconditions_err_refutes hPre c0 hMean)
    | ok edb =>
      have hExEdb := (checkObjPreconditions_ok_props hPre).2.2.2.2.2.2.2
      have hEqEdb : edb = I := extractedEdbFacts_unique hExEdb hExI; subst edb
      obtain ⟨_, _, _, _, _, _, _, ⟨I', hExI', hEntails⟩⟩ := hMean
      have hEqI' : I' = I := extractedEdbFacts_unique hExI' hExI; subst I'
      have hTargetIn : o.targetAtom ∈ runBoundedChase o.tgdRules.toList fuel I :=
        hEntails _ (chaseWitnessOf o.tgdRules.toList _) (SkolemChaseCore.subset_runBoundedChase _ _ _)
          (witnessSatisfiesRules_of_allRulesSatisfied hWfR hSat)
      have hStepOk : checkSemanticKgStep o (.chaseProof fuel) fuel = some .ok := by
        unfold checkSemanticKgStep; rw [hPre]
        have hMemExec : o.targetAtom ∈ (runBoundedChaseExec o.tgdRules fuel I.toArray).toList := by
          rw [SkolemChaseCore.runBoundedChaseExec_eq_spec]; exact hTargetIn
        have hCont : (runBoundedChaseExec o.tgdRules fuel I.toArray).toList.contains o.targetAtom = true :=
          List.contains_iff_mem.mpr hMemExec
        simp only [Nat.le_refl, ↓reduceIte, hCont]
      obtain ⟨v, hDeep⟩ := Judge.deepen_isSome (checkSemanticKgStep o (.chaseProof fuel)) hStepOk
      obtain ⟨i, _, hi⟩ := Judge.deepen_some (checkSemanticKgStep o (.chaseProof fuel)) hDeep
      have hvEq : v = .ok := by
        unfold checkSemanticKgStep at hi; rw [hPre] at hi; dsimp only at hi
        split at hi
        · split at hi
          · exact (Option.some.inj hi).symm
          · cases hi
        · cases hi
      subst hvEq; exact ⟨.chaseProof fuel, fuel, by simp [checkSemanticKg, hDeep]⟩
  mono := by
    intro r r' o c hLe hNe; unfold checkSemanticKg at hNe ⊢
    cases hD : Judge.deepen (checkSemanticKgStep o c) r with
    | none => rw [hD] at hNe; exact False.elim (hNe rfl)
    | some _ => rw [Judge.deepen_mono (checkSemanticKgStep o c) hD hLe]

/-- Inhabitedness witness for `SemanticKgFragment` (proving `Fragment` is non-empty and non-vacuous). -/
theorem semanticKgFragment_inhabited (worldRoot : DatabankRoot256) (rights : UInt64) :
    let db : SemanticDatabank := ⟨worldRoot, #[]⟩
    let r : TgdRule := ⟨1, [0], [], [⟨0, [.var 0]⟩], [⟨1, [.var 0]⟩]⟩
    let o : SemanticKgObj := ⟨db, databankCommit256 db, ⟨wellMatchedJsonVpa, ⟨#[]⟩, #[]⟩,
      #[r], ⟨1, [.const 0]⟩, ⟨⟨[]⟩, rights, .const true⟩, rights, rights, #[]⟩
    SemanticKgFragment o := by
  intro db r o
  have hGuard := checkKgQueryGuard_inhabited ⟨[]⟩ rights
  simp only [checkKgQueryGuard, Bool.and_eq_true] at hGuard
  have hWfDb : WfDatabank o.db = true := by simp [WfDatabank, o, db]
  have hWfR : WfRuleSet [r] = true := by decide
  have hG : IsGuardedRule r = true := by decide
  have hBase : isBaseAtom ⟨1, [.const 0]⟩ = true := by decide
  have hSat0 : allRulesSatisfied [r] (runBoundedChase [r] 0 []) = true := by
    simp [runBoundedChase, allRulesSatisfied, ruleSatisfiedSpec, matchPatAtoms, r]
  refine ⟨hWfDb, rfl, hGuard.1, hGuard.2, hWfR,
    fun r' hr' => (List.mem_singleton.mp hr') ▸ hG, hBase,
    ⟨[], ⟨[], rfl, fun i hi => False.elim (Nat.not_lt_zero i hi), rfl⟩, ⟨0, hSat0⟩⟩⟩

/-! ### JSON Wire Codecs & `"semantic-kg@1"` `Obend.Judge.Format` Registration -/
private def decodeAtomJson (j : Json) : Except String (Atom Term) := do
  let rel ← j.getObjValAs? Nat "rel"; let argsArr ← (← j.getObjVal? "args").getArr?
  let args ← argsArr.toList.mapM fun x => return Term.const (← x.getNat?)
  pure { rel, args }
private def decodePatAtomJson (j : Json) : Except String PatAtom := do
  let rel ← j.getObjValAs? Nat "rel"
  let args ← (← (← j.getObjVal? "args").getArr?).toList.mapM fun x => do
    match x.getObjVal? "var" with
    | .ok v => pure (.var (← v.getNat?)) | .error _ => pure (.const (← x.getObjValAs? Nat "const"))
  pure { rel, args }
private def decodeTgdRuleJson (j : Json) : Except String TgdRule := do
  let id ← j.getObjValAs? Nat "id"
  let frontierVars ← (← (← j.getObjVal? "frontierVars").getArr?).toList.mapM (·.getNat?)
  let existVars ← (← (← j.getObjVal? "existVars").getArr?).toList.mapM (·.getNat?)
  let body ← (← (← j.getObjVal? "body").getArr?).toList.mapM decodePatAtomJson
  let head ← (← (← j.getObjVal? "head").getArr?).toList.mapM decodePatAtomJson
  pure { id, frontierVars, existVars, body, head }
private def decodeGroundTupleJson (j : Json) : Except String Datalog.GroundTuple := do
  let rel ← j.getObjValAs? Nat "rel"; let args ← (← (← j.getObjVal? "args").getArr?).mapM (·.getNat?)
  pure { rel, args }
private def boundedField (j : Json) (key : String) (bits : Nat) : Except String Nat := do
  let n ← j.getObjValAs? Nat key
  if n ≥ 2^bits then throw s!"{key} exceeds {bits} bits"
  pure n

private def optionalArray (j : Json) (key : String) : Except String (Array Json) :=
  match j.getObjVal? key with
  | .ok x => x.getArr?
  | .error _ => .ok #[]

private def hexField (j : Json) (key : String) : Except String ByteArray := do
  let value ← j.getObjValAs? String key
  let some bytes := Obend.Codec.Hex.hexByteArrayStrict? value.toUTF8
    | throw s!"{key} requires lowercase hex bytes"
  return bytes

private def decodeChunk (j : Json) : Except String DocChunkEntry := do
  return ⟨← boundedField j "docId" 64, ← boundedField j "byteOffset" 64, ← hexField j "rawBytes",
    BitVec.ofNat 256 (← boundedField j "chunkDigest256" 256)⟩

private def decodeSpanRule (j : Json) : Except String SpanRuleSpec := do
  let some pattern := SymbolicRegex.decRE (← hexField j "slicePattern") | throw "invalid slicePattern"
  let some ban := SymbolicRegex.decRE (← hexField j "banDelimiter") | throw "invalid banDelimiter"
  return ⟨← hexField j "predTag", (← boundedField j "predSym" 32).toUInt32,
    ← j.getObjValAs? Nat "arity", pattern, ban⟩

private def decodeBinding (j : Json) : Except String (Nat × Obend.Polis.KleenePred3) := do
  let i ← j.getObjValAs? Nat "id"
  match ← j.getObjVal? "value" with
  | .null => return (i, .unbound3)
  | .bool b => return (i, if b then .true3 else .false3)
  | _ => throw "binding value requires true, false or null"

deriving instance Lean.FromJson for Obend.Polis.Caveat

private def decodeKgJson (s : String) : Except String SemanticKgObj := do
  let j ← Json.parse s
  let wRoot ← boundedField j "worldLogRoot256" 256
  let eRoot ← boundedField j "expectedDbRoot" 256
  let chunks ← (← optionalArray j "chunks").mapM decodeChunk
  let entries ← (← optionalArray j "entityDict").mapM fun e => do
    return (← hexField e "raw", (← boundedField e "id" 32).toUInt32)
  let spanRules ← (← optionalArray j "spanRules").mapM decodeSpanRule
  let accept ← match j.getObjVal? "structuralAccept" with
    | .ok x => x.getBool? | .error _ => pure true
  let rules ← (← (← j.getObjVal? "tgdRules").getArr?).mapM decodeTgdRuleJson
  let tgt ← decodeAtomJson (← j.getObjVal? "targetAtom")
  let query ← (← optionalArray j "query").mapM decodePatAtomJson
  let need ← boundedField j "needRights" 64
  let cav ← match j.getObjVal? "caveat" with
    | .ok x => Lean.fromJson? x
    | .error _ => pure (Obend.Polis.Caveat.const (← j.getObjValAs? Bool "caveatConst"))
  let rights ← boundedField j "rights" 64
  let mask ← boundedField j "mask" 64
  let bindings ← (← optionalArray j "bindings").mapM decodeBinding
  pure ⟨⟨BitVec.ofNat 256 wRoot, chunks⟩, BitVec.ofNat 256 eRoot,
    ⟨{ wellMatchedJsonVpa with acc := fun _ => accept }, ⟨entries⟩, spanRules⟩, rules, tgt,
    ⟨⟨query.toList⟩, need.toUInt64, cav⟩, rights.toUInt64, mask.toUInt64, bindings⟩

def decodeSemanticKgObj := decodeKgWith decodeKgJson

theorem decode_encode_semanticKgObj (o : SemanticKgObj) :
    decodeSemanticKgObj (encodeSemanticKgObj o) = .ok o := decodeKgWith_encode _ o

def decodeSemanticKgCert (s : String) : Except String SemanticKgCert := do
  if let some fuel := s.toNat? then return .chaseProof fuel
  let j ← Json.parse s; let kind ← j.getObjValAs? String "kind"
  if kind == "chaseProof" then pure (.chaseProof (← j.getObjValAs? Nat "fuel"))
  else if kind == "countermodel" then
    let terms ← (← (← j.getObjVal? "terms").getArr?).mapM fun x => do pure (Term.const (← x.getNat?))
    let entries ← (← (← j.getObjVal? "entries").getArr?).mapM fun ej => do pure (← decodeGroundTupleJson ej, true)
    let targetTuple ← decodeGroundTupleJson (← j.getObjVal? "targetTuple")
    let gKind ← (← j.getObjVal? "gapCert").getObjValAs? String "kind"
    let gapCert ← if gKind == "empty" then pure .emptyTable else if gKind == "belowFirst" then pure .belowFirst
      else if gKind == "aboveLast" then pure .aboveLast
      else if gKind == "adjacent" then pure (.adjacentGap (← (← j.getObjVal? "gapCert").getObjValAs? Nat "index"))
      else throw s!"unknown gapCert kind {gKind}"
    pure (.countermodel ⟨terms⟩ ⟨entries⟩ targetTuple gapCert)
  else throw s!"unknown semantic-kg certificate kind {kind}"
def SemanticKgClause.describe : SemanticKgClause → String
  | .nonBaseTargetAtom => "target atom contains non-base Skolem term"
  | .queryGuardDenied => "evidenced capability guard or caveat denied query"
  | .invalidRuleSet => "TGD rule set failed well-formedness or rule-ID uniqueness"
  | .unguardedRule i => s!"TGD rule at index {i} is not guarded"
  | .invalidDatabank => "databank failed chunk width bounds or digest integrity"
  | .databankRootMismatch => "databank 256-bit commitment does not match expectedDbRoot"
  | .chunkParseFailed i => s!"databank chunk {i} failed Stage-2 span-bound JSON/VPA extraction"
  | .saturatedCountermodel => "verified finite guarded model contains all EDB facts and omits target atom"
def explainSemanticKg (grade : Nat) (objWire certWire : String) : String :=
  match decodeSemanticKgObj objWire, decodeSemanticKgCert certWire with
  | .error e, _ => s!"object: {e}" | _, .error e => s!"certificate: {e}"
  | .ok o, .ok c => match checkSemanticKg grade o c with
    | .ok => "accepted" | .uncovered => "uncovered within grade" | .refused k _ => k.describe
def badSemanticKgObj : SemanticKgObj :=
  ⟨⟨0, #[]⟩, 0, ⟨wellMatchedJsonVpa, ⟨#[]⟩, #[]⟩, #[], ⟨0, [.skolem 0 0 []]⟩, ⟨⟨[]⟩, 0, .const true⟩, 0, 0, #[]⟩
def badSemanticKgCert : SemanticKgCert := .chaseProof 0
theorem badSemanticKg_refused (r : Nat) :
    semanticKgJudge.check r badSemanticKgObj badSemanticKgCert = .refused .nonBaseTargetAtom [] := by
  have hStep0 : checkSemanticKgStep badSemanticKgObj badSemanticKgCert 0 = some (.refused .nonBaseTargetAtom []) := by
    simp [checkSemanticKgStep, checkSemanticKgObjPreconditions, badSemanticKgObj, isBaseAtom, isBaseTerm]
  obtain ⟨b, hb⟩ := Judge.deepen_isSome (checkSemanticKgStep badSemanticKgObj badSemanticKgCert) hStep0
  obtain ⟨i, hi, hfi⟩ := Judge.deepen_some (checkSemanticKgStep badSemanticKgObj badSemanticKgCert) hb
  have hi0 : i = 0 := Nat.le_zero.mp hi; subst hi0; rw [hStep0, Option.some.injEq] at hfi; subst hfi
  have h0 : semanticKgJudge.check 0 badSemanticKgObj badSemanticKgCert = .refused .nonBaseTargetAtom [] := by
    change checkSemanticKg 0 badSemanticKgObj badSemanticKgCert = _; simp [checkSemanticKg, hb]
  exact (semanticKgJudge.mono (Nat.zero_le r) (by rw [h0]; intro hc; cases hc)).trans h0
@[expose] def semanticKgFormat : Obend.Judge.Format where
  name := "semantic-kg"; version := "1"; Obj := SemanticKgObj; Cert := SemanticKgCert
  judge := semanticKgJudge; decodeObj := decodeSemanticKgObj; decodeCert := decodeSemanticKgCert
  trust := .kernel; regime := .decidable; bad := (badSemanticKgObj, badSemanticKgCert); badGrade := 0
  bad_refused := ⟨.nonBaseTargetAtom, [], badSemanticKg_refused 0⟩; explain := explainSemanticKg

private theorem check_edb_single (o : SemanticKgObj)
    (hPre : checkSemanticKgObjPreconditions o = .ok [o.targetAtom]) :
    semanticKgJudge.check 0 o (.chaseProof 0) = .ok := by
  change (match checkSemanticKgStep o (.chaseProof 0) 0 with
    | some v => v | none => .uncovered) = .ok
  simp [checkSemanticKgStep, hPre, runBoundedChaseExec]

/-- A singleton database answers its extracted fact at grade zero under the object guards. -/
theorem check_single_extraction (o : SemanticKgObj) (c : DocChunkEntry) (a : SpanBoundAtom)
    (hc : o.db.chunks = #[c]) (hr : o.tgdRules = #[])
    (hroot : o.expectedDbRoot = databankCommit256 o.db) (hw : WfDatabank o.db = true)
    (hb : isBaseAtom o.targetAtom = true)
    (hg : checkKgQueryGuard o.queryPolicy o.rights o.mask o.env = true)
    (he : extractSpanBoundAtoms o.grammar c = .ok #[a]) (ha : spanAtomToBaseChaseAtom a = o.targetAtom) :
    semanticKgJudge.check 0 o (.chaseProof 0) = .ok := by
  apply check_edb_single
  have h0 : 0 < (#[c] : Array _).size := Nat.zero_lt_succ 0
  have h1 : ¬1 < (#[c] : Array _).size := Nat.lt_irrefl 1
  have hp : extractAllChunksGo o.grammar #[c] 0 [] = .ok [#[a]] := by
    rw [extractAllChunksGo, dite_eq_left h0]
    change (match extractSpanBoundAtoms o.grammar c with
      | .ok xs => extractAllChunksGo o.grammar #[c] 1 ([] ++ [xs])
      | .error _ => .error 0) = _
    rw [he]
    change extractAllChunksGo o.grammar #[c] 1 [#[a]] = _
    rw [extractAllChunksGo, dite_eq_right h1]
  have hguarded : findUnguardedRuleGo #[] 0 = none := by rw [findUnguardedRuleGo]; rfl
  have hrule : WfRuleSet [] = true := rfl
  simp [checkSemanticKgObjPreconditions, hr, hb, hg, hrule, hguarded, hw, hroot, hc, hp, ha]


end Obend.SemanticKG
end
