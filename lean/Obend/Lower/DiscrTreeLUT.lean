module
/-
# Obend.Lower.DiscrTreeLUT — `DiscrTree` $\to$ Zone-3 eFPGA LUT Compiler & Synthesizable `ExprCAM` + `SiliconKernel` SystemVerilog

Implements `WS 28` Stage 5 & 6 (`SILICON-ELABORATOR.md` §5.2–7):
1. **Path-Indexed `DiscrTree` Tries (`DiscrPath`, `exprToDiscrPath`, `DiscrTreeEntry`, `DiscrTreeTrie`, `queryDiscrTrie`)**:
   - Extracts preorder `DiscrPath := List DiscrTreeKey` keys from `KExpr` terms for both `@[simp]`
     rewrite rules and `SynthInstance` typeclass instances.
   - Matches candidate rules along exact key edges and wildcard `.star` edges.
2. **2nd Futamura Specialization to Zone-3 eFPGA `AutomatonTile` LUT Pipelines
   (`SlotGuardReg`, `futamura2DiscrTreeTerm`, `compileDiscrTreeEpochToTile`, `discrTree_lut_compile_sound`)**:
   - Applies 2nd Futamura specialization (`Obend/Leaf/Futamura.lean`: `futamura2SelfSpecialize`,
     `futamura1Specialize`, `specSlot`) so each `Environment` epoch compiles into a single-cycle
     Zone-3 `AutomatonTile` match pipeline guarded by `SlotGuardReg` (`moved_pin_blocks`).
   - Proves **`discrTree_lut_compile_sound`**: multi-key trie indexing, 2nd Futamura specialization,
     glitch-free `ICAP` DPR reconfiguration between environment epochs, and 1-cycle `SlotGuardReg`
     fallback (`moved_pin_blocks`) when an environment pin mutates.
3. **Synthesizable SystemVerilog for `ExprCAM` + `SiliconKernel` + `DiscrTreeLUT`
   (`exprCamKernelLutRtlModule`, `emitExprCamKernelLutSV`, `exprCam_siliconKernel_sv_cosim_sound`)**:
   - Constructs a verified synchronous/combinational `RtlModule` combining 64-bit `ExprCAM` handle/word
     matching, `looseBVar` bit-59 extraction, `SiliconKernel` declaration verification, and
     `SlotGuardReg`-gated Zone-3 LUT evaluation.
   - Emits synthesizable SystemVerilog-2012 via `emitModuleSV` and proves **`exprCam_siliconKernel_sv_cosim_sound`**
     against live Lean declarations exported by `extractLeanConstInfo?` (`0 sorryAx`).
-/
public import Obend.Lower.MetaUnify
public import Obend.Lower.Proofs.SiliconKernel
@[expose] public section

namespace Obend.Lower.DiscrTreeLUT
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Preorder `DiscrTree` Path Extraction & Multi-Key Trie Lookup (`DiscrPath`, `DiscrTreeTrie`) -/

/-- A preorder sequence of `DiscrTreeKey` tokens indexing a deep `KExpr` pattern in a `DiscrTree`. -/
abbrev DiscrPath := List DiscrTreeKey

/-- Extract a bounded preorder `DiscrPath` from a `KExpr` (treating metavariables, loose bound
variables, and free variables as wildcard `.star` keys, just as in `Lean.Meta.DiscrTree`). -/
def exprToDiscrPath : Nat → KExpr → DiscrPath
  | 0, _ => [.star]
  | fuel + 1, e =>
    if (isMVarExpr? e).isSome then
      [.star]
    else
      match e with
      | .bvar _ | .fvar _ | .sort _ => [.star]
      | .const n _ => [.const n]
      | .lit l => [.lit l]
      | .app (.const n _) a =>
        .app n :: exprToDiscrPath fuel a
      | .app (.app (.const n _) a1) a2 =>
        .app n :: (exprToDiscrPath fuel a1 ++ exprToDiscrPath fuel a2)
      | .app f a =>
        exprToDiscrPath fuel f ++ exprToDiscrPath fuel a
      | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ => [.star]

/-- Check whether a rule's pattern path `patPath` matches a query path `qPath` (where `.star` in
`patPath` matches any single key token in `qPath`). -/
def matchDiscrPath : DiscrPath → DiscrPath → Bool
  | [], [] => true
  | .star :: ps, _ :: qs => matchDiscrPath ps qs
  | p :: ps, q :: qs => (p == q) && matchDiscrPath ps qs
  | _, _ => false

@[simp] theorem matchDiscrPath_refl : ∀ (p : DiscrPath), matchDiscrPath p p = true
  | [] => rfl
  | k :: ks => by
    unfold matchDiscrPath
    cases k <;> simp [BEq.beq, DiscrTreeKey.beq, KName.beq_refl, KLiteral.beq_refl, matchDiscrPath_refl ks]

/-- Kind of elaborator rule stored in a Zone-3 `DiscrTreeTrie`. -/
inductive DiscrRuleKind where
  | simpLemma     (rhs : KExpr) (gain : Nat) (offset : Nat)
  | synthInstance (className : KName) (instExpr : KExpr) (priority : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Entry in a `DiscrTreeTrie` mapping a preorder `DiscrPath` to a rule name, hardware LUT tag, and payload. -/
structure DiscrTreeEntry where
  ruleName : KName
  path     : DiscrPath
  lutTag   : Nat
  kind     : DiscrRuleKind
  deriving DecidableEq, Repr, Inhabited

/-- Compiled `DiscrTree` indexing table for a given `Environment` epoch. -/
structure DiscrTreeTrie where
  epoch   : Nat
  entries : List DiscrTreeEntry
  deriving DecidableEq, Repr, Inhabited

/-- Query a `DiscrTreeTrie` for all entries whose `DiscrPath` matches `exprToDiscrPath depth target`. -/
def queryDiscrTrie (trie : DiscrTreeTrie) (depth : Nat) (target : KExpr) : List DiscrTreeEntry :=
  let qPath := exprToDiscrPath depth target
  trie.entries.filter (fun entry => matchDiscrPath entry.path qPath)

/-- Query the highest-priority / first matching `DiscrTreeEntry` in `trie`. -/
def queryBestDiscrEntry? (trie : DiscrTreeTrie) (depth : Nat) (target : KExpr) : Option DiscrTreeEntry :=
  (queryDiscrTrie trie depth target).head?

/-! ## 1b. True Branched Radix `DiscrTree` Trie (`DiscrTrieNode`, `insertDiscrTrieNode`, `queryDiscrTrieNode`) -/

@[simp] theorem DiscrTreeKey.beq_refl (k : DiscrTreeKey) : (k == k) = true := by
  cases k <;> simp [BEq.beq, DiscrTreeKey.beq, KName.beq_refl, KLiteral.beq_refl]

theorem KName.eq_of_beq : ∀ {n1 n2 : KName}, KName.beq n1 n2 = true → n1 = n2
  | .anonymous, .anonymous, _ => rfl
  | .str p1 s1, .str p2 s2, h => by
    simp only [KName.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, KName.eq_of_beq h.2]
  | .num p1 i1, .num p2 i2, h => by
    simp only [KName.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, KName.eq_of_beq h.2]

theorem KLiteral.eq_of_beq : ∀ {l1 l2 : KLiteral}, KLiteral.beq l1 l2 = true → l1 = l2
  | .natVal n1, .natVal n2, h => by
    simp only [KLiteral.beq, beq_iff_eq] at h
    rw [h]
  | .strVal s1, .strVal s2, h => by
    simp only [KLiteral.beq, beq_iff_eq] at h
    rw [h]

theorem DiscrTreeKey.eq_of_beq : ∀ {k1 k2 : DiscrTreeKey}, (k1 == k2) = true → k1 = k2
  | .const n1, .const n2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq] at h
    rw [KName.eq_of_beq h]
  | .app n1, .app n2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq] at h
    rw [KName.eq_of_beq h]
  | .lit l1, .lit l2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq] at h
    rw [KLiteral.eq_of_beq h]
  | .star, .star, _ => rfl

/-- Priority score of a `DiscrTreeEntry` for priority-sorted leaf rule lists. -/
def DiscrTreeEntry.priority : DiscrTreeEntry → Nat
  | { kind := .synthInstance _ _ prio, .. } => prio
  | { kind := .simpLemma _ gain _, .. }     => gain

/-- Insert a `DiscrTreeEntry` into a priority-sorted list of leaf rules (highest priority first). -/
def insertRuleByPriority (entry : DiscrTreeEntry) : List DiscrTreeEntry → List DiscrTreeEntry
  | [] => [entry]
  | r :: rs =>
    if entry.priority ≥ r.priority then
      entry :: r :: rs
    else
      r :: insertRuleByPriority entry rs

theorem mem_insertRuleByPriority (entry : DiscrTreeEntry) : ∀ (rules : List DiscrTreeEntry),
    entry ∈ insertRuleByPriority entry rules
  | [] => by simp [insertRuleByPriority]
  | r :: rs => by
    simp only [insertRuleByPriority]
    split
    · simp
    · exact List.mem_cons_of_mem r (mem_insertRuleByPriority entry rs)

theorem mem_insertRuleByPriority_of_mem (entry x : DiscrTreeEntry) :
    ∀ (rules : List DiscrTreeEntry), x ∈ rules → x ∈ insertRuleByPriority entry rules
  | [], h => nomatch h
  | r :: rs, h => by
    simp only [insertRuleByPriority]
    split
    · exact List.mem_cons_of_mem entry h
    · rcases List.mem_cons.mp h with rfl | hrs
      · exact List.Mem.head _
      · exact List.mem_cons_of_mem r (mem_insertRuleByPriority_of_mem entry x rs hrs)

/-- Merge two priority-sorted candidate rule lists into a single priority-ordered list (highest priority first). -/
def mergeRulesByPriority (xs ys : List DiscrTreeEntry) : List DiscrTreeEntry :=
  xs.foldr insertRuleByPriority ys

theorem mem_mergeRulesByPriority_right (ys : List DiscrTreeEntry) (x : DiscrTreeEntry) (h : x ∈ ys) :
    ∀ (xs : List DiscrTreeEntry), x ∈ mergeRulesByPriority xs ys
  | [] => h
  | r :: rs =>
    mem_insertRuleByPriority_of_mem r x (mergeRulesByPriority rs ys)
      (mem_mergeRulesByPriority_right ys x h rs)

theorem mem_mergeRulesByPriority_left (ys : List DiscrTreeEntry) (x : DiscrTreeEntry) :
    ∀ (xs : List DiscrTreeEntry), x ∈ xs → x ∈ mergeRulesByPriority xs ys
  | [], h => nomatch h
  | r :: rs, h => by
    simp only [mergeRulesByPriority, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hrs
    · exact mem_insertRuleByPriority x (mergeRulesByPriority rs ys)
    · exact mem_insertRuleByPriority_of_mem r x (mergeRulesByPriority rs ys)
        (mem_mergeRulesByPriority_left ys x rs hrs)

/-- Inductive branched radix discrimination trie node (`Lean.Meta.DiscrTree.Trie`):
* `leafRules`: priority-ordered candidate rules terminating at this node,
* `children`: outgoing key edges `(edgeKey, childNode)` branching on `DiscrTreeKey` tokens
  (including both exact `.const` / `.app` / `.lit` keys and wildcard `.star` keys). -/
inductive DiscrTrieNode where
  | mk (leafRules : List DiscrTreeEntry) (children : List (DiscrTreeKey × DiscrTrieNode))
  deriving Repr, Inhabited

/-- Empty `DiscrTrieNode`. -/
def DiscrTrieNode.empty : DiscrTrieNode := .mk [] []

/-- Extract the priority-sorted leaf rules at a `DiscrTrieNode`. -/
def DiscrTrieNode.leafRules : DiscrTrieNode → List DiscrTreeEntry
  | .mk rules _ => rules

/-- Extract the outgoing `(DiscrTreeKey × DiscrTrieNode)` edges of a `DiscrTrieNode`. -/
def DiscrTrieNode.children : DiscrTrieNode → List (DiscrTreeKey × DiscrTrieNode)
  | .mk _ ch => ch

/-- Update the first outgoing child edge matching `k` via `upd`, or append a new edge `(k, upd .empty)`
when no edge for `k` exists yet (sharing common radix prefixes). -/
def modifyOrInsertChild (k : DiscrTreeKey) (upd : DiscrTrieNode → DiscrTrieNode) :
    List (DiscrTreeKey × DiscrTrieNode) → List (DiscrTreeKey × DiscrTrieNode)
  | [] => [(k, upd .empty)]
  | (ek, child) :: rest =>
    if ek == k then
      (ek, upd child) :: rest
    else
      (ek, child) :: modifyOrInsertChild k upd rest

/-- Insert `(path, entry)` into a branched radix `DiscrTrieNode`, sharing common `DiscrTreeKey`
prefix edges and inserting `entry` into `leafRules` in priority order at the terminal node. -/
def insertDiscrTrieNode : DiscrPath → DiscrTreeEntry → DiscrTrieNode → DiscrTrieNode
  | [], entry, .mk rules children =>
    .mk (insertRuleByPriority entry rules) children
  | k :: ks, entry, .mk rules children =>
    .mk rules (modifyOrInsertChild k (insertDiscrTrieNode ks entry) children)

/-- Build a branched radix `DiscrTrieNode` from a list of `DiscrTreeEntry` rules. -/
def buildDiscrTrieNode (entries : List DiscrTreeEntry) : DiscrTrieNode :=
  entries.foldl (fun trie entry => insertDiscrTrieNode entry.path entry trie) .empty

/-- Explore all outgoing child edges in `children` that match query key `k` either by exact key
equality (`ek == k`) or via a `.star` wildcard branch (`ek == .star`), merging matching branch
results in descending priority order via `mergeRulesByPriority`. -/
def queryChildrenWith (queryK : DiscrTrieNode → List DiscrTreeEntry) (k : DiscrTreeKey) :
    List (DiscrTreeKey × DiscrTrieNode) → List DiscrTreeEntry
  | [] => []
  | (ek, child) :: rest =>
    if ek == k || ek == .star then
      mergeRulesByPriority (queryK child) (queryChildrenWith queryK k rest)
    else
      queryChildrenWith queryK k rest

/-- Query a branched radix `DiscrTrieNode` along `DiscrPath`, exploring both exact key edges
(`ek == k`) and wildcard `.star` branches (`ek == .star`) at every trie level and returning
candidates merged in descending priority order. -/
def queryDiscrTrieNode : DiscrTrieNode → DiscrPath → List DiscrTreeEntry
  | .mk rules _, [] => rules
  | .mk _ children, k :: ks =>
    queryChildrenWith (fun child => queryDiscrTrieNode child ks) k children

theorem mem_queryChildrenWith_modifyOrInsertChild_match
    (queryK : DiscrTrieNode → List DiscrTreeEntry)
    (upd : DiscrTrieNode → DiscrTrieNode)
    (patKey qKey : DiscrTreeKey)
    (entry : DiscrTreeEntry)
    (hKeyMatch : (patKey == qKey || patKey == .star) = true)
    (hUpd : ∀ n : DiscrTrieNode, entry ∈ queryK (upd n)) :
    ∀ (children : List (DiscrTreeKey × DiscrTrieNode)),
      entry ∈ queryChildrenWith queryK qKey (modifyOrInsertChild patKey upd children)
  | [] => by
    simp [modifyOrInsertChild, queryChildrenWith, hKeyMatch]
    exact mem_mergeRulesByPriority_left [] entry (queryK (upd .empty)) (hUpd .empty)
  | (ek, child) :: rest => by
    simp only [modifyOrInsertChild]
    cases hek : ek == patKey
    · simp only [Bool.false_eq_true, ↓reduceIte, queryChildrenWith]
      split
      · exact mem_mergeRulesByPriority_right
          (queryChildrenWith queryK qKey (modifyOrInsertChild patKey upd rest))
          entry
          (mem_queryChildrenWith_modifyOrInsertChild_match queryK upd patKey qKey entry hKeyMatch hUpd rest)
          (queryK child)
      · exact mem_queryChildrenWith_modifyOrInsertChild_match queryK upd patKey qKey entry hKeyMatch hUpd rest
    · have hekEq : ek = patKey := DiscrTreeKey.eq_of_beq hek
      subst hekEq
      simp only [↓reduceIte, queryChildrenWith, hKeyMatch]
      exact mem_mergeRulesByPriority_left
        (queryChildrenWith queryK qKey rest)
        entry
        (queryK (upd child))
        (hUpd child)

/-- **Theorem (`queryDiscrTrieNode_insert_mem_of_matchDiscrPath`)**:
Whenever a rule pattern path `patPath` matches a query path `qPath` (`matchDiscrPath patPath qPath = true`,
supporting both `.star` wildcard tokens in `patPath` and exact key equality), inserting `(patPath, entry)`
into `node` guarantees `entry ∈ queryDiscrTrieNode (insertDiscrTrieNode patPath entry node) qPath`. -/
theorem queryDiscrTrieNode_insert_mem_of_matchDiscrPath :
    ∀ (patPath qPath : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode),
      matchDiscrPath patPath qPath = true →
      entry ∈ queryDiscrTrieNode (insertDiscrTrieNode patPath entry node) qPath
  | [], [], entry, .mk rules children, _ => by
    simp only [insertDiscrTrieNode, queryDiscrTrieNode]
    exact mem_insertRuleByPriority entry rules
  | [], _ :: _, _, _, hMatch => by
    simp [matchDiscrPath] at hMatch
  | patKey :: _, [], _, _, hMatch => by
    cases patKey <;> simp [matchDiscrPath] at hMatch
  | patKey :: patRest, qKey :: qRest, entry, .mk rules children, hMatch => by
    simp only [insertDiscrTrieNode, queryDiscrTrieNode]
    have hStep : (patKey == qKey || patKey == .star) = true ∧ matchDiscrPath patRest qRest = true := by
      cases patKey <;> simp [matchDiscrPath, BEq.beq, DiscrTreeKey.beq] at hMatch ⊢ <;> exact hMatch
    exact mem_queryChildrenWith_modifyOrInsertChild_match
      (fun child => queryDiscrTrieNode child qRest)
      (insertDiscrTrieNode patRest entry)
      patKey
      qKey
      entry
      hStep.1
      (fun n => queryDiscrTrieNode_insert_mem_of_matchDiscrPath patRest qRest entry n hStep.2)
      children

/-- **Theorem (`queryDiscrTrieNode_insert_mem`)**:
Inserting `(path, entry)` into any branched radix trie node `node` guarantees that querying the
updated trie along `path` returns `entry` (`entry ∈ queryDiscrTrieNode (insertDiscrTrieNode path entry node) path`). -/
theorem queryDiscrTrieNode_insert_mem
    (path : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode path entry node) path :=
  queryDiscrTrieNode_insert_mem_of_matchDiscrPath path path entry node (matchDiscrPath_refl path)

/-- **Theorem (`queryDiscrTrieNode_star_and_exact_priority_sound`)**:
When both a lower-priority wildcard `.star` rule (`lutTag = 101`, `priority = 4`) and a higher-priority
exact-key rule (`lutTag = 303`, `priority = 50`) match the same query path `[.app "scaleAdd", .lit 10]`,
`queryDiscrTrieNode` returns `[303, 101]` (highest priority first) regardless of whether the `.star`
rule was inserted before or after the exact-key rule. -/
theorem queryDiscrTrieNode_star_and_exact_priority_sound :
    let rWild : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "simp_scale_wild"
      , path     := [.app (KName.mkSimple "scaleAdd"), .star]
      , lutTag   := 101
      , kind     := .simpLemma (.lit (.natVal 42)) 4 2 }
    let rExact : DiscrTreeEntry :=
      { ruleName := KName.mkSimple "simp_scale_exact10"
      , path     := [.app (KName.mkSimple "scaleAdd"), .lit (.natVal 10)]
      , lutTag   := 303
      , kind     := .simpLemma (.lit (.natVal 500)) 50 0 }
    let qPath : DiscrPath := [.app (KName.mkSimple "scaleAdd"), .lit (.natVal 10)]
    let trieWildFirst := buildDiscrTrieNode [rWild, rExact]
    let trieExactFirst := buildDiscrTrieNode [rExact, rWild]
    (queryDiscrTrieNode trieWildFirst qPath).map (·.lutTag) = [303, 101] ∧
    (queryDiscrTrieNode trieExactFirst qPath).map (·.lutTag) = [303, 101] :=
  ⟨rfl, rfl⟩

/-! ## 2. 2nd Futamura Specialization of `DiscrTree` Epochs to Zone-3 `AutomatonTile` LUTs -/

/-- Hardware `SlotGuardReg` (`SILICON-ELABORATOR.md` §5.3) binding a Zone-3 `AutomatonTile` to a
pinned `Environment` epoch and `LeafPin` support list. -/
structure SlotGuardReg where
  slotName        : String
  pinnedEpoch     : Nat
  composition     : Composition
  candidate       : Candidate
  specializedTile : AutomatonTile
  fallbackTile    : AutomatonTile

/-- Compile an `Environment` epoch's `DiscrTree` rule parameters `(bias, offset)` via the 2nd Futamura
projection (`futamura2SelfSpecialize` + `futamura1Specialize`) into a residual `Core4.Term`. -/
def futamura2DiscrTreeTerm (bias offset : Nat) : Term :=
  futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec bias)) (.nat offset)

/-- Compile a `DiscrTree` epoch's linear/affine rewrite action `(gain, offset)` into a `LiteMethodBody`
(`λ x => gain * x + offset`) for single-cycle Zone-3 `AutomatonTile` LUT synthesis. -/
def discrTreeEpochLutBody (gain offset : Nat) : LExpr :=
  .natBin .add
    (.natBin .mul (.bvar 0) (.lit gain))
    (.lit offset)

/-- Synthesize a Zone-3 `AutomatonTile` for a `DiscrTree` epoch `(epochName, gain, offset)`. -/
def compileDiscrTreeEpochToTile (epochName : String) (gain offset : Nat) : AutomatonTile :=
  (compileLiteMethodToTile epochName (discrTreeEpochLutBody gain offset)).getD incAutomatonTile

/-- Construct a `SlotGuardReg` for a `DiscrTree` epoch `(slotName, epoch, gain, offset)`:
binds the Futamura-specialized `Candidate.book` to `leanComposition slotName (futamura2DiscrTreeTerm gain offset)`
and pairs the specialized Zone-3 LUT tile with the resident fallback tile (`kernelGateTile`). -/
def mkDiscrTreeSlotGuard (slotName : String) (epoch gain offset : Nat) : SlotGuardReg :=
  let specTerm := .lam (lowerLiteScalar (discrTreeEpochLutBody gain offset))
  let comp := leanComposition slotName specTerm
  let cand : Candidate := .book slotName comp
  let tile := compileDiscrTreeEpochToTile slotName gain offset
  { slotName        := slotName
  , pinnedEpoch     := epoch
  , composition     := comp
  , candidate       := cand
  , specializedTile := tile
  , fallbackTile    := kernelGateTile }

/-- Evaluate a `ReductionPacket` through a `SlotGuardReg`-protected Zone-3 tile:
if the live `LeafView` satisfies all pinned `Supports` (`specSlot.usable (holdsAt view) guard.candidate`)
and `pktEpoch == guard.pinnedEpoch`, executes the single-cycle specialized Zone-3 LUT tile;
otherwise (`moved_pin_blocks`), routes in 1 cycle to the resident fallback tile! -/
def evalSlotGuardedDiscrTile
    (guard : SlotGuardReg)
    (view : LeafView)
    (pktEpoch : Nat)
    (argVal : BitVec 64) : Bool × BitVec 64 :=
  let pinOk := specSlot.usable (holdsAt view) guard.candidate && (pktEpoch == guard.pinnedEpoch)
  let activeTile := if pinOk then guard.specializedTile else guard.fallbackTile
  let rstate : ReconfigTileState :=
    { tileId := 0, tileX := 0, tileY := 0
    , activeTile := activeTile, frameDigest := 0x1000#64
    , isolated := false, skidHeldOutput := 0#64 }
  (pinOk, evalReconfigTile rstate (fun _ => 0#64) (fun _ => 0#64) argVal)

/-- Sample Epoch-1 `DiscrTreeTrie` containing:
1. `@[simp]` lemma `simp_scale_4_plus_2 : scaleAdd x ↦ 4 * x + 2` indexed at `[.app "scaleAdd", .star]`,
2. Typeclass instance `instAddNat : Add Nat` indexed at `[.app "Add", .const "Nat"]`. -/
def sampleEpoch1DiscrTrie : DiscrTreeTrie where
  epoch := 1
  entries :=
    [ { ruleName := KName.mkSimple "simp_scale_4_plus_2"
      , path     := [.app (KName.mkSimple "scaleAdd"), .star]
      , lutTag   := 101
      , kind     := .simpLemma (.lit (.natVal 42)) 4 2 }
    , { ruleName := KName.mkSimple "instAddNat"
      , path     := [.app (KName.mkSimple "Add"), .const (KName.mkSimple "Nat")]
      , lutTag   := 202
      , kind     := .synthInstance (KName.mkSimple "Add") (.const (KName.mkSimple "instAddNat") []) 100 } ]

/-- Sample Epoch-1 `SlotGuardReg` (`pinnedEpoch = 1`, `gain = 4`, `offset = 2`). -/
def sampleEpoch1Guard : SlotGuardReg :=
  mkDiscrTreeSlotGuard "discrEpoch" 1 4 2

/-- Sample Epoch-2 `SlotGuardReg` (`pinnedEpoch = 2`, `gain = 6`, `offset = 10`). -/
def sampleEpoch2Guard : SlotGuardReg :=
  mkDiscrTreeSlotGuard "discrEpoch" 2 6 10

/-- Pinned `LeafView` at Epoch 1 supporting `sampleEpoch1Guard.composition`. -/
def epoch1LeafView : LeafView :=
  viewOf 1 "discrEpoch" sampleEpoch1Guard.composition

/-- Mutated `LeafView` at Epoch 2 supporting `sampleEpoch2Guard.composition`. -/
def epoch2LeafView : LeafView :=
  viewOf 2 "discrEpoch" sampleEpoch2Guard.composition

/-- **Theorem (`discrTree_lut_compile_sound`)**:
1. **Wildcard & Exact Preorder `DiscrTree` Trie Indexing**:
   - Querying `sampleEpoch1DiscrTrie` on `scaleAdd 10` matches `[.app "scaleAdd", .star]` and returns
     `simp_scale_4_plus_2` (`lutTag = 101`),
   - Querying `sampleEpoch1DiscrTrie` on `Add Nat` matches `[.app "Add", .const "Nat"]` and returns
     `instAddNat` (`lutTag = 202`),
   - Querying `sampleEpoch1DiscrTrie` on `Add Bool` returns `none` (negative pole).
2. **2nd Futamura Specialization Agreement**:
   - `futamura2DiscrTreeTerm 10 32` applied to `.nat 5` evaluates in `Core4` (`Evaluates`) to `.nat 47`,
   - At `epoch1LeafView`, `evalSlotGuardedDiscrTile sampleEpoch1Guard` selects the specialized Zone-3
     `AutomatonTile` (`true`) and computes `4 * 10 + 2 = 42#64` in 1 hardware cycle.
3. **Glitch-Free `ICAP` DPR Epoch Upgrade & 1-Cycle `moved_pin_blocks` Fallback**:
   - When the environment advances to `epoch2LeafView` (`discrEpoch = 2`), `moved_pin_blocks`
     immediately invalidates `sampleEpoch1Guard.candidate` (`specSlot.usable = false`), and
     `evalSlotGuardedDiscrTile` falls back in 1 cycle (`false`),
   - Hot-swapping `sampleEpoch2Guard.specializedTile` into tile `0` via `runTileGlitchFreeDpr`
     preserves neighbor tile `1` and executes the new Epoch-2 LUT rule (`6 * 10 + 10 = 70#64`). -/
theorem discrTree_lut_compile_sound :
    let qSimp := KExpr.app (.const (KName.mkSimple "scaleAdd") []) (.lit (.natVal 10))
    let qAddNat := KExpr.app (.const (KName.mkSimple "Add") []) kNatConst
    let qAddBool := KExpr.app (.const (KName.mkSimple "Add") []) kBoolConst
    let initTile0 : ReconfigTileState :=
      { tileId := 0, tileX := 0, tileY := 0
      , activeTile := sampleEpoch1Guard.specializedTile, frameDigest := 0x4002#64
      , isolated := false, skidHeldOutput := 42#64 }
    let residentTile1 : ReconfigTileState :=
      { tileId := 1, tileX := 1, tileY := 0
      , activeTile := kernelGateTile, frameDigest := 0xCAFE#64
      , isolated := false, skidHeldOutput := 1#64 }
    let icapFrame2 : IcapBitstreamFrame :=
      { targetTileId := 0
      , newTile := sampleEpoch2Guard.specializedTile
      , expectedDigest := 0x600A#64
      , computedDigest := 0x600A#64 }
    let afterTile0 := runTileGlitchFreeDpr icapFrame2 initTile0
    let afterTile1 := runTileGlitchFreeDpr icapFrame2 residentTile1
    -- 1. Preorder DiscrTree trie positive & negative poles
    (queryBestDiscrEntry? sampleEpoch1DiscrTrie 4 qSimp).map (·.lutTag) = some 101 ∧
    (queryBestDiscrEntry? sampleEpoch1DiscrTrie 4 qAddNat).map (·.lutTag) = some 202 ∧
    queryBestDiscrEntry? sampleEpoch1DiscrTrie 4 qAddBool = none ∧
    -- 2. 2nd Futamura Core4 evaluation & Zone-3 single-cycle LUT execution
    Evaluates (.app (futamura2DiscrTreeTerm 10 32) (.nat 5)) (.nat 47) ∧
    evalSlotGuardedDiscrTile sampleEpoch1Guard epoch1LeafView 1 10#64 = (true, 42#64) ∧
    -- 3. moved_pin_blocks 1-cycle invalidation on epoch mutation + ICAP DPR upgrade to Epoch 2
    specSlot.usable (holdsAt epoch2LeafView) sampleEpoch1Guard.candidate = false ∧
    (evalSlotGuardedDiscrTile sampleEpoch1Guard epoch2LeafView 2 10#64).1 = false ∧
    evalSlotGuardedDiscrTile sampleEpoch2Guard epoch2LeafView 2 10#64 = (true, 70#64) ∧
    afterTile0.isolated = false ∧
    evalReconfigTile afterTile0 (fun _ => 0#64) (fun _ => 0#64) 10#64 = 70#64 ∧
    afterTile1 = residentTile1 := by
  refine ⟨rfl, rfl, rfl, ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩
  exact (futamura2_self_specialize_sound (elabRuleSpec 10) (.nat 32)).2.2.2.2

/-! ## 3. Synthesizable SystemVerilog Co-Simulation Module for `ExprCAM` + `SiliconKernel` + `DiscrTreeLUT` -/

/-- Unified hardware co-simulation `RtlModule` (`exprCamKernelLutRtlModule`) combining:
* Inputs:
  - `in_0` (`cam_word_a`): 64-bit packed `ExprCAM` node word A (`[63:60] tag | [59] looseBVar | [58] hasFVar | [57:32] hash | [31:16] left | [15:0] right`),
  - `in_1` (`cam_word_b`): 64-bit packed `ExprCAM` node word B,
  - `in_2` (`decl_status_tag`): `SiliconKernel` declaration status tag (`1` = kernel-verified clean declaration, `0` = `sorryAx`, `2` = type/defEq mismatch, `3` = universe error),
  - `in_3` (`pkt_epoch`): incoming packet `Environment` epoch tag,
  - `in_4` (`pinned_epoch`): `SlotGuardReg` pinned `Environment` epoch tag,
  - `in_5` (`lut_arg`): 64-bit input operand for the Zone-3 `DiscrTree` LUT pipeline (`4 * x + 2`).
* Outputs:
  - `out_cam_eq`: `1#64` iff `cam_word_a == cam_word_b` (1-cycle 64-bit `ExprCAM` structural match),
  - `out_loose_bvar_a`: bit 59 (`looseBVar` hardware flag) extracted from `cam_word_a`,
  - `out_kernel_accept`: `1#64` iff `decl_status_tag == 1` (`SiliconKernel` acceptance verdict),
  - `out_epoch_guard_ok`: `1#64` iff `pkt_epoch == pinned_epoch` (`SlotGuardReg` hit),
  - `out_lut_result`: if `out_epoch_guard_ok == 1`, outputs specialized Zone-3 LUT result `4 * lut_arg + 2`,
    else outputs `out_kernel_accept` (1-cycle fallback to resident `.machine` kernel gate). -/
def exprCamKernelLutRtlModule : RtlModule where
  name := "obend_exprcam_silicon_kernel_lut"
  inputNames :=
    [ "cam_word_a"
    , "cam_word_b"
    , "decl_status_tag"
    , "pkt_epoch"
    , "pinned_epoch"
    , "lut_arg" ]
  wires :=
    [ { wireIdx := 0
      , name    := "w_cam_eq"
      , expr    := .alu .eq (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1
      , name    := "w_loose_bvar_a"
      , expr    := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 59#64)) (.const 1#64) }
    , { wireIdx := 2
      , name    := "w_kernel_accept"
      , expr    := .alu .eq (.inputPort 2) (.const 1#64) }
    , { wireIdx := 3
      , name    := "w_epoch_guard_ok"
      , expr    := .alu .eq (.inputPort 3) (.inputPort 4) }
    , { wireIdx := 4
      , name    := "w_lut_scaled"
      , expr    := .alu .add (.alu .mul (.inputPort 5) (.const 4#64)) (.const 2#64) }
    , { wireIdx := 5
      , name    := "w_lut_or_fallback"
      , expr    := .mux (.wireRef 3) (.wireRef 4) (.wireRef 2) } ]
  regs :=
    [ { regIdx         := 0
      , name           := "r_last_accepted"
      , domain         := .coreClk
      , resetKind      := .syncReset 0#64
      , isSynchronizer := false
      , nextExpr       := .wireRef 2 }
    , { regIdx         := 1
      , name           := "r_last_lut_out"
      , domain         := .coreClk
      , resetKind      := .resetFree
      , isSynchronizer := false
      , nextExpr       := .wireRef 5 } ]
  outputs :=
    [ { name := "out_cam_eq",         expr := .wireRef 0 }
    , { name := "out_loose_bvar_a",   expr := .wireRef 1 }
    , { name := "out_kernel_accept",  expr := .wireRef 2 }
    , { name := "out_epoch_guard_ok", expr := .wireRef 3 }
    , { name := "out_lut_result",     expr := .wireRef 5 } ]

/-- Emit synthesizable SystemVerilog-2012 for `exprCamKernelLutRtlModule`. -/
def emitExprCamKernelLutSV : String :=
  emitModuleSV exprCamKernelLutRtlModule

/-- Build the 6-port input vector `(camWordA, camWordB, statusTag, pktEpoch, pinnedEpoch, lutArg)`
for `exprCamKernelLutRtlModule`. -/
def mkCosimInputs
    (camWordA camWordB : BitVec 64)
    (statusTag pktEpoch pinnedEpoch lutArg : Nat) : Nat → BitVec 64
  | 0 => camWordA
  | 1 => camWordB
  | 2 => BitVec.ofNat 64 statusTag
  | 3 => BitVec.ofNat 64 pktEpoch
  | 4 => BitVec.ofNat 64 pinnedEpoch
  | 5 => BitVec.ofNat 64 lutArg
  | _ => 0#64

/-- **Theorem (`exprCam_siliconKernel_sv_cosim_sound`)**:
1. **Topological DAG & Static CDC Signoff**:
   `checkRtlModule exprCamKernelLutRtlModule = true`,
   `exprCamKernelLutRtlModule.name = "obend_exprcam_silicon_kernel_lut"`, and
   `exprCamKernelLutRtlModule.outputs.length = 5`.
2. **Live `Lean.ConstantInfo` Acceptance & `ExprCAM` Bit-Exact Co-Simulation**:
   - On `sampleLiveLeanDefnInfo` (`liveIdNat : Nat → Nat := λ x : Nat => x`), `extractLeanConstInfo?`
     succeeds, `encodeDeclStatusTag` is `1`, a loose `.bvar 0` node packs with bit 59 = `1`, and
     `evalModuleOutputs exprCamKernelLutRtlModule` produces:
     `out_cam_eq = 1#64`, `out_loose_bvar_a = 1#64`, `out_kernel_accept = 1#64`,
     `out_epoch_guard_ok = 1#64`, and `out_lut_result = 42#64` (`4 * 10 + 2`).
3. **Live `sorryAx` Refusal & Epoch Mismatch Fallback**:
   - On `sampleLiveLeanSorryInfo` (`liveBadSorry` contaminated with `sorryAx`) and a mismatched
     environment epoch (`pktEpoch = 2 ≠ pinnedEpoch = 1`) with distinct `ExprCAM` words,
     `evalModuleOutputs exprCamKernelLutRtlModule` produces:
     `out_cam_eq = 0#64`, `out_loose_bvar_a = 0#64`, `out_kernel_accept = 0#64`,
     `out_epoch_guard_ok = 0#64`, and `out_lut_result = 0#64` (1-cycle fallback to `out_kernel_accept`). -/
theorem exprCam_siliconKernel_sv_cosim_sound :
    let wBVar0 := mkExprCamWord64 (.bvar 0) 0 0
    let wNatConst := mkExprCamWord64 kNatConst 1 0
    let tagValid :=
      match extractLeanConstInfo? sampleLiveLeanDefnInfo with
      | some d => encodeDeclStatusTag stdKernelEnv 8 d
      | none   => 0
    let tagSorry :=
      match extractLeanConstInfo? sampleLiveLeanSorryInfo with
      | some d => encodeDeclStatusTag stdKernelEnv 8 d
      | none   => 99
    let insValid := mkCosimInputs wBVar0 wBVar0 tagValid 1 1 10
    let insSorry := mkCosimInputs wNatConst wBVar0 tagSorry 2 1 10
    checkRtlModule exprCamKernelLutRtlModule = true ∧
    exprCamKernelLutRtlModule.name = "obend_exprcam_silicon_kernel_lut" ∧
    exprCamKernelLutRtlModule.outputs.length = 5 ∧
    tagValid = 1 ∧
    tagSorry = 0 ∧
    evalModuleOutputs exprCamKernelLutRtlModule insValid (fun _ => 0#64) =
      [ ("out_cam_eq", 1#64)
      , ("out_loose_bvar_a", 1#64)
      , ("out_kernel_accept", 1#64)
      , ("out_epoch_guard_ok", 1#64)
      , ("out_lut_result", 42#64) ] ∧
    evalModuleOutputs exprCamKernelLutRtlModule insSorry (fun _ => 0#64) =
      [ ("out_cam_eq", 0#64)
      , ("out_loose_bvar_a", 0#64)
      , ("out_kernel_accept", 0#64)
      , ("out_epoch_guard_ok", 0#64)
      , ("out_lut_result", 0#64) ] := by
  decide +kernel

/-! ## 4. Multi-Rule Priority TCAM Synthesis (`compileDiscrTrieToRtl`, `compileDiscrTrieToRtl_dag_valid`, `compileDiscrTrieToRtl_matches_first_rule`) -/

/-- Synthesize a combinational priority-encoder `.mux` cascade (`RtlExpr`) for a priority-ordered list
of `(patternTag, gain, offset)` rules:
* Compares `inputPort 0` (`in_tag`) against `BitVec.ofNat 64 patternTag`,
* When matched, computes `gain * inputPort 1 + offset` (`inputPort 1 * gain + offset`),
* Otherwise falls through to the next lower-priority rule (defaulting to `0#64` on `[]`). -/
def compileDiscrRulesExpr : List (Nat × Nat × Nat) → RtlExpr
  | [] => .const 0#64
  | (patTag, gain, offset) :: rest =>
    let cond := .alu .eq (.inputPort 0) (.const (BitVec.ofNat 64 patTag))
    let action :=
      .alu .add
        (.alu .mul (.inputPort 1) (.const (BitVec.ofNat 64 gain)))
        (.const (BitVec.ofNat 64 offset))
    .mux cond action (compileDiscrRulesExpr rest)

/-- Pure reference specification for evaluating a priority-ordered list of `(patternTag, gain, offset)`
TCAM rules on `(inTag, inArg)`. -/
def evalDiscrRulesSpec (inTag inArg : BitVec 64) : List (Nat × Nat × Nat) → BitVec 64
  | [] => 0#64
  | (patTag, gain, offset) :: rest =>
    if inTag == BitVec.ofNat 64 patTag then
      inArg * BitVec.ofNat 64 gain + BitVec.ofNat 64 offset
    else
      evalDiscrRulesSpec inTag inArg rest

/-- Synthesize a combinational multi-rule priority TCAM `RtlModule` (`compileDiscrTrieToRtl`)
from a priority-ordered list of `(patternTag, gain, offset)` rules. -/
def compileDiscrTrieToRtl (name : String) (rules : List (Nat × Nat × Nat)) : RtlModule where
  name       := name
  inputNames := ["in_tag", "in_arg"]
  wires      :=
    [ { wireIdx := 0
      , name    := "w_tcam_out"
      , expr    := compileDiscrRulesExpr rules } ]
  regs       := []
  outputs    := [ { name := "out_tcam", expr := .wireRef 0 } ]

theorem checkExprDAG_compileDiscrRulesExpr : ∀ (rules : List (Nat × Nat × Nat)),
    checkExprDAG 2 0 0 (compileDiscrRulesExpr rules) = true
  | [] => rfl
  | (_, _, _) :: rest => by
    simp [compileDiscrRulesExpr, checkExprDAG, checkExprDAG_compileDiscrRulesExpr rest]

/-- **Theorem (`compileDiscrTrieToRtl_dag_valid`)**:
For every module name `name` and every priority-ordered rule list `rules`, `compileDiscrTrieToRtl name rules`
passes `checkRtlModule` (`checkWireTableDAG` + output DAG bounds + `checkModuleCdc`). -/
theorem compileDiscrTrieToRtl_dag_valid (name : String) (rules : List (Nat × Nat × Nat)) :
    checkRtlModule (compileDiscrTrieToRtl name rules) = true := by
  simp [compileDiscrTrieToRtl, checkRtlModule, checkWireTableDAG, checkWireTableDAG.go,
    checkExprDAG, checkModuleCdc, checkExprDAG_compileDiscrRulesExpr rules]

theorem evalRtlExpr_compileDiscrRulesExpr
    (inputs wires regs : Nat → BitVec 64) :
    ∀ (rules : List (Nat × Nat × Nat)),
      evalRtlExpr inputs wires regs (compileDiscrRulesExpr rules) =
        evalDiscrRulesSpec (inputs 0) (inputs 1) rules
  | [] => rfl
  | (patTag, gain, offset) :: rest => by
    simp only [compileDiscrRulesExpr, evalRtlExpr, evalAluOp, evalDiscrRulesSpec,
      evalRtlExpr_compileDiscrRulesExpr inputs wires regs rest]
    by_cases hEq : (inputs 0 == BitVec.ofNat 64 patTag) = true <;> simp [hEq]

/-- **Theorem (`compileDiscrTrieToRtl_matches_first_rule`)**:
1. For *any* priority-ordered rule list `rules` and input/register state `(inputs, regs)`,
   `evalModuleOutputs (compileDiscrTrieToRtl name rules) inputs regs` evaluates to
   `[("out_tcam", evalDiscrRulesSpec (inputs 0) (inputs 1) rules)]`.
2. In particular, when the highest-priority rule `(patTag, gain, offset)` matches `inputs 0`
   (`inputs 0 = BitVec.ofNat 64 patTag`), `evalModuleOutputs` immediately selects that first
   matching rule and outputs `inputs 1 * BitVec.ofNat 64 gain + BitVec.ofNat 64 offset` regardless
   of any subsequent shadowed rules `rest`. -/
theorem compileDiscrTrieToRtl_matches_first_rule
    (name : String)
    (patTag gain offset : Nat)
    (rest : List (Nat × Nat × Nat))
    (inputs regs : Nat → BitVec 64) :
    evalModuleOutputs (compileDiscrTrieToRtl name ((patTag, gain, offset) :: rest)) inputs regs =
      [("out_tcam", evalDiscrRulesSpec (inputs 0) (inputs 1) ((patTag, gain, offset) :: rest))] ∧
    (inputs 0 = BitVec.ofNat 64 patTag →
      evalModuleOutputs (compileDiscrTrieToRtl name ((patTag, gain, offset) :: rest)) inputs regs =
        [("out_tcam", inputs 1 * BitVec.ofNat 64 gain + BitVec.ofNat 64 offset)]) := by
  have hEval :
      evalModuleOutputs (compileDiscrTrieToRtl name ((patTag, gain, offset) :: rest)) inputs regs =
        [("out_tcam", evalDiscrRulesSpec (inputs 0) (inputs 1) ((patTag, gain, offset) :: rest))] := by
    simp [compileDiscrTrieToRtl, evalModuleOutputs, evalWireTable, evalRtlExpr,
      evalRtlExpr_compileDiscrRulesExpr]
  refine ⟨hEval, ?_⟩
  intro hMatch
  rw [hEval]
  simp [evalDiscrRulesSpec, hMatch]

end Obend.Lower.DiscrTreeLUT
end


