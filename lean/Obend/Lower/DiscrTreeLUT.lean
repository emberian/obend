module
/-
# Obend.Lower.DiscrTreeLUT — Polish-Prefix `DiscrTree` Radix Tries, `SlotGuardReg` Gating & Multi-Rule Priority TCAM Synthesis

Implements `WS 28` Stage 5 & 6 (`SILICON-ELABORATOR.md` §5.2–7):
1. **Arity-Indexed Polish-Prefix `DiscrTree` Keys & Multi-Subterm Wildcard Skipping
   (`DiscrTreeKey`, `DiscrPath`, `exprToDiscrPath`, `skipSubterms`, `matchDiscrPath`)**:
   - Encodes every head symbol with its exact application spine arity (`DiscrTreeKey.arity`),
     yielding a prefix-free Polish-prefix (`Łukasiewicz`) path code (`exprToDiscrPath_prefix_free`,
     `exprToDiscrPath_app_arity_noncollision`).
   - Wildcard `.star` edges skip complete multi-token subterm encodings via `skipSubterms`
     (`skipSubterms_exprToDiscrPath`).
2. **Branched Radix `DiscrTrieNode` Completeness & Priority Ordering
   (`DiscrTrieNode`, `insertDiscrTrieNode`, `queryDiscrTrieNode`)**:
   - Proves universal candidate completeness (`queryDiscrTrieNode_insert_mem_of_matchDiscrPath`,
     `queryDiscrTrieNode_insert_mem`) and insertion-order-independent priority sorting across
     wildcard `.star` and exact compound subterm branches
     (`queryDiscrTrieNode_star_and_exact_priority_sound`).
3. **Zone-3 `SlotGuardReg` Epoch/Pin Gating & Multi-Rule Priority TCAM Synthesis
   (`SlotGuardReg`, `mkSlotGuardFromTile`, `evalSlotGuardedDiscrTile`, `compileDiscrTrieToRtl`)**:
   - Guards specialized `AutomatonTile`s with `specSlot` pin hygiene (`evalSlotGuardedDiscrTile_moved_pin_blocks`).
   - Synthesizes verified priority-encoder TCAM `RtlModule`s (`compileDiscrTrieToRtl_dag_valid`,
     `compileDiscrTrieToRtl_matches_first_rule`).
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
open Obend.Leaf.Static
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

/-! ## 1. Arity-Indexed Polish-Prefix `DiscrTree` Keys & Subterm Skipping -/

/-- Preorder discrimination-tree key token (`Lean.Meta.DiscrTree.Key`) carrying exact subterm arity
so that `DiscrPath` forms a self-delimiting Polish-prefix code without application prefix collisions. -/
inductive DiscrTreeKey where
  | const (name : KName) (arity : Nat)
  | fvar  (id : Nat) (arity : Nat)
  | lit   (val : KLiteral)
  | sort
  | arrow
  | proj  (structName : KName) (idx : Nat) (arity : Nat)
  | star
  deriving DecidableEq, Repr, Inhabited

/-- Exact number of Polish-prefix child subterms immediately following a `DiscrTreeKey` token. -/
def DiscrTreeKey.arity : DiscrTreeKey → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .lit _      => 0
  | .sort       => 0
  | .arrow      => 2
  | .proj _ _ a => a + 1
  | .star       => 0

/-- Structural equality on `DiscrTreeKey`. -/
def DiscrTreeKey.beq : DiscrTreeKey → DiscrTreeKey → Bool
  | .const n1 a1, .const n2 a2     => KName.beq n1 n2 && (a1 == a2)
  | .fvar i1 a1, .fvar i2 a2       => (i1 == i2) && (a1 == a2)
  | .lit l1, .lit l2               => KLiteral.beq l1 l2
  | .sort, .sort                   => true
  | .arrow, .arrow                 => true
  | .proj s1 i1 a1, .proj s2 i2 a2 => KName.beq s1 s2 && (i1 == i2) && (a1 == a2)
  | .star, .star                   => true
  | _, _                           => false

instance : BEq DiscrTreeKey := ⟨DiscrTreeKey.beq⟩

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
  | .const n1 a1, .const n2 a2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [KName.eq_of_beq h.1, h.2]
  | .fvar i1 a1, .fvar i2 a2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, h.2]
  | .lit l1, .lit l2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq] at h
    rw [KLiteral.eq_of_beq h]
  | .sort, .sort, _ => rfl
  | .arrow, .arrow, _ => rfl
  | .proj s1 i1 a1, .proj s2 i2 a2, h => by
    simp only [BEq.beq, DiscrTreeKey.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [KName.eq_of_beq h.1.1, h.1.2, h.2]
  | .star, .star, _ => rfl

/-- A preorder Polish-prefix sequence of `DiscrTreeKey` tokens indexing a deep `KExpr` pattern. -/
abbrev DiscrPath := List DiscrTreeKey

/-- Extract a bounded Polish-prefix `DiscrPath` from a `KExpr`, encoding each spine head with its
exact argument count (`args.length`) so nested applications of distinct arities never collide.
Metavariables (`.mvar`), loose bound variables (`.bvar`), lambdas, dependent Pis, and `let`s
index as wildcard `.star` tokens. -/
def exprToDiscrPath : Nat → KExpr → DiscrPath
  | 0, _ => [.star]
  | fuel + 1, e =>
    let (hd, args) := decomposeAppSpine e
    match hd with
    | .const n _ =>
      .const n args.length :: args.flatMap (exprToDiscrPath fuel)
    | .fvar id =>
      .fvar id args.length :: args.flatMap (exprToDiscrPath fuel)
    | .proj s idx st =>
      .proj s idx args.length :: (exprToDiscrPath fuel st ++ args.flatMap (exprToDiscrPath fuel))
    | .lit l =>
      if args.isEmpty then [.lit l] else [.star]
    | .sort _ =>
      if args.isEmpty then [.sort] else [.star]
    | .forallE d b =>
      if args.isEmpty && !KExpr.hasLooseBVar b then
        .arrow :: (exprToDiscrPath fuel d ++ exprToDiscrPath fuel b)
      else
        [.star]
    | .mvar _ | .bvar _ | .lam _ _ | .letE _ _ _ | .app _ _ =>
      [.star]

/-- Skip `n` complete Polish-prefix subterms from the front of `DiscrPath`, returning the remaining
suffix `some rem` (or `none` if the token stream ends prematurely). -/
def skipSubterms : Nat → DiscrPath → Option DiscrPath
  | 0, qs => some qs
  | _n + 1, [] => none
  | n + 1, q :: qs => skipSubterms (q.arity + n) qs

private theorem skipSubterms_flatMap_aux
    {fuel : Nat}
    (ih : ∀ (sub : KExpr) (m : Nat) (r : DiscrPath),
      skipSubterms (m + 1) (exprToDiscrPath fuel sub ++ r) = skipSubterms m r) :
    ∀ (args : List KExpr) (n : Nat) (rest : DiscrPath),
      skipSubterms (args.length + n) (args.flatMap (exprToDiscrPath fuel) ++ rest) =
        skipSubterms n rest
  | [], _n, _rest => by
    simp
  | a :: as, n, rest => by
    have hLen : (a :: as).length + n = (as.length + n) + 1 := by
      simp [List.length_cons]
      omega
    rw [List.flatMap_cons, List.append_assoc, hLen, ih a (as.length + n),
      skipSubterms_flatMap_aux ih as n rest]

/-- **Theorem (`skipSubterms_exprToDiscrPath`)**:
Every `exprToDiscrPath fuel e` is a self-delimiting Polish-prefix subterm: skipping `n + 1`
subterms from `exprToDiscrPath fuel e ++ rest` consumes `exprToDiscrPath fuel e` in its entirety
and continues skipping `n` subterms from `rest`. -/
theorem skipSubterms_exprToDiscrPath :
    ∀ (fuel : Nat) (e : KExpr) (n : Nat) (rest : DiscrPath),
      skipSubterms (n + 1) (exprToDiscrPath fuel e ++ rest) = skipSubterms n rest
  | 0, _, n, rest => by
    simp [exprToDiscrPath, skipSubterms, DiscrTreeKey.arity]
  | fuel + 1, e, n, rest => by
    unfold exprToDiscrPath
    rcases hSp : decomposeAppSpine e with ⟨hd, args⟩
    simp only []
    have ih := fun sub m r => skipSubterms_exprToDiscrPath fuel sub m r
    cases hd with
    | const nm us =>
      simp only [List.cons_append, skipSubterms, DiscrTreeKey.arity]
      exact skipSubterms_flatMap_aux ih args n rest
    | fvar id =>
      simp only [List.cons_append, skipSubterms, DiscrTreeKey.arity]
      exact skipSubterms_flatMap_aux ih args n rest
    | proj s idx st =>
      simp only [List.cons_append, List.append_assoc, skipSubterms, DiscrTreeKey.arity]
      have hArity : (args.length + 1) + n = (args.length + n) + 1 := by omega
      rw [hArity, ih st (args.length + n), skipSubterms_flatMap_aux ih args n rest]
    | lit l =>
      cases hEmp : args.isEmpty <;> simp [skipSubterms, DiscrTreeKey.arity]
    | sort u =>
      cases hEmp : args.isEmpty <;> simp [skipSubterms, DiscrTreeKey.arity]
    | forallE d b =>
      dsimp only
      cases hArr : (args.isEmpty && !KExpr.hasLooseBVar b) with
      | false =>
        simp [skipSubterms, DiscrTreeKey.arity]
      | true =>
        simp only [↓reduceIte, List.cons_append, List.append_assoc, skipSubterms, DiscrTreeKey.arity]
        have hArity : 2 + n = (n + 1) + 1 := by omega
        rw [hArity, ih d (n + 1), ih b n]
    | mvar _ | bvar _ | lam _ _ | letE _ _ _ | app _ _ =>
      simp [skipSubterms, DiscrTreeKey.arity]

/-- **Theorem (`exprToDiscrPath_prefix_free`)**:
`exprToDiscrPath fuel` is a prefix-free code: if `exprToDiscrPath fuel e1 ++ rest1 =
exprToDiscrPath fuel e2 ++ rest2`, then the suffixes `rest1 = rest2` and the subterm paths
`exprToDiscrPath fuel e1 = exprToDiscrPath fuel e2` agree identically. -/
theorem exprToDiscrPath_prefix_free
    (fuel : Nat) (e1 e2 : KExpr) (rest1 rest2 : DiscrPath)
    (hEq : exprToDiscrPath fuel e1 ++ rest1 = exprToDiscrPath fuel e2 ++ rest2) :
    exprToDiscrPath fuel e1 = exprToDiscrPath fuel e2 ∧ rest1 = rest2 := by
  have hSkip := congrArg (skipSubterms 1) hEq
  rw [skipSubterms_exprToDiscrPath fuel e1 0 rest1,
      skipSubterms_exprToDiscrPath fuel e2 0 rest2] at hSkip
  simp only [skipSubterms, Option.some.injEq] at hSkip
  subst hSkip
  exact ⟨List.append_inj_left' hEq rfl, rfl⟩

/-- **Theorem (`exprToDiscrPath_app_arity_noncollision`)**:
For any positive fuel `fuel + 1`, head symbols `h, c`, universe lists `us1, us2`, and subterms `a, b`,
the binary application `h (c a) b` (`.const h 2 :: ...`) and unary nested application `h (c a b)`
(`.const h 1 :: ...`) have strictly distinct `DiscrPath` encodings — both at the root and when
embedded inside an outer context `ctx (...)`. -/
theorem exprToDiscrPath_app_arity_noncollision
    (fuel : Nat) (ctx h c : KName) (usCtx us1 us2 : List KLevel) (a b : KExpr) :
    let eBinary := KExpr.app (.app (.const h us1) (.app (.const c us2) a)) b
    let eUnary  := KExpr.app (.const h us1) (.app (.app (.const c us2) a) b)
    exprToDiscrPath (fuel + 1) eBinary ≠ exprToDiscrPath (fuel + 1) eUnary ∧
    exprToDiscrPath (fuel + 2) (.app (.const ctx usCtx) eBinary) ≠
      exprToDiscrPath (fuel + 2) (.app (.const ctx usCtx) eUnary) := by
  refine ⟨?_, ?_⟩
  · intro hEq
    simp [exprToDiscrPath, decomposeAppSpine] at hEq
  · intro hEq
    simp [exprToDiscrPath, decomposeAppSpine] at hEq

/-- Check whether a rule's pattern path `patPath` matches a query path `qPath`, where `.star` in
`patPath` matches any complete Polish-prefix subterm (`q :: qs` skipped via `skipSubterms q.arity qs`). -/
def matchDiscrPath : DiscrPath → DiscrPath → Bool
  | [], [] => true
  | .star :: ps, q :: qs =>
    match skipSubterms q.arity qs with
    | some qRem => matchDiscrPath ps qRem
    | none      => false
  | p :: ps, q :: qs => (p == q) && matchDiscrPath ps qs
  | _, _ => false

@[simp] theorem matchDiscrPath_refl : ∀ (p : DiscrPath), matchDiscrPath p p = true
  | [] => rfl
  | k :: ks => by
    cases k <;> simp [matchDiscrPath, skipSubterms, DiscrTreeKey.arity, matchDiscrPath_refl ks]

theorem exprToDiscrPath_ne_nil : ∀ (fuel : Nat) (e : KExpr), exprToDiscrPath fuel e ≠ []
  | 0, _ => by simp [exprToDiscrPath]
  | fuel + 1, e => by
    unfold exprToDiscrPath
    rcases decomposeAppSpine e with ⟨hd, args⟩
    cases hd with
    | const _ _ | fvar _ | proj _ _ _ => simp
    | lit _ | sort _ => cases h : args.isEmpty <;> simp [h]
    | forallE d b => cases h : (args.isEmpty && !KExpr.hasLooseBVar b) <;> simp [h]
    | mvar _ | bvar _ | lam _ _ | letE _ _ _ | app _ _ => simp

/-- Every `exprToDiscrPath fuel e` is matched by a single `.star` wildcard token followed by any
matching suffix (`matchDiscrPath (.star :: ps) (exprToDiscrPath fuel e ++ qs) = matchDiscrPath ps qs`). -/
theorem matchDiscrPath_star_exprToDiscrPath
    (fuel : Nat) (e : KExpr) (ps qs : DiscrPath) :
    matchDiscrPath (.star :: ps) (exprToDiscrPath fuel e ++ qs) = matchDiscrPath ps qs := by
  have hSkip := skipSubterms_exprToDiscrPath fuel e 0 qs
  cases hPath : exprToDiscrPath fuel e with
  | nil => exact False.elim (exprToDiscrPath_ne_nil fuel e hPath)
  | cons q qTail =>
    have hSkip' : skipSubterms 1 ((q :: qTail) ++ qs) = some qs := by
      rw [← hPath]
      simpa [skipSubterms] using hSkip
    simp only [List.cons_append, skipSubterms, Nat.add_zero] at hSkip'
    simp [matchDiscrPath, hSkip']

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

/-! ## 2. Branched Radix `DiscrTree` Trie (`DiscrTrieNode`, `insertDiscrTrieNode`, `queryDiscrTrieNode`) -/

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
  (including both exact arity-keyed edges and wildcard `.star` subterm edges). -/
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

/-- Explore all outgoing child edges in `children`:
* `.star` edges consume the full Polish-prefix subterm headed by `qKey` via `queryStar`,
* non-`.star` edges matching `qKey` (`ek == qKey`) step to the immediate tail via `queryExact`,
merging all matching branch results in descending priority order via `mergeRulesByPriority`. -/
def queryChildrenWith
    (queryExact : DiscrTrieNode → List DiscrTreeEntry)
    (queryStar  : DiscrTrieNode → List DiscrTreeEntry)
    (qKey : DiscrTreeKey) :
    List (DiscrTreeKey × DiscrTrieNode) → List DiscrTreeEntry
  | [] => []
  | (ek, child) :: rest =>
    let restRes := queryChildrenWith queryExact queryStar qKey rest
    if ek == .star then
      mergeRulesByPriority (queryStar child) restRes
    else if ek == qKey then
      mergeRulesByPriority (queryExact child) restRes
    else
      restRes

mutual
  /-- Query a branched radix `DiscrTrieNode` along a Polish-prefix `DiscrPath`, exploring both exact
  key edges (`ek == qKey`) and multi-token subterm wildcard branches (`ek == .star` via `skipSubterms`)
  at every trie level by structural recursion on `DiscrTrieNode`. -/
  def queryDiscrTrieNode : DiscrTrieNode → DiscrPath → List DiscrTreeEntry
    | .mk rules _, [] => rules
    | .mk _ children, qKey :: qRest =>
      queryDiscrChildren qKey qRest (skipSubterms qKey.arity qRest) children

  /-- Structurally recursive child-list traversal for `queryDiscrTrieNode`. -/
  def queryDiscrChildren (qKey : DiscrTreeKey) (qRest : DiscrPath) (qRem? : Option DiscrPath) :
      List (DiscrTreeKey × DiscrTrieNode) → List DiscrTreeEntry
    | [] => []
    | (ek, child) :: rest =>
      let restRes := queryDiscrChildren qKey qRest qRem? rest
      if ek == .star then
        match qRem? with
        | some qRem => mergeRulesByPriority (queryDiscrTrieNode child qRem) restRes
        | none      => mergeRulesByPriority [] restRes
      else if ek == qKey then
        mergeRulesByPriority (queryDiscrTrieNode child qRest) restRes
      else
        restRes
end

theorem queryDiscrChildren_eq_queryChildrenWith
    (qKey : DiscrTreeKey) (qRest : DiscrPath) (qRem? : Option DiscrPath) :
    ∀ (children : List (DiscrTreeKey × DiscrTrieNode)),
      queryDiscrChildren qKey qRest qRem? children =
        queryChildrenWith
          (fun child => queryDiscrTrieNode child qRest)
          (match qRem? with
           | some qRem => fun child => queryDiscrTrieNode child qRem
           | none      => fun _ => [])
          qKey children
  | [] => rfl
  | (ek, child) :: rest => by
    simp only [queryDiscrChildren, queryChildrenWith,
      queryDiscrChildren_eq_queryChildrenWith qKey qRest qRem? rest]
    cases qRem? <;> rfl

theorem mem_queryChildrenWith_modifyOrInsertChild_star
    (queryExact queryStar : DiscrTrieNode → List DiscrTreeEntry)
    (upd : DiscrTrieNode → DiscrTrieNode)
    (qKey : DiscrTreeKey)
    (entry : DiscrTreeEntry)
    (hUpd : ∀ n : DiscrTrieNode, entry ∈ queryStar (upd n)) :
    ∀ (children : List (DiscrTreeKey × DiscrTrieNode)),
      entry ∈ queryChildrenWith queryExact queryStar qKey (modifyOrInsertChild .star upd children)
  | [] => by
    simp [modifyOrInsertChild, queryChildrenWith]
    exact mem_mergeRulesByPriority_left [] entry (queryStar (upd .empty)) (hUpd .empty)
  | (ek, child) :: rest => by
    simp only [modifyOrInsertChild]
    cases hek : ek == .star
    · simp only [Bool.false_eq_true, ↓reduceIte, queryChildrenWith, hek]
      split
      · exact mem_mergeRulesByPriority_right
          (queryChildrenWith queryExact queryStar qKey (modifyOrInsertChild .star upd rest))
          entry
          (mem_queryChildrenWith_modifyOrInsertChild_star queryExact queryStar upd qKey entry hUpd rest)
          (queryExact child)
      · exact mem_queryChildrenWith_modifyOrInsertChild_star queryExact queryStar upd qKey entry hUpd rest
    · have hekEq : ek = .star := DiscrTreeKey.eq_of_beq hek
      subst hekEq
      simp only [↓reduceIte, queryChildrenWith, DiscrTreeKey.beq_refl]
      exact mem_mergeRulesByPriority_left
        (queryChildrenWith queryExact queryStar qKey rest)
        entry
        (queryStar (upd child))
        (hUpd child)

theorem mem_queryChildrenWith_modifyOrInsertChild_exact
    (queryExact queryStar : DiscrTrieNode → List DiscrTreeEntry)
    (upd : DiscrTrieNode → DiscrTrieNode)
    (patKey qKey : DiscrTreeKey)
    (entry : DiscrTreeEntry)
    (hNotStar : (patKey == .star) = false)
    (hKeyEq : (patKey == qKey) = true)
    (hUpd : ∀ n : DiscrTrieNode, entry ∈ queryExact (upd n)) :
    ∀ (children : List (DiscrTreeKey × DiscrTrieNode)),
      entry ∈ queryChildrenWith queryExact queryStar qKey (modifyOrInsertChild patKey upd children)
  | [] => by
    simp [modifyOrInsertChild, queryChildrenWith, hNotStar, hKeyEq]
    exact mem_mergeRulesByPriority_left [] entry (queryExact (upd .empty)) (hUpd .empty)
  | (ek, child) :: rest => by
    simp only [modifyOrInsertChild]
    cases hek : ek == patKey
    · simp only [Bool.false_eq_true, ↓reduceIte, queryChildrenWith]
      split
      · exact mem_mergeRulesByPriority_right
          (queryChildrenWith queryExact queryStar qKey (modifyOrInsertChild patKey upd rest))
          entry
          (mem_queryChildrenWith_modifyOrInsertChild_exact queryExact queryStar upd patKey qKey entry hNotStar hKeyEq hUpd rest)
          (queryStar child)
      · split
        · exact mem_mergeRulesByPriority_right
            (queryChildrenWith queryExact queryStar qKey (modifyOrInsertChild patKey upd rest))
            entry
            (mem_queryChildrenWith_modifyOrInsertChild_exact queryExact queryStar upd patKey qKey entry hNotStar hKeyEq hUpd rest)
            (queryExact child)
        · exact mem_queryChildrenWith_modifyOrInsertChild_exact queryExact queryStar upd patKey qKey entry hNotStar hKeyEq hUpd rest
    · have hekEq : ek = patKey := DiscrTreeKey.eq_of_beq hek
      subst hekEq
      simp only [↓reduceIte, queryChildrenWith, hNotStar, Bool.false_eq_true, hKeyEq]
      exact mem_mergeRulesByPriority_left
        (queryChildrenWith queryExact queryStar qKey rest)
        entry
        (queryExact (upd child))
        (hUpd child)

/-- **Theorem (`queryDiscrTrieNode_insert_mem_of_matchDiscrPath`)**:
Whenever a rule pattern path `patPath` matches a query path `qPath` (`matchDiscrPath patPath qPath = true`,
supporting both multi-token `.star` subterm skipping via `skipSubterms` and exact key equality),
inserting `(patPath, entry)` into `node` guarantees
`entry ∈ queryDiscrTrieNode (insertDiscrTrieNode patPath entry node) qPath`. -/
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
  | .star :: patRest, qKey :: qRest, entry, .mk rules children, hMatch => by
    simp only [matchDiscrPath] at hMatch
    cases hSkip : skipSubterms qKey.arity qRest with
    | none =>
      rw [hSkip] at hMatch
      cases hMatch
    | some qRem =>
      rw [hSkip] at hMatch
      simp only [insertDiscrTrieNode, queryDiscrTrieNode, queryDiscrChildren_eq_queryChildrenWith, hSkip]
      exact mem_queryChildrenWith_modifyOrInsertChild_star
        (fun child => queryDiscrTrieNode child qRest)
        (fun child => queryDiscrTrieNode child qRem)
        (insertDiscrTrieNode patRest entry)
        qKey
        entry
        (fun n => queryDiscrTrieNode_insert_mem_of_matchDiscrPath patRest qRem entry n hMatch)
        children
  | patKey :: patRest, qKey :: qRest, entry, .mk rules children, hMatch => by
    cases hStar : patKey == .star with
    | true =>
      have hEqStar : patKey = .star := DiscrTreeKey.eq_of_beq hStar
      subst hEqStar
      simp only [matchDiscrPath] at hMatch
      cases hSkip : skipSubterms qKey.arity qRest with
      | none =>
        rw [hSkip] at hMatch
        cases hMatch
      | some qRem =>
        rw [hSkip] at hMatch
        simp only [insertDiscrTrieNode, queryDiscrTrieNode, queryDiscrChildren_eq_queryChildrenWith, hSkip]
        exact mem_queryChildrenWith_modifyOrInsertChild_star
          (fun child => queryDiscrTrieNode child qRest)
          (fun child => queryDiscrTrieNode child qRem)
          (insertDiscrTrieNode patRest entry)
          qKey
          entry
          (fun n => queryDiscrTrieNode_insert_mem_of_matchDiscrPath patRest qRem entry n hMatch)
          children
    | false =>
      have hStep : (patKey == qKey) = true ∧ matchDiscrPath patRest qRest = true := by
        cases patKey <;> simp [BEq.beq, DiscrTreeKey.beq] at hStar <;>
          simp [matchDiscrPath, BEq.beq, DiscrTreeKey.beq] at hMatch ⊢ <;> exact hMatch
      simp only [insertDiscrTrieNode, queryDiscrTrieNode, queryDiscrChildren_eq_queryChildrenWith]
      cases hSkip : skipSubterms qKey.arity qRest with
      | some qRem =>
        exact mem_queryChildrenWith_modifyOrInsertChild_exact
          (fun child => queryDiscrTrieNode child qRest)
          (fun child => queryDiscrTrieNode child qRem)
          (insertDiscrTrieNode patRest entry)
          patKey qKey entry hStar hStep.1
          (fun n => queryDiscrTrieNode_insert_mem_of_matchDiscrPath patRest qRest entry n hStep.2)
          children
      | none =>
        exact mem_queryChildrenWith_modifyOrInsertChild_exact
          (fun child => queryDiscrTrieNode child qRest)
          (fun _ => [])
          (insertDiscrTrieNode patRest entry)
          patKey qKey entry hStar hStep.1
          (fun n => queryDiscrTrieNode_insert_mem_of_matchDiscrPath patRest qRest entry n hStep.2)
          children

/-- **Theorem (`queryDiscrTrieNode_insert_mem`)**:
Inserting `(path, entry)` into any branched radix trie node `node` guarantees that querying the
updated trie along `path` returns `entry`. -/
theorem queryDiscrTrieNode_insert_mem
    (path : DiscrPath) (entry : DiscrTreeEntry) (node : DiscrTrieNode) :
    entry ∈ queryDiscrTrieNode (insertDiscrTrieNode path entry node) path :=
  queryDiscrTrieNode_insert_mem_of_matchDiscrPath path path entry node (matchDiscrPath_refl path)

theorem queryDiscrTrieNode_singleton :
    ∀ (path : DiscrPath) (entry : DiscrTreeEntry),
      queryDiscrTrieNode (insertDiscrTrieNode path entry .empty) path = [entry]
  | [], entry => by
    simp [DiscrTrieNode.empty, insertDiscrTrieNode, queryDiscrTrieNode, insertRuleByPriority]
  | k :: ks, entry => by
    have hIH : queryDiscrTrieNode (insertDiscrTrieNode ks entry (.mk [] [])) ks = [entry] :=
      queryDiscrTrieNode_singleton ks entry
    simp only [DiscrTrieNode.empty, insertDiscrTrieNode, modifyOrInsertChild, queryDiscrTrieNode,
      queryDiscrChildren_eq_queryChildrenWith]
    cases hStar : k == .star with
    | true =>
      have hk : k = .star := DiscrTreeKey.eq_of_beq hStar
      subst hk
      simp [DiscrTreeKey.arity, skipSubterms, queryChildrenWith, mergeRulesByPriority,
        insertRuleByPriority, hIH]
    | false =>
      have hRefl : (k == k) = true := DiscrTreeKey.beq_refl k
      cases skipSubterms k.arity ks <;>
        simp [queryChildrenWith, hStar, hRefl, mergeRulesByPriority, insertRuleByPriority, hIH]

private theorem exprToDiscrPath_star_head_nil :
    ∀ (fuel : Nat) (e : KExpr) (qs : DiscrPath),
      exprToDiscrPath fuel e = .star :: qs → qs = []
  | 0, _, qs, h => by
    simp [exprToDiscrPath] at h
    exact h
  | fuel + 1, e, qs, h => by
    unfold exprToDiscrPath at h
    rcases hSp : decomposeAppSpine e with ⟨hd, args⟩
    rw [hSp] at h
    cases hd with
    | const _ _ | fvar _ | proj _ _ _ => simp at h
    | lit _ | sort _ =>
      cases hEmp : args.isEmpty <;> simp [hEmp] at h
      exact h
    | forallE d b =>
      cases hArr : (args.isEmpty && !KExpr.hasLooseBVar b) <;> simp [hArr] at h
      exact h
    | mvar _ | bvar _ | lam _ _ | letE _ _ _ | app _ _ =>
      simp at h
      exact h

/-- **Theorem (`queryDiscrTrieNode_star_and_exact_priority_sound`)**:
For *any* head symbol `fn`, fuel `fuel`, arbitrary (possibly deeply nested) argument `arg : KExpr`,
wildcard rule `rWild` indexed at `[.const fn 1, .star]`, and exact rule `rExact` indexed at
`exprToDiscrPath (fuel + 1) (.app (.const fn []) arg)` with `rExact.priority > rWild.priority`,
querying `buildDiscrTrieNode` on `exprToDiscrPath (fuel + 1) (.app (.const fn []) arg)` returns
`[rExact, rWild]` (highest priority first) regardless of insertion order. -/
theorem queryDiscrTrieNode_star_and_exact_priority_sound
    (fn : KName) (fuel : Nat) (arg : KExpr)
    (rWild rExact : DiscrTreeEntry)
    (hWildPath : rWild.path = [.const fn 1, .star])
    (hExactPath : rExact.path = exprToDiscrPath (fuel + 1) (.app (.const fn []) arg))
    (hPrio : rExact.priority > rWild.priority) :
    let qPath := exprToDiscrPath (fuel + 1) (.app (.const fn []) arg)
    queryDiscrTrieNode (buildDiscrTrieNode [rWild, rExact]) qPath = [rExact, rWild] ∧
    queryDiscrTrieNode (buildDiscrTrieNode [rExact, rWild]) qPath = [rExact, rWild] := by
  have hQPath : exprToDiscrPath (fuel + 1) (.app (.const fn []) arg) =
      .const fn 1 :: exprToDiscrPath fuel arg := by
    simp [exprToDiscrPath, decomposeAppSpine]
  have hConstNotStar : (DiscrTreeKey.const fn 1 == .star) = false := rfl
  have hConstRefl : (DiscrTreeKey.const fn 1 == .const fn 1) = true :=
    DiscrTreeKey.beq_refl (.const fn 1)
  have hLeExact : rWild.priority ≤ rExact.priority := by omega
  have hNotLeWild : ¬ (rExact.priority ≤ rWild.priority) := by omega
  have hSkipSub := skipSubterms_exprToDiscrPath fuel arg 0 []
  cases hSub : exprToDiscrPath fuel arg with
  | nil => exact False.elim (exprToDiscrPath_ne_nil fuel arg hSub)
  | cons qKey qRest =>
    have hSkip' : skipSubterms qKey.arity qRest = some [] := by
      have htmp : skipSubterms 1 ((qKey :: qRest) ++ []) = some [] := by
        rw [← hSub]
        simpa [skipSubterms] using hSkipSub
      simpa [skipSubterms] using htmp
    cases hStar : qKey == .star with
    | true =>
      have hqEq : qKey = .star := DiscrTreeKey.eq_of_beq hStar
      subst hqEq
      have hNil : qRest = [] := exprToDiscrPath_star_head_nil fuel arg qRest hSub
      subst hNil
      simp [buildDiscrTrieNode, hWildPath, hExactPath, hQPath, hSub, DiscrTrieNode.empty,
        insertDiscrTrieNode, modifyOrInsertChild, queryDiscrTrieNode, queryDiscrChildren,
        hConstNotStar, hConstRefl,
        DiscrTreeKey.arity, skipSubterms, insertRuleByPriority, mergeRulesByPriority,
        hLeExact, hNotLeWild]
    | false =>
      have hStarSym : (.star == qKey) = false := by
        cases qKey <;> simp [BEq.beq, DiscrTreeKey.beq] at hStar ⊢
      have hQRefl : (qKey == qKey) = true := DiscrTreeKey.beq_refl qKey
      have hSing : queryDiscrTrieNode (insertDiscrTrieNode qRest rExact (.mk [] [])) qRest = [rExact] :=
        queryDiscrTrieNode_singleton qRest rExact
      simp [buildDiscrTrieNode, hWildPath, hExactPath, hQPath, hSub, DiscrTrieNode.empty,
        insertDiscrTrieNode, modifyOrInsertChild, queryDiscrTrieNode, queryDiscrChildren,
        hConstNotStar, hConstRefl,
        hSkip', hStar, hStarSym, hQRefl, hSing, insertRuleByPriority, mergeRulesByPriority,
        hLeExact, hNotLeWild]

/-! ## 3. Zone-3 `SlotGuardReg` Epoch & `LeafPin` Gating -/

/-- Hardware `SlotGuardReg` (`SILICON-ELABORATOR.md` §5.3) binding a Zone-3 `AutomatonTile` to a
pinned `Environment` epoch and `LeafPin` support list. -/
structure SlotGuardReg where
  slotName        : String
  pinnedEpoch     : Nat
  composition     : Composition
  candidate       : Candidate
  specializedTile : AutomatonTile
  fallbackTile    : AutomatonTile

/-- Construct a `SlotGuardReg` binding a specialized Zone-3 `AutomatonTile` and resident fallback
`AutomatonTile` to `leanComposition slotName specTerm` at `epoch`. -/
def mkSlotGuardFromTile
    (slotName : String)
    (epoch : Nat)
    (specTerm : Term)
    (specializedTile fallbackTile : AutomatonTile) : SlotGuardReg :=
  let comp := leanComposition slotName specTerm
  let cand : Candidate := .book slotName comp
  { slotName        := slotName
  , pinnedEpoch     := epoch
  , composition     := comp
  , candidate       := cand
  , specializedTile := specializedTile
  , fallbackTile    := fallbackTile }

/-- Evaluate a packet through a `SlotGuardReg`-protected Zone-3 tile:
if the live `LeafView` satisfies all pinned `Supports` (`specSlot.usable (holdsAt view) guard.candidate`)
and `pktEpoch == guard.pinnedEpoch`, executes the single-cycle specialized Zone-3 tile;
otherwise (`moved_pin_blocks`), routes in 1 cycle to `guard.fallbackTile`. -/
def evalSlotGuardedDiscrTile
    (guard : SlotGuardReg)
    (view : LeafView)
    (pktEpoch : Nat)
    (argVal : BitVec 64) : Bool × BitVec 64 :=
  let pinOk := specSlot.usable (holdsAt view) guard.candidate && (pktEpoch == guard.pinnedEpoch)
  let activeTile := if pinOk then guard.specializedTile else guard.fallbackTile
  let rstate : ReconfigTileState :=
    { tileId := 0, tileX := 0, tileY := 0
    , activeTile := activeTile, frameCrc64 := 0x1000#64
    , isolated := false, skidHeldOutput := 0#64 }
  (pinOk, evalReconfigTile rstate (fun _ => 0#64) (fun _ => 0#64) argVal)

/-- **Theorem (`evalSlotGuardedDiscrTile_moved_pin_blocks`)**:
Whenever any pinned `LeafPin` `p ∈ guard.candidate.supports` mutates in `view`
(`holdsAt view p = false`), `specSlot.usable (holdsAt view) guard.candidate = false` and
`evalSlotGuardedDiscrTile` immediately rejects the specialized fast path (`(evalSlotGuardedDiscrTile ...).1 = false`)
and evaluates `guard.fallbackTile` in 1 cycle. -/
theorem evalSlotGuardedDiscrTile_moved_pin_blocks
    (guard : SlotGuardReg) (view : LeafView) (p : LeafPin)
    (pktEpoch : Nat) (argVal : BitVec 64)
    (hp : p ∈ guard.candidate.supports)
    (hDead : holdsAt view p = false) :
    specSlot.usable (holdsAt view) guard.candidate = false ∧
    (evalSlotGuardedDiscrTile guard view pktEpoch argVal).1 = false := by
  have hMemDead : p ∈ specSlot.dead (holdsAt view) guard.candidate :=
    (mem_dead_iff _ _ _ _).2 ⟨hp, hDead⟩
  have hUsableFalse : specSlot.usable (holdsAt view) guard.candidate = false := by
    unfold Slot.usable
    cases hd : specSlot.dead (holdsAt view) guard.candidate with
    | nil => rw [hd] at hMemDead; cases hMemDead
    | cons _ _ => simp [List.isEmpty]
  refine ⟨hUsableFalse, ?_⟩
  simp [evalSlotGuardedDiscrTile, hUsableFalse]

/-! ## 4. Multi-Rule Priority TCAM Synthesis (`compileDiscrTrieToRtl`) -/

/-- Synthesize a combinational priority-encoder `.mux` cascade (`RtlExpr`) for a priority-ordered list
of `(patternTag, gain, offset)` rules over `inputPort tagPort` and `inputPort argPort`. -/
def compileDiscrRulesExprAt (tagPort argPort : Nat) : List (Nat × Nat × Nat) → RtlExpr
  | [] => .const 0#64
  | (patTag, gain, offset) :: rest =>
    let cond := .alu .eq (.inputPort tagPort) (.const (BitVec.ofNat 64 patTag))
    let action :=
      .alu .add
        (.alu .mul (.inputPort argPort) (.const (BitVec.ofNat 64 gain)))
        (.const (BitVec.ofNat 64 offset))
    .mux cond action (compileDiscrRulesExprAt tagPort argPort rest)

/-- Synthesize a combinational priority-encoder `.mux` cascade (`RtlExpr`) for a priority-ordered list
of `(patternTag, gain, offset)` rules:
* Compares `inputPort 0` (`in_tag`) against `BitVec.ofNat 64 patternTag`,
* When matched, computes `inputPort 1 * gain + offset`,
* Otherwise falls through to the next lower-priority rule (defaulting to `0#64` on `[]`). -/
abbrev compileDiscrRulesExpr (rules : List (Nat × Nat × Nat)) : RtlExpr :=
  compileDiscrRulesExprAt 0 1 rules

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
    simp [compileDiscrRulesExpr, compileDiscrRulesExprAt, checkExprDAG, checkExprDAG_compileDiscrRulesExpr rest]

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
    simp only [compileDiscrRulesExpr, compileDiscrRulesExprAt, evalRtlExpr, evalAluOp, evalDiscrRulesSpec,
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
