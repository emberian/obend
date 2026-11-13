module
/-
# Obend.Analysis.EqSatHypergraph — Verified Equality Saturation & Clairvoyant Cost-Optimal Hypergraph AD / RTL Extraction

Implements Pillar 3A (`NEXT-MATHEMATICA.md` / `AMBITION.md`):
1. **Hypergraph E-Graph Representation & Consistency Invariant (`EClassId`, `HyperENode`, `EClass`, `HyperEGraph`, `evalENode`, `EGraphConsistent`)**:
   - Lifts any `StrictOpenHypergraph` (including whole-DAG reverse-mode adjoint hypergraphs produced by
     `compileGraphAdjoint`) into an equality-saturation `HyperEGraph` (`hypergraphToEGraph`).
2. **16 Verified Algebraic & Adjoint Rewrite Rules (`EqSatRule`, `applyEqSatRule`, `saturateHyperEGraph`, `autoSaturateCotangentPass`)**:
   - Implements `.scaleOneElim`, `.scaleZeroElim`, `.scaleFuse`, `.addZeroRight`, `.addZeroLeft`,
     `.addComm`, `.mulComm`, `.mulOneRight`, `.mulZeroRight`, `.subSelfZero`, `.addNegScaleToSub`,
     `.fuseMulAddToMac`, `.fuseAddMulToMac`, `.factorRightDistrib`, `.constFoldAdd`, `.constFoldMul`.
   - Proves **`applyEqSatRule_preserves_consistency`** and **`saturateHyperEGraph_preserves_consistency`**
     across all 16 rewrite rules and arbitrary multi-pass saturation schedules.
3. **Clairvoyant Cost-Optimal Hypergraph Extraction (`HyperCostModel`, `defaultRtlCostModel`, `evalHypergraphCost`, `extractMinCostHypergraph`, `optimizeAdjointHypergraph`)**:
   - Extracts minimum-cost `HyperENode`s per E-Class and prunes dead intermediate cotangent hyperedges.
   - Proves universal cost monotonicity **`extractMinCost_improves_cost`**, strict cost reduction on the
     diamond adjoint **`goldenDiamondAdjoint_eqSat_strict_cost_reduction`**, semantic & cotangent
     preservation **`eqSat_preserves_eval_and_adjoint`** & **`optimizeAdjointHypergraph_preserves_cotangents`**,
     pipelined RTL lowering **`eqSat_pipelined_rtl_sound`**, and coupled discrete Pontryagin flowpipe
     adjoint sensitivity **`pontryagin_flowpipe_adjoint_eqSat_sound`**.
-/
public import Obend.Hardware.OpenHypergraph
public import Obend.Analysis.Flowpipe
@[expose] public section

namespace Obend.Analysis
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Hypergraph E-Graph Representation & Semantic Consistency (`EGraphConsistent`) -/

/-- Identifier of an equivalence class in a `HyperEGraph` (indexed by SSA wire ID). -/
abbrev EClassId := Nat

/-- An E-Node in a `HyperEGraph` pairing a `HypergraphOp` with child `EClassId`s. -/
structure HyperENode where
  op       : HypergraphOp
  children : List EClassId
  deriving DecidableEq, Repr

/-- An equivalence class (`EClass`) storing candidate equivalent `HyperENode`s for SSA wire `classId`
alongside the seed hyperedge `origEdge`. -/
structure EClass where
  classId  : EClassId
  nodes    : List HyperENode
  origEdge : HyperEdge
  deriving DecidableEq, Repr

/-- Equality-saturation E-Graph over a `StrictOpenHypergraph`. -/
structure HyperEGraph where
  classes     : List EClass
  numWires    : Nat
  boundaryIn  : List Nat
  boundaryOut : List Nat
  baseEdges   : List HyperEdge
  deriving DecidableEq, Repr

/-- Evaluate a single `HyperENode` under an E-Class valuation `env : EClassId → Int`. -/
def evalENode (env : EClassId → Int) (n : HyperENode) : Int :=
  evalHypergraphOp n.op (n.children.map env)

/-- Semantic consistency invariant of a `HyperEGraph` with respect to a wire/class valuation
`env : EClassId → Int`: every `HyperENode` `n` in every `EClass` `c ∈ eg.classes` evaluates to `env c.classId`. -/
def EGraphConsistent (eg : HyperEGraph) (env : EClassId → Int) : Prop :=
  ∀ c ∈ eg.classes, ∀ n ∈ c.nodes, evalENode env n = env c.classId

/-- Convert a `HyperEdge` into its canonical `HyperENode`. -/
def edgeToENode (e : HyperEdge) : HyperENode :=
  { op := e.op, children := e.srcWires }

/-- Convert a `HyperEdge` into a singleton `EClass`. -/
def edgeToEClass (e : HyperEdge) : EClass :=
  { classId  := e.dstWire
  , nodes    := [edgeToENode e]
  , origEdge := e }

/-- Lift a `StrictOpenHypergraph` `g` into an initial `HyperEGraph`. -/
def hypergraphToEGraph (g : StrictOpenHypergraph) : HyperEGraph :=
  let edges := extractHyperEdges g
  { classes     := edges.map edgeToEClass
  , numWires    := g.nodeTypes.length
  , boundaryIn  := g.boundaryIn.table
  , boundaryOut := g.boundaryOut.table
  , baseEdges   := edges }

/-! ## 2. Pattern-Matching Helpers & Cross-Class Lookup Soundness -/

/-- Look up the candidate `HyperENode` list for `EClassId` `u` in `classes`. -/
def findClassNodes : List EClass → EClassId → List HyperENode
  | [], _ => []
  | c :: rest, u => if c.classId == u then c.nodes else findClassNodes rest u

theorem evalENode_of_mem_findClassNodesAux
    (classes : List EClass) (env : EClassId → Int)
    (hCons : ∀ c ∈ classes, ∀ n ∈ c.nodes, evalENode env n = env c.classId)
    (u : EClassId) (nChild : HyperENode)
    (hMem : nChild ∈ findClassNodes classes u) :
    evalENode env nChild = env u := by
  induction classes with
  | nil =>
    contradiction
  | cons c rest ih =>
    unfold findClassNodes at hMem
    cases hcu : (c.classId == u)
    · simp only [hcu, Bool.false_eq_true, ↓reduceIte] at hMem
      exact ih (fun c' hc' n hn => hCons c' (List.mem_cons_of_mem c hc') n hn) hMem
    · simp only [hcu, ↓reduceIte] at hMem
      have hEq : c.classId = u := LawfulBEq.eq_of_beq hcu
      rw [← hEq]
      exact hCons c List.mem_cons_self nChild hMem

theorem evalENode_of_mem_findClassNodes
    (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (u : EClassId) (nChild : HyperENode)
    (hMem : nChild ∈ findClassNodes eg.classes u) :
    evalENode env nChild = env u :=
  evalENode_of_mem_findClassNodesAux eg.classes env hCons u nChild hMem

/-- Match a nullary `.const v` `HyperENode`. -/
def matchNullaryConst : HyperENode → Option Int
  | ⟨.const v, []⟩ => some v
  | _ => none

theorem matchNullaryConst_sound (env : EClassId → Int) (n : HyperENode) (v : Int)
    (h : matchNullaryConst n = some v) : evalENode env n = v := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨_, _⟩ <;> try contradiction
  simp only [matchNullaryConst, Option.some.injEq] at h
  subst h
  rfl

/-- Match a unary `.scale k [u]` `HyperENode`. -/
def matchUnaryScale : HyperENode → Option (Int × EClassId)
  | ⟨.scale k, [u]⟩ => some (k, u)
  | _ => none

theorem matchUnaryScale_sound (env : EClassId → Int) (n : HyperENode) (k : Int) (u : EClassId)
    (h : matchUnaryScale n = some (k, u)) : evalENode env n = k * env u := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | _⟩ <;> try contradiction
  simp only [matchUnaryScale, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- Match a binary `.add [u, v]` `HyperENode`. -/
def matchBinaryAdd : HyperENode → Option (EClassId × EClassId)
  | ⟨.add, [u, v]⟩ => some (u, v)
  | _ => none

theorem matchBinaryAdd_sound (env : EClassId → Int) (n : HyperENode) (u v : EClassId)
    (h : matchBinaryAdd n = some (u, v)) : evalENode env n = env u + env v := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinaryAdd, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- Match a binary `.sub [u, v]` `HyperENode`. -/
def matchBinarySub : HyperENode → Option (EClassId × EClassId)
  | ⟨.sub, [u, v]⟩ => some (u, v)
  | _ => none

theorem matchBinarySub_sound (env : EClassId → Int) (n : HyperENode) (u v : EClassId)
    (h : matchBinarySub n = some (u, v)) : evalENode env n = env u - env v := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinarySub, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- Match a binary `.mul [u, v]` `HyperENode`. -/
def matchBinaryMul : HyperENode → Option (EClassId × EClassId)
  | ⟨.mul, [u, v]⟩ => some (u, v)
  | _ => none

theorem matchBinaryMul_sound (env : EClassId → Int) (n : HyperENode) (u v : EClassId)
    (h : matchBinaryMul n = some (u, v)) : evalENode env n = env u * env v := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinaryMul, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- Return the first `HyperENode` in a node list if non-empty. -/
def firstNode? : List HyperENode → Option HyperENode
  | [] => none
  | n :: _ => some n

theorem firstNode?_mem {nodes : List HyperENode} {n : HyperENode}
    (h : firstNode? nodes = some n) : n ∈ nodes := by
  cases nodes with
  | nil => contradiction
  | cons hd tl =>
    simp only [firstNode?, Option.some.injEq] at h
    subst h
    exact List.mem_cons_self

theorem firstNode?_sound
    (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (u : EClassId) (nChild : HyperENode)
    (hFind : firstNode? (findClassNodes eg.classes u) = some nChild) :
    evalENode env nChild = env u :=
  evalENode_of_mem_findClassNodes eg env hCons u nChild (firstNode?_mem hFind)

/-- Search a list of `HyperENode`s for a constant `.const v`. -/
def findConstInNodes : List HyperENode → Option Int
  | [] => none
  | n :: rest =>
    match matchNullaryConst n with
    | some v => some v
    | none   => findConstInNodes rest

theorem findConstInNodes_mem (env : EClassId → Int) :
    ∀ (nodes : List HyperENode) (v : Int),
      findConstInNodes nodes = some v → ∃ n ∈ nodes, evalENode env n = v
  | [], _, h => by contradiction
  | n :: rest, v, h => by
    unfold findConstInNodes at h
    cases hm : matchNullaryConst n with
    | some v0 =>
      simp only [hm, Option.some.injEq] at h
      subst h
      exact ⟨n, List.mem_cons_self, matchNullaryConst_sound env n v0 hm⟩
    | none =>
      simp only [hm] at h
      obtain ⟨n', hn'Mem, hn'Val⟩ := findConstInNodes_mem env rest v h
      exact ⟨n', List.mem_cons_of_mem n hn'Mem, hn'Val⟩

theorem findConstInNodes_sound
    (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (u : EClassId) (v : Int)
    (hFind : findConstInNodes (findClassNodes eg.classes u) = some v) :
    env u = v := by
  obtain ⟨n, hnMem, hnVal⟩ := findConstInNodes_mem env (findClassNodes eg.classes u) v hFind
  rw [← evalENode_of_mem_findClassNodes eg env hCons u n hnMem, hnVal]

/-- Search a list of `HyperENode`s for a unary `.scale k [w]`. -/
def findScaleInNodes : List HyperENode → Option (Int × EClassId)
  | [] => none
  | n :: rest =>
    match matchUnaryScale n with
    | some kw => some kw
    | none    => findScaleInNodes rest

theorem findScaleInNodes_mem (env : EClassId → Int) :
    ∀ (nodes : List HyperENode) (k : Int) (w : EClassId),
      findScaleInNodes nodes = some (k, w) → ∃ n ∈ nodes, evalENode env n = k * env w
  | [], _, _, h => by contradiction
  | n :: rest, k, w, h => by
    unfold findScaleInNodes at h
    cases hm : matchUnaryScale n with
    | some kw =>
      rcases kw with ⟨k0, w0⟩
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨n, List.mem_cons_self, matchUnaryScale_sound env n k0 w0 hm⟩
    | none =>
      simp only [hm] at h
      obtain ⟨n', hn'Mem, hn'Val⟩ := findScaleInNodes_mem env rest k w h
      exact ⟨n', List.mem_cons_of_mem n hn'Mem, hn'Val⟩

theorem findScaleInNodes_sound
    (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (u : EClassId) (k : Int) (w : EClassId)
    (hFind : findScaleInNodes (findClassNodes eg.classes u) = some (k, w)) :
    env u = k * env w := by
  obtain ⟨n, hnMem, hnVal⟩ := findScaleInNodes_mem env (findClassNodes eg.classes u) k w hFind
  rw [← evalENode_of_mem_findClassNodes eg env hCons u n hnMem, hnVal]

/-- Search a list of `HyperENode`s for a binary `.mul [x, y]`. -/
def findMulInNodes : List HyperENode → Option (EClassId × EClassId)
  | [] => none
  | n :: rest =>
    match matchBinaryMul n with
    | some xy => some xy
    | none    => findMulInNodes rest

theorem findMulInNodes_mem (env : EClassId → Int) :
    ∀ (nodes : List HyperENode) (x y : EClassId),
      findMulInNodes nodes = some (x, y) → ∃ n ∈ nodes, evalENode env n = env x * env y
  | [], _, _, h => by contradiction
  | n :: rest, x, y, h => by
    unfold findMulInNodes at h
    cases hm : matchBinaryMul n with
    | some xy =>
      rcases xy with ⟨x0, y0⟩
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨n, List.mem_cons_self, matchBinaryMul_sound env n x0 y0 hm⟩
    | none =>
      simp only [hm] at h
      obtain ⟨n', hn'Mem, hn'Val⟩ := findMulInNodes_mem env rest x y h
      exact ⟨n', List.mem_cons_of_mem n hn'Mem, hn'Val⟩

theorem findMulInNodes_sound
    (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (u : EClassId) (x y : EClassId)
    (hFind : findMulInNodes (findClassNodes eg.classes u) = some (x, y)) :
    env u = env x * env y := by
  obtain ⟨n, hnMem, hnVal⟩ := findMulInNodes_mem env (findClassNodes eg.classes u) x y hFind
  rw [← evalENode_of_mem_findClassNodes eg env hCons u n hnMem, hnVal]

/-! ## 3. Verified Equality Saturation Rules (`EqSatRule`, `applyEqSatRule`, `saturateHyperEGraph`) -/

/-- The 16 verified algebraic & reverse-AD cotangent equality-saturation rules over `HyperEGraph`. -/
inductive EqSatRule where
  | scaleOneElim       -- 1 * u ↦ u
  | scaleZeroElim      -- 0 * u ↦ 0
  | scaleFuse          -- k1 * (k2 * w) ↦ (k1 * k2) * w
  | addZeroRight       -- u + 0 ↦ 1 * u
  | addZeroLeft        -- 0 + v ↦ 1 * v
  | addComm            -- u + v ↦ v + u
  | mulComm            -- u * v ↦ v * u
  | mulOneRight        -- u * (1 * w) ↦ u * w  and  u * 1 ↦ 1 * u
  | mulZeroRight       -- u * 0 ↦ 0
  | subSelfZero        -- u - u ↦ 0
  | addNegScaleToSub   -- u + (-1 * w) ↦ u - w
  | fuseMulAddToMac    -- (x * y) + z ↦ mac(x, y, z)
  | fuseAddMulToMac    -- z + (x * y) ↦ mac(x, y, z)
  | factorRightDistrib -- u + u ↦ 2 * u
  | constFoldAdd       -- const(a) + const(b) ↦ const(a + b)
  | constFoldMul       -- const(a) * const(b) ↦ const(a * b)
  deriving DecidableEq, Repr

/-- Derive an algebraically equivalent `HyperENode` from `n` in `classes` under rule `r`. -/
def deriveRuleNode? (r : EqSatRule) (classes : List EClass) (n : HyperENode) : Option HyperENode :=
  match r with
  | .scaleOneElim =>
    match matchUnaryScale n with
    | some (k, u) =>
      if k == 1 then firstNode? (findClassNodes classes u) else none
    | none => none
  | .scaleZeroElim =>
    match matchUnaryScale n with
    | some (k, _) =>
      if k == 0 then some ⟨.const 0, []⟩ else none
    | none => none
  | .scaleFuse =>
    match matchUnaryScale n with
    | some (k1, u) =>
      match findScaleInNodes (findClassNodes classes u) with
      | some (k2, w) => some ⟨.scale (k1 * k2), [w]⟩
      | none => none
    | none => none
  | .addZeroRight =>
    match matchBinaryAdd n with
    | some (u, v) =>
      match findConstInNodes (findClassNodes classes v) with
      | some c => if c == 0 then some ⟨.scale 1, [u]⟩ else none
      | none => none
    | none => none
  | .addZeroLeft =>
    match matchBinaryAdd n with
    | some (u, v) =>
      match findConstInNodes (findClassNodes classes u) with
      | some c => if c == 0 then some ⟨.scale 1, [v]⟩ else none
      | none => none
    | none => none
  | .addComm =>
    match matchBinaryAdd n with
    | some (u, v) => some ⟨.add, [v, u]⟩
    | none => none
  | .mulComm =>
    match matchBinaryMul n with
    | some (u, v) => some ⟨.mul, [v, u]⟩
    | none => none
  | .mulOneRight =>
    match matchBinaryMul n with
    | some (u, v) =>
      match findScaleInNodes (findClassNodes classes v) with
      | some (k, w) => if k == 1 then some ⟨.mul, [u, w]⟩ else none
      | none =>
        match findConstInNodes (findClassNodes classes v) with
        | some c => if c == 1 then some ⟨.scale 1, [u]⟩ else none
        | none => none
    | none => none
  | .mulZeroRight =>
    match matchBinaryMul n with
    | some (_, v) =>
      match findConstInNodes (findClassNodes classes v) with
      | some c => if c == 0 then some ⟨.const 0, []⟩ else none
      | none => none
    | none => none
  | .subSelfZero =>
    match matchBinarySub n with
    | some (u, v) => if u == v then some ⟨.const 0, []⟩ else none
    | none => none
  | .addNegScaleToSub =>
    match matchBinaryAdd n with
    | some (u, v) =>
      match findScaleInNodes (findClassNodes classes v) with
      | some (k, w) => if k == -1 then some ⟨.sub, [u, w]⟩ else none
      | none => none
    | none => none
  | .fuseMulAddToMac =>
    match matchBinaryAdd n with
    | some (u, z) =>
      match findMulInNodes (findClassNodes classes u) with
      | some (x, y) => some ⟨.mac, [x, y, z]⟩
      | none => none
    | none => none
  | .fuseAddMulToMac =>
    match matchBinaryAdd n with
    | some (z, u) =>
      match findMulInNodes (findClassNodes classes u) with
      | some (x, y) => some ⟨.mac, [x, y, z]⟩
      | none => none
    | none => none
  | .factorRightDistrib =>
    match matchBinaryAdd n with
    | some (u, v) => if u == v then some ⟨.scale 2, [u]⟩ else none
    | none => none
  | .constFoldAdd =>
    match matchBinaryAdd n with
    | some (u, v) =>
      match findConstInNodes (findClassNodes classes u) with
      | some a =>
        match findConstInNodes (findClassNodes classes v) with
        | some b => some ⟨.const (a + b), []⟩
        | none => none
      | none => none
    | none => none
  | .constFoldMul =>
    match matchBinaryMul n with
    | some (u, v) =>
      match findConstInNodes (findClassNodes classes u) with
      | some a =>
        match findConstInNodes (findClassNodes classes v) with
        | some b => some ⟨.const (a * b), []⟩
        | none => none
      | none => none
    | none => none

/-- **Lemma (`deriveRuleNode?_sound`)**:
For every rule `r : EqSatRule` and consistent E-Graph `eg`, if `deriveRuleNode? r eg.classes n = some n'`,
then `evalENode env n' = evalENode env n`. -/
theorem deriveRuleNode?_sound
    (r : EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (n n' : HyperENode)
    (hDerive : deriveRuleNode? r eg.classes n = some n') :
    evalENode env n' = evalENode env n := by
  cases r with
  | scaleOneElim =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k, u⟩
      simp only [hm] at hDerive
      cases hk : (k == 1)
      · simp [hk] at hDerive
      · simp only [hk, ↓reduceIte] at hDerive
        have hkEq : k = 1 := LawfulBEq.eq_of_beq hk
        have hnVal := matchUnaryScale_sound env n k u hm
        have hn'Val := firstNode?_sound eg env hCons u n' hDerive
        rw [hn'Val, hnVal, hkEq, Int.one_mul]
  | scaleZeroElim =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k, u⟩
      simp only [hm] at hDerive
      cases hk : (k == 0)
      · simp [hk] at hDerive
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
        have hkEq : k = 0 := LawfulBEq.eq_of_beq hk
        have hnVal := matchUnaryScale_sound env n k u hm
        subst hDerive
        rw [hnVal, hkEq]
        dsimp [evalENode, evalHypergraphOp]
        omega
  | scaleFuse =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k1, u⟩
      simp only [hm] at hDerive
      cases hf : findScaleInNodes (findClassNodes eg.classes u) with
      | none => simp [hf] at hDerive
      | some kw =>
        rcases kw with ⟨k2, w⟩
        simp only [hf, Option.some.injEq] at hDerive
        have hnVal := matchUnaryScale_sound env n k1 u hm
        have huVal := findScaleInNodes_sound eg env hCons u k2 w hf
        subst hDerive
        rw [hnVal, huVal]
        dsimp [evalENode, evalHypergraphOp]
        exact Int.mul_assoc k1 k2 (env w)
  | addZeroRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes eg.classes v) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          have hcEq : c = 0 := LawfulBEq.eq_of_beq hc
          have hnVal := matchBinaryAdd_sound env n u v hm
          have hvVal := findConstInNodes_sound eg env hCons v c hf
          subst hDerive
          rw [hnVal, hvVal, hcEq]
          dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
          omega
  | addZeroLeft =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes eg.classes u) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          have hcEq : c = 0 := LawfulBEq.eq_of_beq hc
          have hnVal := matchBinaryAdd_sound env n u v hm
          have huVal := findConstInNodes_sound eg env hCons u c hf
          subst hDerive
          rw [hnVal, huVal, hcEq]
          dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
          omega
  | addComm =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm, Option.some.injEq] at hDerive
      have hnVal := matchBinaryAdd_sound env n u v hm
      subst hDerive
      rw [hnVal]
      dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
      omega
  | mulComm =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm, Option.some.injEq] at hDerive
      have hnVal := matchBinaryMul_sound env n u v hm
      subst hDerive
      rw [hnVal]
      dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
      exact Int.mul_comm (env v) (env u)
  | mulOneRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      have hnVal := matchBinaryMul_sound env n u v hm
      cases hs : findScaleInNodes (findClassNodes eg.classes v) with
      | some kw =>
        rcases kw with ⟨k, w⟩
        simp only [hs] at hDerive
        cases hk : (k == 1)
        · simp [hk] at hDerive
        · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
          have hkEq : k = 1 := LawfulBEq.eq_of_beq hk
          have hvVal := findScaleInNodes_sound eg env hCons v k w hs
          subst hDerive
          rw [hnVal, hvVal, hkEq, Int.one_mul]
          rfl
      | none =>
        simp only [hs] at hDerive
        cases hcFind : findConstInNodes (findClassNodes eg.classes v) with
        | none => simp [hcFind] at hDerive
        | some c =>
          simp only [hcFind] at hDerive
          cases hc : (c == 1)
          · simp [hc] at hDerive
          · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
            have hcEq : c = 1 := LawfulBEq.eq_of_beq hc
            have hvVal := findConstInNodes_sound eg env hCons v c hcFind
            subst hDerive
            rw [hnVal, hvVal, hcEq]
            dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
            omega
  | mulZeroRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes eg.classes v) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          have hcEq : c = 0 := LawfulBEq.eq_of_beq hc
          have hnVal := matchBinaryMul_sound env n u v hm
          have hvVal := findConstInNodes_sound eg env hCons v c hf
          subst hDerive
          rw [hnVal, hvVal, hcEq, Int.mul_zero]
          rfl
  | subSelfZero =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinarySub n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases huv : (u == v)
      · simp [huv] at hDerive
      · simp only [huv, ↓reduceIte, Option.some.injEq] at hDerive
        have huvEq : u = v := LawfulBEq.eq_of_beq huv
        have hnVal := matchBinarySub_sound env n u v hm
        subst hDerive
        rw [hnVal, huvEq]
        dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
        omega
  | addNegScaleToSub =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findScaleInNodes (findClassNodes eg.classes v) with
      | none => simp [hf] at hDerive
      | some kw =>
        rcases kw with ⟨k, w⟩
        simp only [hf] at hDerive
        cases hk : (k == -1)
        · simp [hk] at hDerive
        · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
          have hkEq : k = -1 := LawfulBEq.eq_of_beq hk
          have hnVal := matchBinaryAdd_sound env n u v hm
          have hvVal := findScaleInNodes_sound eg env hCons v k w hf
          subst hDerive
          rw [hnVal, hvVal, hkEq]
          dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
          omega
  | fuseMulAddToMac =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uz =>
      rcases uz with ⟨u, z⟩
      simp only [hm] at hDerive
      cases hf : findMulInNodes (findClassNodes eg.classes u) with
      | none => simp [hf] at hDerive
      | some xy =>
        rcases xy with ⟨x, y⟩
        simp only [hf, Option.some.injEq] at hDerive
        have hnVal := matchBinaryAdd_sound env n u z hm
        have huVal := findMulInNodes_sound eg env hCons u x y hf
        subst hDerive
        rw [hnVal, huVal]
        rfl
  | fuseAddMulToMac =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some zu =>
      rcases zu with ⟨z, u⟩
      simp only [hm] at hDerive
      cases hf : findMulInNodes (findClassNodes eg.classes u) with
      | none => simp [hf] at hDerive
      | some xy =>
        rcases xy with ⟨x, y⟩
        simp only [hf, Option.some.injEq] at hDerive
        have hnVal := matchBinaryAdd_sound env n z u hm
        have huVal := findMulInNodes_sound eg env hCons u x y hf
        subst hDerive
        rw [hnVal, huVal]
        dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
        omega
  | factorRightDistrib =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases huv : (u == v)
      · simp [huv] at hDerive
      · simp only [huv, ↓reduceIte, Option.some.injEq] at hDerive
        have huvEq : u = v := LawfulBEq.eq_of_beq huv
        have hnVal := matchBinaryAdd_sound env n u v hm
        subst hDerive
        rw [hnVal, huvEq]
        dsimp [evalENode, evalHypergraphOp, List.map, List.getD]
        omega
  | constFoldAdd =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hfa : findConstInNodes (findClassNodes eg.classes u) with
      | none => simp [hfa] at hDerive
      | some a =>
        simp only [hfa] at hDerive
        cases hfb : findConstInNodes (findClassNodes eg.classes v) with
        | none => simp [hfb] at hDerive
        | some b =>
          simp only [hfb, Option.some.injEq] at hDerive
          have hnVal := matchBinaryAdd_sound env n u v hm
          have huVal := findConstInNodes_sound eg env hCons u a hfa
          have hvVal := findConstInNodes_sound eg env hCons v b hfb
          subst hDerive
          rw [hnVal, huVal, hvVal]
          rfl
  | constFoldMul =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hfa : findConstInNodes (findClassNodes eg.classes u) with
      | none => simp [hfa] at hDerive
      | some a =>
        simp only [hfa] at hDerive
        cases hfb : findConstInNodes (findClassNodes eg.classes v) with
        | none => simp [hfb] at hDerive
        | some b =>
          simp only [hfb, Option.some.injEq] at hDerive
          have hnVal := matchBinaryMul_sound env n u v hm
          have huVal := findConstInNodes_sound eg env hCons u a hfa
          have hvVal := findConstInNodes_sound eg env hCons v b hfb
          subst hDerive
          rw [hnVal, huVal, hvVal]
          rfl

/-- Expand a class's `nodes` list with any newly derived equivalent `HyperENode`s under rule `r`. -/
def HypergraphOp.beq : HypergraphOp → HypergraphOp → Bool
  | .const a, .const b => a == b
  | .add, .add => true
  | .sub, .sub => true
  | .mul, .mul => true
  | .scale a, .scale b => a == b
  | .mac, .mac => true
  | .mux, .mux => true
  | _, _ => false

def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && natListBeq xs ys
  | _, _ => false

def HyperENode.beq (a b : HyperENode) : Bool :=
  HypergraphOp.beq a.op b.op && natListBeq a.children b.children

def expandClassNodes (r : EqSatRule) (classes : List EClass) : List HyperENode → List HyperENode
  | [] => []
  | n :: rest =>
    match deriveRuleNode? r classes n with
    | none    => n :: expandClassNodes r classes rest
    | some n' =>
      if HyperENode.beq n' n then n :: expandClassNodes r classes rest
      else n :: n' :: expandClassNodes r classes rest

theorem expandClassNodes_sound
    (r : EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (targetVal : Int) (nodes : List HyperENode)
    (hNodes : ∀ n ∈ nodes, evalENode env n = targetVal) :
    ∀ m ∈ expandClassNodes r eg.classes nodes, evalENode env m = targetVal := by
  induction nodes with
  | nil =>
    intro m hm
    contradiction
  | cons n rest ih =>
    have hnVal : evalENode env n = targetVal := hNodes n List.mem_cons_self
    have hRest : ∀ m ∈ expandClassNodes r eg.classes rest, evalENode env m = targetVal :=
      ih (fun n0 hn0 => hNodes n0 (List.mem_cons_of_mem n hn0))
    intro m hm
    unfold expandClassNodes at hm
    cases hDerive : deriveRuleNode? r eg.classes n with
    | none =>
      simp only [hDerive, List.mem_cons] at hm
      rcases hm with rfl | hmRest
      · exact hnVal
      · exact hRest m hmRest
    | some n' =>
      simp only [hDerive] at hm
      have hn'Val : evalENode env n' = targetVal := by
        rw [deriveRuleNode?_sound r eg env hCons n n' hDerive]
        exact hnVal
      cases hEq : HyperENode.beq n' n
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hm
        rcases hm with rfl | rfl | hmRest
        · exact hnVal
        · exact hn'Val
        · exact hRest m hmRest
      · simp only [hEq, ↓reduceIte, List.mem_cons] at hm
        rcases hm with rfl | hmRest
        · exact hnVal
        · exact hRest m hmRest

/-- Apply a single equality-saturation rule `r : EqSatRule` across all E-Classes of `eg`. -/
def applyEqSatRule (r : EqSatRule) (eg : HyperEGraph) : HyperEGraph :=
  { eg with
    classes := eg.classes.map fun c =>
      { c with nodes := expandClassNodes r eg.classes c.nodes } }

/-- **Theorem (`applyEqSatRule_preserves_consistency`)**:
Applying any `r : EqSatRule` to a semantically consistent `HyperEGraph` preserves `EGraphConsistent`. -/
theorem applyEqSatRule_preserves_consistency
    (r : EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env) :
    EGraphConsistent (applyEqSatRule r eg) env := by
  intro c' hc' m hm
  unfold applyEqSatRule at hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, hcMem, rfl⟩ := hc'
  exact expandClassNodes_sound r eg env hCons (env c.classId) c.nodes (hCons c hcMem) m hm

/-- Apply a list of `EqSatRule`s sequentially in one saturation sweep. -/
def applyEqSatRules (rules : List EqSatRule) (eg : HyperEGraph) : HyperEGraph :=
  rules.foldl (fun cur r => applyEqSatRule r cur) eg

theorem applyEqSatRules_preserves_consistency
    (rules : List EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env) :
    EGraphConsistent (applyEqSatRules rules eg) env := by
  induction rules generalizing eg with
  | nil => exact hCons
  | cons r rest ih =>
    unfold applyEqSatRules
    simp only [List.foldl_cons]
    exact ih (applyEqSatRule r eg) (applyEqSatRule_preserves_consistency r eg env hCons)

/-- Run `fuel` passes of equality saturation over `eg` with `rules`. -/
def saturateHyperEGraph : Nat → List EqSatRule → HyperEGraph → HyperEGraph
  | 0, _, eg => eg
  | fuel + 1, rules, eg =>
    saturateHyperEGraph fuel rules (applyEqSatRules rules eg)

/-- **Theorem (`saturateHyperEGraph_preserves_consistency`)**:
Running `saturateHyperEGraph fuel rules eg` for any number of passes `fuel` and any rule list `rules`
preserves `EGraphConsistent`. -/
theorem saturateHyperEGraph_preserves_consistency
    (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env) :
    EGraphConsistent (saturateHyperEGraph fuel rules eg) env := by
  induction fuel generalizing eg with
  | zero => exact hCons
  | succ k ih =>
    unfold saturateHyperEGraph
    exact ih (applyEqSatRules rules eg) (applyEqSatRules_preserves_consistency rules eg env hCons)

/-- Canonical reverse-mode AD cotangent algebraic rule suite (`defaultAdjointEqSatRules`). -/
def defaultAdjointEqSatRules : List EqSatRule :=
  [ .scaleOneElim
  , .scaleZeroElim
  , .scaleFuse
  , .addZeroRight
  , .addZeroLeft
  , .mulOneRight
  , .mulZeroRight
  , .subSelfZero
  , .addNegScaleToSub
  , .fuseMulAddToMac
  , .fuseAddMulToMac
  , .factorRightDistrib
  , .constFoldAdd
  , .constFoldMul ]

/-- Automatic equality-saturation pass tailored for reverse-mode AD cotangent hypergraphs
(applying `.mulOneRight` wire-forwarding, `.scaleFuse` linear cotangent fusion, and `.fuseAddMulToMac`
multiply-accumulate cotangent fanout fusion). -/
def autoSaturateCotangentPass (eg : HyperEGraph) : HyperEGraph :=
  saturateHyperEGraph 1 [ .mulOneRight, .scaleFuse, .fuseAddMulToMac ] eg

theorem autoSaturateCotangentPass_preserves_consistency
    (eg : HyperEGraph) (env : EClassId → Int) (hCons : EGraphConsistent eg env) :
    EGraphConsistent (autoSaturateCotangentPass eg) env :=
  saturateHyperEGraph_preserves_consistency 1 [ .mulOneRight, .scaleFuse, .fuseAddMulToMac ] eg env hCons

/-! ## 4. Clairvoyant Cost-Optimal Extraction & Dead-Cotangent Pruning (`extractMinCostHypergraph`, `optimizeAdjointHypergraph`) -/

/-- Hardware / RTL operation cost model assigning a non-negative gate/area weight to each `HypergraphOp`. -/
structure HyperCostModel where
  opCost : HypergraphOp → Nat

/-- Default RTL silicon area/delay cost model:
* `.const _`: cost `1`
* `.scale k`: cost `2`
* `.add`, `.sub`: cost `3`
* `.mac`: cost `3` (single-cycle DSP / VOP3 fused multiply-accumulate slice, strictly cheaper than separate `.mul` + `.add` = `6 + 3 = 9`!)
* `.mux`: cost `4`
* `.mul`: cost `6` -/
def defaultRtlCostModel : HyperCostModel where
  opCost
    | .const _ => 1
    | .scale _ => 2
    | .add     => 3
    | .sub     => 3
    | .mux     => 4
    | .mac     => 3
    | .mul     => 6

/-- Sum the operation costs of a list of `HyperEdge`s under `costModel`. -/
def evalEdgesCost (costModel : HyperCostModel) : List HyperEdge → Nat
  | [] => 0
  | e :: rest => costModel.opCost e.op + evalEdgesCost costModel rest

@[simp] theorem evalEdgesCost_reindexHyperEdgesAux
    (costModel : HyperCostModel) (idx : Nat) (edges : List HyperEdge) :
    evalEdgesCost costModel (reindexHyperEdgesAux idx edges) = evalEdgesCost costModel edges := by
  induction edges generalizing idx with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨_, op, srcWires, dstWire⟩
    simp [reindexHyperEdgesAux, evalEdgesCost, ih (idx + 1)]

@[simp] theorem evalEdgesCost_reindexHyperEdges
    (costModel : HyperCostModel) (edges : List HyperEdge) :
    evalEdgesCost costModel (reindexHyperEdges edges) = evalEdgesCost costModel edges :=
  evalEdgesCost_reindexHyperEdgesAux costModel 0 edges

/-- Total RTL operation cost of a `StrictOpenHypergraph` `g` under `costModel`. -/
def evalHypergraphCost (costModel : HyperCostModel) (g : StrictOpenHypergraph) : Nat :=
  evalEdgesCost costModel (extractHyperEdges g)

/-- Select the minimum-cost `HyperENode` from `nodes` starting from `best` (preferring newly
derived nodes on cost ties `≤` so wire-forwarding rewrites like `.mulOneRight` take effect). -/
def pickMinCostNode (costModel : HyperCostModel) (best : HyperENode) : List HyperENode → HyperENode
  | [] => best
  | n :: rest =>
    let best' := if costModel.opCost n.op ≤ costModel.opCost best.op then n else best
    pickMinCostNode costModel best' rest

theorem pickMinCostNode_cost_le
    (costModel : HyperCostModel) (best : HyperENode) (nodes : List HyperENode) :
    costModel.opCost (pickMinCostNode costModel best nodes).op ≤ costModel.opCost best.op := by
  induction nodes generalizing best with
  | nil => exact Nat.le_refl _
  | cons n rest ih =>
    unfold pickMinCostNode
    by_cases hle : costModel.opCost n.op ≤ costModel.opCost best.op
    · simp only [hle, ↓reduceIte]
      exact Nat.le_trans (ih n) hle
    · simp only [hle, ↓reduceIte]
      exact ih best

/-- Extract the minimum-cost `HyperEdge` for a single `EClass` `c`. -/
def extractClassEdge (costModel : HyperCostModel) (c : EClass) : HyperEdge :=
  let best := pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes
  { opIdx    := c.origEdge.opIdx
  , op       := best.op
  , srcWires := best.children
  , dstWire  := c.classId }

theorem extractClassEdge_cost_le (costModel : HyperCostModel) (c : EClass) :
    costModel.opCost (extractClassEdge costModel c).op ≤ costModel.opCost c.origEdge.op := by
  unfold extractClassEdge edgeToENode
  exact pickMinCostNode_cost_le costModel { op := c.origEdge.op, children := c.origEdge.srcWires } c.nodes

theorem evalEdgesCost_extractClassEdges_le
    (costModel : HyperCostModel) (classes : List EClass) :
    evalEdgesCost costModel (classes.map (extractClassEdge costModel)) ≤
      evalEdgesCost costModel (classes.map (·.origEdge)) := by
  induction classes with
  | nil => exact Nat.le_refl 0
  | cons c rest ih =>
    simp only [List.map_cons, evalEdgesCost]
    have hHead := extractClassEdge_cost_le costModel c
    omega

/-- Backward liveness pass pruning dead hyperedges whose `dstWire` is never read by any downstream
live hyperedge or `boundaryOut`. -/
def pruneDeadEdgesAux (liveWires : List Nat) : List HyperEdge → List Nat × List HyperEdge
  | [] => (liveWires, [])
  | e :: rest =>
    match pruneDeadEdgesAux liveWires rest with
    | (liveAfter, keptRest) =>
      if liveAfter.contains e.dstWire then
        (e.srcWires ++ liveAfter, e :: keptRest)
      else
        (liveAfter, keptRest)

/-- Prune dead hyperedges not contributing to `boundaryOut`. -/
def pruneDeadEdges (boundaryOut : List Nat) (edges : List HyperEdge) : List HyperEdge :=
  (pruneDeadEdgesAux boundaryOut edges).2

theorem evalEdgesCost_pruneDeadEdgesAux_le
    (costModel : HyperCostModel) (liveWires : List Nat) (edges : List HyperEdge) :
    evalEdgesCost costModel (pruneDeadEdgesAux liveWires edges).2 ≤ evalEdgesCost costModel edges := by
  induction edges with
  | nil => exact Nat.le_refl 0
  | cons e rest ih =>
    unfold pruneDeadEdgesAux
    cases hRec : pruneDeadEdgesAux liveWires rest with
    | mk liveAfter keptRest =>
      rw [hRec] at ih
      dsimp at ih ⊢
      cases liveAfter.contains e.dstWire
      · simp only [Bool.false_eq_true, ↓reduceIte, evalEdgesCost]
        omega
      · simp only [↓reduceIte, evalEdgesCost]
        omega

theorem evalEdgesCost_pruneDeadEdges_le
    (costModel : HyperCostModel) (boundaryOut : List Nat) (edges : List HyperEdge) :
    evalEdgesCost costModel (pruneDeadEdges boundaryOut edges) ≤ evalEdgesCost costModel edges :=
  evalEdgesCost_pruneDeadEdgesAux_le costModel boundaryOut edges

/-- Extract the minimum-cost `StrictOpenHypergraph` from a saturated `HyperEGraph` `eg` under `costModel`. -/
def extractMinCostHypergraph (costModel : HyperCostModel) (eg : HyperEGraph) : StrictOpenHypergraph :=
  let selectedEdges := eg.classes.map (extractClassEdge costModel)
  let liveEdges     := pruneDeadEdges eg.boundaryOut selectedEdges
  mkStrictOpenHypergraph eg.numWires eg.boundaryIn eg.boundaryOut (reindexHyperEdges liveEdges)

/-- Optimize the whole-graph reverse-mode adjoint `compileGraphAdjoint g` via equality saturation
and minimum-cost extraction. -/
def optimizeAdjointHypergraph (costModel : HyperCostModel) (g : StrictOpenHypergraph) : StrictOpenHypergraph :=
  let gAdj := compileGraphAdjoint g
  let eg0  := hypergraphToEGraph gAdj
  let egSat := autoSaturateCotangentPass eg0
  extractMinCostHypergraph costModel egSat

/-! ## 5. Universal Cost Monotonicity & Strict Cost Reduction Theorems -/

@[simp] theorem applyEqSatRule_origEdges (r : EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRule r eg).classes.map (·.origEdge) = eg.classes.map (·.origEdge) := by
  unfold applyEqSatRule
  simp [List.map_map]

@[simp] theorem applyEqSatRules_origEdges (rules : List EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRules rules eg).classes.map (·.origEdge) = eg.classes.map (·.origEdge) := by
  induction rules generalizing eg with
  | nil => rfl
  | cons r rest ih =>
    rw [applyEqSatRules, List.foldl_cons, ← applyEqSatRules, ih, applyEqSatRule_origEdges]

@[simp] theorem saturateHyperEGraph_origEdges (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph) :
    (saturateHyperEGraph fuel rules eg).classes.map (·.origEdge) = eg.classes.map (·.origEdge) := by
  induction fuel generalizing eg with
  | zero => rfl
  | succ k ih =>
    unfold saturateHyperEGraph
    rw [ih, applyEqSatRules_origEdges]

theorem map_edgeToEClass_origEdge (edges : List HyperEdge) :
    (edges.map edgeToEClass).map (·.origEdge) = edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, edgeToEClass, ih]

@[simp] theorem hypergraphToEGraph_origEdges (g : StrictOpenHypergraph) :
    (hypergraphToEGraph g).classes.map (·.origEdge) = extractHyperEdges g :=
  map_edgeToEClass_origEdge (extractHyperEdges g)

/-- **Theorem (`extractMinCost_improves_cost`)**:
For EVERY `g : StrictOpenHypergraph`, `costModel : HyperCostModel`, saturation depth `fuel : Nat`,
and rule suite `rules : List EqSatRule`, extracting the minimum-cost hypergraph after equality
saturation never increases the hardware cost:
$$\text{evalHypergraphCost}(\text{extractMinCostHypergraph}(\text{saturateHyperEGraph}(g))) \le \text{evalHypergraphCost}(g)$$ -/
theorem extractMinCost_improves_cost
    (costModel : HyperCostModel) (g : StrictOpenHypergraph) (fuel : Nat) (rules : List EqSatRule) :
    evalHypergraphCost costModel
      (extractMinCostHypergraph costModel
        (saturateHyperEGraph fuel rules (hypergraphToEGraph g))) ≤
      evalHypergraphCost costModel g := by
  unfold evalHypergraphCost extractMinCostHypergraph
  rw [extractHyperEdges_mkStrictOpenHypergraph, evalEdgesCost_reindexHyperEdges]
  have hPrune := evalEdgesCost_pruneDeadEdges_le costModel
    (saturateHyperEGraph fuel rules (hypergraphToEGraph g)).boundaryOut
    ((saturateHyperEGraph fuel rules (hypergraphToEGraph g)).classes.map (extractClassEdge costModel))
  have hSelect := evalEdgesCost_extractClassEdges_le costModel
    (saturateHyperEGraph fuel rules (hypergraphToEGraph g)).classes
  rw [saturateHyperEGraph_origEdges, hypergraphToEGraph_origEdges] at hSelect
  exact Nat.le_trans hPrune hSelect

/-! ## 5B. Universal Acyclic Hypergraph Extraction Soundness (`extractMinCostHypergraph_sound`, `saturate_and_extract_preserves_eval`) -/

/-- Acyclic / topological DAG invariant for a list of `HyperEdge`s with respect to wire rank `rank : Nat → Nat`:
1. Every hyperedge `e` reads strictly lower-ranked source wires (`∀ w ∈ e.srcWires, rank w < rank e.dstWire`),
2. Output wires appear in strictly increasing topological rank order
   (`List.Pairwise (fun e1 e2 => rank e1.dstWire < rank e2.dstWire) edges`). -/
def EdgesTopological (rank : Nat → Nat) (edges : List HyperEdge) : Prop :=
  (∀ e ∈ edges, ∀ w ∈ e.srcWires, rank w < rank e.dstWire) ∧
  List.Pairwise (fun e1 e2 => rank e1.dstWire < rank e2.dstWire) edges

/-- Acyclic / topological DAG invariant for a `HyperEGraph` `eg` with respect to wire rank `rank : Nat → Nat`:
1. Every E-Class `c ∈ eg.classes` retains its seed node `edgeToENode c.origEdge ∈ c.nodes` and `c.origEdge.dstWire = c.classId`,
2. Every child wire `w ∈ n.children` of every candidate node `n ∈ c.nodes` has strictly smaller topological
   rank than `c.classId` (`rank w < rank c.classId`),
3. E-Classes appear in strictly increasing topological rank order
   (`List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) eg.classes`). -/
def EGraphTopological (rank : Nat → Nat) (eg : HyperEGraph) : Prop :=
  (∀ c ∈ eg.classes,
    c.origEdge.dstWire = c.classId ∧
    edgeToENode c.origEdge ∈ c.nodes ∧
    (∀ n ∈ c.nodes, ∀ w ∈ n.children, rank w < rank c.classId)) ∧
  List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) eg.classes

/-- Computable topological SSA checker verifying strictly increasing output wire IDs and `w < e.dstWire`
on all source wires (`rank := id`). -/
def checkEdgesTopologicalAux : Option Nat → List HyperEdge → Bool
  | _, [] => true
  | none, e :: rest =>
    e.srcWires.all (fun w => decide (w < e.dstWire)) &&
    checkEdgesTopologicalAux (some e.dstWire) rest
  | some prevDst, e :: rest =>
    decide (prevDst < e.dstWire) &&
    e.srcWires.all (fun w => decide (w < e.dstWire)) &&
    checkEdgesTopologicalAux (some e.dstWire) rest

/-- Computable topological SSA well-formedness check for a `StrictOpenHypergraph`. -/
def checkHypergraphTopologicalSSA (g : StrictOpenHypergraph) : Bool :=
  checkEdgesTopologicalAux none (extractHyperEdges g)

private theorem checkEdgesTopologicalAux_lower (prev : Nat) (edges : List HyperEdge)
    (h : checkEdgesTopologicalAux (some prev) edges = true) :
    (∀ e ∈ edges, prev < e.dstWire ∧ ∀ w ∈ e.srcWires, w < e.dstWire) ∧
    List.Pairwise (fun e1 e2 => e1.dstWire < e2.dstWire) edges := by
  induction edges generalizing prev with
  | nil => exact ⟨(fun _ hm => nomatch hm), List.Pairwise.nil⟩
  | cons e rest ih =>
    unfold checkEdgesTopologicalAux at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hPrev, hSrc⟩, hRest⟩
    obtain ⟨hRestAll, hRestPair⟩ := ih e.dstWire hRest
    refine ⟨?_, List.Pairwise.cons ?_ hRestPair⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | hMem
      · exact ⟨hPrev, hSrc⟩
      · obtain ⟨hGt, hSrc'⟩ := hRestAll e' hMem
        exact ⟨Nat.lt_trans hPrev hGt, hSrc'⟩
    · intro e' he'
      exact (hRestAll e' he').1

theorem checkHypergraphTopologicalSSA_sound (g : StrictOpenHypergraph)
    (h : checkHypergraphTopologicalSSA g = true) :
    EdgesTopological id (extractHyperEdges g) := by
  unfold checkHypergraphTopologicalSSA at h
  cases edges : extractHyperEdges g with
  | nil => exact ⟨(fun _ hm => nomatch hm), List.Pairwise.nil⟩
  | cons e rest =>
    rw [edges] at h
    unfold checkEdgesTopologicalAux at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hSrc, hRest⟩
    obtain ⟨hRestAll, hRestPair⟩ := checkEdgesTopologicalAux_lower e.dstWire rest hRest
    refine ⟨?_, List.Pairwise.cons ?_ hRestPair⟩
    · intro e' he' w hw
      rcases List.mem_cons.mp he' with rfl | hMem
      · exact hSrc w hw
      · exact (hRestAll e' hMem).2 w hw
    · intro e' he'
      exact (hRestAll e' he').1

private theorem map_eq_of_forall_mem {α β : Type} (f g : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.map f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem evalENode_congr {env1 env2 : EClassId → Int} {n : HyperENode}
    (h : ∀ w ∈ n.children, env1 w = env2 w) :
    evalENode env1 n = evalENode env2 n := by
  unfold evalENode
  rw [map_eq_of_forall_mem env1 env2 n.children h]

private theorem stepHyperEdge_self (env : Nat → Int) (e : HyperEdge) :
    stepHyperEdge env e e.dstWire = evalENode env (edgeToENode e) := by
  unfold stepHyperEdge evalENode edgeToENode
  simp

private theorem stepHyperEdge_ne (env : Nat → Int) (e : HyperEdge) (w : Nat)
    (hne : w ≠ e.dstWire) :
    stepHyperEdge env e w = env w := by
  unfold stepHyperEdge
  cases hbeq : (w == e.dstWire)
  · rfl
  · exact absurd (LawfulBEq.eq_of_beq hbeq) hne

theorem evalHyperEdgesComb_preserve_unwritten
    (env : Nat → Int) (edges : List HyperEdge) (w : Nat)
    (hUnwritten : ∀ e ∈ edges, w ≠ e.dstWire) :
    evalHyperEdgesComb env edges w = env w := by
  induction edges generalizing env with
  | nil => rfl
  | cons e rest ih =>
    unfold evalHyperEdgesComb
    simp only [List.foldl_cons]
    change evalHyperEdgesComb (stepHyperEdge env e) rest w = env w
    rw [ih (stepHyperEdge env e) (fun e' he' => hUnwritten e' (List.mem_cons_of_mem e he'))]
    exact stepHyperEdge_ne env e w (hUnwritten e List.mem_cons_self)

theorem evalHyperEdgesComb_edge_consistent
    (rank : Nat → Nat) (edges : List HyperEdge) (initEnv : Nat → Int)
    (hTopo : EdgesTopological rank edges) :
    ∀ e ∈ edges,
      evalENode (evalHyperEdgesComb initEnv edges) (edgeToENode e) =
        evalHyperEdgesComb initEnv edges e.dstWire := by
  induction edges generalizing initEnv with
  | nil =>
    intro _ he
    nomatch he
  | cons e0 rest ih =>
    rcases hTopo with ⟨hSrc, hPair⟩
    cases hPair with
    | cons hHeadLt hRestPair =>
      have hRestTopo : EdgesTopological rank rest :=
        ⟨fun e' he' => hSrc e' (List.mem_cons_of_mem e0 he'), hRestPair⟩
      intro e he
      unfold evalHyperEdgesComb
      simp only [List.foldl_cons]
      change evalENode (evalHyperEdgesComb (stepHyperEdge initEnv e0) rest) (edgeToENode e) =
        evalHyperEdgesComb (stepHyperEdge initEnv e0) rest e.dstWire
      rcases List.mem_cons.mp he with rfl | heRest
      · have hDstUnwritten : ∀ e' ∈ rest, e.dstWire ≠ e'.dstWire := by
          intro e' he' hEq
          have hLt := hHeadLt e' he'
          rw [hEq] at hLt
          exact Nat.lt_irrefl _ hLt
        have hDstPres :
            evalHyperEdgesComb (stepHyperEdge initEnv e) rest e.dstWire =
              evalENode initEnv (edgeToENode e) := by
          rw [evalHyperEdgesComb_preserve_unwritten (stepHyperEdge initEnv e) rest e.dstWire hDstUnwritten]
          exact stepHyperEdge_self initEnv e
        have hChildrenPres :
            ∀ w ∈ (edgeToENode e).children,
              evalHyperEdgesComb (stepHyperEdge initEnv e) rest w = initEnv w := by
          intro w hw
          have hwRank : rank w < rank e.dstWire := hSrc e List.mem_cons_self w hw
          have hwNeSelf : w ≠ e.dstWire := by
            intro hEq
            rw [hEq] at hwRank
            exact Nat.lt_irrefl _ hwRank
          have hwUnwritten : ∀ e' ∈ rest, w ≠ e'.dstWire := by
            intro e' he' hEq
            have hLt := Nat.lt_trans hwRank (hHeadLt e' he')
            rw [hEq] at hLt
            exact Nat.lt_irrefl _ hLt
          rw [evalHyperEdgesComb_preserve_unwritten (stepHyperEdge initEnv e) rest w hwUnwritten]
          exact stepHyperEdge_ne initEnv e w hwNeSelf
        rw [evalENode_congr hChildrenPres, hDstPres]
      · exact ih (stepHyperEdge initEnv e0) hRestTopo e heRest

private theorem pairwise_map_edgeToEClass (rank : Nat → Nat) (edges : List HyperEdge)
    (hp : List.Pairwise (fun e1 e2 => rank e1.dstWire < rank e2.dstWire) edges) :
    List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) (edges.map edgeToEClass) := by
  induction hp with
  | nil => exact List.Pairwise.nil
  | @cons e rest hHead _ ih =>
    simp only [List.map_cons]
    refine List.Pairwise.cons ?_ ih
    intro c' hc'
    rw [List.mem_map] at hc'
    obtain ⟨e', he', rfl⟩ := hc'
    exact hHead e' he'

/-- **Seed Consistency Theorem (`hypergraphToEGraph_consistent`)**:
For every topologically ordered `StrictOpenHypergraph` `g` and initial valuation `initEnv`,
`hypergraphToEGraph g` is semantically consistent with `evalHyperEdgesComb initEnv (extractHyperEdges g)`. -/
theorem hypergraphToEGraph_consistent
    (rank : Nat → Nat) (g : StrictOpenHypergraph) (initEnv : Nat → Int)
    (hTopo : EdgesTopological rank (extractHyperEdges g)) :
    EGraphConsistent (hypergraphToEGraph g) (evalHyperEdgesComb initEnv (extractHyperEdges g)) := by
  intro c hc n hn
  unfold hypergraphToEGraph at hc
  simp only [List.mem_map] at hc
  obtain ⟨e, heMem, rfl⟩ := hc
  unfold edgeToEClass at hn ⊢
  simp only [List.mem_singleton] at hn
  subst hn
  exact evalHyperEdgesComb_edge_consistent rank (extractHyperEdges g) initEnv hTopo e heMem

/-- **Seed Topological Invariant (`hypergraphToEGraph_topological`)**:
Lifting a topologically ordered `StrictOpenHypergraph` `g` produces an `EGraphTopological` E-Graph. -/
theorem hypergraphToEGraph_topological
    (rank : Nat → Nat) (g : StrictOpenHypergraph)
    (hTopo : EdgesTopological rank (extractHyperEdges g)) :
    EGraphTopological rank (hypergraphToEGraph g) := by
  rcases hTopo with ⟨hSrc, hPair⟩
  refine ⟨?_, pairwise_map_edgeToEClass rank (extractHyperEdges g) hPair⟩
  intro c hc
  unfold hypergraphToEGraph at hc
  simp only [List.mem_map] at hc
  obtain ⟨e, heMem, rfl⟩ := hc
  refine ⟨rfl, List.mem_cons_self, ?_⟩
  intro n hn w hw
  unfold edgeToEClass at hn
  simp only [List.mem_singleton] at hn
  subst hn
  exact hSrc e heMem w hw

theorem hypergraphToEGraph_unwritten
    (g : StrictOpenHypergraph) (initEnv : Nat → Int) (w : Nat)
    (hNoClass : ∀ c ∈ (hypergraphToEGraph g).classes, c.classId ≠ w) :
    evalHyperEdgesComb initEnv (extractHyperEdges g) w = initEnv w := by
  refine evalHyperEdgesComb_preserve_unwritten initEnv (extractHyperEdges g) w ?_
  intro e he hEq
  have hcMem : edgeToEClass e ∈ (hypergraphToEGraph g).classes := by
    unfold hypergraphToEGraph
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  exact hNoClass (edgeToEClass e) hcMem hEq.symm

private theorem matchUnaryScale_mem {n : HyperENode} {k : Int} {u : EClassId}
    (h : matchUnaryScale n = some (k, u)) : u ∈ n.children := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | _⟩ <;> try contradiction
  simp only [matchUnaryScale, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact List.mem_cons_self

private theorem matchBinaryAdd_mem {n : HyperENode} {u v : EClassId}
    (h : matchBinaryAdd n = some (u, v)) : u ∈ n.children ∧ v ∈ n.children := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinaryAdd, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem matchBinarySub_mem {n : HyperENode} {u v : EClassId}
    (h : matchBinarySub n = some (u, v)) : u ∈ n.children ∧ v ∈ n.children := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinarySub, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem matchBinaryMul_mem {n : HyperENode} {u v : EClassId}
    (h : matchBinaryMul n = some (u, v)) : u ∈ n.children ∧ v ∈ n.children := by
  rcases n with ⟨op, children⟩
  cases op <;> try contradiction
  rcases children with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩ <;> try contradiction
  simp only [matchBinaryMul, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem mem_findClassNodes_rank
    (rank : Nat → Nat) (classes : List EClass)
    (hClasses : ∀ c0 ∈ classes, ∀ m ∈ c0.nodes, ∀ w ∈ m.children, rank w < rank c0.classId)
    (u : EClassId) (m : HyperENode)
    (hMem : m ∈ findClassNodes classes u) :
    ∀ w ∈ m.children, rank w < rank u := by
  induction classes with
  | nil => contradiction
  | cons c0 rest ih =>
    unfold findClassNodes at hMem
    cases hcu : (c0.classId == u)
    · simp only [hcu, Bool.false_eq_true, ↓reduceIte] at hMem
      exact ih (fun c' hc' => hClasses c' (List.mem_cons_of_mem c0 hc')) hMem
    · simp only [hcu, ↓reduceIte] at hMem
      have hEq : c0.classId = u := LawfulBEq.eq_of_beq hcu
      intro w hw
      rw [← hEq]
      exact hClasses c0 List.mem_cons_self m hMem w hw

private theorem findScaleInNodes_mem_node :
    ∀ (nodes : List HyperENode) (k : Int) (w : EClassId),
      findScaleInNodes nodes = some (k, w) → ∃ m ∈ nodes, w ∈ m.children
  | [], _, _, h => by contradiction
  | m :: rest, k, w, h => by
    unfold findScaleInNodes at h
    cases hm : matchUnaryScale m with
    | some kw =>
      rcases kw with ⟨k0, w0⟩
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨m, List.mem_cons_self, matchUnaryScale_mem hm⟩
    | none =>
      simp only [hm] at h
      obtain ⟨m', hm', hw'⟩ := findScaleInNodes_mem_node rest k w h
      exact ⟨m', List.mem_cons_of_mem m hm', hw'⟩

private theorem findMulInNodes_mem_node :
    ∀ (nodes : List HyperENode) (x y : EClassId),
      findMulInNodes nodes = some (x, y) → ∃ m ∈ nodes, x ∈ m.children ∧ y ∈ m.children
  | [], _, _, h => by contradiction
  | m :: rest, x, y, h => by
    unfold findMulInNodes at h
    cases hm : matchBinaryMul m with
    | some xy =>
      rcases xy with ⟨x0, y0⟩
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨m, List.mem_cons_self, matchBinaryMul_mem hm⟩
    | none =>
      simp only [hm] at h
      obtain ⟨m', hm', hx', hy'⟩ := findMulInNodes_mem_node rest x y h
      exact ⟨m', List.mem_cons_of_mem m hm', hx', hy'⟩

/-- **Rule Acyclicity Preservation (`deriveRuleNode?_preserves_rank`)**:
Every algebraic/cotangent rule in `EqSatRule` preserves strict topological child rank ordering. -/
theorem deriveRuleNode?_preserves_rank
    (rank : Nat → Nat) (r : EqSatRule) (classes : List EClass)
    (hClasses : ∀ c0 ∈ classes, ∀ m ∈ c0.nodes, ∀ w ∈ m.children, rank w < rank c0.classId)
    (targetRank : Nat) (n n' : HyperENode)
    (hnRank : ∀ w ∈ n.children, rank w < targetRank)
    (hDerive : deriveRuleNode? r classes n = some n') :
    ∀ w ∈ n'.children, rank w < targetRank := by
  cases r with
  | scaleOneElim =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k, u⟩
      simp only [hm] at hDerive
      cases hk : (k == 1)
      · simp [hk] at hDerive
      · simp only [hk, ↓reduceIte] at hDerive
        intro w hw
        exact Nat.lt_trans
          (mem_findClassNodes_rank rank classes hClasses u n' (firstNode?_mem hDerive) w hw)
          (hnRank u (matchUnaryScale_mem hm))
  | scaleZeroElim =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k, _⟩
      simp only [hm] at hDerive
      cases hk : (k == 0)
      · simp [hk] at hDerive
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
        subst hDerive
        intro _ hw
        nomatch hw
  | scaleFuse =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchUnaryScale n with
    | none => simp [hm] at hDerive
    | some ku =>
      rcases ku with ⟨k1, u⟩
      simp only [hm] at hDerive
      cases hf : findScaleInNodes (findClassNodes classes u) with
      | none => simp [hf] at hDerive
      | some kw =>
        rcases kw with ⟨k2, w0⟩
        simp only [hf, Option.some.injEq] at hDerive
        subst hDerive
        obtain ⟨m, hmMem, hw0Mem⟩ := findScaleInNodes_mem_node _ k2 w0 hf
        intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact Nat.lt_trans
          (mem_findClassNodes_rank rank classes hClasses u m hmMem w hw0Mem)
          (hnRank u (matchUnaryScale_mem hm))
  | addZeroRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes classes v) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          subst hDerive
          intro w hw
          simp only [List.mem_singleton] at hw
          subst hw
          exact hnRank w (matchBinaryAdd_mem hm).1
  | addZeroLeft =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes classes u) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          subst hDerive
          intro w hw
          simp only [List.mem_singleton] at hw
          subst hw
          exact hnRank w (matchBinaryAdd_mem hm).2
  | addComm =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm, Option.some.injEq] at hDerive
      subst hDerive
      obtain ⟨hu, hv⟩ := matchBinaryAdd_mem hm
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw1
      · exact hnRank w hv
      · simp only [List.mem_singleton] at hw1
        subst hw1
        exact hnRank w hu
  | mulComm =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm, Option.some.injEq] at hDerive
      subst hDerive
      obtain ⟨hu, hv⟩ := matchBinaryMul_mem hm
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw1
      · exact hnRank w hv
      · simp only [List.mem_singleton] at hw1
        subst hw1
        exact hnRank w hu
  | mulOneRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      obtain ⟨hu, hv⟩ := matchBinaryMul_mem hm
      cases hs : findScaleInNodes (findClassNodes classes v) with
      | some kw =>
        rcases kw with ⟨k, w0⟩
        simp only [hs] at hDerive
        cases hk : (k == 1)
        · simp [hk] at hDerive
        · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
          subst hDerive
          obtain ⟨m, hmMem, hw0Mem⟩ := findScaleInNodes_mem_node _ k w0 hs
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw1
          · exact hnRank w hu
          · simp only [List.mem_singleton] at hw1
            subst hw1
            exact Nat.lt_trans
              (mem_findClassNodes_rank rank classes hClasses v m hmMem w hw0Mem)
              (hnRank v hv)
      | none =>
        simp only [hs] at hDerive
        cases hcFind : findConstInNodes (findClassNodes classes v) with
        | none => simp [hcFind] at hDerive
        | some c =>
          simp only [hcFind] at hDerive
          cases hc : (c == 1)
          · simp [hc] at hDerive
          · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
            subst hDerive
            intro w hw
            simp only [List.mem_singleton] at hw
            subst hw
            exact hnRank w hu
  | mulZeroRight =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨_, v⟩
      simp only [hm] at hDerive
      cases hf : findConstInNodes (findClassNodes classes v) with
      | none => simp [hf] at hDerive
      | some c =>
        simp only [hf] at hDerive
        cases hc : (c == 0)
        · simp [hc] at hDerive
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hDerive
          subst hDerive
          intro _ hw
          nomatch hw
  | subSelfZero =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinarySub n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases huv : (u == v)
      · simp [huv] at hDerive
      · simp only [huv, ↓reduceIte, Option.some.injEq] at hDerive
        subst hDerive
        intro _ hw
        nomatch hw
  | addNegScaleToSub =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      obtain ⟨hu, hv⟩ := matchBinaryAdd_mem hm
      cases hf : findScaleInNodes (findClassNodes classes v) with
      | none => simp [hf] at hDerive
      | some kw =>
        rcases kw with ⟨k, w0⟩
        simp only [hf] at hDerive
        cases hk : (k == -1)
        · simp [hk] at hDerive
        · simp only [hk, ↓reduceIte, Option.some.injEq] at hDerive
          subst hDerive
          obtain ⟨m, hmMem, hw0Mem⟩ := findScaleInNodes_mem_node _ k w0 hf
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw1
          · exact hnRank w hu
          · simp only [List.mem_singleton] at hw1
            subst hw1
            exact Nat.lt_trans
              (mem_findClassNodes_rank rank classes hClasses v m hmMem w hw0Mem)
              (hnRank v hv)
  | fuseMulAddToMac =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uz =>
      rcases uz with ⟨u, z⟩
      simp only [hm] at hDerive
      obtain ⟨hu, hz⟩ := matchBinaryAdd_mem hm
      cases hf : findMulInNodes (findClassNodes classes u) with
      | none => simp [hf] at hDerive
      | some xy =>
        rcases xy with ⟨x, y⟩
        simp only [hf, Option.some.injEq] at hDerive
        subst hDerive
        obtain ⟨m, hmMem, hxMem, hyMem⟩ := findMulInNodes_mem_node _ x y hf
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw1
        · exact Nat.lt_trans
            (mem_findClassNodes_rank rank classes hClasses u m hmMem w hxMem)
            (hnRank u hu)
        · rcases List.mem_cons.mp hw1 with rfl | hw2
          · exact Nat.lt_trans
              (mem_findClassNodes_rank rank classes hClasses u m hmMem w hyMem)
              (hnRank u hu)
          · simp only [List.mem_singleton] at hw2
            subst hw2
            exact hnRank w hz
  | fuseAddMulToMac =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some zu =>
      rcases zu with ⟨z, u⟩
      simp only [hm] at hDerive
      obtain ⟨hz, hu⟩ := matchBinaryAdd_mem hm
      cases hf : findMulInNodes (findClassNodes classes u) with
      | none => simp [hf] at hDerive
      | some xy =>
        rcases xy with ⟨x, y⟩
        simp only [hf, Option.some.injEq] at hDerive
        subst hDerive
        obtain ⟨m, hmMem, hxMem, hyMem⟩ := findMulInNodes_mem_node _ x y hf
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw1
        · exact Nat.lt_trans
            (mem_findClassNodes_rank rank classes hClasses u m hmMem w hxMem)
            (hnRank u hu)
        · rcases List.mem_cons.mp hw1 with rfl | hw2
          · exact Nat.lt_trans
              (mem_findClassNodes_rank rank classes hClasses u m hmMem w hyMem)
              (hnRank u hu)
          · simp only [List.mem_singleton] at hw2
            subst hw2
            exact hnRank w hz
  | factorRightDistrib =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases huv : (u == v)
      · simp [huv] at hDerive
      · simp only [huv, ↓reduceIte, Option.some.injEq] at hDerive
        subst hDerive
        intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact hnRank w (matchBinaryAdd_mem hm).1
  | constFoldAdd =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryAdd n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hfa : findConstInNodes (findClassNodes classes u) with
      | none => simp [hfa] at hDerive
      | some _ =>
        simp only [hfa] at hDerive
        cases hfb : findConstInNodes (findClassNodes classes v) with
        | none => simp [hfb] at hDerive
        | some _ =>
          simp only [hfb, Option.some.injEq] at hDerive
          subst hDerive
          intro _ hw
          nomatch hw
  | constFoldMul =>
    unfold deriveRuleNode? at hDerive
    cases hm : matchBinaryMul n with
    | none => simp [hm] at hDerive
    | some uv =>
      rcases uv with ⟨u, v⟩
      simp only [hm] at hDerive
      cases hfa : findConstInNodes (findClassNodes classes u) with
      | none => simp [hfa] at hDerive
      | some _ =>
        simp only [hfa] at hDerive
        cases hfb : findConstInNodes (findClassNodes classes v) with
        | none => simp [hfb] at hDerive
        | some _ =>
          simp only [hfb, Option.some.injEq] at hDerive
          subst hDerive
          intro _ hw
          nomatch hw

theorem mem_expandClassNodes_of_mem
    (r : EqSatRule) (classes : List EClass) (nodes : List HyperENode)
    {m : HyperENode} (hm : m ∈ nodes) :
    m ∈ expandClassNodes r classes nodes := by
  induction nodes with
  | nil => nomatch hm
  | cons n rest ih =>
    unfold expandClassNodes
    rcases List.mem_cons.mp hm with rfl | hmRest
    · cases hDerive : deriveRuleNode? r classes m with
      | none => simp [hDerive]
      | some n' =>
        cases hEq : HyperENode.beq n' m <;> simp [hDerive, hEq]
    · cases hDerive : deriveRuleNode? r classes n with
      | none =>
        simp only [hDerive]
        exact List.mem_cons_of_mem n (ih hmRest)
      | some n' =>
        simp only [hDerive]
        cases hEq : HyperENode.beq n' n
        · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
          exact List.mem_cons_of_mem n (List.mem_cons_of_mem n' (ih hmRest))
        · simp only [hEq, ↓reduceIte]
          exact List.mem_cons_of_mem n (ih hmRest)

theorem expandClassNodes_preserves_rank
    (rank : Nat → Nat) (r : EqSatRule) (classes : List EClass)
    (hClasses : ∀ c0 ∈ classes, ∀ m ∈ c0.nodes, ∀ w ∈ m.children, rank w < rank c0.classId)
    (targetRank : Nat) (nodes : List HyperENode)
    (hNodes : ∀ n ∈ nodes, ∀ w ∈ n.children, rank w < targetRank) :
    ∀ m ∈ expandClassNodes r classes nodes, ∀ w ∈ m.children, rank w < targetRank := by
  induction nodes with
  | nil =>
    intro _ hm
    contradiction
  | cons n rest ih =>
    have hnRank : ∀ w ∈ n.children, rank w < targetRank := hNodes n List.mem_cons_self
    have hRest : ∀ m ∈ expandClassNodes r classes rest, ∀ w ∈ m.children, rank w < targetRank :=
      ih (fun n0 hn0 => hNodes n0 (List.mem_cons_of_mem n hn0))
    intro m hm
    unfold expandClassNodes at hm
    cases hDerive : deriveRuleNode? r classes n with
    | none =>
      simp only [hDerive, List.mem_cons] at hm
      rcases hm with rfl | hmRest
      · exact hnRank
      · exact hRest m hmRest
    | some n' =>
      simp only [hDerive] at hm
      have hn'Rank := deriveRuleNode?_preserves_rank rank r classes hClasses targetRank n n' hnRank hDerive
      cases hEq : HyperENode.beq n' n
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hm
        rcases hm with rfl | rfl | hmRest
        · exact hnRank
        · exact hn'Rank
        · exact hRest m hmRest
      · simp only [hEq, ↓reduceIte, List.mem_cons] at hm
        rcases hm with rfl | hmRest
        · exact hnRank
        · exact hRest m hmRest

private theorem pairwise_map_preserve_classId (rank : Nat → Nat) (f : EClass → EClass)
    (hf : ∀ c, (f c).classId = c.classId) (classes : List EClass)
    (hp : List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) classes) :
    List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) (classes.map f) := by
  induction hp with
  | nil => exact List.Pairwise.nil
  | @cons c rest hHead _ ih =>
    simp only [List.map_cons]
    refine List.Pairwise.cons ?_ ih
    intro c' hc'
    rw [List.mem_map] at hc'
    obtain ⟨c0, hc0, rfl⟩ := hc'
    rw [hf c, hf c0]
    exact hHead c0 hc0

theorem applyEqSatRule_preserves_topological
    (rank : Nat → Nat) (r : EqSatRule) (eg : HyperEGraph)
    (hTopo : EGraphTopological rank eg) :
    EGraphTopological rank (applyEqSatRule r eg) := by
  rcases hTopo with ⟨hClasses, hPair⟩
  have hNodesRank : ∀ c0 ∈ eg.classes, ∀ m ∈ c0.nodes, ∀ w ∈ m.children, rank w < rank c0.classId :=
    fun c0 hc0 => (hClasses c0 hc0).2.2
  refine ⟨?_, pairwise_map_preserve_classId rank
    (fun c => { c with nodes := expandClassNodes r eg.classes c.nodes })
    (fun _ => rfl) eg.classes hPair⟩
  intro c' hc'
  unfold applyEqSatRule at hc'
  simp only [List.mem_map] at hc'
  obtain ⟨c, hcMem, rfl⟩ := hc'
  obtain ⟨hOrigDst, hOrigMem, hcRank⟩ := hClasses c hcMem
  refine ⟨hOrigDst, mem_expandClassNodes_of_mem r eg.classes c.nodes hOrigMem, ?_⟩
  exact expandClassNodes_preserves_rank rank r eg.classes hNodesRank (rank c.classId) c.nodes hcRank

theorem applyEqSatRules_preserves_topological
    (rank : Nat → Nat) (rules : List EqSatRule) (eg : HyperEGraph)
    (hTopo : EGraphTopological rank eg) :
    EGraphTopological rank (applyEqSatRules rules eg) := by
  induction rules generalizing eg with
  | nil => exact hTopo
  | cons r rest ih =>
    unfold applyEqSatRules
    simp only [List.foldl_cons]
    exact ih (applyEqSatRule r eg) (applyEqSatRule_preserves_topological rank r eg hTopo)

theorem saturateHyperEGraph_preserves_topological
    (rank : Nat → Nat) (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph)
    (hTopo : EGraphTopological rank eg) :
    EGraphTopological rank (saturateHyperEGraph fuel rules eg) := by
  induction fuel generalizing eg with
  | zero => exact hTopo
  | succ k ih =>
    unfold saturateHyperEGraph
    exact ih (applyEqSatRules rules eg) (applyEqSatRules_preserves_topological rank rules eg hTopo)

@[simp] theorem applyEqSatRule_classIds (r : EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRule r eg).classes.map (·.classId) = eg.classes.map (·.classId) := by
  unfold applyEqSatRule
  simp [List.map_map]

@[simp] theorem applyEqSatRules_classIds (rules : List EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRules rules eg).classes.map (·.classId) = eg.classes.map (·.classId) := by
  induction rules generalizing eg with
  | nil => rfl
  | cons r rest ih =>
    rw [applyEqSatRules, List.foldl_cons, ← applyEqSatRules, ih, applyEqSatRule_classIds]

@[simp] theorem saturateHyperEGraph_classIds (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph) :
    (saturateHyperEGraph fuel rules eg).classes.map (·.classId) = eg.classes.map (·.classId) := by
  induction fuel generalizing eg with
  | zero => rfl
  | succ k ih =>
    unfold saturateHyperEGraph
    rw [ih, applyEqSatRules_classIds]

@[simp] theorem applyEqSatRule_boundaryOut (r : EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRule r eg).boundaryOut = eg.boundaryOut := rfl

@[simp] theorem applyEqSatRules_boundaryOut (rules : List EqSatRule) (eg : HyperEGraph) :
    (applyEqSatRules rules eg).boundaryOut = eg.boundaryOut := by
  induction rules generalizing eg with
  | nil => rfl
  | cons r rest ih =>
    rw [applyEqSatRules, List.foldl_cons, ← applyEqSatRules, ih, applyEqSatRule_boundaryOut]

@[simp] theorem saturateHyperEGraph_boundaryOut (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph) :
    (saturateHyperEGraph fuel rules eg).boundaryOut = eg.boundaryOut := by
  induction fuel generalizing eg with
  | zero => rfl
  | succ k ih =>
    unfold saturateHyperEGraph
    rw [ih, applyEqSatRules_boundaryOut]

theorem pickMinCostNode_mem
    (costModel : HyperCostModel) (best : HyperENode) (nodes : List HyperENode) :
    pickMinCostNode costModel best nodes ∈ best :: nodes := by
  induction nodes generalizing best with
  | nil => exact List.mem_cons_self
  | cons n rest ih =>
    unfold pickMinCostNode
    by_cases hle : costModel.opCost n.op ≤ costModel.opCost best.op
    · simp only [hle, ↓reduceIte]
      exact List.mem_cons_of_mem best (ih n)
    · simp only [hle, ↓reduceIte]
      rcases List.mem_cons.mp (ih best) with hEq | hMemRest
      · rw [hEq]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem n hMemRest)

private theorem evalHyperEdgesComb_extractClassEdgesAux
    (rank : Nat → Nat) (costModel : HyperCostModel) (finalEnv : Nat → Int)
    (todo : List EClass)
    (hTodoEval : ∀ c ∈ todo,
      evalENode finalEnv (pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes) = finalEnv c.classId)
    (hTodoRank : ∀ c ∈ todo,
      ∀ w ∈ (pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes).children, rank w < rank c.classId)
    (hTodoPair : List.Pairwise (fun c1 c2 => rank c1.classId < rank c2.classId) todo)
    (curEnv : Nat → Int)
    (hAgree : ∀ w, (∀ c ∈ todo, c.classId ≠ w) → curEnv w = finalEnv w) :
    ∀ w, evalHyperEdgesComb curEnv (todo.map (extractClassEdge costModel)) w = finalEnv w := by
  induction todo generalizing curEnv with
  | nil =>
    intro w
    exact hAgree w (fun _ hm => nomatch hm)
  | cons c rest ih =>
    cases hTodoPair with
    | cons hHeadLt hRestPair =>
      let best := pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes
      let ec := extractClassEdge costModel c
      have hChildrenAgree : ∀ u ∈ best.children, curEnv u = finalEnv u := by
        intro u hu
        have huRank : rank u < rank c.classId := hTodoRank c List.mem_cons_self u hu
        refine hAgree u ?_
        intro c' hc' hEq
        rcases List.mem_cons.mp hc' with rfl | hc'Rest
        · rw [hEq] at huRank
          exact Nat.lt_irrefl _ huRank
        · have hLt := Nat.lt_trans huRank (hHeadLt c' hc'Rest)
          rw [hEq] at hLt
          exact Nat.lt_irrefl _ hLt
      have hBestEval : evalENode curEnv best = finalEnv c.classId := by
        rw [evalENode_congr hChildrenAgree]
        exact hTodoEval c List.mem_cons_self
      have hStepAgree : ∀ w, (∀ c' ∈ rest, c'.classId ≠ w) → stepHyperEdge curEnv ec w = finalEnv w := by
        intro w hwRest
        by_cases hwc : w = c.classId
        · subst hwc
          have hSelf : stepHyperEdge curEnv ec c.classId = evalENode curEnv best := by
            change stepHyperEdge curEnv ec ec.dstWire = evalENode curEnv (edgeToENode ec)
            exact stepHyperEdge_self curEnv ec
          rw [hSelf, hBestEval]
        · have hStepNe : stepHyperEdge curEnv ec w = curEnv w :=
            stepHyperEdge_ne curEnv ec w hwc
          rw [hStepNe]
          refine hAgree w ?_
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'Rest
          · exact Ne.symm hwc
          · exact hwRest c' hc'Rest
      intro w
      simp only [List.map_cons, evalHyperEdgesComb, List.foldl_cons]
      exact ih
        (fun c' hc' => hTodoEval c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hTodoRank c' (List.mem_cons_of_mem c hc'))
        hRestPair
        (stepHyperEdge curEnv ec)
        hStepAgree
        w

theorem evalHyperEdgesComb_extractClassEdges_eq
    (rank : Nat → Nat) (costModel : HyperCostModel) (eg : HyperEGraph)
    (initEnv finalEnv : Nat → Int)
    (hCons : EGraphConsistent eg finalEnv)
    (hTopo : EGraphTopological rank eg)
    (hUnwritten : ∀ w, (∀ c ∈ eg.classes, c.classId ≠ w) → finalEnv w = initEnv w) :
    ∀ w, evalHyperEdgesComb initEnv (eg.classes.map (extractClassEdge costModel)) w = finalEnv w := by
  rcases hTopo with ⟨hClasses, hPair⟩
  refine evalHyperEdgesComb_extractClassEdgesAux rank costModel finalEnv eg.classes ?_ ?_ hPair initEnv ?_
  · intro c hc
    have hBestMem : pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes ∈ c.nodes := by
      rcases List.mem_cons.mp (pickMinCostNode_mem costModel (edgeToENode c.origEdge) c.nodes) with hEq | hIn
      · rw [hEq]
        exact (hClasses c hc).2.1
      · exact hIn
    exact hCons c hc _ hBestMem
  · intro c hc w hw
    have hBestMem : pickMinCostNode costModel (edgeToENode c.origEdge) c.nodes ∈ c.nodes := by
      rcases List.mem_cons.mp (pickMinCostNode_mem costModel (edgeToENode c.origEdge) c.nodes) with hEq | hIn
      · rw [hEq]
        exact (hClasses c hc).2.1
      · exact hIn
    exact (hClasses c hc).2.2 _ hBestMem w hw
  · intro w hw
    exact (hUnwritten w hw).symm

private theorem ne_of_contains_false {xs : List Nat} {x y : Nat}
    (hFalse : xs.contains x = false) (hMem : y ∈ xs) : y ≠ x := by
  induction xs with
  | nil => nomatch hMem
  | cons z zs ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hFalse
    rcases List.mem_cons.mp hMem with rfl | hMemRest
    · intro hEq
      subst hEq
      have hSelf : (y == y) = true := beq_iff_eq.mpr rfl
      rw [hSelf] at hFalse
      exact Bool.noConfusion hFalse.1
    · exact ih hFalse.2 hMemRest

/-- **Backward Liveness Dead-Edge Pruning Soundness (`evalHyperEdgesComb_pruneDeadEdgesAux_eq`)**:
For EVERY `List HyperEdge` and wire valuations `env1, env2` agreeing on the backward-live input set
`(pruneDeadEdgesAux liveWires edges).1`, evaluating the pruned edge list `(pruneDeadEdgesAux liveWires edges).2`
from `env1` agrees identically on all `w ∈ liveWires` with evaluating the full `edges` list from `env2`. -/
theorem evalHyperEdgesComb_pruneDeadEdgesAux_eq
    (liveWires : List Nat) (edges : List HyperEdge) (env1 env2 : Nat → Int)
    (hAgree : ∀ w ∈ (pruneDeadEdgesAux liveWires edges).1, env1 w = env2 w) :
    ∀ w ∈ liveWires,
      evalHyperEdgesComb env1 (pruneDeadEdgesAux liveWires edges).2 w =
        evalHyperEdgesComb env2 edges w := by
  induction edges generalizing env1 env2 with
  | nil =>
    intro w hw
    exact hAgree w hw
  | cons e rest ih =>
    unfold pruneDeadEdgesAux at hAgree ⊢
    cases hRec : pruneDeadEdgesAux liveWires rest with
    | mk liveAfter keptRest =>
      rw [hRec] at hAgree
      dsimp only at hAgree ⊢
      cases hCont : liveAfter.contains e.dstWire
      · simp only [hCont, Bool.false_eq_true, ↓reduceIte] at hAgree ⊢
        have hStepAgree : ∀ u ∈ liveAfter, env1 u = stepHyperEdge env2 e u := by
          intro u hu
          have hNe : u ≠ e.dstWire := ne_of_contains_false hCont hu
          rw [stepHyperEdge_ne env2 e u hNe]
          exact hAgree u hu
        have hSub := ih env1 (stepHyperEdge env2 e) (by rw [hRec]; exact hStepAgree)
        rw [hRec] at hSub
        exact hSub
      · simp only [hCont, ↓reduceIte] at hAgree ⊢
        have hStepAgree : ∀ u ∈ liveAfter, stepHyperEdge env1 e u = stepHyperEdge env2 e u := by
          intro u hu
          by_cases hEq : u = e.dstWire
          · subst hEq
            rw [stepHyperEdge_self, stepHyperEdge_self]
            exact evalENode_congr (fun s (hs : s ∈ e.srcWires) =>
              hAgree s (List.mem_append.mpr (Or.inl hs)))
          · rw [stepHyperEdge_ne env1 e u hEq, stepHyperEdge_ne env2 e u hEq]
            exact hAgree u (List.mem_append.mpr (Or.inr hu))
        have hSub := ih (stepHyperEdge env1 e) (stepHyperEdge env2 e) (by rw [hRec]; exact hStepAgree)
        rw [hRec] at hSub
        exact hSub

/-- **Dead-Edge Pruning Soundness (`pruneDeadEdges_sound`)**:
Pruning dead hyperedges preserves combinational evaluation on all `boundaryOut` wires for EVERY `List HyperEdge`. -/
theorem pruneDeadEdges_sound
    (boundaryOut : List Nat) (edges : List HyperEdge) (initEnv : Nat → Int) :
    boundaryOut.map (evalHyperEdgesComb initEnv (pruneDeadEdges boundaryOut edges)) =
      boundaryOut.map (evalHyperEdgesComb initEnv edges) := by
  refine map_eq_of_forall_mem _ _ boundaryOut ?_
  exact evalHyperEdgesComb_pruneDeadEdgesAux_eq boundaryOut edges initEnv initEnv (fun _ _ => rfl)

/-- **Universal E-Graph Minimum-Cost Extraction Soundness (`extractMinCostHypergraph_sound`)**:
For EVERY `eg : HyperEGraph` that is semantically consistent (`EGraphConsistent eg finalEnv`) and
topologically acyclic (`EGraphTopological rank eg`), extracting the minimum-cost `StrictOpenHypergraph`
under ANY `costModel : HyperCostModel` evaluates identically to `eg.boundaryOut.map finalEnv`! -/
theorem extractMinCostHypergraph_sound
    (rank : Nat → Nat) (costModel : HyperCostModel) (eg : HyperEGraph)
    (initEnv finalEnv : Nat → Int)
    (hCons : EGraphConsistent eg finalEnv)
    (hTopo : EGraphTopological rank eg)
    (hUnwritten : ∀ w, (∀ c ∈ eg.classes, c.classId ≠ w) → finalEnv w = initEnv w) :
    evalHypergraphComb (extractMinCostHypergraph costModel eg) initEnv =
      eg.boundaryOut.map finalEnv := by
  unfold extractMinCostHypergraph
  rw [evalHypergraphComb_mkStrictOpenHypergraph_reindex, pruneDeadEdges_sound]
  exact map_eq_of_forall_mem _ _ eg.boundaryOut fun w _ =>
    evalHyperEdgesComb_extractClassEdges_eq rank costModel eg initEnv finalEnv hCons hTopo hUnwritten w

/-- **Universal Acyclic Hypergraph Equality-Saturation & Extraction Soundness (`saturate_and_extract_preserves_eval`)**:
For **EVERY** topologically acyclic `g : StrictOpenHypergraph` (`EdgesTopological rank (extractHyperEdges g)`),
**EVERY** `costModel : HyperCostModel`, **EVERY** saturation depth `fuel : Nat`, **EVERY** rule list
`rules : List EqSatRule`, and **EVERY** wire valuation `initEnv : Nat → Int`:
$$\text{evalHypergraphComb}(\text{extractMinCostHypergraph}(\text{saturateHyperEGraph}(g)), \text{initEnv}) = \text{evalHypergraphComb}(g, \text{initEnv}).$$ -/
theorem saturate_and_extract_preserves_eval
    (rank : Nat → Nat) (costModel : HyperCostModel) (g : StrictOpenHypergraph)
    (fuel : Nat) (rules : List EqSatRule) (initEnv : Nat → Int)
    (hTopo : EdgesTopological rank (extractHyperEdges g)) :
    evalHypergraphComb
      (extractMinCostHypergraph costModel
        (saturateHyperEGraph fuel rules (hypergraphToEGraph g)))
      initEnv =
    evalHypergraphComb g initEnv := by
  let finalEnv := evalHyperEdgesComb initEnv (extractHyperEdges g)
  have hSeedCons : EGraphConsistent (hypergraphToEGraph g) finalEnv :=
    hypergraphToEGraph_consistent rank g initEnv hTopo
  have hSeedTopo : EGraphTopological rank (hypergraphToEGraph g) :=
    hypergraphToEGraph_topological rank g hTopo
  have hSatCons : EGraphConsistent (saturateHyperEGraph fuel rules (hypergraphToEGraph g)) finalEnv :=
    saturateHyperEGraph_preserves_consistency fuel rules (hypergraphToEGraph g) finalEnv hSeedCons
  have hSatTopo : EGraphTopological rank (saturateHyperEGraph fuel rules (hypergraphToEGraph g)) :=
    saturateHyperEGraph_preserves_topological rank fuel rules (hypergraphToEGraph g) hSeedTopo
  have hSatUnwritten :
      ∀ w, (∀ c ∈ (saturateHyperEGraph fuel rules (hypergraphToEGraph g)).classes, c.classId ≠ w) →
        finalEnv w = initEnv w := by
    intro w hw
    refine hypergraphToEGraph_unwritten g initEnv w ?_
    intro c hc hEq
    have hIdMem : c.classId ∈ (hypergraphToEGraph g).classes.map (·.classId) :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    rw [← saturateHyperEGraph_classIds fuel rules (hypergraphToEGraph g), List.mem_map] at hIdMem
    obtain ⟨c', hc'Mem, hc'Id⟩ := hIdMem
    exact hw c' hc'Mem (hc'Id.trans hEq)
  rw [extractMinCostHypergraph_sound rank costModel
        (saturateHyperEGraph fuel rules (hypergraphToEGraph g))
        initEnv finalEnv hSatCons hSatTopo hSatUnwritten]
  rw [saturateHyperEGraph_boundaryOut]
  rfl

/-- Computable-guard corollary (`saturate_and_extract_preserves_eval_ssa`):
Whenever `checkHypergraphTopologicalSSA g = true`, equality saturation + minimum-cost extraction
preserves `evalHypergraphComb` across all `costModel`, `fuel`, `rules`, and `initEnv`. -/
theorem saturate_and_extract_preserves_eval_ssa
    (costModel : HyperCostModel) (g : StrictOpenHypergraph)
    (fuel : Nat) (rules : List EqSatRule) (initEnv : Nat → Int)
    (hCheck : checkHypergraphTopologicalSSA g = true) :
    evalHypergraphComb
      (extractMinCostHypergraph costModel
        (saturateHyperEGraph fuel rules (hypergraphToEGraph g)))
      initEnv =
    evalHypergraphComb g initEnv :=
  saturate_and_extract_preserves_eval id costModel g fuel rules initEnv
    (checkHypergraphTopologicalSSA_sound g hCheck)

/-- Universal soundness of `optimizeAdjointHypergraph` (`optimizeAdjointHypergraph_sound_universal`):
For EVERY `g : StrictOpenHypergraph` whose reverse-mode adjoint `compileGraphAdjoint g` passes
`checkHypergraphTopologicalSSA`, `optimizeAdjointHypergraph costModel g` evaluates identically to
`compileGraphAdjoint g` on ALL wire assignments `initEnv : Nat → Int`. -/
theorem optimizeAdjointHypergraph_sound_universal
    (costModel : HyperCostModel) (g : StrictOpenHypergraph) (initEnv : Nat → Int)
    (hCheck : checkHypergraphTopologicalSSA (compileGraphAdjoint g) = true) :
    evalHypergraphComb (optimizeAdjointHypergraph costModel g) initEnv =
      evalHypergraphComb (compileGraphAdjoint g) initEnv :=
  saturate_and_extract_preserves_eval_ssa costModel (compileGraphAdjoint g)
    1 [ .mulOneRight, .scaleFuse, .fuseAddMulToMac ] initEnv hCheck

/-- **Theorem (`goldenDiamondAdjoint_eqSat_strict_cost_reduction`)**:
On `compileGraphAdjoint goldenDiamondHypergraph` ($f(x_0, x_1, x_2, x_3) = (x_0 + x_1)(x_2 + x_3) + 10$),
`optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph`:
1. Strictly reduces the hardware RTL cost (`36 < 40`) and reduces the hyperedge count from `13` to `11`
   (bypassing wire `10` via `.mulOneRight` and eliminating both redundant `.scale 1` cotangent edges on
   wires `10` and `11`),
2. Preserves structural well-formedness (`wf = true`),
3. Preserves exact combinational, sequential wavefront, and synchronous wavefront evaluation
   (`[87, 11, 11, 7, 7]` at `(3, 4, 5, 6)` with `dOut = 1`)! -/
theorem goldenDiamondAdjoint_eqSat_strict_cost_reduction :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0
    evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
    (extractHyperEdges gOpt).length < (extractHyperEdges gAdj).length ∧
    (extractHyperEdges gOpt).length = 11 ∧
    (extractHyperEdges gAdj).length = 13 ∧
    gOpt.wf = true ∧
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env = [87, 11, 11, 7, 7] ∧
    evalHypergraphLayeredSync gOpt env = [87, 11, 11, 7, 7] := by
  decide +kernel

/-- Explicit 13-edge list of `compileGraphAdjoint goldenDiamondHypergraph`. -/
def goldenDiamondAdjEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .add,     srcWires := [0, 1],  dstWire := 4 }
  , { opIdx := 1,  op := .add,     srcWires := [2, 3],  dstWire := 5 }
  , { opIdx := 2,  op := .mul,     srcWires := [4, 5],  dstWire := 6 }
  , { opIdx := 3,  op := .const 10, srcWires := [],     dstWire := 7 }
  , { opIdx := 4,  op := .add,     srcWires := [6, 7],  dstWire := 8 }
  , { opIdx := 5,  op := .scale 1, srcWires := [9],     dstWire := 10 }
  , { opIdx := 6,  op := .scale 1, srcWires := [9],     dstWire := 11 }
  , { opIdx := 7,  op := .mul,     srcWires := [5, 10], dstWire := 12 }
  , { opIdx := 8,  op := .mul,     srcWires := [4, 10], dstWire := 13 }
  , { opIdx := 9,  op := .scale 1, srcWires := [13],    dstWire := 14 }
  , { opIdx := 10, op := .scale 1, srcWires := [13],    dstWire := 15 }
  , { opIdx := 11, op := .scale 1, srcWires := [12],    dstWire := 16 }
  , { opIdx := 12, op := .scale 1, srcWires := [12],    dstWire := 17 } ]

/-- Explicit 11-edge list of `optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph`
after equality saturation (`.mulOneRight` wire-forwarding + dead-cotangent pruning of wires `10` and `11`). -/
def goldenDiamondOptEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .add,     srcWires := [0, 1], dstWire := 4 }
  , { opIdx := 1,  op := .add,     srcWires := [2, 3], dstWire := 5 }
  , { opIdx := 2,  op := .mul,     srcWires := [4, 5], dstWire := 6 }
  , { opIdx := 3,  op := .const 10, srcWires := [],    dstWire := 7 }
  , { opIdx := 4,  op := .add,     srcWires := [6, 7], dstWire := 8 }
  , { opIdx := 5,  op := .mul,     srcWires := [5, 9], dstWire := 12 }
  , { opIdx := 6,  op := .mul,     srcWires := [4, 9], dstWire := 13 }
  , { opIdx := 7,  op := .scale 1, srcWires := [13],   dstWire := 14 }
  , { opIdx := 8,  op := .scale 1, srcWires := [13],   dstWire := 15 }
  , { opIdx := 9,  op := .scale 1, srcWires := [12],   dstWire := 16 }
  , { opIdx := 10, op := .scale 1, srcWires := [12],   dstWire := 17 } ]

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_goldenDiamondAdj :
    extractHyperEdges (compileGraphAdjoint goldenDiamondHypergraph) = goldenDiamondAdjEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_goldenDiamondOpt :
    extractHyperEdges (optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph) =
      goldenDiamondOptEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_goldenDiamondAdj :
    (compileGraphAdjoint goldenDiamondHypergraph).boundaryOut.table = [8, 16, 17, 14, 15] := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_goldenDiamondOpt :
    (optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph).boundaryOut.table =
      [8, 16, 17, 14, 15] := by
  decide +kernel

/-- **Theorem (`optimizeAdjointHypergraph_preserves_cotangents`)**:
For EVERY symbolic input assignment `(x0, x1, x2, x3, dOut : Int)` to `goldenDiamondHypergraph`,
`optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph` computes the exact same
symbolic forward output and all 4 reverse-mode input cotangents as `compileGraphAdjoint goldenDiamondHypergraph`:
$$[(x_0 + x_1)(x_2 + x_3) + 10,\; (x_2 + x_3)\,\text{dOut},\; (x_2 + x_3)\,\text{dOut},\; (x_0 + x_1)\,\text{dOut},\; (x_0 + x_1)\,\text{dOut}]$$ -/
theorem optimizeAdjointHypergraph_preserves_cotangents (x0 x1 x2 x3 dOut : Int) :
    let gAdj := compileGraphAdjoint goldenDiamondHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph
    let env : Nat → Int := fun w =>
      match w with
      | 0 => x0
      | 1 => x1
      | 2 => x2
      | 3 => x3
      | 9 => dOut
      | _ => 0
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env =
      [ (x0 + x1) * (x2 + x3) + 10
      , (x2 + x3) * dOut
      , (x2 + x3) * dOut
      , (x0 + x1) * dOut
      , (x0 + x1) * dOut ] := by
  dsimp only
  unfold evalHypergraphComb
  rw [extractHyperEdges_goldenDiamondOpt, boundaryOut_goldenDiamondOpt,
      extractHyperEdges_goldenDiamondAdj, boundaryOut_goldenDiamondAdj]
  dsimp [goldenDiamondOptEdgesLiteral, goldenDiamondAdjEdgesLiteral,
    evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp, List.foldl, List.map]
  grind

/-- **Theorem (`eqSat_preserves_eval_and_adjoint`)**:
Master theorem combining:
1. Universal E-Graph saturation semantic consistency (`saturateHyperEGraph_preserves_consistency`),
2. Universal cost improvement (`extractMinCost_improves_cost`),
3. Symbolic cotangent equivalence (`optimizeAdjointHypergraph_preserves_cotangents`) across all
   `(x0, x1, x2, x3, dOut : Int)`! -/
theorem eqSat_preserves_eval_and_adjoint
    (fuel : Nat) (rules : List EqSatRule) (eg : HyperEGraph) (env : EClassId → Int)
    (hCons : EGraphConsistent eg env)
    (costModel : HyperCostModel) (g : StrictOpenHypergraph)
    (x0 x1 x2 x3 dOut : Int) :
    EGraphConsistent (saturateHyperEGraph fuel rules eg) env ∧
    evalHypergraphCost costModel
      (extractMinCostHypergraph costModel (saturateHyperEGraph fuel rules (hypergraphToEGraph g))) ≤
      evalHypergraphCost costModel g ∧
    evalHypergraphComb (optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph)
      (fun w => match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0) =
    evalHypergraphComb (compileGraphAdjoint goldenDiamondHypergraph)
      (fun w => match w with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 9 => dOut | _ => 0) :=
  ⟨ saturateHyperEGraph_preserves_consistency fuel rules eg env hCons
  , extractMinCost_improves_cost costModel g fuel rules
  , (optimizeAdjointHypergraph_preserves_cotangents x0 x1 x2 x3 dOut).1 ⟩

/-! ## 6. Pipelined RTL Lowering of E-Graph Optimized Adjoint Hypergraphs (`eqSat_pipelined_rtl_sound`) -/

/-- **Theorem (`eqSat_pipelined_rtl_sound`)**:
Lowering the equality-saturated minimum-cost adjoint hypergraph
`gOpt := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph` through
`compileHypergraphToRtlPipelined`:
1. Produces a structurally valid synchronous `RtlModule` (`checkRtlModule = true`),
2. Strictly reduces the pipeline wavefront stage depth from `5` cycles (`layerHypergraph gAdj`) to
   `4` cycles (`layerHypergraph gOpt`) AND reduces the pipeline register count from `90` registers
   (`5 × 18`) to `72` registers (`4 × 18`),
3. After `4` synchronous clock cycles (`runModuleTrace`), latches the exact 64-bit forward output and
   4 input cotangents `[87#64, 11#64, 11#64, 7#64, 7#64]` matching the unoptimized 5-cycle adjoint RTL! -/
theorem eqSat_pipelined_rtl_sound :
    let gAdj  := compileGraphAdjoint goldenDiamondHypergraph
    let gOpt  := optimizeAdjointHypergraph defaultRtlCostModel goldenDiamondHypergraph
    let mAdj  := compileHypergraphToRtlPipelined "diamond_adj_raw" gAdj
    let mOpt  := compileHypergraphToRtlPipelined "diamond_adj_opt" gOpt
    let initEnvInt : Nat → Int := fun w =>
      match w with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 9 => 1 | _ => 0
    let insBv : Nat → BitVec 64 := fun u => BitVec.ofInt 64 (initEnvInt u)
    let initRegs : Nat → BitVec 64 := fun _ => 0#64
    let trace4 : List (Bool × (Nat → BitVec 64)) :=
      [(false, insBv), (false, insBv), (false, insBv), (false, insBv)]
    let trace5 : List (Bool × (Nat → BitVec 64)) :=
      [(false, insBv), (false, insBv), (false, insBv), (false, insBv), (false, insBv)]
    let regsOpt4 := runModuleTrace mOpt initRegs trace4
    let regsAdj5 := runModuleTrace mAdj initRegs trace5
    checkRtlModule mOpt = true ∧
    (layerHypergraph gOpt).length = 4 ∧
    (layerHypergraph gAdj).length = 5 ∧
    mOpt.regs.length < mAdj.regs.length ∧
    mOpt.regs.length = 72 ∧
    mAdj.regs.length = 90 ∧
    (evalModuleOutputs mOpt insBv regsOpt4).map Prod.snd =
      [87#64, 11#64, 11#64, 7#64, 7#64] ∧
    (evalModuleOutputs mOpt insBv regsOpt4).map Prod.snd =
      (evalModuleOutputs mAdj insBv regsAdj5).map Prod.snd := by
  decide +kernel

/-! ## 7. Coupled Discrete Pontryagin Flowpipe Adjoint Sensitivity (`pontryagin_flowpipe_adjoint_eqSat_sound`) -/

/-- Discrete-time Euler–Pontryagin step hypergraph for the 2D coupled damped oscillator
($x_{k+1} = x_k + v_k,\; v_{k+1} = v_k - (x_k + v_k)$ in scaled integer coordinates):
* Wire `0`: state $x_k$,
* Wire `1`: velocity $v_k$,
* Wire `2`: $x_{k+1} = x_k + v_k$ (`.add [0, 1]`),
* Wire `3`: $s = x_k + v_k$ (`.add [0, 1]`),
* Wire `4`: $v_{k+1} = v_k - s$ (`.sub [1, 3]`),
* Boundary inputs: `[0, 1]`, boundary outputs: `[2, 4]`. -/
def coupledOscillatorStepHypergraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 5 [0, 1] [2, 4]
    [ { opIdx := 0, op := .add, srcWires := [0, 1], dstWire := 2 }
    , { opIdx := 1, op := .add, srcWires := [0, 1], dstWire := 3 }
    , { opIdx := 2, op := .sub, srcWires := [1, 3], dstWire := 4 } ]

/-- **Theorem (`pontryagin_flowpipe_adjoint_eqSat_sound`)**:
Couples $N$-dimensional validated Picard–Lindelöf ODE flowpipes (`Flowpipe.lean`) with whole-DAG
reverse-mode adjoint compilation (`compileGraphAdjoint_dag_sound`) and E-Graph equality saturation
(`optimizeAdjointHypergraph`):
1. **Continuous 2D Validated Picard–Lindelöf Enclosure**:
   `stepPicardValidated coupledOscillatorOde` certifies the 2D state-velocity enclosure
   `[("x", ⟨994/1000, 9965/10000⟩), ("v", ⟨-97/1000, -93/1000⟩)]` with off-diagonal coupled Lie
   derivative $\mathcal{L}_f f_x(\tilde{X}) = [-6/5, -7/10]$,
2. **Whole-DAG Pontryagin Adjoint Pullback (`compileGraphAdjoint` + EqSat Optimization)**:
   Differentiating `coupledOscillatorStepHypergraph` via `compileGraphAdjoint` and optimizing via
   `optimizeAdjointHypergraph defaultRtlCostModel` strictly reduces hardware cost (`28 < 30`),
   eliminates dead cotangent hyperedges (`11 < 12`), and computes the exact discrete Pontryagin
   costate sensitivities
   $$\lambda_{x_k} = \lambda_{x_{k+1}} - \lambda_{v_{k+1}}, \qquad \lambda_{v_k} = \lambda_{x_{k+1}}$$
   (`[13, -10, -3, 2]` at $x_k = 10, v_k = 3, \lambda_{x_{k+1}} = 2, \lambda_{v_{k+1}} = 5$)! -/
theorem pontryagin_flowpipe_adjoint_eqSat_sound :
    let oscX0 := [("x", (⟨1, 1⟩ : Interval)), ("v", (⟨0, 0⟩ : Interval))]
    let oscXTilde :=
      [ ("x", ⟨CanonicalRat.mk 9 10, CanonicalRat.mk 11 10⟩)
      , ("v", ⟨CanonicalRat.mk (-1) 5, CanonicalRat.mk 1 10⟩) ]
    let oscH : CanonicalRat := CanonicalRat.mk 1 10
    let gAdj := compileGraphAdjoint coupledOscillatorStepHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel coupledOscillatorStepHypergraph
    let env : Nat → Int := fun w =>
      match w with | 0 => 10 | 1 => 3 | 5 => 2 | 6 => 5 | _ => 0
    verifyPicardAPriori coupledOscillatorOde oscX0 oscXTilde oscH = true ∧
    stepPicardValidated coupledOscillatorOde oscX0 oscXTilde oscH =
      some [ ("x", ⟨CanonicalRat.mk 994 1000, CanonicalRat.mk 9965 10000⟩)
           , ("v", ⟨CanonicalRat.mk (-97) 1000, CanonicalRat.mk (-93) 1000⟩) ] ∧
    evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
    (extractHyperEdges gOpt).length < (extractHyperEdges gAdj).length ∧
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env = [13, -10, -3, 2] := by
  decide +kernel

/-! ## 8. Differentiable Multi-Link Featherstone `RNEA` & Coupled Stator Multiphysics Adjoint Hypergraphs (`rnea2Link_adjoint_eqSat_sound`, `statorCoupledLoss_adjoint_eqSat_sound`) -/

/-- Forward `HyperEdge` list for the 2-Link Featherstone `RNEA` Inverse-Dynamics & Trajectory Torque Cost
Hypergraph (`rnea2LinkCostHypergraph`):
* Boundary inputs `[0, 1, 2, 3, 4, 5, 6, 7]` = `(q1, dq1, ddq1, ddq2, I1, I2, m1, m2)`:
  - Wire `0`: joint 1 position $q_1$
  - Wire `1`: joint 1 velocity $\dot{q}_1$
  - Wire `2`: joint 1 angular acceleration $\ddot{q}_1$
  - Wire `3`: joint 2 angular acceleration $\ddot{q}_2$
  - Wire `4`: link 1 rotational inertia $I_1$
  - Wire `5`: link 2 rotational inertia $I_2$
  - Wire `6`: link 1 mass $m_1$
  - Wire `7`: link 2 distal mass $m_2$
* Forward RNEA outward acceleration & inward wrench recursion:
  - Wire `8`: $a_2 = \ddot{q}_1 + \ddot{q}_2$ (`.add [2, 3]`)
  - Wire `9`: $f_{\text{inert},2} = I_2 \cdot a_2$ (`.mul [5, 8]`)
  - Wire `10`: $f_{\text{grav},2} = m_2 \cdot q_1$ (`.mul [7, 0]`)
  - Wire `11`: distal link wrench $\tau_2 = I_2(\ddot{q}_1 + \ddot{q}_2) + m_2 q_1$ (`.add [9, 10]`)
  - Wire `12`: $f_{\text{inert},1} = I_1 \cdot \ddot{q}_1$ (`.mul [4, 2]`)
  - Wire `13`: $f_{\text{cor},1} = m_1 \cdot \dot{q}_1$ (`.mul [6, 1]`)
  - Wire `14`: $\tau_{1,\text{loc}} = I_1 \ddot{q}_1 + m_1 \dot{q}_1$ (`.add [12, 13]`)
  - Wire `15`: proximal link wrench $\tau_1 = \tau_{1,\text{loc}} + \tau_2$ (`.add [14, 11]`)
  - Wire `16`: $\tau_1^2 = \tau_1 \cdot \tau_1$ (`.mul [15, 15]`)
  - Wire `17`: $\tau_2^2 = \tau_2 \cdot \tau_2$ (`.mul [11, 11]`)
  - Wire `18`: quadratic actuator effort $J = \tau_1^2 + \tau_2^2$ (`.add [16, 17]`). -/
def rnea2LinkFwdEdges : List HyperEdge :=
  [ { opIdx := 0,  op := .add, srcWires := [2, 3],   dstWire := 8 }
  , { opIdx := 1,  op := .mul, srcWires := [5, 8],   dstWire := 9 }
  , { opIdx := 2,  op := .mul, srcWires := [7, 0],   dstWire := 10 }
  , { opIdx := 3,  op := .add, srcWires := [9, 10],  dstWire := 11 }
  , { opIdx := 4,  op := .mul, srcWires := [4, 2],   dstWire := 12 }
  , { opIdx := 5,  op := .mul, srcWires := [6, 1],   dstWire := 13 }
  , { opIdx := 6,  op := .add, srcWires := [12, 13], dstWire := 14 }
  , { opIdx := 7,  op := .add, srcWires := [14, 11], dstWire := 15 }
  , { opIdx := 8,  op := .mul, srcWires := [15, 15], dstWire := 16 }
  , { opIdx := 9,  op := .mul, srcWires := [11, 11], dstWire := 17 }
  , { opIdx := 10, op := .add, srcWires := [16, 17], dstWire := 18 } ]

/-- **2-Link Featherstone `RNEA` Inverse-Dynamics & Trajectory Torque Cost Hypergraph (`rnea2LinkCostHypergraph`)**:
Maps `(q1, dq1, ddq1, ddq2, I1, I2, m1, m2)` (wires `0..7`) to link wrenches $(\tau_1, \tau_2)$ and
quadratic actuator effort $J = \tau_1^2 + \tau_2^2$ (wire `18`). -/
def rnea2LinkCostHypergraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 19 [0, 1, 2, 3, 4, 5, 6, 7] [18] (reindexHyperEdges rnea2LinkFwdEdges)

/-- Explicit 37-edge list of `compileGraphAdjoint rnea2LinkCostHypergraph`. -/
def rnea2LinkAdjEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .add,     srcWires := [2, 3],   dstWire := 8 }
  , { opIdx := 1,  op := .mul,     srcWires := [5, 8],   dstWire := 9 }
  , { opIdx := 2,  op := .mul,     srcWires := [7, 0],   dstWire := 10 }
  , { opIdx := 3,  op := .add,     srcWires := [9, 10],  dstWire := 11 }
  , { opIdx := 4,  op := .mul,     srcWires := [4, 2],   dstWire := 12 }
  , { opIdx := 5,  op := .mul,     srcWires := [6, 1],   dstWire := 13 }
  , { opIdx := 6,  op := .add,     srcWires := [12, 13], dstWire := 14 }
  , { opIdx := 7,  op := .add,     srcWires := [14, 11], dstWire := 15 }
  , { opIdx := 8,  op := .mul,     srcWires := [15, 15], dstWire := 16 }
  , { opIdx := 9,  op := .mul,     srcWires := [11, 11], dstWire := 17 }
  , { opIdx := 10, op := .add,     srcWires := [16, 17], dstWire := 18 }
  , { opIdx := 11, op := .scale 1, srcWires := [19],     dstWire := 20 }
  , { opIdx := 12, op := .scale 1, srcWires := [19],     dstWire := 21 }
  , { opIdx := 13, op := .mul,     srcWires := [11, 21], dstWire := 22 }
  , { opIdx := 14, op := .mul,     srcWires := [11, 21], dstWire := 23 }
  , { opIdx := 15, op := .add,     srcWires := [22, 23], dstWire := 24 }
  , { opIdx := 16, op := .mul,     srcWires := [15, 20], dstWire := 25 }
  , { opIdx := 17, op := .mul,     srcWires := [15, 20], dstWire := 26 }
  , { opIdx := 18, op := .add,     srcWires := [25, 26], dstWire := 27 }
  , { opIdx := 19, op := .scale 1, srcWires := [27],     dstWire := 28 }
  , { opIdx := 20, op := .scale 1, srcWires := [27],     dstWire := 29 }
  , { opIdx := 21, op := .add,     srcWires := [24, 29], dstWire := 30 }
  , { opIdx := 22, op := .scale 1, srcWires := [28],     dstWire := 31 }
  , { opIdx := 23, op := .scale 1, srcWires := [28],     dstWire := 32 }
  , { opIdx := 24, op := .mul,     srcWires := [1, 32],  dstWire := 33 }
  , { opIdx := 25, op := .mul,     srcWires := [6, 32],  dstWire := 34 }
  , { opIdx := 26, op := .mul,     srcWires := [2, 31],  dstWire := 35 }
  , { opIdx := 27, op := .mul,     srcWires := [4, 31],  dstWire := 36 }
  , { opIdx := 28, op := .scale 1, srcWires := [30],     dstWire := 37 }
  , { opIdx := 29, op := .scale 1, srcWires := [30],     dstWire := 38 }
  , { opIdx := 30, op := .mul,     srcWires := [0, 38],  dstWire := 39 }
  , { opIdx := 31, op := .mul,     srcWires := [7, 38],  dstWire := 40 }
  , { opIdx := 32, op := .mul,     srcWires := [8, 37],  dstWire := 41 }
  , { opIdx := 33, op := .mul,     srcWires := [5, 37],  dstWire := 42 }
  , { opIdx := 34, op := .scale 1, srcWires := [42],     dstWire := 43 }
  , { opIdx := 35, op := .add,     srcWires := [36, 43], dstWire := 44 }
  , { opIdx := 36, op := .scale 1, srcWires := [42],     dstWire := 45 } ]

/-- Explicit 28-edge list of `optimizeAdjointHypergraph defaultRtlCostModel rnea2LinkCostHypergraph`
after E-Graph saturation (fusing 5 `.mul` + `.add` chains into `.mac` and pruning 9 dead cotangent wires). -/
def rnea2LinkOptEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .add,     srcWires := [2, 3],       dstWire := 8 }
  , { opIdx := 1,  op := .mul,     srcWires := [5, 8],       dstWire := 9 }
  , { opIdx := 2,  op := .mac,     srcWires := [7, 0, 9],    dstWire := 11 }
  , { opIdx := 3,  op := .mul,     srcWires := [4, 2],       dstWire := 12 }
  , { opIdx := 4,  op := .mac,     srcWires := [6, 1, 12],   dstWire := 14 }
  , { opIdx := 5,  op := .add,     srcWires := [14, 11],     dstWire := 15 }
  , { opIdx := 6,  op := .mul,     srcWires := [15, 15],     dstWire := 16 }
  , { opIdx := 7,  op := .mac,     srcWires := [11, 11, 16], dstWire := 18 }
  , { opIdx := 8,  op := .scale 1, srcWires := [19],         dstWire := 20 }
  , { opIdx := 9,  op := .scale 1, srcWires := [19],         dstWire := 21 }
  , { opIdx := 10, op := .mul,     srcWires := [11, 19],     dstWire := 22 }
  , { opIdx := 11, op := .mac,     srcWires := [11, 21, 22], dstWire := 24 }
  , { opIdx := 12, op := .mul,     srcWires := [15, 19],     dstWire := 25 }
  , { opIdx := 13, op := .mac,     srcWires := [15, 20, 25], dstWire := 27 }
  , { opIdx := 14, op := .scale 1, srcWires := [27],         dstWire := 28 }
  , { opIdx := 15, op := .scale 1, srcWires := [27],         dstWire := 29 }
  , { opIdx := 16, op := .add,     srcWires := [24, 29],     dstWire := 30 }
  , { opIdx := 17, op := .mul,     srcWires := [1, 28],      dstWire := 33 }
  , { opIdx := 18, op := .mul,     srcWires := [6, 28],      dstWire := 34 }
  , { opIdx := 19, op := .mul,     srcWires := [2, 28],      dstWire := 35 }
  , { opIdx := 20, op := .mul,     srcWires := [4, 28],      dstWire := 36 }
  , { opIdx := 21, op := .mul,     srcWires := [0, 30],      dstWire := 39 }
  , { opIdx := 22, op := .mul,     srcWires := [7, 30],      dstWire := 40 }
  , { opIdx := 23, op := .mul,     srcWires := [8, 30],      dstWire := 41 }
  , { opIdx := 24, op := .mul,     srcWires := [5, 30],      dstWire := 42 }
  , { opIdx := 25, op := .scale 1, srcWires := [42],         dstWire := 43 }
  , { opIdx := 26, op := .add,     srcWires := [36, 43],     dstWire := 44 }
  , { opIdx := 27, op := .scale 1, srcWires := [42],         dstWire := 45 } ]

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_rnea2LinkAdj :
    extractHyperEdges (compileGraphAdjoint rnea2LinkCostHypergraph) = rnea2LinkAdjEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_rnea2LinkOpt :
    extractHyperEdges (optimizeAdjointHypergraph defaultRtlCostModel rnea2LinkCostHypergraph) =
      rnea2LinkOptEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_rnea2LinkAdj :
    (compileGraphAdjoint rnea2LinkCostHypergraph).boundaryOut.table =
      [18, 40, 34, 44, 45, 35, 41, 33, 39] := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_rnea2LinkOpt :
    (optimizeAdjointHypergraph defaultRtlCostModel rnea2LinkCostHypergraph).boundaryOut.table =
      [18, 40, 34, 44, 45, 35, 41, 33, 39] := by
  decide +kernel

/-- Wire environment for `compileGraphAdjoint rnea2LinkCostHypergraph` and
`optimizeAdjointHypergraph defaultRtlCostModel rnea2LinkCostHypergraph`, binding primal inputs `0..7`
and output cotangent seed wire `19 ↦ dOut`. -/
def rnea2LinkAdjointEnv (q1 dq1 ddq1 ddq2 I1 I2 m1 m2 dOut : Int) (w : Nat) : Int :=
  match w with
  | 0 => q1
  | 1 => dq1
  | 2 => ddq1
  | 3 => ddq2
  | 4 => I1
  | 5 => I2
  | 6 => m1
  | 7 => m2
  | 19 => dOut
  | _ => 0

set_option maxHeartbeats 800000 in
/-- **2-Link Featherstone `RNEA` Adjoint E-Graph Saturation & Symbolic Gradient Soundness
(`rnea2Link_adjoint_eqSat_sound`)**:
Proves that differentiating `rnea2LinkCostHypergraph` via `compileGraphAdjoint` and optimizing via
`optimizeAdjointHypergraph defaultRtlCostModel`:
1. Preserves `StrictOpenHypergraph` well-formedness (`gOpt.wf = true`),
2. Strictly reduces hardware RTL cost (`117 < 155`), hyperedge count (`28 < 37`, pruning 9 dead edges
   and fusing 5 `.mul` + `.add` chains into `.mac`), and synchronous pipeline stage depth (`14 < 16`),
3. For EVERY symbolic state & inertia assignment `(q1, dq1, ddq1, ddq2, I1, I2, m1, m2, dOut : Int)`,
   the E-Graph-saturated adjoint `gOpt` and the unoptimized adjoint `gAdj` evaluate to the exact
   analytical / dual partial derivatives:
   - $J = \tau_1^2 + \tau_2^2$,
   - $\frac{\partial J}{\partial q_1} \cdot \text{dOut} = m_2 (2 \tau_2 + 2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial \dot{q}_1} \cdot \text{dOut} = m_1 (2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial \ddot{q}_1} \cdot \text{dOut} = (I_1 (2 \tau_1) + I_2 (2 \tau_2 + 2 \tau_1)) \text{dOut}$,
   - $\frac{\partial J}{\partial \ddot{q}_2} \cdot \text{dOut} = I_2 (2 \tau_2 + 2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial I_1} \cdot \text{dOut} = \ddot{q}_1 (2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial I_2} \cdot \text{dOut} = (\ddot{q}_1 + \ddot{q}_2) (2 \tau_2 + 2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial m_1} \cdot \text{dOut} = \dot{q}_1 (2 \tau_1) \text{dOut}$,
   - $\frac{\partial J}{\partial m_2} \cdot \text{dOut} = q_1 (2 \tau_2 + 2 \tau_1) \text{dOut}$. -/
theorem rnea2Link_adjoint_eqSat_sound
    (q1 dq1 ddq1 ddq2 I1 I2 m1 m2 dOut : Int) :
    let gAdj := compileGraphAdjoint rnea2LinkCostHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel rnea2LinkCostHypergraph
    let env := rnea2LinkAdjointEnv q1 dq1 ddq1 ddq2 I1 I2 m1 m2 dOut
    let tau2 := I2 * (ddq1 + ddq2) + m2 * q1
    let tau1 := I1 * ddq1 + m1 * dq1 + tau2
    let dTau1 := (tau1 + tau1) * dOut
    let dTau2 := (tau2 + tau2 + (tau1 + tau1)) * dOut
    gOpt.wf = true ∧
    evalHypergraphCost defaultRtlCostModel gOpt = 117 ∧
    evalHypergraphCost defaultRtlCostModel gAdj = 155 ∧
    evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
    (extractHyperEdges gOpt).length = 28 ∧
    (extractHyperEdges gAdj).length = 37 ∧
    (extractHyperEdges gOpt).length < (extractHyperEdges gAdj).length ∧
    (layerHypergraph gOpt).length = 14 ∧
    (layerHypergraph gAdj).length = 16 ∧
    (layerHypergraph gOpt).length < (layerHypergraph gAdj).length ∧
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env =
      [ tau1 * tau1 + tau2 * tau2
      , m2 * dTau2
      , m1 * dTau1
      , I1 * dTau1 + I2 * dTau2
      , I2 * dTau2
      , ddq1 * dTau1
      , (ddq1 + ddq2) * dTau2
      , dq1 * dTau1
      , q1 * dTau2 ] := by
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  unfold evalHypergraphComb
  rw [extractHyperEdges_rnea2LinkOpt, boundaryOut_rnea2LinkOpt,
      extractHyperEdges_rnea2LinkAdj, boundaryOut_rnea2LinkAdj]
  dsimp [rnea2LinkOptEdgesLiteral, rnea2LinkAdjEdgesLiteral,
    evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp, rnea2LinkAdjointEnv,
    List.foldl, List.map]
  grind

/-- Forward `HyperEdge` list for the Coupled LC Drives Stator Electro-Thermal-Magnetic Loss
Hypergraph (`statorCoupledLossHypergraph`):
* Boundary inputs `[0, 1, 2, 3]` = `(currentA, toothWidthUm, channelAspect, fcmlFreqKhz)`:
  - Wire `0`: phase RMS current $I$ (`currentA`)
  - Wire `1`: stator tooth width / flux factor $w_{\text{tooth}}$ (`toothWidthUm`)
  - Wire `2`: microchannel cooling aspect ratio $\alpha_{\text{ch}}$ (`channelAspect`)
  - Wire `3`: FCML switching frequency $f_{\text{fcml}}$ (`fcmlFreqKhz`)
* Forward electro-thermal-magnetic edges:
  - Wire `4`: $I^2 = I \cdot I$ (`.mul [0, 0]`)
  - Wire `5`: $R_{\text{eff}}(T) = w_{\text{tooth}} + \alpha_{\text{ch}}$ (`.add [1, 2]`)
  - Wire `6`: ohmic copper loss $P_{\text{Cu}} = I^2 \cdot R_{\text{eff}}(T)$ (`.mul [4, 5]`)
  - Wire `7`: Steinmetz core loss $P_{\text{Fe}} = w_{\text{tooth}} \cdot f_{\text{fcml}}$ (`.mul [1, 3]`)
  - Wire `8`: total electromagnetic loss $P_{\text{tot}} = P_{\text{Cu}} + P_{\text{Fe}}$ (`.add [6, 7]`)
  - Wire `9`: microchannel convective relief $\Delta T_{\text{cool}} = 2 \alpha_{\text{ch}}$ (`.scale 2 [2]`)
  - Wire `10`: net thermal rise $\Delta T_{\text{net}} = P_{\text{tot}} - \Delta T_{\text{cool}}$ (`.sub [8, 9]`)
  - Wire `11`: coolant ambient temperature $T_{\text{amb}} = 25$ (`.const 25 []`)
  - Wire `12`: peak winding temperature $T_{\text{peak}} = \Delta T_{\text{net}} + 25$ (`.add [10, 11]`). -/
def statorCoupledLossFwdEdges : List HyperEdge :=
  [ { opIdx := 0, op := .mul,      srcWires := [0, 0],   dstWire := 4 }
  , { opIdx := 1, op := .add,      srcWires := [1, 2],   dstWire := 5 }
  , { opIdx := 2, op := .mul,      srcWires := [4, 5],   dstWire := 6 }
  , { opIdx := 3, op := .mul,      srcWires := [1, 3],   dstWire := 7 }
  , { opIdx := 4, op := .add,      srcWires := [6, 7],   dstWire := 8 }
  , { opIdx := 5, op := .scale 2,  srcWires := [2],      dstWire := 9 }
  , { opIdx := 6, op := .sub,      srcWires := [8, 9],   dstWire := 10 }
  , { opIdx := 7, op := .const 25, srcWires := [],       dstWire := 11 }
  , { opIdx := 8, op := .add,      srcWires := [10, 11], dstWire := 12 } ]

/-- **Coupled LC Drives Stator Electro-Thermal-Magnetic Loss Hypergraph (`statorCoupledLossHypergraph`)**:
Maps `(currentA, toothWidthUm, channelAspect, fcmlFreqKhz)` (wires `0..3`) to $I^2 R(T)$ copper loss +
Steinmetz core loss + peak winding temperature $T_{\text{peak}}$ (wire `12`). -/
def statorCoupledLossHypergraph : StrictOpenHypergraph :=
  mkStrictOpenHypergraph 13 [0, 1, 2, 3] [12] (reindexHyperEdges statorCoupledLossFwdEdges)

/-- Explicit 27-edge list of `compileGraphAdjoint statorCoupledLossHypergraph`. -/
def statorLossAdjEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .mul,        srcWires := [0, 0],   dstWire := 4 }
  , { opIdx := 1,  op := .add,        srcWires := [1, 2],   dstWire := 5 }
  , { opIdx := 2,  op := .mul,        srcWires := [4, 5],   dstWire := 6 }
  , { opIdx := 3,  op := .mul,        srcWires := [1, 3],   dstWire := 7 }
  , { opIdx := 4,  op := .add,        srcWires := [6, 7],   dstWire := 8 }
  , { opIdx := 5,  op := .scale 2,    srcWires := [2],      dstWire := 9 }
  , { opIdx := 6,  op := .sub,        srcWires := [8, 9],   dstWire := 10 }
  , { opIdx := 7,  op := .const 25,   srcWires := [],       dstWire := 11 }
  , { opIdx := 8,  op := .add,        srcWires := [10, 11], dstWire := 12 }
  , { opIdx := 9,  op := .scale 1,    srcWires := [13],     dstWire := 14 }
  , { opIdx := 10, op := .scale 1,    srcWires := [13],     dstWire := 15 }
  , { opIdx := 11, op := .scale 1,    srcWires := [14],     dstWire := 16 }
  , { opIdx := 12, op := .scale (-1), srcWires := [14],     dstWire := 17 }
  , { opIdx := 13, op := .scale 2,    srcWires := [17],     dstWire := 18 }
  , { opIdx := 14, op := .scale 1,    srcWires := [16],     dstWire := 19 }
  , { opIdx := 15, op := .scale 1,    srcWires := [16],     dstWire := 20 }
  , { opIdx := 16, op := .mul,        srcWires := [3, 20],  dstWire := 21 }
  , { opIdx := 17, op := .mul,        srcWires := [1, 20],  dstWire := 22 }
  , { opIdx := 18, op := .mul,        srcWires := [5, 19],  dstWire := 23 }
  , { opIdx := 19, op := .mul,        srcWires := [4, 19],  dstWire := 24 }
  , { opIdx := 20, op := .scale 1,    srcWires := [24],     dstWire := 25 }
  , { opIdx := 21, op := .add,        srcWires := [21, 25], dstWire := 26 }
  , { opIdx := 22, op := .scale 1,    srcWires := [24],     dstWire := 27 }
  , { opIdx := 23, op := .add,        srcWires := [18, 27], dstWire := 28 }
  , { opIdx := 24, op := .mul,        srcWires := [0, 23],  dstWire := 29 }
  , { opIdx := 25, op := .mul,        srcWires := [0, 23],  dstWire := 30 }
  , { opIdx := 26, op := .add,        srcWires := [29, 30], dstWire := 31 } ]

/-- Explicit 21-edge list of `optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph`
after E-Graph saturation (fusing `.mul` + `.add` into `.mac`, fusing `.scale 2 (.scale (-1) ...)` into
`.scale (-2)`, and pruning 6 dead cotangent edges). -/
def statorLossOptEdgesLiteral : List HyperEdge :=
  [ { opIdx := 0,  op := .mul,        srcWires := [0, 0],      dstWire := 4 }
  , { opIdx := 1,  op := .add,        srcWires := [1, 2],      dstWire := 5 }
  , { opIdx := 2,  op := .mul,        srcWires := [4, 5],      dstWire := 6 }
  , { opIdx := 3,  op := .mac,        srcWires := [1, 3, 6],   dstWire := 8 }
  , { opIdx := 4,  op := .scale 2,    srcWires := [2],         dstWire := 9 }
  , { opIdx := 5,  op := .sub,        srcWires := [8, 9],      dstWire := 10 }
  , { opIdx := 6,  op := .const 25,   srcWires := [],          dstWire := 11 }
  , { opIdx := 7,  op := .add,        srcWires := [10, 11],    dstWire := 12 }
  , { opIdx := 8,  op := .scale 1,    srcWires := [13],        dstWire := 14 }
  , { opIdx := 9,  op := .scale 1,    srcWires := [13],        dstWire := 16 }
  , { opIdx := 10, op := .scale (-2), srcWires := [14],        dstWire := 18 }
  , { opIdx := 11, op := .mul,        srcWires := [3, 16],     dstWire := 21 }
  , { opIdx := 12, op := .mul,        srcWires := [1, 16],     dstWire := 22 }
  , { opIdx := 13, op := .mul,        srcWires := [5, 16],     dstWire := 23 }
  , { opIdx := 14, op := .mul,        srcWires := [4, 16],     dstWire := 24 }
  , { opIdx := 15, op := .scale 1,    srcWires := [24],        dstWire := 25 }
  , { opIdx := 16, op := .add,        srcWires := [21, 25],    dstWire := 26 }
  , { opIdx := 17, op := .scale 1,    srcWires := [24],        dstWire := 27 }
  , { opIdx := 18, op := .add,        srcWires := [18, 27],    dstWire := 28 }
  , { opIdx := 19, op := .mul,        srcWires := [0, 23],     dstWire := 29 }
  , { opIdx := 20, op := .mac,        srcWires := [0, 23, 29], dstWire := 31 } ]

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_statorLossAdj :
    extractHyperEdges (compileGraphAdjoint statorCoupledLossHypergraph) = statorLossAdjEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem extractHyperEdges_statorLossOpt :
    extractHyperEdges (optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph) =
      statorLossOptEdgesLiteral := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_statorLossAdj :
    (compileGraphAdjoint statorCoupledLossHypergraph).boundaryOut.table = [12, 31, 26, 28, 22] := by
  decide +kernel

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem boundaryOut_statorLossOpt :
    (optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph).boundaryOut.table =
      [12, 31, 26, 28, 22] := by
  decide +kernel

/-- Wire environment for `compileGraphAdjoint statorCoupledLossHypergraph` and
`optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph`, binding primal inputs `0..3`
and output cotangent seed wire `13 ↦ dOut`. -/
def statorCoupledLossAdjointEnv (currentA toothWidthUm channelAspect fcmlFreqKhz dOut : Int) (w : Nat) : Int :=
  match w with
  | 0 => currentA
  | 1 => toothWidthUm
  | 2 => channelAspect
  | 3 => fcmlFreqKhz
  | 13 => dOut
  | _ => 0

set_option maxHeartbeats 800000 in
/-- **Coupled Stator Electro-Thermal-Magnetic Adjoint E-Graph Saturation & Symbolic Sensitivity Soundness
(`statorCoupledLoss_adjoint_eqSat_sound`)**:
Proves that differentiating `statorCoupledLossHypergraph` via `compileGraphAdjoint` and optimizing via
`optimizeAdjointHypergraph defaultRtlCostModel`:
1. Preserves `StrictOpenHypergraph` well-formedness (`gOpt.wf = true`),
2. Strictly reduces hardware RTL cost (`76 < 96`), hyperedge count (`21 < 27`, pruning 6 dead cotangent
   edges and fusing `.mul` + `.add` into `.mac` and `.scale 2 (.scale (-1) ...)` into `.scale (-2)`),
   and synchronous pipeline stage depth (`10 < 12`),
3. For EVERY symbolic operating point `(currentA, toothWidthUm, channelAspect, fcmlFreqKhz, dOut : Int)`,
   the E-Graph-saturated adjoint `gOpt` and the unoptimized adjoint `gAdj` evaluate to the exact
   symbolic electro-thermal-magnetic sensitivities:
   - $T_{\text{peak}} = I^2 (w_{\text{tooth}} + \alpha_{\text{ch}}) + w_{\text{tooth}} f_{\text{fcml}} - 2 \alpha_{\text{ch}} + 25$,
   - $\frac{\partial T_{\text{peak}}}{\partial I} \cdot \text{dOut} = 2 I (w_{\text{tooth}} + \alpha_{\text{ch}}) \text{dOut}$,
   - $\frac{\partial T_{\text{peak}}}{\partial w_{\text{tooth}}} \cdot \text{dOut} = (I^2 + f_{\text{fcml}}) \text{dOut}$,
   - $\frac{\partial T_{\text{peak}}}{\partial \alpha_{\text{ch}}} \cdot \text{dOut} = (I^2 - 2) \text{dOut}$,
   - $\frac{\partial T_{\text{peak}}}{\partial f_{\text{fcml}}} \cdot \text{dOut} = w_{\text{tooth}} \text{dOut}$. -/
theorem statorCoupledLoss_adjoint_eqSat_sound
    (currentA toothWidthUm channelAspect fcmlFreqKhz dOut : Int) :
    let gAdj := compileGraphAdjoint statorCoupledLossHypergraph
    let gOpt := optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph
    let env := statorCoupledLossAdjointEnv currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    let iSq := currentA * currentA
    let rEff := toothWidthUm + channelAspect
    let tPeak := iSq * rEff + toothWidthUm * fcmlFreqKhz - 2 * channelAspect + 25
    gOpt.wf = true ∧
    evalHypergraphCost defaultRtlCostModel gOpt = 76 ∧
    evalHypergraphCost defaultRtlCostModel gAdj = 96 ∧
    evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
    (extractHyperEdges gOpt).length = 21 ∧
    (extractHyperEdges gAdj).length = 27 ∧
    (extractHyperEdges gOpt).length < (extractHyperEdges gAdj).length ∧
    (layerHypergraph gOpt).length = 10 ∧
    (layerHypergraph gAdj).length = 12 ∧
    (layerHypergraph gOpt).length < (layerHypergraph gAdj).length ∧
    evalHypergraphComb gOpt env = evalHypergraphComb gAdj env ∧
    evalHypergraphComb gOpt env =
      [ tPeak
      , (currentA + currentA) * rEff * dOut
      , (iSq + fcmlFreqKhz) * dOut
      , (iSq - 2) * dOut
      , toothWidthUm * dOut ] := by
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  unfold evalHypergraphComb
  rw [extractHyperEdges_statorLossOpt, boundaryOut_statorLossOpt,
      extractHyperEdges_statorLossAdj, boundaryOut_statorLossAdj]
  dsimp [statorLossOptEdgesLiteral, statorLossAdjEdgesLiteral,
    evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp, statorCoupledLossAdjointEnv,
    List.foldl, List.map]
  grind

end Obend.Analysis
end
