module
/- Equitable quotients of causal SSA open hypergraphs
Forward evaluation lifts across a certified quotient. Reverse evaluation sums cotangents over its fibers. -/
public import Obend.Hardware.OpenHypergraph
public import Obend.Hardware.QuantumMatter
public import Obend.Analysis.Equitable
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.QuantumMatter
import all Obend.Analysis.Equitable

public section

namespace Obend.Hardware.OpenHypergraphQuotient
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.QuantumMatter
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. Decidable Causal SSA, General Quotient Certificate & Equitable Incidence Matrix -/

/-- Exact source-wire arity for each `HypergraphOp`. -/
@[expose] def hypergraphOpArity : HypergraphOp → Nat
  | .const _ => 0 | .scale _ => 1 | .add | .sub | .mul => 2 | .mac | .mux => 3

/-- Decidable list-order causal SSA certificate on `edges`. -/
@[expose] def checkEdgesCausalSSA (numWires : Nat) (inWires : List Nat) (edges : List HyperEdge) : Bool :=
  edges.all (fun e =>
    (e.srcWires.length == hypergraphOpArity e.op) &&
    decide (e.dstWire < numWires) && e.srcWires.all (fun u => decide (u < numWires))) &&
  inWires.all (fun w => decide (w < numWires) && !(edges.any (fun e => e.dstWire == w))) &&
  (List.range edges.length).all (fun i =>
    match edges[i]? with
    | none => false
    | some e =>
      !(e.srcWires.contains e.dstWire) &&
      (edges.drop (i + 1)).all (fun e' => (e'.dstWire != e.dstWire) && !(e.srcWires.contains e'.dstWire)))

/-- Decidable causal SSA certificate for a `StrictOpenHypergraph`. -/
@[expose] def checkHypergraphCausalSSA (G : StrictOpenHypergraph) : Bool :=
  checkEdgesCausalSSA G.nodeTypes.length G.boundaryIn.table (extractHyperEdges G)

/-- Decidable general equitable quotient homomorphism certificate between `StrictOpenHypergraph`s. -/
@[expose] def checkHypergraphQuotient
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) : Bool :=
  let nG := G.nodeTypes.length; let nQ := Q.nodeTypes.length
  let edgesG := extractHyperEdges G; let edgesQ := extractHyperEdges Q
  G.wf && Q.wf && checkHypergraphCausalSSA G && checkHypergraphCausalSSA Q &&
  (List.range nG).all (fun w =>
    decide (wireClass w < nQ) &&
    ((edgesG.any (fun e => e.dstWire == w)) == (edgesQ.any (fun e => e.dstWire == wireClass w)))) &&
  (List.range nQ).all (fun q => decide (1 ≤ cellSize (List.range nG) wireClass q)) &&
  G.boundaryIn.table.all (fun w => Q.boundaryIn.table.contains (wireClass w)) &&
  G.boundaryOut.table.all (fun w => Q.boundaryOut.table.contains (wireClass w)) &&
  (List.range edgesG.length).all (fun i =>
    match edgesG[i]?, edgesQ[edgeClass i]? with
    | some eG, some eQ =>
      decide (edgeClass i < edgesQ.length) && (wireClass eG.dstWire == eQ.dstWire) &&
      (eG.op == eQ.op) && (eG.srcWires.map wireClass == eQ.srcWires)
    | _, _ => false)

/-- Wire-to-wire incidence matrix of `G`: `(u, v)` counts occurrences of `v` in the unique edge writing `u`. -/
@[expose] def hypergraphIncidenceMatrix (G : StrictOpenHypergraph) : IntMatrix :=
  let wires := List.range G.nodeTypes.length; let edges := extractHyperEdges G
  { dim  := G.nodeTypes.length
  , rows := wires.map (fun u =>
      match edges.find? (fun e => e.dstWire == u) with
      | none => wires.map (fun _ => (0 : Int))
      | some e => wires.map (fun v => (e.srcWires.count v : Int))) }

private theorem mem_iff_exists_getElem? {α : Type} {xs : List α} {x : α} :
    x ∈ xs ↔ ∃ i, i < xs.length ∧ xs[i]? = some x :=
  ⟨fun h => by obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h; exact ⟨i, hi, List.getElem?_eq_getElem hi⟩,
   fun ⟨i, hi, hG⟩ => by rw [List.getElem?_eq_getElem hi] at hG; injection hG with h; exact h ▸ List.getElem_mem hi⟩

private theorem cellMembers_range_nodup (n : Nat) (part : Nat → Nat) (q : Nat) :
    (cellMembers (List.range n) part q).Nodup := List.Pairwise.filter _ List.nodup_range

private theorem mem_cellMembers_range (n : Nat) (part : Nat → Nat) (q w : Nat) :
    w ∈ cellMembers (List.range n) part q ↔ w < n ∧ part w = q := by
  simp [cellMembers, List.mem_filter, List.mem_range]

private theorem sumIntOver_ite_eq_of_nodup (c : Int) (target : Nat) :
    ∀ (xs : List Nat), xs.Nodup → sumIntOver (fun v => if v == target then c else 0) xs = if target ∈ xs then c else 0
  | [], _ => by simp [sumIntOver]
  | x :: xs, hN => by
    obtain ⟨hxNot, hRest⟩ := List.nodup_cons.mp hN
    dsimp only [sumIntOver]; rw [sumIntOver_ite_eq_of_nodup c target xs hRest]
    by_cases h : x = target
    · subst x; simp [hxNot]
    · simp [h, Ne.symm h, List.mem_cons]

private theorem sumIntOver_count_cellMembers (n : Nat) (part : Nat → Nat) (q : Nat) :
    ∀ (ws : List Nat), (∀ x ∈ ws, x < n) →
      sumIntOver (fun v => (ws.count v : Int)) (cellMembers (List.range n) part q) = ((ws.map part).count q : Int)
  | [], _ => by simp [sumIntOver_zero]
  | x :: xs, hB => by
    have hStep : ∀ v : Nat, ((x :: xs).count v : Int) = (if v == x then (1 : Int) else 0) + (xs.count v : Int) := fun v => by
      rw [List.count_cons]; by_cases hEq : v = x; (subst hEq; simp; omega); simp [beq_false_of_ne (Ne.symm hEq), beq_false_of_ne hEq]
    rw [sumIntOver_congr _ _ _ (fun v _ => hStep v), sumIntOver_add,
        sumIntOver_ite_eq_of_nodup 1 x _ (cellMembers_range_nodup n part q),
        sumIntOver_count_cellMembers n part q xs (fun y hy => hB y (List.mem_cons_of_mem x hy)), List.map_cons, List.count_cons]
    by_cases hP : part x = q
    · simp [(mem_cellMembers_range n part q x).mpr ⟨hB x List.mem_cons_self, hP⟩, hP]; omega
    · simp [show x ∉ cellMembers (List.range n) part q from fun h => hP ((mem_cellMembers_range n part q x).mp h).2, beq_false_of_ne hP]

/-- Unpacked semantic properties guaranteed by `checkEdgesCausalSSA`. -/
structure CausalSSASpec (numWires : Nat) (inWires : List Nat) (edges : List HyperEdge) : Prop where
  arity_ok : ∀ e ∈ edges, e.srcWires.length = hypergraphOpArity e.op
  dst_lt : ∀ e ∈ edges, e.dstWire < numWires
  src_lt : ∀ e ∈ edges, ∀ u ∈ e.srcWires, u < numWires
  in_lt : ∀ w ∈ inWires, w < numWires
  in_disjoint : ∀ w ∈ inWires, ∀ e ∈ edges, e.dstWire ≠ w
  dst_nodup : ∀ i j, i < edges.length → j < edges.length → i ≠ j →
    ∀ ei ej, edges[i]? = some ei → edges[j]? = some ej → ei.dstWire ≠ ej.dstWire
  causal : ∀ i j, i < edges.length → j < edges.length → i ≤ j →
    ∀ ei ej, edges[i]? = some ei → edges[j]? = some ej → ej.dstWire ∉ ei.srcWires

theorem checkEdgesCausalSSA_sound (numWires : Nat) (inWires : List Nat) (edges : List HyperEdge)
    (hCheck : checkEdgesCausalSSA numWires inWires edges = true) : CausalSSASpec numWires inWires edges := by
  simp only [checkEdgesCausalSSA, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true', List.any_eq_false] at hCheck
  obtain ⟨⟨hE, hIn⟩, hIdx⟩ := hCheck
  have pair i j (hi : i < edges.length) (hj : j < edges.length) (lt : i < j) ei ej
      (hei : edges[i]? = some ei) (hej : edges[j]? = some ej) : ej.dstWire ≠ ei.dstWire ∧ ej.dstWire ∉ ei.srcWires := by
    have h := hIdx i hi; rw [hei] at h; simp only [Bool.and_eq_true] at h
    have mem : ej ∈ edges.drop (i + 1) := List.mem_of_getElem? (i := j - (i + 1))
      (by rw [List.getElem?_drop, show i + 1 + (j - (i + 1)) = j by omega]; exact hej)
    simpa using (List.all_eq_true.mp h.2 ej mem)
  refine ⟨fun e he => (hE e he).1.1, fun e he => (hE e he).1.2, fun e he => (hE e he).2,
    fun w hw => (hIn w hw).1, fun w hw => by simpa using (hIn w hw).2, ?_, ?_⟩
  · intro i j hi hj hne ei ej hei hej
    by_cases h : i < j; exact (pair i j hi hj h ei ej hei hej).1.symm
    exact (pair j i hj hi (by omega) ej ei hej hei).1
  · intro i j hi hj hle ei ej hei hej
    obtain rfl | lt := Nat.eq_or_lt_of_le hle
    · have h := hIdx i hi; rw [hei] at h; rw [hei] at hej
      cases hej; simp only [Bool.and_eq_true] at h; simpa using h.1
    · exact (pair i j hi hj lt ei ej hei hej).2

private theorem find?_eq_some_of_causalSSA {n : Nat} {inW : List Nat} {es : List HyperEdge}
    (hSSA : CausalSSASpec n inW es) {e : HyperEdge} (he : e ∈ es) : es.find? (fun e' => e'.dstWire == e.dstWire) = some e := by
  cases hF : es.find? (fun e' => e'.dstWire == e.dstWire) with
  | none => exact absurd (beq_self_eq_true e.dstWire) (by simpa using List.find?_eq_none.mp hF e he)
  | some e' =>
    obtain ⟨i, hi, hei⟩ := mem_iff_exists_getElem?.mp he
    obtain ⟨j, hj, hej⟩ := mem_iff_exists_getElem?.mp (List.mem_of_find?_eq_some hF)
    have found := List.find?_some hF
    have dst := beq_iff_eq.mp found
    by_cases h : j = i; subst j; exact hej.symm.trans hei
    exact absurd dst (hSSA.dst_nodup j i hj hi h e' e hej hei)

/-- Unpacked semantic properties guaranteed by `checkHypergraphQuotient`. -/
structure QuotientHomSpec (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) : Prop where
  wfG : G.wf = true
  wfQ : Q.wf = true
  ssaG : CausalSSASpec G.nodeTypes.length G.boundaryIn.table (extractHyperEdges G)
  ssaQ : CausalSSASpec Q.nodeTypes.length Q.boundaryIn.table (extractHyperEdges Q)
  wire_lt : ∀ w < G.nodeTypes.length, wireClass w < Q.nodeTypes.length
  dst_align : ∀ w < G.nodeTypes.length,
    ((extractHyperEdges G).any (fun e => e.dstWire == w)) = ((extractHyperEdges Q).any (fun e => e.dstWire == wireClass w))
  cell_nonempty : ∀ q < Q.nodeTypes.length, 1 ≤ cellSize (List.range G.nodeTypes.length) wireClass q
  in_align : ∀ w ∈ G.boundaryIn.table, wireClass w ∈ Q.boundaryIn.table
  out_align : ∀ w ∈ G.boundaryOut.table, wireClass w ∈ Q.boundaryOut.table
  edge_hom : ∀ i < (extractHyperEdges G).length, ∀ eG, (extractHyperEdges G)[i]? = some eG →
    edgeClass i < (extractHyperEdges Q).length ∧
    ∃ eQ, (extractHyperEdges Q)[edgeClass i]? = some eQ ∧
      wireClass eG.dstWire = eQ.dstWire ∧ eG.op = eQ.op ∧ eG.srcWires.map wireClass = eQ.srcWires

theorem checkHypergraphQuotient_sound (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat)
    (hCheck : checkHypergraphQuotient G Q wireClass edgeClass = true) : QuotientHomSpec G Q wireClass edgeClass := by
  simp only [checkHypergraphQuotient, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at hCheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨wg,wq⟩,sg⟩,sq⟩,wires⟩,cells⟩,ins⟩,outs⟩,edges⟩ := hCheck
  refine ⟨wg,wq,checkEdgesCausalSSA_sound _ _ _ sg,checkEdgesCausalSSA_sound _ _ _ sq,
    fun w hw => (wires w hw).1, fun w hw => (wires w hw).2, cells, ins, outs, ?_⟩
  intro i hi e he; have h := edges i hi; rw [he] at h
  cases ht : (extractHyperEdges Q)[edgeClass i]? with
  | none => simp [ht] at h
  | some t => simp [ht] at h; exact ⟨h.1.1.1, t, rfl, h.1.1.2, h.1.2, h.2⟩

private theorem hypergraphIncidenceMatrix_entry (G : StrictOpenHypergraph) (u v : Nat)
    (hu : u < G.nodeTypes.length) (hv : v < G.nodeTypes.length) :
    (hypergraphIncidenceMatrix G).entry u v =
      match (extractHyperEdges G).find? (fun e => e.dstWire == u) with | none => 0 | some e => (e.srcWires.count v : Int) := by
  unfold hypergraphIncidenceMatrix IntMatrix.entry listGetInt
  simp only [List.getElem?_map, List.getElem?_range hu, Option.map_some]
  cases (extractHyperEdges G).find? (fun e => e.dstWire == u) <;> simp [List.getElem?_map, List.getElem?_range hv]

/-- A quotient certificate also certifies the equitable partition of the wire incidence matrix. -/
theorem checkHypergraphQuotient_implies_equitablePartition
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat)
    (hCheck : checkHypergraphQuotient G Q wireClass edgeClass = true) :
    checkEquitablePartition (hypergraphIncidenceMatrix G) Q.nodeTypes.length wireClass
      (hypergraphIncidenceMatrix Q).entry = true := by
  have hHom := checkHypergraphQuotient_sound G Q wireClass edgeClass hCheck
  unfold checkEquitablePartition; rw [show (hypergraphIncidenceMatrix G).dim = G.nodeTypes.length from rfl]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨hHom.wire_lt, hHom.cell_nonempty⟩, fun u hu q hq => ?_⟩
  have hwu := hHom.wire_lt u hu; unfold cellRowSum
  cases hAnyG : (extractHyperEdges G).any (fun e => e.dstWire == u) with
  | false =>
    have absent (es : List HyperEdge) (p : HyperEdge → Bool) (h : es.any p = false) : es.find? p = none := by
      simpa [List.find?_eq_none, List.any_eq_false] using h
    have hFG := absent _ _ hAnyG; have hFQ := absent _ _ ((hHom.dst_align u hu).symm.trans hAnyG)
    rw [hypergraphIncidenceMatrix_entry Q (wireClass u) q hwu hq, hFQ,
        sumIntOver_congr _ (fun _ => 0) _ (fun v hv => by rw [hypergraphIncidenceMatrix_entry G u v hu ((mem_cellMembers_range _ _ _ _).mp hv).1, hFG]), sumIntOver_zero]
  | true =>
    obtain ⟨eG, heGM, heGD⟩ := List.any_eq_true.mp hAnyG; have hDstEq := beq_iff_eq.mp heGD
    obtain ⟨i, hi, hei⟩ := mem_iff_exists_getElem?.mp heGM
    obtain ⟨hj, eQ, heQ, hQDst, _, hSrcMap⟩ := hHom.edge_hom i hi eG hei
    have hFG : (extractHyperEdges G).find? (fun e => e.dstWire == u) = some eG := hDstEq ▸ find?_eq_some_of_causalSSA hHom.ssaG heGM
    have hFQ : (extractHyperEdges Q).find? (fun e => e.dstWire == wireClass u) = some eQ := by
      rw [← hDstEq, hQDst]; exact find?_eq_some_of_causalSSA hHom.ssaQ (mem_iff_exists_getElem?.mpr ⟨edgeClass i, hj, heQ⟩)
    rw [hypergraphIncidenceMatrix_entry Q (wireClass u) q hwu hq, hFQ,
        sumIntOver_congr _ (fun v => (eG.srcWires.count v : Int)) _
          (fun v hv => by rw [hypergraphIncidenceMatrix_entry G u v hu ((mem_cellMembers_range _ _ _ _).mp hv).1, hFG]),
        sumIntOver_count_cellMembers G.nodeTypes.length wireClass q eG.srcWires (hHom.ssaG.src_lt eG heGM), hSrcMap]

/-! ## 2. General Forward Intertwining (`evalHypergraph_quotient_intertwines_general`) -/

/-- A single-assignment sweep can interpret the same wiring with a different local update. -/
private def writeWire (v : Nat → Int) (u : Nat) (x : Int) := fun w => if w == u then x else v w
private def sweep (rule : HyperEdge → (Nat → Int) → Int) (v : Nat → Int) (es : List HyperEdge) :=
  es.foldl (fun t e => writeWire t e.dstWire (rule e t)) v

private theorem sweep_untouched (rule : HyperEdge → (Nat → Int) → Int) (w : Nat) (es : List HyperEdge)
    (v : Nat → Int) (h : ∀ e ∈ es, e.dstWire ≠ w) : sweep rule v es w = v w := by
  induction es generalizing v with
  | nil => rfl
  | cons e rest ih =>
    change sweep rule (writeWire v _ _) rest w = _
    rw [ih _ (fun t ht => h t (by simp [ht]))]; simp [writeWire, Ne.symm (h e (by simp))]

private theorem sweep_at_edge {n i : Nat} {ins : List Nat} {es : List HyperEdge} {e : HyperEdge}
    (ssa : CausalSSASpec n ins es) (get : es[i]? = some e) (rule : HyperEdge → (Nat → Int) → Int) (v : Nat → Int) :
    let before := sweep rule v (es.take i)
    sweep rule v es e.dstWire = rule e before ∧ before e.dstWire = v e.dstWire ∧
      ∀ w ∈ e.srcWires, before w = sweep rule v es w := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp get
  have splitAt : es = es.take i ++ es[i] :: es.drop (i+1) := by rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have later (t : HyperEdge) (ht : t ∈ es.drop (i+1)) : t.dstWire ≠ es[i].dstWire ∧ t.dstWire ∉ es[i].srcWires := by
    obtain ⟨k, hk, hget⟩ := mem_iff_exists_getElem?.mp ht
    rw [List.getElem?_drop] at hget; rw [List.length_drop] at hk
    exact And.intro (ssa.dst_nodup _ i (by omega) hi (by omega) t _ hget get)
      (ssa.causal i _ hi (by omega) (by omega) _ t get hget)
  have run : sweep rule v es = sweep rule (writeWire (sweep rule v (es.take i)) es[i].dstWire
      (rule es[i] (sweep rule v (es.take i)))) (es.drop (i+1)) := by
    conv => lhs; rw [splitAt]; simp only [sweep, List.foldl_append, List.foldl_cons]
    rfl
  refine ⟨by rw [run, sweep_untouched _ _ _ _ (fun t ht => (later t ht).1)]; simp [writeWire], ?_, ?_⟩
  · apply sweep_untouched; intro t ht; obtain ⟨k, hk, hget⟩ := mem_iff_exists_getElem?.mp ht
    simp only [List.length_take] at hk; rw [List.getElem?_take_of_lt (by omega)] at hget
    exact ssa.dst_nodup k i (by omega) hi (by omega) t _ hget get
  · intro w hw; rw [run, sweep_untouched _ _ _ _ (fun t ht h => (later t ht).2 (h ▸ hw))]
    simp [writeWire, show w ≠ es[i].dstWire from fun h => ssa.causal i i hi hi (Nat.le_refl _) _ _ get get (h ▸ hw)]

private theorem boundaryOut_lt_of_wf (G : StrictOpenHypergraph) (hWf : G.wf = true) : ∀ w ∈ G.boundaryOut.table, w < G.nodeTypes.length := by
  unfold StrictOpenHypergraph.wf at hWf; simp only [Bool.and_eq_true] at hWf
  have hBnd := hWf.1.1.1.1.1.1.2; unfold FiniteFunction.wf at hBnd; simp only [Bool.and_eq_true] at hBnd
  intro w hw; rw [← beq_iff_eq.mp hWf.2]; exact of_decide_eq_true ((list_all_iff_forall _ _).mp hBnd.2 w hw)

private theorem sweep_quotient {G Q : StrictOpenHypergraph} {wireClass edgeClass : Nat → Nat}
    (hHom : QuotientHomSpec G Q wireClass edgeClass) (rG rQ : HyperEdge → (Nat → Int) → Int)
    (initEnvG initEnvQ : Nat → Int) (hInit : ∀ w < G.nodeTypes.length, (∀ e ∈ extractHyperEdges G, e.dstWire ≠ w) → initEnvG w = initEnvQ (wireClass w))
    (compatible : ∀ e ∈ extractHyperEdges G, ∀ t : HyperEdge, wireClass e.dstWire = t.dstWire → e.op = t.op → e.srcWires.map wireClass = t.srcWires →
      ∀ {v z : Nat → Int}, v e.dstWire = initEnvG e.dstWire → z t.dstWire = initEnvQ t.dstWire → (∀ u ∈ e.srcWires, v u = z (wireClass u)) → rG e v = rQ t z) :
    ∀ w < G.nodeTypes.length, sweep rG initEnvG (extractHyperEdges G) w = sweep rQ initEnvQ (extractHyperEdges Q) (wireClass w) := by
  let E := extractHyperEdges G; let F := extractHyperEdges Q
  let rec hW (limit w : Nat) (hw : w < G.nodeTypes.length)
      (ready : ∀ i e, E[i]? = some e → e.dstWire = w → i < limit) :
      sweep rG initEnvG E w = sweep rQ initEnvQ F (wireClass w) := by
    cases ha : E.any (fun e => e.dstWire == w) with
    | false =>
      have hb := (hHom.dst_align w hw).symm.trans ha
      simp only [List.any_eq_false, beq_iff_eq] at ha hb
      rw [sweep_untouched _ _ _ _ ha, sweep_untouched _ _ _ _ hb, hInit w hw ha]
    | true =>
      obtain ⟨e, he, hd⟩ := List.any_eq_true.mp ha
      obtain ⟨i, hi, hei⟩ := mem_iff_exists_getElem?.mp he
      obtain ⟨hj, t, het, hdst, hop, hsrc⟩ := hHom.edge_hom i hi e hei
      obtain ⟨outG, oldG, srcG⟩ := sweep_at_edge hHom.ssaG hei rG initEnvG
      obtain ⟨outQ, oldQ, srcQ⟩ := sweep_at_edge hHom.ssaQ het rQ initEnvQ
      rw [← beq_iff_eq.mp hd, hdst, outG, outQ]; refine compatible e he t hdst hop hsrc oldG oldQ fun u hu => ?_
      rw [srcG u hu, srcQ _ (hsrc ▸ List.mem_map_of_mem hu)]
      apply hW i u (hHom.ssaG.src_lt e he u hu); intro j t get dst
      obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp get
      exact Nat.lt_of_not_ge fun le => hHom.ssaG.causal i j hi hj' le e t hei get (dst ▸ hu)
  termination_by limit
  decreasing_by exact ready i e hei (beq_iff_eq.mp hd)
  exact fun w hw => hW E.length w hw fun _ _ get _ => by obtain ⟨lt, _⟩ := List.getElem?_eq_some_iff.mp get; exact lt

/-- A certified quotient intertwines the wire evaluator and all three boundary evaluators. Initial environments need to agree on undriven wires only. -/
theorem evalHypergraph_quotient_intertwines_general
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) (initEnvG initEnvQ : Nat → Int)
    (hQuot : checkHypergraphQuotient G Q wireClass edgeClass = true)
    (hInit : ∀ w < G.nodeTypes.length, (∀ e ∈ extractHyperEdges G, e.dstWire ≠ w) → initEnvG w = initEnvQ (wireClass w)) :
    (∀ w < G.nodeTypes.length,
      evalHyperEdgesComb initEnvG (extractHyperEdges G) w = evalHyperEdgesComb initEnvQ (extractHyperEdges Q) (wireClass w)) ∧
    evalHypergraphComb G initEnvG = (G.boundaryOut.table.map wireClass).map (evalHyperEdgesComb initEnvQ (extractHyperEdges Q)) ∧
    evalHypergraphLayered G initEnvG = (G.boundaryOut.table.map wireClass).map (evalHyperEdgesComb initEnvQ (extractHyperEdges Q)) ∧
    evalHypergraphLayeredSync G initEnvG = (G.boundaryOut.table.map wireClass).map (evalHyperEdgesComb initEnvQ (extractHyperEdges Q)) := by
  have hHom := checkHypergraphQuotient_sound G Q wireClass edgeClass hQuot
  have hW : ∀ w < G.nodeTypes.length, evalHyperEdgesComb initEnvG (extractHyperEdges G) w =
      evalHyperEdgesComb initEnvQ (extractHyperEdges Q) (wireClass w) := by
    let rule := fun (e : HyperEdge) (v : Nat → Int) => evalHypergraphOp e.op (e.srcWires.map v)
    apply sweep_quotient hHom rule rule _ _ hInit
    intro e _ t _ op src v z _ _ inputs; simp only [rule, op, ← src, List.map_map]; congr 1; exact List.map_congr_left inputs
  have hComb : evalHypergraphComb G initEnvG = (G.boundaryOut.table.map wireClass).map (evalHyperEdgesComb initEnvQ (extractHyperEdges Q)) := by
    unfold evalHypergraphComb; rw [List.map_map]; exact List.map_congr_left fun w hw => hW w (boundaryOut_lt_of_wf G hHom.wfG w hw)
  have hP := evalHypergraph_pipelined_eq_comb G initEnvG
  exact ⟨hW, hComb, hP.1.trans hComb, hP.2.trans hComb⟩

/-! ## 3. General Reverse-Mode Adjoint Intertwining (`adjoint_quotient_intertwines_general`) -/

/-- Orbit-summed cotangent pushforward from full graph `G` onto quotient wire `q`. -/
@[expose] def orbitSumCot (numWiresG : Nat) (wireClass : Nat → Nat) (cotG : Nat → Int) (q : Nat) : Int :=
  sumIntOver cotG (cellMembers (List.range numWiresG) wireClass q)

/-- Mathematical seed cotangent map corresponding to `seedCotangentStateAux`. -/
def seedCotangentSpec (seedStart : Nat) (outWires : List Nat) (env : Nat → Int) : Nat → Int :=
  match outWires with | [] => fun _ => 0 | wOut :: rest => addSpecCotangent wOut (env seedStart) (seedCotangentSpec (seedStart + 1) rest env)

private theorem accumSpecCotangents_nil (cot : Nat → Int) : accumSpecCotangents [] cot = cot := rfl
private theorem accumSpecCotangents_cons (p : Nat × Int) (rest : List (Nat × Int)) (cot : Nat → Int) :
    accumSpecCotangents (p :: rest) cot = accumSpecCotangents rest (addSpecCotangent p.1 p.2 cot) := rfl
private theorem specGradRevOrder_nil (fwd cot : Nat → Int) : specGradRevOrder fwd [] cot = cot := rfl
private theorem specGradRevOrder_cons (fwd : Nat → Int) (e : HyperEdge) (rest : List HyperEdge) (cot : Nat → Int) :
    specGradRevOrder fwd (e :: rest) cot = specGradRevOrder fwd rest (specGradEdgeStep fwd e cot) := rfl
private theorem specGradRevOrder_append (fwd : Nat → Int) (es1 es2 : List HyperEdge) (cot : Nat → Int) :
    specGradRevOrder fwd (es1 ++ es2) cot = specGradRevOrder fwd es2 (specGradRevOrder fwd es1 cot) := List.foldl_append

private theorem wireAt_mem_of_lt {ws : List Nat} {i : Nat} (hi : i < ws.length) : wireAt ws i ∈ ws := by
  induction ws generalizing i with | nil => simp at hi | cons w rest ih => cases i with | zero => exact List.mem_cons_self | succ k => exact List.mem_cons_of_mem w (ih (by simp at hi; omega))

private theorem wireAt_map (f : Nat → Nat) (ws : List Nat) (i : Nat) (hi : i < ws.length) : f (wireAt ws i) = wireAt (ws.map f) i := by
  induction ws generalizing i with | nil => simp at hi | cons w rest ih => cases i with | zero => rfl | succ k => exact ih k (by simp at hi; omega)

private theorem specGradRevOrder_congr (fwd : Nat → Int) (P : Nat → Prop) :
    ∀ (es : List HyperEdge) (c1 c2 : Nat → Int),
      (∀ e ∈ es, P e.dstWire) → (∀ w, P w → c1 w = c2 w) → ∀ w, P w → specGradRevOrder fwd es c1 w = specGradRevOrder fwd es c2 w
  | [], _, _, _, hEq, w, hw => hEq w hw
  | e :: rest, c1, c2, hP, hEq, w, hw => by
    rw [specGradRevOrder_cons, specGradRevOrder_cons]
    apply specGradRevOrder_congr fwd P rest _ _ (fun x hx => hP x (List.mem_cons_of_mem e hx)) _ w hw
    intro u hu; unfold specGradEdgeStep; rw [hEq e.dstWire (hP e List.mem_cons_self)]
    induction specEdgeLocalPullback fwd e (c2 e.dstWire) generalizing c1 c2 u with
    | nil => exact hEq u hu
    | cons p ps ihP => rw [accumSpecCotangents_cons, accumSpecCotangents_cons]; exact ihP _ _ (fun z hz => by unfold addSpecCotangent; rw [hEq z hz]) u hu

/-- Pairing a cotangent with a tangent converts reverse accumulation to a forward sweep. -/
private def pairing (n : Nat) (c v : Nat → Int) := sumIntOver (fun w => c w * v w) (List.range n)
private def slope (fwd : Nat → Int) (e : HyperEdge) (v : Nat → Int) : Int :=
  ((specEdgeLocalPullback fwd e 1).map fun p => p.2 * v p.1).sum
-- Adding the destination's incoming tangent models an independent perturbation even at an internal wire.
private def tangentRule (fwd : Nat → Int) (e : HyperEdge) (v : Nat → Int) := v e.dstWire + slope fwd e v

private theorem pairing_add {n u : Nat} (hu : u < n) (d : Int) (c v : Nat → Int) :
    pairing n (addSpecCotangent u d c) v = pairing n c v + d * v u := by
  unfold pairing; rw [← sumIntOver_ite_range_eq (d * v u) u n hu, ← sumIntOver_add]
  apply sumIntOver_congr; intro w _; by_cases h : w = u <;> simp [addSpecCotangent, h, Ne.symm, Int.add_mul]

private theorem pairing_comm (n : Nat) (c v : Nat → Int) : pairing n c v = pairing n v c :=
  sumIntOver_congr _ _ _ fun _ _ => Int.mul_comm ..

private theorem pairing_step {n : Nat} (fwd c v : Nat → Int) (e : HyperEdge) (ha : e.srcWires.length = hypergraphOpArity e.op)
    (hd : e.dstWire < n) (hs : ∀ u ∈ e.srcWires, u < n) :
    pairing n (specGradEdgeStep fwd e c) v = pairing n c (writeWire v e.dstWire (tangentRule fwd e v)) := by
  have update : writeWire v e.dstWire (tangentRule fwd e v) = addSpecCotangent e.dstWire (slope fwd e v) v := by
    funext w; by_cases h : w = e.dstWire <;> simp [writeWire, tangentRule, addSpecCotangent, h]
  rw [update, pairing_comm n c (addSpecCotangent _ _ _), pairing_add hd, pairing_comm n v c]
  have bound (i : Nat) (hi : i < hypergraphOpArity e.op) : wireAt e.srcWires i < n := hs _ (wireAt_mem_of_lt (ha ▸ hi))
  rcases e with ⟨_, op, src, dst⟩; dsimp only at bound; cases op <;> simp only [hypergraphOpArity] at bound <;>
    simp (disch := exact bound _ (by decide)) [specGradEdgeStep, slope, specEdgeLocalPullback, accumSpecCotangents_cons,
      accumSpecCotangents_nil, pairing_add] <;> (repeat' split <;> simp_all) <;> grind only

private theorem pairing_reverse {n : Nat} (fwd : Nat → Int) (es : List HyperEdge) (v c : Nat → Int)
    (valid : ∀ e ∈ es, e.srcWires.length = hypergraphOpArity e.op ∧ e.dstWire < n ∧ ∀ w ∈ e.srcWires, w < n) :
    pairing n (specGradEdges fwd es c) v = pairing n c (sweep (tangentRule fwd) v es) := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    simp only [specGradEdges, List.reverse_cons, specGradRevOrder_append, specGradRevOrder_cons, specGradRevOrder_nil]
    obtain ⟨ha, hd, hs⟩ := valid e (by simp)
    rw [pairing_step fwd _ v e ha hd hs]; exact ih _ (fun t ht => valid t (by simp [ht]))

private theorem tangent_compatible {p : Nat → Nat} {f g v z : Nat → Int} {e t : HyperEdge}
    (ha : e.srcWires.length = hypergraphOpArity e.op) (op : e.op = t.op) (src : e.srcWires.map p = t.srcWires)
    (primal : ∀ u ∈ e.srcWires, f u = g (p u)) (dst : v e.dstWire = z t.dstWire)
    (tan : ∀ u ∈ e.srcWires, v u = z (p u)) : tangentRule f e v = tangentRule g t z := by
  rcases e with ⟨_, o, ws, _⟩; rcases t with ⟨_, ot, wt, _⟩; dsimp only at *; subst ot wt
  have atWire (i : Nat) (hi : i < hypergraphOpArity o) : f (wireAt ws i) = g (wireAt (ws.map p) i) ∧ v (wireAt ws i) = z (wireAt (ws.map p) i) := by
    have mem := wireAt_mem_of_lt (ws := ws) (ha ▸ hi)
    exact And.intro ((primal _ mem).trans (congrArg g (wireAt_map p ws i (ha ▸ hi))))
      ((tan _ mem).trans (congrArg z (wireAt_map p ws i (ha ▸ hi))))
  have primalAt := fun i hi => (atWire i hi).1
  have tangentAt := fun i hi => (atWire i hi).2
  cases o <;> simp only [hypergraphOpArity] at primalAt tangentAt <;> simp (disch := decide) [tangentRule, slope, specEdgeLocalPullback, dst, primalAt, tangentAt]

private theorem pairing_orbit {n m : Nat} {p : Nat → Nat} (bound : ∀ w < n, p w < m) (c v : Nat → Int) :
    pairing n c (fun w => v (p w)) = pairing m (orbitSumCot n p c) v := by
  unfold pairing; rw [← sumIntOver_cellMembers_partition _ p m (List.range n) (fun w hw => bound w (List.mem_range.mp hw))]
  apply sumIntOver_congr; intro q _; unfold orbitSumCot; rw [← sumIntOver_mul_right]
  exact sumIntOver_congr _ _ _ fun w hw => by dsimp only; rw [((mem_cellMembers_range _ _ _ _).mp hw).2]

private theorem pairing_indicator (c : Nat → Int) (p : Nat → Nat) (q : Nat) (xs : List Nat) :
    sumIntOver (fun w => c w * (if p w == q then 1 else 0)) xs = sumIntOver c (cellMembers xs p q) := by
  induction xs with
  | nil => rfl
  | cons w xs ih => rw [sumIntOver_cons, sumIntOver_cellMembers_cons, ih]; cases p w == q <;> simp

private theorem specGradRevOrder_scale (fwd : Nat → Int) (s : Int) (es : List HyperEdge) (cot : Nat → Int) :
    specGradRevOrder fwd es (fun w => s * cot w) = fun w => s * specGradRevOrder fwd es cot w := by
  induction es generalizing cot with
  | nil => rfl
  | cons e rest ih =>
    simp only [specGradRevOrder_cons, ← ih]
    congr 1; funext w; rcases e with ⟨_, op, src, dst⟩
    cases op <;> simp only [specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents_cons,
      accumSpecCotangents_nil, addSpecCotangent] <;> (repeat' split <;> simp_all) <;> grind

private theorem accumWireCotangent_preserves_invariant
    (numPrimal : Nat) (fwdEnv specCot : Nat → Int) (w seedWire : Nat) (st : CotangentBuilderState)
    (hInv : CotStateInvariant numPrimal fwdEnv specCot st) (hSeedLt : seedWire < st.nextWire)
    (hSeedVal : evalHyperEdgesComb fwdEnv st.revEdges seedWire = fwdEnv seedWire) :
    CotStateInvariant numPrimal fwdEnv (addSpecCotangent w (fwdEnv seedWire) specCot) (accumWireCotangent w seedWire st) ∧
    st.nextWire ≤ (accumWireCotangent w seedWire st).nextWire ∧
    (∀ u < st.nextWire, evalHyperEdgesComb fwdEnv (accumWireCotangent w seedWire st).revEdges u = evalHyperEdgesComb fwdEnv st.revEdges u) := by
  rcases st with ⟨cotMap, nextWire, revEdges⟩; unfold accumWireCotangent; dsimp only at hSeedLt hSeedVal ⊢
  cases hUp : upsertCotWire w seedWire nextWire cotMap with
  | mk opt cotMap' =>
    have look : cotMap.lookup w = opt := by rw [← upsertCotWire_fst w seedWire nextWire cotMap, hUp]
    have updated := congrArg Prod.snd hUp
    have other u (hu : (u == w) = false) := upsertCotWire_snd_lookup_ne w u seedWire nextWire cotMap hu
    have self := upsertCotWire_snd_lookup_self w seedWire nextWire cotMap
    rw [updated] at self; rw [look] at self
    have primal := hInv.primal_le_next
    cases opt <;> dsimp only at *
    all_goals
      refine (fun facts (keep : _ → _) => And.intro (keep facts) facts) (And.intro (by omega) ?_) ?_
      · intro u hu; first | rfl | (rw [evalHyperEdgesComb_append, evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]; apply stepHyperEdge_ne; dsimp; omega)
      rintro ⟨inc, below⟩; refine ⟨Nat.le_trans primal inc, fun u hu => (below u (by omega)).trans (hInv.primal_preserved u hu), fun u hn => ?_, fun u cw hs => ?_⟩
      · by_cases h : u = w
        · subst u; simp_all
        · rw [← updated, other u (beq_false_of_ne h)] at hn; simp [addSpecCotangent, h, hInv.lookup_none u hn]
      · by_cases h : u = w
        · subst u; rw [self] at hs; cases hs
          first
          | exact ⟨hSeedLt, by simp [addSpecCotangent, hInv.lookup_none w look, hSeedVal]⟩
          | obtain ⟨_, val⟩ := hInv.lookup_some _ _ look; dsimp only at val
            exact ⟨by dsimp only; omega, by simp [evalHyperEdgesComb_append, evalHyperEdgesComb_cons, evalHyperEdgesComb_nil,
              stepHyperEdge, evalHypergraphOp, addSpecCotangent, val, hSeedVal]⟩
        · rw [← updated, other u (beq_false_of_ne h)] at hs; obtain ⟨hlt, val⟩ := hInv.lookup_some u cw hs
          exact ⟨Nat.lt_of_lt_of_le hlt inc, by simpa [addSpecCotangent, h] using (below cw hlt).trans val⟩

private theorem seedCotangentStateAux_invariant_gen (numPrimal : Nat) (fwdEnv env : Nat → Int) :
    ∀ (outWires : List Nat) (seedStart : Nat) (accCot : Nat → Int) (st : CotangentBuilderState),
      CotStateInvariant numPrimal fwdEnv accCot st → seedStart + outWires.length ≤ st.nextWire →
      (∀ k < outWires.length, evalHyperEdgesComb fwdEnv st.revEdges (seedStart + k) = fwdEnv (seedStart + k) ∧ fwdEnv (seedStart + k) = env (seedStart + k)) →
      CotStateInvariant numPrimal fwdEnv (fun w => accCot w + seedCotangentSpec seedStart outWires env w) (seedCotangentStateAux seedStart outWires st)
  | [], _, _, _, hInv, _, _ => by simpa only [seedCotangentSpec, seedCotangentStateAux, Int.add_zero] using hInv
  | wOut :: rest, seedStart, accCot, st, hInv, hB, hSeeds => by
    dsimp only [seedCotangentStateAux]; have hS0 := hSeeds 0 (by simp); simp only [Nat.add_zero] at hS0
    obtain ⟨hInv1, _, hBelow1⟩ := accumWireCotangent_preserves_invariant numPrimal fwdEnv accCot wOut seedStart st hInv (by simp at hB; omega) hS0.1
    have hRec := seedCotangentStateAux_invariant_gen numPrimal fwdEnv env rest (seedStart + 1)
      (addSpecCotangent wOut (fwdEnv seedStart) accCot) (accumWireCotangent wOut seedStart st) hInv1 (by simp at hB; omega)
      fun k hk => by
        have hSk := hSeeds (k + 1) (by simp; omega); rw [show seedStart + (k + 1) = seedStart + 1 + k by omega] at hSk
        exact ⟨by rw [hBelow1 _ (by simp at hB; omega), hSk.1], hSk.2⟩
    have hCotEq : (fun w => addSpecCotangent wOut (fwdEnv seedStart) accCot w + seedCotangentSpec (seedStart + 1) rest env w) =
        (fun w => accCot w + seedCotangentSpec seedStart (wOut :: rest) env w) := by
      funext w; by_cases hw : w = wOut <;> simp [seedCotangentSpec, addSpecCotangent, hS0.2, hw] <;> omega
    rwa [hCotEq] at hRec

/-- **Theorem (`seedCotangentStateAux_invariant`)**: Seeding output wires establishes `CotStateInvariant`. -/
theorem seedCotangentStateAux_invariant (numPrimal : Nat) (outWires : List Nat) (fwdEnv env : Nat → Int)
    (hSeedsEq : ∀ k < outWires.length, fwdEnv (numPrimal + k) = env (numPrimal + k)) :
    CotStateInvariant numPrimal fwdEnv (seedCotangentSpec numPrimal outWires env)
      (seedCotangentStateAux numPrimal outWires { cotMap := [], nextWire := numPrimal + outWires.length, revEdges := [] }) := by
  have hGen := seedCotangentStateAux_invariant_gen numPrimal fwdEnv env outWires numPrimal (fun _ => 0)
    { cotMap := [], nextWire := numPrimal + outWires.length, revEdges := [] }
    ⟨Nat.le_add_right _ _, fun _ _ => congrFun (evalHyperEdgesComb_nil fwdEnv) _, fun _ _ => rfl, fun _ _ h => nomatch h⟩
    (Nat.le_refl _) (fun k hk => ⟨congrFun (evalHyperEdgesComb_nil fwdEnv) _, hSeedsEq k hk⟩)
  simpa only [Int.zero_add] using hGen

private theorem wireAt_of_ge : ∀ (ws : List Nat) (i : Nat), ¬ i < ws.length → wireAt ws i = 0
  | [], _, _ => rfl | _ :: _, 0, h => absurd (Nat.zero_lt_succ _) h | _ :: r, i + 1, h => wireAt_of_ge r i (by simp at h; omega)

private theorem edgeSrcBounded_of_bounds {n : Nat} {es : List HyperEdge}
    (hDst : ∀ e ∈ es, e.dstWire < n) (hSrc : ∀ e ∈ es, ∀ u ∈ e.srcWires, u < n) : ∀ e ∈ es, EdgeSrcBounded n e := fun e he i => by
  by_cases hi : i < e.srcWires.length; exact hSrc e he (wireAt e.srcWires i) (wireAt_mem_of_lt hi)
  rw [wireAt_of_ge e.srcWires i hi]; have := hDst e he; omega

/-- Whole-DAG evaluation formula for `compileGraphAdjoint` on any wire-bounded `StrictOpenHypergraph`. -/
theorem compileGraphAdjoint_eval_eq_spec (G : StrictOpenHypergraph) (env : Nat → Int)
    (hOutLt : ∀ w ∈ G.boundaryOut.table, w < G.nodeTypes.length)
    (hDstLt : ∀ e ∈ extractHyperEdges G, e.dstWire < G.nodeTypes.length)
    (hSrcLt : ∀ e ∈ extractHyperEdges G, ∀ u ∈ e.srcWires, u < G.nodeTypes.length) :
    let fwdEnv := evalHyperEdgesComb env (extractHyperEdges G)
    let grad := specGradEdges fwdEnv (extractHyperEdges G) (seedCotangentSpec G.nodeTypes.length G.boundaryOut.table env)
    evalHypergraphComb (compileGraphAdjoint G) env = G.boundaryOut.table.map fwdEnv ++ G.boundaryIn.table.map grad ∧
    evalHypergraphLayered (compileGraphAdjoint G) env = G.boundaryOut.table.map fwdEnv ++ G.boundaryIn.table.map grad ∧
    evalHypergraphLayeredSync (compileGraphAdjoint G) env = G.boundaryOut.table.map fwdEnv ++ G.boundaryIn.table.map grad := by
  intro fwd grad
  have hDag := compileGraphAdjoint_dag_sound G.nodeTypes.length (evalHyperEdgesComb env (extractHyperEdges G))
    (extractHyperEdges G) G.boundaryIn.table (seedCotangentSpec G.nodeTypes.length G.boundaryOut.table env) _
    (edgeSrcBounded_of_bounds hDstLt hSrcLt)
    (seedCotangentStateAux_invariant _ _ _ _ fun k _ => sweep_untouched
      (fun e v => evalHypergraphOp e.op (e.srcWires.map v)) _ _ env fun e he => by have := hDstLt e he; omega)
  have hComb : evalHypergraphComb (compileGraphAdjoint G) env = G.boundaryOut.table.map fwd ++ G.boundaryIn.table.map grad := by
    dsimp only [fwd, grad]
    unfold compileGraphAdjoint; rw [evalHypergraphComb_compileGraphAdjointAux]; unfold evalBuildGraphAdjointComb buildGraphAdjointState; dsimp only
    rw [List.map_append]; simp only [evalHyperEdgesComb_append]
    exact congr (congrArg (· ++ ·) (List.map_congr_left fun w hw => hDag.2.2.1 w (hOutLt w hw))) hDag.2.2.2
  have hP := evalHypergraph_pipelined_eq_comb (compileGraphAdjoint G) env
  exact ⟨hComb, hP.1.trans hComb, hP.2.trans hComb⟩

/-- Reverse AD sums cotangents over each fiber, whatever the fiber sizes. A constant fiber contributes its size times its common value. -/
theorem adjoint_quotient_intertwines_general
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) (initEnvG initEnvQ seedCotG : Nat → Int)
    (hQuot : checkHypergraphQuotient G Q wireClass edgeClass = true)
    (hInit : ∀ w < G.nodeTypes.length, (∀ e ∈ extractHyperEdges G, e.dstWire ≠ w) → initEnvG w = initEnvQ (wireClass w)) :
    let fwdG := evalHyperEdgesComb initEnvG (extractHyperEdges G)
    let fwdQ := evalHyperEdgesComb initEnvQ (extractHyperEdges Q)
    let gradG := specGradEdges fwdG (extractHyperEdges G) seedCotG
    let gradQ := specGradEdges fwdQ (extractHyperEdges Q) (orbitSumCot G.nodeTypes.length wireClass seedCotG)
    (∀ q < Q.nodeTypes.length, gradQ q = orbitSumCot G.nodeTypes.length wireClass gradG q) ∧
    ((∀ q < Q.nodeTypes.length,
        seedCotangentSpec Q.nodeTypes.length Q.boundaryOut.table initEnvQ q =
          orbitSumCot G.nodeTypes.length wireClass (seedCotangentSpec G.nodeTypes.length G.boundaryOut.table initEnvG) q) →
      let adjGradG := specGradEdges fwdG (extractHyperEdges G) (seedCotangentSpec G.nodeTypes.length G.boundaryOut.table initEnvG)
      evalHypergraphComb (compileGraphAdjoint Q) initEnvQ = Q.boundaryOut.table.map fwdQ ++ Q.boundaryIn.table.map (orbitSumCot G.nodeTypes.length wireClass adjGradG) ∧
      evalHypergraphLayered (compileGraphAdjoint Q) initEnvQ = Q.boundaryOut.table.map fwdQ ++ Q.boundaryIn.table.map (orbitSumCot G.nodeTypes.length wireClass adjGradG) ∧
      evalHypergraphLayeredSync (compileGraphAdjoint Q) initEnvQ = Q.boundaryOut.table.map fwdQ ++ Q.boundaryIn.table.map (orbitSumCot G.nodeTypes.length wireClass adjGradG)) ∧
    (∀ (q m : Nat) (g0 : Int), q < Q.nodeTypes.length → cellSize (List.range G.nodeTypes.length) wireClass q = m →
      (∀ w ∈ cellMembers (List.range G.nodeTypes.length) wireClass q, gradG w = g0) → gradQ q = (m : Int) * g0) := by
  have hHom := checkHypergraphQuotient_sound G Q wireClass edgeClass hQuot
  have hFwd := (evalHypergraph_quotient_intertwines_general G Q wireClass edgeClass initEnvG initEnvQ hQuot hInit).1
  intro fwdG fwdQ gradG gradQ
  have spec (seed : Nat → Int) (q : Nat) (hq : q < Q.nodeTypes.length) :
      specGradEdges fwdQ (extractHyperEdges Q) (orbitSumCot G.nodeTypes.length wireClass seed) q =
      orbitSumCot G.nodeTypes.length wireClass (specGradEdges fwdG (extractHyperEdges G) seed) q := by
    let basis := fun j : Nat => if j == q then (1 : Int) else 0
    let v := sweep (tangentRule fwdQ) basis (extractHyperEdges Q)
    have tan := sweep_quotient hHom (tangentRule fwdG) (tangentRule fwdQ) (basis ∘ wireClass) basis (fun _ _ _ => rfl)
      fun e he _ dst op src _ _ hv hz inputs => tangent_compatible (hHom.ssaG.arity_ok e he) op src
        (fun u hu => hFwd u (hHom.ssaG.src_lt e he u hu)) (hv.trans ((congrArg basis dst).trans hz.symm)) inputs
    have dual {X : StrictOpenHypergraph} (ssa : CausalSSASpec X.nodeTypes.length X.boundaryIn.table (extractHyperEdges X)) (f b c : Nat → Int) :=
      pairing_reverse f (extractHyperEdges X) b c (fun e he => ⟨ssa.arity_ok e he, ssa.dst_lt e he, ssa.src_lt e he⟩)
    have push : pairing G.nodeTypes.length seed (sweep (tangentRule fwdG) (basis ∘ wireClass) (extractHyperEdges G)) =
        pairing Q.nodeTypes.length (orbitSumCot G.nodeTypes.length wireClass seed) v :=
      (sumIntOver_congr _ _ _ fun w hw => congrArg (seed w * ·) (tan w (List.mem_range.mp hw))).trans
        (pairing_orbit hHom.wire_lt seed v)
    rw [← dual hHom.ssaG, ← dual hHom.ssaQ] at push
    have singleton (c : Nat → Int) : pairing Q.nodeTypes.length c basis = c q := by
      unfold pairing; rw [← sumIntOver_ite_range_eq (c q) q Q.nodeTypes.length hq]
      exact sumIntOver_congr _ _ _ fun w _ => by by_cases h : w = q <;> simp [basis, h, Ne.symm]
    rw [singleton] at push; exact push.symm.trans (pairing_indicator _ wireClass q _)
  have hPart1 : ∀ q < Q.nodeTypes.length, gradQ q = orbitSumCot G.nodeTypes.length wireClass gradG q := spec seedCotG
  refine ⟨hPart1, ?_, fun q m g0 hq hSize hConst => by rw [hPart1 q hq]; unfold orbitSumCot; rw [sumIntOver_const_of_eq _ g0 _ hConst]; unfold cellSize at hSize; rw [hSize]⟩
  intro hSeedAlign
  have hEvalQ := compileGraphAdjoint_eval_eq_spec Q initEnvQ (boundaryOut_lt_of_wf Q hHom.wfQ) hHom.ssaQ.dst_lt hHom.ssaQ.src_lt
  dsimp only at hEvalQ
  have hMapEq :
      Q.boundaryIn.table.map (specGradEdges (evalHyperEdgesComb initEnvQ (extractHyperEdges Q)) (extractHyperEdges Q) (seedCotangentSpec Q.nodeTypes.length Q.boundaryOut.table initEnvQ)) =
      Q.boundaryIn.table.map (orbitSumCot G.nodeTypes.length wireClass (specGradEdges (evalHyperEdgesComb initEnvG (extractHyperEdges G)) (extractHyperEdges G) (seedCotangentSpec G.nodeTypes.length G.boundaryOut.table initEnvG))) :=
    List.map_congr_left fun q hqM =>
      (specGradRevOrder_congr _ (· < Q.nodeTypes.length) (extractHyperEdges Q).reverse _ _ (fun e he => hHom.ssaQ.dst_lt e (List.mem_reverse.mp he)) hSeedAlign q (hHom.ssaQ.in_lt q hqM)).trans
      (spec _ q (hHom.ssaQ.in_lt q hqM))
  rwa [hMapEq] at hEvalQ

/-! ## 4. Equivariant Hypergraph Perturbation & Corollary 1 (`quantumMatter_4lane_quotient_corollary`) -/

/-- Equivariant scalar parameter perturbation on a `HypergraphOp`. -/
def perturbOp (delta : Int) : HypergraphOp → HypergraphOp
  | .const c => .const (c + delta) | .scale k => .scale (k + delta) | op => op

/-- Apply per-edge parameter offsets `edgeDelta` to all hyperedge ops of `G`. -/
def perturbHypergraphOps (G : StrictOpenHypergraph) (edgeDelta : Nat → Int) : StrictOpenHypergraph :=
  { G with ops := G.ops.zipIdx.map (fun p => perturbOp (edgeDelta p.2) p.1) }

private theorem extractHyperEdges_perturbHypergraphOps (G : StrictOpenHypergraph) (edgeDelta : Nat → Int) :
    extractHyperEdges (perturbHypergraphOps G edgeDelta) = (extractHyperEdges G).map (fun e => { e with op := perturbOp (edgeDelta e.opIdx) e.op }) := by
  unfold extractHyperEdges perturbHypergraphOps; dsimp only
  suffices h : ∀ (idx : Nat) (ops : List HypergraphOp) (sS sV tV : List Nat),
      extractHyperEdgesAux idx ((ops.zipIdx idx).map (fun p => perturbOp (edgeDelta p.2) p.1)) sS sV tV =
        (extractHyperEdgesAux idx ops sS sV tV).map (fun e => { e with op := perturbOp (edgeDelta e.opIdx) e.op }) by
    simpa [List.zipIdx] using h 0 G.ops G.sources.sizes.table G.sources.values.table G.targets.values.table
  intro idx ops; induction ops generalizing idx with
  | nil => intro _ _ _; rfl
  | cons _ _ ih => intro sS sV tV; cases sS <;> cases tV <;> simp [List.zipIdx, extractHyperEdgesAux, ih (idx + 1)]

private theorem extractHyperEdgesAux_opIdx (idx : Nat) (ops : List HypergraphOp) (sS sV tV : List Nat) (k : Nat) (e : HyperEdge)
    (hGet : (extractHyperEdgesAux idx ops sS sV tV)[k]? = some e) : e.opIdx = idx + k := by
  induction ops generalizing idx sS sV tV k with
  | nil => exact nomatch hGet
  | cons _ _ ih => cases sS <;> cases tV <;> cases k <;> simp [extractHyperEdgesAux] at hGet <;> first | (subst hGet; simp) | (have := ih (idx + 1) _ _ _ _ hGet; omega)

private theorem perturbHypergraphOps_preserves_quotient
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) (deltaQ : Nat → Int)
    (hQuot : checkHypergraphQuotient G Q wireClass edgeClass = true) :
    checkHypergraphQuotient (perturbHypergraphOps G (fun i => deltaQ (edgeClass i))) (perturbHypergraphOps Q deltaQ) wireClass edgeClass = true := by
  have hArityP : ∀ d op, hypergraphOpArity (perturbOp d op) = hypergraphOpArity op := fun _ op => by cases op <;> rfl
  have hSSAP : ∀ (X : StrictOpenHypergraph) (d : Nat → Int), checkHypergraphCausalSSA X = true → checkHypergraphCausalSSA (perturbHypergraphOps X d) = true := fun X d hS => by
    unfold checkHypergraphCausalSSA at hS ⊢; rw [extractHyperEdges_perturbHypergraphOps]
    change checkEdgesCausalSSA X.nodeTypes.length X.boundaryIn.table _ = true
    unfold checkEdgesCausalSSA at hS ⊢; simp only [Bool.and_eq_true] at hS ⊢
    rcases hS with ⟨⟨h1, h2⟩, h3⟩; rw [list_all_iff_forall] at h1 h2 h3
    refine ⟨⟨(list_all_iff_forall _ _).mpr fun e he => by obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he; simpa [hArityP] using h1 e0 he0,
             (list_all_iff_forall _ _).mpr fun w hw => by simpa [List.any_map] using h2 w hw⟩,
            (list_all_iff_forall _ _).mpr fun i hiM => ?_⟩
    simp only [List.length_map, List.mem_range] at hiM; have h0 := h3 i (List.mem_range.mpr hiM); rw [List.getElem?_map]
    cases hG : (extractHyperEdges X)[i]? with | none => rw [hG] at h0; exact Bool.noConfusion h0 | some _ => rw [hG] at h0; simpa [← List.map_drop, List.all_map] using h0
  have hWfP : ∀ (X : StrictOpenHypergraph) (d : Nat → Int), X.wf = true → (perturbHypergraphOps X d).wf = true := fun X _ hX => by
    unfold StrictOpenHypergraph.wf at hX ⊢; unfold perturbHypergraphOps; simpa [List.length_map, List.length_zipIdx] using hX
  unfold checkHypergraphQuotient at hQuot ⊢; simp only [Bool.and_eq_true] at hQuot ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hWfP G _ hQuot.1.1.1.1.1.1.1.1, hWfP Q _ hQuot.1.1.1.1.1.1.1.2⟩,
    hSSAP G _ hQuot.1.1.1.1.1.1.2⟩, hSSAP Q _ hQuot.1.1.1.1.1.2⟩, ?_⟩, hQuot.1.1.1.2⟩, hQuot.1.1.2⟩, hQuot.1.2⟩, ?_⟩
  · change (List.range G.nodeTypes.length).all (fun w => decide (wireClass w < Q.nodeTypes.length) &&
      ((extractHyperEdges (perturbHypergraphOps G _)).any (fun e => e.dstWire == w) == (extractHyperEdges (perturbHypergraphOps Q _)).any (fun e => e.dstWire == wireClass w))) = true
    rw [extractHyperEdges_perturbHypergraphOps, extractHyperEdges_perturbHypergraphOps]; simp only [List.any_map]; exact hQuot.1.1.1.1.2
  · rw [extractHyperEdges_perturbHypergraphOps, extractHyperEdges_perturbHypergraphOps, list_all_iff_forall]
    intro i hiM; simp only [List.length_map, List.mem_range] at hiM
    have hE := (list_all_iff_forall _ _).mp hQuot.2 i (List.mem_range.mpr hiM); rw [List.getElem?_map, List.getElem?_map]
    cases hG : (extractHyperEdges G)[i]? with
    | none => rw [hG] at hE; exact Bool.noConfusion hE
    | some eG =>
      rw [hG] at hE; cases hQ : (extractHyperEdges Q)[edgeClass i]? with
      | none => rw [hQ] at hE; exact Bool.noConfusion hE
      | some eQ =>
        rw [hQ] at hE; simp only [Option.map_some, List.length_map, Bool.and_eq_true] at hE ⊢
        have hIG := extractHyperEdgesAux_opIdx 0 G.ops G.sources.sizes.table G.sources.values.table G.targets.values.table i eG hG
        have hIQ := extractHyperEdgesAux_opIdx 0 Q.ops Q.sources.sizes.table Q.sources.values.table Q.targets.values.table (edgeClass i) eQ hQ
        refine ⟨⟨⟨hE.1.1.1, hE.1.1.2⟩, ?_⟩, hE.2⟩
        rw [show eG.opIdx = i by omega, show eQ.opIdx = edgeClass i by omega, beq_iff_eq.mp hE.1.2]; exact beq_self_eq_true _

/-- Wire orbit projection mapping 4-lane symmetric hypergraph wires `0..23` onto 2-cell wires `0..11`. -/
def sym4LaneWireClass (w : Nat) : Nat := if w < 12 then w % 6 else 6 + (w % 6)

/-- Edge orbit projection mapping 4-lane symmetric hypergraph edges onto 2-cell quotient edges. -/
def sym4LaneEdgeClass (op2 : OpticOp) (i : Nat) : Nat :=
  let k := 1 + (opticFwdHyperEdges op2 2 1 3 5).length; if i < 2 * k then i % k else k + (i % k)

/-- Exchange the two six-wire lanes in each pair. -/
def swapSym4LaneWire (w : Nat) : Nat := if w / 6 % 2 = 0 then w + 6 else w - 6

private def swapSym4LaneEdge (op : OpticOp) (i : Nat) : Nat :=
  let k := 1 + (opticFwdHyperEdges op 2 1 3 5).length
  if i / k % 2 = 0 then i + k else i - k

/-- Four lanes with paired weights have equal gradients within each pair. Doubling the quotient seeds
recovers the pair sums, while the original seeds recover each lane of the compiled adjoint. -/
theorem quantumMatter_4lane_quotient_corollary
    (W0 W1 : Int) (op2 : OpticOp) (x0 y0 x1 y1 dOut0 dOut1 : Int) :
    let gFull := buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2
    let gQuot := quotientOpenHypergraph W0 W1 op2
    let envFull := liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuot := quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuotSum := quotientHypergraphInitEnv x0 y0 x1 y1 (2 * dOut0) (2 * dOut1)
    let fwdFull := evalHyperEdgesComb envFull (extractHyperEdges gFull)
    let fwdQuot := evalHyperEdgesComb envQuotSum (extractHyperEdges gQuot)
    let gradFull := specGradEdges fwdFull (extractHyperEdges gFull) (seedCotangentSpec gFull.nodeTypes.length gFull.boundaryOut.table envFull)
    checkHypergraphQuotient gFull gQuot sym4LaneWireClass (sym4LaneEdgeClass op2) = true ∧
    evalHypergraphComb gFull envFull = [fwdQuot 3, fwdQuot 3, fwdQuot 9, fwdQuot 9] ∧
    evalHypergraphLayered gFull envFull = [fwdQuot 3, fwdQuot 3, fwdQuot 9, fwdQuot 9] ∧
    evalHypergraphComb (compileGraphAdjoint gQuot) envQuotSum = [fwdQuot 3, fwdQuot 9, gradFull 0 + gradFull 6, gradFull 1 + gradFull 7, gradFull 12 + gradFull 18, gradFull 13 + gradFull 19] ∧
    evalHypergraphLayered (compileGraphAdjoint gQuot) envQuotSum = [fwdQuot 3, fwdQuot 9, gradFull 0 + gradFull 6, gradFull 1 + gradFull 7, gradFull 12 + gradFull 18, gradFull 13 + gradFull 19] ∧
    (gradFull 0 = gradFull 6 ∧ gradFull 1 = gradFull 7 ∧ gradFull 12 = gradFull 18 ∧ gradFull 13 = gradFull 19) ∧
    evalHypergraphComb (compileGraphAdjoint gFull) envFull =
      liftQuotientAdjointOutputs (evalHypergraphComb (compileGraphAdjoint gQuot) envQuot) ∧
    evalHypergraphLayered (compileGraphAdjoint gFull) envFull =
      liftQuotientAdjointOutputs (evalHypergraphLayered (compileGraphAdjoint gQuot) envQuot) := by
  intro G Q env unit doubled fwd fwdSum grad
  have cert : checkHypergraphQuotient G Q sym4LaneWireClass (sym4LaneEdgeClass op2) = true := by cases op2 <;> cbv
  have swap : checkHypergraphQuotient G G swapSym4LaneWire (swapSym4LaneEdge op2) = true := by cases op2 <;> cbv
  have init : ∀ a b w, w < 24 → env w = quotientHypergraphInitEnv x0 y0 x1 y1 a b (sym4LaneWireClass w) := by
    intro a b w hw; match w with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => rfl
    | _ + 24 => omega
  have inv : ∀ w, w < 24 → env w = env (swapSym4LaneWire w) := by
    intro w hw; match w with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => rfl
    | _ + 24 => omega
  let seed := seedCotangentSpec 24 [3, 9, 15, 21] env
  let qSeed := seedCotangentSpec 12 [3, 9] unit
  let qGrad := specGradEdges (evalHyperEdgesComb unit (extractHyperEdges Q)) (extractHyperEdges Q) qSeed
  have singleton (q : Nat) (hq : q < 24) : cellMembers (List.range 24) swapSym4LaneWire q = [swapSym4LaneWire q] := by
    exact (show ∀ i : Fin 24, cellMembers (List.range 24) swapSym4LaneWire i = [swapSym4LaneWire i] by decide +kernel) ⟨q,hq⟩
  have invariantSeed : orbitSumCot 24 swapSym4LaneWire seed = seed := by
    funext q; match q with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => change _ + 0 = _; rw [Int.add_zero]; rfl
    | _ + 24 => rfl
  have symmetry (q : Nat) (hq : q < 24) : grad q = grad (swapSym4LaneWire q) := by
    have swapped' := (adjoint_quotient_intertwines_general G G _ _ env env seed swap fun w hw _ => inv w hw).1 q hq
    change specGradEdges fwd _ (orbitSumCot 24 swapSym4LaneWire seed) q = orbitSumCot 24 swapSym4LaneWire grad q at swapped'
    rw [invariantSeed, orbitSumCot, singleton q hq, sumIntOver_cons, sumIntOver, Int.add_zero] at swapped'
    exact swapped'
  have doubledSeed : orbitSumCot 24 sym4LaneWireClass seed = fun q => 2 * qSeed q := by
    funext q
    match q with
    | 3 => change (0 + dOut0) + ((0 + dOut0) + 0) = 2 * (0 + dOut0); omega
    | 9 => change (0 + dOut1) + ((0 + dOut1) + 0) = 2 * (0 + dOut1); omega
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 10 | 11 | _ + 12 => rfl
  have sumSeed (q : Nat) : seedCotangentSpec 12 [3, 9] doubled q = 2 * qSeed q := by
    simp [seedCotangentSpec, addSpecCotangent, qSeed, doubled, unit, quotientHypergraphInitEnv]; grind
  have hom := checkHypergraphQuotient_sound G Q _ _ cert
  have forward := evalHypergraph_quotient_intertwines_general G Q _ _ env doubled cert fun w hw _ => init _ _ w hw
  have summed := (adjoint_quotient_intertwines_general G Q _ _ env doubled seed cert fun w hw _ => init _ _ w hw).2.1
    (fun q _ => (sumSeed q).trans (congrFun doubledSeed q).symm)
  have orbit (q : Nat) (hq : q < 12) : 2 * qGrad q = orbitSumCot 24 sym4LaneWireClass grad q := by
    have h := (adjoint_quotient_intertwines_general G Q _ _ env unit seed cert fun w hw _ => init _ _ w hw).1 q hq
    change specGradRevOrder _ _ (orbitSumCot 24 sym4LaneWireClass seed) q = _ at h
    rwa [doubledSeed, specGradRevOrder_scale] at h
  have pair (a b q : Nat) (hq : q < 12) (cell : cellMembers (List.range 24) sym4LaneWireClass q = [a,b])
      (same : grad a = grad b) : qGrad q = grad a := by
    have h := orbit q hq; rw [orbitSumCot, cell, sumIntOver_cons, sumIntOver_cons, sumIntOver, Int.add_zero] at h; omega
  have hs : grad 0 = grad 6 ∧ grad 1 = grad 7 ∧ grad 12 = grad 18 ∧ grad 13 = grad 19 :=
    ⟨symmetry 0 (by decide), symmetry 1 (by decide), symmetry 12 (by decide), symmetry 13 (by decide)⟩
  have full := (compileGraphAdjoint_eval_eq_spec G env (boundaryOut_lt_of_wf _ hom.wfG) hom.ssaG.dst_lt hom.ssaG.src_lt).1
  have small := (compileGraphAdjoint_eval_eq_spec Q unit (boundaryOut_lt_of_wf _ hom.wfQ) hom.ssaQ.dst_lt hom.ssaQ.src_lt).1
  have unitFwd := (evalHypergraph_quotient_intertwines_general G Q _ _ env unit cert fun w hw _ => init _ _ w hw).2.1
  have exactAdj : evalHypergraphComb (compileGraphAdjoint G) env = liftQuotientAdjointOutputs (evalHypergraphComb (compileGraphAdjoint Q) unit) := by
    rw [full, small]; change evalHypergraphComb G env ++ _ = _
    rw [unitFwd]
    let z := evalHyperEdgesComb unit (extractHyperEdges Q)
    change [z 3,z 3,z 9,z 9,grad 0,grad 1,grad 6,grad 7,grad 12,grad 13,grad 18,grad 19] =
      [z 3,z 3,z 9,z 9,qGrad 0,qGrad 1,qGrad 0,qGrad 1,qGrad 6,qGrad 7,qGrad 6,qGrad 7]
    rw [pair 0 6 0 (by decide) rfl hs.1, pair 1 7 1 (by decide) rfl hs.2.1,
      pair 12 18 6 (by decide) rfl hs.2.2.1, pair 13 19 7 (by decide) rfl hs.2.2.2, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
  have sums (f : Nat → Int) : [0,1,6,7].map (orbitSumCot 24 sym4LaneWireClass f) =
      [f 0 + f 6, f 1 + f 7, f 12 + f 18, f 13 + f 19] := by
    change [f 0 + (f 6 + 0), f 1 + (f 7 + 0), f 12 + (f 18 + 0), f 13 + (f 19 + 0)] = _; simp
  change _ = [fwdSum 3, fwdSum 9] ++ [0,1,6,7].map (orbitSumCot 24 sym4LaneWireClass grad) ∧ _ at summed
  refine ⟨cert, forward.2.1, forward.2.2.1, by simpa only [sums, List.cons_append, List.nil_append] using summed.1,
    ?_, hs, exactAdj, ?_⟩
  · rw [(evalHypergraph_pipelined_eq_comb _ _).1, summed.1, sums]; rfl
  · rwa [(evalHypergraph_pipelined_eq_comb _ _).1, (evalHypergraph_pipelined_eq_comb _ _).1]

/-! ## 5. Corollary 2: Arbitrary $K$-Lane Parallel + `.add`-Reduction-Tree Intertwining -/

private def singleLaneEdges (W : Int) (op2 : OpticOp) (base : Nat) : List HyperEdge :=
  opticFwdHyperEdges (.scale W) base (base + 1) (base + 2) (base + 4) ++ opticFwdHyperEdges op2 (base + 2) (base + 1) (base + 3) (base + 5)

private def redEdgesOf (K m : Nat) : List HyperEdge :=
  (List.range m).map (fun r => ({ opIdx := 0, op := .add, srcWires := [if r == 0 then 3 else 6 * K + (r - 1), 6 * (r + 1) + 3], dstWire := 6 * K + r } : HyperEdge))

/-- Sum the outputs of `K ≥ 1` parallel lanes with a chain of `K - 1` additions. -/
@[expose] def buildKLaneReductionHypergraph (K : Nat) (W : Int) (op2 : OpticOp) : StrictOpenHypergraph :=
  mkStrictOpenHypergraph (6 * K + (K - 1)) ((List.range K).flatMap (fun u => [6 * u, 6 * u + 1]))
    [if K ≤ 1 then 3 else 6 * K + (K - 2)]
    (reindexHyperEdges (((List.range K).flatMap (fun u =>
      opticFwdHyperEdges (.scale W) (6 * u) (6 * u + 1) (6 * u + 2) (6 * u + 4) ++
      opticFwdHyperEdges op2 (6 * u + 2) (6 * u + 1) (6 * u + 3) (6 * u + 5))) ++
      (List.range (K - 1)).map (fun r =>
        { opIdx := 0, op := .add, srcWires := [if r == 0 then 3 else 6 * K + (r - 1), 6 * (r + 1) + 3], dstWire := 6 * K + r })))

/-- The seven-wire quotient evaluates one lane and scales its output by `K`. -/
@[expose] def quotientKLaneReductionHypergraph (K : Nat) (W : Int) (op2 : OpticOp) : StrictOpenHypergraph :=
  let lane0 := opticFwdHyperEdges (.scale W) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  mkStrictOpenHypergraph 7 [0, 1] [6] (reindexHyperEdges (lane0 ++ [{ opIdx := 0, op := .scale (K : Int), srcWires := [3], dstWire := 6 }]))

/-- Lifted wire environment for `buildKLaneReductionHypergraph K W op2` and its adjoint. -/
def kLaneInitEnv (K : Nat) (x y dOut : Int) (w : Nat) : Int :=
  if w < 6 * K then (if w % 6 == 0 then x else if w % 6 == 1 then y else 0) else if w == 6 * K + (K - 1) then dOut else 0

/-- Wire environment for `quotientKLaneReductionHypergraph K W op2` and its adjoint. -/
def quotientKLaneInitEnv (x y dOut : Int) (w : Nat) : Int := if w == 0 then x else if w == 1 then y else if w == 7 then dOut else 0

private theorem singleLaneEdges_fwd (W : Int) (op2 : OpticOp) (base : Nat) (env : Nat → Int) (x y : Int) (hx : env base = x) (hy : env (base + 1) = y) :
    let env' := evalHyperEdgesComb env (singleLaneEdges W op2 base)
    env' base = x ∧ env' (base + 1) = y ∧ env' (base + 2) = W * x ∧
    env' (base + 3) = (evalOpticChain2Fwd (.scale W) op2 x y).1 ∧ (∀ w, w < base ∨ base + 6 ≤ w → env' w = env w) := by
  cases op2 <;> dsimp [singleLaneEdges, opticFwdHyperEdges, evalHyperEdgesComb, stepHyperEdge,
    evalHypergraphOp, evalOpticChain2Fwd, evalOpticFwd, List.map, List.getD] <;>
    refine ⟨?_, ?_, ?_, ?_, fun w hw => ?_⟩ <;> simp +arith (disch := omega) [beq_iff_eq, hx, hy] <;> grind

private theorem singleLaneEdges_bwd (W : Int) (op2 : OpticOp) (base : Nat) (fwd cot : Nat → Int) (x y dOut : Int)
    (hy : fwd (base + 1) = y) (hm : fwd (base + 2) = W * x)
    (hc0 : cot base = 0) (hc1 : cot (base + 1) = 0) (hc2 : cot (base + 2) = 0) (hc3 : cot (base + 3) = dOut) (hc5 : cot (base + 5) = 0) :
    let cot' := specGradRevOrder fwd (singleLaneEdges W op2 base).reverse cot
    let rev := evalOpticChain2Rev (compileOpticAdjoint (.scale W)) (compileOpticAdjoint op2) (evalOpticChain2Fwd (.scale W) op2 x y).2 dOut
    cot' base = rev.1 ∧ cot' (base + 1) = rev.2 ∧ (∀ w, w < base ∨ base + 6 ≤ w → cot' w = cot w) := by
  cases op2 <;> simp only [singleLaneEdges, opticFwdHyperEdges, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil, specGradRevOrder_cons, specGradRevOrder_nil, specGradEdgeStep,
    specEdgeLocalPullback, accumSpecCotangents_cons, accumSpecCotangents_nil, addSpecCotangent, wireAt,
    evalOpticChain2Rev, evalOpticChain2Fwd, evalOpticFwd, evalOpticRev, compileOpticAdjoint] <;>
    refine ⟨?_, ?_, fun w hw => ?_⟩ <;>
    simp (disch := omega) [beq_iff_eq, hc0, hc1, hc2, hc3, hc5, hy, hm] <;> grind

private theorem allLanesEdges_fwd (K : Nat) (W : Int) (op2 : OpticOp) (x y dOut : Int) :
    ∀ (m : Nat), m ≤ K →
      let env' := evalHyperEdgesComb (kLaneInitEnv K x y dOut) ((List.range m).flatMap (fun u => singleLaneEdges W op2 (6 * u)))
      (∀ u < m, env' (6 * u) = x ∧ env' (6 * u + 1) = y ∧ env' (6 * u + 2) = W * x ∧ env' (6 * u + 3) = (evalOpticChain2Fwd (.scale W) op2 x y).1) ∧
      (∀ w, 6 * m ≤ w → env' w = kLaneInitEnv K x y dOut w)
  | 0, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | m + 1, hm => by
    have hIH := allLanesEdges_fwd K W op2 x y dOut m (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, evalHyperEdgesComb_append]
    have hS := singleLaneEdges_fwd W op2 (6*m) (evalHyperEdgesComb (kLaneInitEnv K x y dOut)
      ((List.range m).flatMap (fun u => singleLaneEdges W op2 (6*u)))) x y (by rw [hIH.2 _ (by omega)]; simp [kLaneInitEnv, show 6*m < 6*K by omega])
      (by rw [hIH.2 _ (by omega)]; simp [kLaneInitEnv, show 6*m+1 < 6*K by omega, show (6*m+1)%6 = 1 by omega])
    refine ⟨fun u hu => ?_, fun w hw => (hS.2.2.2.2 w (Or.inr (by omega))).trans (hIH.2 w (by omega))⟩
    obtain rfl | lt := Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hu)
    · exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
    · simpa (disch := omega) only [hS.2.2.2.2] using hIH.1 u lt

private theorem redEdges_fwd (K : Nat) (z : Int) (env : Nat → Int) (hLanes : ∀ u < K, env (6 * u + 3) = z) :
    ∀ (m : Nat), m ≤ K - 1 →
      let env' := evalHyperEdgesComb env (redEdgesOf K m)
      (∀ r < m, env' (6 * K + r) = ((r + 2 : Nat) : Int) * z) ∧ (∀ w, w < 6 * K ∨ 6 * K + m ≤ w → env' w = env w)
  | 0, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | m + 1, hm => by
    have hIH := redEdges_fwd K z env hLanes m (by omega)
    let eM : HyperEdge := { opIdx := 0, op := .add, srcWires := [if m == 0 then 3 else 6 * K + (m - 1), 6 * (m + 1) + 3], dstWire := 6 * K + m }
    have hSplit : redEdgesOf K (m + 1) = redEdgesOf K m ++ [eM] := by unfold redEdgesOf; rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hSplit, evalHyperEdgesComb_append, evalHyperEdgesComb_cons, evalHyperEdgesComb_nil]
    have hR : evalHyperEdgesComb env (redEdgesOf K m) (6 * (m + 1) + 3) = z := by rw [hIH.2 _ (Or.inl (by omega))]; exact hLanes (m + 1) (by omega)
    have hL : evalHyperEdgesComb env (redEdgesOf K m) (if m == 0 then 3 else 6 * K + (m - 1)) = ((m + 1 : Nat) : Int) * z := by
      cases m with
      | zero => simp only [beq_self_eq_true, ↓reduceIte]; rw [hIH.2 3 (Or.inl (by omega)), hLanes 0 (by omega)]; simp
      | succ m' => simp only [beq_false_of_ne (show m' + 1 ≠ 0 by omega), Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]; exact hIH.1 m' (by omega)
    refine ⟨fun r hr => ?_, fun w hw => by rw [stepHyperEdge_ne _ _ w (by dsimp [eM]; omega), hIH.2 w (by omega)]⟩
    by_cases hEq : r = m
    · subst hEq; change stepHyperEdge _ eM eM.dstWire = _; rw [stepHyperEdge_eq_self]; dsimp [eM, evalHypergraphOp, List.map, List.getD]; rw [hL, hR, show ((r : Int) + 2) = ((r + 1 : Nat) : Int) + 1 by omega, Int.add_mul, Int.one_mul]
    · rw [stepHyperEdge_ne _ _ _ (by dsimp [eM]; omega)]; exact hIH.1 r (by omega)

/-- A reverse reduction adds the output seed to every participating lane, preserving its prior cotangent. -/
private theorem redEdges_bwd (K : Nat) (fwd : Nat → Int) (d : Int) (m : Nat) (hm : m ≤ K-1)
    (c : Nat → Int) (fresh : ∀ r < m, c (6*K+r) = 0) (w : Nat) (hw : w < 6*K) :
    specGradRevOrder fwd (redEdgesOf K m).reverse (addSpecCotangent (if m == 0 then 3 else 6*K+(m-1)) d c) w =
      c w + (if w % 6 = 3 ∧ w / 6 ≤ m then d else 0) := by
  induction m generalizing c with
  | zero => simp [redEdgesOf, specGradRevOrder_nil, addSpecCotangent]; grind
  | succ m ih =>
    let right := 6*(m+1)+3
    let tailCot := addSpecCotangent right d (addSpecCotangent (6*K+m) d c)
    let prev := if m == 0 then 3 else 6*K+(m-1)
    let edge : HyperEdge := ⟨0, .add, [prev, right], 6*K+m⟩
    have splitAt : redEdgesOf K (m+1) = redEdgesOf K m ++ [edge] := by simp [redEdgesOf, List.range_succ, edge, prev, right]
    rw [splitAt, List.reverse_append, List.reverse_singleton, List.singleton_append, specGradRevOrder_cons]
    have step : specGradEdgeStep fwd edge (addSpecCotangent (if m+1 == 0 then 3 else 6*K+(m+1-1)) d c) =
        addSpecCotangent prev d tailCot := by
      funext u; simp [edge, tailCot, specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, wireAt,
        addSpecCotangent, fresh m (by omega)]; grind
    rw [step, ih (by omega) tailCot (fun r hr => by simp [tailCot, right, addSpecCotangent, fresh r (by omega)]; grind)]
    simp [tailCot, right, addSpecCotangent]; grind

private theorem allLanesEdges_bwd (K : Nat) (W : Int) (op2 : OpticOp) (fwd : Nat → Int) (x y dOut : Int)
    (hFwd : ∀ u < K, fwd (6 * u + 1) = y ∧ fwd (6 * u + 2) = W * x) :
    ∀ (m : Nat) (cot : Nat → Int), m ≤ K →
      (∀ u < m, cot (6 * u) = 0 ∧ cot (6 * u + 1) = 0 ∧ cot (6 * u + 2) = 0 ∧ cot (6 * u + 3) = dOut ∧ cot (6 * u + 5) = 0) →
      let cot' := specGradRevOrder fwd ((List.range m).flatMap (fun u => singleLaneEdges W op2 (6 * u))).reverse cot
      let rev := evalOpticChain2Rev (compileOpticAdjoint (.scale W)) (compileOpticAdjoint op2) (evalOpticChain2Fwd (.scale W) op2 x y).2 dOut
      (∀ u < m, cot' (6 * u) = rev.1 ∧ cot' (6 * u + 1) = rev.2) ∧ (∀ w, 6 * m ≤ w → cot' w = cot w)
  | 0, _, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | m + 1, cot, hm, hCot => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.reverse_append, specGradRevOrder_append]
    have hFm := hFwd m (by omega); have hCm := hCot m (by omega)
    have hS := singleLaneEdges_bwd W op2 (6 * m) fwd cot x y dOut hFm.1 hFm.2 hCm.1 hCm.2.1 hCm.2.2.1 hCm.2.2.2.1 hCm.2.2.2.2
    have hIH := allLanesEdges_bwd K W op2 fwd x y dOut hFwd m (specGradRevOrder fwd (singleLaneEdges W op2 (6 * m)).reverse cot) (by omega) fun u hu => by
      simpa (disch := omega) only [hS.2.2] using hCot u (by omega)
    refine ⟨fun u hu => ?_, fun w hw => by rw [hIH.2 w (by omega), hS.2.2 w (Or.inr (by omega))]⟩
    by_cases hEq : u = m
    · subst hEq; exact ⟨by rw [hIH.2 (6 * u) (Nat.le_refl _), hS.1], by rw [hIH.2 (6 * u + 1) (by omega), hS.2.1]⟩
    · exact hIH.1 u (by omega)

private theorem buildKLaneReductionHypergraph_bounds (K : Nat) (W : Int) (op2 : OpticOp) (hK : 1 ≤ K) :
    (buildKLaneReductionHypergraph K W op2).wf = true ∧
    (∀ w ∈ (buildKLaneReductionHypergraph K W op2).boundaryOut.table, w < (buildKLaneReductionHypergraph K W op2).nodeTypes.length) ∧
    (∀ e ∈ extractHyperEdges (buildKLaneReductionHypergraph K W op2),
      e.dstWire < (buildKLaneReductionHypergraph K W op2).nodeTypes.length ∧ ∀ u ∈ e.srcWires, u < (buildKLaneReductionHypergraph K W op2).nodeTypes.length) := by
  let numWires := 6 * K + (K - 1)
  have hRM : ∀ (idx : Nat) (es : List HyperEdge) (e : HyperEdge), e ∈ reindexHyperEdgesAux idx es → ∃ e0 ∈ es, e.srcWires = e0.srcWires ∧ e.dstWire = e0.dstWire := by
    intro idx es; induction es generalizing idx with
    | nil => intro _ h; exact nomatch h
    | cons x xs ih => intro e he; rcases x with ⟨_, op, s, d⟩; rcases List.mem_cons.mp he with rfl | hR; exact ⟨⟨_, op, s, d⟩, List.mem_cons_self, rfl, rfl⟩; obtain ⟨e0, he0, h1, h2⟩ := ih (idx + 1) e hR; exact ⟨e0, List.mem_cons_of_mem _ he0, h1, h2⟩
  have hRaw : ∀ e ∈ ((List.range K).flatMap (fun u => singleLaneEdges W op2 (6 * u))) ++ redEdgesOf K (K - 1), e.dstWire < numWires ∧ ∀ v ∈ e.srcWires, v < numWires := fun e he => by
    rcases List.mem_append.mp he with hL | hR
    · obtain ⟨u, hu, heU⟩ := List.mem_flatMap.mp hL; have := List.mem_range.mp hu
      cases op2 <;> simp only [singleLaneEdges, opticFwdHyperEdges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at heU <;>
        rcases heU with rfl | rfl | rfl <;> exact ⟨by dsimp [numWires]; omega, fun v hv => by simp at hv; dsimp [numWires]; omega⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hR; have := List.mem_range.mp hr
      refine ⟨by dsimp [numWires]; omega, fun v hv => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl; (cases r <;> simp [numWires] <;> omega); dsimp [numWires]; omega
  have hSumLen {α : Type} (xs : List (List α)) : sumNatList (xs.map List.length) = xs.flatten.length := by
    simp [sumNatList, List.sum_eq_foldl]
  have hSizeLt {α : Type} (xs : List (List α)) : (xs.map List.length).all (fun y => decide (y < xs.flatten.length + 1)) = true := by
    simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq]; rintro _ ⟨s, hs, rfl⟩
    induction xs with | nil => contradiction | cons _ _ ih => simp_all [List.mem_cons]; grind

  have bounded (e) (he : e ∈ reindexHyperEdges (((List.range K).flatMap (fun u => singleLaneEdges W op2 (6*u))) ++ redEdgesOf K (K-1))) :
      e.dstWire < numWires ∧ ∀ u ∈ e.srcWires, u < numWires := by
    obtain ⟨raw, hr, hs, hd⟩ := hRM 0 _ e he; rw [hs, hd]; exact hRaw raw hr
  have out : (if K ≤ 1 then 3 else 6*K + (K-2)) < numWires := by dsimp [numWires]; split <;> omega
  have wf : (buildKLaneReductionHypergraph K W op2).wf = true := by
    unfold buildKLaneReductionHypergraph mkStrictOpenHypergraph StrictOpenHypergraph.wf IndexedCoproduct.wf IndexedCoproduct.fromSegments FiniteFunction.wf
    simp only [Bool.and_eq_true, List.length_replicate, List.length_map, beq_self_eq_true, true_and, and_true, hSumLen, hSizeLt]
    simp only [List.all_eq_true, decide_eq_true_eq, List.mem_flatten, List.mem_map, List.mem_flatMap]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rintro w ⟨_, ⟨e, he, rfl⟩, hw⟩; exact (bounded e he).2 w hw
    · rintro w ⟨_, ⟨e, he, rfl⟩, hw⟩; exact (List.mem_singleton.mp hw) ▸ (bounded e he).1
    · rintro w ⟨u, hu, hw⟩; simp at hu hw; omega
    · rintro _ ⟨_, ⟨_, _, rfl⟩, rfl⟩; rfl
    · rintro w hw; exact (List.mem_singleton.mp hw) ▸ out
  refine ⟨wf, boundaryOut_lt_of_wf _ wf, fun e he => ?_⟩
  unfold buildKLaneReductionHypergraph at he; rw [extractHyperEdges_mkStrictOpenHypergraph] at he
  simpa only [buildKLaneReductionHypergraph, mkStrictOpenHypergraph, List.length_replicate] using bounded e he

private theorem specGradRevOrder_reindex (fwd : Nat → Int) (es : List HyperEdge) (c : Nat → Int) :
    specGradRevOrder fwd (reindexHyperEdges es).reverse c = specGradRevOrder fwd es.reverse c := by
  suffices h : ∀ (idx : Nat) (xs : List HyperEdge) (cot : Nat → Int), specGradRevOrder fwd (reindexHyperEdgesAux idx xs).reverse cot = specGradRevOrder fwd xs.reverse cot from h 0 es c
  intro idx xs; induction xs generalizing idx with
  | nil => intro _; rfl
  | cons e rest ih => intro cot; rcases e with ⟨_, op, s, d⟩; simp only [reindexHyperEdgesAux, List.reverse_cons, specGradRevOrder_append, specGradRevOrder_cons, specGradRevOrder_nil]; rw [ih (idx + 1)]; rfl

/-- Summing `K ≥ 1` identical lanes agrees with scaling one lane by `K`, in forward and reverse mode. -/
theorem kLane_reduction_tree_intertwines_eval_and_adjoint
    (K : Nat) (hK : 1 ≤ K) (W : Int) (op2 : OpticOp) (x y dOut : Int) :
    let gK := buildKLaneReductionHypergraph K W op2
    let qK := quotientKLaneReductionHypergraph K W op2
    let envK := kLaneInitEnv K x y dOut
    let envQ := quotientKLaneInitEnv x y dOut
    let z := (evalOpticChain2Fwd (.scale W) op2 x y).1
    let res := (evalOpticChain2Fwd (.scale W) op2 x y).2
    let rev1 := evalOpticChain2Rev (compileOpticAdjoint (.scale W)) (compileOpticAdjoint op2) res dOut
    let fwdK := evalHyperEdgesComb envK (extractHyperEdges gK)
    let gradK := specGradEdges fwdK (extractHyperEdges gK) (seedCotangentSpec gK.nodeTypes.length gK.boundaryOut.table envK)
    gK.wf = true ∧ qK.wf = true ∧ qK.nodeTypes.length = 7 ∧
    evalHypergraphComb gK envK = [(K : Int) * z] ∧ evalHypergraphLayered gK envK = [(K : Int) * z] ∧
    evalHypergraphComb qK envQ = [(K : Int) * z] ∧ evalHypergraphLayered qK envQ = [(K : Int) * z] ∧
    evalHypergraphComb (compileGraphAdjoint gK) envK = [(K : Int) * z] ++ (List.range K).flatMap (fun _ => [rev1.1, rev1.2]) ∧
    evalHypergraphLayered (compileGraphAdjoint gK) envK = [(K : Int) * z] ++ (List.range K).flatMap (fun _ => [rev1.1, rev1.2]) ∧
    evalHypergraphComb (compileGraphAdjoint qK) envQ = [(K : Int) * z, (K : Int) * rev1.1, (K : Int) * rev1.2] ∧
    evalHypergraphLayered (compileGraphAdjoint qK) envQ = [(K : Int) * z, (K : Int) * rev1.1, (K : Int) * rev1.2] ∧
    sumIntOver (fun u => gradK (6 * u)) (List.range K) = (K : Int) * rev1.1 ∧
    sumIntOver (fun u => gradK (6 * u + 1)) (List.range K) = (K : Int) * rev1.2 := by
  intro gK qK envK envQ z res rev1 fwdK gradK
  obtain ⟨hWfK, hOutK, hExtK⟩ := buildKLaneReductionHypergraph_bounds K W op2 hK
  have hWfQ : (quotientKLaneReductionHypergraph K W op2).wf = true := by cases op2 <;> rfl
  have ssaQ := checkEdgesCausalSSA_sound _ _ _ (show checkHypergraphCausalSSA qK = true by cases op2 <;> rfl)
  have small := (compileGraphAdjoint_eval_eq_spec qK envQ (boundaryOut_lt_of_wf _ hWfQ) ssaQ.dst_lt ssaQ.src_lt).1
  have quotient : evalHypergraphComb qK envQ = [(K : Int) * z] ∧
      evalHypergraphComb (compileGraphAdjoint qK) envQ = [(K : Int) * z, (K : Int) * rev1.1, (K : Int) * rev1.2] := by
    rw [small]; simp only [evalHypergraphComb, qK, quotientKLaneReductionHypergraph, extractHyperEdges_mkStrictOpenHypergraph]
    cases op2 <;> simp [envQ, z, rev1, res, quotientKLaneInitEnv, mkStrictOpenHypergraph, reindexHyperEdges, reindexHyperEdgesAux,
        opticFwdHyperEdges, evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp, specGradEdges, specGradRevOrder,
        specGradEdgeStep, specEdgeLocalPullback, accumSpecCotangents, addSpecCotangent, seedCotangentSpec,
        wireAt, evalOpticChain2Rev, evalOpticChain2Fwd, evalOpticFwd, evalOpticRev, compileOpticAdjoint] <;> grind
  have hLanesFwd := allLanesEdges_fwd K W op2 x y dOut K (Nat.le_refl K)
  have hRedFwd := redEdges_fwd K z (evalHyperEdgesComb envK ((List.range K).flatMap (fun u => singleLaneEdges W op2 (6 * u)))) (fun u hu => (hLanesFwd.1 u hu).2.2.2) (K - 1) (Nat.le_refl _)
  have hExtEqK : extractHyperEdges gK = reindexHyperEdges (((List.range K).flatMap (fun u => singleLaneEdges W op2 (6 * u))) ++ redEdgesOf K (K - 1)) :=
    extractHyperEdges_mkStrictOpenHypergraph _ _ _ _
  have hFwdKOut : evalHyperEdgesComb envK (extractHyperEdges gK) (if K ≤ 1 then 3 else 6 * K + (K - 2)) = (K : Int) * z := by
    rw [hExtEqK, evalHyperEdgesComb_reindexHyperEdges, evalHyperEdgesComb_append]
    by_cases hOne : K ≤ 1
    · obtain rfl : K = 1 := by omega
      simpa [redEdgesOf, envK, z, evalHyperEdgesComb_nil] using (hLanesFwd.1 0 (by decide)).2.2.2
    · simpa only [hOne, ↓reduceIte, show K-2+2 = K by omega] using hRedFwd.1 (K-2) (by omega)
  have hCombK : evalHypergraphComb gK envK = [(K : Int) * z] := by unfold evalHypergraphComb; change [evalHyperEdgesComb _ _ _] = _; rw [hFwdKOut]
  have hAdjK := (compileGraphAdjoint_eval_eq_spec gK envK hOutK (fun e he => (hExtK e he).1) (fun e he => (hExtK e he).2)).1
  have hSeedK : seedCotangentSpec gK.nodeTypes.length gK.boundaryOut.table envK = addSpecCotangent (if K - 1 == 0 then 3 else 6 * K + (K - 1 - 1)) dOut (fun _ => 0) := by
    simp [gK, buildKLaneReductionHypergraph, mkStrictOpenHypergraph, seedCotangentSpec, envK, kLaneInitEnv]
    congr 1 <;> (repeat' split) <;> omega
  have hGradKEq (u : Nat) (hu : u < K) : gradK (6 * u) = rev1.1 ∧ gradK (6 * u + 1) = rev1.2 := by
    dsimp only [gradK]; rw [hSeedK]
    have hFwdV (j : Nat) (hj : j < K) : fwdK (6 * j + 1) = y ∧ fwdK (6 * j + 2) = W * x := by
      dsimp only [fwdK]; rw [hExtEqK, evalHyperEdgesComb_reindexHyperEdges, evalHyperEdgesComb_append]
      have keep (w : Nat) (hw : w < 6*K) := hRedFwd.2 w (Or.inl hw)
      simp (disch := omega) only [keep]
      exact ⟨(hLanesFwd.1 j hj).2.1, (hLanesFwd.1 j hj).2.2.1⟩
    have reduced := redEdges_bwd K fwdK dOut (K-1) (Nat.le_refl _) (fun _ => 0) (fun _ _ => rfl)
    have hAllB := allLanesEdges_bwd K W op2 _ x y dOut hFwdV K (specGradRevOrder fwdK (redEdgesOf K (K-1)).reverse
      (addSpecCotangent (if K-1 == 0 then 3 else 6*K+(K-1-1)) dOut (fun _ => 0))) (Nat.le_refl K) fun j hj => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [reduced _ (by omega)] <;> simp only [Int.zero_add] <;> split <;> first | rfl | omega
    unfold specGradEdges; rw [congrArg List.reverse hExtEqK, specGradRevOrder_reindex, List.reverse_append, specGradRevOrder_append]
    exact hAllB.1 u hu
  have hMapInK : gK.boundaryIn.table.map gradK = (List.range K).flatMap (fun _ => [rev1.1, rev1.2]) := by
    change ((List.range K).flatMap (fun u => [6 * u, 6 * u + 1])).map _ = _
    rw [List.map_flatMap]; apply congrArg List.flatten; apply List.map_congr_left; intro u hu
    obtain ⟨h1, h2⟩ := hGradKEq u (List.mem_range.mp hu); simp [h1, h2]
  have adjK : evalHypergraphComb (compileGraphAdjoint gK) envK = [(K : Int)*z] ++ (List.range K).flatMap (fun _ => [rev1.1, rev1.2]) := by
    rw [hAdjK, hMapInK]; exact congrArg (· ++ _) hCombK
  simp only [(evalHypergraph_pipelined_eq_comb _ _).1]
  exact ⟨hWfK, hWfQ, rfl, hCombK, hCombK, quotient.1, quotient.1, adjK, adjK, quotient.2, quotient.2,
    by rw [sumIntOver_const_of_eq _ rev1.1 _ (fun u hu => (hGradKEq u (List.mem_range.mp hu)).1), List.length_range],
    by rw [sumIntOver_const_of_eq _ rev1.2 _ (fun u hu => (hGradKEq u (List.mem_range.mp hu)).2), List.length_range]⟩

/-! ## 6. General Equivariant Perturbation Zero-Leakage (`equivariant_perturbation_preserves_orbit_subspace`) -/

/-- Squared intra-orbit subspace leakage metric: non-negative and `0` iff `v` is orbit-constant. -/
@[expose] def orbitSubspaceLeakageSq (numWires : Nat) (wireClass : Nat → Nat) (v : Nat → Int) : Int :=
  let wires := List.range numWires
  sumIntOver (fun u => sumIntOver (fun w => if wireClass u == wireClass w then let d := v u - v w; d * d else 0) wires) wires

private theorem sumIntOver_eq_zero_iff_of_nonneg (f : Nat → Int) :
    ∀ (xs : List Nat), (∀ x ∈ xs, 0 ≤ f x) → (sumIntOver f xs = 0 ↔ ∀ x ∈ xs, f x = 0)
  | [], _ => ⟨(fun _ _ h => nomatch h), (fun _ => rfl)⟩
  | x :: xs, hNN => by
    have hx := hNN x List.mem_cons_self; have hR := fun y hy => hNN y (List.mem_cons_of_mem x hy)
    have hRS := sumIntOver_nonneg f xs hR; have hIH := sumIntOver_eq_zero_iff_of_nonneg f xs hR
    dsimp only [sumIntOver]
    exact ⟨fun hS y hy => by rcases List.mem_cons.mp hy with rfl | hY; omega; exact hIH.mp (by omega) y hY,
           fun hA => by have := hA x List.mem_cons_self; have := hIH.mpr (fun y hy => hA y (List.mem_cons_of_mem x hy)); omega⟩

/-- Universal non-negativity of `orbitSubspaceLeakageSq`. -/
theorem orbitSubspaceLeakageSq_nonneg (numWires : Nat) (wireClass : Nat → Nat) (v : Nat → Int) :
    0 ≤ orbitSubspaceLeakageSq numWires wireClass v := by
  unfold orbitSubspaceLeakageSq
  refine sumIntOver_nonneg _ _ fun u _ => sumIntOver_nonneg _ _ fun w _ => ?_
  cases (wireClass u == wireClass w); (simp only [Bool.false_eq_true, ↓reduceIte]; omega); simp only [↓reduceIte]; exact equitable_int_sq_nonneg (v u - v w)

/-- Exact zero characterization of `orbitSubspaceLeakageSq`. -/
theorem orbitSubspaceLeakageSq_eq_zero_iff (numWires : Nat) (wireClass : Nat → Nat) (v : Nat → Int) :
    orbitSubspaceLeakageSq numWires wireClass v = 0 ↔ ∀ u < numWires, ∀ w < numWires, wireClass u = wireClass w → v u = v w := by
  have nn u w : 0 ≤ (if wireClass u == wireClass w then (v u-v w)*(v u-v w) else 0) := by
    split <;> first | exact equitable_int_sq_nonneg _ | omega
  unfold orbitSubspaceLeakageSq
  simp only [sumIntOver_eq_zero_iff_of_nonneg _ _ (fun u _ => sumIntOver_nonneg _ _ (fun w _ => nn u w)),
    sumIntOver_eq_zero_iff_of_nonneg _ _ (fun w _ => nn _ w), List.mem_range]
  constructor
  · intro h u hu w hw same; have eq := h u hu w hw
    simp only [same, beq_self_eq_true, ↓reduceIte, Int.mul_eq_zero, or_self] at eq; omega
  · intro h u hu w hw; split <;> rename_i hc; · simp [h u hu w hw (beq_iff_eq.mp hc)]
    · rfl

/-- Multi-step trajectory of `v0` under a schedule of perturbed Hamiltonians `H + ε_k · dH`. -/
def evolvePerturbedTrajectory (dim : Nat) (H dH : Nat → Nat → Int) (epsSteps : List Int) (v0 : Nat → Int) : Nat → Int :=
  epsSteps.foldl (fun v eps => matVec (List.range dim) (perturbedHamiltonian H dH eps) v) v0

/-- Multi-step quotient trajectory of `w0` under `Q_H + ε_k · Q_dH`. -/
def evolvePerturbedQuotientTrajectory (numCells : Nat) (Q dQ : Nat → Nat → Int) (epsSteps : List Int) (w0 : Nat → Int) : Nat → Int :=
  epsSteps.foldl (fun w eps => quotientMatVec (perturbedQuotient Q dQ eps) (List.range numCells) w) w0

private theorem evolvePerturbedTrajectory_intertwines
    (H dH : IntMatrix) (numCells : Nat) (part : Nat → Nat) (Q_H Q_dH : Nat → Nat → Int)
    (hDim : H.dim = dH.dim) (hEqH : checkEquitablePartition H numCells part Q_H = true) (hEqDH : checkEquitablePartition dH numCells part Q_dH = true) :
    ∀ (epsSteps : List Int) (w0 : Nat → Int) (u : Nat), u < H.dim →
      evolvePerturbedTrajectory H.dim H.entry dH.entry epsSteps (liftQuotientVec part w0) u =
        liftQuotientVec part (evolvePerturbedQuotientTrajectory numCells Q_H Q_dH epsSteps w0) u := by
  intro epsSteps w0; unfold evolvePerturbedTrajectory evolvePerturbedQuotientTrajectory
  apply List.foldl_rel (l := epsSteps) (r := fun (v w : Nat → Int) => ∀ x < H.dim, v x = liftQuotientVec part w x) (fun _ _ => rfl)
  intro eps _ v w agree x hx
  rw [matVec_congr _ _ v (liftQuotientVec part w) x (fun y hy => agree y (List.mem_range.mp hy))]
  unfold matVec perturbedHamiltonian
  rw [sumIntOver_congr _ _ _ (fun y _ => by rw [Int.add_mul, Int.mul_assoc]), sumIntOver_add, sumIntOver_mul_left]
  have a := equitable_intertwining_step_unpartitioned H numCells part Q_H w x hEqH hx
  have b := equitable_intertwining_step_unpartitioned dH numCells part Q_dH w x hEqDH (hDim ▸ hx)
  rw [← hDim] at b; dsimp only [matVec] at a b; rw [a, b]
  unfold liftQuotientVec quotientMatVec perturbedQuotient; rw [← sumIntOver_mul_left, ← sumIntOver_add]
  exact sumIntOver_congr _ _ _ fun j _ => by rw [Int.add_mul, Int.mul_assoc]

/-- Equivariant perturbations preserve orbit-constant graph values and arbitrary finite operator trajectories. -/
theorem equivariant_perturbation_preserves_orbit_subspace
    (G Q : StrictOpenHypergraph) (wireClass edgeClass : Nat → Nat) (deltaQ : Nat → Int)
    (initEnvG initEnvQ etaG etaQ : Nat → Int)
    (hQuot : checkHypergraphQuotient G Q wireClass edgeClass = true)
    (hInit : ∀ w < G.nodeTypes.length, (∀ e ∈ extractHyperEdges G, e.dstWire ≠ w) → initEnvG w = initEnvQ (wireClass w))
    (hEta : ∀ w < G.nodeTypes.length, (∀ e ∈ extractHyperEdges G, e.dstWire ≠ w) → etaG w = etaQ (wireClass w))
    (H dH : IntMatrix) (numCells : Nat) (part : Nat → Nat) (Q_H Q_dH : Nat → Nat → Int)
    (epsSteps : List Int) (w0 : Nat → Int) (hDim : H.dim = dH.dim)
    (hEqH : checkEquitablePartition H numCells part Q_H = true)
    (hEqDH : checkEquitablePartition dH numCells part Q_dH = true) :
    let G' := perturbHypergraphOps G (fun i => deltaQ (edgeClass i))
    let Q' := perturbHypergraphOps Q deltaQ
    let trajH := evolvePerturbedTrajectory H.dim H.entry dH.entry epsSteps (liftQuotientVec part w0)
    let trajQ := evolvePerturbedQuotientTrajectory numCells Q_H Q_dH epsSteps w0
    checkHypergraphQuotient G' Q' wireClass edgeClass = true ∧
    orbitSubspaceLeakageSq G.nodeTypes.length wireClass (evalHyperEdgesComb (fun w => initEnvG w + etaG w) (extractHyperEdges G')) = 0 ∧
    (∀ u < H.dim, trajH u = liftQuotientVec part trajQ u) ∧
    orbitSubspaceLeakageSq H.dim part trajH = 0 := by
  have hQuot' := perturbHypergraphOps_preserves_quotient G Q wireClass edgeClass deltaQ hQuot
  have hFwdP := (evalHypergraph_quotient_intertwines_general
    (perturbHypergraphOps G (fun i => deltaQ (edgeClass i))) (perturbHypergraphOps Q deltaQ)
    wireClass edgeClass (fun w => initEnvG w + etaG w) (fun q => initEnvQ q + etaQ q)
    hQuot' (fun w hw hU => by
      have hU' : ∀ e ∈ extractHyperEdges G, e.dstWire ≠ w := fun e he => hU { e with op := perturbOp (deltaQ (edgeClass e.opIdx)) e.op } (by rw [extractHyperEdges_perturbHypergraphOps]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
      rw [hInit w hw hU', hEta w hw hU'])).1
  have hTraj := evolvePerturbedTrajectory_intertwines H dH numCells part Q_H Q_dH hDim hEqH hEqDH epsSteps w0
  exact ⟨hQuot',
    (orbitSubspaceLeakageSq_eq_zero_iff _ _ _).mpr fun u hu w hw hC => by rw [hFwdP u hu, hFwdP w hw, hC],
    hTraj,
    (orbitSubspaceLeakageSq_eq_zero_iff _ _ _).mpr fun u hu w hw hC => by rw [hTraj u hu, hTraj w hw]; unfold liftQuotientVec; rw [hC]⟩

/-! ## 7. Concrete Mutation-Sensitivity Witnesses (`example`s and `#tooth`, Zero Closed Theorems) -/

example : checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [0], 1⟩, ⟨1, .add, [0, 1], 2⟩] = true := by decide +kernel

example :
    checkHypergraphQuotient (buildSymmetric4LaneHypergraph 5 5 7 7 (.bilinear 3)) (quotientOpenHypergraph 5 7 (.bilinear 3))
      sym4LaneWireClass (sym4LaneEdgeClass (.bilinear 3)) = true ∧
    checkHypergraphQuotient (buildSymmetric4LaneHypergraph 5 99 7 7 (.bilinear 3)) (quotientOpenHypergraph 5 7 (.bilinear 3))
      sym4LaneWireClass (sym4LaneEdgeClass (.bilinear 3)) = false ∧
    (let g := buildSymmetric4LaneHypergraph 5 99 7 7 (.bilinear 3)
     checkHypergraphQuotient g g swapSym4LaneWire (swapSym4LaneEdge (.bilinear 3)) = false) ∧
    checkHypergraphCausalSSA (mkStrictOpenHypergraph 3 [0] [2]
      [ { opIdx := 0, op := .add, srcWires := [0, 2], dstWire := 1 }
      , { opIdx := 1, op := .scale 2, srcWires := [1], dstWire := 2 } ]) = false ∧
    orbitSubspaceLeakageSq 4 majoranaParityPart (liftQuotientVec majoranaParityPart (fun i => if i == 0 then 5 else -3)) = 0 ∧
    orbitSubspaceLeakageSq 4 majoranaParityPart (fun i => if i == 0 then 5 else 2) = 18 := by
  decide +kernel

-- One planted fault per `checkEdgesCausalSSA` clause, in order: arity, destination bound, source bound, input bound,
-- driven input, self-loop, double write, read before write. The empty edge list passes, even with no wires at all.
example :
    checkEdgesCausalSSA 0 [] [] = true ∧ checkEdgesCausalSSA 3 [0] [⟨0, .add, [0], 1⟩] = false ∧ checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [0], 3⟩] = false ∧
    checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [3], 1⟩] = false ∧ checkEdgesCausalSSA 3 [3] [] = false ∧
    checkEdgesCausalSSA 3 [0] [⟨0, .const 1, [], 0⟩] = false ∧ checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [1], 1⟩] = false ∧
    checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [0], 1⟩, ⟨1, .scale 3, [0], 1⟩] = false ∧
    checkEdgesCausalSSA 3 [0] [⟨0, .scale 2, [2], 1⟩, ⟨1, .scale 3, [0], 2⟩] = false := by decide +kernel

-- Three layers with fibers of unequal size: the shared parameter wire `7` (fiber size 1) feeds both lanes (`.mul`, then
-- `.mac`), which rejoin in one product. Wire ids run against the edge order. The quotient keeps one lane and squares it.
private def fanoutFull (numWires : Nat) : StrictOpenHypergraph := mkStrictOpenHypergraph numWires [7, 5, 6] [0]
  [⟨0, .mul, [7, 5], 3⟩, ⟨1, .mul, [7, 6], 4⟩, ⟨2, .mac, [3, 5, 7], 1⟩, ⟨3, .mac, [4, 6, 7], 2⟩, ⟨4, .mul, [1, 2], 0⟩]
private def fanoutQuot (numWires : Nat) (ins outs : List Nat) : StrictOpenHypergraph := mkStrictOpenHypergraph numWires ins outs
  [⟨0, .mul, [4, 3], 2⟩, ⟨1, .mac, [2, 3, 4], 1⟩, ⟨2, .mul, [1, 1], 0⟩]
private def fanoutClass (w : Nat) : Nat := (w + 1) / 2
private def fanoutEnv (q : Nat) : Int := if q == 4 then 3 else if q == 3 then 2 else if q == 5 then 1 else 0

-- Fiber sizes are `[1, 2, 2, 2, 1]`: the quotient adjoint returns the shared wire's gradient once (`150`) and the lane input's
-- summed over its two-wire fiber (`180 + 180`). Then one planted fault per `checkHypergraphQuotient` clause: edge map, output
-- boundary, input boundary, empty cell, ill-formed quotient, undriven wire in a driven class, class out of range (the ninth wire alone is harmless).
example :
    checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 5 [4, 3] [0]) fanoutClass (· / 2) = true ∧
    (List.range 5).map (cellSize (List.range 8) fanoutClass) = [1, 2, 2, 2, 1] ∧
    evalHypergraphComb (compileGraphAdjoint (fanoutFull 8)) (fun w => if w == 8 then 1 else fanoutEnv (fanoutClass w)) = [225, 150, 180, 180] ∧
    evalHypergraphComb (compileGraphAdjoint (fanoutQuot 5 [4, 3] [0])) fanoutEnv = [225, 150, 180 + 180] ∧
    checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 5 [4, 3] [0]) fanoutClass id = false ∧ checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 5 [4, 3] [1]) fanoutClass (· / 2) = false ∧
    checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 5 [4] [0]) fanoutClass (· / 2) = false ∧ checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 6 [4, 3] [0]) fanoutClass (· / 2) = false ∧
    checkHypergraphQuotient (fanoutFull 8) (fanoutQuot 5 [4, 3] [0, 9]) fanoutClass (· / 2) = false ∧
    checkHypergraphQuotient (fanoutFull 9) (fanoutQuot 5 [4, 3] [0]) (fun w => if w == 8 then 0 else fanoutClass w) (· / 2) = false ∧
    checkHypergraphQuotient (fanoutFull 9) (fanoutQuot 5 [4, 3] [0]) (fun w => if w == 8 then 5 else fanoutClass w) (· / 2) = false ∧
    checkHypergraphQuotient (fanoutFull 9) (fanoutQuot 5 [4, 3] [0]) fanoutClass (· / 2) = true := by decide +kernel

-- Edge-free routing: the quotient folds wire pairs and the compiled adjoint only routes seeds `4..7` back to the inputs.
example :
    checkHypergraphQuotient (mkStrictOpenHypergraph 4 [0, 1, 2, 3] [1, 0, 3, 2] []) (mkStrictOpenHypergraph 2 [0, 1] [0, 1] []) (· / 2) id = true ∧
    evalHypergraphComb (compileGraphAdjoint (mkStrictOpenHypergraph 4 [0, 1, 2, 3] [1, 0, 3, 2] [])) (fun w => 10 * (w : Int)) = [10, 0, 30, 20, 50, 40, 70, 60] := by decide +kernel

end Obend.Hardware.OpenHypergraphQuotient
end
