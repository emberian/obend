module
/- Lafont interaction combinators on finite labelled port graphs. Annihilation contracts
alternating wire/bridge paths, including internal loops. The arena correspondence requires
external auxiliary partners. Confluence and uniqueness up to renaming hold for every well-formed net. -/
public import Obend.Hardware.ReductionMachine.Arena
public import Obend.Hardware.Hvm.Inet
import all Obend.Hardware.ReductionMachine

public section

namespace Obend.Hardware.IC
open Obend.Hardware.ReductionMachine
set_option autoImplicit false
private theorem ite_t {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
private theorem ite_f {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

/-! ## 1. Combinator Net Carrier & Decidable Well-Formedness (`WfNet`) -/
inductive CombKind where
  | era | con | dup (label : Nat)
  deriving DecidableEq, Repr, Inhabited
def CombKind.arity : CombKind → Nat | .era => 0 | .con => 2 | .dup _ => 2
def CombKind.toINet : CombKind → INetNodeKind × Nat
  | .era => (.era, 0) | .con => (.con, 0) | .dup l => (.dup, l + 1)
structure Agent where
  id   : Nat
  kind : CombKind
  deriving DecidableEq, Repr, Inhabited
def agentPorts (a : Agent) : List PortRef := match a.kind with | .era => [⟨a.id, 0⟩] | .con | .dup _ => [⟨a.id, 0⟩, ⟨a.id, 1⟩, ⟨a.id, 2⟩]
def agentAuxPorts (a : Agent) : List PortRef := match a.kind with | .era => [] | .con | .dup _ => [⟨a.id, 1⟩, ⟨a.id, 2⟩]
structure ICNet where
  agents    : List Agent
  freePorts : List PortRef
  links     : List (PortRef × PortRef)
  nextId    : Nat
  deriving DecidableEq, Repr, Inhabited
def livePorts (N : ICNet) : List PortRef := (N.agents.flatMap agentPorts) ++ N.freePorts
@[expose] def ICNet.partner (N : ICNet) (p : PortRef) : PortRef := (N.links.lookup p).getD p
structure WfNet (N : ICNet) : Prop where
  agents_nodup : (N.agents.map (·.id)).Nodup
  agents_lt    : ∀ a ∈ N.agents, a.id < N.nextId
  free_nodup   : N.freePorts.Nodup
  free_spec    : ∀ p ∈ N.freePorts, p.slot = 0 ∧ p.nodeId < N.nextId
  free_disj    : ∀ p ∈ N.freePorts, ∀ a ∈ N.agents, p.nodeId ≠ a.id
  links_nodup  : (N.links.map Prod.fst).Nodup
  links_keys   : ∀ p, p ∈ N.links.map Prod.fst ↔ p ∈ livePorts N
  partner_wf   : ∀ p ∈ livePorts N, N.partner p ∈ livePorts N ∧ N.partner p ≠ p ∧ N.partner (N.partner p) = p
def nodupB {α : Type} [DecidableEq α] : List α → Bool
  | [] => true | x :: xs => !(decide (x ∈ xs)) && nodupB xs
theorem nodupB_iff {α : Type} [DecidableEq α] (l : List α) : nodupB l = true ↔ l.Nodup := by induction l <;> simp_all [nodupB]
@[expose] def checkWfNet (N : ICNet) : Bool := let lp := livePorts N; let ks := N.links.map Prod.fst; nodupB (N.agents.map (·.id)) && N.agents.all (fun a => decide (a.id < N.nextId)) &&
  nodupB N.freePorts && N.freePorts.all (fun p => p.slot == 0 && decide (p.nodeId < N.nextId)) &&
  N.freePorts.all (fun p => N.agents.all (fun a => p.nodeId != a.id)) && nodupB ks &&
  ks.all (fun p => decide (p ∈ lp)) && lp.all (fun p => decide (p ∈ ks)) &&
  lp.all (fun p => let q := N.partner p; decide (q ∈ lp) && (q != p) && (N.partner q == p))
theorem checkWfNet_iff (N : ICNet) : checkWfNet N = true ↔ WfNet N := by
  unfold checkWfNet; simp only [Bool.and_eq_true, nodupB_iff, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne]; exact ⟨fun ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, fun p => ⟨h7 p, h8 p⟩, fun p hp => let ⟨⟨a, b⟩, c⟩ := h9 p hp; ⟨a, b, c⟩⟩,
    fun h => ⟨⟨⟨⟨⟨⟨⟨⟨h.agents_nodup, h.agents_lt⟩, h.free_nodup⟩, h.free_spec⟩, h.free_disj⟩, h.links_nodup⟩, fun p hp => (h.links_keys p).1 hp⟩, fun p hp => (h.links_keys p).2 hp⟩,
      fun p hp => let ⟨a, b, c⟩ := h.partner_wf p hp; ⟨⟨a, b⟩, c⟩⟩⟩
def findAgent (N : ICNet) (id : Nat) : Option Agent := N.agents.find? (·.id == id)
def mkLinks (ports : List PortRef) (σ : PortRef → PortRef) : List (PortRef × PortRef) := ports.map fun p => (p, σ p)
def mkNetFrom (agents : List Agent) (freePorts : List PortRef) (σ : PortRef → PortRef) (nextId : Nat) : ICNet := { agents, freePorts, links := mkLinks ((agents.flatMap agentPorts) ++ freePorts) σ, nextId }
theorem mkLinks_map_fst (ports : List PortRef) (σ : PortRef → PortRef) : (mkLinks ports σ).map Prod.fst = ports := by
  induction ports with | nil => rfl | cons _ _ ih => simp only [mkLinks, List.map_cons] at ih ⊢; exact congrArg _ ih
theorem lookup_mkLinks (ports : List PortRef) (σ : PortRef → PortRef) (p : PortRef) : (mkLinks ports σ).lookup p = if p ∈ ports then some (σ p) else none := by
  induction ports with
  | nil => rfl
  | cons q _ ih =>
    simp only [mkLinks, List.map_cons, List.lookup_cons, List.mem_cons]; by_cases h : p = q
    · subst h; simp
    · simp [h, beq_false_of_ne h]; exact ih
theorem partner_mkNetFrom (agents : List Agent) (freePorts : List PortRef) (σ : PortRef → PortRef) (nextId : Nat) (p : PortRef) :
    (mkNetFrom agents freePorts σ nextId).partner p = if p ∈ livePorts (mkNetFrom agents freePorts σ nextId) then σ p else p := by
  simp only [ICNet.partner, mkNetFrom, livePorts, lookup_mkLinks]; by_cases h : p ∈ agents.flatMap agentPorts ++ freePorts <;> simp [h]
theorem partner_of_not_live {N : ICNet} (hWf : WfNet N) {p : PortRef} (hp : p ∉ livePorts N) : N.partner p = p := by
  unfold ICNet.partner; cases h : N.links.lookup p with
  | none => rfl
  | some v => obtain ⟨_, _, hl, _⟩ := List.lookup_eq_some_iff.1 h; exact absurd ((hWf.links_keys p).1 (List.mem_map.2 ⟨(p, v), by simp [hl], rfl⟩)) hp
theorem mem_agentPorts_nodeId {a : Agent} {p : PortRef} (hp : p ∈ agentPorts a) : p.nodeId = a.id := by cases hk : a.kind <;> simp [agentPorts, hk] at hp <;> grind only
theorem principal_mem_agentPorts (a : Agent) : ⟨a.id, 0⟩ ∈ agentPorts a := by cases hk : a.kind <;> simp [agentPorts, hk]
private theorem principal_live {N : ICNet} {a : Agent} (ha : a ∈ N.agents) : ⟨a.id,0⟩ ∈ livePorts N := List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, ha, principal_mem_agentPorts a⟩)
theorem agent_eq_of_id_eq {agents : List Agent} (hnd : (agents.map (·.id)).Nodup) {a b : Agent} (ha : a ∈ agents) (hb : b ∈ agents) (hid : a.id = b.id) : a = b := by
  induction agents with
  | nil => cases ha
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd; rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb <;> grind only
theorem nodup_map_of_inj {α β : Type} {f : α → β} : ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | _, h, inj => List.pairwise_map.2 (h.imp_of_mem fun ha hb ne eq => ne (inj _ ha _ hb eq))
theorem findAgent_list_of_mem : ∀ {as : List Agent}, (as.map (·.id)).Nodup → ∀ {a : Agent}, a ∈ as → as.find? (·.id == a.id) = some a
  | [], _, _, h => by cases h
  | x :: xs, hnd, a, ha => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd; rw [List.find?_cons]; rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · rw [beq_false_of_ne (fun e => hnd.1 ⟨a, ha, e.symm⟩)]; exact findAgent_list_of_mem hnd.2 ha
theorem findAgent_of_mem {N : ICNet} (hWf : WfNet N) {a : Agent} (ha : a ∈ N.agents) : findAgent N a.id = some a := findAgent_list_of_mem hWf.agents_nodup ha
theorem livePorts_lt_nextId {N : ICNet} (hWf : WfNet N) {p : PortRef} (hp : p ∈ livePorts N) : p.nodeId < N.nextId := by
  simp only [livePorts, List.mem_append, List.mem_flatMap] at hp; rcases hp with ⟨a, ha, hpa⟩ | hpf
  · rw [mem_agentPorts_nodeId hpa]; exact hWf.agents_lt a ha
  · exact (hWf.free_spec p hpf).2
theorem wfNet_mkNetFrom {agents : List Agent} {freePorts : List PortRef} {σ : PortRef → PortRef} {nextId : Nat} (hndA : (agents.map (·.id)).Nodup) (hltA : ∀ a ∈ agents, a.id < nextId)
    (hndF : freePorts.Nodup) (hspecF : ∀ p ∈ freePorts, p.slot = 0 ∧ p.nodeId < nextId) (hdisjF : ∀ p ∈ freePorts, ∀ a ∈ agents, p.nodeId ≠ a.id)
    (hσ : ∀ p ∈ (agents.flatMap agentPorts) ++ freePorts, σ p ∈ (agents.flatMap agentPorts) ++ freePorts ∧ σ p ≠ p ∧ σ (σ p) = p) :
    WfNet (mkNetFrom agents freePorts σ nextId) := by
  have hfm : (agents.flatMap agentPorts).Nodup := List.pairwise_flatMap.mpr ⟨ fun a _ => by cases hk : a.kind <;> simp [agentPorts, hk],
    (List.pairwise_map.mp hndA).imp fun ne x hx y hy eq => ne ((mem_agentPorts_nodeId hx).symm.trans (eq ▸ mem_agentPorts_nodeId hy))⟩
  refine ⟨hndA, hltA, hndF, hspecF, hdisjF, ?_, fun p => by simp [mkNetFrom, livePorts, mkLinks_map_fst], fun p hp => ?_⟩
  · simp only [mkNetFrom, mkLinks_map_fst]; rw [List.nodup_append]
    exact ⟨hfm, hndF, fun p hp q hq he => by subst he; obtain ⟨a, ha, hpa⟩ := List.mem_flatMap.1 hp; exact hdisjF p hq a ha (mem_agentPorts_nodeId hpa)⟩
  · obtain ⟨hmem, hne, hinv⟩ := hσ p hp; have hmem' : σ p ∈ livePorts (mkNetFrom agents freePorts σ nextId) := hmem; rw [partner_mkNetFrom, ite_t hp, partner_mkNetFrom, ite_t hmem']; exact ⟨hmem', hne, hinv⟩

/-! ## 2. Active Pairs & Structural Non-Overlap (`wfNet_distinct_redexes_disjoint`) -/
structure IsActivePair (N : ICNet) (i j : Nat) : Prop where
  hne    : i ≠ j
  hi     : ∃ a ∈ N.agents, a.id = i
  hj     : ∃ b ∈ N.agents, b.id = j
  facing : N.partner ⟨i, 0⟩ = ⟨j, 0⟩
theorem IsActivePair.symm {N : ICNet} {i j : Nat} (hWf : WfNet N) (h : IsActivePair N i j) : IsActivePair N j i := by
  obtain ⟨a, ha, rfl⟩ := h.hi; have hinv := (hWf.partner_wf ⟨a.id, 0⟩ (principal_live ha)).2.2; rw [h.facing] at hinv; exact ⟨h.hne.symm, h.hj, ⟨a, ha, rfl⟩, hinv⟩
@[expose] def activePairs (N : ICNet) : List (Nat × Nat) := N.agents.filterMap fun a =>
    let q := N.partner ⟨a.id, 0⟩
    if q.slot == 0 && decide (a.id < q.nodeId) && N.agents.any (fun b => b.id == q.nodeId) then some (a.id, q.nodeId) else none
theorem mem_activePairs_iff {N : ICNet} {i j : Nat} : (i, j) ∈ activePairs N ↔ IsActivePair N i j ∧ i < j := by
  unfold activePairs; rw [List.mem_filterMap]; constructor
  · rintro ⟨a, ha, hs⟩; dsimp only at hs; split at hs <;> simp_all only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true, Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
    obtain ⟨rfl, rfl⟩ := hs; constructor
    · constructor <;> first | solve | grind only | cases eq : N.partner ⟨a.id,0⟩ <;> grind only
    · grind only
  · rintro ⟨⟨_, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hfac⟩, hlt⟩
    have hb' : N.agents.any (fun x => x.id == b.id) = true := List.any_eq_true.2 ⟨b, hb, beq_self_eq_true _⟩; exact ⟨a, ha, by simp [hfac, hlt, hb']⟩
theorem wfNet_distinct_redexes_disjoint (N : ICNet) (i₁ j₁ i₂ j₂ : Nat) (hWf : WfNet N) (h₁ : IsActivePair N i₁ j₁) (h₂ : IsActivePair N i₂ j₂)
    (hdiff : ¬((i₁ = i₂ ∧ j₁ = j₂) ∨ (i₁ = j₂ ∧ j₁ = i₂))) : (i₁ ≠ i₂ ∧ i₁ ≠ j₂ ∧ j₁ ≠ i₂ ∧ j₁ ≠ j₂) ∧
      (∀ a₁ ∈ N.agents, ∀ a₂ ∈ N.agents, (a₁.id = i₁ ∨ a₁.id = j₁) → (a₂.id = i₂ ∨ a₂.id = j₂) → ∀ p ∈ agentPorts a₁, p ∉ agentPorts a₂) := by
  have := h₁.facing; have := h₂.facing; have := (h₁.symm hWf).facing; have := (h₂.symm hWf).facing; grind only [→ mem_agentPorts_nodeId]

/-! ## 3. Port-Pair Involution & Finite Bridge-Contraction Algebra -/
def pairsDom (ps : List (PortRef × PortRef)) : List PortRef := ps.flatMap fun pq => [pq.1, pq.2]
def swapList : List (PortRef × PortRef) → PortRef → PortRef
  | [], x => x | (p, q) :: ps, x => if x = p then q else if x = q then p else swapList ps x
private theorem pairsDom_cons (u v : PortRef) (ps : List (PortRef × PortRef)) : pairsDom ((u,v) :: ps) = u :: v :: pairsDom ps := rfl
theorem swapList_outside : ∀ {ps : List (PortRef × PortRef)} {x : PortRef}, x ∉ pairsDom ps → swapList ps x = x
  | [], _, _ => rfl
  | (_, _) :: _, _, hx => by
    simp only [pairsDom, List.flatMap_cons, List.cons_append, List.nil_append, List.mem_cons, not_or] at hx; simp only [swapList, hx.1, hx.2.1, ite_false]; exact swapList_outside hx.2.2
theorem swapList_wf : ∀ {ps : List (PortRef × PortRef)}, (pairsDom ps).Nodup → (∀ x, swapList ps (swapList ps x) = x) ∧ (∀ x ∈ pairsDom ps, swapList ps x ∈ pairsDom ps ∧ swapList ps x ≠ x)
  | [], _ => ⟨fun _ => rfl, fun _ h => by cases h⟩
  | (p, q) :: ps, hnd => by
    rw [pairsDom_cons] at hnd ⊢; simp only [List.nodup_cons, List.mem_cons, not_or] at hnd; obtain ⟨inv, within⟩ := swapList_wf hnd.2.2
    have hp := swapList_outside hnd.1.2; have hq := swapList_outside hnd.2.1; simp only [swapList, List.mem_cons]; grind -verbose (splits := 16) only
theorem swapList_comm {ps₁ ps₂ : List (PortRef × PortRef)} (h1 : (pairsDom ps₁).Nodup) (h2 : (pairsDom ps₂).Nodup)
    (hdisj : ∀ x ∈ pairsDom ps₁, x ∉ pairsDom ps₂) (x : PortRef) : swapList ps₁ (swapList ps₂ x) = swapList ps₂ (swapList ps₁ x) := by
  by_cases hx1 : x ∈ pairsDom ps₁
  · rw [swapList_outside (hdisj x hx1), swapList_outside (hdisj _ ((swapList_wf h1).2 x hx1).1)]
  · by_cases hx2 : x ∈ pairsDom ps₂
    · rw [swapList_outside hx1, swapList_outside (fun hm => hdisj _ hm ((swapList_wf h2).2 x hx2).1)]
    · rw [swapList_outside hx1, swapList_outside hx2, swapList_outside hx1]
private theorem swapList_map_at {f : PortRef → PortRef} : ∀ (ps : List (PortRef × PortRef)) (x : PortRef), (∀ u ∈ pairsDom ps, f x = f u → x = u) →
    f (swapList ps x) = swapList (ps.map fun pq => (f pq.1, f pq.2)) (f x) := by
  intro ps; induction ps with
  | nil => intro _ _; rfl
  | cons uv ps ih =>
    obtain ⟨u,v⟩ := uv; intro x h; simp only [pairsDom_cons, List.mem_cons] at h; have rest := ih x (fun w hw => h w (.inr (.inr hw))); simp only [List.map_cons, swapList]; grind -verbose only
theorem swapList_map_inj {f : PortRef → PortRef} (hinj : ∀ x y, f x = f y → x = y) : ∀ (ps : List (PortRef × PortRef)) (x : PortRef), f (swapList ps x) = swapList (ps.map fun pq => (f pq.1, f pq.2)) (f x)
  | ps, x => swapList_map_at ps x fun u _ => hinj x u
private theorem mem_pairsDom {ps : List (PortRef × PortRef)} {x : PortRef} : x ∈ pairsDom ps ↔ x ∈ ps.map Prod.fst ∨ x ∈ ps.map Prod.snd := by simp [pairsDom, List.mem_flatMap, List.mem_map]; grind only
private theorem outside_rho {ps : List (PortRef × PortRef)} {i j b s : Nat} (old : ∀ x ∈ ps.map Prod.fst, x.nodeId = i ∨ x.nodeId = j) (new : ∀ x ∈ ps.map Prod.snd, b ≤ x.nodeId ∧ x.nodeId < b + s ∧ x.slot = 0)
    {x : PortRef} (hx : x.nodeId < b) (hi : x.nodeId ≠ i) (hj : x.nodeId ≠ j) : x ∉ pairsDom ps := by
  intro h; rcases mem_pairsDom.mp h with h | h
  · exact (old x h).elim hi hj
  · exact Nat.not_le_of_lt hx (new x h).1
theorem swapList_pair_eq {ps : List (PortRef × PortRef)} (hnd : (pairsDom ps).Nodup) : ∀ {p q : PortRef}, (p, q) ∈ ps → swapList ps p = q ∧ swapList ps q = p := by
  induction ps with
  | nil => intro _ _ h; cases h
  | cons uv ps ih =>
    obtain ⟨u,v⟩ := uv; rw [pairsDom_cons] at hnd; simp only [List.nodup_cons, List.mem_cons, not_or] at hnd; intro p q hpq; rcases List.mem_cons.mp hpq with eq | hm
    · cases eq; simp [swapList, Ne.symm hnd.1.1]
    · have hp : p ∈ pairsDom ps := List.mem_flatMap.mpr ⟨(p,q), hm, by simp⟩
      have hq : q ∈ pairsDom ps := List.mem_flatMap.mpr ⟨(p,q), hm, by simp⟩
      have := ih hnd.2.2 hm; simp only [swapList]; grind only
def applyConj (ρ τ : PortRef → PortRef) (F_aux : List PortRef) (σ : PortRef → PortRef) (p : PortRef) : PortRef := if p ∈ F_aux then τ p else ρ (σ (ρ p))
theorem applyConj_wf {K A F_prin F_aux : List PortRef} {σ ρ τ : PortRef → PortRef} (hσ : ∀ p ∈ K ++ A, σ p ∈ K ++ A ∧ σ p ≠ p ∧ σ (σ p) = p) (hρ_inv : ∀ p, ρ (ρ p) = p) (hρ_map : ∀ p, p ∈ K ++ F_prin ↔ ρ p ∈ K ++ A)
    (hτ : ∀ p ∈ F_aux, τ p ∈ F_aux ∧ τ p ≠ p ∧ τ (τ p) = p) (hdisj : ∀ p ∈ F_aux, p ∉ K ++ F_prin) :
    ∀ p ∈ K ++ F_prin ++ F_aux, applyConj ρ τ F_aux σ p ∈ K ++ F_prin ++ F_aux ∧ applyConj ρ τ F_aux σ p ≠ p ∧ applyConj ρ τ F_aux σ (applyConj ρ τ F_aux σ p) = p := by
  intro p hp; unfold applyConj; by_cases hfa : p ∈ F_aux
  · obtain ⟨h1, h2, h3⟩ := hτ p hfa; simp [hfa, h1, h2, h3]
  · obtain ⟨hs1, hs2, hs3⟩ := hσ (ρ p) ((hρ_map p).1 ((List.mem_append.1 hp).resolve_right hfa)); have hkf : ρ (σ (ρ p)) ∈ K ++ F_prin := by rw [hρ_map, hρ_inv]; exact hs1
    have hnf : ρ (σ (ρ p)) ∉ F_aux := fun hm => hdisj _ hm hkf; simp only [hfa, hnf, ite_false]; exact ⟨List.mem_append_left _ hkf, fun he => hs2 (by rw [← hρ_inv (σ (ρ p)), he]), by rw [hρ_inv, hs3, hρ_inv]⟩
theorem applyConj_comm {ρ₁ τ₁ ρ₂ τ₂ : PortRef → PortRef} {F₁ F₂ : List PortRef} (σ : PortRef → PortRef) (hρ_comm : ∀ x, ρ₁ (ρ₂ x) = ρ₂ (ρ₁ x)) (hF1_ρ2 : ∀ x ∈ F₁, ρ₂ x = x) (hF2_ρ1 : ∀ x ∈ F₂, ρ₁ x = x)
    (hF1_τ1 : ∀ x ∈ F₁, τ₁ x ∈ F₁) (hF2_τ2 : ∀ x ∈ F₂, τ₂ x ∈ F₂) (hF_disj : ∀ x ∈ F₁, x ∉ F₂)
    (hρ1_F2 : ∀ x, ρ₁ x ∈ F₂ ↔ x ∈ F₂) (hρ2_F1 : ∀ x, ρ₂ x ∈ F₁ ↔ x ∈ F₁) (p : PortRef) :
    applyConj ρ₂ τ₂ F₂ (applyConj ρ₁ τ₁ F₁ σ) p = applyConj ρ₁ τ₁ F₁ (applyConj ρ₂ τ₂ F₂ σ) p := by
  unfold applyConj; by_cases h2 : p ∈ F₂
  · have h1 : p ∉ F₁ := fun hm => hF_disj p hm h2; simp [h2, h1, hF2_ρ1 p h2, hF2_ρ1 _ (hF2_τ2 p h2)]
  · by_cases h1 : p ∈ F₁
    · simp [h2, h1, hF1_ρ2 p h1, hF1_ρ2 _ (hF1_τ1 p h1)]
    · simp [h2, h1, show ρ₂ p ∉ F₁ by rwa [hρ2_F1], show ρ₁ p ∉ F₂ by rwa [hρ1_F2], hρ_comm]

/-! ### Finite Involution Bridge Contraction (`contractBridge`) -/
def walkAux (σ β : PortRef → PortRef) (inA : PortRef → Bool) : Nat → PortRef → PortRef
  | 0, q => q | fuel + 1, q => if inA q then walkAux σ β inA fuel (σ (β q)) else q
def contractBridge (σ β : PortRef → PortRef) (A : List PortRef) (p : PortRef) : PortRef := walkAux σ β (fun q => decide (q ∈ A)) A.length (σ p)
def bridgeFwd (σ β : PortRef → PortRef) : Nat → PortRef → PortRef
  | 0, p => σ p | k + 1, p => σ (β (bridgeFwd σ β k p))
theorem bridgeFwd_succ_right (σ β : PortRef → PortRef) (k : Nat) (p : PortRef) : bridgeFwd σ β (k + 1) p = bridgeFwd σ β k (β (σ p)) := by
  induction k with | zero => rfl | succ _ ih => exact congrArg (fun x => σ (β x)) ih
theorem bridgeFwd_rev {σ β : PortRef → PortRef} {P A : List PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ : ∀ x ∈ A, β x ∈ A ∧ β (β x) = x) (hAP : ∀ x ∈ A, x ∈ P) :
    ∀ (k : Nat) (p : PortRef), p ∈ P → (∀ j < k, bridgeFwd σ β j p ∈ A) → (∀ j < k, bridgeFwd σ β j (bridgeFwd σ β k p) = β (bridgeFwd σ β (k - 1 - j) p)) ∧ bridgeFwd σ β k (bridgeFwd σ β k p) = p
  | 0, p, hp, _ => ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), (hσ p hp).2⟩
  | k + 1, p, hp, hall => by
    have h0A := hall 0 (Nat.zero_lt_succ k); obtain ⟨ih_lt, ih_eq⟩ := bridgeFwd_rev hσ hβ hAP k (β (σ p)) (hAP _ (hβ _ h0A).1) (fun j hj => by rw [← bridgeFwd_succ_right]; exact hall (j + 1) (Nat.succ_lt_succ hj))
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [bridgeFwd_succ_right]; by_cases hjk : j < k
      · rw [ih_lt j hjk, show k + 1 - 1 - j = (k - 1 - j) + 1 by omega, bridgeFwd_succ_right]
      · have hje : j = k := by omega
        rw [hje, ih_eq, show k + 1 - 1 - k = 0 by omega]; rfl
    · change σ (β (bridgeFwd σ β k (bridgeFwd σ β (k + 1) p))) = p; rw [bridgeFwd_succ_right σ β k p, ih_eq]; have h0A' : σ p ∈ A := h0A; rw [(hβ _ h0A').2, (hσ p hp).2]
theorem bridgeFwd_mem_P {σ β : PortRef → PortRef} {P A : List PortRef} (hσ : ∀ x ∈ P, σ x ∈ P) (hβ : ∀ x ∈ A, β x ∈ A) (hAP : ∀ x ∈ A, x ∈ P) {p : PortRef} (hp : p ∈ P) :
    ∀ (k : Nat), (∀ j < k, bridgeFwd σ β j p ∈ A) → bridgeFwd σ β k p ∈ P
  | 0, _ => hσ p hp
  | k + 1, hall => hσ _ (hAP _ (hβ _ (hall k (Nat.lt_succ_self k))))
theorem bridgeFwd_inj_steps {σ β : PortRef → PortRef} {P A : List PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ : ∀ x ∈ A, β x ∈ A ∧ β (β x) = x) (hAP : ∀ x ∈ A, x ∈ P)
    {p : PortRef} (hp : p ∈ P) (hpA : p ∉ A) {m : Nat} (hall : ∀ j < m, bridgeFwd σ β j p ∈ A) :
    ∀ {a b : Nat}, a < b → b ≤ m → bridgeFwd σ β a p = bridgeFwd σ β b p → False
  | 0, 0, hab, _, _ => by omega
  | 0, b' + 1, _, hbm, heq => by
    have hβA := (hβ _ (hall b' (by omega))).1
    have h1 := congrArg σ heq; simp only [bridgeFwd] at h1; rw [(hσ p hp).2, (hσ _ (hAP _ hβA)).2] at h1; exact hpA (h1 ▸ hβA)
  | _ + 1, 0, hab, _, _ => by omega
  | a' + 1, b' + 1, hab, hbm, heq => by
    have haA := hall a' (by omega); have hbA := hall b' (by omega)
    have h1 := congrArg σ heq; simp only [bridgeFwd] at h1; rw [(hσ _ (hAP _ (hβ _ haA).1)).2, (hσ _ (hAP _ (hβ _ hbA).1)).2] at h1
    have h2 := congrArg β h1; rw [(hβ _ haA).2, (hβ _ hbA).2] at h2; exact bridgeFwd_inj_steps hσ hβ hAP hp hpA hall (by omega) (by omega) h2
theorem bridgeFwd_exists_exit {σ β : PortRef → PortRef} {P A : List PortRef}
    (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ : ∀ x ∈ A, β x ∈ A ∧ β (β x) = x) (hAP : ∀ x ∈ A, x ∈ P) {p : PortRef} (hp : p ∈ P) (hpA : p ∉ A) :
    ∃ k ≤ A.length, (∀ j < k, bridgeFwd σ β j p ∈ A) ∧ bridgeFwd σ β k p ∉ A := by
  let path := bridgeFwd σ β; apply Classical.byContradiction; intro missing; have allA (k : Nat) (hk : k ≤ A.length) : path k p ∈ A := by
    induction k using Nat.strongRecOn with
    | ind k ih => exact Decidable.byContradiction fun h => missing ⟨k, hk, fun j hj => ih j hj (by omega), h⟩
  have distinct {a b : Nat} (hab : a < b) (hb : b ≤ A.length) : path a p = path b p → False := bridgeFwd_inj_steps hσ hβ hAP hp hpA (m := A.length) (fun j hj => allA j (by omega)) hab hb
  have nd : ((List.range (A.length + 1)).map (fun j => path j p)).Nodup := nodup_map_of_inj List.nodup_range fun a ha b hb eq => by
      simp only [List.mem_range] at ha hb; rcases Nat.lt_trichotomy a b with h | h | h
      · exact (distinct h (by omega) eq).elim
      · exact h
      · exact (distinct h (by omega) eq.symm).elim
  have bound := nd.length_le_of_subset (l₂ := A) (by intro x hx; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx; exact allA j (by simp at hj; omega))
  simp at bound; omega
theorem walkAux_eq_bridgeFwd (σ β : PortRef → PortRef) (A : List PortRef) : ∀ (fuel k : Nat) (q : PortRef), k ≤ fuel →
      (∀ j < k, bridgeFwd σ β j q ∈ A) → bridgeFwd σ β k q ∉ A → walkAux σ β (fun x => decide (x ∈ A)) fuel (σ q) = bridgeFwd σ β k q
  | 0, k, _, hk, _, _ => by
      have hk0 : k = 0 := by omega
      subst hk0; rfl
  | _ + 1, 0, q, _, _, hex => by have h0 : σ q ∉ A := hex; simp [walkAux, h0, bridgeFwd]
  | fuel + 1, k' + 1, q, hk, hall, hex => by
    have h0 : σ q ∈ A := hall 0 (Nat.zero_lt_succ k'); simp only [walkAux, decide_eq_true h0, ite_true]; rw [bridgeFwd_succ_right σ β k' q]
    exact walkAux_eq_bridgeFwd σ β A fuel k' (β (σ q)) (by omega) (fun j hj => by rw [← bridgeFwd_succ_right]; exact hall (j + 1) (Nat.succ_lt_succ hj)) (by rw [← bridgeFwd_succ_right]; exact hex)
def WalkSpec (σ β : PortRef → PortRef) (A : List PortRef) (p q : PortRef) : Prop := ∃ k, (∀ j < k, bridgeFwd σ β j p ∈ A) ∧ bridgeFwd σ β k p = q ∧ q ∉ A
theorem walkSpec_unique {σ β : PortRef → PortRef} {A : List PortRef} {p q₁ q₂ : PortRef} (h₁ : WalkSpec σ β A p q₁) (h₂ : WalkSpec σ β A p q₂) : q₁ = q₂ := by
  obtain ⟨k₁, ha₁, rfl, he₁⟩ := h₁; obtain ⟨k₂, ha₂, rfl, he₂⟩ := h₂; grind only
theorem contractBridge_spec {σ β : PortRef → PortRef} {P A : List PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ : ∀ x ∈ A, β x ∈ A ∧ β (β x) = x) (hAP : ∀ x ∈ A, x ∈ P)
    {p : PortRef} (hp : p ∈ P) (hpA : p ∉ A) : WalkSpec σ β A p (contractBridge σ β A p) := by
  obtain ⟨k, hkle, hall, hex⟩ := bridgeFwd_exists_exit hσ hβ hAP hp hpA; have heq : contractBridge σ β A p = bridgeFwd σ β k p := walkAux_eq_bridgeFwd σ β A A.length k p hkle hall hex
  exact ⟨k, hall, heq.symm, by rwa [heq]⟩
theorem contractBridge_wf {σ β : PortRef → PortRef} {P A : List PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ x ≠ x ∧ σ (σ x) = x) (hβ : ∀ x ∈ A, β x ∈ A ∧ β x ≠ x ∧ β (β x) = x)
    (hAP : ∀ x ∈ A, x ∈ P) {p : PortRef} (hp : p ∈ P) (hpA : p ∉ A) :
    let q := contractBridge σ β A p; q ∈ P ∧ q ∉ A ∧ q ≠ p ∧ contractBridge σ β A q = p := by
  have hσ2 : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x := fun x hx => ⟨(hσ x hx).1, (hσ x hx).2.2⟩; have hβ2 : ∀ x ∈ A, β x ∈ A ∧ β (β x) = x := fun x hx => ⟨(hβ x hx).1, (hβ x hx).2.2⟩
  obtain ⟨k, hall, hqeq, hqA⟩ := contractBridge_spec hσ2 hβ2 hAP hp hpA
  have hqP : contractBridge σ β A p ∈ P := by rw [← hqeq]; exact bridgeFwd_mem_P (fun x hx => (hσ x hx).1) (fun x hx => (hβ x hx).1) hAP hp k hall
  obtain ⟨hrev_lt, hrev_eq⟩ := bridgeFwd_rev hσ2 hβ2 hAP k p hp hall; have hinv : contractBridge σ β A (contractBridge σ β A p) = p := walkSpec_unique (contractBridge_spec hσ2 hβ2 hAP hqP hqA)
      ⟨k, fun j hj => by rw [← hqeq, hrev_lt j hj]; exact (hβ _ (hall (k - 1 - j) (by omega))).1, by rw [← hqeq]; exact hrev_eq, hpA⟩
  have hne : contractBridge σ β A p ≠ p := by
    intro heq; rw [heq] at hqeq; cases k with
    | zero => exact (hσ p hp).2.1 hqeq
    | succ k' =>
      by_cases hpar : k' % 2 = 0
      · have h1 := hrev_lt (k' / 2) (by omega); rw [hqeq, show k' + 1 - 1 - k' / 2 = k' / 2 by omega] at h1
        exact (hβ _ (hall (k' / 2) (by omega))).2.1 h1.symm
      · have h1 := hrev_lt (k' / 2) (by omega); rw [hqeq, show k' + 1 - 1 - k' / 2 = k' / 2 + 1 by omega] at h1
        have h2 := congrArg β h1; rw [(hβ _ (hall (k' / 2 + 1) (by omega))).2.2] at h2
        exact (hσ _ (hAP _ (hβ _ (hall (k' / 2) (by omega))).1)).2.1 h2.symm
  exact ⟨hqP, hqA, hne, hinv⟩
private theorem bridge_transport {D : PortRef → Prop} {A₁ A₂ : List PortRef} {σ₁ β₁ σ₂ β₂ f : PortRef → PortRef}
    (hσ₁ : ∀ p, D p → D (σ₁ p)) (next : ∀ p ∈ A₁, D (β₁ p)) (hA_iff : ∀ p, D p → (p ∈ A₁ ↔ f p ∈ A₂)) (hσ_f : ∀ p, D p → f (σ₁ p) = σ₂ (f p))
    (hβ_f : ∀ p ∈ A₁, f (β₁ p) = β₂ (f p)) (hlen : A₁.length = A₂.length) {p : PortRef} (hp : D p) :
    f (contractBridge σ₁ β₁ A₁ p) = contractBridge σ₂ β₂ A₂ (f p) := by
  have hwalk : ∀ fuel q, D q → f (walkAux σ₁ β₁ (fun x => decide (x ∈ A₁)) fuel q) = walkAux σ₂ β₂ (fun x => decide (x ∈ A₂)) fuel (f q) := by
    intro fuel; induction fuel with
    | zero => intro _ _; rfl
    | succ fuel ih =>
      intro q hq; simp only [walkAux]; by_cases hqA : q ∈ A₁
      · simp only [decide_eq_true hqA, decide_eq_true ((hA_iff q hq).1 hqA), ite_true]; have hβq := next q hqA; rw [ih _ (hσ₁ _ hβq), hσ_f _ hβq, hβ_f q hqA]
      · simp [decide_eq_false_iff_not.2 hqA, decide_eq_false_iff_not.2 (fun h => hqA ((hA_iff q hq).2 h))]
  unfold contractBridge; rw [← hlen, hwalk A₁.length (σ₁ p) (hσ₁ p hp), hσ_f p hp]
/-- Conjugation can cross a bridge walk of any fuel because it fixes every internal endpoint. -/
private theorem bridge_conj {A F : List PortRef} {σ β ρ τ : PortRef → PortRef}
    (next : ∀ x ∈ A, β x ∈ A) (fix : ∀ x ∈ A, ρ x = x) (mem : ∀ x, ρ x ∈ A ↔ x ∈ A) (fresh : ∀ x ∈ F, τ x ∈ F) (apart : ∀ x ∈ F, x ∉ A) (p : PortRef) :
    contractBridge (applyConj ρ τ F σ) β A p = applyConj ρ τ F (contractBridge σ β A) p := by
  have walk (fuel : Nat) (x : PortRef) : walkAux (applyConj ρ τ F σ) β (fun y => decide (y ∈ A)) fuel (ρ x) = ρ (walkAux σ β (fun y => decide (y ∈ A)) fuel x) := by
    induction fuel generalizing x with
    | zero => rfl
    | succ _ ih =>
      by_cases hx : x ∈ A
      · have hb := next x hx; have hf : β x ∉ F := fun h => apart _ h hb; simp only [walkAux, decide_eq_true hx, ite_true, fix x hx, applyConj, hf, ite_false, fix _ hb, ih]
      · simp [walkAux, hx, show ρ x ∉ A from fun h => hx ((mem x).1 h)]
  by_cases hp : p ∈ F
  · have h := apart _ (fresh p hp); cases he : A.length <;> simp [applyConj, hp, contractBridge, he, walkAux, h]
  · simpa only [applyConj, hp, ite_false, contractBridge] using walk A.length (σ (ρ p))
theorem mergeBridge_wf {A₁ A₂ : List PortRef} {β₁ β₂ : PortRef → PortRef} (hβ₁ : ∀ x ∈ A₁, β₁ x ∈ A₁ ∧ β₁ (β₁ x) = x) (hβ₂ : ∀ x ∈ A₂, β₂ x ∈ A₂ ∧ β₂ (β₂ x) = x) (hdisj : ∀ x ∈ A₁, x ∉ A₂) :
    ∀ x ∈ A₁ ++ A₂, (if x ∈ A₁ then β₁ x else β₂ x) ∈ A₁ ++ A₂ ∧ (if (if x ∈ A₁ then β₁ x else β₂ x) ∈ A₁ then β₁ (if x ∈ A₁ then β₁ x else β₂ x) else β₂ (if x ∈ A₁ then β₁ x else β₂ x)) = x := by
  intro x hx; by_cases h1 : x ∈ A₁
  · simp [h1, (hβ₁ x h1).1, (hβ₁ x h1).2]
  · have h2 := (List.mem_append.1 hx).resolve_left h1; simp [h1, show β₂ x ∉ A₁ from fun hm => hdisj _ hm (hβ₂ x h2).1, (hβ₂ x h2).1, (hβ₂ x h2).2]
theorem contractBridge_nested {P A₁ A₂ : List PortRef} {σ β₁ β₂ : PortRef → PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ₁ : ∀ x ∈ A₁, β₁ x ∈ A₁ ∧ β₁ (β₁ x) = x)
    (hβ₂ : ∀ x ∈ A₂, β₂ x ∈ A₂ ∧ β₂ (β₂ x) = x) (hAP₁ : ∀ x ∈ A₁, x ∈ P) (hAP₂ : ∀ x ∈ A₂, x ∈ P)
    (hdisj : ∀ x ∈ A₁, x ∉ A₂) {p : PortRef} (hp : p ∈ P) (hp1 : p ∉ A₁) (hp2 : p ∉ A₂) : contractBridge (contractBridge σ β₁ A₁) β₂ A₂ p =
      contractBridge σ (fun x => if x ∈ A₁ then β₁ x else β₂ x) (A₁ ++ A₂) p := by
  let β₁₂ := fun x => if x ∈ A₁ then β₁ x else β₂ x; have hβ₁₂ := mergeBridge_wf hβ₁ hβ₂ hdisj; have hAP₁₂ : ∀ x ∈ A₁ ++ A₂, x ∈ P := fun x hx => (List.mem_append.1 hx).elim (hAP₁ x) (hAP₂ x)
  have hnest : ∀ (k : Nat) (x q : PortRef), x ∈ P → x ∉ A₁ → (∀ j < k, bridgeFwd σ β₁₂ j x ∈ A₁ ++ A₂) → bridgeFwd σ β₁₂ k x = q → q ∉ A₁ ++ A₂ → WalkSpec (contractBridge σ β₁ A₁) β₂ A₂ x q := by
    intro k; induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x q hxP hx1 hall hqeq hq12; obtain ⟨m, hm_all, hmr, hr1⟩ := contractBridge_spec hσ hβ₁ hAP₁ hxP hx1; have hagree : ∀ j ≤ m, bridgeFwd σ β₁₂ j x = bridgeFwd σ β₁ j x := by
        intro j hj; induction j with
        | zero => rfl
        | succ j' ihj => simp only [bridgeFwd, ihj (by omega), β₁₂, hm_all j' (by omega), ite_true]
      have hmk : m ≤ k := by
        by_cases hle : m ≤ k
        · exact hle
        · exact False.elim (hq12 (List.mem_append_left _ (by rw [← hqeq, hagree k (by omega)]; exact hm_all k (by omega))))
      by_cases heq : m = k
      · subst heq; exact ⟨0, fun _ hj => absurd hj (Nat.not_lt_zero _), (by change contractBridge σ β₁ A₁ x = q; rw [← hmr, ← hagree m (Nat.le_refl _), hqeq]), fun h => hq12 (List.mem_append_right _ h)⟩
      · have hr2 : contractBridge σ β₁ A₁ x ∈ A₂ := (List.mem_append.1 (by rw [← hmr, ← hagree m (Nat.le_refl _)]; exact hall m (by omega))).resolve_left hr1
        let x' := β₂ (contractBridge σ β₁ A₁ x); have hx'2 := (hβ₂ _ hr2).1; have hshift : ∀ j, bridgeFwd σ β₁₂ j x' = bridgeFwd σ β₁₂ (m + 1 + j) x := by
          intro j; induction j with
          | zero => simp only [bridgeFwd, x']; rw [hagree m (Nat.le_refl _), hmr]; simp [β₁₂, hr1]
          | succ j' ihj => rw [show m + 1 + (j' + 1) = (m + 1 + j') + 1 by omega, bridgeFwd, bridgeFwd, ihj]
        obtain ⟨t, ht_all, ht_eq, ht_ex⟩ := ih (k - (m + 1)) (by omega) x' q (hAP₂ x' hx'2) (fun hm => hdisj x' hm hx'2) (fun j hj => by rw [hshift j]; exact hall (m + 1 + j) (by omega))
          (by rw [hshift, show m + 1 + (k - (m + 1)) = k by omega]; exact hqeq) hq12
        exact ⟨t + 1, fun j hj => by cases j with | zero => exact hr2 | succ j' => rw [bridgeFwd_succ_right]; exact ht_all j' (by omega), by rw [bridgeFwd_succ_right]; exact ht_eq, ht_ex⟩
  obtain ⟨k, hall, hqeq, hq12⟩ := contractBridge_spec hσ hβ₁₂ hAP₁₂ hp (fun h => (List.mem_append.1 h).elim hp1 hp2)
  have hσ₁_P : ∀ x ∈ P.filter (fun y => !(decide (y ∈ A₁))), contractBridge σ β₁ A₁ x ∈ P.filter (fun y => !(decide (y ∈ A₁))) ∧ contractBridge σ β₁ A₁ (contractBridge σ β₁ A₁ x) = x := by
    intro x hx; simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hx ⊢; obtain ⟨m, hm_all, hmr, hr1⟩ := contractBridge_spec hσ hβ₁ hAP₁ hx.1 hx.2
    have hrP : contractBridge σ β₁ A₁ x ∈ P := by rw [← hmr]; exact bridgeFwd_mem_P (fun y hy => (hσ y hy).1) (fun y hy => (hβ₁ y hy).1) hAP₁ hx.1 m hm_all
    obtain ⟨hrev_lt, hrev_eq⟩ := bridgeFwd_rev hσ hβ₁ hAP₁ m x hx.1 hm_all; exact ⟨⟨hrP, hr1⟩, walkSpec_unique (contractBridge_spec hσ hβ₁ hAP₁ hrP hr1)
      ⟨m, fun j hj => by rw [← hmr, hrev_lt j hj]; exact (hβ₁ _ (hm_all (m - 1 - j) (by omega))).1, by rw [← hmr]; exact hrev_eq, hx.2⟩⟩
  exact walkSpec_unique (contractBridge_spec hσ₁_P hβ₂ (fun x hx => List.mem_filter.2 ⟨hAP₂ x hx, by have hnd : x ∉ A₁ := fun hm => hdisj x hm hx; simp [hnd]⟩)
    (List.mem_filter.2 ⟨hp, by simp [hp1]⟩) hp2) (hnest k p _ hp hp1 hall hqeq hq12)
/-- **Disjoint bridge commutation**. -/
theorem contractBridge_comm {P A₁ A₂ : List PortRef} {σ β₁ β₂ : PortRef → PortRef} (hσ : ∀ x ∈ P, σ x ∈ P ∧ σ (σ x) = x) (hβ₁ : ∀ x ∈ A₁, β₁ x ∈ A₁ ∧ β₁ (β₁ x) = x)
    (hβ₂ : ∀ x ∈ A₂, β₂ x ∈ A₂ ∧ β₂ (β₂ x) = x) (hAP₁ : ∀ x ∈ A₁, x ∈ P) (hAP₂ : ∀ x ∈ A₂, x ∈ P)
    (hdisj : ∀ x ∈ A₁, x ∉ A₂) {p : PortRef} (hp : p ∈ P) (hp1 : p ∉ A₁) (hp2 : p ∉ A₂) :
    contractBridge (contractBridge σ β₁ A₁) β₂ A₂ p = contractBridge (contractBridge σ β₂ A₂) β₁ A₁ p := by
  have hdisj' : ∀ x ∈ A₂, x ∉ A₁ := fun x hx hm => hdisj x hm hx; rw [contractBridge_nested hσ hβ₁ hβ₂ hAP₁ hAP₂ hdisj hp hp1 hp2, contractBridge_nested hσ hβ₂ hβ₁ hAP₂ hAP₁ hdisj' hp hp2 hp1]
  refine bridge_transport (f := id) (p := p) (A₁ := A₁ ++ A₂) (A₂ := A₂ ++ A₁) (σ₁ := σ) (σ₂ := σ) (β₁ := fun x => if x ∈ A₁ then β₁ x else β₂ x) (β₂ := fun x => if x ∈ A₂ then β₂ x else β₁ x)
    (D := fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => by simp [or_comm]) (fun _ _ => rfl)
    (fun x hx => by simp only [List.mem_append] at hx; dsimp; grind only)
    (by simp [Nat.add_comm]) trivial

/-! ## 4. Unified Lafont Rules (`PairKind`, `RuleOp`), `fireActivePair` & `WfNet` Preservation -/
inductive PairKind where | void | era (bin : Nat) | anni | comm (ka kb : CombKind) deriving DecidableEq
def classifyPair (i j : Nat) : CombKind → CombKind → PairKind
  | .era, .era => .void
  | .era, .con | .era, .dup _ => .era j
  | .con, .era | .dup _, .era => .era i
  | .con, .con => .anni
  | .dup l1, .dup l2 => if l1 = l2 then .anni else .comm (.dup l1) (.dup l2)
  | .con, .dup l => .comm .con (.dup l)
  | .dup l, .con => .comm (.dup l) .con
inductive RuleOp where
  | conj (s : Nat) (sp : List Agent) (rhoPairs tauPairs : List (PortRef × PortRef))
  | bridge (bridgePairs : List (PortRef × PortRef))
def RuleOp.spawnCount : RuleOp → Nat | .conj s _ _ _ => s | .bridge _ => 0
def RuleOp.spawned : RuleOp → List Agent | .conj _ sp _ _ => sp | .bridge _ => []
def RuleOp.apply (op : RuleOp) (σ : PortRef → PortRef) : PortRef → PortRef := match op with
  | .conj _ _ rP tP => applyConj (swapList rP) (swapList tP) (pairsDom tP) σ
  | .bridge bP => contractBridge σ (swapList bP) (pairsDom bP)
def commTauPairs (b : Nat) : List (PortRef × PortRef) := [(⟨b, 1⟩, ⟨b + 2, 1⟩), (⟨b, 2⟩, ⟨b + 3, 1⟩), (⟨b + 1, 1⟩, ⟨b + 2, 2⟩), (⟨b + 1, 2⟩, ⟨b + 3, 2⟩)]
def PairKind.toOp (i j b : Nat) : PairKind → RuleOp
  | .void => .conj 0 [] [] []
  | .era bin => .conj 2 [⟨b, .era⟩, ⟨b + 1, .era⟩] [(⟨bin, 1⟩, ⟨b, 0⟩), (⟨bin, 2⟩, ⟨b + 1, 0⟩)] []
  | .anni => .bridge [(⟨i, 1⟩, ⟨j, 1⟩), (⟨i, 2⟩, ⟨j, 2⟩)]
  | .comm ka kb => .conj 4 [⟨b, kb⟩, ⟨b + 1, kb⟩, ⟨b + 2, ka⟩, ⟨b + 3, ka⟩] [(⟨i, 1⟩, ⟨b, 0⟩), (⟨i, 2⟩, ⟨b + 1, 0⟩), (⟨j, 1⟩, ⟨b + 2, 0⟩), (⟨j, 2⟩, ⟨b + 3, 0⟩)] (commTauPairs b)
def classifyRule (i j : Nat) (ki kj : CombKind) (b : Nat) : RuleOp := (classifyPair i j ki kj).toOp i j b
private theorem spawned_shift {i j i' j' b b' : Nat} {ka kb : CombKind} {f : Nat → Nat}
    (shift : ∀ k < (classifyRule i j ka kb b).spawnCount, f (b + k) = b' + k) (x : Agent) (hx : x ∈ (classifyRule i j ka kb b).spawned) :
    ⟨f x.id, x.kind⟩ ∈ (classifyRule i' j' ka kb b').spawned := by
  cases ka <;> cases kb <;> unfold classifyRule classifyPair at *
  all_goals try (rename_i l r; by_cases h : l = r <;> simp only [h, ite_true, ite_false] at *)
  all_goals simp [PairKind.toOp, RuleOp.spawned, RuleOp.spawnCount] at hx shift ⊢
  all_goals have h0 := shift 0; have h1 := shift 1; have h2 := shift 2; have h3 := shift 3
  all_goals simp_all <;> grind only
def firePairWith (N : ICNet) (i j : Nat) (ki kj : CombKind) (base : Nat) : ICNet := let op := classifyRule i j ki kj base; mkNetFrom (N.agents.filter (fun a => a.id != i && a.id != j) ++ op.spawned)
    N.freePorts (op.apply N.partner) (base + op.spawnCount)
@[expose] def fireActivePair (N : ICNet) (i j : Nat) : Option ICNet := if i == j then none else match findAgent N i, findAgent N j with
    | some a, some b => if N.partner ⟨i, 0⟩ == ⟨j, 0⟩ && N.partner ⟨j, 0⟩ == ⟨i, 0⟩ then some (firePairWith N i j a.kind b.kind N.nextId) else none
    | _, _ => none
inductive Step : ICNet → ICNet → Prop where
  | fire {N N' : ICNet} {i j : Nat} : IsActivePair N i j → fireActivePair N i j = some N' → Step N N'
inductive Steps : ICNet → ICNet → Prop where
  | refl (N : ICNet) : Steps N N
  | next {N₁ N₂ N₃ : ICNet} : Step N₁ N₂ → Steps N₂ N₃ → Steps N₁ N₃
theorem Steps.single {N₁ N₂ : ICNet} (h : Step N₁ N₂) : Steps N₁ N₂ := .next h (.refl _)
theorem Steps.trans {N₁ N₂ N₃ : ICNet} (h₁ : Steps N₁ N₂) (h₂ : Steps N₂ N₃) : Steps N₁ N₃ := by induction h₁ with | refl => exact h₂ | next s _ ih => exact .next s (ih h₂)
private theorem fire_known {N : ICNet} {a b : Agent} (wf : WfNet N) (active : IsActivePair N a.id b.id) (ha : a ∈ N.agents) (hb : b ∈ N.agents) :
    fireActivePair N a.id b.id = some (firePairWith N a.id b.id a.kind b.kind N.nextId) := by
  simp [fireActivePair, beq_false_of_ne active.hne, findAgent_of_mem wf ha, findAgent_of_mem wf hb, active.facing, (active.symm wf).facing]
theorem fireActivePair_of_active {N : ICNet} {i j : Nat} (hWf : WfNet N) (hAct : IsActivePair N i j) :
    ∃ a b, a ∈ N.agents ∧ a.id = i ∧ b ∈ N.agents ∧ b.id = j ∧ fireActivePair N i j = some (firePairWith N i j a.kind b.kind N.nextId) := by
  obtain ⟨a, ha, rfl⟩ := hAct.hi; obtain ⟨b, hb, rfl⟩ := hAct.hj; exact ⟨a, b, ha, rfl, hb, rfl, fire_known hWf hAct ha hb⟩
theorem livePorts_split {N : ICNet} (hWf : WfNet N) {a b : Agent} (ha : a ∈ N.agents) (hb : b ∈ N.agents) (hne : a.id ≠ b.id) (p : PortRef) :
    let K := ((N.agents.filter (fun x => x.id != a.id && x.id != b.id)).flatMap agentPorts) ++ N.freePorts
    (p ∈ livePorts N ↔ p ∈ K ∨ p = ⟨a.id, 0⟩ ∨ p = ⟨b.id, 0⟩ ∨ p ∈ agentAuxPorts a ∨ p ∈ agentAuxPorts b) ∧
    (p ∈ K → p.nodeId ≠ a.id ∧ p.nodeId ≠ b.id) := by
  have ports (c : Agent) : p ∈ agentPorts c ↔ p = ⟨c.id, 0⟩ ∨ p ∈ agentAuxPorts c := by cases hk : c.kind <;> simp [agentPorts, agentAuxPorts, hk]
  have _ := hne; have uniq := @agent_eq_of_id_eq N.agents hWf.agents_nodup; have disj := hWf.free_disj; dsimp only
  simp only [livePorts, List.mem_append, List.mem_flatMap, List.mem_filter, Bool.and_eq_true, bne_iff_ne]; grind only [→ mem_agentPorts_nodeId]
theorem classifyPair_spec (a b : Agent) : match classifyPair a.id b.id a.kind b.kind with
    | .void => a.kind = .era ∧ b.kind = .era
    | .era bin => (bin = a.id ∧ a.kind.arity = 2 ∧ b.kind = .era) ∨ (bin = b.id ∧ b.kind.arity = 2 ∧ a.kind = .era)
    | .anni => a.kind = b.kind ∧ a.kind.arity = 2
    | .comm ka kb => ka = a.kind ∧ kb = b.kind ∧ ka.arity = 2 ∧ kb.arity = 2 ∧ ka.toINet.2 ≠ kb.toINet.2 := by
  cases hka : a.kind <;> cases hkb : b.kind <;> simp [classifyPair, CombKind.arity, CombKind.toINet]; rename_i l1 l2; by_cases hl : l1 = l2
  · subst hl; simp
  · simp [hl]
theorem agentAuxPorts_of_arity2 {a : Agent} (h : a.kind.arity = 2) : agentAuxPorts a = [⟨a.id, 1⟩, ⟨a.id, 2⟩] := by cases hk : a.kind <;> simp [CombKind.arity, agentAuxPorts, hk] at h ⊢
theorem agentPorts_of_arity2 {a : Agent} (h : a.kind.arity = 2) : agentPorts a = [⟨a.id, 0⟩, ⟨a.id, 1⟩, ⟨a.id, 2⟩] := by cases hk : a.kind <;> simp [CombKind.arity, agentPorts, hk] at h ⊢
theorem classifyRule_struct (a b : Agent) (base : Nat) (hne : a.id ≠ b.id) (ha : a.id < base) (hb : b.id < base) :
    let op := classifyRule a.id b.id a.kind b.kind base; (op.spawned.map (·.id)).Nodup ∧ (∀ x ∈ op.spawned, base ≤ x.id ∧ x.id < base + op.spawnCount) ∧
    match op with
    | .conj s sp rP tP =>
      (pairsDom rP).Nodup ∧ (pairsDom tP).Nodup ∧
      (∀ p, p ∈ sp.flatMap agentPorts ↔ p ∈ rP.map Prod.snd ++ pairsDom tP) ∧
      (∀ p, p ∈ rP.map Prod.fst ↔ p ∈ agentAuxPorts a ++ agentAuxPorts b) ∧
      (∀ p ∈ pairsDom tP, base ≤ p.nodeId ∧ p.nodeId < base + s ∧ p.slot ≠ 0) ∧
      (∀ p ∈ rP.map Prod.snd, base ≤ p.nodeId ∧ p.nodeId < base + s ∧ p.slot = 0) ∧
      (∀ p ∈ rP.map Prod.fst, p.nodeId = a.id ∨ p.nodeId = b.id)
    | .bridge bP =>
      (pairsDom bP).Nodup ∧ (∀ p, p ∈ pairsDom bP ↔ p ∈ agentAuxPorts a ++ agentAuxPorts b) ∧
      (∀ p ∈ pairsDom bP, p.nodeId = a.id ∨ p.nodeId = b.id) := by
  have hbases := And.intro ha hb; have hsp := classifyPair_spec a b; unfold classifyRule
  cases hpk : classifyPair a.id b.id a.kind b.kind <;> rw [hpk] at hsp <;> simp only [PairKind.toOp, RuleOp.spawned, RuleOp.spawnCount]
  · obtain ⟨hka, hkb⟩ := hsp; simp [pairsDom, agentAuxPorts, hka, hkb]
  · rcases hsp with ⟨rfl, har, hk⟩ | ⟨rfl, har, hk⟩ <;> rw [agentAuxPorts_of_arity2 har] <;> simp [pairsDom, agentPorts, agentAuxPorts, hk] <;> grind only
  · obtain ⟨hk, ha2⟩ := hsp; simp [pairsDom, agentAuxPorts_of_arity2 ha2, agentAuxPorts_of_arity2 (a := b) (hk ▸ ha2), hne]; grind only
  · obtain ⟨rfl, rfl, ha2, hb2, _⟩ := hsp; have ports (k : CombKind) (hk : k.arity = 2) (n : Nat) : agentPorts ⟨n,k⟩ = [⟨n,0⟩, ⟨n,1⟩, ⟨n,2⟩] := agentPorts_of_arity2 (a := ⟨n,k⟩) hk
    simp [pairsDom, commTauPairs, ports a.kind ha2, ports b.kind hb2, agentAuxPorts_of_arity2 ha2, agentAuxPorts_of_arity2 hb2]; grind -verbose (splits := 32) only
theorem conj_rho_live {M : ICNet} (hWfM : WfNet M) {c d : Agent} (hc : c ∈ M.agents) (hd : d ∈ M.agents) (hne : c.id ≠ d.id) {s : Nat} {sp : List Agent} {rP tP : List (PortRef × PortRef)}
    (hcr : classifyRule c.id d.id c.kind d.kind M.nextId = .conj s sp rP tP)
    {q : PortRef} (hq : q ∈ livePorts (firePairWith M c.id d.id c.kind d.kind M.nextId)) (hqnT : q ∉ pairsDom tP) : swapList rP q ∈ livePorts M := by
  have hst := (classifyRule_struct c d M.nextId hne (hWfM.agents_lt c hc) (hWfM.agents_lt d hd)).2.2
  rw [hcr] at hst; obtain ⟨hrnd, _, hsp_p, hfst_aux, _, hsnd_rg, hfst_cd⟩ := hst; unfold firePairWith at hq; rw [hcr] at hq
  simp only [livePorts, mkNetFrom, RuleOp.spawned, List.flatMap_append, List.mem_append, hsp_p] at hq
  have hK_case : ∀ hqK : q ∈ ((M.agents.filter (fun y => y.id != c.id && y.id != d.id)).flatMap agentPorts) ++ M.freePorts, swapList rP q ∈ livePorts M := fun hqK => by
    have hqL : q ∈ livePorts M := ((livePorts_split hWfM hc hd hne q).1).2 (.inl hqK); have ⟨hnc, hnd'⟩ := (livePorts_split hWfM hc hd hne q).2 hqK; have hlt := livePorts_lt_nextId hWfM hqL
    rw [swapList_outside (outside_rho hfst_cd hsnd_rg hlt hnc hnd')]; exact hqL
  rcases hq with (hK | (hS | hT)) | hF
  · exact hK_case (List.mem_append_left _ hK)
  · obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.1 hS; rw [(swapList_pair_eq hrnd huv).2]
    exact ((livePorts_split hWfM hc hd hne u).1).2 (.inr (.inr (.inr (List.mem_append.1 ((hfst_aux u).1 (List.mem_map.2 ⟨(u, v), huv, rfl⟩))))))
  · exact absurd hT hqnT
  · exact hK_case (List.mem_append_right _ hF)
theorem step_preserves_wfNet (N N' : ICNet) (hWf : WfNet N) (hStep : Step N N') : WfNet N' := by
  cases hStep with
  | @fire i j hAct hFire =>
    obtain ⟨a, b, ha, rfl, hb, rfl, hfeq⟩ := fireActivePair_of_active hWf hAct; rw [hfeq, Option.some.injEq] at hFire; subst hFire
    have hne := hAct.hne; have hfac1 := hAct.facing; have hfac2 := (hAct.symm hWf).facing; let keep := N.agents.filter (fun x => x.id != a.id && x.id != b.id); let K := (keep.flatMap agentPorts) ++ N.freePorts
    have hkeep_sub : ∀ x ∈ keep, x ∈ N.agents ∧ x.id ≠ a.id ∧ x.id ≠ b.id := fun x hx => by simp only [keep, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hx; exact ⟨hx.1, hx.2.1, hx.2.2⟩
    have hK_lt : ∀ p ∈ K, p.nodeId < N.nextId := fun p hp => livePorts_lt_nextId hWf (((livePorts_split hWf ha hb hne p).1).2 (.inl hp))
    have hσ_KA : ∀ p ∈ K ++ (agentAuxPorts a ++ agentAuxPorts b), N.partner p ∈ K ++ (agentAuxPorts a ++ agentAuxPorts b) ∧ N.partner p ≠ p ∧ N.partner (N.partner p) = p := by
      intro p hp; have hpL : p ∈ livePorts N := by rw [(livePorts_split hWf ha hb hne p).1]; simp only [List.mem_append] at hp; grind
      have hp_n0 : p ≠ ⟨a.id, 0⟩ ∧ p ≠ ⟨b.id, 0⟩ := by
        simp only [List.mem_append] at hp; rcases hp with h | h | h
        · have ⟨h1, h2⟩ := (livePorts_split hWf ha hb hne p).2 h; exact ⟨fun e => h1 (e ▸ rfl), fun e => h2 (e ▸ rfl)⟩
        · cases hk : a.kind <;> simp [agentAuxPorts, hk] at h <;> rcases h with rfl | rfl <;> simp [hne]
        · cases hk : b.kind <;> simp [agentAuxPorts, hk] at h <;> rcases h with rfl | rfl <;> simp [hne.symm]
      obtain ⟨hmem, hnep, hinv⟩ := hWf.partner_wf p hpL; have hq_n0a : N.partner p ≠ ⟨a.id, 0⟩ := fun e => hp_n0.2 (by have := congrArg N.partner e; rwa [hinv, hfac1] at this)
      have hq_n0b : N.partner p ≠ ⟨b.id, 0⟩ := fun e => hp_n0.1 (by have := congrArg N.partner e; rwa [hinv, hfac2] at this)
      rw [(livePorts_split hWf ha hb hne _).1] at hmem; refine ⟨?_, hnep, hinv⟩; simp only [List.mem_append]; grind
    obtain ⟨hndS, hrgS, hrest⟩ := classifyRule_struct a b N.nextId hne (hWf.agents_lt a ha) (hWf.agents_lt b hb); unfold firePairWith; refine wfNet_mkNetFrom ?_ ?_ hWf.free_nodup ?_ ?_ ?_
    · rw [List.map_append, List.nodup_append]; refine ⟨((List.filter_sublist.map Agent.id).nodup hWf.agents_nodup), hndS, fun id1 h1 id2 h2 heq => ?_⟩
      subst heq; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h1; obtain ⟨y, hy, he⟩ := List.mem_map.1 h2; have := hWf.agents_lt x (hkeep_sub x hx).1; have := (hrgS y hy).1; omega
    · intro x hx; rcases List.mem_append.1 hx with hx | hx
      · have := hWf.agents_lt x (hkeep_sub x hx).1; omega
      · exact (hrgS x hx).2
    · intro p hp; obtain ⟨hs, hl⟩ := hWf.free_spec p hp; exact ⟨hs, by omega⟩
    · intro p hp x hx; rcases List.mem_append.1 hx with hx | hx
      · exact hWf.free_disj p hp x (hkeep_sub x hx).1
      · have := (hWf.free_spec p hp).2; have := (hrgS x hx).1; omega
    · cases hop : classifyRule a.id b.id a.kind b.kind N.nextId with
      | conj s sp rP tP =>
        rw [hop] at hrest; obtain ⟨hrnd, htnd, hsp_p, hfst_aux, ht_rg, hsnd_rg, hfst_ab⟩ := hrest; simp only [RuleOp.spawned, RuleOp.apply]
        have hlp_iff : ∀ p, p ∈ ((keep ++ sp).flatMap agentPorts) ++ N.freePorts ↔ p ∈ K ++ rP.map Prod.snd ++ pairsDom tP := fun p => by simp only [K, List.flatMap_append, List.mem_append, hsp_p]; grind
        have hK_out (q : PortRef) (hq : q ∈ K) : swapList rP q = q := by obtain ⟨ha', hb'⟩ := (livePorts_split hWf ha hb hne q).2 hq; exact swapList_outside (outside_rho hfst_ab hsnd_rg (hK_lt q hq) ha' hb')
        have hρ_map (p : PortRef) : p ∈ K ++ rP.map Prod.snd ↔ swapList rP p ∈ K ++ (agentAuxPorts a ++ agentAuxPorts b) := by
          have inv := (swapList_wf hrnd).1; have fixed (q : PortRef) : swapList rP q ∈ K ↔ q ∈ K := ⟨fun h => by rwa [← inv q, hK_out _ h], fun h => by rwa [hK_out q h]⟩
          rw [List.mem_append (a := p), List.mem_append (a := swapList rP p), fixed, ← hfst_aux]; have ends := @swapList_pair_eq rP hrnd; simp only [List.mem_map]; grind -verbose only
        have hw := applyConj_wf hσ_KA (swapList_wf hrnd).1 hρ_map (fun p hp => ⟨((swapList_wf htnd).2 p hp).1, ((swapList_wf htnd).2 p hp).2, (swapList_wf htnd).1 p⟩) (fun p hp hkf => by
            obtain ⟨hge, _, hsn0⟩ := ht_rg p hp; exact (List.mem_append.1 hkf).elim (fun hK => by have := hK_lt p hK; omega) (fun hS => hsn0 (hsnd_rg p hS).2.2))
        intro p hp; obtain ⟨h1, h2, h3⟩ := hw p ((hlp_iff p).1 hp); exact ⟨(hlp_iff _).2 h1, h2, h3⟩
      | bridge bP =>
        rw [hop] at hrest; obtain ⟨hbnd, hbaux, hbab⟩ := hrest; simp only [RuleOp.spawned, RuleOp.apply, List.append_nil]
        have hσ_Kb : ∀ p ∈ K ++ pairsDom bP, N.partner p ∈ K ++ pairsDom bP ∧ N.partner p ≠ p ∧ N.partner (N.partner p) = p := fun p hp => by
          obtain ⟨h1, h2, h3⟩ := hσ_KA p (List.mem_append.2 ((List.mem_append.1 hp).imp_right (hbaux p).1)); exact ⟨List.mem_append.2 ((List.mem_append.1 h1).imp_right (hbaux _).2), h2, h3⟩
        intro p hp; have hp_nb : p ∉ pairsDom bP := fun hm => by have ⟨hna, hnb⟩ := (livePorts_split hWf ha hb hne p).2 hp; have := hbab p hm; omega
        obtain ⟨h1, h2, h3, h4⟩ := contractBridge_wf hσ_Kb (fun x hx => ⟨((swapList_wf hbnd).2 x hx).1, ((swapList_wf hbnd).2 x hx).2, (swapList_wf hbnd).1 x⟩)
          (fun _ hx => List.mem_append_right _ hx) (List.mem_append_left _ hp) hp_nb
        exact ⟨(List.mem_append.1 h1).resolve_right h2, h3, h4⟩
theorem steps_preserves_wfNet (N N' : ICNet) (hWf : WfNet N) (hSteps : Steps N N') : WfNet N' := by induction hSteps with | refl => exact hWf | next s _ ih => exact ih (step_preserves_wfNet _ _ hWf s)

/-! ## 5. `ReductionMachine.Arena` Simulation (`icNet_simulates_arenaStep`) -/
@[expose] def ICNet.toArena (N : ICNet) : Arena where
  node := fun id => (findAgent N id).map fun a => (a.kind.toINet.1, a.kind.toINet.2, 0)
  link := N.partner
  next := N.nextId
structure ArenaMatchesNet (A : Arena) (N : ICNet) : Prop where
  node_eq   : ∀ id, A.node id = N.toArena.node id
  link_live : ∀ p ∈ livePorts N, A.link p = N.partner p
  next_eq   : A.next = N.nextId
theorem arenaMatchesNet_toArena (N : ICNet) : ArenaMatchesNet N.toArena N := ⟨fun _ => rfl, fun _ _ => rfl, rfl⟩
def LoopFreePair (N : ICNet) (i j : Nat) : Prop := ∀ a ∈ N.agents, (a.id = i ∨ a.id = j) → ∀ p ∈ agentAuxPorts a, (N.partner p).nodeId ≠ i ∧ (N.partner p).nodeId ≠ j
theorem reduceActivePair_of_classifyPair (a b : Agent) (l r : INetNode) (nx : Nat) (hne : a.id ≠ b.id)
    (hl : l.kind = a.kind.toINet.1 ∧ l.label = a.kind.toINet.2) (hr : r.kind = b.kind.toINet.1 ∧ r.label = b.kind.toINet.2) :
    match classifyPair a.id b.id a.kind b.kind with
    | .void => reduceActivePair ⟨l, r⟩ nx = .erase []
    | .era bin => reduceActivePair ⟨l, r⟩ nx = .erase (if bin = a.id then [l.aux1, l.aux2] else [r.aux1, r.aux2])
    | .anni => reduceActivePair ⟨l, r⟩ nx = .annihilate (l.aux1, r.aux1) (l.aux2, r.aux2)
    | .comm _ _ => reduceActivePair ⟨l, r⟩ nx = .commute (commuteSpawnedNodes l r nx) (commuteSplices l r nx) := by
  cases l; cases r; simp only at hl hr; obtain ⟨rfl, rfl⟩ := hl; obtain ⟨rfl, rfl⟩ := hr
  cases hka : a.kind <;> cases hkb : b.kind <;> simp [classifyPair, reduceActivePair, CombKind.toINet, Ne.symm hne]
  rename_i l1 l2; by_cases hl : l1 = l2
  · subst hl; simp
  · simp [hl]
private theorem port_before {x : PortRef} {n slot : Nat} (h : x.nodeId < n) : x ≠ ⟨n, slot⟩ := by rintro rfl; exact Nat.lt_irrefl _ h
private theorem port_after {x : PortRef} {n slot : Nat} (h : x.nodeId < n) : (⟨n, slot⟩ : PortRef) ≠ x := (port_before h).symm
/-- On a retained wire, conjugation redirects exactly the partners of replaced auxiliaries. -/
private def redirect (σ : PortRef → PortRef) (p : PortRef) : List (PortRef × PortRef) → PortRef
  | [] => σ p
  | (u, v) :: ps => if p = σ u then v else redirect σ p ps
private theorem retained_lookup {σ : PortRef → PortRef} {p : PortRef} (ps : List (PortRef × PortRef))
    (inv : σ (σ p) = p) (ends : ∀ uv ∈ ps, σ (σ uv.1) = uv.1 ∧ σ p ≠ uv.2) : swapList ps (σ p) = redirect σ p ps := by
  induction ps with
  | nil => rfl
  | cons uv ps ih =>
    obtain ⟨u,v⟩ := uv; obtain ⟨hu,hv⟩ := ends (u,v) List.mem_cons_self; have eq : σ p = u ↔ p = σ u := ⟨fun h => inv ▸ congrArg σ h, fun h => h ▸ hu⟩
    simp only [swapList, redirect, eq, hv, ite_false, ih (fun a ha => ends a (List.mem_cons_of_mem _ ha))]
/-- Normalize an arena read through the concrete sequence of node placements and wire writes. -/
local macro "arena_reads" : tactic => `(tactic| simp only [Arena.erasers, Arena.splice, Arena.connect_link, Arena.place_link, Arena.drop_link, Arena.connect_next,
    Arena.drop_next, Arena.place_next, commuteSpawnedNodes, commuteSplices, mkEraNode, List.foldl_cons, List.foldl_nil])
private theorem arena_find_keep {N : ICNet} {A : Arena} {a b : Agent} (hMatch : ArenaMatchesNet A N)
    (sp : List Agent) (σ' : PortRef → PortRef) (nx id : Nat)
    (hWfM : WfNet (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++ sp) N.freePorts σ' nx)) :
    (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++ sp) N.freePorts σ' nx).toArena.node id =
      match sp.find? (·.id == id) with
      | some x => some (x.kind.toINet.1, x.kind.toINet.2, 0)
      | none => if id = b.id then none else if id = a.id then none else A.node id := by
  simp only [ICNet.toArena]
  cases hfs : sp.find? (·.id == id) with
  | some x =>
    rw [← beq_iff_eq.1 (List.find?_some (p := fun y : Agent => y.id == id) hfs),
      findAgent_of_mem hWfM (List.mem_append_right _ (List.mem_of_find?_eq_some hfs))]
    rfl
  | none =>
    have filtered : (N.agents.filter (fun x => x.id != a.id && x.id != b.id)).find? (·.id == id) =
        if id = b.id ∨ id = a.id then none else findAgent N id := by
      rw [List.find?_filter]; split
      · rw [List.find?_eq_none]; intro x _; simp; grind only
      · unfold findAgent; congr 1; funext x; by_cases h : x.id = id <;> simp [h] <;> grind only
    rw [hMatch.node_eq]
    simp only [ICNet.toArena, findAgent, mkNetFrom, List.find?_append, filtered, hfs]
    split <;> split <;> simp_all [findAgent]

private theorem arena_active_aux_props {N : ICNet} {A : Arena} {i j : Nat}
    (hWf : WfNet N) (hMatch : ArenaMatchesNet A N) (hLoopFree : LoopFreePair N i j)
    (c : Agent) (hc : c ∈ N.agents) (hcid : c.id = i ∨ c.id = j) (har : c.kind.arity = 2) :
    A.link ⟨c.id, 1⟩ = N.partner ⟨c.id, 1⟩ ∧ A.link ⟨c.id, 2⟩ = N.partner ⟨c.id, 2⟩ ∧
    (N.partner ⟨c.id, 1⟩).nodeId < N.nextId ∧ (N.partner ⟨c.id, 2⟩).nodeId < N.nextId ∧
    (N.partner ⟨c.id, 1⟩).nodeId ≠ i ∧ (N.partner ⟨c.id, 1⟩).nodeId ≠ j ∧
    (N.partner ⟨c.id, 2⟩).nodeId ≠ i ∧ (N.partner ⟨c.id, 2⟩).nodeId ≠ j ∧
    N.partner ⟨c.id, 1⟩ ≠ N.partner ⟨c.id, 2⟩ ∧
    N.partner (N.partner ⟨c.id, 1⟩) = ⟨c.id, 1⟩ ∧ N.partner (N.partner ⟨c.id, 2⟩) = ⟨c.id, 2⟩ := by
  have hm1 : ⟨c.id, 1⟩ ∈ livePorts N :=
    List.mem_append_left _ (List.mem_flatMap.2 ⟨c, hc, by rw [agentPorts_of_arity2 har]; simp⟩)
  have hm2 : ⟨c.id, 2⟩ ∈ livePorts N :=
    List.mem_append_left _ (List.mem_flatMap.2 ⟨c, hc, by rw [agentPorts_of_arity2 har]; simp⟩)
  have hi1 := (hWf.partner_wf _ hm1).2.2
  have hi2 := (hWf.partner_wf _ hm2).2.2
  have hlf1 := hLoopFree c hc hcid ⟨c.id, 1⟩ (by rw [agentAuxPorts_of_arity2 har]; simp)
  have hlf2 := hLoopFree c hc hcid ⟨c.id, 2⟩ (by rw [agentAuxPorts_of_arity2 har]; simp)
  exact ⟨hMatch.link_live _ hm1, hMatch.link_live _ hm2,
    livePorts_lt_nextId hWf (hWf.partner_wf _ hm1).1, livePorts_lt_nextId hWf (hWf.partner_wf _ hm2).1,
    hlf1.1, hlf1.2, hlf2.1, hlf2.2,
    (fun e => by have := congrArg N.partner e; rw [hi1, hi2] at this; cases this), hi1, hi2⟩

private theorem contractBridge_anni_eq {N : ICNet} {i j : Nat} (hne : i ≠ j)
    (hq1a : (N.partner ⟨i, 1⟩).nodeId ≠ i) (hq1b : (N.partner ⟨i, 1⟩).nodeId ≠ j)
    (hq2a : (N.partner ⟨i, 2⟩).nodeId ≠ i) (hq2b : (N.partner ⟨i, 2⟩).nodeId ≠ j)
    (hq3a : (N.partner ⟨j, 1⟩).nodeId ≠ i) (hq3b : (N.partner ⟨j, 1⟩).nodeId ≠ j)
    (hq4a : (N.partner ⟨j, 2⟩).nodeId ≠ i) (hq4b : (N.partner ⟨j, 2⟩).nodeId ≠ j) (q : PortRef) :
    contractBridge N.partner (swapList [(⟨i, 1⟩, ⟨j, 1⟩), (⟨i, 2⟩, ⟨j, 2⟩)])
      (pairsDom [(⟨i, 1⟩, ⟨j, 1⟩), (⟨i, 2⟩, ⟨j, 2⟩)]) q =
      if N.partner q = ⟨i, 1⟩ then N.partner ⟨j, 1⟩
      else if N.partner q = ⟨j, 1⟩ then N.partner ⟨i, 1⟩
      else if N.partner q = ⟨i, 2⟩ then N.partner ⟨j, 2⟩
      else if N.partner q = ⟨j, 2⟩ then N.partner ⟨i, 2⟩ else N.partner q := by
  unfold contractBridge
  change walkAux _ _ _ 4 (N.partner q) = _
  have off {u : PortRef} {m k : Nat} (h : u.nodeId ≠ m) : u ≠ ⟨m, k⟩ := fun eq => h (eq ▸ rfl)
  by_cases h : N.partner q ∈ pairsDom [(⟨i, 1⟩, ⟨j, 1⟩), (⟨i, 2⟩, ⟨j, 2⟩)]
  · simp [pairsDom] at h
    rcases h with h | h | h | h <;>
      simp (disch := assumption) [h, walkAux, swapList, pairsDom, off, hne.symm]
  · simp [pairsDom] at h; simp [walkAux, pairsDom, h]

private theorem icNet_simulates_era {N : ICNet} {A : Arena} {a b c : Agent}
    (hWf : WfNet N) (hMatch : ArenaMatchesNet A N) (hLoopFree : LoopFreePair N a.id b.id)
    (ha : a ∈ N.agents) (hb : b ∈ N.agents) (hne : a.id ≠ b.id)
    (hc : c ∈ N.agents) (hcid : c.id = a.id ∨ c.id = b.id) (har : c.kind.arity = 2)
    (hinet_a : A.inet? a.id = some ⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩)
    (hinet_b : A.inet? b.id = some ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩)
    (hAl1 : A.link ⟨a.id, 0⟩ = ⟨b.id, 0⟩) (hAl2 : A.link ⟨b.id, 0⟩ = ⟨a.id, 0⟩)
    (hred' : reduceActivePair ⟨⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩,
        ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩⟩ A.next =
      .erase [A.link ⟨c.id, 1⟩, A.link ⟨c.id, 2⟩])
    (hWf' : WfNet (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++
        [⟨N.nextId, .era⟩, ⟨N.nextId + 1, .era⟩]) N.freePorts
      (applyConj (swapList [(⟨c.id, 1⟩, ⟨N.nextId, 0⟩), (⟨c.id, 2⟩, ⟨N.nextId + 1, 0⟩)])
        (swapList []) (pairsDom []) N.partner) (N.nextId + 2))) :
    ∃ A', Arena.Step A A' ∧ ArenaMatchesNet A'
      (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++
          [⟨N.nextId, .era⟩, ⟨N.nextId + 1, .era⟩]) N.freePorts
        (applyConj (swapList [(⟨c.id, 1⟩, ⟨N.nextId, 0⟩), (⟨c.id, 2⟩, ⟨N.nextId + 1, 0⟩)])
          (swapList []) (pairsDom []) N.partner) (N.nextId + 2)) := by
  let B := (A.drop a.id).drop b.id
  have hBn : B.next = N.nextId := by simp [B, hMatch.next_eq]
  have hBl : B.link = A.link := by simp [B]
  obtain ⟨hl1, hl2, hq1lt, hq2lt, hq1a, hq1b, hq2a, hq2b, hq12, hq1inv, hq2inv⟩ :=
    arena_active_aux_props hWf hMatch hLoopFree c hc hcid har
  have hltc := hWf.agents_lt c hc
  have hq1c : (N.partner ⟨c.id, 1⟩).nodeId ≠ c.id := hcid.elim (· ▸ hq1a) (· ▸ hq1b)
  have hq2c : (N.partner ⟨c.id, 2⟩).nodeId ≠ c.id := hcid.elim (· ▸ hq2a) (· ▸ hq2b)
  refine ⟨B.erasers [N.partner ⟨c.id, 1⟩, N.partner ⟨c.id, 2⟩],
    .fire hne hinet_a hinet_b hAl1 hAl2 (by rw [hred', hl1, hl2]; simp [Arena.apply, B]),
    fun id => ?_, fun p hp => ?_, by simp [mkNetFrom, Arena.erasers, hBn]⟩
  · rw [arena_find_keep hMatch _ _ _ id hWf']
    simp only [Arena.erasers, Arena.connect_node, Arena.connect_next, Arena.place_node, B,
      Arena.drop_node, Arena.drop_next, hMatch.next_eq, mkEraNode, List.find?_cons, List.find?_nil, CombKind.toINet]
    grind -verbose only
  · rw [partner_mkNetFrom, ite_t hp]
    let keep := N.agents.filter (fun x => x.id != a.id && x.id != b.id)
    have hsp : p ∈ (keep.flatMap agentPorts) ++ N.freePorts ∨ p = ⟨N.nextId, 0⟩ ∨ p = ⟨N.nextId + 1, 0⟩ := by
      simp only [keep, livePorts, mkNetFrom, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        agentPorts, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      grind
    arena_reads
    simp only [hBn, hBl, applyConj, pairsDom, List.flatMap_nil, List.not_mem_nil, ite_false]
    rcases hsp with hpK | rfl | rfl
    · have hpL := ((livePorts_split hWf ha hb hne p).1).2 (.inl hpK)
      have hplt := livePorts_lt_nextId hWf hpL
      have hne_ab := (livePorts_split hWf ha hb hne p).2 hpK
      have hinv := (hWf.partner_wf p hpL).2.2
      have hnplt := livePorts_lt_nextId hWf (hWf.partner_wf p hpL).1
      have hpnc : p.nodeId ≠ c.id := hcid.elim (· ▸ hne_ab.1) (· ▸ hne_ab.2)
      rw [hMatch.link_live p hpL, swapList_outside (x := p) (by simp [pairsDom]; grind only),
        retained_lookup _ hinv (by intro uv hu; simp at hu; rcases hu with rfl | rfl <;> grind only)]
      simp only [redirect]; grind only
    all_goals simp (disch := omega) [swapList, port_after, port_before] <;> grind -verbose only

private theorem icNet_simulates_anni {N : ICNet} {A : Arena} {a b : Agent}
    (hWf : WfNet N) (hMatch : ArenaMatchesNet A N) (hLoopFree : LoopFreePair N a.id b.id)
    (ha : a ∈ N.agents) (hb : b ∈ N.agents) (hne : a.id ≠ b.id) (hk : a.kind = b.kind) (ha2 : a.kind.arity = 2)
    (hinet_a : A.inet? a.id = some ⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩)
    (hinet_b : A.inet? b.id = some ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩)
    (hAl1 : A.link ⟨a.id, 0⟩ = ⟨b.id, 0⟩) (hAl2 : A.link ⟨b.id, 0⟩ = ⟨a.id, 0⟩)
    (hred : reduceActivePair ⟨⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩,
        ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩⟩ A.next =
      .annihilate (A.link ⟨a.id, 1⟩, A.link ⟨b.id, 1⟩) (A.link ⟨a.id, 2⟩, A.link ⟨b.id, 2⟩))
    (hWf' : WfNet (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++ []) N.freePorts
      (contractBridge N.partner (swapList [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)])
        (pairsDom [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)])) (N.nextId + 0))) :
    ∃ A', Arena.Step A A' ∧ ArenaMatchesNet A'
      (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++ []) N.freePorts
        (contractBridge N.partner (swapList [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)])
          (pairsDom [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)])) (N.nextId + 0)) := by
  let B := (A.drop a.id).drop b.id
  obtain ⟨hl1, hl2, _, _, hq1a, hq1b, hq2a, hq2b, _, hq1inv, hq2inv⟩ :=
    arena_active_aux_props hWf hMatch hLoopFree a ha (.inl rfl) ha2
  obtain ⟨hr1, hr2, _, _, hq3a, hq3b, hq4a, hq4b, _, hq3inv, hq4inv⟩ :=
    arena_active_aux_props hWf hMatch hLoopFree b hb (.inr rfl) (hk ▸ ha2)
  let A' := (B.connect (N.partner ⟨a.id, 1⟩) (N.partner ⟨b.id, 1⟩)).connect (N.partner ⟨a.id, 2⟩) (N.partner ⟨b.id, 2⟩)
  refine ⟨A', .fire hne hinet_a hinet_b hAl1 hAl2 (by rw [hred]; simp [hl1, hl2, hr1, hr2, Arena.apply, A', B]),
    fun id => by simpa [A', B, Arena.connect_node, Arena.drop_node] using (arena_find_keep hMatch [] _ N.nextId id (by simpa using hWf')).symm,
    fun p hp => ?_, by simp [A', B, mkNetFrom, hMatch.next_eq]⟩
  rw [partner_mkNetFrom, ite_t hp]
  have hpL := ((livePorts_split hWf ha hb hne p).1).2 (.inl (by simpa [livePorts, mkNetFrom] using hp))
  have hinv := (hWf.partner_wf p hpL).2.2
  have hAl := hMatch.link_live p hpL
  rw [contractBridge_anni_eq hne hq1a hq1b hq2a hq2b hq3a hq3b hq4a hq4b p]
  simp only [A', B, Arena.connect_link, Arena.drop_link]
  grind -verbose (splits := 20) only

private theorem icNet_simulates_comm_link {N : ICNet} {A : Arena} {a b : Agent}
    (hWf : WfNet N) (hMatch : ArenaMatchesNet A N) (hLoopFree : LoopFreePair N a.id b.id)
    (ha : a ∈ N.agents) (hb : b ∈ N.agents) (hne : a.id ≠ b.id) (ha2 : a.kind.arity = 2) (hb2 : b.kind.arity = 2)
    (p : PortRef)
    (hp : p ∈ livePorts (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++
        [⟨N.nextId, b.kind⟩, ⟨N.nextId + 1, b.kind⟩, ⟨N.nextId + 2, a.kind⟩, ⟨N.nextId + 3, a.kind⟩]) N.freePorts
      (applyConj (swapList [(⟨a.id, 1⟩, ⟨N.nextId, 0⟩), (⟨a.id, 2⟩, ⟨N.nextId + 1, 0⟩),
        (⟨b.id, 1⟩, ⟨N.nextId + 2, 0⟩), (⟨b.id, 2⟩, ⟨N.nextId + 3, 0⟩)])
        (swapList (commTauPairs N.nextId)) (pairsDom (commTauPairs N.nextId)) N.partner) (N.nextId + 4))) :
    let l : INetNode := ⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩
    let r : INetNode := ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩
    let B := (A.drop a.id).drop b.id
    let sp := commuteSpawnedNodes l r A.next
    let A' := ({ sp.foldl Arena.place B with next := A.next + sp.length }).splice (commuteSplices l r A.next)
    A'.link p = (mkNetFrom (N.agents.filter (fun x => x.id != a.id && x.id != b.id) ++
        [⟨N.nextId, b.kind⟩, ⟨N.nextId + 1, b.kind⟩, ⟨N.nextId + 2, a.kind⟩, ⟨N.nextId + 3, a.kind⟩]) N.freePorts
      (applyConj (swapList [(⟨a.id, 1⟩, ⟨N.nextId, 0⟩), (⟨a.id, 2⟩, ⟨N.nextId + 1, 0⟩),
        (⟨b.id, 1⟩, ⟨N.nextId + 2, 0⟩), (⟨b.id, 2⟩, ⟨N.nextId + 3, 0⟩)])
        (swapList (commTauPairs N.nextId)) (pairsDom (commTauPairs N.nextId)) N.partner) (N.nextId + 4)).partner p := by
  intro l r B sp A'
  have hltA := hWf.agents_lt a ha
  have hltB := hWf.agents_lt b hb
  have hBl : B.link = A.link := by simp [B]
  obtain ⟨hl1, hl2, hq1lt, hq2lt, hq1a, hq1b, hq2a, hq2b, hq12, hq1inv, hq2inv⟩ :=
    arena_active_aux_props hWf hMatch hLoopFree a ha (.inl rfl) ha2
  obtain ⟨hr1, hr2, hq3lt, hq4lt, hq3a, hq3b, hq4a, hq4b, hq34, hq3inv, hq4inv⟩ :=
    arena_active_aux_props hWf hMatch hLoopFree b hb (.inr rfl) hb2
  rw [partner_mkNetFrom, ite_t hp]
  have hpA : ∀ id, agentPorts ⟨id, a.kind⟩ = [⟨id, 0⟩, ⟨id, 1⟩, ⟨id, 2⟩] :=
    fun id => agentPorts_of_arity2 (a := ⟨id, a.kind⟩) ha2
  have hpB : ∀ id, agentPorts ⟨id, b.kind⟩ = [⟨id, 0⟩, ⟨id, 1⟩, ⟨id, 2⟩] :=
    fun id => agentPorts_of_arity2 (a := ⟨id, b.kind⟩) hb2
  let keep := N.agents.filter (fun x => x.id != a.id && x.id != b.id)
  have hsp : p ∈ (keep.flatMap agentPorts) ++ N.freePorts ∨
      p ∈ [⟨N.nextId, 0⟩, ⟨N.nextId + 1, 0⟩, ⟨N.nextId + 2, 0⟩, ⟨N.nextId + 3, 0⟩] ∨
      p ∈ pairsDom (commTauPairs N.nextId) := by
    simp only [keep, livePorts, mkNetFrom, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      hpA, hpB, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, pairsDom, commTauPairs] at hp ⊢
    grind
  dsimp only [A', sp]; arena_reads
  simp only [l, r, hl1, hl2, hr1, hr2, hMatch.next_eq, hBl, applyConj]
  rcases hsp with hpK | hpF | hpT
  · have hpL := ((livePorts_split hWf ha hb hne p).1).2 (.inl hpK)
    have hplt := livePorts_lt_nextId hWf hpL
    have _ := (livePorts_split hWf ha hb hne p).2 hpK
    have hinv := (hWf.partner_wf p hpL).2.2
    have hnplt := livePorts_lt_nextId hWf (hWf.partner_wf p hpL).1
    have outside : p ∉ pairsDom (commTauPairs N.nextId) := by simp [pairsDom, commTauPairs]; grind only
    simp only [ite_f outside, hMatch.link_live p hpL]
    rw [swapList_outside (x := p) (by simp [pairsDom]; grind -verbose only),
      retained_lookup _ hinv (by intro uv hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> grind only)]
    simp (disch := omega) only [redirect, port_before, ite_false]; grind -verbose only
  · simp at hpF
    rcases hpF with rfl | rfl | rfl | rfl <;>
      simp (disch := omega) [pairsDom, commTauPairs, swapList, port_before] <;> grind -verbose only
  · simp [pairsDom, commTauPairs] at hpT
    rcases hpT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) [swapList, pairsDom, commTauPairs, port_after]

theorem icNet_simulates_arenaStep (N N' : ICNet) (A : Arena) (i j : Nat) (hWf : WfNet N) (hMatch : ArenaMatchesNet A N) (hAct : IsActivePair N i j)
    (hFire : fireActivePair N i j = some N') (hLoopFree : LoopFreePair N i j) : ∃ A', Arena.Step A A' ∧ ArenaMatchesNet A' N' := by
  obtain ⟨a, b, ha, rfl, hb, rfl, hfeq⟩ := fireActivePair_of_active hWf hAct
  rw [hfeq, Option.some.injEq] at hFire; subst hFire
  have hne := hAct.hne
  let l : INetNode := ⟨a.id, a.kind.toINet.1, a.kind.toINet.2, 0, A.link ⟨a.id, 1⟩, A.link ⟨a.id, 2⟩⟩
  let r : INetNode := ⟨b.id, b.kind.toINet.1, b.kind.toINet.2, 0, A.link ⟨b.id, 1⟩, A.link ⟨b.id, 2⟩⟩
  have hinet_a : A.inet? a.id = some l := by simp [Arena.inet?, hMatch.node_eq, ICNet.toArena, findAgent_of_mem hWf ha, l]
  have hinet_b : A.inet? b.id = some r := by simp [Arena.inet?, hMatch.node_eq, ICNet.toArena, findAgent_of_mem hWf hb, r]
  have hAl1 : A.link ⟨a.id, 0⟩ = ⟨b.id, 0⟩ := by rw [hMatch.link_live _ (principal_live ha), hAct.facing]
  have hAl2 : A.link ⟨b.id, 0⟩ = ⟨a.id, 0⟩ := by rw [hMatch.link_live _ (principal_live hb), (hAct.symm hWf).facing]
  have hWf' := step_preserves_wfNet N _ hWf (.fire hAct hfeq)
  have hred := reduceActivePair_of_classifyPair a b l r A.next hne ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hspec := classifyPair_spec a b
  unfold firePairWith classifyRule at hWf' ⊢
  let B := (A.drop a.id).drop b.id
  cases hpk : classifyPair a.id b.id a.kind b.kind <;> rw [hpk] at hred hspec hWf' <;>
    simp only [PairKind.toOp, RuleOp.spawned, RuleOp.spawnCount, RuleOp.apply] at hWf' ⊢
  · refine ⟨B, .fire hne hinet_a hinet_b hAl1 hAl2 (by rw [hred]; simp [Arena.apply, Arena.erasers, l, r, B]),
      fun id => by simpa [B, Arena.drop_node] using (arena_find_keep hMatch [] _ N.nextId id (by simpa using hWf')).symm,
      fun p hp => by
        rw [partner_mkNetFrom, ite_t hp]
        simp [B, applyConj, pairsDom, swapList,
          hMatch.link_live p (((livePorts_split hWf ha hb hne p).1).2 (.inl (by simpa [livePorts, mkNetFrom] using hp)))],
      by simp [mkNetFrom, B, hMatch.next_eq]⟩
  · rename_i bin
    rcases hspec with ⟨rfl, ha2, _⟩ | ⟨rfl, hb2, _⟩
    · exact icNet_simulates_era hWf hMatch hLoopFree ha hb hne ha (.inl rfl) ha2 hinet_a hinet_b hAl1 hAl2 (by simpa [l] using hred) hWf'
    · exact icNet_simulates_era hWf hMatch hLoopFree ha hb hne hb (.inr rfl) hb2 hinet_a hinet_b hAl1 hAl2 (by simpa [hne.symm, r] using hred) hWf'
  · obtain ⟨hk, ha2⟩ := hspec
    exact icNet_simulates_anni hWf hMatch hLoopFree ha hb hne hk ha2 hinet_a hinet_b hAl1 hAl2 hred hWf'
  · rename_i ka kb
    obtain ⟨rfl, rfl, ha2, hb2, _⟩ := hspec
    let sp := commuteSpawnedNodes l r A.next
    let A' := ({ sp.foldl Arena.place B with next := A.next + sp.length }).splice (commuteSplices l r A.next)
    refine ⟨A', .fire hne hinet_a hinet_b hAl1 hAl2 (by rw [hred]; simp [Arena.apply, l, r, A', sp, B]),
      fun id => ?_,
      fun p hp => icNet_simulates_comm_link hWf hMatch hLoopFree ha hb hne ha2 hb2 p hp,
      by simp [A', sp, commuteSpawnedNodes, commuteSplices, Arena.splice, mkNetFrom, hMatch.next_eq]⟩
    rw [arena_find_keep hMatch _ _ _ id hWf']
    simp only [A', sp, commuteSplices, Arena.splice, Arena.connect_node, commuteSpawnedNodes,
      List.foldl_cons, List.foldl_nil, Arena.place_node, B, Arena.drop_node, hMatch.next_eq,
      List.find?_cons, List.find?_nil, l, r]
    grind -verbose only
theorem icNet_toArena_simulates_arenaStep (N N' : ICNet) (i j : Nat) (hWf : WfNet N) (hAct : IsActivePair N i j) (hFire : fireActivePair N i j = some N') (hLoopFree : LoopFreePair N i j) :
    ∃ A', Arena.Step N.toArena A' ∧ ArenaMatchesNet A' N' :=
  icNet_simulates_arenaStep N N' N.toArena i j hWf (arenaMatchesNet_toArena N) hAct hFire hLoopFree

/-! ## 6. α-Equivalence (`AlphaEquiv`), Canonicalization & Simulation -/
def mapPort (φ : Nat → Nat) (p : PortRef) : PortRef := ⟨φ p.nodeId, p.slot⟩
structure AlphaIso (N₁ N₂ : ICNet) where
  free_eq     : N₁.freePorts = N₂.freePorts
  φ           : Nat → Nat
  ψ           : Nat → Nat
  free_fix_φ  : ∀ p ∈ N₁.freePorts, φ p.nodeId = p.nodeId
  free_fix_ψ  : ∀ p ∈ N₂.freePorts, ψ p.nodeId = p.nodeId
  left_inv    : ∀ a ∈ N₁.agents, ψ (φ a.id) = a.id
  right_inv   : ∀ b ∈ N₂.agents, φ (ψ b.id) = b.id
  map_agent   : ∀ a ∈ N₁.agents, ⟨φ a.id, a.kind⟩ ∈ N₂.agents
  inv_agent   : ∀ b ∈ N₂.agents, ⟨ψ b.id, b.kind⟩ ∈ N₁.agents
  partner_eq  : ∀ p ∈ livePorts N₁, mapPort φ (N₁.partner p) = N₂.partner (mapPort φ p)
  partner_inv : ∀ q ∈ livePorts N₂, mapPort ψ (N₂.partner q) = N₁.partner (mapPort ψ q)
def AlphaEquiv (N₁ N₂ : ICNet) : Prop := Nonempty (AlphaIso N₁ N₂)
theorem mapPort_mem_of_parts {N₁ N₂ : ICNet} {φ : Nat → Nat} (hfe : N₁.freePorts = N₂.freePorts) (hff : ∀ p ∈ N₁.freePorts, φ p.nodeId = p.nodeId)
    (hma : ∀ a ∈ N₁.agents, ⟨φ a.id, a.kind⟩ ∈ N₂.agents) {p : PortRef} (hp : p ∈ livePorts N₁) : mapPort φ p ∈ livePorts N₂ := by
  simp only [livePorts, List.mem_append, List.mem_flatMap] at hp ⊢; rcases hp with ⟨a, ha, hpa⟩ | hpf
  · refine .inl ⟨⟨φ a.id, a.kind⟩, hma a ha, ?_⟩
    cases hk : a.kind <;> simp [agentPorts, hk] at hpa ⊢ <;> rcases hpa with rfl | rfl | rfl <;> simp [mapPort]
  · right; have : mapPort φ p = p := by cases p; simp [mapPort, hff _ hpf]
    rw [this, ← hfe]; exact hpf
theorem mapPort_left_inv_of_parts {N₁ N₂ : ICNet} {φ ψ : Nat → Nat} (hfe : N₁.freePorts = N₂.freePorts) (hff : ∀ p ∈ N₁.freePorts, φ p.nodeId = p.nodeId)
    (hfψ : ∀ p ∈ N₂.freePorts, ψ p.nodeId = p.nodeId) (hl : ∀ a ∈ N₁.agents, ψ (φ a.id) = a.id)
    {p : PortRef} (hp : p ∈ livePorts N₁) : mapPort ψ (mapPort φ p) = p := by
  simp only [livePorts, List.mem_append, List.mem_flatMap] at hp; rcases hp with ⟨a, ha, hpa⟩ | hpf
  · have hid := mem_agentPorts_nodeId hpa; cases p; dsimp at hid; subst hid; simp [mapPort, hl a ha]
  · cases p; simp [mapPort, hff _ hpf, hfψ _ (hfe ▸ hpf)]
theorem AlphaEquiv.mkOfWf {N₁ N₂ : ICNet} (hWf₁ : WfNet N₁) (free_eq : N₁.freePorts = N₂.freePorts) (φ ψ : Nat → Nat)
    (free_fix_φ : ∀ p ∈ N₁.freePorts, φ p.nodeId = p.nodeId) (free_fix_ψ : ∀ p ∈ N₂.freePorts, ψ p.nodeId = p.nodeId)
    (left_inv : ∀ a ∈ N₁.agents, ψ (φ a.id) = a.id) (right_inv : ∀ b ∈ N₂.agents, φ (ψ b.id) = b.id)
    (map_agent : ∀ a ∈ N₁.agents, ⟨φ a.id, a.kind⟩ ∈ N₂.agents) (inv_agent : ∀ b ∈ N₂.agents, ⟨ψ b.id, b.kind⟩ ∈ N₁.agents)
    (partner_eq : ∀ p ∈ livePorts N₁, mapPort φ (N₁.partner p) = N₂.partner (mapPort φ p)) : AlphaEquiv N₁ N₂ :=
  ⟨⟨free_eq, φ, ψ, free_fix_φ, free_fix_ψ, left_inv, right_inv, map_agent, inv_agent, partner_eq, fun q hq => by
    have hψm := mapPort_mem_of_parts free_eq.symm free_fix_ψ inv_agent hq; have hpe := partner_eq (mapPort ψ q) hψm; rw [mapPort_left_inv_of_parts free_eq.symm free_fix_ψ free_fix_φ right_inv hq] at hpe; rw [← hpe]
    exact mapPort_left_inv_of_parts free_eq free_fix_φ free_fix_ψ left_inv (hWf₁.partner_wf _ hψm).1⟩⟩
theorem AlphaEquiv.refl (N : ICNet) : AlphaEquiv N N := ⟨⟨rfl, id, id, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl⟩⟩
theorem AlphaEquiv.symm {N₁ N₂ : ICNet} (h : AlphaEquiv N₁ N₂) : AlphaEquiv N₂ N₁ :=
  let ⟨i⟩ := h; ⟨⟨i.free_eq.symm, i.ψ, i.φ, i.free_fix_ψ, i.free_fix_φ, i.right_inv, i.left_inv, i.inv_agent, i.map_agent, i.partner_inv, i.partner_eq⟩⟩
theorem AlphaEquiv.trans {N₁ N₂ N₃ : ICNet} (h₁ : AlphaEquiv N₁ N₂) (h₂ : AlphaEquiv N₂ N₃) : AlphaEquiv N₁ N₃ := let ⟨i1⟩ := h₁; let ⟨i2⟩ := h₂
  ⟨⟨i1.free_eq.trans i2.free_eq, fun x => i2.φ (i1.φ x), fun y => i1.ψ (i2.ψ y), fun p hp => by rw [i1.free_fix_φ p hp, i2.free_fix_φ p (i1.free_eq ▸ hp)],
    fun p hp => by rw [i2.free_fix_ψ p hp, i1.free_fix_ψ p (i2.free_eq.symm ▸ hp)],
    fun a ha => by rw [i2.left_inv _ (i1.map_agent a ha), i1.left_inv a ha],
    fun c hc => by rw [i1.right_inv _ (i2.inv_agent c hc), i2.right_inv c hc],
    fun a ha => i2.map_agent _ (i1.map_agent a ha), fun c hc => i1.inv_agent _ (i2.inv_agent c hc),
    fun p hp => by change mapPort i2.φ (mapPort i1.φ (N₁.partner p)) = _; rw [i1.partner_eq p hp, i2.partner_eq _ (mapPort_mem_of_parts i1.free_eq i1.free_fix_φ i1.map_agent hp)]; rfl,
    fun q hq => by change mapPort i1.ψ (mapPort i2.ψ (N₃.partner q)) = _; rw [i2.partner_inv q hq, i1.partner_inv _ (mapPort_mem_of_parts i2.free_eq.symm i2.free_fix_ψ i2.inv_agent hq)]; rfl⟩⟩
def freePortsBound (fp : List PortRef) : Nat := fp.foldl (fun m p => max m (p.nodeId + 1)) 0
def indexOfAgent : List Agent → Nat → Nat → Option Nat
  | [], _, _ => none | a :: as, id, idx => if a.id == id then some idx else indexOfAgent as id (idx + 1)
def reindexAgents (base : Nat) : List Agent → Nat → List Agent
  | [], _ => [] | a :: as, k => ⟨base + k, a.kind⟩ :: reindexAgents base as (k + 1)
@[expose] def canonicalizeNet (N : ICNet) : ICNet := let base := freePortsBound N.freePorts; let φ := fun id => match indexOfAgent N.agents id 0 with | some k => base + k | none => id
  let ψ := fun id => if h : base ≤ id ∧ id < base + N.agents.length then (N.agents[id - base]'(by omega)).id else id
  mkNetFrom (reindexAgents base N.agents 0) N.freePorts (fun q => mapPort φ (N.partner (mapPort ψ q))) (base + N.agents.length)
theorem lt_freePortsBound_aux : ∀ (fp : List PortRef) (m : Nat) (p : PortRef), p ∈ fp → p.nodeId < fp.foldl (fun acc q => max acc (q.nodeId + 1)) m
  | [], _, _, h => by cases h
  | _ :: qs, m, p, h => by
    have hle : ∀ (l : List PortRef) (k : Nat), k ≤ l.foldl (fun acc r => max acc (r.nodeId + 1)) k := by
      intro l; induction l with | nil => intro _; exact Nat.le_refl _ | cons _ _ ih => intro _; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
    simp only [List.foldl_cons]; rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) (hle qs _)
    · exact lt_freePortsBound_aux qs _ p h'
theorem indexOfAgent_getElem : ∀ (as : List Agent) (k idx : Nat), (as.map (·.id)).Nodup → (hk : k < as.length) → indexOfAgent as (as[k]'hk).id idx = some (idx + k)
  | [], _, _, _, hk => by cases hk
  | _ :: _, 0, _, _, _ => by simp [indexOfAgent]
  | a :: as, k + 1, idx, hnd, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd; have hne : a.id ≠ (as[k]'(Nat.lt_of_succ_lt_succ hk)).id := fun e => hnd.1 ⟨_, List.getElem_mem _, e.symm⟩
    simp only [List.getElem_cons_succ, indexOfAgent, beq_false_of_ne hne, Bool.false_eq_true, ite_false]; rw [indexOfAgent_getElem as k (idx + 1) hnd.2 (Nat.lt_of_succ_lt_succ hk)]; congr 1; omega
theorem reindexAgents_mem_iff (base : Nat) : ∀ (as : List Agent) (k : Nat) (b : Agent), b ∈ reindexAgents base as k ↔ ∃ (j : Nat) (hj : j < as.length), b = ⟨base + k + j, (as[j]'hj).kind⟩
  | [], _, _ => by simp [reindexAgents]
  | _ :: as, k, b => by
    simp only [reindexAgents, List.mem_cons, reindexAgents_mem_iff base as (k + 1) b]
    exact ⟨fun h => h.elim (fun e => ⟨0, Nat.zero_lt_succ _, by simp [e]⟩) (fun ⟨j, hj, e⟩ => ⟨j + 1, Nat.succ_lt_succ hj, by simp [e, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩),
      fun ⟨j, hj, e⟩ => by cases j with | zero => left; simpa using e | succ j' => right; exact ⟨j', Nat.lt_of_succ_lt_succ hj, by simp [e, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩⟩
theorem canonicalizeNet_wf_and_alphaEquiv (N : ICNet) (hWf : WfNet N) : WfNet (canonicalizeNet N) ∧ AlphaEquiv N (canonicalizeNet N) := by
  let base := freePortsBound N.freePorts; let agents' := reindexAgents base N.agents 0; let φ := fun id => match indexOfAgent N.agents id 0 with | some k => base + k | none => id
  let ψ := fun id => if h : base ≤ id ∧ id < base + N.agents.length then (N.agents[id - base]'(by omega)).id else id
  have hnd' : ∀ (as : List Agent) (k : Nat), ((reindexAgents base as k).map (·.id)).Nodup := by
    intro as; induction as with | nil => intro _; exact List.nodup_nil | cons _ as ih =>
      intro k; simp only [reindexAgents, List.map_cons, List.nodup_cons, List.mem_map]
      exact ⟨fun ⟨b, hb, hid⟩ => by obtain ⟨_, _, rfl⟩ := (reindexAgents_mem_iff base as (k + 1) b).1 hb; dsimp at hid; omega, ih (k + 1)⟩
  have hφ_free : ∀ p ∈ N.freePorts, φ p.nodeId = p.nodeId := fun p hp => by
    have haux : ∀ (as : List Agent) (idx : Nat), (∀ a ∈ as, p.nodeId ≠ a.id) → indexOfAgent as p.nodeId idx = none := by
      intro as; induction as with | nil => intro _ _; rfl | cons a _ ih => intro idx hd; simp [indexOfAgent, beq_false_of_ne (hd a List.mem_cons_self).symm, ih (idx + 1) (fun x hx => hd x (List.mem_cons_of_mem _ hx))]
    simp [φ, haux N.agents 0 (hWf.free_disj p hp)]
  have hψ_free : ∀ p ∈ N.freePorts, ψ p.nodeId = p.nodeId := fun p hp => by
    have hlt : p.nodeId < base := lt_freePortsBound_aux N.freePorts 0 p hp; simp [ψ, show ¬(base ≤ p.nodeId ∧ p.nodeId < base + N.agents.length) by omega]
  have atIndex (j : Nat) (hj : j < N.agents.length) : φ N.agents[j].id = base + j ∧ ψ (base + j) = N.agents[j].id := by
    simp [φ, indexOfAgent_getElem N.agents j 0 hWf.agents_nodup hj, ψ, show base ≤ base + j ∧ base + j < base + N.agents.length by omega]
  have hleft (a : Agent) (ha : a ∈ N.agents) : ψ (φ a.id) = a.id := by obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha; rw [(atIndex j hj).1, (atIndex j hj).2]
  have hright (b : Agent) (hb : b ∈ agents') : φ (ψ b.id) = b.id := by obtain ⟨j, hj, rfl⟩ := (reindexAgents_mem_iff base N.agents 0 b).1 hb; simpa [(atIndex j hj).2] using (atIndex j hj).1
  have hmap_a (a : Agent) (ha : a ∈ N.agents) : ⟨φ a.id, a.kind⟩ ∈ agents' := by obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha; exact (reindexAgents_mem_iff base N.agents 0 _).2 ⟨j, hj, by simp [(atIndex j hj).1]⟩
  have hinv_a (b : Agent) (hb : b ∈ agents') : ⟨ψ b.id, b.kind⟩ ∈ N.agents := by
    obtain ⟨j, hj, rfl⟩ := (reindexAgents_mem_iff base N.agents 0 b).1 hb; simp only [Nat.add_zero, (atIndex j hj).2]; exact List.getElem_mem hj
  have hWf' : WfNet (canonicalizeNet N) := wfNet_mkNetFrom (hnd' N.agents 0) (fun b hb => by obtain ⟨j, hj, rfl⟩ := (reindexAgents_mem_iff base N.agents 0 b).1 hb; dsimp; omega) hWf.free_nodup
    (fun p hp => ⟨(hWf.free_spec p hp).1, Nat.lt_of_lt_of_le (lt_freePortsBound_aux N.freePorts 0 p hp) (Nat.le_add_right _ _)⟩)
    (fun p hp b hb => by obtain ⟨j, _, rfl⟩ := (reindexAgents_mem_iff base N.agents 0 b).1 hb; have hlt : p.nodeId < base := lt_freePortsBound_aux N.freePorts 0 p hp; dsimp; omega)
    fun q hq => by
      have hqN := mapPort_mem_of_parts (N₁ := canonicalizeNet N) (N₂ := N) rfl hψ_free hinv_a hq; obtain ⟨h1, h2, h3⟩ := hWf.partner_wf _ hqN
      have hψφ := mapPort_left_inv_of_parts (N₁ := N) (N₂ := canonicalizeNet N) rfl hφ_free hψ_free hleft h1; have hφψ := mapPort_left_inv_of_parts (N₁ := canonicalizeNet N) (N₂ := N) rfl hψ_free hφ_free hright hq
      exact ⟨mapPort_mem_of_parts (N₁ := N) (N₂ := canonicalizeNet N) rfl hφ_free hmap_a h1, fun he => h2 (by have := congrArg (mapPort ψ) he; rwa [hψφ] at this), by rw [hψφ, h3, hφψ]⟩
  refine ⟨hWf', AlphaEquiv.mkOfWf hWf rfl φ ψ hφ_free hψ_free hleft hright hmap_a hinv_a fun p hp => ?_⟩
  have hmp : mapPort φ p ∈ livePorts (mkNetFrom agents' N.freePorts (fun q => mapPort φ (N.partner (mapPort ψ q))) (base + N.agents.length)) :=
    mapPort_mem_of_parts (N₁ := N) (N₂ := canonicalizeNet N) rfl hφ_free hmap_a hp
  have hψφ := mapPort_left_inv_of_parts (N₁ := N) (N₂ := canonicalizeNet N) rfl hφ_free hψ_free hleft hp
  change mapPort φ (N.partner p) = (mkNetFrom agents' N.freePorts (fun q => mapPort φ (N.partner (mapPort ψ q))) (base + N.agents.length)).partner (mapPort φ p); rw [partner_mkNetFrom, ite_t hmp, hψφ]
theorem pairsDom_map (f : PortRef → PortRef) (ps : List (PortRef × PortRef)) : pairsDom (ps.map fun pq => (f pq.1, f pq.2)) = (pairsDom ps).map f := by
  induction ps with | nil => rfl | cons _ _ ih => simp only [pairsDom, List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢; exact congrArg _ (congrArg _ ih)
private theorem conj_transport {f σ σ' ρ ρ' τ τ' : PortRef → PortRef} {T T' : List PortRef} {p : PortRef}
    (mem : p ∈ T ↔ f p ∈ T') (internal : p ∈ T → f (τ p) = τ' (f p)) (outer : p ∉ T → f (ρ (σ (ρ p))) = ρ' (σ' (ρ' (f p)))) :
    f (applyConj ρ τ T σ p) = applyConj ρ' τ' T' σ' (f p) := by
  unfold applyConj; by_cases h : p ∈ T
  · rw [ite_t h, ite_t (mem.mp h)]; exact internal h
  · rw [ite_f h, ite_f (fun h' => h (mem.mpr h'))]; exact outer h
theorem ruleOp_apply_equiv {P₁ P₂ : List PortRef} {op₁ op₂ : RuleOp} {σ₁ σ₂ f : PortRef → PortRef} (hσ₁ : ∀ p ∈ P₁, σ₁ p ∈ P₁) (hσ_f : ∀ p ∈ P₁, f (σ₁ p) = σ₂ (f p)) (hmatch : match op₁, op₂ with
      | .conj _ _ rP₁ tP₁, .conj _ _ rP₂ tP₂ =>
        rP₂ = rP₁.map (fun pq => (f pq.1, f pq.2)) ∧ tP₂ = tP₁.map (fun pq => (f pq.1, f pq.2)) ∧
        (∀ x ∈ P₁ ++ pairsDom rP₁ ++ pairsDom tP₁, ∀ y ∈ P₁ ++ pairsDom rP₁ ++ pairsDom tP₁, f x = f y → x = y) ∧
        (∀ p ∈ P₂, p ∉ pairsDom tP₁ → swapList rP₁ p ∈ P₁)
      | .bridge bP₁, .bridge bP₂ =>
        bP₂ = bP₁.map (fun pq => (f pq.1, f pq.2)) ∧ (pairsDom bP₁).Nodup ∧
        (∀ x ∈ pairsDom bP₁, x ∈ P₁) ∧ (∀ x ∈ P₁, ∀ y ∈ pairsDom bP₁, f x = f y → x = y) ∧ (∀ p ∈ P₂, p ∈ P₁)
      | _, _ => False) {p : PortRef} (hp : p ∈ P₂) : f (op₁.apply σ₁ p) = op₂.apply σ₂ (f p) := by
  cases op₁ <;> cases op₂
  · rename_i _ _ rP1 tP1 _ _ rP2 tP2; obtain ⟨rfl, rfl, hinj, hρP1⟩ := hmatch; simp only [RuleOp.apply, pairsDom_map]; have hpU : p ∈ P₁ ++ pairsDom rP1 ++ pairsDom tP1 := by
      by_cases ht : p ∈ pairsDom tP1
      · exact List.mem_append_right _ ht
      · by_cases hr : p ∈ pairsDom rP1
        · exact List.mem_append_left _ (List.mem_append_right _ hr)
        · exact List.mem_append_left _ (List.mem_append_left _ (by have := hρP1 p hp ht; rwa [swapList_outside hr] at this))
    apply conj_transport
    · exact ⟨fun h => List.mem_map.2 ⟨p, h, rfl⟩, fun h => by obtain ⟨u, hu, he⟩ := List.mem_map.1 h; exact hinj p hpU u (List.mem_append_right _ hu) he.symm ▸ hu⟩
    · exact fun _ => swapList_map_at tP1 p fun u hu => hinj p hpU u (List.mem_append_right _ hu)
    · intro ht; have hρ := hρP1 p hp ht; have hσρ := hσ₁ _ hρ
      rw [swapList_map_at rP1 _ (fun u hu => hinj _ (List.mem_append_left _ (List.mem_append_left _ hσρ)) u (List.mem_append_left _ (List.mem_append_right _ hu))),
        hσ_f _ hρ, swapList_map_at rP1 p (fun u hu => hinj p hpU u (List.mem_append_left _ (List.mem_append_right _ hu)))]
  · cases hmatch
  · cases hmatch
  · rename_i bP1 bP2; obtain ⟨rfl, hbnd, hbP1, hinj, hpP1⟩ := hmatch; simp only [RuleOp.apply, pairsDom_map]; exact bridge_transport (D := (· ∈ P₁)) hσ₁ (fun x hx => hbP1 _ (((swapList_wf hbnd).2 x hx).1))
      (fun x hx => ⟨fun hm => List.mem_map.2 ⟨x, hm, rfl⟩, fun hm => by obtain ⟨y, hy, he⟩ := List.mem_map.1 hm; exact hinj x hx y hy he.symm ▸ hy⟩)
      hσ_f (fun x hx => swapList_map_at bP1 x fun u hu => hinj x (hbP1 x hx) u hu) (by simp) (hpP1 p hp)
private def PairsMapped (f : Nat → Nat) : RuleOp → RuleOp → Prop
  | .conj _ _ r t, .conj _ _ r' t' => r' = r.map (fun uv => (mapPort f uv.1, mapPort f uv.2)) ∧ t' = t.map (fun uv => (mapPort f uv.1, mapPort f uv.2))
  | .bridge r, .bridge r' => r' = r.map (fun uv => (mapPort f uv.1, mapPort f uv.2))
  | _, _ => False
private theorem classified_map {f : Nat → Nat} {i j i' j' b b' : Nat} {ka kb : CombKind} (hi : f i = i') (hj : f j = j') (shift : ∀ k < (classifyRule i j ka kb b).spawnCount, f (b + k) = b' + k) :
    PairsMapped f (classifyRule i j ka kb b) (classifyRule i' j' ka kb b') := by
  subst i' j'; cases ka <;> cases kb <;> unfold classifyRule classifyPair at *
  all_goals try (rename_i l r; by_cases h : l = r <;> simp only [h, ite_true, ite_false] at *)
  all_goals simp only [PairKind.toOp, RuleOp.spawnCount] at shift ⊢
  all_goals have h0 := shift 0; have h1 := shift 1; have h2 := shift 2; have h3 := shift 3
  all_goals simp_all [PairsMapped, commTauPairs, mapPort]
private theorem spawnCount_eq (i j i' j' b b' : Nat) (ka kb : CombKind) : (classifyRule i j ka kb b).spawnCount = (classifyRule i' j' ka kb b').spawnCount := by
  cases ka <;> cases kb <;> simp [classifyRule, classifyPair, PairKind.toOp, RuleOp.spawnCount]; rename_i l r; by_cases h : l = r <;> simp [h]
private def extend (f : Nat → Nat) (b c s x : Nat) : Nat := if b ≤ x ∧ x < b + s then c + (x - b) else f x
private theorem extend_inv {f g : Nat → Nat} {b c s x : Nat} (dom : (x < b ∧ f x < c ∧ g (f x) = x) ∨ (b ≤ x ∧ x < b+s)) : extend g c b s (extend f b c s x) = x := by unfold extend; grind only
theorem alphaEquiv_step_simulates (N₁ N₂ M₁ : ICNet) (hWf₁ : WfNet N₁) (hWf₂ : WfNet N₂) (hα : AlphaEquiv N₁ N₂) (hStep : Step N₁ M₁) : ∃ M₂, Step N₂ M₂ ∧ AlphaEquiv M₁ M₂ := by
  obtain ⟨iso⟩ := hα; cases hStep with
  | @fire i₁ j₁ hAct₁ hFire₁ =>
    obtain ⟨a₁, b₁, ha₁, rfl, hb₁, rfl, hfeq₁⟩ := fireActivePair_of_active hWf₁ hAct₁; rw [hfeq₁, Option.some.injEq] at hFire₁; subst hFire₁; let i₂ := iso.φ a₁.id; let j₂ := iso.φ b₁.id
    have hne₂ : i₂ ≠ j₂ := fun e => hAct₁.hne (by have := congrArg iso.ψ e; rwa [iso.left_inv a₁ ha₁, iso.left_inv b₁ hb₁] at this)
    have ha₂ := iso.map_agent a₁ ha₁; have hb₂ := iso.map_agent b₁ hb₁
    have hfac₂ : N₂.partner ⟨i₂, 0⟩ = ⟨j₂, 0⟩ := by simpa [mapPort, hAct₁.facing, i₂, j₂] using (iso.partner_eq ⟨a₁.id, 0⟩ (principal_live ha₁)).symm
    have hAct₂ : IsActivePair N₂ i₂ j₂ := ⟨hne₂, ⟨⟨i₂, a₁.kind⟩, ha₂, rfl⟩, ⟨⟨j₂, b₁.kind⟩, hb₂, rfl⟩, hfac₂⟩
    have hfeq₂ := fire_known hWf₂ hAct₂ ha₂ hb₂; let op₁ := classifyRule a₁.id b₁.id a₁.kind b₁.kind N₁.nextId
    let op₂ := classifyRule i₂ j₂ a₁.kind b₁.kind N₂.nextId; let s := op₁.spawnCount; have hs_eq : op₂.spawnCount = s := spawnCount_eq _ _ _ _ _ _ _ _
    let φ' := extend iso.φ N₁.nextId N₂.nextId s; let ψ' := extend iso.ψ N₂.nextId N₁.nextId s
    have hWfM₁ := step_preserves_wfNet N₁ _ hWf₁ (.fire hAct₁ hfeq₁); refine ⟨firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId, .fire hAct₂ hfeq₂, ?_⟩
    have hst₁ := classifyRule_struct a₁ b₁ N₁.nextId hAct₁.hne (hWf₁.agents_lt a₁ ha₁) (hWf₁.agents_lt b₁ hb₁)
    have hst₂ := classifyRule_struct ⟨i₂, a₁.kind⟩ ⟨j₂, b₁.kind⟩ N₂.nextId hne₂ (hWf₂.agents_lt _ ha₂) (hWf₂.agents_lt _ hb₂)
    have hφ'_lt : ∀ x, x < N₁.nextId → φ' x = iso.φ x := fun x hx => by simp [φ', extend, show ¬(N₁.nextId ≤ x ∧ x < N₁.nextId + s) by omega]
    have hψ'_lt : ∀ y, y < N₂.nextId → ψ' y = iso.ψ y := fun y hy => by simp [ψ', extend, show ¬(N₂.nextId ≤ y ∧ y < N₂.nextId + s) by omega]
    have hφ'_sh : ∀ k < s, φ' (N₁.nextId + k) = N₂.nextId + k := fun k hk => by simp [φ', extend, show N₁.nextId ≤ N₁.nextId + k ∧ N₁.nextId + k < N₁.nextId + s by omega]
    have hψ'_sh : ∀ k < s, ψ' (N₂.nextId + k) = N₁.nextId + k := fun k hk => by simp [ψ', extend, show N₂.nextId ≤ N₂.nextId + k ∧ N₂.nextId + k < N₂.nextId + s by omega]
    have hsp_φ := spawned_shift (i := a₁.id) (j := b₁.id) (ka := a₁.kind) (kb := b₁.kind) (i' := i₂) (j' := j₂) hφ'_sh
    have hsp_ψ := spawned_shift (i := i₂) (j := j₂) (i' := a₁.id) (j' := b₁.id) (ka := a₁.kind) (kb := b₁.kind) (fun k hk => hψ'_sh k (hs_eq ▸ hk))
    have hfree_φ : ∀ p ∈ (firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId).freePorts, φ' p.nodeId = p.nodeId := fun p hp => by rw [hφ'_lt _ (hWf₁.free_spec p hp).2, iso.free_fix_φ p hp]
    have hfree_ψ : ∀ p ∈ (firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId).freePorts, ψ' p.nodeId = p.nodeId := fun p hp => by rw [hψ'_lt _ (hWf₂.free_spec p hp).2, iso.free_fix_ψ p hp]
    have hma : ∀ x ∈ (firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId).agents, ⟨φ' x.id, x.kind⟩ ∈ (firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId).agents := fun x hx => by
      rcases List.mem_append.1 hx with hxk | hxs
      · simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hxk; rw [hφ'_lt _ (hWf₁.agents_lt x hxk.1)]; refine List.mem_append_left _ (List.mem_filter.2 ⟨iso.map_agent x hxk.1, ?_⟩)
        simp only [Bool.and_eq_true, bne_iff_ne]; exact ⟨fun e => hxk.2.1 (by have := congrArg iso.ψ e; rwa [iso.left_inv x hxk.1, iso.left_inv a₁ ha₁] at this),
          fun e => hxk.2.2 (by have := congrArg iso.ψ e; rwa [iso.left_inv x hxk.1, iso.left_inv b₁ hb₁] at this)⟩
      · exact List.mem_append_right _ (hsp_φ x hxs)
    have hia : ∀ y ∈ (firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId).agents, ⟨ψ' y.id, y.kind⟩ ∈ (firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId).agents := fun y hy => by
      rcases List.mem_append.1 hy with hyk | hys
      · simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hyk; rw [hψ'_lt _ (hWf₂.agents_lt y hyk.1)]; refine List.mem_append_left _ (List.mem_filter.2 ⟨iso.inv_agent y hyk.1, ?_⟩)
        simp only [Bool.and_eq_true, bne_iff_ne]
        exact ⟨fun e => hyk.2.1 (by have := congrArg iso.φ e; rwa [iso.right_inv y hyk.1] at this), fun e => hyk.2.2 (by have := congrArg iso.φ e; rwa [iso.right_inv y hyk.1] at this)⟩
      · exact List.mem_append_right _ (hsp_ψ y hys)
    have hleft (x : Agent) (hx : x ∈ (firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId).agents) : ψ' (φ' x.id) = x.id := by
      apply extend_inv; rcases List.mem_append.mp hx with h | h
      · have old := (List.mem_filter.mp h).1; exact .inl ⟨hWf₁.agents_lt _ old, hWf₂.agents_lt _ (iso.map_agent x old), iso.left_inv x old⟩
      · exact .inr (hst₁.2.1 x h)
    have hright (x : Agent) (hx : x ∈ (firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId).agents) : φ' (ψ' x.id) = x.id := by
      apply extend_inv; rcases List.mem_append.mp hx with h | h
      · have old := (List.mem_filter.mp h).1; exact .inl ⟨hWf₂.agents_lt _ old, hWf₁.agents_lt _ (iso.inv_agent x old), iso.right_inv x old⟩
      · exact .inr (hs_eq ▸ hst₂.2.1 x h)
    refine AlphaEquiv.mkOfWf hWfM₁ iso.free_eq φ' ψ' hfree_φ hfree_ψ hleft hright hma hia fun p hp => ?_
    have hmp := mapPort_mem_of_parts (N₁ := firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId) (N₂ := firePairWith N₂ i₂ j₂ a₁.kind b₁.kind N₂.nextId) iso.free_eq hfree_φ hma hp
    unfold firePairWith at hp hmp ⊢; rw [partner_mkNetFrom, ite_t hp, partner_mkNetFrom, ite_t hmp]
    have hφ'_N1 : ∀ q ∈ livePorts N₁, mapPort φ' q = mapPort iso.φ q := fun q hq => by cases q; simp [mapPort, hφ'_lt _ (livePorts_lt_nextId hWf₁ hq)]
    have hinj_ext : ∀ x y, (x ∈ livePorts N₁ ∨ (N₁.nextId ≤ x.nodeId ∧ x.nodeId < N₁.nextId + s)) → (y ∈ livePorts N₁ ∨ (N₁.nextId ≤ y.nodeId ∧ y.nodeId < N₁.nextId + s)) → mapPort φ' x = mapPort φ' y → x = y := by
      have inv (p : PortRef) (h : p ∈ livePorts N₁ ∨ (N₁.nextId ≤ p.nodeId ∧ p.nodeId < N₁.nextId+s)) : mapPort ψ' (mapPort φ' p) = p := by
        obtain ⟨i, k⟩ := p; simp only [mapPort, PortRef.mk.injEq, and_true]; apply extend_inv
        refine h.imp_left fun old => ⟨livePorts_lt_nextId hWf₁ old, livePorts_lt_nextId hWf₂ (mapPort_mem_of_parts (N₁ := N₁) (N₂ := N₂) (p := ⟨i, k⟩) iso.free_eq iso.free_fix_φ iso.map_agent old), ?_⟩
        exact congrArg PortRef.nodeId (mapPort_left_inv_of_parts (N₁ := N₁) (N₂ := N₂) (p := ⟨i, k⟩) iso.free_eq iso.free_fix_φ iso.free_fix_ψ iso.left_inv old)
      intro x y hx hy eq; rw [← inv x hx, eq, inv y hy]
    refine ruleOp_apply_equiv (op₁ := op₁) (op₂ := op₂) (P₁ := livePorts N₁) (P₂ := livePorts (firePairWith N₁ a₁.id b₁.id a₁.kind b₁.kind N₁.nextId))
      (fun q hq => (hWf₁.partner_wf q hq).1) (fun q hq => by rw [hφ'_N1 _ (hWf₁.partner_wf q hq).1, hφ'_N1 q hq, iso.partner_eq q hq]) ?_ hp
    have hop_map : PairsMapped φ' op₁ op₂ := classified_map (hφ'_lt _ (hWf₁.agents_lt a₁ ha₁)) (hφ'_lt _ (hWf₁.agents_lt b₁ hb₁)) hφ'_sh; cases hop1 : op₁ <;> cases hop2 : op₂ <;> rw [hop1, hop2] at hop_map
    · rename_i s1 _ rP1 tP1 _ _ _ _; obtain ⟨hr2, ht2⟩ := hop_map; have hst1' := hst₁.2.2; rw [show classifyRule a₁.id b₁.id a₁.kind b₁.kind N₁.nextId = _ from hop1] at hst1'
      obtain ⟨_, _, _, hfst_aux, ht_rg, hsnd_rg, _⟩ := hst1'; have hs1 : s1 = s := by simp only [s]; rw [hop1]; rfl
      subst hs1; have hU : ∀ x ∈ livePorts N₁ ++ pairsDom rP1 ++ pairsDom tP1, x ∈ livePorts N₁ ∨ (N₁.nextId ≤ x.nodeId ∧ x.nodeId < N₁.nextId + s) := by
        intro x hx; simp only [List.mem_append] at hx; rcases hx with (h | h) | h
        · exact .inl h
        · obtain ⟨⟨u, v⟩, huv, hxu⟩ := List.mem_flatMap.1 h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hxu; rcases hxu with rfl | rfl
          · exact .inl (((livePorts_split hWf₁ ha₁ hb₁ hAct₁.hne x).1).2 (.inr (.inr (.inr (List.mem_append.1 ((hfst_aux x).1 (List.mem_map.2 ⟨(x, v), huv, rfl⟩)))))))
          · have := hsnd_rg x (List.mem_map.2 ⟨(u, x), huv, rfl⟩); exact .inr ⟨this.1, this.2.1⟩
        · have := ht_rg x h; exact .inr ⟨this.1, this.2.1⟩
      exact ⟨hr2, ht2, fun x hx y hy => hinj_ext x y (hU x hx) (hU y hy), fun q hq hqnT => conj_rho_live hWf₁ ha₁ hb₁ hAct₁.hne hop1 hq hqnT⟩
    · cases hop_map
    · cases hop_map
    · rename_i bP1 _; have hst1' := hst₁.2.2; rw [show classifyRule a₁.id b₁.id a₁.kind b₁.kind N₁.nextId = _ from hop1] at hst1'; obtain ⟨hbnd, hbaux, _⟩ := hst1'
      have hb_in : ∀ x ∈ pairsDom bP1, x ∈ livePorts N₁ := fun x hx => ((livePorts_split hWf₁ ha₁ hb₁ hAct₁.hne x).1).2 (.inr (.inr (.inr (List.mem_append.1 ((hbaux x).1 hx)))))
      refine ⟨hop_map, hbnd, hb_in, fun x hx y hy => hinj_ext x y (.inl hx) (.inl (hb_in y hy)), fun q hq => ?_⟩
      unfold firePairWith at hq; rw [show classifyRule a₁.id b₁.id a₁.kind b₁.kind N₁.nextId = _ from hop1] at hq
      exact ((livePorts_split hWf₁ ha₁ hb₁ hAct₁.hne q).1).2 (.inl (by simpa [livePorts, mkNetFrom, RuleOp.spawned] using hq))
theorem alphaEquiv_steps_simulates (N₁ N₂ M₁ : ICNet) (hWf₁ : WfNet N₁) (hWf₂ : WfNet N₂) (hα : AlphaEquiv N₁ N₂) (hSteps : Steps N₁ M₁) : ∃ M₂, Steps N₂ M₂ ∧ AlphaEquiv M₁ M₂ := by
  induction hSteps generalizing N₂ with
  | refl => exact ⟨N₂, .refl _, hα⟩
  | next hStep _ ih =>
    obtain ⟨N₂', hStep₂, hα'⟩ := alphaEquiv_step_simulates _ N₂ _ hWf₁ hWf₂ hα hStep; obtain ⟨M₂, hRest₂, hα''⟩ := ih N₂' (step_preserves_wfNet _ _ hWf₁ hStep) (step_preserves_wfNet _ _ hWf₂ hStep₂) hα'
    exact ⟨M₂, .next hStep₂ hRest₂, hα''⟩

/-! ## 7. Orientation Symmetry & Strong One-Step Diamond (`wfNet_strong_diamond`) -/
private theorem mapPort_partner_fixed {N : ICNet} (wf : WfNet N) {f : Nat → Nat} (inj : ∀ x y, mapPort f x = mapPort f y → x = y) (fix : ∀ i < N.nextId, f i = i) (p : PortRef) :
    mapPort f (N.partner p) = N.partner (mapPort f p) := by
  have fixed (x : PortRef) (hx : x ∈ livePorts N) : mapPort f x = x := by cases x; simp [mapPort, fix _ (livePorts_lt_nextId wf hx)]
  by_cases hp : p ∈ livePorts N
  · rw [fixed p hp, fixed _ (wf.partner_wf p hp).1]
  · have out : mapPort f p ∉ livePorts N := fun h => hp (inj _ _ (fixed _ h).symm ▸ h); rw [partner_of_not_live wf hp, partner_of_not_live wf out]
theorem fireActivePair_swap_alphaEquiv (N N₁ N₂ : ICNet) (i j : Nat) (hWf : WfNet N) (hAct : IsActivePair N i j) (h₁ : fireActivePair N i j = some N₁) (h₂ : fireActivePair N j i = some N₂) : AlphaEquiv N₁ N₂ := by
  obtain ⟨a, b, ha, rfl, hb, rfl, hfeq₁⟩ := fireActivePair_of_active hWf hAct; have hfeq₂ := fire_known hWf (hAct.symm hWf) hb ha
  rw [hfeq₁, Option.some.injEq] at h₁; rw [hfeq₂, Option.some.injEq] at h₂; subst h₁ h₂; have hWf₁ := step_preserves_wfNet N _ hWf (.fire hAct hfeq₁)
  have hkeep_eq : N.agents.filter (fun x => x.id != a.id && x.id != b.id) = N.agents.filter (fun x => x.id != b.id && x.id != a.id) := by congr 1; funext x; exact Bool.and_comm _ _
  let n := N.nextId; let sw : Nat → Nat := fun x => if x = n then n + 2 else if x = n + 1 then n + 3 else if x = n + 2 then n else if x = n + 3 then n + 1 else x
  have hsw_inv : ∀ x, sw (sw x) = x := fun x => by simp only [sw]; grind
  have hsw_lt : ∀ x, x < n → sw x = x := fun x hx => by simp only [sw]; grind
  have hpk_swap : match classifyPair a.id b.id a.kind b.kind with
      | .void => classifyPair b.id a.id b.kind a.kind = .void | .era bin => classifyPair b.id a.id b.kind a.kind = .era bin
      | .anni => classifyPair b.id a.id b.kind a.kind = .anni | .comm ka kb => classifyPair b.id a.id b.kind a.kind = .comm kb ka := by
    cases hka : a.kind <;> cases hkb : b.kind <;> simp [classifyPair]; rename_i l1 l2; by_cases hl : l1 = l2
    · subst hl; simp
    · simp [hl, Ne.symm hl]
  unfold firePairWith classifyRule at hWf₁ ⊢; cases hpk : classifyPair a.id b.id a.kind b.kind <;> rw [hpk] at hpk_swap hWf₁ <;> rw [hpk_swap]
  · simp [PairKind.toOp, hkeep_eq]; exact AlphaEquiv.refl _
  · simp [PairKind.toOp, hkeep_eq]; exact AlphaEquiv.refl _
  · rw [← hkeep_eq]; simp only [PairKind.toOp, RuleOp.spawned, RuleOp.spawnCount, RuleOp.apply, List.append_nil, Nat.add_zero] at hWf₁ ⊢
    refine AlphaEquiv.mkOfWf hWf₁ rfl id id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h) (fun _ h => h) fun p hp => ?_
    have map_id (x : PortRef) : mapPort id x = x := rfl; simp only [map_id, partner_mkNetFrom, ite_t hp]; rw [ite_t (by exact hp)]
    have hbr : ∀ x, swapList [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)] x = swapList [(⟨b.id, 1⟩, ⟨a.id, 1⟩), (⟨b.id, 2⟩, ⟨a.id, 2⟩)] x := fun x => by simp only [swapList]; grind [hAct.hne]
    have hdm : ∀ x, x ∈ pairsDom [(⟨a.id, 1⟩, ⟨b.id, 1⟩), (⟨a.id, 2⟩, ⟨b.id, 2⟩)] ↔ x ∈ pairsDom [(⟨b.id, 1⟩, ⟨a.id, 1⟩), (⟨b.id, 2⟩, ⟨a.id, 2⟩)] := fun _ => by simp [pairsDom]; grind
    exact bridge_transport (D := fun _ => True) (f := id) (p := p) (σ₁ := N.partner) (σ₂ := N.partner) (fun _ _ => trivial) (fun _ _ => trivial) (fun x _ => hdm x) (fun _ _ => rfl) (fun x _ => hbr x) rfl trivial
  · rename_i ka kb; rw [← hkeep_eq]; simp only [PairKind.toOp, RuleOp.spawned, RuleOp.spawnCount, RuleOp.apply] at hWf₁ ⊢
    have hltA := hWf.agents_lt a ha; have hltB := hWf.agents_lt b hb; let keep := N.agents.filter (fun x => x.id != a.id && x.id != b.id)
    have perm (ka kb : CombKind) : ∀ x ∈ keep ++ [⟨n, kb⟩, ⟨n + 1, kb⟩, ⟨n + 2, ka⟩, ⟨n + 3, ka⟩], ⟨sw x.id, x.kind⟩ ∈ keep ++ [⟨n, ka⟩, ⟨n + 1, ka⟩, ⟨n + 2, kb⟩, ⟨n + 3, kb⟩] := fun x hx => by
      rcases List.mem_append.1 hx with hxk | hxs
      · rw [hsw_lt _ (hWf.agents_lt x (List.mem_filter.1 hxk).1)]; exact List.mem_append_left _ hxk
      · refine List.mem_append_right _ ?_; simp at hxs
        rcases hxs with rfl | rfl | rfl | rfl <;> simp [sw]
    have hma := perm ka kb; have hia := perm kb ka; let M₁ := mkNetFrom (keep ++ [⟨n, kb⟩, ⟨n + 1, kb⟩, ⟨n + 2, ka⟩, ⟨n + 3, ka⟩]) N.freePorts
      (applyConj (swapList [(⟨a.id, 1⟩, ⟨n, 0⟩), (⟨a.id, 2⟩, ⟨n + 1, 0⟩), (⟨b.id, 1⟩, ⟨n + 2, 0⟩), (⟨b.id, 2⟩, ⟨n + 3, 0⟩)]) (swapList (commTauPairs n)) (pairsDom (commTauPairs n)) N.partner) (n + 4)
    let M₂ := mkNetFrom (keep ++ [⟨n, ka⟩, ⟨n + 1, ka⟩, ⟨n + 2, kb⟩, ⟨n + 3, kb⟩]) N.freePorts
      (applyConj (swapList [(⟨b.id, 1⟩, ⟨n, 0⟩), (⟨b.id, 2⟩, ⟨n + 1, 0⟩), (⟨a.id, 1⟩, ⟨n + 2, 0⟩), (⟨a.id, 2⟩, ⟨n + 3, 0⟩)]) (swapList (commTauPairs n)) (pairsDom (commTauPairs n)) N.partner) (n + 4)
    change WfNet M₁ at hWf₁; change AlphaEquiv M₁ M₂; refine AlphaEquiv.mkOfWf hWf₁ rfl sw sw (fun p hp => hsw_lt _ (hWf.free_spec p hp).2)
      (fun p hp => hsw_lt _ (hWf.free_spec p hp).2) (fun x _ => hsw_inv x.id) (fun y _ => hsw_inv y.id) hma hia fun p hp => ?_
    have hmp := mapPort_mem_of_parts (N₁ := M₁) (N₂ := M₂) rfl (fun q hq => hsw_lt _ (hWf.free_spec q hq).2) hma hp; dsimp only [M₁, M₂] at hp hmp ⊢; rw [partner_mkNetFrom, ite_t hp, partner_mkNetFrom, ite_t hmp]
    have hsw_inj : ∀ x y, mapPort sw x = mapPort sw y → x = y := fun x y he => by have := congrArg (mapPort sw) he; cases x; cases y; simpa only [mapPort, hsw_inv] using this
    have hσ_sw := mapPort_partner_fixed hWf hsw_inj hsw_lt; have hρ_sw : ∀ x, mapPort sw (swapList [(⟨a.id, 1⟩, ⟨n, 0⟩), (⟨a.id, 2⟩, ⟨n + 1, 0⟩), (⟨b.id, 1⟩, ⟨n + 2, 0⟩), (⟨b.id, 2⟩, ⟨n + 3, 0⟩)] x) =
        swapList [(⟨b.id, 1⟩, ⟨n, 0⟩), (⟨b.id, 2⟩, ⟨n + 1, 0⟩), (⟨a.id, 1⟩, ⟨n + 2, 0⟩), (⟨a.id, 2⟩, ⟨n + 3, 0⟩)] (mapPort sw x) := fun x => by
      rw [swapList_map_inj hsw_inj]; simp only [List.map_cons, List.map_nil, mapPort, hsw_lt a.id hltA, hsw_lt b.id hltB, show sw n = n + 2 by simp [sw], show sw (n + 1) = n + 3 by simp [sw],
        show sw (n + 2) = n by simp [sw], show sw (n + 3) = n + 1 by simp [sw], swapList]
      have hne' := hAct.hne; change a.id < n at hltA; change b.id < n at hltB; grind -verbose -zetaDelta (splits := 32) only
    have hT_iff : ∀ x, x ∈ pairsDom (commTauPairs n) ↔ mapPort sw x ∈ pairsDom (commTauPairs n) := by
      have hf : ∀ x, x ∈ pairsDom (commTauPairs n) → mapPort sw x ∈ pairsDom (commTauPairs n) := fun x hx => by
        simp [pairsDom, commTauPairs] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mapPort, sw] <;> omega
      exact fun x => ⟨hf x, fun h => by have := hf _ h; cases x; simpa [mapPort, hsw_inv] using this⟩
    unfold applyConj; by_cases hT : p ∈ pairsDom (commTauPairs n)
    · simp only [hT, (hT_iff p).1 hT, ite_true]; simp [pairsDom, commTauPairs] at hT; rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp (disch := omega) [swapList, commTauPairs, mapPort, sw])
    · simp only [← hT_iff, hT, ite_false]; rw [hρ_sw, hσ_sw, hρ_sw]
def swapBlocks (n s₁ s₂ x : Nat) : Nat := if n ≤ x ∧ x < n + s₁ then x + s₂ else if n + s₁ ≤ x ∧ x < n + s₁ + s₂ then x - s₁ else x
theorem swapBlocks_inv (n s₁ s₂ x : Nat) : swapBlocks n s₂ s₁ (swapBlocks n s₁ s₂ x) = x := by unfold swapBlocks; grind
theorem ruleOp_congr {op : RuleOp} {σ₁ σ₂ : PortRef → PortRef} {P : List PortRef} (hcongr : ∀ q ∈ P, σ₁ q = σ₂ q) (hcl : ∀ q ∈ P, σ₁ q ∈ P) {p : PortRef} (hdom : match op with
      | .conj _ _ rP tP => p ∉ pairsDom tP → swapList rP p ∈ P
      | .bridge bP => (∀ x ∈ pairsDom bP, x ∈ P ∧ swapList bP x ∈ pairsDom bP) ∧ p ∈ P) :
    op.apply σ₁ p = op.apply σ₂ p := by
  cases op with
  | conj _ _ rP tP =>
    dsimp only at hdom; simp only [RuleOp.apply, applyConj]; by_cases ht : p ∈ pairsDom tP
    · rw [ite_t ht, ite_t ht]
    · rw [ite_f ht, ite_f ht]; exact congrArg (swapList rP) (hcongr _ (hdom ht))
  | bridge bP =>
    obtain ⟨hA, hpP⟩ := hdom; exact bridge_transport (D := (· ∈ P)) (f := id) (p := p) (σ₁ := σ₁) (σ₂ := σ₂) (β₁ := swapList bP) (β₂ := swapList bP) hcl (fun x hx => (hA _ (hA x hx).2).1)
      (fun _ _ => Iff.rfl) hcongr (fun _ _ => rfl) rfl hpP
private def touched : RuleOp → List PortRef
  | .conj _ _ r t => pairsDom r ++ pairsDom t | .bridge b => pairsDom b
private def removed : RuleOp → List PortRef | .bridge b => pairsDom b | .conj .. => []
private def validWires (N : ICNet) : RuleOp → Prop
  | .conj _ _ r t => (pairsDom r).Nodup ∧ (pairsDom t).Nodup
  | .bridge b => (pairsDom b).Nodup ∧ ∀ x ∈ pairsDom b, x ∈ livePorts N
private theorem wiring_bounds {N : ICNet} (wf : WfNet N) {a b : Agent} (ha : a ∈ N.agents) (hb : b ∈ N.agents) (ne : a.id ≠ b.id) {base : Nat} (hbase : N.nextId ≤ base) :
    let op := classifyRule a.id b.id a.kind b.kind base; validWires N op ∧ (∀ x ∈ removed op, x.nodeId = a.id ∨ x.nodeId = b.id) ∧
      ∀ x ∈ touched op, x.nodeId = a.id ∨ x.nodeId = b.id ∨ (base ≤ x.nodeId ∧ x.nodeId < base + op.spawnCount) := by
  have spec := (classifyRule_struct a b base ne (Nat.lt_of_lt_of_le (wf.agents_lt a ha) hbase) (Nat.lt_of_lt_of_le (wf.agents_lt b hb) hbase)).2.2
  dsimp only; cases eq : classifyRule a.id b.id a.kind b.kind base <;> rw [eq] at spec
  · obtain ⟨hr, ht, _, _, tr, sr, old⟩ := spec; refine ⟨⟨hr, ht⟩, by simp [removed], fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · rcases mem_pairsDom.mp h with h | h
      · exact (old x h).imp_right Or.inl
      · exact .inr (.inr ⟨(sr x h).1, (sr x h).2.1⟩)
    · exact .inr (.inr ⟨(tr x h).1, (tr x h).2.1⟩)
  · obtain ⟨hbnd, aux, old⟩ := spec; exact ⟨⟨hbnd, fun x hx => ((livePorts_split wf ha hb ne x).1).2 (.inr (.inr (.inr (List.mem_append.mp ((aux x).1 hx)))))⟩, old, fun x hx => (old x hx).imp_right Or.inl⟩
private theorem bridge_stops {σ β : PortRef → PortRef} {A : List PortRef} {p : PortRef} (out : σ p ∉ A) : contractBridge σ β A p = σ p := by cases h : A.length <;> simp [contractBridge, h, walkAux, out]
private theorem untouched {op : RuleOp} {σ : PortRef → PortRef} {p : PortRef} (a : p ∉ touched op) (b : σ p ∉ touched op) : op.apply σ p = σ p := by
  cases op with
  | bridge => exact bridge_stops b
  | conj _ _ r t => simp only [touched, List.mem_append, not_or] at a b; simp [RuleOp.apply, applyConj, a.2, swapList_outside a.1, swapList_outside b.1]
private theorem fixed_mem {ps : List (PortRef × PortRef)} {F : List PortRef} (nd : (pairsDom ps).Nodup) (apart : ∀ x ∈ F, x ∉ pairsDom ps) (x : PortRef) : swapList ps x ∈ F ↔ x ∈ F :=
  ⟨fun h => by rwa [← (swapList_wf nd).1 x, swapList_outside (apart _ h)], fun h => by rwa [swapList_outside (apart _ h)]⟩
private theorem wires_commute {N : ICNet} (wf : WfNet N) {o₁ o₂ : RuleOp} (v₁ : validWires N o₁) (v₂ : validWires N o₂)
    (apart : ∀ x ∈ touched o₁, x ∉ touched o₂) {q : PortRef} (qr₁ : q ∉ removed o₁) (qr₂ : q ∉ removed o₂) :
    o₂.apply (o₁.apply N.partner) q = o₁.apply (o₂.apply N.partner) q := by
  have mixed {b r t : List (PortRef × PortRef)} (bn : (pairsDom b).Nodup) (rn : (pairsDom r).Nodup) (tn : (pairsDom t).Nodup) (br : ∀ x ∈ pairsDom b, x ∉ pairsDom r) (tb : ∀ x ∈ pairsDom t, x ∉ pairsDom b) :=
    bridge_conj (σ := N.partner) (fun x h => ((swapList_wf bn).2 x h).1) (fun x h => swapList_outside (br x h)) (fixed_mem rn br) (fun x h => ((swapList_wf tn).2 x h).1) tb q
  cases o₁ <;> cases o₂ <;> simp only [validWires, touched, List.mem_append, not_or] at v₁ v₂ apart
  · obtain ⟨rn₁, tn₁⟩ := v₁; obtain ⟨rn₂, tn₂⟩ := v₂; have t₁r₂ := fun x h => (apart x (.inr h)).1; have t₂r₁ := fun x h h' => (apart x (.inl h')).2 h
    exact applyConj_comm N.partner (swapList_comm rn₁ rn₂ fun x h => (apart x (.inl h)).1) (fun x h => swapList_outside (t₁r₂ x h)) (fun x h => swapList_outside (t₂r₁ x h))
      (fun x h => ((swapList_wf tn₁).2 x h).1) (fun x h => ((swapList_wf tn₂).2 x h).1)
      (fun x h => (apart x (.inr h)).2) (fixed_mem rn₁ t₂r₁) (fixed_mem rn₂ t₁r₂) q
  · exact mixed v₂.1 v₁.1 v₁.2 (fun x hb hr => apart x (.inl hr) hb) (fun x ht => apart x (.inr ht))
  · exact (mixed v₁.1 v₂.1 v₂.2 (fun x h => (apart x h).1) (fun x ht hb => (apart x hb).2 ht)).symm
  · by_cases hq : q ∈ livePorts N
    · exact contractBridge_comm (fun x h => ⟨(wf.partner_wf x h).1, (wf.partner_wf x h).2.2⟩) (fun x h => ⟨((swapList_wf v₁.1).2 x h).1, (swapList_wf v₁.1).1 x⟩)
        (fun x h => ⟨((swapList_wf v₂.1).2 x h).1, (swapList_wf v₂.1).1 x⟩) v₁.2 v₂.2 apart hq qr₁ qr₂
    · rename_i b₁ b₂; have fix := partner_of_not_live wf hq; have x₁ : contractBridge N.partner (swapList b₁) (pairsDom b₁) q = q := (bridge_stops (fix.symm ▸ qr₁)).trans fix
      have x₂ : contractBridge N.partner (swapList b₂) (pairsDom b₂) q = q := (bridge_stops (fix.symm ▸ qr₂)).trans fix
      have s₁ : contractBridge (contractBridge N.partner (swapList b₁) (pairsDom b₁)) (swapList b₂) (pairsDom b₂) q = q :=
        (bridge_stops (σ := contractBridge N.partner (swapList b₁) (pairsDom b₁)) (β := swapList b₂) (x₁.symm ▸ qr₂)).trans x₁
      have s₂ : contractBridge (contractBridge N.partner (swapList b₂) (pairsDom b₂)) (swapList b₁) (pairsDom b₁) q = q :=
        (bridge_stops (σ := contractBridge N.partner (swapList b₂) (pairsDom b₂)) (β := swapList b₁) (x₂.symm ▸ qr₁)).trans x₂
      exact s₁.trans s₂.symm
theorem disjoint_pair_stays_active {N : ICNet} (hWf : WfNet N) {c d e f : Agent}
    (hc : c ∈ N.agents) (hd : d ∈ N.agents) (he : e ∈ N.agents) (hf : f ∈ N.agents) (hAcd : IsActivePair N c.id d.id) (hAef : IsActivePair N e.id f.id)
    (hce : c.id ≠ e.id) (hcf : c.id ≠ f.id) (hde : d.id ≠ e.id) (hdf : d.id ≠ f.id) : let M := firePairWith N c.id d.id c.kind d.kind N.nextId
    IsActivePair M e.id f.id ∧ e ∈ M.agents ∧ f ∈ M.agents := by
  intro M; have hMe : e ∈ M.agents := List.mem_append_left _ (by simp [he, hce.symm, hde.symm])
  have hMf : f ∈ M.agents := List.mem_append_left _ (by simp [hf, hcf.symm, hdf.symm])
  have hpe0 : ⟨e.id, 0⟩ ∈ livePorts M := principal_live hMe; have ⟨_, _, bound⟩ := wiring_bounds hWf hc hd hAcd.hne (Nat.le_refl _); have he_lt := hWf.agents_lt e he; have hf_lt := hWf.agents_lt f hf
  have hfacM : M.partner ⟨e.id,0⟩ = ⟨f.id,0⟩ := by
    unfold M firePairWith at hpe0 ⊢; rw [partner_mkNetFrom, ite_t hpe0]; rw [untouched (fun h => by have := bound ⟨e.id,0⟩ h; dsimp at this; omega)
      (fun h => by rw [hAef.facing] at h; have := bound ⟨f.id,0⟩ h; dsimp at this; omega), hAef.facing]
  exact ⟨⟨hAef.hne, ⟨e, hMe, rfl⟩, ⟨f, hMf, rfl⟩, hfacM⟩, hMe, hMf⟩
/-- **Strong One-Step Diamond (`wfNet_strong_diamond`)**. -/
theorem wfNet_strong_diamond (N N₁ N₂ : ICNet) (hWf : WfNet N) (h₁ : Step N N₁) (h₂ : Step N N₂) : AlphaEquiv N₁ N₂ ∨ ∃ N₁' N₂', Step N₁ N₁' ∧ Step N₂ N₂' ∧ AlphaEquiv N₁' N₂' := by
  cases h₁ with
  | @fire i₁ j₁ hAct₁ hFire₁ =>
    cases h₂ with
    | @fire i₂ j₂ hAct₂ hFire₂ =>
      by_cases hsame : (i₁ = i₂ ∧ j₁ = j₂) ∨ (i₁ = j₂ ∧ j₁ = i₂)
      · left; rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hFire₁, Option.some.injEq] at hFire₂; subst hFire₂; exact AlphaEquiv.refl _
        · exact fireActivePair_swap_alphaEquiv N N₁ N₂ i₁ j₁ hWf hAct₁ hFire₁ hFire₂
      · right; obtain ⟨⟨hd1, hd2, hd3, hd4⟩, _⟩ := wfNet_distinct_redexes_disjoint N i₁ j₁ i₂ j₂ hWf hAct₁ hAct₂ hsame
        obtain ⟨a₁, b₁, ha₁, rfl, hb₁, rfl, hfeq₁⟩ := fireActivePair_of_active hWf hAct₁; obtain ⟨a₂, b₂, ha₂, rfl, hb₂, rfl, hfeq₂⟩ := fireActivePair_of_active hWf hAct₂
        rw [hfeq₁, Option.some.injEq] at hFire₁; rw [hfeq₂, Option.some.injEq] at hFire₂; subst hFire₁ hFire₂
        have hWf₁ := step_preserves_wfNet N _ hWf (.fire hAct₁ hfeq₁); have hWf₂ := step_preserves_wfNet N _ hWf (.fire hAct₂ hfeq₂)
        obtain ⟨hAct2_1, ha2_1, hb2_1⟩ := disjoint_pair_stays_active hWf ha₁ hb₁ ha₂ hb₂ hAct₁ hAct₂ hd1 hd2 hd3 hd4
        obtain ⟨hAct1_2, ha1_2, hb1_2⟩ := disjoint_pair_stays_active hWf ha₂ hb₂ ha₁ hb₁ hAct₂ hAct₁ hd1.symm hd3.symm hd2.symm hd4.symm
        have hfeq₁₂ := fire_known hWf₁ hAct2_1 ha2_1 hb2_1; have hfeq₂₁ := fire_known hWf₂ hAct1_2 ha1_2 hb1_2; let n := N.nextId
        let op₁ := fun b => classifyRule a₁.id b₁.id a₁.kind b₁.kind b; let op₂ := fun b => classifyRule a₂.id b₂.id a₂.kind b₂.kind b
        let s₁ := (op₁ n).spawnCount; let s₂ := (op₂ n).spawnCount; have hs1_c (b : Nat) : (op₁ b).spawnCount = s₁ := spawnCount_eq _ _ _ _ _ _ _ _
        have hs2_c (b : Nat) : (op₂ b).spawnCount = s₂ := spawnCount_eq _ _ _ _ _ _ _ _; let N₁ := firePairWith N a₁.id b₁.id a₁.kind b₁.kind n; let N₂ := firePairWith N a₂.id b₂.id a₂.kind b₂.kind n
        let N₁' := firePairWith N₁ a₂.id b₂.id a₂.kind b₂.kind N₁.nextId; let N₂' := firePairWith N₂ a₁.id b₁.id a₁.kind b₁.kind N₂.nextId; refine ⟨N₁', N₂', .fire hAct2_1 hfeq₁₂, .fire hAct1_2 hfeq₂₁, ?_⟩
        have hWf₁' := step_preserves_wfNet N₁ N₁' hWf₁ (.fire hAct2_1 hfeq₁₂); let φ := swapBlocks n s₁ s₂; let ψ := swapBlocks n s₂ s₁; have hlt_a1 := hWf.agents_lt a₁ ha₁; have hlt_b1 := hWf.agents_lt b₁ hb₁
        have hlt_a2 := hWf.agents_lt a₂ ha₂; have hlt_b2 := hWf.agents_lt b₂ hb₂; have hfix_lt : ∀ x, x < n → φ x = x ∧ ψ x = x := fun x hx => ⟨by unfold φ swapBlocks; grind, by unfold ψ swapBlocks; grind⟩
        have hst1_n := classifyRule_struct a₁ b₁ n hAct₁.hne hlt_a1 hlt_b1; have hst2_n := classifyRule_struct a₂ b₂ n hAct₂.hne hlt_a2 hlt_b2
        have hst1_s2 := classifyRule_struct a₁ b₁ (n + s₂) hAct₁.hne (by omega) (by omega)
        have hN1'_a (x : Agent) : x ∈ N₁'.agents ↔ (x ∈ N.agents ∧ x.id ≠ a₁.id ∧ x.id ≠ b₁.id ∧ x.id ≠ a₂.id ∧ x.id ≠ b₂.id) ∨ x ∈ (op₁ n).spawned ∨ x ∈ (op₂ (n + s₁)).spawned := by
          simp only [N₁', N₁, op₁, op₂, s₁, firePairWith, mkNetFrom, List.mem_append, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
          refine ⟨fun h => by rcases h with ((⟨⟨hx, h1, h2⟩ | h1, h3, h4⟩) | h2) <;> grind, fun h => ?_⟩
          rcases h with ⟨hx, h1, h2, h3, h4⟩ | h1 | h2
          · exact .inl ⟨.inl ⟨hx, h1, h2⟩, h3, h4⟩
          · have := (hst1_n.2.1 x h1).1; exact .inl ⟨.inr h1, by omega, by omega⟩
          · exact .inr h2
        have hN2'_a (y : Agent) : y ∈ N₂'.agents ↔ (y ∈ N.agents ∧ y.id ≠ a₁.id ∧ y.id ≠ b₁.id ∧ y.id ≠ a₂.id ∧ y.id ≠ b₂.id) ∨ y ∈ (op₂ n).spawned ∨ y ∈ (op₁ (n + s₂)).spawned := by
          simp only [N₂', N₂, op₁, op₂, s₂, firePairWith, mkNetFrom, List.mem_append, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
          refine ⟨fun h => by rcases h with ((⟨⟨hy, h3, h4⟩ | h2, h1, h2'⟩) | h1) <;> grind, fun h => ?_⟩
          rcases h with ⟨hy, h1, h2, h3, h4⟩ | h2 | h1
          · exact .inl ⟨.inl ⟨hy, h3, h4⟩, h1, h2⟩
          · have := (hst2_n.2.1 y h2).1; exact .inl ⟨.inr h2, by omega, by omega⟩
          · exact .inr h1
        have hma : ∀ x ∈ N₁'.agents, ⟨φ x.id, x.kind⟩ ∈ N₂'.agents := fun x hx => by
          rw [hN2'_a]; rcases (hN1'_a x).1 hx with ⟨hxN, h1, h2, h3, h4⟩ | hsp1 | hsp2
          · rw [(hfix_lt x.id (hWf.agents_lt x hxN)).1]; exact .inl ⟨hxN, h1, h2, h3, h4⟩
          · exact .inr (.inr (spawned_shift (i' := a₁.id) (j' := b₁.id) (b' := n + s₂) (f := φ) (fun k hk => by unfold φ swapBlocks; grind) x hsp1))
          · exact .inr (.inl (spawned_shift (i' := a₂.id) (j' := b₂.id) (b' := n) (f := φ) (fun k hk => by have := hs2_c (n + s₁); unfold φ swapBlocks; grind) x hsp2))
        have hia : ∀ y ∈ N₂'.agents, ⟨ψ y.id, y.kind⟩ ∈ N₁'.agents := fun y hy => by
          rw [hN1'_a]; rcases (hN2'_a y).1 hy with ⟨hyN, h1, h2, h3, h4⟩ | hsp2 | hsp1
          · rw [(hfix_lt y.id (hWf.agents_lt y hyN)).2]; exact .inl ⟨hyN, h1, h2, h3, h4⟩
          · exact .inr (.inr (spawned_shift (i' := a₂.id) (j' := b₂.id) (b' := n + s₁) (f := ψ) (fun k hk => by unfold ψ swapBlocks; grind) y hsp2))
          · exact .inr (.inl (spawned_shift (i' := a₁.id) (j' := b₁.id) (b' := n) (f := ψ) (fun k hk => by have := hs1_c (n + s₂); unfold ψ swapBlocks; grind) y hsp1))
        refine AlphaEquiv.mkOfWf hWf₁' rfl φ ψ (fun p hp => (hfix_lt p.nodeId (hWf.free_spec p hp).2).1) (fun p hp => (hfix_lt p.nodeId (hWf.free_spec p hp).2).2)
          (fun x _ => swapBlocks_inv n s₁ s₂ x.id) (fun y _ => swapBlocks_inv n s₂ s₁ y.id) hma hia fun p hp => ?_
        have hmp := mapPort_mem_of_parts (N₁ := N₁') (N₂ := N₂') rfl (fun q hq => (hfix_lt q.nodeId (hWf.free_spec q hq).2).1) hma hp
        have hP1' : N₁'.partner p = (op₂ (n + s₁)).apply N₁.partner p := by unfold N₁' firePairWith at hp ⊢; rw [partner_mkNetFrom, ite_t hp]; rfl
        have hP2' : N₂'.partner (mapPort φ p) = (op₁ (n + s₂)).apply N₂.partner (mapPort φ p) := by unfold N₂' firePairWith at hmp ⊢; rw [partner_mkNetFrom, ite_t hmp]; rfl
        rw [hP1', hP2']; have hraw : ∀ (M : ICNet) (c d : Agent) (opM : RuleOp) (hWfM : WfNet M) (hcM : c ∈ M.agents) (hdM : d ∈ M.agents)
            (hnecd : c.id ≠ d.id) (hMeq : ∀ q ∈ livePorts M, M.partner q = opM.apply N.partner q)
            {x : PortRef} (hx : x ∈ livePorts (firePairWith M c.id d.id c.kind d.kind M.nextId)),
            (classifyRule c.id d.id c.kind d.kind M.nextId).apply M.partner x = (classifyRule c.id d.id c.kind d.kind M.nextId).apply (opM.apply N.partner) x := fun M c d opM hWfM hcM hdM hnecd hMeq x hx => by
          refine ruleOp_congr hMeq (fun q hq => (hWfM.partner_wf q hq).1) ?_
          cases hop : classifyRule c.id d.id c.kind d.kind M.nextId with
          | conj _ _ _ _ => exact fun hxnT => conj_rho_live hWfM hcM hdM hnecd hop hx hxnT
          | bridge bP =>
            have hst := (classifyRule_struct c d M.nextId hnecd (hWfM.agents_lt c hcM) (hWfM.agents_lt d hdM)).2.2; rw [hop] at hst; obtain ⟨hbnd, hbaux, _⟩ := hst
            refine ⟨fun y hy => ⟨((livePorts_split hWfM hcM hdM hnecd y).1).2 (.inr (.inr (.inr (List.mem_append.1 ((hbaux y).1 hy))))), ((swapList_wf hbnd).2 y hy).1⟩, ?_⟩
            unfold firePairWith at hx; rw [hop] at hx; exact ((livePorts_split hWfM hcM hdM hnecd x).1).2 (.inl (by simpa [livePorts, mkNetFrom, RuleOp.spawned] using hx))
        have hL := hraw N₁ a₂ b₂ (op₁ n) hWf₁ ha2_1 hb2_1 hAct₂.hne (fun q hq => by unfold N₁ firePairWith at hq ⊢; rw [partner_mkNetFrom, ite_t hq]) hp
        have hR := hraw N₂ a₁ b₁ (op₂ n) hWf₂ ha1_2 hb1_2 hAct₁.hne (fun q hq => by unfold N₂ firePairWith at hq ⊢; rw [partner_mkNetFrom, ite_t hq]) hmp
        change (op₂ (n + s₁)).apply N₁.partner p = _ at hL; change (op₁ (n + s₂)).apply N₂.partner (mapPort φ p) = _ at hR; rw [hL, hR]; have hφ_inj : ∀ x y, mapPort φ x = mapPort φ y → x = y := fun x y he => by
          have := congrArg (mapPort ψ) he; cases x; cases y; dsimp only [φ, ψ, mapPort] at this; rw [swapBlocks_inv, swapBlocks_inv] at this; exact this
        have hσ_φ := mapPort_partner_fixed hWf hφ_inj (fun x hx => (hfix_lt x hx).1)
        have hop_glob : ∀ (c d : Agent) (b₁ b₂ : Nat) (σ₁ σ₂ : PortRef → PortRef), c.id < n → d.id < n → (∀ k < (classifyRule c.id d.id c.kind d.kind b₁).spawnCount, φ (b₁ + k) = b₂ + k) →
            (∀ x, mapPort φ (σ₁ x) = σ₂ (mapPort φ x)) →
            ∀ x, mapPort φ ((classifyRule c.id d.id c.kind d.kind b₁).apply σ₁ x) = (classifyRule c.id d.id c.kind d.kind b₂).apply σ₂ (mapPort φ x) := by
          intro c d b₁ b₂ σ₁ σ₂ hlc hld hsh hσe x; have hfc := (hfix_lt c.id hlc).1; have hfd := (hfix_lt d.id hld).1
          have hmm : ∀ (ps : List (PortRef × PortRef)) (y : PortRef), y ∈ pairsDom ps ↔ mapPort φ y ∈ (pairsDom ps).map (mapPort φ) :=
            fun ps y => ⟨fun h => List.mem_map.2 ⟨y, h, rfl⟩, fun h => by obtain ⟨z, hz, he⟩ := List.mem_map.1 h; exact hφ_inj _ _ he ▸ hz⟩
          have hm := classified_map (ka := c.kind) (kb := d.kind) hfc hfd hsh; cases h1' : classifyRule c.id d.id c.kind d.kind b₁ <;> cases h2' : classifyRule c.id d.id c.kind d.kind b₂ <;> rw [h1', h2'] at hm
          · obtain ⟨rfl, rfl⟩ := hm; simp only [RuleOp.apply, pairsDom_map]; exact conj_transport (hmm _ x) (fun _ => swapList_map_inj hφ_inj _ x)
              (fun _ => by rw [swapList_map_inj hφ_inj, hσe, swapList_map_inj hφ_inj])
          · cases hm
          · cases hm
          · rename_i ps _; subst hm; simp only [RuleOp.apply, pairsDom_map]
            exact bridge_transport (D := fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial) (fun y _ => hmm ps y) (fun y _ => hσe y) (fun y _ => swapList_map_inj hφ_inj ps y) (by simp) trivial
        change mapPort φ ((classifyRule a₂.id b₂.id a₂.kind b₂.kind (n + s₁)).apply ((classifyRule a₁.id b₁.id a₁.kind b₁.kind n).apply N.partner) p) =
          (classifyRule a₁.id b₁.id a₁.kind b₁.kind (n + s₂)).apply ((classifyRule a₂.id b₂.id a₂.kind b₂.kind n).apply N.partner) (mapPort φ p)
        rw [hop_glob a₂ b₂ (n + s₁) n _ _ hlt_a2 hlt_b2 (fun k hk => by have := hs2_c (n + s₁); unfold φ swapBlocks; grind)
          (hop_glob a₁ b₁ n (n + s₂) N.partner N.partner hlt_a1 hlt_b1 (fun k hk => by unfold φ swapBlocks; grind) hσ_φ) p]
        change (op₂ n).apply ((op₁ (n + s₂)).apply N.partner) (mapPort φ p) = (op₁ (n + s₂)).apply ((op₂ n).apply N.partner) (mapPort φ p); let q := mapPort φ p
        have hq_no : q.nodeId ≠ a₁.id ∧ q.nodeId ≠ b₁.id ∧ q.nodeId ≠ a₂.id ∧ q.nodeId ≠ b₂.id := by
          simp only [livePorts, List.mem_append, List.mem_flatMap] at hmp; rcases hmp with ⟨y, hy, hqy⟩ | hqf
          · rw [mem_agentPorts_nodeId hqy]; rcases (hN2'_a y).1 hy with ⟨_, h1, h2, h3, h4⟩ | h2 | h1
            · exact ⟨h1, h2, h3, h4⟩
            · have := (hst2_n.2.1 y h2).1; omega
            · have := (hst1_s2.2.1 y h1).1; omega
          · exact ⟨hWf.free_disj q hqf a₁ ha₁, hWf.free_disj q hqf b₁ hb₁, hWf.free_disj q hqf a₂ ha₂, hWf.free_disj q hqf b₂ hb₂⟩
        obtain ⟨v₁, removed₁, touch₁⟩ := wiring_bounds hWf ha₁ hb₁ hAct₁.hne (Nat.le_add_right n s₂); obtain ⟨v₂, removed₂, touch₂⟩ := wiring_bounds hWf ha₂ hb₂ hAct₂.hne (Nat.le_refl n)
        apply wires_commute hWf v₁ v₂ _ (fun h => by have := removed₁ q h; omega) (fun h => by have := removed₂ q h; omega)
        intro x h₁ h₂; have := touch₁ x h₁; have := touch₂ x h₂; change _ ∨ _ ∨ (_ ∧ x.nodeId < n + s₂) at this; omega

/-! ## 8. Multi-Step Church–Rosser Confluence, Unique Normal Forms & Verified Reducer -/
theorem wfNet_strip_confluence (N N₁ M : ICNet) (hWf : WfNet N) (hStep : Step N N₁) (hSteps : Steps N M) : ∃ W₁ W₂, Steps N₁ W₁ ∧ Steps M W₂ ∧ AlphaEquiv W₁ W₂ := by
  induction hSteps generalizing N₁ with
  | refl => exact ⟨N₁, N₁, .refl _, .single hStep, AlphaEquiv.refl _⟩
  | next hStep2 hRest ih =>
    have hWf₁ := step_preserves_wfNet _ _ hWf hStep; have hWf₂ := step_preserves_wfNet _ _ hWf hStep2; rcases wfNet_strong_diamond _ _ _ hWf hStep hStep2 with hα | ⟨N₁', N₂', h1', h2', hα⟩
    · obtain ⟨W₁, hW1, hα'⟩ := alphaEquiv_steps_simulates _ _ _ hWf₂ hWf₁ hα.symm hRest; exact ⟨W₁, _, hW1, .refl _, hα'.symm⟩
    · obtain ⟨U₁, U₂, hU1, hU2, hαU⟩ := ih N₂' hWf₂ h2'; obtain ⟨W₁, hW1, hαW⟩ := alphaEquiv_steps_simulates _ _ _ (step_preserves_wfNet _ _ hWf₂ h2') (step_preserves_wfNet _ _ hWf₁ h1') hα.symm hU1
      exact ⟨W₁, U₂, .next h1' hW1, hU2, hαW.symm.trans hαU⟩
theorem wfNet_church_rosser_confluent (N M₁ M₂ : ICNet) (hWf : WfNet N) (h₁ : Steps N M₁) (h₂ : Steps N M₂) : ∃ W₁ W₂, Steps M₁ W₁ ∧ Steps M₂ W₂ ∧ AlphaEquiv W₁ W₂ := by
  induction h₁ generalizing M₂ with
  | refl => exact ⟨M₂, M₂, h₂, .refl _, AlphaEquiv.refl _⟩
  | next hStep _ ih =>
    have hWf₁ := step_preserves_wfNet _ _ hWf hStep; obtain ⟨U₁, U₂, hU1, hU2, hαU⟩ := wfNet_strip_confluence _ _ _ hWf hStep h₂
    obtain ⟨V₁, V₂, hV1, hV2, hαV⟩ := ih U₁ hWf₁ hU1; obtain ⟨W₂, hW2, hαW⟩ := alphaEquiv_steps_simulates _ _ _ (steps_preserves_wfNet _ _ hWf₁ hU1)
      (steps_preserves_wfNet _ _ (steps_preserves_wfNet _ _ hWf h₂) hU2) hαU hV2
    exact ⟨V₁, W₂, hV1, hU2.trans hW2, hαV.trans hαW⟩
def IsNormalForm (V : ICNet) : Prop := ¬ ∃ V', Step V V'
@[expose] def isNormalFormB (N : ICNet) : Bool := (activePairs N).isEmpty
theorem isNormalFormB_iff (N : ICNet) (hWf : WfNet N) : isNormalFormB N = true ↔ IsNormalForm N := by
  unfold isNormalFormB IsNormalForm; cases hap : activePairs N with
  | nil =>
    simp only [List.isEmpty]; refine ⟨fun _ ⟨_, hStep⟩ => ?_, fun _ => trivial⟩; cases hStep with
    | @fire i j hAct _ =>
      rcases Nat.lt_or_gt_of_ne hAct.hne with hlt | hgt
      · have hm := mem_activePairs_iff.2 ⟨hAct, hlt⟩; rw [hap] at hm; cases hm
      · have hm := mem_activePairs_iff.2 ⟨hAct.symm hWf, hgt⟩; rw [hap] at hm; cases hm
  | cons p _ =>
    simp only [List.isEmpty]; obtain ⟨hAct, _⟩ := mem_activePairs_iff.1 (hap ▸ List.mem_cons_self)
    obtain ⟨_, _, _, _, _, _, hfeq⟩ := fireActivePair_of_active hWf hAct; exact ⟨(fun h => by cases h), fun hnf => absurd ⟨_, .fire hAct hfeq⟩ hnf⟩
theorem wfNet_unique_normal_form (N V₁ V₂ : ICNet) (hWf : WfNet N) (h₁ : Steps N V₁) (h₂ : Steps N V₂) (hnf₁ : IsNormalForm V₁) (hnf₂ : IsNormalForm V₂) : AlphaEquiv V₁ V₂ := by
  obtain ⟨W₁, W₂, hW1, hW2, hα⟩ := wfNet_church_rosser_confluent N V₁ V₂ hWf h₁ h₂; have he1 : V₁ = W₁ := by cases hW1 with | refl => rfl | next s _ => exact absurd ⟨_, s⟩ hnf₁
  have he2 : V₂ = W₂ := by cases hW2 with | refl => rfl | next s _ => exact absurd ⟨_, s⟩ hnf₂
  rwa [← he1, ← he2] at hα
@[expose] def evalNet : Nat → ICNet → ICNet
  | 0, N => N
  | fuel + 1, N => match activePairs N with
    | [] => N
    | (i, j) :: _ => match fireActivePair N i j with | some N' => evalNet fuel N' | none => N
theorem evalNet_sound (fuel : Nat) (N : ICNet) (hWf : WfNet N) : Steps N (evalNet fuel N) ∧ WfNet (evalNet fuel N) := by
  induction fuel generalizing N with
  | zero => exact ⟨.refl N, hWf⟩
  | succ fuel ih =>
    unfold evalNet; cases hap : activePairs N with
    | nil => exact ⟨.refl N, hWf⟩
    | cons p _ =>
      obtain ⟨i, j⟩ := p; dsimp only; obtain ⟨hAct, _⟩ := mem_activePairs_iff.1 (hap ▸ List.mem_cons_self); cases hf : fireActivePair N i j with
      | none => exact ⟨.refl N, hWf⟩
      | some N' => dsimp only; have hStep : Step N N' := .fire hAct hf; obtain ⟨hR, hW⟩ := ih N' (step_preserves_wfNet N N' hWf hStep); exact ⟨.next hStep hR, hW⟩

/-! ## 9. Constructive Inhabitedness & Concrete Witnesses -/
def witnessTwoRedexNet : ICNet :=
  { agents := [⟨0, .era⟩, ⟨1, .era⟩, ⟨2, .con⟩, ⟨3, .dup 0⟩], freePorts := [⟨10, 0⟩, ⟨11, 0⟩, ⟨12, 0⟩, ⟨13, 0⟩]
    links := [(⟨0, 0⟩, ⟨1, 0⟩), (⟨1, 0⟩, ⟨0, 0⟩), (⟨2, 0⟩, ⟨3, 0⟩), (⟨3, 0⟩, ⟨2, 0⟩), (⟨2, 1⟩, ⟨10, 0⟩), (⟨10, 0⟩, ⟨2, 1⟩), (⟨2, 2⟩, ⟨11, 0⟩), (⟨11, 0⟩, ⟨2, 2⟩),
      (⟨3, 1⟩, ⟨12, 0⟩), (⟨12, 0⟩, ⟨3, 1⟩), (⟨3, 2⟩, ⟨13, 0⟩), (⟨13, 0⟩, ⟨3, 2⟩)], nextId := 14 }

end Obend.Hardware.IC
end
