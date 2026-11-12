module
/-
# Obend.Hardware.HvmConfluence — commuting interactions, and Δ-nets

Two parts.

## Part 1: interactions of `Hvm.Step` that commute

`Obend.Hardware.Hvm` says of `Step`: "that HVM2's own schedule reaches the same normal form is the
strong confluence the paper claims, not proved here". This part proves the commutations that do
not need a notion of equality up to renaming:

* `Fire book fresh r ns`: the redex `r` fires to `ns`, allocating the variables `fresh`. It covers
  every rule of `Step` but LINK (the local rules in either orientation, the `REF` copy, CALL, COMM).
  `Fire.toSteps`: it is a reduction wherever the redex sits in the bag, when `fresh` is fresh there.
* `diamond_of_disjoint`: two firings at two positions of the bag, each one's fresh variables apart
  from the configuration and from the other's outcome, commute to the same configuration.
* `diamond_link_disjoint`: two LINKs of different variables, neither occurring in the other's tree,
  commute to the same configuration (`subst_one_comm`).
* `batch_schedule_invariant`: a batch of pairwise independent firings (`Plan.Indep`), fired in any
  order whatever (`PlanSteps`), ends at one configuration, `Plan.settle`.

Not proved: a LINK against an interaction that reads the linked variable (`num ~ opr (var x) b`
after `x` is linked to a number joins only after a second OPER), and confluence of the whole
relation, which holds only up to the names CALL and COMM allocate.

## Part 2: Δ-nets (Salvadori, arXiv:2505.20314)

Three agents: the fan, the eraser, and the replicator, which has a level, any number of auxiliary
ports and an integer level delta per port. The rules, as the paper states them: equal agents
annihilate, and two replicators are equal exactly when level and deltas agree
(`replicatorsAnnihilate`; a port's delta is one entry, so the port count agrees too); an eraser
erases; a fan and a replicator commute, the replicator copied unchanged; two replicators of
different levels commute, the lower copying the higher once per port and adding that port's delta to
the copy's level (`shiftRepLevel`). Replicators of one level that differ are stuck: the paper gives
them no rule. `lit` is a fourth, nullary agent for observable results (as HVM2's numbers: it copies
itself into whatever it meets).

The translation of λ-terms follows the paper's Figure 5: an application's argument is one level
deeper, a binder's replicator is one level above its abstraction, a port's delta is the occurrence's
level minus the replicator's, and a replicator with one port of delta 0 is a wire.

* `normalize_sound`: the executable head-redex reducer is a reduction of the relation.
* `deltaNet_idId_reduces`: `(λid. id id n) (λx. x)`, a duplicated higher-order λ, reduces to `n`.
* `hvmLower_refuses_lambda_argument`: `Hvm.Lower` refuses every `(λx. b) (λy. a)`, at every sort.
* `deltaStep_preserves_linmem`: the wires of a run are a valid linear memory
  (`Obend.SymbolicZk.LinMem`): a wire id is never reused, so each wire is produced once and consumed
  once, and the cells left are the wires of the configuration reached (`wireLedger_final`).

The paper's canonicalization (merging unpaired replicators, the leftmost-outermost order it needs
for optimality) is not modelled.
-/
public import Obend.Hardware.Hvm.Model
public import Obend.Hardware.Hvm.Lower
public import Obend.SymbolicZk.LinMem
public import Lean
public section

namespace Obend.Hardware.Delta
open Lean Elab Tactic Meta in
/-- Close `a = b` with `Eq.refl a`, leaving the conversion to the kernel. The elaborator's own
unifier is not asked: on a long run of an interpreter it re-evaluates what the kernel shares. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  match (← whnfR (← g.getType)).eq? with
  | some (_, lhs, _) => g.assign (← mkEqRefl lhs)
  | none => throwError "kernel_rfl: the goal is not an equality"
end Obend.Hardware.Delta

namespace Obend.Hardware.Hvm
set_option autoImplicit false

/-! ## Part 1. Commuting interactions of `Step` -/

/-- `r` fires to `ns`, allocating the variables `fresh`: every rule of `Step` but LINK. -/
inductive Fire (book : List HDef) : List Nat → Redex → List Redex → Prop where
  | rule {a b : HTree} {ns : List Redex} : localRule a b = some ns → Fire book [] (a, b) ns
  | ruleSwap {a b : HTree} {ns : List Redex} : localRule b a = some ns → Fire book [] (a, b) ns
  | copyRef {f : String} {a b : HTree} {d : HDef} :
      book.find? (·.name == f) = some d → d.safe = true →
      Fire book [] (.ref f, .dup a b) [(.ref f, a), (.ref f, b)]
  | call {f : String} {t : HTree} {d : HDef} (r : Nat → Nat) :
      book.find? (·.name == f) = some d →
      (∃ k a b, t.bin? = some (k, a, b) ∧ k ≠ .dup) →
      (∀ u ∈ d.vars, ∀ v ∈ d.vars, r u = r v → u = v) →
      Fire book (d.vars.map r) (.ref f, t) ((d.root.rename r, t) :: d.bag.map (Redex.rename r))
  | comm {a b a1 a2 b1 b2 : HTree} {ka kb : BinKind} {v0 v1 v2 v3 : Nat} :
      a.bin? = some (ka, a1, a2) → b.bin? = some (kb, b1, b2) → ka ≠ kb →
      [v0, v1, v2, v3].Nodup →
      Fire book [v0, v1, v2, v3] (a, b)
        [(mkBin kb (.var v0) (.var v1), a1), (mkBin kb (.var v2) (.var v3), a2),
          (mkBin ka (.var v0) (.var v2), b1), (mkBin ka (.var v1) (.var v3), b2)]

theorem mem_bagVars_append {v : Nat} {l₁ l₂ : List Redex} :
    v ∈ bagVars (l₁ ++ l₂) ↔ v ∈ bagVars l₁ ∨ v ∈ bagVars l₂ := by
  simp [bagVars]

theorem mem_bagVars_cons {v : Nat} {r : Redex} {l : List Redex} :
    v ∈ bagVars (r :: l) ↔ v ∈ redexVars r ∨ v ∈ bagVars l := by
  simp [bagVars]

theorem mem_cfgVars {v : Nat} {root : HTree} {bag : List Redex} :
    v ∈ Cfg.vars ⟨root, bag⟩ ↔ v ∈ root.vars ∨ v ∈ bagVars bag := by
  simp [Cfg.vars]

theorem mem_bagVars_of_mem {v : Nat} {r : Redex} {l : List Redex} (hr : r ∈ l)
    (hv : v ∈ redexVars r) : v ∈ bagVars l := by
  simp only [bagVars, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨r, hr, rfl⟩, hv⟩

/-- **A firing is a reduction** at any position of the bag where its variables are fresh. -/
theorem Fire.toSteps {book : List HDef} {fresh : List Nat} {r : Redex} {ns : List Redex}
    (h : Fire book fresh r ns) (root : HTree) (pre post : List Redex)
    (hf : ∀ v ∈ fresh, v ∉ Cfg.vars ⟨root, pre ++ r :: post⟩) :
    Steps book ⟨root, pre ++ r :: post⟩ ⟨root, pre ++ ns ++ post⟩ := by
  cases h with
  | rule h => exact .single (.rule h)
  | ruleSwap h => exact .next .swap (.single (.rule h))
  | copyRef h1 h2 => exact .single (.copyRef h1 h2)
  | call r h1 h2 h3 =>
    have := Step.call (book := book) (root := root) (pre := pre) (post := post) r h1 h2 h3
      (fun u hu => hf _ (List.mem_map.2 ⟨u, hu, rfl⟩))
    exact .single this
  | comm h1 h2 h3 h4 => exact .single (.comm h1 h2 h3 h4 hf)

/-- **Strong diamond on disjoint redexes.** Two firings at two positions of one bag, each one's
fresh variables apart from the configuration and from the other's outcome: either may go first, and
the other then fires to the same configuration. -/
theorem diamond_of_disjoint {book : List HDef} {f₁ f₂ : List Nat} {r₁ r₂ : Redex}
    {ns₁ ns₂ : List Redex} (root : HTree) (pre mid post : List Redex)
    (h₁ : Fire book f₁ r₁ ns₁) (h₂ : Fire book f₂ r₂ ns₂)
    (hc₁ : ∀ v ∈ f₁, v ∉ Cfg.vars ⟨root, pre ++ r₁ :: (mid ++ r₂ :: post)⟩)
    (hc₂ : ∀ v ∈ f₂, v ∉ Cfg.vars ⟨root, pre ++ r₁ :: (mid ++ r₂ :: post)⟩)
    (hx₁ : ∀ v ∈ f₁, v ∉ bagVars ns₂) (hx₂ : ∀ v ∈ f₂, v ∉ bagVars ns₁) :
    Steps book ⟨root, pre ++ r₁ :: (mid ++ r₂ :: post)⟩ ⟨root, pre ++ ns₁ ++ (mid ++ r₂ :: post)⟩ ∧
    Steps book ⟨root, pre ++ r₁ :: (mid ++ r₂ :: post)⟩ ⟨root, pre ++ r₁ :: (mid ++ ns₂ ++ post)⟩ ∧
    Steps book ⟨root, pre ++ ns₁ ++ (mid ++ r₂ :: post)⟩ ⟨root, pre ++ ns₁ ++ (mid ++ ns₂ ++ post)⟩ ∧
    Steps book ⟨root, pre ++ r₁ :: (mid ++ ns₂ ++ post)⟩ ⟨root, pre ++ ns₁ ++ (mid ++ ns₂ ++ post)⟩ := by
  refine ⟨h₁.toSteps root pre _ hc₁, ?_, ?_, ?_⟩
  · have := h₂.toSteps root (pre ++ r₁ :: mid) post (by
      intro v hv hm
      refine hc₂ v hv ?_
      simpa only [List.append_assoc, List.cons_append] using hm)
    simpa only [List.append_assoc, List.cons_append] using this
  · have := h₂.toSteps root (pre ++ ns₁ ++ mid) post (by
      intro v hv hm
      simp only [mem_cfgVars, mem_bagVars_append, mem_bagVars_cons] at hm
      have hc := hc₂ v hv
      simp only [mem_cfgVars, mem_bagVars_append, mem_bagVars_cons] at hc
      have hx := hx₂ v hv
      grind)
    simpa only [List.append_assoc, List.cons_append] using this
  · exact h₁.toSteps root pre _ (by
      intro v hv hm
      simp only [mem_cfgVars, mem_bagVars_append, mem_bagVars_cons] at hm
      have hc := hc₁ v hv
      simp only [mem_cfgVars, mem_bagVars_append, mem_bagVars_cons] at hc
      have hx := hx₁ v hv
      grind)

/-! ### Two LINKs commute -/

theorem subst_one_of_not_mem (x : Nat) (u : HTree) :
    ∀ t : HTree, x ∉ t.vars → t.subst (one x u) = t := by
  intro t
  induction t with
  | var n =>
    intro h
    have : n ≠ x := fun e => h (by simp [HTree.vars, e])
    simp [HTree.subst, one, this]
  | era => intro _; rfl
  | ref f => intro _; rfl
  | num v => intro _; rfl
  | con a b iha ihb | dup a b iha ihb | opr a b iha ihb | swi a b iha ihb =>
    intro h
    simp only [HTree.vars, List.mem_append, not_or] at h
    simp only [HTree.subst, iha h.1, ihb h.2]

/-- Substitutions of two different variables, neither in the other's tree, commute. -/
theorem subst_one_comm {x₁ x₂ : Nat} {t₁ t₂ : HTree} (hne : x₁ ≠ x₂) (h₁ : x₁ ∉ t₂.vars)
    (h₂ : x₂ ∉ t₁.vars) :
    ∀ t : HTree, (t.subst (one x₁ t₁)).subst (one x₂ t₂) = (t.subst (one x₂ t₂)).subst (one x₁ t₁) := by
  intro t
  induction t with
  | var n =>
    by_cases e1 : n = x₁
    · subst e1
      have a1 : (HTree.var n).subst (one n t₁) = t₁ := by simp [HTree.subst, one]
      have a2 : (HTree.var n).subst (one x₂ t₂) = .var n := by simp [HTree.subst, one, hne]
      rw [a1, a2, a1, subst_one_of_not_mem x₂ t₂ t₁ h₂]
    · by_cases e2 : n = x₂
      · subst e2
        have a1 : (HTree.var n).subst (one n t₂) = t₂ := by simp [HTree.subst, one]
        have a2 : (HTree.var n).subst (one x₁ t₁) = .var n := by simp [HTree.subst, one, e1]
        rw [a2, a1, subst_one_of_not_mem x₁ t₁ t₂ h₁]
      · have a1 : (HTree.var n).subst (one x₁ t₁) = .var n := by simp [HTree.subst, one, e1]
        have a2 : (HTree.var n).subst (one x₂ t₂) = .var n := by simp [HTree.subst, one, e2]
        rw [a1, a2, a1]
  | era => rfl
  | ref f => rfl
  | num v => rfl
  | con a b iha ihb | dup a b iha ihb | opr a b iha ihb | swi a b iha ihb =>
    simp only [HTree.subst, iha, ihb]

theorem redex_subst_comm {x₁ x₂ : Nat} {t₁ t₂ : HTree} (hne : x₁ ≠ x₂) (h₁ : x₁ ∉ t₂.vars)
    (h₂ : x₂ ∉ t₁.vars) (r : Redex) :
    (r.subst (one x₁ t₁)).subst (one x₂ t₂) = (r.subst (one x₂ t₂)).subst (one x₁ t₁) := by
  simp only [Redex.subst, subst_one_comm hne h₁ h₂]

/-- **Two LINKs commute.** Wires `x₁ ~ t₁` and `x₂ ~ t₂` at two positions of the bag, with
`x₁ ≠ x₂` and neither variable in the other's tree: either LINK may go first, and the other then
reaches the same configuration. -/
theorem diamond_link_disjoint (book : List HDef) (root : HTree) (pre mid post : List Redex)
    {x₁ x₂ : Nat} {t₁ t₂ : HTree} (hne : x₁ ≠ x₂) (h₁ : x₁ ∉ t₂.vars) (h₂ : x₂ ∉ t₁.vars) :
    Step book ⟨root, pre ++ (.var x₁, t₁) :: (mid ++ (.var x₂, t₂) :: post)⟩
      ⟨root.subst (one x₁ t₁), (pre ++ (mid ++ (.var x₂, t₂) :: post)).map (Redex.subst (one x₁ t₁))⟩ ∧
    Step book ⟨root, pre ++ (.var x₁, t₁) :: (mid ++ (.var x₂, t₂) :: post)⟩
      ⟨root.subst (one x₂ t₂), (pre ++ (.var x₁, t₁) :: (mid ++ post)).map (Redex.subst (one x₂ t₂))⟩ ∧
    Step book
      ⟨root.subst (one x₁ t₁), (pre ++ (mid ++ (.var x₂, t₂) :: post)).map (Redex.subst (one x₁ t₁))⟩
      ⟨(root.subst (one x₁ t₁)).subst (one x₂ t₂),
        ((pre ++ (mid ++ post)).map (Redex.subst (one x₁ t₁))).map (Redex.subst (one x₂ t₂))⟩ ∧
    Step book
      ⟨root.subst (one x₂ t₂), (pre ++ (.var x₁, t₁) :: (mid ++ post)).map (Redex.subst (one x₂ t₂))⟩
      ⟨(root.subst (one x₁ t₁)).subst (one x₂ t₂),
        ((pre ++ (mid ++ post)).map (Redex.subst (one x₁ t₁))).map (Redex.subst (one x₂ t₂))⟩ := by
  have hne' : x₂ ≠ x₁ := fun e => hne e.symm
  have keep₂ : Redex.subst (one x₁ t₁) (.var x₂, t₂) = (.var x₂, t₂) := by
    simp [Redex.subst, HTree.subst, one, hne', subst_one_of_not_mem x₁ t₁ t₂ h₁]
  have keep₁ : Redex.subst (one x₂ t₂) (.var x₁, t₁) = (.var x₁, t₁) := by
    simp [Redex.subst, HTree.subst, one, hne, subst_one_of_not_mem x₂ t₂ t₁ h₂]
  refine ⟨.link, ?_, ?_, ?_⟩
  · have := Step.link (book := book) (root := root) (pre := pre ++ (.var x₁, t₁) :: mid)
      (post := post) (x := x₂) (t := t₂)
    simpa only [List.append_assoc, List.cons_append] using this
  · have := Step.link (book := book) (root := root.subst (one x₁ t₁))
      (pre := (pre ++ mid).map (Redex.subst (one x₁ t₁)))
      (post := post.map (Redex.subst (one x₁ t₁))) (x := x₂) (t := t₂)
    simpa only [List.map_append, List.map_cons, keep₂, List.append_assoc] using this
  · have := Step.link (book := book) (root := root.subst (one x₂ t₂))
      (pre := pre.map (Redex.subst (one x₂ t₂)))
      (post := (mid ++ post).map (Redex.subst (one x₂ t₂))) (x := x₁) (t := t₁)
    have e : ∀ l : List Redex, (l.map (Redex.subst (one x₂ t₂))).map (Redex.subst (one x₁ t₁)) =
        (l.map (Redex.subst (one x₁ t₁))).map (Redex.subst (one x₂ t₂)) := by
      intro l
      simp only [List.map_map]
      refine List.map_congr_left fun r _ => ?_
      exact (redex_subst_comm hne h₁ h₂ r).symm
    rw [subst_one_comm hne h₁ h₂ root, ← e]
    simpa only [List.map_append, List.map_cons, keep₁, List.append_assoc] using this

/-! ### A batch of independent firings, in any order -/

/-- An entry of a batch: a redex, and the firing chosen for it (its fresh variables and its
outcome), or none. -/
abbrev PlanEntry := Redex × Option (List Nat × List Redex)

/-- A batch over a segment of the bag. -/
abbrev Plan := List PlanEntry

/-- The bag segment a plan stands for. -/
@[expose] def Plan.bag (p : Plan) : List Redex := p.map (·.1)

/-- What an entry is once fired. -/
@[expose] def PlanEntry.outcome : PlanEntry → Plan
  | (r, none) => [(r, none)]
  | (_, some (_, ns)) => ns.map fun n => (n, none)

/-- The plan with every chosen firing done. -/
@[expose] def Plan.settle (p : Plan) : Plan := p.flatMap PlanEntry.outcome

@[expose] def PlanEntry.fresh : PlanEntry → List Nat
  | (_, none) => []
  | (_, some (f, _)) => f

/-- The variables an entry touches: its redex's and its outcome's. -/
@[expose] def PlanEntry.vars : PlanEntry → List Nat
  | (r, none) => redexVars r
  | (r, some (_, ns)) => redexVars r ++ bagVars ns

/-- One firing of the batch, at any position. -/
inductive PlanStep : Plan → Plan → Prop where
  | fire (A B : Plan) (r : Redex) (f : List Nat) (ns : List Redex) :
      PlanStep (A ++ (r, some (f, ns)) :: B) (A ++ ns.map (fun n => (n, none)) ++ B)

/-- A schedule: firings of the batch in any order. -/
inductive PlanSteps : Plan → Plan → Prop where
  | refl (p : Plan) : PlanSteps p p
  | next {p q s : Plan} : PlanStep p q → PlanSteps q s → PlanSteps p s

/-- The batch is independent: each chosen firing is a firing whose fresh variables are apart from
the rest of the configuration (`base`) and from its own redex, and any two entries are apart: the
fresh variables of each are not among the variables the other touches. -/
structure Plan.Indep (book : List HDef) (base : List Nat) (p : Plan) : Prop where
  fires : ∀ r f ns, (r, some (f, ns)) ∈ p → Fire book f r ns ∧ ∀ v ∈ f, v ∉ base ∧ v ∉ redexVars r
  apart : p.Pairwise fun e e' => (∀ v ∈ e.fresh, v ∉ e'.vars) ∧ (∀ v ∈ e'.fresh, v ∉ e.vars)

theorem settle_fired (ns : List Redex) :
    Plan.settle (ns.map fun n => ((n, none) : PlanEntry)) = ns.map fun n => (n, none) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [Plan.settle, List.map_cons, List.flatMap_cons, PlanEntry.outcome] at ih ⊢
    rw [ih]
    rfl

theorem PlanStep.settle_eq {p q : Plan} (h : PlanStep p q) : q.settle = p.settle := by
  cases h with
  | fire A B r f ns =>
    have := settle_fired ns
    simp only [Plan.settle] at this
    simp only [Plan.settle, List.flatMap_append, List.flatMap_cons, PlanEntry.outcome, this,
      List.append_assoc]

theorem settle_of_done : ∀ (p : Plan), (∀ e ∈ p, e.2 = none) → p.settle = p
  | [], _ => rfl
  | (r, none) :: p, h => by
    have := settle_of_done p fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [Plan.settle] at this
    simp only [Plan.settle, List.flatMap_cons, PlanEntry.outcome, this, List.singleton_append]
  | (r, some x) :: p, h => by
    have := h _ List.mem_cons_self
    cases this

theorem pairwise_of_all {α : Type} {R : α → α → Prop} (h : ∀ a b, R a b) :
    ∀ l : List α, l.Pairwise R
  | [] => .nil
  | _ :: l => .cons (fun b _ => h _ b) (pairwise_of_all h l)

theorem fresh_fired (n : Redex) : PlanEntry.fresh ((n, none) : PlanEntry) = [] := rfl

theorem pairwise_replace {α : Type} {R : α → α → Prop} {A B X : List α} {e : α}
    (h : (A ++ e :: B).Pairwise R) (hX : X.Pairwise R) (hl : ∀ a, R a e → ∀ x ∈ X, R a x)
    (hr : ∀ b, R e b → ∀ x ∈ X, R x b) : (A ++ X ++ B).Pairwise R := by
  obtain ⟨hA, heB, hAeB⟩ := List.pairwise_append.1 h
  obtain ⟨heB', hB⟩ := List.pairwise_cons.1 heB
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hA, hX, fun a ha x hx =>
    hl a (hAeB a ha e List.mem_cons_self) x hx⟩, hB, ?_⟩
  intro a ha b hb
  rcases List.mem_append.1 ha with ha | ha
  · exact hAeB a ha b (List.mem_cons_of_mem _ hb)
  · exact hr b (heB' b hb) a ha

/-- A firing leaves the rest of the batch independent. -/
theorem PlanStep.indep {book : List HDef} {base : List Nat} {p q : Plan}
    (hi : Plan.Indep book base p) (h : PlanStep p q) : Plan.Indep book base q := by
  cases h with
  | fire A B r f ns =>
    constructor
    · intro r' f' ns' hm
      refine hi.fires r' f' ns' ?_
      simp only [List.mem_append, List.mem_map, List.mem_cons] at hm ⊢
      rcases hm with (hm | ⟨n, _, hn⟩) | hm
      · exact Or.inl hm
      · cases hn
      · exact Or.inr (Or.inr hm)
    · refine pairwise_replace hi.apart ?_ ?_ ?_
      · refine List.pairwise_map.2 (pairwise_of_all ?_ _)
        intro a b
        rw [fresh_fired, fresh_fired]
        exact ⟨fun v hv => absurd hv List.not_mem_nil, fun v hv => absurd hv List.not_mem_nil⟩
      · intro a ha x hx
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
        rw [fresh_fired]
        refine ⟨fun v hv hm => ha.1 v hv ?_, fun v hv => absurd hv List.not_mem_nil⟩
        exact List.mem_append_right _ (mem_bagVars_of_mem hn hm)
      · intro b hb x hx
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
        rw [fresh_fired]
        refine ⟨fun v hv => absurd hv List.not_mem_nil, fun v hv hm => hb.2 v hv ?_⟩
        exact List.mem_append_right _ (mem_bagVars_of_mem hn hm)

theorem mem_planBag_vars {v : Nat} : ∀ {A : Plan}, v ∈ bagVars (Plan.bag A) → ∃ e ∈ A, v ∈ e.vars
  | [], h => by simp [Plan.bag, bagVars] at h
  | e :: A, h => by
    have h' : v ∈ bagVars (e.1 :: Plan.bag A) := h
    rw [mem_bagVars_cons] at h'
    rcases h' with h' | h'
    · refine ⟨e, List.mem_cons_self, ?_⟩
      obtain ⟨r, o⟩ := e
      cases o with
      | none => exact h'
      | some x => exact List.mem_append_left _ h'
    · obtain ⟨e', he', hv⟩ := mem_planBag_vars h'
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

theorem planBag_fired (ns : List Redex) : Plan.bag (ns.map fun n => ((n, none) : PlanEntry)) = ns := by
  simp only [Plan.bag, List.map_map]
  exact List.map_id _

/-- A firing of the batch is a reduction of the configuration around it. -/
theorem PlanStep.toSteps {book : List HDef} {root : HTree} {pre post : List Redex} {p q : Plan}
    (hi : Plan.Indep book (root.vars ++ bagVars pre ++ bagVars post) p) (h : PlanStep p q) :
    Steps book ⟨root, pre ++ p.bag ++ post⟩ ⟨root, pre ++ q.bag ++ post⟩ := by
  cases h with
  | fire A B r f ns =>
    obtain ⟨hfire, hbase⟩ := hi.fires r f ns (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨_, heB, hAeB⟩ := List.pairwise_append.1 hi.apart
    obtain ⟨heB', _⟩ := List.pairwise_cons.1 heB
    have := hfire.toSteps root (pre ++ Plan.bag A) (Plan.bag B ++ post) (by
      intro v hv hm
      simp only [mem_cfgVars, mem_bagVars_append, mem_bagVars_cons] at hm
      have hb := hbase v hv
      simp only [List.mem_append, not_or] at hb
      rcases hm with hm | (hm | hm) | hm | hm | hm
      · exact hb.1.1.1 hm
      · exact hb.1.1.2 hm
      · obtain ⟨e, he, hve⟩ := mem_planBag_vars hm
        exact (hAeB e he _ List.mem_cons_self).2 v hv hve
      · exact hb.2 hm
      · obtain ⟨e, he, hve⟩ := mem_planBag_vars hm
        exact (heB' e he).1 v hv hve
      · exact hb.1.2 hm)
    have e1 : pre ++ Plan.bag (A ++ (r, some (f, ns)) :: B) ++ post =
        pre ++ Plan.bag A ++ r :: (Plan.bag B ++ post) := by
      simp only [Plan.bag, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    have e2 : pre ++ Plan.bag (A ++ ns.map (fun n => ((n, none) : PlanEntry)) ++ B) ++ post =
        pre ++ Plan.bag A ++ ns ++ (Plan.bag B ++ post) := by
      have := planBag_fired ns
      simp only [Plan.bag] at this
      simp only [Plan.bag, List.map_append, this, List.append_assoc]
    rw [e1, e2]
    exact this

/-- **Schedule invariance of a batch.** Independent firings, fired in any order until none is
left, reach one configuration: the plan settled. -/
theorem batch_schedule_invariant {book : List HDef} {root : HTree} {pre post : List Redex}
    {p q : Plan} (hs : PlanSteps p q)
    (hi : Plan.Indep book (root.vars ++ bagVars pre ++ bagVars post) p)
    (hdone : ∀ e ∈ q, e.2 = none) :
    q = p.settle ∧
      Steps book ⟨root, pre ++ p.bag ++ post⟩ ⟨root, pre ++ p.settle.bag ++ post⟩ := by
  induction hs with
  | refl p =>
    rw [settle_of_done p hdone]
    exact ⟨rfl, .refl _⟩
  | next hstep _ ih =>
    obtain ⟨hq, hsteps⟩ := ih (hstep.indep hi) hdone
    rw [hstep.settle_eq] at hq hsteps
    exact ⟨hq, (hstep.toSteps hi).trans hsteps⟩

theorem PlanSteps.append_left (C : Plan) {p q : Plan} (h : PlanSteps p q) :
    PlanSteps (C ++ p) (C ++ q) := by
  induction h with
  | refl p => exact .refl _
  | next hstep _ ih =>
    cases hstep with
    | fire A B r f ns =>
      have := PlanStep.fire (C ++ A) B r f ns
      simp only [List.append_assoc] at this ih ⊢
      exact .next this ih

/-- A complete schedule exists: left to right. -/
theorem planSteps_settle : ∀ p : Plan, PlanSteps p p.settle
  | [] => .refl _
  | (r, none) :: p => by
    have := (planSteps_settle p).append_left [(r, none)]
    simpa only [Plan.settle, List.flatMap_cons, PlanEntry.outcome, List.singleton_append] using this
  | (r, some (f, ns)) :: p => by
    have h1 := PlanStep.fire [] p r f ns
    have h2 := (planSteps_settle p).append_left (ns.map fun n => ((n, none) : PlanEntry))
    simp only [List.nil_append] at h1
    have e : Plan.settle ((r, some (f, ns)) :: p) =
        (ns.map fun n => ((n, none) : PlanEntry)) ++ Plan.settle p := by
      simp only [Plan.settle, List.flatMap_cons, PlanEntry.outcome]
    rw [e]
    exact .next h1 h2

theorem settle_done (p : Plan) : ∀ e ∈ p.settle, e.2 = none := by
  intro e he
  simp only [Plan.settle, List.mem_flatMap] at he
  obtain ⟨⟨r, o⟩, _, hm⟩ := he
  cases o with
  | none =>
    simp only [PlanEntry.outcome, List.mem_singleton] at hm
    rw [hm]
  | some x =>
    simp only [PlanEntry.outcome, List.mem_map] at hm
    obtain ⟨n, _, rfl⟩ := hm
    rfl

/-! ### `Hvm.Lower` refuses a λ as an argument -/

/-- **The single-duplicator refusal.** `Hvm.Lower` translates no β-redex whose argument is a
λ-abstraction, at any sort, in any context: HVM2's one duplicator cannot share a duplicated
higher-order λ soundly, so the lowering never emits one. -/
theorem hvmLower_refuses_lambda_argument (pfx : String) (Γ : List CEnt) (dep : Nat)
    (b a : Obend.Core.Term.Term) (σ : HSort) (k : Nat) :
    ∃ e, toS pfx Γ dep (.app (.lam b) (.lam a)) σ k = .error e := by
  rw [toS]
  by_cases hw : σ.width = 0
  · simp only [hw, ite_true]
    exact ⟨_, rfl⟩
  · simp only [hw, ite_false]
    rw [sortOf]
    exact ⟨_, rfl⟩

end Obend.Hardware.Hvm

/-! ## Part 2. Δ-nets -/

namespace Obend.Hardware.Delta
open Obend.SymbolicZk
set_option autoImplicit false

/-- A tree of a Δ-net: a wire end, an eraser, a number, a fan with its two auxiliary ports, or a
replicator with its level, its ports' deltas and its ports. The principal port is the tree's root. -/
inductive DTree where
  | var (n : Nat)
  | era
  | lit (v : UInt64)
  | fan (a b : DTree)
  | rep (level : Nat) (deltas : List Int) (aux : List DTree)
  deriving Repr, Inhabited

/-- An active pair. -/
abbrev DRedex := DTree × DTree

/-- A net: the root tree and the active pairs. -/
structure DCfg where
  root : DTree
  bag : List DRedex
  deriving Repr, Inhabited

mutual
/-- The wire ends of a tree, with repetition. -/
def DTree.vars : DTree → List Nat
  | .var n => [n]
  | .era => []
  | .lit _ => []
  | .fan a b => a.vars ++ b.vars
  | .rep _ _ ts => varsL ts
def varsL : List DTree → List Nat
  | [] => []
  | t :: ts => t.vars ++ varsL ts
end

def dBagVars : List DRedex → List Nat
  | [] => []
  | r :: rs => r.1.vars ++ r.2.vars ++ dBagVars rs

def DCfg.vars (c : DCfg) : List Nat := c.root.vars ++ dBagVars c.bag

mutual
/-- The wire `x` connected to the tree `u`. -/
def DTree.subst : DTree → Nat → DTree → DTree
  | .var n, x, u => if n = x then u else .var n
  | .era, _, _ => .era
  | .lit v, _, _ => .lit v
  | .fan a b, x, u => .fan (a.subst x u) (b.subst x u)
  | .rep l ds ts, x, u => .rep l ds (substL ts x u)
def substL : List DTree → Nat → DTree → List DTree
  | [], _, _ => []
  | t :: ts, x, u => t.subst x u :: substL ts x u
end

def substBag : List DRedex → Nat → DTree → List DRedex
  | [], _, _ => []
  | r :: rs, x, u => (r.1.subst x u, r.2.subst x u) :: substBag rs x u

/-- **Replicator equality**: same level and same deltas (so also the same number of ports). Two
replicators annihilate exactly when this holds. -/
def replicatorsAnnihilate (l1 : Nat) (d1 : List Int) (l2 : Nat) (d2 : List Int) : Bool :=
  l1 == l2 && d1 == d2

/-- The level of a copy of a higher replicator that left a lower one through a port of delta
`delta`. -/
def shiftRepLevel (level : Nat) (delta : Int) : Nat := (Int.ofNat level + delta).toNat

/-- The rules that allocate nothing, the nullary agent on the left: void, erasure (a number is
copied where an eraser erases), and the annihilation of equal agents. -/
def deltaInteract : DTree → DTree → Option (List DRedex)
  | .era, .era | .era, .lit _ | .lit _, .era | .lit _, .lit _ => some []
  | .era, .fan a b => some [(.era, a), (.era, b)]
  | .lit n, .fan a b => some [(.lit n, a), (.lit n, b)]
  | .era, .rep _ _ ts => some (ts.map fun t => (.era, t))
  | .lit n, .rep _ _ ts => some (ts.map fun t => (.lit n, t))
  | .fan a1 a2, .fan b1 b2 => some [(a1, b1), (a2, b2)]
  | .rep l1 d1 as, .rep l2 d2 bs =>
    if replicatorsAnnihilate l1 d1 l2 d2 = true then some (as.zip bs) else none
  | _, _ => none

/-- `n` fresh wire ends `f s, f (s+1), …`. -/
def freshFrom (f : Nat → Nat) : Nat → Nat → List DTree
  | _, 0 => []
  | s, n + 1 => .var (f s) :: freshFrom f (s + 1) n

/-- Each tree of the list, at its index, against the agent `mk` builds for that index. -/
def pairIdx (mk : Nat → DTree) : Nat → List DTree → List DRedex
  | _, [] => []
  | i, t :: ts => (mk i, t) :: pairIdx mk (i + 1) ts

/-- The commutations, on wires numbered from `base`. A fan and a replicator pass through each
other: two copies of the replicator, unchanged, and one fan per replicator port. A lower replicator
and a higher one pass through each other: per port of the lower, a copy of the higher at its level
plus that port's delta; per port of the higher, a copy of the lower, unchanged. -/
def deltaCommute (base : Nat) : DTree → DTree → Option (List DRedex)
  | .fan a1 a2, .rep l ds bs =>
    some ((.rep l ds (freshFrom (fun j => base + 2 * j) 0 bs.length), a1) ::
      (.rep l ds (freshFrom (fun j => base + 2 * j + 1) 0 bs.length), a2) ::
      pairIdx (fun j => .fan (.var (base + 2 * j)) (.var (base + 2 * j + 1))) 0 bs)
  | .rep l1 d1 as, .rep l2 d2 bs =>
    if l1 < l2 then
      some (pairIdx (fun i => .rep (shiftRepLevel l2 (d1.getD i 0)) d2
          (freshFrom (fun j => base + i * bs.length + j) 0 bs.length)) 0 as ++
        pairIdx (fun j => .rep l1 d1 (freshFrom (fun i => base + i * bs.length + j) 0 as.length)) 0 bs)
    else none
  | _, _ => none

/-- The interaction relation: any active pair, in either orientation. -/
inductive DStep : DCfg → DCfg → Prop where
  | rule {root : DTree} {pre post : List DRedex} {a b : DTree} {ns : List DRedex} :
      deltaInteract a b = some ns → DStep ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ ns ++ post⟩
  | swap {root : DTree} {pre post : List DRedex} {a b : DTree} :
      DStep ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ (b, a) :: post⟩
  | link {root : DTree} {pre post : List DRedex} {x : Nat} {t : DTree} :
      DStep ⟨root, pre ++ (.var x, t) :: post⟩ ⟨root.subst x t, substBag (pre ++ post) x t⟩
  | comm {root : DTree} {pre post : List DRedex} {a b : DTree} {ns : List DRedex} (base : Nat) :
      deltaCommute base a b = some ns →
      (∀ v ∈ DCfg.vars ⟨root, pre ++ (a, b) :: post⟩, v < base) →
      DStep ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ ns ++ post⟩

inductive DSteps : DCfg → DCfg → Prop where
  | refl (c : DCfg) : DSteps c c
  | next {a b c : DCfg} : DStep a b → DSteps b c → DSteps a c

theorem DSteps.trans {a b c : DCfg} (h₁ : DSteps a b) (h₂ : DSteps b c) : DSteps a c := by
  induction h₁ with
  | refl => exact h₂
  | next s _ ih => exact .next s (ih h₂)

theorem DSteps.single {a b : DCfg} (s : DStep a b) : DSteps a b := .next s (.refl _)

/-! ### Where the wires of a step come from -/

theorem mem_dBagVars_append {v : Nat} : ∀ {l₁ l₂ : List DRedex},
    v ∈ dBagVars (l₁ ++ l₂) ↔ v ∈ dBagVars l₁ ∨ v ∈ dBagVars l₂
  | [], l₂ => by simp [dBagVars]
  | r :: l₁, l₂ => by
    simp only [List.cons_append, dBagVars, List.mem_append, mem_dBagVars_append (l₁ := l₁), or_assoc]

theorem mem_dcfgVars {v : Nat} {root : DTree} {bag : List DRedex} :
    v ∈ DCfg.vars ⟨root, bag⟩ ↔ v ∈ root.vars ∨ v ∈ dBagVars bag := by
  simp [DCfg.vars]

mutual
theorem subst_vars (x : Nat) (u : DTree) (v : Nat) :
    ∀ t : DTree, v ∈ (t.subst x u).vars → v ∈ t.vars ∨ v ∈ u.vars
  | .var n => by
    by_cases h : n = x
    · simp only [DTree.subst, h, ite_true]; exact Or.inr
    · simp only [DTree.subst, h, ite_false]; exact Or.inl
  | .era => by simp [DTree.subst, DTree.vars]
  | .lit _ => by simp [DTree.subst, DTree.vars]
  | .fan a b => by
    simp only [DTree.subst, DTree.vars, List.mem_append]
    rintro (h | h)
    · rcases subst_vars x u v a h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases subst_vars x u v b h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .rep l ds ts => by
    simp only [DTree.subst, DTree.vars]
    exact substL_vars x u v ts
theorem substL_vars (x : Nat) (u : DTree) (v : Nat) :
    ∀ ts : List DTree, v ∈ varsL (substL ts x u) → v ∈ varsL ts ∨ v ∈ u.vars
  | [] => by simp [substL, varsL]
  | t :: ts => by
    simp only [substL, varsL, List.mem_append]
    rintro (h | h)
    · rcases subst_vars x u v t h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases substL_vars x u v ts h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
end

theorem substBag_vars (x : Nat) (u : DTree) (v : Nat) :
    ∀ rs : List DRedex, v ∈ dBagVars (substBag rs x u) → v ∈ dBagVars rs ∨ v ∈ u.vars
  | [] => by simp [substBag, dBagVars]
  | r :: rs => by
    simp only [substBag, dBagVars, List.mem_append]
    rintro ((h | h) | h)
    · rcases subst_vars x u v r.1 h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases subst_vars x u v r.2 h with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases substBag_vars x u v rs h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem zip_vars (v : Nat) : ∀ (as bs : List DTree),
    v ∈ dBagVars (as.zip bs) → v ∈ varsL as ∨ v ∈ varsL bs
  | [], _ => by simp [dBagVars]
  | _ :: _, [] => by simp [dBagVars]
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, dBagVars, varsL, List.mem_append]
    rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · rcases zip_vars v as bs h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem mapLeft_vars (v : Nat) (n : DTree) (hn : n.vars = []) : ∀ ts : List DTree,
    v ∈ dBagVars (ts.map fun t => (n, t)) → v ∈ varsL ts
  | [] => by simp [dBagVars]
  | t :: ts => by
    simp only [List.map_cons, dBagVars, varsL, List.mem_append, hn, List.not_mem_nil, false_or]
    rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (mapLeft_vars v n hn ts h)

/-- An interaction that allocates nothing brings no wire. -/
theorem deltaInteract_vars {a b : DTree} {ns : List DRedex} (h : deltaInteract a b = some ns)
    (v : Nat) (hv : v ∈ dBagVars ns) : v ∈ a.vars ∨ v ∈ b.vars := by
  unfold deltaInteract at h
  split at h
  all_goals first
    | (cases h; simp [dBagVars] at hv; done)
    | (cases h
       simp only [dBagVars, DTree.vars, List.mem_append, List.not_mem_nil, false_or, or_false] at hv ⊢
       first | exact Or.inr hv | exact hv | grind)
    | (cases h
       exact Or.inr (by simpa only [DTree.vars] using mapLeft_vars v _ rfl _ hv))
    | (split at h
       · cases h
         simpa only [DTree.vars] using zip_vars v _ _ hv
       · cases h)
    | cases h

theorem freshFrom_vars (f : Nat → Nat) (v : Nat) : ∀ (n s : Nat),
    v ∈ varsL (freshFrom f s n) → ∃ j, v = f j
  | 0, _ => by simp [freshFrom, varsL]
  | n + 1, s => by
    simp only [freshFrom, varsL, DTree.vars, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact ⟨s, h⟩
    · exact freshFrom_vars f v n (s + 1) h

theorem pairIdx_vars (mk : Nat → DTree) (v : Nat) : ∀ (ts : List DTree) (i : Nat),
    v ∈ dBagVars (pairIdx mk i ts) → (∃ j, v ∈ (mk j).vars) ∨ v ∈ varsL ts
  | [], _ => by simp [pairIdx, dBagVars]
  | t :: ts, i => by
    simp only [pairIdx, dBagVars, varsL, List.mem_append]
    rintro ((h | h) | h)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr (Or.inl h)
    · rcases pairIdx_vars mk v ts (i + 1) h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- A commutation brings only wires numbered from `base`. -/
theorem deltaCommute_vars {base : Nat} {a b : DTree} {ns : List DRedex}
    (h : deltaCommute base a b = some ns) (v : Nat) (hv : v ∈ dBagVars ns) :
    v ∈ a.vars ∨ v ∈ b.vars ∨ base ≤ v := by
  unfold deltaCommute at h
  split at h
  · cases h
    simp only [dBagVars, DTree.vars, List.mem_append] at hv ⊢
    rcases hv with ((hv | hv) | (hv | hv) | hv)
    · obtain ⟨j, rfl⟩ := freshFrom_vars _ v _ _ hv
      exact Or.inr (Or.inr (by omega))
    · exact Or.inl (Or.inl hv)
    · obtain ⟨j, rfl⟩ := freshFrom_vars _ v _ _ hv
      exact Or.inr (Or.inr (by omega))
    · exact Or.inl (Or.inr hv)
    · rcases pairIdx_vars _ v _ _ hv with ⟨j, hj⟩ | hv
      · simp only [DTree.vars, List.mem_append, List.mem_singleton] at hj
        exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inl hv)
  · split at h
    · cases h
      rw [mem_dBagVars_append] at hv
      simp only [DTree.vars]
      rcases hv with hv | hv
      · rcases pairIdx_vars _ v _ _ hv with ⟨j, hj⟩ | hv
        · simp only [DTree.vars] at hj
          obtain ⟨i, rfl⟩ := freshFrom_vars _ v _ _ hj
          exact Or.inr (Or.inr (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
        · exact Or.inl hv
      · rcases pairIdx_vars _ v _ _ hv with ⟨j, hj⟩ | hv
        · simp only [DTree.vars] at hj
          obtain ⟨i, rfl⟩ := freshFrom_vars _ v _ _ hj
          exact Or.inr (Or.inr (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
        · exact Or.inr (Or.inl hv)
    · cases h
  · cases h

/-! ### The executable reducer -/

/-- One past the largest wire number of a list. -/
def boundOf : List Nat → Nat → Nat
  | [], m => m
  | v :: vs, m => boundOf vs (max m (v + 1))

theorem le_boundOf : ∀ (vs : List Nat) (m : Nat), m ≤ boundOf vs m
  | [], _ => Nat.le_refl _
  | _ :: vs, _ => Nat.le_trans (Nat.le_max_left _ _) (le_boundOf vs _)

theorem lt_boundOf {v : Nat} : ∀ (vs : List Nat) (m : Nat), v ∈ vs → v < boundOf vs m
  | [], _, h => by cases h
  | w :: vs, m, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
        (le_boundOf vs _)
    · exact lt_boundOf vs _ h

/-- One past the largest wire number of a net. -/
def DCfg.bound (c : DCfg) : Nat := boundOf c.vars 0

theorem DCfg.lt_bound (c : DCfg) : ∀ v ∈ c.vars, v < c.bound := fun _ h => lt_boundOf _ _ h

def DTree.asVar : DTree → Option Nat
  | .var x => some x
  | _ => none

theorem asVar_some {t : DTree} {x : Nat} (h : t.asVar = some x) : t = .var x := by
  cases t <;> simp [DTree.asVar] at h
  rw [h]

/-- One step of the head-redex schedule, with the next free wire number: a wire is connected; else
a rule that allocates nothing fires, in either orientation; else a commutation, on wires numbered
from `next`. `none` when the bag is empty or the head pair is stuck. -/
def stepHead (c : DCfg) (next : Nat) : Option (DCfg × Nat) :=
  match c.bag with
  | [] => none
  | (a, b) :: post =>
    match a.asVar with
    | some x => some (⟨c.root.subst x b, substBag post x b⟩, next)
    | none =>
      match b.asVar with
      | some x => some (⟨c.root.subst x a, substBag post x a⟩, next)
      | none =>
        match deltaInteract a b with
        | some ns => some (⟨c.root, ns ++ post⟩, next)
        | none =>
          match deltaInteract b a with
          | some ns => some (⟨c.root, ns ++ post⟩, next)
          | none =>
            match deltaCommute next a b with
            | some ns => some (⟨c.root, ns ++ post⟩, max next (DCfg.bound ⟨c.root, ns ++ post⟩))
            | none =>
              match deltaCommute next b a with
              | some ns => some (⟨c.root, ns ++ post⟩, max next (DCfg.bound ⟨c.root, ns ++ post⟩))
              | none => none

/-- **A head step is a reduction**, and it keeps the wire discipline: the counter covers the new
net, and a wire of the new net is a wire of the old one or a number the counter had not reached. -/
theorem stepHead_sound {c c' : DCfg} {next next' : Nat} (hb : ∀ v ∈ c.vars, v < next)
    (h : stepHead c next = some (c', next')) :
    DSteps c c' ∧ next ≤ next' ∧ (∀ v ∈ c'.vars, v < next') ∧
      (∀ v ∈ c'.vars, v ∈ c.vars ∨ next ≤ v) := by
  obtain ⟨root, bag⟩ := c
  have sub : ∀ {d : DCfg}, DSteps ⟨root, bag⟩ d → (∀ v ∈ d.vars, v ∈ DCfg.vars ⟨root, bag⟩) →
      DSteps ⟨root, bag⟩ d ∧ next ≤ next ∧ (∀ v ∈ d.vars, v < next) ∧
        (∀ v ∈ d.vars, v ∈ DCfg.vars ⟨root, bag⟩ ∨ next ≤ v) :=
    fun hs hsub => ⟨hs, Nat.le_refl _, fun v hv => hb v (hsub v hv), fun v hv => Or.inl (hsub v hv)⟩
  cases bag with
  | nil => simp [stepHead] at h
  | cons r post =>
    obtain ⟨a, b⟩ := r
    simp only [stepHead] at h
    cases hav : a.asVar with
    | some x =>
      simp only [hav, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ea := asVar_some hav
      subst ea
      refine sub (.single (DStep.link (pre := []))) ?_
      intro v hv
      simp only [mem_dcfgVars, dBagVars, List.mem_append, DTree.vars] at hv ⊢
      rcases hv with hv | hv
      · rcases subst_vars x b v root hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (Or.inl (Or.inr hv))
      · rcases substBag_vars x b v post hv with hv | hv
        · exact Or.inr (Or.inr hv)
        · exact Or.inr (Or.inl (Or.inr hv))
    | none =>
      simp only [hav] at h
      cases hbv : b.asVar with
      | some x =>
        simp only [hbv, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have eb := asVar_some hbv
        subst eb
        refine sub (.next (DStep.swap (pre := [])) (.single (DStep.link (pre := [])))) ?_
        intro v hv
        simp only [mem_dcfgVars, dBagVars, List.mem_append, DTree.vars] at hv ⊢
        rcases hv with hv | hv
        · rcases subst_vars x a v root hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Or.inl (Or.inl hv))
        · rcases substBag_vars x a v post hv with hv | hv
          · exact Or.inr (Or.inr hv)
          · exact Or.inr (Or.inl (Or.inl hv))
      | none =>
        simp only [hbv] at h
        cases hi : deltaInteract a b with
        | some ns =>
          simp only [hi, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine sub (.single (DStep.rule (pre := []) hi)) ?_
          intro v hv
          simp only [mem_dcfgVars, mem_dBagVars_append, dBagVars, List.mem_append] at hv ⊢
          rcases hv with hv | hv | hv
          · exact Or.inl hv
          · exact Or.inr (Or.inl (deltaInteract_vars hi v hv))
          · exact Or.inr (Or.inr hv)
        | none =>
          simp only [hi] at h
          cases hi' : deltaInteract b a with
          | some ns =>
            simp only [hi', Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine sub (.next (DStep.swap (pre := [])) (.single (DStep.rule (pre := []) hi'))) ?_
            intro v hv
            simp only [mem_dcfgVars, mem_dBagVars_append, dBagVars, List.mem_append] at hv ⊢
            rcases hv with hv | hv | hv
            · exact Or.inl hv
            · exact Or.inr (Or.inl ((deltaInteract_vars hi' v hv).symm))
            · exact Or.inr (Or.inr hv)
          | none =>
            simp only [hi'] at h
            cases hc : deltaCommute next a b with
            | some ns =>
              simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨.single (DStep.comm (pre := []) next hc hb), Nat.le_max_left _ _,
                fun v hv => Nat.lt_of_lt_of_le (DCfg.lt_bound _ v hv) (Nat.le_max_right _ _), ?_⟩
              intro v hv
              simp only [mem_dcfgVars, mem_dBagVars_append, dBagVars, List.mem_append] at hv ⊢
              rcases hv with hv | hv | hv
              · exact Or.inl (Or.inl hv)
              · rcases deltaCommute_vars hc v hv with hv | hv | hv
                · exact Or.inl (Or.inr (Or.inl (Or.inl hv)))
                · exact Or.inl (Or.inr (Or.inl (Or.inr hv)))
                · exact Or.inr hv
              · exact Or.inl (Or.inr (Or.inr hv))
            | none =>
              simp only [hc] at h
              cases hc' : deltaCommute next b a with
              | some ns =>
                simp only [hc', Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hb' : ∀ v ∈ DCfg.vars ⟨root, [] ++ (b, a) :: post⟩, v < next := by
                  intro v hv
                  refine hb v ?_
                  simp only [mem_dcfgVars, dBagVars, List.mem_append, List.nil_append] at hv ⊢
                  rcases hv with hv | (hv | hv) | hv
                  · exact Or.inl hv
                  · exact Or.inr (Or.inl (Or.inr hv))
                  · exact Or.inr (Or.inl (Or.inl hv))
                  · exact Or.inr (Or.inr hv)
                refine ⟨.next (DStep.swap (pre := [])) (.single (DStep.comm (pre := []) next hc' hb')),
                  Nat.le_max_left _ _,
                  fun v hv => Nat.lt_of_lt_of_le (DCfg.lt_bound _ v hv) (Nat.le_max_right _ _), ?_⟩
                intro v hv
                simp only [mem_dcfgVars, mem_dBagVars_append, dBagVars, List.mem_append] at hv ⊢
                rcases hv with hv | hv | hv
                · exact Or.inl (Or.inl hv)
                · rcases deltaCommute_vars hc' v hv with hv | hv | hv
                  · exact Or.inl (Or.inr (Or.inl (Or.inr hv)))
                  · exact Or.inl (Or.inr (Or.inl (Or.inl hv)))
                  · exact Or.inr hv
                · exact Or.inl (Or.inr (Or.inr hv))
              | none => simp only [hc'] at h; cases h

/-- A void pair at the head is removed. -/
theorem stepHead_void (root : DTree) (post : List DRedex) (next : Nat) :
    stepHead ⟨root, (.era, .era) :: post⟩ next = some (⟨root, post⟩, next) := by
  simp only [stepHead, DTree.asVar, deltaInteract, List.nil_append]

/-- The head-redex schedule, for at most `fuel` steps. -/
def run : Nat → DCfg → Nat → DCfg × Nat
  | 0, c, next => (c, next)
  | fuel + 1, c, next =>
    match stepHead c next with
    | some (c', next') => run fuel c' next'
    | none => (c, next)

theorem run_sound : ∀ (fuel : Nat) (c : DCfg) (next : Nat), (∀ v ∈ c.vars, v < next) →
    DSteps c (run fuel c next).1
  | 0, c, _, _ => .refl c
  | fuel + 1, c, next, hb => by
    simp only [run]
    cases hs : stepHead c next with
    | none => exact .refl c
    | some p =>
      obtain ⟨c', next'⟩ := p
      obtain ⟨h1, _, h3, _⟩ := stepHead_sound hb hs
      exact h1.trans (run_sound fuel c' next' h3)

/-- The reducer, from a net's own wire bound. -/
def normalize (fuel : Nat) (c : DCfg) : DCfg := (run fuel c c.bound).1

/-- **The reducer is a reduction of the relation.** -/
theorem normalize_sound (fuel : Nat) (c : DCfg) : DSteps c (normalize fuel c) :=
  run_sound fuel c c.bound c.lt_bound

/-! ### Replicator equality is what annihilates -/

/-- **Two replicators have a rule that allocates nothing exactly when they are equal agents**: same
level, same deltas. Unequal ones commute (different levels) or are stuck. -/
theorem rep_interacts_iff_equal (l1 : Nat) (d1 : List Int) (as : List DTree) (l2 : Nat)
    (d2 : List Int) (bs : List DTree) :
    (deltaInteract (.rep l1 d1 as) (.rep l2 d2 bs)).isSome = true ↔ l1 = l2 ∧ d1 = d2 := by
  simp only [deltaInteract, replicatorsAnnihilate, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    by_cases hc : l1 = l2 ∧ d1 = d2
    · exact hc
    · simp only [hc, ite_false, Option.isSome_none] at h
      cases h
  · intro h
    simp only [h, and_self, ite_true, Option.isSome_some]

/-- Equal replicators connect their ports pairwise. -/
theorem rep_annihilates (l : Nat) (d : List Int) (as bs : List DTree) :
    deltaInteract (.rep l d as) (.rep l d bs) = some (as.zip bs) := by
  simp only [deltaInteract, replicatorsAnnihilate, beq_self_eq_true, Bool.and_self, ite_true]

/-! ### λ-terms as Δ-nets -/

/-- λ-terms with numbers, de Bruijn. -/
inductive HoLam where
  | var (idx : Nat)
  | lam (body : HoLam)
  | app (fn arg : HoLam)
  | lit (n : UInt64)
  deriving Repr, Inhabited

/-- The translation's state: the next wire number, the active pairs so far, and for each enclosing
binder, innermost first, its occurrences so far as `(wire, level)`. -/
structure CSt where
  next : Nat
  bag : List DRedex
  scopes : List (List (Nat × Nat))

/-- The tree at a binder's port, for an abstraction at level `lvl`: an eraser for no occurrence; a
replicator at level `lvl + 1` with one port per occurrence, of delta the occurrence's level minus
the replicator's; a bare wire for one occurrence of delta 0. -/
def binderTree (lvl : Nat) : List (Nat × Nat) → DTree
  | [] => .era
  | [(x, l)] =>
    if l = lvl + 1 then .var x
    else .rep (lvl + 1) [Int.ofNat l - Int.ofNat (lvl + 1)] [.var x]
  | occ => .rep (lvl + 1) (occ.map fun o => Int.ofNat o.2 - Int.ofNat (lvl + 1))
      (occ.map fun o => .var o.1)

/-- Record an occurrence for the binder `i` scopes out. -/
def recordOcc : Nat → Nat × Nat → List (List (Nat × Nat)) → List (List (Nat × Nat))
  | _, _, [] => []
  | 0, o, s :: ss => (s ++ [o]) :: ss
  | i + 1, o, s :: ss => s :: recordOcc i o ss

/-- The translation at level `lvl`: the tree whose principal port is the term's, and the state. An
application's argument is one level deeper; a variable is a fresh wire recorded at its binder. -/
def compileAux : HoLam → Nat → CSt → DTree × CSt
  | .lit n, _, st => (.lit n, st)
  | .var i, lvl, st =>
    (.var st.next, { st with next := st.next + 1, scopes := recordOcc i (st.next, lvl) st.scopes })
  | .lam b, lvl, st =>
    match compileAux b lvl { st with scopes := [] :: st.scopes } with
    | (body, st1) =>
      match st1.scopes with
      | occ :: rest => (.fan (binderTree lvl occ) body, { st1 with scopes := rest })
      | [] => (.fan .era body, st1)
  | .app f a, lvl, st =>
    match compileAux f lvl st with
    | (f', st1) =>
      match compileAux a (lvl + 1) st1 with
      | (a', st2) =>
        (.var st2.next, { st2 with next := st2.next + 1,
                                   bag := st2.bag ++ [(f', .fan a' (.var st2.next))] })

/-- **The translation of a closed λ-term**, at level 0. -/
def compileToDeltaNet (t : HoLam) : DCfg :=
  match compileAux t 0 ⟨0, [], []⟩ with
  | (root, st) => ⟨root, st.bag⟩

/-- `(λid. id id n) (λx. x)`: the identity, a λ-abstraction, is used twice, once applied to
itself. -/
def idIdLit (n : UInt64) : HoLam :=
  .app (.lam (.app (.app (.var 0) (.var 0)) (.lit n))) (.lam (.var 0))

/-- The reducer's run of `(λid. id id n) (λx. x)`, for every `n`. -/
theorem normalize_idId (n : UInt64) :
    normalize 64 (compileToDeltaNet (idIdLit n)) = ⟨.lit n, []⟩ := by
  kernel_rfl

/-- **A duplicated higher-order λ reduces.** `(λid. id id n) (λx. x)` reduces to `n` with nothing
left in the bag, for every `n`. -/
theorem deltaNet_idId_reduces (n : UInt64) :
    DSteps (compileToDeltaNet (idIdLit n)) ⟨.lit n, []⟩ := by
  have := normalize_sound 64 (compileToDeltaNet (idIdLit n))
  rw [normalize_idId n] at this
  exact this

/-! ### The wires of a run are a linear memory -/

/-- The run, with the lifetime ledger of its wires. -/
def runLedger : Nat → DCfg → Nat → Ledger → DCfg × Nat × Ledger
  | 0, c, next, L => (c, next, L)
  | fuel + 1, c, next, L =>
    match stepHead c next with
    | some (c', next') => runLedger fuel c' next' (L.advance c'.vars next')
    | none => (c, next, L)

theorem runLedger_inv : ∀ (fuel : Nat) (c : DCfg) (next : Nat) (L : Ledger), L.Inv → L.next ≤ next →
    (∀ v ∈ c.vars, v < next) → (∀ x, x ∈ L.live.map (·.1) ↔ x ∈ c.vars) →
    (runLedger fuel c next L).2.2.Inv ∧
      (runLedger fuel c next L).2.2.next ≤ (runLedger fuel c next L).2.1 ∧
      (runLedger fuel c next L).2.2.step ≤ L.step + fuel ∧
      (∀ x, x ∈ (runLedger fuel c next L).2.2.live.map (·.1) ↔ x ∈ (runLedger fuel c next L).1.vars) ∧
      (runLedger fuel c next L).1 = (run fuel c next).1 ∧
      (runLedger fuel c next L).2.1 = (run fuel c next).2
  | 0, c, next, L, hI, hn, _, hl => ⟨hI, hn, Nat.le_refl _, hl, rfl, rfl⟩
  | fuel + 1, c, next, L, hI, hn, hb, hl => by
    simp only [runLedger, run]
    cases hs : stepHead c next with
    | none => exact ⟨hI, hn, Nat.le_add_right _ _, hl, rfl, rfl⟩
    | some p =>
      obtain ⟨c', next'⟩ := p
      obtain ⟨_, h2, h3, h4⟩ := stepHead_sound hb hs
      have hI' : (L.advance c'.vars next').Inv := Ledger.advance_inv L hI c'.vars next'
        (fun x hx => by
          rcases h4 x hx with h | h
          · exact Or.inl ((hl x).2 h)
          · exact Or.inr (Nat.le_trans hn h))
        h3 (Nat.le_trans hn h2)
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := runLedger_inv fuel c' next' (L.advance c'.vars next') hI'
        (Nat.le_refl _) h3 (Ledger.advance_live L c'.vars next')
      refine ⟨r1, r2, Nat.le_trans r3 ?_, r4, r5, r6⟩
      show L.step + 1 + fuel ≤ L.step + (fuel + 1)
      omega

/-- The ledger of a run from a net's own wire bound. -/
def wireLedger (fuel : Nat) (c : DCfg) : Ledger :=
  (runLedger fuel c c.bound (Ledger.start c.vars c.bound)).2.2

/-- The linear-memory trace of a run: a cell per wire, born when the wire appears and consumed when
it is gone. -/
def wireTrace (fuel : Nat) (c : DCfg) : LinMemTrace := (wireLedger fuel c).toTrace

/-- The cells a run leaves are the wires of the net it reaches. -/
theorem wireLedger_final (fuel : Nat) (c : DCfg) (x : Nat) :
    x ∈ (wireLedger fuel c).live.map (·.1) ↔ x ∈ (normalize fuel c).vars := by
  obtain ⟨_, _, _, r4, r5, _⟩ := runLedger_inv fuel c c.bound (Ledger.start c.vars c.bound)
    (Ledger.start_inv c.vars c.bound c.lt_bound) (Nat.le_refl _) c.lt_bound
    (Ledger.start_live c.vars c.bound)
  rw [normalize, ← r5]
  exact r4 x

/-- **Δ-net reduction keeps its wires linear.** The wire trace of any run of the reducer, of fewer
than `2^64` steps and wire numbers, is accepted by the linear-memory checker: no wire id is
allocated twice, every wire is consumed strictly after it is produced, and produced and initial
wires are exactly the consumed and the remaining ones. -/
theorem deltaStep_preserves_linmem (fuel : Nat) (c : DCfg) (hfuel : fuel < 2 ^ 64)
    (hids : (run fuel c c.bound).2 ≤ 2 ^ 64) : verifyLinMemExec (wireTrace fuel c) = true := by
  obtain ⟨r1, r2, r3, _, _, r6⟩ := runLedger_inv fuel c c.bound (Ledger.start c.vars c.bound)
    (Ledger.start_inv c.vars c.bound c.lt_bound) (Nat.le_refl _) c.lt_bound
    (Ledger.start_live c.vars c.bound)
  rw [verifyLinMemExec_iff_spec]
  refine Ledger.toTrace_spec _ r1 ?_ ?_
  · rw [r6] at r2
    exact Nat.le_trans r2 hids
  · have : (Ledger.start c.vars c.bound).step = 0 := rfl
    have h : (wireLedger fuel c).step ≤ 0 + fuel := by rw [← this]; exact r3
    omega

end Obend.Hardware.Delta
