module
/-
# Obend.Polis.EpistemicVouchMarket — stake-bonded vouching, cut-bounded trust, judged slashing

Principals bond collateral and stake it on other principals or on claims.

1. **Trust capacity.** The vouch graph is a capacitated network; trust from a root to a target is
   the minimum cut between them (`effectiveTrustCapacity`). Evidence of trust is a packing of
   vouch chains (`packingValue`). No packing exceeds any cut (`vouchPacking_le_cut`: weak duality,
   Ford and Fulkerson 1956), and a packing with a cut of equal value certifies the capacity in
   linear time (`certifyTrustCapacity_exact`). `sybilSplit_non_amplifying` is the cut argument of
   Levien and Aiken 1998 and Yu et al. 2006: a region of pseudonyms adds at most the capacity
   that enters it, whatever the edges inside.
2. **Books.** One indexed book (treasury, each principal's free and bonded account) whose indices
   are the account keys of `Obend.Logic.ConservedValue`; `BookDelta` says two books differ by one.
3. **Slashing.** `slashRefutedClaim` fires only on a refuting run of an `Obend.Judge`, seizes the
   loss fraction of every live stake in the claim's vouching genealogy, and splits it between the
   bounty hunter and the treasury.
4. **Turns and traces.** `stepEpistemicMarket`, `ValidEpistemicMarketTrace`, the invariant
   `MarketInv`, conservation over traces, and `marketStep_skip_implies_violation`.
-/
public import Obend.Judge.Class
public import Obend.Logic.SeparationFrame

public section
namespace Obend.Polis.EpistemicVouchMarket
set_option autoImplicit false

open Obend.Logic (ConservedValue deltaAt)

/-! ## 1. Sums over lists -/

/-- `Σ f a` over a list. -/
def sumBy {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => f a + sumBy f l

theorem sumBy_le_add {α : Type} {f g h : α → Nat} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a + h a) → sumBy f l ≤ sumBy g l + sumBy h l
  | [], _ => Nat.zero_le _
  | a :: l, hl => by
    have h1 := hl a List.mem_cons_self
    have h2 := sumBy_le_add (l := l) fun b hb => hl b (List.mem_cons_of_mem _ hb)
    simp only [sumBy]; omega
theorem sumBy_le {α : Type} {f g : α → Nat} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) → sumBy f l ≤ sumBy g l
  | [], _ => Nat.le_refl _
  | a :: l, hl => by
    have h1 := hl a List.mem_cons_self
    have h2 := sumBy_le (l := l) fun b hb => hl b (List.mem_cons_of_mem _ hb)
    simp only [sumBy]; omega
theorem sumBy_congr {α : Type} {f g : α → Nat} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    sumBy f l = sumBy g l :=
  Nat.le_antisymm (sumBy_le fun a ha => Nat.le_of_eq (h a ha))
    (sumBy_le fun a ha => Nat.le_of_eq (h a ha).symm)

theorem sumBy_filter {α : Type} (p : α → Bool) (f : α → Nat) :
    ∀ l : List α, sumBy f (l.filter p) = sumBy (fun a => if p a then f a else 0) l
  | [] => rfl
  | a :: l => by
    have ih := sumBy_filter p f l
    cases hp : p a <;> simp [List.filter, hp, sumBy, ih]
theorem sumBy_map {α β : Type} (g : β → α) (f : α → Nat) :
    ∀ l : List β, sumBy f (l.map g) = sumBy (fun b => f (g b)) l
  | [] => rfl
  | b :: l => by simp [sumBy, sumBy_map g f l]

theorem ite_some {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : (if c then some a else none) = some b) : c ∧ a = b := by
  split at h
  · exact ⟨‹c›, Option.some.inj h⟩
  · cases h

/-! ## 2. The vouch network, cuts, and packings of vouch chains -/

/-- A node of the vouch graph: a principal, or a claim named by its 256-bit digest. -/
inductive TrustNode where
  | principal (id : Nat)
  | claim (digest : BitVec 256)
  deriving DecidableEq

/-- A capacitated edge: `cap` is what the voucher `src` loses if `dst` is refuted. -/
structure CapEdge where
  src : TrustNode
  dst : TrustNode
  cap : Nat
  deriving DecidableEq

/-- What an edge contributes to the cut whose root side is `side`. -/
def crossing (side : TrustNode → Bool) (e : CapEdge) : Nat :=
  if side e.src && !side e.dst then e.cap else 0

/-- The capacity leaving the root side. -/
def cutCapacity (net : List CapEdge) (side : TrustNode → Bool) : Nat := sumBy (crossing side) net

/-- Draw `a` units from the edge at index `i`: the edge, and the network with that capacity spent. -/
def drawEdge (a : Nat) : List CapEdge → Nat → Option (CapEdge × List CapEdge)
  | [], _ => none
  | e :: es, 0 => if a ≤ e.cap then some (e, { e with cap := e.cap - a } :: es) else none
  | e :: es, i + 1 => (drawEdge a es i).map fun x => (x.1, e :: x.2)

/-- Push `a` units along a chain of edge indices starting at `cur`: each edge must leave the node
the previous one entered. Returns the residual network and the node reached. -/
def pushChain (a : Nat) : List CapEdge → TrustNode → List Nat → Option (List CapEdge × TrustNode)
  | net, cur, [] => some (net, cur)
  | net, cur, i :: rest =>
    match drawEdge a net i with
    | some (e, net') => if e.src = cur then pushChain a net' e.dst rest else none
    | none => none

/-- The value of a packing of vouch chains from `r` to `c`: every chain runs from `r` to `c` and
draws its amount from the capacity the earlier chains left. `none` when some chain is not such a
walk or overdraws an edge. -/
def packingValue (r c : TrustNode) : List CapEdge → List (Nat × List Nat) → Option Nat
  | _, [] => some 0
  | net, (a, chain) :: rest =>
    match pushChain a net r chain with
    | some (net', fin) => if fin = c then (packingValue r c net' rest).map (a + ·) else none
    | none => none

theorem crossing_spend (side : TrustNode → Bool) (e : CapEdge) {a : Nat} (h : a ≤ e.cap) :
    crossing side { e with cap := e.cap - a } +
      (if (side e.src && !side e.dst) = true then a else 0) = crossing side e := by
  simp only [crossing]; split <;> omega

theorem drawEdge_cut (side : TrustNode → Bool) (a : Nat) :
    ∀ {net : List CapEdge} {i : Nat} {e : CapEdge} {net' : List CapEdge},
      drawEdge a net i = some (e, net') →
      cutCapacity net' side + (if (side e.src && !side e.dst) = true then a else 0) =
        cutCapacity net side
  | [], _, _, _, h => by simp [drawEdge] at h
  | e :: es, 0, e', net', h => by
    simp only [drawEdge] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := crossing_spend side e hle
      simp only [cutCapacity, sumBy] at this ⊢; omega
    · cases h
  | e :: es, i + 1, e', net', h => by
    simp only [drawEdge, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, hx, rfl, rfl⟩ := h
    have ih := drawEdge_cut side a hx
    simp only [cutCapacity, sumBy] at ih ⊢
    omega

theorem pushChain_cut (side : TrustNode → Bool) (a : Nat) :
    ∀ {chain : List Nat} {net : List CapEdge} {cur : TrustNode} {net' : List CapEdge}
      {fin : TrustNode}, pushChain a net cur chain = some (net', fin) →
      cutCapacity net' side ≤ cutCapacity net side ∧
        (side cur = true → side fin = false → cutCapacity net' side + a ≤ cutCapacity net side)
  | [], net, cur, net', fin, h => by
    simp only [pushChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun h1 h2 => by rw [h1] at h2; cases h2⟩
  | i :: rest, net, cur, net', fin, h => by
    simp only [pushChain] at h
    cases hd : drawEdge a net i with
    | none => rw [hd] at h; cases h
    | some p =>
      obtain ⟨e, net₁⟩ := p
      rw [hd] at h; dsimp only at h
      split at h
      · rename_i hsrc
        have hcut := drawEdge_cut side a hd
        obtain ⟨hmono, hstep⟩ := pushChain_cut side a h
        refine ⟨by split at hcut <;> omega, fun hcur hfin => ?_⟩
        subst hsrc
        cases hdst : side e.dst with
        | true => have := hstep hdst hfin; split at hcut <;> omega
        | false => simp only [hcur, hdst, Bool.not_false, Bool.and_self, ↓reduceIte] at hcut; omega
      · cases h

/-- **Weak duality.** No packing of vouch chains from `r` to `c` is worth more than a cut that
separates them: every chain crosses the cut, and what it draws there is gone. -/
theorem vouchPacking_le_cut (r c : TrustNode) (side : TrustNode → Bool) (hr : side r = true)
    (hc : side c = false) :
    ∀ {packing : List (Nat × List Nat)} {net : List CapEdge} {v : Nat},
      packingValue r c net packing = some v → v ≤ cutCapacity net side
  | [], _, _, h => by simp only [packingValue, Option.some.injEq] at h; omega
  | (a, chain) :: rest, net, v, h => by
    simp only [packingValue] at h
    cases hp : pushChain a net r chain with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨net₁, fin⟩ := p
      rw [hp] at h; dsimp only at h
      split at h
      · rename_i hfin
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨w, hw, rfl⟩ := h
        have := vouchPacking_le_cut r c side hr hc hw
        have := (pushChain_cut side a hp).2 hr (hfin ▸ hc)
        omega
      · cases h

/-! ### The minimum cut -/

def memB {α : Type} [DecidableEq α] (v : α) : List α → Bool
  | [] => false
  | w :: ws => decide (v = w) || memB v ws

theorem memB_iff {α : Type} [DecidableEq α] {v : α} : ∀ {l : List α}, memB v l = true ↔ v ∈ l
  | [] => by simp [memB]
  | w :: ws => by simp [memB, memB_iff (l := ws)]

def addNode (v : TrustNode) (l : List TrustNode) : List TrustNode := if memB v l then l else v :: l
theorem mem_addNode_self (v : TrustNode) (l : List TrustNode) : v ∈ addNode v l := by
  unfold addNode; split
  · rename_i h; exact memB_iff.1 h
  · exact List.mem_cons_self
theorem mem_addNode_of_mem (v : TrustNode) {w : TrustNode} {l : List TrustNode} (h : w ∈ l) :
    w ∈ addNode v l := by
  unfold addNode; split
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- The endpoints of a network, each once. -/
def nodesOf : List CapEdge → List TrustNode
  | [] => []
  | e :: es => addNode e.src (addNode e.dst (nodesOf es))

theorem mem_nodesOf : ∀ {net : List CapEdge} {e : CapEdge}, e ∈ net →
    e.src ∈ nodesOf net ∧ e.dst ∈ nodesOf net
  | [], _, h => by cases h
  | e' :: es, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨mem_addNode_self _ _, mem_addNode_of_mem _ (mem_addNode_self _ _)⟩
    · exact ⟨mem_addNode_of_mem _ (mem_addNode_of_mem _ (mem_nodesOf h).1),
        mem_addNode_of_mem _ (mem_addNode_of_mem _ (mem_nodesOf h).2)⟩

/-- Every sublist. -/
def subsets : List TrustNode → List (List TrustNode)
  | [] => [[]]
  | v :: vs => subsets vs ++ (subsets vs).map (v :: ·)

theorem filter_mem_subsets (p : TrustNode → Bool) : ∀ l : List TrustNode, l.filter p ∈ subsets l
  | [] => by simp [subsets]
  | v :: vs => by
    have ih := filter_mem_subsets p vs
    cases hp : p v <;> simp [List.filter, hp, subsets, ih]

/-- The root side that holds `r`, the listed nodes, and never `c`. -/
def rootSide (r c : TrustNode) (S : List TrustNode) (v : TrustNode) : Bool :=
  decide (v = r) || (!decide (v = c) && memB v S)

def minOf : Nat → List Nat → Nat
  | m, [] => m
  | m, x :: xs => minOf (min m x) xs

theorem minOf_le_seed : ∀ (xs : List Nat) (m : Nat), minOf m xs ≤ m
  | [], _ => Nat.le_refl _
  | x :: xs, m => Nat.le_trans (minOf_le_seed xs _) (Nat.min_le_left m x)
theorem minOf_le_mem : ∀ {xs : List Nat} (m : Nat) {x : Nat}, x ∈ xs → minOf m xs ≤ x
  | y :: ys, m, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (minOf_le_seed ys _) (Nat.min_le_right m x)
    · show minOf (min m y) ys ≤ x
      exact minOf_le_mem _ h
theorem minOf_attained : ∀ (xs : List Nat) (m : Nat), minOf m xs = m ∨ minOf m xs ∈ xs
  | [], _ => Or.inl rfl
  | x :: xs, m => by
    rcases minOf_attained xs (min m x) with h | h
    · rcases Nat.le_total m x with hle | hle
      · exact Or.inl (by rw [minOf, h, Nat.min_eq_left hle])
      · exact Or.inr (by rw [minOf, h, Nat.min_eq_right hle]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **Trust capacity**: the least capacity of a cut between the root `r` and the target `c`, over
every set of the network's nodes. The specification; `certifyTrustCapacity` is how it is run. -/
def effectiveTrustCapacity (net : List CapEdge) (r c : TrustNode) : Nat :=
  minOf (cutCapacity net (rootSide r c []))
    ((subsets (nodesOf net)).map fun S => cutCapacity net (rootSide r c S))

theorem rootSide_root (r c : TrustNode) (S : List TrustNode) : rootSide r c S r = true := by
  simp [rootSide]
theorem rootSide_target {r c : TrustNode} (h : r ≠ c) (S : List TrustNode) :
    rootSide r c S c = false := by
  simp [rootSide, Ne.symm h]

/-- The capacity is below every cut, listed or not. -/
theorem effectiveTrustCapacity_le_cut (net : List CapEdge) (r c : TrustNode)
    (side : TrustNode → Bool) (hr : side r = true) (hc : side c = false) :
    effectiveTrustCapacity net r c ≤ cutCapacity net side := by
  have agree : ∀ v ∈ nodesOf net, rootSide r c ((nodesOf net).filter side) v = side v := by
    intro v hv
    by_cases h1 : v = r
    · subst h1; rw [rootSide_root, hr]
    · by_cases h2 : v = c
      · subst h2; simp [rootSide, h1, hc]
      · have hm : memB v ((nodesOf net).filter side) = side v := by
          cases hs : side v
          · exact Bool.eq_false_iff.2 fun hm => by
              have := memB_iff.1 hm; simp [List.mem_filter, hs] at this
          · exact memB_iff.2 (List.mem_filter.2 ⟨hv, hs⟩)
        simp [rootSide, h1, h2, hm]
  have key : cutCapacity net (rootSide r c ((nodesOf net).filter side)) = cutCapacity net side :=
    sumBy_congr fun e he => by
      simp only [crossing, agree _ (mem_nodesOf he).1, agree _ (mem_nodesOf he).2]
  rw [← key]
  exact minOf_le_mem _ (List.mem_map_of_mem (filter_mem_subsets side _))

/-- The capacity is the capacity of some cut. -/
theorem effectiveTrustCapacity_attained (net : List CapEdge) {r c : TrustNode} (h : r ≠ c) :
    ∃ side : TrustNode → Bool, side r = true ∧ side c = false ∧
      cutCapacity net side = effectiveTrustCapacity net r c := by
  rcases minOf_attained ((subsets (nodesOf net)).map fun S => cutCapacity net (rootSide r c S))
    (cutCapacity net (rootSide r c [])) with heq | hmem
  · exact ⟨rootSide r c [], rootSide_root r c [], rootSide_target h [], heq.symm⟩
  · obtain ⟨S, _, hS⟩ := List.mem_map.1 hmem
    exact ⟨rootSide r c S, rootSide_root r c S, rootSide_target h S, hS⟩

/-- Every packing of vouch chains is worth at most the trust capacity. -/
theorem vouchPacking_le_effective {net : List CapEdge} {r c : TrustNode} (h : r ≠ c)
    {packing : List (Nat × List Nat)} {v : Nat} (hp : packingValue r c net packing = some v) :
    v ≤ effectiveTrustCapacity net r c := by
  obtain ⟨side, hr, hc, heq⟩ := effectiveTrustCapacity_attained net h
  rw [← heq]; exact vouchPacking_le_cut r c side hr hc hp

/-- The certificate checker: a packing and a root side of the same value. One pass over the
packing and one over the edges, where the specification visits every subset of the nodes. -/
def certifyTrustCapacity (net : List CapEdge) (r c : TrustNode) (packing : List (Nat × List Nat))
    (S : List TrustNode) : Option Nat :=
  if r = c then none
  else match packingValue r c net packing with
    | some v => if v = cutCapacity net (rootSide r c S) then some v else none
    | none => none

/-- **Certified capacity is exact**: an accepted certificate's value is the minimum cut. -/
theorem certifyTrustCapacity_exact {net : List CapEdge} {r c : TrustNode}
    {packing : List (Nat × List Nat)} {S : List TrustNode} {v : Nat}
    (h : certifyTrustCapacity net r c packing S = some v) : effectiveTrustCapacity net r c = v := by
  unfold certifyTrustCapacity at h
  split at h
  · cases h
  · rename_i hrc
    cases hp : packingValue r c net packing with
    | none => rw [hp] at h; cases h
    | some w =>
      rw [hp] at h; dsimp only at h
      split at h
      · rename_i hw
        cases h
        exact Nat.le_antisymm
          (hw ▸ effectiveTrustCapacity_le_cut net r c _ (rootSide_root r c S) (rootSide_target hrc S))
          (vouchPacking_le_effective hrc hp)
      · cases h

/-! ### Sybil regions -/

/-- The capacity entering a region `A` from outside it. -/
def externalInflow (net : List CapEdge) (A : TrustNode → Bool) : Nat :=
  sumBy (fun e => if !A e.src && A e.dst then e.cap else 0) net

/-- The network with every edge that touches `A` removed. -/
def honestSubnet (net : List CapEdge) (A : TrustNode → Bool) : List CapEdge :=
  net.filter fun e => !A e.src && !A e.dst

/-- **Splitting an identity buys no trust.** Let `A` be any region that does not hold the root:
one pseudonym or `k` of them, with any edges whatever leaving its nodes (rings of mutual vouches,
self-vouches, edges of any stated capacity to any target). If the capacity entering `A` from
outside totals at most `S`, then a target inside `A` receives at most `S`, and a target anywhere
receives at most `S` more than it does in the network with `A` deleted. -/
theorem sybilSplit_non_amplifying (net : List CapEdge) {r c : TrustNode} (A : TrustNode → Bool)
    (S : Nat) (hrc : r ≠ c) (hr : A r = false) (hS : externalInflow net A ≤ S) :
    (A c = true → effectiveTrustCapacity net r c ≤ S) ∧
      effectiveTrustCapacity net r c ≤ effectiveTrustCapacity (honestSubnet net A) r c + S := by
  constructor
  · intro hc
    refine Nat.le_trans (effectiveTrustCapacity_le_cut net r c (fun v => !A v) (by simp [hr])
      (by simp [hc])) (Nat.le_trans (Nat.le_of_eq ?_) hS)
    exact sumBy_congr fun e _ => by simp [crossing]
  · obtain ⟨side, hsr, hsc, heq⟩ := effectiveTrustCapacity_attained (honestSubnet net A) hrc
    have hcut := effectiveTrustCapacity_le_cut net r c (fun v => side v && !A v) (by simp [hsr, hr])
      (by simp [hsc])
    have hsplit : cutCapacity net (fun v => side v && !A v) ≤
        cutCapacity (honestSubnet net A) side + externalInflow net A := by
      unfold cutCapacity honestSubnet externalInflow
      rw [sumBy_filter]
      refine sumBy_le_add fun e _ => ?_
      have split : ∀ (s t a b : Bool) (cap : Nat),
          (if (s && !a && !(t && !b)) = true then cap else 0) ≤
            (if (!a && !b) = true then (if (s && !t) = true then cap else 0) else 0) +
              (if (!a && b) = true then cap else 0) := by
        intro s t a b cap; cases s <;> cases t <;> cases a <;> cases b <;> simp
      exact split _ _ _ _ _
    omega

/-! ## 3. Books: one indexed list of balances, moved only by transfers -/

/-- The balance at account `a`; an account past the end holds nothing. -/
def bal : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, a + 1 => bal xs a

def credit : List Nat → Nat → Nat → List Nat
  | [], 0, v => [v]
  | [], a + 1, v => 0 :: credit [] a v
  | x :: xs, 0, v => (x + v) :: xs
  | x :: xs, a + 1, v => x :: credit xs a v
def debit : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, 0, v => (x - v) :: xs
  | x :: xs, a + 1, v => x :: debit xs a v

/-- Every unit the book holds. -/
def bookTotal (L : List Nat) : Nat := sumBy (fun x => x) L

/-- Move `v` units from account `s` to account `d`. -/
def transfer (L : List Nat) (s d v : Nat) : List Nat := credit (debit L s v) d v

theorem bal_credit : ∀ (L : List Nat) (a v b : Nat),
    bal (credit L a v) b = bal L b + if b = a then v else 0
  | [], 0, _, 0 => by simp [credit, bal]
  | [], 0, _, _ + 1 => by simp [credit, bal]
  | [], _ + 1, _, 0 => by simp [credit, bal]
  | [], a + 1, v, b + 1 => by simpa [credit, bal] using bal_credit [] a v b
  | _ :: _, 0, _, 0 => by simp [credit, bal]
  | _ :: _, 0, _, _ + 1 => by simp [credit, bal]
  | _ :: _, _ + 1, _, 0 => by simp [credit, bal]
  | _ :: xs, a + 1, v, b + 1 => by simpa [credit, bal] using bal_credit xs a v b
theorem bal_debit : ∀ (L : List Nat) (a v b : Nat),
    bal (debit L a v) b = bal L b - if b = a then v else 0
  | [], _, _, _ => by simp [debit, bal]
  | _ :: _, 0, _, 0 => by simp [debit, bal]
  | _ :: _, 0, _, _ + 1 => by simp [debit, bal]
  | _ :: _, _ + 1, _, 0 => by simp [debit, bal]
  | _ :: xs, a + 1, v, b + 1 => by simpa [debit, bal] using bal_debit xs a v b
theorem bookTotal_credit : ∀ (L : List Nat) (a v : Nat), bookTotal (credit L a v) = bookTotal L + v
  | [], 0, _ => by simp [credit, bookTotal, sumBy]
  | [], a + 1, v => by
    have := bookTotal_credit [] a v
    simp only [credit, bookTotal, sumBy] at this ⊢; omega
  | _ :: _, 0, _ => by simp only [credit, bookTotal, sumBy]; omega
  | _ :: xs, a + 1, v => by
    have := bookTotal_credit xs a v
    simp only [credit, bookTotal, sumBy] at this ⊢; omega
theorem bookTotal_debit : ∀ (L : List Nat) (a v : Nat), v ≤ bal L a →
    bookTotal (debit L a v) + v = bookTotal L
  | [], _, v, h => by simp only [bal] at h; simp only [debit, bookTotal, sumBy]; omega
  | _ :: _, 0, _, h => by simp only [bal] at h; simp only [debit, bookTotal, sumBy]; omega
  | _ :: xs, a + 1, v, h => by
    have := bookTotal_debit xs a v (by simpa only [bal] using h)
    simp only [debit, bookTotal, sumBy] at this ⊢; omega

theorem bal_transfer (L : List Nat) (s d v a : Nat) :
    bal (transfer L s d v) a = (bal L a - if a = s then v else 0) + if a = d then v else 0 := by
  rw [transfer, bal_credit, bal_debit]
theorem bal_transfer_other {L : List Nat} {s d v a : Nat} (hs : a ≠ s) (hd : a ≠ d) :
    bal (transfer L s d v) a = bal L a := by simp [bal_transfer, hs, hd]
theorem bal_transfer_src {L : List Nat} {s d v : Nat} (h : s ≠ d) :
    bal (transfer L s d v) s = bal L s - v := by simp [bal_transfer, h]
theorem bal_transfer_dst {L : List Nat} {s d v : Nat} (h : s ≠ d) :
    bal (transfer L s d v) d = bal L d + v := by simp [bal_transfer, Ne.symm h]
theorem bal_transfer_ge {L : List Nat} {s d v a : Nat} (hs : a ≠ s) :
    bal L a ≤ bal (transfer L s d v) a := by
  simp only [bal_transfer, hs, ↓reduceIte]; split <;> omega

/-- A covered transfer loses and makes nothing. -/
theorem bookTotal_transfer {L : List Nat} {s d v : Nat} (h : v ≤ bal L s) :
    bookTotal (transfer L s d v) = bookTotal L := by
  have := bookTotal_debit L s v h
  rw [transfer, bookTotal_credit]; omega

/-- `L'` is `L` plus a conserved value: a sparse vector of account deltas that sum to zero
(`Obend.Logic.ConservedValue`), under which no balance goes below zero. -/
def BookDelta (L L' : List Nat) : Prop :=
  ∃ cv : ConservedValue, ∀ a : Nat, (bal L' a : Int) = bal L a + deltaAt cv.entries a

theorem BookDelta.refl (L : List Nat) : BookDelta L L :=
  ⟨.zero, fun a => by simp [ConservedValue.zero, deltaAt]⟩

theorem BookDelta.trans {L₁ L₂ L₃ : List Nat} (h₁ : BookDelta L₁ L₂) (h₂ : BookDelta L₂ L₃) :
    BookDelta L₁ L₃ := by
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  refine ⟨c₁.add c₂, fun a => ?_⟩
  have := Obend.Logic.deltaAt_addDeltaLists c₁.wf c₂.wf a
  show (bal L₃ a : Int) = bal L₁ a + deltaAt (Obend.Logic.addDeltaLists c₁.entries c₂.entries) a
  rw [this, e₂, e₁]; omega

/-- A covered transfer is the two-account conserved value `ConservedValue.transfer`. -/
theorem bookDelta_transfer {L : List Nat} {s d v : Nat} (h : v ≤ bal L s) :
    BookDelta L (transfer L s d v) :=
  ⟨ConservedValue.transfer s d v, fun a => by
    rw [ConservedValue.transfer_deltaAt, bal_transfer]
    simp only [beq_iff_eq]
    by_cases h1 : a = s
    · subst h1
      by_cases h2 : a = d
      · subst h2; simp only [eq_self, ↓reduceIte]; omega
      · simp only [eq_self, h2, ↓reduceIte]; omega
    · by_cases h2 : a = d
      · subst h2; simp only [eq_self, h1, ↓reduceIte]; omega
      · simp only [h1, h2, ↓reduceIte]; omega⟩

/-- The treasury's account, a principal's free account, and its bonded account. -/
def treasuryAcct : Nat := 0
def freeAcct (p : Nat) : Nat := 2 * p + 1
def bondAcct (p : Nat) : Nat := 2 * p + 2

theorem bond_ne_free (u h : Nat) : bondAcct u ≠ freeAcct h := by unfold bondAcct freeAcct; omega
theorem bond_ne_treasury (u : Nat) : bondAcct u ≠ treasuryAcct := by unfold bondAcct; exact nofun
theorem free_ne_treasury (h : Nat) : freeAcct h ≠ treasuryAcct := by unfold freeAcct; exact nofun
theorem bondAcct_ne {u w : Nat} (h : u ≠ w) : bondAcct u ≠ bondAcct w := by unfold bondAcct; omega
theorem freeAcct_ne {u w : Nat} (h : u ≠ w) : freeAcct u ≠ freeAcct w := by unfold freeAcct; omega

/-! ## 4. Vouches, the vouching genealogy of a claim, and the market's state -/

/-- A vouch: `voucher` stakes `stake` on `target`, loses `lossBps` basis points of it if the
target is refuted, and cannot take it back before `unlockEpoch`. -/
structure VouchEdge where
  voucher : Nat
  target : TrustNode
  stake : Nat
  lossBps : Nat
  unlockEpoch : Nat
  deriving DecidableEq

/-- What a refutation takes from the stake. -/
def slashableCapacity (e : VouchEdge) : Nat := e.stake * e.lossBps / 10000

theorem slashableCapacity_le_stake {e : VouchEdge} (h : e.lossBps ≤ 10000) :
    slashableCapacity e ≤ e.stake :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ h)

structure Challenge where
  claim : BitVec 256
  challenger : Nat
  deadline : Nat
  deriving DecidableEq
structure UnbondRequest where
  principal : Nat
  amount : Nat
  cooldownExpiry : Nat
  deriving DecidableEq

structure MarketState where
  epoch : Nat
  book : List Nat
  edges : List VouchEdge
  challenges : List Challenge
  unbonds : List UnbondRequest
  deriving DecidableEq

/-- A vouch is live, and its stake locked, until its unlock epoch. -/
def live (epoch : Nat) (e : VouchEdge) : Bool := decide (epoch < e.unlockEpoch)

def bonded (st : MarketState) (p : Nat) : Nat := bal st.book (bondAcct p)
def freeBal (st : MarketState) (p : Nat) : Nat := bal st.book (freeAcct p)
def totalValue (st : MarketState) : Nat := bookTotal st.book

/-- The stake `u` has locked in live vouches. -/
def lockedStake (epoch u : Nat) (edges : List VouchEdge) : Nat :=
  sumBy (fun e => if e.voucher = u ∧ epoch < e.unlockEpoch then e.stake else 0) edges

/-- What `u` has asked to unbond and not yet received. -/
def pendingUnbond (u : Nat) (rs : List UnbondRequest) : Nat :=
  sumBy (fun r => if r.principal = u then r.amount else 0) rs

/-- Collateral `u` cannot move: locked stakes and pending unbonds. -/
def committed (st : MarketState) (u : Nat) : Nat :=
  lockedStake st.epoch u st.edges + pendingUnbond u st.unbonds

/-- The live vouches as a capacitated network. -/
def trustNetwork (st : MarketState) : List CapEdge :=
  (st.edges.filter (live st.epoch)).map fun e =>
    ⟨.principal e.voucher, e.target, slashableCapacity e⟩

def isDirect (d : BitVec 256) (e : VouchEdge) : Bool := decide (e.target = .claim d)

def targetsOneOf (ws : List Nat) (e : VouchEdge) : Bool :=
  match e.target with
  | .principal w => memB w ws
  | .claim _ => false

/-- The vouchers answerable for claim `d` through at most `k` vouches for vouchers. -/
def liable (edges : List VouchEdge) (d : BitVec 256) : Nat → List Nat
  | 0 => (edges.filter (isDirect d)).map (·.voucher)
  | k + 1 => liable edges d k ++ (edges.filter (targetsOneOf (liable edges d k))).map (·.voucher)

/-- Whether a vouch lies in the vouching genealogy of claim `d`, to depth `k`. -/
def inGenealogy (edges : List VouchEdge) (d : BitVec 256) : Nat → VouchEdge → Bool
  | 0, e => isDirect d e
  | k + 1, e => isDirect d e || targetsOneOf (liable edges d k) e

/-- The genealogy as a relation: a vouch backs `d` when it is on `d`, or on a voucher whose own
vouch backs `d` one level nearer. -/
inductive Backs (edges : List VouchEdge) (d : BitVec 256) : Nat → VouchEdge → Prop
  | direct {k : Nat} {e : VouchEdge} : e.target = .claim d → Backs edges d k e
  | via {k : Nat} {e e' : VouchEdge} : e' ∈ edges → Backs edges d k e' →
      e.target = .principal e'.voucher → Backs edges d (k + 1) e

theorem Backs.mono {edges : List VouchEdge} {d : BitVec 256} {k : Nat} {e : VouchEdge}
    (h : Backs edges d k e) : Backs edges d (k + 1) e := by
  induction h with
  | direct hd => exact .direct hd
  | via hm _ ht ih => exact .via hm ih ht

theorem targetsOneOf_iff {ws : List Nat} {e : VouchEdge} :
    targetsOneOf ws e = true ↔ ∃ w ∈ ws, e.target = .principal w := by
  unfold targetsOneOf
  cases e.target with
  | principal w => simp [memB_iff]
  | claim d => simp

theorem mem_liable {edges : List VouchEdge} {d : BitVec 256} : ∀ {k : Nat} {w : Nat},
    w ∈ liable edges d k ↔ ∃ e ∈ edges, e.voucher = w ∧ Backs edges d k e
  | 0, w => by
    simp only [liable, List.mem_map, List.mem_filter, isDirect, decide_eq_true_eq]
    constructor
    · rintro ⟨e, ⟨he, hd⟩, rfl⟩; exact ⟨e, he, rfl, .direct hd⟩
    · rintro ⟨e, he, rfl, hb⟩; cases hb with | direct hd => exact ⟨e, ⟨he, hd⟩, rfl⟩
  | k + 1, w => by
    simp only [liable, List.mem_append, List.mem_map, List.mem_filter, mem_liable (k := k),
      targetsOneOf_iff]
    constructor
    · rintro (⟨e, he, rfl, hb⟩ | ⟨e, ⟨he, w', ⟨e', he', rfl, hb'⟩, ht⟩, rfl⟩)
      · exact ⟨e, he, rfl, hb.mono⟩
      · exact ⟨e, he, rfl, .via he' hb' ht⟩
    · rintro ⟨e, he, rfl, hb⟩
      cases hb with
      | direct hd => exact Or.inl ⟨e, he, rfl, .direct hd⟩
      | via he' hb' ht => exact Or.inr ⟨e, ⟨he, _, ⟨_, he', rfl, hb'⟩, ht⟩, rfl⟩

/-- The executable genealogy is the relation. -/
theorem inGenealogy_iff {edges : List VouchEdge} {d : BitVec 256} : ∀ {k : Nat} {e : VouchEdge},
    inGenealogy edges d k e = true ↔ Backs edges d k e
  | 0, e => by
    simp only [inGenealogy, isDirect, decide_eq_true_eq]
    exact ⟨.direct, fun hb => by cases hb with | direct hd => exact hd⟩
  | k + 1, e => by
    simp only [inGenealogy, Bool.or_eq_true, isDirect, decide_eq_true_eq, targetsOneOf_iff,
      mem_liable]
    constructor
    · rintro (hd | ⟨_, ⟨e', he', rfl, hb'⟩, ht⟩)
      · exact .direct hd
      · exact .via he' hb' ht
    · intro hb
      cases hb with
      | direct hd => exact Or.inl hd
      | via he' hb' ht => exact Or.inr ⟨_, ⟨_, he', rfl, hb'⟩, ht⟩

/-- The vouches a refutation of `d` takes from: live, and in the genealogy of `d` among the live. -/
def slashHit (horizon : Nat) (st : MarketState) (d : BitVec 256) (e : VouchEdge) : Bool :=
  live st.epoch e && inGenealogy (st.edges.filter (live st.epoch)) d horizon e
theorem slashHit_live {horizon : Nat} {st : MarketState} {d : BitVec 256} {e : VouchEdge}
    (h : slashHit horizon st d e = true) : st.epoch < e.unlockEpoch := by
  simp only [slashHit, live, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
theorem slashHit_of_direct {horizon : Nat} {st : MarketState} {d : BitVec 256} {e : VouchEdge}
    (hl : st.epoch < e.unlockEpoch) (hd : e.target = .claim d) : slashHit horizon st d e = true := by
  simp only [slashHit, live, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hl, inGenealogy_iff.2 (.direct hd)⟩

/-! ## 5. Refutation by a judge, and what it seizes -/

section Judged
variable {Obj Cert : Type}

/-- A judge's run on the claim that ends in a refusal by a refuting clause. -/
def refutationHolds [J : Judge Obj Cert] (claim : Obj) (grade : Nat) (cert : Cert) : Bool :=
  match J.check grade claim cert with
  | .refused k _ => J.refutes k
  | _ => false

/-- A refutation means the claim has no certificate at all: it is false, not unproved. -/
theorem refutationHolds_sound [J : Judge Obj Cert] {claim : Obj} {grade : Nat} {cert : Cert}
    (h : refutationHolds claim grade cert = true) : ∀ c' : Cert, ¬ J.Meaning claim c' := by
  unfold refutationHolds at h
  cases hc : J.check grade claim cert with
  | ok => rw [hc] at h; cases h
  | uncovered => rw [hc] at h; cases h
  | refused k p => rw [hc] at h; exact J.refuted hc h

/-- What a refutation takes from one vouch: its slashable capacity, never more than the bond holds. -/
def seizable (e : VouchEdge) (L : List Nat) : Nat :=
  min (slashableCapacity e) (bal L (bondAcct e.voucher))

/-- Take it out of the voucher's bond: `bps` basis points to the bounty hunter, every remaining
unit to the treasury. -/
def seize (bps hunter : Nat) (e : VouchEdge) (L : List Nat) : List Nat :=
  transfer (transfer L (bondAcct e.voucher) (freeAcct hunter) (seizable e L * bps / 10000))
    (bondAcct e.voucher) treasuryAcct (seizable e L - seizable e L * bps / 10000)

def slashStep (bps hunter : Nat) (hit : VouchEdge → Bool) (e : VouchEdge) (L : List Nat) :
    List Nat :=
  if hit e then seize bps hunter e L else L

def slashBook (bps hunter : Nat) (hit : VouchEdge → Bool) : List VouchEdge → List Nat → List Nat
  | [], L => L
  | e :: es, L => slashBook bps hunter hit es (slashStep bps hunter hit e L)

theorem bounty_le_seized {bps : Nat} (hb : bps ≤ 10000) (x : Nat) : x * bps / 10000 ≤ x :=
  Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ hb)

theorem seize_conserves {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat) (e : VouchEdge)
    (L : List Nat) :
    bookTotal (seize bps hunter e L) = bookTotal L ∧ BookDelta L (seize bps hunter e L) := by
  have h1 := bounty_le_seized hb (seizable e L)
  have h2 : seizable e L ≤ bal L (bondAcct e.voucher) := Nat.min_le_right _ _
  have hfirst : seizable e L * bps / 10000 ≤ bal L (bondAcct e.voucher) := Nat.le_trans h1 h2
  have hsecond : seizable e L - seizable e L * bps / 10000 ≤ bal (transfer L (bondAcct e.voucher)
      (freeAcct hunter) (seizable e L * bps / 10000)) (bondAcct e.voucher) := by
    rw [bal_transfer_src (bond_ne_free _ _)]; omega
  exact ⟨by rw [seize, bookTotal_transfer hsecond, bookTotal_transfer hfirst],
    (bookDelta_transfer hfirst).trans (bookDelta_transfer hsecond)⟩

theorem seize_bond {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat) (e : VouchEdge) (L : List Nat) :
    bal (seize bps hunter e L) (bondAcct e.voucher) + seizable e L = bal L (bondAcct e.voucher) := by
  have h1 := bounty_le_seized hb (seizable e L)
  have h2 : seizable e L ≤ bal L (bondAcct e.voucher) := Nat.min_le_right _ _
  rw [seize, bal_transfer_src (bond_ne_treasury _), bal_transfer_src (bond_ne_free _ _)]; omega
theorem seize_bond_other (bps hunter : Nat) {e : VouchEdge} {u : Nat} (h : e.voucher ≠ u)
    (L : List Nat) : bal (seize bps hunter e L) (bondAcct u) = bal L (bondAcct u) := by
  rw [seize, bal_transfer_other (bondAcct_ne (Ne.symm h)) (bond_ne_treasury _),
    bal_transfer_other (bondAcct_ne (Ne.symm h)) (bond_ne_free _ _)]
theorem seize_free_other (bps : Nat) {hunter h : Nat} (hne : h ≠ hunter) (e : VouchEdge)
    (L : List Nat) : bal (seize bps hunter e L) (freeAcct h) = bal L (freeAcct h) := by
  rw [seize, bal_transfer_other (Ne.symm (bond_ne_free _ _)) (free_ne_treasury _),
    bal_transfer_other (Ne.symm (bond_ne_free _ _)) (freeAcct_ne hne)]

/-- The hunter and the treasury together receive exactly what the bond lost. -/
theorem seize_payout {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat) (e : VouchEdge) (L : List Nat) :
    bal (seize bps hunter e L) treasuryAcct + bal (seize bps hunter e L) (freeAcct hunter) =
      bal L treasuryAcct + bal L (freeAcct hunter) + seizable e L := by
  have h1 := bounty_le_seized hb (seizable e L)
  rw [seize, bal_transfer_dst (bond_ne_treasury _),
    bal_transfer_other (Ne.symm (bond_ne_treasury _)) (Ne.symm (free_ne_treasury _)),
    bal_transfer_other (Ne.symm (bond_ne_free _ _)) (free_ne_treasury _),
    bal_transfer_dst (bond_ne_free _ _)]
  omega

theorem slashBook_conserves {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat)
    (hit : VouchEdge → Bool) : ∀ (es : List VouchEdge) (L : List Nat),
    bookTotal (slashBook bps hunter hit es L) = bookTotal L ∧
      BookDelta L (slashBook bps hunter hit es L)
  | [], L => ⟨rfl, .refl L⟩
  | e :: es, L => by
    have ih := slashBook_conserves hb hunter hit es (slashStep bps hunter hit e L)
    have hs : bookTotal (slashStep bps hunter hit e L) = bookTotal L ∧
        BookDelta L (slashStep bps hunter hit e L) := by
      unfold slashStep; split
      · exact seize_conserves hb hunter e L
      · exact ⟨rfl, .refl L⟩
    exact ⟨ih.1.trans hs.1, hs.2.trans ih.2⟩

theorem slashStep_bond_frame (bps hunter : Nat) {hit : VouchEdge → Bool} {e : VouchEdge} {u : Nat}
    (h : e.voucher = u → hit e = false) (L : List Nat) :
    bal (slashStep bps hunter hit e L) (bondAcct u) = bal L (bondAcct u) := by
  unfold slashStep; split
  · rename_i hh; exact seize_bond_other bps hunter (fun hv => by rw [h hv] at hh; cases hh) L
  · rfl

/-- A principal none of whose vouches is hit keeps its bond. -/
theorem slashBook_bond_frame (bps hunter : Nat) (hit : VouchEdge → Bool) (u : Nat) :
    ∀ (es : List VouchEdge) (L : List Nat), (∀ e ∈ es, e.voucher = u → hit e = false) →
      bal (slashBook bps hunter hit es L) (bondAcct u) = bal L (bondAcct u)
  | [], _, _ => rfl
  | e :: es, L, h => by
    have ih := slashBook_bond_frame bps hunter hit u es (slashStep bps hunter hit e L)
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    exact ih.trans (slashStep_bond_frame bps hunter (h e List.mem_cons_self) L)

/-- Slashing moves no free balance but the hunter's. -/
theorem slashBook_free_frame (bps : Nat) {hunter h : Nat} (hne : h ≠ hunter)
    (hit : VouchEdge → Bool) : ∀ (es : List VouchEdge) (L : List Nat),
      bal (slashBook bps hunter hit es L) (freeAcct h) = bal L (freeAcct h)
  | [], _ => rfl
  | e :: es, L => by
    have ih := slashBook_free_frame bps hne hit es (slashStep bps hunter hit e L)
    have hs : bal (slashStep bps hunter hit e L) (freeAcct h) = bal L (freeAcct h) := by
      unfold slashStep; split
      · exact seize_free_other bps hne e L
      · rfl
    exact ih.trans hs

/-- What the bonds lose to a slash is covered by the stakes the slash releases. -/
theorem slashBook_covers {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat) (hit : VouchEdge → Bool)
    (epoch u : Nat) : ∀ (es : List VouchEdge) (L : List Nat),
      (∀ e ∈ es, hit e = true → epoch < e.unlockEpoch ∧ e.lossBps ≤ 10000) →
      bal L (bondAcct u) + lockedStake epoch u (es.filter fun e => !hit e) ≤
        bal (slashBook bps hunter hit es L) (bondAcct u) + lockedStake epoch u es
  | [], _, _ => Nat.le_refl _
  | e :: es, L, h => by
    have ih := slashBook_covers hb hunter hit epoch u es (slashStep bps hunter hit e L)
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases hh : hit e with
    | false =>
      simp only [slashBook, slashStep, hh, List.filter, Bool.not_false, lockedStake, sumBy,
        Bool.false_eq_true, ↓reduceIte] at ih ⊢
      omega
    | true =>
      obtain ⟨hlive, hloss⟩ := h e List.mem_cons_self hh
      have hcap := slashableCapacity_le_stake hloss
      have hmin : seizable e L ≤ slashableCapacity e := Nat.min_le_left _ _
      simp only [slashBook, slashStep, hh, List.filter, Bool.not_true, lockedStake, sumBy,
        ↓reduceIte] at ih ⊢
      by_cases hu : e.voucher = u
      · have := seize_bond hb hunter e L
        subst hu; simp only [hlive, and_self, ↓reduceIte]; omega
      · rw [seize_bond_other bps hunter hu L] at ih
        simp only [hu, false_and, ↓reduceIte]; omega

/-- **A slash finds the collateral intact.** When every hit stake is covered by its voucher's
bond, the hunter and the treasury receive the full slashable capacity of every hit vouch. -/
theorem slashBook_seizes_all {bps : Nat} (hb : bps ≤ 10000) (hunter : Nat)
    (hit : VouchEdge → Bool) (epoch : Nat) : ∀ (es : List VouchEdge) (L : List Nat),
      (∀ e ∈ es, hit e = true → epoch < e.unlockEpoch ∧ e.lossBps ≤ 10000) →
      (∀ u, lockedStake epoch u (es.filter hit) ≤ bal L (bondAcct u)) →
      bal (slashBook bps hunter hit es L) treasuryAcct +
          bal (slashBook bps hunter hit es L) (freeAcct hunter) =
        bal L treasuryAcct + bal L (freeAcct hunter) +
          sumBy (fun e => if hit e then slashableCapacity e else 0) es
  | [], _, _, _ => rfl
  | e :: es, L, h, hcov => by
    have hrest : ∀ e' ∈ es, hit e' = true → epoch < e'.unlockEpoch ∧ e'.lossBps ≤ 10000 :=
      fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases hh : hit e with
    | false =>
      have ih := slashBook_seizes_all hb hunter hit epoch es L hrest fun u => by
        simpa [List.filter, hh] using hcov u
      simp only [slashBook, slashStep, hh, sumBy, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      omega
    | true =>
      obtain ⟨hlive, hloss⟩ := h e List.mem_cons_self hh
      have hcap := slashableCapacity_le_stake hloss
      have hself := hcov e.voucher
      simp only [List.filter, hh, lockedStake, sumBy, hlive, and_self, ↓reduceIte] at hself
      have hfull : seizable e L = slashableCapacity e := Nat.min_eq_left (by omega)
      have hbond := seize_bond hb hunter e L
      have hpay := seize_payout hb hunter e L
      have ih := slashBook_seizes_all hb hunter hit epoch es (seize bps hunter e L) hrest fun u => by
        have hu := hcov u
        simp only [List.filter, hh, lockedStake, sumBy] at hu
        by_cases hv : e.voucher = u
        · subst hv; simp only [hlive, and_self, ↓reduceIte] at hu
          simp only [lockedStake]; omega
        · rw [seize_bond_other bps hunter hv L]
          simp only [hv, false_and, ↓reduceIte] at hu
          simp only [lockedStake]; omega
      simp only [slashBook, slashStep, hh, sumBy, ↓reduceIte] at ih ⊢
      omega

/-! ## 6. Turns -/

structure MarketParams (Obj : Type) where
  /-- how a claim is named on a vouch -/
  digestOf : Obj → BitVec 256
  /-- epochs a challenge stays open, and the least lock of a new vouch -/
  challengeWindow : Nat
  /-- epochs between asking to unbond and receiving -/
  cooldown : Nat
  /-- what a challenger pays the treasury to open a challenge -/
  challengeFee : Nat
  /-- the hunter's share of a seizure, in basis points -/
  bountyBps : Nat
  /-- how many vouches for vouchers a refutation follows -/
  horizon : Nat
  bounty_le : bountyBps ≤ 10000

inductive MarketTurn (Obj Cert : Type) where
  | depositBond (p amount : Nat)
  | addVouch (e : VouchEdge)
  | advanceEpoch
  | challengeClaim (challenger : Nat) (claim : BitVec 256)
  | slashRefuted (bountyHunter : Nat) (claim : Obj) (grade : Nat) (cert : Cert)
  | requestUnbond (p amount : Nat)
  | finalizeUnbond (p : Nat)

def wellFormedVouch (e : VouchEdge) : Bool :=
  decide (0 < e.stake ∧ 0 < e.lossBps ∧ e.lossBps ≤ 10000)
def lockCoversWindow (window : Nat) (st : MarketState) (e : VouchEdge) : Bool :=
  decide (st.epoch + window ≤ e.unlockEpoch)

/-- Whether `u`'s bond covers what it has committed and `extra` more. -/
def collateralized (st : MarketState) (u extra : Nat) : Bool :=
  decide (committed st u + extra ≤ bonded st u)
def pendingChallenge (st : MarketState) (d : BitVec 256) (challenger : Nat) : Bool :=
  st.challenges.any fun ch =>
    decide (ch.claim = d ∧ ch.challenger = challenger ∧ st.epoch < ch.deadline)

/-- A request of `p` whose cooldown has run out. -/
def matured (epoch p : Nat) (r : UnbondRequest) : Bool :=
  decide (r.principal = p ∧ r.cooldownExpiry ≤ epoch)

def takeMatured (epoch p : Nat) : List UnbondRequest → Option (UnbondRequest × List UnbondRequest)
  | [] => none
  | r :: rs =>
    if matured epoch p r then some (r, rs)
    else (takeMatured epoch p rs).map fun x => (x.1, r :: x.2)

/-- A challenge holds every hit vouch through its deadline. -/
def extendLock (hit : VouchEdge → Bool) (deadline : Nat) (e : VouchEdge) : VouchEdge :=
  if hit e then { e with unlockEpoch := max e.unlockEpoch deadline } else e

/-- **Slashing.** Only the challenger of a still-open challenge, and only with a refuting run of
the judge on the claim whose digest was challenged. Every hit vouch is seized and removed, and the
claim's challenges close. -/
def slashRefutedClaim (P : MarketParams Obj) [Judge Obj Cert] (st : MarketState) (hunter : Nat)
    (claim : Obj) (grade : Nat) (cert : Cert) : Option MarketState :=
  if pendingChallenge st (P.digestOf claim) hunter && refutationHolds claim grade cert then
    some { st with
      book := slashBook P.bountyBps hunter (slashHit P.horizon st (P.digestOf claim)) st.edges
        st.book
      edges := st.edges.filter fun e => !slashHit P.horizon st (P.digestOf claim) e
      challenges := st.challenges.filter fun ch => decide (ch.claim ≠ P.digestOf claim) }
  else none

def stepEpistemicMarket (P : MarketParams Obj) [Judge Obj Cert] (st : MarketState) :
    MarketTurn Obj Cert → Option MarketState
  | .depositBond p amount =>
    if amount ≤ freeBal st p then
      some { st with book := transfer st.book (freeAcct p) (bondAcct p) amount }
    else none
  | .addVouch e =>
    if wellFormedVouch e && lockCoversWindow P.challengeWindow st e &&
        collateralized st e.voucher e.stake then
      some { st with edges := e :: st.edges }
    else none
  | .advanceEpoch => some { st with epoch := st.epoch + 1 }
  | .challengeClaim who d =>
    if P.challengeFee ≤ freeBal st who then
      some { st with
        book := transfer st.book (freeAcct who) treasuryAcct P.challengeFee
        edges := st.edges.map (extendLock (slashHit P.horizon st d) (st.epoch + P.challengeWindow))
        challenges := ⟨d, who, st.epoch + P.challengeWindow⟩ :: st.challenges }
    else none
  | .slashRefuted hunter claim grade cert => slashRefutedClaim P st hunter claim grade cert
  | .requestUnbond p amount =>
    if decide (0 < amount) && collateralized st p amount then
      some { st with unbonds := ⟨p, amount, st.epoch + P.cooldown⟩ :: st.unbonds }
    else none
  | .finalizeUnbond p =>
    match takeMatured st.epoch p st.unbonds with
    | some (r, rest) =>
      if r.amount ≤ bonded st p then
        some { st with book := transfer st.book (bondAcct p) (freeAcct p) r.amount, unbonds := rest }
      else none
    | none => none

/-- A run of turns, each accepted. -/
inductive ValidEpistemicMarketTrace (P : MarketParams Obj) [Judge Obj Cert] :
    MarketState → List (MarketTurn Obj Cert) → MarketState → Prop
  | done (st : MarketState) : ValidEpistemicMarketTrace P st [] st
  | turn {st st₁ st₂ : MarketState} {t : MarketTurn Obj Cert} {ts : List (MarketTurn Obj Cert)} :
      stepEpistemicMarket P st t = some st₁ → ValidEpistemicMarketTrace P st₁ ts st₂ →
      ValidEpistemicMarketTrace P st (t :: ts) st₂

def runMarket (P : MarketParams Obj) [Judge Obj Cert] :
    MarketState → List (MarketTurn Obj Cert) → Option MarketState
  | st, [] => some st
  | st, t :: ts =>
    match stepEpistemicMarket P st t with
    | some st₁ => runMarket P st₁ ts
    | none => none

theorem validTrace_iff_run (P : MarketParams Obj) [Judge Obj Cert] :
    ∀ {turns : List (MarketTurn Obj Cert)} {st st' : MarketState},
      ValidEpistemicMarketTrace P st turns st' ↔ runMarket P st turns = some st'
  | [], st, st' => by
    simp only [runMarket, Option.some.injEq]
    exact ⟨fun h => by cases h; rfl, fun h => h ▸ .done st⟩
  | t :: ts, st, st' => by
    simp only [runMarket]
    constructor
    · intro h
      cases h with
      | turn hs ht => rw [hs]; exact (validTrace_iff_run P).1 ht
    · intro h
      cases hs : stepEpistemicMarket P st t with
      | none => rw [hs] at h; cases h
      | some st₁ => rw [hs] at h; exact .turn hs ((validTrace_iff_run P).2 h)

/-! ## 7. Refusal is complete -/

/-- Why a turn is refused. `advanceEpoch` has no constructor: it is never refused. -/
inductive MarketViolation (P : MarketParams Obj) [Judge Obj Cert] (st : MarketState) :
    MarketTurn Obj Cert → Prop
  | insufficientFree {p amount : Nat} : freeBal st p < amount →
      MarketViolation P st (.depositBond p amount)
  | malformedVouch {e : VouchEdge} : wellFormedVouch e = false → MarketViolation P st (.addVouch e)
  | lockShorterThanChallengeWindow {e : VouchEdge} :
      e.unlockEpoch < st.epoch + P.challengeWindow → MarketViolation P st (.addVouch e)
  | undercollateralizedVouch {e : VouchEdge} :
      bonded st e.voucher < committed st e.voucher + e.stake → MarketViolation P st (.addVouch e)
  | cannotPayChallengeFee {who : Nat} {d : BitVec 256} : freeBal st who < P.challengeFee →
      MarketViolation P st (.challengeClaim who d)
  | noPendingChallenge {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert} :
      pendingChallenge st (P.digestOf claim) hunter = false →
      MarketViolation P st (.slashRefuted hunter claim grade cert)
  | claimNotRefuted {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert} :
      refutationHolds claim grade cert = false →
      MarketViolation P st (.slashRefuted hunter claim grade cert)
  | emptyUnbond {p : Nat} : MarketViolation P st (.requestUnbond p 0)
  | withdrawsCommittedStake {p amount : Nat} : bonded st p < committed st p + amount →
      MarketViolation P st (.requestUnbond p amount)
  | cooldownNotExpired {p : Nat} :
      (∀ r ∈ st.unbonds, r.principal = p → st.epoch < r.cooldownExpiry) →
      MarketViolation P st (.finalizeUnbond p)
  | bondBelowRequest {p : Nat} {r : UnbondRequest} {rest : List UnbondRequest} :
      takeMatured st.epoch p st.unbonds = some (r, rest) → bonded st p < r.amount →
      MarketViolation P st (.finalizeUnbond p)

theorem takeMatured_none {epoch p : Nat} : ∀ {rs : List UnbondRequest},
    takeMatured epoch p rs = none ↔ ∀ r ∈ rs, matured epoch p r = false
  | [] => by simp [takeMatured]
  | r :: rs => by
    cases hm : matured epoch p r <;> simp [takeMatured, hm, takeMatured_none (rs := rs)]
theorem takeMatured_some {epoch p : Nat} :
    ∀ {rs : List UnbondRequest} {r : UnbondRequest} {rest : List UnbondRequest},
      takeMatured epoch p rs = some (r, rest) → matured epoch p r = true ∧
        ∀ u, pendingUnbond u rs = pendingUnbond u rest + if r.principal = u then r.amount else 0
  | [], _, _, h => by simp [takeMatured] at h
  | r' :: rs, r, rest, h => by
    simp only [takeMatured] at h
    split at h
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm, fun u => by simp only [pendingUnbond, sumBy]; omega⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨x, hx, rfl, rfl⟩ := h
      obtain ⟨hm, hp⟩ := takeMatured_some hx
      exact ⟨hm, fun u => by have := hp u; simp only [pendingUnbond, sumBy] at this ⊢; omega⟩

/-- **Refusal is complete.** A turn is refused exactly when it commits a named violation; every
other turn is taken. The step function skips nothing it could have run. -/
theorem marketStep_skip_implies_violation (P : MarketParams Obj) [Judge Obj Cert]
    (st : MarketState) (turn : MarketTurn Obj Cert) :
    stepEpistemicMarket P st turn = none ↔ MarketViolation P st turn := by
  constructor
  · intro h
    cases turn <;> simp only [stepEpistemicMarket, slashRefutedClaim, reduceCtorEq] at h
    case depositBond p amount =>
      split at h <;> first | exact .insufficientFree (by omega) | cases h
    case addVouch e =>
      split at h; · cases h
      rename_i hn
      cases hw : wellFormedVouch e
      · exact .malformedVouch hw
      cases hl : lockCoversWindow P.challengeWindow st e
      · simp only [lockCoversWindow, decide_eq_false_iff_not] at hl
        exact .lockShorterThanChallengeWindow (by omega)
      cases hc : collateralized st e.voucher e.stake
      · simp only [collateralized, decide_eq_false_iff_not] at hc
        exact .undercollateralizedVouch (by omega)
      simp [hw, hl, hc] at hn
    case challengeClaim who d =>
      split at h <;> first | exact .cannotPayChallengeFee (by omega) | cases h
    case slashRefuted hunter claim grade cert =>
      split at h; · cases h
      rename_i hn
      cases hp : pendingChallenge st (P.digestOf claim) hunter
      · exact .noPendingChallenge hp
      cases hr : refutationHolds claim grade cert
      · exact .claimNotRefuted hr
      simp [hp, hr] at hn
    case requestUnbond p amount =>
      split at h; · cases h
      rename_i hn
      cases amount with
      | zero => exact .emptyUnbond
      | succ n =>
        cases hc : collateralized st p (n + 1)
        · simp only [collateralized, decide_eq_false_iff_not] at hc
          exact .withdrawsCommittedStake (by omega)
        simp [hc] at hn
    case finalizeUnbond p =>
      cases hm : takeMatured st.epoch p st.unbonds with
      | none =>
        refine .cooldownNotExpired fun r hr hp => ?_
        have := takeMatured_none.1 hm r hr
        simp only [matured, decide_eq_false_iff_not] at this
        omega
      | some x =>
        obtain ⟨r, rest⟩ := x
        rw [hm] at h; dsimp only at h
        split at h <;> first | exact .bondBelowRequest hm (by omega) | cases h
  · intro v
    cases v with
    | insufficientFree hlt => simp [stepEpistemicMarket, Nat.not_le.2 hlt]
    | malformedVouch hw => simp [stepEpistemicMarket, hw]
    | @lockShorterThanChallengeWindow e hl =>
      have : lockCoversWindow P.challengeWindow st e = false := by
        simp only [lockCoversWindow, decide_eq_false_iff_not]; omega
      simp [stepEpistemicMarket, this]
    | @undercollateralizedVouch e hc =>
      have : collateralized st e.voucher e.stake = false := by
        simp only [collateralized, decide_eq_false_iff_not]; omega
      simp [stepEpistemicMarket, this]
    | cannotPayChallengeFee hlt => simp [stepEpistemicMarket, Nat.not_le.2 hlt]
    | noPendingChallenge hp => simp [stepEpistemicMarket, slashRefutedClaim, hp]
    | claimNotRefuted hr => simp [stepEpistemicMarket, slashRefutedClaim, hr]
    | emptyUnbond => simp [stepEpistemicMarket]
    | @withdrawsCommittedStake p amount hc =>
      have : collateralized st p amount = false := by
        simp only [collateralized, decide_eq_false_iff_not]; omega
      simp [stepEpistemicMarket, this]
    | @cooldownNotExpired p hall =>
      have : takeMatured st.epoch p st.unbonds = none := takeMatured_none.2 fun r hr => by
        simp only [matured, decide_eq_false_iff_not]
        intro hm; have := hall r hr hm.1; omega
      simp [stepEpistemicMarket, this]
    | bondBelowRequest hm hlt => simp [stepEpistemicMarket, hm, Nat.not_le.2 hlt]

/-! ## 8. The invariant, conservation, slashing, and the cooldown -/

/-- What every reachable state satisfies. -/
structure MarketInv (P : MarketParams Obj) (st : MarketState) : Prop where
  /-- locked stakes and pending unbonds are covered by bonded collateral -/
  solvent : ∀ u, committed st u ≤ bonded st u
  lossBounded : ∀ e ∈ st.edges, e.lossBps ≤ 10000
  /-- a live stake on a challenged claim stays locked through the challenge's deadline -/
  challengeLock : ∀ ch ∈ st.challenges, ∀ e ∈ st.edges, st.epoch < e.unlockEpoch →
    e.target = .claim ch.claim → ch.deadline ≤ e.unlockEpoch
  deadlineBound : ∀ ch ∈ st.challenges, ch.deadline ≤ st.epoch + P.challengeWindow

/-- A market with no vouches satisfies the invariant, whatever its book. -/
theorem marketInv_genesis (P : MarketParams Obj) (book : List Nat) :
    MarketInv P ⟨0, book, [], [], []⟩ :=
  ⟨fun u => by simp [committed, lockedStake, pendingUnbond, sumBy], fun _ h => (nomatch h),
    fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem lockedStake_anti {ep ep' : Nat} (h : ep ≤ ep') (u : Nat) (es : List VouchEdge) :
    lockedStake ep' u es ≤ lockedStake ep u es :=
  sumBy_le fun e _ => by
    by_cases h1 : e.voucher = u ∧ ep' < e.unlockEpoch
    · have h2 : e.voucher = u ∧ ep < e.unlockEpoch := ⟨h1.1, by omega⟩
      simp [h1, h2]
    · simp [h1]

theorem extendLock_spec (hit : VouchEdge → Bool) (D : Nat) (e : VouchEdge) :
    (extendLock hit D e).voucher = e.voucher ∧ (extendLock hit D e).target = e.target ∧
      (extendLock hit D e).stake = e.stake ∧ (extendLock hit D e).lossBps = e.lossBps ∧
      e.unlockEpoch ≤ (extendLock hit D e).unlockEpoch ∧
      (hit e = true → D ≤ (extendLock hit D e).unlockEpoch) ∧
      (hit e = false → extendLock hit D e = e) := by
  unfold extendLock; cases hit e <;> simp <;> omega
theorem lockedStake_extend {hit : VouchEdge → Bool} {epoch : Nat}
    (hl : ∀ e, hit e = true → epoch < e.unlockEpoch) (D u : Nat) (es : List VouchEdge) :
    lockedStake epoch u (es.map (extendLock hit D)) = lockedStake epoch u es := by
  unfold lockedStake; rw [sumBy_map]
  refine sumBy_congr fun e _ => ?_
  obtain ⟨hv, _, hs, _, hle, _, hsame⟩ := extendLock_spec hit D e
  cases hh : hit e with
  | false => rw [hsame hh]
  | true =>
    have h1 := hl e hh
    have h2 : epoch < (extendLock hit D e).unlockEpoch := by omega
    simp [hv, hs, h1, h2]

/-- Every accepted turn keeps the invariant. -/
theorem step_preserves_inv {P : MarketParams Obj} [Judge Obj Cert] {st st' : MarketState}
    {turn : MarketTurn Obj Cert} (hinv : MarketInv P st)
    (h : stepEpistemicMarket P st turn = some st') : MarketInv P st' := by
  obtain ⟨hsol, hloss, hlock, hdl⟩ := hinv
  cases turn <;> simp only [stepEpistemicMarket, slashRefutedClaim, Option.some.injEq] at h
  case depositBond p amount =>
    obtain ⟨-, rfl⟩ := ite_some h
    refine ⟨fun u => ?_, hloss, hlock, hdl⟩
    have := hsol u
    have hge := bal_transfer_ge (L := st.book) (d := bondAcct p) (v := amount) (bond_ne_free u p)
    simp only [committed, bonded] at this ⊢; omega
  case addVouch e =>
    obtain ⟨hg, rfl⟩ := ite_some h
    simp only [Bool.and_eq_true, wellFormedVouch, lockCoversWindow, collateralized,
      decide_eq_true_eq] at hg
    obtain ⟨⟨hwf, hlk⟩, hcol⟩ := hg
    refine ⟨fun u => ?_, fun e' he' => ?_, fun ch hch e' he' hl ht => ?_, hdl⟩
    · have := hsol u
      simp only [committed, bonded, lockedStake, sumBy] at this hcol ⊢
      split
      · rename_i hu; obtain ⟨rfl, _⟩ := hu; omega
      · omega
    · rcases List.mem_cons.1 he' with rfl | he'
      · exact hwf.2.2
      · exact hloss e' he'
    · rcases List.mem_cons.1 he' with rfl | he'
      · have := hdl ch hch; omega
      · exact hlock ch hch e' he' hl ht
  case advanceEpoch =>
    subst h
    refine ⟨fun u => ?_, hloss,
      fun ch hch e he hl ht => hlock ch hch e he (by dsimp only at hl; omega) ht, fun ch hch => ?_⟩
    · have h1 := hsol u
      have h2 := lockedStake_anti (Nat.le_add_right st.epoch 1) u st.edges
      simp only [committed, bonded] at h1 ⊢; omega
    · have := hdl ch hch; dsimp only; omega
  case challengeClaim who d =>
    obtain ⟨-, rfl⟩ := ite_some h
    refine ⟨fun u => ?_, fun e' he' => ?_, fun ch hch e' he' hl ht => ?_, fun ch hch => ?_⟩
    · have := hsol u
      simp only [committed, bonded] at this ⊢
      rw [lockedStake_extend (fun e => slashHit_live),
        bal_transfer_other (bond_ne_free u who) (bond_ne_treasury u)]
      exact this
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      rw [(extendLock_spec _ _ e).2.2.2.1]; exact hloss e he
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      obtain ⟨_, htgt, _, _, hle, hhit, hsame⟩ :=
        extendLock_spec (slashHit P.horizon st d) (st.epoch + P.challengeWindow) e
      have hlive : st.epoch < e.unlockEpoch := by
        cases hh : slashHit P.horizon st d e with
        | true => exact slashHit_live hh
        | false => rw [hsame hh] at hl; exact hl
      rcases List.mem_cons.1 hch with rfl | hch
      · cases hh : slashHit P.horizon st d e with
        | true => exact hhit hh
        | false => rw [slashHit_of_direct hlive (htgt.symm.trans ht)] at hh; cases hh
      · exact Nat.le_trans (hlock ch hch e he hlive (htgt.symm.trans ht)) hle
    · rcases List.mem_cons.1 hch with rfl | hch
      · exact Nat.le_refl _
      · exact hdl ch hch
  case slashRefuted hunter claim grade cert =>
    obtain ⟨-, rfl⟩ := ite_some h
    refine ⟨fun u => ?_, fun e he => hloss e (List.mem_filter.1 he).1,
      fun ch hch e he hl ht => hlock ch (List.mem_filter.1 hch).1 e (List.mem_filter.1 he).1 hl ht,
      fun ch hch => hdl ch (List.mem_filter.1 hch).1⟩
    have := hsol u
    have hcov := slashBook_covers P.bounty_le hunter (slashHit P.horizon st (P.digestOf claim))
      st.epoch u st.edges st.book fun e he hh => ⟨slashHit_live hh, hloss e he⟩
    simp only [committed, bonded] at this ⊢; omega
  case requestUnbond p amount =>
    obtain ⟨hg, rfl⟩ := ite_some h
    simp only [Bool.and_eq_true, collateralized, decide_eq_true_eq] at hg
    refine ⟨fun u => ?_, hloss, hlock, hdl⟩
    have := hsol u
    simp only [committed, bonded, pendingUnbond, sumBy] at this hg ⊢
    split
    · rename_i hu; subst hu; omega
    · omega
  case finalizeUnbond p =>
    cases hm : takeMatured st.epoch p st.unbonds with
    | none => rw [hm] at h; cases h
    | some x =>
      obtain ⟨r, rest⟩ := x
      rw [hm] at h
      obtain ⟨hle, rfl⟩ := ite_some h
      obtain ⟨hmat, hpend⟩ := takeMatured_some hm
      simp only [matured, decide_eq_true_eq] at hmat
      refine ⟨fun u => ?_, hloss, hlock, hdl⟩
      have := hsol u
      have hp := hpend u
      simp only [committed, bonded] at this hle ⊢
      by_cases hu : u = p
      · subst hu
        rw [bal_transfer_src (bond_ne_free _ _)]
        simp only [hmat.1, ↓reduceIte] at hp; omega
      · rw [bal_transfer_other (bondAcct_ne hu) (bond_ne_free _ _)]
        have hne : r.principal ≠ u := fun h' => hu (h'.symm.trans hmat.1)
        simp only [hne, ↓reduceIte] at hp; omega

theorem trace_preserves_inv {P : MarketParams Obj} [Judge Obj Cert] {st st' : MarketState}
    {turns : List (MarketTurn Obj Cert)} (htr : ValidEpistemicMarketTrace P st turns st')
    (hinv : MarketInv P st) : MarketInv P st' := by
  induction htr with
  | done => exact hinv
  | turn hs _ ih => exact ih (step_preserves_inv hinv hs)

theorem slashHit_iff {horizon : Nat} {st : MarketState} {d : BitVec 256} {e : VouchEdge} :
    slashHit horizon st d e = true ↔
      st.epoch < e.unlockEpoch ∧ Backs (st.edges.filter (live st.epoch)) d horizon e := by
  simp only [slashHit, live, Bool.and_eq_true, decide_eq_true_eq, inGenealogy_iff]

/-- **A slash conserves value.** The total over the treasury and every free and bonded account is
unchanged, and the new book is the old one plus a `ConservedValue`: deltas that sum to zero. -/
theorem slash_conserves_total_value {P : MarketParams Obj} [Judge Obj Cert] {st st' : MarketState}
    {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert}
    (h : slashRefutedClaim P st hunter claim grade cert = some st') :
    totalValue st' = totalValue st ∧ BookDelta st.book st'.book := by
  obtain ⟨-, rfl⟩ := ite_some h
  exact slashBook_conserves P.bounty_le hunter _ st.edges st.book

/-- **Only refuted claims are slashed.** A slash happened only if the judge's run refutes the
claim, so that no certificate could mean it, and only for the challenger of an open challenge on
the claim's digest. -/
theorem slash_only_refuted {P : MarketParams Obj} [J : Judge Obj Cert] {st st' : MarketState}
    {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert}
    (h : slashRefutedClaim P st hunter claim grade cert = some st') :
    (∀ c' : Cert, ¬ J.Meaning claim c') ∧ ∃ ch ∈ st.challenges,
      ch.claim = P.digestOf claim ∧ ch.challenger = hunter ∧ st.epoch < ch.deadline := by
  obtain ⟨hg, -⟩ := ite_some h
  simp only [Bool.and_eq_true, pendingChallenge, List.any_eq_true, decide_eq_true_eq] at hg
  exact ⟨refutationHolds_sound hg.2, hg.1⟩

/-- **Uninvolved vouchers are untouched.** A principal with no live vouch in the refuted claim's
genealogy keeps its bond to the unit and every one of its vouches; its free balance changes only
if it is the bounty hunter. -/
theorem honest_uninvolved_vouchers_untouched {P : MarketParams Obj} [Judge Obj Cert]
    {st st' : MarketState} {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert}
    (h : slashRefutedClaim P st hunter claim grade cert = some st') (honest : Nat)
    (hclean : ∀ e ∈ st.edges, e.voucher = honest → ¬ (st.epoch < e.unlockEpoch ∧
      Backs (st.edges.filter (live st.epoch)) (P.digestOf claim) P.horizon e)) :
    bonded st' honest = bonded st honest ∧
      (honest ≠ hunter → freeBal st' honest = freeBal st honest) ∧
      ∀ e ∈ st.edges, e.voucher = honest → e ∈ st'.edges := by
  have hmiss : ∀ e ∈ st.edges, e.voucher = honest →
      slashHit P.horizon st (P.digestOf claim) e = false := fun e he hv =>
    Bool.eq_false_iff.2 fun hh => hclean e he hv (slashHit_iff.1 hh)
  obtain ⟨-, rfl⟩ := ite_some h
  exact ⟨slashBook_bond_frame _ _ _ honest st.edges st.book hmiss,
    fun hne => slashBook_free_frame _ hne _ st.edges st.book,
    fun e he hv => List.mem_filter.2 ⟨he, by simp [hmiss e he hv]⟩⟩

/-- **A slash in a reachable state is paid in full**: the hunter and the treasury together gain
the slashable capacity of every hit vouch. No voucher got its stake out first. -/
theorem slash_finds_collateral_intact {P : MarketParams Obj} [Judge Obj Cert]
    {st st' : MarketState} {hunter : Nat} {claim : Obj} {grade : Nat} {cert : Cert}
    (hinv : MarketInv P st) (h : slashRefutedClaim P st hunter claim grade cert = some st') :
    bal st'.book treasuryAcct + freeBal st' hunter =
      bal st.book treasuryAcct + freeBal st hunter +
        sumBy (fun e => if slashHit P.horizon st (P.digestOf claim) e then slashableCapacity e
          else 0) st.edges := by
  obtain ⟨-, rfl⟩ := ite_some h
  refine slashBook_seizes_all P.bounty_le hunter _ st.epoch st.edges st.book
    (fun e he hh => ⟨slashHit_live hh, hinv.lossBounded e he⟩) fun u => ?_
  refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_add_right _ _) (hinv.solvent u))
  unfold lockedStake; rw [sumBy_filter]
  exact sumBy_le fun e _ => by split <;> simp

theorem step_conserves {P : MarketParams Obj} [Judge Obj Cert] {st st' : MarketState}
    {turn : MarketTurn Obj Cert} (h : stepEpistemicMarket P st turn = some st') :
    totalValue st' = totalValue st ∧ BookDelta st.book st'.book := by
  cases turn <;> simp only [stepEpistemicMarket, Option.some.injEq] at h
  case depositBond p amount =>
    obtain ⟨hle, rfl⟩ := ite_some h; exact ⟨bookTotal_transfer hle, bookDelta_transfer hle⟩
  case addVouch e => obtain ⟨-, rfl⟩ := ite_some h; exact ⟨rfl, .refl _⟩
  case advanceEpoch => subst h; exact ⟨rfl, .refl _⟩
  case challengeClaim who d =>
    obtain ⟨hle, rfl⟩ := ite_some h; exact ⟨bookTotal_transfer hle, bookDelta_transfer hle⟩
  case slashRefuted hunter claim grade cert => exact slash_conserves_total_value h
  case requestUnbond p amount => obtain ⟨-, rfl⟩ := ite_some h; exact ⟨rfl, .refl _⟩
  case finalizeUnbond p =>
    cases hm : takeMatured st.epoch p st.unbonds with
    | none => rw [hm] at h; cases h
    | some x =>
      obtain ⟨r, rest⟩ := x
      rw [hm] at h
      obtain ⟨hle, rfl⟩ := ite_some h; exact ⟨bookTotal_transfer hle, bookDelta_transfer hle⟩

/-- **Every trace conserves value**: across any accepted run of deposits, vouches, epochs,
challenges, slashes and unbonds, the total is unchanged and the final book is the first plus a
conserved value (so no balance went below zero on the way to it). -/
theorem validMarketTrace_conserves_total_value {P : MarketParams Obj} [Judge Obj Cert]
    {st st' : MarketState} {turns : List (MarketTurn Obj Cert)}
    (htr : ValidEpistemicMarketTrace P st turns st') :
    totalValue st' = totalValue st ∧ BookDelta st.book st'.book := by
  induction htr with
  | done st => exact ⟨rfl, .refl _⟩
  | turn hs _ ih => exact ⟨ih.1.trans (step_conserves hs).1, (step_conserves hs).2.trans ih.2⟩

/-- **No hit and run.** In every state reached from one satisfying the invariant: (1) each
principal's locked stakes and pending unbonds are still in its bond; (2) a live stake on a claim
under challenge is locked through the challenge's deadline; (3) asking to unbond collateral that
is committed is refused; (4) taking an unbond before its cooldown has run out is refused. -/
theorem cooldown_prevents_hit_and_run {P : MarketParams Obj} [Judge Obj Cert]
    {st st' : MarketState} {turns : List (MarketTurn Obj Cert)} (hinv : MarketInv P st)
    (htr : ValidEpistemicMarketTrace P st turns st') :
    (∀ u, lockedStake st'.epoch u st'.edges + pendingUnbond u st'.unbonds ≤ bonded st' u) ∧
    (∀ ch ∈ st'.challenges, ∀ e ∈ st'.edges, st'.epoch < e.unlockEpoch →
      e.target = .claim ch.claim → ch.deadline ≤ e.unlockEpoch) ∧
    (∀ p amount, bonded st' p < committed st' p + amount →
      stepEpistemicMarket P st' (.requestUnbond p amount : MarketTurn Obj Cert) = none) ∧
    (∀ p, (∀ r ∈ st'.unbonds, r.principal = p → st'.epoch < r.cooldownExpiry) →
      stepEpistemicMarket P st' (.finalizeUnbond p : MarketTurn Obj Cert) = none) :=
  have hinv' := trace_preserves_inv htr hinv
  ⟨hinv'.solvent, hinv'.challengeLock,
    fun _ _ hlt => (marketStep_skip_implies_violation P st' _).2 (.withdrawsCommittedStake hlt),
    fun _ hall => (marketStep_skip_implies_violation P st' _).2 (.cooldownNotExpired hall)⟩

/-- A withdrawal that happened was of a pending request of that principal whose cooldown had run
out. -/
theorem unbond_only_after_cooldown {P : MarketParams Obj} [Judge Obj Cert] {st st' : MarketState}
    {p : Nat} (h : stepEpistemicMarket P st (.finalizeUnbond p : MarketTurn Obj Cert) = some st') :
    ∃ r : UnbondRequest, r.principal = p ∧ r.cooldownExpiry ≤ st.epoch ∧
      pendingUnbond p st.unbonds = pendingUnbond p st'.unbonds + r.amount := by
  simp only [stepEpistemicMarket] at h
  cases hm : takeMatured st.epoch p st.unbonds with
  | none => rw [hm] at h; cases h
  | some x =>
    obtain ⟨r, rest⟩ := x
    rw [hm] at h
    obtain ⟨-, rfl⟩ := ite_some h
    obtain ⟨hmat, hpend⟩ := takeMatured_some hm
    simp only [matured, decide_eq_true_eq] at hmat
    exact ⟨r, hmat.1, hmat.2, by simpa [hmat.1] using hpend p⟩

/-- The other half of the cooldown: once a request has matured, taking it succeeds, and moves
exactly the requested amount from the bond to the free account. -/
theorem post_cooldown_unbond_succeeds {P : MarketParams Obj} [Judge Obj Cert] {st : MarketState}
    (hinv : MarketInv P st) {r : UnbondRequest} (hr : r ∈ st.unbonds)
    (hexp : r.cooldownExpiry ≤ st.epoch) :
    ∃ (st' : MarketState) (r' : UnbondRequest),
      stepEpistemicMarket P st (.finalizeUnbond r.principal : MarketTurn Obj Cert) = some st' ∧
      freeBal st' r.principal = freeBal st r.principal + r'.amount ∧
      bonded st' r.principal + r'.amount = bonded st r.principal := by
  cases hm : takeMatured st.epoch r.principal st.unbonds with
  | none =>
    have := takeMatured_none.1 hm r hr
    simp [matured, hexp] at this
  | some x =>
    obtain ⟨r', rest⟩ := x
    obtain ⟨hmat, hpend⟩ := takeMatured_some hm
    simp only [matured, decide_eq_true_eq] at hmat
    have hsol := hinv.solvent r.principal
    have hp := hpend r.principal
    simp only [hmat.1, ↓reduceIte] at hp
    have hle : r'.amount ≤ bonded st r.principal := by simp only [committed] at hsol; omega
    refine ⟨_, r', by simp only [stepEpistemicMarket, hm, hle, ↓reduceIte]; rfl, ?_, ?_⟩
    · exact bal_transfer_dst (bond_ne_free _ _)
    · show bal (transfer st.book _ _ _) _ + _ = _
      rw [bal_transfer_src (bond_ne_free _ _)]; simp only [bonded] at hle ⊢; omega

/-- **A principal's bond caps the trust it confers.** Whatever a root vouches for, and however the
rest of the graph is wired, the capacity from it to any target is at most its bonded collateral. -/
theorem trust_bounded_by_bond {P : MarketParams Obj} {st : MarketState} (hinv : MarketInv P st)
    (r : Nat) {c : TrustNode} (hc : c ≠ .principal r) :
    effectiveTrustCapacity (trustNetwork st) (.principal r) c ≤ bonded st r := by
  refine Nat.le_trans (effectiveTrustCapacity_le_cut _ _ _ (fun v => decide (v = .principal r))
    (by simp) (by simpa using hc)) ?_
  refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_add_right _ _) (hinv.solvent r))
  unfold cutCapacity trustNetwork lockedStake
  rw [sumBy_map, sumBy_filter]
  refine sumBy_le fun e he => ?_
  have hcap := slashableCapacity_le_stake (hinv.lossBounded e he)
  by_cases h1 : e.voucher = r <;> by_cases h2 : st.epoch < e.unlockEpoch <;>
    simp [crossing, live, h1, h2] <;> split <;> omega

end Judged

/-! ## 9. A judge of tallies, and witnesses that the premises above are inhabited -/

/-- The claim that `entries` sum to `total`. -/
structure TallyClaim where
  entries : List Nat
  total : Nat

inductive TallyClause where
  | mismatch

/-- Judges a tally by adding it up, when the grade covers its length. A refusal is a refutation;
every tally is in the fragment. -/
instance tallyJudge : Judge TallyClaim Unit where
  Clause := TallyClause
  Meaning o _ := bookTotal o.entries = o.total
  check r o _ :=
    if o.entries.length ≤ r then
      if bookTotal o.entries = o.total then .ok else .refused .mismatch []
    else .uncovered
  sound := @fun r o _ h => by
    split at h
    · split at h
      · assumption
      · cases h
    · cases h
  refutes := fun _ => true
  refuted := @fun r o _ _ _ h _ _ hm => by
    simp only [hm, ↓reduceIte] at h
    split at h <;> cases h
  Fragment := fun _ => True
  complete := @fun o _ hm => by
    obtain ⟨_, hm⟩ := hm
    exact ⟨(), o.entries.length, by simp [hm]⟩
  mono := @fun r r' o _ hle hne => by
    by_cases h : o.entries.length ≤ r
    · have h' : o.entries.length ≤ r' := Nat.le_trans h hle
      simp only [h, h', ↓reduceIte]
    · simp [h] at hne

/-- Names a tally by folding it into 256 bits. A name for small vectors: a deployed market
supplies a collision-resistant digest here. -/
def tallyDigest (o : TallyClaim) : BitVec 256 :=
  (o.total :: o.entries).foldl
    (fun acc x => acc * 1099511628211#256 + BitVec.ofNat 256 x + 1#256) 14695981039346656037#256

/-- A market over tallies: window 2, cooldown 3, fee 1, a quarter of each seizure to the hunter,
one level of vouches for vouchers. -/
def tallyMarket : MarketParams TallyClaim := ⟨tallyDigest, 2, 3, 1, 2500, 1, by decide⟩

example : refutationHolds (⟨[1, 2], 4⟩ : TallyClaim) 2 () = true := by decide
example : refutationHolds (⟨[1, 2], 3⟩ : TallyClaim) 2 () = false := by decide

example : certifyTrustCapacity
    [⟨.principal 0, .principal 1, 5⟩, ⟨.principal 1, .claim 7#256, 3⟩]
    (.principal 0) (.claim 7#256) [(3, [0, 1])] [.principal 1] = some 3 := by decide

/-- A trace that deposits, vouches for a false tally, is challenged and slashed: of the 30 units
seized, 7 reach the hunter and 23 the treasury. -/
example : ValidEpistemicMarketTrace tallyMarket ⟨0, [0, 10, 0, 100], [], [], []⟩
    [.depositBond 1 80, .addVouch ⟨1, .claim (tallyDigest ⟨[1, 2], 4⟩), 60, 5000, 2⟩,
      .challengeClaim 0 (tallyDigest ⟨[1, 2], 4⟩), .slashRefuted 0 ⟨[1, 2], 4⟩ 2 ()]
    ⟨0, [24, 16, 0, 20, 50], [], [], []⟩ :=
  (validTrace_iff_run tallyMarket).2 (by decide)

end Obend.Polis.EpistemicVouchMarket
end
