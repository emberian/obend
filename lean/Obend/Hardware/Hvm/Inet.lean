module
/-
# Obend.Hardware.Hvm.Inet — HVM2's combinator nets as the reduction machine's arenas

The map from the HVM2 model (`Hvm.Model`) to `ReductionMachine`'s arena (`ReductionMachine.Arena`),
for the fragment of the interaction combinators: `CON` (the machine's `con`, label 0), `DUP` (`dup`,
label 1) and `ERA` (`era`).

`Repr A ρ c` says the arena `A` is the configuration `c`, with the root at the free port `ρ`. Every
`CON`, `DUP` and `ERA` node of `c` (the root tree and both sides of every redex) is one node of `A`,
and `A` has no other; a child's principal port and its parent's auxiliary port face each other in
the link table, both ways, and so do the principal ports of the two sides of a redex. A variable
occurrence is recorded with the port it sits at (`Tree`'s occurrences); `Paired` says that across
the wire from every occurrence is an occurrence of the same variable. A redex whose two sides are
both variables is not an arena: it is a wire with no node, and `Repr` has none.

`inetOfHvm_sound`: from an arena representing `c`, every interaction step of `c` on `CON`, `DUP` and
`ERA` (VOID, ERAS, ANNI, COMM, `Interacts`) is one `Arena.Step`, the pair rewritten by
`reduceActivePair`'s outcome, to an arena representing the result; when ANNI joins two variables,
the result is represented after HVM2's LINK of them (`Steps`). `repr_swap`: a redex's orientation
does not matter.

Not covered, by name:
* **A loop at the pair**: a wire between two auxiliary ports of the fired pair (a variable twice
  among the pair's children). `Interacts` asks the children's variables to be distinct; the arena's
  `apply` wires outside ports and does not resolve a wire whose far end is in the pair itself.
* **LINK of a variable with a node** (`x ~ t`, `t` not a variable): no arena step (the wire is
  already there); that `Repr` is preserved needs `t` to move to the other occurrence of `x`, which
  needs linearity (each variable exactly twice), not part of `Repr`.
* **`NUM`, `REF`, `OPR`, `SWI`**: `INetNodeKind` has no counterpart. `NUM` needs a kind carrying a
  U24 (or `Numb`) and the rules ERAS-on-number and VOID with it; `OPR` a binary kind and OPER (a
  number meeting `OPR` is held in the node and the second number completes the operation, so the
  outcome rewrites the node in place); `SWI` a binary kind and SWIT (a number meeting `SWI` builds a
  `CON` of the branches and an eraser, a three-node outcome); `REF` a kind naming a definition and
  CALL (the outcome is a whole definition net placed under a renaming, not a fixed number of nodes)
  and the copy of a reference meeting `DUP`. The machine's `nat64`/`lam`/`app` and `betaNat64` are
  not these rules (`betaNat64` has no arena reading).
-/
public import Obend.Hardware.Hvm.Model
public import Obend.Hardware.ReductionMachine.Arena
@[expose] public section

namespace Obend.Hardware.Hvm
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## Node by node -/

/-- The reduction machine's kind and label for an HVM2 node, where it has one. -/
def inetKindOf : HTree → Option (INetNodeKind × Nat)
  | .con _ _ => some (.con, 0)
  | .dup _ _ => some (.dup, 1)
  | .era => some (.era, 0)
  | _ => none

/-- An HVM2 node as an `INetNode`, its auxiliary ports at the given references. -/
def inetOfHvm (id : Nat) (t : HTree) (a1 a2 : PortRef) : Option INetNode :=
  (inetKindOf t).map fun kl => ⟨id, kl.1, kl.2, 0, a1, a2⟩

/-- **Annihilation agrees**: two `CON` (or two `DUP`) nodes annihilate in both models, the auxiliary
ports wired pairwise. -/
theorem inetOfHvm_annihilate (id1 id2 next : Nat) (a1 a2 b1 b2 : PortRef) (A1 A2 B1 B2 : HTree) :
    (∀ l r, inetOfHvm id1 (.con A1 A2) a1 a2 = some l → inetOfHvm id2 (.con B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .annihilate (a1, b1) (a2, b2)) ∧
    localRule (.con A1 A2) (.con B1 B2) = some [(A1, B1), (A2, B2)] ∧
    (∀ l r, inetOfHvm id1 (.dup A1 A2) a1 a2 = some l → inetOfHvm id2 (.dup B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .annihilate (a1, b1) (a2, b2)) ∧
    localRule (.dup A1 A2) (.dup B1 B2) = some [(A1, B1), (A2, B2)] := by
  refine ⟨fun l r hl hr => ?_, rfl, fun l r hl hr => ?_, rfl⟩ <;>
    simp only [inetOfHvm, inetKindOf, Option.map_some, Option.some.injEq] at hl hr <;>
    subst hl hr <;> simp [reduceActivePair]

/-- **Erasure agrees**: an eraser meeting `CON` or `DUP` erases both auxiliary ports. -/
theorem inetOfHvm_erase (id1 id2 next : Nat) (a1 a2 b1 b2 : PortRef) (B1 B2 : HTree) :
    (∀ l r, inetOfHvm id1 .era a1 a2 = some l → inetOfHvm id2 (.con B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .erase [b1, b2]) ∧
    localRule .era (.con B1 B2) = some [(.era, B1), (.era, B2)] := by
  refine ⟨fun l r hl hr => ?_, rfl⟩
  simp only [inetOfHvm, inetKindOf, Option.map_some, Option.some.injEq] at hl hr
  subst hl hr; simp [reduceActivePair]

/-- **Commutation agrees**: `CON` meeting `DUP` commutes in both models. The machine's four copies and
splices (`commuteSpawnedNodes`, `commuteSplices`) are HVM2's COMM: copies of the `DUP` face the
`CON`'s auxiliary ports, copies of the `CON` the `DUP`'s, auxiliary port `j` of the `k`-th `DUP`
copy wired to auxiliary port `k` of the `j`-th `CON` copy, as COMM's four fresh variables wire them. -/
theorem inetOfHvm_commute (id1 id2 next : Nat) (a1 a2 b1 b2 : PortRef) (A1 A2 B1 B2 : HTree) :
    ∀ l r, inetOfHvm id1 (.con A1 A2) a1 a2 = some l → inetOfHvm id2 (.dup B1 B2) b1 b2 = some r →
      reduceActivePair ⟨l, r⟩ next = .commute (commuteSpawnedNodes l r next) (commuteSplices l r next) := by
  intro l r hl hr
  simp only [inetOfHvm, inetKindOf, Option.map_some, Option.some.injEq] at hl hr
  subst hl hr; simp [reduceActivePair]

/-! ## Configurations as arenas -/

/-- `CON` and `DUP` as the machine's kind and label, with their two children. -/
def cdOf : HTree → Option (INetNodeKind × Nat × HTree × HTree)
  | .con a b => some (.con, 0, a, b)
  | .dup a b => some (.dup, 1, a, b)
  | _ => none

/-- What a tree shows its parent: a node's principal port, or a variable. -/
inductive Up where
  | port (p : PortRef)
  | var (x : Nat)
  deriving DecidableEq

def Up.rename (f : Nat → Nat) : Up → Up
  | .port p => .port p
  | .var x => .var (f x)

/-- The wire from port `p` to what a tree shows: both directions in the link table for a node; a
variable is recorded as an occurrence at `p` instead (`edgeOcc`). -/
def Edge (A : Arena) (p : PortRef) : Up → Prop
  | .port q => A.link p = q ∧ A.link q = p
  | .var _ => True

def edgeOcc (p : PortRef) : Up → List (Nat × PortRef)
  | .port _ => []
  | .var x => [(x, p)]

/-- `Tree A t u ids occ`: the tree `t` is laid out in `A` on the nodes `ids`, shows `u`, and its
variable occurrences sit at the ports `occ` records. -/
inductive Tree (A : Arena) : HTree → Up → List Nat → List (Nat × PortRef) → Prop where
  | var (x : Nat) : Tree A (.var x) (.var x) [] []
  | era (i : Nat) : A.node i = some (.era, 0, 0) → Tree A .era (.port ⟨i, 0⟩) [i] []
  | bin {t a b : HTree} {k : INetNodeKind} {lb : Nat} {ua ub : Up} {ia ib : List Nat}
      {oa ob : List (Nat × PortRef)} (i : Nat) :
      cdOf t = some (k, lb, a, b) → A.node i = some (k, lb, 0) →
      Tree A a ua ia oa → Tree A b ub ib ob → Edge A ⟨i, 1⟩ ua → Edge A ⟨i, 2⟩ ub →
      Tree A t (.port ⟨i, 0⟩) (i :: (ia ++ ib)) (edgeOcc ⟨i, 1⟩ ua ++ edgeOcc ⟨i, 2⟩ ub ++ oa ++ ob)

/-- The wire between the two sides of a redex: principal ports facing each other, or an occurrence
of the variable side at the node side's principal port. Two variables are not an arena. -/
def Facing (A : Arena) : Up → Up → List (Nat × PortRef) → Prop
  | .port p, .port q, o => A.link p = q ∧ A.link q = p ∧ o = []
  | .var x, .port q, o => o = [(x, q)]
  | .port p, .var y, o => o = [(y, p)]
  | .var _, .var _, _ => False

/-- The redexes of a bag, laid out on the nodes `ids`, their occurrences `occ`. -/
inductive BagIn (A : Arena) : List Redex → List Nat → List (Nat × PortRef) → Prop where
  | nil : BagIn A [] [] []
  | cons {a b : HTree} {rs : List Redex} {ua ub : Up} {ia ib is : List Nat}
      {oa ob o os : List (Nat × PortRef)} :
      Tree A a ua ia oa → Tree A b ub ib ob → Facing A ua ub o → BagIn A rs is os →
      BagIn A ((a, b) :: rs) (ia ++ ib ++ is) (oa ++ ob ++ o ++ os)

/-- Across the wire from every occurrence is an occurrence of the same variable. -/
def Paired (A : Arena) (occ : List (Nat × PortRef)) : Prop :=
  ∀ x p, (x, p) ∈ occ → (x, A.link p) ∈ occ ∧ A.link p ≠ p ∧ A.link (A.link p) = p

/-- **The arena is the configuration**, its root at the free port `ρ`: the root tree and the bag
laid out on distinct nodes, older than `A.next`, which are all of `A`'s nodes; the root faces `ρ`;
every occurrence paired. -/
def Repr (A : Arena) (ρ : PortRef) (c : Cfg) : Prop :=
  ∃ (u : Up) (ir ib : List Nat) (or ob : List (Nat × PortRef)),
    Tree A c.root u ir or ∧ Edge A ρ u ∧ BagIn A c.bag ib ob ∧
    (ir ++ ib).Nodup ∧ (∀ k ∈ ir ++ ib, k < A.next) ∧ (∀ k, A.node k ≠ none → k ∈ ir ++ ib) ∧
    ρ.nodeId < A.next ∧ ρ.nodeId ∉ ir ++ ib ∧
    Paired A (edgeOcc ρ u ++ or ++ ob)

/-! ## The interaction steps -/

/-- A child's variable, if it is one. -/
def topVar : HTree → List Nat
  | .var x => [x]
  | _ => []

/-- The variables among a node's two children. -/
def kidVars (t : HTree) : List Nat :=
  match cdOf t with
  | some (_, _, a, b) => topVar a ++ topVar b
  | none => []

/-- The steps that fire a pair: a local rule (VOID, ERAS, ANNI, ...) or COMM, the pair's children
sharing no variable (no wire between two of the pair's own auxiliary ports). -/
inductive Interacts : Cfg → Cfg → Prop where
  | rule {root : HTree} {pre post : List Redex} {a b : HTree} {ns : List Redex} :
      localRule a b = some ns → (kidVars a ++ kidVars b).Nodup →
      Interacts ⟨root, pre ++ (a, b) :: post⟩ ⟨root, pre ++ ns ++ post⟩
  | comm {root : HTree} {pre post : List Redex} {a b a1 a2 b1 b2 : HTree} {ka kb : BinKind}
      {v0 v1 v2 v3 : Nat} :
      a.bin? = some (ka, a1, a2) → b.bin? = some (kb, b1, b2) → ka ≠ kb →
      [v0, v1, v2, v3].Nodup →
      (∀ v ∈ [v0, v1, v2, v3], v ∉ (Cfg.vars ⟨root, pre ++ (a, b) :: post⟩)) →
      (kidVars a ++ kidVars b).Nodup →
      Interacts ⟨root, pre ++ (a, b) :: post⟩
        ⟨root, pre ++ [(mkBin kb (.var v0) (.var v1), a1), (mkBin kb (.var v2) (.var v3), a2),
          (mkBin ka (.var v0) (.var v2), b1), (mkBin ka (.var v1) (.var v3), b2)] ++ post⟩

theorem Interacts.step {book : List HDef} {c c' : Cfg} : Interacts c c' → Step book c c'
  | .rule h _ => .rule h
  | .comm ha hb hk hv hf _ => .comm ha hb hk hv hf

/-! ## Facts about layouts -/

theorem mem_edgeOcc {q : PortRef} {u : Up} {x : Nat} {p : PortRef} :
    (x, p) ∈ edgeOcc q u ↔ u = .var x ∧ p = q := by
  cases u <;> simp [edgeOcc, eq_comm]

theorem Tree.var_inv {A : Arena} {x : Nat} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A (.var x) u ids occ) : u = .var x ∧ ids = [] ∧ occ = [] := by
  cases h with
  | var => exact ⟨rfl, rfl, rfl⟩
  | bin _ hc => simp [cdOf] at hc

theorem Tree.era_inv {A : Arena} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A .era u ids occ) : ∃ i, u = .port ⟨i, 0⟩ ∧ ids = [i] ∧ occ = [] ∧ A.node i = some (.era, 0, 0) := by
  cases h with
  | era i hn => exact ⟨i, rfl, rfl, rfl, hn⟩
  | bin _ hc => simp [cdOf] at hc

theorem Tree.bin_inv {A : Arena} {t a b : HTree} {k : INetNodeKind} {lb : Nat} {u : Up} {ids : List Nat}
    {occ : List (Nat × PortRef)} (h : Tree A t u ids occ) (hc : cdOf t = some (k, lb, a, b)) :
    ∃ i ua ub ia ib oa ob, u = .port ⟨i, 0⟩ ∧ ids = i :: (ia ++ ib) ∧
      occ = edgeOcc ⟨i, 1⟩ ua ++ edgeOcc ⟨i, 2⟩ ub ++ oa ++ ob ∧ A.node i = some (k, lb, 0) ∧
      Tree A a ua ia oa ∧ Tree A b ub ib ob ∧ Edge A ⟨i, 1⟩ ua ∧ Edge A ⟨i, 2⟩ ub := by
  cases h with
  | var => simp [cdOf] at hc
  | era => simp [cdOf] at hc
  | bin i hc' hn ha hb ea eb =>
    rw [hc] at hc'
    simp only [Option.some.injEq, Prod.mk.injEq] at hc'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc'
    exact ⟨i, _, _, _, _, _, _, rfl, rfl, rfl, hn, ha, hb, ea, eb⟩

/-- Only variables, erasers, `CON` and `DUP` are laid out. -/
theorem Tree.shape {A : Arena} {t : HTree} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A t u ids occ) : (∃ x, t = .var x) ∨ t = .era ∨ ∃ k lb a b, cdOf t = some (k, lb, a, b) := by
  cases h with
  | var x => exact .inl ⟨x, rfl⟩
  | era => exact .inr (.inl rfl)
  | bin _ hc => exact .inr (.inr ⟨_, _, _, _, hc⟩)

theorem Tree.up_var {A : Arena} {t : HTree} {x : Nat} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A t (.var x) ids occ) : t = .var x ∧ ids = [] ∧ occ = [] := by
  cases h with
  | var => exact ⟨rfl, rfl, rfl⟩

theorem Tree.up_port {A : Arena} {t : HTree} {p : PortRef} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A t (.port p) ids occ) : p.slot = 0 ∧ p.nodeId ∈ ids := by
  cases h with
  | era => simp
  | bin => simp

/-- Occurrences sit at auxiliary ports of the tree's own nodes. -/
theorem Tree.occ_mem {A : Arena} {t : HTree} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A t u ids occ) : ∀ x p, (x, p) ∈ occ → p.nodeId ∈ ids ∧ p.slot ≠ 0 := by
  induction h with
  | var => simp
  | era => simp
  | bin i _ _ _ _ _ _ iha ihb =>
    intro x p hp
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hp; simp
    · obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hp; simp
    · have := iha x p hp; simp [this]
    · have := ihb x p hp; simp [this]

theorem nodup_iff_count {l : List Nat} : l.Nodup ↔ ∀ a, l.count a ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.nodup_cons, ih]
    constructor
    · rintro ⟨hb, h⟩ a
      rw [List.count_cons]
      by_cases hab : a = b
      · subst hab; have := List.count_eq_zero.2 hb; simp [this]
      · have := h a; have hba : ¬b = a := fun h => hab h.symm; simp [hba, this]
    · intro h
      refine ⟨fun hb => ?_, fun a => ?_⟩
      · have h1 := h b; rw [List.count_cons] at h1
        have := List.count_pos_iff.2 hb; simp at h1; omega
      · have h1 := h a; rw [List.count_cons] at h1; split at h1 <;> omega

/-- **Frame**: a layout depends only on its own nodes and on the links of its own ports other than
its occurrences and its top. -/
theorem Tree.frame {A A' : Arena} {t : HTree} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : Tree A t u ids occ) (hnd : ids.Nodup) (hn : ∀ k ∈ ids, A'.node k = A.node k)
    (hl : ∀ p : PortRef, p.nodeId ∈ ids → (∀ x, (x, p) ∉ occ) → (∀ k, u = .port ⟨k, 0⟩ → p ≠ ⟨k, 0⟩) →
      A'.link p = A.link p) :
    Tree A' t u ids occ := by
  induction h with
  | var x => exact .var x
  | era i hi => exact .era i (by rw [hn i (by simp)]; exact hi)
  | @bin t a b k lb ua ub ia ib oa ob i hc hi ha hb ea eb iha ihb =>
    rw [List.nodup_cons, List.nodup_append] at hnd
    obtain ⟨hiab, hna, hnb, hdis⟩ := hnd
    have hia : i ∉ ia := fun h => hiab (List.mem_append_left _ h)
    have hib : i ∉ ib := fun h => hiab (List.mem_append_right _ h)
    have oa_mem := ha.occ_mem
    have ob_mem := hb.occ_mem
    have notocc : ∀ p : PortRef, (∀ x, (x, p) ∈ oa → False) → (∀ x, (x, p) ∈ ob → False) →
        (∀ x, (x, p) ∈ edgeOcc ⟨i, 1⟩ ua → False) → (∀ x, (x, p) ∈ edgeOcc ⟨i, 2⟩ ub → False) →
        ∀ x, (x, p) ∉ edgeOcc ⟨i, 1⟩ ua ++ edgeOcc ⟨i, 2⟩ ub ++ oa ++ ob := by
      intro p h1 h2 h3 h4 x hx
      simp only [List.mem_append] at hx
      rcases hx with ((hx | hx) | hx) | hx
      · exact h3 x hx
      · exact h4 x hx
      · exact h1 x hx
      · exact h2 x hx
    have edge : ∀ (s : Nat) (us : Up) (is : List Nat) (os : List (Nat × PortRef)) (ts : HTree),
        (s = 1 ∨ s = 2) → is.Sublist (ia ++ ib) → (∀ x p, (x, p) ∈ os → p.nodeId ∈ is ∧ p.slot ≠ 0) →
        Tree A ts us is os → os.Sublist (oa ++ ob) → Edge A ⟨i, s⟩ us →
        (us = ua ∧ s = 1 ∨ us = ub ∧ s = 2) → Edge A' ⟨i, s⟩ us := by
      intro s us is os ts hs hsub hos ht hosub he hwhich
      cases us with
      | var => trivial
      | port q =>
        obtain ⟨hq0, hqi⟩ := ht.up_port
        have hqne : q.nodeId ≠ i := fun h => hiab (h ▸ hsub.subset hqi)
        obtain ⟨e1, e2⟩ := he
        refine ⟨?_, ?_⟩
        · rw [hl ⟨i, s⟩ (by simp) ?_ (by intro k hk; simp at hk ⊢; omega)]; exact e1
          refine notocc _ (fun x hx => hia (by simpa using (oa_mem x _ hx).1))
            (fun x hx => hib (by simpa using (ob_mem x _ hx).1)) (fun x hx => ?_) (fun x hx => ?_)
          · obtain ⟨rfl, h⟩ := mem_edgeOcc.1 hx
            rcases hwhich with ⟨h1, -⟩ | ⟨-, h2⟩
            · cases h1
            · simp at h; omega
          · obtain ⟨rfl, h⟩ := mem_edgeOcc.1 hx
            rcases hwhich with ⟨-, h1⟩ | ⟨h2, -⟩
            · simp at h; omega
            · cases h2
        · rw [hl q (by simp [hsub.subset hqi]) ?_ ?_]; exact e2
          · refine notocc _ (fun x hx => (oa_mem x _ hx).2 hq0) (fun x hx => (ob_mem x _ hx).2 hq0)
              (fun x hx => ?_) (fun x hx => ?_) <;>
            · obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx; simp at hq0
          · intro k hk; simp only [Up.port.injEq, PortRef.mk.injEq] at hk; obtain ⟨rfl, -⟩ := hk
            intro hq; apply hqne; rw [hq]
    refine .bin i hc (by rw [hn i (by simp)]; exact hi) (iha hna (fun k hk => hn k (by simp [hk])) ?_)
      (ihb hnb (fun k hk => hn k (by simp [hk])) ?_)
      (edge 1 ua ia oa a (.inl rfl) (List.sublist_append_left _ _) oa_mem ha (List.sublist_append_left _ _) ea
        (.inl ⟨rfl, rfl⟩))
      (edge 2 ub ib ob b (.inr rfl) (List.sublist_append_right _ _) ob_mem hb (List.sublist_append_right _ _) eb
        (.inr ⟨rfl, rfl⟩))
    · intro p hp hpo hpt
      have hpi : p.nodeId ≠ i := fun h => hia (h ▸ hp)
      refine hl p (by simp [hp]) (notocc _ hpo (fun x hx => hdis _ hp _ (ob_mem x _ hx).1 rfl)
        (fun x hx => hpi (by obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx; rfl))
        (fun x hx => hpi (by obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx; rfl))) ?_
      intro k hk; simp only [Up.port.injEq, PortRef.mk.injEq] at hk; obtain ⟨rfl, -⟩ := hk
      intro hpk; exact hpi (by rw [hpk])
    · intro p hp hpo hpt
      have hpi : p.nodeId ≠ i := fun h => hib (h ▸ hp)
      refine hl p (by simp [hp]) (notocc _ (fun x hx => hdis _ (oa_mem x _ hx).1 _ hp rfl) hpo
        (fun x hx => hpi (by obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx; rfl))
        (fun x hx => hpi (by obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx; rfl))) ?_
      intro k hk; simp only [Up.port.injEq, PortRef.mk.injEq] at hk; obtain ⟨rfl, -⟩ := hk
      intro hpk; exact hpi (by rw [hpk])

/-- Renaming an occurrence's variable. -/
def renOcc (f : Nat → Nat) (e : Nat × PortRef) : Nat × PortRef := (f e.1, e.2)

theorem cdOf_rename (f : Nat → Nat) {t a b : HTree} {k : INetNodeKind} {lb : Nat}
    (h : cdOf t = some (k, lb, a, b)) : cdOf (t.rename f) = some (k, lb, a.rename f, b.rename f) := by
  cases t <;> simp [cdOf, HTree.rename] at h ⊢ <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> simp

theorem edge_rename (A : Arena) (p : PortRef) (f : Nat → Nat) (u : Up) :
    Edge A p (u.rename f) ↔ Edge A p u := by
  cases u <;> rfl

theorem edgeOcc_rename (p : PortRef) (f : Nat → Nat) (u : Up) :
    edgeOcc p (u.rename f) = (edgeOcc p u).map (renOcc f) := by
  cases u <;> rfl

/-- Renaming variables renames occurrences and changes nothing else. -/
theorem Tree.rename {A : Arena} {t : HTree} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (f : Nat → Nat) (h : Tree A t u ids occ) :
    Tree A (t.rename f) (u.rename f) ids (occ.map (renOcc f)) := by
  induction h with
  | var x => exact .var (f x)
  | era i hi => exact .era i hi
  | bin i hc hi _ _ ea eb iha ihb =>
    have := Tree.bin i (cdOf_rename f hc) hi iha ihb ((edge_rename _ _ _ _).2 ea) ((edge_rename _ _ _ _).2 eb)
    rw [edgeOcc_rename, edgeOcc_rename] at this
    simpa only [List.map_append, Up.rename] using this

theorem facing_rename {A : Arena} {ua ub : Up} {o : List (Nat × PortRef)} (f : Nat → Nat)
    (h : Facing A ua ub o) : Facing A (ua.rename f) (ub.rename f) (o.map (renOcc f)) := by
  cases ua <;> cases ub <;> simp_all [Facing, Up.rename, renOcc]

theorem BagIn.rename {A : Arena} {bag : List Redex} {ids : List Nat} {occ : List (Nat × PortRef)}
    (f : Nat → Nat) (h : BagIn A bag ids occ) :
    BagIn A (bag.map (Redex.rename f)) ids (occ.map (renOcc f)) := by
  induction h with
  | nil => exact .nil
  | cons ha hb hf _ ih =>
    simpa [List.map_append, Redex.rename] using BagIn.cons (ha.rename f) (hb.rename f) (facing_rename f hf) ih

theorem BagIn.append_iff {A : Arena} {xs ys : List Redex} {ids : List Nat} {occ : List (Nat × PortRef)} :
    BagIn A (xs ++ ys) ids occ ↔
      ∃ i1 i2 o1 o2, BagIn A xs i1 o1 ∧ BagIn A ys i2 o2 ∧ ids = i1 ++ i2 ∧ occ = o1 ++ o2 := by
  induction xs generalizing ids occ with
  | nil =>
    constructor
    · intro h; exact ⟨[], ids, [], occ, .nil, h, rfl, rfl⟩
    · rintro ⟨i1, i2, o1, o2, h1, h2, rfl, rfl⟩; cases h1; exact h2
  | cons r xs ih =>
    constructor
    · intro h
      cases h with
      | cons ha hb hf hr =>
        obtain ⟨i1, i2, o1, o2, h1, h2, rfl, rfl⟩ := ih.1 hr
        exact ⟨_, i2, _, o2, .cons ha hb hf h1, h2, by simp, by simp⟩
    · rintro ⟨i1, i2, o1, o2, h1, h2, rfl, rfl⟩
      cases h1 with
      | cons ha hb hf hr =>
        have := BagIn.cons ha hb hf (ih.2 ⟨_, i2, _, o2, hr, h2, rfl, rfl⟩)
        simpa using this

theorem facing_occ {A : Arena} {ua ub : Up} {o : List (Nat × PortRef)} (h : Facing A ua ub o)
    {x : Nat} {p : PortRef} (hp : (x, p) ∈ o) : ua = .port p ∨ ub = .port p := by
  cases ua <;> cases ub <;> simp_all [Facing]

/-- Occurrences in a bag sit at ports of its own nodes. -/
theorem BagIn.occ_mem {A : Arena} {bag : List Redex} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : BagIn A bag ids occ) : ∀ x p, (x, p) ∈ occ → p.nodeId ∈ ids := by
  induction h with
  | nil => simp
  | cons ha hb hf _ ih =>
    intro x p hp
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · simp [(ha.occ_mem x p hp).1]
    · simp [(hb.occ_mem x p hp).1]
    · rcases facing_occ hf hp with h | h
      · subst h; simp [ha.up_port.2]
      · subst h; simp [hb.up_port.2]
    · simp [ih x p hp]

/-- Occurrences at a principal port in a bag are those of a redex's variable side. -/
theorem BagIn.occ_slot0 {A : Arena} {bag : List Redex} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : BagIn A bag ids occ) : ∀ x p, (x, p) ∈ occ → p.slot = 0 →
      ∃ pre post t, bag = pre ++ (.var x, t) :: post ∨ bag = pre ++ (t, .var x) :: post := by
  induction h with
  | nil => simp
  | @cons a b rs ua ub ia ib is oa ob o os ha hb hf _ ih =>
    intro x p hp h0
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · exact absurd h0 (ha.occ_mem x p hp).2
    · exact absurd h0 (hb.occ_mem x p hp).2
    · cases ua <;> cases ub <;> simp only [Facing] at hf
      · obtain ⟨-, -, rfl⟩ := hf; simp at hp
      · subst hf; simp at hp; obtain ⟨rfl, -⟩ := hp
        obtain ⟨rfl, -, -⟩ := hb.up_var
        exact ⟨[], rs, a, .inr rfl⟩
      · subst hf; simp at hp; obtain ⟨rfl, -⟩ := hp
        obtain ⟨rfl, -, -⟩ := ha.up_var
        exact ⟨[], rs, b, .inl rfl⟩
    · obtain ⟨pre, post, t, h⟩ := ih x p hp h0
      refine ⟨(a, b) :: pre, post, t, ?_⟩
      rcases h with h | h <;> simp [h]

/-- **Frame** for a bag: it depends only on its nodes and the links of its ports other than its
occurrences. -/
theorem BagIn.frame {A A' : Arena} {bag : List Redex} {ids : List Nat} {occ : List (Nat × PortRef)}
    (h : BagIn A bag ids occ) (hnd : ids.Nodup) (hn : ∀ k ∈ ids, A'.node k = A.node k)
    (hl : ∀ p : PortRef, p.nodeId ∈ ids → (∀ x, (x, p) ∉ occ) → A'.link p = A.link p) :
    BagIn A' bag ids occ := by
  induction h with
  | nil => exact .nil
  | @cons a b rs ua ub ia ib is oa ob o os ha hb hf hr ih =>
    rw [List.nodup_append, List.nodup_append] at hnd
    obtain ⟨⟨hna, hnb, hab⟩, hns, hdis⟩ := hnd
    have oa_mem := ha.occ_mem
    have ob_mem := hb.occ_mem
    have os_mem := hr.occ_mem
    -- a port of one part is an occurrence of the whole only if it is one of that part
    have notin : ∀ p : PortRef, (∀ x, (x, p) ∈ oa → False) → (∀ x, (x, p) ∈ ob → False) →
        (∀ x, (x, p) ∈ o → False) → (∀ x, (x, p) ∈ os → False) → ∀ x, (x, p) ∉ oa ++ ob ++ o ++ os := by
      intro p h1 h2 h3 h4 x hx
      simp only [List.mem_append] at hx
      rcases hx with ((hx | hx) | hx) | hx
      · exact h1 x hx
      · exact h2 x hx
      · exact h3 x hx
      · exact h4 x hx
    have fac : ∀ x p, (x, p) ∈ o → (ua = .port p ∧ p.nodeId ∈ ia) ∨ (ub = .port p ∧ p.nodeId ∈ ib) := by
      intro x p hp
      rcases facing_occ hf hp with h | h
      · exact .inl ⟨h, by subst h; exact ha.up_port.2⟩
      · exact .inr ⟨h, by subst h; exact hb.up_port.2⟩
    refine .cons (ha.frame hna (fun k hk => hn k (by simp [hk])) ?_) (hb.frame hnb (fun k hk => hn k (by simp [hk])) ?_)
      ?_ (ih hns (fun k hk => hn k (by simp [hk])) ?_)
    · intro p hp hpo hpt
      refine hl p (by simp [hp]) (notin p hpo (fun x hx => hab _ hp _ (ob_mem x p hx).1 rfl) (fun x hx => ?_)
        (fun x hx => hdis _ (by simp [hp]) _ (os_mem x p hx) rfl))
      rcases fac x p hx with ⟨h, -⟩ | ⟨-, h'⟩
      · have h0 : p.slot = 0 := by subst h; exact ha.up_port.1
        obtain ⟨n, s⟩ := p
        simp only at h0; subst h0
        exact hpt n h rfl
      · exact hab _ hp _ h' rfl
    · intro p hp hpo hpt
      refine hl p (by simp [hp]) (notin p (fun x hx => hab _ (oa_mem x p hx).1 _ hp rfl) hpo (fun x hx => ?_)
        (fun x hx => hdis _ (by simp [hp]) _ (os_mem x p hx) rfl))
      rcases fac x p hx with ⟨-, h'⟩ | ⟨h, -⟩
      · exact hab _ h' _ hp rfl
      · have h0 : p.slot = 0 := by subst h; exact hb.up_port.1
        obtain ⟨n, s⟩ := p
        simp only at h0; subst h0
        exact hpt n h rfl
    · cases ua <;> cases ub <;> simp only [Facing] at hf ⊢
      · rename_i p q
        obtain ⟨e1, e2, rfl⟩ := hf
        have hp := ha.up_port
        have hq := hb.up_port
        refine ⟨?_, ?_, rfl⟩
        · rw [hl p (by simp [hp.2]) (notin p (fun x hx => (oa_mem x p hx).2 hp.1) (fun x hx => (ob_mem x p hx).2 hp.1)
            (fun x hx => by simp at hx) (fun x hx => hdis _ (by simp [hp.2]) _ (os_mem x p hx) rfl))]; exact e1
        · rw [hl q (by simp [hq.2]) (notin q (fun x hx => (oa_mem x q hx).2 hq.1) (fun x hx => (ob_mem x q hx).2 hq.1)
            (fun x hx => by simp at hx) (fun x hx => hdis _ (by simp [hq.2]) _ (os_mem x q hx) rfl))]; exact e2
      · exact hf
      · exact hf
    · intro p hp hpo
      refine hl p (by simp [hp]) (notin p ?_ ?_ ?_ hpo)
      · intro x hx; exact hdis _ (by simp [(oa_mem x p hx).1]) _ hp rfl
      · intro x hx; exact hdis _ (by simp [(ob_mem x p hx).1]) _ hp rfl
      · intro x hx
        rcases fac x p hx with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact hdis _ (by simp [h']) _ hp rfl
        · exact hdis _ (by simp [h']) _ hp rfl

theorem subst_one_var (x y : Nat) : ∀ t : HTree,
    t.subst (one x (.var y)) = t.rename (fun z => if z = x then y else z)
  | .var n => by by_cases h : n = x <;> simp [HTree.subst, HTree.rename, one, h]
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b => by simp [HTree.subst, HTree.rename, subst_one_var x y a, subst_one_var x y b]
  | .dup a b => by simp [HTree.subst, HTree.rename, subst_one_var x y a, subst_one_var x y b]
  | .opr a b => by simp [HTree.subst, HTree.rename, subst_one_var x y a, subst_one_var x y b]
  | .swi a b => by simp [HTree.subst, HTree.rename, subst_one_var x y a, subst_one_var x y b]

theorem redex_subst_one_var (x y : Nat) (r : Redex) :
    r.subst (one x (.var y)) = r.rename (fun z => if z = x then y else z) := by
  simp [Redex.subst, Redex.rename, subst_one_var]

theorem rename_id' : ∀ t : HTree, t.rename (fun x => x) = t
  | .var _ => rfl
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b => by simp [HTree.rename, rename_id' a, rename_id' b]
  | .dup a b => by simp [HTree.rename, rename_id' a, rename_id' b]
  | .opr a b => by simp [HTree.rename, rename_id' a, rename_id' b]
  | .swi a b => by simp [HTree.rename, rename_id' a, rename_id' b]

theorem rename_rename (f g : Nat → Nat) : ∀ t : HTree, (t.rename f).rename g = t.rename (fun x => g (f x))
  | .var _ => rfl
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b => by simp [HTree.rename, rename_rename f g a, rename_rename f g b]
  | .dup a b => by simp [HTree.rename, rename_rename f g a, rename_rename f g b]
  | .opr a b => by simp [HTree.rename, rename_rename f g a, rename_rename f g b]
  | .swi a b => by simp [HTree.rename, rename_rename f g a, rename_rename f g b]

theorem paired_congr {A : Arena} {L1 L2 : List (Nat × PortRef)} (h : ∀ e, e ∈ L1 ↔ e ∈ L2)
    (hP : Paired A L1) : Paired A L2 := by
  intro x p hp
  obtain ⟨h1, h2, h3⟩ := hP x p ((h _).2 hp)
  exact ⟨(h _).1 h1, h2, h3⟩

theorem nodup_fresh {F L : List Nat} {n : Nat} (hF : F.Nodup) (hFn : ∀ k ∈ F, n ≤ k) (hL : L.Nodup)
    (hLn : ∀ k ∈ L, k < n) : (F ++ L).Nodup :=
  List.nodup_append.2 ⟨hF, hL, fun a ha b hb hab => by have := hFn a ha; have := hLn b hb; omega⟩

/-- A configuration's layout around one redex. -/
theorem repr_split {A : Arena} {ρ : PortRef} {root a b : HTree} {pre post : List Redex}
    (h : Repr A ρ ⟨root, pre ++ (a, b) :: post⟩) :
    ∃ (u ua ub : Up) (ir ipre ipost ia ib : List Nat) (or opre opost oa ob o : List (Nat × PortRef)),
      Tree A root u ir or ∧ Edge A ρ u ∧ BagIn A pre ipre opre ∧ BagIn A post ipost opost ∧
      Tree A a ua ia oa ∧ Tree A b ub ib ob ∧ Facing A ua ub o ∧
      (ir ++ ipre ++ ipost ++ (ia ++ ib)).Nodup ∧ (∀ k ∈ ir ++ ipre ++ ipost ++ (ia ++ ib), k < A.next) ∧
      (∀ k, A.node k ≠ none → k ∈ ir ++ ipre ++ ipost ++ (ia ++ ib)) ∧
      ρ.nodeId < A.next ∧ ρ.nodeId ∉ ir ++ ipre ++ ipost ++ (ia ++ ib) ∧
      Paired A (edgeOcc ρ u ++ or ++ opre ++ opost ++ (oa ++ ob ++ o)) := by
  obtain ⟨u, ir, ibag, or, obag, ht, he, hb, hnd, hlt, hall, hρ, hρn, hP⟩ := h
  obtain ⟨ipre, irest, opre, orest, hpre, hrest, rfl, rfl⟩ := BagIn.append_iff.1 hb
  cases hrest with
  | @cons _ _ _ ua ub ia ib ipost oa ob o opost ha hb' hf hpost =>
    have hperm : (ir ++ (ipre ++ (ia ++ ib ++ ipost))).Perm (ir ++ ipre ++ ipost ++ (ia ++ ib)) :=
      List.perm_iff_count.2 fun k => by simp only [List.count_append]; omega
    refine ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, ha, hb', hf,
      hperm.nodup_iff.1 hnd, fun k hk => hlt k (hperm.mem_iff.2 hk), fun k hk => hperm.mem_iff.1 (hall k hk),
      hρ, fun h => hρn (hperm.mem_iff.2 h), paired_congr (fun e => (List.perm_iff_count.2 fun e => ?_).mem_iff) hP⟩
    simp only [List.count_append]; omega

/-- A layout assembled around a new middle, all variables renamed by `f` (HVM2's LINK of variables). -/
theorem repr_join {A : Arena} {ρ : PortRef} {root : HTree} {pre post M : List Redex} {f : Nat → Nat}
    {u : Up} {ir ipre ipost im : List Nat} {or opre opost om : List (Nat × PortRef)}
    (ht : Tree A root u ir or) (he : Edge A ρ u) (hpre : BagIn A pre ipre opre) (hpost : BagIn A post ipost opost)
    (hm : BagIn A M im om) (hnd : (ir ++ ipre ++ ipost ++ im).Nodup)
    (hlt : ∀ k ∈ ir ++ ipre ++ ipost ++ im, k < A.next)
    (hall : ∀ k, A.node k ≠ none → k ∈ ir ++ ipre ++ ipost ++ im)
    (hρ : ρ.nodeId < A.next) (hρn : ρ.nodeId ∉ ir ++ ipre ++ ipost ++ im)
    (hP : Paired A ((edgeOcc ρ u ++ or ++ opre ++ opost ++ om).map (renOcc f))) :
    Repr A ρ ⟨root.rename f, (pre ++ M ++ post).map (Redex.rename f)⟩ := by
  have hbag : BagIn A (pre ++ M ++ post) (ipre ++ (im ++ ipost)) (opre ++ (om ++ opost)) := by
    rw [List.append_assoc]
    exact BagIn.append_iff.2 ⟨_, _, _, _, hpre, BagIn.append_iff.2 ⟨_, _, _, _, hm, hpost, rfl, rfl⟩, rfl, rfl⟩
  have hperm : (ir ++ (ipre ++ (im ++ ipost))).Perm (ir ++ ipre ++ ipost ++ im) :=
    List.perm_iff_count.2 fun k => by simp only [List.count_append]; omega
  refine ⟨u.rename f, ir, ipre ++ (im ++ ipost), or.map (renOcc f), (opre ++ (om ++ opost)).map (renOcc f),
    ht.rename f, (edge_rename _ _ _ _).2 he, hbag.rename f, hperm.nodup_iff.2 hnd,
    fun k hk => hlt k (hperm.mem_iff.1 hk), fun k hk => hperm.mem_iff.2 (hall k hk), hρ,
    fun h => hρn (hperm.mem_iff.1 h), paired_congr (fun e => (List.perm_iff_count.2 fun e => ?_).mem_iff) hP⟩
  simp only [edgeOcc_rename, List.map_append, List.count_append]; omega

/-- **Pairing across a rewrite**: the occurrences `K` survive, those at the pair's auxiliary ports
`Ds` (`D`) go, new ones `N` come; links change only at fresh ports and at the ports across the wires
from `Ds`. Then the occurrences stay paired, as long as each of those ports and each new occurrence
is, and every variable renamed by `f`. -/
theorem paired_transfer {A A' : Arena} {K D N : List (Nat × PortRef)} {Ds : List PortRef} {n : Nat}
    {f : Nat → Nat} (hP : Paired A (K ++ D)) (hD : ∀ x p, (x, p) ∈ D → p ∈ Ds)
    (hKd : ∀ x p, (x, p) ∈ K → p ∉ Ds) (hKo : ∀ x p, (x, p) ∈ K → p.nodeId < n)
    (hinv : ∀ d ∈ Ds, A.link (A.link d) = d)
    (hfr : ∀ p : PortRef, (∀ d ∈ Ds, p ≠ A.link d) → p.nodeId < n → A'.link p = A.link p)
    (hB : ∀ x d, d ∈ Ds → (x, A.link d) ∈ K →
      (f x, A'.link (A.link d)) ∈ (K ++ N).map (renOcc f) ∧ A'.link (A.link d) ≠ A.link d ∧
        A'.link (A'.link (A.link d)) = A.link d)
    (hN : ∀ x p, (x, p) ∈ N →
      (f x, A'.link p) ∈ (K ++ N).map (renOcc f) ∧ A'.link p ≠ p ∧ A'.link (A'.link p) = p) :
    Paired A' ((K ++ N).map (renOcc f)) := by
  intro y p hp
  obtain ⟨⟨x, p'⟩, hmem, heq⟩ := List.mem_map.1 hp
  simp only [renOcc, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  rcases List.mem_append.1 hmem with hK | hN'
  · by_cases hb : ∃ d ∈ Ds, p' = A.link d
    · obtain ⟨d, hd, rfl⟩ := hb
      exact hB x d hd hK
    · have hb' : ∀ d ∈ Ds, p' ≠ A.link d := fun d hd h => hb ⟨d, hd, h⟩
      rw [hfr p' hb' (hKo x p' hK)]
      obtain ⟨hq, hne, hback⟩ := hP x p' (List.mem_append_left _ hK)
      rcases List.mem_append.1 hq with hqK | hqD
      · have hq' : ∀ d ∈ Ds, A.link p' ≠ A.link d := by
          intro d hd h
          apply hKd x p' hK
          have : A.link (A.link p') = A.link (A.link d) := by rw [h]
          rw [hback, hinv d hd] at this
          exact this ▸ hd
        refine ⟨List.mem_map.2 ⟨(x, A.link p'), List.mem_append_left _ hqK, rfl⟩, hne, ?_⟩
        rw [hfr _ hq' (hKo x _ hqK), hback]
      · exact absurd ⟨A.link p', hD x _ hqD, hback.symm⟩ hb
  · exact hN x p' hN'

/-! ## The commutation arena -/

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-- The arena `Arena.apply` gives for a commutation of `l ~ r`. -/
def commArena (A : Arena) (l r : INetNode) : Arena :=
  { (commuteSpawnedNodes l r A.next).foldl Arena.place ((A.drop l.id).drop r.id) with
    next := A.next + 4 }.splice (commuteSplices l r A.next)

theorem apply_commute (A : Arena) (l r : INetNode) :
    A.apply l r (.commute (commuteSpawnedNodes l r A.next) (commuteSplices l r A.next)) = some (commArena A l r) := rfl

theorem commArena_next (A : Arena) (l r : INetNode) : (commArena A l r).next = A.next + 4 := rfl

theorem commArena_node (A : Arena) (l r : INetNode) (k : Nat) :
    (commArena A l r).node k =
      if k = A.next + 3 then some (l.kind, l.label, l.immVal) else
      if k = A.next + 2 then some (l.kind, l.label, l.immVal) else
      if k = A.next + 1 then some (r.kind, r.label, r.immVal) else
      if k = A.next then some (r.kind, r.label, r.immVal) else
      if k = r.id then none else if k = l.id then none else A.node k := by
  simp only [commArena, commuteSpawnedNodes, commuteSplices, List.foldl, Arena.splice, Arena.connect_node,
    Arena.place_node, Arena.drop_node]

/-- The commutation arena's links, given four distinct outside ports older than the fresh ids. -/
theorem commArena_link (A : Arena) (l r : INetNode)
    (hd : [l.aux1, l.aux2, r.aux1, r.aux2].Nodup)
    (ho : ∀ p ∈ [l.aux1, l.aux2, r.aux1, r.aux2], p.nodeId < A.next) :
    let n := A.next
    let L := (commArena A l r).link
    (∀ p : PortRef, p.nodeId < n → p ∉ [l.aux1, l.aux2, r.aux1, r.aux2] → L p = A.link p) ∧
    L ⟨n, 0⟩ = l.aux1 ∧ L l.aux1 = ⟨n, 0⟩ ∧ L ⟨n + 1, 0⟩ = l.aux2 ∧ L l.aux2 = ⟨n + 1, 0⟩ ∧
    L ⟨n + 2, 0⟩ = r.aux1 ∧ L r.aux1 = ⟨n + 2, 0⟩ ∧ L ⟨n + 3, 0⟩ = r.aux2 ∧ L r.aux2 = ⟨n + 3, 0⟩ ∧
    L ⟨n, 1⟩ = ⟨n + 2, 1⟩ ∧ L ⟨n, 2⟩ = ⟨n + 3, 1⟩ ∧ L ⟨n + 1, 1⟩ = ⟨n + 2, 2⟩ ∧ L ⟨n + 1, 2⟩ = ⟨n + 3, 2⟩ ∧
    L ⟨n + 2, 1⟩ = ⟨n, 1⟩ ∧ L ⟨n + 2, 2⟩ = ⟨n + 1, 1⟩ ∧ L ⟨n + 3, 1⟩ = ⟨n, 2⟩ ∧ L ⟨n + 3, 2⟩ = ⟨n + 1, 2⟩ := by
  dsimp only
  generalize hn : A.next = n
  obtain ⟨li, lk, ll, lv, ⟨x1, s1⟩, ⟨x2, s2⟩⟩ := l
  obtain ⟨ri, rk, rl, rv, ⟨y1, t1⟩, ⟨y2, t2⟩⟩ := r
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, PortRef.mk.injEq,
    not_or, not_and] at hd
  obtain ⟨h1, h2, h3, h4⟩ := ho
  obtain ⟨⟨e12, e13, e14⟩, ⟨e23, e24⟩, e34, -⟩ := hd
  have hL : ∀ q, (commArena A ⟨li, lk, ll, lv, ⟨x1, s1⟩, ⟨x2, s2⟩⟩ ⟨ri, rk, rl, rv, ⟨y1, t1⟩, ⟨y2, t2⟩⟩).link q = (if q = ⟨y2, t2⟩ then ⟨n + 3, 0⟩ else if q = ⟨n + 3, 0⟩ then ⟨y2, t2⟩ else
      if q = ⟨y1, t1⟩ then ⟨n + 2, 0⟩ else if q = ⟨n + 2, 0⟩ then ⟨y1, t1⟩ else
      if q = ⟨x2, s2⟩ then ⟨n + 1, 0⟩ else if q = ⟨n + 1, 0⟩ then ⟨x2, s2⟩ else
      if q = ⟨x1, s1⟩ then ⟨n, 0⟩ else if q = ⟨n, 0⟩ then ⟨x1, s1⟩ else
      if q = ⟨n + 3, 2⟩ then ⟨n + 1, 2⟩ else if q = ⟨n + 3, 1⟩ then ⟨n, 2⟩ else
      if q = ⟨n + 2, 2⟩ then ⟨n + 1, 1⟩ else if q = ⟨n + 2, 1⟩ then ⟨n, 1⟩ else
      if q = ⟨n + 1, 2⟩ then ⟨n + 3, 2⟩ else if q = ⟨n + 1, 1⟩ then ⟨n + 2, 2⟩ else
      if q = ⟨n, 2⟩ then ⟨n + 3, 1⟩ else if q = ⟨n, 1⟩ then ⟨n + 2, 1⟩ else A.link q) := fun q => by subst hn; rfl
  refine ⟨fun p hp hq => ?_, ?_⟩
  · obtain ⟨pn, ps⟩ := p
    simp only [List.mem_cons, List.not_mem_nil, or_false, PortRef.mk.injEq, not_or, not_and] at hq
    dsimp only at hp
    obtain ⟨q1, q2, q3, q4⟩ := hq
    rw [hL]
    simp only [PortRef.mk.injEq]
    repeat' rw [ite_neg' (by omega)]
  · simp only [hL, PortRef.mk.injEq, and_true, true_and, ite_true]
    repeat' apply And.intro
    all_goals (repeat' first | rw [ite_pos' (by omega)] | rw [ite_neg' (by omega)]) <;> rfl

/-! ## The annihilation and erasure arenas -/

theorem annArena_link (A : Arena) (i j : Nat) (q1 q2 q3 q4 : PortRef) (hd : [q1, q2, q3, q4].Nodup) :
    let L := (((A.drop i).drop j |>.connect q1 q3).connect q2 q4).link
    (∀ p : PortRef, p ∉ [q1, q2, q3, q4] → L p = A.link p) ∧
    L q1 = q3 ∧ L q3 = q1 ∧ L q2 = q4 ∧ L q4 = q2 := by
  dsimp only
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34, -⟩ := hd
  simp only [Arena.connect_link, Arena.drop_link]
  refine ⟨fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
    obtain ⟨p1, p2, p3, p4⟩ := hp
    simp [p1, p2, p3, p4]
  all_goals simp [n12, n13, n14, n24, n34, Ne.symm n23]

theorem annArena_node (A : Arena) (i j : Nat) (q1 q2 q3 q4 : PortRef) (k : Nat) :
    (((A.drop i).drop j |>.connect q1 q3).connect q2 q4).node k = if k = j then none else if k = i then none else A.node k := by
  simp only [Arena.connect_node, Arena.drop_node]

theorem eraArena_eq (A : Arena) (q1 q2 : PortRef) :
    A.erasers [q1, q2] = ({ ({ A.place (mkEraNode A.next) with next := A.next + 1 }.connect ⟨A.next, 0⟩ q1).place
      (mkEraNode (A.next + 1)) with next := A.next + 2 }.connect ⟨A.next + 1, 0⟩ q2) := rfl

theorem eraArena_facts (A : Arena) (q1 q2 : PortRef) (hd : q1 ≠ q2) (h1 : q1.nodeId < A.next)
    (h2 : q2.nodeId < A.next) :
    let E := A.erasers [q1, q2]
    E.next = A.next + 2 ∧
    (∀ k, E.node k = if k = A.next + 1 then some (.era, 0, 0) else if k = A.next then some (.era, 0, 0) else A.node k) ∧
    (∀ p : PortRef, p.nodeId < A.next → p ≠ q1 → p ≠ q2 → E.link p = A.link p) ∧
    E.link ⟨A.next, 0⟩ = q1 ∧ E.link q1 = ⟨A.next, 0⟩ ∧ E.link ⟨A.next + 1, 0⟩ = q2 ∧ E.link q2 = ⟨A.next + 1, 0⟩ := by
  dsimp only
  rw [eraArena_eq]
  obtain ⟨x1, s1⟩ := q1
  obtain ⟨x2, s2⟩ := q2
  dsimp only at h1 h2
  have hE : ∀ q : PortRef, ({ ({ A.place (mkEraNode A.next) with next := A.next + 1 }.connect ⟨A.next, 0⟩ ⟨x1, s1⟩).place
      (mkEraNode (A.next + 1)) with next := A.next + 2 }.connect ⟨A.next + 1, 0⟩ ⟨x2, s2⟩).link q =
      if q = ⟨x2, s2⟩ then ⟨A.next + 1, 0⟩ else if q = ⟨A.next + 1, 0⟩ then ⟨x2, s2⟩ else
      if q = ⟨A.next + 1, 2⟩ then ⟨0, 0⟩ else if q = ⟨A.next + 1, 1⟩ then ⟨0, 0⟩ else
      if q = ⟨x1, s1⟩ then ⟨A.next, 0⟩ else if q = ⟨A.next, 0⟩ then ⟨x1, s1⟩ else
      if q = ⟨A.next, 2⟩ then ⟨0, 0⟩ else if q = ⟨A.next, 1⟩ then ⟨0, 0⟩ else A.link q := fun q => rfl
  refine ⟨rfl, fun k => ?_, fun p hp hp1 hp2 => ?_, ?_⟩
  · simp only [Arena.connect_node, Arena.place_node, mkEraNode]
  · obtain ⟨pn, ps⟩ := p
    dsimp only at hp
    rw [hE]
    simp only [ne_eq, PortRef.mk.injEq, not_and] at hp1 hp2
    simp only [PortRef.mk.injEq]
    repeat' rw [ite_neg' (by omega)]
  · simp only [hE, PortRef.mk.injEq, and_true, true_and, ite_true]
    simp only [ne_eq, PortRef.mk.injEq, not_and] at hd
    repeat' apply And.intro
    all_goals (repeat' first | rw [ite_pos' (by omega)] | rw [ite_neg' (by omega)]) <;> rfl

/-! ## The context of a redex -/

theorem ctx_occ {A : Arena} {ρ : PortRef} {root : HTree} {pre post : List Redex} {u : Up}
    {ir ipre ipost : List Nat} {or opre opost : List (Nat × PortRef)}
    (ht : Tree A root u ir or) (hpre : BagIn A pre ipre opre) (hpost : BagIn A post ipost opost) :
    ∀ x p, (x, p) ∈ edgeOcc ρ u ++ or ++ opre ++ opost → p = ρ ∨ p.nodeId ∈ ir ++ ipre ++ ipost := by
  intro x p hp
  simp only [List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · exact .inl (mem_edgeOcc.1 hp).2
  · exact .inr (by simp [(ht.occ_mem x p hp).1])
  · exact .inr (by simp [hpre.occ_mem x p hp])
  · exact .inr (by simp [hpost.occ_mem x p hp])

/-- **Frame** for the context of a redex: the root tree, its wire to `ρ`, and the redexes before and
after. -/
theorem ctx_frame {A A' : Arena} {ρ : PortRef} {root : HTree} {pre post : List Redex} {u : Up}
    {ir ipre ipost : List Nat} {or opre opost : List (Nat × PortRef)}
    (ht : Tree A root u ir or) (he : Edge A ρ u) (hpre : BagIn A pre ipre opre) (hpost : BagIn A post ipost opost)
    (hnd : (ir ++ ipre ++ ipost).Nodup) (hρ : ρ.nodeId ∉ ir ++ ipre ++ ipost)
    (hn : ∀ k ∈ ir ++ ipre ++ ipost, A'.node k = A.node k)
    (hl : ∀ p : PortRef, (p.nodeId ∈ ir ++ ipre ++ ipost ∨ p = ρ) →
      (∀ x, (x, p) ∉ edgeOcc ρ u ++ or ++ opre ++ opost) → A'.link p = A.link p) :
    Tree A' root u ir or ∧ Edge A' ρ u ∧ BagIn A' pre ipre opre ∧ BagIn A' post ipost opost := by
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨hnr, hnpre, hd1⟩, hnpost, hd2⟩ := hnd
  have or_mem := ht.occ_mem
  have opre_mem := hpre.occ_mem
  have opost_mem := hpost.occ_mem
  have notin : ∀ p : PortRef, (∀ x, (x, p) ∈ edgeOcc ρ u → False) → (∀ x, (x, p) ∈ or → False) →
      (∀ x, (x, p) ∈ opre → False) → (∀ x, (x, p) ∈ opost → False) →
      ∀ x, (x, p) ∉ edgeOcc ρ u ++ or ++ opre ++ opost := by
    intro p h1 h2 h3 h4 x hx
    simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact h1 x hx
    · exact h2 x hx
    · exact h3 x hx
    · exact h4 x hx
  have ρne : ∀ p : PortRef, p.nodeId ∈ ir ++ ipre ++ ipost → ∀ x, (x, p) ∈ edgeOcc ρ u → False := by
    intro p hp x hx
    obtain ⟨-, rfl⟩ := mem_edgeOcc.1 hx
    exact hρ hp
  refine ⟨ht.frame hnr (fun k hk => hn k (by simp [hk])) ?_, ?_, hpre.frame hnpre (fun k hk => hn k (by simp [hk])) ?_,
    hpost.frame hnpost (fun k hk => hn k (by simp [hk])) ?_⟩
  · intro p hp hpo hpt
    exact hl p (.inl (by simp [hp])) (notin p (ρne p (by simp [hp])) hpo
      (fun x hx => hd1 _ hp _ (opre_mem x p hx) rfl)
      (fun x hx => hd2 _ (by simp [hp]) _ (opost_mem x p hx) rfl))
  · cases u with
    | var => trivial
    | port q =>
      obtain ⟨e1, e2⟩ := he
      obtain ⟨hq0, hqi⟩ := ht.up_port
      refine ⟨?_, ?_⟩
      · rw [hl ρ (.inr rfl) (notin ρ (fun x hx => by simp [edgeOcc] at hx)
          (fun x hx => hρ (by simp [(or_mem x ρ hx).1]))
          (fun x hx => hρ (by simp [opre_mem x ρ hx])) (fun x hx => hρ (by simp [opost_mem x ρ hx])))]
        exact e1
      · rw [hl q (.inl (by simp [hqi])) (notin q (fun x hx => by simp [edgeOcc] at hx)
          (fun x hx => (or_mem x q hx).2 hq0)
          (fun x hx => hd1 _ hqi _ (opre_mem x q hx) rfl)
          (fun x hx => hd2 _ (by simp [hqi]) _ (opost_mem x q hx) rfl))]
        exact e2
  · intro p hp hpo
    exact hl p (.inl (by simp [hp])) (notin p (ρne p (by simp [hp]))
      (fun x hx => hd1 _ (or_mem x p hx).1 _ hp rfl) hpo
      (fun x hx => hd2 _ (by simp [hp]) _ (opost_mem x p hx) rfl))
  · intro p hp hpo
    exact hl p (.inl (by simp [hp])) (notin p (ρne p (by simp [hp]))
      (fun x hx => hd2 _ (by simp [(or_mem x p hx).1]) _ hp rfl)
      (fun x hx => hd2 _ (by simp [opre_mem x p hx]) _ hp rfl) hpo)

/-- The far side of a node's auxiliary wire: the port across it leads back, and is the child's
principal port or another occurrence of the child variable. -/
theorem boundary {A : Arena} {occ : List (Nat × PortRef)} (hP : Paired A occ) {d : PortRef} {t : HTree}
    {us : Up} {is : List Nat} {os : List (Nat × PortRef)} (ht : Tree A t us is os) (he : Edge A d us)
    (hs : d.slot ≠ 0) (hin : ∀ x, us = .var x → (x, d) ∈ occ) :
    A.link (A.link d) = d ∧ A.link d ≠ d ∧ (∀ c, us = .port c → A.link d = c) ∧
      (∀ x, us = .var x → (x, A.link d) ∈ occ) := by
  cases us with
  | port c =>
    obtain ⟨e1, e2⟩ := he
    have hc0 := ht.up_port.1
    refine ⟨by rw [e1, e2], ?_, fun c' h => (by cases h; exact e1), fun x h => (by cases h)⟩
    rw [e1]; intro h; rw [h] at hc0; exact hs hc0
  | var x =>
    obtain ⟨h1, h2, h3⟩ := hP x _ (hin x rfl)
    exact ⟨h3, h2, fun c h => (by cases h), fun y h => (by cases h; exact h1)⟩

/-! ## Binary nodes -/

/-- HVM2's `CON` and `DUP` as the machine's kind and label. -/
def binInet : BinKind → INetNodeKind × Nat
  | .con => (.con, 0)
  | .dup => (.dup, 1)
  | .opr => (.con, 2)
  | .swi => (.con, 3)

theorem bin_cd {A : Arena} {t a1 a2 : HTree} {ka : BinKind} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (ht : Tree A t u ids occ) (hb : t.bin? = some (ka, a1, a2)) :
    (ka = .con ∨ ka = .dup) ∧ cdOf t = some ((binInet ka).1, (binInet ka).2, a1, a2) := by
  rcases ht.shape with ⟨x, rfl⟩ | rfl | ⟨k, lb, a, b, hc⟩
  · simp [HTree.bin?] at hb
  · simp [HTree.bin?] at hb
  · cases t <;> simp [cdOf] at hc <;> simp [HTree.bin?] at hb <;> obtain ⟨rfl, rfl, rfl⟩ := hb <;>
      simp [cdOf, binInet]

theorem cdOf_mkBin {ka : BinKind} (h : ka = .con ∨ ka = .dup) (x y : HTree) :
    cdOf (mkBin ka x y) = some ((binInet ka).1, (binInet ka).2, x, y) := by
  rcases h with rfl | rfl <;> rfl

theorem reduce_cd {ka kb : BinKind} (hka : ka = .con ∨ ka = .dup) (hkb : kb = .con ∨ kb = .dup)
    (i j n v w : Nat) (a1 a2 b1 b2 : PortRef) :
    reduceActivePair ⟨⟨i, (binInet ka).1, (binInet ka).2, v, a1, a2⟩, ⟨j, (binInet kb).1, (binInet kb).2, w, b1, b2⟩⟩ n =
      if ka = kb then .annihilate (a1, b1) (a2, b2)
      else .commute (commuteSpawnedNodes ⟨i, (binInet ka).1, (binInet ka).2, v, a1, a2⟩ ⟨j, (binInet kb).1, (binInet kb).2, w, b1, b2⟩ n)
        (commuteSplices ⟨i, (binInet ka).1, (binInet ka).2, v, a1, a2⟩ ⟨j, (binInet kb).1, (binInet kb).2, w, b1, b2⟩ n) := by
  rcases hka with rfl | rfl <;> rcases hkb with rfl | rfl <;> simp [reduceActivePair, binInet]

theorem inet?_of_node {A : Arena} {i : Nat} {k : INetNodeKind} {lb v : Nat} (h : A.node i = some (k, lb, v)) :
    A.inet? i = some ⟨i, k, lb, v, A.link ⟨i, 1⟩, A.link ⟨i, 2⟩⟩ := by
  simp [Arena.inet?, h]

/-! ## A fired pair and its surroundings -/

theorem fst_unique {L : List (Nat × PortRef)} (h : (L.map Prod.fst).Nodup) {x : Nat} {p p' : PortRef}
    (hp : (x, p) ∈ L) (hp' : (x, p') ∈ L) : p = p' := by
  induction L with
  | nil => simp at hp
  | cons e L ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hp with h1 | hp1 <;> rcases List.mem_cons.1 hp' with h2 | hp2
    · have := h1.trans h2.symm; simp only [Prod.mk.injEq] at this; exact this.2
    · subst h1; exact absurd (show x ∈ L.map Prod.fst from List.mem_map.2 ⟨(x, p'), hp2, rfl⟩) h.1
    · subst h2; exact absurd (show x ∈ L.map Prod.fst from List.mem_map.2 ⟨(x, p), hp1, rfl⟩) h.1
    · exact ih h.2 hp1 hp2

theorem flatMap_disj {α : Type} {L : List α} {f : α → List Nat} (h : (L.flatMap f).Nodup) {a b : α}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) {x : Nat} (hxa : x ∈ f a) (hxb : x ∈ f b) : False := by
  induction L with
  | nil => simp at ha
  | cons c L ih =>
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, hL, hdis⟩ := h
    rcases List.mem_cons.1 ha with h1 | ha' <;> rcases List.mem_cons.1 hb with h2 | hb'
    · exact hab (h1.trans h2.symm)
    · subst h1; exact hdis x hxa x (List.mem_flatMap.2 ⟨b, hb', hxb⟩) rfl
    · subst h2; exact hdis x hxb x (List.mem_flatMap.2 ⟨a, ha', hxa⟩) rfl
    · exact ih hL ha' hb'

theorem edgeOcc_fst {A : Arena} {t : HTree} {u : Up} {ids : List Nat} {occ : List (Nat × PortRef)}
    (ht : Tree A t u ids occ) (d : PortRef) : (edgeOcc d u).map Prod.fst = topVar t := by
  cases u with
  | var x => obtain ⟨rfl, -, -⟩ := ht.up_var; rfl
  | port q =>
    rcases ht.shape with ⟨x, rfl⟩ | rfl | ⟨k, lb, a, b, hc⟩
    · obtain ⟨h, -, -⟩ := ht.var_inv; cases h
    · rfl
    · cases t <;> simp [cdOf] at hc <;> rfl

theorem sublist_flatMap {α : Type} {L : List α} {f : α → List Nat} {a : α} (h : a ∈ L) :
    (f a).Sublist (L.flatMap f) := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-- One child of the fired pair: the pair's auxiliary port `d` and the tree hanging from it. -/
structure Kid where
  d : PortRef
  t : HTree
  u : Up
  ids : List Nat
  occ : List (Nat × PortRef)

/-- A fired pair `i ~ j` in a laid-out configuration: the context (root and the other redexes), the
pair's children, and what `Repr` gives about them. -/
structure PairData (A : Arena) (ρ : PortRef) (root : HTree) (pre post : List Redex) where
  u : Up
  ir : List Nat
  ipre : List Nat
  ipost : List Nat
  or : List (Nat × PortRef)
  opre : List (Nat × PortRef)
  opost : List (Nat × PortRef)
  i : Nat
  j : Nat
  kids : List Kid
  ht : Tree A root u ir or
  he : Edge A ρ u
  hpre : BagIn A pre ipre opre
  hpost : BagIn A post ipost opost
  hkid : ∀ k ∈ kids, Tree A k.t k.u k.ids k.occ ∧ Edge A k.d k.u ∧ (k.d.nodeId = i ∨ k.d.nodeId = j) ∧ k.d.slot ≠ 0
  hds : (kids.map Kid.d).Nodup
  hij : i ≠ j
  hnd : (ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids).Nodup
  hi : i ∉ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids
  hj : j ∉ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids
  hlt : ∀ k ∈ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids, k < A.next
  hilt : i < A.next
  hjlt : j < A.next
  hall : ∀ k, A.node k ≠ none → k = i ∨ k = j ∨ k ∈ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids
  hρ : ρ.nodeId < A.next
  hρn : ρ.nodeId ∉ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids
  hρi : ρ.nodeId ≠ i
  hρj : ρ.nodeId ≠ j
  hP : Paired A (edgeOcc ρ u ++ or ++ opre ++ opost ++ kids.flatMap Kid.occ ++
    kids.flatMap (fun k => edgeOcc k.d k.u))
  hvars : ((kids.flatMap fun k => edgeOcc k.d k.u).map Prod.fst).Nodup
  hlij : A.link ⟨i, 0⟩ = ⟨j, 0⟩
  hlji : A.link ⟨j, 0⟩ = ⟨i, 0⟩

namespace PairData
variable {A : Arena} {ρ : PortRef} {root : HTree} {pre post : List Redex} (P : PairData A ρ root pre post)

/-- The surviving occurrences. -/
def K : List (Nat × PortRef) := edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ++ P.kids.flatMap Kid.occ
/-- The occurrences at the pair's auxiliary ports. -/
def D : List (Nat × PortRef) := P.kids.flatMap (fun k => edgeOcc k.d k.u)
/-- The context's nodes. -/
def X : List Nat := P.ir ++ P.ipre ++ P.ipost
/-- The pair's auxiliary ports. -/
def Ds : List PortRef := P.kids.map Kid.d

theorem paired : Paired A (P.K ++ P.D) := P.hP

theorem mem_D {x : Nat} {p : PortRef} (h : (x, p) ∈ P.D) : ∃ k ∈ P.kids, k.d = p ∧ k.u = .var x := by
  obtain ⟨k, hk, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hx
  exact ⟨k, hk, rfl, hu⟩

theorem mem_K' {x : Nat} {p : PortRef} (h : (x, p) ∈ P.K) :
    (x, p) ∈ edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ∨ ∃ k ∈ P.kids, (x, p) ∈ k.occ ∧ p.nodeId ∈ k.ids := by
  rcases List.mem_append.1 h with h | h
  · exact .inl h
  · obtain ⟨k, hk, hx⟩ := List.mem_flatMap.1 h
    exact .inr ⟨k, hk, hx, ((P.hkid k hk).1.occ_mem x p hx).1⟩

theorem mem_K {x : Nat} {p : PortRef} (h : (x, p) ∈ P.K) :
    p = ρ ∨ p.nodeId ∈ P.X ∨ ∃ k ∈ P.kids, (x, p) ∈ k.occ ∧ p.nodeId ∈ k.ids := by
  rcases P.mem_K' h with h | h
  · rcases ctx_occ P.ht P.hpre P.hpost x p h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem K_port {x : Nat} {p : PortRef} (h : (x, p) ∈ P.K) :
    p.nodeId < A.next ∧ p.nodeId ≠ P.i ∧ p.nodeId ≠ P.j := by
  rcases P.mem_K h with rfl | h | ⟨k, hk, -, h⟩
  · exact ⟨P.hρ, P.hρi, P.hρj⟩
  · have hm : p.nodeId ∈ P.ir ++ P.ipre ++ P.ipost ++ P.kids.flatMap Kid.ids :=
      List.mem_append_left _ h
    exact ⟨P.hlt _ hm, fun e => P.hi (e ▸ hm), fun e => P.hj (e ▸ hm)⟩
  · have hm : p.nodeId ∈ P.ir ++ P.ipre ++ P.ipost ++ P.kids.flatMap Kid.ids :=
      List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, h⟩)
    exact ⟨P.hlt _ hm, fun e => P.hi (e ▸ hm), fun e => P.hj (e ▸ hm)⟩

theorem Ds_dead {d : PortRef} (h : d ∈ P.Ds) : d.nodeId = P.i ∨ d.nodeId = P.j := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  exact (P.hkid k hk).2.2.1

theorem K_notDs {x : Nat} {p : PortRef} (h : (x, p) ∈ P.K) : p ∉ P.Ds := fun hd => by
  obtain ⟨-, h1, h2⟩ := P.K_port h
  rcases P.Ds_dead hd with e | e <;> simp_all

theorem kid_ids {k : Kid} (hk : k ∈ P.kids) {m : Nat} (hm : m ∈ k.ids) :
    m ∈ P.ir ++ P.ipre ++ P.ipost ++ P.kids.flatMap Kid.ids :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hm⟩)

/-- The port across from each auxiliary port of the pair. -/
theorem bdry {k : Kid} (hk : k ∈ P.kids) :
    A.link (A.link k.d) = k.d ∧ A.link k.d ≠ k.d ∧ (∀ c, k.u = .port c → A.link k.d = c) ∧
      (∀ x, k.u = .var x → (x, A.link k.d) ∈ P.K ++ P.D) := by
  obtain ⟨ht, he, -, hs⟩ := P.hkid k hk
  exact boundary P.paired ht he hs
    (fun x hx => List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, by rw [hx]; simp [edgeOcc]⟩))

/-- **No loop**: the port across from an auxiliary port of the pair is not on the pair, older than
the fresh ids, and either the child's principal port or a surviving occurrence. -/
theorem across {k : Kid} (hk : k ∈ P.kids) :
    (A.link k.d).nodeId < A.next ∧ (A.link k.d).nodeId ≠ P.i ∧ (A.link k.d).nodeId ≠ P.j ∧
      ((∃ c, k.u = .port c ∧ A.link k.d = c ∧ c.nodeId ∈ k.ids) ∨
        (∃ x, k.u = .var x ∧ (x, A.link k.d) ∈ P.K)) := by
  obtain ⟨hinv, hne, hport, hvar⟩ := P.bdry hk
  obtain ⟨ht, -, -, -⟩ := P.hkid k hk
  cases hu : k.u with
  | port c =>
    have hc := hport c hu
    rw [hu] at ht
    have hci := ht.up_port.2
    have hm := P.kid_ids hk hci
    rw [hc]
    exact ⟨P.hlt _ hm, fun e => P.hi (e ▸ hm), fun e => P.hj (e ▸ hm), .inl ⟨c, rfl, rfl, hci⟩⟩
  | var x =>
    have hx := hvar x hu
    rcases List.mem_append.1 hx with hK | hD
    · obtain ⟨h1, h2, h3⟩ := P.K_port hK
      exact ⟨h1, h2, h3, .inr ⟨x, rfl, hK⟩⟩
    · exfalso
      have hkD : (x, k.d) ∈ P.D := List.mem_flatMap.2 ⟨k, hk, by rw [hu]; simp [edgeOcc]⟩
      exact hne (fst_unique P.hvars hD hkD)

theorem across_notDs {k : Kid} (hk : k ∈ P.kids) : A.link k.d ∉ P.Ds := fun hd => by
  obtain ⟨-, h1, h2, -⟩ := P.across hk
  rcases P.Ds_dead hd with e | e <;> simp_all

theorem across_inj {k k' : Kid} (hk : k ∈ P.kids) (hk' : k' ∈ P.kids) (h : A.link k.d = A.link k'.d) :
    k.d = k'.d := by
  have := congrArg A.link h
  rwa [(P.bdry hk).1, (P.bdry hk').1] at this

/-- **Frame**: an arena that keeps the surviving nodes, and the links of old ports not across from
the pair, keeps the context and the children. -/
theorem frame {A' : Arena} (hn : ∀ m ∈ P.ir ++ P.ipre ++ P.ipost ++ P.kids.flatMap Kid.ids, A'.node m = A.node m)
    (hl : ∀ p : PortRef, p.nodeId < A.next → (∀ k ∈ P.kids, p ≠ A.link k.d) → A'.link p = A.link p) :
    (Tree A' root P.u P.ir P.or ∧ Edge A' ρ P.u ∧ BagIn A' pre P.ipre P.opre ∧ BagIn A' post P.ipost P.opost) ∧
      ∀ k ∈ P.kids, Tree A' k.t k.u k.ids k.occ := by
  have hnd := P.hnd
  rw [List.nodup_append] at hnd
  obtain ⟨hX, hF, hXF⟩ := hnd
  refine ⟨ctx_frame P.ht P.he P.hpre P.hpost hX (fun h => P.hρn (List.mem_append_left _ h))
    (fun m hm => hn m (List.mem_append_left _ hm)) ?_, ?_⟩
  · intro p hp hpo
    have hpo' : p.nodeId < A.next := by
      rcases hp with hp | rfl
      · exact P.hlt _ (List.mem_append_left _ hp)
      · exact P.hρ
    refine hl p hpo' fun k hk he => ?_
    obtain ⟨-, -, -, h⟩ := P.across hk
    rcases h with ⟨c, -, hc, hci⟩ | ⟨x, -, hK⟩
    · rw [hc] at he; subst he
      rcases hp with hp | hp
      · exact hXF _ hp _ (List.mem_flatMap.2 ⟨k, hk, hci⟩) rfl
      · subst hp; exact P.hρn (P.kid_ids hk hci)
    · rw [← he] at hK
      rcases P.mem_K' hK with h | ⟨k', hk', -, hid⟩
      · exact hpo x h
      · rcases hp with hp | rfl
        · exact hXF _ hp _ (List.mem_flatMap.2 ⟨k', hk', hid⟩) rfl
        · exact P.hρn (P.kid_ids hk' hid)
  · intro k hk
    obtain ⟨ht, -, -, -⟩ := P.hkid k hk
    have hsub : k.ids.Sublist (P.kids.flatMap Kid.ids) := sublist_flatMap hk
    refine ht.frame (hF.sublist hsub) (fun m hm => hn m (P.kid_ids hk hm)) fun p hp hpo hpt => ?_
    refine hl p (P.hlt _ (P.kid_ids hk hp)) fun k' hk' he => ?_
    obtain ⟨-, -, -, h⟩ := P.across hk'
    rcases h with ⟨c, hu, hc, hci⟩ | ⟨x, -, hK⟩
    · rw [hc] at he; subst he
      by_cases hkk : k = k'
      · subst hkk
        rw [hu] at ht
        have h0 := ht.up_port.1
        obtain ⟨n, s⟩ := p
        simp only at h0; subst h0
        exact hpt n hu rfl
      · exact flatMap_disj hF hk hk' hkk hp hci
    · rw [← he] at hK
      rcases P.mem_K' hK with h | ⟨k'', hk'', hx, hid⟩
      · rcases ctx_occ P.ht P.hpre P.hpost x p h with h | h
        · subst h; exact P.hρn (P.kid_ids hk hp)
        · exact hXF _ h _ (List.mem_flatMap.2 ⟨k, hk, hp⟩) rfl
      · by_cases hkk : k = k''
        · subst hkk; exact hpo x hx
        · exact flatMap_disj hF hk hk'' hkk hp hid

theorem eq_of_map_eq {α β : Type} {L : List α} {f : α → β} (h : (L.map f).Nodup) {a b : α} (ha : a ∈ L)
    (hb : b ∈ L) (hab : f a = f b) : a = b := by
  induction L with
  | nil => simp at ha
  | cons c L ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with h1 | ha' <;> rcases List.mem_cons.1 hb with h2 | hb'
    · exact h1.trans h2.symm
    · subst h1; exact absurd (hab ▸ List.mem_map.2 ⟨b, hb', rfl⟩) h.1
    · subst h2; exact absurd (hab.symm ▸ List.mem_map.2 ⟨a, ha', rfl⟩) h.1
    · exact ih h.2 ha' hb'

/-- An occurrence across from an auxiliary port of the pair is of the child variable there. -/
theorem across_var {k : Kid} (hk : k ∈ P.kids) {x : Nat} (h : (x, A.link k.d) ∈ P.K) : k.u = .var x := by
  obtain ⟨h1, -, -⟩ := P.paired x _ (List.mem_append_left _ h)
  rw [(P.bdry hk).1] at h1
  rcases List.mem_append.1 h1 with hK | hD
  · exact absurd (List.mem_map.2 ⟨k, hk, rfl⟩) (P.K_notDs hK)
  · obtain ⟨k', hk', hd, hu⟩ := P.mem_D hD
    rw [eq_of_map_eq P.hds hk hk' hd.symm]; exact hu

/-- The new arena's nodes are the fresh ones and the survivors. -/
theorem ids_new {A' : Arena} {F im : List Nat} (hperm : im.Perm (F ++ P.kids.flatMap Kid.ids)) (hF : F.Nodup)
    (hFn : ∀ k ∈ F, A.next ≤ k ∧ k < A'.next) (hn' : A.next ≤ A'.next)
    (hnode : ∀ k, A'.node k ≠ none → k ∈ F ∨ (k ≠ P.i ∧ k ≠ P.j ∧ A.node k ≠ none)) :
    (P.ir ++ P.ipre ++ P.ipost ++ im).Nodup ∧ (∀ k ∈ P.ir ++ P.ipre ++ P.ipost ++ im, k < A'.next) ∧
      (∀ k, A'.node k ≠ none → k ∈ P.ir ++ P.ipre ++ P.ipost ++ im) ∧
      ρ.nodeId < A'.next ∧ ρ.nodeId ∉ P.ir ++ P.ipre ++ P.ipost ++ im := by
  have hp2 : (P.ir ++ P.ipre ++ P.ipost ++ im).Perm (F ++ (P.ir ++ P.ipre ++ P.ipost ++ P.kids.flatMap Kid.ids)) :=
    List.perm_iff_count.2 fun k => by
      rw [List.count_append, hperm.count_eq]; simp only [List.count_append]; omega
  refine ⟨hp2.nodup_iff.2 (nodup_fresh hF (fun k hk => (hFn k hk).1) P.hnd P.hlt), fun k hk => ?_, fun k hk => ?_,
    by have := P.hρ; omega, fun h => ?_⟩
  · rcases List.mem_append.1 (hp2.mem_iff.1 hk) with h | h
    · exact (hFn k h).2
    · have := P.hlt k h; omega
  · rcases hnode k hk with h | ⟨hi, hj, h⟩
    · exact hp2.mem_iff.2 (List.mem_append_left _ h)
    · rcases P.hall k h with h' | h' | h'
      · exact absurd h' hi
      · exact absurd h' hj
      · exact hp2.mem_iff.2 (List.mem_append_right _ h')
  · rcases List.mem_append.1 (hp2.mem_iff.1 h) with h | h
    · have := (hFn _ h).1; have := P.hρ; omega
    · exact P.hρn h

/-- The occurrences stay paired across the rewrite (`paired_transfer` for a fired pair). -/
theorem paired_new {A' : Arena} {N : List (Nat × PortRef)} {f : Nat → Nat}
    (hfr : ∀ p : PortRef, p.nodeId < A.next → (∀ k ∈ P.kids, p ≠ A.link k.d) → A'.link p = A.link p)
    (hB : ∀ x, ∀ k ∈ P.kids, k.u = .var x → (x, A.link k.d) ∈ P.K →
      (f x, A'.link (A.link k.d)) ∈ (P.K ++ N).map (renOcc f) ∧ A'.link (A.link k.d) ≠ A.link k.d ∧
        A'.link (A'.link (A.link k.d)) = A.link k.d)
    (hN : ∀ x p, (x, p) ∈ N →
      (f x, A'.link p) ∈ (P.K ++ N).map (renOcc f) ∧ A'.link p ≠ p ∧ A'.link (A'.link p) = p) :
    Paired A' ((P.K ++ N).map (renOcc f)) := by
  refine paired_transfer (D := P.D) (Ds := P.Ds) (n := A.next) P.paired
    (fun x p h => by obtain ⟨k, hk, rfl, -⟩ := P.mem_D h; exact List.mem_map.2 ⟨k, hk, rfl⟩)
    (fun x p h => P.K_notDs h) (fun x p h => (P.K_port h).1)
    (fun d hd => by obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hd; exact (P.bdry hk).1)
    (fun p hp ho => hfr p ho fun k hk => hp k.d (List.mem_map.2 ⟨k, hk, rfl⟩))
    (fun x d hd h => ?_) hN
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hd
  exact hB x k hk (P.across_var hk h) h

end PairData

/-- Package a fired pair: its ids `R` are `i`, `j` and the children's, its occurrences `O` the
children's and those at its auxiliary ports. -/
def PairData.build {A : Arena} {ρ : PortRef} {root : HTree} {pre post : List Redex} {u : Up}
    {ir ipre ipost : List Nat} {or opre opost : List (Nat × PortRef)} (i j : Nat) (kids : List Kid)
    (R : List Nat) (O : List (Nat × PortRef))
    (ht : Tree A root u ir or) (he : Edge A ρ u) (hpre : BagIn A pre ipre opre) (hpost : BagIn A post ipost opost)
    (hkid : ∀ k ∈ kids, Tree A k.t k.u k.ids k.occ ∧ Edge A k.d k.u ∧ (k.d.nodeId = i ∨ k.d.nodeId = j) ∧ k.d.slot ≠ 0)
    (hds : (kids.map Kid.d).Nodup)
    (hR : R.Perm ([i, j] ++ kids.flatMap Kid.ids))
    (hO : O.Perm (kids.flatMap Kid.occ ++ kids.flatMap fun k => edgeOcc k.d k.u))
    (hnd : (ir ++ ipre ++ ipost ++ R).Nodup) (hlt : ∀ k ∈ ir ++ ipre ++ ipost ++ R, k < A.next)
    (hall : ∀ k, A.node k ≠ none → k ∈ ir ++ ipre ++ ipost ++ R) (hρ : ρ.nodeId < A.next)
    (hρn : ρ.nodeId ∉ ir ++ ipre ++ ipost ++ R) (hP : Paired A (edgeOcc ρ u ++ or ++ opre ++ opost ++ O))
    (hvars : ((kids.flatMap fun k => edgeOcc k.d k.u).map Prod.fst).Nodup)
    (hlij : A.link ⟨i, 0⟩ = ⟨j, 0⟩) (hlji : A.link ⟨j, 0⟩ = ⟨i, 0⟩) : PairData A ρ root pre post :=
  have hp : (ir ++ ipre ++ ipost ++ R).Perm ([i, j] ++ (ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids)) :=
    List.perm_iff_count.2 fun k => by
      rw [List.count_append, hR.count_eq]; simp only [List.count_append]; omega
  have hnd' := hp.nodup_iff.1 hnd
  have hij : i ≠ j := by
    have := (List.nodup_append.1 hnd').1; simp at this; exact this
  have hi : i ∉ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids := fun h =>
    (List.nodup_append.1 hnd').2.2 i (by simp) i h rfl
  have hj : j ∉ ir ++ ipre ++ ipost ++ kids.flatMap Kid.ids := fun h =>
    (List.nodup_append.1 hnd').2.2 j (by simp) j h rfl
  { u := u, ir := ir, ipre := ipre, ipost := ipost, or := or, opre := opre, opost := opost, i := i, j := j,
    kids := kids, ht := ht, he := he, hpre := hpre, hpost := hpost, hkid := hkid, hds := hds, hij := hij,
    hnd := (List.nodup_append.1 hnd').2.1, hi := hi, hj := hj,
    hlt := fun k hk => hlt k (hp.mem_iff.2 (List.mem_append_right _ hk)),
    hilt := hlt i (hp.mem_iff.2 (by simp)), hjlt := hlt j (hp.mem_iff.2 (by simp)),
    hall := fun k hk => by
      have := hp.mem_iff.1 (hall k hk)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (by simpa only [List.mem_append] using h)),
    hρ := hρ, hρn := fun h => hρn (hp.mem_iff.2 (List.mem_append_right _ h)),
    hρi := fun h => hρn (hp.mem_iff.2 (by simp [h])), hρj := fun h => hρn (hp.mem_iff.2 (by simp [h])),
    hP := paired_congr (fun e => (List.perm_iff_count.2 fun e => by
      simp only [List.count_append]; rw [hO.count_eq]; simp only [List.count_append]; omega).mem_iff) hP,
    hvars := hvars, hlij := hlij, hlji := hlji }

theorem map_renOcc_id (L : List (Nat × PortRef)) : L.map (renOcc fun x => x) = L := by
  induction L with
  | nil => rfl
  | cons e L ih => simp [renOcc, ih]

theorem cfg_rename_id (root : HTree) (bag : List Redex) :
    (⟨root.rename (fun x => x), bag.map (Redex.rename fun x => x)⟩ : Cfg) = ⟨root, bag⟩ := by
  have : ∀ r : Redex, r.rename (fun x => x) = r := fun r => by simp [Redex.rename, rename_id']
  rw [rename_id', List.map_congr_left (fun r _ => this r), List.map_id']

/-- A fresh node's principal port facing a child: the wire both ways, or the child variable's
occurrence. -/
theorem facing_new {A A' : Arena} {P0 d : PortRef} {u : Up} (h1 : A'.link P0 = A.link d)
    (h2 : A'.link (A.link d) = P0) (h3 : ∀ c, u = .port c → A.link d = c) :
    Facing A' (.port P0) u (edgeOcc P0 u) := by
  cases u with
  | port c => have := h3 c rfl; subst this; exact ⟨h1, h2, rfl⟩
  | var x => rfl

theorem kidVars_cd {t a b : HTree} {k : INetNodeKind} {lb : Nat} (h : cdOf t = some (k, lb, a, b)) :
    kidVars t = topVar a ++ topVar b := by
  simp [kidVars, h]

/-- A fresh binary node with two variable children. -/
theorem tree_fresh {A : Arena} {t : HTree} {k : INetNodeKind} {lb m x y : Nat}
    (hc : cdOf t = some (k, lb, .var x, .var y)) (hn : A.node m = some (k, lb, 0)) :
    Tree A t (.port ⟨m, 0⟩) [m] [(x, ⟨m, 1⟩), (y, ⟨m, 2⟩)] :=
  Tree.bin m hc hn (.var x) (.var y) trivial trivial

/-! ## COMM -/

/-- **COMM is one arena step**: a `CON` meeting a `DUP` in a represented configuration fires as an
active pair, rewritten by `reduceActivePair`'s commutation, to an arena representing COMM's result. -/
theorem sim_comm {A : Arena} {ρ : PortRef} {root a b a1 a2 b1 b2 : HTree} {pre post : List Redex}
    {ka kb : BinKind} {v0 v1 v2 v3 : Nat}
    (hR : Repr A ρ ⟨root, pre ++ (a, b) :: post⟩) (ha : a.bin? = some (ka, a1, a2))
    (hb : b.bin? = some (kb, b1, b2)) (hk : ka ≠ kb) (hkid : (kidVars a ++ kidVars b).Nodup) :
    ∃ A', Arena.Step A A' ∧ Repr A' ρ ⟨root, pre ++ [(mkBin kb (.var v0) (.var v1), a1),
      (mkBin kb (.var v2) (.var v3), a2), (mkBin ka (.var v0) (.var v2), b1),
      (mkBin ka (.var v1) (.var v3), b2)] ++ post⟩ := by
  obtain ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, hta, htb, hf,
    hnd, hlt, hall, hρ, hρn, hP⟩ := repr_split hR
  obtain ⟨hka, hca⟩ := bin_cd hta ha
  obtain ⟨hkb, hcb⟩ := bin_cd htb hb
  obtain ⟨i, u1, u2, ia1, ia2, oa1, oa2, rfl, rfl, rfl, hni, ht1, ht2, e1, e2⟩ := hta.bin_inv hca
  obtain ⟨j, w1, w2, ib1, ib2, ob1, ob2, rfl, rfl, rfl, hnj, ht3, ht4, e3, e4⟩ := htb.bin_inv hcb
  obtain ⟨hlij, hlji, rfl⟩ := hf
  have hij : i ≠ j := by
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 i (by simp) j (by simp); exact this
  let kids : List Kid := [⟨⟨i, 1⟩, a1, u1, ia1, oa1⟩, ⟨⟨i, 2⟩, a2, u2, ia2, oa2⟩, ⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩,
    ⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩]
  have hkids : ∀ k ∈ kids, Tree A k.t k.u k.ids k.occ ∧ Edge A k.d k.u ∧ (k.d.nodeId = i ∨ k.d.nodeId = j) ∧
      k.d.slot ≠ 0 := by
    intro k hk
    simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨ht1, e1, .inl rfl, by simp⟩
    · exact ⟨ht2, e2, .inl rfl, by simp⟩
    · exact ⟨ht3, e3, .inr rfl, by simp⟩
    · exact ⟨ht4, e4, .inr rfl, by simp⟩
  have hds : (kids.map Kid.d).Nodup := by
    simp only [kids, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      PortRef.mk.injEq, not_or]
    refine ⟨⟨by omega, fun h => hij h.1, fun h => hij h.1⟩, ⟨fun h => hij h.1, fun h => hij h.1⟩, by omega, by simp,
      List.nodup_nil⟩
  have hvars : ((kids.flatMap fun k => edgeOcc k.d k.u).map Prod.fst).Nodup := by
    rw [kidVars_cd hca, kidVars_cd hcb] at hkid
    simpa [kids, List.flatMap_cons, List.map_append, edgeOcc_fst ht1, edgeOcc_fst ht2, edgeOcc_fst ht3,
      edgeOcc_fst ht4] using hkid
  have hRp : (i :: (ia1 ++ ia2) ++ j :: (ib1 ++ ib2)).Perm ([i, j] ++ kids.flatMap Kid.ids) :=
    List.perm_iff_count.2 fun k => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_cons, List.count_nil]
      omega
  have hOp : (edgeOcc ⟨i, 1⟩ u1 ++ edgeOcc ⟨i, 2⟩ u2 ++ oa1 ++ oa2 ++
      (edgeOcc ⟨j, 1⟩ w1 ++ edgeOcc ⟨j, 2⟩ w2 ++ ob1 ++ ob2) ++ []).Perm
      (kids.flatMap Kid.occ ++ kids.flatMap fun (k : Kid) => edgeOcc k.d k.u) :=
    List.perm_iff_count.2 fun e => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_nil]
      omega
  let P : PairData A ρ root pre post := PairData.build i j kids _ _ ht he hpre hpost hkids hds hRp hOp
    hnd hlt hall hρ hρn hP hvars hlij hlji
  have k1 : (⟨⟨i, 1⟩, a1, u1, ia1, oa1⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k2 : (⟨⟨i, 2⟩, a2, u2, ia2, oa2⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k3 : (⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k4 : (⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  -- the pair and its rewrite
  let l : INetNode := ⟨i, (binInet ka).1, (binInet ka).2, 0, A.link ⟨i, 1⟩, A.link ⟨i, 2⟩⟩
  let r : INetNode := ⟨j, (binInet kb).1, (binInet kb).2, 0, A.link ⟨j, 1⟩, A.link ⟨j, 2⟩⟩
  have hred : reduceActivePair ⟨l, r⟩ A.next = .commute (commuteSpawnedNodes l r A.next) (commuteSplices l r A.next) := by
    rw [reduce_cd hka hkb, ite_neg' hk]
  refine ⟨commArena A l r, .fire hij (inet?_of_node hni) (inet?_of_node hnj) hlij hlji
    (by rw [hred]; exact apply_commute A l r), ?_⟩
  -- the ports across the pair's auxiliary wires
  obtain ⟨c1lt, c1i, c1j, c1⟩ := P.across k1
  obtain ⟨c2lt, c2i, c2j, c2⟩ := P.across k2
  obtain ⟨c3lt, c3i, c3j, c3⟩ := P.across k3
  obtain ⟨c4lt, c4i, c4j, c4⟩ := P.across k4
  have b1 := P.bdry k1
  have b2 := P.bdry k2
  have b3 := P.bdry k3
  have b4 := P.bdry k4
  dsimp only at c1lt c1i c1j c1 c2lt c2i c2j c2 c3lt c3i c3j c3 c4lt c4i c4j c4 b1 b2 b3 b4
  have hd : [l.aux1, l.aux2, r.aux1, r.aux2].Nodup := by
    have inj := fun {k k'} (hk : k ∈ P.kids) (hk' : k' ∈ P.kids) h => P.across_inj hk hk' h
    simp only [l, r, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, by simp, List.nodup_nil⟩
    · have := inj k1 k2 h; simp at this
    · have := inj k1 k3 h; simp at this; omega
    · have := inj k1 k4 h; simp at this
    · have := inj k2 k3 h; simp at this
    · have := inj k2 k4 h; simp at this; omega
    · have := inj k3 k4 h; simp at this
  have ho : ∀ p ∈ [l.aux1, l.aux2, r.aux1, r.aux2], p.nodeId < A.next := by
    simp only [l, r, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨c1lt, c2lt, c3lt, c4lt⟩
  obtain ⟨hfr, L0, L0', L1, L1', L2, L2', L3, L3', I1, I2, I3, I4, I5, I6, I7, I8⟩ := commArena_link A l r hd ho
  simp only [l, r] at hfr L0 L0' L1 L1' L2 L2' L3 L3'
  have hnode := commArena_node A l r
  simp only [l, r] at hnode
  generalize hA' : commArena A l r = A' at hfr L0 L0' L1 L1' L2 L2' L3 L3' I1 I2 I3 I4 I5 I6 I7 I8 hnode
  have hnext : A'.next = A.next + 4 := by rw [← hA']; rfl
  obtain ⟨n, hn⟩ : ∃ n, A.next = n := ⟨_, rfl⟩
  rw [hn] at hfr L0 L0' L1 L1' L2 L2' L3 L3' I1 I2 I3 I4 I5 I6 I7 I8 hnode hnext c1lt c2lt c3lt c4lt
  -- the survivors, unchanged
  have hacr : ∀ p : PortRef, p.nodeId < n → (∀ k ∈ P.kids, p ≠ A.link k.d) → A'.link p = A.link p := by
    intro p hp hne
    refine hfr p hp ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hne _ k1, hne _ k2, hne _ k3, hne _ k4⟩
  obtain ⟨⟨ht', he', hpre', hpost'⟩, hkid'⟩ := P.frame (A' := A')
    (fun m hm => by
      have := P.hlt m hm
      have hmi : m ≠ i := fun h => P.hi (by subst h; exact hm)
      have hmj : m ≠ j := fun h => P.hj (by subst h; exact hm)
      rw [hnode, ite_neg' (show ¬m = n + 3 by omega), ite_neg' (show ¬m = n + 2 by omega),
        ite_neg' (show ¬m = n + 1 by omega), ite_neg' (show ¬m = n by omega), ite_neg' hmj, ite_neg' hmi])
    (fun p hp hne => hacr p (hn ▸ hp) hne)
  have ht1' := hkid' _ k1
  have ht2' := hkid' _ k2
  have ht3' := hkid' _ k3
  have ht4' := hkid' _ k4
  dsimp only at ht1' ht2' ht3' ht4'
  -- the four copies
  have nB1 : A'.node n = some ((binInet kb).1, (binInet kb).2, 0) := by simp [hnode]
  have nB2 : A'.node (n + 1) = some ((binInet kb).1, (binInet kb).2, 0) := by simp [hnode]
  have nA1 : A'.node (n + 2) = some ((binInet ka).1, (binInet ka).2, 0) := by simp [hnode]
  have nA2 : A'.node (n + 3) = some ((binInet ka).1, (binInet ka).2, 0) := by simp [hnode]
  have tB1 := tree_fresh (cdOf_mkBin hkb (.var v0) (.var v1)) nB1
  have tB2 := tree_fresh (cdOf_mkBin hkb (.var v2) (.var v3)) nB2
  have tA1 := tree_fresh (cdOf_mkBin hka (.var v0) (.var v2)) nA1
  have tA2 := tree_fresh (cdOf_mkBin hka (.var v1) (.var v3)) nA2
  have f1 := facing_new L0 L0' b1.2.2.1
  have f2 := facing_new L1 L1' b2.2.2.1
  have f3 := facing_new L2 L2' b3.2.2.1
  have f4 := facing_new L3 L3' b4.2.2.1
  have hM := BagIn.cons tB1 ht1' f1 (BagIn.cons tB2 ht2' f2 (BagIn.cons tA1 ht3' f3 (BagIn.cons tA2 ht4' f4 .nil)))
  -- nodes
  obtain ⟨hnd', hlt', hall', hρ', hρn'⟩ := P.ids_new (A' := A') (F := [n, n + 1, n + 2, n + 3])
    (im := [n] ++ ia1 ++ ([n + 1] ++ ia2 ++ ([n + 2] ++ ib1 ++ ([n + 3] ++ ib2 ++ []))))
    (List.perm_iff_count.2 fun k => by
      simp only [P, PairData.build, kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_cons,
        List.count_nil, List.append_nil]
      omega)
    (by simp) (fun k hk => by simp at hk; omega) (by omega)
    (fun k hk => by
      rw [hnode] at hk
      by_cases h3 : k = n + 3
      · exact .inl (by simp [h3])
      by_cases h2 : k = n + 2
      · exact .inl (by simp [h2])
      by_cases h1 : k = n + 1
      · exact .inl (by simp [h1])
      by_cases h0 : k = n
      · exact .inl (by simp [h0])
      rw [ite_neg' h3, ite_neg' h2, ite_neg' h1, ite_neg' h0] at hk
      by_cases hj : k = j
      · rw [ite_pos' hj] at hk; exact absurd rfl hk
      by_cases hi : k = i
      · rw [ite_neg' hj, ite_pos' hi] at hk; exact absurd rfl hk
      rw [ite_neg' hj, ite_neg' hi] at hk
      exact .inr ⟨hi, hj, hk⟩)
  -- occurrences
  let N : List (Nat × PortRef) := [(v0, ⟨n, 1⟩), (v1, ⟨n, 2⟩), (v2, ⟨n + 1, 1⟩), (v3, ⟨n + 1, 2⟩),
    (v0, ⟨n + 2, 1⟩), (v2, ⟨n + 2, 2⟩), (v1, ⟨n + 3, 1⟩), (v3, ⟨n + 3, 2⟩)] ++
    edgeOcc ⟨n, 0⟩ u1 ++ edgeOcc ⟨n + 1, 0⟩ u2 ++ edgeOcc ⟨n + 2, 0⟩ w1 ++ edgeOcc ⟨n + 3, 0⟩ w2
  have edge_case : ∀ (d P0 : PortRef) (uk : Up) (x : Nat), uk = .var x →
      (A.link d).nodeId < n → P0.nodeId = n ∨ P0.nodeId = n + 1 ∨ P0.nodeId = n + 2 ∨ P0.nodeId = n + 3 →
      A'.link P0 = A.link d → A'.link (A.link d) = P0 →
      ∀ is : List Nat, ((∃ c, uk = .port c ∧ A.link d = c ∧ c.nodeId ∈ is) ∨
        ∃ x', uk = .var x' ∧ (x', A.link d) ∈ P.K) →
      (x, A'.link P0) ∈ P.K ++ N ∧ A'.link P0 ≠ P0 ∧ A'.link (A'.link P0) = P0 := by
    intro d P0 uk x hu hlt0 hP0 e1 e2 is hc
    have hK : (x, A.link d) ∈ P.K := by
      rcases hc with ⟨c, hc, -, -⟩ | ⟨x', hx', hK⟩
      · rw [hu] at hc; cases hc
      · rw [hu] at hx'; cases hx'; exact hK
    refine ⟨by rw [e1]; exact List.mem_append_left _ hK, ?_, by rw [e1, e2]⟩
    rw [e1]; intro h; rw [h] at hlt0; omega
  have hP' := P.paired_new (A' := A') (N := N) (f := fun x => x) (fun p hp hne => hacr p (hn ▸ hp) hne)
    (fun x k hk hu hK => by
      rw [map_renOcc_id]
      simp only [P, PairData.build, kids, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> dsimp only at hu hK ⊢
      · rw [L0']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L0⟩
        rw [← h] at c1lt; dsimp only at c1lt; omega
      · rw [L1']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L1⟩
        rw [← h] at c2lt; dsimp only at c2lt; omega
      · rw [L2']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L2⟩
        rw [← h] at c3lt; dsimp only at c3lt; omega
      · rw [L3']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L3⟩
        rw [← h] at c4lt; dsimp only at c4lt; omega)
    (fun x p hp => by
      rw [map_renOcc_id]
      simp only [N, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩) | hp) | hp) | hp) | hp
      · rw [I1, I5]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I2, I7]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I3, I6]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I4, I8]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I5, I1]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I6, I3]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I7, I2]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · rw [I8, I4]; exact ⟨List.mem_append_right _ (by simp [N]), by simp, rfl⟩
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c1lt (.inl rfl) L0 L0' _ c1
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c2lt (.inr (.inl rfl)) L1 L1' _ c2
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c3lt (.inr (.inr (.inl rfl))) L2 L2' _ c3
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c4lt (.inr (.inr (.inr rfl))) L3 L3' _ c4)
  rw [map_renOcc_id] at hP'
  have hP'' : Paired A' ((edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ++
      ([((v0, ⟨n, 1⟩) : Nat × PortRef), (v1, ⟨n, 2⟩)] ++ oa1 ++ edgeOcc ⟨n, 0⟩ u1 ++
        ([((v2, ⟨n + 1, 1⟩) : Nat × PortRef), (v3, ⟨n + 1, 2⟩)] ++ oa2 ++ edgeOcc ⟨n + 1, 0⟩ u2 ++
          ([((v0, ⟨n + 2, 1⟩) : Nat × PortRef), (v2, ⟨n + 2, 2⟩)] ++ ob1 ++ edgeOcc ⟨n + 2, 0⟩ w1 ++
            ([((v1, ⟨n + 3, 1⟩) : Nat × PortRef), (v3, ⟨n + 3, 2⟩)] ++ ob2 ++ edgeOcc ⟨n + 3, 0⟩ w2 ++ []))))).map
      (renOcc fun x => x)) := by
    rw [map_renOcc_id]
    refine paired_congr (fun e => (List.perm_iff_count.2 fun e => ?_).mem_iff) hP'
    simp only [PairData.K, P, PairData.build, kids, N, List.flatMap_cons, List.flatMap_nil, List.count_append,
      List.count_cons, List.count_nil, List.append_nil]
    omega
  have := repr_join ht' he' hpre' hpost' hM hnd' hlt' hall' hρ' hρn' hP''
  rwa [cfg_rename_id] at this

/-! ## ERAS and VOID -/

/-- **ERAS is one arena step**: an eraser meeting `CON` or `DUP` fires, each child now facing a fresh
eraser. -/
theorem sim_eras {A : Arena} {ρ : PortRef} {root b b1 b2 : HTree} {pre post : List Redex}
    {kb : INetNodeKind} {lbb : Nat}
    (hR : Repr A ρ ⟨root, pre ++ (.era, b) :: post⟩) (hcb : cdOf b = some (kb, lbb, b1, b2))
    (hkid : (kidVars b).Nodup) :
    ∃ A', Arena.Step A A' ∧ Repr A' ρ ⟨root, pre ++ [(.era, b1), (.era, b2)] ++ post⟩ := by
  obtain ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, hta, htb, hf,
    hnd, hlt, hall, hρ, hρn, hP⟩ := repr_split hR
  obtain ⟨i, rfl, rfl, rfl, hni⟩ := hta.era_inv
  obtain ⟨j, w1, w2, ib1, ib2, ob1, ob2, rfl, rfl, rfl, hnj, ht3, ht4, e3, e4⟩ := htb.bin_inv hcb
  obtain ⟨hlij, hlji, rfl⟩ := hf
  have hij : i ≠ j := by
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 i (by simp) j (by simp); exact this
  let kids : List Kid := [⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩, ⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩]
  have hkids : ∀ k ∈ kids, Tree A k.t k.u k.ids k.occ ∧ Edge A k.d k.u ∧ (k.d.nodeId = i ∨ k.d.nodeId = j) ∧
      k.d.slot ≠ 0 := by
    intro k hk
    simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨ht3, e3, .inr rfl, by simp⟩
    · exact ⟨ht4, e4, .inr rfl, by simp⟩
  have hds : (kids.map Kid.d).Nodup := by simp [kids]
  have hvars : ((kids.flatMap fun k => edgeOcc k.d k.u).map Prod.fst).Nodup := by
    rw [kidVars_cd hcb] at hkid
    simpa [kids, List.flatMap_cons, List.map_append, edgeOcc_fst ht3, edgeOcc_fst ht4] using hkid
  have hRp : ([i] ++ j :: (ib1 ++ ib2)).Perm ([i, j] ++ kids.flatMap Kid.ids) :=
    List.perm_iff_count.2 fun k => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_cons, List.count_nil]
      omega
  have hOp : ([] ++ (edgeOcc ⟨j, 1⟩ w1 ++ edgeOcc ⟨j, 2⟩ w2 ++ ob1 ++ ob2) ++ []).Perm
      (kids.flatMap Kid.occ ++ kids.flatMap fun (k : Kid) => edgeOcc k.d k.u) :=
    List.perm_iff_count.2 fun e => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_nil]
      omega
  let P : PairData A ρ root pre post := PairData.build i j kids _ _ ht he hpre hpost hkids hds hRp hOp
    hnd hlt hall hρ hρn hP hvars hlij hlji
  have k3 : (⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k4 : (⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  obtain ⟨c3lt, c3i, c3j, c3⟩ := P.across k3
  obtain ⟨c4lt, c4i, c4j, c4⟩ := P.across k4
  have b3 := P.bdry k3
  have b4 := P.bdry k4
  dsimp only at c3lt c3i c3j c3 c4lt c4i c4j c4 b3 b4
  let l : INetNode := ⟨i, .era, 0, 0, A.link ⟨i, 1⟩, A.link ⟨i, 2⟩⟩
  let r : INetNode := ⟨j, kb, lbb, 0, A.link ⟨j, 1⟩, A.link ⟨j, 2⟩⟩
  have hkb : kb = .con ∨ kb = .dup := by
    cases b <;> simp [cdOf] at hcb <;> obtain ⟨rfl, -⟩ := hcb <;> simp
  have hred : reduceActivePair ⟨l, r⟩ A.next = .erase [A.link ⟨j, 1⟩, A.link ⟨j, 2⟩] := by
    rcases hkb with rfl | rfl <;> rfl
  have hne : A.link ⟨j, 1⟩ ≠ A.link ⟨j, 2⟩ := fun h => by have := P.across_inj k3 k4 h; simp at this
  obtain ⟨hnext, hnode, hfr, L0, L0', L1, L1'⟩ := eraArena_facts ((A.drop i).drop j) _ _ hne c3lt c4lt
  refine ⟨((A.drop i).drop j).erasers [A.link ⟨j, 1⟩, A.link ⟨j, 2⟩],
    .fire hij (inet?_of_node hni) (inet?_of_node hnj) hlij hlji (by rw [hred]; rfl), ?_⟩
  generalize hA' : ((A.drop i).drop j).erasers [A.link ⟨j, 1⟩, A.link ⟨j, 2⟩] = A' at hnext hnode hfr L0 L0' L1 L1'
  obtain ⟨n, hn⟩ : ∃ n, A.next = n := ⟨_, rfl⟩
  simp only [Arena.drop_next, Arena.drop_link, Arena.drop_node, hn] at hnext hnode hfr L0 L0' L1 L1'
  rw [hn] at c3lt c4lt
  have hacr : ∀ p : PortRef, p.nodeId < n → (∀ k ∈ P.kids, p ≠ A.link k.d) → A'.link p = A.link p :=
    fun p hp hne => hfr p hp (hne _ k3) (hne _ k4)
  obtain ⟨⟨ht', he', hpre', hpost'⟩, hkid'⟩ := P.frame (A' := A')
    (fun m hm => by
      have := P.hlt m hm
      have hmi : m ≠ i := fun h => P.hi (by subst h; exact hm)
      have hmj : m ≠ j := fun h => P.hj (by subst h; exact hm)
      rw [hnode, ite_neg' (show ¬m = n + 1 by omega), ite_neg' (show ¬m = n by omega), ite_neg' hmj, ite_neg' hmi])
    (fun p hp hne => hacr p (hn ▸ hp) hne)
  have ht3' := hkid' _ k3
  have ht4' := hkid' _ k4
  dsimp only at ht3' ht4'
  have tE1 : Tree A' .era (.port ⟨n, 0⟩) [n] [] := .era n (by simp [hnode])
  have tE2 : Tree A' .era (.port ⟨n + 1, 0⟩) [n + 1] [] := .era (n + 1) (by simp [hnode])
  have f3 := facing_new L0 L0' b3.2.2.1
  have f4 := facing_new L1 L1' b4.2.2.1
  have hM := BagIn.cons tE1 ht3' f3 (BagIn.cons tE2 ht4' f4 .nil)
  obtain ⟨hnd', hlt', hall', hρ', hρn'⟩ := P.ids_new (A' := A') (F := [n, n + 1])
    (im := [n] ++ ib1 ++ ([n + 1] ++ ib2 ++ []))
    (List.perm_iff_count.2 fun k => by
      simp only [P, PairData.build, kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_cons,
        List.count_nil, List.append_nil]
      omega)
    (by simp) (fun k hk => by simp at hk; omega) (by omega)
    (fun k hk => by
      rw [hnode] at hk
      by_cases h1 : k = n + 1
      · exact .inl (by simp [h1])
      by_cases h0 : k = n
      · exact .inl (by simp [h0])
      rw [ite_neg' h1, ite_neg' h0] at hk
      by_cases hj : k = j
      · rw [ite_pos' hj] at hk; exact absurd rfl hk
      by_cases hi : k = i
      · rw [ite_neg' hj, ite_pos' hi] at hk; exact absurd rfl hk
      rw [ite_neg' hj, ite_neg' hi] at hk
      exact .inr ⟨hi, hj, hk⟩)
  let N : List (Nat × PortRef) := edgeOcc ⟨n, 0⟩ w1 ++ edgeOcc ⟨n + 1, 0⟩ w2
  have edge_case : ∀ (d P0 : PortRef) (uk : Up) (x : Nat), uk = .var x → (A.link d).nodeId < n →
      P0.nodeId = n ∨ P0.nodeId = n + 1 → A'.link P0 = A.link d → A'.link (A.link d) = P0 →
      ∀ is : List Nat, ((∃ c, uk = .port c ∧ A.link d = c ∧ c.nodeId ∈ is) ∨
        ∃ x', uk = .var x' ∧ (x', A.link d) ∈ P.K) →
      (x, A'.link P0) ∈ P.K ++ N ∧ A'.link P0 ≠ P0 ∧ A'.link (A'.link P0) = P0 := by
    intro d P0 uk x hu hlt0 hP0 e1 e2 is hc
    have hK : (x, A.link d) ∈ P.K := by
      rcases hc with ⟨c, hc, -, -⟩ | ⟨x', hx', hK⟩
      · rw [hu] at hc; cases hc
      · rw [hu] at hx'; cases hx'; exact hK
    refine ⟨by rw [e1]; exact List.mem_append_left _ hK, ?_, by rw [e1, e2]⟩
    rw [e1]; intro h; rw [h] at hlt0; omega
  have hP' := P.paired_new (A' := A') (N := N) (f := fun x => x) (fun p hp hne => hacr p (hn ▸ hp) hne)
    (fun x k hk hu hK => by
      rw [map_renOcc_id]
      simp only [P, PairData.build, kids, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> dsimp only at hu hK ⊢
      · rw [L0']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L0⟩
        rw [← h] at c3lt; dsimp only at c3lt; omega
      · rw [L1']; refine ⟨List.mem_append_right _ (by simp [N, hu, edgeOcc]), fun h => ?_, L1⟩
        rw [← h] at c4lt; dsimp only at c4lt; omega)
    (fun x p hp => by
      rw [map_renOcc_id]
      simp only [N, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c3lt (.inl rfl) L0 L0' _ c3
      · obtain ⟨hu, rfl⟩ := mem_edgeOcc.1 hp
        exact edge_case _ _ _ x hu c4lt (.inr rfl) L1 L1' _ c4)
  rw [map_renOcc_id] at hP'
  have hP'' : Paired A' ((edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ++
      (([] : List (Nat × PortRef)) ++ ob1 ++ edgeOcc ⟨n, 0⟩ w1 ++
        (([] : List (Nat × PortRef)) ++ ob2 ++ edgeOcc ⟨n + 1, 0⟩ w2 ++ []))).map (renOcc fun x => x)) := by
    rw [map_renOcc_id]
    refine paired_congr (fun e => (List.perm_iff_count.2 fun e => ?_).mem_iff) hP'
    simp only [PairData.K, P, PairData.build, kids, N, List.flatMap_cons, List.flatMap_nil, List.count_append,
      List.count_nil, List.append_nil]
    omega
  have := repr_join ht' he' hpre' hpost' hM hnd' hlt' hall' hρ' hρn' hP''
  rwa [cfg_rename_id] at this

/-- **VOID is one arena step**: two erasers meeting vanish. -/
theorem sim_void {A : Arena} {ρ : PortRef} {root : HTree} {pre post : List Redex}
    (hR : Repr A ρ ⟨root, pre ++ (.era, .era) :: post⟩) :
    ∃ A', Arena.Step A A' ∧ Repr A' ρ ⟨root, pre ++ [] ++ post⟩ := by
  obtain ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, hta, htb, hf,
    hnd, hlt, hall, hρ, hρn, hP⟩ := repr_split hR
  obtain ⟨i, rfl, rfl, rfl, hni⟩ := hta.era_inv
  obtain ⟨j, rfl, rfl, rfl, hnj⟩ := htb.era_inv
  obtain ⟨hlij, hlji, rfl⟩ := hf
  have hij : i ≠ j := by
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 i (by simp) j (by simp); exact this
  let P : PairData A ρ root pre post := PairData.build i j [] _ _ ht he hpre hpost (by simp) (by simp)
    (List.perm_iff_count.2 fun k => by simp) (List.perm_iff_count.2 fun e => by simp)
    hnd hlt hall hρ hρn hP (by simp) hlij hlji
  refine ⟨(A.drop i).drop j, .fire hij (inet?_of_node hni) (inet?_of_node hnj) hlij hlji rfl, ?_⟩
  obtain ⟨⟨ht', he', hpre', hpost'⟩, -⟩ := P.frame (A' := (A.drop i).drop j)
    (fun m hm => by
      have hmi : m ≠ i := fun h => P.hi (by subst h; exact hm)
      have hmj : m ≠ j := fun h => P.hj (by subst h; exact hm)
      simp [Arena.drop_node, hmi, hmj])
    (fun p _ _ => rfl)
  obtain ⟨hnd', hlt', hall', hρ', hρn'⟩ := P.ids_new (A' := (A.drop i).drop j) (F := []) (im := [])
    (by simp [P, PairData.build]) (by simp) (by simp) (by simp)
    (fun k hk => by
      simp only [Arena.drop_node] at hk
      by_cases hj : k = j
      · rw [ite_pos' hj] at hk; exact absurd rfl hk
      by_cases hi : k = i
      · rw [ite_neg' hj, ite_pos' hi] at hk; exact absurd rfl hk
      rw [ite_neg' hj, ite_neg' hi] at hk
      exact .inr ⟨hi, hj, hk⟩)
  have hP' := P.paired_new (A' := (A.drop i).drop j) (N := []) (f := fun x => x) (fun p _ _ => rfl)
    (fun x k hk => by simp [P, PairData.build] at hk) (fun x p hp => by simp at hp)
  rw [map_renOcc_id] at hP'
  have hP'' : Paired ((A.drop i).drop j) ((edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ++ []).map
      (renOcc fun x => x)) := by
    rw [map_renOcc_id]
    refine paired_congr (fun e => (List.perm_iff_count.2 fun e => ?_).mem_iff) hP'
    simp [PairData.K, P, PairData.build]
  have := repr_join ht' he' hpre' hpost' .nil hnd' hlt' hall' hρ' hρn' hP''
  rwa [cfg_rename_id] at this

/-! ## ANNI -/

/-- The redex ANNI leaves between two children, unless both are variables (a bare wire, which LINK
removes). -/
def keepPair : HTree → HTree → List Redex
  | .var _, .var _ => []
  | a, b => [(a, b)]

/-- The occurrences of the redex `keepPair` leaves, its sides facing the ports `qa` and `qb` across
from them. -/
def pairOcc (qa qb : PortRef) : Up → Up → List (Nat × PortRef)
  | .var _, .var _ => []
  | u, w => edgeOcc qb u ++ edgeOcc qa w

theorem bag_keep {A' : Arena} {ta tb : HTree} {u w : Up} {ia ib : List Nat} {oa ob : List (Nat × PortRef)}
    {qa qb : PortRef} (hta : Tree A' ta u ia oa) (htb : Tree A' tb w ib ob)
    (hu : ∀ c, u = .port c → qa = c) (hw : ∀ c, w = .port c → qb = c)
    (e1 : A'.link qa = qb) (e2 : A'.link qb = qa) :
    BagIn A' (keepPair ta tb) (ia ++ ib ++ []) (oa ++ ob ++ pairOcc qa qb u w ++ []) := by
  cases u with
  | var x =>
    obtain ⟨rfl, rfl, rfl⟩ := hta.up_var
    cases w with
    | var y => obtain ⟨rfl, rfl, rfl⟩ := htb.up_var; exact .nil
    | port c =>
      have := hw c rfl; subst this
      have hk : keepPair (.var x) tb = [(.var x, tb)] := by
        rcases htb.shape with ⟨y, rfl⟩ | rfl | ⟨_, _, _, _, hc⟩
        · obtain ⟨h, -, -⟩ := htb.var_inv; cases h
        · rfl
        · cases tb <;> simp [cdOf] at hc <;> rfl
      rw [hk]
      exact .cons (.var x) htb rfl .nil
  | port c =>
    have := hu c rfl; subst this
    have hk : keepPair ta tb = [(ta, tb)] := by
      rcases hta.shape with ⟨y, rfl⟩ | rfl | ⟨_, _, _, _, hc⟩
      · obtain ⟨h, -, -⟩ := hta.var_inv; cases h
      · rfl
      · cases ta <;> simp [cdOf] at hc <;> rfl
    rw [hk]
    cases w with
    | var y => exact .cons hta htb rfl .nil
    | port c' => have := hw c' rfl; subst this; exact .cons hta htb ⟨e1, e2, rfl⟩ .nil

theorem link_vv (book : List HDef) (root : HTree) (pre post : List Redex) (x y : Nat) :
    Step book ⟨root, pre ++ (.var x, .var y) :: post⟩
      ⟨root.rename (fun z => if z = x then y else z), (pre ++ post).map (Redex.rename fun z => if z = x then y else z)⟩ := by
  have := Step.link (book := book) (root := root) (pre := pre) (post := post) (x := x) (t := .var y)
  rwa [subst_one_var, List.map_congr_left (fun r _ => redex_subst_one_var x y r)] at this

theorem cd_kind {t a b : HTree} {k : INetNodeKind} {lb : Nat} (h : cdOf t = some (k, lb, a, b)) :
    (k = .con ∧ lb = 0) ∨ (k = .dup ∧ lb = 1) := by
  cases t <;> simp [cdOf] at h <;> obtain ⟨rfl, rfl, -⟩ := h <;> simp

theorem reduce_same {k : INetNodeKind} {lb : Nat} (h : (k = .con ∧ lb = 0) ∨ (k = .dup ∧ lb = 1))
    (i j n : Nat) (a1 a2 b1 b2 : PortRef) :
    reduceActivePair ⟨⟨i, k, lb, 0, a1, a2⟩, ⟨j, k, lb, 0, b1, b2⟩⟩ n = .annihilate (a1, b1) (a2, b2) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [reduceActivePair]

theorem pairOcc_ok {A' : Arena} {K N : List (Nat × PortRef)} {f : Nat → Nat} {u w : Up} {qa qb : PortRef}
    (h1 : A'.link qa = qb) (h2 : A'.link qb = qa) (hne : qa ≠ qb)
    (hu : ∀ x, u = .var x → (x, qa) ∈ K) (hw : ∀ y, w = .var y → (y, qb) ∈ K) :
    ∀ x p, (x, p) ∈ pairOcc qa qb u w →
      (f x, A'.link p) ∈ (K ++ N).map (renOcc f) ∧ A'.link p ≠ p ∧ A'.link (A'.link p) = p := by
  intro x p hp
  cases u <;> cases w <;> simp only [pairOcc, edgeOcc, List.nil_append, List.append_nil, List.mem_cons,
    or_false, Prod.mk.injEq, List.mem_nil_iff] at hp
  · obtain ⟨rfl, rfl⟩ := hp
    rw [h1]; exact ⟨List.mem_map.2 ⟨_, List.mem_append_left _ (hw x rfl), rfl⟩, fun h => hne h.symm, by rw [h2]⟩
  · obtain ⟨rfl, rfl⟩ := hp
    rw [h2]; exact ⟨List.mem_map.2 ⟨_, List.mem_append_left _ (hu x rfl), rfl⟩, fun h => hne h, by rw [h1]⟩

theorem pair_hB {A' : Arena} {K N : List (Nat × PortRef)} {f : Nat → Nat} {u w : Up} {qa qb : PortRef}
    (h1 : A'.link qa = qb) (h2 : A'.link qb = qa) (hne : qa ≠ qb) (hN : ∀ e ∈ pairOcc qa qb u w, e ∈ N)
    (hu : ∀ x, u = .var x → (x, qa) ∈ K) (hw : ∀ y, w = .var y → (y, qb) ∈ K)
    (hf : ∀ x y, u = .var x → w = .var y → f x = f y) :
    (∀ x, u = .var x → (f x, A'.link qa) ∈ (K ++ N).map (renOcc f) ∧ A'.link qa ≠ qa ∧ A'.link (A'.link qa) = qa) ∧
    (∀ y, w = .var y → (f y, A'.link qb) ∈ (K ++ N).map (renOcc f) ∧ A'.link qb ≠ qb ∧ A'.link (A'.link qb) = qb) := by
  refine ⟨fun x hx => ⟨?_, by rw [h1]; exact fun h => hne h.symm, by rw [h1, h2]⟩,
    fun y hy => ⟨?_, by rw [h2]; exact hne, by rw [h2, h1]⟩⟩
  · rw [h1]
    cases w with
    | var y => exact List.mem_map.2 ⟨(y, qb), List.mem_append_left _ (hw y rfl), by simp [renOcc, hf x y hx rfl]⟩
    | port c =>
      subst hx
      exact List.mem_map.2 ⟨(x, qb), List.mem_append_right _ (hN _ (by simp [pairOcc, edgeOcc])), rfl⟩
  · rw [h2]
    cases u with
    | var x => exact List.mem_map.2 ⟨(x, qa), List.mem_append_left _ (hu x rfl), by simp [renOcc, hf x y rfl hy]⟩
    | port c =>
      subst hy
      exact List.mem_map.2 ⟨(y, qa), List.mem_append_right _ (hN _ (by simp [pairOcc, edgeOcc])), rfl⟩

/-- **ANNI is one arena step**: two `CON` (or two `DUP`) nodes meeting annihilate, the children's
wires joined pairwise. A pair of variable children is a bare wire: the result is represented after
HVM2's LINK of them. -/
theorem sim_anni (book : List HDef) {A : Arena} {ρ : PortRef} {root a b a1 a2 b1 b2 : HTree}
    {pre post : List Redex} {k : INetNodeKind} {lb : Nat}
    (hR : Repr A ρ ⟨root, pre ++ (a, b) :: post⟩) (hca : cdOf a = some (k, lb, a1, a2))
    (hcb : cdOf b = some (k, lb, b1, b2)) (hkid : (kidVars a ++ kidVars b).Nodup) :
    ∃ A' c'', Arena.Step A A' ∧ Steps book ⟨root, pre ++ [(a1, b1), (a2, b2)] ++ post⟩ c'' ∧ Repr A' ρ c'' := by
  obtain ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, hta, htb, hf,
    hnd, hlt, hall, hρ, hρn, hP⟩ := repr_split hR
  obtain ⟨i, u1, u2, ia1, ia2, oa1, oa2, rfl, rfl, rfl, hni, ht1, ht2, e1, e2⟩ := hta.bin_inv hca
  obtain ⟨j, w1, w2, ib1, ib2, ob1, ob2, rfl, rfl, rfl, hnj, ht3, ht4, e3, e4⟩ := htb.bin_inv hcb
  obtain ⟨hlij, hlji, rfl⟩ := hf
  have hij : i ≠ j := by
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 i (by simp) j (by simp); exact this
  let kids : List Kid := [⟨⟨i, 1⟩, a1, u1, ia1, oa1⟩, ⟨⟨i, 2⟩, a2, u2, ia2, oa2⟩, ⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩,
    ⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩]
  have hkids : ∀ k ∈ kids, Tree A k.t k.u k.ids k.occ ∧ Edge A k.d k.u ∧ (k.d.nodeId = i ∨ k.d.nodeId = j) ∧
      k.d.slot ≠ 0 := by
    intro k hk
    simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨ht1, e1, .inl rfl, by simp⟩
    · exact ⟨ht2, e2, .inl rfl, by simp⟩
    · exact ⟨ht3, e3, .inr rfl, by simp⟩
    · exact ⟨ht4, e4, .inr rfl, by simp⟩
  have hds : (kids.map Kid.d).Nodup := by
    simp only [kids, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      PortRef.mk.injEq, not_or]
    refine ⟨⟨by omega, fun h => hij h.1, fun h => hij h.1⟩, ⟨fun h => hij h.1, fun h => hij h.1⟩, by omega, by simp,
      List.nodup_nil⟩
  rw [kidVars_cd hca, kidVars_cd hcb] at hkid
  have hvars : ((kids.flatMap fun k => edgeOcc k.d k.u).map Prod.fst).Nodup := by
    simpa [kids, List.flatMap_cons, List.map_append, edgeOcc_fst ht1, edgeOcc_fst ht2, edgeOcc_fst ht3,
      edgeOcc_fst ht4] using hkid
  have hRp : (i :: (ia1 ++ ia2) ++ j :: (ib1 ++ ib2)).Perm ([i, j] ++ kids.flatMap Kid.ids) :=
    List.perm_iff_count.2 fun k => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_cons, List.count_nil]
      omega
  have hOp : (edgeOcc ⟨i, 1⟩ u1 ++ edgeOcc ⟨i, 2⟩ u2 ++ oa1 ++ oa2 ++
      (edgeOcc ⟨j, 1⟩ w1 ++ edgeOcc ⟨j, 2⟩ w2 ++ ob1 ++ ob2) ++ []).Perm
      (kids.flatMap Kid.occ ++ kids.flatMap fun (k : Kid) => edgeOcc k.d k.u) :=
    List.perm_iff_count.2 fun e => by
      simp only [kids, List.flatMap_cons, List.flatMap_nil, List.count_append, List.count_nil]
      omega
  let P : PairData A ρ root pre post := PairData.build i j kids _ _ ht he hpre hpost hkids hds hRp hOp
    hnd hlt hall hρ hρn hP hvars hlij hlji
  have k1 : (⟨⟨i, 1⟩, a1, u1, ia1, oa1⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k2 : (⟨⟨i, 2⟩, a2, u2, ia2, oa2⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k3 : (⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  have k4 : (⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩ : Kid) ∈ P.kids := by simp [P, PairData.build, kids]
  obtain ⟨c1lt, c1i, c1j, c1⟩ := P.across k1
  obtain ⟨c2lt, c2i, c2j, c2⟩ := P.across k2
  obtain ⟨c3lt, c3i, c3j, c3⟩ := P.across k3
  obtain ⟨c4lt, c4i, c4j, c4⟩ := P.across k4
  have b1' := P.bdry k1
  have b2' := P.bdry k2
  have b3' := P.bdry k3
  have b4' := P.bdry k4
  dsimp only at c1lt c1i c1j c1 c2lt c2i c2j c2 c3lt c3i c3j c3 c4lt c4i c4j c4 b1' b2' b3' b4'
  have hd : [A.link ⟨i, 1⟩, A.link ⟨i, 2⟩, A.link ⟨j, 1⟩, A.link ⟨j, 2⟩].Nodup := by
    have inj := fun {k k'} (hk : k ∈ P.kids) (hk' : k' ∈ P.kids) h => P.across_inj hk hk' h
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, by simp, List.nodup_nil⟩
    · have := inj k1 k2 h; simp at this <;> exact hij this
    · have := inj k1 k3 h; simp at this <;> exact hij this
    · have := inj k1 k4 h; simp at this <;> exact hij this
    · have := inj k2 k3 h; simp at this <;> exact hij this
    · have := inj k2 k4 h; simp at this <;> exact hij this
    · have := inj k3 k4 h; simp at this <;> exact hij this
  let l : INetNode := ⟨i, k, lb, 0, A.link ⟨i, 1⟩, A.link ⟨i, 2⟩⟩
  let r : INetNode := ⟨j, k, lb, 0, A.link ⟨j, 1⟩, A.link ⟨j, 2⟩⟩
  have hred : reduceActivePair ⟨l, r⟩ A.next =
      .annihilate (A.link ⟨i, 1⟩, A.link ⟨j, 1⟩) (A.link ⟨i, 2⟩, A.link ⟨j, 2⟩) := reduce_same (cd_kind hca) _ _ _ _ _ _ _
  obtain ⟨hfr, L13, L31, L24, L42⟩ := annArena_link A i j _ _ _ _ hd
  have hnode := annArena_node A i j (A.link ⟨i, 1⟩) (A.link ⟨i, 2⟩) (A.link ⟨j, 1⟩) (A.link ⟨j, 2⟩)
  generalize hA' : (((A.drop i).drop j).connect (A.link ⟨i, 1⟩) (A.link ⟨j, 1⟩)).connect (A.link ⟨i, 2⟩)
    (A.link ⟨j, 2⟩) = A' at hfr L13 L31 L24 L42 hnode
  have hstep : Arena.Step A A' := .fire hij (inet?_of_node hni) (inet?_of_node hnj) hlij hlji
    (by rw [hred, ← hA']; rfl)
  have hnext : A'.next = A.next := by rw [← hA']; rfl
  have hacr : ∀ p : PortRef, p.nodeId < A.next → (∀ k ∈ P.kids, p ≠ A.link k.d) → A'.link p = A.link p := by
    intro p _ hne
    refine hfr p ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hne _ k1, hne _ k2, hne _ k3, hne _ k4⟩
  obtain ⟨⟨ht', he', hpre', hpost'⟩, hkid'⟩ := P.frame (A' := A')
    (fun m hm => by
      have hmi : m ≠ i := fun h => P.hi (by subst h; exact hm)
      have hmj : m ≠ j := fun h => P.hj (by subst h; exact hm)
      rw [hnode, ite_neg' hmj, ite_neg' hmi])
    hacr
  have ht1' := hkid' _ k1
  have ht2' := hkid' _ k2
  have ht3' := hkid' _ k3
  have ht4' := hkid' _ k4
  dsimp only at ht1' ht2' ht3' ht4'
  have hM1 := bag_keep ht1' ht3' b1'.2.2.1 b3'.2.2.1 L13 L31
  have hM2 := bag_keep ht2' ht4' b2'.2.2.1 b4'.2.2.1 L24 L42
  have hM := BagIn.append_iff.2 ⟨_, _, _, _, hM1, hM2, rfl, rfl⟩
  obtain ⟨hnd', hlt', hall', hρ', hρn'⟩ := P.ids_new (A' := A') (F := [])
    (im := ia1 ++ ib1 ++ [] ++ (ia2 ++ ib2 ++ []))
    (List.perm_iff_count.2 fun k => by
      simp only [P, PairData.build, kids, List.flatMap_cons, List.flatMap_nil, List.count_append,
        List.append_nil, List.nil_append]
      omega)
    (by simp) (by simp) (by omega)
    (fun k hk => by
      rw [hnode] at hk
      by_cases hj : k = j
      · rw [ite_pos' hj] at hk; exact absurd rfl hk
      by_cases hi : k = i
      · rw [ite_neg' hj, ite_pos' hi] at hk; exact absurd rfl hk
      rw [ite_neg' hj, ite_neg' hi] at hk
      exact .inr ⟨hi, hj, hk⟩)
  -- the representation, every variable renamed by any `f` that joins each pair of variable children
  have core : ∀ f : Nat → Nat, (∀ x y, u1 = .var x → w1 = .var y → f x = f y) →
      (∀ x y, u2 = .var x → w2 = .var y → f x = f y) →
      Repr A' ρ ⟨root.rename f, (pre ++ (keepPair a1 b1 ++ keepPair a2 b2) ++ post).map (Redex.rename f)⟩ := by
    intro f hf1 hf2
    have kv : ∀ (k : Kid) (uk : Up), k.u = uk → ∀ (c : (∃ c, uk = .port c ∧ A.link k.d = c ∧ c.nodeId ∈ k.ids) ∨
        (∃ x, uk = .var x ∧ (x, A.link k.d) ∈ P.K)), ∀ x, uk = .var x → (x, A.link k.d) ∈ P.K := by
      intro k uk _ c x hx
      rcases c with ⟨c, hc, -, -⟩ | ⟨x', hx', hK⟩
      · rw [hx] at hc; cases hc
      · rw [hx] at hx'; cases hx'; exact hK
    have v1 := kv ⟨⟨i, 1⟩, a1, u1, ia1, oa1⟩ u1 rfl c1
    have v2 := kv ⟨⟨i, 2⟩, a2, u2, ia2, oa2⟩ u2 rfl c2
    have v3 := kv ⟨⟨j, 1⟩, b1, w1, ib1, ob1⟩ w1 rfl c3
    have v4 := kv ⟨⟨j, 2⟩, b2, w2, ib2, ob2⟩ w2 rfl c4
    dsimp only at v1 v2 v3 v4
    have n13 : A.link ⟨i, 1⟩ ≠ A.link ⟨j, 1⟩ := fun h => by have := P.across_inj k1 k3 h; simp at this; exact hij this
    have n24 : A.link ⟨i, 2⟩ ≠ A.link ⟨j, 2⟩ := fun h => by have := P.across_inj k2 k4 h; simp at this; exact hij this
    let N := pairOcc (A.link ⟨i, 1⟩) (A.link ⟨j, 1⟩) u1 w1 ++ pairOcc (A.link ⟨i, 2⟩) (A.link ⟨j, 2⟩) u2 w2
    obtain ⟨hB1, hB3⟩ := pair_hB (K := P.K) (N := N) (f := f) L13 L31 n13
      (fun e he => List.mem_append_left _ he) v1 v3 hf1
    obtain ⟨hB2, hB4⟩ := pair_hB (K := P.K) (N := N) (f := f) L24 L42 n24
      (fun e he => List.mem_append_right _ he) v2 v4 hf2
    have hP' := P.paired_new (A' := A') (N := N) (f := f) hacr
      (fun x k hk hu _ => by
        simp only [P, PairData.build, kids, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> dsimp only at hu ⊢
        · exact hB1 x hu
        · exact hB2 x hu
        · exact hB3 x hu
        · exact hB4 x hu)
      (fun x p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact pairOcc_ok L13 L31 n13 v1 v3 x p hp
        · exact pairOcc_ok L24 L42 n24 v2 v4 x p hp)
    have hP'' : Paired A' ((edgeOcc ρ P.u ++ P.or ++ P.opre ++ P.opost ++
        (oa1 ++ ob1 ++ pairOcc (A.link ⟨i, 1⟩) (A.link ⟨j, 1⟩) u1 w1 ++ [] ++
          (oa2 ++ ob2 ++ pairOcc (A.link ⟨i, 2⟩) (A.link ⟨j, 2⟩) u2 w2 ++ []))).map (renOcc f)) := by
      refine paired_congr (fun e => (List.Perm.map _ (List.perm_iff_count.2 fun e => ?_)).mem_iff) hP'
      simp only [PairData.K, P, PairData.build, kids, N, List.flatMap_cons, List.flatMap_nil, List.count_append,
        List.append_nil]
      omega
    exact repr_join ht' he' hpre' hpost' hM hnd' (fun k hk => hnext ▸ hlt' k hk) hall' (hnext ▸ hρ') hρn' hP''
  -- which pairs of children are bare wires
  have up_of : ∀ {t : HTree} {u : Up} {is : List Nat} {os : List (Nat × PortRef)}, Tree A t u is os →
      ∀ x, u = .var x → t = .var x := fun h x hx => by subst hx; exact h.up_var.1
  have redex_rr : ∀ (f g : Nat → Nat) (r : Redex), (r.rename f).rename g = r.rename (fun v => g (f v)) := by
    intro f g r; simp [Redex.rename, rename_rename]
  by_cases v1 : ∃ x y, a1 = .var x ∧ b1 = .var y <;> by_cases v2 : ∃ x y, a2 = .var x ∧ b2 = .var y
  · obtain ⟨x, y, rfl, rfl⟩ := v1
    obtain ⟨z, w, rfl, rfl⟩ := v2
    have hxz : x ≠ z := by rintro rfl; have := nodup_iff_count.1 hkid x; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    have hxy : x ≠ y := by rintro rfl; have := nodup_iff_count.1 hkid x; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    have hxw : x ≠ w := by rintro rfl; have := nodup_iff_count.1 hkid x; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    have hzy : z ≠ y := by rintro rfl; have := nodup_iff_count.1 hkid z; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    have hzw : z ≠ w := by rintro rfl; have := nodup_iff_count.1 hkid z; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    let f1 := fun v => if v = x then y else v
    let f2 := fun v => if v = z then w else v
    have h := core (fun v => f2 (f1 v))
      (fun x' y' hx hy => by
        rw [(ht1.var_inv).1] at hx; rw [(ht3.var_inv).1] at hy; cases hx; cases hy
        simp [f1, f2, Ne.symm hzy])
      (fun x' y' hx hy => by
        rw [(ht2.var_inv).1] at hx; rw [(ht4.var_inv).1] at hy; cases hx; cases hy
        simp [f1, f2, Ne.symm hxz, Ne.symm hxw])
    refine ⟨A', _, hstep, ?_, h⟩
    have s1 := link_vv book root pre ((.var z, .var w) :: post) x y
    have e1 : ((pre ++ (HTree.var z, HTree.var w) :: post).map (Redex.rename f1)) =
        pre.map (Redex.rename f1) ++ (HTree.var z, HTree.var w) :: post.map (Redex.rename f1) := by
      simp [Redex.rename, HTree.rename, f1, Ne.symm hxz, Ne.symm hxw]
    rw [e1] at s1
    have s2 := link_vv book (root.rename f1) (pre.map (Redex.rename f1)) (post.map (Redex.rename f1)) z w
    have e2 : (⟨(root.rename f1).rename f2, (pre.map (Redex.rename f1) ++ post.map (Redex.rename f1)).map
        (Redex.rename f2)⟩ : Cfg) = ⟨root.rename (fun v => f2 (f1 v)),
          (pre ++ (keepPair (.var x) (.var y) ++ keepPair (.var z) (.var w)) ++ post).map
            (Redex.rename fun v => f2 (f1 v))⟩ := by
      simp only [keepPair, List.append_nil, rename_rename, List.map_append, List.map_map]
      congr 1
      simp only [Function.comp_def, redex_rr]
    rw [e2] at s2
    have e0 : pre ++ [(HTree.var x, HTree.var y), (HTree.var z, HTree.var w)] ++ post =
        pre ++ (HTree.var x, HTree.var y) :: (HTree.var z, HTree.var w) :: post := by simp
    rw [e0]
    exact .next s1 (.single s2)
  · obtain ⟨x, y, rfl, rfl⟩ := v1
    have hxy : x ≠ y := by rintro rfl; have := nodup_iff_count.1 hkid x; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    let f1 := fun v => if v = x then y else v
    have h := core f1
      (fun x' y' hx hy => by
        rw [(ht1.var_inv).1] at hx; rw [(ht3.var_inv).1] at hy; cases hx; cases hy
        simp [f1])
      (fun x' y' hx hy => absurd ⟨x', y', up_of ht2 x' hx, up_of ht4 y' hy⟩ v2)
    have hk2 : keepPair a2 b2 = [(a2, b2)] := by
      cases a2 <;> cases b2 <;> first | rfl | exact absurd ⟨_, _, rfl, rfl⟩ v2
    rw [hk2] at h
    refine ⟨A', _, hstep, ?_, h⟩
    have s1 := link_vv book root pre ((a2, b2) :: post) x y
    have e0 : pre ++ [(HTree.var x, HTree.var y), (a2, b2)] ++ post = pre ++ (HTree.var x, HTree.var y) :: (a2, b2) :: post := by
      simp
    rw [e0]
    simpa [keepPair] using Steps.single s1
  · obtain ⟨z, w, rfl, rfl⟩ := v2
    have hzw : z ≠ w := by rintro rfl; have := nodup_iff_count.1 hkid z; simp only [topVar, List.count_append, List.count_cons, List.count_nil,
        beq_self_eq_true, ite_true] at this; omega
    let f2 := fun v => if v = z then w else v
    have h := core f2
      (fun x' y' hx hy => absurd ⟨x', y', up_of ht1 x' hx, up_of ht3 y' hy⟩ v1)
      (fun x' y' hx hy => by
        rw [(ht2.var_inv).1] at hx; rw [(ht4.var_inv).1] at hy; cases hx; cases hy
        simp [f2])
    have hk1 : keepPair a1 b1 = [(a1, b1)] := by
      cases a1 <;> cases b1 <;> first | rfl | exact absurd ⟨_, _, rfl, rfl⟩ v1
    rw [hk1] at h
    refine ⟨A', _, hstep, ?_, h⟩
    have s1 := link_vv book root (pre ++ [(a1, b1)]) post z w
    have e0 : pre ++ [(a1, b1), (HTree.var z, HTree.var w)] ++ post = pre ++ [(a1, b1)] ++ (HTree.var z, HTree.var w) :: post := by
      simp
    rw [e0]
    simpa [keepPair] using Steps.single s1
  · have h := core (fun v => v)
      (fun x' y' hx hy => absurd ⟨x', y', up_of ht1 x' hx, up_of ht3 y' hy⟩ v1)
      (fun x' y' hx hy => absurd ⟨x', y', up_of ht2 x' hx, up_of ht4 y' hy⟩ v2)
    have hk1 : keepPair a1 b1 = [(a1, b1)] := by
      cases a1 <;> cases b1 <;> first | rfl | exact absurd ⟨_, _, rfl, rfl⟩ v1
    have hk2 : keepPair a2 b2 = [(a2, b2)] := by
      cases a2 <;> cases b2 <;> first | rfl | exact absurd ⟨_, _, rfl, rfl⟩ v2
    rw [hk1, hk2, cfg_rename_id] at h
    exact ⟨A', _, hstep, by simpa using Steps.refl _, by simpa using h⟩

/-! ## The map -/

theorem facing_swap {A : Arena} {ua ub : Up} {o : List (Nat × PortRef)} (h : Facing A ua ub o) :
    Facing A ub ua o := by
  cases ua <;> cases ub <;> simp only [Facing] at h ⊢
  · exact ⟨h.2.1, h.1, h.2.2⟩
  · exact h
  · exact h

/-- **Orientation does not matter**: a redex and its swap are the same arena. -/
theorem repr_swap {A : Arena} {ρ : PortRef} {root a b : HTree} {pre post : List Redex}
    (hR : Repr A ρ ⟨root, pre ++ (a, b) :: post⟩) : Repr A ρ ⟨root, pre ++ (b, a) :: post⟩ := by
  obtain ⟨u, ua, ub, ir, ipre, ipost, ia, ib, or, opre, opost, oa, ob, o, ht, he, hpre, hpost, hta, htb, hf,
    hnd, hlt, hall, hρ, hρn, hP⟩ := repr_split hR
  have hp : (ir ++ ipre ++ ipost ++ (ib ++ ia ++ [])).Perm (ir ++ ipre ++ ipost ++ (ia ++ ib)) :=
    List.perm_iff_count.2 fun k => by simp only [List.count_append, List.count_nil]; omega
  have := repr_join (f := fun x => x) ht he hpre hpost (BagIn.cons htb hta (facing_swap hf) .nil)
    (hp.nodup_iff.2 hnd) (fun k hk => hlt k (hp.mem_iff.1 hk)) (fun k hk => hp.mem_iff.2 (hall k hk)) hρ
    (fun h => hρn (hp.mem_iff.1 h))
    (by
      rw [map_renOcc_id]
      exact paired_congr (fun e => (List.perm_iff_count.2 fun e => by
        simp only [List.count_append, List.count_nil]; omega).mem_iff) hP)
  rw [cfg_rename_id] at this
  simpa using this

theorem localRule_var (x : Nat) (b : HTree) : localRule (.var x) b = none := by
  cases b <;> rfl

/-- **`inetOfHvm_sound`**: in an arena representing a configuration, every interaction step of the
configuration (VOID, ERAS, ANNI on `CON`/`DUP`/`ERA`, and COMM) is one `Arena.Step` (the pair fired
and rewritten by `reduceActivePair`'s outcome) to an arena representing the result, after HVM2's
LINK of the bare wires ANNI leaves. -/
theorem inetOfHvm_sound (book : List HDef) {A : Arena} {ρ : PortRef} {c c' : Cfg}
    (hR : Repr A ρ c) (hs : Interacts c c') :
    ∃ A' c'', Arena.Step A A' ∧ Steps book c' c'' ∧ Repr A' ρ c'' := by
  cases hs with
  | comm ha hb hk _ _ hkid =>
    obtain ⟨A', hst, hr⟩ := sim_comm hR ha hb hk hkid
    exact ⟨A', _, hst, .refl _, hr⟩
  | @rule root pre post a b ns h hkid =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hta, htb, _⟩ := repr_split hR
    rcases hta.shape with ⟨x, rfl⟩ | rfl | ⟨ka, lba, a1, a2, hca⟩
    · rw [localRule_var] at h; cases h
    · rcases htb.shape with ⟨y, rfl⟩ | rfl | ⟨kb, lbb, b1, b2, hcb⟩
      · simp [localRule] at h
      · simp only [localRule, Option.some.injEq] at h; subst h
        obtain ⟨A', hst, hr⟩ := sim_void hR
        exact ⟨A', _, hst, .refl _, hr⟩
      · have hk : (kidVars b).Nodup := by simpa [kidVars, cdOf] using hkid
        cases b <;> simp [cdOf] at hcb <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hcb <;>
          simp only [localRule, Option.some.injEq] at h <;> subst h <;>
          · obtain ⟨A', hst, hr⟩ := sim_eras hR (by rfl) hk
            exact ⟨A', _, hst, .refl _, hr⟩
    · rcases htb.shape with ⟨y, rfl⟩ | rfl | ⟨kb, lbb, b1, b2, hcb⟩
      · cases a <;> simp [cdOf] at hca <;> simp [localRule] at h
      · cases a <;> simp [cdOf] at hca <;> simp [localRule] at h
      · cases a <;> simp [cdOf] at hca <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hca <;>
          cases b <;> simp [cdOf] at hcb <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hcb <;>
          simp only [localRule, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
          exact sim_anni book hR rfl rfl hkid

end Obend.Hardware.Hvm
