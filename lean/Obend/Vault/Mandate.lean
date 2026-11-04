module
/-
# Obend.Vault.Mandate — confined agent capability mandates, attenuation trees, & invocation validation

Absorbs `breadstuffs/Dregg2/Agent/Mandate.lean`, `starbridge-v2/src/powerbox.rs`, and `resident_agent.rs`
onto `Obend/Intention.lean` and `Obend/Run/Fork.lean`.

Addresses Requirement R3 and Milestone 3 Feature 28 (`Mandate`):
1. **Mandate Structure** (rekeyed 2026-11-04): a mandate names WHO may act — a `Principal`, the vault
   member identity (`Obend.Vault.Store.Member`: name and id) that `Obend.Vault.commit` binds into every
   write as its poster — and UNDER WHICH GRANT it acts (`Grant`: the root grant of a target by its
   owner, or the parent mandate it was delegated from), with the target domain, capability set
   (`rights`), spend ceiling (`budget`), cell mask (`cells`), expiration (`expiresAt`) and runtime
   method filter (`caveat`). Until then the holder and grantor were strings a turn asserted.
2. **Strict Attenuation Preorder**: `attenuates child parent : Prop`, reflexive and transitive.
   Delegation (`Mandate.delegate`) returns the parent AFTER and the child: the child's budget is carved
   out of the parent's by construction (`delegate_conserves`: their sum is the parent's budget before),
   the child attenuates the parent (`delegate_child_attenuates`) and so does what the parent keeps
   (`delegate_parent_attenuates`); there is no second ledger to check.
3. **Invocation Validation & Soundness**: `checkInvocation` validates the principal and the authority
   before a turn; `refusal` says why not, naming the principal and the grant (`Refusal`,
   `refusal_none_iff`). `authorizedBy_attenuates`: an invocation authorized under an attenuated child
   mandate is authorized under the parent.
4. **Delegation Trees & Resource Conservation**: `DelegTree` models hierarchical agent delegation cones.
   Proves no-amplification down the tree (`subtree_budget_le_root`, `subtree_expires_le_root`,
   `subtree_target_eq_root`, `subtree_authorized_by_root`) and budget partition conservation
   (`BudgetPartitioned`, `children_no_oversubscribe`).
5. **Connection to Intention & Narrows Preorder**: Equates mandate attenuation to forever-crown law
   refinement preorder `mandateNarrows` (`NEXT-MATHEMATICA.md:62`).
-/
public import Obend.Core.Digest
public import Obend.Digest.HashBytes

@[expose] public section

namespace Obend.Vault.Mandate

set_option autoImplicit false

/-! ## 1. Authority Kinds & Runtime Caveat Windows -/

/-- Authority kinds representing seL4/Dregg2 IPC authorities. -/
inductive Auth where
  | read
  | write
  | grant
  | call
  | reply
  | reset
  | control
  | notify
  deriving DecidableEq, Repr

/-- A runtime caveat: evaluates an action's method code to decide admissibility.
    Sub-delegation conjoins caveats so a child is bound by its own AND all ancestors' restrictions. -/
structure Caveat where
  admits : Nat → Bool

def Caveat.any : Caveat := ⟨fun _ => true⟩

def Caveat.and (c₁ c₂ : Caveat) : Caveat :=
  ⟨fun m => c₁.admits m && c₂.admits m⟩

/-! ## 2. Principals, Grants, Mandates & Invocations -/

/-- Who may act: a member of the vault, by name and id — the identity `Obend.Vault.Store.Member`
carries and `Obend.Vault.commit` binds into every write as its poster. A mandate names a principal,
not a string a turn asserts. -/
structure Principal where
  name : String
  id   : Nat
  deriving DecidableEq, Repr

def Principal.describe (p : Principal) : String := s!"{p.name}#{p.id}"

/-- The capability a mandate is under: the root grant of a target by its owner, or the parent mandate
it was delegated from, by that mandate's id. A refusal names it. -/
inductive Grant where
  | root (owner : Principal) (target : String)
  | under (parent : Nat)
  deriving DecidableEq, Repr

def Grant.describe : Grant → String
  | .root owner target => s!"the root grant of {target} by {owner.describe}"
  | .under parent => s!"mandate {parent}"

/-- A confined agent capability mandate.
    - `id`: this mandate's id, what a child's `grant` names
    - `grant`: the capability it is under
    - `principal`: who may act under it
    - `target`: the target domain / system
    - `rights`: the capability set
    - `budget`: the resource spend quota / ceiling
    - `cells`: cell access mask (authorized cell IDs)
    - `expiresAt`: expiration term / epoch
    - `caveat`: runtime method filter window -/
structure Mandate where
  id        : Nat
  grant     : Grant
  principal : Principal
  target    : String
  rights    : List Auth
  budget    : Nat
  cells     : List Nat
  expiresAt : Nat
  caveat    : Caveat

/-- An action invocation attempted by a principal. -/
structure Invocation where
  principal    : Principal
  target       : String
  cell         : Nat
  method       : Nat
  requiredAuth : List Auth
  cost         : Nat
  epoch        : Nat
  deriving DecidableEq, Repr

/-! ## 3. Attenuation Preorder -/

/-- **The Attenuation Relation**: `attenuates child parent` holds iff every dimension of `child`
    is narrower than or equal to `parent`. -/
def attenuates (child parent : Mandate) : Prop :=
  child.rights ⊆ parent.rights ∧
  child.budget ≤ parent.budget ∧
  child.cells ⊆ parent.cells ∧
  child.expiresAt ≤ parent.expiresAt ∧
  child.target = parent.target ∧
  (∀ m, child.caveat.admits m = true → parent.caveat.admits m = true)

/-- Reflexivity of attenuation. -/
theorem attenuates_refl (m : Mandate) : attenuates m m := by
  refine ⟨fun _ ha => ha, Nat.le_refl _, fun _ hc => hc, Nat.le_refl _, rfl, fun _ h => h⟩

/-- **Transitivity of Attenuation**: Attenuation chains down arbitrary delegation depths. -/
theorem attenuates_trans {m₁ m₂ m₃ : Mandate}
    (h12 : attenuates m₁ m₂) (h23 : attenuates m₂ m₃) : attenuates m₁ m₃ := by
  rcases h12 with ⟨hr12, hb12, hc12, he12, ht12, hcv12⟩
  rcases h23 with ⟨hr23, hb23, hc23, he23, ht23, hcv23⟩
  refine ⟨fun a ha => hr23 (hr12 ha),
          Nat.le_trans hb12 hb23,
          fun c hc => hc23 (hc12 hc),
          Nat.le_trans he12 he23,
          ht12.trans ht23,
          fun m hm => hcv23 m (hcv12 m hm)⟩

/-- **Delegation debits the parent by construction.** `delegate parent childId child …` is the pair
(parent after, child): the child's budget is `min parent.budget quota` and the parent keeps
`parent.budget - child.budget`; the child's grant is `.under parent.id`. There is no second ledger to
check (`delegate_conserves`). -/
def Mandate.delegate (parent : Mandate) (childId : Nat) (child : Principal) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) : Mandate × Mandate :=
  let childBudget := min parent.budget quota
  ({ parent with budget := parent.budget - childBudget },
   { id        := childId
     grant     := .under parent.id
     principal := child
     target    := parent.target
     rights    := parent.rights.filter (fun a => reqRights.contains a)
     budget    := childBudget
     cells     := parent.cells.filter (fun c => mask.contains c)
     expiresAt := min parent.expiresAt term
     caveat    := parent.caveat.and cv })

theorem delegate_conserves (parent : Mandate) (childId : Nat) (child : Principal) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) :
    (parent.delegate childId child reqRights quota mask term cv).1.budget +
      (parent.delegate childId child reqRights quota mask term cv).2.budget = parent.budget := by
  simp only [Mandate.delegate]
  exact Nat.sub_add_cancel (Nat.min_le_left _ _)

theorem delegate_child_grant (parent : Mandate) (childId : Nat) (child : Principal) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) :
    (parent.delegate childId child reqRights quota mask term cv).2.grant = .under parent.id := rfl

theorem delegate_parent_attenuates (parent : Mandate) (childId : Nat) (child : Principal) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) :
    attenuates (parent.delegate childId child reqRights quota mask term cv).1 parent :=
  ⟨fun _ ha => ha, Nat.sub_le _ _, fun _ hc => hc, Nat.le_refl _, rfl, fun _ hm => hm⟩

/-- The pre-2026-11-04 constructor, kept as the child half of `delegate` for the two proofs below. -/
def Mandate.subDelegate (parent : Mandate) (child : String) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) : Mandate where
  id        := 0
  grant     := .under parent.id
  principal := ⟨child, 0⟩
  target    := parent.target
  rights    := parent.rights.filter (fun a => reqRights.contains a)
  budget    := min parent.budget quota
  cells     := parent.cells.filter (fun c => mask.contains c)
  expiresAt := min parent.expiresAt term
  caveat    := parent.caveat.and cv

/-- **Sub-delegation is Strictly Attenuating**: the child never amplifies authority. -/
theorem subDelegate_attenuates (parent : Mandate) (child : String) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) :
    attenuates (parent.subDelegate child reqRights quota mask term cv) parent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (List.mem_filter.mp ha).1
  · exact Nat.min_le_left _ _
  · intro c hc; exact (List.mem_filter.mp hc).1
  · exact Nat.min_le_left _ _
  · rfl
  · intro m hm
    simp only [Mandate.subDelegate, Caveat.and] at hm
    exact (Bool.and_eq_true _ _ |>.mp hm).1

theorem delegate_child_attenuates (parent : Mandate) (childId : Nat) (child : Principal) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) :
    attenuates (parent.delegate childId child reqRights quota mask term cv).2 parent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (List.mem_filter.mp ha).1
  · exact Nat.min_le_left _ _
  · intro c hc; exact (List.mem_filter.mp hc).1
  · exact Nat.min_le_left _ _
  · rfl
  · intro m hm
    simp only [Mandate.delegate, Caveat.and] at hm
    exact (Bool.and_eq_true _ _ |>.mp hm).1

/-! ## 4. Invocation Validation & Soundness -/

/-- Check whether an invocation's parameters fall within a mandate's authorization envelope. -/
def authorizedBy (m : Mandate) (inv : Invocation) : Bool :=
  (inv.target == m.target) &&
  (inv.requiredAuth.all m.rights.contains) &&
  (inv.cost ≤ m.budget) &&
  (m.cells.contains inv.cell) &&
  (inv.epoch ≤ m.expiresAt) &&
  (m.caveat.admits inv.method)

/-- Full invocation check: the principal, then the authorization envelope. -/
def checkInvocation (m : Mandate) (inv : Invocation) : Bool :=
  (inv.principal == m.principal) && authorizedBy m inv

/-- Why an invocation is refused. Every clause names the principal and the grant the mandate is under,
so a refusal says who and under what, and what is missing. -/
inductive Refusal where
  | notThePrincipal (holder actual : Principal) (grant : Grant)
  | wrongTarget (p : Principal) (grant : Grant) (target : String)
  | missingRight (p : Principal) (grant : Grant) (right : Auth)
  | overBudget (p : Principal) (grant : Grant) (cost budget : Nat)
  | cellOutside (p : Principal) (grant : Grant) (cell : Nat)
  | expired (p : Principal) (grant : Grant) (epoch expiresAt : Nat)
  | methodRefused (p : Principal) (grant : Grant) (method : Nat)
  deriving DecidableEq, Repr

def Refusal.describe : Refusal → String
  | .notThePrincipal holder actual grant =>
    s!"{actual.describe} is not the principal of this mandate ({holder.describe}, under {grant.describe})"
  | .wrongTarget p grant target => s!"{p.describe} under {grant.describe} has no authority over {target}"
  | .missingRight p grant r => s!"{p.describe} under {grant.describe} lacks {toString (repr r)}"
  | .overBudget p grant cost budget => s!"{p.describe} under {grant.describe}: cost {cost} exceeds budget {budget}"
  | .cellOutside p grant cell => s!"{p.describe} under {grant.describe} may not touch cell {cell}"
  | .expired p grant epoch expiresAt => s!"{p.describe} under {grant.describe} expired at {expiresAt} (epoch {epoch})"
  | .methodRefused p grant method => s!"{p.describe} under {grant.describe}: method {method} refused by caveat"

/-- The refusal, if any: the same tests as `checkInvocation`, in order, naming what failed. -/
def refusal (m : Mandate) (inv : Invocation) : Option Refusal :=
  if !(inv.principal == m.principal) then some (.notThePrincipal m.principal inv.principal m.grant)
  else if !(inv.target == m.target) then some (.wrongTarget m.principal m.grant inv.target)
  else match inv.requiredAuth.find? (fun a => !m.rights.contains a) with
  | some a => some (.missingRight m.principal m.grant a)
  | none =>
    if !decide (inv.cost ≤ m.budget) then some (.overBudget m.principal m.grant inv.cost m.budget)
    else if !m.cells.contains inv.cell then some (.cellOutside m.principal m.grant inv.cell)
    else if !decide (inv.epoch ≤ m.expiresAt) then some (.expired m.principal m.grant inv.epoch m.expiresAt)
    else if !m.caveat.admits inv.method then some (.methodRefused m.principal m.grant inv.method)
    else none

theorem find_not_none_iff_all {α : Type} (p : α → Bool) (l : List α) :
    l.find? (fun a => !p a) = none ↔ l.all p = true := by
  simp [List.find?_eq_none, List.all_eq_true]

theorem find_not_some_all_false {α : Type} (p : α → Bool) (l : List α) {a : α}
    (h : l.find? (fun a => !p a) = some a) : l.all p = false := by
  have hmem := List.mem_of_find?_eq_some h
  have hpa := List.find?_some h
  cases hall : l.all p
  · rfl
  · exfalso
    have := List.all_eq_true.1 hall a hmem
    rw [this] at hpa
    cases hpa

/-- **A refusal is exactly a failed check**: `refusal` is `none` iff `checkInvocation` holds, so what a
refusal names is what the check tested. -/
theorem refusal_none_iff (m : Mandate) (inv : Invocation) :
    refusal m inv = none ↔ checkInvocation m inv = true := by
  unfold refusal checkInvocation authorizedBy
  cases hf : inv.requiredAuth.find? (fun a => !m.rights.contains a) with
  | some a =>
    have hall := find_not_some_all_false _ _ hf
    have hmem := List.mem_of_find?_eq_some hf
    have hpa := List.find?_some hf
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_iff_mem] at hpa
    cases hp : (inv.principal == m.principal) <;> cases ht : (inv.target == m.target) <;>
      simp_all <;> exact fun h => absurd (h a hmem) hpa
  | none =>
    have hall := (find_not_none_iff_all _ _).1 hf
    cases hp : (inv.principal == m.principal) <;>
    cases ht : (inv.target == m.target) <;>
    cases hb : decide (inv.cost ≤ m.budget) <;>
    cases hc : m.cells.contains inv.cell <;>
    cases he : decide (inv.epoch ≤ m.expiresAt) <;>
    cases hm : m.caveat.admits inv.method <;>
    simp_all

/-- **Invocation Soundness Theorem**: Any invocation authorized by an attenuated child mandate
    is provably authorized under the enclosing parent mandate. -/
theorem authorizedBy_attenuates {m_child m_parent : Mandate} {inv : Invocation}
    (hatten : attenuates m_child m_parent)
    (hauth : authorizedBy m_child inv = true) :
    authorizedBy m_parent inv = true := by
  rcases hatten with ⟨hr, hb, hc, he, ht, hcv⟩
  simp only [authorizedBy, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hauth ⊢
  obtain ⟨⟨⟨⟨⟨htgt, hauth_req⟩, hcost⟩, hcell⟩, hepoch⟩, hmeth⟩ := hauth
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← ht]; exact htgt
  · simp only [List.all_eq_true] at hauth_req ⊢
    intro a ha
    have ha' := hauth_req a ha
    rw [List.contains_iff_mem] at ha' ⊢
    exact hr ha'
  · exact Nat.le_trans hcost hb
  · rw [List.contains_iff_mem] at hcell ⊢
    exact hc hcell
  · exact Nat.le_trans hepoch he
  · exact hcv inv.method hmeth

/-! ## 5. Capability Delegation Trees & Tree-Level Metatheorems -/

/-- A node of the capability delegation tree: a mandate paired with its children subtrees. -/
inductive DelegTree where
  | node (m : Mandate) (children : List DelegTree)

def DelegTree.mandate : DelegTree → Mandate
  | .node m _ => m

def DelegTree.children : DelegTree → List DelegTree
  | .node _ cs => cs

/-- Structural invariant: every edge in the delegation tree is a valid, non-amplifying attenuation. -/
def DelegTree.WellAttenuated : DelegTree → Prop
  | .node m cs =>
      (∀ c ∈ cs, attenuates c.mandate m ∧ c.mandate.grant = .under m.id) ∧
      (∀ c ∈ cs, c.WellAttenuated)

theorem WellAttenuated_edge {m : Mandate} {cs : List DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) :
    ∀ c ∈ cs, attenuates c.mandate m ∧ c.mandate.grant = .under m.id := by
  rw [DelegTree.WellAttenuated] at hw; exact hw.1

theorem WellAttenuated_children {m : Mandate} {cs : List DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) :
    ∀ c ∈ cs, c.WellAttenuated := by
  rw [DelegTree.WellAttenuated] at hw; exact hw.2

def DelegTree.childrenBudget (t : DelegTree) : Nat :=
  (t.children.map (fun c => c.mandate.budget)).sum

/-- Budget partition invariant: immediate children's budgets sum to at most the node's budget. -/
def DelegTree.BudgetPartitioned : DelegTree → Prop
  | t@(.node _ cs) => t.childrenBudget ≤ t.mandate.budget ∧ (∀ c ∈ cs, c.BudgetPartitioned)

/-- Conservation: No node oversubscribes its budget to its children. -/
theorem children_no_oversubscribe {m : Mandate} {cs : List DelegTree}
    (hp : (DelegTree.node m cs).BudgetPartitioned) :
    (cs.map (fun c => c.mandate.budget)).sum ≤ m.budget := by
  rw [DelegTree.BudgetPartitioned] at hp
  exact hp.1

/-- Tree-level authorization soundness: an invocation authorized by a child is authorized by the root. -/
theorem subtree_authorized_by_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ (c : DelegTree), c ∈ t.children → ∀ (inv : Invocation),
    authorizedBy c.mandate inv = true → authorizedBy t.mandate inv
  | .node m cs, hw, c, hc, inv, hauth => by
    have hedge := WellAttenuated_edge hw c hc
    exact authorizedBy_attenuates hedge.1 hauth

def DelegTree.budgets : DelegTree → List Nat
  | .node m cs => m.budget :: cs.flatMap DelegTree.budgets

/-- **No Descendant Out-Spends Root**: Every budget in a well-attenuated tree is bounded by root budget. -/
theorem subtree_budget_le_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ b ∈ t.budgets, b ≤ t.mandate.budget
  | .node m cs, hw => by
      intro b hb
      rw [DelegTree.budgets] at hb
      rcases List.mem_cons.mp hb with hroot | hsub
      · subst hroot; exact Nat.le_refl _
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, hbc⟩ := hsub
        have hedge := WellAttenuated_edge hw c hc
        have hchild : c.mandate.budget ≤ m.budget := hedge.1.2.1
        have hrec : b ≤ c.mandate.budget :=
          subtree_budget_le_root c (WellAttenuated_children hw c hc) b hbc
        exact Nat.le_trans hrec hchild

def DelegTree.expirations : DelegTree → List Nat
  | .node m cs => m.expiresAt :: cs.flatMap DelegTree.expirations

/-- **No Descendant Out-Lives Root**: Every expiration in a well-attenuated tree is bounded by root expiration. -/
theorem subtree_expires_le_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ e ∈ t.expirations, e ≤ t.mandate.expiresAt
  | .node m cs, hw => by
      intro e he
      rw [DelegTree.expirations] at he
      rcases List.mem_cons.mp he with hroot | hsub
      · subst hroot; exact Nat.le_refl _
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, hec⟩ := hsub
        have hedge := WellAttenuated_edge hw c hc
        have hchild : c.mandate.expiresAt ≤ m.expiresAt := hedge.1.2.2.2.1
        have hrec : e ≤ c.mandate.expiresAt :=
          subtree_expires_le_root c (WellAttenuated_children hw c hc) e hec
        exact Nat.le_trans hrec hchild

def DelegTree.targetList : DelegTree → List String
  | .node m cs => m.target :: cs.flatMap DelegTree.targetList

/-- **Target Sharing**: Every mandate in a well-attenuated tree shares the root target. -/
theorem subtree_target_eq_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ tgt ∈ t.targetList, tgt = t.mandate.target
  | .node m cs, hw => by
      intro tgt ht
      rw [DelegTree.targetList] at ht
      rcases List.mem_cons.mp ht with hroot | hsub
      · exact hroot
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, htc⟩ := hsub
        have hedge := WellAttenuated_edge hw c hc
        have hrec : tgt = c.mandate.target :=
          subtree_target_eq_root c (WellAttenuated_children hw c hc) tgt htc
        rw [hrec]
        exact hedge.1.2.2.2.2.1

/-! ## 6. Forever-Crown Preorder (`mandateNarrows`) -/

/-- Refinement preorder over agent mandates, matching `NEXT-MATHEMATICA.md:62`. -/
def mandateNarrows (m_child m_parent : Mandate) : Prop :=
  attenuates m_child m_parent

theorem mandateNarrows_refl (m : Mandate) : mandateNarrows m m :=
  attenuates_refl m

theorem mandateNarrows_trans {m₁ m₂ m₃ : Mandate}
    (h12 : mandateNarrows m₁ m₂) (h23 : mandateNarrows m₂ m₃) :
    mandateNarrows m₁ m₃ :=
  attenuates_trans h12 h23

end Obend.Vault.Mandate
