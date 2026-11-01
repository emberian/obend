module
/-
# Obend.Vault.Mandate — confined agent capability mandates, attenuation trees, & invocation validation

Absorbs `breadstuffs/Dregg2/Agent/Mandate.lean`, `starbridge-v2/src/powerbox.rs`, and `resident_agent.rs`
onto `Obend/Intention.lean` and `Obend/Run/Fork.lean`.

Addresses Requirement R3 and Milestone 3 Feature 28 (`Mandate`):
1. **Mandate Structure**: Encapsulates grantor, holder, target domain, capability set (`rights`),
   spend/quota limit (`budget`), cell access mask (`cells`), expiration epoch (`expiresAt`), and runtime
   dynamic execution filter (`caveat`).
2. **Strict Attenuation Preorder**: Formulates `attenuates child parent : Prop` and proves reflexivity
   (`attenuates_refl`) and transitivity (`attenuates_trans`). Sub-delegation (`subDelegate`) can only
   attenuate permissions, never amplify (`subDelegate_attenuates`).
3. **Invocation Validation & Soundness**: `checkInvocation` validates agent identity and authority before
   executing turns. `authorizedBy_attenuates` proves that any invocation authorized under an attenuated
   child mandate is provably authorized under the parent mandate.
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

/-! ## 2. Mandate & Invocation Structures -/

/-- A confined agent capability mandate.
    - `grantor`: who delegated the capability
    - `holder`: the agent holding the authority
    - `target`: the target domain / system
    - `rights`: the capability set
    - `budget`: the resource spend quota / ceiling
    - `cells`: cell access mask (authorized cell IDs)
    - `expiresAt`: expiration term / epoch
    - `caveat`: runtime method filter window -/
structure Mandate where
  grantor   : String
  holder    : String
  target    : String
  rights    : List Auth
  budget    : Nat
  cells     : List Nat
  expiresAt : Nat
  caveat    : Caveat

/-- An action invocation attempted by an agent. -/
structure Invocation where
  agent        : String
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

/-- Strict sub-delegation constructor: narrows rights, clamps budget, intersects cell masks,
    bounds expiration, and conjoins caveats. -/
def Mandate.subDelegate (parent : Mandate) (child : String) (reqRights : List Auth)
    (quota : Nat) (mask : List Nat) (term : Nat) (cv : Caveat) : Mandate where
  grantor   := parent.holder
  holder    := child
  target    := parent.target
  rights    := parent.rights.filter (fun a => reqRights.contains a)
  budget    := min parent.budget quota
  cells     := parent.cells.filter (fun c => mask.contains c)
  expiresAt := min parent.expiresAt term
  caveat    := parent.caveat.and cv

/-- **Sub-delegation is Strictly Attenuating**: Creating a child mandate via `subDelegate`
    never amplifies authority. -/
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

/-! ## 4. Invocation Validation & Soundness -/

/-- Check whether an invocation's parameters fall within a mandate's authorization envelope. -/
def authorizedBy (m : Mandate) (inv : Invocation) : Bool :=
  (inv.target == m.target) &&
  (inv.requiredAuth.all m.rights.contains) &&
  (inv.cost ≤ m.budget) &&
  (m.cells.contains inv.cell) &&
  (inv.epoch ≤ m.expiresAt) &&
  (m.caveat.admits inv.method)

/-- Full invocation check: confirms agent identity and parameter authorization. -/
def checkInvocation (m : Mandate) (inv : Invocation) : Bool :=
  (inv.agent == m.holder) && authorizedBy m inv

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
      (∀ c ∈ cs, attenuates c.mandate m ∧ c.mandate.grantor = m.holder) ∧
      (∀ c ∈ cs, c.WellAttenuated)

theorem WellAttenuated_edge {m : Mandate} {cs : List DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) :
    ∀ c ∈ cs, attenuates c.mandate m ∧ c.mandate.grantor = m.holder := by
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
