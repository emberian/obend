module

/-!
# `Obend.SymbolicZk.SkolemChaseCore` — Verified Restricted Skolem Chase, Weak Acyclicity & Core Retraction
Constructive (`0 Classical.choice`, `0 sorryAx`, `0` custom axioms) formalization of existential
tuple-generating dependencies ($\forall \vec{x}.\, B(\vec{x}) \to \exists \vec{y}.\, H(\vec{x}, \vec{y})$)
and the **Restricted (Standard) Skolem Chase**:
1. **Spec Layer**: `Term`/`SkolemTerm`, `Atom Dom`, `PatAtom`, `TgdRule`, `FactSet`, `isSatisfied`.
2. **Exec Engine**: `Array`-backed `stepChaseExec`, `runBoundedChaseExec`, `runBoundedChaseExec_eq_spec`.
3. **Universal Model (`skolemChase_universal_homomorphism`)**: `chase_fixpoint_models_rules` + canonical `evalSkolemHom`.
4. **Weak Acyclicity (`weaklyAcyclic_rank_bound`)**: `checkWeaklyAcyclic` proving `skolemDepth t ≤ maxRankOf rk`.
5. **Core Retraction (`checkRetractionCore_sound`)**: verified retraction `r : M → C` preserving all BCQs/UCQs.
-/

public section
namespace Obend.SymbolicZk.SkolemChaseCore
set_option autoImplicit false

/-! ## §1. Identifiers, Canonical Skolem Terms & Relational Atoms -/
abbrev RelId := Nat
abbrev RuleId := Nat
abbrev ConstId := Nat
abbrev VarId := Nat
inductive Term where
  | const (c : ConstId) : Term
  | skolem (ruleId : RuleId) (existVar : VarId) (frontierTuple : List Term) : Term
  deriving Repr
abbrev SkolemTerm := Term
mutual
  @[expose] def termEq (t₁ t₂ : Term) : Bool :=
    match t₁, t₂ with
    | .const c₁, .const c₂ => c₁ == c₂
    | .skolem r₁ v₁ ts₁, .skolem r₂ v₂ ts₂ => ((r₁ == r₂) && (v₁ == v₂)) && termListEq ts₁ ts₂
    | _, _ => false
    termination_by structural t₁
  @[expose] def termListEq (ts₁ ts₂ : List Term) : Bool :=
    match ts₁, ts₂ with
    | [], [] => true
    | t₁ :: rest₁, t₂ :: rest₂ => termEq t₁ t₂ && termListEq rest₁ rest₂
    | _, _ => false
    termination_by structural ts₁
end
mutual
  theorem termEq_refl (t : Term) : termEq t t = true := by
    cases t with
    | const _ => simp [termEq]
    | skolem _ _ ts => simp [termEq, termListEq_refl ts]
    termination_by structural t
  theorem termListEq_refl (ts : List Term) : termListEq ts ts = true := by
    cases ts with
    | nil => rfl
    | cons t rest => simp [termListEq, termEq_refl t, termListEq_refl rest]
    termination_by structural ts
end
mutual
  theorem termEq_eq_of_true (t₁ t₂ : Term) (h : termEq t₁ t₂ = true) : t₁ = t₂ := by
    cases t₁ <;> cases t₂
    case const.const => simp [termEq] at h; exact congrArg Term.const h
    case const.skolem => simp [termEq] at h
    case skolem.const => simp [termEq] at h
    case skolem.skolem r₁ v₁ ts₁ r₂ v₂ ts₂ =>
      simp [termEq] at h; rcases h with ⟨⟨hr, hv⟩, hts⟩; subst hr; subst hv
      exact congrArg (Term.skolem r₁ v₁) (termListEq_eq_of_true ts₁ ts₂ hts)
    termination_by structural t₁
  theorem termListEq_eq_of_true (ts₁ ts₂ : List Term) (h : termListEq ts₁ ts₂ = true) : ts₁ = ts₂ := by
    cases ts₁ <;> cases ts₂
    case nil.nil => rfl
    case nil.cons => simp [termListEq] at h
    case cons.nil => simp [termListEq] at h
    case cons.cons t₁ r₁ t₂ r₂ =>
      simp [termListEq] at h; rcases h with ⟨ht, hr⟩
      rw [termEq_eq_of_true t₁ t₂ ht, termListEq_eq_of_true r₁ r₂ hr]
    termination_by structural ts₁
end
theorem termEq_iff (t₁ t₂ : Term) : termEq t₁ t₂ = true ↔ t₁ = t₂ :=
  ⟨termEq_eq_of_true t₁ t₂, fun h => h ▸ termEq_refl t₁⟩
instance instBEqTerm : BEq Term := ⟨termEq⟩
instance instLawfulBEqTerm : LawfulBEq Term where
  eq_of_beq {a b} h := termEq_eq_of_true a b h
  rfl {a} := termEq_refl a
instance instDecidableEqTerm : DecidableEq Term := fun t₁ t₂ =>
  if h : termEq t₁ t₂ = true then isTrue (termEq_eq_of_true t₁ t₂ h)
  else isFalse (fun heq => h (heq ▸ termEq_refl t₁))
mutual
  @[expose] def skolemDepth (t : Term) : Nat :=
    match t with | .const _ => 0 | .skolem _ _ args => 1 + skolemDepthList args
    termination_by structural t
  @[expose] def skolemDepthList (ts : List Term) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => let dt := skolemDepth t; let dr := skolemDepthList rest; if dt ≤ dr then dr else dt
    termination_by structural ts
end
def isBaseTerm : Term → Bool | .const _ => true | .skolem _ _ _ => false
def extractConstId : Term → ConstId | .const c => c | .skolem _ _ _ => 0
structure Atom (Dom : Type) where
  rel : RelId
  args : List Dom
  deriving DecidableEq, Repr
instance instBEqAtom {Dom : Type} [DecidableEq Dom] : BEq (Atom Dom) := ⟨fun a b => decide (a = b)⟩
instance instLawfulBEqAtom {Dom : Type} [DecidableEq Dom] : LawfulBEq (Atom Dom) where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
@[expose] def mapAtom {α β : Type} (h : α → β) (a : Atom α) : Atom β :=
  { rel := a.rel, args := a.args.map h }
@[simp] theorem mapAtom_id {α : Type} (a : Atom α) : mapAtom id a = a := by cases a; simp [mapAtom]
theorem mapAtom_comp {α β γ : Type} (g : β → γ) (f : α → β) (a : Atom α) :
    mapAtom g (mapAtom f a) = mapAtom (g ∘ f) a := by cases a; simp [mapAtom, List.map_map]
abbrev FactSet := List (Atom Term)
def isBaseAtom (a : Atom Term) : Bool := a.args.all isBaseTerm
def IsBaseFactSet (I : FactSet) : Bool := I.all isBaseAtom
def embedBaseAtom {DomN : Type} (constOf : ConstId → DomN) (a : Atom Term) : Atom DomN :=
  mapAtom (fun t => constOf (extractConstId t)) a

/-! ## §2. Pattern Atoms, TGD Rules, Substitutions & Constructive Pattern Matching -/
inductive PatTerm where | var (v : VarId) | const (c : ConstId) deriving DecidableEq, Repr, BEq
structure PatAtom where
  rel : RelId
  args : List PatTerm
  deriving DecidableEq, Repr, BEq
structure TgdRule where
  id : RuleId
  frontierVars : List VarId
  existVars : List VarId
  body : List PatAtom
  head : List PatAtom
  deriving DecidableEq, Repr, BEq
def varsOfPatAtom (pa : PatAtom) : List VarId :=
  pa.args.filterMap fun pt => match pt with | .var v => some v | .const _ => none
def varsOfPatAtoms (pas : List PatAtom) : List VarId := pas.flatMap varsOfPatAtom
def nodupVars : List VarId → Bool | [] => true | v :: vs => (!vs.contains v) && nodupVars vs
def WfRule (r : TgdRule) : Bool :=
  let bodyVars := varsOfPatAtoms r.body
  let headVars := varsOfPatAtoms r.head
  nodupVars r.frontierVars && nodupVars r.existVars &&
  r.existVars.all (fun y => !r.frontierVars.contains y) &&
  r.frontierVars.all (fun x => bodyVars.contains x) &&
  headVars.all (fun v => r.frontierVars.contains v || r.existVars.contains v)
def WfRuleSet (rules : List TgdRule) : Bool := rules.all WfRule
abbrev Subst (Dom : Type) := List (VarId × Dom)
def lookupSubst {Dom : Type} (σ : Subst Dom) (v : VarId) : Option Dom :=
  match σ with | [] => none | (k, val) :: rest => if k == v then some val else lookupSubst rest v
def mapSubst {α β : Type} (f : α → β) (σ : Subst α) : Subst β := σ.map fun (k, val) => (k, f val)
def ExtendsSubst {Dom : Type} (σ τ : Subst Dom) : Prop :=
  ∀ v val, lookupSubst σ v = some val → lookupSubst τ v = some val
theorem ExtendsSubst.refl {Dom : Type} (σ : Subst Dom) : ExtendsSubst σ σ := fun _ _ h => h
theorem ExtendsSubst.trans {Dom : Type} {σ₁ σ₂ σ₃ : Subst Dom}
    (h₁₂ : ExtendsSubst σ₁ σ₂) (h₂₃ : ExtendsSubst σ₂ σ₃) : ExtendsSubst σ₁ σ₃ :=
  fun v val h => h₂₃ v val (h₁₂ v val h)
theorem ExtendsSubst.nil {Dom : Type} (τ : Subst Dom) : ExtendsSubst [] τ := fun _ _ h => nomatch h
theorem lookupSubst_mapSubst {α β : Type} (f : α → β) (σ : Subst α) (v : VarId) :
    lookupSubst (mapSubst f σ) v = (lookupSubst σ v).map f := by
  induction σ with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, val⟩; simp only [mapSubst, List.map_cons, lookupSubst]
    cases (k == v); exact ih; rfl
theorem lookupSubst_append_left {Dom : Type} (xs ys : Subst Dom) (v : VarId) (val : Dom)
    (h : lookupSubst xs v = some val) : lookupSubst (xs ++ ys) v = some val := by
  induction xs with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, d⟩; simp only [lookupSubst, List.cons_append] at h ⊢
    cases hk : (k == v) <;> rw [hk] at h; exact ih h; exact h
def evalPatTerm {Dom : Type} (constOf : ConstId → Dom) (σ : Subst Dom) : PatTerm → Option Dom
  | .const c => some (constOf c) | .var v => lookupSubst σ v
def evalPatArgs {Dom : Type} (constOf : ConstId → Dom) (σ : Subst Dom) : List PatTerm → Option (List Dom)
  | [] => some []
  | pt :: pts =>
    match evalPatTerm constOf σ pt, evalPatArgs constOf σ pts with
    | some d, some ds => some (d :: ds) | _, _ => none
def evalPatAtom {Dom : Type} (constOf : ConstId → Dom) (σ : Subst Dom) (pa : PatAtom) : Option (Atom Dom) :=
  match evalPatArgs constOf σ pa.args with | some args => some { rel := pa.rel, args := args } | none => none
def evalPatAtoms {Dom : Type} (constOf : ConstId → Dom) (σ : Subst Dom) : List PatAtom → Option (List (Atom Dom))
  | [] => some []
  | pa :: pas =>
    match evalPatAtom constOf σ pa, evalPatAtoms constOf σ pas with
    | some a, some as => some (a :: as) | _, _ => none
theorem evalPatTerm_ext {Dom : Type} (constOf : ConstId → Dom) {σ τ : Subst Dom}
    (hext : ExtendsSubst σ τ) (pt : PatTerm) (d : Dom) (h : evalPatTerm constOf σ pt = some d) :
    evalPatTerm constOf τ pt = some d := by cases pt with | const _ => exact h | var v => exact hext v d h
theorem evalPatArgs_ext {Dom : Type} (constOf : ConstId → Dom) {σ τ : Subst Dom}
    (hext : ExtendsSubst σ τ) (pts : List PatTerm) (ds : List Dom)
    (h : evalPatArgs constOf σ pts = some ds) : evalPatArgs constOf τ pts = some ds := by
  induction pts generalizing ds with
  | nil => exact h
  | cons pt rest ih =>
    simp only [evalPatArgs] at h ⊢
    cases h₁ : evalPatTerm constOf σ pt <;> simp only [h₁] at h
    · cases h
    · cases h₂ : evalPatArgs constOf σ rest <;> simp only [h₂] at h
      · cases h
      · injection h with hds; subst hds; simp only [evalPatTerm_ext constOf hext pt _ h₁, ih _ h₂]
theorem evalPatAtom_ext {Dom : Type} (constOf : ConstId → Dom) {σ τ : Subst Dom}
    (hext : ExtendsSubst σ τ) (pa : PatAtom) (a : Atom Dom)
    (h : evalPatAtom constOf σ pa = some a) : evalPatAtom constOf τ pa = some a := by
  simp only [evalPatAtom] at h ⊢
  cases hargs : evalPatArgs constOf σ pa.args <;> simp only [hargs] at h
  · cases h
  · injection h with ha; subst ha; simp only [evalPatArgs_ext constOf hext pa.args _ hargs]
theorem evalPatAtoms_ext {Dom : Type} (constOf : ConstId → Dom) {σ τ : Subst Dom}
    (hext : ExtendsSubst σ τ) (pas : List PatAtom) (as : List (Atom Dom))
    (h : evalPatAtoms constOf σ pas = some as) : evalPatAtoms constOf τ pas = some as := by
  induction pas generalizing as with
  | nil => exact h
  | cons pa rest ih =>
    simp only [evalPatAtoms] at h ⊢
    cases h₁ : evalPatAtom constOf σ pa <;> simp only [h₁] at h
    · cases h
    · cases h₂ : evalPatAtoms constOf σ rest <;> simp only [h₂] at h
      · cases h
      · injection h with has; subst has; simp only [evalPatAtom_ext constOf hext pa _ h₁, ih _ h₂]
theorem evalPatTerm_mapSubst {α β : Type} (cα : ConstId → α) (cβ : ConstId → β)
    (f : α → β) (hConst : ∀ c, f (cα c) = cβ c) (σ : Subst α) (pt : PatTerm) :
    evalPatTerm cβ (mapSubst f σ) pt = (evalPatTerm cα σ pt).map f := by
  cases pt with | const c => simp [evalPatTerm, hConst c] | var v => simp [evalPatTerm, lookupSubst_mapSubst]
theorem evalPatArgs_mapSubst {α β : Type} (cα : ConstId → α) (cβ : ConstId → β)
    (f : α → β) (hConst : ∀ c, f (cα c) = cβ c) (σ : Subst α) (pts : List PatTerm) :
    evalPatArgs cβ (mapSubst f σ) pts = (evalPatArgs cα σ pts).map (List.map f) := by
  induction pts with
  | nil => rfl
  | cons pt rest ih =>
    simp only [evalPatArgs, evalPatTerm_mapSubst cα cβ f hConst σ pt, ih]
    cases evalPatTerm cα σ pt <;> cases evalPatArgs cα σ rest <;> rfl
theorem evalPatAtom_mapSubst {α β : Type} (cα : ConstId → α) (cβ : ConstId → β)
    (f : α → β) (hConst : ∀ c, f (cα c) = cβ c) (σ : Subst α) (pa : PatAtom) :
    evalPatAtom cβ (mapSubst f σ) pa = (evalPatAtom cα σ pa).map (mapAtom f) := by
  simp only [evalPatAtom, evalPatArgs_mapSubst cα cβ f hConst σ pa.args]
  cases evalPatArgs cα σ pa.args <;> rfl
theorem evalPatAtoms_mapSubst {α β : Type} (cα : ConstId → α) (cβ : ConstId → β)
    (f : α → β) (hConst : ∀ c, f (cα c) = cβ c) (σ : Subst α) (pas : List PatAtom) :
    evalPatAtoms cβ (mapSubst f σ) pas = (evalPatAtoms cα σ pas).map (List.map (mapAtom f)) := by
  induction pas with
  | nil => rfl
  | cons pa rest ih =>
    simp only [evalPatAtoms, evalPatAtom_mapSubst cα cβ f hConst σ pa, ih]
    cases evalPatAtom cα σ pa <;> cases evalPatAtoms cα σ rest <;> rfl
def matchPatTerm {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) (pt : PatTerm) (d : Dom) : Option (Subst Dom) :=
  match pt with
  | .const c => if constOf c = d then some σ else none
  | .var v =>
    match lookupSubst σ v with
    | some prev => if prev = d then some σ else none
    | none => some ((v, d) :: σ)
def matchPatArgs {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) : List PatTerm → List Dom → Option (Subst Dom)
  | [], [] => some σ
  | pt :: pts, d :: ds =>
    match matchPatTerm constOf σ pt d with | some σ₁ => matchPatArgs constOf σ₁ pts ds | none => none
  | _, _ => none
def matchPatAtom {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) (pa : PatAtom) (a : Atom Dom) : Option (Subst Dom) :=
  if pa.rel = a.rel then matchPatArgs constOf σ pa.args a.args else none
def matchPatAtoms {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) : List PatAtom → List (Atom Dom) → List (Subst Dom)
  | [], _ => [σ]
  | pa :: pas, M =>
    M.flatMap fun a =>
      match matchPatAtom constOf σ pa a with | some σ₁ => matchPatAtoms constOf σ₁ pas M | none => []
theorem matchPatTerm_sound {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ σ' : Subst Dom) (pt : PatTerm) (d : Dom) (hm : matchPatTerm constOf σ pt d = some σ') :
    ExtendsSubst σ σ' ∧ evalPatTerm constOf σ' pt = some d := by
  cases pt with
  | const c =>
    simp only [matchPatTerm] at hm; split at hm
    · rename_i hc; injection hm with hσ; subst hσ; exact ⟨ExtendsSubst.refl σ, congrArg some hc⟩
    · cases hm
  | var v =>
    cases hlook : lookupSubst σ v
    · simp only [matchPatTerm, hlook] at hm; injection hm with hσ; subst hσ
      refine ⟨?_, by simp [evalPatTerm, lookupSubst]⟩
      intro u val hu; simp only [lookupSubst]; cases huv : (v == u)
      · exact hu
      · have hveq : v = u := LawfulBEq.eq_of_beq huv; subst hveq; rw [hlook] at hu; cases hu
    · rename_i prev; simp only [matchPatTerm, hlook] at hm; split at hm
      · rename_i hprev; injection hm with hσ; subst hσ; subst hprev; exact ⟨ExtendsSubst.refl σ, hlook⟩
      · cases hm
theorem matchPatTerm_complete {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ τ : Subst Dom) (hext : ExtendsSubst σ τ) (pt : PatTerm) (d : Dom)
    (hev : evalPatTerm constOf τ pt = some d) :
    ∃ σ', matchPatTerm constOf σ pt d = some σ' ∧ ExtendsSubst σ' τ := by
  cases pt with
  | const c =>
    simp only [evalPatTerm] at hev; injection hev with hc; exact ⟨σ, by simp [matchPatTerm, hc], hext⟩
  | var v =>
    simp only [evalPatTerm] at hev; simp only [matchPatTerm]; cases hlook : lookupSubst σ v
    · refine ⟨(v, d) :: σ, rfl, ?_⟩
      intro u val hu; simp only [lookupSubst] at hu; cases huv : (v == u) <;> rw [huv] at hu
      · exact hext u val hu
      · injection hu with hd; subst hd; have hveq : v = u := LawfulBEq.eq_of_beq huv; subst hveq; exact hev
    · rename_i prev; have hτ := hext v prev hlook; rw [hev] at hτ; injection hτ with hpd; subst hpd
      exact ⟨σ, by simp, hext⟩
theorem matchPatArgs_sound {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ σ' : Subst Dom) (pts : List PatTerm) (ds : List Dom)
    (hm : matchPatArgs constOf σ pts ds = some σ') :
    ExtendsSubst σ σ' ∧ evalPatArgs constOf σ' pts = some ds := by
  induction pts generalizing σ ds with
  | nil =>
    cases ds with
    | nil => injection hm with hσ; subst hσ; exact ⟨ExtendsSubst.refl σ, rfl⟩
    | cons _ _ => cases hm
  | cons pt rest ih =>
    cases ds with
    | nil => cases hm
    | cons d restD =>
      simp only [matchPatArgs] at hm
      cases hm₁ : matchPatTerm constOf σ pt d <;> simp only [hm₁] at hm
      · cases hm
      · rename_i σ₁
        have ⟨hext₁, hev₁⟩ := matchPatTerm_sound constOf σ σ₁ pt d hm₁
        have ⟨hext₂, hev₂⟩ := ih σ₁ restD hm
        exact ⟨ExtendsSubst.trans hext₁ hext₂,
          by simp [evalPatArgs, evalPatTerm_ext constOf hext₂ pt d hev₁, hev₂]⟩
theorem matchPatArgs_complete {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ τ : Subst Dom) (hext : ExtendsSubst σ τ) (pts : List PatTerm) (ds : List Dom)
    (hev : evalPatArgs constOf τ pts = some ds) :
    ∃ σ', matchPatArgs constOf σ pts ds = some σ' ∧ ExtendsSubst σ' τ := by
  induction pts generalizing σ ds with
  | nil => injection hev with hds; subst hds; exact ⟨σ, rfl, hext⟩
  | cons pt rest ih =>
    simp only [evalPatArgs] at hev
    cases h₁ : evalPatTerm constOf τ pt <;> simp only [h₁] at hev
    · cases hev
    · cases h₂ : evalPatArgs constOf τ rest <;> simp only [h₂] at hev
      · cases hev
      · injection hev with hds; subst hds
        obtain ⟨σ₁, hm₁, hext₁⟩ := matchPatTerm_complete constOf σ τ hext pt _ h₁
        obtain ⟨σ', hm₂, hext₂⟩ := ih σ₁ hext₁ _ h₂
        exact ⟨σ', by simp [matchPatArgs, hm₁, hm₂], hext₂⟩
theorem matchPatAtom_sound {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ σ' : Subst Dom) (pa : PatAtom) (a : Atom Dom)
    (hm : matchPatAtom constOf σ pa a = some σ') :
    ExtendsSubst σ σ' ∧ evalPatAtom constOf σ' pa = some a := by
  simp only [matchPatAtom] at hm; split at hm
  · rename_i hrel; have ⟨hext, hev⟩ := matchPatArgs_sound constOf σ σ' pa.args a.args hm
    cases a; simp only at hrel; subst hrel; exact ⟨hext, by simp [evalPatAtom, hev]⟩
  · cases hm
theorem matchPatAtom_complete {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ τ : Subst Dom) (hext : ExtendsSubst σ τ) (pa : PatAtom) (a : Atom Dom)
    (hev : evalPatAtom constOf τ pa = some a) :
    ∃ σ', matchPatAtom constOf σ pa a = some σ' ∧ ExtendsSubst σ' τ := by
  simp only [evalPatAtom] at hev
  cases hargs : evalPatArgs constOf τ pa.args <;> simp only [hargs] at hev
  · cases hev
  · injection hev with ha; subst ha
    obtain ⟨σ', hm, hext'⟩ := matchPatArgs_complete constOf σ τ hext pa.args _ hargs
    exact ⟨σ', by simp [matchPatAtom, hm], hext'⟩
theorem matchPatAtoms_sound {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ σ' : Subst Dom) (pas : List PatAtom) (M : List (Atom Dom))
    (hm : σ' ∈ matchPatAtoms constOf σ pas M) :
    ExtendsSubst σ σ' ∧
      ∃ groundAtoms, evalPatAtoms constOf σ' pas = some groundAtoms ∧ ∀ a ∈ groundAtoms, a ∈ M := by
  induction pas generalizing σ with
  | nil =>
    simp only [matchPatAtoms, List.mem_singleton] at hm; cases hm
    exact ⟨ExtendsSubst.refl σ', [], rfl, (fun _ h => nomatch h)⟩
  | cons pa rest ih =>
    simp only [matchPatAtoms, List.mem_flatMap] at hm; rcases hm with ⟨a, haMem, hmRest⟩
    cases hm₁ : matchPatAtom constOf σ pa a <;> simp only [hm₁] at hmRest
    · cases hmRest
    · rename_i σ₁
      have ⟨hext₁, hev₁⟩ := matchPatAtom_sound constOf σ σ₁ pa a hm₁
      have ⟨hext₂, restAtoms, hev₂, hSub⟩ := ih σ₁ hmRest
      refine ⟨ExtendsSubst.trans hext₁ hext₂, a :: restAtoms,
        by simp [evalPatAtoms, evalPatAtom_ext constOf hext₂ pa a hev₁, hev₂], ?_⟩
      intro x hx; cases hx with | head => exact haMem | tail _ h => exact hSub x h
theorem matchPatAtoms_complete {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ τ : Subst Dom) (hext : ExtendsSubst σ τ) (pas : List PatAtom)
    (groundAtoms M : List (Atom Dom))
    (hev : evalPatAtoms constOf τ pas = some groundAtoms) (hSub : ∀ a ∈ groundAtoms, a ∈ M) :
    ∃ σ' ∈ matchPatAtoms constOf σ pas M, ExtendsSubst σ' τ := by
  induction pas generalizing σ groundAtoms with
  | nil => exact ⟨σ, by simp [matchPatAtoms], hext⟩
  | cons pa rest ih =>
    simp only [evalPatAtoms] at hev
    cases h₁ : evalPatAtom constOf τ pa <;> simp only [h₁] at hev
    · cases hev
    · cases h₂ : evalPatAtoms constOf τ rest <;> simp only [h₂] at hev
      · cases hev
      · injection hev with hga; subst hga; rename_i a restAtoms
        obtain ⟨σ₁, hm₁, hext₁⟩ := matchPatAtom_complete constOf σ τ hext pa a h₁
        obtain ⟨σ', hmRest, hext₂⟩ := ih σ₁ hext₁ restAtoms h₂ (fun b hb => hSub b (.tail _ hb))
        refine ⟨σ', ?_, hext₂⟩; simp only [matchPatAtoms, List.mem_flatMap]
        exact ⟨a, hSub a (.head _), by rw [hm₁]; exact hmRest⟩

/-! ## §3. Frontier Extraction, Restricted `isSatisfied` Check & Spec Chase Engine -/
def extractFrontierTuple {Dom : Type} (frontierVars : List VarId) (σ : Subst Dom) : Option (List Dom) :=
  match frontierVars with
  | [] => some []
  | v :: vs =>
    match lookupSubst σ v, extractFrontierTuple vs σ with
    | some d, some ds => some (d :: ds) | _, _ => none
def frontierSubst {Dom : Type} (frontierVars : List VarId) (σ : Subst Dom) : Subst Dom :=
  match extractFrontierTuple frontierVars σ with | some vals => frontierVars.zip vals | none => []
def buildHeadSubst {Dom : Type} (frontierVars : List VarId) (frontierVals : List Dom)
    (existVars : List VarId) (mkExist : VarId → Dom) : Subst Dom :=
  (frontierVars.zip frontierVals) ++ existVars.map (fun y => (y, mkExist y))
theorem extractFrontierTuple_mapSubst {α β : Type} (f : α → β) (vars : List VarId) (σ : Subst α) :
    extractFrontierTuple vars (mapSubst f σ) = (extractFrontierTuple vars σ).map (List.map f) := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    simp only [extractFrontierTuple, lookupSubst_mapSubst, ih]
    cases lookupSubst σ v <;> cases extractFrontierTuple vs σ <;> rfl
theorem mapSubst_zip {α β : Type} (f : α → β) (vars : List VarId) (vals : List α) :
    mapSubst f (vars.zip vals) = vars.zip (vals.map f) := by
  induction vars generalizing vals with
  | nil => rfl
  | cons v _ ih => cases vals with | nil => rfl | cons d ds => exact congrArg ((v, f d) :: ·) (ih ds)
theorem mapSubst_buildHeadSubst {α β : Type} (f : α → β)
    (frontierVars : List VarId) (frontierVals : List α) (existVars : List VarId) (mkExist : VarId → α) :
    mapSubst f (buildHeadSubst frontierVars frontierVals existVars mkExist) =
      buildHeadSubst frontierVars (frontierVals.map f) existVars (fun y => f (mkExist y)) := by
  simp only [buildHeadSubst, mapSubst, List.map_append]; congr 1
  · exact mapSubst_zip f frontierVars frontierVals
  · rw [List.map_map]; rfl
theorem lookupSubst_zip_of_extract {Dom : Type} (vars : List VarId) (σ : Subst Dom)
    (vals : List Dom) (hex : extractFrontierTuple vars σ = some vals) :
    ∀ x ∈ vars, lookupSubst (vars.zip vals) x = lookupSubst σ x := by
  induction vars generalizing vals with
  | nil => intro _ hx; cases hx
  | cons v vs ih =>
    simp only [extractFrontierTuple] at hex
    cases hv : lookupSubst σ v <;> simp only [hv] at hex
    · cases hex
    · cases hvs : extractFrontierTuple vs σ <;> simp only [hvs] at hex
      · cases hex
      · injection hex with hvals; subst hvals; intro x hx; simp only [List.zip_cons_cons, lookupSubst]
        cases hvx : (v == x)
        · cases hx with | head => simp at hvx | tail _ hxRest => exact ih _ hvs x hxRest
        · have heq : v = x := LawfulBEq.eq_of_beq hvx; subst heq; exact hv.symm
def isSatisfied {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (r : TgdRule) (σ : Subst Dom) (M : List (Atom Dom)) : Bool :=
  !(matchPatAtoms constOf (frontierSubst r.frontierVars σ) r.head M).isEmpty
def insertFactSpec (M : FactSet) (a : Atom Term) : FactSet := if M.contains a then M else M ++ [a]
def insertFactsSpec (M : FactSet) (as : FactSet) : FactSet := as.foldl insertFactSpec M
def instantiateRuleHead (r : TgdRule) (tTuple : List Term) : Option FactSet :=
  evalPatAtoms Term.const
    (buildHeadSubst r.frontierVars tTuple r.existVars (fun y => Term.skolem r.id y tTuple)) r.head
def fireMatchSpec (r : TgdRule) (M : FactSet) (σ : Subst Term) : FactSet :=
  if isSatisfied Term.const r σ M then M
  else match extractFrontierTuple r.frontierVars σ with
    | none => M
    | some tTuple => match instantiateRuleHead r tTuple with
      | none => M | some headAtoms => insertFactsSpec M headAtoms
def fireRuleSpec (M : FactSet) (r : TgdRule) : FactSet :=
  (matchPatAtoms Term.const [] r.body M).foldl (fireMatchSpec r) M
def stepChase (rules : List TgdRule) (M : FactSet) : FactSet := rules.foldl fireRuleSpec M
def ruleSatisfiedSpec (r : TgdRule) (M : FactSet) : Bool :=
  (matchPatAtoms Term.const [] r.body M).all (fun σ => isSatisfied Term.const r σ M)
def allRulesSatisfied (rules : List TgdRule) (M : FactSet) : Bool := rules.all (ruleSatisfiedSpec · M)
def runBoundedChase (rules : List TgdRule) : Nat → FactSet → FactSet
  | 0, M => M
  | fuel + 1, M => if allRulesSatisfied rules M then M else runBoundedChase rules fuel (stepChase rules M)

/-! ## §4. Fast `Array`-Backed `Exec` Engine & `Spec ↔ Exec` Equivalence -/
def matchPatAtomsExec {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) : List PatAtom → Array (Atom Dom) → Array (Subst Dom)
  | [], _ => #[σ]
  | pa :: pas, M =>
    M.foldl (fun acc a =>
      match matchPatAtom constOf σ pa a with
      | some σ₁ => acc ++ matchPatAtomsExec constOf σ₁ pas M | none => acc) #[]
def isSatisfiedExec (r : TgdRule) (σ : Subst Term) (M : Array (Atom Term)) : Bool :=
  !(matchPatAtomsExec Term.const (frontierSubst r.frontierVars σ) r.head M).isEmpty
def insertFactExec (M : Array (Atom Term)) (a : Atom Term) : Array (Atom Term) :=
  if M.contains a then M else M.push a
def insertFactsExec (M : Array (Atom Term)) (as : FactSet) : Array (Atom Term) := as.foldl insertFactExec M
def fireMatchExec (r : TgdRule) (M : Array (Atom Term)) (σ : Subst Term) : Array (Atom Term) :=
  if isSatisfiedExec r σ M then M
  else match extractFrontierTuple r.frontierVars σ with
    | none => M
    | some tTuple => match instantiateRuleHead r tTuple with
      | none => M | some headAtoms => insertFactsExec M headAtoms
def fireRuleExec (M : Array (Atom Term)) (r : TgdRule) : Array (Atom Term) :=
  (matchPatAtomsExec Term.const [] r.body M).foldl (fireMatchExec r) M
def stepChaseExec (rules : Array TgdRule) (M : Array (Atom Term)) : Array (Atom Term) :=
  rules.foldl fireRuleExec M
def allRulesSatisfiedExec (rules : Array TgdRule) (M : Array (Atom Term)) : Bool :=
  rules.all fun r => (matchPatAtomsExec Term.const [] r.body M).all fun σ => isSatisfiedExec r σ M
def runBoundedChaseExec (rules : Array TgdRule) : Nat → Array (Atom Term) → Array (Atom Term)
  | 0, M => M
  | fuel + 1, M =>
    if allRulesSatisfiedExec rules M then M else runBoundedChaseExec rules fuel (stepChaseExec rules M)
private theorem foldl_append_eq_flatMap {α β : Type} (xs : List α) (f : α → Array β) (init : Array β) :
    (xs.foldl (fun acc x => acc ++ f x) init).toList = init.toList ++ xs.flatMap (fun x => (f x).toList) := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]; rw [ih (init ++ f x), Array.toList_append, List.append_assoc]
theorem matchPatAtomsExec_eq_spec {Dom : Type} [DecidableEq Dom] (constOf : ConstId → Dom)
    (σ : Subst Dom) (pas : List PatAtom) (M : Array (Atom Dom)) :
    (matchPatAtomsExec constOf σ pas M).toList = matchPatAtoms constOf σ pas M.toList := by
  induction pas generalizing σ with
  | nil => rfl
  | cons pa rest ih =>
    simp only [matchPatAtomsExec, matchPatAtoms, ← Array.foldl_toList]
    let stepFn : Atom Dom → Array (Subst Dom) := fun a =>
      match matchPatAtom constOf σ pa a with | some σ₁ => matchPatAtomsExec constOf σ₁ rest M | none => #[]
    have hcongr :
        M.toList.foldl (fun acc a =>
          match matchPatAtom constOf σ pa a with
          | some σ₁ => acc ++ matchPatAtomsExec constOf σ₁ rest M | none => acc) #[] =
        M.toList.foldl (fun acc a => acc ++ stepFn a) #[] := by
      congr 1; funext acc a; simp only [stepFn]; cases matchPatAtom constOf σ pa a <;> simp
    rw [hcongr, foldl_append_eq_flatMap]; simp only [List.nil_append, stepFn]; congr 1; funext a
    cases matchPatAtom constOf σ pa a with | none => rfl | some σ₁ => exact ih σ₁
theorem isSatisfiedExec_eq_spec (r : TgdRule) (σ : Subst Term) (M : Array (Atom Term)) :
    isSatisfiedExec r σ M = isSatisfied Term.const r σ M.toList := by
  simp only [isSatisfiedExec, isSatisfied]; rw [← Array.isEmpty_toList, matchPatAtomsExec_eq_spec]
theorem insertFactExec_eq_spec (M : Array (Atom Term)) (a : Atom Term) :
    (insertFactExec M a).toList = insertFactSpec M.toList a := by
  have hContains : M.contains a = M.toList.contains a := by
    cases h₁ : M.contains a <;> cases h₂ : M.toList.contains a
    · rfl
    · exfalso
      have hmA := Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp (List.contains_iff_mem.mp h₂))
      rw [h₁] at hmA; cases hmA
    · exfalso
      have hm := List.contains_iff_mem.mpr (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp h₁))
      rw [h₂] at hm; cases hm
    · rfl
  simp only [insertFactExec, insertFactSpec, hContains]; cases M.toList.contains a <;> simp
theorem insertFactsExec_eq_spec (M : Array (Atom Term)) (as : FactSet) :
    (insertFactsExec M as).toList = insertFactsSpec M.toList as := by
  unfold insertFactsExec insertFactsSpec
  induction as generalizing M with
  | nil => rfl
  | cons a _ ih => simp only [List.foldl_cons]; rw [ih (insertFactExec M a), insertFactExec_eq_spec]
theorem fireMatchExec_eq_spec (r : TgdRule) (M : Array (Atom Term)) (σ : Subst Term) :
    (fireMatchExec r M σ).toList = fireMatchSpec r M.toList σ := by
  simp only [fireMatchExec, fireMatchSpec, isSatisfiedExec_eq_spec]
  cases isSatisfied Term.const r σ M.toList
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases extractFrontierTuple r.frontierVars σ <;> simp only
    rename_i tTuple; cases instantiateRuleHead r tTuple <;> simp only
    exact insertFactsExec_eq_spec M _
  · rfl
private theorem foldl_fireMatch_eq (r : TgdRule) (σs : List (Subst Term)) (M : Array (Atom Term)) :
    (σs.foldl (fireMatchExec r) M).toList = σs.foldl (fireMatchSpec r) M.toList := by
  induction σs generalizing M with
  | nil => rfl
  | cons σ _ ih => simp only [List.foldl_cons]; rw [ih (fireMatchExec r M σ), fireMatchExec_eq_spec]
theorem fireRuleExec_eq_spec (M : Array (Atom Term)) (r : TgdRule) :
    (fireRuleExec M r).toList = fireRuleSpec M.toList r := by
  simp only [fireRuleExec, fireRuleSpec, ← Array.foldl_toList, matchPatAtomsExec_eq_spec]
  exact foldl_fireMatch_eq r _ M
private theorem foldl_fireRule_eq (rs : List TgdRule) (M : Array (Atom Term)) :
    (rs.foldl fireRuleExec M).toList = rs.foldl fireRuleSpec M.toList := by
  induction rs generalizing M with
  | nil => rfl
  | cons r _ ih => simp only [List.foldl_cons]; rw [ih (fireRuleExec M r), fireRuleExec_eq_spec]
theorem stepChaseExec_eq_spec (rules : Array TgdRule) (M : Array (Atom Term)) :
    (stepChaseExec rules M).toList = stepChase rules.toList M.toList := by
  simp only [stepChaseExec, stepChase, ← Array.foldl_toList]; exact foldl_fireRule_eq rules.toList M
theorem allRulesSatisfiedExec_eq_spec (rules : Array TgdRule) (M : Array (Atom Term)) :
    allRulesSatisfiedExec rules M = allRulesSatisfied rules.toList M.toList := by
  simp only [allRulesSatisfiedExec, allRulesSatisfied, ruleSatisfiedSpec, ← Array.all_toList]
  congr 1; funext r; rw [matchPatAtomsExec_eq_spec]; congr 1; funext σ; exact isSatisfiedExec_eq_spec r σ M
theorem runBoundedChaseExec_eq_spec (rules : Array TgdRule) (fuel : Nat) (M : Array (Atom Term)) :
    (runBoundedChaseExec rules fuel M).toList = runBoundedChase rules.toList fuel M.toList := by
  induction fuel generalizing M with
  | zero => rfl
  | succ _ ih =>
    simp only [runBoundedChaseExec, runBoundedChase, allRulesSatisfiedExec_eq_spec]
    cases allRulesSatisfied rules.toList M.toList
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [ih (stepChaseExec rules M), stepChaseExec_eq_spec]
    · rfl

/-! ## §5. Chase Invariant Combinator, Fixpoint Soundness & Universal Homomorphism -/
private theorem mem_insertFactSpec (M : FactSet) (a x : Atom Term) :
    x ∈ insertFactSpec M a ↔ x ∈ M ∨ x = a := by
  simp only [insertFactSpec]; cases h : M.contains a
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
  · simp only [↓reduceIte]; have haMem := List.contains_iff_mem.mp h
    exact ⟨Or.inl, fun hOr => hOr.elim id (fun hxa => hxa ▸ haMem)⟩
private theorem subset_insertFactsSpec (M as : FactSet) {x : Atom Term} (hx : x ∈ M) :
    x ∈ insertFactsSpec M as := by
  unfold insertFactsSpec; induction as generalizing M with
  | nil => exact hx
  | cons b₀ _ ih => exact ih (insertFactSpec M b₀) ((mem_insertFactSpec M b₀ x).mpr (Or.inl hx))
private theorem forall_insertFactsSpec {P : Atom Term → Prop} (M as : FactSet)
    (hM : ∀ x ∈ M, P x) (has : ∀ a ∈ as, P a) : ∀ x ∈ insertFactsSpec M as, P x := by
  unfold insertFactsSpec; induction as generalizing M with
  | nil => exact hM
  | cons b₀ _ ih =>
    apply ih (insertFactSpec M b₀)
    · intro x hx; rcases (mem_insertFactSpec M b₀ x).mp hx with hxM | hEq
      · exact hM x hxM
      · rw [hEq]; exact has b₀ (.head _)
    · intro b hb; exact has b (.tail _ hb)
theorem subset_stepChase (rules : List TgdRule) (M : FactSet) : ∀ x ∈ M, x ∈ stepChase rules M := by
  have hMatch : ∀ (r : TgdRule) (σs : List (Subst Term)) (acc : FactSet),
      ∀ x ∈ acc, x ∈ σs.foldl (fireMatchSpec r) acc := by
    intro r σs; induction σs with
    | nil => intro acc x hx; exact hx
    | cons σ _ ih =>
      intro acc x hx; apply ih; simp only [fireMatchSpec]; split
      · exact hx
      · cases extractFrontierTuple r.frontierVars σ <;> simp only
        · exact hx
        · rename_i tTuple; cases instantiateRuleHead r tTuple <;> simp only
          · exact hx
          · exact subset_insertFactsSpec acc _ hx
  have hRules : ∀ (rs : List TgdRule) (acc : FactSet), ∀ x ∈ acc, x ∈ rs.foldl fireRuleSpec acc := by
    intro rs; induction rs with
    | nil => intro acc x hx; exact hx
    | cons r _ ih => intro acc x hx; exact ih _ x (hMatch r _ acc x hx)
  exact hRules rules M
theorem subset_runBoundedChase (rules : List TgdRule) (fuel : Nat) (I : FactSet) :
    ∀ x ∈ I, x ∈ runBoundedChase rules fuel I := by
  induction fuel generalizing I with
  | zero => intro x hx; exact hx
  | succ _ ih =>
    intro x hx; simp only [runBoundedChase]; split
    · exact hx
    · exact ih (stepChase rules I) x (subset_stepChase rules I x hx)
private theorem runBoundedChase_invariant (P : Atom Term → Prop) (rules : List TgdRule)
    (hHead : ∀ r ∈ rules, ∀ (σ : Subst Term) (bodyAtoms tTuple_atoms : FactSet) (tTuple : List Term),
      evalPatAtoms Term.const σ r.body = some bodyAtoms → (∀ b ∈ bodyAtoms, P b) →
      extractFrontierTuple r.frontierVars σ = some tTuple →
      instantiateRuleHead r tTuple = some tTuple_atoms → ∀ a ∈ tTuple_atoms, P a)
    (fuel : Nat) (I : FactSet) (hI : ∀ a ∈ I, P a) : ∀ a ∈ runBoundedChase rules fuel I, P a := by
  have hStep : ∀ (M : FactSet), (∀ a ∈ M, P a) → ∀ a ∈ stepChase rules M, P a := by
    intro M hM
    have hFireMatch : ∀ r ∈ rules, ∀ (σs : List (Subst Term)) (acc : FactSet),
        (∀ x ∈ σs, x ∈ matchPatAtoms Term.const [] r.body acc ∨
          ∃ bodyAtoms, evalPatAtoms Term.const x r.body = some bodyAtoms ∧ ∀ b ∈ bodyAtoms, P b) →
        (∀ a ∈ acc, P a) → ∀ a ∈ σs.foldl (fireMatchSpec r) acc, P a := by
      intro r hrMem σs; induction σs with
      | nil => intro acc _ hAcc a ha; exact hAcc a ha
      | cons σ rest ih =>
        intro acc hσs hAcc
        have hNext : ∀ a ∈ fireMatchSpec r acc σ, P a := by
          simp only [fireMatchSpec]; split
          · exact hAcc
          · cases hExt : extractFrontierTuple r.frontierVars σ <;> simp only
            · exact hAcc
            · rename_i tTuple; cases hInst : instantiateRuleHead r tTuple <;> simp only
              · exact hAcc
              · rename_i headAtoms; apply forall_insertFactsSpec acc headAtoms hAcc
                rcases hσs σ (.head _) with hMemMatch | ⟨bAtoms, hevB, hbP⟩
                · obtain ⟨_, bAtoms, hevB, hbSub⟩ := matchPatAtoms_sound Term.const [] σ r.body acc hMemMatch
                  exact hHead r hrMem σ bAtoms headAtoms tTuple hevB (fun b hb => hAcc b (hbSub b hb)) hExt hInst
                · exact hHead r hrMem σ bAtoms headAtoms tTuple hevB hbP hExt hInst
        apply ih (fireMatchSpec r acc σ) _ hNext
        intro x hxRest; rcases hσs x (.tail _ hxRest) with hMemMatch | hDirect
        · obtain ⟨_, bAtoms, hevB, hbSub⟩ := matchPatAtoms_sound Term.const [] x r.body acc hMemMatch
          exact Or.inr ⟨bAtoms, hevB, fun b hb => hAcc b (hbSub b hb)⟩
        · exact Or.inr hDirect
    have hFoldRules : ∀ (rs : List TgdRule) (acc : FactSet),
        (∀ r ∈ rs, r ∈ rules) → (∀ a ∈ acc, P a) → ∀ a ∈ rs.foldl fireRuleSpec acc, P a := by
      intro rs; induction rs with
      | nil => intro acc _ hAcc; exact hAcc
      | cons r _ ih =>
        intro acc hrsSub hAcc
        exact ih (fireRuleSpec acc r) (fun r' hr' => hrsSub r' (.tail _ hr'))
          (hFireMatch r (hrsSub r (.head _)) _ acc (fun x hx => Or.inl hx) hAcc)
    exact hFoldRules rules M (fun r hr => hr) hM
  induction fuel generalizing I with
  | zero => exact hI
  | succ _ ih => simp only [runBoundedChase]; split; exact hI; exact ih (stepChase rules I) (hStep I hI)
def ModelsRule {Dom : Type} (constOf : ConstId → Dom) (r : TgdRule) (M : List (Atom Dom)) : Prop :=
  ∀ (τ : Subst Dom) (bodyAtoms : List (Atom Dom)),
    evalPatAtoms constOf τ r.body = some bodyAtoms → (∀ a ∈ bodyAtoms, a ∈ M) →
    ∃ (τ' : Subst Dom) (headAtoms : List (Atom Dom)),
      (∀ x ∈ r.frontierVars, lookupSubst τ' x = lookupSubst τ x) ∧
      evalPatAtoms constOf τ' r.head = some headAtoms ∧ (∀ a ∈ headAtoms, a ∈ M)
def ModelsRules {Dom : Type} (constOf : ConstId → Dom) (rules : List TgdRule) (M : List (Atom Dom)) : Prop :=
  ∀ r ∈ rules, ModelsRule constOf r M
private theorem bound_of_mem_varsOfPatArgs {Dom : Type} (constOf : ConstId → Dom)
    (σ : Subst Dom) (pts : List PatTerm) (ds : List Dom) (v : VarId)
    (hv : v ∈ pts.filterMap (fun pt => match pt with | .var u => some u | .const _ => none))
    (hargs : evalPatArgs constOf σ pts = some ds) : ∃ d, lookupSubst σ v = some d := by
  induction pts generalizing ds with
  | nil => cases hv
  | cons pt rest ih =>
    simp only [evalPatArgs] at hargs
    cases h₁ : evalPatTerm constOf σ pt <;> simp only [h₁] at hargs
    · cases hargs
    · cases h₂ : evalPatArgs constOf σ rest <;> simp only [h₂] at hargs
      · cases hargs
      · cases pt with
        | const _ => simp only [List.filterMap_cons] at hv; exact ih _ hv h₂
        | var _ =>
          simp only [List.filterMap_cons, List.mem_cons] at hv
          rcases hv with rfl | hvRest; exact ⟨_, h₁⟩; exact ih _ hvRest h₂
private theorem bound_of_mem_varsOfPatAtoms {Dom : Type} (constOf : ConstId → Dom)
    (σ : Subst Dom) (pas : List PatAtom) (as : List (Atom Dom)) (v : VarId)
    (hv : v ∈ varsOfPatAtoms pas) (hev : evalPatAtoms constOf σ pas = some as) :
    ∃ d, lookupSubst σ v = some d := by
  simp only [varsOfPatAtoms, List.mem_flatMap] at hv; rcases hv with ⟨targetPa, hpaMem, hvPa⟩
  induction pas generalizing as with
  | nil => cases hpaMem
  | cons p₀ rest ih =>
    simp only [evalPatAtoms] at hev
    cases h₁ : evalPatAtom constOf σ p₀ <;> simp only [h₁] at hev
    · cases hev
    · cases h₂ : evalPatAtoms constOf σ rest <;> simp only [h₂] at hev
      · cases hev
      · cases hpaMem with
        | head =>
          simp only [evalPatAtom] at h₁
          cases hargs : evalPatArgs constOf σ targetPa.args <;> simp only [hargs] at h₁
          · cases h₁
          · exact bound_of_mem_varsOfPatArgs constOf σ targetPa.args _ v hvPa hargs
        | tail _ hMemRest => exact ih _ h₂ hMemRest
private theorem extractFrontierTuple_some_of_all_bound {Dom : Type} (vars : List VarId) (σ : Subst Dom)
    (hBound : ∀ x ∈ vars, ∃ d, lookupSubst σ x = some d) : ∃ vals, extractFrontierTuple vars σ = some vals := by
  induction vars with
  | nil => exact ⟨[], rfl⟩
  | cons v _ ih =>
    obtain ⟨d, hd⟩ := hBound v (.head _)
    obtain ⟨ds, hds⟩ := ih (fun x hx => hBound x (.tail _ hx))
    exact ⟨d :: ds, by simp [extractFrontierTuple, hd, hds]⟩
theorem chase_fixpoint_models_rules (rules : List TgdRule) (fuel : Nat) (I : FactSet)
    (hWf : WfRuleSet rules = true)
    (hSat : allRulesSatisfied rules (runBoundedChase rules fuel I) = true) :
    (∀ a ∈ I, a ∈ runBoundedChase rules fuel I) ∧
      ModelsRules Term.const rules (runBoundedChase rules fuel I) := by
  let M := runBoundedChase rules fuel I
  refine ⟨subset_runBoundedChase rules fuel I, ?_⟩
  intro r hrMem τ bodyAtoms hevBody hBodySub
  have hWfRule : WfRule r = true := by simp only [WfRuleSet, List.all_eq_true] at hWf; exact hWf r hrMem
  have hFrontInBody : ∀ x ∈ r.frontierVars, x ∈ varsOfPatAtoms r.body := by
    simp only [WfRule, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hWfRule; exact hWfRule.1.2
  obtain ⟨σ, hσMem, hextστ⟩ :=
    matchPatAtoms_complete Term.const [] τ (ExtendsSubst.nil τ) r.body bodyAtoms M hevBody hBodySub
  obtain ⟨_, σBodyAtoms, hevσBody, _⟩ := matchPatAtoms_sound Term.const [] σ r.body M hσMem
  have hσBound : ∀ x ∈ r.frontierVars, ∃ d, lookupSubst σ x = some d :=
    fun x hx => bound_of_mem_varsOfPatAtoms Term.const σ r.body σBodyAtoms x (hFrontInBody x hx) hevσBody
  obtain ⟨tTuple, hExtract⟩ := extractFrontierTuple_some_of_all_bound r.frontierVars σ hσBound
  have hRuleSat : ruleSatisfiedSpec r M = true := by
    simp only [allRulesSatisfied, List.all_eq_true] at hSat; exact hSat r hrMem
  have hIsSat : isSatisfied Term.const r σ M = true := by
    simp only [ruleSatisfiedSpec, List.all_eq_true] at hRuleSat; exact hRuleSat σ hσMem
  cases hHeadMatches : matchPatAtoms Term.const (frontierSubst r.frontierVars σ) r.head M with
  | nil => simp [isSatisfied, hHeadMatches] at hIsSat
  | cons τ' _ =>
    have hτ'Mem : τ' ∈ matchPatAtoms Term.const (frontierSubst r.frontierVars σ) r.head M := by
      rw [hHeadMatches]; exact .head _
    obtain ⟨hextFront, headAtoms, hevHead, hHeadSub⟩ :=
      matchPatAtoms_sound Term.const (frontierSubst r.frontierVars σ) τ' r.head M hτ'Mem
    refine ⟨τ', headAtoms, ?_, hevHead, hHeadSub⟩; intro x hx
    obtain ⟨d, hdσ⟩ := hσBound x hx
    have hZipLookup : lookupSubst (frontierSubst r.frontierVars σ) x = some d := by
      simp only [frontierSubst, hExtract]
      rw [lookupSubst_zip_of_extract r.frontierVars σ tTuple hExtract x hx]; exact hdσ
    rw [hextFront x d hZipLookup, hextστ x d hdσ]
def WitnessSatisfiesRules {DomN : Type} (constOf : ConstId → DomN) (rules : List TgdRule) (N : List (Atom DomN))
    (chooseWitness : RuleId → List DomN → VarId → DomN) : Prop :=
  ∀ r ∈ rules, ∀ (σN : Subst DomN) (bodyAtomsN : List (Atom DomN)),
    evalPatAtoms constOf σN r.body = some bodyAtomsN → (∀ a ∈ bodyAtomsN, a ∈ N) →
    ∀ dTuple : List DomN, extractFrontierTuple r.frontierVars σN = some dTuple →
      ∃ headAtomsN : List (Atom DomN),
        evalPatAtoms constOf
          (buildHeadSubst r.frontierVars dTuple r.existVars (chooseWitness r.id dTuple))
          r.head = some headAtomsN ∧ (∀ a ∈ headAtomsN, a ∈ N)
mutual
  @[expose] def evalSkolemHom {DomN : Type} (constOf : ConstId → DomN)
      (chooseWitness : RuleId → List DomN → VarId → DomN) (t : SkolemTerm) : DomN :=
    match t with
    | .const c => constOf c
    | .skolem ruleId existVar frontierTuple =>
        chooseWitness ruleId (evalSkolemHomList constOf chooseWitness frontierTuple) existVar
    termination_by structural t
  @[expose] def evalSkolemHomList {DomN : Type} (constOf : ConstId → DomN)
      (chooseWitness : RuleId → List DomN → VarId → DomN) (ts : List SkolemTerm) : List DomN :=
    match ts with
    | [] => []
    | t :: rest => evalSkolemHom constOf chooseWitness t :: evalSkolemHomList constOf chooseWitness rest
    termination_by structural ts
end
private theorem evalSkolemHomList_eq_map {DomN : Type} (constOf : ConstId → DomN)
    (chooseWitness : RuleId → List DomN → VarId → DomN) (ts : List Term) :
    evalSkolemHomList constOf chooseWitness ts = ts.map (evalSkolemHom constOf chooseWitness) := by
  induction ts with | nil => rfl | cons _ _ ih => simp [evalSkolemHomList, ih]
private theorem mapAtom_evalSkolemHom_eq_embedBase {DomN : Type}
    (constOf : ConstId → DomN) (chooseWitness : RuleId → List DomN → VarId → DomN)
    (a : Atom Term) (hBase : isBaseAtom a = true) :
    mapAtom (evalSkolemHom constOf chooseWitness) a = embedBaseAtom constOf a := by
  rcases a with ⟨rel, args⟩; simp only [isBaseAtom, List.all_eq_true] at hBase
  simp only [embedBaseAtom, mapAtom, Atom.mk.injEq, true_and]
  induction args with
  | nil => rfl
  | cons t _ ih =>
    have ht := hBase t (.head _)
    cases t with
    | skolem _ _ _ => cases ht
    | const c => exact congrArg (constOf c :: ·) (ih (fun x hx => hBase x (.tail _ hx)))
theorem runBoundedChase_homomorphism {DomN : Type} (constOf : ConstId → DomN)
    (rules : List TgdRule) (fuel : Nat) (I : FactSet) (N : List (Atom DomN))
    (chooseWitness : RuleId → List DomN → VarId → DomN)
    (hBaseI : IsBaseFactSet I = true) (hIinN : ∀ a ∈ I, embedBaseAtom constOf a ∈ N)
    (hNWit : WitnessSatisfiesRules constOf rules N chooseWitness) :
    ∀ a ∈ runBoundedChase rules fuel I, mapAtom (evalSkolemHom constOf chooseWitness) a ∈ N := by
  let h := evalSkolemHom constOf chooseWitness
  have hConst : ∀ c, h (.const c) = constOf c := fun _ => rfl
  refine runBoundedChase_invariant (fun a => mapAtom h a ∈ N) rules ?_ fuel I ?_
  · intro r hrMem σ bodyAtoms headAtoms tTuple hevBody hBodyInN hExt hInst
    have hevBodyN : evalPatAtoms constOf (mapSubst h σ) r.body = some (bodyAtoms.map (mapAtom h)) := by
      rw [evalPatAtoms_mapSubst Term.const constOf h hConst σ r.body, hevBody]; rfl
    have hBodySubN : ∀ b ∈ bodyAtoms.map (mapAtom h), b ∈ N := by
      intro b hb; rcases List.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩; exact hBodyInN b₀ hb₀
    have hExtN : extractFrontierTuple r.frontierVars (mapSubst h σ) = some (tTuple.map h) := by
      rw [extractFrontierTuple_mapSubst h r.frontierVars σ, hExt]; rfl
    obtain ⟨headAtomsN, hevHeadN, hHeadInN⟩ :=
      hNWit r hrMem (mapSubst h σ) (bodyAtoms.map (mapAtom h)) hevBodyN hBodySubN (tTuple.map h) hExtN
    let σSkolem := buildHeadSubst r.frontierVars tTuple r.existVars (fun y => Term.skolem r.id y tTuple)
    have hMapSkolem : mapSubst h σSkolem =
        buildHeadSubst r.frontierVars (tTuple.map h) r.existVars (chooseWitness r.id (tTuple.map h)) := by
      rw [mapSubst_buildHeadSubst h r.frontierVars tTuple r.existVars]
      congr 1; funext y; simp [h, evalSkolemHom, evalSkolemHomList_eq_map]
    have hevHeadMapped :
        evalPatAtoms constOf (mapSubst h σSkolem) r.head = some (headAtoms.map (mapAtom h)) := by
      rw [evalPatAtoms_mapSubst Term.const constOf h hConst σSkolem r.head]
      simp only [instantiateRuleHead] at hInst; rw [hInst]; rfl
    rw [hMapSkolem] at hevHeadMapped; rw [hevHeadMapped] at hevHeadN
    injection hevHeadN with hEqHeads; subst hEqHeads
    intro a ha; exact hHeadInN (mapAtom h a) (List.mem_map_of_mem ha)
  · intro a ha; simp only [IsBaseFactSet, List.all_eq_true] at hBaseI
    rw [mapAtom_evalSkolemHom_eq_embedBase constOf chooseWitness a (hBaseI a ha)]; exact hIinN a ha
theorem skolemChase_universal_homomorphism {DomN : Type} (constOf : ConstId → DomN)
    (rules : List TgdRule) (fuel : Nat) (I : FactSet) (N : List (Atom DomN))
    (chooseWitness : RuleId → List DomN → VarId → DomN)
    (hWf : WfRuleSet rules = true) (hBaseI : IsBaseFactSet I = true)
    (hSat : allRulesSatisfied rules (runBoundedChase rules fuel I) = true)
    (hIinN : ∀ a ∈ I, embedBaseAtom constOf a ∈ N)
    (hNWit : WitnessSatisfiesRules constOf rules N chooseWitness) :
    let M := runBoundedChase rules fuel I
    (∀ a ∈ I, a ∈ M) ∧ ModelsRules Term.const rules M ∧
    ∃ h : SkolemTerm → DomN, (∀ c : ConstId, h (.const c) = constOf c) ∧ (∀ a ∈ M, mapAtom h a ∈ N) := by
  obtain ⟨hSub, hMod⟩ := chase_fixpoint_models_rules rules fuel I hWf hSat
  exact ⟨hSub, hMod, evalSkolemHom constOf chooseWitness, fun _ => rfl,
    runBoundedChase_homomorphism constOf rules fuel I N chooseWitness hBaseI hIinN hNWit⟩

/-! ## §6. Weak Acyclicity Position Ranking & Skolem Depth Bound (`weaklyAcyclic_rank_bound`) -/
structure RelPos where
  rel : RelId
  pos : Nat
  deriving DecidableEq, Repr, BEq
abbrev PosRankMap := List (RelPos × Nat)
def rankOf (rk : PosRankMap) (p : RelPos) : Nat :=
  match rk with | [] => 0 | (q, val) :: rest => if q == p then val else rankOf rest p
def maxRankOf (rk : PosRankMap) : Nat := rk.foldl (fun acc kv => if acc ≤ kv.2 then kv.2 else acc) 0
private theorem foldl_max_ge_init (rk : PosRankMap) (init : Nat) :
    init ≤ rk.foldl (fun acc kv => if acc ≤ kv.2 then kv.2 else acc) init := by
  induction rk generalizing init with
  | nil => exact Nat.le_refl init
  | cons kv rest ih =>
    simp only [List.foldl_cons]
    if hle : init ≤ kv.2 then simp only [hle, ↓reduceIte]; exact Nat.le_trans hle (ih kv.2)
    else simp only [hle, ↓reduceIte]; exact ih init
theorem rankOf_le_maxRankOf (rk : PosRankMap) (p : RelPos) : rankOf rk p ≤ maxRankOf rk := by
  have hGen : ∀ (entries : PosRankMap) (init : Nat),
      rankOf entries p ≤ entries.foldl (fun acc kv => if acc ≤ kv.2 then kv.2 else acc) init := by
    intro entries; induction entries with
    | nil => intro _; simp [rankOf]
    | cons kv rest ih =>
      intro init; rcases kv with ⟨q, val⟩; simp only [rankOf, List.foldl_cons]
      cases (q == p)
      · exact ih _
      · if hle : init ≤ val then simp only [hle, ↓reduceIte]; exact foldl_max_ge_init rest val
        else
          simp only [hle, ↓reduceIte]
          exact Nat.le_trans (Nat.le_of_lt (Nat.gt_of_not_le hle)) (foldl_max_ge_init rest init)
  exact hGen rk 0
def enumFrom {α : Type} (startIdx : Nat) : List α → List (Nat × α)
  | [] => [] | x :: xs => (startIdx, x) :: enumFrom (startIdx + 1) xs
def varPositionsIn (v : VarId) (pas : List PatAtom) : List RelPos :=
  pas.flatMap fun pa =>
    (enumFrom 0 pa.args).filterMap fun (idx, pt) =>
      if decide (pt = .var v) then some { rel := pa.rel, pos := idx } else none
def checkWeaklyAcyclicRule (rk : PosRankMap) (r : TgdRule) : Bool :=
  r.frontierVars.all (fun x => !(varPositionsIn x r.body).isEmpty) &&
  r.head.all fun pa =>
    (enumFrom 0 pa.args).all fun (j, pt) =>
      let headRank := rankOf rk { rel := pa.rel, pos := j }
      match pt with
      | .const _ => true
      | .var v =>
        if r.frontierVars.contains v then
          (varPositionsIn v r.body).all fun pB => decide (rankOf rk pB ≤ headRank)
        else if r.existVars.contains v then
          decide (1 ≤ headRank) &&
          r.frontierVars.all fun x => (varPositionsIn x r.body).all fun pB => decide (rankOf rk pB + 1 ≤ headRank)
        else false
def checkWeaklyAcyclic (rk : PosRankMap) (rules : List TgdRule) : Bool := rules.all (checkWeaklyAcyclicRule rk)
def AtomPosRanked (rk : PosRankMap) (a : Atom Term) : Prop :=
  ∀ idx t, (idx, t) ∈ enumFrom 0 a.args → skolemDepth t ≤ rankOf rk { rel := a.rel, pos := idx }
private theorem mem_enumFrom_of_mem {α : Type} (xs : List α) (startIdx : Nat) (x : α)
    (hx : x ∈ xs) : ∃ idx, (idx, x) ∈ enumFrom startIdx xs := by
  induction xs generalizing startIdx with
  | nil => cases hx
  | cons _ _ ih =>
    cases hx with
    | head => exact ⟨startIdx, .head _⟩
    | tail _ hxRest => obtain ⟨idx, hMem⟩ := ih (startIdx + 1) hxRest; exact ⟨idx, .tail _ hMem⟩
private theorem atomPosRanked_of_isBaseAtom (rk : PosRankMap) (a : Atom Term)
    (hBase : isBaseAtom a = true) : AtomPosRanked rk a := by
  rcases a with ⟨rel, args⟩; simp only [isBaseAtom, List.all_eq_true] at hBase; intro idx t hMem
  have htMem : t ∈ args := by
    have hGen : ∀ (k : Nat) (xs : List Term), (idx, t) ∈ enumFrom k xs → t ∈ xs := by
      intro k xs; induction xs generalizing k with
      | nil => intro h; cases h
      | cons _ _ ih => intro h; cases h with | head => exact .head _ | tail _ hr => exact .tail _ (ih (k + 1) hr)
    exact hGen 0 args hMem
  have htBase := hBase t htMem; cases t with | skolem _ _ _ => cases htBase | const _ => simp [skolemDepth]
private theorem evalPatArgs_enumFrom_correspondence (σ : Subst Term) (pts : List PatTerm)
    (ds : List Term) (startIdx : Nat) (hev : evalPatArgs Term.const σ pts = some ds) :
    (∀ idx d, (idx, d) ∈ enumFrom startIdx ds →
      ∃ pt, (idx, pt) ∈ enumFrom startIdx pts ∧ evalPatTerm Term.const σ pt = some d) ∧
    (∀ idx pt, (idx, pt) ∈ enumFrom startIdx pts →
      ∃ d, (idx, d) ∈ enumFrom startIdx ds ∧ evalPatTerm Term.const σ pt = some d) := by
  induction pts generalizing ds startIdx with
  | nil => injection hev with hds; subst hds; exact ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | cons pt rest ih =>
    simp only [evalPatArgs] at hev
    cases h₁ : evalPatTerm Term.const σ pt <;> simp only [h₁] at hev
    · cases hev
    · cases h₂ : evalPatArgs Term.const σ rest <;> simp only [h₂] at hev
      · cases hev
      · injection hev with hds; subst hds; rename_i d restD
        obtain ⟨ihL, ihR⟩ := ih restD (startIdx + 1) h₂; refine ⟨?_, ?_⟩
        · intro idx d' hMem; cases hMem with
          | head => exact ⟨pt, .head _, h₁⟩
          | tail _ hRest => obtain ⟨pt', hpt', hev'⟩ := ihL idx d' hRest; exact ⟨pt', .tail _ hpt', hev'⟩
        · intro idx pt' hMem; cases hMem with
          | head => exact ⟨d, .head _, h₁⟩
          | tail _ hRest => obtain ⟨d', hd', hev'⟩ := ihR idx pt' hRest; exact ⟨d', .tail _ hd', hev'⟩
private theorem body_var_depth_le_posRank (rk : PosRankMap) (σ : Subst Term)
    (body : List PatAtom) (bodyAtoms : FactSet)
    (hevBody : evalPatAtoms Term.const σ body = some bodyAtoms)
    (hRankedBody : ∀ a ∈ bodyAtoms, AtomPosRanked rk a)
    (v : VarId) (pB : RelPos) (hpB : pB ∈ varPositionsIn v body)
    (d : Term) (hlook : lookupSubst σ v = some d) : skolemDepth d ≤ rankOf rk pB := by
  simp only [varPositionsIn, List.mem_flatMap] at hpB; rcases hpB with ⟨ba, hbaMem, hpBba⟩
  have hexAtom : ∃ a ∈ bodyAtoms, evalPatAtom Term.const σ ba = some a := by
    induction body generalizing bodyAtoms with
    | nil => cases hbaMem
    | cons p₀ rest ih =>
      simp only [evalPatAtoms] at hevBody
      cases h₁ : evalPatAtom Term.const σ p₀ <;> simp only [h₁] at hevBody
      · cases hevBody
      · cases h₂ : evalPatAtoms Term.const σ rest <;> simp only [h₂] at hevBody
        · cases hevBody
        · injection hevBody with hga; subst hga; cases hbaMem with
          | head => exact ⟨_, .head _, h₁⟩
          | tail _ hRest =>
            obtain ⟨a, ha, heva⟩ := ih _ h₂ (fun b hb => hRankedBody b (.tail _ hb)) hRest
            exact ⟨a, .tail _ ha, heva⟩
  rcases hexAtom with ⟨a, haMem, heva⟩; simp only [List.mem_filterMap] at hpBba
  rcases hpBba with ⟨⟨idx, pt⟩, hIdxPt, hPtVar⟩; split at hPtVar
  · rename_i hptDec; have hptEq : pt = .var v := of_decide_eq_true hptDec
    injection hPtVar with hpBEq; subst hptEq; subst hpBEq
    simp only [evalPatAtom] at heva
    cases hargs : evalPatArgs Term.const σ ba.args <;> simp only [hargs] at heva
    · cases heva
    · injection heva with haEq; subst haEq; rename_i aArgs
      obtain ⟨_, hR⟩ := evalPatArgs_enumFrom_correspondence σ ba.args aArgs 0 hargs
      obtain ⟨d', hd'Mem, hevd'⟩ := hR idx (.var v) hIdxPt
      simp only [evalPatTerm, hlook, Option.some.injEq] at hevd'; subst hevd'
      exact hRankedBody { rel := ba.rel, args := aArgs } haMem idx d hd'Mem
  · cases hPtVar
private theorem lookupSubst_buildHeadSubst_frontier (frontierVars : List VarId) (tTuple : List Term)
    (existVars : List VarId) (mkExist : VarId → Term) (σ : Subst Term)
    (hExt : extractFrontierTuple frontierVars σ = some tTuple) {x : VarId} (hx : x ∈ frontierVars) :
    lookupSubst (buildHeadSubst frontierVars tTuple existVars mkExist) x = lookupSubst σ x := by
  have hBound : ∃ d, lookupSubst σ x = some d := by
    induction frontierVars generalizing tTuple with
    | nil => cases hx
    | cons v vs ih =>
      simp only [extractFrontierTuple] at hExt
      cases hv : lookupSubst σ v <;> simp only [hv] at hExt
      · cases hExt
      · cases hvs : extractFrontierTuple vs σ <;> simp only [hvs] at hExt
        · cases hExt
        · cases hx with | head => exact ⟨_, hv⟩ | tail _ hr => exact ih _ hvs hr
  rcases hBound with ⟨d, hd⟩
  have hZip : lookupSubst (frontierVars.zip tTuple) x = some d := by
    rw [lookupSubst_zip_of_extract frontierVars σ tTuple hExt x hx]; exact hd
  rw [hd]; exact lookupSubst_append_left (frontierVars.zip tTuple) _ x d hZip
private theorem lookupSubst_map_mkExist (existVars : List VarId) (mkExist : VarId → Term)
    {y : VarId} (hy : y ∈ existVars) :
    lookupSubst (existVars.map (fun z => (z, mkExist z))) y = some (mkExist y) := by
  induction existVars with
  | nil => cases hy
  | cons z _ ih =>
    simp only [List.map_cons, lookupSubst]; cases hzy : (z == y)
    · cases hy with | head => simp at hzy | tail _ hr => exact ih hr
    · have heq : z = y := LawfulBEq.eq_of_beq hzy; subst heq; rfl
private theorem lookupSubst_zip_none_of_not_mem {Dom : Type} (vars : List VarId) (vals : List Dom)
    {y : VarId} (hyNot : y ∉ vars) : lookupSubst (vars.zip vals) y = none := by
  induction vars generalizing vals with
  | nil => rfl
  | cons v _ ih =>
    cases vals with
    | nil => rfl
    | cons _ ds =>
      simp only [List.zip_cons_cons, lookupSubst]; cases hvy : (v == y)
      · exact ih ds (fun h => hyNot (.tail _ h))
      · have heq : v = y := LawfulBEq.eq_of_beq hvy; subst heq; exact False.elim (hyNot (.head _))
private theorem lookupSubst_append_of_left_none {Dom : Type} (xs ys : Subst Dom) (v : VarId)
    (hNone : lookupSubst xs v = none) : lookupSubst (xs ++ ys) v = lookupSubst ys v := by
  induction xs with
  | nil => rfl
  | cons kv _ ih =>
    rcases kv with ⟨k, _⟩; simp only [lookupSubst, List.cons_append] at hNone ⊢
    cases hk : (k == v) <;> rw [hk] at hNone; exact ih hNone; cases hNone
private theorem skolemDepthList_add_one_le (ts : List Term) (bound : Nat)
    (hBound : 1 ≤ bound) (hEach : ∀ t ∈ ts, skolemDepth t + 1 ≤ bound) :
    1 + skolemDepthList ts ≤ bound := by
  induction ts with
  | nil => simp [skolemDepthList, hBound]
  | cons t rest ih =>
    simp only [skolemDepthList]
    have ht : 1 + skolemDepth t ≤ bound := by rw [Nat.add_comm]; exact hEach t (.head _)
    have hrest : 1 + skolemDepthList rest ≤ bound := ih (fun x hx => hEach x (.tail _ hx))
    split; exact hrest; exact ht
private theorem mem_extractFrontierTuple_imp_var (vars : List VarId) (σ : Subst Term)
    (vals : List Term) (hExt : extractFrontierTuple vars σ = some vals)
    {t : Term} (ht : t ∈ vals) : ∃ x ∈ vars, lookupSubst σ x = some t := by
  induction vars generalizing vals with
  | nil => injection hExt with hvals; subst hvals; cases ht
  | cons v vs ih =>
    simp only [extractFrontierTuple] at hExt
    cases hv : lookupSubst σ v <;> simp only [hv] at hExt
    · cases hExt
    · cases hvs : extractFrontierTuple vs σ <;> simp only [hvs] at hExt
      · cases hExt
      · injection hExt with hvals; subst hvals; cases ht with
        | head => exact ⟨v, .head _, hv⟩
        | tail _ htRest => obtain ⟨x, hx, hlx⟩ := ih _ hvs htRest; exact ⟨x, .tail _ hx, hlx⟩
theorem weaklyAcyclic_rank_bound (rk : PosRankMap) (rules : List TgdRule)
    (fuel : Nat) (I : FactSet) (hWA : checkWeaklyAcyclic rk rules = true)
    (hBaseI : IsBaseFactSet I = true) :
    ∀ a ∈ runBoundedChase rules fuel I, ∀ t ∈ a.args, skolemDepth t ≤ maxRankOf rk := by
  have hRunRk : ∀ a ∈ runBoundedChase rules fuel I, AtomPosRanked rk a := by
    refine runBoundedChase_invariant (AtomPosRanked rk) rules ?_ fuel I ?_
    · intro r hrMem σ bodyAtoms headAtoms tTuple hevBody hBodyRk hExt hInst
      have hRuleWA : checkWeaklyAcyclicRule rk r = true := by
        simp only [checkWeaklyAcyclic, List.all_eq_true] at hWA; exact hWA r hrMem
      simp only [checkWeaklyAcyclicRule, Bool.and_eq_true, List.all_eq_true] at hRuleWA
      rcases hRuleWA with ⟨hFrontNE, hHeadWA⟩
      let σSkolem := buildHeadSubst r.frontierVars tTuple r.existVars (fun y => Term.skolem r.id y tTuple)
      have hHeadEach : ∀ (pas : List PatAtom) (as : FactSet), (∀ pa ∈ pas, pa ∈ r.head) →
          evalPatAtoms Term.const σSkolem pas = some as → ∀ a ∈ as, AtomPosRanked rk a := by
        intro pas; induction pas with
        | nil => intro as _ hev a ha; injection hev with has; subst has; cases ha
        | cons pa restP ihP =>
          intro as hSubP hevP a ha; simp only [evalPatAtoms] at hevP
          cases h₁ : evalPatAtom Term.const σSkolem pa <;> simp only [h₁] at hevP
          · cases hevP
          · cases h₂ : evalPatAtoms Term.const σSkolem restP <;> simp only [h₂] at hevP
            · cases hevP
            · injection hevP with hasEq; subst hasEq; cases ha with
              | tail _ haRest => exact ihP _ (fun p hp => hSubP p (.tail _ hp)) h₂ a haRest
              | head =>
                simp only [evalPatAtom] at h₁
                cases hargs : evalPatArgs Term.const σSkolem pa.args <;> simp only [hargs] at h₁
                · cases h₁
                · injection h₁ with haMk; subst haMk; rename_i aArgs; intro j t hjtMem
                  obtain ⟨hL, _⟩ := evalPatArgs_enumFrom_correspondence σSkolem pa.args aArgs 0 hargs
                  obtain ⟨pt, hptMem, hevPt⟩ := hL j t hjtMem
                  have hpaClause := hHeadWA pa (hSubP pa (.head _)) (j, pt) hptMem
                  cases pt with
                  | const _ => simp only [evalPatTerm, Option.some.injEq] at hevPt; subst hevPt; simp [skolemDepth]
                  | var v =>
                    simp only at hpaClause; cases hvFront : r.frontierVars.contains v
                    · rw [hvFront] at hpaClause
                      cases hvExist : r.existVars.contains v <;> rw [hvExist] at hpaClause
                      · cases hpaClause
                      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
                          List.all_eq_true, decide_eq_true_eq] at hpaClause
                        rcases hpaClause with ⟨hOneLe, hSpecial⟩
                        have hvNotFront : v ∉ r.frontierVars :=
                          fun hm => by rw [List.contains_iff_mem.mpr hm] at hvFront; cases hvFront
                        have hLookSkolem : lookupSubst σSkolem v = some (Term.skolem r.id v tTuple) := by
                          simp only [σSkolem, buildHeadSubst]
                          rw [lookupSubst_append_of_left_none _ _ v
                            (lookupSubst_zip_none_of_not_mem r.frontierVars tTuple hvNotFront)]
                          exact lookupSubst_map_mkExist r.existVars _ (List.contains_iff_mem.mp hvExist)
                        simp only [evalPatTerm, hLookSkolem, Option.some.injEq] at hevPt
                        subst hevPt; simp only [skolemDepth]
                        apply skolemDepthList_add_one_le tTuple _ hOneLe; intro tArg htArg
                        obtain ⟨x, hxFront, hlx⟩ :=
                          mem_extractFrontierTuple_imp_var r.frontierVars σ tTuple hExt htArg
                        have hxPosNE := hFrontNE x hxFront
                        cases hPosList : varPositionsIn x r.body with
                        | nil => simp [hPosList] at hxPosNE
                        | cons pB _ =>
                          have hpBMem : pB ∈ varPositionsIn x r.body := by rw [hPosList]; exact .head _
                          exact Nat.le_trans
                            (Nat.add_le_add_right
                              (body_var_depth_le_posRank rk σ r.body bodyAtoms hevBody hBodyRk x pB hpBMem tArg hlx) 1)
                            (hSpecial x hxFront pB hpBMem)
                    · rw [hvFront] at hpaClause
                      simp only [↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hpaClause
                      have hvInFront := List.contains_iff_mem.mp hvFront
                      have hLookFront : lookupSubst σSkolem v = lookupSubst σ v :=
                        lookupSubst_buildHeadSubst_frontier r.frontierVars tTuple r.existVars
                          (fun y => Term.skolem r.id y tTuple) σ hExt hvInFront
                      simp only [evalPatTerm, hLookFront] at hevPt
                      have hvPosNE := hFrontNE v hvInFront
                      cases hPosList : varPositionsIn v r.body with
                      | nil => simp [hPosList] at hvPosNE
                      | cons pB _ =>
                        have hpBMem : pB ∈ varPositionsIn v r.body := by rw [hPosList]; exact .head _
                        exact Nat.le_trans
                          (body_var_depth_le_posRank rk σ r.body bodyAtoms hevBody hBodyRk v pB hpBMem t hevPt)
                          (hpaClause pB hpBMem)
      exact hHeadEach r.head headAtoms (fun p hp => hp) hInst
    · intro a ha; simp only [IsBaseFactSet, List.all_eq_true] at hBaseI
      exact atomPosRanked_of_isBaseAtom rk a (hBaseI a ha)
  intro a ha t ht; obtain ⟨idx, hIdxMem⟩ := mem_enumFrom_of_mem a.args 0 t ht
  exact Nat.le_trans (hRunRk a ha idx t hIdxMem) (rankOf_le_maxRankOf rk { rel := a.rel, pos := idx })

/-! ## §7. Core Minimization / Retraction Certificate (`checkRetractionCore`) -/
structure ConjunctiveQuery where
  atoms : List PatAtom
  deriving DecidableEq, Repr, BEq
def evalBCQ (q : ConjunctiveQuery) (M : FactSet) : Bool := !(matchPatAtoms Term.const [] q.atoms M).isEmpty
def evalUCQ (qs : List ConjunctiveQuery) (M : FactSet) : Bool := qs.any (evalBCQ · M)
structure RetractionCert where
  termMap : List (Term × Term)
  deriving DecidableEq, Repr
def lookupTermMap (entries : List (Term × Term)) (t : Term) : Option Term :=
  match entries with | [] => none | (src, dst) :: rest => if src == t then some dst else lookupTermMap rest t
@[expose] def applyRetraction (cert : RetractionCert) (t : Term) : Term :=
  match t with | .const c => .const c | .skolem _ _ _ => (lookupTermMap cert.termMap t).getD t
def checkRetractionCore (cert : RetractionCert) (M C : FactSet) : Bool :=
  cert.termMap.all (fun (src, dst) => match src with | .const _ => src == dst | .skolem _ _ _ => true) &&
  C.all (fun a => M.contains a) &&
  M.all (fun a => C.contains (mapAtom (applyRetraction cert) a)) &&
  C.all (fun a => mapAtom (applyRetraction cert) a == a)
private theorem evalBCQ_mono_of_hom (f : Term → Term) (hConst : ∀ c, f (.const c) = .const c)
    (A B : FactSet) (hHom : ∀ a ∈ A, mapAtom f a ∈ B)
    (q : ConjunctiveQuery) (hq : evalBCQ q A = true) : evalBCQ q B = true := by
  cases hMatches : matchPatAtoms Term.const [] q.atoms A with
  | nil => simp [evalBCQ, hMatches] at hq
  | cons σ _ =>
    have hσMem : σ ∈ matchPatAtoms Term.const [] q.atoms A := by rw [hMatches]; exact .head _
    obtain ⟨_, groundAtoms, hev, hSub⟩ := matchPatAtoms_sound Term.const [] σ q.atoms A hσMem
    have hevMapped : evalPatAtoms Term.const (mapSubst f σ) q.atoms = some (groundAtoms.map (mapAtom f)) := by
      rw [evalPatAtoms_mapSubst Term.const Term.const f hConst σ q.atoms, hev]; rfl
    have hSubMapped : ∀ b ∈ groundAtoms.map (mapAtom f), b ∈ B := by
      intro b hb; rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩; exact hHom a (hSub a ha)
    obtain ⟨σ', hσ'Mem, _⟩ :=
      matchPatAtoms_complete Term.const [] (mapSubst f σ) (ExtendsSubst.nil (mapSubst f σ))
        q.atoms (groundAtoms.map (mapAtom f)) B hevMapped hSubMapped
    cases hMatchesB : matchPatAtoms Term.const [] q.atoms B with
    | nil => rw [hMatchesB] at hσ'Mem; cases hσ'Mem
    | cons _ _ => simp [evalBCQ, hMatchesB]
theorem checkRetractionCore_sound (cert : RetractionCert) (M C : FactSet)
    (hOk : checkRetractionCore cert M C = true) :
    (∀ a ∈ C, a ∈ M) ∧ (∀ a ∈ M, mapAtom (applyRetraction cert) a ∈ C) ∧
    (∀ a ∈ C, mapAtom (applyRetraction cert) a = a) ∧
    (∀ q : ConjunctiveQuery, evalBCQ q M = evalBCQ q C) := by
  simp only [checkRetractionCore, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hOk
  rcases hOk with ⟨⟨⟨_, hCsubM⟩, hMtoC⟩, hFixC⟩
  refine ⟨hCsubM, hMtoC, fun a ha => LawfulBEq.eq_of_beq (hFixC a ha), ?_⟩; intro q
  cases hqM : evalBCQ q M <;> cases hqC : evalBCQ q C
  · rfl
  · have hMTrue := evalBCQ_mono_of_hom id (fun _ => rfl) C M (fun a ha => by rw [mapAtom_id]; exact hCsubM a ha) q hqC
    rw [hqM] at hMTrue; cases hMTrue
  · have hCTrue := evalBCQ_mono_of_hom (applyRetraction cert) (fun _ => rfl) M C hMtoC q hqM
    rw [hqC] at hCTrue; cases hCTrue
  · rfl
theorem checkRetractionCore_preserves_ucq (cert : RetractionCert) (M C : FactSet)
    (hOk : checkRetractionCore cert M C = true) (qs : List ConjunctiveQuery) :
    evalUCQ qs M = evalUCQ qs C := by
  have hBCQ := (checkRetractionCore_sound cert M C hOk).2.2.2
  simp only [evalUCQ]; congr 1; funext q; exact hBCQ q
theorem checkRetractionCore_inhabited (rel c0 c1 : Nat) :
    ∃ (cert : RetractionCert) (M C : FactSet),
      M.length > C.length ∧ C.length > 0 ∧ checkRetractionCore cert M C = true :=
  ⟨{ termMap := [(.skolem 1 1 [.const c0], .const c1)] },
   [{ rel := rel, args := [.const c0, .const c1] },
    { rel := rel, args := [.const c0, .skolem 1 1 [.const c0]] }],
   [{ rel := rel, args := [.const c0, .const c1] }],
   by simp, by simp, by simp [checkRetractionCore, applyRetraction, lookupTermMap, mapAtom]⟩
end Obend.SymbolicZk.SkolemChaseCore
end
