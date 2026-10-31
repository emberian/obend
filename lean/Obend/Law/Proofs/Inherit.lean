module
/-
# Obend.Law.Proofs.Inherit — the effective law is the conjunction of its precedence list

* `effective_law_eval`: for closed laws, `Admits (effective lin) o n rq ↔ ∀ p ∈ lin, Admits p.2 o n rq`
  (the audit's `eval (effective c) = (lin c).all (fun p => eval p.body)`, over `Evaluates`).
* `inherited_never_widens`: an effective law admits nothing an ancestor refuses.
* `effective_refusal_names`: a refusal of the effective law names the FIRST ancestor on the
  precedence list that refused, carries its reason, and every ancestor before it admitted;
  `effective_refuses_first` is the converse.
* `effectiveVia_eval`: the same, through a C4 linearization of the parent graph and the name table.
* `precedence_ok` (`precedence_monotone`, `precedence_local`): the list the effective law is built
  from starts at the head, repeats nothing, and keeps every parent's precedence list and every local
  chain in order (Barrett et al. 1996).
* `c3_tree_is_chain`: on a tree C4's `linearize` is the chain to the root; `precedence_tree`: the
  validation never refuses an acyclic tree; `effectiveVia_tree`: the effective law is the
  conjunction along the chain.
* `effectiveVia_parent`, `child_never_widens`: a child's effective law admits nothing a parent's
  (precedence list, or effective law at a coherent parent) refuses.
-/
public import Obend.Law.Inherit
public import Obend.Law.Proofs.Std
public import Obend.Law.Proofs.Claim
public import Obend.Tactic.Tooth
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
set_option autoImplicit false

theorem subst_chain_cons (σ : Nat → Term) (d : Nat) (name : String) (L : Term)
    (rest : List (String × Term)) (hL : closedB L = true) :
    (chainAt ⟨d⟩ ((name, L) :: rest)).substitute σ =
      .case (.app (.app (.app L (σ (d + 2))) (σ (d + 1))) (σ d))
        [("ok", (chainAt ⟨d + 1⟩ rest).substitute (liftSubstitution σ)),
         ("refused", (blameT name).substitute (liftSubstitution σ))] := by
  simp [chainAt, Term.substitute, closedB_subst hL, At.old, At.new, At.req, At.under]

theorem blame_inst (name : String) (σ : Nat → Term) (p : Term) :
    instantiate ((blameT name).substitute (liftSubstitution σ)) p = blamed name p := by
  rw [instantiate_lift]
  simp [blameT, blamed, Term.substitute]

theorem blamed_value (name : String) (why : Term) : Value (blamed name why) := .inject _ _

/-- The effective chain at depth `d`, under a substitution that holds the request, the new and
the old state at `d`, `d + 1`, `d + 2`, admits exactly when every law on it does. -/
theorem chain_eval {o n rq : Data} : ∀ (lin : List (String × Term)) (d : Nat) (σ : Nat → Term),
    (∀ p ∈ lin, closedB p.2 = true) → σ d = rq.term → σ (d + 1) = n.term → σ (d + 2) = o.term →
    ((∃ w, Evaluates ((chainAt ⟨d⟩ lin).substitute σ) (.inject "ok" w)) ↔ ∀ p ∈ lin, Admits p.2 o n rq)
  | [], d, σ, _, _, _, _ => by
      simp only [chainAt, subst_okT, List.not_mem_nil, false_implies, implies_true, iff_true]
      exact ⟨_, evaluates_self (.inject _ _)⟩
  | (name, L) :: rest, d, σ, hc, h0, h1, h2 => by
      have hL : closedB L = true := hc _ (List.mem_cons_self ..)
      have hrest : ∀ p ∈ rest, closedB p.2 = true := fun p hp => hc p (List.mem_cons_of_mem _ hp)
      rw [subst_chain_cons σ d name L rest hL, h0, h1, h2]
      constructor
      · rintro ⟨w, h⟩
        obtain ⟨l, p, body, hs, hf, hb⟩ := case_inv h
        have hm := List.mem_of_find?_eq_some hf
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [instantiate_lift] at hb
          have ih := (chain_eval rest (d + 1) (scons p σ) hrest h0 h1 h2).1 ⟨w, hb⟩
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ⟨p, hs⟩
          · exact ih q hq
        · rw [blame_inst] at hb
          have := evaluates_value (blamed_value _ _) hb
          simp [blamed] at this
      · intro hall
        obtain ⟨w, hw⟩ := hall _ (List.mem_cons_self ..)
        obtain ⟨w', hw'⟩ := (chain_eval rest (d + 1) (scons w σ) hrest h0 h1 h2).2
          (fun q hq => hall q (List.mem_cons_of_mem _ hq))
        refine ⟨w', evaluates_case (body := (chainAt ⟨d + 1⟩ rest).substitute (liftSubstitution σ)) hw (by simp) ?_⟩
        rw [instantiate_lift]
        exact hw'

/-- **The effective law is the conjunction of its precedence list.** -/
public theorem effective_law_eval {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    (o n rq : Data) : Admits (effective lin) o n rq ↔ ∀ p ∈ lin, Admits p.2 o n rq := by
  rw [effective, admits_iff]
  exact chain_eval lin 0 _ hc rfl rfl rfl

/-- **An inherited law never widens**: what an ancestor does not admit, the effective law does not
admit. -/
public theorem inherited_never_widens {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    {name : String} {L : Term} (hp : (name, L) ∈ lin) {o n rq : Data} (h : ¬ Admits L o n rq) :
    ¬ Admits (effective lin) o n rq :=
  fun he => h ((effective_law_eval hc o n rq).1 he _ hp)

/-- In particular an ancestor's refusal is a refusal of the effective law. -/
public theorem inherited_refusal_kept {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    {name : String} {L : Term} (hp : (name, L) ∈ lin) {o n rq : Data} {why : String}
    (h : Refuses L o n rq why) : ¬ Admits (effective lin) o n rq :=
  inherited_never_widens hc hp (refuses_not_admits h)

theorem chain_refused {o n rq : Data} : ∀ (lin : List (String × Term)) (d : Nat) (σ : Nat → Term),
    (∀ p ∈ lin, closedB p.2 = true) → σ d = rq.term → σ (d + 1) = n.term → σ (d + 2) = o.term →
    ∀ {r : Term}, Evaluates ((chainAt ⟨d⟩ lin).substitute σ) (.inject "refused" r) →
      ∃ pre name L post why, lin = pre ++ (name, L) :: post ∧ (∀ q ∈ pre, Admits q.2 o n rq) ∧
        Evaluates (applyLaw L o n rq) (.inject "refused" why) ∧
        r = .record [("by", .label name), ("reason", why)]
  | [], d, σ, _, _, _, _, r, h => by
      simp only [chainAt, subst_okT] at h
      have := evaluates_value (.inject _ _) h
      simp [okT] at this
  | (name, L) :: rest, d, σ, hc, h0, h1, h2, r, h => by
      have hL : closedB L = true := hc _ (List.mem_cons_self ..)
      have hrest : ∀ p ∈ rest, closedB p.2 = true := fun p hp => hc p (List.mem_cons_of_mem _ hp)
      rw [subst_chain_cons σ d name L rest hL, h0, h1, h2] at h
      obtain ⟨l, p, body, hs, hf, hb⟩ := case_inv h
      have hm := List.mem_of_find?_eq_some hf
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [instantiate_lift] at hb
        obtain ⟨pre, name', L', post, why, hlin, hpre, hL', hr⟩ :=
          chain_refused rest (d + 1) (scons p σ) hrest h0 h1 h2 hb
        refine ⟨(name, L) :: pre, name', L', post, why, by simp [hlin], ?_, hL', hr⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨p, hs⟩
        · exact hpre q hq
      · rw [blame_inst] at hb
        have := evaluates_value (blamed_value _ _) hb
        simp only [blamed, Term.inject.injEq, true_and] at this
        exact ⟨[], name, L, rest, p, rfl, by simp, hs, this⟩

/-- **A refusal names the ancestor clause**: when the effective law refuses, its refusal is
`{by = name, reason = why}` for the first `(name, L)` on the precedence list that refused (with
`why`); every law before it admitted. -/
public theorem effective_refusal_names {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    {o n rq : Data} {r : Term} (h : Evaluates (applyLaw (effective lin) o n rq) (.inject "refused" r)) :
    ∃ pre name L post why, lin = pre ++ (name, L) :: post ∧ (∀ q ∈ pre, Admits q.2 o n rq) ∧
      Evaluates (applyLaw L o n rq) (.inject "refused" why) ∧ RefusedBy (effective lin) o n rq name why := by
  have h' := evaluates_of_steps (applyLaw_steps _ o n rq) h
  obtain ⟨pre, name, L, post, why, hlin, hpre, hL, rfl⟩ := chain_refused lin 0 _ hc rfl rfl rfl h'
  exact ⟨pre, name, L, post, why, hlin, hpre, hL, h⟩

theorem chain_refuses_first {o n rq : Data} {name : String} {L : Term} {why : Term}
    (hL : closedB L = true) (hrefuse : Evaluates (applyLaw L o n rq) (.inject "refused" why)) :
    ∀ (pre post : List (String × Term)) (d : Nat) (σ : Nat → Term),
      (∀ p ∈ pre, closedB p.2 = true) → (∀ q ∈ pre, Admits q.2 o n rq) →
      σ d = rq.term → σ (d + 1) = n.term → σ (d + 2) = o.term →
      Evaluates ((chainAt ⟨d⟩ (pre ++ (name, L) :: post)).substitute σ) (blamed name why)
  | [], post, d, σ, _, _, h0, h1, h2 => by
      simp only [List.nil_append]
      rw [subst_chain_cons σ d name L post hL, h0, h1, h2]
      refine evaluates_case (body := (blameT name).substitute (liftSubstitution σ)) hrefuse (by simp) ?_
      rw [blame_inst]
      exact evaluates_self (blamed_value _ _)
  | (name', L') :: pre, post, d, σ, hc, ha, h0, h1, h2 => by
      have hL' : closedB L' = true := hc _ (List.mem_cons_self ..)
      simp only [List.cons_append]
      rw [subst_chain_cons σ d name' L' _ hL', h0, h1, h2]
      obtain ⟨w, hw⟩ := ha _ (List.mem_cons_self ..)
      refine evaluates_case (body := (chainAt ⟨d + 1⟩ (pre ++ (name, L) :: post)).substitute (liftSubstitution σ))
        hw (by simp) ?_
      rw [instantiate_lift]
      exact chain_refuses_first hL hrefuse pre post (d + 1) (scons w σ)
        (fun p hp => hc p (List.mem_cons_of_mem _ hp)) (fun q hq => ha q (List.mem_cons_of_mem _ hq)) h0 h1 h2

/-- **The first refusing ancestor is the one named**: if every law before `(name, L)` admits and
`L` refuses with `why`, the effective law refuses naming `name` with `why`. -/
public theorem effective_refuses_first {pre post : List (String × Term)} {name : String} {L : Term}
    (hc : ∀ p ∈ pre ++ (name, L) :: post, closedB p.2 = true) {o n rq : Data} {why : Term}
    (hpre : ∀ q ∈ pre, Admits q.2 o n rq) (hL : Evaluates (applyLaw L o n rq) (.inject "refused" why)) :
    RefusedBy (effective (pre ++ (name, L) :: post)) o n rq name why := by
  unfold RefusedBy effective
  refine evaluates_steps (applyLaw_steps _ o n rq) ?_
  exact chain_refuses_first (hc (name, L) (by simp)) hL pre post 0 _ (fun p hp => hc p (by simp [hp])) hpre
    rfl rfl rfl

/-! ## Through a C4 linearization -/

public theorem resolve_ok {laws : List (String × Term)} : ∀ {names : List String} {ls : List (String × Term)},
    resolve laws names = .ok ls →
      ls.map Prod.fst = names ∧ ∀ p ∈ ls, laws.lookup p.1 = some p.2 ∧ closedB p.2 = true
  | [], ls, h => by simp [resolve] at h; subst h; simp
  | name :: rest, ls, h => by
      simp only [resolve] at h
      split at h
      · cases h
      · rename_i law hl
        split at h
        · rename_i hcl
          split at h
          · rename_i ls' hr
            cases h
            obtain ⟨h1, h2⟩ := resolve_ok hr
            refine ⟨by simp [h1], ?_⟩
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact ⟨hl, hcl⟩
            · exact h2 p hp
          · cases h
        · cases h

/-- **The effective law of a node, through C4**: when `effectiveVia` builds a law, it admits exactly
when the law of every name on the node's C4 precedence list admits. -/
public theorem effectiveVia_eval {g : Obend.Spec.C4.Graph} {laws : List (String × Term)} {head : String}
    {parents : List (List String)} {t : Term} (h : effectiveVia g laws head parents = .ok t) :
    ∃ names, precedence g head parents = .ok names ∧ ∀ o n rq : Data,
      (Admits t o n rq ↔ ∀ name ∈ names, ∃ L, laws.lookup name = some L ∧ Admits L o n rq) := by
  unfold effectiveVia at h
  split at h
  · cases h
  · rename_i names hn
    split at h
    · rename_i ls hr
      cases h
      obtain ⟨hnames, hls⟩ := resolve_ok hr
      refine ⟨names, hn, fun o n rq => ?_⟩
      rw [effective_law_eval (fun p hp => (hls p hp).2)]
      constructor
      · intro hall name hname
        rw [← hnames] at hname
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hname
        exact ⟨p.2, (hls p hp).1, hall p hp⟩
      · intro hall p hp
        obtain ⟨L, hL, hadm⟩ := hall p.1 (hnames ▸ List.mem_map_of_mem hp)
        rw [(hls p hp).1] at hL
        cases hL
        exact hadm
    · cases h

/-! ## Precedence lists: the head, no repeats, monotonicity, local precedence -/

public theorem nodupB_sound : ∀ {l : List String}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have h' : x ∉ xs ∧ nodupB xs = true := by simpa [nodupB] using h
      exact List.nodup_cons.2 ⟨h'.1, nodupB_sound h'.2⟩

public theorem nodupB_complete : ∀ {l : List String}, l.Nodup → nodupB l = true
  | [], _ => rfl
  | x :: xs, h => by
      obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h
      simp [nodupB, hx, nodupB_complete hxs]

/-- **What a precedence list is.** A list `precedence` accepts starts at the head, names nothing
twice, keeps every local chain in order and every parent's own precedence list in order. -/
public theorem precedence_ok {g : Obend.Spec.C4.Graph} {head : String} {parents : List (List String)}
    {lin : List String} (h : precedence g head parents = .ok lin) :
    lin.head? = some head ∧ lin.Nodup ∧ (∀ chain ∈ parents, chain.Sublist lin) ∧
      ∀ chain ∈ parents, ∀ p ∈ chain, (g.precedence p).Sublist lin := by
  unfold precedence at h
  split at h
  · split at h
    · rename_i hok
      cases h
      simp only [precedenceOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        List.isSublist_iff_sublist] at hok
      obtain ⟨⟨hh, hn⟩, hp⟩ := hok
      exact ⟨hh, nodupB_sound hn, fun c hc => (hp c hc).1, fun c hc p hp' => (hp c hc).2 p hp'⟩
    · cases h
  · cases h

/-- **Monotonicity** (Barrett et al. 1996): every parent's precedence list is kept, in order. -/
public theorem precedence_monotone {g : Obend.Spec.C4.Graph} {head : String} {parents : List (List String)}
    {lin : List String} (h : precedence g head parents = .ok lin) :
    ∀ chain ∈ parents, ∀ p ∈ chain, (g.precedence p).Sublist lin :=
  (precedence_ok h).2.2.2

/-- **Local precedence**: every local chain of parents is kept, in order. -/
public theorem precedence_local {g : Obend.Spec.C4.Graph} {head : String} {parents : List (List String)}
    {lin : List String} (h : precedence g head parents = .ok lin) :
    ∀ chain ∈ parents, chain.Sublist lin :=
  (precedence_ok h).2.2.1

/-! ## Trees -/

theorem chain_head (t : Tree) : ∀ (n : Nat) (x : String), ∃ rest, t.chain n x = x :: rest
  | 0, x => ⟨[], rfl⟩
  | n + 1, x => ⟨_, rfl⟩

/-- **On a tree the C4 linearization is the chain to the root** (C3 and C4 agree with single
inheritance): the linearization of `x` with its one parent is `x` followed by the parent's chain. -/
public theorem c3_tree_is_chain (t : Tree) (n : Nat) (x : String) :
    Obend.Spec.C4.linearize (t.graph n) [x] (t.parents x) = .ok (t.chain (n + 1) x, none) := by
  unfold Tree.parents
  cases hp : t.parent x with
  | none => simp [Obend.Spec.C4.linearize, Tree.chain, hp]; rfl
  | some p =>
      have : List.find? (fun _ => false) (t.chain n p).tail = none := List.find?_eq_none.2 (by simp)
      simp [Obend.Spec.C4.linearize, Tree.chain, hp, Tree.graph, Obend.Spec.C4.superSuffix, this]; rfl

/-- On an acyclic tree the validated precedence is the chain: the check never refuses. -/
public theorem precedence_tree (t : Tree) (n : Nat) (x : String) (acyclic : (t.chain (n + 1) x).Nodup) :
    precedence (t.graph n) x (t.parents x) = .ok (t.chain (n + 1) x) := by
  unfold precedence
  rw [c3_tree_is_chain]
  simp only
  rw [if_pos]
  simp only [precedenceOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.isSublist_iff_sublist]
  refine ⟨⟨by simp [Tree.chain], nodupB_complete acyclic⟩, ?_⟩
  intro chain hc
  unfold Tree.parents at hc
  cases hp : t.parent x with
  | none => rw [hp] at hc; cases hc
  | some p =>
      rw [hp] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      have hch : t.chain (n + 1) x = x :: t.chain n p := by simp [Tree.chain, hp]
      obtain ⟨rest, hr⟩ := chain_head t n p
      refine ⟨?_, ?_⟩
      · rw [hch, hr]
        exact List.Sublist.cons _ (List.Sublist.cons_cons _ (List.nil_sublist _))
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        rw [hch]
        exact List.Sublist.cons _ (List.Sublist.refl _)

/-- **On a tree the effective law is the conjunction along the chain to the root.** -/
public theorem effectiveVia_tree {t : Tree} {n : Nat} {laws : List (String × Term)} {x : String} {law : Term}
    (h : effectiveVia (t.graph n) laws x (t.parents x) = .ok law) (o new rq : Data) :
    Admits law o new rq ↔ ∀ name ∈ t.chain (n + 1) x, ∃ L, laws.lookup name = some L ∧ Admits L o new rq := by
  obtain ⟨names, hn, hev⟩ := effectiveVia_eval h
  have : names = t.chain (n + 1) x := by
    unfold precedence at hn
    rw [c3_tree_is_chain] at hn
    simp only at hn
    split at hn
    · cases hn; rfl
    · cases hn
  subst this
  exact hev o new rq

/-- **A child's law is at least as strict as each parent's precedence list**: what the child's
effective law admits, the law of every name on every parent's precedence list admits. -/
public theorem effectiveVia_parent {g : Obend.Spec.C4.Graph} {laws : List (String × Term)} {head : String}
    {parents : List (List String)} {t : Term} (h : effectiveVia g laws head parents = .ok t)
    {o n rq : Data} (ha : Admits t o n rq) :
    ∀ chain ∈ parents, ∀ p ∈ chain, ∀ name ∈ g.precedence p,
      ∃ L, laws.lookup name = some L ∧ Admits L o n rq := by
  obtain ⟨names, hn, hev⟩ := effectiveVia_eval h
  intro chain hc p hp name hname
  exact (hev o n rq).1 ha name ((precedence_monotone hn chain hc p hp).subset hname)

/-- **A child never widens a parent's effective law.** When the graph's precedence of a parent `p`
is `p`'s own validated precedence (the graph is coherent at `p`), what the child's effective law
admits, `p`'s effective law admits. -/
public theorem child_never_widens {g : Obend.Spec.C4.Graph} {laws : List (String × Term)} {head : String}
    {parents : List (List String)} {t : Term} (h : effectiveVia g laws head parents = .ok t)
    {p : String} (hp : ∃ chain ∈ parents, p ∈ chain) {ps : List (List String)}
    (coherent : precedence g p ps = .ok (g.precedence p)) {tp : Term}
    (hpt : effectiveVia g laws p ps = .ok tp) {o n rq : Data} (ha : Admits t o n rq) : Admits tp o n rq := by
  obtain ⟨names, hn, hev⟩ := effectiveVia_eval hpt
  rw [coherent] at hn
  cases hn
  obtain ⟨chain, hc, hpc⟩ := hp
  exact (hev o n rq).2 (effectiveVia_parent h ha chain hc p hpc)

/-! ## Teeth -/

/-- The run reached a refusal naming an ancestor, and the ancestor's reason. -/
@[expose] public def blameOf : Option Term → Option (String × String)
  | some (.inject "refused" (.record [("by", .label b), ("reason", .label why)])) => some (b, why)
  | _ => none

theorem refusedBy_of_run {law : Term} {o n rq : Data} {name why : String} (fuel : Nat)
    (h : blameOf (run fuel (applyLaw law o n rq)) = some (name, why)) :
    RefusedBy law o n rq name (.label why) := by
  unfold blameOf at h
  split at h
  · cases h; exact run_sound fuel (by assumption)
  · cases h

/-- A room bounds `total`; a board admits only its members; `board2` (under both) is signed by
the owner. -/
@[expose] public def boardLaws : List (String × Term) :=
  [("board2", ownerSigns unitTy), ("board", allowlistLaw unitTy ["ann", "bob"]),
   ("room", bounded unitTy "total" 5)]

public theorem boardLaws_closed : ∀ p ∈ boardLaws, closedB p.2 = true := by
  intro p hp
  simp only [boardLaws, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem inherit_tooth :
    Admits (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) "room" (.label "total over the bound") ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) "board" (.label "not on the allowlist") ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 9) (rqBy "bob" "ann" writeO) "board2" (.label "not signed by the owner") ∧
      Admits (bounded unitTy "total" 5) (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) :=
  ⟨admits_of_run 500 (by decide +kernel), refusedBy_of_run 500 (by decide +kernel),
    refusedBy_of_run 500 (by decide +kernel), refusedBy_of_run 500 (by decide +kernel),
    admits_of_run 500 (by decide +kernel)⟩

/-- A chain of single parents: `board2 → board → room`. -/
@[expose] public def boardGraph : Obend.Spec.C4.Graph where
  precedence x := if x = "board" then ["board", "room"] else if x = "room" then ["room"] else [x]
  isSuffix _ := false

theorem c4_tooth :
    (precedence boardGraph "board2" [["board"]]).toOption = some ["board2", "board", "room"] ∧
      ((effectiveVia boardGraph boardLaws "board2" [["board"]]).toOption.map
        fun t => okB (run 500 (applyLaw t (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO)))) = some true ∧
      (effectiveVia boardGraph [] "board2" [["board"]]).toOption.isNone = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A three-level tree `board2 → board → room`. -/
@[expose] public def boardTree : Tree := ⟨fun x => if x = "board2" then some "board" else if x = "board" then some "room" else none⟩

theorem tree_tooth :
    (Obend.Spec.C4.linearize (boardTree.graph 4) ["board2"] (boardTree.parents "board2")).toOption =
      some (["board2", "board", "room"], none) ∧
    (precedence (boardTree.graph 4) "board2" (boardTree.parents "board2")).toOption = some ["board2", "board", "room"] ∧
    ((effectiveVia (boardTree.graph 4) boardLaws "board2" (boardTree.parents "board2")).toOption.map
        fun t => okB (run 500 (applyLaw t (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO)))) = some true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- An incoherent oracle: the parent's "precedence" does not start at the parent, so the produced
list breaks local precedence, and the validated precedence refuses it. -/
@[expose] public def incoherentGraph : Obend.Spec.C4.Graph := ⟨fun x => if x = "board" then ["room"] else [x], fun _ => false⟩

theorem unordered_tooth :
    (Obend.Spec.C4.linearize incoherentGraph ["board2"] [["board"]]).toOption.map (·.1) = some ["board2", "room"] ∧
      (match precedence incoherentGraph "board2" [["board"]] with
        | .error e => some e
        | .ok _ => none) = some (.unordered "board2") :=
  ⟨by decide +kernel, by decide +kernel⟩

#tooth precedence_local by mutation precedenceOk := fun _ _ _ _ => true
#tooth precedence_monotone by mutation precedenceOk := fun _ _ _ _ => true

end Obend.Law
