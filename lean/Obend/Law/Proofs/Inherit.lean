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
-/
public import Obend.Law.Inherit
public import Obend.Law.Proofs.Std
public import Obend.Law.Proofs.Claim
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

theorem boardLaws_closed : ∀ p ∈ boardLaws, closedB p.2 = true := by
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

end Obend.Law
