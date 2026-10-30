module
/-
# Obend.Law.Proofs.Std — what each stdlib law means, over Core4's reference semantics

Every theorem here reads an ADMITTED law (`Admits`: its application evaluates to `ok`) back to a
fact about the old state, the new state and the request, as data. They are proved
compositionally from the combinators' inversion lemmas (`guard_ok`, `allOf_ok`, `anyOf_true`,
`lawCase6_arm`), never by evaluating a generated term. Ported from nanodregg `Lang/Proofs/Std.lean`
(origin/main `2dcc9ea`), where the semantics was big-step over environments; here it is Core4's
small-step `Evaluates` over substitution (`Obend.Law.Proofs.Eval`).

Every theorem whose hypothesis could be unsatisfiable has a tooth beside it: a concrete instance,
run by `decide +kernel` through `run` and read back by `run_sound`, where the law admits (so the
hypothesis is inhabited) and one where it refuses with the named reason (so the law is not `ok`).
-/
public import Obend.Law.Std
public import Obend.Law.Proofs.Eval
public import Obend.AxiomPin
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
set_option autoImplicit false

/-! ## Substitution through the combinators -/

@[simp] public theorem subst_okT (σ : Nat → Term) : okT.substitute σ = okT := by
  simp [okT, Term.substitute]
@[simp] public theorem subst_refusedT (σ : Nat → Term) (why : String) :
    (refusedT why).substitute σ = refusedT why := by
  simp [refusedT, Term.substitute]
@[simp] public theorem subst_trueT (σ : Nat → Term) : trueT.substitute σ = trueT := by
  simp [trueT, Term.substitute]
@[simp] public theorem subst_falseT (σ : Nat → Term) : falseT.substitute σ = falseT := by
  simp [falseT, Term.substitute]
@[simp] public theorem subst_natT (σ : Nat → Term) (k : Nat) : (natT k).substitute σ = natT k := by
  simp [natT, Term.substitute]
@[simp] public theorem subst_label (σ : Nat → Term) (s : String) : (Term.label s).substitute σ = .label s := by
  simp [Term.substitute]
@[simp] public theorem subst_boolean (σ : Nat → Term) (b : Bool) :
    (Term.boolean b).substitute σ = .boolean b := by
  simp [Term.substitute]
@[simp] public theorem subst_bound (σ : Nat → Term) (i : Nat) : (Term.bound i).substitute σ = σ i := by
  simp [Term.substitute]
@[simp] public theorem subst_get (σ : Nat → Term) (t : Term) (f : String) :
    (Term.get t f).substitute σ = .get (t.substitute σ) f := by
  simp [Term.substitute]
@[simp] public theorem subst_app (σ : Nat → Term) (a b : Term) :
    (Term.app a b).substitute σ = .app (a.substitute σ) (b.substitute σ) := by
  simp [Term.substitute]
@[simp] public theorem subst_ifBool (σ : Nat → Term) (c x y : Term) :
    (Term.ifBool c x y).substitute σ = .ifBool (c.substitute σ) (x.substitute σ) (y.substitute σ) := by
  simp [Term.substitute]
@[simp] public theorem subst_binary (σ : Nat → Term) (p : Primitive) (a b : Term) :
    (Term.binary p a b).substitute σ = .binary p (a.substitute σ) (b.substitute σ) := by
  simp [Term.substitute]
@[simp] public theorem subst_guard (σ : Nat → Term) (c : Term) (why : String) (rest : Term) :
    (guard c why rest).substitute σ = guard (c.substitute σ) why (rest.substitute σ) := by
  simp [guard]
@[simp] public theorem subst_guards (σ : Nat → Term) : (l : List (Term × String)) → (t : Term) →
    (guards l t).substitute σ = guards (l.map fun p => (p.1.substitute σ, p.2)) (t.substitute σ)
  | [], t => by simp [guards]
  | (c, w) :: r, t => by simp [guards, subst_guards σ r t]
@[simp] public theorem subst_allOf (σ : Nat → Term) (l : List (Term × String)) :
    (allOf l).substitute σ = allOf (l.map fun p => (p.1.substitute σ, p.2)) := by
  simp [allOf]
@[simp] public theorem subst_anyOf (σ : Nat → Term) : (cs : List Term) →
    (anyOf cs).substitute σ = anyOf (cs.map (·.substitute σ))
  | [] => by simp [anyOf]
  | c :: r => by simp [anyOf, subst_anyOf σ r]
@[simp] public theorem subst_andT (σ : Nat → Term) (a b : Term) :
    (andT a b).substitute σ = andT (a.substitute σ) (b.substitute σ) := by simp [andT]
@[simp] public theorem subst_notT (σ : Nat → Term) (a : Term) :
    (notT a).substitute σ = notT (a.substitute σ) := by simp [notT]
@[simp] public theorem subst_eqNat (σ : Nat → Term) (a b : Term) :
    (eqNat a b).substitute σ = eqNat (a.substitute σ) (b.substitute σ) := by simp [eqNat]
@[simp] public theorem subst_eqLabel (σ : Nat → Term) (a b : Term) :
    (eqLabel a b).substitute σ = eqLabel (a.substitute σ) (b.substitute σ) := by simp [eqLabel]
@[simp] public theorem subst_leNat (σ : Nat → Term) (a b : Term) :
    (leNat a b).substitute σ = leNat (a.substitute σ) (b.substitute σ) := by simp [leNat]
@[simp] public theorem subst_ltNat (σ : Nat → Term) (a b : Term) :
    (ltNat a b).substitute σ = ltNat (a.substitute σ) (b.substitute σ) := by simp [ltNat]
@[simp] public theorem subst_addNat (σ : Nat → Term) (a b : Term) :
    (addNat a b).substitute σ = addNat (a.substitute σ) (b.substitute σ) := by simp [addNat]
@[simp] public theorem subst_divNat (σ : Nat → Term) (a b : Term) :
    (divNat a b).substitute σ = divNat (a.substitute σ) (b.substitute σ) := by simp [divNat]
@[simp] public theorem subst_modNat (σ : Nat → Term) (a b : Term) :
    (modNat a b).substitute σ = modNat (a.substitute σ) (b.substitute σ) := by simp [modNat]

/-- The clause environment: payload, request, new state, old state. -/
@[expose] public def armEnv (x o n rq : Term) : Nat → Term := scons x (lawEnv o n rq)

@[simp] public theorem armEnv_0 (x o n rq : Term) : armEnv x o n rq 0 = x := rfl
@[simp] public theorem armEnv_1 (x o n rq : Term) : armEnv x o n rq 1 = rq := rfl
@[simp] public theorem armEnv_2 (x o n rq : Term) : armEnv x o n rq 2 = n := rfl
@[simp] public theorem armEnv_3 (x o n rq : Term) : armEnv x o n rq 3 = o := rfl

@[simp] public theorem at1_old : (⟨1⟩ : At).old = .bound 3 := rfl
@[simp] public theorem at1_new : (⟨1⟩ : At).new = .bound 2 := rfl
@[simp] public theorem at1_req : (⟨1⟩ : At).req = .bound 1 := rfl
@[simp] public theorem at1_payload : (⟨1⟩ : At).payload = .bound 0 := rfl
@[simp] public theorem at_under (d : Nat) : (⟨d⟩ : At).under = ⟨d + 1⟩ := rfl
@[simp] public theorem at_oldF (a : At) (f : String) : a.oldF f = .get a.old f := rfl
@[simp] public theorem at_newF (a : At) (f : String) : a.newF f = .get a.new f := rfl
@[simp] public theorem at_reqF (a : At) (f : String) : a.reqF f = .get a.req f := rfl

/-! ## The combinators -/

public theorem okT_value {v : Term} (h : Evaluates okT v) : v = okT :=
  evaluates_value (.inject _ _) h

public theorem refusedT_not_ok {why : String} {w : Term} : ¬ Evaluates (refusedT why) (.inject "ok" w) := by
  intro h
  have := evaluates_value (.inject _ _) h
  simp [refusedT] at this

public theorem guard_ok {c rest w : Term} {why : String}
    (h : Evaluates (guard c why rest) (.inject "ok" w)) :
    Evaluates c (.boolean true) ∧ Evaluates rest (.inject "ok" w) := by
  obtain ⟨b, hc, hr⟩ := ifBool_inv h
  cases b
  · exact (refusedT_not_ok hr).elim
  · exact ⟨hc, hr⟩

public theorem guards_ok {w : Term} : ∀ {l : List (Term × String)} {rest : Term},
    Evaluates (guards l rest) (.inject "ok" w) →
      (∀ p ∈ l, Evaluates p.1 (.boolean true)) ∧ Evaluates rest (.inject "ok" w)
  | [], _, h => ⟨by simp, h⟩
  | (c, why) :: l, rest, h => by
    obtain ⟨hc, hr⟩ := guard_ok (c := c) (why := why) h
    obtain ⟨hl, hrest⟩ := guards_ok hr
    refine ⟨?_, hrest⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hc
    · exact hl p hp

public theorem allOf_ok {l : List (Term × String)} {w : Term}
    (h : Evaluates (allOf l) (.inject "ok" w)) : ∀ p ∈ l, Evaluates p.1 (.boolean true) :=
  (guards_ok h).1

public theorem anyOf_true : ∀ {cs : List Term}, Evaluates (anyOf cs) (.boolean true) →
    ∃ c ∈ cs, Evaluates c (.boolean true)
  | [], h => by
    have := evaluates_value (.boolean _) h
    simp [anyOf, falseT] at this
  | c :: cs, h => by
    obtain ⟨b, hc, hr⟩ := ifBool_inv h
    cases b
    · obtain ⟨c', hc', h'⟩ := anyOf_true hr
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩
    · exact ⟨c, List.mem_cons_self .., hc⟩

public theorem andT_true {a b : Term} (h : Evaluates (andT a b) (.boolean true)) :
    Evaluates a (.boolean true) ∧ Evaluates b (.boolean true) := by
  obtain ⟨x, ha, hr⟩ := ifBool_inv h
  cases x
  · have := evaluates_value (.boolean _) hr; simp [falseT] at this
  · exact ⟨ha, hr⟩

public theorem notT_true {a : Term} (h : Evaluates (notT a) (.boolean true)) :
    Evaluates a (.boolean false) := by
  obtain ⟨x, ha, hr⟩ := ifBool_inv h
  cases x
  · exact ha
  · have := evaluates_value (.boolean _) hr; simp [falseT] at this

public theorem notT_false {a : Term} (h : Evaluates (notT a) (.boolean false)) :
    Evaluates a (.boolean true) := by
  obtain ⟨x, ha, hr⟩ := ifBool_inv h
  cases x
  · have := evaluates_value (.boolean _) hr; simp [trueT] at this
  · exact ha

/-! ## Primitive conditions -/

public theorem eqLabel_bool {a b : Term} {bo : Bool} (h : Evaluates (eqLabel a b) (.boolean bo)) :
    ∃ s t, Evaluates a (.label s) ∧ Evaluates b (.label t) ∧ decide (s = t) = bo := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, by simpa using hp⟩

public theorem eqLabel_true {a b : Term} (h : Evaluates (eqLabel a b) (.boolean true)) :
    ∃ s, Evaluates a (.label s) ∧ Evaluates b (.label s) := by
  obtain ⟨s, t, ha, hb, hst⟩ := eqLabel_bool h
  simp at hst; subst hst; exact ⟨s, ha, hb⟩

public theorem eqNat_bool {a b : Term} {bo : Bool} (h : Evaluates (eqNat a b) (.boolean bo)) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ decide (m = k) = bo := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, by simpa using hp⟩

public theorem eqNat_true {a b : Term} (h : Evaluates (eqNat a b) (.boolean true)) :
    ∃ m, Evaluates a (.nat m) ∧ Evaluates b (.nat m) := by
  obtain ⟨s, t, ha, hb, hst⟩ := eqNat_bool h
  simp at hst; subst hst; exact ⟨s, ha, hb⟩

public theorem leNat_true {a b : Term} (h : Evaluates (leNat a b) (.boolean true)) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ m ≤ k := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, hp⟩

public theorem ltNat_true {a b : Term} (h : Evaluates (ltNat a b) (.boolean true)) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ m < k := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, hp⟩

public theorem addNat_val {a b v : Term} (h : Evaluates (addNat a b) v) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ v = .nat (m + k) := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, hp.symm⟩

public theorem divNat_val {a b v : Term} (h : Evaluates (divNat a b) v) :
    ∃ m k, Evaluates a (.nat m) ∧ Evaluates b (.nat k) ∧ v = .nat (m / k) := by
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  cases x <;> cases y <;> simp [primitiveResult] at hp
  exact ⟨_, _, hx, hy, hp.symm⟩

public theorem nat_eval {k : Nat} {v : Term} (h : Evaluates (.nat k) v) : v = .nat k :=
  evaluates_value (.natural _) h

public theorem natT_eval {k m : Nat} (h : Evaluates (natT k) (.nat m)) : m = k := by
  have := nat_eval h; simpa using this

/-! ## Data fields -/

public theorem get_nat {d : Data} {f : String} {m : Nat} (h : Evaluates (.get d.term f) (.nat m)) :
    d.field f = some (.natural m) := by
  obtain ⟨e, he, hv⟩ := get_data h
  rw [data_term_nat hv.symm] at he; exact he

public theorem get_label {d : Data} {f : String} {s : String} (h : Evaluates (.get d.term f) (.label s)) :
    d.field f = some (.label s) := by
  obtain ⟨e, he, hv⟩ := get_data h
  rw [data_term_label hv.symm] at he; exact he

public theorem get_inject {d : Data} {f l : String} {p : Term} (h : Evaluates (.get d.term f) (.inject l p)) :
    ∃ x, d.field f = some (.variant l x) ∧ p = x.term := by
  obtain ⟨e, he, hv⟩ := get_data h
  obtain ⟨x, rfl, rfl⟩ := data_term_inject hv.symm
  exact ⟨x, he, rfl⟩

/-! ## The law skeleton -/

/-- A `case` under a substitution: the scrutinee's injection selects an arm, which runs under
`scons payload σ`. -/
public theorem case_subst_inv {s v : Term} {arms : List (String × Term)} {σ : Nat → Term}
    (h : Evaluates ((Term.case s arms).substitute σ) v) :
    ∃ l p body, Evaluates (s.substitute σ) (.inject l p) ∧
      arms.find? (fun arm => arm.1 == l) = some (l, body) ∧ Evaluates (body.substitute (scons p σ)) v := by
  simp only [Term.substitute] at h
  obtain ⟨l, p, body', hs, hf, hb⟩ := case_inv h
  rw [List.find?_map] at hf
  obtain ⟨arm, harm, heq⟩ := Option.map_eq_some_iff.1 hf
  simp only [Prod.mk.injEq] at heq
  obtain ⟨h1, rfl⟩ := heq
  refine ⟨l, p, arm.2, hs, ?_, by rwa [instantiate_lift] at hb⟩
  have : arm = (l, arm.2) := by cases arm; simp_all
  rw [← this]
  simpa [Function.comp_def] using harm

/-- The six arms of `lawCase6`, in `occasionRow`'s order. -/
@[expose] public def arms6 (b ad rl rt wr iv : At → Term) : List (String × Term) :=
  [("adopt", ad ⟨1⟩), ("birth", b ⟨1⟩), ("invoke", iv ⟨1⟩), ("relaw", rl ⟨1⟩),
   ("retire", rt ⟨1⟩), ("write", wr ⟨1⟩)]

/-- **An admitted `lawCase6` ran the arm of the request's occasion**, on its payload. -/
public theorem lawCase6_arm {b ad rl rt wr iv : At → Term} {o n rq x : Data} {ℓ : String} {v : Term}
    (ho : rq.field "occasion" = some (.variant ℓ x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    ∃ body, (arms6 b ad rl rt wr iv).find? (fun arm => arm.1 == ℓ) = some (ℓ, body) ∧
      Evaluates (body.substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨l, p, body, hs, hf, hb⟩ := case_subst_inv h
  simp only [subst_get, subst_bound, lawEnv, scons_zero] at hs
  obtain ⟨y, hy, rfl⟩ := get_inject hs
  rw [ho] at hy
  cases hy
  exact ⟨body, hf, hb⟩

public theorem lawCase6_birth {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "birth" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((b ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

public theorem lawCase6_adopt {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "adopt" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((ad ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

public theorem lawCase6_relaw {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "relaw" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((rl ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

public theorem lawCase6_retire {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "retire" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((rt ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

public theorem lawCase6_write {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "write" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((wr ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

public theorem lawCase6_invoke {b ad rl rt wr iv : At → Term} {o n rq x : Data} {v : Term}
    (ho : rq.field "occasion" = some (.variant "invoke" x))
    (h : Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) v) :
    Evaluates ((iv ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho h
  simp [arms6] at hf; subst hf; exact hb

/-- A write or an invoke runs the change clause of `lawCase`. -/
public theorem lawCase_change {b ad rl rt c : At → Term} {o n rq occ : Data} {v : Term}
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ)
    (h : Evaluates ((lawCase b ad rl rt c).substitute (lawEnv o.term n.term rq.term)) v) :
    ∃ x : Data, Evaluates ((c ⟨1⟩).substitute (armEnv x.term o.term n.term rq.term)) v := by
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨x, lawCase6_write ho h⟩
  · exact ⟨x, lawCase6_invoke ho h⟩

/-- What a law built by `lawOf` admits is what its arm admits. -/
public theorem lawOf_admits {S : Ty} {b ad rl rt c : At → Term} {o n rq : Data}
    (h : Admits (lawOf S b ad rl rt c) o n rq) :
    ∃ w, Evaluates ((lawCase b ad rl rt c).substitute (lawEnv o.term n.term rq.term)) (.inject "ok" w) :=
  (admits_iff _ o n rq).1 h

public theorem lawOf6_admits {b ad rl rt wr iv : At → Term} {o n rq : Data}
    (h : Admits (lawOf6 b ad rl rt wr iv) o n rq) :
    ∃ w, Evaluates ((lawCase6 b ad rl rt wr iv).substitute (lawEnv o.term n.term rq.term)) (.inject "ok" w) :=
  (admits_iff _ o n rq).1 h

/-- When every arm is the same clause, the arm found is that clause. -/
public theorem arms6_const {c : At → Term} {ℓ : String} {body : Term}
    (h : (arms6 c c c c c c).find? (fun arm => arm.1 == ℓ) = some (ℓ, body)) : body = c ⟨1⟩ := by
  have := List.mem_of_find?_eq_some h
  simp [arms6] at this
  rcases this with h | h | h | h | h | h <;> exact h.2

/-! ## Authority -/

/-- **`ownerSigns`**: in every admitted act, of every occasion, the signer IS the principal. -/
public theorem ownerSigns_spec {S : Ty} {o n rq x : Data} {ℓ : String}
    (h : Admits (ownerSigns S) o n rq) (ho : rq.field "occasion" = some (.variant ℓ x)) :
    ∃ s, rq.field "agent" = some (.label s) ∧ rq.field "principal" = some (.label s) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho hw
  rw [arms6_const hf] at hb
  simp at hb
  obtain ⟨s, ha, hp⟩ := eqLabel_true (allOf_ok hb _ (List.mem_singleton_self _))
  exact ⟨s, get_label ha, get_label hp⟩

public theorem listed_true {ids : List String} {rq : Data} {σ : Nat → Term} (hσ : σ 1 = rq.term)
    (h : Evaluates ((listedT ids ⟨1⟩).substitute σ) (.boolean true)) :
    ∃ m ∈ ids, rq.field "agent" = some (.label m) := by
  simp only [listedT, subst_anyOf, List.map_map] at h
  obtain ⟨c, hc, hct⟩ := anyOf_true h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
  simp [hσ] at hct
  obtain ⟨s, ha, hb⟩ := eqLabel_true hct
  have := evaluates_value (.label _) hb
  cases this
  exact ⟨m, hm, get_label ha⟩

/-- **`allowlistLaw`**: every admitted act, of every occasion, is signed by a listed member. -/
public theorem allowlist_spec {S : Ty} {ids : List String} {o n rq x : Data} {ℓ : String}
    (h : Admits (allowlistLaw S ids) o n rq) (ho : rq.field "occasion" = some (.variant ℓ x)) :
    ∃ m ∈ ids, rq.field "agent" = some (.label m) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  obtain ⟨body, hf, hb⟩ := lawCase6_arm ho hw
  rw [arms6_const hf] at hb
  simp only [subst_allOf, List.map_cons, List.map_nil] at hb
  exact listed_true rfl (allOf_ok hb _ (List.mem_singleton_self _))

/-! ## Bounds -/

/-- **`bounded S f max`**: in every admitted birth, adoption, write and invoke, the NEW value of
`f` is a natural at most `max` (so the law cannot be added over a state that already breaks it). -/
public theorem bounded_spec {S : Ty} {f : String} {max : Nat} {o n rq occ : Data}
    (h : Admits (bounded S f max) o n rq) (ho : rq.field "occasion" = some occ)
    (hc : IsChange occ ∨ (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x) :
    ∃ m, n.field f = some (.natural m) ∧ m ≤ max := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  have key : ∀ x : Data,
      Evaluates ((allOf [(leNat ((⟨1⟩ : At).newF f) (natT max), f ++ " over the bound")]).substitute
        (armEnv x.term o.term n.term rq.term)) (.inject "ok" w) →
      ∃ m, n.field f = some (.natural m) ∧ m ≤ max := by
    intro x hx
    simp at hx
    obtain ⟨a, b, ha, hb, hab⟩ := leNat_true (allOf_ok hx _ (List.mem_singleton_self _))
    have := natT_eval hb; subst this
    exact ⟨a, get_nat ha, hab⟩
  rcases hc with hc | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := lawCase_change ho hc hw
    exact key x hx
  · exact key x (lawCase6_birth ho hw)
  · exact key x (lawCase6_adopt ho hw)

/-! ## Machines -/

public theorem isState_true {states : List String} {t : Term} {s : String} {σ : Nat → Term} {d : Data}
    {f : String} (hd : t.substitute σ = .get d.term f)
    (h : Evaluates ((isState states t s).substitute σ) (.boolean true)) :
    ∃ y, d.field f = some (.variant s y) := by
  obtain ⟨l, p, body, hs, hf, hb⟩ := case_subst_inv h
  rw [hd] at hs
  obtain ⟨y, hy, rfl⟩ := get_inject hs
  have hmem := List.mem_of_find?_eq_some hf
  simp only [List.mem_map] at hmem
  obtain ⟨z, _, hz⟩ := hmem
  simp only [Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  simp at hb
  have := evaluates_value (.boolean _) hb
  simp at this
  subst this
  exact ⟨y, hy⟩

/-- The machine's start clause: the new field is the initial state. -/
public theorem machine_start {states : List String} {f initial : String} {n : Data} {σ : Nat → Term} {w : Term}
    (hσ : σ 2 = n.term)
    (h : Evaluates ((allOf [(isState states ((⟨1⟩ : At).newF f) initial, f ++ " does not start at " ++ initial)]).substitute σ)
      (.inject "ok" w)) :
    ∃ y, n.field f = some (.variant initial y) := by
  simp only [subst_allOf, List.map_cons, List.map_nil] at h
  exact isState_true (by simp [hσ]) (allOf_ok h _ (List.mem_singleton_self _))

/-- **A machine starts at its initial state.** -/
public theorem machine_birth {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (h : Admits (machineLaw S f states initial edges) o n rq)
    (ho : rq.field "occasion" = some (.variant "birth" x)) :
    ∃ y, n.field f = some (.variant initial y) := by
  obtain ⟨w, hw⟩ := lawOf6_admits h
  exact machine_start rfl (lawCase6_birth ho hw)

/-- **A machine is adopted only at its initial state.** -/
public theorem machine_adopt {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (h : Admits (machineLaw S f states initial edges) o n rq)
    (ho : rq.field "occasion" = some (.variant "adopt" x)) :
    ∃ y, n.field f = some (.variant initial y) := by
  obtain ⟨w, hw⟩ := lawOf6_admits h
  exact machine_start rfl (lawCase6_adopt ho hw)

/-- **A machine moves only along an edge, by that edge's method.** -/
public theorem machine_invoke {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (h : Admits (machineLaw S f states initial edges) o n rq)
    (ho : rq.field "occasion" = some (.variant "invoke" x)) :
    ∃ e ∈ edges, x = .natural e.2.1 ∧ (∃ y, o.field f = some (.variant e.1 y)) ∧
      ∃ z, n.field f = some (.variant e.2.2 z) := by
  obtain ⟨w, hw⟩ := lawOf6_admits h
  have hb := lawCase6_invoke ho hw
  simp only [subst_allOf, List.map_cons, List.map_nil] at hb
  have ha := allOf_ok hb _ (List.mem_singleton_self _)
  simp only [subst_anyOf, List.map_map] at ha
  obtain ⟨c, hc, hct⟩ := anyOf_true ha
  obtain ⟨⟨a, m, b⟩, he, rfl⟩ := List.mem_map.1 hc
  simp only [Function.comp, subst_andT] at hct
  obtain ⟨h1, h23⟩ := andT_true hct
  obtain ⟨h2, h3⟩ := andT_true h23
  simp at h1
  obtain ⟨m', hx, hm⟩ := eqNat_true h1
  have := natT_eval hm; subst this
  refine ⟨(a, m', b), he, ?_, isState_true (by simp) h2, isState_true (by simp) h3⟩
  have := evaluates_data hx
  exact (data_term_nat this.symm)

public theorem machine_frozen {σ : Nat → Term} {w : Term}
    (h : Evaluates ((refusedT "a machine changes only by its methods").substitute σ) (.inject "ok" w)) : False := by
  simp only [subst_refusedT] at h
  exact refusedT_not_ok h

/-- **A machine admits no write.** -/
public theorem machine_write_refused {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (ho : rq.field "occasion" = some (.variant "write" x)) :
    ¬ Admits (machineLaw S f states initial edges) o n rq := by
  intro h
  obtain ⟨w, hw⟩ := lawOf6_admits h
  exact machine_frozen (lawCase6_write ho hw)

/-- **A machine admits no replacement of laws.** -/
public theorem machine_relaw_refused {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (ho : rq.field "occasion" = some (.variant "relaw" x)) :
    ¬ Admits (machineLaw S f states initial edges) o n rq := by
  intro h
  obtain ⟨w, hw⟩ := lawOf6_admits h
  exact machine_frozen (lawCase6_relaw ho hw)

/-- **A machine admits no retirement**: a machine object is permanent. -/
public theorem machine_retire_refused {S : Ty} {f : String} {states : List String} {initial : String}
    {edges : List (String × Nat × String)} {o n rq x : Data}
    (ho : rq.field "occasion" = some (.variant "retire" x)) :
    ¬ Admits (machineLaw S f states initial edges) o n rq := by
  intro h
  obtain ⟨w, hw⟩ := lawOf6_admits h
  exact machine_frozen (lawCase6_retire ho hw)

/-! ## Quorum -/

public theorem bit_val {t v : Term} {i : Nat} {d : Data} {f : String} (ht : t = .get d.term f)
    (h : Evaluates (bit t i) v) : ∃ a, d.field f = some (.natural a) ∧ v = .nat (a / pow2 i % 2) := by
  subst ht
  obtain ⟨x, y, hx, hy, hp⟩ := binary_inv h
  have := evaluates_value (.natural _) hy; subst this
  obtain ⟨a, b, ha, hb, rfl⟩ := divNat_val hx
  have := natT_eval hb; subst this
  simp [primitiveResult] at hp
  exact ⟨_, get_nat ha, hp.symm⟩

public theorem popcount_fold {d : Data} {f : String} :
    ∀ (l : List Nat) (acc : Term) {p : Nat},
      Evaluates (l.foldl (fun acc j => addNat acc (bit (.get d.term f) j)) acc) (.nat p) →
      ∃ q, Evaluates acc (.nat q) ∧
        (∀ a, d.field f = some (.natural a) → p = l.foldl (fun s j => s + a / pow2 j % 2) q) ∧
        (l ≠ [] → ∃ a, d.field f = some (.natural a))
  | [], acc, p, h => ⟨p, h, fun _ _ => rfl, fun h => (h rfl).elim⟩
  | j :: l, acc, p, h => by
    obtain ⟨q', hq', hl, _⟩ := popcount_fold l _ h
    obtain ⟨u, b, hu, hb, hv⟩ := addNat_val hq'
    cases hv
    obtain ⟨a, ha, hbv⟩ := bit_val rfl hb
    cases hbv
    refine ⟨u, hu, fun a' ha' => ?_, fun _ => ⟨a, ha⟩⟩
    rw [ha] at ha'; cases ha'
    simpa using hl a ha

public theorem subst_bit (σ : Nat → Term) (t : Term) (i : Nat) :
    (bit t i).substitute σ = bit (t.substitute σ) i := by simp [bit]

public theorem subst_fold (σ : Nat → Term) (t : Term) :
    ∀ (l : List Nat) (acc : Term),
      (l.foldl (fun acc j => addNat acc (bit t j)) acc).substitute σ =
        l.foldl (fun acc j => addNat acc (bit (t.substitute σ) j)) (acc.substitute σ)
  | [], acc => rfl
  | j :: l, acc => by
    simp only [List.foldl_cons]
    rw [subst_fold σ t l]
    simp [subst_bit]

public theorem subst_popcount (σ : Nat → Term) (t : Term) (cnt : Nat) :
    (popcount t cnt).substitute σ = popcount (t.substitute σ) cnt := by
  simp [popcount, subst_fold]

/-- The quorum's threshold: `k` set bits among the old approvals. -/
public theorem quorate_true {k cnt : Nat} {o : Data} {σ : Nat → Term} (hσ : σ 3 = o.term) (hc : 0 < cnt)
    (h : Evaluates ((leNat (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") cnt)).substitute σ) (.boolean true)) :
    ∃ a, o.field "approvals" = some (.natural a) ∧ k ≤ popcountNat a cnt := by
  simp only [subst_leNat, subst_natT, subst_popcount, at_oldF, at1_old, subst_get, subst_bound, hσ] at h
  obtain ⟨k', p, hk, hp, hle⟩ := leNat_true h
  have := natT_eval hk; subst this
  obtain ⟨q, hq, hval, hex⟩ := popcount_fold _ _ hp
  have := natT_eval hq; subst this
  obtain ⟨a, ha⟩ := hex (by simp [List.range_eq_nil]; omega)
  refine ⟨a, ha, ?_⟩
  rw [hval a ha] at hle
  exact hle

public theorem member_true {ms : List String} {rq : Data} {σ : Nat → Term} (hσ : σ 1 = rq.term)
    (h : Evaluates ((isMember ms ⟨1⟩).substitute σ) (.boolean true)) :
    ∃ m ∈ ms, rq.field "agent" = some (.label m) :=
  listed_true hσ h

public theorem fresh_approvals {n : Data} {σ : Nat → Term} {w : Term} (hσ : σ 2 = n.term)
    (h : Evaluates ((allOf [(eqNat ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals at birth")]).substitute σ)
      (.inject "ok" w)) :
    n.field "approvals" = some (.natural 0) := by
  simp only [subst_allOf, List.map_cons, List.map_nil] at h
  have hc := allOf_ok h _ (List.mem_singleton_self _)
  simp [hσ] at hc
  obtain ⟨m, ha, hb⟩ := eqNat_true hc
  have := natT_eval hb; subst this
  exact get_nat ha

/-- **Quorum at birth**: an admitted birth starts with no approvals. -/
public theorem quorum_birth_empty {S T : Ty} {ms : List String} {k : Nat} {g : String} {o n rq x : Data}
    (h : Admits (quorumLaw S T ms k g) o n rq) (ho : rq.field "occasion" = some (.variant "birth" x)) :
    n.field "approvals" = some (.natural 0) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  exact fresh_approvals rfl (lawCase6_birth ho hw)

/-- **Quorum at its adoption is fresh**: the quorum can be added over a state only if that state
has no approvals (approvals written under the previous laws prove nothing, LANG-24). -/
public theorem quorum_adopt_fresh {S T : Ty} {ms : List String} {k : Nat} {g : String} {o n rq x : Data}
    (h : Admits (quorumLaw S T ms k g) o n rq) (ho : rq.field "occasion" = some (.variant "adopt" x)) :
    n.field "approvals" = some (.natural 0) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  exact fresh_approvals rfl (lawCase6_adopt ho hw)

/-- **A quorum admits no retirement.** -/
public theorem quorum_retire_refused {S T : Ty} {ms : List String} {k : Nat} {g : String} {o n rq x : Data}
    (ho : rq.field "occasion" = some (.variant "retire" x)) : ¬ Admits (quorumLaw S T ms k g) o n rq := by
  intro h
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  have hb := lawCase6_retire ho hw
  simp only [subst_refusedT] at hb
  exact refusedT_not_ok hb

/-- **Quorum at a relaw**: an admitted replacement of the laws is by a member, with `k` approvals
among the old ones, of exactly the incoming laws. -/
public theorem quorum_relaw_needs_k {S T : Ty} {ms : List String} {k : Nat} {g : String} {o n rq x : Data}
    (h : Admits (quorumLaw S T ms k g) o n rq) (ho : rq.field "occasion" = some (.variant "relaw" x)) :
    (∃ m ∈ ms, rq.field "agent" = some (.label m)) ∧
      (∃ a, o.field "approvals" = some (.natural a) ∧ k ≤ popcountNat a ms.length) ∧
      ∃ L, x = .label L ∧ ∃ y, o.field "proposal" = some (.variant "laws" y) ∧ y = .label L := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  have hb := lawCase6_relaw ho hw
  simp only [subst_guards, subst_allOf, List.map_cons, List.map_nil] at hb
  obtain ⟨hm, hrest⟩ := guards_ok hb
  have hmem := member_true rfl (hm _ (List.mem_singleton_self _))
  obtain ⟨m, hmm, _⟩ := id hmem
  have hpos : 0 < ms.length := List.length_pos_of_mem hmm
  refine ⟨hmem, quorate_true rfl hpos (allOf_ok hrest _ (List.mem_cons_self ..)), ?_⟩
  have hp := allOf_ok hrest _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain ⟨l, p, body, hs, hf, hbody⟩ := case_subst_inv hp
  simp at hs
  obtain ⟨y, hy, rfl⟩ := get_inject hs
  have hmem2 := List.mem_of_find?_eq_some hf
  simp at hmem2
  rcases hmem2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [proposedLaws, At.payload] at hbody
    obtain ⟨L, h1, h2⟩ := eqLabel_true hbody
    have e1 := data_term_label (evaluates_data h1).symm
    have e2 := data_term_label (evaluates_data h2).symm
    exact ⟨L, e2, y, hy, e1⟩
  · simp only [falseT, subst_boolean] at hbody
    have := evaluates_value (.boolean _) hbody
    simp at this

public theorem subst_eqAt (σ : Nat → Term) (T : Ty) (a b : Term) :
    (eqAt T a b).substitute σ = eqAt T (a.substitute σ) (b.substitute σ) := by
  cases T <;> simp [eqAt]

/-- `eqAt` that says `true` of two terms: both evaluate to one scalar. -/
public theorem eqAt_true {T : Ty} {a b : Term} (h : Evaluates (eqAt T a b) (.boolean true)) :
    ∃ v, Evaluates a v ∧ Evaluates b v ∧ ((∃ m, v = .nat m) ∨ (∃ s, v = .label s) ∨ ∃ c, v = .boolean c) := by
  cases T with
  | label =>
      obtain ⟨s, ha, hb⟩ := eqLabel_true h
      exact ⟨_, ha, hb, .inr (.inl ⟨s, rfl⟩)⟩
  | boolean =>
      obtain ⟨c, ha, hr⟩ := ifBool_inv h
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte] at hr
        exact ⟨_, ha, notT_true hr, .inr (.inr ⟨false, rfl⟩)⟩
      · simp only [↓reduceIte] at hr
        exact ⟨_, ha, hr, .inr (.inr ⟨true, rfl⟩)⟩
  | _ =>
      obtain ⟨m, ha, hb⟩ := eqNat_true h
      exact ⟨_, ha, hb, .inl ⟨m, rfl⟩⟩

/-- `eqAt` of the new and old value of a field, `true`: the field is unchanged. -/
public theorem eqAt_fields_true {T : Ty} {g : String} {o n : Data}
    (h : Evaluates (eqAt T (.get n.term g) (.get o.term g)) (.boolean true)) : n.field g = o.field g := by
  obtain ⟨v, ha, hb, hs⟩ := eqAt_true h
  obtain ⟨e1, h1, rfl⟩ := get_data ha
  obtain ⟨e2, h2, he⟩ := get_data hb
  rw [h1, h2]
  congr 1
  rcases hs with ⟨m, hm⟩ | ⟨s, hm⟩ | ⟨c, hm⟩
  · rw [data_term_nat hm, data_term_nat (he.symm.trans hm)]
  · rw [data_term_label hm, data_term_label (he.symm.trans hm)]
  · rw [data_term_boolean hm, data_term_boolean (he.symm.trans hm)]

/-- **The commit needs k**: an admitted write or invoke that changes the guarded field is by a
member, with `k` approvals among the old ones, and resets the approvals. -/
public theorem quorum_change_needs_k {S T : Ty} {ms : List String} {k : Nat} {g : String} {o n rq occ : Data}
    (h : Admits (quorumLaw S T ms k g) o n rq) (ho : rq.field "occasion" = some occ) (hc : IsChange occ)
    (hne : n.field g ≠ o.field g) :
    (∃ m ∈ ms, rq.field "agent" = some (.label m)) ∧
      (∃ a, o.field "approvals" = some (.natural a) ∧ k ≤ popcountNat a ms.length) ∧
      n.field "approvals" = some (.natural 0) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  obtain ⟨x, hx⟩ := lawCase_change ho hc hw
  simp only [subst_guards, List.map_cons, List.map_nil] at hx
  obtain ⟨hm, hrest⟩ := guards_ok hx
  have hmem := member_true rfl (hm _ (List.mem_cons_self ..))
  obtain ⟨m, hmm, _⟩ := id hmem
  have hpos : 0 < ms.length := List.length_pos_of_mem hmm
  simp only [subst_ifBool, subst_notT, subst_eqAt] at hrest
  obtain ⟨b, hb, hr⟩ := ifBool_inv hrest
  cases b
  · have := eqAt_fields_true (by simpa using notT_false hb)
    exact (hne this).elim
  · simp only [↓reduceIte, subst_allOf, List.map_cons, List.map_nil] at hr
    refine ⟨hmem, quorate_true rfl hpos (allOf_ok hr _ (List.mem_cons_self ..)), ?_⟩
    have hz := allOf_ok hr _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    simp at hz
    obtain ⟨z, ha, hb⟩ := eqNat_true hz
    have := natT_eval hb; subst this
    exact get_nat ha

/-! ## Windowed -/

public theorem div_req {rq : Data} {f : String} {W : Nat} {v : Term} {σ : Nat → Term} (hσ : σ 1 = rq.term)
    (h : Evaluates ((divNat ((⟨1⟩ : At).reqF f) (natT W)).substitute σ) v) :
    ∃ a, rq.field f = some (.natural a) ∧ v = .nat (a / W) := by
  simp [hσ] at h
  obtain ⟨a, b, ha, hb, rfl⟩ := divNat_val h
  have := natT_eval hb; subst this
  exact ⟨a, get_nat ha, rfl⟩

/-- The window facts: the call's window lies in one epoch of width `W`, and the new state's epoch is
that one. -/
public theorem inOneEpoch_true {W : Nat} {n rq : Data} {σ : Nat → Term} (h1 : σ 1 = rq.term) (h2 : σ 2 = n.term)
    (h : ∀ p ∈ (inOneEpoch W ⟨1⟩).map (fun p => (p.1.substitute σ, p.2)), Evaluates p.1 (.boolean true)) :
    ∃ nb vu, rq.field "notBefore" = some (.natural nb) ∧ rq.field "validUntil" = some (.natural vu) ∧
      vu / W = nb / W ∧ n.field "epoch" = some (.natural (nb / W)) := by
  simp only [inOneEpoch, List.map_cons, List.map_nil, List.forall_mem_cons, subst_eqNat] at h
  obtain ⟨hA, hB, -⟩ := h
  obtain ⟨m, hvu, hnb⟩ := eqNat_true hA
  obtain ⟨vu, hvu', e1⟩ := div_req h1 hvu
  obtain ⟨nb, hnb', e2⟩ := div_req h1 hnb
  obtain ⟨m', hep, hnb2⟩ := eqNat_true hB
  obtain ⟨nb', hnb'', e3⟩ := div_req h1 hnb2
  rw [hnb'] at hnb''; cases hnb''
  simp [h2] at hep
  injection e1 with e1; injection e2 with e2; injection e3 with e3
  refine ⟨nb, vu, hnb', hvu', by omega, ?_⟩
  rw [← e3]
  exact get_nat hep

/-- **Windowed lands in the call's epoch**: every admitted birth, adoption, write and invoke has a
signed window inside one epoch of width `W`, and the new state's epoch is that one. -/
public theorem windowed_lands_in_epoch {S T : Ty} {W limit : Nat} {g : String} {o n rq occ : Data}
    (h : Admits (windowedLaw S T W limit g) o n rq) (ho : rq.field "occasion" = some occ)
    (hc : IsChange occ ∨ (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x) :
    ∃ nb vu, rq.field "notBefore" = some (.natural nb) ∧ rq.field "validUntil" = some (.natural vu) ∧
      vu / W = nb / W ∧ n.field "epoch" = some (.natural (nb / W)) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  have fresh : ∀ x : Data, Evaluates ((guards (inOneEpoch W ⟨1⟩)
      (allOf [(eqNat ((⟨1⟩ : At).newF "count") (natT 0), "count at birth")])).substitute
        (armEnv x.term o.term n.term rq.term)) (.inject "ok" w) → _ := fun x hx => by
    rw [subst_guards] at hx
    exact inOneEpoch_true rfl rfl (guards_ok hx).1
  rcases hc with hc | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hx := lawCase6_write ho hw
      rw [subst_guards] at hx
      exact inOneEpoch_true rfl rfl (guards_ok hx).1
    · have hx := lawCase6_invoke ho hw
      rw [subst_guards] at hx
      exact inOneEpoch_true rfl rfl (guards_ok hx).1
  · exact fresh x (lawCase6_birth ho hw)
  · exact fresh x (lawCase6_adopt ho hw)

/-- **Windowed starts at zero**: an admitted birth or adoption has `count = 0`. -/
public theorem windowed_fresh {S T : Ty} {W limit : Nat} {g : String} {o n rq occ : Data}
    (h : Admits (windowedLaw S T W limit g) o n rq) (ho : rq.field "occasion" = some occ)
    (hc : (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x) :
    n.field "count" = some (.natural 0) := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  have key : ∀ x : Data, Evaluates ((guards (inOneEpoch W ⟨1⟩)
      (allOf [(eqNat ((⟨1⟩ : At).newF "count") (natT 0), "count at birth")])).substitute
        (armEnv x.term o.term n.term rq.term)) (.inject "ok" w) → n.field "count" = some (.natural 0) := by
    intro x hx
    rw [subst_guards] at hx
    have hr := (guards_ok hx).2
    simp only [subst_allOf, List.map_cons, List.map_nil] at hr
    have hc := allOf_ok hr _ (List.mem_singleton_self _)
    simp at hc
    obtain ⟨m, ha, hb⟩ := eqNat_true hc
    have := natT_eval hb; subst this
    exact get_nat ha
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact key x (lawCase6_birth ho hw)
  · exact key x (lawCase6_adopt ho hw)

/-- **Windowed is a rate limit**: in an admitted write or invoke the new `count` is at most `limit`. -/
public theorem windowed_limit {S T : Ty} {W limit : Nat} {g : String} {o n rq occ : Data}
    (h : Admits (windowedLaw S T W limit g) o n rq) (ho : rq.field "occasion" = some occ)
    (hc : IsChange occ) : ∃ c, n.field "count" = some (.natural c) ∧ c ≤ limit := by
  obtain ⟨w, hw⟩ := lawOf_admits (S := S) h
  obtain ⟨x, hx⟩ := lawCase_change ho hc hw
  rw [subst_guards] at hx
  have hr := (guards_ok hx).2
  simp only [subst_ifBool, subst_allOf, List.map_cons, List.map_nil] at hr
  obtain ⟨b, _, hb⟩ := ifBool_inv hr
  have hle : Evaluates ((leNat ((⟨1⟩ : At).newF "count") (natT limit)).substitute
      (armEnv x.term o.term n.term rq.term)) (.boolean true) := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hb
      exact allOf_ok hb _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · simp only [↓reduceIte] at hb
      exact allOf_ok hb _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp at hle
  obtain ⟨c, l, hc', hl, hcl⟩ := leNat_true hle
  have := natT_eval hl; subst this
  exact ⟨c, get_nat hc', hcl⟩

/-! ## Teeth

Each meaning theorem above has a hypothesis `Admits …`; the teeth show it is inhabited (a concrete
admission, run through `run` by the kernel and read back by `admits_of_run`) and that the law is
not trivially `ok` (a concrete refusal with the named reason, `refuses_of_run`). -/

/-- A request by `agent` under `principal`'s authority, window `[0, 9]`. -/
@[expose] public def rqBy (agent principal : String) (occasion : Data) : Data :=
  request agent principal 0 9 occasion

@[expose] public def totalIs (k : Nat) : Data := .record [("total", .natural k)]

public theorem ownerSigns_tooth :
    Admits (ownerSigns unitTy) (totalIs 0) (totalIs 1) (rqBy "ann" "ann" writeO) ∧
      Refuses (ownerSigns unitTy) (totalIs 0) (totalIs 1) (rqBy "bob" "ann" writeO) "not signed by the owner" :=
  ⟨admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel)⟩

public theorem allowlist_tooth :
    Admits (allowlistLaw unitTy ["ann", "bob"]) (totalIs 0) (totalIs 1) (rqBy "bob" "ann" (relawO "L")) ∧
      Refuses (allowlistLaw unitTy ["ann", "bob"]) (totalIs 0) (totalIs 1) (rqBy "eve" "ann" birthO)
        "not on the allowlist" :=
  ⟨admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel)⟩

public theorem bounded_tooth :
    Admits (bounded unitTy "total" 5) (totalIs 1) (totalIs 5) (rqBy "ann" "ann" (invokeO 0)) ∧
      Refuses (bounded unitTy "total" 5) (totalIs 1) (totalIs 6) (rqBy "ann" "ann" (adoptO "L"))
        "total over the bound" ∧
      Admits (bounded unitTy "total" 5) (totalIs 9) (totalIs 9) (rqBy "ann" "ann" retireO) :=
  ⟨admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel),
    admits_of_run 200 (by decide +kernel)⟩

/-- A door: `shut --open--> open --close--> shut`, methods `open` (0) and `close` (1). -/
@[expose] public def doorLaw : Term :=
  machineLaw unitTy "door" ["open", "shut"] "shut" [("shut", 0, "open"), ("open", 1, "shut")]

@[expose] public def door (s : String) : Data := .record [("door", .variant s (.record []))]

public theorem machine_tooth :
    Admits doorLaw (door "shut") (door "shut") (rqBy "ann" "ann" birthO) ∧
      Refuses doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (adoptO "L")) "door does not start at shut" ∧
      Admits doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (invokeO 0)) ∧
      Refuses doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (invokeO 1)) "no edge" ∧
      Refuses doorLaw (door "shut") (door "shut") (rqBy "ann" "ann" writeO) "a machine changes only by its methods" :=
  ⟨admits_of_run 400 (by decide +kernel), refuses_of_run 400 (by decide +kernel),
    admits_of_run 400 (by decide +kernel), refuses_of_run 400 (by decide +kernel),
    refuses_of_run 400 (by decide +kernel)⟩

/-- Three members, two approvals needed, guarding `total`. -/
@[expose] public def councilLaw : Term := quorumLaw unitTy .natural ["ann", "bob", "cy"] 2 "total"

@[expose] public def council (total approvals : Nat) (proposal : Data) : Data :=
  .record [("approvals", .natural approvals), ("proposal", proposal), ("total", .natural total)]

public theorem quorum_tooth :
    Admits councilLaw (council 0 0 (.variant "set" (.natural 0))) (council 0 0 (.variant "set" (.natural 0)))
      (rqBy "ann" "ann" birthO) ∧
      Refuses councilLaw (council 0 3 (.variant "set" (.natural 0))) (council 0 3 (.variant "set" (.natural 0)))
        (rqBy "ann" "ann" (adoptO "L")) "approvals at birth" ∧
      Admits councilLaw (council 0 3 (.variant "laws" (.label "L"))) (council 0 3 (.variant "laws" (.label "L")))
        (rqBy "bob" "ann" (relawO "L")) ∧
      Refuses councilLaw (council 0 1 (.variant "laws" (.label "L"))) (council 0 1 (.variant "laws" (.label "L")))
        (rqBy "bob" "ann" (relawO "L")) "no quorum" ∧
      Refuses councilLaw (council 0 3 (.variant "laws" (.label "L"))) (council 0 3 (.variant "laws" (.label "M")))
        (rqBy "bob" "ann" (relawO "M")) "not the proposal" ∧
      Admits councilLaw (council 0 1 (.variant "set" (.natural 7))) (council 0 3 (.variant "set" (.natural 7)))
        (rqBy "bob" "ann" writeO) ∧
      Admits councilLaw (council 0 3 (.variant "set" (.natural 7))) (council 7 0 (.variant "set" (.natural 7)))
        (rqBy "cy" "ann" writeO) ∧
      Refuses councilLaw (council 0 1 (.variant "set" (.natural 7))) (council 7 0 (.variant "set" (.natural 7)))
        (rqBy "cy" "ann" writeO) "no quorum" ∧
      Refuses councilLaw (council 0 0 (.variant "set" (.natural 0))) (council 0 0 (.variant "set" (.natural 0)))
        (rqBy "ann" "ann" retireO) "quorum" :=
  ⟨admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    refuses_of_run 2000 (by decide +kernel), admits_of_run 2000 (by decide +kernel),
    admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    refuses_of_run 2000 (by decide +kernel)⟩

/-- At most one change of `total` per epoch of 10 heights. -/
@[expose] public def rateLaw : Term := windowedLaw unitTy .natural 10 1 "total"

@[expose] public def rated (total count epoch : Nat) : Data :=
  .record [("count", .natural count), ("epoch", .natural epoch), ("total", .natural total)]

public theorem windowed_tooth :
    Admits rateLaw (rated 0 0 0) (rated 0 0 0) (rqBy "ann" "ann" birthO) ∧
      Admits rateLaw (rated 0 0 0) (rated 1 1 0) (rqBy "ann" "ann" writeO) ∧
      Refuses rateLaw (rated 1 1 0) (rated 2 2 0) (rqBy "ann" "ann" writeO) "over the rate limit" ∧
      Refuses rateLaw (rated 0 0 0) (rated 0 0 0) (request "ann" "ann" 5 15 birthO) "window spans epochs" ∧
      Refuses rateLaw (rated 0 1 0) (rated 0 1 0) (rqBy "ann" "ann" (adoptO "L")) "count at birth" :=
  ⟨admits_of_run 1000 (by decide +kernel), admits_of_run 1000 (by decide +kernel),
    refuses_of_run 1000 (by decide +kernel), refuses_of_run 1000 (by decide +kernel),
    refuses_of_run 1000 (by decide +kernel)⟩

#assert_axioms subst_okT subst_refusedT subst_guard subst_guards subst_allOf subst_anyOf
  okT_value refusedT_not_ok guard_ok guards_ok allOf_ok anyOf_true andT_true notT_true notT_false
  eqLabel_bool eqLabel_true eqNat_bool eqNat_true leNat_true ltNat_true addNat_val divNat_val
  get_nat get_label get_inject case_subst_inv lawCase6_arm lawCase6_birth lawCase6_adopt
  lawCase6_relaw lawCase6_retire lawCase6_write lawCase6_invoke lawCase_change lawOf_admits
  lawOf6_admits arms6_const
  ownerSigns_spec listed_true allowlist_spec bounded_spec isState_true machine_start machine_birth
  machine_adopt machine_invoke machine_write_refused machine_relaw_refused machine_retire_refused
  bit_val popcount_fold subst_popcount quorate_true member_true fresh_approvals quorum_birth_empty
  quorum_adopt_fresh quorum_retire_refused quorum_relaw_needs_k subst_eqAt eqAt_true eqAt_fields_true
  quorum_change_needs_k div_req inOneEpoch_true
  windowed_lands_in_epoch windowed_fresh windowed_limit
  ownerSigns_tooth allowlist_tooth bounded_tooth machine_tooth quorum_tooth windowed_tooth

end Obend.Law
