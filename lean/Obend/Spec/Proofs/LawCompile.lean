module
/-
# Obend.Spec.Proofs.LawCompile — the compiled law means what the fragment says, and has its type

For the declared state type `S` and every state that fits `S` at the fields the law reads
(`Fits`), the compiled law `compile S name e` (`Obend.Spec.LawCompile`) evaluates, under Core4's
reference semantics, to `ok` exactly when the fragment's meaning `LawExpr.denote` holds and to
`refused name` exactly when it does not:

* `compile_change`: a write or an invoke, judged with the old state;
* `compile_first`: a birth or an adoption, judged as a first write (no old state);
* `compile_inert`: a relaw or a retirement, admitted;

and so `compile_admits_*` / `compile_refuses_*` state `Admits` and `Refuses` as iffs with
`denote`. Each is proved by building the evaluation (`cond_eval`: the condition evaluates to the
boolean `denote` computes), not by evaluating a term. `compile_checks`: the compiled law checks at
`lawTy S` under `Bidirectional.checkAgainst`, with no annotations, for every canonical shareable
`S` (`Obend.Law.Proofs.Typing`).
-/
public import Obend.Spec.LawCompile
public import Obend.Law.Proofs.Std
public import Obend.Law.Proofs.Typing
public import Obend.AxiomPin
namespace Obend.Spec.LawCompile
open Obend.Law
open Obend.Law.Typing
open Obend.Spec.Law (LawRef LawExpr Facts scalarOf firstScalarField fieldOf)
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data fieldsTerm)
set_option autoImplicit false

/-! ## Building evaluations -/

theorem steps_binL {p : Primitive} {l l' r : Term} (h : Steps l l') : Steps (.binary p l r) (.binary p l' r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft _ _ s) ih

theorem steps_binR {p : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary p l r) (.binary p l r') := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight _ _ hl s) ih

theorem ev_binary {p : Primitive} {l r lv rv v : Term} (hl : Evaluates l lv) (hr : Evaluates r rv)
    (hp : primitiveResult p lv rv = some v) : Evaluates (.binary p l r) v :=
  evaluates_steps (steps_trans (steps_binL hl.1) (steps_binR hl.2 hr.1))
    (evaluates_step (.primitive _ _ _ _ hl.2 hr.2 hp) (evaluates_self (primitiveResult_value hp)))

theorem find_fieldsTerm (f : String) : (fs : List (String × Data)) →
    (fieldsTerm fs).find? (fun field => field.1 == f) = (fieldsLookup f fs).map (fun d => (f, d.term))
  | [] => by simp [fieldsTerm, fieldsLookup]
  | (g, d) :: rest => by
      simp only [fieldsTerm, fieldsLookup, List.find?_cons]
      by_cases h : g = f
      · subst h; simp
      · have : (g == f) = false := by simp [h]
        simp only [this]
        exact find_fieldsTerm f rest

/-- A field of data, selected, evaluates to the field. -/
theorem ev_get {d e : Data} {f : String} (h : d.field f = some e) : Evaluates (.get d.term f) e.term := by
  cases d with
  | record fs =>
    have hf : (fieldsTerm fs).find? (fun field => field.1 == f) = some (f, e.term) := by
      rw [find_fieldsTerm]; simp only [Data.field] at h; simp [h]
    exact evaluates_step (.field _ _ _ hf) (evaluates_self (data_value e))
  | _ => simp [Data.field] at h

theorem ev_bool (b : Bool) : Evaluates (.boolean b) (.boolean b) := evaluates_self (.boolean b)
theorem ev_nat (k : Nat) : Evaluates (.nat k) (.nat k) := evaluates_self (.natural k)

theorem ev_andT {a b : Term} {x y : Bool} (ha : Evaluates a (.boolean x))
    (hb : x = true → Evaluates b (.boolean y)) : Evaluates (andT a b) (.boolean (x && y)) := by
  cases x
  · exact evaluates_ifBool ha (ev_bool false)
  · exact evaluates_ifBool ha (hb rfl)

theorem ev_notT {a : Term} {x : Bool} (ha : Evaluates a (.boolean x)) : Evaluates (notT a) (.boolean (!x)) := by
  cases x
  · exact evaluates_ifBool ha (ev_bool true)
  · exact evaluates_ifBool ha (ev_bool false)

theorem ev_orT {a b : Term} {x y : Bool} (ha : Evaluates a (.boolean x)) (hb : Evaluates b (.boolean y)) :
    Evaluates (orT a b) (.boolean (x || y)) := by
  cases x
  · exact evaluates_ifBool ha hb
  · exact evaluates_ifBool ha (ev_bool true)

theorem ev_impliesT {a b : Term} {x y : Bool} (ha : Evaluates a (.boolean x)) (hb : Evaluates b (.boolean y)) :
    Evaluates (impliesT a b) (.boolean (!x || y)) := by
  cases x
  · exact evaluates_ifBool ha (ev_bool true)
  · exact evaluates_ifBool ha hb

theorem ev_anyOf {α : Type} {g : α → Term} {P : α → Bool} : ∀ {l : List α},
    (∀ c ∈ l, Evaluates (g c) (.boolean (P c))) → Evaluates (anyOf (l.map g)) (.boolean (l.any P))
  | [], _ => ev_bool false
  | c :: l, h => by
    have hc := h c List.mem_cons_self
    have hl := ev_anyOf (l := l) fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    simp only [List.map_cons, anyOf, List.any_cons]
    cases hp : P c
    · rw [hp] at hc; exact evaluates_ifBool hc hl
    · rw [hp] at hc; exact evaluates_ifBool hc (ev_bool true)

theorem ev_eqNat {a b : Term} {m k : Nat} (ha : Evaluates a (.nat m)) (hb : Evaluates b (.nat k)) :
    Evaluates (eqNat a b) (.boolean (m == k)) := ev_binary ha hb rfl
theorem ev_leNat {a b : Term} {m k : Nat} (ha : Evaluates a (.nat m)) (hb : Evaluates b (.nat k)) :
    Evaluates (leNat a b) (.boolean (decide (m ≤ k))) := ev_binary ha hb rfl
theorem ev_addNat {a b : Term} {m k : Nat} (ha : Evaluates a (.nat m)) (hb : Evaluates b (.nat k)) :
    Evaluates (addNat a b) (.nat (m + k)) := ev_binary ha hb rfl

/-- A `case` under a substitution, built forward: the scrutinee's injection selects the arm. -/
theorem ev_case_subst {s : Term} {arms : List (String × Term)} {σ : Nat → Term} {l : String}
    {p body v : Term} (hs : Evaluates (s.substitute σ) (.inject l p))
    (hf : arms.find? (fun arm => arm.1 == l) = some (l, body))
    (h : Evaluates (body.substitute (scons p σ)) v) : Evaluates ((Term.case s arms).substitute σ) v := by
  simp only [Term.substitute]
  refine evaluates_case hs ?_ (by rw [instantiate_lift]; exact h)
  rw [List.find?_map]
  simp only [Function.comp_def]
  rw [hf]; rfl

/-! ## Readings -/

theorem firstScalar_of_lookup {f : String} {d : Data} {v : Int} (hv : scalarOf d = some v) :
    ∀ {fs : List (String × Data)}, fieldsLookup f fs = some d → firstScalarField f fs = some v
  | (g, d') :: rest, h => by
    simp only [fieldsLookup] at h
    by_cases hg : g = f
    · subst hg; simp only [beq_self_eq_true, ite_true, Option.some.injEq] at h; subst h
      simp [firstScalarField, hv]
    · have : (g == f) = false := by simp [hg]
      rw [this] at h; simp only [Bool.false_eq_true, ite_false] at h
      simp only [firstScalarField, hg, ite_false]
      exact firstScalar_of_lookup hv h

theorem kind_member {S : Ty} {f : String} {k : Kind} (h : fieldKind S f = some k) :
    Obend.Core.Bidirectional.rowMember S f = some (match k with | .nat => .natural | .bool => .boolean) := by
  unfold fieldKind at h
  split at h
  · rename_i heq; cases h; exact heq
  · rename_i heq; cases h; exact heq
  · cases h

@[simp] theorem subst_scalarRead (σ : Nat → Term) (k : Kind) (t : Term) :
    (scalarRead k t).substitute σ = scalarRead k (t.substitute σ) := by
  cases k <;> simp only [scalarRead, subst_ifBool, subst_natT]

/-- A field `S` reads as a scalar: present in fitting data, and its term evaluates to the
natural `scalarOf` reads. -/
theorem field_read {S : Ty} {f : String} {k : Kind} {fs : List (String × Data)} (hk : fieldKind S f = some k)
    (hfit : fitsField S fs f = true) :
    ∃ m : Nat, fieldOf f (.record fs) = some (Int.ofNat m) ∧
      Evaluates (scalarRead k (.get (Data.record fs).term f)) (.nat m) := by
  unfold fitsField at hfit
  rw [hk] at hfit
  cases k with
  | nat =>
    split at hfit <;> simp_all
    rename_i m hl
    exact ⟨m, firstScalar_of_lookup rfl hl, ev_get (e := .natural m) (by simp [Data.field, hl])⟩
  | bool =>
    split at hfit <;> simp_all
    rename_i b hl
    refine ⟨if b then 1 else 0, ?_, ?_⟩
    · simp only [fieldOf]; rw [firstScalar_of_lookup rfl hl]; cases b <;> rfl
    · refine evaluates_ifBool (ev_get (e := .boolean b) (by simp [Data.field, hl])) ?_
      cases b <;> exact ev_nat _

theorem field_absent {S : Ty} {f : String} {fs : List (String × Data)} (hk : fieldKind S f = none)
    (hfit : fitsField S fs f = true) : fieldOf f (.record fs) = none := by
  unfold fitsField at hfit
  rw [hk] at hfit
  simpa [fieldOf] using hfit

/-- The environment of a clause at depth `d`: the request, the new state, the old state. -/
@[expose] public def EnvAt (d : Nat) (σ : Nat → Term) (o n rq : Data) : Prop :=
  σ d = rq.term ∧ σ (d + 1) = n.term ∧ σ (d + 2) = o.term

theorem req_field_opt {ag pr : String} {nb vu : Nat} {occ : Data} {facts : Facts} :
    (reqOf ag pr nb vu occ facts).field "subject" = some (optNat facts.subject) ∧
      (reqOf ag pr nb vu occ facts).field "caller" = some (optNat facts.caller) ∧
      (reqOf ag pr nb vu occ facts).field "height" = some (.natural facts.height) ∧
      (reqOf ag pr nb vu occ facts).field "turn" = some (.natural facts.turn) ∧
      (reqOf ag pr nb vu occ facts).field "occasion" = some occ := by
  simp [reqOf, requestAt, Data.field, fieldsLookup]

theorem opt_read {t : Term} {σ : Nat → Term} {x : Option Nat} (ht : Evaluates (t.substitute σ) (optNat x).term) :
    Evaluates ((optRead t).present.substitute σ) (.boolean x.isSome) ∧
      ∀ m, x = some m → Evaluates ((optRead t).value.substitute σ) (.nat m) := by
  cases x with
  | none =>
    refine ⟨ev_case_subst ht rfl ?_, fun _ h => by cases h⟩
    simp only [subst_falseT]; exact ev_bool false
  | some k =>
    refine ⟨ev_case_subst ht rfl ?_, fun m h => ?_⟩
    · simp only [subst_trueT]; exact ev_bool true
    · cases h
      exact ev_case_subst ht rfl (by simp only [subst_bound, scons_zero]; exact ev_nat k)

/-- **What a reference reads**: an optional natural `ro` that `LawRef.read` agrees with, a
presence term evaluating to whether it is there, and a value term evaluating to it. -/
theorem read_spec {S : Ty} {d : Nat} {σ : Nat → Term} {o rq : Data} {fs : List (String × Data)}
    {ag pr : String} {nb vu : Nat} {occ : Data} {facts : Facts} (r : LawRef)
    (hσ : EnvAt d σ o (.record fs) rq) (hrq : rq = reqOf ag pr nb vu occ facts)
    (hfit : ∀ f ∈ r.fields, fitsField S fs f = true) :
    ∃ ro : Option Nat, r.read facts (.record fs) = ro.map Int.ofNat ∧
      Evaluates ((refRead S ⟨d⟩ r).present.substitute σ) (.boolean ro.isSome) ∧
      ∀ m, ro = some m → Evaluates ((refRead S ⟨d⟩ r).value.substitute σ) (.nat m) := by
  obtain ⟨h0, h1, _⟩ := hσ
  obtain ⟨hs, hc, hh, ht, _⟩ := req_field_opt (ag := ag) (pr := pr) (nb := nb) (vu := vu) (occ := occ) (facts := facts)
  subst hrq
  cases r with
  | field f =>
    have hf := hfit f (by simp [LawRef.fields])
    cases hk : fieldKind S f with
    | none =>
      refine ⟨none, by simp [LawRef.read, field_absent hk hf], ?_, fun _ h => by cases h⟩
      simp only [refRead, fieldRead, hk, subst_falseT]; exact ev_bool false
    | some k =>
      obtain ⟨m, hm, hev⟩ := field_read hk hf
      refine ⟨some m, by simp [LawRef.read, hm], ?_, fun m' h => ?_⟩
      · simp only [refRead, fieldRead, hk, subst_trueT]; exact ev_bool true
      · cases h
        simp only [refRead, fieldRead, hk, At.newF, At.new, subst_scalarRead, subst_get, subst_bound, h1]
        exact hev
  | subject =>
    have := opt_read (t := (⟨d⟩ : At).reqF "subject") (σ := σ) (x := facts.subject)
      (by simp only [At.reqF, At.req, subst_get, subst_bound, h0]; exact ev_get hs)
    exact ⟨facts.subject, by simp [LawRef.read], this⟩
  | caller =>
    have := opt_read (t := (⟨d⟩ : At).reqF "caller") (σ := σ) (x := facts.caller)
      (by simp only [At.reqF, At.req, subst_get, subst_bound, h0]; exact ev_get hc)
    exact ⟨facts.caller, by simp [LawRef.read], this⟩
  | height =>
    refine ⟨some facts.height, by simp [LawRef.read], by simp only [refRead, subst_trueT]; exact ev_bool true,
      fun m h => ?_⟩
    cases h
    simp only [refRead, At.reqF, At.req, subst_get, subst_bound, h0]; exact ev_get hh
  | turn =>
    refine ⟨some facts.turn, by simp [LawRef.read], by simp only [refRead, subst_trueT]; exact ev_bool true,
      fun m h => ?_⟩
    cases h
    simp only [refRead, At.reqF, At.req, subst_get, subst_bound, h0]; exact ev_get ht

/-! ## The condition evaluates to the meaning -/

theorem ev_eq {t : Term} {b b' : Bool} (h : Evaluates t (.boolean b)) (hb : b = b') : Evaluates t (.boolean b') :=
  hb ▸ h

/-- A present-guarded comparison. -/
theorem ev_guarded {p v : Term} {ro : Option Nat} {P : Nat → Bool} (hp : Evaluates p (.boolean ro.isSome))
    (hv : ∀ m, ro = some m → Evaluates v (.boolean (P m))) :
    Evaluates (andT p v) (.boolean (match ro with | some m => P m | none => false)) := by
  cases ro with
  | none => exact ev_andT (y := false) hp (fun h => by cases h)
  | some m => exact ev_andT hp (fun _ => hv m rfl)

/-- A comparison of two readings, both present. -/
theorem ev_both {p q c : Term} {rx ry : Option Nat} {P : Nat → Nat → Bool}
    (hp : Evaluates p (.boolean rx.isSome)) (hq : Evaluates q (.boolean ry.isSome))
    (hc : ∀ a b, rx = some a → ry = some b → Evaluates c (.boolean (P a b))) :
    Evaluates (andT p (andT q c)) (.boolean (match rx, ry with | some a, some b => P a b | _, _ => false)) := by
  cases rx with
  | none => exact ev_andT (y := false) hp (fun h => by cases h)
  | some a =>
    cases ry with
    | none => exact ev_eq (ev_andT hp fun _ => ev_andT (y := false) hq (fun h => by cases h)) rfl
    | some b => exact ev_eq (ev_andT hp fun _ => ev_andT hq fun _ => hc a b rfl rfl) (by simp)

@[simp] theorem subst_orT (σ : Nat → Term) (a b : Term) :
    (orT a b).substitute σ = orT (a.substitute σ) (b.substitute σ) := by simp [orT]
@[simp] theorem subst_impliesT (σ : Nat → Term) (a b : Term) :
    (impliesT a b).substitute σ = impliesT (a.substitute σ) (b.substitute σ) := by
  simp [impliesT]
@[simp] theorem subst_both (σ : Nat → Term) (x y : Read) (cmp : Term → Term → Term) :
    (both x y cmp).substitute σ = andT (x.present.substitute σ) (andT (y.present.substitute σ)
      ((cmp x.value y.value).substitute σ)) := by
  simp [both]

theorem contains_filter (m : Nat) : ∀ cs : List Int,
    cs.contains (Int.ofNat m) = (cs.filter (0 ≤ ·)).any (fun c => m == c.toNat)
  | [] => rfl
  | c :: cs => by
    have ih := contains_filter m cs
    by_cases hc : 0 ≤ c
    · simp only [List.contains_cons, List.filter_cons, hc, decide_true, ite_true, List.any_cons, ih]
      have : (Int.ofNat m == c) = (m == c.toNat) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Int.ofNat_eq_natCast]; omega
      rw [this]
    · simp only [List.contains_cons, List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false, ih]
      have : (Int.ofNat m == c) = false := by
        rw [beq_eq_false_iff_ne, Int.ofNat_eq_natCast]; omega
      rw [this]; rfl

theorem old_left {o : Data} {hasOld : Bool} {l r : List String} {S : Ty}
    (h : hasOld = true → ∃ ofs, o = .record ofs ∧ ∀ f ∈ l ++ r, fitsField S ofs f = true) :
    hasOld = true → ∃ ofs, o = .record ofs ∧ ∀ f ∈ l, fitsField S ofs f = true := fun hh => by
  obtain ⟨ofs, ho, hf⟩ := h hh
  exact ⟨ofs, ho, fun f hm => hf f (List.mem_append_left _ hm)⟩

theorem old_right {o : Data} {hasOld : Bool} {l r : List String} {S : Ty}
    (h : hasOld = true → ∃ ofs, o = .record ofs ∧ ∀ f ∈ l ++ r, fitsField S ofs f = true) :
    hasOld = true → ∃ ofs, o = .record ofs ∧ ∀ f ∈ r, fitsField S ofs f = true := fun hh => by
  obtain ⟨ofs, ho, hf⟩ := h hh
  exact ⟨ofs, ho, fun f hm => hf f (List.mem_append_right _ hm)⟩

-- Each atom's last step closes a Boolean equation with one shared simp set; not every lemma in it
-- fires at every atom.
set_option linter.unusedSimpArgs false in
/-- **The compiled condition evaluates to the fragment's meaning**, on a new state that fits `S`
at the fields the law reads (and an old one, when the act has one), under the clause environment
of any depth. -/
public theorem cond_eval {S : Ty} {d : Nat} {σ : Nat → Term} {o rq : Data} {fs : List (String × Data)}
    {ag pr : String} {nb vu : Nat} {occ : Data} {facts : Facts}
    (hσ : EnvAt d σ o (.record fs) rq) (hrq : rq = reqOf ag pr nb vu occ facts) (hasOld : Bool) :
    ∀ (e : LawExpr), (∀ f ∈ e.fields, fitsField S fs f = true) →
      (hasOld = true → ∃ ofs, o = .record ofs ∧ ∀ f ∈ e.fields, fitsField S ofs f = true) →
      Evaluates ((cond S hasOld ⟨d⟩ e).substitute σ)
        (.boolean (e.denote facts (if hasOld then some o else none) (.record fs)))
  | .eqC r c, hf, _ => by
    obtain ⟨ro, hr, hp, hv⟩ := read_spec (S := S) r hσ hrq hf
    simp only [cond, LawExpr.denote, hr]
    by_cases hc : 0 ≤ c
    · simp only [hc, ite_true, subst_andT, subst_eqNat, subst_natT]
      refine ev_eq (ev_guarded hp fun m hm => ev_eqNat (hv m hm) (ev_nat _)) ?_
      cases ro with
      | none => simp
      | some m => (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
    · simp only [hc, ite_false, subst_falseT]
      refine ev_eq (ev_bool false) ?_
      cases ro with
      | none => simp
      | some m => (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .leC r c, hf, _ => by
    obtain ⟨ro, hr, hp, hv⟩ := read_spec (S := S) r hσ hrq hf
    simp only [cond, LawExpr.denote, hr]
    by_cases hc : 0 ≤ c
    · simp only [hc, ite_true, subst_andT, subst_leNat, subst_natT]
      refine ev_eq (ev_guarded hp fun m hm => ev_leNat (hv m hm) (ev_nat _)) ?_
      cases ro with
      | none => simp
      | some m => (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
    · simp only [hc, ite_false, subst_falseT]
      refine ev_eq (ev_bool false) ?_
      cases ro with
      | none => simp
      | some m => (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .inC r cs, hf, _ => by
    obtain ⟨ro, hr, hp, hv⟩ := read_spec (S := S) r hσ hrq hf
    simp only [cond, LawExpr.denote, hr, subst_andT, subst_anyOf, List.map_map]
    refine ev_eq (ev_guarded (P := fun m => (cs.filter (0 ≤ ·)).any (fun (c : Int) => m == c.toNat)) hp
      fun m hm => ev_anyOf (g := fun (c : Int) => (eqNat (refRead S ⟨d⟩ r).value (natT c.toNat)).substitute σ)
        fun c _ => by simp only [subst_eqNat, subst_natT]; exact ev_eqNat (hv m hm) (ev_nat _)) ?_
    cases ro with
    | none => rfl
    | some m => simp only [Option.map_some]; rw [contains_filter]
  | .eqR l r, hf, _ => by
    obtain ⟨rx, hrx, hpx, hvx⟩ := read_spec (S := S) l hσ hrq fun f h => hf f (List.mem_append_left _ h)
    obtain ⟨ry, hry, hpy, hvy⟩ := read_spec (S := S) r hσ hrq fun f h => hf f (List.mem_append_right _ h)
    simp only [cond, LawExpr.denote, hrx, hry, subst_both, subst_eqNat]
    refine ev_eq (ev_both hpx hpy fun a b ha hb => ev_eqNat (hvx a ha) (hvy b hb)) ?_
    cases rx <;> cases ry <;> simp only [Option.map_some, Option.map_none]
    (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .leR l r, hf, _ => by
    obtain ⟨rx, hrx, hpx, hvx⟩ := read_spec (S := S) l hσ hrq fun f h => hf f (List.mem_append_left _ h)
    obtain ⟨ry, hry, hpy, hvy⟩ := read_spec (S := S) r hσ hrq fun f h => hf f (List.mem_append_right _ h)
    simp only [cond, LawExpr.denote, hrx, hry, subst_both, subst_leNat]
    refine ev_eq (ev_both hpx hpy fun a b ha hb => ev_leNat (hvx a ha) (hvy b hb)) ?_
    cases rx <;> cases ry <;> simp only [Option.map_some, Option.map_none]
    (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .leROff l r k, hf, _ => by
    obtain ⟨rx, hrx, hpx, hvx⟩ := read_spec (S := S) l hσ hrq fun f h => hf f (List.mem_append_left _ h)
    obtain ⟨ry, hry, hpy, hvy⟩ := read_spec (S := S) r hσ hrq fun f h => hf f (List.mem_append_right _ h)
    simp only [cond, LawExpr.denote, hrx, hry]
    by_cases hk : 0 ≤ k
    · simp only [hk, ite_true, subst_both, subst_leNat, subst_addNat, subst_natT]
      refine ev_eq (ev_both hpx hpy fun a b ha hb => ev_leNat (hvx a ha) (ev_addNat (hvy b hb) (ev_nat _))) ?_
      cases rx <;> cases ry <;> simp only [Option.map_some, Option.map_none]
      (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
    · simp only [hk, ite_false, subst_both, subst_leNat, subst_addNat, subst_natT]
      refine ev_eq (ev_both hpx hpy fun a b ha hb => ev_leNat (ev_addNat (hvx a ha) (ev_nat _)) (hvy b hb)) ?_
      cases rx <;> cases ry <;> simp only [Option.map_some, Option.map_none]
      (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .monotone f, hf, ho => by
    cases hasOld with
    | false => simp only [cond, Bool.false_eq_true, ite_false, subst_falseT, LawExpr.denote,
        Option.bind_none]; exact ev_bool false
    | true =>
      obtain ⟨ofs, rfl, hfo⟩ := ho rfl
      have hfn := hf f (by simp [LawExpr.fields])
      have hfo := hfo f (by simp [LawExpr.fields])
      simp only [cond, ite_true, LawExpr.denote, Option.bind_some]
      cases hk : fieldKind S f with
      | none =>
        simp only [subst_falseT, field_absent hk hfn, field_absent hk hfo]; exact ev_bool false
      | some k =>
        obtain ⟨m, hm, hev⟩ := field_read hk hfn
        obtain ⟨m', hm', hev'⟩ := field_read hk hfo
        simp only [hm, hm', subst_leNat, subst_scalarRead, At.oldF, At.newF, At.old, At.new, subst_get,
          subst_bound, hσ.2.1, hσ.2.2]
        refine ev_eq (ev_leNat hev' hev) ?_
        (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .writeOnce f, hf, ho => by
    cases hasOld with
    | false => simp only [cond, Bool.false_eq_true, ite_false, subst_trueT, LawExpr.denote,
        Option.bind_none]; exact ev_bool true
    | true =>
      obtain ⟨ofs, rfl, hfo⟩ := ho rfl
      have hfn := hf f (by simp [LawExpr.fields])
      have hfo := hfo f (by simp [LawExpr.fields])
      simp only [cond, ite_true, LawExpr.denote, Option.bind_some]
      cases hk : fieldKind S f with
      | none => simp only [subst_trueT, field_absent hk hfo]; exact ev_bool true
      | some k =>
        obtain ⟨m, hm, hev⟩ := field_read hk hfn
        obtain ⟨m', hm', hev'⟩ := field_read hk hfo
        simp only [hm, hm', subst_ifBool, subst_eqNat, subst_trueT, subst_natT, subst_scalarRead, At.oldF,
          At.newF, At.old, At.new, subst_get, subst_bound, hσ.2.1, hσ.2.2]
        by_cases h0 : m' = 0
        · subst h0
          refine evaluates_ifBool (ev_eqNat hev' (ev_nat 0)) (ev_eq (ev_bool true) ?_)
          simp
        · have hne : (m' == 0) = false := by simpa using h0
          refine evaluates_ifBool (b := false) (hne ▸ ev_eqNat hev' (ev_nat 0)) (ev_eq (ev_eqNat hev hev') ?_)
          have : ((Int.ofNat m' == 0) = false) := by simp [h0]
          rw [this, Bool.false_or]
          (apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Option.map_some, Option.map_none, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast]; omega)
  | .not e, hf, ho => by
    simp only [cond, LawExpr.denote, subst_notT]
    exact ev_notT (cond_eval hσ hrq hasOld e hf ho)
  | .and l r, hf, ho => by
    simp only [cond, LawExpr.denote, subst_andT]
    exact ev_andT (cond_eval hσ hrq hasOld l (fun f h => hf f (List.mem_append_left _ h)) (old_left ho))
      fun _ => cond_eval hσ hrq hasOld r (fun f h => hf f (List.mem_append_right _ h)) (old_right ho)
  | .or l r, hf, ho => by
    simp only [cond, LawExpr.denote, subst_orT]
    exact ev_orT (cond_eval hσ hrq hasOld l (fun f h => hf f (List.mem_append_left _ h)) (old_left ho))
      (cond_eval hσ hrq hasOld r (fun f h => hf f (List.mem_append_right _ h)) (old_right ho))
  | .implies l r, hf, ho => by
    simp only [cond, LawExpr.denote, subst_impliesT]
    exact ev_impliesT (cond_eval hσ hrq hasOld l (fun f h => hf f (List.mem_append_left _ h)) (old_left ho))
      (cond_eval hσ hrq hasOld r (fun f h => hf f (List.mem_append_right _ h)) (old_right ho))

/-! ## The law -/

/-- **A `lawOf6` law, applied, runs the arm of the request's occasion** (built forward). -/
public theorem lawOf6_eval {b ad rl rt wr iv : At → Term} {o n rq x : Data} {ℓ : String} {body v : Term}
    (ho : rq.field "occasion" = some (.variant ℓ x))
    (hf : (arms6 b ad rl rt wr iv).find? (fun arm => arm.1 == ℓ) = some (ℓ, body))
    (h : Evaluates (body.substitute (armEnv x.term o.term n.term rq.term)) v) :
    Evaluates (applyLaw (lawOf6 b ad rl rt wr iv) o n rq) v := by
  refine evaluates_steps (applyLaw_steps _ o n rq) ?_
  refine ev_case_subst (l := ℓ) (p := x.term) ?_ hf h
  simp only [subst_get, subst_bound, lawEnv, scons_zero]
  exact ev_get ho

theorem clause_eval {S : Ty} {name : String} {e : LawExpr} {hasOld : Bool} {σ : Nat → Term} {b : Bool}
    (h : Evaluates ((cond S hasOld ⟨1⟩ e).substitute σ) (.boolean b)) :
    Evaluates ((clause S name e hasOld ⟨1⟩).substitute σ) (verdictOf name b) := by
  simp only [clause, subst_guard, subst_okT]
  cases b
  · exact evaluates_ifBool h (evaluates_self (.inject _ _))
  · exact evaluates_ifBool h (evaluates_self (.inject _ _))

theorem armEnv_at {x o n rq : Data} : EnvAt 1 (armEnv x.term o.term n.term rq.term) o n rq :=
  ⟨rfl, rfl, rfl⟩

/-- **A write or an invoke**: the compiled law evaluates to the verdict `denote` gives with the old
state. -/
public theorem compile_change {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hc : IsChange occ) (hfo : Fits S e o = true) (hfn : Fits S e n = true) :
    Evaluates (applyLaw (compile S name e) o n (reqOf ag pr nb vu occ facts))
      (verdictOf name (e.denote facts (some o) n)) := by
  cases n with
  | record fs =>
    cases o with
    | record ofs =>
      have hfn' : ∀ f ∈ e.fields, fitsField S fs f = true := by simpa [Fits] using hfn
      have hfo' : ∀ f ∈ e.fields, fitsField S ofs f = true := by simpa [Fits] using hfo
      have hocc := (req_field_opt (ag := ag) (pr := pr) (nb := nb) (vu := vu) (occ := occ) (facts := facts)).2.2.2.2
      rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · have hcx := cond_eval (S := S) (armEnv_at (x := x) (o := .record ofs) (n := .record fs)
          (rq := reqOf ag pr nb vu (.variant "write" x) facts)) rfl true e hfn' fun _ => ⟨ofs, rfl, hfo'⟩
        exact lawOf6_eval hocc rfl (clause_eval hcx)
      · have hcx := cond_eval (S := S) (armEnv_at (x := x) (o := .record ofs) (n := .record fs)
          (rq := reqOf ag pr nb vu (.variant "invoke" x) facts)) rfl true e hfn' fun _ => ⟨ofs, rfl, hfo'⟩
        exact lawOf6_eval hocc rfl (clause_eval hcx)
    | _ => simp [Fits] at hfo
  | _ => simp [Fits] at hfn

/-- **A birth or an adoption**: judged as a first write, with no old state. -/
public theorem compile_first {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hocc : (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x)
    (hfn : Fits S e n = true) :
    Evaluates (applyLaw (compile S name e) o n (reqOf ag pr nb vu occ facts))
      (verdictOf name (e.denote facts none n)) := by
  cases n with
  | record fs =>
    have hfn' : ∀ f ∈ e.fields, fitsField S fs f = true := by simpa [Fits] using hfn
    have ho := (req_field_opt (ag := ag) (pr := pr) (nb := nb) (vu := vu) (occ := occ) (facts := facts)).2.2.2.2
    rcases hocc with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hcx := cond_eval (S := S) (armEnv_at (x := x) (o := o) (n := .record fs)
        (rq := reqOf ag pr nb vu (.variant "birth" x) facts)) rfl false e hfn' (fun h => by cases h)
      exact lawOf6_eval ho rfl (clause_eval hcx)
    · have hcx := cond_eval (S := S) (armEnv_at (x := x) (o := o) (n := .record fs)
        (rq := reqOf ag pr nb vu (.variant "adopt" x) facts)) rfl false e hfn' (fun h => by cases h)
      exact lawOf6_eval ho rfl (clause_eval hcx)
  | _ => simp [Fits] at hfn

/-- **A relaw or a retirement** writes no state: admitted, whatever the states. -/
public theorem compile_inert {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hocc : (∃ x, occ = .variant "relaw" x) ∨ ∃ x, occ = .variant "retire" x) :
    Evaluates (applyLaw (compile S name e) o n (reqOf ag pr nb vu occ facts)) okT := by
  have ho := (req_field_opt (ag := ag) (pr := pr) (nb := nb) (vu := vu) (occ := occ) (facts := facts)).2.2.2.2
  rcases hocc with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact lawOf6_eval ho rfl (by rw [subst_okT]; exact evaluates_self (.inject _ _))
  · exact lawOf6_eval ho rfl (by rw [subst_okT]; exact evaluates_self (.inject _ _))

/-- A law that evaluates to a predicted verdict admits exactly when it is `ok`, and refuses with
the name exactly when it is not. -/
theorem verdict_iff {L : Term} {o n rq : Data} {name : String} {b : Bool}
    (h : Evaluates (applyLaw L o n rq) (verdictOf name b)) :
    (Admits L o n rq ↔ b = true) ∧ (Refuses L o n rq name ↔ b = false) := by
  cases b
  · refine ⟨⟨fun ⟨w, hw⟩ => ?_, fun h => by cases h⟩, ⟨fun _ => rfl, fun _ => h⟩⟩
    have := evaluates_unique h hw
    simp [verdictOf, refusedT] at this
  · refine ⟨⟨fun _ => rfl, fun _ => ⟨_, h⟩⟩, ⟨fun hr => ?_, fun h => by cases h⟩⟩
    have := evaluates_unique h hr
    simp [verdictOf, okT, refusedT] at this

/-- **Admits iff the fragment holds**, at a write or an invoke. -/
public theorem compile_admits_change {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hc : IsChange occ) (hfo : Fits S e o = true) (hfn : Fits S e n = true) :
    Admits (compile S name e) o n (reqOf ag pr nb vu occ facts) ↔ e.denote facts (some o) n = true :=
  (verdict_iff (compile_change hc hfo hfn)).1

/-- **Refuses, naming the law, iff the fragment fails**, at a write or an invoke. -/
public theorem compile_refuses_change {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hc : IsChange occ) (hfo : Fits S e o = true) (hfn : Fits S e n = true) :
    Refuses (compile S name e) o n (reqOf ag pr nb vu occ facts) name ↔ e.denote facts (some o) n = false :=
  (verdict_iff (compile_change hc hfo hfn)).2

public theorem compile_admits_first {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hocc : (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x)
    (hfn : Fits S e n = true) :
    Admits (compile S name e) o n (reqOf ag pr nb vu occ facts) ↔ e.denote facts none n = true :=
  (verdict_iff (compile_first hocc hfn)).1

public theorem compile_refuses_first {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hocc : (∃ x, occ = .variant "birth" x) ∨ ∃ x, occ = .variant "adopt" x)
    (hfn : Fits S e n = true) :
    Refuses (compile S name e) o n (reqOf ag pr nb vu occ facts) name ↔ e.denote facts none n = false :=
  (verdict_iff (compile_first hocc hfn)).2

public theorem compile_admits_inert {S : Ty} {name : String} {e : LawExpr} {o n occ : Data} {facts : Facts}
    {ag pr : String} {nb vu : Nat} (hocc : (∃ x, occ = .variant "relaw" x) ∨ ∃ x, occ = .variant "retire" x) :
    Admits (compile S name e) o n (reqOf ag pr nb vu occ facts) :=
  ⟨_, compile_inert hocc⟩

/-! ## The compiled law checks at `lawTy S` -/

theorem chk_opt {S P : Ty} (hsh : S.shareable = true) (hP : P.shareable = true) (fld : String)
    (hm : Obend.Core.Bidirectional.rowMember reqTy fld = some optNatTy) :
    Chk (clauseCtx S P) (optRead ((⟨1⟩ : At).reqF fld)).present .boolean ∧
      Chk (clauseCtx S P) (optRead ((⟨1⟩ : At).reqF fld)).value .natural := by
  have cl := clean_clause hsh hP
  have hs : Syn (clauseCtx S P) ((⟨1⟩ : At).reqF fld) optNatTy := syn_get (syn_bound rfl) hm
  exact ⟨chk_case cl hs rfl (.cons rfl rfl (chk_boolean _ _) (.cons rfl rfl (chk_boolean _ _) .nil)) rfl (by simp),
    chk_case cl hs rfl (.cons rfl rfl (chk_nat _ _) (.cons rfl rfl
      (chk_bound (i := 0) (b := ⟨.natural, .unrestricted⟩) rfl) .nil)) rfl (by simp)⟩

theorem chk_scalarRead {S P : Ty} {f : String} {k : Kind} {i : Nat} (hk : fieldKind S f = some k)
    (hi : (clauseCtx S P)[i]? = some ⟨S, .unrestricted⟩) :
    Chk (clauseCtx S P) (scalarRead k (.get (.bound i) f)) .natural := by
  have hm := kind_member hk
  cases k with
  | nat => exact chk_field hi hm
  | bool => exact chk_ifBool (chk_field hi hm) (chk_nat _ _) (chk_nat _ _)

theorem chk_read {S P : Ty} (hsh : S.shareable = true) (hP : P.shareable = true) (r : LawRef) :
    Chk (clauseCtx S P) (refRead S ⟨1⟩ r).present .boolean ∧
      Chk (clauseCtx S P) (refRead S ⟨1⟩ r).value .natural := by
  cases r with
  | field f =>
    simp only [refRead, fieldRead]
    cases hk : fieldKind S f with
    | none => exact ⟨chk_boolean _ _, chk_nat _ _⟩
    | some k => exact ⟨chk_boolean _ _, chk_scalarRead hk rfl⟩
  | subject => exact chk_opt hsh hP "subject" rfl
  | caller => exact chk_opt hsh hP "caller" rfl
  | height => exact ⟨chk_boolean _ _, chk_field rfl rfl⟩
  | turn => exact ⟨chk_boolean _ _, chk_field rfl rfl⟩

theorem chk_cond {S P : Ty} (hsh : S.shareable = true) (hP : P.shareable = true) (hasOld : Bool) :
    ∀ e : LawExpr, Chk (clauseCtx S P) (cond S hasOld ⟨1⟩ e) .boolean
  | .eqC r c => by
    have := chk_read (P := P) hsh hP r
    simp only [cond]; split
    · exact chk_andT this.1 (chk_bin rfl this.2 (chk_nat _ _))
    · exact chk_boolean _ _
  | .leC r c => by
    have := chk_read (P := P) hsh hP r
    simp only [cond]; split
    · exact chk_andT this.1 (chk_bin rfl this.2 (chk_nat _ _))
    · exact chk_boolean _ _
  | .inC r cs => by
    have := chk_read (P := P) hsh hP r
    simp only [cond]
    refine chk_andT this.1 (chk_anyOf fun c hc => ?_)
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hc
    exact chk_bin rfl this.2 (chk_nat _ _)
  | .eqR l r => by
    have hl := chk_read (P := P) hsh hP l
    have hr := chk_read (P := P) hsh hP r
    exact chk_andT hl.1 (chk_andT hr.1 (chk_bin rfl hl.2 hr.2))
  | .leR l r => by
    have hl := chk_read (P := P) hsh hP l
    have hr := chk_read (P := P) hsh hP r
    exact chk_andT hl.1 (chk_andT hr.1 (chk_bin rfl hl.2 hr.2))
  | .leROff l r k => by
    have hl := chk_read (P := P) hsh hP l
    have hr := chk_read (P := P) hsh hP r
    simp only [cond]; split
    · exact chk_andT hl.1 (chk_andT hr.1 (chk_bin rfl hl.2 (chk_bin rfl hr.2 (chk_nat _ _))))
    · exact chk_andT hl.1 (chk_andT hr.1 (chk_bin rfl (chk_bin rfl hl.2 (chk_nat _ _)) hr.2))
  | .monotone f => by
    simp only [cond]; split
    · split
      · rename_i k hk; exact chk_bin rfl (chk_scalarRead hk rfl) (chk_scalarRead hk rfl)
      · exact chk_boolean _ _
    · exact chk_boolean _ _
  | .writeOnce f => by
    simp only [cond]; split
    · split
      · rename_i k hk
        exact chk_ifBool (chk_bin rfl (chk_scalarRead hk rfl) (chk_nat _ _)) (chk_boolean _ _)
          (chk_bin rfl (chk_scalarRead hk rfl) (chk_scalarRead hk rfl))
      · exact chk_boolean _ _
    · exact chk_boolean _ _
  | .not e => chk_notT (chk_cond hsh hP hasOld e)
  | .and l r => chk_andT (chk_cond hsh hP hasOld l) (chk_cond hsh hP hasOld r)
  | .or l r => chk_ifBool (chk_cond hsh hP hasOld l) (chk_boolean _ _) (chk_cond hsh hP hasOld r)
  | .implies l r => chk_ifBool (chk_cond hsh hP hasOld l) (chk_cond hsh hP hasOld r) (chk_boolean _ _)

/-- **The compiled law checks at `lawTy S`** under `Bidirectional.checkAgainst`, with no
annotations, for every canonical shareable state type: whatever fields the law names (a field `S`
lacks reads as absent, statically). -/
public theorem compile_checks {S : Ty} (name : String) (e : LawExpr) (hS : S.isCanonical)
    (hsh : S.shareable = true) : ChecksAt (compile S name e) S := by
  have cl (P : Ty) (hP : P.shareable = true) (h : Bool) : Chk (clauseCtx S P) (clause S name e h ⟨1⟩) verdictTy :=
    chk_guard (chk_cond hsh hP h e) (chk_okT _)
  exact lawOf6_checks hS hsh ⟨cl _ rfl false, cl _ rfl false, cl _ rfl true, chk_okT _, chk_okT _, cl _ rfl true⟩

/-- Every law of a package, compiled, checks. -/
public theorem compilePackage_checks {S : Ty} (laws : List (String × LawExpr)) (hS : S.isCanonical)
    (hsh : S.shareable = true) : ∀ p ∈ compilePackage S laws, ChecksAt p.2 S := by
  intro p hp
  obtain ⟨⟨name, e⟩, _, rfl⟩ := List.mem_map.1 hp
  exact compile_checks name e hS hsh

/-! ## Teeth

The hypotheses are inhabited and the verdicts are not constant: on a state type with a boolean
`flag` and a natural `total`, the tally law admits a write and refuses one by name; at a birth
`monotone` has no old state and refuses, `writeOnce` admits; a relaw is admitted; a negative
constant and an absent subject decide statically; and the compiled law checks at its type. Each
`denote` and `Fits` fact is `decide`d in the kernel. -/

namespace Teeth

@[expose] public def flagTotal : Ty := .field "flag" .boolean (.field "total" .natural .emptyRow)
@[expose] public def st (flag : Bool) (total : Nat) : Data := .record [("flag", .boolean flag), ("total", .natural total)]
@[expose] public def facts : Facts := ⟨some 3, some 7, 10, 2⟩

/-- `new.total <= 1000 and monotone(total) and (new.flag == 1 implies request.caller == new.total)`. -/
@[expose] public def tally : LawExpr :=
  .and (.and (.leC (.field "total") 1000) (.monotone "total"))
    (.implies (.eqC (.field "flag") 1) (.eqR .caller (.field "total")))

theorem tally_write_admitted :
    Admits (compile flagTotal "tally" tally) (st false 5) (st true 7) (reqOf "ann" "ann" 0 9 writeO facts) :=
  (compile_admits_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide)

theorem tally_write_refused :
    Refuses (compile flagTotal "tally" tally) (st false 5) (st true 6) (reqOf "ann" "ann" 0 9 writeO facts) "tally" ∧
      Refuses (compile flagTotal "tally" tally) (st false 5) (st false 4) (reqOf "ann" "ann" 0 9 (invokeO 1) facts)
        "tally" :=
  ⟨(compile_refuses_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_refuses_change (.inr ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide)⟩

theorem first_write_teeth :
    Refuses (compile flagTotal "m" (.monotone "total")) (st false 0) (st false 5)
        (reqOf "ann" "ann" 0 9 birthO facts) "m" ∧
      Admits (compile flagTotal "w" (.writeOnce "total")) (st false 9) (st false 5)
        (reqOf "ann" "ann" 0 9 (adoptO "L") facts) ∧
      Refuses (compile flagTotal "w" (.writeOnce "total")) (st false 9) (st false 5)
        (reqOf "ann" "ann" 0 9 writeO facts) "w" ∧
      Admits (compile flagTotal "w" (.writeOnce "total")) (st false 0) (st false 5)
        (reqOf "ann" "ann" 0 9 writeO facts) :=
  ⟨(compile_refuses_first (.inl ⟨_, rfl⟩) (by decide)).2 (by decide),
    (compile_admits_first (.inr ⟨_, rfl⟩) (by decide)).2 (by decide),
    (compile_refuses_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_admits_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide)⟩

theorem static_teeth :
    Refuses (compile flagTotal "neg" (.leC (.field "total") (-1))) (st false 0) (st false 0)
        (reqOf "ann" "ann" 0 9 writeO facts) "neg" ∧
      Refuses (compile flagTotal "sub" (.eqC .subject 3)) (st false 0) (st false 0)
        (reqOf "ann" "ann" 0 9 writeO ⟨none, none, 0, 0⟩) "sub" ∧
      Admits (compile flagTotal "sub" (.eqC .subject 3)) (st false 0) (st false 0)
        (reqOf "ann" "ann" 0 9 writeO facts) ∧
      Refuses (compile flagTotal "gap" (.leC (.field "missing") 5)) (st false 0) (st false 0)
        (reqOf "ann" "ann" 0 9 writeO facts) "gap" ∧
      Admits (compile flagTotal "off" (.leROff (.field "total") .height (-3))) (st false 0) (st false 7)
        (reqOf "ann" "ann" 0 9 writeO facts) ∧
      Admits (compile flagTotal "tally" tally) (st false 5) (st false 0) (reqOf "ann" "ann" 0 9 (relawO "L") facts) :=
  ⟨(compile_refuses_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_refuses_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_admits_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_refuses_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    (compile_admits_change (.inl ⟨_, rfl⟩) (by decide) (by decide)).2 (by decide),
    compile_admits_inert (.inl ⟨_, rfl⟩)⟩

/-- The kernel's own run agrees with the theorem on the refused tally write. -/
theorem tally_run_agrees :
    refusalOf (run 4000 (applyLaw (compile flagTotal "tally" tally) (st false 5) (st true 6)
      (reqOf "ann" "ann" 0 9 writeO facts))) = some "tally" := by decide +kernel

theorem tally_typed : ChecksAt (compile flagTotal "tally" tally) flagTotal :=
  compile_checks "tally" tally (Obend.Law.Typing.Teeth.isCanonical_of (by decide)) rfl

end Teeth

#assert_axioms steps_binL steps_binR ev_binary find_fieldsTerm ev_get ev_bool ev_nat ev_andT ev_notT
  ev_orT ev_impliesT ev_anyOf ev_eqNat ev_leNat ev_addNat ev_case_subst firstScalar_of_lookup
  kind_member subst_scalarRead field_read field_absent req_field_opt opt_read read_spec ev_eq
  ev_guarded ev_both subst_orT subst_impliesT subst_both contains_filter old_left old_right cond_eval
  lawOf6_eval clause_eval armEnv_at compile_change compile_first compile_inert verdict_iff
  compile_admits_change compile_refuses_change compile_admits_first compile_refuses_first
  compile_admits_inert chk_opt chk_scalarRead chk_read chk_cond compile_checks compilePackage_checks
  Teeth.tally_write_admitted Teeth.tally_write_refused Teeth.first_write_teeth Teeth.static_teeth
  Teeth.tally_run_agrees Teeth.tally_typed

end Obend.Spec.LawCompile
