module
/-
# Obend.Spec.Proofs.Ecosystem — Layer Composition Contracts, Package-Law Narrowing, and Ecosystem Turn Pinning

Consolidates (`Wave C2-Core`, `3 → 1`):
1. `Obend.Spec.Contract`: `run_append`, `run_assoc`, `checkLayer_ok`, `missing_nil_get`, `discharge_ok`.
2. `Obend.Spec.PackageLaw`: `package_law_eval`, `package_never_widens`, `package_refusal_names`, `packages_tooth`.
3. `Obend.Spec.Ecosystem`: `turn_pins_every_root`, `resolve_fill`, `stale_iff_blocked`,
   `admit_stale_names_moved`, `admit_refuses_moved`, `admit_admitted`, `moved_pin_stale_forever`,
   `retired_stale_forever`, `turn_stale_forever`, `closure_law_inherited`.
-/
public import Obend.Spec.Contract
public import Obend.Spec.PackageLaw
public import Obend.Spec.Ecosystem
public import Obend.Slot.World
public import Obend.Law.Proofs.Inherit
public import Obend.Law.Proofs.Eval
public import Obend.Law.Std
public import Obend.Tactic.Tooth
import all Obend.Spec.Ecosystem
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Eval

/-! ## Consolidated from `lean/Obend/Spec/Proofs/Contract.lean` -/
namespace Obend.Spec.Contract
set_option autoImplicit false

variable {τ : Type} [BEq τ]

/-! ## The composition law -/

/-- **`C_{A;B}(S,I) = C_A(S,I) ∧ C_B(S, F_A(S,I))` and `F_{A;B} = F_B ∘ F_A`**: checking the
composition of two chains is checking the first from the seed, then the second from the row the
first leaves. Associativity of composition is therefore the associativity of `++` on chains:
`run_assoc`. -/
public theorem run_append (self : Row τ) (seed : Row τ) (first second : List (Layer τ)) :
    run self seed (first ++ second) = (run self seed first).bind fun mid => run self mid second := by
  induction first generalizing seed with
  | nil => rfl
  | cons layer rest ih =>
    simp only [List.cons_append, run]
    cases checkLayer self seed layer with
    | error _ => rfl
    | ok next => exact ih next

public theorem run_assoc (self seed : Row τ) (a b c : List (Layer τ)) :
    run self seed ((a ++ b) ++ c) = run self seed (a ++ (b ++ c)) := by
  rw [List.append_assoc]

/-- An admitted layer met every clause of its contract, and left `F_L(S, I)`. -/
public theorem checkLayer_ok {self beneath next : Row τ} {layer : Layer τ}
    (admitted : checkLayer self beneath layer = .ok next) :
    missing self layer.assumes = [] ∧ missing beneath layer.consumes = [] ∧
      replaced beneath layer.provides = [] ∧ next = layer.leaves beneath := by
  unfold checkLayer checkBounds checkProvides at admitted
  by_cases a : (missing self layer.assumes).isEmpty
  · by_cases b : (missing beneath layer.consumes).isEmpty
    · by_cases r : (replaced beneath layer.provides).isEmpty
      · simp only [a, b, r, Bool.not_true, Bool.false_eq_true, if_false, Except.bind] at admitted
        cases admitted
        exact ⟨List.isEmpty_iff.mp a, List.isEmpty_iff.mp b, List.isEmpty_iff.mp r, rfl⟩
      · simp [a, b, r, Except.bind] at admitted
    · simp [a, b, Except.bind] at admitted
  · simp [a, Except.bind] at admitted

public theorem missing_nil_get {actual required : Row τ} (h : missing actual required = []) :
    ∀ n t, (n, t) ∈ required → get? actual n == some t := by
  intro n t mem
  unfold missing at h
  have := List.filterMap_eq_nil_iff.mp h (n, t) mem
  by_cases e : (get? actual n == some t) = true
  · exact e
  · simp [e] at this

/-- A discharged composition: every layer's assumptions hold in the final self, and the row the
chain leaves gives every member of the final self its declared type and declares nothing else. -/
public theorem discharge_ok {self seed : Row τ} {chain : List (Layer τ)}
    (admitted : discharge self seed chain = .ok ()) :
    ∃ final, run self seed chain = .ok final ∧
      (∀ n t, (n, t) ∈ self → get? final n == some t) ∧
      (∀ n, n ∈ names final → (get? self n).isSome) := by
  unfold discharge at admitted
  cases h : run self seed chain with
  | error e => rw [h] at admitted; cases admitted
  | ok final =>
    rw [h] at admitted
    refine ⟨final, rfl, ?_⟩
    simp only [Except.bind] at admitted
    unfold close at admitted
    by_cases m : (missing final self).isEmpty
    · simp only [m, if_true] at admitted
      by_cases x : (names final).all (fun n => (get? self n).isSome)
      · refine ⟨missing_nil_get (List.isEmpty_iff.mp m), fun n mem => ?_⟩
        exact (List.all_eq_true.mp x) n mem
      · simp [x] at admitted
    · revert admitted
      simp only [m, Bool.false_eq_true, if_false]
      split <;> (try split) <;> simp

end Obend.Spec.Contract

/-! ## Consolidated from `lean/Obend/Spec/Proofs/PackageLaw.lean` -/
namespace Obend.Spec.PackageLaw
open Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data)
set_option autoImplicit false

theorem mem_packageClauses {laws : String → List (String × Term)} {order : List String} {q : String × Term} :
    q ∈ packageClauses laws order ↔ ∃ pkg ∈ order, ∃ c ∈ laws pkg, q = (clauseName pkg c.1, c.2) := by
  simp only [packageClauses, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨pkg, hp, c, hc, rfl⟩
    exact ⟨pkg, hp, c, hc, rfl⟩
  · rintro ⟨pkg, hp, c, hc, rfl⟩
    exact ⟨pkg, hp, c, hc, rfl⟩

theorem effectivePackages_ok {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) :
    law = effective (packageClauses laws order) ∧ ∀ p ∈ packageClauses laws order, closedB p.2 = true := by
  unfold effectivePackages at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hf
    cases h
    refine ⟨rfl, fun p hp => ?_⟩
    rw [List.find?_eq_none] at hf
    simpa using hf p hp

/-- **The effective package law is the conjunction of every package's clauses.** -/
public theorem package_law_eval {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) (o n rq : Data) :
    Admits law o n rq ↔ ∀ pkg ∈ order, ∀ c ∈ laws pkg, Admits c.2 o n rq := by
  obtain ⟨rfl, hc⟩ := effectivePackages_ok h
  rw [effective_law_eval hc]
  constructor
  · intro hall pkg hp c hcl
    exact hall (clauseName pkg c.1, c.2) (mem_packageClauses.2 ⟨pkg, hp, c, hcl, rfl⟩)
  · intro hall q hq
    obtain ⟨pkg, hp, c, hcl, rfl⟩ := mem_packageClauses.1 hq
    exact hall pkg hp c hcl

/-- **A child package only narrows**: a write an ancestor package's clause refuses is refused. -/
public theorem package_never_widens {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) {pkg : String} (hp : pkg ∈ order) {c : String × Term}
    (hcl : c ∈ laws pkg) {o n rq : Data} (hn : ¬ Admits c.2 o n rq) : ¬ Admits law o n rq :=
  fun ha => hn ((package_law_eval h o n rq).1 ha pkg hp c hcl)

/-- **A refusal names the ancestor package and its clause.** -/
public theorem package_refusal_names {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) {o n rq : Data} {r : Term}
    (hr : Evaluates (applyLaw law o n rq) (.inject "refused" r)) :
    ∃ pkg ∈ order, ∃ c ∈ laws pkg, ∃ why, Evaluates (applyLaw c.2 o n rq) (.inject "refused" why) ∧
      RefusedBy law o n rq (clauseName pkg c.1) why := by
  obtain ⟨rfl, hc⟩ := effectivePackages_ok h
  obtain ⟨pre, name, L, post, why, hlin, _, hL, hby⟩ := effective_refusal_names hc hr
  have hmem : (name, L) ∈ packageClauses laws order := by rw [hlin]; simp
  obtain ⟨pkg, hp, c, hcl, heq⟩ := mem_packageClauses.1 hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨pkg, hp, c, hcl, why, hL, hby⟩

/-! ## Teeth: a report and its reviewer, as packages -/

/-- `papers/report` bounds `total`; `lab/review`, extending it, admits only its members. -/
def reportLaws (pkg : String) : List (String × Term) :=
  if pkg = "papers/report" then [("bounded", bounded unitTy "total" 5)]
  else if pkg = "lab/review" then [("members", allowlistLaw unitTy ["ann", "bob"])]
  else []

-- fixture kept in place (2026-11-04): a 10-line closed evaluation; worth a pre-push run, but its fixture data is private to this module, so it cannot move to Obend/Teeth/
theorem packages_tooth :
    (effectivePackages reportLaws ["lab/review", "papers/report"]).toOption.isSome = true ∧
      (match effectivePackages reportLaws ["lab/review", "papers/report"] with
        | .ok law => blameOf (run 500 (applyLaw law (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO))) ==
            some ("papers/report law bounded", "total over the bound") &&
          blameOf (run 500 (applyLaw law (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO))) ==
            some ("lab/review law members", "not on the allowlist") &&
          okB (run 500 (applyLaw law (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO)))
        | .error _ => false) = true := by
  decide +kernel

end Obend.Spec.PackageLaw

/-! ## Consolidated from `lean/Obend/Spec/Proofs/Ecosystem.lean` -/
namespace Obend.Spec.Ecosystem
open Obend.Slot
set_option autoImplicit false

theorem covered_none {v : View} {entry : String} {cl : Closure} {order : List String}
    (h : covered v entry cl order = none) :
    (∀ n ∈ order, n ≠ entry → ∃ p ∈ cl.pins, p.name = n) ∧ (∀ r ∈ cl.chosen, r.name ∈ order) ∧
      ∀ p ∈ cl.pins, p.current v = true := by
  unfold covered at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · cases h
      · rename_i h3
        rw [List.find?_eq_none] at h1 h2 h3
        refine ⟨fun n hn hne => ?_, fun r hr => ?_, fun p hp => ?_⟩
        · have := h1 n hn
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_and, Bool.not_eq_false] at this
          have hany := this hne
          rw [List.any_eq_true] at hany
          obtain ⟨p, hp, hpn⟩ := hany
          exact ⟨p, hp, by simpa using hpn⟩
        · have := h2 r hr
          simpa using this
        · have := h3 p hp
          simpa using this

/-- **A turn pins every root it resolved.** -/
public theorem turn_pins_every_root {v : View} {e : Release} {cl : Closure} (h : close v e = .ok cl) :
    cl.entry = e ∧ (∀ n ∈ cl.order, n ≠ e.name → ∃ p ∈ cl.pins, p.name = n) ∧
      (∀ r ∈ cl.chosen, r.name ∈ cl.order) ∧ ∀ p ∈ cl.pins, p.current v = true := by
  unfold close at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i cl0 _
    split at h
    · cases h
    · rename_i hc
      cases h
      exact ⟨rfl, covered_none hc⟩

/-- Resolving an intention is a fill of its slot: the pin passes the slot's judge, and the support
it cites holds at the view it was resolved at (`Obend.Intention.resolve_fill` for `packages`). -/
public theorem resolve_fill {v : View} {n : String} {m : Nat} {r : Release} {p : Pin}
    (h : resolve v (.intention n m) = .ok (r, p)) :
    (intentionSlot n m).usable (holds v) p = true ∧ p.current v = true ∧ p.name = n ∧ r.major = m := by
  have hp : packages.resolve v (.intention n m) = .ok p := by
    show (resolve v _).map _ = _; rw [h]; rfl
  obtain ⟨href, hu, hc⟩ := packages.resolve_fill hp
  refine ⟨hu, hc, ?_, ?_⟩
  · cases p with
    | intention n' _ _ _ _ => simp [packages, Pin.ref] at href; simp [Pin.name, href.1]
    | extension _ _ => simp [packages, Pin.ref] at href
  · simp only [resolve] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i hm; cases h; simpa using hm
          · cases h

/-- **Staleness is a blocked slot read**: an intention pin is not current at a view exactly when the
read of its slot there is blocked, naming its one support (`Obend.Intention.stale_iff_blocked` for
`packages`). -/
public theorem stale_iff_blocked (v : View) (n : String) (m pin : Nat) (version hash : String) :
    (Pin.intention n m pin version hash).current v = false ↔
      (intentionSlot n m).read (holds v) (some (.intention n m pin version hash)) =
        .blocked (.intention n m pin version hash) [⟨n, m, pin, version⟩] := by
  have hg := packages.stale_iff_blocked (r := .intention n m) (p := .intention n m pin version hash) rfl v
  unfold Pin.current intentionSlot
  rw [hg]
  cases hh : holds v ⟨n, m, pin, version⟩ <;>
    simp [packages, Pin.supports, Pin.ref, hh, Obend.Intention.slot, Slot.read, Slot.dead]

/-- An extension pin is current at every view: a hash is fixed forever. -/
public theorem extension_current (v : View) (n h : String) : (Pin.extension n h).current v = true := by rfl

/-- A pin of an intention is current exactly when the record line it read still holds. -/
theorem intention_current (v : View) (n : String) (m pin : Nat) (version hash : String) :
    (Pin.intention n m pin version hash).current v = holds v ⟨n, m, pin, version⟩ := by
  simp [Pin.current, Obend.Intention.current, packages, Pin.supports]

/-- **Admission names a moved pin**: `stale p` only for a pin of the turn that is not current. -/
public theorem admit_stale_names_moved {v : View} {t : Turn} {p : Pin} (h : admit v t = .stale p) :
    p ∈ t.pins ∧ p.current v = false := by
  unfold admit at h
  split at h
  · rename_i q hq
    cases h
    have := List.find?_some hq
    exact ⟨List.mem_of_find?_eq_some hq, by simpa using this⟩
  · split at h <;> (try split at h) <;> cases h

/-- **A moved pin is stale**: a turn holding a pin that is not current is refused `stale`, naming a
pin of the turn that is not current. -/
public theorem admit_refuses_moved {v : View} {t : Turn} (h : ∃ p ∈ t.pins, p.current v = false) :
    ∃ p, admit v t = .stale p ∧ p ∈ t.pins ∧ p.current v = false := by
  unfold admit
  cases hf : t.pins.find? (fun p => !p.current v) with
  | none =>
    obtain ⟨p, hp, hc⟩ := h
    rw [List.find?_eq_none] at hf
    have := hf p hp
    simp [hc] at this
  | some q =>
    have := List.find?_some hf
    exact ⟨q, rfl, List.mem_of_find?_eq_some hf, by simpa using this⟩

/-- **Admission re-derives**: an admitted turn's closure is `close` at the view, with the turn's
own pins and precedence order. -/
public theorem admit_admitted {v : View} {t : Turn} {cl : Closure} (h : admit v t = .admitted cl) :
    close v t.entry = .ok cl ∧ cl.pins = t.pins ∧ cl.order = t.order := by
  unfold admit at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i cl' hcl
      split at h
      · rename_i heq
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        exact ⟨hcl, heq.1, heq.2⟩
      · cases h

/-- A turn whose pins are all extensions is never stale. -/
public theorem admit_never_stale_extensions {v : View} {t : Turn}
    (hx : ∀ p ∈ t.pins, ∃ n h, p = .extension n h) (p : Pin) : admit v t ≠ .stale p := by
  intro h
  obtain ⟨hp, hc⟩ := admit_stale_names_moved h
  obtain ⟨n, hh, rfl⟩ := hx p hp
  rw [extension_current] at hc
  cases hc

/-- Along record steps a line persists, its pin never decreases, and a retired line stays retired. -/
theorem line_later {v v' : View} (hr : Reaches Step v v') {n : String} {m : Nat} {l : RecordLine}
    (hl : v.line n m = some l) :
    ∃ l', v'.line n m = some l' ∧ l.pin ≤ l'.pin ∧ (l.fill = none → l'.fill = none) := by
  induction hr with
  | refl => exact ⟨l, hl, Nat.le_refl _, id⟩
  | tail _ step ih =>
    obtain ⟨l1, h1, hp1, hf1⟩ := ih
    obtain ⟨l2, h2, hp2, hf2⟩ := step n m l1 h1
    exact ⟨l2, h2, Nat.le_trans hp1 hp2, fun h => hf2 (hf1 h)⟩

/-- **A pin the record has moved past stays stale**: if at `v` the line's pin is past the turn's,
the turn's pin is not current at any later view. -/
public theorem moved_pin_stale_forever {v v' : View} (hr : Reaches Step v v') {n : String} {m pin : Nat}
    {version hash : String} {l : RecordLine} (hl : v.line n m = some l) (hpast : pin < l.pin) :
    (Pin.intention n m pin version hash).current v' = false := by
  obtain ⟨l', h', hp, _⟩ := line_later hr hl
  have hne : l'.pin ≠ pin := by omega
  simp [intention_current, holds, h', hne]

/-- **A retired line stays stale**: a pin of a line its owner retired is not current at any later
view. -/
public theorem retired_stale_forever {v v' : View} (hr : Reaches Step v v') {n : String} {m pin : Nat}
    {version hash : String} {l : RecordLine} (hl : v.line n m = some l) (hret : l.fill = none) :
    (Pin.intention n m pin version hash).current v' = false := by
  obtain ⟨l', h', _, hf⟩ := line_later hr hl
  simp [intention_current, holds, h', hf hret]

/-- A turn pinning a line the record has moved past is refused `stale` at every later view. -/
public theorem turn_stale_forever {v v' : View} (hr : Reaches Step v v') {t : Turn} {n : String}
    {m pin : Nat} {version hash : String} {l : RecordLine}
    (hp : Pin.intention n m pin version hash ∈ t.pins) (hl : v.line n m = some l) (hpast : pin < l.pin) :
    ∃ q, admit v' t = .stale q ∧ q ∈ t.pins ∧ q.current v' = false :=
  admit_refuses_moved ⟨_, hp, moved_pin_stale_forever hr hl hpast⟩

/-- **Package laws inherit across the package boundary**: the effective law of a closure admits a
write only if every clause of every package the closure chose admits it. -/
public theorem closure_law_inherited {v : View} {e : Release} {cl : Closure} (hc : close v e = .ok cl)
    {laws : String → List (String × Obend.Core.Term.Term)} {law : Obend.Core.Term.Term}
    (hl : Obend.Spec.PackageLaw.effectivePackages laws cl.order = .ok law) {o n rq : Obend.Core.Data.Data}
    (ha : Obend.Law.Admits law o n rq) :
    ∀ r ∈ cl.chosen, ∀ c ∈ laws r.name, Obend.Law.Admits c.2 o n rq := by
  obtain ⟨_, _, hchosen, _⟩ := turn_pins_every_root hc
  intro r hr c hcl
  exact (Obend.Spec.PackageLaw.package_law_eval hl o n rq).1 ha r.name (hchosen r hr) c hcl

/-! ## Teeth: a chain closed and admitted; a record step that moves the base; a diamond that
reaches its base once by two routes, its C4 order computed by the kernel; the same diamond after the
base moved, refused by name. -/

def baseR : Release := ⟨"base", "1.0.0", 1, "aa", []⟩
def leftR : Release := ⟨"left", "1.0.0", 1, "bb", [.intention "base" 1]⟩
def rightR : Release := ⟨"right", "1.0.0", 1, "cc", [.extension "base" "aa"]⟩
def chainR : Release := ⟨"chain", "0.1.0", 0, "dd", [.intention "left" 1]⟩
def diamondR : Release := ⟨"diamond", "0.1.0", 0, "ff", [.intention "left" 1, .intention "right" 1]⟩
def base2R : Release := ⟨"base", "1.1.0", 1, "ee", []⟩

def view0 : View :=
  ⟨[baseR, leftR, rightR, base2R],
   [⟨"base", 1, 3, some "1.0.0", "ada"⟩, ⟨"left", 1, 1, some "1.0.0", "bo"⟩, ⟨"right", 1, 7, some "1.0.0", "cy"⟩]⟩
/-- The owner of `base` names 1.1.0 at pin 4. -/
def view1 : View :=
  ⟨view0.releases,
   [⟨"base", 1, 4, some "1.1.0", "ada"⟩, ⟨"left", 1, 1, some "1.0.0", "bo"⟩, ⟨"right", 1, 7, some "1.0.0", "cy"⟩]⟩

-- fixture kept in place (2026-11-04): a 14-line closed evaluation; worth a pre-push run, but its fixture data is private to this module, so it cannot move to Obend/Teeth/
example :
    ((close view0 chainR).toOption.map (·.order)) = some ["chain", "left", "base"] ∧
      ((close view0 chainR).toOption.map (·.pins)) =
        some [.intention "left" 1 1 "1.0.0" "bb", .intention "base" 1 3 "1.0.0" "aa"] ∧
      ((close view0 chainR).toOption.map fun cl => (admit view0 cl.turn) matches .admitted _) = some true ∧
      ((close view0 chainR).toOption.map fun cl => admit view1 cl.turn) =
        some (.stale (.intention "base" 1 3 "1.0.0" "aa")) ∧
      -- at view0 both routes reach base 1.0.0: one release, applied once, in C4 order
      ((close view0 diamondR).toOption.map (·.order)) = some ["diamond", "left", "right", "base"] ∧
      -- at view1 `left` reaches base 1.1.0 by name, `right` base 1.0.0 by hash: two releases, refused
      (match close view1 diamondR with
        | .error e => decide (e = .incompatible "base" "1.1.0" "1.0.0")
        | .ok _ => false) = true := by
  decide +kernel

end Obend.Spec.Ecosystem
