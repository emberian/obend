module
/-
# Obend.Logic.Obligation — a claim is a slot whose candidates are certificates

`review/PROGRAM-LOGIC-20261101.md` §4.2, §4.3, §5.2. Every claim of a composition is a slot
(`Obend.Slot`): its candidates are rewrite derivations, a candidate's supports are the members it
unfolds with what each unfolded to (`supports`), its judge is the claim checker, and a view is a
composition. The status of a claim is the slot's read of its selection at the view
(`readStatus`): `unchecked` (no candidate), `checked` (usable), `blocked` naming exactly the dead
supports (`status_blocked_exact`, from `Slot.read_blocked_exact`), `refuted` at a ground instance,
or `attested`. A usable read at a view is an accepted check there (`usable_checks`, through T3).

The certificate is tied to its claim by the claim's content address (`Core.Code.address (quote c)`,
`digest_of_quote`): the registered format `claimFormat` (`rewrite@1`) decodes a statement only when
its stated address is the quoted claim's, so a certificate presented with another claim is refused
`malformed` before any step runs. Statements, certificates and receipts are JSON, terms as their
quotations (`Data` on the wire, `Spec.DataWire`).
-/
public import Obend.Logic.Frame
public import Obend.Logic.Ground
public import Obend.Slot
public import Obend.Spec.DataWire
@[expose] public section
namespace Obend.Logic
open Obend.Core.Term
open Obend.Core.Data (Data)
open Obend.Equiv
open Lean (Json toJson)
set_option autoImplicit false

/-! ## The claim judge -/

theorem liftVerdict_ne {v : Judge.Verdict RClause} (h : liftVerdict v ≠ .uncovered) : v ≠ .uncovered := by
  cases v <;> simp_all [liftVerdict]

theorem claimCheck_mono {k k' : Nat} {o : ClaimObj} {steps : List RStep} (le : k ≤ k')
    (hne : claimCheck k o steps ≠ .uncovered) : claimCheck k' o steps = claimCheck k o steps := by
  unfold claimCheck at hne ⊢
  by_cases hw : o.wellFormed = true
  · simp only [hw, ite_true] at hne ⊢
    cases hs : o.sides with
    | none => rfl
    | some x =>
      obtain ⟨_, l, r⟩ := x
      rw [hs] at hne
      simp only
      rw [rewriteWith_mono le (liftVerdict_ne hne)]
  · simp only [hw] at hne ⊢; rfl

/-- **The claim judge.** Objects are claims of compositions, certificates derivations. It never
refutes: the ground judge does. -/
instance claimJudge : Judge ClaimObj (List RStep) where
  Clause := ClaimClause
  Meaning o _ := claimMeaning o
  check := claimCheck
  sound := by intro k o steps h; exact claim_sound h
  refutes _ := false
  refuted := by intro _ _ _ _ _ h hk; cases hk
  Fragment o := ∃ steps k, claimCheck k o steps = .ok
  complete := by rintro o ⟨steps, k, h⟩ _; exact ⟨steps, k, h⟩
  mono := by intro k k' o steps le hne; exact claimCheck_mono le hne

/-! ## Supports -/

/-- A support: a member the derivation unfolds, with the provider and body it unfolded to. -/
structure Support where
  member : String
  unfolded : Option (String × Term)

def optEq : Option (String × Term) → Option (String × Term) → Bool
  | none, none => true
  | some (a, t), some (b, u) => a == b && Obend.Law.termEq t u
  | _, _ => false

theorem optEq_sound {x y : Option (String × Term)} (h : optEq x y = true) : x = y := by
  match x, y, h with
  | none, none, _ => rfl
  | some (a, t), some (b, u), h =>
    simp only [optEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, termEq_sound' h.2]

/-- The supports of a derivation for a claim. -/
def supports (o : ClaimObj) (steps : List RStep) : List Support :=
  (membersList steps).map fun m => ⟨m, symUnfold o.comp o.self m⟩

/-- A support holds at a view (a composition) when the member unfolds there as it did. -/
def Support.holds (C : Composition) (s : Nat) (sp : Support) : Bool := optEq (symUnfold C s sp.member) sp.unfolded

/-- The claim's slot at grade `k`. -/
def claimSlot (o : ClaimObj) (k : Nat) : Obend.Slot.Slot Support (List RStep) where
  supports := supports o
  judge steps := claimCheck k o steps == .ok

/-- **A usable read is an accepted check at the view.** If the claim's selected derivation reads
usable at the composition `C'` (with the claim at index `j'` there, well formed), the claim checker
accepts it there: T3 with the slot's supports as its hypothesis. -/
theorem usable_checks {o : ClaimObj} {k : Nat} {steps : List RStep} {C' : Composition} {j' : Nat}
    {ev : List (Support × Bool)}
    (h : (claimSlot o k).read (Support.holds C' o.self) (some steps) = .usable steps ev)
    (hwf : ({ o with comp := C', layer := j' } : ClaimObj).wellFormed = true) :
    claimCheck k { o with comp := C', layer := j' } steps = .ok := by
  have ⟨hj, hall⟩ := (Obend.Slot.read_usable_supports _ _ steps).1 ⟨ev, h⟩
  have hok : claimCheck k o steps = .ok := by simpa [claimSlot] using hj
  refine claim_frame hok (fun m hm => ?_) hwf
  have := hall ⟨m, symUnfold o.comp o.self m⟩ (by simp only [claimSlot, supports, List.mem_map]; exact ⟨m, hm, rfl⟩)
  exact optEq_sound this

/-! ## Status: the slot's read -/

/-- What a claim's status says. -/
inductive Status where
  /-- no candidate: the obligation is a hole -/
  | unchecked
  /-- the selected certificate is usable at this view -/
  | checked (format trust : String) (address : Nat)
  /-- the selected certificate's supports were withdrawn, by member -/
  | blocked (members : List String)
  /-- a ground run returned `false` at this instance -/
  | refuted (args : List Data)
  /-- a named party's word, nothing re-checked -/
  | attested (who : String)

def Status.label : Status → String
  | .unchecked => "unchecked"
  | .checked .. => "checked"
  | .blocked .. => "blocked"
  | .refuted .. => "refuted"
  | .attested .. => "attested"

/-- The status of claim `o` at the view `C` (the claim at index `j` there): a refutation first,
else the slot's read of the selection. -/
def readStatus (o : ClaimObj) (k : Nat) (C : Composition) (selected : Option (List RStep))
    (refutation : Option (List Data)) (attestation : Option String) : Status :=
  match refutation with
  | some ds => .refuted ds
  | none =>
    match (claimSlot o k).read (Support.holds C o.self) selected with
    | .empty => match attestation with
      | some who => .attested who
      | none => .unchecked
    | .usable _ _ => .checked "rewrite@1" "compiled" (Obend.Core.Code.address o.claim)
    | .blocked _ dead => .blocked (dead.map (·.member))
    | .rejected _ => .unchecked

/-- **A blocked status names exactly the members whose support is dead at the view.** -/
theorem status_blocked_exact {o : ClaimObj} {k : Nat} {C : Composition} {steps : List RStep}
    {att : Option String} {ms : List String}
    (h : readStatus o k C (some steps) none att = .blocked ms) :
    ∃ dead, ms = dead.map (·.member) ∧ dead ≠ [] ∧
      ∀ sp, sp ∈ dead ↔ sp ∈ supports o steps ∧ sp.holds C o.self = false := by
  unfold readStatus at h
  simp only at h
  cases hr : (claimSlot o k).read (Support.holds C o.self) (some steps) with
  | empty => rw [hr] at h; cases att <;> cases h
  | rejected c => rw [hr] at h; cases h
  | usable c ev => rw [hr] at h; cases h
  | blocked c d =>
    rw [hr] at h
    cases h
    obtain ⟨hne, hd⟩ := Obend.Slot.read_blocked_exact (claimSlot o k) _ steps c d hr
    exact ⟨d, rfl, hne, fun sp => by simpa [claimSlot] using hd sp⟩

/-! ## The wire -/

/-- A term on the wire: its quotation. -/
def termJson (t : Term) : Json := Obend.Spec.DataWire.dataJson (Obend.Core.Code.quote t)

def wireDepth : Nat := 1000000

def termOf (j : Json) : Except String Term := do
  let d ← Obend.Spec.DataWire.decodeData wireDepth j
  match Obend.Core.Code.unquote d with
  | some t => pure t
  | none => throw "not the quotation of a term"

def rstepJson : RStep → Json
  | .run n => Json.mkObj [("run", toJson n)]
  | .lateBinding m l => Json.mkObj [("lateBinding", Json.mkObj [("member", toJson m), ("layer", toJson l)])]
  | .assoc d => Json.mkObj [("assoc", toJson d)]
  | .composeAssoc d => Json.mkObj [("composeAssoc", toJson d)]
  | .congr C a inner => Json.mkObj [("congr", Json.mkObj [("context", termJson C), ("hole", termJson a),
      ("inner", Json.arr (inner.map rstepJson).toArray)])]
  | .trans f s => Json.mkObj [("trans", Json.arr #[Json.arr (f.map rstepJson).toArray, Json.arr (s.map rstepJson).toArray])]

def rstepOf : Nat → Json → Except String RStep
  | 0, _ => throw "derivation nesting capacity"
  | fuel + 1, j => do
    if let .ok n := j.getObjValAs? Nat "run" then return .run n
    if let .ok b := j.getObjVal? "lateBinding" then
      return .lateBinding (← b.getObjValAs? String "member") (← b.getObjValAs? String "layer")
    if let .ok d := j.getObjValAs? Bool "assoc" then return .assoc d
    if let .ok d := j.getObjValAs? Bool "composeAssoc" then return .composeAssoc d
    if let .ok c := j.getObjVal? "congr" then
      let inner ← (← c.getObjVal? "inner").getArr?
      return .congr (← termOf (← c.getObjVal? "context")) (← termOf (← c.getObjVal? "hole"))
        (← inner.toList.mapM (rstepOf fuel))
    if let .ok t := j.getObjVal? "trans" then
      let a ← t.getArr?
      let (some f, some s) := (a[0]?, a[1]?) | throw "trans: two derivations"
      return .trans (← (← f.getArr?).toList.mapM (rstepOf fuel)) (← (← s.getArr?).toList.mapM (rstepOf fuel))
    throw "unknown derivation step"

def stepsOf (j : Json) : Except String (List RStep) := do
  (← j.getArr?).toList.mapM (rstepOf 4096)

/-- The statement of a claim on the wire: the quoted claim with its content address, the quoted
object, the claim's layer and arity. -/
def statementJson (o : ClaimObj) : Json :=
  Json.mkObj [("claim", termJson o.claim), ("address", toJson (toString (Obend.Core.Code.address o.claim))),
    ("object", termJson o.comp.object), ("layer", toJson o.layer), ("arity", toJson o.arity)]

/-- Decode a statement; refused when the stated address is not the quoted claim's. -/
def statementOf (s : String) : Except String ClaimObj := do
  let j ← Json.parse s
  let claim ← termOf (← j.getObjVal? "claim")
  let object ← termOf (← j.getObjVal? "object")
  let stated ← j.getObjValAs? String "address"
  unless stated == toString (Obend.Core.Code.address claim) do
    throw s!"the stated address {stated} is not the quoted claim's"
  let some comp := decodeObject object | throw "the object is not fix (compose …) {seed}"
  return ⟨comp, ← j.getObjValAs? Nat "layer", claim, ← j.getObjValAs? Nat "arity"⟩

def certificateOf (s : String) : Except String (List RStep) := do
  stepsOf (← (← Json.parse s).getObjVal? "steps")

/-- The planted bad claim: an open claim term (`self` free), refused `illFormed` at every grade. -/
def badClaim : ClaimObj := ⟨⟨{ name := "", metadata := .record [], fields := [] }, [], []⟩, 0, .bound 0, 0⟩

theorem badClaim_refused : claimCheck 0 badClaim [] = .refused .illFormed [] := by decide +kernel

/-- **The registered format `rewrite@1`.** -/
def claimFormat : Judge.Format where
  name := "rewrite"
  version := "1"
  Obj := ClaimObj
  Cert := List RStep
  judge := claimJudge
  decodeObj := statementOf
  decodeCert := certificateOf
  trust := .compiled
  regime := .semidecidable
  bad := (badClaim, [])
  badGrade := 0
  bad_refused := ⟨_, _, badClaim_refused⟩

end Obend.Logic
end
