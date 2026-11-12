module
/-
# Obend.Vault.FormCheck — each judgment of a form, checked once with its changing parts open

A fill of a form is judged by judgments (`Obend.Vault.JudgeCall`): each page it writes by its own
laws (`Prepared.call`), and by the laws over links of every page linking to it (`Prepared.theirCalls`),
each a term the judge runs (`JudgeCall.term`: the law applied to the old state, the new and the
request). A fill changes only some of that term: the moved field, the measures a write moves (its
bytes, its version, its poster), and the request (who signs, the turn, the height). The CHECK of a
judgment (`unitOf`, a `CheckUnit`) is that term with those parts declared holes
(`PartialTyping.hole`): the state's changing fields (`holeOut`) and the request (`CheckUnit.req`).

* **The judge runs the checked term** (`judge_runs_checked`): a judgment's term IS its check's term
  filled with the values its write holds and its request (`fillOf`), exactly, where the law has no
  holes of its own (`holeFree`, part of `CheckUnit.accepted`).
* **The request is typed** (`requestBy_typed`): whoever signs, on any occasion, with any facts.
* **Checked once** (`judged_typed`, `kept_typed`): a judgment whose check the checker accepted is
  typed by that check's derivation through the fill lemma (`fill_typed`), not checked itself.
* **The residual reads true** (`coreTerm_evaluates`, `residual_reads`): the form's residual over its
  natural holes, as a Core term filled with a fill's naturals, evaluates to the value the fill's leg
  leaves (`5 + amount` filled with 30 evaluates to `35`), the value the judge then reads at the hole.
* **What a capture checks** (`Form.checksAt`): every judgment a fill makes at the capture's store, for
  fills that put 1 for each natural hole and each captured page for each page hole (the check does not
  depend on the amount: the moved field is a hole of it), those the checker accepts. They are world
  state, kept as records (`CheckRecord`, `Replay.World.checked`) made by the turn that captured or
  abstracted the form, so by every replay of its log. A command that uses a form's checks makes them
  again from the records (`checksOf`): a record is not the checker's word, and made again the checks
  are the capture's (`checksOf_records`). A fill's judgment is never checked.
* **Kept or checked now** (`classify`): a judgment of a proposal is kept when its check is one the
  capture made; else it is checked now. None is checked twice (`rechecked_zero`).
-/
public import Obend.Vault.Form
public import Obend.Core.Proofs.FillTyping
public import Obend.Law.Proofs.Fill
@[expose] public section

namespace Obend.Vault.Form

set_option autoImplicit false

open Obend.Core.Data (Data)
open Obend.Core.Term (Term)
open Obend.Core.Ty (Ty Binding Context validContext safeUses)
open Obend.Core.Check (Assumptions HoleDecl PartialTyping Annotations)
open Obend.Core.Bidirectional (checkAt Against)
open Obend.Law (fnTy reqTy verdictTy lawTy)
open Obend.Spec.Law (LawExpr)
open Obend.Core.Proofs.FillTyping (FillersTyped FillerTyped checkAt_fill)
open Obend.Core.Term (Value Steps Evaluates Primitive)
open Obend.Core.TermTraverse (Shape Tag encode)
open Obend.Core.Traverse (Tree)
open Obend.Doc (Graph AtomId)

/-! ## The form's residual as a Core term -/

/-- A hole's number: its place among the form's holes. -/
def Form.holeIndex (f : Form) (h : String) : Nat := (f.holes.map (·.1)).idxOf h

/-- A residual expression as a Core term over the form's natural holes; none where it still reads a
page (a page the capture does not know is read where the form is judged). -/
def NExpr.coreTerm (f : Form) : NExpr → Option Term
  | .lit n => some (.nat n)
  | .hole h => if f.holes.lookup h == some .nat then some (.hole (f.holeIndex h) []) else none
  | .field _ _ => none
  | .add x y => do pure (.binary .add (← x.coreTerm f) (← y.coreTerm f))
  | .sub x y => do pure (.binary .subtract (← x.coreTerm f) (← y.coreTerm f))

/-- A fill's naturals, as fillers of the holes they fill: a literal. -/
def Form.natFill (f : Form) (a : Assignment) (i : Nat) : Option Term :=
  match f.holes[i]? with
  | some (h, .nat) => (a.nats.lookup h).map Term.nat
  | _ => none

/-! ## Terms, compared; terms with no holes -/

/-- Terms are equal when their shapes are (`Obend.Law.treeEq`, sound and reflexive). -/
instance : DecidableEq Term := fun a b =>
  if h : Obend.Law.treeEq (encode a) (encode b) = true then
    isTrue (Obend.Core.TermTraverse.encode_injective (Obend.Core.Code.treeEq_sound h))
  else isFalse fun e => h (e ▸ Obend.Core.Code.treeEq_refl _)

mutual
/-- A shape with no hole node. -/
def holeFreeS : Shape → Bool
  | .var _ => true
  | .bind b => holeFreeS b
  | .node (.hole _) _ => false
  | .node _ cs => holeFreesS cs
def holeFreesS : List Shape → Bool
  | [] => true
  | c :: cs => holeFreeS c && holeFreesS cs
end

mutual
theorem fillS_holeFree (θ : Nat → Option Shape) :
    ∀ s : Shape, holeFreeS s = true → Obend.Core.TermTraverse.fillS θ s = s
  | .var _, _ => Obend.Core.TermTraverse.fillS_var _ _
  | .bind b, h => by
    rw [Obend.Core.TermTraverse.fillS_bind, fillS_holeFree θ b (by simpa [holeFreeS] using h)]
  | .node tag cs, h => by
    rw [Obend.Core.TermTraverse.fillS_node]
    cases tag
    case hole => simp [holeFreeS] at h
    all_goals
      simp only [holeFreeS] at h
      simp only [Obend.Core.TermTraverse.fillNode, fillsS_holeFree θ cs h]
theorem fillsS_holeFree (θ : Nat → Option Shape) :
    ∀ cs : List Shape, holeFreesS cs = true → cs.map (Obend.Core.TermTraverse.fillS θ) = cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [holeFreesS, Bool.and_eq_true] at h
    simp only [List.map_cons, fillS_holeFree θ c h.1, fillsS_holeFree θ cs h.2]
end

/-- A term with no hole of its own. -/
def holeFree (t : Term) : Bool := holeFreeS (encode t)

/-- **A term with no holes is its own fill.** -/
theorem fill_holeFree {t : Term} (h : holeFree t = true) (θ : Nat → Option Term) : t.fill θ = t :=
  Obend.Core.TermTraverse.encode_injective (by
    rw [Obend.Core.Term.encode_fill, fillS_holeFree _ _ h])

mutual
/-- Data has no holes: its term is its own fill. -/
theorem data_term_fill (θ : Nat → Option Term) : (d : Data) → d.term.fill θ = d.term
  | .natural _ => by simp [Data.term, Term.fill]
  | .boolean _ => by simp [Data.term, Term.fill]
  | .label _ => by simp [Data.term, Term.fill]
  | .record fs => by
    simp only [Data.term, Term.fill]
    rw [fieldsTerm_fill θ fs]
  | .variant _ p => by
    simp only [Data.term, Term.fill]
    rw [data_term_fill θ p]
theorem fieldsTerm_fill (θ : Nat → Option Term) :
    (fs : List (String × Data)) →
      (Obend.Core.Data.fieldsTerm fs).map (fun f => (f.1, f.2.fill θ)) = Obend.Core.Data.fieldsTerm fs
  | [] => rfl
  | (_, v) :: rest => by
    simp only [Obend.Core.Data.fieldsTerm, List.map_cons]
    rw [data_term_fill θ v, fieldsTerm_fill θ rest]
end

/-! ## A page state with holes where a write changes it -/

/-- Where the field `k` of a state is a hole of the checked term, the hole's type and the filler the
state gives it: the moved fields and every measure (what a write changes: the moved field, the bytes,
the version, the poster), where they hold a natural or a label. -/
def slotOf (moved : List String) (k : String) (v : Data) : Option (Ty × Term) :=
  if moved.contains k || measureNames.contains k then
    match v with
    | .natural m => some (.natural, .nat m)
    | .label s => some (.label, .label s)
    | _ => none
  else none

theorem slotOf_some {moved : List String} {k : String} {v : Data} {x : Ty × Term}
    (h : slotOf moved k v = some x) :
    (x.1 = .natural ∧ ∃ m, x.2 = .nat m ∧ v = .natural m) ∨ (x.1 = .label ∧ ∃ s, x.2 = .label s ∧ v = .label s) := by
  unfold slotOf at h
  split at h
  · cases v with
    | natural m => simp only [Option.some.injEq] at h; subst h; exact .inl ⟨rfl, m, rfl, rfl⟩
    | label s => simp only [Option.some.injEq] at h; subst h; exact .inr ⟨rfl, s, rfl, rfl⟩
    | _ => simp at h
  · cases h

/-- The holes of a record's fields, in order: each a type and a filler. -/
def slotsOf (moved : List String) (fs : List (String × Data)) : List (Ty × Term) :=
  fs.filterMap fun (k, v) => slotOf moved k v

/-- The fields with each slot a hole, numbered from `i`. -/
def holeOutFields (moved : List String) : Nat → List (String × Data) → List (String × Term)
  | _, [] => []
  | i, (k, v) :: fs => match slotOf moved k v with
    | some _ => (k, .hole i []) :: holeOutFields moved (i + 1) fs
    | none => (k, v.term) :: holeOutFields moved i fs

/-- **A state with holes**: a record whose moved fields and measures are holes. -/
def holeOut (moved : List String) : Data → Term
  | .record fs => .record (holeOutFields moved 0 fs)
  | d => d.term

/-- The slots of a state. -/
def stateSlots (moved : List String) : Data → List (Ty × Term)
  | .record fs => slotsOf moved fs
  | _ => []

/-- Each of a list, numbered from `i`. -/
def numbered {α β : Type} (g : α → β) : Nat → List α → List (Nat × β)
  | _, [] => []
  | i, x :: xs => (i, g x) :: numbered g (i + 1) xs

theorem lookup_numbered {α β : Type} (g : α → β) :
    ∀ (i n : Nat) (l : List α), (numbered g i l).lookup (i + n) = l[n]?.map g
  | _, _, [] => rfl
  | i, 0, x :: xs => by simp [numbered]
  | i, n + 1, x :: xs => by
    have := lookup_numbered g (i + 1) n xs
    simp only [numbered, List.lookup, List.getElem?_cons_succ]
    rw [show i + (n + 1) = i + 1 + n by omega] at *
    have hne : (i + 1 + n == i) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [hne]
    exact this

/-- The declared holes of a state: each slot's type, over no variables. -/
def stateHoles (moved : List String) (d : Data) : List (Nat × HoleDecl) :=
  numbered (fun x => (⟨[], x.1⟩ : HoleDecl)) 0 (stateSlots moved d)

/-- The fill a state gives its holes: each slot its value. -/
def stateFill (moved : List String) (d : Data) (i : Nat) : Option Term := ((stateSlots moved d)[i]?).map (·.2)

theorem holeOutFields_fill (moved : List String) (θ : Nat → Option Term) :
    ∀ (i : Nat) (fs : List (String × Data)),
      (∀ j, j < (slotsOf moved fs).length → θ (i + j) = ((slotsOf moved fs)[j]?).map (·.2)) →
      (holeOutFields moved i fs).map (fun p => (p.1, p.2.fill θ)) = Obend.Core.Data.fieldsTerm fs
  | _, [], _ => rfl
  | i, (k, v) :: fs, hθ => by
    simp only [holeOutFields, slotsOf, List.filterMap_cons] at hθ ⊢
    cases hs : slotOf moved k v with
    | none =>
      simp only [hs] at hθ ⊢
      simp only [List.map_cons, data_term_fill, Obend.Core.Data.fieldsTerm]
      exact congrArg _ (holeOutFields_fill moved θ i fs hθ)
    | some x =>
      simp only [hs] at hθ ⊢
      have h0 := hθ 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.map_some] at h0
      have hv : x.2 = v.term ∧ x.2.substitute (Obend.Core.Term.listSubst []) = x.2 := by
        rcases slotOf_some hs with ⟨_, m, h1, h2⟩ | ⟨_, m, h1, h2⟩ <;>
          (rw [h1, h2]; exact ⟨rfl, by simp [Term.substitute]⟩)
      simp only [List.map_cons, Obend.Core.Data.fieldsTerm, Term.fill, h0, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, true_and]
      refine ⟨by rw [hv.2, hv.1], holeOutFields_fill moved θ (i + 1) fs fun j hj => by
        have := hθ (j + 1) (by simpa [slotsOf] using hj)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        simpa [slotsOf] using this⟩

/-- **The state is its holed state filled with its own values**: the holed state, filled with the
values the state holds at its holes (and anything past them), is the state's term. -/
theorem holeOut_fill (moved : List String) (d : Data) (θ : Nat → Option Term)
    (hθ : ∀ j, j < (stateSlots moved d).length → θ j = ((stateSlots moved d)[j]?).map (·.2)) :
    (holeOut moved d).fill θ = d.term := by
  cases d with
  | record fs =>
    simp only [holeOut, Term.fill, Obend.Core.Data.Data.term]
    exact congrArg _ (holeOutFields_fill moved _ 0 fs (fun j hj => by simpa [stateSlots] using hθ j hj))
  | _ => exact data_term_fill _ _

theorem slotsOf_typed (moved : List String) (fs : List (String × Data)) :
    ∀ x ∈ slotsOf moved fs, (x.1 = .natural ∧ ∃ m, x.2 = .nat m) ∨ (x.1 = .label ∧ ∃ s, x.2 = .label s) := by
  intro x hx
  obtain ⟨⟨k, v⟩, _, hs⟩ := List.mem_filterMap.1 hx
  rcases slotOf_some hs with ⟨h1, m, h2, _⟩ | ⟨h1, m, h2, _⟩
  · exact .inl ⟨h1, m, h2⟩
  · exact .inr ⟨h1, m, h2⟩

/-- Each slot's filler is typed at its type, over no variables. -/
theorem slot_typed (moved : List String) (d : Data) (hs : List (Nat × HoleDecl)) {x : Ty × Term}
    (hmem : x ∈ stateSlots moved d) : FillerTyped { holes := hs } ⟨[], x.1⟩ x.2 := by
  have hk : (x.1 = .natural ∧ ∃ m, x.2 = .nat m) ∨ (x.1 = .label ∧ ∃ s, x.2 = .label s) := by
    cases d with
    | record fs => exact slotsOf_typed moved fs x hmem
    | _ => simp [stateSlots] at hmem
  rcases hk with ⟨h1, m, h2⟩ | ⟨h1, s, h2⟩
  · refine ⟨[], ?_, by simp [validContext], fun j b h => by simp at h⟩
    rw [h1, h2]; exact .natural [] m
  · refine ⟨[], ?_, by simp [validContext], fun j b h => by simp at h⟩
    rw [h1, h2]; exact .label [] s

theorem lookup_append_of_none {β : Type} :
    ∀ (l₁ l₂ : List (Nat × β)) (n : Nat), l₁.lookup n = none → (l₁ ++ l₂).lookup n = l₂.lookup n
  | [], _, _, _ => rfl
  | (k, v) :: l₁, l₂, n, h => by
    simp only [List.lookup] at h ⊢
    split at h
    · cases h
    · rename_i hk
      simp only [List.cons_append, List.lookup, hk]
      exact lookup_append_of_none l₁ l₂ n h

theorem lookup_append_of_some {β : Type} :
    ∀ (l₁ l₂ : List (Nat × β)) (n : Nat) (x : β), l₁.lookup n = some x → (l₁ ++ l₂).lookup n = some x
  | [], _, _, _, h => by cases h
  | (k, v) :: l₁, l₂, n, x, h => by
    simp only [List.lookup] at h ⊢
    split at h
    · rename_i hk; simp only [List.cons_append, List.lookup, hk]; exact h
    · rename_i hk
      simp only [List.cons_append, List.lookup, hk]
      exact lookup_append_of_some l₁ l₂ n x h

/-! ## The request a law is applied to -/

theorem optNat_typed (hs : List (Nat × HoleDecl)) :
    ∀ o : Option Nat, PartialTyping { holes := hs } [] (Obend.Law.optNat o).term Obend.Law.optNatTy []
  | none => .inject (fuel := 3) (.record (.nil []) rfl) rfl rfl
  | some k => .inject (fuel := 3) (.natural [] k) rfl rfl

theorem occ_typed (hs : List (Nat × HoleDecl)) :
    ∀ k : Occ, PartialTyping { holes := hs } [] k.data.term Obend.Law.occasionTy []
  | .write => .inject (fuel := 7) (.record (.nil []) rfl) rfl rfl
  | .birth => .inject (fuel := 7) (.record (.nil []) rfl) rfl rfl
  | .adopt => .inject (fuel := 7) (.label [] "page") rfl rfl

/-- **A request is typed at `reqTy`**: whoever signs it, whoever's authority it carries, on any
occasion, with any facts (the turn, the height, the subject, the caller). -/
theorem requestBy_typed (hs : List (Nat × HoleDecl)) (who pr : String) (k : Occ) (facts : Obend.Spec.Law.Facts) :
    PartialTyping { holes := hs } [] (requestBy who pr k facts).term reqTy [] :=
  .record (.cons (.label [] who) (.cons (optNat_typed hs facts.caller) (.cons (.natural [] facts.height)
    (.cons (.natural [] 0) (.cons (occ_typed hs k) (.cons (.label [] pr) (.cons (optNat_typed hs facts.subject)
    (.cons (.natural [] facts.turn) (.cons (.natural [] 0) (.nil []) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)
    (by simp [Data.term, Obend.Core.Data.fieldsTerm,
      Obend.Core.Check.labelsDistinct])

/-! ## A judgment, checked once with its state's holes open -/

/-- A law applied to its old and new states and its request. -/
def overStates (L o n rq : Term) : Term := .app (.app (.app L o) n) rq

/-- The path of the `case` the effective law opens on its `i`-th law (`Obend.Law.chainAt`): under the
three applications of the check and the effective law's three binders, then each earlier law's
`ok` arm. -/
def chainPath (i : Nat) : List Nat := [0, 0, 0, 0, 0, 0] ++ (List.replicate i [1, 0]).flatten

/-- What the checker needs to apply the effective law of `n` laws, compiled for `S`: the type of each
function applied, the effective law's at the top, each law's at its `case`. -/
def lawAnnotations (S : Ty) (n : Nat) : Annotations := fun p =>
  let V := Obend.Law.inheritedVerdictTy
  if p = [] then some ⟨fnTy reqTy V, V, .unrestricted, .reusable⟩
  else if p = [0] then some ⟨fnTy S (fnTy reqTy V), fnTy reqTy V, .unrestricted, .reusable⟩
  else if p = [0, 0] then some ⟨Obend.Law.inheritedLawTy S, fnTy S (fnTy reqTy V), .unrestricted, .reusable⟩
  else if (List.range n).any (fun i => p == chainPath i ++ [0]) then
    some ⟨fnTy reqTy verdictTy, verdictTy, .unrestricted, .reusable⟩
  else if (List.range n).any (fun i => p == chainPath i ++ [0, 0]) then
    some ⟨fnTy S (fnTy reqTy verdictTy), fnTy reqTy verdictTy, .unrestricted, .reusable⟩
  else if (List.range n).any (fun i => p == chainPath i ++ [0, 0, 0]) then
    some ⟨lawTy S, fnTy S (fnTy reqTy verdictTy), .unrestricted, .reusable⟩
  else none

/-- **A judgment as a check**: at the page `page`, the laws `laws` of the page `pkg`, compiled for the
state type `S` and combined (`law`), applied to the old state and the new with the fields a write
changes left open (`old`, `new`), and to the request, open (the hole `req`: who signs, the turn,
the height). The holes are declared in `holes`. Compared whole: two judgments are one check when
everything in them is the same. -/
structure CheckUnit where
  page : String
  pkg : String
  laws : List String
  holes : List (Nat × HoleDecl)
  req : Nat
  S : Ty
  law : Term
  old : Term
  new : Term
deriving DecidableEq

/-- The theory a unit is checked in: its holes declared. -/
def CheckUnit.asm (u : CheckUnit) : Assumptions := { holes := u.holes }

/-- The term checked: the law over the holed states and the open request. -/
def CheckUnit.term (u : CheckUnit) : Term := overStates u.law u.old u.new (.hole u.req [])

/-- **The one check**: the checker on the law over the holed states and the open request, at the
type of the effective law's verdict (`Obend.Law.inheritedVerdictTy`: a refusal names its law). -/
def CheckUnit.check (u : CheckUnit) :
    Except Obend.Core.Bidirectional.CheckRefusal (Against u.asm [] u.term Obend.Law.inheritedVerdictTy) :=
  checkAt u.asm (lawAnnotations u.S u.laws.length) [] [] u.term Obend.Law.inheritedVerdictTy

/-- A unit the checker accepted, whose law has no holes of its own (a hole of the law would be filled
with the state's values). -/
def CheckUnit.accepted (u : CheckUnit) : Bool := holeFree u.law && u.check.toBool

/-- **The check of a judgment**: its law; its old state (the new, for a law over links); its new state
with the moved fields `moved` and the measures holes; the request a hole after them. -/
def unitOf (page : String) (moved : List String) (c : JudgeCall) : CheckUnit where
  page := page
  pkg := c.pkg
  laws := c.lin.map (·.1)
  holes := stateHoles moved c.n ++ [((stateSlots moved c.n).length, ⟨[], reqTy⟩)]
  req := (stateSlots moved c.n).length
  S := c.S
  law := Obend.Law.effective (compiled c.S c.pkg c.lin)
  old := if c.linked then holeOut moved c.n else c.o.term
  new := holeOut moved c.n

/-- **The fill a judgment gives its check**: the values its new state holds at the holes, and its
request. -/
def fillOf (moved : List String) (c : JudgeCall) (i : Nat) : Option Term :=
  if i = (stateSlots moved c.n).length then some c.rq.term else stateFill moved c.n i

mutual
/-- Data is closed: a substitution leaves its term alone. -/
theorem data_term_substitute (σ : Nat → Term) : (d : Data) → d.term.substitute σ = d.term
  | .natural _ => by simp [Data.term, Term.substitute]
  | .boolean _ => by simp [Data.term]
  | .label _ => by simp [Data.term]
  | .record fs => by
    simp only [Data.term, Term.substitute]
    rw [fieldsTerm_substitute σ fs]
  | .variant _ p => by
    simp only [Data.term, Term.substitute]
    rw [data_term_substitute σ p]
theorem fieldsTerm_substitute (σ : Nat → Term) :
    (fs : List (String × Data)) →
      (Obend.Core.Data.fieldsTerm fs).map (fun f => (f.1, f.2.substitute σ)) = Obend.Core.Data.fieldsTerm fs
  | [] => rfl
  | (_, v) :: rest => by
    simp only [Obend.Core.Data.fieldsTerm, List.map_cons]
    rw [data_term_substitute σ v, fieldsTerm_substitute σ rest]
end

theorem fillOf_slots (moved : List String) (c : JudgeCall) :
    ∀ j, j < (stateSlots moved c.n).length → fillOf moved c j = ((stateSlots moved c.n)[j]?).map (·.2) := by
  intro j hj
  simp [fillOf, Nat.ne_of_lt hj, stateFill]

/-- **The judge runs the checked term.** A judgment's term (`JudgeCall.term`, what `judge` runs) is
its check's term filled with the values its new state holds at the holes and with its request:
exactly, where the law has no holes of its own and a law over links reads the page as old and new. -/
theorem judge_runs_checked (page : String) (moved : List String) (c : JudgeCall)
    (hl : holeFree (unitOf page moved c).law = true) (hlk : c.linked = true → c.o = c.n) :
    c.term = (unitOf page moved c).term.fill (fillOf moved c) := by
  have hlaw := fill_holeFree hl (fillOf moved c)
  simp only [unitOf] at hlaw
  have hn := holeOut_fill moved c.n (fillOf moved c) (fillOf_slots moved c)
  have hrq : (Term.hole (stateSlots moved c.n).length []).fill (fillOf moved c) = c.rq.term := by
    simp only [Term.fill, fillOf, ite_true, List.map_nil]
    exact data_term_substitute _ _
  have hold : Term.fill (fillOf moved c) (if c.linked = true then holeOut moved c.n else c.o.term) = c.o.term := by
    cases hk : c.linked
    · simp [data_term_fill]
    · simp only [ite_true, hn, hlk hk]
  have fill_app : ∀ a b : Term, (Term.app a b).fill (fillOf moved c) = .app (a.fill (fillOf moved c)) (b.fill (fillOf moved c)) :=
    fun a b => by simp [Term.fill]
  simp only [JudgeCall.term, Obend.Law.applyLaw, CheckUnit.term, overStates, unitOf]
  rw [fill_app, fill_app, fill_app, hlaw, hold, hn, hrq]

/-- The fill a judgment gives its check is typed as the check declares its holes, where its request
is a request. -/
theorem fillOf_typed (page : String) (moved : List String) (c : JudgeCall)
    {who pr : String} {k : Occ} {facts : Obend.Spec.Law.Facts} (hrq : c.rq = requestBy who pr k facts) :
    FillersTyped (unitOf page moved c).asm (fillOf moved c) := by
  intro n t decl hθ hl
  simp only [CheckUnit.asm, unitOf] at hl
  have hnum := lookup_numbered (fun x => (⟨[], x.1⟩ : HoleDecl)) 0 n (stateSlots moved c.n)
  simp only [Nat.zero_add] at hnum
  by_cases hn : n = (stateSlots moved c.n).length
  · subst hn
    have hnone : (stateHoles moved c.n).lookup (stateSlots moved c.n).length = none := by
      simp [stateHoles, hnum]
    rw [lookup_append_of_none _ _ _ hnone] at hl
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
    subst hl
    simp only [fillOf, ite_true, Option.some.injEq] at hθ
    subst hθ
    rw [hrq]
    exact ⟨[], requestBy_typed _ who pr k facts, by simp [validContext], fun j b h => by simp at h⟩
  · simp only [fillOf, hn, ite_false, stateFill] at hθ
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hθ
    have hs : (stateHoles moved c.n).lookup n = some ⟨[], x.1⟩ := by simp [stateHoles, hnum, hx]
    rw [lookup_append_of_some _ _ _ _ hs] at hl
    simp only [Option.some.injEq] at hl
    subst hl
    exact slot_typed moved c.n _ (List.mem_of_getElem? hx)

/-- **Checked once.** A judgment whose check the checker accepted is typed, at the verdict's type, by
the derivation that check returned, through the fill lemma (`fill_typed`): its new state's values and
its request (`requestBy_typed`) fill the check's holes. The judgment's term is not checked. -/
theorem judged_typed (page : String) (moved : List String) (c : JudgeCall)
    (h : (unitOf page moved c).accepted = true) (hlk : c.linked = true → c.o = c.n)
    {who pr : String} {k : Occ} {facts : Obend.Spec.Law.Facts} (hrq : c.rq = requestBy who pr k facts) :
    ∃ us, PartialTyping (unitOf page moved c).asm [] c.term Obend.Law.inheritedVerdictTy us := by
  simp only [CheckUnit.accepted, Bool.and_eq_true] at h
  obtain ⟨hl, hc⟩ := h
  cases hr : (unitOf page moved c).check with
  | error e => rw [hr] at hc; cases hc
  | ok r =>
    have hu : r.uses = [] :=
      List.eq_nil_of_length_eq_zero (Obend.Core.MachineTyping.source_uses_length r.derivation)
    obtain ⟨u', typed, _, _⟩ := checkAt_fill hr (by simp [validContext]) (by rw [hu]; rfl)
      (fillOf_typed page moved c hrq)
    rw [judge_runs_checked page moved c hl hlk]
    exact ⟨u', typed⟩

/-! ## The residual, filled, evaluates to what the judge reads -/

theorem steps_trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with
  | refl => exact h2
  | next s _ ih => exact .next s (ih h2)

theorem steps_binaryLeft (p : Primitive) (r : Term) {a b : Term} (h : Steps a b) :
    Steps (.binary p a r) (.binary p b r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft p r s) ih

theorem steps_binaryRight (p : Primitive) {l : Term} (hl : Value l) {a b : Term} (h : Steps a b) :
    Steps (.binary p l a) (.binary p l b) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight p l hl s) ih

theorem lookup_idxOf {β : Type} : ∀ (l : List (String × β)) (h : String) (x : β), l.lookup h = some x →
    l[(l.map (·.1)).idxOf h]? = some (h, x)
  | [], _, _, hl => by simp at hl
  | (k, y) :: l, h, x, hl => by
    by_cases hk : h = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
      subst hl
      simp [List.idxOf_cons_self]
    · have hb : (h == k) = false := beq_eq_false_iff_ne.mpr hk
      simp only [List.lookup, hb] at hl
      have := lookup_idxOf l h x hl
      simp only [List.map_cons, List.idxOf_cons, show (k == h) = false from beq_eq_false_iff_ne.mpr (Ne.symm hk)]
      exact this

/-- **The residual, filled, evaluates to its value**: a residual expression over the form's natural
holes, as a Core term, filled with a fill's naturals, evaluates to the natural the fill makes it
(`5 + amount` filled with 30 evaluates to `35`). -/
theorem coreTerm_evaluates (f : Form) (a : Assignment) (k : Known) :
    ∀ (e : NExpr) {t : Term} {v : Nat}, e.coreTerm f = some t → (e.subst a).eval k = some v →
      Evaluates (t.fill (f.natFill a)) (.nat v)
  | .lit n, t, v, ht, hv => by
    simp only [NExpr.coreTerm, Option.some.injEq] at ht
    simp only [NExpr.subst, NExpr.eval, Option.some.injEq] at hv
    subst ht hv
    simp only [Term.fill]
    exact ⟨.refl _, .natural _⟩
  | .hole h, t, v, ht, hv => by
    simp only [NExpr.coreTerm] at ht
    split at ht
    · rename_i hn
      simp only [Option.some.injEq] at ht
      subst ht
      have hl : f.holes.lookup h = some .nat := by simpa using hn
      simp only [NExpr.subst] at hv
      split at hv
      · rename_i n hn'
        simp only [NExpr.eval, Option.some.injEq] at hv
        subst hv
        have hi := lookup_idxOf f.holes h .nat hl
        have hθ : f.natFill a (f.holeIndex h) = some (.nat n) := by
          simp only [Form.natFill, Form.holeIndex, hi, hn', Option.map_some]
        simp only [Term.fill, hθ]
        exact ⟨by simp [Term.substitute]; exact .refl _, .natural _⟩
      · simp [NExpr.eval] at hv
    · cases ht
  | .field _ _, t, v, ht, _ => by simp [NExpr.coreTerm] at ht
  | .add x y, t, v, ht, hv => by
    simp only [NExpr.coreTerm, bind, Option.bind] at ht
    cases hx : x.coreTerm f with
    | none => simp [hx] at ht
    | some tx =>
      cases hy : y.coreTerm f with
      | none => simp [hx, hy] at ht
      | some ty =>
        simp only [hx, hy, pure, Option.some.injEq] at ht
        subst ht
        simp only [NExpr.subst, NExpr.eval, bind, Option.bind] at hv
        cases hu : (x.subst a).eval k with
        | none => simp [hu] at hv
        | some u =>
          cases hw : (y.subst a).eval k with
          | none => simp [hu, hw] at hv
          | some w =>
            simp only [hu, hw, pure, Option.some.injEq] at hv
            subst hv
            obtain ⟨sx, _⟩ := coreTerm_evaluates f a k x hx hu
            obtain ⟨sy, _⟩ := coreTerm_evaluates f a k y hy hw
            refine ⟨?_, .natural _⟩
            simp only [Term.fill]
            exact steps_trans (steps_binaryLeft _ _ sx) (steps_trans (steps_binaryRight _ (.natural u) sy)
              (.next (.primitive _ _ _ _ (.natural u) (.natural w) rfl) (.refl _)))
  | .sub x y, t, v, ht, hv => by
    simp only [NExpr.coreTerm, bind, Option.bind] at ht
    cases hx : x.coreTerm f with
    | none => simp [hx] at ht
    | some tx =>
      cases hy : y.coreTerm f with
      | none => simp [hx, hy] at ht
      | some ty =>
        simp only [hx, hy, pure, Option.some.injEq] at ht
        subst ht
        simp only [NExpr.subst, NExpr.eval, bind, Option.bind] at hv
        cases hu : (x.subst a).eval k with
        | none => simp [hu] at hv
        | some u =>
          cases hw : (y.subst a).eval k with
          | none => simp [hu, hw] at hv
          | some w =>
            simp only [hu, hw] at hv
            split at hv
            · simp only [pure, Option.some.injEq] at hv
              subst hv
              obtain ⟨sx, _⟩ := coreTerm_evaluates f a k x hx hu
              obtain ⟨sy, _⟩ := coreTerm_evaluates f a k y hy hw
              refine ⟨?_, .natural _⟩
              simp only [Term.fill]
              exact steps_trans (steps_binaryLeft _ _ sx) (steps_trans (steps_binaryRight _ (.natural u) sy)
                (.next (.primitive _ _ _ _ (.natural u) (.natural w) rfl) (.refl _)))
            · cases hv

/-- **What a leg leaves at its pages, the residual computes**: for a move of a fill evaluated to its
two legs, the residual's debit and credit, as Core terms filled with the fill's naturals, evaluate
to the values the legs leave at the source and the destination. -/
theorem RMove.pair_after {k : Known} {r : RMove} {p : LegPair} (h : r.pair k = .ok p) :
    r.debit.eval k = some p.srcAfter ∧ r.credit.eval k = some p.dstAfter := by
  unfold RMove.pair at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; constructor <;> assumption)
    | cases h

theorem residual_reads (f : Form) (a : Assignment) (k : Known) {r : RMove} {p : LegPair}
    (hp : (r.subst a).pair k = .ok p) :
    (∀ t, r.debit.coreTerm f = some t → Evaluates (t.fill (f.natFill a)) (.nat p.srcAfter)) ∧
    (∀ t, r.credit.coreTerm f = some t → Evaluates (t.fill (f.natFill a)) (.nat p.dstAfter)) := by
  obtain ⟨hd, hc⟩ := RMove.pair_after hp
  exact ⟨fun t ht => coreTerm_evaluates f a k _ ht (by simpa [RMove.subst] using hd),
    fun t ht => coreTerm_evaluates f a k _ ht (by simpa [RMove.subst] using hc)⟩

/-! ## The judgments of a proposal -/

/-- **A fill's writes, prepared and not yet judged**: the membrane and the form's resources (`admit`),
the pins, and the write of every page the fill moves, prepared (`prepareAll`): what `judgeProposal`
then judges and lands. -/
def preparedOf (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) (hops : List Grant) (a : Assignment) :
    Except String (Admitted × List Prepared) :=
  match admit (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty (.label f.name) with
  | .error r => .error (refusalText f r)
  | .ok ad =>
    match admitFootprint (stateStore s.entries) ad.turn.readPins with
    | .error _ => .error "refused: its pins do not hold here"
    | .ok _ =>
      match legWritesOf H s ad.holder ad.turn.writeCells with
      | .error e => .error e
      | .ok ws =>
        match prepareAll s.entries .owner s.turn ad.holder s.environment ws with
        | .error e => .error e
        | .ok prs => .ok (ad, prs)

theorem commitTurn_prepared {es res : List Entry} {ws : List (Page × Graph × List (AtomId × String))}
    {who : Actor} {turn : Nat} {poster : String} {env : Environment} {prs : List Prepared}
    (h : commitTurn es res ws who turn poster env = .ok prs) :
    prepareAll es who turn poster env ws = .ok prs ∧ judgeAll es res (tipOf prs) prs = .ok () := by
  unfold commitTurn at h
  split at h
  · cases h
  · rename_i prs' hp
    split at h
    · cases h
    · rename_i hj
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨hp, hj⟩

/-- **What a proposal lands, its prepared writes are**: a landed proposal's admission and writes are
`preparedOf`'s, every one judged on the turn's tip (`judgeAll`), and the store after is all of them
landed. -/
theorem judgeProposal_prepared {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant}
    {a : Assignment} {ad : Admitted} {t : VaultTurn} (h : judgeProposal H s f hops a = .ok (s', ad, t)) :
    ∃ prs, preparedOf H s f hops a = .ok (ad, prs) ∧ judgeAll s.entries s.entries (tipOf prs) prs = .ok () ∧
      s' = s.landAll prs := by
  obtain ⟨had, hfp, ws, prs, hws, hprs, _, rfl⟩ := judgeProposal_ok h
  obtain ⟨hp, hj⟩ := commitTurn_prepared hprs
  exact ⟨prs, by simp [preparedOf, had, hfp, hws, hp], hj, rfl⟩

/-- **A prepared write's own judgment**: what `judgePrepared` admits, its own laws admit
(`Prepared.call`). -/
theorem judgePrepared_call {es res : List Entry} {pr : Prepared} {over : List (String × Data)}
    (h : judgePrepared es res pr over = .ok ()) : pr.call.verdict = .admitted := by
  unfold judgePrepared judgePreparedFrom at h
  cases hv : pr.call.verdict with
  | admitted => rfl
  | refused law why => simp [hv] at h
  | undecided why => simp [hv] at h

/-- The request of every prepared write is a request: who signs it, whose text it is, the occasion,
the facts. -/
theorem prepareWrite_rq {es : List Entry} {p : Page} {G' : Graph} {added : List (AtomId × String)}
    {who : Actor} {turn : Nat} {poster : String} {env : Environment} {pr : Prepared}
    (h : prepareWrite es p G' added who turn poster env = .ok pr) :
    pr.rq = requestBy pr.who.name pr.poster pr.occ pr.facts := by
  unfold prepareWrite prepareFrom at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | cases h

/-- The judgments of a turn's prepared writes, each with the page it is made at: the page's own laws
(where it has any), and the laws over links of every page linking to it, on the turn's tip: the
judgments `judgeAll` makes (`commitTurn`, the store's entries for both lists). -/
def callsOf (es : List Entry) (prs : List Prepared) : List (String × JudgeCall) :=
  prs.flatMap fun pr =>
    (if pr.lin.isEmpty then [] else [(pr.p.name, pr.call)]) ++
      (pr.theirCalls es es (tipOf prs)).map fun c => (pr.p.name, c)

/-- Every judgment of a turn's writes reads the page as old and new where it judges a law over links. -/
theorem callsOf_linked (es : List Entry) (prs : List Prepared) :
    ∀ x ∈ callsOf es prs, x.2.linked = true → x.2.o = x.2.n := by
  intro x hx hl
  simp only [callsOf, List.mem_flatMap, List.mem_append, List.mem_map] at hx
  obtain ⟨pr, _, hx⟩ := hx
  rcases hx with hx | ⟨c, hc, rfl⟩
  · split at hx
    · cases hx
    · simp only [List.mem_singleton] at hx; subst hx; simp [Prepared.call] at hl
  · simp only [Prepared.theirCalls, List.mem_flatMap] at hc
    obtain ⟨e, _, hc⟩ := hc
    split at hc
    · split at hc
      · split at hc
        · cases hc
        · split at hc
          · simp only [List.mem_singleton] at hc; subst hc; rfl
          · cases hc
      · cases hc
    · cases hc

/-! ## What a capture checks -/

/-- The fills a capture checks with: each natural hole 1, each page hole each page the form captured.
(A judgment's check does not depend on the amount: the moved field is a hole of it.) -/
def Form.witnesses (f : Form) : List Assignment :=
  let nats := f.holes.filterMap fun (h, t) => if t == .nat then some (h, 1) else none
  let pageHoles := f.holes.filterMap fun (h, t) => if t == .page then some h else none
  (pageHoles.foldr (fun h acc => acc.flatMap fun ps => f.cells.map fun c => (h, c.name) :: ps) [[]]).map
    fun ps => { nats := nats, pages := ps }

/-- What a check is made from: a judgment (its request aside, which the check leaves open) at a
page, with the fields it leaves open. Small, and enough to make the check again (`CheckKey.unit`). -/
structure CheckKey where
  page : String
  moved : List String
  S : Ty
  pkg : String
  lin : List (String × LawExpr)
  o : Data
  n : Data
  linked : Bool
deriving DecidableEq

/-- The judgment a key stands for, its request left unread. -/
def CheckKey.call (k : CheckKey) : JudgeCall := ⟨k.S, k.pkg, k.lin, k.o, k.n, .record [], k.linked⟩

/-- The check a key makes. -/
def CheckKey.unit (k : CheckKey) : CheckUnit := unitOf k.page k.moved k.call

/-- The key of a judgment at a page. -/
def keyOf (page : String) (moved : List String) (c : JudgeCall) : CheckKey :=
  ⟨page, moved, c.S, c.pkg, c.lin, c.o, c.n, c.linked⟩

/-- **A judgment's check does not read its request**: a key makes the judgment's own check. -/
theorem keyOf_unit (page : String) (moved : List String) (c : JudgeCall) :
    (keyOf page moved c).unit = unitOf page moved c := rfl

/-- A check the vault made and the checker accepted, of a judgment of the form `form`. -/
structure Checked where
  form : String
  key : CheckKey
  ok : key.unit.accepted = true

/-- The check itself. -/
def Checked.unit (c : Checked) : CheckUnit := c.key.unit

instance : DecidableEq Checked := fun a b =>
  if h : a.form = b.form ∧ a.key = b.key then
    isTrue (by cases a; cases b; simp only at h; obtain ⟨rfl, rfl⟩ := h; rfl)
  else isFalse fun e => h (by subst e; exact ⟨rfl, rfl⟩)

/-- Keep a key whose check the checker accepts. -/
def Checked.of (form : String) (k : CheckKey) : Option Checked :=
  if h : k.unit.accepted = true then some ⟨form, k, h⟩ else none

/-- **What a capture checks, once**: the check of every judgment a fill of the form makes at the store
`s`, for each witness fill (`preparedOf`, `callsOf`), each once, those the checker accepts. -/
def Form.checksAt (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) : List Checked :=
  let keys := f.witnesses.flatMap fun a =>
    match preparedOf H s f [] a with
    | .ok (_, prs) => (callsOf s.entries prs).map fun x => keyOf x.1 f.assets x.2
    | .error _ => []
  -- each check once: a later key whose check an earlier key makes is dropped
  let once := keys.foldl (fun acc k => if acc.any (·.unit == k.unit) then acc else acc ++ [k]) []
  once.filterMap (Checked.of f.name)

/-- What the world keeps of a check: the form and the key (`Replay.World.checked`). A record is not
the checker's word: where a command uses the checks of a form, it makes them again from their keys
(`checksOf`), and a record whose check the checker refuses is not a check. -/
structure CheckRecord where
  form : String
  key : CheckKey
deriving DecidableEq

def Checked.record (c : Checked) : CheckRecord := ⟨c.form, c.key⟩

/-- **The checks of a form, made from the world's records**: each record of the form whose check the
checker accepts. -/
def checksOf (rs : List CheckRecord) (form : String) : List Checked :=
  rs.filterMap fun r => if r.form == form then Checked.of r.form r.key else none

theorem Checked.of_record (c : Checked) : Checked.of c.form c.key = some c := by
  cases c with
  | mk form key ok => simp [Checked.of, ok]

/-- **The checks made again are the capture's**: from the records of the checks a capture made, the
checks of a form are made again exactly (the checker is a function, `CheckUnit.check`). -/
theorem checksOf_records (cs : List Checked) (form : String) :
    checksOf (cs.map Checked.record) form = cs.filter (·.form == form) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [checksOf, List.map_cons, List.filterMap_cons, List.filter_cons, Checked.record] at ih ⊢
    by_cases h : c.form == form
    · simp only [h, ite_true, Checked.of_record, ↓reduceIte]; exact congrArg _ ih
    · simp only [h, Bool.false_eq_true, ite_false, ↓reduceIte]; exact ih

/-! ## A proposal's judgments: kept from the capture, or checked now -/

/-- A judgment of a proposal, its check, and whether the capture made that check (`kept`). -/
structure Judged where
  page : String
  call : JudgeCall
  unit : CheckUnit
  kept : Bool

/-- The judgments of a proposal against the checks the vault keeps for its form: each is kept when
its check is one the capture made. -/
def classify (checked : List Checked) (form : String) (moved : List String) (calls : List (String × JudgeCall)) :
    List Judged :=
  calls.map fun x =>
    let u := unitOf x.1 moved x.2
    ⟨x.1, x.2, u, checked.any fun c => c.form == form && c.unit == u⟩

/-- The check a judgment runs now: none for a kept one, its check's verdict otherwise. -/
def Judged.checkNow (x : Judged) : Option Bool := if x.kept then none else some x.unit.accepted

/-- How many judgments are checked now whose check the vault keeps from the capture. -/
def rechecked (checked : List Checked) (form : String) (xs : List Judged) : Nat :=
  (xs.filter fun x => x.checkNow.isSome && checked.any fun c => c.form == form && c.unit == x.unit).length

/-- **Re-checked 0**: no judgment whose check the capture made is checked again. -/
theorem rechecked_zero (checked : List Checked) (form : String) (moved : List String)
    (calls : List (String × JudgeCall)) : rechecked checked form (classify checked form moved calls) = 0 := by
  simp only [rechecked, classify, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_map]
  rintro x ⟨y, _, rfl⟩
  by_cases h : checked.any (fun c => c.form == form && c.unit == unitOf y.1 moved y.2) = true
  · simp [Judged.checkNow, h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-- **A kept judgment is typed by the capture's check.** A judgment of a proposal kept from the capture
is the check the vault keeps, filled (`judge_runs_checked`), and typed by the derivation that check
returned (`judged_typed`): the judgment itself is not checked. -/
theorem kept_typed {checked : List Checked} {form : String} {moved : List String}
    {calls : List (String × JudgeCall)} {x : Judged} (hx : x ∈ classify checked form moved calls)
    (hk : x.kept = true) (hlk : x.call.linked = true → x.call.o = x.call.n)
    {who pr : String} {k : Occ} {facts : Obend.Spec.Law.Facts} (hrq : x.call.rq = requestBy who pr k facts) :
    (∃ c ∈ checked, c.form = form ∧ c.unit = x.unit) ∧
      x.call.term = x.unit.term.fill (fillOf moved x.call) ∧
      ∃ us, PartialTyping x.unit.asm [] x.call.term Obend.Law.inheritedVerdictTy us := by
  simp only [classify, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨c, hc, hf, hu⟩ := hk
  have hacc : (unitOf y.1 moved y.2).accepted = true := hu ▸ c.ok
  exact ⟨⟨c, hc, hf, hu⟩,
    judge_runs_checked y.1 moved y.2 (by simp only [CheckUnit.accepted, Bool.and_eq_true] at hacc; exact hacc.1) hlk,
    judged_typed y.1 moved y.2 hacc hlk hrq⟩

/-! ## A check, written and read back -/

open Lean (Json toJson)
open Obend.Spec.DataWire (dataJson decodeData)

/-- A page state, small: a record of naturals and labels as `[[name, value], …]` (a natural a
number, a label a string); anything else as the data wire has it. -/
def stateJson : Data → Json
  | .record fs =>
    if fs.all (fun (_, v) => match v with | .natural _ | .label _ => true | _ => false) then
      Json.arr (fs.map fun (k, v) => Json.arr #[Json.str k, match v with
        | .natural n => toJson n
        | .label l => Json.str l
        | _ => Json.null]).toArray
    else dataJson (.record fs)
  | d => dataJson d

def stateOfJson (j : Json) : Except String Data :=
  match j.getArr? with
  | .ok xs => do
    let fs ← xs.toList.mapM fun x => do
      let k ← (← x.getArrVal? 0).getStr?
      let v ← x.getArrVal? 1
      match v.getNat? with
      | .ok n => pure (k, Data.natural n)
      | .error _ => pure (k, Data.label (← v.getStr?))
    pure (.record fs)
  | .error _ => decodeData 64 j

/-- The type of a page state: a record of its fields, each a natural or a label as it holds
(`stateTyWith`, the type every judgment's state is built at). -/
def stateTyOf : Data → Ty
  | .record fs => stateTyWith (fs.map (·.1)) (fs.filterMap fun (k, v) => match v with | .label _ => some k | _ => none)
  | _ => stateTy []

/-- A check as JSON: what it is made from (`CheckKey`), small: each law by its text, the states as
pairs, the old state only where it is not the new, the state type only where it is not the state's
own (`stateTyOf`). -/
def checkedJson (c : CheckRecord) : Json :=
  Json.mkObj ([("form", Json.str c.form), ("page", Json.str c.key.page),
    ("moved", Json.arr (c.key.moved.map Json.str).toArray), ("pkg", Json.str c.key.pkg),
    ("laws", Json.arr (c.key.lin.map fun (n, e) => Json.arr #[Json.str n, Json.str e.render]).toArray),
    ("new", stateJson c.key.n), ("linked", Json.bool c.key.linked)] ++
    (if c.key.linked then [] else [("old", stateJson c.key.o)]) ++
    (if c.key.S == stateTyOf c.key.n then [] else [("S", dataJson (Obend.Core.Code.tyData c.key.S))]))

/-- A check's record read back (a world read from bytes: a checkpoint, a compacted log); its check is
made again where it is used (`checksOf`), so no bytes stand in for the checker. -/
def checkedOf (j : Json) : Except String CheckRecord := do
  let lin ← (← j.getObjValAs? (Array Json) "laws").toList.mapM fun x => do
    let n ← (← x.getArrVal? 0).getStr?
    match Obend.Spec.Law.parse (← (← x.getArrVal? 1).getStr?) with
    | .ok e => pure (n, e)
    | .error m => throw m
  let n ← stateOfJson (← j.getObjVal? "new")
  let linked ← j.getObjValAs? Bool "linked"
  let o ← if linked then pure n else stateOfJson (← j.getObjVal? "old")
  let S ← match j.getObjVal? "S" with
    | .ok sj => match Obend.Core.Code.tyOf (← decodeData 64 sj) with
      | some S => pure S
      | none => throw "not a type"
    | .error _ => pure (stateTyOf n)
  let moved ← (← j.getObjValAs? (Array Json) "moved").toList.mapM fun x => x.getStr?
  let k : CheckKey := ⟨← j.getObjValAs? String "page", moved, S, ← j.getObjValAs? String "pkg", lin, o, n, linked⟩
  return ⟨← j.getObjValAs? String "form", k⟩

end Obend.Vault.Form

end
