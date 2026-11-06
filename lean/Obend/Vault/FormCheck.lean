module
/-
# Obend.Vault.FormCheck — a law over a holed state, checked once

A form's residual leaves its natural holes in the states it writes (`100 - amount`). Each law the
kernel will judge a page of the form by (`Store.judgePrepared`: the page's own laws and every linking
page's laws over links, compiled for the page's state) is applied, at capture, to the page's state
with the hole in it: a Core term with a declared hole (`PartialTyping.hole`), checked by the checker
once (`Form.checkOver`). A fill puts a natural literal for each hole; the filled application is typed
by the derivation the capture's check returned, through the fill lemma
(`Obend.Core.Proofs.FillTyping.fill_typed`), and the checker is not run again (`checked_once`).
-/
public import Obend.Vault.Form
public import Obend.Core.Proofs.FillTyping
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
open Obend.Core.Proofs.FillTyping (FillersTyped checkAt_fill)

/-! ## The holes, declared -/

/-- Each natural hole, numbered by its place among the form's holes: a natural over no variables. -/
def natDecls : Nat → List (String × HoleTy) → List (Nat × HoleDecl)
  | _, [] => []
  | i, (_, .nat) :: hs => (i, ⟨[], .natural⟩) :: natDecls (i + 1) hs
  | i, (_, .page) :: hs => natDecls (i + 1) hs

theorem natDecls_lookup : ∀ (i : Nat) (hs : List (String × HoleTy)) (n : Nat) (d : HoleDecl),
    (natDecls i hs).lookup n = some d → d = ⟨[], .natural⟩
  | _, [], _, _, h => by simp [natDecls] at h
  | i, (_, .nat) :: hs, n, d, h => by
    simp only [natDecls, List.lookup_cons] at h
    split at h
    · cases h; rfl
    · exact natDecls_lookup (i + 1) hs n d h
  | i, (_, .page) :: hs, n, d, h => by
    simp only [natDecls] at h
    exact natDecls_lookup (i + 1) hs n d h

/-- The theory a form's states are checked in: its natural holes declared. -/
def Form.assumptions (f : Form) : Assumptions := { holes := natDecls 0 f.holes }

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

/-- Every filler a fill gives is typed as its hole is declared: a literal is a natural. -/
theorem natFill_typed (f : Form) (a : Assignment) : FillersTyped f.assumptions (f.natFill a) := by
  intro n t decl hθ hl
  have hd := natDecls_lookup 0 f.holes n decl hl
  subst hd
  unfold Form.natFill at hθ
  split at hθ
  · obtain ⟨v, _, rfl⟩ := Option.map_eq_some_iff.mp hθ
    exact ⟨[], .natural [] v, rfl, fun j b h => by simp at h⟩
  · cases hθ

/-! ## A law over a holed state -/

/-- A state with the moved field's value a term: the field `asset` of the record `n` is `t`. -/
def holedState (n : Data) (asset : String) (t : Term) : Term :=
  match n with
  | .record fs => .record (fs.map fun (k, v) => (k, if k == asset then t else v.term))
  | d => d.term

/-- The law applied to its old and new states: a function of the request. -/
def overStates (L o n : Term) : Term := .app (.app L o) n

/-- What the checker needs to apply a law: the type of each function applied. -/
def lawAnnotations (S : Ty) : Annotations := fun p =>
  if p = [] then some ⟨fnTy S (fnTy reqTy verdictTy), fnTy reqTy verdictTy, .unrestricted, .reusable⟩
  else if p = [0] then some ⟨lawTy S, fnTy S (fnTy reqTy verdictTy), .unrestricted, .reusable⟩
  else none

/-- **The one check**: a law over a holed state, at the type of a function of the request. -/
def Form.checkOver (f : Form) (S : Ty) (t : Term) :
    Except Obend.Core.Bidirectional.CheckRefusal (Against f.assumptions [] t (fnTy reqTy verdictTy)) :=
  checkAt f.assumptions (lawAnnotations S) [] [] t (fnTy reqTy verdictTy)

/-- **Checked once.** A law over a form's holed state that the checker accepted is typed, after any
fill, at the same type: by the derivation that one check returned, through the fill lemma. The fill
is not checked again. -/
theorem checked_once {f : Form} {S : Ty} {t : Term} {r : Against f.assumptions [] t (fnTy reqTy verdictTy)}
    (h : f.checkOver S t = .ok r) (a : Assignment) :
    ∃ u, PartialTyping f.assumptions [] (t.fill (f.natFill a)) (fnTy reqTy verdictTy) u := by
  have hl : r.uses = [] :=
    List.eq_nil_of_length_eq_zero (Obend.Core.MachineTyping.source_uses_length r.derivation)
  obtain ⟨u, typed, _, _⟩ := checkAt_fill h (by simp [validContext]) (by rw [hl]; rfl) (natFill_typed f a)
  exact ⟨u, typed⟩

/-- The filled law over the filled states: the fill reaches each part. -/
theorem overStates_fill (θ : Nat → Option Term) (L o n : Term) :
    (overStates L o n).fill θ = overStates (L.fill θ) (o.fill θ) (n.fill θ) := by
  simp [overStates, Term.fill]

/-! ## The laws a form's pages are judged by -/

/-- The laws judged at the page `c`, of state `d` (`Store.judgePrepared`): its own, then every
linking page's laws over links, each compiled for `d` restated as the judge restates it (`rekey`).
Each with the page that wrote it, its name, its text, the state type, the state, and whether it reads
the page as the old state too (a law over links judges the linked page as it is). -/
def lawsAtPage (es : List Entry) (c : String) (d : Data) :
    List (String × String × String × Ty × Data × Term × Bool) :=
  match es.find? (·.name == c) with
  | none => []
  | some pe =>
    let own := match lawsFor es c pe.graph with
      | .ok laws =>
        let lin := (laws.filter fun l => !isLinkLaw l.2.2 && (lawSubject l.1).isNone).map fun (n, x, _) => (n, x)
        let (S, nd) := rekey lin d
        (compiled S c lin).map fun (n, L) => (c, n, ((laws.map fun (m, _, t) => (m, t)).lookup n).getD "", S, nd, L, false)
      | .error _ => []
    let theirs := es.flatMap fun e =>
      if e.name != c && (linkTargets e.graph).contains pe.id then
        match lawsFor es e.name e.graph with
        | .ok elaws =>
          let lin := linkLaws elaws
          let (S, nd) := rekey lin d
          (compiled S e.name lin).map fun (n, L) =>
            (e.name, n, ((elaws.map fun (m, _, t) => (m, t)).lookup n).getD "", S, nd, L, true)
        | .error _ => []
      else []
    own ++ theirs

/-- One law over one leg of a form: the move, the leg (`src`: the page the move takes from), the page,
the law (its page, name and text), the state type and the term checked. -/
structure LawApp where
  move : Nat
  src : Bool
  page : String
  pkg : String
  law : String
  text : String
  S : Ty
  term : Term
deriving Repr

/-- What identifies a law over a leg: everything it is, said. -/
def LawApp.key (x : LawApp) : String := (repr x).pretty

/-- The pages a leg may write: the page, or for a hole every page the form captured. -/
def Form.legPages (f : Form) : PRef → List String
  | .page s => [s]
  | .hole _ => f.cells.map (·.name)

/-- The residual of a move with the leg's page put: a hole of it filled with `s`. -/
def legResidual (f : Form) (r : RMove) (side : PRef) (s : String) : RMove :=
  match side with
  | .hole h => (r.subst ⟨[], [(h, s)]⟩).peval f.known
  | .page _ => r

/-- Every law over every leg a fill of the form may write, at the store `es`. -/
def Form.lawApps (f : Form) (es : List Entry) : List LawApp :=
  let rs := f.residual f.known
  (List.range rs.length).flatMap fun i =>
    match rs[i]? with
    | none => []
    | some r =>
      let leg (src : Bool) : List LawApp :=
        let side := if src then r.src else r.dst
        (f.legPages side).flatMap fun s =>
          let r' := legResidual f r side s
          let e := if src then r'.debit else r'.credit
          match e.coreTerm f, f.known s with
          | some t, some d =>
            (lawsAtPage es s d).map fun (pkg, n, txt, S, nd, L, link) =>
              let holed := holedState nd r.asset t
              ⟨i, src, s, pkg, n, txt, S, overStates L (if link then holed else nd.term) holed⟩
          | _, _ => []
      leg true ++ leg false

/-- The laws over the legs a fill writes: each move's two pages as the fill names them. -/
def Form.lawAppsOf (f : Form) (es : List Entry) (a : Assignment) : List LawApp :=
  let rs := f.residual f.known
  (f.lawApps es).filter fun x =>
    match rs[x.move]? with
    | none => false
    | some r =>
      let side := if x.src then r.src else r.dst
      match side.subst a with
      | .page s => s == x.page
      | .hole _ => false

/-- The laws over the form's legs the checker accepts, checked once each: their keys. -/
def Form.checkedOnce (f : Form) (es : List Entry) : List String :=
  ((f.lawApps es).filter fun x => (f.checkOver x.S x.term).toBool).map LawApp.key

end Obend.Vault.Form

end
