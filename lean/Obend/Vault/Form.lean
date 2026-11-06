module
/-
# Obend.Vault.Form — a captured membrane is a form; a filled form is a proposal the kernel judges

ember's test: a screenshot sent to a friend should not be dead pixels. A participant captures a page
situation into a MEMBRANE (the per-viewer, cap-bounded capture of `Obend.Vault.Rehydration`: what the
viewer's grant shows, culled by name and by cap, the rest absent); substitutes variables for some of
its data (`abstract`), so the capture becomes a FORM; hands the form to someone else, who fills it
offline (`fill`) and sends back a PROPOSAL; and the proposal comes back to the vault, where the kernel
judges it as it judges any write (`judgeProposal`: each page it writes through `commit`, the laws as
they stand, laws over links included). The refusal names what refused: the membrane, the form's
resources, a stale reading, or the law and the clause.

**The form.** A form is the captured cells (each page's state as captured, only the pages the grant
shows), the pages it names without capturing (`refs`, kept as `Sturdyref`s, read live where the form
is judged), its holes with their types, the reshare chain of grants it was issued under, and its
MOVES: transfers of an amount of one field from a page to a page, where the amount and either page
may be a hole. The arithmetic a move does is an expression (`NExpr`); the form's RESIDUAL is each
move's expressions evaluated as far as the captured state allows (`NExpr.peval`), the holes and the
reads of uncaptured pages left in place.

**What is proved.**
* The substitution lemma (`eval_fill_eq_subst_residual`): filling the form and evaluating it equals
  substituting the fill into the residual, and the residual may be computed with LESS knowledge than
  the judgment has (the capture's, where the judgment also reads live every page the form did not
  capture): the work done before the fill is never wrong. `residual_reads_nothing_known`: the residual reads no page whose
  state it knew, so the work is never redone. `abstract_then_fill`: abstracting a value into a fresh
  hole and filling the hole with that value gives back the live turn (the screenshot stays live).
* No amplification through forms (`admit_no_amplification`): an admitted fill's turn writes and reads
  only pages the membrane's final viewer may write and see, and therefore (`resolveChain_attenuates`,
  through `Membrane.reshare`'s attenuation, `reshare_some_attenuates`) only pages the root holder could
  have written directly. A hidden page (one the viewer's grant does not permit) is in neither
  footprint (`admit_hidden_untouched`), is absent from the capture (`capture_hidden_absent`), and
  changing it changes nothing downstream (`hidden_change_invisible_through_form`: the same form, the
  same admission, the same turn). The membrane's refusal reads no store (`judgeProposal_gate_first`):
  a hidden page and a page that does not exist are refused alike.
* The strong hole, reopened: a hole in a conservation position is admissible as a FAMILY of conserving
  turns parameterized by the amount. `pairsTurn` builds the turn for every amount with `balanced` a
  theorem, not a check (`pairs_balanced`); its half-edges report the actual change of the moved field
  (`admit_halfEdges_honest`); so for every amount the fill admits, every field's total over the pages
  written is unchanged (`admit_conserves_written`), and so is its total over any pages of the store
  that include them (`admit_conserves_total`, through `applyTurn_conserves_total`, which holds of any
  turn whose half-edges are honest) — what `carry_conserves_total_book` says of a carry, said of a
  form. Authority and resources are discharged at fill time (`admit`), not before.
* What the kernel lands, the gate admitted (`judgeProposal_ok`), so every landed proposal stays inside
  the membrane and conserves (`judgeProposal_sound`).

**What is not.** The residual language is the form's own (`NExpr`: naturals, holes, field reads, `+`,
a `-` that may not go below zero), not Core's `Term` with `.hole n σ`: lifting it there needs Core's
step relation stable under hole filling, which is not done. A hole carries a type (a natural, a
page); its context is the form's scope, checked by the membrane at the fill, not a substitution the
hole carries. The turn a proposal denotes records the
moved field; the page the kernel writes moves its other measures (bytes, version) as `commit` says.
A proposal's legs are judged in order, each against the store the earlier legs made, and any refusal
refuses the whole proposal; the vault has no multi-page commit to judge them at once.
-/
public import Obend.Vault.Store
public import Obend.Vault.Rehydration
public import Obend.Spec.DataWire
public import Lean.Data.Json
@[expose] public section

namespace Obend.Vault.Form

set_option autoImplicit false

open Obend.Core.Data (Data)
open Obend.Vault.Affordance (Auth fireGate fireGate_iff_subset fireGate_trans)
open Obend.Vault.Rehydration (MembraneViewer Membrane.reshare reshare_some_attenuates Sturdyref)

/-! ## 1. Positions, expressions, and the residual -/

/-- A page position of a form: a page, or a hole a page will fill. -/
inductive PRef where
  | page (name : String)
  | hole (name : String)
deriving DecidableEq, Repr

/-- A natural position: a constant, a hole, the value of a field of a page, a sum, or a difference
that may not go below zero. -/
inductive NExpr where
  | lit (n : Nat)
  | hole (name : String)
  | field (p : PRef) (f : String)
  | add (a b : NExpr)
  | sub (a b : NExpr)
deriving DecidableEq, Repr

/-- What is known of the pages: each page's state, or none (not captured, not read). -/
abbrev Known := String → Option Data

/-- `k'` knows less than `k`: wherever `k'` knows a page, `k` knows it alike. -/
def Agrees (k' k : Known) : Prop := ∀ n d, k' n = some d → k n = some d

theorem Agrees.refl (k : Known) : Agrees k k := fun _ _ h => h

/-- A fill: a natural for each natural hole, a page for each page hole. -/
structure Assignment where
  nats : List (String × Nat) := []
  pages : List (String × String) := []
deriving DecidableEq, Repr

def PRef.subst (a : Assignment) : PRef → PRef
  | .page n => .page n
  | .hole h => match a.pages.lookup h with
    | some n => .page n
    | none => .hole h

def NExpr.subst (a : Assignment) : NExpr → NExpr
  | .lit n => .lit n
  | .hole h => match a.nats.lookup h with
    | some n => .lit n
    | none => .hole h
  | .field p f => .field (p.subst a) f
  | .add x y => .add (x.subst a) (y.subst a)
  | .sub x y => .sub (x.subst a) (y.subst a)

/-- Evaluate, where everything an expression reads is known and every hole is filled; a difference
below zero does not evaluate. -/
def NExpr.eval (k : Known) : NExpr → Option Nat
  | .lit n => some n
  | .hole _ => none
  | .field (.page n) f => (k n).map (natAt · f)
  | .field (.hole _) _ => none
  | .add x y => do
    let u ← x.eval k
    let v ← y.eval k
    pure (u + v)
  | .sub x y => do
    let u ← x.eval k
    let v ← y.eval k
    if v ≤ u then pure (u - v) else none

/-- A sum, folded where both sides are constants. -/
def addN : NExpr → NExpr → NExpr
  | .lit u, .lit v => .lit (u + v)
  | x, y => .add x y

/-- A difference, folded where both sides are constants and it does not go below zero. -/
def subN : NExpr → NExpr → NExpr
  | .lit u, .lit v => if v ≤ u then .lit (u - v) else .sub (.lit u) (.lit v)
  | x, y => .sub x y

/-- **The residual**: an expression evaluated as far as `k` allows: every read of a page `k` knows is
its value, every constant subexpression folded; holes, and reads of pages `k` does not know, stay. -/
def NExpr.peval (k : Known) : NExpr → NExpr
  | .lit n => .lit n
  | .hole h => .hole h
  | .field (.page n) f => match k n with
    | some d => .lit (natAt d f)
    | none => .field (.page n) f
  | .field (.hole h) f => .field (.hole h) f
  | .add x y => addN (x.peval k) (y.peval k)
  | .sub x y => subN (x.peval k) (y.peval k)

theorem eval_subst_addN (k : Known) (a : Assignment) (x y : NExpr) :
    ((addN x y).subst a).eval k = ((NExpr.add x y).subst a).eval k := by
  cases x <;> cases y <;> simp [addN, NExpr.subst, NExpr.eval]

theorem eval_subst_subN (k : Known) (a : Assignment) (x y : NExpr) :
    ((subN x y).subst a).eval k = ((NExpr.sub x y).subst a).eval k := by
  cases x <;> cases y <;> simp only [subN, NExpr.subst, NExpr.eval] <;> try rfl
  rename_i u v
  by_cases h : v ≤ u <;> simp [h, NExpr.subst, NExpr.eval]

/-- **The substitution lemma, for one expression.** Substituting a fill into the residual computed
with knowledge `k'` and evaluating with knowledge `k ⊇ k'` is substituting it into the expression and
evaluating: the residual is never wrong, whatever was learned between the residual and the fill. -/
theorem eval_subst_peval {k' k : Known} (hk : Agrees k' k) (a : Assignment) :
    ∀ e : NExpr, ((e.peval k').subst a).eval k = (e.subst a).eval k
  | .lit _ => rfl
  | .hole _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases h : k' n with
    | none => rfl
    | some d => simp [NExpr.subst, PRef.subst, NExpr.eval, hk n d h]
  | .field (.hole _) _ => rfl
  | .add x y => by
    simp only [NExpr.peval]
    rw [eval_subst_addN]
    simp only [NExpr.subst, NExpr.eval]
    rw [eval_subst_peval hk a x, eval_subst_peval hk a y]
  | .sub x y => by
    simp only [NExpr.peval]
    rw [eval_subst_subN]
    simp only [NExpr.subst, NExpr.eval]
    rw [eval_subst_peval hk a x, eval_subst_peval hk a y]

/-- Whether an expression reads no page `k` knows. -/
def NExpr.knownFree (k : Known) : NExpr → Bool
  | .lit _ | .hole _ | .field (.hole _) _ => true
  | .field (.page n) _ => (k n).isNone
  | .add x y | .sub x y => x.knownFree k && y.knownFree k

theorem knownFree_addN (k : Known) (x y : NExpr) (hx : x.knownFree k = true) (hy : y.knownFree k = true) :
    (addN x y).knownFree k = true := by
  cases x <;> cases y <;> simp_all [addN, NExpr.knownFree]

theorem knownFree_subN (k : Known) (x y : NExpr) (hx : x.knownFree k = true) (hy : y.knownFree k = true) :
    (subN x y).knownFree k = true := by
  cases x <;> cases y <;> simp_all [subN, NExpr.knownFree] <;> split <;> simp [NExpr.knownFree]

/-- **The work is never redone**: the residual reads no page whose state was known when it was
computed; every such read is already its value. -/
theorem residual_reads_nothing_known (k : Known) : ∀ e : NExpr, (e.peval k).knownFree k = true
  | .lit _ | .hole _ | .field (.hole _) _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases h : k n with
    | none => simp [NExpr.knownFree, h]
    | some d => rfl
  | .add x y => knownFree_addN k _ _ (residual_reads_nothing_known k x) (residual_reads_nothing_known k y)
  | .sub x y => knownFree_subN k _ _ (residual_reads_nothing_known k x) (residual_reads_nothing_known k y)

/-! ## 2. Abstraction: a value becomes a hole -/

/-- Replace the constant `v` by the hole `h`. -/
def NExpr.abstractNat (v : Nat) (h : String) : NExpr → NExpr
  | .lit n => if n == v then .hole h else .lit n
  | .hole x => .hole x
  | .field p f => .field p f
  | .add x y => .add (x.abstractNat v h) (y.abstractNat v h)
  | .sub x y => .sub (x.abstractNat v h) (y.abstractNat v h)

/-- Replace the page `n` by the hole `h`. -/
def PRef.abstractPage (n h : String) : PRef → PRef
  | .page m => if m == n then .hole h else .page m
  | .hole x => .hole x

def NExpr.abstractPage (n h : String) : NExpr → NExpr
  | .lit m => .lit m
  | .hole x => .hole x
  | .field p f => .field (p.abstractPage n h) f
  | .add x y => .add (x.abstractPage n h) (y.abstractPage n h)
  | .sub x y => .sub (x.abstractPage n h) (y.abstractPage n h)

/-- The holes an expression has. -/
def PRef.holes : PRef → List String
  | .page _ => []
  | .hole h => [h]

def NExpr.holes : NExpr → List String
  | .lit _ => []
  | .hole h => [h]
  | .field p _ => p.holes
  | .add x y | .sub x y => x.holes ++ y.holes

theorem PRef.subst_abstractPage_cons (n h : String) (a : Assignment) :
    ∀ p : PRef, h ∉ p.holes →
      (p.abstractPage n h).subst ⟨a.nats, (h, n) :: a.pages⟩ = p.subst a
  | .page m, _ => by
    by_cases hm : m = n
    · subst hm; simp [PRef.abstractPage, PRef.subst]
    · simp [PRef.abstractPage, PRef.subst, hm]
  | .hole x, hx => by
    have hne : (x == h) = false := by simpa using fun e => hx (by simp [PRef.holes, e])
    simp [PRef.abstractPage, PRef.subst, List.lookup, hne]

theorem NExpr.subst_abstractNat_cons (v : Nat) (h : String) (a : Assignment) :
    ∀ e : NExpr, h ∉ e.holes →
      (e.abstractNat v h).subst ⟨(h, v) :: a.nats, a.pages⟩ = e.subst a
  | .lit n, _ => by
    by_cases hn : n = v
    · subst hn; simp [NExpr.abstractNat, NExpr.subst]
    · simp [NExpr.abstractNat, NExpr.subst, hn]
  | .hole x, hx => by
    have hne : (x == h) = false := by simpa using fun e => hx (by simp [NExpr.holes, e])
    simp [NExpr.abstractNat, NExpr.subst, List.lookup, hne]
  | .field p f, _ => by simp [NExpr.abstractNat, NExpr.subst, PRef.subst]
  | .add x y, hxy => by
    simp only [NExpr.holes, List.mem_append, not_or] at hxy
    simp [NExpr.abstractNat, NExpr.subst, subst_abstractNat_cons v h a x hxy.1,
      subst_abstractNat_cons v h a y hxy.2]
  | .sub x y, hxy => by
    simp only [NExpr.holes, List.mem_append, not_or] at hxy
    simp [NExpr.abstractNat, NExpr.subst, subst_abstractNat_cons v h a x hxy.1,
      subst_abstractNat_cons v h a y hxy.2]

theorem NExpr.subst_abstractPage_cons (n h : String) (a : Assignment) :
    ∀ e : NExpr, h ∉ e.holes →
      (e.abstractPage n h).subst ⟨a.nats, (h, n) :: a.pages⟩ = e.subst a
  | .lit _, _ => rfl
  | .hole x, hx => by
    simp [NExpr.abstractPage, NExpr.subst]
  | .field p f, hp => by
    simp only [NExpr.holes] at hp
    simp [NExpr.abstractPage, NExpr.subst, PRef.subst_abstractPage_cons n h a p hp]
  | .add x y, hxy => by
    simp only [NExpr.holes, List.mem_append, not_or] at hxy
    simp [NExpr.abstractPage, NExpr.subst, subst_abstractPage_cons n h a x hxy.1,
      subst_abstractPage_cons n h a y hxy.2]
  | .sub x y, hxy => by
    simp only [NExpr.holes, List.mem_append, not_or] at hxy
    simp [NExpr.abstractPage, NExpr.subst, subst_abstractPage_cons n h a x hxy.1,
      subst_abstractPage_cons n h a y hxy.2]

/-! ## 3. The membrane: grants, the reshare chain, the capture -/

def allAuths : List Auth := [.read, .write, .grant, .call, .reply, .reset, .control, .notify]

/-- A grant, as a form carries it: who holds it, the caps it holds, the page patterns it permits
(`patternMatches`: a page, `folder/*` or `*`). A `MembraneViewer` with a finite description. -/
structure Grant where
  holder : String
  held : List Auth
  patterns : List String
deriving DecidableEq, Repr

def Grant.permits (g : Grant) (n : String) : Bool := g.patterns.any (patternMatches · n)

/-- The viewer a grant is, over the names `scope`. -/
def Grant.viewer (g : Grant) (scope : List String) : MembraneViewer :=
  { held := g.held, permits := g.permits, activeNames := scope }

/-- The vault's owner: every cap, every page. -/
def ownerGrant : Grant := { holder := "owner", held := allAuths, patterns := ["*"] }

/-- Why a form's fill is refused before the laws are asked. -/
inductive Refusal where
  /-- a hop of the reshare chain would amplify what its holder holds (`Membrane.reshare` is none) -/
  | amplifies (holder delegate : String) (held asked : List Auth)
  /-- the fill names a page the form neither captured nor refers to -/
  | notInForm (page holder : String)
  /-- the page is the form's, but the membrane's final viewer may not write it -/
  | notWritable (page holder : String) (held : List Auth)
  | unfilled (hole : String)
  | unknownPage (page : String)
  /-- the move takes more of the field than the page holds -/
  | resources (page asset : String) (holds moves : Nat)
  | unevaluated (what : String)
  /-- the fill's turn writes one page twice -/
  | twice (page : String)
deriving DecidableEq, Repr

/-- **The reshare chain**, from the viewer `cur` held by `who`: each grant is a hop through
`Membrane.reshare`, which admits it only as an attenuation. The final viewer and its holder. -/
def resolveChain (scope : List String) : MembraneViewer → String → List Grant →
    Except Refusal (MembraneViewer × String)
  | cur, who, [] => .ok (cur, who)
  | cur, who, g :: rest =>
    match Membrane.reshare cur (g.viewer scope) with
    | some m => resolveChain scope m g.holder rest
    | none => .error (.amplifies who g.holder cur.held g.held)

/-- **Every chain attenuates**: the final viewer holds no cap and permits no page its root does not. -/
theorem resolveChain_attenuates (scope : List String) (gs : List Grant) (cur : MembraneViewer)
    (who : String) {v : MembraneViewer} {w : String} (h : resolveChain scope cur who gs = .ok (v, w)) :
    v.held ⊆ cur.held ∧ ∀ n, v.permits n = true → cur.permits n = true := by
  induction gs generalizing cur who with
  | nil =>
    simp only [resolveChain, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ hx => hx, fun _ hn => hn⟩
  | cons g rest ih =>
    simp only [resolveChain] at h
    split at h
    · rename_i m hm
      have ⟨hheld, _, _, hperm, _⟩ := reshare_some_attenuates (φ := Unit) hm
      have ⟨ih1, ih2⟩ := ih m g.holder h
      exact ⟨List.Subset.trans ih1 hheld, fun n hn => hperm n (ih2 n hn)⟩
    · cases h

/-- A captured cell: a page, the caps a viewer needs to see it, its state as captured. -/
structure Cell where
  name : String
  required : List Auth := [.read]
  state : Data
deriving Repr

/-- Whether a viewer sees a cell: its caps cover the cell's, and its grant permits the page
(`membraneShows`, on cells). -/
def shows (v : MembraneViewer) (c : Cell) : Bool := fireGate c.required v.held && v.permits c.name

/-- **The capture**: the cells a viewer sees. A cell it does not see is absent, not redacted. -/
def capture (v : MembraneViewer) (cs : List Cell) : List Cell := cs.filter (shows v)

theorem capture_hidden_absent (v : MembraneViewer) (cs : List Cell) (c : Cell)
    (hhide : shows v c = false) : c ∉ capture v cs := by
  intro hc
  have := (List.mem_filter.mp hc).2
  rw [hhide] at this
  cases this

/-- Changing a cell the viewer does not see leaves the capture as it was. -/
theorem capture_hidden_change (v : MembraneViewer) (pre post : List Cell) (c c' : Cell)
    (hc : shows v c = false) (hc' : shows v c' = false) :
    capture v (pre ++ c :: post) = capture v (pre ++ c' :: post) := by
  simp [capture, List.filter_append, hc, hc']

/-! ## 4. Forms, moves, and fills -/

/-- A hole's type: a natural, or a page (of the form's scope; the membrane checks it). -/
inductive HoleTy where
  | nat
  | page
deriving DecidableEq, Repr

/-- A move: `amount` of the field `asset` from the page `src` to the page `dst`. -/
structure Move where
  asset : String
  src : PRef
  dst : PRef
  amount : NExpr
deriving DecidableEq, Repr

/-- **A form**: a capture, with holes. `grants` is the chain it was issued under, its first hop from
the owner; `refs` the pages it names without capturing them (read live where it is judged). -/
structure Form where
  name : String
  grants : List Grant
  cells : List Cell
  refs : List String := []
  holes : List (String × HoleTy) := []
  moves : List Move
deriving Repr

/-- The pages a form may name: the cells it captured and the pages it refers to. -/
def Form.scope (f : Form) : List String := f.cells.map (·.name) ++ f.refs

/-- What the form knows: each captured page's state as captured. -/
def Form.known (f : Form) : Known := fun n => (f.cells.find? (·.name == n)).map (·.state)

/-- What the kernel knows where the form is judged: the captured states (pinned, so they are the live
ones when the pins hold), and every other page as it is. -/
def Form.knownLive (f : Form) (live : VaultStore) : Known := fun n =>
  match f.known n with
  | some d => some d
  | none => live n

theorem Form.known_agrees (f : Form) (live : VaultStore) : Agrees f.known (f.knownLive live) := by
  intro n d h
  simp [Form.knownLive, h]

/-- The `Sturdyref` a reference is: the page, live at the vault that issued the form. -/
def Form.sturdyref (_f : Form) (vault : String) (lineage : MembraneViewer) (page : String) : Sturdyref Data :=
  { uri := "obend://" ++ vault ++ "/" ++ page, surface := [], log := [], lineage := lineage,
    reachable := true, cellId := page }

theorem Form.sturdyref_live (f : Form) (vault : String) (lineage : MembraneViewer) (page : String) :
    (f.sturdyref vault lineage page).liveness = .Live := rfl

/-- A move unfolded into what it computes: the amount, the source's field after (`debit`), the
destination's after (`credit`). -/
structure RMove where
  asset : String
  src : PRef
  dst : PRef
  amount : NExpr
  debit : NExpr
  credit : NExpr
deriving DecidableEq, Repr

def Move.unfold (m : Move) : RMove :=
  { asset := m.asset, src := m.src, dst := m.dst, amount := m.amount,
    debit := .sub (.field m.src m.asset) m.amount, credit := .add (.field m.dst m.asset) m.amount }

def RMove.peval (k : Known) (r : RMove) : RMove :=
  { r with amount := r.amount.peval k, debit := r.debit.peval k, credit := r.credit.peval k }

def RMove.subst (a : Assignment) (r : RMove) : RMove :=
  { asset := r.asset, src := r.src.subst a, dst := r.dst.subst a, amount := r.amount.subst a,
    debit := r.debit.subst a, credit := r.credit.subst a }

/-- **The residual of a form**: each move evaluated as far as `k` allows. -/
def Form.residual (k : Known) (f : Form) : List RMove := f.moves.map fun m => m.unfold.peval k

/-- One move's two legs, evaluated: the pages, their states before, the amount, the moved field's
value after at each. -/
structure LegPair where
  asset : String
  src : String
  dst : String
  srcPre : Data
  dstPre : Data
  amount : Nat
  srcAfter : Nat
  dstAfter : Nat
deriving Repr

/-- The first hole of an expression, said. -/
def NExpr.firstHole (e : NExpr) : String := (e.holes.head?).getD "?"

/-- Evaluate a substituted move at `k`. -/
def RMove.pair (k : Known) (r : RMove) : Except Refusal LegPair :=
  match r.src, r.dst with
  | .hole h, _ => .error (.unfilled h)
  | .page _, .hole h => .error (.unfilled h)
  | .page s, .page d =>
    match k s, k d with
    | none, _ => .error (.unknownPage s)
    | some _, none => .error (.unknownPage d)
    | some ps, some pd =>
      match r.amount.eval k with
      | none => .error (if r.amount.holes.isEmpty then .unevaluated "the amount" else .unfilled r.amount.firstHole)
      | some x =>
        match r.debit.eval k, r.credit.eval k with
        | some sa, some da => .ok ⟨r.asset, s, d, ps, pd, x, sa, da⟩
        | none, _ => .error (.resources s r.asset (natAt ps r.asset) x)
        | some _, none => .error (.unevaluated (d ++ "." ++ r.asset))

/-- Every move of a fill, evaluated, in order. -/
def pairsOf (k : Known) : List RMove → Except Refusal (List LegPair)
  | [] => .ok []
  | r :: rs => do
    let p ← r.pair k
    let ps ← pairsOf k rs
    pure (p :: ps)

theorem holes_subst_addN (a : Assignment) (x y : NExpr) :
    ((addN x y).subst a).holes = ((NExpr.add x y).subst a).holes := by
  cases x <;> cases y <;> simp [addN, NExpr.subst, NExpr.holes]

theorem holes_subst_subN (a : Assignment) (x y : NExpr) :
    ((subN x y).subst a).holes = ((NExpr.sub x y).subst a).holes := by
  cases x <;> cases y <;> simp only [subN, NExpr.subst, NExpr.holes] <;> try rfl
  rename_i u v
  by_cases h : v ≤ u <;> simp [h, NExpr.subst, NExpr.holes]

/-- The residual keeps every hole the expression had, in order. -/
theorem holes_subst_peval (k : Known) (a : Assignment) :
    ∀ e : NExpr, ((e.peval k).subst a).holes = (e.subst a).holes
  | .lit _ | .hole _ | .field (.hole _) _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases k n <;> rfl
  | .add x y => by
    simp only [NExpr.peval]
    rw [holes_subst_addN]
    simp only [NExpr.subst, NExpr.holes, holes_subst_peval k a x, holes_subst_peval k a y]
  | .sub x y => by
    simp only [NExpr.peval]
    rw [holes_subst_subN]
    simp only [NExpr.subst, NExpr.holes, holes_subst_peval k a x, holes_subst_peval k a y]

theorem RMove.pair_peval_subst {k' k : Known} (hk : Agrees k' k) (a : Assignment) (r : RMove) :
    ((r.peval k').subst a).pair k = (r.subst a).pair k := by
  simp only [RMove.peval, RMove.subst, RMove.pair, eval_subst_peval hk, NExpr.firstHole,
    holes_subst_peval]
  rfl

/-- **The substitution lemma** (`eval (fill f a) = subst a (residual f)`). Evaluating the form with
the fill substituted in is substituting the fill into the form's residual and evaluating that; the
residual computed with the capture's knowledge `k'`, the evaluation at the judgment's `k ⊇ k'`. -/
theorem eval_fill_eq_subst_residual {k' k : Known} (hk : Agrees k' k) (f : Form) (a : Assignment) :
    pairsOf k ((f.residual k').map (·.subst a)) = pairsOf k (f.moves.map fun m => m.unfold.subst a) := by
  unfold Form.residual
  induction f.moves with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, pairsOf]
    rw [RMove.pair_peval_subst hk]
    simp only [List.map_map] at ih ⊢
    rw [ih]

/-! ## 5. The turn a fill denotes: a family of conserving turns -/

/-- One entry of a record, with the field `f` set to `v`. -/
def setEntry (f : String) (v : Nat) (e : String × Data) : String × Data :=
  if e.1 == f then (e.1, .natural v) else e

/-- A state with a natural field set (added if the record lacks it). -/
def putNat (d : Data) (f : String) (v : Nat) : Data :=
  match d with
  | .record fs =>
    if fs.any (·.1 == f) then .record (fs.map (setEntry f v))
    else .record (fs ++ [(f, .natural v)])
  | _ => .record [(f, .natural v)]

theorem lookup_map_set (f : String) (v : Nat) :
    ∀ fs : List (String × Data), fs.any (·.1 == f) = true →
      (fs.map (setEntry f v)).lookup f = some (.natural v)
  | [], h => by simp at h
  | (k, x) :: rest, h => by
    by_cases hk : k = f
    · subst hk; simp [setEntry]
    · have hne : (f == k) = false := by simpa using Ne.symm hk
      have hne' : (k == f) = false := by simpa using hk
      simp only [List.any_cons, hne', Bool.false_or] at h
      have ih := lookup_map_set f v rest h
      simp only [List.map_cons, setEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup, hne]
      exact ih

theorem lookup_map_set_ne (f g : String) (v : Nat) (hg : g ≠ f) :
    ∀ fs : List (String × Data), (fs.map (setEntry f v)).lookup g = fs.lookup g
  | [] => rfl
  | (k, x) :: rest => by
    have ih := lookup_map_set_ne f g v hg rest
    by_cases hk : k = f
    · subst hk
      have hne : (g == k) = false := by simpa using hg
      simp only [List.map_cons, setEntry, beq_self_eq_true, ↓reduceIte, List.lookup, hne]
      exact ih
    · have hne' : (k == f) = false := by simpa using hk
      simp only [List.map_cons, setEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup]
      split
      · rfl
      · exact ih

theorem lookup_append_absent (f : String) (d : Data) :
    ∀ fs : List (String × Data), fs.any (·.1 == f) = false → (fs ++ [(f, d)]).lookup f = some d
  | [], _ => by simp
  | (k, x) :: rest, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hne : (f == k) = false := by
      have : k ≠ f := by simpa using h.1
      simpa using Ne.symm this
    simp [List.lookup, hne, lookup_append_absent f d rest h.2]

theorem lookup_append_ne (f g : String) (d : Data) (hg : g ≠ f) :
    ∀ fs : List (String × Data), (fs ++ [(f, d)]).lookup g = fs.lookup g
  | [] => by
    have hne : (g == f) = false := by simpa using hg
    simp [List.lookup, hne]
  | (k, x) :: rest => by
    simp only [List.cons_append, List.lookup]
    split <;> simp_all [lookup_append_ne f g d hg rest]

/-- The field set is the value written. -/
theorem natAt_putNat (d : Data) (f : String) (v : Nat) : natAt (putNat d f v) f = v := by
  unfold putNat
  split
  · rename_i fs
    split
    · rename_i h; simp [natAt, lookup_map_set f v fs h]
    · rename_i h
      have h' : fs.any (·.1 == f) = false := by
        revert h; cases fs.any (·.1 == f) <;> simp
      simp [natAt, lookup_append_absent f _ fs h']
  · simp [natAt, List.lookup]

/-- Every other field is as it was. -/
theorem natAt_putNat_ne (d : Data) (f g : String) (v : Nat) (hg : g ≠ f) :
    natAt (putNat d f v) g = natAt d g := by
  unfold putNat
  split
  · rename_i fs
    split
    · simp [natAt, lookup_map_set_ne f g v hg fs]
    · simp [natAt, lookup_append_ne f g _ hg fs]
  · rename_i hnot
    have hne : (g == f) = false := by simpa using hg
    cases d with
    | record fs => exact absurd rfl (hnot fs)
    | _ => simp [natAt, List.lookup, hne]

/-- The source leg of a move, in turn `tid`: its half-edge is the amount, taken. -/
def LegPair.srcDelta (tid : ByteArray) (p : LegPair) : CellDelta :=
  { cell := p.src, preState := p.srcPre, postState := putNat p.srcPre p.asset p.srcAfter,
    touchedFields := [p.asset], halfEdges := [(p.asset, -(p.amount : Int))],
    cert := some (.byLoweredDecider "form-leg" [] tid) }

/-- The destination leg: its half-edge is the amount, given. -/
def LegPair.dstDelta (tid : ByteArray) (p : LegPair) : CellDelta :=
  { cell := p.dst, preState := p.dstPre, postState := putNat p.dstPre p.asset p.dstAfter,
    touchedFields := [p.asset], halfEdges := [(p.asset, (p.amount : Int))],
    cert := some (.byLoweredDecider "form-leg" [] tid) }

def pairDeltas (tid : ByteArray) : List LegPair → List CellDelta
  | [] => []
  | p :: ps => p.srcDelta tid :: p.dstDelta tid :: pairDeltas tid ps

theorem foldl_add_int (l : List Int) (acc : Int) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, Int.add_assoc]

theorem deltaAsset_src (tid : ByteArray) (p : LegPair) (a : String) :
    deltaAsset (p.srcDelta tid) a = if p.asset == a then -(p.amount : Int) else 0 := by
  unfold deltaAsset LegPair.srcDelta
  by_cases h : p.asset = a <;> simp [h]

theorem deltaAsset_dst (tid : ByteArray) (p : LegPair) (a : String) :
    deltaAsset (p.dstDelta tid) a = if p.asset == a then (p.amount : Int) else 0 := by
  unfold deltaAsset LegPair.dstDelta
  by_cases h : p.asset = a <;> simp [h]

/-- **The family is conserving, for every amount.** The half-edges of a fill's legs sum to zero at
every asset whatever the amounts are: `balanced` is a theorem of the shape, not a check of a value. -/
theorem pairs_balanced (tid : ByteArray) (ps : List LegPair) (a : String) :
    sumAssetDelta (pairDeltas tid ps) a = 0 := by
  unfold sumAssetDelta
  rw [foldl_add_int, Int.zero_add]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairDeltas, List.map_cons, List.sum_cons, deltaAsset_src, deltaAsset_dst]
    rw [ih]
    split <;> omega

theorem legTurnId_pairDeltas (tid : ByteArray) (ps : List LegPair) :
    ∀ d ∈ pairDeltas tid ps, legTurnId d = tid := by
  induction ps with
  | nil => intro d hd; cases hd
  | cons p ps ih =>
    intro d hd
    simp only [pairDeltas, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · rfl
    · rfl
    · exact ih d hd

/-- **The turn a fill denotes**, for any amounts: two legs per move, conserving by `pairs_balanced`. -/
def pairsTurn (tid : ByteArray) (pins : Footprint) (occ : Data) (ps : List LegPair)
    (h : ((pairDeltas tid ps).map CellDelta.cell).Nodup) : VaultTurn where
  turnId := tid
  readPins := pins
  writeCells := pairDeltas tid ps
  occasion := occ
  agree := legTurnId_pairDeltas tid ps
  balanced := pairs_balanced tid ps
  nodup_cells := h

/-! ## 6. The membrane's gate: authority and resources, discharged at fill time -/

/-- The viewer may write a page: its grant permits the page, and it holds the caps to see and write. -/
def mayWrite (v : MembraneViewer) (n : String) : Bool := v.permits n && fireGate [.read, .write] v.held

/-- The viewer may see a page. -/
def maySee (v : MembraneViewer) (n : String) : Bool := v.permits n && fireGate [.read] v.held

theorem maySee_of_mayWrite {v : MembraneViewer} {n : String} (h : mayWrite v n = true) :
    maySee v n = true := by
  simp only [mayWrite, maySee, Bool.and_eq_true, fireGate_iff_subset] at h ⊢
  exact ⟨h.1, fun x hx => h.2 (by simp at hx; simp [hx])⟩

/-- What a viewer may write, a viewer it attenuates may write. -/
theorem mayWrite_mono {v w : MembraneViewer} (hheld : v.held ⊆ w.held)
    (hperm : ∀ n, v.permits n = true → w.permits n = true) {n : String} (h : mayWrite v n = true) :
    mayWrite w n = true := by
  simp only [mayWrite, Bool.and_eq_true] at h ⊢
  exact ⟨hperm n h.1, fireGate_trans hheld h.2⟩

theorem maySee_mono {v w : MembraneViewer} (hheld : v.held ⊆ w.held)
    (hperm : ∀ n, v.permits n = true → w.permits n = true) {n : String} (h : maySee v n = true) :
    maySee w n = true := by
  simp only [maySee, Bool.and_eq_true] at h ⊢
  exact ⟨hperm n h.1, fireGate_trans hheld h.2⟩

/-- The gate on one page position of a fill: a page (not a hole), of the form's scope, that the
membrane's final viewer may write. -/
def checkPage (f : Form) (v : MembraneViewer) (holder : String) : PRef → Except Refusal Unit
  | .hole h => .error (.unfilled h)
  | .page n =>
    if !f.scope.contains n then .error (.notInForm n holder)
    else if !mayWrite v n then .error (.notWritable n holder v.held)
    else .ok ()

def checkMoves (f : Form) (v : MembraneViewer) (holder : String) : List RMove → Except Refusal Unit
  | [] => .ok ()
  | r :: rs => do
    checkPage f v holder r.src
    checkPage f v holder r.dst
    checkMoves f v holder rs

/-- **The membrane's gate**: the reshare chain from the root, then every page the fill names. It
reads no store. -/
def gate (root : MembraneViewer) (f : Form) (hops : List Grant) (rs : List RMove) :
    Except Refusal (MembraneViewer × String) :=
  match resolveChain f.scope root "owner" (f.grants ++ hops) with
  | .error r => .error r
  | .ok (v, holder) =>
    match checkMoves f v holder rs with
    | .error r => .error r
    | .ok () => .ok (v, holder)

/-- The read pins of a fill: every captured page it writes, at its state as captured (a page the form
only refers to is read live, unpinned). -/
def Form.pinsOf (f : Form) (ps : List LegPair) : Footprint :=
  (ps.flatMap fun p => [p.src, p.dst]).filterMap fun c => (f.known c).map fun d => ⟨c, some d⟩

/-- The fill of a form: the fill substituted into its residual (the capture's). -/
def Form.fill (f : Form) (a : Assignment) : List RMove := (f.residual f.known).map (·.subst a)

/-- An admitted fill: the membrane's final viewer and its holder, the legs, and the turn. -/
structure Admitted where
  viewer : MembraneViewer
  holder : String
  pairs : List LegPair
  turn : VaultTurn

/-- **Admit a fill**: the gate (authority), then the legs evaluated at `k` (resources: a move may
not take more than the page holds), then the turn, which may not write a page twice. -/
def admit (root : MembraneViewer) (f : Form) (hops : List Grant) (k : Known) (a : Assignment)
    (tid : ByteArray) (occ : Data) : Except Refusal Admitted :=
  match gate root f hops (f.fill a) with
  | .error r => .error r
  | .ok (v, holder) =>
    match pairsOf k (f.fill a) with
    | .error r => .error r
    | .ok ps =>
      if h : ((pairDeltas tid ps).map CellDelta.cell).Nodup then
        .ok ⟨v, holder, ps, pairsTurn tid (f.pinsOf ps) occ ps h⟩
      else .error (.twice ((firstDuplicateCell? ((pairDeltas tid ps).map CellDelta.cell)).getD "?"))

theorem checkPage_ok {f : Form} {v : MembraneViewer} {holder : String} {p : PRef}
    (h : checkPage f v holder p = .ok ()) : ∃ n, p = .page n ∧ n ∈ f.scope ∧ mayWrite v n = true := by
  cases p with
  | hole x => cases h
  | page n =>
    simp only [checkPage] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2
        refine ⟨n, rfl, ?_, ?_⟩
        · simpa using h1
        · simpa using h2

theorem checkMoves_ok {f : Form} {v : MembraneViewer} {holder : String} :
    ∀ {rs : List RMove}, checkMoves f v holder rs = .ok () → ∀ r ∈ rs,
      checkPage f v holder r.src = .ok () ∧ checkPage f v holder r.dst = .ok ()
  | [], _, r, hr => by cases hr
  | q :: qs, h, r, hr => by
    simp only [checkMoves, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hs
      split at h
      · cases h
      · rename_i hd
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨hs, hd⟩
        · exact checkMoves_ok h r hr

theorem gate_ok {root : MembraneViewer} {f : Form} {hops : List Grant} {rs : List RMove}
    {v : MembraneViewer} {holder : String} (h : gate root f hops rs = .ok (v, holder)) :
    resolveChain f.scope root "owner" (f.grants ++ hops) = .ok (v, holder) ∧
      checkMoves f v holder rs = .ok () := by
  unfold gate at h
  split at h
  · cases h
  · rename_i v' holder' hres
    split at h
    · cases h
    · rename_i hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hres, hc⟩

/-- What a move's evaluation says of its legs. -/
theorem RMove.pair_ok {k : Known} {r : RMove} {p : LegPair} (h : r.pair k = .ok p) :
    r.src = .page p.src ∧ r.dst = .page p.dst ∧ k p.src = some p.srcPre ∧ k p.dst = some p.dstPre ∧
      r.amount.eval k = some p.amount ∧ r.debit.eval k = some p.srcAfter ∧
      r.credit.eval k = some p.dstAfter ∧ r.asset = p.asset := by
  unfold RMove.pair at h
  split at h
  · cases h
  · cases h
  · rename_i s d hs hd
    split at h
    · cases h
    · cases h
    · rename_i ps pd hps hpd
      split at h
      · cases h
      · rename_i x hx
        split at h
        · rename_i sa da hsa hda
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨hs, hd, hps, hpd, hx, hsa, hda, rfl⟩
        · cases h
        · cases h

theorem pairsOf_ok {k : Known} :
    ∀ {rs : List RMove} {ps : List LegPair}, pairsOf k rs = .ok ps → ∀ p ∈ ps, ∃ r ∈ rs, r.pair k = .ok p
  | [], ps, h, p, hp => by
    simp only [pairsOf, Except.ok.injEq] at h
    subst h; cases hp
  | r :: rs, ps, h, p, hp => by
    simp only [pairsOf, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i qs hqs
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨r, List.mem_cons_self .., hq⟩
        · obtain ⟨r', hr', h'⟩ := pairsOf_ok hqs p hp
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem mem_pairDeltas {tid : ByteArray} {d : CellDelta} :
    ∀ {ps : List LegPair}, d ∈ pairDeltas tid ps → ∃ p ∈ ps, d = p.srcDelta tid ∨ d = p.dstDelta tid
  | [], h => by cases h
  | p :: ps, h => by
    simp only [pairDeltas, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨p, List.mem_cons_self .., Or.inl rfl⟩
    · exact ⟨p, List.mem_cons_self .., Or.inr rfl⟩
    · obtain ⟨q, hq, hd⟩ := mem_pairDeltas h
      exact ⟨q, List.mem_cons_of_mem _ hq, hd⟩

theorem admit_ok {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment}
    {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) :
    gate root f hops (f.fill a) = .ok (ad.viewer, ad.holder) ∧ pairsOf k (f.fill a) = .ok ad.pairs ∧
      ad.turn.writeCells = pairDeltas tid ad.pairs ∧ ad.turn.readPins = f.pinsOf ad.pairs := by
  unfold admit at h
  split at h
  · cases h
  · rename_i v holder hg
    split at h
    · cases h
    · rename_i ps hps
      split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hg, hps, rfl, rfl⟩
      · cases h

/-- Every page an admitted turn writes is a page of the form its final viewer may write. -/
theorem admit_writes {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) :
    ∀ d ∈ ad.turn.writeCells, mayWrite ad.viewer d.cell = true ∧ d.cell ∈ f.scope := by
  obtain ⟨hg, hps, hw, _⟩ := admit_ok h
  obtain ⟨_, hc⟩ := gate_ok hg
  intro d hd
  rw [hw] at hd
  obtain ⟨p, hp, hdp⟩ := mem_pairDeltas hd
  obtain ⟨r, hr, hpair⟩ := pairsOf_ok hps p hp
  obtain ⟨hsrc, hdst, _⟩ := RMove.pair_ok hpair
  obtain ⟨hcs, hcd⟩ := checkMoves_ok hc r hr
  rcases hdp with rfl | rfl
  · rw [hsrc] at hcs
    obtain ⟨n, hn, hscope, hmay⟩ := checkPage_ok hcs
    cases hn
    exact ⟨hmay, hscope⟩
  · rw [hdst] at hcd
    obtain ⟨n, hn, hscope, hmay⟩ := checkPage_ok hcd
    cases hn
    exact ⟨hmay, hscope⟩

theorem mem_pinsOf {f : Form} {ps : List LegPair} {q : FootprintPin} (hq : q ∈ f.pinsOf ps) :
    ∃ p ∈ ps, q.cell = p.src ∨ q.cell = p.dst := by
  simp only [Form.pinsOf, List.mem_filterMap, List.mem_flatMap] at hq
  obtain ⟨c, ⟨p, hp, hc⟩, hq⟩ := hq
  cases hk : f.known c with
  | none => rw [hk] at hq; cases hq
  | some d =>
    rw [hk] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨p, hp, hc⟩

theorem srcDelta_mem {tid : ByteArray} {p : LegPair} : ∀ {ps : List LegPair}, p ∈ ps →
    p.srcDelta tid ∈ pairDeltas tid ps ∧ p.dstDelta tid ∈ pairDeltas tid ps
  | [], h => by cases h
  | q :: qs, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [pairDeltas]
    · have := srcDelta_mem (tid := tid) h
      simp [pairDeltas, this.1, this.2]

/-- A turn the viewer `v` could have written directly: every page it writes, `v` may write, and
every page it reads, `v` may see. -/
def DirectlyAdmits (v : MembraneViewer) (t : VaultTurn) : Prop :=
  (∀ d ∈ t.writeCells, mayWrite v d.cell = true) ∧ (∀ q ∈ t.readPins, maySee v q.cell = true)

/-- **No amplification through forms.** An admitted fill's turn is one the membrane's final viewer
could have written directly, and so is one the root could have written directly: the reshare chain
(each hop `Membrane.reshare`) only attenuates (`resolveChain_attenuates`), and the fill adds no
authority to it, whatever it puts in the holes. -/
theorem admit_no_amplification {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) :
    DirectlyAdmits ad.viewer ad.turn ∧ DirectlyAdmits root ad.turn ∧
      ad.viewer.held ⊆ root.held ∧ (∀ n, ad.viewer.permits n = true → root.permits n = true) := by
  obtain ⟨hg, hps, hw, hpins⟩ := admit_ok h
  obtain ⟨hres, _⟩ := gate_ok hg
  obtain ⟨hheld, hperm⟩ := resolveChain_attenuates f.scope _ root "owner" hres
  have hwrites := admit_writes h
  have hreads : ∀ q ∈ ad.turn.readPins, maySee ad.viewer q.cell = true := by
    intro q hq
    rw [hpins] at hq
    obtain ⟨p, hp, hc⟩ := mem_pinsOf hq
    have hsd : p.srcDelta tid ∈ ad.turn.writeCells ∧ p.dstDelta tid ∈ ad.turn.writeCells := by
      rw [hw]; exact srcDelta_mem hp
    rcases hc with hc | hc
    · rw [hc]; exact maySee_of_mayWrite (hwrites _ hsd.1).1
    · rw [hc]; exact maySee_of_mayWrite (hwrites _ hsd.2).1
  refine ⟨⟨fun d hd => (hwrites d hd).1, hreads⟩, ⟨fun d hd => ?_, fun q hq => ?_⟩, hheld, hperm⟩
  · exact mayWrite_mono hheld hperm (hwrites d hd).1
  · exact maySee_mono hheld hperm (hreads q hq)

/-- **A hidden page stays hidden through the fill**: a page the root (or the final viewer) does not
permit is neither written nor read by any admitted fill's turn. -/
theorem admit_hidden_untouched {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) {n : String} (hn : root.permits n = false) :
    n ∉ ad.turn.writeFootprint ∧ n ∉ ad.turn.readFootprint := by
  obtain ⟨⟨_, _⟩, ⟨hw, hr⟩, _, _⟩ := admit_no_amplification h
  constructor
  · intro hmem
    simp only [VaultTurn.writeFootprint, List.mem_map] at hmem
    obtain ⟨d, hd, rfl⟩ := hmem
    have := hw d hd
    simp [mayWrite, hn] at this
  · intro hmem
    simp only [VaultTurn.readFootprint, List.mem_map] at hmem
    obtain ⟨q, hq, rfl⟩ := hmem
    have := hr q hq
    simp [maySee, hn] at this

/-- A form made by capture: the cells the viewer `v` sees, culled from `cs`. -/
def captureForm (name : String) (grants : List Grant) (v : MembraneViewer) (cs : List Cell)
    (refs : List String) (holes : List (String × HoleTy)) (moves : List Move) : Form :=
  { name := name, grants := grants, cells := capture v cs, refs := refs, holes := holes, moves := moves }

/-- **A hidden change is invisible through the whole passage**: changing a cell the capturing
viewer does not see gives the same form, so the same residual, the same admission and the same turn
for every fill. -/
theorem hidden_change_invisible_through_form (name : String) (grants : List Grant) (v : MembraneViewer)
    (pre post : List Cell) (c c' : Cell) (hc : shows v c = false) (hc' : shows v c' = false)
    (refs : List String) (holes : List (String × HoleTy)) (moves : List Move)
    (root : MembraneViewer) (hops : List Grant) (k : Known) (a : Assignment) (tid : ByteArray) (occ : Data) :
    captureForm name grants v (pre ++ c :: post) refs holes moves =
      captureForm name grants v (pre ++ c' :: post) refs holes moves ∧
    admit root (captureForm name grants v (pre ++ c :: post) refs holes moves) hops k a tid occ =
      admit root (captureForm name grants v (pre ++ c' :: post) refs holes moves) hops k a tid occ := by
  have heq : captureForm name grants v (pre ++ c :: post) refs holes moves =
      captureForm name grants v (pre ++ c' :: post) refs holes moves := by
    simp only [captureForm, capture_hidden_change v pre post c c' hc hc']
  exact ⟨heq, by rw [heq]⟩

/-! ## 7. What the family conserves -/

/-- The legs of an admitted fill are honest: the source's field after is what it held less the
amount (which it held at least), the destination's what it held plus the amount. -/
theorem admit_pairs_honest {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) :
    ∀ p ∈ ad.pairs, p.srcAfter + p.amount = natAt p.srcPre p.asset ∧
      p.dstAfter = natAt p.dstPre p.asset + p.amount := by
  obtain ⟨_, hps, _, _⟩ := admit_ok h
  intro p hp
  obtain ⟨r, hr, hpair⟩ := pairsOf_ok hps p hp
  simp only [Form.fill, Form.residual, List.map_map, List.mem_map, Function.comp] at hr
  obtain ⟨m, _, rfl⟩ := hr
  rw [RMove.pair_peval_subst hk] at hpair
  obtain ⟨hsrc, hdst, hks, hkd, hx, hdeb, hcred, hasset⟩ := RMove.pair_ok hpair
  simp only [Move.unfold, RMove.subst] at hsrc hdst hx hdeb hcred hasset
  rw [← hasset]
  simp only [NExpr.subst, NExpr.eval, hsrc, hdst, hks, hkd, hx, Option.map_some, Option.bind_eq_bind,
    Option.bind_some] at hdeb hcred
  constructor
  · split at hdeb
    · rename_i hle
      simp only [pure, Option.some.injEq] at hdeb
      omega
    · cases hdeb
  · simp only [pure, Option.some.injEq] at hcred
    omega

/-- **The half-edges report the change.** Every leg of an admitted fill's turn moves every field by
exactly its half-edge: the field moved by the amount, every other field not at all. -/
theorem admit_halfEdges_honest {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) :
    ∀ d ∈ ad.turn.writeCells, ∀ A : String,
      (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A := by
  obtain ⟨_, _, hw, _⟩ := admit_ok h
  have hhon := admit_pairs_honest hk h
  intro d hd A
  rw [hw] at hd
  obtain ⟨p, hp, hdp⟩ := mem_pairDeltas hd
  obtain ⟨h1, h2⟩ := hhon p hp
  rcases hdp with rfl | rfl
  · rw [deltaAsset_src]
    simp only [LegPair.srcDelta]
    by_cases hA : p.asset = A
    · subst hA; simp only [natAt_putNat, beq_self_eq_true, ↓reduceIte]; omega
    · have hne : (p.asset == A) = false := by simpa using hA
      rw [natAt_putNat_ne _ _ _ _ (Ne.symm hA)]; simp [hne]
  · rw [deltaAsset_dst]
    simp only [LegPair.dstDelta]
    by_cases hA : p.asset = A
    · subst hA; simp only [natAt_putNat, beq_self_eq_true, ↓reduceIte]; omega
    · have hne : (p.asset == A) = false := by simpa using hA
      rw [natAt_putNat_ne _ _ _ _ (Ne.symm hA)]; simp [hne]

theorem sum_map_add {l : List CellDelta} {post pre δ : CellDelta → Int}
    (h : ∀ d ∈ l, post d = pre d + δ d) : (l.map post).sum = (l.map pre).sum + (l.map δ).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h d (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    omega

/-- **`carry_conserves_total_book`, for a form.** For every fill the kernel's gate admits, whatever
amount filled the hole, every field's total over the pages the turn writes is what it was: the
strong hole is a family of conserving turns, its resources discharged at the fill. -/
theorem admit_conserves_written {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) (A : String) :
    (ad.turn.writeCells.map fun d => (natAt d.postState A : Int)).sum =
      (ad.turn.writeCells.map fun d => (natAt d.preState A : Int)).sum := by
  rw [sum_map_add (δ := fun d => deltaAsset d A) (admit_halfEdges_honest hk h · · A)]
  have hb := ad.turn.balanced A
  unfold sumAssetDelta at hb
  rw [foldl_add_int, Int.zero_add] at hb
  rw [hb, Int.add_zero]

/-- The total of the field `A` over the pages `cs` of a store (a page with no state counts 0). -/
def total (s : VaultStore) (A : String) (cs : List String) : Int :=
  (cs.map fun c => (((s c).map (natAt · A)).getD 0 : Int)).sum

theorem sum_filter_or {α : Type} (l : List α) (p q : α → Bool) (g : α → Int)
    (hdis : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) :
    ((l.filter fun x => p x || q x).map g).sum = ((l.filter p).map g).sum + ((l.filter q).map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih fun y hy => hdis y (List.mem_cons_of_mem _ hy)
    have hx := hdis x (List.mem_cons_self ..)
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- In a list of legs naming each page once, the legs writing a page are its one leg. -/
theorem filter_cell_single {d : CellDelta} :
    ∀ {W : List CellDelta}, (W.map CellDelta.cell).Nodup → d ∈ W → (W.filter fun x => x.cell == d.cell) = [d]
  | [], _, hd => by cases hd
  | x :: xs, hnd, hd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hd with rfl | hd'
    · have : (xs.filter fun y => y.cell == d.cell) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyc
        exact hnd.1 (by simp at hyc; rw [← hyc]; exact List.mem_map_of_mem hy)
      simp [this]
    · have hne : (x.cell == d.cell) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem hd')
      simp [hne, filter_cell_single hnd.2 hd']

/-- The change at one page, as the legs that write it say. -/
theorem change_at (s : VaultStore) (t : VaultTurn) (A c : String)
    (hpre : ∀ d ∈ t.writeCells, s d.cell = some d.preState) :
    ((((applyTurn s t c).map (natAt · A)).getD 0 : Nat) : Int) - (((s c).map (natAt · A)).getD 0 : Nat) =
      ((t.writeCells.filter fun d => d.cell == c).map fun d =>
        (natAt d.postState A : Int) - natAt d.preState A).sum := by
  by_cases hc : c ∈ t.writeFootprint
  · simp only [VaultTurn.writeFootprint, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rw [applyTurn_write s t d hd, hpre d hd]
    rw [filter_cell_single t.nodup_cells hd]
    simp
  · rw [applyTurn_frame_of_not_mem s t c hc]
    have : (t.writeCells.filter fun d => d.cell == c) = [] := by
      rw [List.filter_eq_nil_iff]
      intro d hd hdc
      simp at hdc
      exact hc (hdc ▸ List.mem_map_of_mem hd)
    simp [this]

theorem sum_over_cells (W : List CellDelta) (h : CellDelta → Int) :
    ∀ cs : List String, cs.Nodup →
      (cs.map fun c => ((W.filter fun d => d.cell == c).map h).sum).sum =
        ((W.filter fun d => cs.contains d.cell).map h).sum
  | [], _ => by
    have : (W.filter fun d => ([] : List String).contains d.cell) = [] := by
      rw [List.filter_eq_nil_iff]; intro d _; simp
    rw [this]; rfl
  | c :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, sum_over_cells W h rest hnd.2]
    have hsplit := sum_filter_or W (fun d => d.cell == c) (fun d => rest.contains d.cell) h (by
      intro d _ ⟨h1, h2⟩
      simp at h1 h2
      exact hnd.1 (h1 ▸ h2))
    have hfun : (fun d : CellDelta => (c :: rest).contains d.cell) =
        (fun d => (d.cell == c) || rest.contains d.cell) := by
      funext d; simp only [List.contains_cons]
    rw [hfun, hsplit]

/-- **A turn whose half-edges are honest conserves every total.** Over any pages `cs` (each once)
that include every page the turn writes, applied where its pre-states hold, the total of every field
is what it was: the turn's half-edges sum to zero (`balanced`), and each leg moves the field by its
half-edge. -/
theorem applyTurn_conserves_total (s : VaultStore) (t : VaultTurn) (A : String) (cs : List String)
    (hcs : cs.Nodup) (hw : ∀ c ∈ t.writeFootprint, c ∈ cs)
    (hpre : ∀ d ∈ t.writeCells, s d.cell = some d.preState)
    (hhon : ∀ d ∈ t.writeCells, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A) :
    total (applyTurn s t) A cs = total s A cs := by
  unfold total
  have hdiff : ∀ c ∈ cs, ((((applyTurn s t c).map (natAt · A)).getD 0 : Nat) : Int) =
      (((s c).map (natAt · A)).getD 0 : Nat) +
        ((t.writeCells.filter fun d => d.cell == c).map fun d =>
          (natAt d.postState A : Int) - natAt d.preState A).sum := by
    intro c _
    have := change_at s t A c hpre
    omega
  rw [List.map_congr_left hdiff]
  rw [show ∀ (l : List String) (f g : String → Int), (l.map fun c => f c + g c).sum = (l.map f).sum + (l.map g).sum
    from fun l f g => by induction l <;> simp_all [Int.add_assoc, Int.add_left_comm]]
  rw [sum_over_cells _ _ cs hcs]
  have hall : (t.writeCells.filter fun d => cs.contains d.cell) = t.writeCells := by
    rw [List.filter_eq_self]
    intro d hd
    simpa using hw d.cell (List.mem_map_of_mem hd)
  rw [hall]
  have hz : (t.writeCells.map fun d => (natAt d.postState A : Int) - natAt d.preState A).sum = 0 := by
    have hb := t.balanced A
    unfold sumAssetDelta at hb
    rw [foldl_add_int, Int.zero_add] at hb
    rw [← hb]
    congr 1
    exact List.map_congr_left fun d hd => by have := hhon d hd; omega
  rw [hz, Int.add_zero]

/-- **`carry_conserves_total_book`, for a form, at the store.** Applied where its pre-states hold
(what its pins and `ValidAt` ask), the turn of any fill the gate admits leaves the total of every field
over any pages that include those it writes as it was, whatever amount filled the hole. -/
theorem admit_conserves_total {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known}
    (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted}
    (h : admit root f hops k a tid occ = .ok ad) (s : VaultStore)
    (hpre : ∀ d ∈ ad.turn.writeCells, s d.cell = some d.preState) (A : String) (cs : List String)
    (hcs : cs.Nodup) (hw : ∀ c ∈ ad.turn.writeFootprint, c ∈ cs) :
    total (applyTurn s ad.turn) A cs = total s A cs :=
  applyTurn_conserves_total s ad.turn A cs hcs hw hpre fun d hd => admit_halfEdges_honest hk h d hd A

/-! ## 8. Abstraction of a form: the screenshot stays live -/

def Move.abstractNat (v : Nat) (h : String) (m : Move) : Move := { m with amount := m.amount.abstractNat v h }

def Move.abstractPage (n h : String) (m : Move) : Move :=
  { m with src := m.src.abstractPage n h, dst := m.dst.abstractPage n h, amount := m.amount.abstractPage n h }

def Move.holes (m : Move) : List String := m.src.holes ++ m.dst.holes ++ m.amount.holes

theorem PRef.subst_nats (p : PRef) (a : Assignment) (x : String × Nat) :
    p.subst ⟨x :: a.nats, a.pages⟩ = p.subst a := by
  cases p <;> rfl

theorem Move.unfold_subst_abstractNat (v : Nat) (h : String) (a : Assignment) (m : Move)
    (hf : h ∉ m.holes) :
    (m.abstractNat v h).unfold.subst ⟨(h, v) :: a.nats, a.pages⟩ = m.unfold.subst a := by
  simp only [Move.holes, List.mem_append, not_or] at hf
  simp only [Move.abstractNat, Move.unfold, RMove.subst, NExpr.subst, PRef.subst_nats,
    NExpr.subst_abstractNat_cons v h a m.amount hf.2]

theorem Move.unfold_subst_abstractPage (n h : String) (a : Assignment) (m : Move)
    (hf : h ∉ m.holes) :
    (m.abstractPage n h).unfold.subst ⟨a.nats, (h, n) :: a.pages⟩ = m.unfold.subst a := by
  simp only [Move.holes, List.mem_append, not_or] at hf
  simp only [Move.abstractPage, Move.unfold, RMove.subst, NExpr.subst,
    PRef.subst_abstractPage_cons n h a m.src hf.1.1, PRef.subst_abstractPage_cons n h a m.dst hf.1.2,
    NExpr.subst_abstractPage_cons n h a m.amount hf.2]

/-- A natural of the form's moves becomes the natural hole `h`. -/
def Form.abstractNat (f : Form) (v : Nat) (h : String) : Form :=
  { f with moves := f.moves.map (·.abstractNat v h), holes := f.holes ++ [(h, .nat)] }

/-- A page of the form's moves becomes the page hole `h`. -/
def Form.abstractPage (f : Form) (n h : String) : Form :=
  { f with moves := f.moves.map (·.abstractPage n h), holes := f.holes ++ [(h, .page)] }

/-- **Abstracting keeps the situation live.** Abstract a value of a form into a fresh hole and fill
the hole with that value: the legs are the original form's, for every other fill and every
knowledge `k` the judgment has. A captured turn with no holes is the live turn itself; a form is a
screenshot with some of its data replaced by variables, and filling them back gives it back. -/
theorem abstract_then_fill {k : Known} (f : Form) (hk : Agrees f.known k) (a : Assignment) (h : String)
    (hf : ∀ m ∈ f.moves, h ∉ m.holes) :
    (∀ v : Nat, pairsOf k ((f.abstractNat v h).fill ⟨(h, v) :: a.nats, a.pages⟩) = pairsOf k (f.fill a)) ∧
    (∀ n : String, pairsOf k ((f.abstractPage n h).fill ⟨a.nats, (h, n) :: a.pages⟩) = pairsOf k (f.fill a)) := by
  constructor
  · intro v
    have hk' : Agrees (f.abstractNat v h).known k := hk
    simp only [Form.fill]
    rw [eval_fill_eq_subst_residual hk', eval_fill_eq_subst_residual hk]
    congr 1
    simp only [Form.abstractNat, List.map_map]
    exact List.map_congr_left fun m hm => Move.unfold_subst_abstractNat v h a m (hf m hm)
  · intro n
    have hk' : Agrees (f.abstractPage n h).known k := hk
    simp only [Form.fill]
    rw [eval_fill_eq_subst_residual hk', eval_fill_eq_subst_residual hk]
    congr 1
    simp only [Form.abstractPage, List.map_map]
    exact List.map_congr_left fun m hm => Move.unfold_subst_abstractPage n h a m (hf m hm)

/-- **Abstract** `value` in a form into the hole `hole`: a natural becomes a natural hole, anything
else is a page name and becomes a page hole. Refused when the hole's name is taken or the value is
not in the form's moves. -/
def Form.abstract (f : Form) (value hole : String) : Except String Form :=
  if f.holes.any (·.1 == hole) || (f.moves.flatMap Move.holes).contains hole then
    .error ("the form " ++ f.name ++ " has a hole named " ++ hole)
  else match value.toNat? with
    | some v =>
      let g := f.abstractNat v hole
      if g.moves == f.moves then .error ("no " ++ value ++ " in the moves of " ++ f.name) else .ok g
    | none =>
      let g := f.abstractPage value hole
      if g.moves == f.moves then .error ("no page " ++ value ++ " in the moves of " ++ f.name) else .ok g

/-! ## 9. The kernel judges a proposal as it judges any write -/

/-- Set the frontmatter line `field: N` of a page's text; none when the page has no such line. -/
def setFront (md field : String) (v : Nat) : Option String :=
  match md.splitOn "\n" with
  | first :: rest =>
    if trim first != "---" then none else
    let fm := rest.takeWhile fun l => trim l != "---"
    let after := rest.drop fm.length
    let isField (l : String) : Bool := (splitColon l).map (·.1) == some field
    if after.isEmpty || !(fm.any isField) then none
    else some ("\n".intercalate (first :: fm.map (fun l => if isField l then field ++ ": " ++ toString v else l) ++ after))
  | [] => none

/-- A leg of a proposal as a write of the page's text `md`: the owner's write (the kernel's door for
every page write, `commit`, the laws as they stand, laws over links included), whose text is the
poster's (`new.poster`). -/
def legWrite (H : Obend.Digest.HashBytes.Hash) (s : Store) (p : Page) (md poster : String) : Change :=
  match p.current with
  | none => ⟨p.history, md, p.authors, some (p.name ++ " has no version to write"), p.kind⟩
  | some G =>
    let b := editPatch H G (align (pieces G p.name p.who) (Obend.Doc.contents (resolveIn H s.entries)
      (stripToks (Obend.Doc.tokens md)))) "owner"
    if b.ops.isEmpty then ⟨p.history, md, p.authors, none, p.kind⟩
    else match commit s.entries p (G.apply b.ops) (b.added.map (·, poster)) .owner s.turn
        (poster := poster) (env := s.environment) with
      | .ok ch => { ch with note := none }
      | .error msg => ⟨p.history, md, p.authors, some msg, p.kind⟩

/-- Write a proposal's legs, in order, each judged against the store the earlier legs made; the
first refusal refuses them all. -/
def writeLegs (H : Obend.Digest.HashBytes.Hash) (poster : String) : Store → List CellDelta → Except String Store
  | s, [] => .ok s
  | s, d :: ds =>
    match s.page? d.cell with
    | none => .error (d.cell ++ " is not a page here")
    | some p =>
      match p.render?, d.touchedFields.head? with
      | some md, some field =>
        match setFront md field (natAt d.postState field) with
        | none => .error (d.cell ++ " has no frontmatter line `" ++ field ++ ":`")
        | some md' =>
          let ch := legWrite H s p md' poster
          match ch.note with
          | some why => .error ("at " ++ d.cell ++ ": " ++ why)
          | none => writeLegs H poster (s.setPage (p.withChange ch)) ds
      | _, _ => .error (d.cell ++ " has no version to write")

def authName : Auth → String
  | .read => "read" | .write => "write" | .grant => "grant" | .call => "call"
  | .reply => "reply" | .reset => "reset" | .control => "control" | .notify => "notify"

def authOf : String → Option Auth
  | "read" => some .read | "write" => some .write | "grant" => some .grant | "call" => some .call
  | "reply" => some .reply | "reset" => some .reset | "control" => some .control
  | "notify" => some .notify | _ => none

def showAuths (l : List Auth) : String := if l.isEmpty then "nothing" else ", ".intercalate (l.map authName)

/-- Why a fill was refused before the laws were asked, said to a person. -/
def refusalText (f : Form) : Refusal → String
  | .amplifies who delegate held asked =>
    "refused by the membrane: " ++ who ++ " holds " ++ showAuths held ++ "; resharing " ++
      showAuths asked ++ " to " ++ delegate ++ " would amplify it"
  | .notInForm page holder =>
    "refused by the membrane: " ++ page ++ " is not a page of this form (" ++ holder ++ " may name " ++
      ", ".intercalate f.scope ++ ")"
  | .notWritable page holder held =>
    "refused by the membrane: " ++ holder ++ "'s grant does not let it write " ++ page ++
      " (it holds " ++ showAuths held ++ ")"
  | .unfilled h => "refused: the hole " ++ h ++ " is not filled"
  | .unknownPage page => "refused: " ++ page ++ " has no state to read"
  | .resources page asset holds moves =>
    "refused by the form's resources: " ++ page ++ " holds " ++ asset ++ " " ++ toString holds ++
      "; the fill moves " ++ toString moves
  | .unevaluated what => "refused: " ++ what ++ " does not evaluate"
  | .twice page => "refused: the fill writes " ++ page ++ " twice"

/-- The viewer of the vault's owner over a form's scope: the root of every chain. -/
def ownerViewer (f : Form) : MembraneViewer := ownerGrant.viewer f.scope

/-- **Judge a proposal**: the membrane's gate and the form's resources (`admit`, at what the kernel
knows: the captured states and every other page as it is), then the pins (each captured page the
turn writes must be as captured; else the refusal says what moved, as a merge does), then every leg
through `commit`, the laws live now. The store after, and the admitted turn. -/
def judgeProposal (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) (hops : List Grant)
    (a : Assignment) : Except String (Store × Admitted) :=
  match admit (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty
      (.label f.name) with
  | .error r => .error (refusalText f r)
  | .ok ad =>
    match admitFootprint (stateStore s.entries) ad.turn.readPins with
    | .error (.footprintStale cell exp cur) =>
      .error ("refused: stale: the form read " ++ cell ++ " as it was when captured (" ++
        stateDiffText exp cur ++ "); capture it again")
    | .error _ => .error "refused: its pins do not hold here"
    | .ok _ =>
      match writeLegs H ad.holder s ad.turn.writeCells with
      | .error e => .error e
      | .ok s' => .ok (s', ad)

/-- **The membrane refuses before anything is read**: a fill the gate refuses is refused with the
same words at every store, so a page hidden from the holder and a page that does not exist are
refused alike. -/
theorem judgeProposal_gate_first (H : Obend.Digest.HashBytes.Hash) (f : Form) (hops : List Grant)
    (a : Assignment) {r : Refusal} (hg : gate (ownerViewer f) f hops (f.fill a) = .error r) (s : Store) :
    judgeProposal H s f hops a = .error (refusalText f r) := by
  simp only [judgeProposal, admit, hg]

/-- **What the kernel landed, the gate admitted**: a proposal judged into a store was admitted by the
membrane at what the kernel knew, its pins held, and every leg passed `commit`. So every theorem of
`admit` holds of every landed proposal. -/
theorem judgeProposal_ok {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant}
    {a : Assignment} {ad : Admitted} (h : judgeProposal H s f hops a = .ok (s', ad)) :
    admit (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty (.label f.name) = .ok ad ∧
      admitFootprint (stateStore s.entries) ad.turn.readPins = .ok () ∧
      writeLegs H ad.holder s ad.turn.writeCells = .ok s' := by
  unfold judgeProposal at h
  split at h
  · cases h
  · rename_i ad' had
    split at h
    · cases h
    · cases h
    · rename_i u hfp
      split at h
      · cases h
      · rename_i s'' hw
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨had, hfp, hw⟩

/-- **A landed proposal conserves, and stays inside the membrane**: the corollary of
`judgeProposal_ok`, `admit_no_amplification` and `admit_conserves_written`, at the store it landed in. -/
theorem judgeProposal_sound {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant}
    {a : Assignment} {ad : Admitted} (h : judgeProposal H s f hops a = .ok (s', ad)) :
    DirectlyAdmits (ownerViewer f) ad.turn ∧ DirectlyAdmits ad.viewer ad.turn ∧
      (∀ d ∈ ad.turn.writeCells, d.cell ∈ f.scope) ∧
      ∀ A, (ad.turn.writeCells.map fun d => (natAt d.postState A : Int)).sum =
        (ad.turn.writeCells.map fun d => (natAt d.preState A : Int)).sum := by
  obtain ⟨had, _, _⟩ := judgeProposal_ok h
  obtain ⟨hv, hroot, _, _⟩ := admit_no_amplification had
  exact ⟨hroot, hv, fun d hd => (admit_writes had d hd).2,
    admit_conserves_written (f.known_agrees _) had⟩

/-! ## 10. On the wire: a form, a proposal, a receipt -/

open Lean (Json toJson)
open Obend.Spec.DataWire (dataJson decodeData)
open Obend.Vault.Rehydration (WitnessReceipt mkReceipt)

def grantJson (g : Grant) : Json :=
  Json.mkObj [("holder", g.holder), ("held", Json.arr (g.held.map fun x => toJson (authName x)).toArray),
    ("patterns", Json.arr (g.patterns.map toJson).toArray)]

def grantOf (j : Json) : Except String Grant := do
  let holder ← j.getObjValAs? String "holder"
  let held ← j.getObjValAs? (Array String) "held"
  let patterns ← j.getObjValAs? (Array String) "patterns"
  let auths ← held.toList.mapM fun x => match authOf x with
    | some a => .ok a
    | none => .error ("no cap named " ++ x)
  return ⟨holder, auths, patterns.toList⟩

def prefJson : PRef → Json
  | .page n => Json.mkObj [("page", n)]
  | .hole h => Json.mkObj [("hole", h)]

def prefOf (j : Json) : Except String PRef :=
  match j.getObjValAs? String "page" with
  | .ok n => .ok (.page n)
  | .error _ => do return .hole (← j.getObjValAs? String "hole")

def nexprJson : NExpr → Json
  | .lit n => Json.mkObj [("lit", toJson n)]
  | .hole h => Json.mkObj [("hole", h)]
  | .field p f => Json.mkObj [("field", f), ("of", prefJson p)]
  | .add x y => Json.mkObj [("add", Json.arr #[nexprJson x, nexprJson y])]
  | .sub x y => Json.mkObj [("sub", Json.arr #[nexprJson x, nexprJson y])]

def nexprOf : Nat → Json → Except String NExpr
  | 0, _ => .error "an expression nested too deep"
  | fuel + 1, j =>
    match j.getObjValAs? Nat "lit", j.getObjValAs? String "hole", j.getObjValAs? String "field" with
    | .ok n, _, _ => .ok (.lit n)
    | _, .ok h, _ => .ok (.hole h)
    | _, _, .ok f => do return .field (← prefOf (← j.getObjVal? "of")) f
    | _, _, _ =>
      let two (key : String) : Except String (NExpr × NExpr) := do
        let xs ← j.getObjValAs? (Array Json) key
        match xs.toList with
        | [x, y] => return (← nexprOf fuel x, ← nexprOf fuel y)
        | _ => .error "a sum or difference has two sides"
      match two "add", two "sub" with
      | .ok (x, y), _ => .ok (.add x y)
      | _, .ok (x, y) => .ok (.sub x y)
      | _, _ => .error "not an expression"

def moveJson (m : Move) : Json :=
  Json.mkObj [("asset", m.asset), ("from", prefJson m.src), ("to", prefJson m.dst), ("amount", nexprJson m.amount)]

def moveOf (j : Json) : Except String Move := do
  return ⟨← j.getObjValAs? String "asset", ← prefOf (← j.getObjVal? "from"), ← prefOf (← j.getObjVal? "to"),
    ← nexprOf 64 (← j.getObjVal? "amount")⟩

def cellJson (c : Cell) : Json :=
  Json.mkObj [("page", c.name), ("required", Json.arr (c.required.map fun x => toJson (authName x)).toArray),
    ("state", dataJson c.state)]

def cellOf (j : Json) : Except String Cell := do
  let req ← j.getObjValAs? (Array String) "required"
  let auths ← req.toList.mapM fun x => match authOf x with
    | some a => .ok a
    | none => .error ("no cap named " ++ x)
  return ⟨← j.getObjValAs? String "page", auths, ← decodeData 16 (← j.getObjVal? "state")⟩

def holeTyName : HoleTy → String
  | .nat => "natural"
  | .page => "page"

def formJson (f : Form) : Json :=
  Json.mkObj [("name", f.name), ("grants", Json.arr (f.grants.map grantJson).toArray),
    ("cells", Json.arr (f.cells.map cellJson).toArray), ("refs", Json.arr (f.refs.map toJson).toArray),
    ("holes", Json.arr (f.holes.map fun (h, t) => Json.mkObj [("hole", h), ("type", holeTyName t)]).toArray),
    ("moves", Json.arr (f.moves.map moveJson).toArray)]

def formOf (j : Json) : Except String Form := do
  let grants ← (← j.getObjValAs? (Array Json) "grants").toList.mapM grantOf
  let cells ← (← j.getObjValAs? (Array Json) "cells").toList.mapM cellOf
  let refs ← j.getObjValAs? (Array String) "refs"
  let holes ← (← j.getObjValAs? (Array Json) "holes").toList.mapM fun h => do
    let t ← h.getObjValAs? String "type"
    return (← h.getObjValAs? String "hole", if t == "page" then HoleTy.page else .nat)
  let moves ← (← j.getObjValAs? (Array Json) "moves").toList.mapM moveOf
  return { name := ← j.getObjValAs? String "name", grants := grants, cells := cells, refs := refs.toList,
           holes := holes, moves := moves }

def assignmentJson (a : Assignment) : Json :=
  Json.mkObj [("nats", Json.arr (a.nats.map fun (h, n) => Json.mkObj [("hole", h), ("value", toJson n)]).toArray),
    ("pages", Json.arr (a.pages.map fun (h, n) => Json.mkObj [("hole", h), ("page", n)]).toArray)]

def assignmentOf (j : Json) : Except String Assignment := do
  let nats ← (← j.getObjValAs? (Array Json) "nats").toList.mapM fun x => do
    return (← x.getObjValAs? String "hole", ← x.getObjValAs? Nat "value")
  let pages ← (← j.getObjValAs? (Array Json) "pages").toList.mapM fun x => do
    return (← x.getObjValAs? String "hole", ← x.getObjValAs? String "page")
  return ⟨nats, pages⟩

/-- A string's digest, as a natural: the first eight bytes of the vault's hash. -/
def digestNat (H : Obend.Digest.HashBytes.Hash) (s : String) : Nat :=
  ((H s.toUTF8.toList).take 8).foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Sixteen hex digits. -/
def hex16 (n : Nat) : String :=
  let ds := (List.range 16).reverse.map fun i => (n / 16 ^ i) % 16
  String.ofList (ds.map fun d => if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d))

/-- The digest of a form as it was issued: a proposal names it, and is judged only against it. -/
def formDigest (H : Obend.Digest.HashBytes.Hash) (f : Form) : String := hex16 (digestNat H (formJson f).compress)

def receiptJson (r : WitnessReceipt) : Json :=
  Json.mkObj [("prev", toJson r.prevHash), ("old", toJson r.oldCommit), ("new", toJson r.newCommit),
    ("effects", toJson r.effectsHash)]

def receiptOf (j : Json) : Except String WitnessReceipt := do
  return mkReceipt (← j.getObjValAs? Nat "prev") (← j.getObjValAs? Nat "old") (← j.getObjValAs? Nat "new")
    (← j.getObjValAs? Nat "effects")

def receiptDigest (H : Obend.Digest.HashBytes.Hash) (r : WitnessReceipt) : Nat :=
  digestNat H (receiptJson r).compress

/-- The receipt of a landed proposal, linked onto the last one (`mkReceipt`): the states its turn
read, the states it wrote, and the proposal (form, fill, holder). -/
def receiptFor (H : Obend.Digest.HashBytes.Hash) (prev : Option WitnessReceipt) (f : Form) (a : Assignment)
    (ad : Admitted) : WitnessReceipt :=
  let states (post : Bool) : String := (Json.arr (ad.turn.writeCells.map fun d =>
    Json.mkObj [("page", d.cell), ("state", dataJson (if post then d.postState else d.preState))]).toArray).compress
  mkReceipt ((prev.map (receiptDigest H)).getD Obend.Vault.Rehydration.genesisSentinel)
    (digestNat H (states false)) (digestNat H (states true))
    (digestNat H (Json.mkObj [("form", formDigest H f), ("fill", assignmentJson a), ("by", ad.holder)]).compress)

/-! ## 11. Said to a person -/

def PRef.show : PRef → String
  | .page n => n
  | .hole h => h

def NExpr.show : NExpr → String
  | .lit n => toString n
  | .hole h => h
  | .field p f => p.show ++ "." ++ f
  | .add x y => x.show ++ " + " ++ y.show
  | .sub x (.add a b) => x.show ++ " - (" ++ a.show ++ " + " ++ b.show ++ ")"
  | .sub x (.sub a b) => x.show ++ " - (" ++ (NExpr.sub a b).show ++ ")"
  | .sub x y => x.show ++ " - " ++ y.show

/-- A residual move, said: the two lines it writes. -/
def RMove.lines (r : RMove) : List String :=
  [r.src.show ++ "." ++ r.asset ++ " := " ++ r.debit.show,
   r.dst.show ++ "." ++ r.asset ++ " := " ++ r.credit.show]

/-- A form, as its holder sees it: the pages it captured, the pages it refers to, its holes, its
residual. -/
def Form.describe (f : Form) : List String :=
  let holder := ((f.grants.getLast?).map (·.holder)).getD "owner"
  let g := f.grants.getLast?
  [f.name ++ ": a form for " ++ holder ++ (match g with
      | some g => " (" ++ showAuths g.held ++ " on " ++ ", ".intercalate g.patterns ++ ")"
      | none => "")] ++
  (f.cells.map fun c => "  " ++ c.name ++ ": " ++ ", ".intercalate
      (((f.moves.map (·.asset)).eraseDups).map fun a => a ++ " " ++ toString (natAt c.state a))) ++
  (f.refs.map fun r => "  " ++ r ++ ": a reference (read where the form is judged)") ++
  (f.holes.map fun (h, t) => "  hole " ++ h ++ ": a " ++ holeTyName t) ++
  ((f.residual f.known).flatMap fun r => r.lines.map ("  " ++ ·))

/-! ## 12. Capturing a page situation from the vault -/

/-- **Capture** the situation of page `situation` (the page and every page it links to, and the
move's two pages) as the form `name` for the grant `g`: the cells `g` shows, each page at its state
now; the move `amount` of `field` from `src` to `dst`, with no holes (the live turn). The grant must be
a reshare of the owner's (`Membrane.reshare`), the move's pages shown to it, the references
permitted. With the form, how many pages of the situation the grant does not show. -/
def captureFrom (s : Store) (situation name : String) (g : Grant) (src dst : String) (amount : Nat)
    (field : String) (refs : List String) : Except String (Form × Nat) := do
  let some p := s.page? situation | throw ("no page named " ++ situation)
  let some G := p.current | throw (situation ++ " has no version yet")
  let names := ([situation] ++ citedNames s.entries G ++ [src, dst]).eraseDups
  let live := stateStore s.entries
  let cands : List Cell := names.filterMap fun n => (live n).map fun d => { name := n, state := d }
  let scope := cands.map (·.name) ++ refs
  let root := ownerGrant.viewer scope
  if (Membrane.reshare root (g.viewer scope)).isNone then
    throw (refusalText { name := name, grants := [], cells := [], moves := [] }
      (.amplifies "owner" g.holder root.held g.held))
  let v := g.viewer scope
  let cells := capture v cands
  for n in [src, dst] do
    unless cells.any (·.name == n) do
      throw (n ++ " is not shown to " ++ g.holder ++ "'s grant (" ++ showAuths g.held ++ " on " ++
        ", ".intercalate g.patterns ++ ")")
  for r in refs do
    unless g.permits r do throw (r ++ " is not permitted to " ++ g.holder ++ "'s grant")
  let mv : Move := { asset := field, src := .page src, dst := .page dst, amount := .lit amount }
  let f : Form := { name := name, grants := [g], cells := cells, refs := refs, moves := [mv] }
  return (f, cands.length - cells.length)

/-- What a fill makes of a form where the form is: the fill substituted into the residual, evaluated
again as far as the capture allows (a page the form did not capture stays a read). -/
def Form.preview (f : Form) (a : Assignment) : List String :=
  (f.fill a).flatMap fun r => (r.peval f.known).lines

end Obend.Vault.Form

end
