module
/-
# Obend.Leaf.Specialize — the emitted book as a candidate of a slot

DESIGN §7: an emitted leaf is a candidate whose supports are the pins it assumed, the machine is
the always-usable fallback, and deoptimization is the withdrawal of a support. This is the slot
(`Obend.Slot`) over two kinds of candidate, with no new slot theory:

* `Candidate.book name C`: the book `emit C` for the object `name`; its supports are the pins of the
  layers it flattened (`LeafCell.layer key ↦ L.code`) and of the object's composition, the layers in
  order and the seed (`LeafCell.object name ↦ C.code`); its judge admits compositions in the scope of
  `flatten_sound` (`Composition.closedB`);
* `Candidate.machine`: the unflattened term, no supports, always usable (`machine_usable`).

A view (`LeafView`) says what each cell holds now; `viewOf` is the view a program's object gives.
The read is the slot's: `book_usable_sound` says a usable book is the book of the composition the
view holds, so it computes what that object computes (`book_sound`); `specialize_choice` is the
incumbent-first law (`incumbent_choice`) at the order `[book, machine]`: the stored book is kept
exactly while its supports hold, else the machine is selected; `moved_pin_blocks` is
`read_blocked_exact`: a support that no longer holds blocks the book, and the read names it.
`specialize_integrity` is `slotFiller_integrity` at this world.

What the pins are, and what the guard costs (2026-11-04, `review/EXPERT-compiler-runtime-20261103.md`
§2.4). A pin is the **whole code** of a layer or of the object's composition, and it holds when the
view's term is structurally equal to it: `holdsOfPin` is `Obend.Law.termEq`, a comparison of the two
encodings, linear in the size of the layer. There is no hash, no epoch and no content address in this
module; a design that guards by `Obend.Core.Code.address` is `PROPOSED`, not built. The granularity is
the whole object: a change to any layer or to the seed blocks the whole book. The finer candidate
`Candidate.slotBook`, pinned to a member's read cone (`coneSupports`), exists and is proved
(`slotBook_moved_pin_blocks`) but is not in `specOrder`; nothing selects it. The decision is made
**once, before a run**, by whoever reads the slot (`obend specialize` rebuilds the view from source
and chooses); the demand machine carries no guard, no activation is invalidated while it runs, and
there is no on-stack replacement. "One-cycle deoptimization" in older documents named this choice,
not a mechanism in the machine.
-/
public import Obend.Leaf.Emit
public import Obend.Slot.Selection
import all Obend.Leaf.UpTo
import all Obend.Leaf.Flatten
import all Obend.Leaf.Emit
public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
set_option autoImplicit false

/-- What a support pins: a layer under its key, or an object's composition under its name. -/
inductive LeafCell where
  | layer (key : String)
  | object (name : String)
  deriving DecidableEq, Repr

/-- A support: the cell, and the code it held when the book was emitted. -/
structure LeafPin where
  cell : LeafCell
  code : Term

/-- A view: a clock, and what each cell holds now (`none`: absent). -/
structure LeafView where
  clock : Nat
  decl : LeafCell → Option Term

/-- The world of the specialization slot: each cell pinned to its code at the view's clock; a step
moves the clock forward. A support holds when its cell holds the code it pinned (`termEq`, so the
pin is exact: no collision disjunct is owed). -/
instance : World LeafView LeafPin where
  Cell := LeafCell
  Pin := Nat × Option Term
  cell := LeafPin.cell
  pin v c := some (v.clock, v.decl c)
  holdsOfPin _ p f := match p with
    | some (_, some t) => Obend.Law.termEq t f.code
    | _ => false
  Step v v' := v.clock < v'.clock
  dead_none _ := rfl
  retired_step _ _ _ _ h := by cases h
  Ver := Nat × Option Term
  ver v c := (v.clock, v.decl c)
  Past a b := a.1 < b.1
  past_irrefl _ := Nat.lt_irrefl _
  past_trans _ _ _ := Nat.lt_trans
  pinOf _ := some
  pin_ver _ _ := rfl
  ver_step _ _ _ h := .inr h

/-- Winning provenance layer name for member `m` in a stack of layers (outermost first). -/
@[expose] def provLayers : List Layer → String → String
  | [], _ => "seed"
  | L :: rest, m => if L.provides m then L.name else if L.flat then L.name else provLayers rest m

/-- Provenance layer of member `m` in composition `C`. -/
abbrev _root_.Obend.Logic.Composition.provenance (C : Composition) (m : String) : String :=
  provLayers C.layers m

/-- Resolved symbolic unfolding of member `m` in composition `C` (under 1 `self` binder at index 0). -/
abbrev _root_.Obend.Logic.Composition.symUnfold (C : Composition) (m : String) : Term :=
  match (flatRow C.seed C.layers).find? (·.1 == m) with
  | some (_, b) => resolve b
  | none => .label "missing"

/-- Split a reversed character list at the first `'.'` delimiter. -/
@[expose] def splitBeforeFirstDot : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if c == '.' then
      some ([], cs)
    else
      (splitBeforeFirstDot cs).map fun (pre, post) => (c :: pre, post)

/-- Split a scoped layer-member key `"provLayer.member"` at its last `'.'` into `(provLayer, member)`. -/
abbrev splitScopedLayerKey (k : String) : Option (String × String) :=
  match splitBeforeFirstDot k.toList.reverse with
  | some (revMember, revProv) =>
    some (String.ofList revProv.reverse, String.ofList revMember.reverse)
  | none => none

/-- Resolve `.layer k` in `viewOf`: first checks whole-layer declarations `C.layers`, then resolves
fine-grained per-member provenance keys `provLayer ++ "." ++ m` to `C.symUnfold m` when
`C.provenance m == provLayer`. -/
@[expose] def resolveLayerDecl (C : Composition) (k : String) : Option Term :=
  match (C.layers.find? (·.name == k)).map Layer.code with
  | some c => some c
  | none =>
    match splitScopedLayerKey k with
    | some (provLayer, m) =>
      if C.provenance m == provLayer then some (C.symUnfold m) else none
    | none => none

/-- The view a program's object gives: each of its layers under its key, each member under its
provenance-scoped key `provLayer ++ "." ++ m`, and its composition under its name. -/
abbrev viewOf (clock : Nat) (name : String) (C : Composition) : LeafView where
  clock := clock
  decl
    | .layer k => resolveLayerDecl C k
    | .object n => if n == name then some C.code else none

/-- The read-support cone of a slot `member` in composition `C`: `member` itself together with
all `self`-fields read by its unfolded body `C.symUnfold member` (and 1-hop transitive reads). -/
abbrev slotReadCone (C : Composition) (member : String) : List String :=
  let direct := selfReads 0 (C.symUnfold member)
  let twoHop := (direct.map (fun r => selfReads 0 (C.symUnfold r))).flatten
  member :: (direct ++ twoHop)

/-- Pin a single member `m` to its winning provenance layer and symbolic unfolding
`⟨.layer (C.provenance m ++ "." ++ m), C.symUnfold m⟩`. -/
abbrev memberConePin (C : Composition) (m : String) : LeafPin :=
  ⟨.layer (C.provenance m ++ "." ++ m), C.symUnfold m⟩

/-- Fine-grained per-slot support pins for a read-support `cone` of composition `C`. -/
abbrev coneSupports (C : Composition) (cone : List String) : List LeafPin :=
  cone.map (memberConePin C)

theorem holdsAt_eq (v : LeafView) (p : LeafPin) :
    holdsAt v p = match v.decl p.cell with
      | some t => Obend.Law.termEq t p.code
      | none => false := by
  show (match some (v.clock, v.decl p.cell) with
    | some (_, some t) => Obend.Law.termEq t p.code
    | _ => false) = _
  cases v.decl p.cell <;> rfl


/-! ## Dependency Support Extraction & Conservatism (`extractReadMembers`, `AgreeOnMembers`, `extractReadMembers_conservative`) -/

/-- String key of a `LeafCell`. -/
abbrev LeafCell.key : LeafCell → String
  | .layer k => k
  | .object n => n

/-- Helper for `.get g m` in `extractReadMembersAt`: when `g = .bound i` with `i == d`,
records member `m`; otherwise returns the reads of `g`. -/
abbrev extractMemberGet (d : Nat) : Term → List String → String → List String
  | .bound i, _, m => if i == d then [m] else []
  | _, gReads, _ => gReads

/-- Extract all member names read from the target binder at de Bruijn depth `d`
(`.get (.bound i) m` with `i == d`), traversing all subterms. -/
@[expose] def extractReadMembersAt (d : Nat) : Term → List String
  | .hole _ σ => (σ.map (extractReadMembersAt d)).flatten
  | .bound _ => []
  | .lam b => extractReadMembersAt (d + 1) b
  | .app f a => extractReadMembersAt d f ++ extractReadMembersAt d a
  | .mix l u => extractReadMembersAt d l ++ extractReadMembersAt d u
  | .fix s i => extractReadMembersAt d s ++ extractReadMembersAt d i
  | .specification m e => extractReadMembersAt d m ++ extractReadMembersAt d e
  | .prototype s g => extractReadMembersAt d s ++ extractReadMembersAt d g
  | .reflect p => extractReadMembersAt d p
  | .metadata p => extractReadMembersAt d p
  | .project p => extractReadMembersAt d p
  | .nat _ => []
  | .boolean _ => []
  | .label _ => []
  | .binary _ l r => extractReadMembersAt d l ++ extractReadMembersAt d r
  | .extend i fs => extractReadMembersAt d i ++ (fs.map fun f => extractReadMembersAt d f.2).flatten
  | .record fs => (fs.map fun f => extractReadMembersAt d f.2).flatten
  | .get g m => extractMemberGet d g (extractReadMembersAt d g) m
  | .ifZero v z s => extractReadMembersAt d v ++ extractReadMembersAt d z ++ extractReadMembersAt (d + 1) s
  | .inject _ p => extractReadMembersAt d p
  | .case sc arms => extractReadMembersAt d sc ++ (arms.map fun a => extractReadMembersAt (d + 1) a.2).flatten
  | .ifBool c x y => extractReadMembersAt d c ++ extractReadMembersAt d x ++ extractReadMembersAt d y
  | .perform p => extractReadMembersAt d p
  | .done p => extractReadMembersAt d p
  | .split t _ f => extractReadMembersAt d t ++ extractReadMembersAt d f
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- Extract all member names read via `.get (.bound 0) m` (adjusting binder depth under `.lam`,
`.ifZero`, and `.case`) across a `Term`. -/
@[expose] def extractReadMembers (t : Term) : List String :=
  extractReadMembersAt 0 t

/-- Alias for `extractReadMembers`. -/
abbrev extractReadPins : Term → List String := extractReadMembers

theorem attach_map_eq_map {α β : Type} (l : List α) (g : α → β) :
    (l.attach.map fun ⟨x, _⟩ => g x) = l.map g := by
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.map_map]; rfl

/-- **`extractReadMembersAt_eq_selfReads`**: `extractReadMembersAt d t` computes the exact same
member read list as `Obend.Leaf.selfReads d t` in `Emit.lean`. -/
theorem extractReadMembersAt_eq_selfReads :
    (d : Nat) → (t : Term) → extractReadMembersAt d t = selfReads d t
  | d, .hole _ σ => by
    simp only [extractReadMembersAt, selfReads,
      attach_map_eq_map σ (fun t => selfReads d t)]
    congr 1
    exact List.map_congr_left fun x hx => extractReadMembersAt_eq_selfReads d x
  | _, .bound _ | _, .nat _ | _, .boolean _ | _, .label _ => by
    simp [extractReadMembersAt, selfReads]
  | d, .lam b => by
    simp only [extractReadMembersAt, selfReads, extractReadMembersAt_eq_selfReads (d + 1) b]
  | d, .app f a | d, .mix f a | d, .fix f a | d, .specification f a
  | d, .prototype f a | d, .binary _ f a | d, .split f _ a => by
    simp only [extractReadMembersAt, selfReads,
      extractReadMembersAt_eq_selfReads d f, extractReadMembersAt_eq_selfReads d a]
  | d, .reflect p | d, .metadata p | d, .project p | d, .inject _ p
  | d, .perform p | d, .done p => by
    simp only [extractReadMembersAt, selfReads, extractReadMembersAt_eq_selfReads d p]
  | d, .extend i fs => by
    simp only [extractReadMembersAt, selfReads,
      attach_map_eq_map fs (fun f : String × Term => selfReads d f.2),
      extractReadMembersAt_eq_selfReads d i]
    congr 2
    exact List.map_congr_left fun f hf => extractReadMembersAt_eq_selfReads d f.2
  | d, .record fs => by
    simp only [extractReadMembersAt, selfReads,
      attach_map_eq_map fs (fun f : String × Term => selfReads d f.2)]
    congr 1
    exact List.map_congr_left fun f hf => extractReadMembersAt_eq_selfReads d f.2
  | d, .get g m => by
    have ih := extractReadMembersAt_eq_selfReads d g
    cases g <;> simp [extractReadMembersAt, extractMemberGet, selfReads, ih]
  | d, .ifZero v z s => by
    simp only [extractReadMembersAt, selfReads,
      extractReadMembersAt_eq_selfReads d v,
      extractReadMembersAt_eq_selfReads d z,
      extractReadMembersAt_eq_selfReads (d + 1) s]
  | d, .case sc arms => by
    simp only [extractReadMembersAt, selfReads,
      attach_map_eq_map arms (fun a : String × Term => selfReads (d + 1) a.2),
      extractReadMembersAt_eq_selfReads d sc]
    congr 2
    exact List.map_congr_left fun a ha => extractReadMembersAt_eq_selfReads (d + 1) a.2
  | d, .ifBool c x y => by
    simp only [extractReadMembersAt, selfReads,
      extractReadMembersAt_eq_selfReads d c,
      extractReadMembersAt_eq_selfReads d x,
      extractReadMembersAt_eq_selfReads d y]
termination_by _ t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hf; omega)
    | (have := sizeOf_snd_lt_of_mem ha; omega)

@[simp] theorem extractReadMembers_eq_selfReads (t : Term) :
    extractReadMembers t = selfReads 0 t :=
  extractReadMembersAt_eq_selfReads 0 t


/-- Two member environments `env1` and `env2` agree on `ms` when every member name `m ∈ ms`
has the identical binding in both environments. -/
abbrev AgreeOnMembers (ms : List String) (env1 env2 : String → Option Term) : Prop :=
  ∀ m ∈ ms, env1 m = env2 m

theorem AgreeOnMembers.refl (ms : List String) (env : String → Option Term) :
    AgreeOnMembers ms env env :=
  fun _ _ => rfl

theorem AgreeOnMembers.symm {ms : List String} {env1 env2 : String → Option Term}
    (h : AgreeOnMembers ms env1 env2) : AgreeOnMembers ms env2 env1 :=
  fun m hm => (h m hm).symm

theorem AgreeOnMembers.trans {ms : List String} {env1 env2 env3 : String → Option Term}
    (h12 : AgreeOnMembers ms env1 env2) (h23 : AgreeOnMembers ms env2 env3) :
    AgreeOnMembers ms env1 env3 :=
  fun m hm => (h12 m hm).trans (h23 m hm)

theorem AgreeOnMembers.left {ms1 ms2 : List String} {env1 env2 : String → Option Term}
    (h : AgreeOnMembers (ms1 ++ ms2) env1 env2) : AgreeOnMembers ms1 env1 env2 :=
  fun m hm => h m (List.mem_append_left ms2 hm)

theorem AgreeOnMembers.right {ms1 ms2 : List String} {env1 env2 : String → Option Term}
    (h : AgreeOnMembers (ms1 ++ ms2) env1 env2) : AgreeOnMembers ms2 env1 env2 :=
  fun m hm => h m (List.mem_append_right ms1 hm)

theorem AgreeOnMembers.of_subset {ms1 ms2 : List String} {env1 env2 : String → Option Term}
    (hsub : ∀ m ∈ ms1, m ∈ ms2) (h : AgreeOnMembers ms2 env1 env2) :
    AgreeOnMembers ms1 env1 env2 :=
  fun m hm => h m (hsub m hm)

theorem mem_flatten_map {α β : Type} {l : List α} (f : α → List β) {x : α} (hx : x ∈ l)
    {y : β} (hy : y ∈ f x) :
    y ∈ (l.map f).flatten :=
  List.mem_flatten.2 ⟨f x, List.mem_map.2 ⟨x, hx, rfl⟩, hy⟩

/-- Helper for `.get g m` in `substMemberEnvAt`: when `g = .bound i` with `i == d`,
substitutes `env m` if present; otherwise keeps `.get g' m`. -/
abbrev resolveMemberGet (d : Nat) (env : String → Option Term) : Term → Term → String → Term
  | .bound i, _, m =>
    if i == d then
      match env m with
      | some v => v
      | none => .get (.bound i) m
    else
      .get (.bound i) m
  | _, g', m => .get g' m

/-- Substitute pinned member values from `env` for `.get (.bound i) m` reads at de Bruijn depth `d`. -/
@[expose] def substMemberEnvAt (d : Nat) (env : String → Option Term) : Term → Term
  | .hole n σ => .hole n (σ.map (substMemberEnvAt d env))
  | .bound i => .bound i
  | .lam b => .lam (substMemberEnvAt (d + 1) env b)
  | .app f a => .app (substMemberEnvAt d env f) (substMemberEnvAt d env a)
  | .mix l u => .mix (substMemberEnvAt d env l) (substMemberEnvAt d env u)
  | .fix s i => .fix (substMemberEnvAt d env s) (substMemberEnvAt d env i)
  | .specification m e => .specification (substMemberEnvAt d env m) (substMemberEnvAt d env e)
  | .prototype s g => .prototype (substMemberEnvAt d env s) (substMemberEnvAt d env g)
  | .reflect p => .reflect (substMemberEnvAt d env p)
  | .metadata p => .metadata (substMemberEnvAt d env p)
  | .project p => .project (substMemberEnvAt d env p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => .binary op (substMemberEnvAt d env l) (substMemberEnvAt d env r)
  | .extend i fs => .extend (substMemberEnvAt d env i) (fs.map fun f => (f.1, substMemberEnvAt d env f.2))
  | .record fs => .record (fs.map fun f => (f.1, substMemberEnvAt d env f.2))
  | .get g m => resolveMemberGet d env g (substMemberEnvAt d env g) m
  | .ifZero v z s => .ifZero (substMemberEnvAt d env v) (substMemberEnvAt d env z) (substMemberEnvAt (d + 1) env s)
  | .inject l p => .inject l (substMemberEnvAt d env p)
  | .case sc arms => .case (substMemberEnvAt d env sc) (arms.map fun a => (a.1, substMemberEnvAt (d + 1) env a.2))
  | .ifBool c x y => .ifBool (substMemberEnvAt d env c) (substMemberEnvAt d env x) (substMemberEnvAt d env y)
  | .perform p => .perform (substMemberEnvAt d env p)
  | .done p => .done (substMemberEnvAt d env p)
  | .split t ns f => .split (substMemberEnvAt d env t) ns (substMemberEnvAt d env f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- Specialize a `Term` by resolving `.get (.bound 0) m` reads against member environment `env`. -/
abbrev substMemberEnv (env : String → Option Term) (t : Term) : Term :=
  substMemberEnvAt 0 env t

/-- Evaluate `t` under member environment `env` using `fuel` steps of `Obend.Law.run`. -/
def evalWithMemberEnv (fuel : Nat) (env : String → Option Term) (t : Term) : Option Term :=
  Obend.Law.run fuel (substMemberEnv env t)

theorem resolveMemberGet_congr (d : Nat) (g g1 g2 : Term) (m : String)
    {env1 env2 : String → Option Term}
    (readsG : List String)
    (h : AgreeOnMembers (extractMemberGet d g readsG m) env1 env2)
    (ih : AgreeOnMembers readsG env1 env2 → g1 = g2) :
    resolveMemberGet d env1 g g1 m = resolveMemberGet d env2 g g2 m := by
  cases g <;> try (simp only [extractMemberGet] at h; simp [resolveMemberGet, ih h])
  rename_i i
  simp only [extractMemberGet] at h
  simp only [resolveMemberGet]
  by_cases hid : (i == d) = true
  · simp only [hid, ite_true] at h ⊢
    rw [h m List.mem_cons_self]
  · simp [hid]

/-- **Core Support Extraction Conservatism Lemma (`extractReadMembersAt_conservative`)**:
If `env1` and `env2` agree on `extractReadMembersAt d t`, then specializing `t` at depth `d`
under `env1` and under `env2` produces the exact same `Term`. -/
theorem extractReadMembersAt_conservative :
    (d : Nat) → (t : Term) → ∀ {env1 env2 : String → Option Term},
      AgreeOnMembers (extractReadMembersAt d t) env1 env2 →
      substMemberEnvAt d env1 t = substMemberEnvAt d env2 t
  | d, .hole n σ, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp only [substMemberEnvAt, Term.hole.injEq, true_and]
    apply List.map_congr_left
    intro x hx
    exact extractReadMembersAt_conservative d x
      (fun m hm => h m (mem_flatten_map (extractReadMembersAt d) hx hm))
  | _, .bound _, _, _, _ => by simp [substMemberEnvAt]
  | _, .nat _, _, _, _ => by simp [substMemberEnvAt]
  | _, .boolean _, _, _, _ => by simp [substMemberEnvAt]
  | _, .label _, _, _, _ => by simp [substMemberEnvAt]
  | d, .lam b, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative (d + 1) b h]
  | d, .app f a, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d f h.left,
      extractReadMembersAt_conservative d a h.right]
  | d, .mix l u, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d l h.left,
      extractReadMembersAt_conservative d u h.right]
  | d, .fix s i, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d s h.left,
      extractReadMembersAt_conservative d i h.right]
  | d, .specification m e, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d m h.left,
      extractReadMembersAt_conservative d e h.right]
  | d, .prototype s g, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d s h.left,
      extractReadMembersAt_conservative d g h.right]
  | d, .reflect p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .metadata p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .project p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .inject _ p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .perform p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .done p, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d p h]
  | d, .binary op l r, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d l h.left,
      extractReadMembersAt_conservative d r h.right]
  | d, .extend i fs, _, _, h => by
    simp only [extractReadMembersAt] at h
    have hi := extractReadMembersAt_conservative d i h.left
    have hfs := h.right
    simp only [substMemberEnvAt, hi, Term.extend.injEq, true_and]
    apply List.map_congr_left
    intro f hf
    simp only [Prod.mk.injEq, true_and]
    exact extractReadMembersAt_conservative d f.2
      (fun m hm => hfs m (mem_flatten_map (fun x : String × Term => extractReadMembersAt d x.2) hf hm))
  | d, .record fs, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp only [substMemberEnvAt, Term.record.injEq]
    apply List.map_congr_left
    intro f hf
    simp only [Prod.mk.injEq, true_and]
    exact extractReadMembersAt_conservative d f.2
      (fun m hm => h m (mem_flatten_map (fun x : String × Term => extractReadMembersAt d x.2) hf hm))
  | d, .get g m, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp only [substMemberEnvAt]
    exact resolveMemberGet_congr d g _ _ m (extractReadMembersAt d g) h
      (extractReadMembersAt_conservative d g)
  | d, .ifZero v z s, _, _, h => by
    simp only [extractReadMembersAt] at h
    have hvz := h.left
    simp [substMemberEnvAt,
      extractReadMembersAt_conservative d v hvz.left,
      extractReadMembersAt_conservative d z hvz.right,
      extractReadMembersAt_conservative (d + 1) s h.right]
  | d, .case sc arms, _, _, h => by
    simp only [extractReadMembersAt] at h
    have hsc := extractReadMembersAt_conservative d sc h.left
    have harms := h.right
    simp only [substMemberEnvAt, hsc, Term.case.injEq, true_and]
    apply List.map_congr_left
    intro a ha
    simp only [Prod.mk.injEq, true_and]
    exact extractReadMembersAt_conservative (d + 1) a.2
      (fun m hm => harms m (mem_flatten_map (fun x : String × Term => extractReadMembersAt (d + 1) x.2) ha hm))
  | d, .ifBool c x y, _, _, h => by
    simp only [extractReadMembersAt] at h
    have hcx := h.left
    simp [substMemberEnvAt,
      extractReadMembersAt_conservative d c hcx.left,
      extractReadMembersAt_conservative d x hcx.right,
      extractReadMembersAt_conservative d y h.right]
  | d, .split t ns f, _, _, h => by
    simp only [extractReadMembersAt] at h
    simp [substMemberEnvAt, extractReadMembersAt_conservative d t h.left,
      extractReadMembersAt_conservative d f h.right]
termination_by _ t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_snd_lt_of_mem hf; omega)
    | (have := sizeOf_snd_lt_of_mem ha; omega)

/-- **Support Extraction Conservatism & Reuse Theorem (`extractReadMembers_conservative`)**:
If two member environments `env1` and `env2` agree on `extractReadMembers t`, then:
1. Specializing `t` under `env1` and `env2` yields the exact same `Term` (`substMemberEnv env1 t = substMemberEnv env2 t`),
2. Evaluating `t` under `env1` and `env2` produces the exact same result at every fuel bound (`evalWithMemberEnv fuel env1 t = evalWithMemberEnv fuel env2 t`),
3. Reference evaluation `Evaluates` and ground observations `Halts` are identical under `env1` and `env2`. -/
theorem extractReadMembers_conservative {t : Term} {env1 env2 : String → Option Term}
    (h : AgreeOnMembers (extractReadMembers t) env1 env2) :
    substMemberEnv env1 t = substMemberEnv env2 t ∧
    (∀ fuel, evalWithMemberEnv fuel env1 t = evalWithMemberEnv fuel env2 t) ∧
    (∀ v, Evaluates (substMemberEnv env1 t) v ↔ Evaluates (substMemberEnv env2 t) v) ∧
    (∀ o, Halts (substMemberEnv env1 t) o ↔ Halts (substMemberEnv env2 t) o) := by
  have heq : substMemberEnv env1 t = substMemberEnv env2 t :=
    extractReadMembersAt_conservative 0 t h
  refine ⟨heq, fun fuel => by simp [evalWithMemberEnv, heq],
    fun v => by rw [heq], fun o => by rw [heq]⟩

/-- Mutate a single member `k` in a member environment `env`. -/
abbrev mutateMemberEnv (env : String → Option Term) (k : String) (v : Option Term) : String → Option Term :=
  fun m => if m == k then v else env m

theorem agreeOnMembers_mutate_outside {ms : List String} (env : String → Option Term)
    {k : String} (v : Option Term) (hk : k ∉ ms) :
    AgreeOnMembers ms (mutateMemberEnv env k v) env := by
  intro m hm
  unfold mutateMemberEnv
  have hne : (m == k) = false := by
    cases hmk : m == k with
    | false => rfl
    | true =>
      have : m = k := beq_iff_eq.1 hmk
      subst this
      exact absurd hm hk
  simp [hne]

/-- **Non-Supported Field Mutation Invariance (`extractReadMembers_mutation_invariant`)**:
Any store/environment mutation to a field `k ∉ extractReadMembers t` leaves the specialized term
and its evaluation completely invariant. -/
theorem extractReadMembers_mutation_invariant (t : Term) (env : String → Option Term)
    {k : String} (v : Option Term) (hk : k ∉ extractReadMembers t) :
    substMemberEnv (mutateMemberEnv env k v) t = substMemberEnv env t ∧
    (∀ fuel, evalWithMemberEnv fuel (mutateMemberEnv env k v) t = evalWithMemberEnv fuel env t) := by
  have hcons := extractReadMembers_conservative (agreeOnMembers_mutate_outside env v hk)
  exact ⟨hcons.1, hcons.2.1⟩

/-- Member environment induced by the layer declarations of a `LeafView`. -/
def viewLayerEnv (v : LeafView) : String → Option Term :=
  fun m => v.decl (.layer m)

/-- Member environment induced by a list of `LeafPin` supports. -/
abbrev pinListEnv (pins : List LeafPin) : String → Option Term :=
  fun m => (pins.find? (fun p => p.cell.key == m)).map (·.code)

/-- A support list `pins` covers member names `ms` when every `m ∈ ms` has a layer pin in `pins`. -/
abbrev SupportsCoverMembers (pins : List LeafPin) (ms : List String) : Prop :=
  ∀ m ∈ ms, ∃ code, LeafPin.mk (.layer m) code ∈ pins

/-- If `pins` cover `ms` and all `pins` hold in both `v1` and `v2`, then `viewLayerEnv v1`
and `viewLayerEnv v2` agree on `ms`. -/
theorem supports_cover_agree_of_holdsAt {pins : List LeafPin} {ms : List String}
    {v1 v2 : LeafView} (hcov : SupportsCoverMembers pins ms)
    (h1 : ∀ p ∈ pins, holdsAt v1 p = true)
    (h2 : ∀ p ∈ pins, holdsAt v2 p = true) :
    AgreeOnMembers ms (viewLayerEnv v1) (viewLayerEnv v2) := by
  intro m hm
  obtain ⟨code, hp⟩ := hcov m hm
  have hv1 := h1 ⟨.layer m, code⟩ hp
  have hv2 := h2 ⟨.layer m, code⟩ hp
  rw [holdsAt_eq] at hv1 hv2
  unfold viewLayerEnv
  cases hd1 : v1.decl (.layer m) with
  | none => rw [hd1] at hv1; cases hv1
  | some t1 =>
    rw [hd1] at hv1
    cases hd2 : v2.decl (.layer m) with
    | none => rw [hd2] at hv2; cases hv2
    | some t2 =>
      rw [hd2] at hv2
      have e1 : t1 = code := termEq_sound' hv1
      have e2 : t2 = code := termEq_sound' hv2
      rw [e1, e2]

/-- **Candidate Support Reuse Theorem (`candidate_supports_conservative`)**:
Whenever a candidate's `pins` cover `extractReadMembers t` and hold at views `v1` and `v2`,
evaluating `t` under `v1` and `v2` produces the exact same specialized term and evaluation result,
regardless of any mutations to non-supported cells. -/
theorem candidate_supports_conservative {t : Term} {pins : List LeafPin} {v1 v2 : LeafView}
    (hcov : SupportsCoverMembers pins (extractReadMembers t))
    (h1 : ∀ p ∈ pins, holdsAt v1 p = true)
    (h2 : ∀ p ∈ pins, holdsAt v2 p = true) :
    substMemberEnv (viewLayerEnv v1) t = substMemberEnv (viewLayerEnv v2) t ∧
    (∀ fuel, evalWithMemberEnv fuel (viewLayerEnv v1) t = evalWithMemberEnv fuel (viewLayerEnv v2) t) := by
  have hagree := supports_cover_agree_of_holdsAt hcov h1 h2
  have hcons := extractReadMembers_conservative hagree
  exact ⟨hcons.1, hcons.2.1⟩

/-! ## Binding pins into a book (`bindBookPins`), and the judge of a specialized book

A pin `⟨.layer m, v⟩` binds the member `m`: every `self.m` read in a definition's code is replaced by
`v`, syntactically (`substMemberEnvAt`), and the definition's `reads` are recomputed. `v` is inserted
where the read stood, under whatever binders stand there, so it must be closed; and the read it
replaces runs, in the dispatcher, to the entry of `m`, so `v` must meet that entry. Those two
conditions are what `specializedJudgeB` decides, by running the dispatcher (`Obend.Law.run`), and what
`Obend.Leaf.Served` proves sufficient: `B.link ≈b (bindBookPins B pins).link`. A pin that merely holds
at a view is not enough (`Obend.Teeth.Leaf.StaticTeeth`, the counterexample). -/

/-- Extract the member names read via `self` inside a definition `code` (matching `substPinsInCode`). -/
@[expose] def extractReadMembersCode : Term → List String
  | .lam inner => extractReadMembersAt 0 inner
  | other => extractReadMembersAt 0 other

/-- Substitute pinned member values from `pins` for `self.m` reads inside a definition's `code`. -/
@[expose] def substPinsInCode (pins : List LeafPin) : Term → Term
  | .lam inner => .lam (substMemberEnvAt 0 (pinListEnv pins) inner)
  | other => substMemberEnvAt 0 (pinListEnv pins) other

/-- Compute the residual slot indices still read through `self` after binding `pins`. -/
@[expose] def residualSlotReads (slots : List String) (pins : List LeafPin) (d : LeafDef) : List Nat :=
  let pinnedCode := substPinsInCode pins d.code
  let bodyForReads := match d.kind, pinnedCode with
    | .method, .lam b => b
    | .cell, .lam (.lam b) => b
    | _, b => b
  let readDepth := match d.kind with
    | .method => 0
    | .cell => 1
  ((extractReadMembersAt readDepth bodyForReads).filterMap slots.idxOf?).eraseDups

/-- Bind `pins` into a `LeafDef` (prior to running the folder). -/
def bindLeafDef (slots : List String) (pins : List LeafPin) (d : LeafDef) : LeafDef :=
  { d with
    code := substPinsInCode pins d.code
    reads := residualSlotReads slots pins d }

/-- Bind `pins` into a `BookItem`; statics are untouched. -/
def bindBookItem (slots : List String) (pins : List LeafPin) : BookItem → BookItem
  | .slot d => .slot (bindLeafDef slots pins d)
  | .static m v => .static m v

/-- Bind `pins` across all definitions of a `Book`. -/
def bindBookPins (B : Book) (pins : List LeafPin) : Book :=
  { items := B.items.map (bindBookItem B.slots pins) }

/-- Fuel for the judge's runs of the dispatcher: a read of a member is a few β steps and the
member's own value. -/
def servesFuel : Nat := 100000

/-- `t` and `v` meet: both run to one value within `fuel` steps. -/
def meetsB (fuel : Nat) (t v : Term) : Bool :=
  match Obend.Law.run fuel t, Obend.Law.run fuel v with
  | some a, some b => Obend.Law.termEq a b
  | _, _ => false

/-- The dispatcher of `B` serves the pin `p`: its code is closed and meets the read of its member. -/
def Book.servesB (B : Book) (fuel : Nat) (p : LeafPin) : Bool :=
  Obend.Law.closedB p.code && meetsB fuel (.get B.link p.cell.key) p.code

/-- Every definition's code is `λself. …`, as `emit` writes them. -/
def Book.lamCodesB (B : Book) : Bool :=
  B.defs.all fun d => match d.code with | .lam _ => true | _ => false

/-- **The judge of a specialized book**: the book's link and the bound book's link are closed, every
definition is a lambda, and the dispatcher serves every pin. `Obend.Leaf.Served.served_of_judgeB` reads
it back as the hypotheses of `link_bequiv_bindBookPins`. -/
def specializedJudgeB (B : Book) (pins : List LeafPin) : Bool :=
  Obend.Law.closedB B.link && Obend.Law.closedB (bindBookPins B pins).link &&
    B.lamCodesB && pins.all (B.servesB servesFuel)

/-! ## The candidates of the specialization slot -/

/-- The candidates of the specialization slot. -/
inductive Candidate where
  /-- the whole-object book `emit comp`, for the object `name` -/
  | book (name : String) (comp : Composition)
  /-- a per-slot specialized definition `defItem` for `member` of `objectName`, pinned ONLY to its read-support cone -/
  | slotBook (objectName : String) (member : String) (comp : Composition) (defItem : LeafDef)
  /-- the whole-object book folded under `pins` (`specializeBook (emit comp) pins`, `Obend.Leaf.Static`),
  for the object `name`; its judge decides that `emit comp`'s dispatcher serves every pin
  (`specializedJudgeB`), which is what makes the folded book compute the object -/
  | specialized (name : String) (comp : Composition) (pins : List LeafPin)
  /-- the machine: the unflattened term -/
  | machine

/-- The pins a candidate assumed:
- `.book`: its object's composition and each layer it flattened;
- `.slotBook`: only the member's read-support cone (`coneSupports comp (slotReadCone comp member)`);
- `.specialized`: as `.book`; the pins it folded under are judged against the book, not pinned on the world;
- `.machine`: none. -/
@[expose] def Candidate.supports : Candidate → List LeafPin
  | .book name C => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .slotBook _ member C _ => coneSupports C (slotReadCone C member)
  | .specialized name C _ => ⟨.object name, C.code⟩ :: C.layers.map fun L => ⟨.layer L.name, L.code⟩
  | .machine => []

/-- A book or slotBook is admitted for compositions in the scope of `flatten_sound`; a specialized book
when, besides, its dispatcher serves every pin it folded under (`specializedJudgeB`); the machine always. -/
@[expose] def Candidate.judge : Candidate → Bool
  | .book _ C => C.closedB
  | .slotBook _ _ C _ => C.closedB
  | .specialized _ C pins => C.closedB && specializedJudgeB (emit C) pins
  | .machine => true

/-- **The specialization slot.** -/
abbrev specSlot : Slot LeafPin Candidate := ⟨Candidate.supports, Candidate.judge⟩

/-- The order a chooser gives: the book first, the machine as the fallback. -/
abbrev specOrder (name : String) (C : Composition) : List Candidate := [.book name C, .machine]

/-- **The machine is always usable.** -/
theorem machine_usable (v : LeafView) : specSlot.usable (holdsAt v) .machine = true := by
  simp [Slot.usable, Slot.dead, Candidate.supports, Candidate.judge]

/-- **A usable book is the book of the view's composition**: the view's object has the code the book
pinned, so it emits the same book, and (when that object is closed, as an elaborated program's is)
every member the book computes is the member that object computes. -/
theorem book_usable_sound {k : Nat} {name : String} {C C' : Composition}
    (h : specSlot.usable (holdsAt (viewOf k name C')) (.book name C) = true) :
    emit C = emit C' ∧ (C'.closedB = true → ∀ m, .get (emit C).link m ≈b .get C'.object m) := by
  obtain ⟨_, hall⟩ := (usable_iff _ _ _).1 h
  have ho := hall ⟨.object name, C.code⟩ (by simp [Candidate.supports])
  rw [holdsAt_eq] at ho
  simp only [beq_self_eq_true, ite_true] at ho
  have e : emit C = emit C' := emit_congr (termEq_sound' ho).symm
  exact ⟨e, fun hc m => e ▸ book_sound C' hc m⟩

/-- Inhabitedness witness for `book_usable_sound`. -/
theorem book_usable_inhabited :
    let C : Composition :=
      ⟨{ name := "base", metadata := .record [], fields := [("id", .lam (.bound 0))], flat := true }, [], []⟩
    specSlot.usable (holdsAt (viewOf 0 "idObj" C)) (.book "idObj" C) = true := by
  decide +kernel

/-- **Incumbent-first, at the order `[book, machine]`**: a stored book is kept exactly while it is
usable; otherwise the machine is selected. `incumbent_choice`, applied. -/
theorem specialize_choice (v : LeafView) (name : String) (C : Composition) :
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v (specOrder name C)
        (some (.book name C)) =
      if specSlot.usable (holdsAt v) (.book name C) then .ok (.book name C) else .ok .machine := by
  split
  · rename_i hu
    exact (incumbent_choice specSlot v _ _ _).2 (.inl ⟨rfl, hu⟩)
  · rename_i hu
    have hf : specSlot.usable (holdsAt v) (.book name C) = false := by simpa using hu
    refine (incumbent_choice specSlot v _ _ _).2 (.inr ⟨fun c e => by cases e; exact hf, ?_⟩)
    simp [Slot.select, Slot.alternatives, specOrder, hf, machine_usable]

/-- **A moved pin blocks the book by name**: when a support of an admitted book does not hold at a
view, the book's read there is blocked, and the blocked read names exactly the supports that do not
hold, this one among them. `read_blocked_exact`, applied. -/
theorem moved_pin_blocks {v : LeafView} {name : String} {C : Composition} (hj : C.closedB = true)
    {p : LeafPin} (hp : p ∈ (Candidate.book name C).supports) (hd : holdsAt v p = false) :
    ∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d ∧
      ∀ q, q ∈ d ↔ q ∈ (Candidate.book name C).supports ∧ holdsAt v q = false := by
  have hmem : p ∈ specSlot.dead (holdsAt v) (.book name C) := (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hread : ∃ d, specSlot.read (holdsAt v) (some (.book name C)) = .blocked (.book name C) d ∧ p ∈ d := by
    simp only [Slot.read, Candidate.judge, hj, ite_true]
    cases hdd : specSlot.dead (holdsAt v) (.book name C) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  obtain ⟨d, hr, hpd⟩ := hread
  exact ⟨d, hr, hpd, (read_blocked_exact specSlot _ _ _ _ hr).2⟩

/-- **A moved pin blocks a `slotBook` by name**: when a support of an admitted `slotBook` does not
hold at a view, its read is `.blocked` and names the exact stale cone pins. -/
theorem slotBook_moved_pin_blocks {v : LeafView} {name member : String} {C : Composition}
    {defItem : LeafDef} (hj : C.closedB = true)
    {p : LeafPin} (hp : p ∈ (Candidate.slotBook name member C defItem).supports)
    (hd : holdsAt v p = false) :
    ∃ d, specSlot.read (holdsAt v) (some (.slotBook name member C defItem)) =
      .blocked (.slotBook name member C defItem) d ∧ p ∈ d ∧
      ∀ q, q ∈ d ↔ q ∈ (Candidate.slotBook name member C defItem).supports ∧ holdsAt v q = false := by
  have hmem : p ∈ specSlot.dead (holdsAt v) (.slotBook name member C defItem) :=
    (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hread : ∃ d, specSlot.read (holdsAt v) (some (.slotBook name member C defItem)) =
      .blocked (.slotBook name member C defItem) d ∧ p ∈ d := by
    simp only [Slot.read, Candidate.judge, hj, ite_true]
    cases hdd : specSlot.dead (holdsAt v) (.slotBook name member C defItem) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  obtain ⟨d, hr, hpd⟩ := hread
  exact ⟨d, hr, hpd, (read_blocked_exact specSlot _ _ _ _ hr).2⟩

/-- The specialization slot's filler and advance have CONTEXTITY INTEGRITY ∧ TRANSITION. -/
theorem specialize_integrity :
    Integrity (slotFiller : Filler LeafView LeafPin Candidate) (slotAdvance : Advance LeafView LeafPin Candidate) :=
  slotFiller_integrity


end Obend.Leaf
end
