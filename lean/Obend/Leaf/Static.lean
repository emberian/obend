module
/-
# Obend.Leaf.Static — static reduction in context, and the book specializer

What this module is: a bottom-up constant folder on `Core4` terms (`dataPinPass`: β where the
function is a literal λ, field selection on a literal record, destructor and `case` on literal
records and injections, `ifBool`/`ifZero` on literal scalars, primitives on literal operands),
iterated a fixed four times (`dataPinSpecialize`); the same folder applied to every definition of
a `Leaf.Book` after the `self.m` reads that `pins` fix have been substituted (`specializeBook`);
and an encoding of books and pins as `Core4` terms (`encodeBookTerm`, `decodeBookTerm?`) that the
folder commutes with.

What is proved: every pass is a reduction in context (`ahead_dataPinPass : Ahead t (dataPinPass t)`),
so `t ≈b dataPinSpecialize t` (`bequiv_dataPinSpecialize`) and the ground observations agree
(`halts_dataPinSpecialize_iff`); applying a term to a static argument and folding keeps the slot
theorems of `Obend.Leaf.Specialize` (`staticApply_slot_sound`); `specializeBook` is `dataPinSpecialize`
under `bindBookPins` (`specializeBook_eq_mapBookCode_bindBookPins`), each specialized definition is
`≈b` the pinned one (`specializeDefCode_bequiv_and_halts`), and the lookup functions commute
(`lookupBookCode_specializeBook`, `evalBook_specializeBook_eq_evalBook`).

What is not proved, and must not be read into the names: `evalBook`, `evalBookAt`,
`evalBookUnderPinsAt` and `evalResidualBookAt` are *syntactic normal forms under this folder*, not
runs of the demand machine; a theorem of the form `evalResidualBookAt (specializeBook B pins) m x =
evalBookUnderPinsAt B pins m x` says that two applications of the folder agree, nothing more. The
link of a specialized book against the link of the original (`(specializeBook B pins).link ≈b B.link`
when the pins are what the dispatcher serves) is open; the per-definition theorem is the one in hand.

History: this module was `Obend/Leaf/Futamura.lean` until 2026-11-04, and carried "2nd and 3rd
Futamura projections" (`quoteMixTerm`, `quoteBookMixTerm`, `quoteMetaCogenTerm`, `cogenBookInCore`,
`futamura2BookCompiler`, `inCoreBookCompiler`). Those terms were a three-arm arithmetic function and
the `apply` combinator, not a specializer; the folder that did the work was this Lean function,
never a `Core4` term, so nothing was self-applied. They were deleted, not renamed
(`review/EXPERT-compiler-runtime-20261103.md` §2.1); all callers now import this module directly.
-/
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Served
public import Obend.Lower.Proofs.Book
import all Obend.Leaf.UpTo
import all Obend.Leaf.Flatten
import all Obend.Leaf.Emit
import all Obend.Leaf.Specialize
import all Obend.Leaf.Served
public section

namespace Obend.Leaf.Static
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Lower
set_option autoImplicit false

/-! ## 1. The one-step folds: a literal at the head of a redex (`resolveApp`, `resolveGet`, `resolveSplit`, `resolveCase`, `resolveIfBool`, `resolveIfZero`, `resolveBinary`) -/

/-- Statically β-reduce an application when the function is a literal λ-abstraction. -/
@[expose] def resolveApp : Term → Term → Term
  | .lam b, a => instantiate b a
  | f, a => .app f a

/-- Statically resolve a record destructor when the target is a literal record containing `names`. -/
abbrev resolveSplit : Term → List String → Term → Term
  | .record fs, names, f =>
    match splitValues fs names with
    | some vs => applyAll f vs
    | none => .split (.record fs) names f
  | g, names, f => .split g names f

/-- Statically resolve a constructor `case` when the scrutinee is a literal `.inject tag payload`. -/
abbrev resolveCase : Term → List (String × Term) → Term
  | .inject tag payload, arms =>
    match arms.find? (·.1 == tag) with
    | some (_, body) => instantiate body payload
    | none => .case (.inject tag payload) arms
  | sc, arms => .case sc arms

/-- Statically resolve a Boolean conditional when the condition is a literal `.boolean b`. -/
@[expose] def resolveIfBool : Term → Term → Term → Term
  | .boolean true, x, _ => x
  | .boolean false, _, y => y
  | c, x, y => .ifBool c x y

/-- Statically resolve a natural-number conditional when the scrutinee is a literal `.nat n`. -/
abbrev resolveIfZero : Term → Term → Term → Term
  | .nat 0, z, _ => z
  | .nat (n + 1), _, s => instantiate s (.nat n)
  | v, z, s => .ifZero v z s

/-- Statically fold a binary primitive operation when both operands are literals in the domain of `op`. -/
@[expose] def resolveBinary (op : Primitive) (l r : Term) : Term :=
  match primitiveResult op l r with
  | some res => res
  | none => .binary op l r

theorem ahead_resolveApp {f f' a a' : Term} (hf : Ahead f f') (ha : Ahead a a') :
    Ahead (.app f a) (resolveApp f' a') := by
  unfold resolveApp
  split
  · rename_i b'
    obtain ⟨b, sf, hb⟩ := Obend.Equiv.inv_lam_ahead hf
    exact .run (steps_snoc (steps_app a sf) (.beta b a)) (ahead_instantiate hb ha)
  · exact .app hf ha

theorem ahead_resolveSplit {g g' f f' : Term} (names : List String)
    (hg : Ahead g g') (hf : Ahead f f') :
    Ahead (.split g names f) (resolveSplit g' names f') := by
  unfold resolveSplit
  split
  · rename_i fs'
    split
    · rename_i vs' hit
      obtain ⟨fs, sg, n1, r1⟩ := Obend.Equiv.inv_record_ahead hg
      obtain ⟨vs, hv, a⟩ := splitValues_right n1 r1 hf hit
      exact .run (steps_snoc (steps_split names f sg) (.splitRecord fs names f vs hv)) a
    · exact .split names hg hf
  · exact .split names hg hf

theorem ahead_resolveCase {sc sc' : Term} {arms arms' : List (String × Term)}
    (hsc : Ahead sc sc') (n1 : arms.map Prod.fst = arms'.map Prod.fst)
    (r1 : ∀ p ∈ arms.zip arms', Ahead p.1.2 p.2.2) :
    Ahead (.case sc arms) (resolveCase sc' arms') := by
  unfold resolveCase
  split
  · rename_i tag payload'
    split
    · rename_i k body' hit
      have hk : k = tag := by have := List.find?_some hit; simpa using this
      subst hk
      obtain ⟨payload, ssc, hpay⟩ := Obend.Equiv.inv_inject_ahead hsc
      obtain ⟨body, hit0, hbody⟩ := find_right n1 r1 hit
      exact .run (steps_snoc (steps_case arms ssc) (.caseInject k payload arms body hit0))
        (ahead_instantiate hbody hpay)
    · exact .case hsc n1 r1
  · exact .case hsc n1 r1

theorem ahead_resolveIfBool {c c' x x' y y' : Term}
    (hc : Ahead c c') (hx : Ahead x x') (hy : Ahead y y') :
    Ahead (.ifBool c x y) (resolveIfBool c' x' y') := by
  unfold resolveIfBool
  split
  · have sc := Obend.Equiv.inv_literal_ahead (.boolean true) hc
    exact .run (steps_snoc (steps_ifBool x y sc) (.ifTrue x y)) hx
  · have sc := Obend.Equiv.inv_literal_ahead (.boolean false) hc
    exact .run (steps_snoc (steps_ifBool x y sc) (.ifFalse x y)) hy
  · exact .ifBool hc hx hy

theorem ahead_resolveIfZero {v v' z z' s s' : Term}
    (hv : Ahead v v') (hz : Ahead z z') (hs : Ahead s s') :
    Ahead (.ifZero v z s) (resolveIfZero v' z' s') := by
  unfold resolveIfZero
  split
  · have sv := Obend.Equiv.inv_literal_ahead (.nat 0) hv
    exact .run (steps_snoc (steps_ifZero z s sv) (.zero z s)) hz
  · rename_i n
    have sv := Obend.Equiv.inv_literal_ahead (.nat (n + 1)) hv
    exact .run (steps_snoc (steps_ifZero z s sv) (.successor n z s)) (ahead_instantiate hs (.nat n))
  · exact .ifZero hv hz hs

theorem ahead_resolveBinary (op : Primitive) {l l' r r' : Term}
    (hl : Ahead l l') (hr : Ahead r r') :
    Ahead (.binary op l r) (resolveBinary op l' r') := by
  unfold resolveBinary
  split
  · rename_i res hit
    obtain ⟨litL, litR, _⟩ := primitiveResult_literal hit
    have sl := Obend.Equiv.inv_literal_ahead litL hl
    have sr := Obend.Equiv.inv_literal_ahead litR hr
    have step1 := steps_binaryLeft op r sl
    have step2 := steps_binaryRight op litL.value sr
    have step3 := Step.primitive op l' r' res litL.value litR.value hit
    exact .run (steps_snoc (steps_trans step1 step2) step3) (.refl res)
  · exact .binary op hl hr

/-! ## 2. One bottom-up pass, and four of them (`dataPinPass`, `dataPinSpecialize`) -/

/-- One bottom-up pass of static data-pin specialization over a `Core4` `Term`. -/
@[expose] def dataPinPass : Term → Term
  | .hole n σ => .hole n (σ.map dataPinPass)
  | .bound i => .bound i
  | .lam b => .lam (dataPinPass b)
  | .app f a => resolveApp (dataPinPass f) (dataPinPass a)
  | .mix l u => .mix (dataPinPass l) (dataPinPass u)
  | .fix s i => .fix (dataPinPass s) (dataPinPass i)
  | .specification m e => .specification (dataPinPass m) (dataPinPass e)
  | .prototype s g => .prototype (dataPinPass s) (dataPinPass g)
  | .reflect p => .reflect (dataPinPass p)
  | .metadata p => .metadata (dataPinPass p)
  | .project p => .project (dataPinPass p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => resolveBinary op (dataPinPass l) (dataPinPass r)
  | .extend i fs => .extend (dataPinPass i) (fs.map fun f => (f.1, dataPinPass f.2))
  | .record fs => .record (fs.map fun f => (f.1, dataPinPass f.2))
  | .get g p => resolveGet (dataPinPass g) p
  | .ifZero v z s => resolveIfZero (dataPinPass v) (dataPinPass z) (dataPinPass s)
  | .inject l p => .inject l (dataPinPass p)
  | .case sc arms => resolveCase (dataPinPass sc) (arms.map fun a => (a.1, dataPinPass a.2))
  | .ifBool c x y => resolveIfBool (dataPinPass c) (dataPinPass x) (dataPinPass y)
  | .perform p => .perform (dataPinPass p)
  | .done v => .done (dataPinPass v)
  | .split t names f => resolveSplit (dataPinPass t) names (dataPinPass f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)

/-- One pass is a reduction in context: `Ahead t (dataPinPass t)`. -/
theorem ahead_dataPinPass : (t : Term) → Ahead t (dataPinPass t)
  | .hole n σ => by
    simp only [dataPinPass]
    refine .hole n (by simp) ?_
    intro p hp
    rw [List.zip_map_right] at hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hp
    obtain ⟨he, ha⟩ := zip_self σ (a, b) hab
    have hb : a = b := he
    subst hb
    have member : a ∈ σ := ha
    exact ahead_dataPinPass a
  | .bound i => by simp only [dataPinPass]; exact .bound i
  | .lam b => by simp only [dataPinPass]; exact .lam (ahead_dataPinPass b)
  | .app f a => by simp only [dataPinPass]; exact ahead_resolveApp (ahead_dataPinPass f) (ahead_dataPinPass a)
  | .mix l u => by simp only [dataPinPass]; exact .mix (ahead_dataPinPass l) (ahead_dataPinPass u)
  | .fix s i => by simp only [dataPinPass]; exact .fix (ahead_dataPinPass s) (ahead_dataPinPass i)
  | .specification m e => by
    simp only [dataPinPass]; exact .specification (ahead_dataPinPass m) (ahead_dataPinPass e)
  | .prototype s g => by
    simp only [dataPinPass]; exact .prototype (ahead_dataPinPass s) (ahead_dataPinPass g)
  | .reflect p => by simp only [dataPinPass]; exact .reflect (ahead_dataPinPass p)
  | .metadata p => by simp only [dataPinPass]; exact .metadata (ahead_dataPinPass p)
  | .project p => by simp only [dataPinPass]; exact .project (ahead_dataPinPass p)
  | .nat n => by simp only [dataPinPass]; exact .nat n
  | .boolean b => by simp only [dataPinPass]; exact .boolean b
  | .label l => by simp only [dataPinPass]; exact .label l
  | .binary op l r => by
    simp only [dataPinPass]; exact ahead_resolveBinary op (ahead_dataPinPass l) (ahead_dataPinPass r)
  | .extend i fs => by
    simp only [dataPinPass]
    exact .extend (ahead_dataPinPass i) (names_map _ fs).symm
      (zip_map_self_rel dataPinPass fs fun x _ => ahead_dataPinPass x.2)
  | .record fs => by
    simp only [dataPinPass]
    exact .record (names_map _ fs).symm
      (zip_map_self_rel dataPinPass fs fun x _ => ahead_dataPinPass x.2)
  | .get g p => by simp only [dataPinPass]; exact ahead_resolveGet p (ahead_dataPinPass g)
  | .ifZero v z s => by
    simp only [dataPinPass]
    exact ahead_resolveIfZero (ahead_dataPinPass v) (ahead_dataPinPass z) (ahead_dataPinPass s)
  | .inject l p => by simp only [dataPinPass]; exact .inject l (ahead_dataPinPass p)
  | .case sc arms => by
    simp only [dataPinPass]
    exact ahead_resolveCase (ahead_dataPinPass sc) (names_map _ arms).symm
      (zip_map_self_rel dataPinPass arms fun x _ => ahead_dataPinPass x.2)
  | .ifBool c x y => by
    simp only [dataPinPass]
    exact ahead_resolveIfBool (ahead_dataPinPass c) (ahead_dataPinPass x) (ahead_dataPinPass y)
  | .perform p => by simp only [dataPinPass]; exact .perform (ahead_dataPinPass p)
  | .done v => by simp only [dataPinPass]; exact .done (ahead_dataPinPass v)
  | .split t names f => by
    simp only [dataPinPass]
    exact ahead_resolveSplit names (ahead_dataPinPass t) (ahead_dataPinPass f)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem hmem; omega)
    | (have := List.sizeOf_lt_of_mem member; omega)

/-- Iterate `dataPinPass` `k` times. -/
@[expose] def dataPinSteps : Nat → Term → Term
  | 0, t => t
  | k + 1, t => dataPinPass (dataPinSteps k t)

theorem bequiv_dataPinPass (t : Term) : t ≈b dataPinPass t :=
  bequiv_of_ahead (ahead_dataPinPass t)

theorem bequiv_dataPinSteps : ∀ (k : Nat) (t : Term), t ≈b dataPinSteps k t
  | 0, t => BEquiv.refl t
  | k + 1, t =>
    BEquiv.trans (bequiv_dataPinSteps k t) (bequiv_dataPinPass (dataPinSteps k t))

/-- Four passes of `dataPinPass`. Four is a budget, not a fixpoint: a term may still hold folds after it. Every
β-redex whose function is a literal λ is reduced regardless of how often the bound variable occurs, so the result
can duplicate work on the demand machine; nothing here bounds that. -/
@[expose] def dataPinSpecialize (t : Term) : Term :=
  dataPinSteps 4 t

theorem bequiv_dataPinSpecialize (t : Term) : t ≈b dataPinSpecialize t :=
  bequiv_dataPinSteps 4 t

theorem halts_dataPinSpecialize_iff (t : Term) (o : Observation) :
    Halts t o ↔ Halts (dataPinSpecialize t) o :=
  (bequiv_dataPinSpecialize t).sameRuns.halts o

/-- `≈b` applied to the same argument on both sides has the same completed runs. -/
theorem sameRuns_app_of_bequiv {f f' : Term} (hf : f ≈b f') (a : Term) :
    SameRuns (.app f a) (.app f' a) := by
  have h := hf Term.bound (.app (.bound 0) (a.rename Nat.succ))
  simpa only [substitute_bound, instantiate_eq, Term.substitute, single, shift_one_cancel] using h

/-! ## 3. A static environment record folds under the reader that selects from it -/

/-- A pinned environment: constant names and the `Core4` values they hold. -/
abbrev EnvPinTable := List (String × Term)

/-- The environment as a `Core4` record. -/
def pinTableToTerm (env : EnvPinTable) : Term :=
  .record env

/-- The reader `λenv. env.get name`. -/
def envLookupTerm (name : String) : Term :=
  .lam (.get (.bound 0) name)

/-- Applying the reader of `name` to a literal environment record that binds `name` to `val` folds, in
two passes, to `val` folded twice: the β-redex in the first pass, the field selection in the second. -/
theorem envLookup_folds (env : EnvPinTable) (name : String) (val : Term)
    (hfind : env.find? (·.1 == name) = some (name, val)) :
    dataPinSteps 2 (.app (envLookupTerm name) (pinTableToTerm env)) = dataPinPass (dataPinPass val) := by
  have hmap :
      (env.map fun f => (f.1, dataPinPass (dataPinPass f.2))).find? (·.1 == name) =
      some (name, dataPinPass (dataPinPass val)) := by
    simpa [mapFields] using find_mapFields (fun x => dataPinPass (dataPinPass x)) hfind
  simp [dataPinSteps, envLookupTerm, pinTableToTerm, dataPinPass, resolveApp,
    instantiate, resolveGet, List.map_map, Function.comp_def, hmap]

/-! ## 4. A term applied to a static argument, folded, as a candidate of the specialization slot -/

/-- `f` applied to the static argument `a`, folded: the residual of `f` at `a`. -/
abbrev staticApply (f a : Term) : Term :=
  dataPinSpecialize (.app f a)

/-- The residual as a one-layer composition under `memberName` (`Obend.Lower.leanComposition`). -/
abbrev staticApplyComposition (memberName : String) (f a : Term) : Composition :=
  leanComposition memberName (staticApply f a)

/-- The book of that composition. -/
def staticApplyBook (memberName : String) (f a : Term) : Book :=
  emit (staticApplyComposition memberName f a)

/-- The residual book as a candidate of `specSlot`. -/
abbrev staticApplyCandidate (memberName : String) (f a : Term) : Candidate :=
  .book memberName (staticApplyComposition memberName f a)

/-- The residual is `≈b` the application; when its composition is closed the emitted book's member is
too; and under `specSlot` the stored book is kept exactly while its pins hold (`specialize_choice`) and
blocked, naming the moved pin, when one does not (`moved_pin_blocks`). Nothing here is specific to
elaborators or environments: `f` and `a` are any terms. -/
theorem staticApply_slot_sound
    (memberName : String) (f a : Term)
    (hc : (staticApplyComposition memberName f a).closedB = true) :
    (.app f a ≈b staticApply f a) ∧
    (.get (staticApplyBook memberName f a).link memberName ≈b .app f a) ∧
    (∀ v : LeafView,
      (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v
        (specOrder memberName (staticApplyComposition memberName f a))
        (some (staticApplyCandidate memberName f a)) =
      if specSlot.usable (holdsAt v) (staticApplyCandidate memberName f a)
      then .ok (staticApplyCandidate memberName f a)
      else .ok .machine) ∧
    (∀ (v : LeafView) (p : LeafPin),
      p ∈ (staticApplyCandidate memberName f a).supports →
      holdsAt v p = false →
      (∃ d, specSlot.read (holdsAt v) (some (staticApplyCandidate memberName f a)) =
        .blocked (staticApplyCandidate memberName f a) d ∧ p ∈ d) ∧
      (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v
        (specOrder memberName (staticApplyComposition memberName f a))
        (some (staticApplyCandidate memberName f a)) = .ok .machine) := by
  refine ⟨bequiv_dataPinSpecialize (.app f a), ?_, ?_, ?_⟩
  · exact BEquiv.trans
      (book_member memberName (staticApply f a) hc)
      (bequiv_dataPinSpecialize (.app f a)).symm
  · intro v
    exact specialize_choice v memberName (staticApplyComposition memberName f a)
  · intro v p hp hd
    obtain ⟨d, hread, hpd, _⟩ := moved_pin_blocks hc hp hd
    refine ⟨⟨d, hread, hpd⟩, ?_⟩
    have hunusable : specSlot.usable (holdsAt v) (staticApplyCandidate memberName f a) = false := by
      cases hu : specSlot.usable (holdsAt v) (staticApplyCandidate memberName f a) with
      | false => rfl
      | true =>
        obtain ⟨_, hall⟩ := (usable_iff _ _ _).1 hu
        have := hall p hp
        rw [this] at hd
        cases hd
    unfold staticApplyCandidate at hunusable ⊢
    rw [specialize_choice, hunusable]
    rfl

/-- Inhabitedness witness for `staticApply_slot_sound`. -/
theorem staticApplyComposition_inhabited :
    (staticApplyComposition "id" (.lam (.bound 0)) (.nat 7)).closedB = true := by
  decide +kernel

/-! ## 5. Books and pins as `Core4` terms (`encodeBookTerm`, `decodeBookTerm?`) -/

/-- Encode a `DefKind` as a `Core4` `.label`. -/
def encodeDefKind : DefKind → Term
  | .method => .label "method"
  | .cell => .label "cell"

/-- Decode a `DefKind` from a `Core4` `Term`. -/
def decodeDefKind? : Term → Option DefKind
  | .label "method" => some .method
  | .label "cell" => some .cell
  | _ => none

@[simp] theorem decodeDefKind_encodeDefKind (k : DefKind) :
    decodeDefKind? (encodeDefKind k) = some k := by
  cases k <;> rfl

/-- Encode a `List Nat` (such as `LeafDef.reads`) as a `Core4` `Term`. -/
def encodeNatList : List Nat → Term
  | [] => .inject "nil" (.record [])
  | n :: ns => .inject "cons" (.record [("head", .nat n), ("tail", encodeNatList ns)])

/-- Decode a `List Nat` from a `Core4` `Term`. -/
def decodeNatList? : Term → Option (List Nat)
  | .inject "nil" (.record []) => some []
  | .inject "cons" (.record [("head", .nat n), ("tail", rest)]) =>
    (decodeNatList? rest).map (n :: ·)
  | _ => none

@[simp] theorem decodeNatList_encodeNatList : ∀ (ns : List Nat),
    decodeNatList? (encodeNatList ns) = some ns
  | [] => rfl
  | n :: ns => by
    change (decodeNatList? (encodeNatList ns)).map (n :: ·) = some (n :: ns)
    rw [decodeNatList_encodeNatList ns]
    rfl

/-- Look up a named field in a `Core4` `.record` field list (matching `Core4` `Step.field` and `resolveGet`). -/
def lookupRecordField? (fs : List (String × Term)) (name : String) : Option Term :=
  (fs.find? (·.1 == name)).map (·.2)

/-- Encode a `LeafDef` as a `Core4` `.record` `Term`. -/
def encodeLeafDef (d : LeafDef) : Term :=
  .record
    [ ("member", .label d.member)
    , ("slot", .nat d.slot)
    , ("kind", encodeDefKind d.kind)
    , ("code", d.code)
    , ("reads", encodeNatList d.reads) ]

/-- Decode a `LeafDef` from a `Core4` `Term` (order-independent over `.record` fields). -/
def decodeLeafDef? : Term → Option LeafDef
  | .record fs => do
    let m ← match lookupRecordField? fs "member" with
      | some (.label m) => some m
      | _ => none
    let s ← match lookupRecordField? fs "slot" with
      | some (.nat s) => some s
      | _ => none
    let kt ← lookupRecordField? fs "kind"
    let k ← decodeDefKind? kt
    let c ← lookupRecordField? fs "code"
    let rt ← lookupRecordField? fs "reads"
    let r ← decodeNatList? rt
    pure { member := m, slot := s, kind := k, code := c, reads := r }
  | _ => none

@[simp] theorem decodeLeafDef_encodeLeafDef (d : LeafDef) :
    decodeLeafDef? (encodeLeafDef d) = some d := by
  cases d with
  | mk m s k c r =>
    change (do
      let k' ← decodeDefKind? (encodeDefKind k)
      let r' ← decodeNatList? (encodeNatList r)
      pure (LeafDef.mk m s k' c r')) =
      some (LeafDef.mk m s k c r)
    rw [decodeDefKind_encodeDefKind, decodeNatList_encodeNatList]
    rfl

/-- Encode a `BookItem` as a `Core4` `.inject` `Term`. -/
def encodeBookItem : BookItem → Term
  | .slot d => .inject "slot" (encodeLeafDef d)
  | .static m v => .inject "static" (.record [("member", .label m), ("value", v)])

/-- Decode a `BookItem` from a `Core4` `Term` (order-independent over `.record` fields). -/
def decodeBookItem? : Term → Option BookItem
  | .inject "slot" dt => (decodeLeafDef? dt).map .slot
  | .inject "static" (.record fs) => do
    let m ← match lookupRecordField? fs "member" with
      | some (.label m) => some m
      | _ => none
    let v ← lookupRecordField? fs "value"
    pure (.static m v)
  | _ => none

@[simp] theorem decodeBookItem_encodeBookItem (item : BookItem) :
    decodeBookItem? (encodeBookItem item) = some item := by
  cases item with
  | slot d =>
    change (decodeLeafDef? (encodeLeafDef d)).map BookItem.slot = some (.slot d)
    rw [decodeLeafDef_encodeLeafDef]
    rfl
  | static m v => rfl

/-- Encode a list of `BookItem`s as a `Core4` `Term`. -/
def encodeBookItems : List BookItem → Term
  | [] => .inject "nil" (.record [])
  | item :: rest =>
    .inject "cons" (.record [("head", encodeBookItem item), ("tail", encodeBookItems rest)])

/-- Decode a list of `BookItem`s from a `Core4` `Term`. -/
def decodeBookItems? : Term → Option (List BookItem)
  | .inject "nil" (.record []) => some []
  | .inject "cons" (.record [("head", h), ("tail", t)]) => do
    let item ← decodeBookItem? h
    let rest ← decodeBookItems? t
    pure (item :: rest)
  | _ => none

@[simp] theorem decodeBookItems_encodeBookItems : ∀ (items : List BookItem),
    decodeBookItems? (encodeBookItems items) = some items
  | [] => rfl
  | item :: rest => by
    change (do
      let item' ← decodeBookItem? (encodeBookItem item)
      let rest' ← decodeBookItems? (encodeBookItems rest)
      pure (item' :: rest')) = some (item :: rest)
    rw [decodeBookItem_encodeBookItem, decodeBookItems_encodeBookItems rest]
    rfl

/-- **Encode a `Leaf.Book` as a `Core4` `Term` (`encodeBookTerm`).** -/
def encodeBookTerm (B : Book) : Term :=
  .record [("items", encodeBookItems B.items)]

/-- **Decode a `Leaf.Book` from a `Core4` `Term` (`decodeBookTerm?`, order-independent over `.record` fields).** -/
def decodeBookTerm? : Term → Option Book
  | .record fs => do
    let itemsTerm ← lookupRecordField? fs "items"
    let items ← decodeBookItems? itemsTerm
    pure (Book.mk items)
  | _ => none

/-- **Roundtrip Theorem (`decodeBookTerm_encodeBookTerm`)**:
Encoding any `Book` into `Core4.Term` and decoding it recovers `some b` exactly. -/
@[simp] theorem decodeBookTerm_encodeBookTerm (b : Book) :
    decodeBookTerm? (encodeBookTerm b) = some b := by
  cases b with
  | mk items =>
    change (do
      let items' ← decodeBookItems? (encodeBookItems items)
      pure (Book.mk items')) = some (Book.mk items)
    rw [decodeBookItems_encodeBookItems]
    rfl

/-- Encode a `LeafCell` as a `Core4` `Term`. -/
def encodeLeafCell : LeafCell → Term
  | .layer k => .inject "layer" (.label k)
  | .object n => .inject "object" (.label n)

/-- Decode a `LeafCell` from a `Core4` `Term`. -/
def decodeLeafCell? : Term → Option LeafCell
  | .inject "layer" (.label k) => some (.layer k)
  | .inject "object" (.label n) => some (.object n)
  | _ => none

@[simp] theorem decodeLeafCell_encodeLeafCell (c : LeafCell) :
    decodeLeafCell? (encodeLeafCell c) = some c := by
  cases c <;> rfl

/-- Encode a `LeafPin` as a `Core4` `Term`. -/
def encodeLeafPin (p : LeafPin) : Term :=
  .record [("cell", encodeLeafCell p.cell), ("code", p.code)]

/-- Decode a `LeafPin` from a `Core4` `Term` (order-independent over `.record` fields). -/
def decodeLeafPin? : Term → Option LeafPin
  | .record fs => do
    let ct ← lookupRecordField? fs "cell"
    let c ← decodeLeafCell? ct
    let code ← lookupRecordField? fs "code"
    pure ⟨c, code⟩
  | _ => none

@[simp] theorem decodeLeafPin_encodeLeafPin (p : LeafPin) :
    decodeLeafPin? (encodeLeafPin p) = some p := by
  cases p with
  | mk c code =>
    change (do
      let c' ← decodeLeafCell? (encodeLeafCell c)
      pure (LeafPin.mk c' code)) = some (LeafPin.mk c code)
    rw [decodeLeafCell_encodeLeafCell]
    rfl

/-- Encode a `List LeafPin` as a `Core4` `.record` mapping each pin's cell key to its pinned code. -/
def encodePinsRecord (pins : List LeafPin) : Term :=
  .record (pins.map fun p => (p.cell.key, p.code))

/-! ## 6. The folder commutes with the encoding -/

/-- Apply a code transformation `f` to the `code` / `value` payload of a `BookItem`. -/
def mapBookItemCode (f : Term → Term) : BookItem → BookItem
  | .slot d => .slot { d with code := f d.code }
  | .static m v => .static m (f v)

/-- Apply a code transformation `f` to every item in a `Book`. -/
def mapBookCode (f : Term → Term) (B : Book) : Book :=
  { items := B.items.map (mapBookItemCode f) }

@[simp] theorem mapBookItemCode_mapBookItemCode (f g : Term → Term) (item : BookItem) :
    mapBookItemCode g (mapBookItemCode f item) = mapBookItemCode (fun t => g (f t)) item := by
  cases item <;> rfl

@[simp] theorem mapBookCode_mapBookCode (f g : Term → Term) (B : Book) :
    mapBookCode g (mapBookCode f B) = mapBookCode (fun t => g (f t)) B := by
  cases B
  simp [mapBookCode, List.map_map, Function.comp_def]

@[simp] theorem mapBookItemCode_id (item : BookItem) :
    mapBookItemCode (fun t => t) item = item := by
  cases item <;> rfl

@[simp] theorem mapBookCode_id (B : Book) :
    mapBookCode (fun t => t) B = B := by
  rcases B with ⟨items⟩
  simp only [mapBookCode, Book.mk.injEq]
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp [mapBookItemCode_id, ih]

@[simp] theorem dataPinPass_encodeDefKind (k : DefKind) :
    dataPinPass (encodeDefKind k) = encodeDefKind k := by
  cases k <;> simp [encodeDefKind, dataPinPass]

@[simp] theorem dataPinPass_encodeNatList : ∀ (ns : List Nat),
    dataPinPass (encodeNatList ns) = encodeNatList ns
  | [] => by simp [encodeNatList, dataPinPass]
  | n :: ns => by simp [encodeNatList, dataPinPass, dataPinPass_encodeNatList ns]

@[simp] theorem dataPinPass_encodeLeafDef (d : LeafDef) :
    dataPinPass (encodeLeafDef d) = encodeLeafDef { d with code := dataPinPass d.code } := by
  cases d
  simp [encodeLeafDef, dataPinPass]

@[simp] theorem dataPinPass_encodeBookItem (item : BookItem) :
    dataPinPass (encodeBookItem item) = encodeBookItem (mapBookItemCode dataPinPass item) := by
  cases item <;> simp [encodeBookItem, mapBookItemCode, dataPinPass]

@[simp] theorem dataPinPass_encodeBookItems : ∀ (items : List BookItem),
    dataPinPass (encodeBookItems items) = encodeBookItems (items.map (mapBookItemCode dataPinPass))
  | [] => by simp [encodeBookItems, dataPinPass]
  | item :: rest => by
    simp [encodeBookItems, dataPinPass, dataPinPass_encodeBookItem, dataPinPass_encodeBookItems rest]

/-- **`dataPinPass` commutes with `encodeBookTerm`**: running `dataPinPass` on an encoded `Book`
term literally runs `dataPinPass` on every definition body inside the `Book`. -/
@[simp] theorem dataPinPass_encodeBookTerm (B : Book) :
    dataPinPass (encodeBookTerm B) = encodeBookTerm (mapBookCode dataPinPass B) := by
  cases B
  simp [encodeBookTerm, mapBookCode, dataPinPass]

@[simp] theorem dataPinSteps_encodeBookTerm : ∀ (k : Nat) (B : Book),
    dataPinSteps k (encodeBookTerm B) = encodeBookTerm (mapBookCode (dataPinSteps k) B)
  | 0, B => by
    simp [dataPinSteps]
  | k + 1, B => by
    simp [dataPinSteps, dataPinSteps_encodeBookTerm k B]

/-- **`dataPinSpecialize` commutes with `encodeBookTerm`**. -/
@[simp] theorem dataPinSpecialize_encodeBookTerm (B : Book) :
    dataPinSpecialize (encodeBookTerm B) = encodeBookTerm (mapBookCode dataPinSpecialize B) :=
  dataPinSteps_encodeBookTerm 4 B

/-! ## 7. The book specializer (`specializeBook`): bind the pinned `self.m` reads (`bindBookPins`,
`Obend.Leaf.Specialize`), then fold every definition -/

/-- A definition's `code` under `pins`: the pinned `self.m` reads substituted, then the four passes. -/
abbrev specializeDefCode (pins : List LeafPin) (code : Term) : Term :=
  dataPinSpecialize (substPinsInCode pins code)

/-- Specialize a `LeafDef` against `pins`. -/
abbrev specializeLeafDef (slots : List String) (pins : List LeafPin) (d : LeafDef) : LeafDef :=
  { d with
    code := specializeDefCode pins d.code
    reads := residualSlotReads slots pins d }

/-- Specialize a `BookItem` against `pins`. -/
abbrev specializeBookItem (slots : List String) (pins : List LeafPin) : BookItem → BookItem
  | .slot d => .slot (specializeLeafDef slots pins d)
  | .static m v => .static m (dataPinSpecialize v)

/-- **The book specializer**: every definition's pinned `self.m` reads substituted and folded, its
`reads` recomputed; every static folded. With `pins = []` this is the folder on each definition. -/
@[expose] def specializeBook (B : Book) (pins : List LeafPin) : Book :=
  { items := B.items.map (specializeBookItem B.slots pins) }

theorem specializeBook_eq_mapBookCode_bindBookPins (B : Book) (pins : List LeafPin) :
    specializeBook B pins = mapBookCode dataPinSpecialize (bindBookPins B pins) := by
  unfold specializeBook bindBookPins mapBookCode
  simp only [List.map_map, Function.comp_def, Book.mk.injEq]
  apply List.map_congr_left
  intro item _
  cases item <;> rfl

/-! ## 8. Lookup under pins: syntactic normal forms, and how `specializeBook` commutes with them -/

/-- Extract a canonical pin entry `(member, value)` from a `BookItem` when the item is a static
member or a self-independent cell/method. -/
abbrev itemPinEntry : BookItem → Option (String × Term)
  | .static m v => some (m, v)
  | .slot d =>
    match d.kind, d.code with
    | .cell, .lam (.lam v) =>
      if (extractReadMembersAt 1 v).isEmpty then some (d.member, v) else none
    | .method, .lam v =>
      if (extractReadMembersAt 0 v).isEmpty then some (d.member, v) else none
    | _, _ => none

/-- The canonical `LeafPin` list of a `Book`'s self-independent cells, methods, and statics. -/
@[expose] def bookCanonicalPins (B : Book) : List LeafPin :=
  (B.items.filterMap itemPinEntry).map fun (m, v) => ⟨.layer m, v⟩

/-- Look up the raw code of member `m` in `B`. -/
@[expose] def lookupBookCode (B : Book) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d => some d.code
  | none => (B.statics.find? (·.1 == m)).map (·.2)

/-- The code of member `m` of `B` with the `self.m'` reads that `pins` fix substituted and folded. A
syntactic normal form under `dataPinSpecialize`, not a run. -/
def evalBookUnderPins (B : Book) (pins : List LeafPin) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d => some (specializeDefCode pins d.code)
  | none => (B.statics.find? (·.1 == m)).map (fun (_, v) => dataPinSpecialize v)

/-- The code of member `m` of `B`, with its `self` reads resolved against `bookCanonicalPins B` and
folded when it has any (`d.reads` non-empty), as it stands otherwise. A syntactic normal form, not a run. -/
@[expose] def evalBook (B : Book) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d =>
    if d.reads.isEmpty then
      some d.code
    else
      some (specializeDefCode (bookCanonicalPins B) d.code)
  | none =>
    (B.statics.find? (·.1 == m)).map (fun (_, v) => dataPinSpecialize v)

theorem substPinsInCode_congr_of_agree {pins1 pins2 : List LeafPin} (code : Term)
    (h : AgreeOnMembers (extractReadMembersCode code) (pinListEnv pins1) (pinListEnv pins2)) :
    substPinsInCode pins1 code = substPinsInCode pins2 code := by
  cases code <;> simp only [extractReadMembersCode, substPinsInCode] at h ⊢
  all_goals first
    | exact congrArg Term.lam (extractReadMembersAt_conservative 0 _ h)
    | exact extractReadMembersAt_conservative 0 _ h

theorem specializeDefCode_congr_of_agree {pins1 pins2 : List LeafPin} (code : Term)
    (h : AgreeOnMembers (extractReadMembersCode code) (pinListEnv pins1) (pinListEnv pins2)) :
    specializeDefCode pins1 code = specializeDefCode pins2 code := by
  simp only [specializeDefCode, substPinsInCode_congr_of_agree code h]

/-- `evalBook B m` applied to `self := {}` and `x`, folded. Syntactic; the machine is not run. -/
@[expose] def evalBookAt (B : Book) (m : String) (x : Term) : Option Term :=
  (evalBook B m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- `evalBookUnderPins B pins m` applied to `self := {}` and `x`, folded. Syntactic. -/
def evalBookUnderPinsAt (B : Book) (pins : List LeafPin) (m : String) (x : Term) : Option Term :=
  (evalBookUnderPins B pins m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- The code of `m` in `B_res` applied to `self := {}` and `x`, folded. Syntactic. -/
abbrev evalResidualBookAt (B_res : Book) (m : String) (x : Term) : Option Term :=
  (lookupBookCode B_res m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- The empty base `LeafView` with no declared layer cells. -/
@[simp] theorem substMemberEnvAt_empty : (d : Nat) → (t : Term) →
    substMemberEnvAt d (fun _ => none) t = t
  | d, .hole n σ => by
    simp only [substMemberEnvAt, Term.hole.injEq, true_and]
    conv => rhs; rw [← List.map_id σ]
    apply List.map_congr_left
    intro x hx
    exact substMemberEnvAt_empty d x
  | _, .bound _ => by simp [substMemberEnvAt]
  | _, .nat _ => by simp [substMemberEnvAt]
  | _, .boolean _ => by simp [substMemberEnvAt]
  | _, .label _ => by simp [substMemberEnvAt]
  | d, .lam b => by simp [substMemberEnvAt, substMemberEnvAt_empty (d + 1) b]
  | d, .app f a => by simp [substMemberEnvAt, substMemberEnvAt_empty d f, substMemberEnvAt_empty d a]
  | d, .mix l u => by simp [substMemberEnvAt, substMemberEnvAt_empty d l, substMemberEnvAt_empty d u]
  | d, .fix s i => by simp [substMemberEnvAt, substMemberEnvAt_empty d s, substMemberEnvAt_empty d i]
  | d, .specification m e => by simp [substMemberEnvAt, substMemberEnvAt_empty d m, substMemberEnvAt_empty d e]
  | d, .prototype s g => by simp [substMemberEnvAt, substMemberEnvAt_empty d s, substMemberEnvAt_empty d g]
  | d, .reflect p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .metadata p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .project p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .inject _ p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .perform p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .done p => by simp [substMemberEnvAt, substMemberEnvAt_empty d p]
  | d, .binary _ l r => by simp [substMemberEnvAt, substMemberEnvAt_empty d l, substMemberEnvAt_empty d r]
  | d, .extend i fs => by
    simp only [substMemberEnvAt, substMemberEnvAt_empty d i, Term.extend.injEq, true_and]
    conv => rhs; rw [← List.map_id fs]
    apply List.map_congr_left
    intro (k, v) _
    simp [substMemberEnvAt_empty d v]
  | d, .record fs => by
    simp only [substMemberEnvAt, Term.record.injEq]
    conv => rhs; rw [← List.map_id fs]
    apply List.map_congr_left
    intro (k, v) _
    simp [substMemberEnvAt_empty d v]
  | d, .get g m => by
    simp only [substMemberEnvAt, substMemberEnvAt_empty d g]
    cases g <;> simp [resolveMemberGet]
  | d, .ifZero v z s => by
    simp [substMemberEnvAt, substMemberEnvAt_empty d v, substMemberEnvAt_empty d z, substMemberEnvAt_empty (d + 1) s]
  | d, .case sc arms => by
    simp only [substMemberEnvAt, substMemberEnvAt_empty d sc, Term.case.injEq, true_and]
    conv => rhs; rw [← List.map_id arms]
    apply List.map_congr_left
    intro (k, v) _
    simp [substMemberEnvAt_empty (d + 1) v]
  | d, .ifBool c x y => by
    simp [substMemberEnvAt, substMemberEnvAt_empty d c, substMemberEnvAt_empty d x, substMemberEnvAt_empty d y]
  | d, .split t _ f => by
    simp [substMemberEnvAt, substMemberEnvAt_empty d t, substMemberEnvAt_empty d f]
termination_by _ t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp at this; omega)

@[simp] theorem pinListEnv_nil : pinListEnv [] = (fun _ => none) := rfl

@[simp] theorem substPinsInCode_nil (t : Term) : substPinsInCode [] t = t := by
  cases t <;> simp [substPinsInCode]

theorem filterMap_def?_specializeBookItem (slots : List String) (pins : List LeafPin) :
    ∀ (items : List BookItem),
      (items.map (specializeBookItem slots pins)).filterMap BookItem.def? =
        (items.filterMap BookItem.def?).map (specializeLeafDef slots pins)
  | [] => rfl
  | .slot d :: rest => by
    simp [specializeBookItem, BookItem.def?,
      filterMap_def?_specializeBookItem slots pins rest]
  | .static m v :: rest => by
    simp [List.filterMap_cons, specializeBookItem, BookItem.def?,
      filterMap_def?_specializeBookItem slots pins rest]

theorem filterMap_static?_specializeBookItem (slots : List String) (pins : List LeafPin) :
    ∀ (items : List BookItem),
      (items.map (specializeBookItem slots pins)).filterMap BookItem.static? =
        (items.filterMap BookItem.static?).map (fun (m, v) => (m, dataPinSpecialize v))
  | [] => rfl
  | .slot d :: rest => by
    simp [List.filterMap_cons, specializeBookItem, BookItem.static?,
      filterMap_static?_specializeBookItem slots pins rest]
  | .static m v :: rest => by
    simp [specializeBookItem, BookItem.static?,
      filterMap_static?_specializeBookItem slots pins rest]

theorem defs_specializeBook (B : Book) (pins : List LeafPin) :
    (specializeBook B pins).defs = B.defs.map (specializeLeafDef B.slots pins) :=
  filterMap_def?_specializeBookItem B.slots pins B.items

theorem statics_specializeBook (B : Book) (pins : List LeafPin) :
    (specializeBook B pins).statics = B.statics.map (fun (m, v) => (m, dataPinSpecialize v)) :=
  filterMap_static?_specializeBookItem B.slots pins B.items

theorem find?_defs_specializeBook (B : Book) (pins : List LeafPin) (m : String) :
    ((specializeBook B pins).defs).find? (·.member == m) =
      (B.defs.find? (·.member == m)).map (specializeLeafDef B.slots pins) := by
  rw [defs_specializeBook]
  induction B.defs with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.find?_cons]
    have hmem : (specializeLeafDef B.slots pins d).member = d.member := rfl
    rw [hmem]
    cases hm : (d.member == m)
    · exact ih
    · rfl

theorem find?_statics_specializeBook (B : Book) (pins : List LeafPin) (m : String) :
    ((specializeBook B pins).statics).find? (·.1 == m) =
      (B.statics.find? (·.1 == m)).map (fun (k, v) => (k, dataPinSpecialize v)) := by
  rw [statics_specializeBook]
  induction B.statics with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.map_cons, List.find?_cons]
    cases hm : (k == m)
    · exact ih
    · rfl

/-- Looking up `m` in `specializeBook B pins` is `evalBookUnderPins B pins m`: both are the same
substitution followed by the same folder. -/
theorem lookupBookCode_specializeBook (B : Book) (pins : List LeafPin) (m : String) :
    lookupBookCode (specializeBook B pins) m = evalBookUnderPins B pins m := by
  unfold lookupBookCode evalBookUnderPins
  rw [find?_defs_specializeBook, find?_statics_specializeBook]
  cases B.defs.find? (·.member == m) with
  | some d => rfl
  | none =>
    cases B.statics.find? (·.1 == m) <;> rfl

/-- The same, applied to `{}` and `x` and folded once more on each side. -/
theorem evalResidualBookAt_specializeBook (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    evalResidualBookAt (specializeBook B pins) m x = evalBookUnderPinsAt B pins m x := by
  unfold evalResidualBookAt evalBookUnderPinsAt
  rw [lookupBookCode_specializeBook]

/-- Predicate stating that `pins` is a sound, complete pin assignment for member `m` of `Book` `B`:
1. If `m` is a slot definition `d`, `pins` covers all slot reads of `d` (`residualSlotReads = []`),
   agrees with `bookCanonicalPins B` on `extractReadMembersCode d.code`, and if `d` already had
   no `self` reads (`d.reads.isEmpty = true`), `d.code` is already normalized under `specializeDefCode pins`.
2. If `m` is a static entry `(m, v)`, `dataPinSpecialize v` is a fixed point of `dataPinSpecialize`. -/
abbrev HoldsForBookMember (B : Book) (pins : List LeafPin) (m : String) : Prop :=
  (∀ d : LeafDef, B.defs.find? (·.member == m) = some d →
    (residualSlotReads B.slots pins d).isEmpty = true ∧
    AgreeOnMembers (extractReadMembersCode d.code) (pinListEnv pins) (pinListEnv (bookCanonicalPins B)) ∧
    (d.reads.isEmpty = true → specializeDefCode pins d.code = d.code)) ∧
  (B.defs.find? (·.member == m) = none →
    ∀ kv : String × Term, B.statics.find? (·.1 == m) = some kv →
      dataPinSpecialize (dataPinSpecialize kv.2) = dataPinSpecialize kv.2)

/-- When `pins` covers and agrees with the book's own canonical pins on what `m` reads
(`HoldsForBookMember`), `evalBook` of the specialized book at `m` is `evalBook` of the original. -/
theorem evalBook_specializeBook_eq_evalBook (B : Book) (pins : List LeafPin) (m : String)
    (h : HoldsForBookMember B pins m) :
    evalBook (specializeBook B pins) m = evalBook B m := by
  unfold evalBook
  rw [find?_defs_specializeBook, find?_statics_specializeBook]
  cases hd : B.defs.find? (·.member == m) with
  | some d =>
    obtain ⟨hres, hagree, hempty⟩ := h.1 d hd
    simp only [Option.map_some, specializeLeafDef, hres, ite_true]
    cases hr : d.reads.isEmpty with
    | true =>
      simp only [ite_true, Option.some.injEq]
      exact hempty hr
    | false =>
      simp only [Bool.false_eq_true, ite_false, Option.some.injEq]
      exact specializeDefCode_congr_of_agree d.code hagree
  | none =>
    simp only [Option.map_none]
    cases hs : B.statics.find? (·.1 == m) with
    | none => rfl
    | some kv =>
      rcases kv with ⟨k, v⟩
      simp only [Option.map_some, Option.some.injEq]
      exact h.2 hd (k, v) hs

/-- For every definition `code` and pin assignment `pins`, `specializeDefCode pins code` is
behaviorally equivalent (`≈b`) to `substPinsInCode pins code`, and preserves `SameRuns`, `Halts`,
and `Evaluates` under application to any `self` argument and runtime argument `x`. -/
theorem specializeDefCode_bequiv_and_halts (pins : List LeafPin) (code selfArg x : Term) :
    (substPinsInCode pins code ≈b specializeDefCode pins code) ∧
    (∀ o : Observation,
      Halts (.app (.app (substPinsInCode pins code) selfArg) x) o ↔
      Halts (.app (.app (specializeDefCode pins code) selfArg) x) o) ∧
    (∀ n : Nat,
      Evaluates (.app (.app (substPinsInCode pins code) selfArg) x) (.nat n) ↔
      Evaluates (.app (.app (specializeDefCode pins code) selfArg) x) (.nat n)) := by
  have hbeq : substPinsInCode pins code ≈b specializeDefCode pins code :=
    bequiv_dataPinSpecialize (substPinsInCode pins code)
  have hctx : SameRuns
      (.app (.app (substPinsInCode pins code) selfArg) x)
      (.app (.app (specializeDefCode pins code) selfArg) x) := by
    have h := hbeq Term.bound (.app (.app (.bound 0) (selfArg.rename Nat.succ)) (x.rename Nat.succ))
    simpa only [substitute_bound, instantiate_eq, Term.substitute, single, shift_one_cancel] using h
  refine ⟨hbeq, fun o => hctx.halts o, fun n => ?_⟩
  constructor
  · intro hev
    have hhalts : Halts (.app (.app (substPinsInCode pins code) selfArg) x) (.natural n) :=
      ⟨.nat n, hev, .natural n⟩
    obtain ⟨v, hev', hobs⟩ := (hctx.halts (.natural n)).1 hhalts
    cases hobs
    exact hev'
  · intro hev'
    have hhalts : Halts (.app (.app (specializeDefCode pins code) selfArg) x) (.natural n) :=
      ⟨.nat n, hev', .natural n⟩
    obtain ⟨v, hev, hobs⟩ := (hctx.halts (.natural n)).2 hhalts
    cases hobs
    exact hev

/-! ## 9. Boolean equality on optional terms, for `decide`d fixtures -/

/-- Boolean equality on `Option Term` via `Obend.Law.termEq`. -/
@[expose] def optTermEq : Option Term → Option Term → Bool
  | some a, some b => Obend.Law.termEq a b
  | none, none => true
  | _, _ => false

theorem optTermEq_sound {x y : Option Term} (h : optTermEq x y = true) : x = y := by
  cases x <;> cases y <;> simp [optTermEq] at h ⊢
  exact Obend.Law.termEq_sound h

/-- Inhabitedness witness for `optTermEq_sound`. -/
theorem optTermEq_inhabited : optTermEq (some (.nat 42)) (some (.nat 42)) = true := by
  decide +kernel


/-! ## 10. Folding a whole book, and what it does to the link

`foldBook B` folds every definition and static of `B` with `dataPinSpecialize` and keeps the
dispatcher. This is the one specialization step that is proved at the level the machine sees:
`B.link ≈b (foldBook B).link`, because one pass is a reduction in context at every entry of the
dispatcher's record (`link_ahead_mapBookCode`), and four passes compose. With `book_sound`, every
member of the folded book of a closed composition is `≈b` the member of the object
(`foldBook_member_sound`). `reads` are kept as they were: folding can only remove `self` reads, so
the recorded reads over-approximate. `specializeBook B pins` with pins that the dispatcher does not
serve is a different thing and has no link-level theorem. -/

/-- The names and entries of the dispatcher's record, item by item, before and after mapping a
code transformation that is a reduction in context. -/
theorem entries_ahead (f : Term → Term) (hf : ∀ t, Ahead t (f t)) :
    ∀ items : List BookItem,
      (items.map BookItem.entry).map Prod.fst =
        ((items.map (mapBookItemCode f)).map BookItem.entry).map Prod.fst ∧
      ∀ p ∈ (items.map BookItem.entry).zip ((items.map (mapBookItemCode f)).map BookItem.entry),
        Ahead p.1.2 p.2.2
  | [] => ⟨rfl, by simp⟩
  | item :: rest => by
    obtain ⟨n, r⟩ := entries_ahead f hf rest
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
    refine ⟨?_, ?_⟩
    · cases item with
      | slot d => simp only [BookItem.entry, mapBookItemCode, n]
      | static m v => simp only [BookItem.entry, mapBookItemCode, n]
    · rintro p (rfl | hp)
      · cases item with
        | slot d =>
          cases hk : d.kind
          · simp only [BookItem.entry, mapBookItemCode, LeafDef.call, hk]
            exact .app (ahead_rename (hf d.code) _) (.bound 1)
          · simp only [BookItem.entry, mapBookItemCode, LeafDef.call, hk]
            exact .app (.app (ahead_rename (hf d.code) _) (.bound 1)) (.refl _)
        | static m v =>
          simp only [BookItem.entry, mapBookItemCode]
          exact ahead_rename (hf v) _
      · exact r p hp

/-- Mapping a reduction in context over every code of a book is a reduction in context of its link. -/
theorem link_ahead_mapBookCode (f : Term → Term) (hf : ∀ t, Ahead t (f t)) (B : Book) :
    Ahead B.link (mapBookCode f B).link := by
  obtain ⟨n, r⟩ := entries_ahead f hf B.items
  exact .fix (.lam (.lam (.record n r))) (.refl _)

/-- One pass of the folder over every code of the book. -/
def foldBookOnce (B : Book) : Book := mapBookCode dataPinPass B

theorem link_bequiv_foldBookOnce (B : Book) : B.link ≈b (foldBookOnce B).link :=
  bequiv_of_ahead (link_ahead_mapBookCode dataPinPass ahead_dataPinPass B)

/-- **The folded book**: every definition and static folded by `dataPinSpecialize`; the dispatcher
and the `reads` as they were. -/
def foldBook (B : Book) : Book := mapBookCode dataPinSpecialize B

/-- Four passes, written out. -/
theorem dataPinSpecialize_eq_four :
    dataPinSpecialize = fun t => dataPinPass (dataPinPass (dataPinPass (dataPinPass t))) := by
  funext t; rfl

theorem foldBook_eq_four (B : Book) :
    foldBook B = foldBookOnce (foldBookOnce (foldBookOnce (foldBookOnce B))) := by
  simp only [foldBook, foldBookOnce, mapBookCode_mapBookCode, dataPinSpecialize_eq_four]

/-- **The folded book's link is `≈b` the book's link.** -/
theorem link_bequiv_foldBook (B : Book) : B.link ≈b (foldBook B).link := by
  rw [foldBook_eq_four]
  exact ((link_bequiv_foldBookOnce B).trans (link_bequiv_foldBookOnce _)).trans
    ((link_bequiv_foldBookOnce _).trans (link_bequiv_foldBookOnce _))

/-- Every member read from the folded book is `≈b` the member read from the book. -/
theorem foldBook_member_bequiv (B : Book) (m : String) :
    .get (foldBook B).link m ≈b .get B.link m := by
  have step : ∀ B' : Book, .get B'.link m ≈b .get (foldBookOnce B').link m := fun B' =>
    bequiv_of_ahead (.get m (link_ahead_mapBookCode dataPinPass ahead_dataPinPass B'))
  rw [foldBook_eq_four]
  exact (((step B).trans (step _)).trans ((step _).trans (step _))).symm

/-- **The folded book of a closed composition computes what the object computes**: `book_sound`
through `foldBook_member_bequiv`. -/
theorem foldBook_member_sound (C : Composition) (hc : C.closedB = true) (m : String) :
    .get (foldBook (emit C)).link m ≈b .get C.object m :=
  (foldBook_member_bequiv (emit C) m).trans (book_sound C hc m)

/-- `foldBook` keeps the slot table: it changes codes, never members or their order. -/
theorem filterMap_def?_mapBookItemCode (f : Term → Term) :
    ∀ items : List BookItem,
      (items.map (mapBookItemCode f)).filterMap BookItem.def? =
        (items.filterMap BookItem.def?).map (fun d => { d with code := f d.code })
  | [] => rfl
  | .slot d :: rest => by
    simp [mapBookItemCode, BookItem.def?, filterMap_def?_mapBookItemCode f rest]
  | .static m v :: rest => by
    simp [List.filterMap_cons, mapBookItemCode, BookItem.def?, filterMap_def?_mapBookItemCode f rest]

theorem defs_mapBookCode (f : Term → Term) (B : Book) :
    (mapBookCode f B).defs = B.defs.map (fun d => { d with code := f d.code }) :=
  filterMap_def?_mapBookItemCode f B.items

theorem slots_foldBook (B : Book) : (foldBook B).slots = B.slots := by
  simp [foldBook, Book.slots, defs_mapBookCode, List.map_map, Function.comp_def]


/-! ## 11. The specialized book's link, and the slot candidate that carries the proof

`specializeBook B pins = foldBook (bindBookPins B pins)`. The binding step is `link_bequiv_bindBookPins`
(`Obend.Leaf.Served`): sound when the dispatcher serves every pin, which `specializedJudgeB` decides.
The folding step is `link_bequiv_foldBook`. Together: **`B.link ≈b (specializeBook B pins).link`**,
and through `book_sound`, every member of the specialized book of a closed composition is the member
of the object. `Candidate.specialized name C pins` (`Obend.Leaf.Specialize`) carries exactly this:
its judge is `C.closedB && specializedJudgeB (emit C) pins`, so a usable candidate computes the
view's object (`specialized_usable_sound`), is kept exactly while its pins hold
(`specialized_choice`) and is blocked, naming the moved pin, when one does not
(`specialized_moved_pin_blocks`). -/

/-- The hole of a context read at `m`: the substitution that turns a context `C` into `C[.get hole m]`. -/
def getHole (m : String) : Nat → Term
  | 0 => .get (.bound 0) m
  | n + 1 => .bound (n + 1)

/-- Filling the hole of `C[.get hole m]` with `x` is filling the hole of `C` with `.get x m`. -/
theorem instantiate_getHole (C x : Term) (m : String) :
    instantiate (C.substitute (getHole m)) x = instantiate C (.get x m) := by
  rw [instantiate_eq, instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1; funext i; cases i <;> simp only [getHole, Term.substitute, single]

/-- `≈b` is a congruence for member reads. -/
theorem bequiv_get {t t' : Term} (h : t ≈b t') (m : String) : .get t m ≈b .get t' m := by
  intro ρ C
  have := h ρ (C.substitute (getHole m))
  rw [instantiate_getHole, instantiate_getHole] at this
  simpa only [Term.substitute] using this

/-- `specializeBook` is the folder over the bound book. -/
theorem specializeBook_eq_foldBook_bindBookPins (B : Book) (pins : List LeafPin) :
    specializeBook B pins = foldBook (bindBookPins B pins) :=
  specializeBook_eq_mapBookCode_bindBookPins B pins

/-- **The specialized book's link is the book's link**, when the judge admits the pins. -/
theorem link_bequiv_specializeBook (B : Book) (pins : List LeafPin)
    (h : specializedJudgeB B pins = true) : B.link ≈b (specializeBook B pins).link := by
  rw [specializeBook_eq_foldBook_bindBookPins]
  exact (Served.link_bequiv_bindBookPins_of_judgeB h).trans (link_bequiv_foldBook _)

/-- Every member of the specialized book of a closed composition is the member of the object. -/
theorem specializeBook_member_sound (C : Composition) (hc : C.closedB = true) (pins : List LeafPin)
    (h : specializedJudgeB (emit C) pins = true) (m : String) :
    .get (specializeBook (emit C) pins).link m ≈b .get C.object m :=
  (bequiv_get (link_bequiv_specializeBook (emit C) pins h) m).symm.trans (book_sound C hc m)

/-- **A usable specialized book is the specialization of the view's book, and computes its object**:
the view's object has the code the candidate pinned, so it emits the same book; the judge admitted
the pins against that book; and the object, when closed, computes what the book computes. -/
theorem specialized_usable_sound {k : Nat} {name : String} {C C' : Composition} {pins : List LeafPin}
    (h : specSlot.usable (holdsAt (viewOf k name C')) (.specialized name C pins) = true) :
    emit C = emit C' ∧
    (emit C').link ≈b (specializeBook (emit C') pins).link ∧
    (C'.closedB = true → ∀ m, .get (specializeBook (emit C) pins).link m ≈b .get C'.object m) := by
  obtain ⟨hj, hall⟩ := (usable_iff _ _ _).1 h
  have ho := hall ⟨.object name, C.code⟩ (by simp [Candidate.supports])
  rw [holdsAt_eq] at ho
  simp only [beq_self_eq_true, ite_true] at ho
  have e : emit C = emit C' := emit_congr (termEq_sound' ho).symm
  have hjudge : specializedJudgeB (emit C) pins = true := by
    simp only [Candidate.judge, Bool.and_eq_true] at hj
    exact hj.2
  refine ⟨e, e ▸ link_bequiv_specializeBook (emit C) pins hjudge, fun hc m => ?_⟩
  rw [e]
  exact specializeBook_member_sound C' hc pins (e ▸ hjudge) m

/-- The order a chooser gives for a specialized book: it first, the machine as the fallback. -/
def specializedOrder (name : String) (C : Composition) (pins : List LeafPin) : List Candidate :=
  [.specialized name C pins, .machine]

/-- **Incumbent-first for the specialized book**: kept exactly while usable, else the machine. -/
theorem specialized_choice (v : LeafView) (name : String) (C : Composition) (pins : List LeafPin) :
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v (specializedOrder name C pins)
        (some (.specialized name C pins)) =
      if specSlot.usable (holdsAt v) (.specialized name C pins) then .ok (.specialized name C pins)
      else .ok .machine := by
  split
  · rename_i hu
    exact (incumbent_choice specSlot v _ _ _).2 (.inl ⟨rfl, hu⟩)
  · rename_i hu
    have hf : specSlot.usable (holdsAt v) (.specialized name C pins) = false := by simpa using hu
    refine (incumbent_choice specSlot v _ _ _).2 (.inr ⟨fun c e => by cases e; exact hf, ?_⟩)
    simp [Slot.select, Slot.alternatives, specializedOrder, hf, machine_usable]

/-- **A moved pin blocks the specialized book by name**, as `moved_pin_blocks` for the book. -/
theorem specialized_moved_pin_blocks {v : LeafView} {name : String} {C : Composition}
    {pins : List LeafPin} (hj : specSlot.judge (.specialized name C pins) = true)
    {p : LeafPin} (hp : p ∈ (Candidate.specialized name C pins).supports) (hd : holdsAt v p = false) :
    ∃ d, specSlot.read (holdsAt v) (some (.specialized name C pins)) = .blocked (.specialized name C pins) d ∧
      p ∈ d ∧ ∀ q, q ∈ d ↔ q ∈ (Candidate.specialized name C pins).supports ∧ holdsAt v q = false := by
  have hmem : p ∈ specSlot.dead (holdsAt v) (.specialized name C pins) := (mem_dead_iff _ _ _ _).2 ⟨hp, hd⟩
  have hjudge : (Candidate.specialized name C pins).judge = true := hj
  have hread : ∃ d, specSlot.read (holdsAt v) (some (.specialized name C pins)) =
      .blocked (.specialized name C pins) d ∧ p ∈ d := by
    simp only [Slot.read, hjudge, ite_true]
    cases hdd : specSlot.dead (holdsAt v) (.specialized name C pins) with
    | nil => rw [hdd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hdd ▸ hmem⟩
  obtain ⟨d, hr, hpd⟩ := hread
  exact ⟨d, hr, hpd, (read_blocked_exact specSlot _ _ _ _ hr).2⟩


end Obend.Leaf.Static

end
