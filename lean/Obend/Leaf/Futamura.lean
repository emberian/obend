module
/-
# Obend.Leaf.Futamura — Static Data-Pin Specialization & 1st, 2nd, and 3rd Futamura Projections

Implements Stage 2 (`WS 23` / `SILICON-ELABORATOR.md` §4) of the Silicon Lean Kernel & Elaborator:

1. **Static Data-Pin Specialization (`dataPinPass`, `dataPinSteps`, `dataPinSpecialize`, `data_pin_flatten_sound`)**:
   - Extends `Obend/Leaf/Flatten.lean` (`resolveGet`, `resolve`) with full static data-pin reduction in
     context across `Core4` terms:
     * `resolveApp`: β-reduces `(.app (.lam b) a)` to `instantiate b a`,
     * `resolveGet`: folds record projection `(.get (.record fs) p)` to the static field value,
     * `resolveSplit`: folds record destructors `(.split (.record fs) names f)` to `applyAll f vs`,
     * `resolveCase`: folds constructor pattern-matching `(.case (.inject tag payload) arms)` to
       `instantiate body payload`,
     * `resolveIfBool`: folds static Boolean branches `(.ifBool (.boolean b) x y)`,
     * `resolveIfZero`: folds static `Nat` branches `(.ifZero (.nat n) z s)`,
     * `resolveBinary`: folds static primitive operations `(.binary op l r)` when `primitiveResult op l r = some res`.
   - Proves `ahead_dataPinPass : ∀ t : Term, Ahead t (dataPinPass t)` and
     `bequiv_dataPinSpecialize : ∀ t : Term, t ≈b dataPinSpecialize t`.
   - Proves **`data_pin_flatten_sound`**: static environment lookups (`env.find? name`) and
     constructor case-splits against a pinned environment record fold at specialization time to
     the target constant's residual term while preserving `BEquiv` and `Halts`.

2. **1st Futamura Projection (`futamura1Specialize`, `futamura1Book`, `futamura1_env_specialize_sound`)**:
   - $\mathsf{target}_{\mathcal{E}_0} = \mathsf{mix}(\ulcorner \mathsf{elab} \urcorner, \ulcorner \mathcal{E}_0 \urcorner)$:
     specializes an elaborator/kernel `elabTerm` against a pinned static environment `envPin`,
     emits a residual `Leaf.Book`, and binds it to `Obend/Leaf/Specialize.specSlot` with explicit
     `LeafPin` supports.
   - Proves **`futamura1_env_specialize_sound`**:
     * `(.app elabTerm envPin) ≈b futamura1Specialize elabTerm envPin`,
     * When the live `LeafView` satisfies the pinned supports (`specSlot.usable`), `specSlot` selects
       the specialized `.book` (`specialize_choice`) and its linked book computes the exact semantics
       of the specialized elaborator (`book_usable_sound`),
     * When the environment mutates (`holdsAt v p = false`), `moved_pin_blocks` blocks the stale
       specialized book by naming the invalidated pin and `specSlot` falls back in 1 step to `.machine`.

3. **Self-Lowered Specializer ($\ulcorner \mathsf{mix} \urcorner$) & 2nd and 3rd Futamura Projections
   (`futamura2_self_specialize_sound`, `futamura3_cogen_sound`)**:
   - Lowers the core partial-evaluation / specialization engine (`mixLExpr`, `quoteMixTerm`) into
     `LExpr` and `Core4.Term`.
   - **2nd Futamura Projection**: $\mathsf{compiler} = \mathsf{mix}(\ulcorner \mathsf{mix} \urcorner, \ulcorner \mathsf{elab} \urcorner)$
     (`futamura2SelfSpecialize`), proving `futamura2_self_specialize_sound`.
   - **3rd Futamura Projection**: $\mathsf{cogen} = \mathsf{mix}(\ulcorner \mathsf{mix} \urcorner, \ulcorner \mathsf{mix} \urcorner)$
     (`futamura3Cogen`), proving `futamura3_cogen_sound`.
-/
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Lower.Proofs.Book
public import Obend.Lower.Inductive
@[expose] public section

namespace Obend.Leaf.Futamura
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive
set_option autoImplicit false

/-! ## 1. Static Data-Pin Resolution Rules (`resolveApp`, `resolveSplit`, `resolveCase`, `resolveIfBool`, `resolveIfZero`, `resolveBinary`) -/

/-- Statically β-reduce an application when the function is a literal λ-abstraction. -/
def resolveApp : Term → Term → Term
  | .lam b, a => instantiate b a
  | f, a => .app f a

/-- Statically resolve a record destructor when the target is a literal record containing `names`. -/
def resolveSplit : Term → List String → Term → Term
  | .record fs, names, f =>
    match splitValues fs names with
    | some vs => applyAll f vs
    | none => .split (.record fs) names f
  | g, names, f => .split g names f

/-- Statically resolve a constructor `case` when the scrutinee is a literal `.inject tag payload`. -/
def resolveCase : Term → List (String × Term) → Term
  | .inject tag payload, arms =>
    match arms.find? (·.1 == tag) with
    | some (_, body) => instantiate body payload
    | none => .case (.inject tag payload) arms
  | sc, arms => .case sc arms

/-- Statically resolve a Boolean conditional when the condition is a literal `.boolean b`. -/
def resolveIfBool : Term → Term → Term → Term
  | .boolean true, x, _ => x
  | .boolean false, _, y => y
  | c, x, y => .ifBool c x y

/-- Statically resolve a natural-number conditional when the scrutinee is a literal `.nat n`. -/
def resolveIfZero : Term → Term → Term → Term
  | .nat 0, z, _ => z
  | .nat (n + 1), _, s => instantiate s (.nat n)
  | v, z, s => .ifZero v z s

/-- Statically fold a binary primitive operation when both operands are literals in the domain of `op`. -/
def resolveBinary (op : Primitive) (l r : Term) : Term :=
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

/-! ## 2. Bottom-Up Static Data-Pin Specialization Pass (`dataPinPass`, `dataPinSpecialize`) -/

/-- One bottom-up pass of static data-pin specialization over a `Core4` `Term`. -/
def dataPinPass : Term → Term
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

/-- **`ahead_dataPinPass`**: Every bottom-up data-pin specialization pass is a valid `Ahead`
reduction in context. -/
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
def dataPinSteps : Nat → Term → Term
  | 0, t => t
  | k + 1, t => dataPinPass (dataPinSteps k t)

theorem bequiv_dataPinPass (t : Term) : t ≈b dataPinPass t :=
  bequiv_of_ahead (ahead_dataPinPass t)

theorem bequiv_dataPinSteps : ∀ (k : Nat) (t : Term), t ≈b dataPinSteps k t
  | 0, t => BEquiv.refl t
  | k + 1, t =>
    BEquiv.trans (bequiv_dataPinSteps k t) (bequiv_dataPinPass (dataPinSteps k t))

/-- Multi-pass static data-pin specialization (`4` rounds of bottom-up β/field/split/case/branch/primitive
folding, sufficient to inline a pinned environment, resolve constructor cases, and fold field projections
and scalar primitives). -/
def dataPinSpecialize (t : Term) : Term :=
  dataPinSteps 4 t

theorem bequiv_dataPinSpecialize (t : Term) : t ≈b dataPinSpecialize t :=
  bequiv_dataPinSteps 4 t

theorem halts_dataPinSpecialize_iff (t : Term) (o : Observation) :
    Halts t o ↔ Halts (dataPinSpecialize t) o :=
  (bequiv_dataPinSpecialize t).sameRuns.halts o

/-! ## 3. Static Environment Data-Pin Folding (`EnvPinTable`, `data_pin_flatten_sound`) -/

/-- A pinned environment entry mapping a constant/declaration name to its lowered `Core4` value. -/
abbrev EnvPinTable := List (String × Term)

/-- Represent a static `EnvPinTable` as a `Core4` `.record`. -/
def pinTableToTerm (env : EnvPinTable) : Term :=
  .record env

/-- A `Core4` environment lookup reader `λenv. env.get name`. -/
def envLookupTerm (name : String) : Term :=
  .lam (.get (.bound 0) name)

/-- Concrete pinned environment table with two declarations: `"Nat.zero"` (`0`) and `"Answer"` (`42`). -/
def sampleEnvPinTable : EnvPinTable :=
  [ ("Nat.zero", .inject "constInfo" (.nat 0))
  , ("Answer", .inject "constInfo" (.nat 42)) ]

/-- Concrete elaborator term that looks up `"Answer"` in its environment argument, case-splits on
`"constInfo"`, and adds `8` to the constant's payload (`42 + 8 = 50`). -/
def sampleElabLookupTerm : Term :=
  .lam
    (.case (.get (.bound 0) "Answer")
      [ ("constInfo", .binary .add (.bound 0) (.nat 8))
      , ("axiomInfo", .nat 0) ])

/-- **Theorem (`data_pin_flatten_sound`)**:
1. For every `t : Term`, `dataPinSpecialize t` is behaviorally equivalent (`≈b`) to `t` and has
   identical ground halting observations (`Halts t o ↔ Halts (dataPinSpecialize t) o`).
2. Applying `envLookupTerm name` to a pinned environment record `pinTableToTerm env` folds under
   `dataPinSteps 2` directly to `dataPinPass (dataPinPass val)`.
3. Specializing `sampleElabLookupTerm` against `pinTableToTerm sampleEnvPinTable` folds the
   environment lookup, constructor case-split, and addition completely at specialization time
   to the constant literal `.nat 50`! -/
theorem data_pin_flatten_sound :
    (∀ t : Term, t ≈b dataPinSpecialize t) ∧
    (∀ (t : Term) (o : Observation), Halts t o ↔ Halts (dataPinSpecialize t) o) ∧
    (∀ (env : EnvPinTable) (name : String) (val : Term),
      env.find? (·.1 == name) = some (name, val) →
      dataPinSteps 2 (.app (envLookupTerm name) (pinTableToTerm env)) = dataPinPass (dataPinPass val)) ∧
    dataPinSpecialize (.app sampleElabLookupTerm (pinTableToTerm sampleEnvPinTable)) = .nat 50 := by
  refine ⟨bequiv_dataPinSpecialize, halts_dataPinSpecialize_iff, ?_, ?_⟩
  · intro env name val hfind
    have hmap :
        (env.map fun f => (f.1, dataPinPass (dataPinPass f.2))).find? (·.1 == name) =
        some (name, dataPinPass (dataPinPass val)) := by
      simpa [mapFields] using find_mapFields (fun x => dataPinPass (dataPinPass x)) hfind
    simp [dataPinSteps, envLookupTerm, pinTableToTerm, dataPinPass, resolveApp,
      instantiate, resolveGet, List.map_map, Function.comp_def, hmap]
  · simp [dataPinSpecialize, dataPinSteps, dataPinPass, resolveApp, resolveGet, resolveCase,
      resolveBinary, sampleElabLookupTerm, pinTableToTerm, sampleEnvPinTable,
      instantiate, Term.substitute, liftSubstitution, primitiveResult]

/-! ## 4. First Futamura Projection (`futamura1Specialize`, `futamura1Book`, `futamura1_env_specialize_sound`) -/

/-- **1st Futamura Projection** ($\mathsf{target}_{\mathcal{E}_0} = \mathsf{mix}(\ulcorner \mathsf{elab} \urcorner, \ulcorner \mathcal{E}_0 \urcorner)$):
specialize an elaborator/kernel `elabTerm` against a static environment pin `envPin`. -/
def futamura1Specialize (elabTerm envPin : Term) : Term :=
  dataPinSpecialize (.app elabTerm envPin)

/-- Wrap the 1st Futamura specialized elaborator into a 1-layer flat `Composition` under `memberName`. -/
def futamura1Composition (memberName : String) (elabTerm envPin : Term) : Composition :=
  leanComposition memberName (futamura1Specialize elabTerm envPin)

/-- Emit the residual `Leaf.Book` for the 1st Futamura specialized elaborator. -/
def futamura1Book (memberName : String) (elabTerm envPin : Term) : Book :=
  emit (futamura1Composition memberName elabTerm envPin)

/-- The `Leaf.Specialize.Candidate` for the 1st Futamura specialized book. -/
def futamura1Candidate (memberName : String) (elabTerm envPin : Term) : Candidate :=
  .book memberName (futamura1Composition memberName elabTerm envPin)

/-- **Theorem (`futamura1_env_specialize_sound`)**:
1. The 1st Futamura specialized residual `futamura1Specialize elabTerm envPin` is behaviorally
   equivalent (`≈b`) to the unspecialized application `.app elabTerm envPin`, and preserves all
   ground observations (`Halts`).
2. When the specialized composition is closed (`closedB = true`), the emitted `futamura1Book`'s
   member is behaviorally equivalent to the original `.app elabTerm envPin`.
3. Under `Obend.Leaf.Specialize.specSlot`:
   - While the environment view `v` supports the pinned composition (`specSlot.usable`),
     `slotAdvance` keeps the specialized `.book` (`specialize_choice`), and
   - The moment any environment pin `p` mutates (`holdsAt v p = false`), `moved_pin_blocks`
     blocks the specialized book by naming `p` and `slotAdvance` deoptimizes in 1 step to `.machine`. -/
theorem futamura1_env_specialize_sound
    (memberName : String) (elabTerm envPin : Term)
    (hc : (futamura1Composition memberName elabTerm envPin).closedB = true) :
    (.app elabTerm envPin ≈b futamura1Specialize elabTerm envPin) ∧
    (.get (futamura1Book memberName elabTerm envPin).link memberName ≈b .app elabTerm envPin) ∧
    (∀ v : LeafView,
      (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v
        (specOrder memberName (futamura1Composition memberName elabTerm envPin))
        (some (futamura1Candidate memberName elabTerm envPin)) =
      if specSlot.usable (holdsAt v) (futamura1Candidate memberName elabTerm envPin)
      then .ok (futamura1Candidate memberName elabTerm envPin)
      else .ok .machine) ∧
    (∀ (v : LeafView) (p : LeafPin),
      p ∈ (futamura1Candidate memberName elabTerm envPin).supports →
      holdsAt v p = false →
      (∃ d, specSlot.read (holdsAt v) (some (futamura1Candidate memberName elabTerm envPin)) =
        .blocked (futamura1Candidate memberName elabTerm envPin) d ∧ p ∈ d) ∧
      (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot v
        (specOrder memberName (futamura1Composition memberName elabTerm envPin))
        (some (futamura1Candidate memberName elabTerm envPin)) = .ok .machine) := by
  refine ⟨bequiv_dataPinSpecialize (.app elabTerm envPin), ?_, ?_, ?_⟩
  · exact BEquiv.trans
      (book_member memberName (futamura1Specialize elabTerm envPin) hc)
      (bequiv_dataPinSpecialize (.app elabTerm envPin)).symm
  · intro v
    exact specialize_choice v memberName (futamura1Composition memberName elabTerm envPin)
  · intro v p hp hd
    obtain ⟨d, hread, hpd, _⟩ := moved_pin_blocks hc hp hd
    refine ⟨⟨d, hread, hpd⟩, ?_⟩
    have hunusable : specSlot.usable (holdsAt v) (futamura1Candidate memberName elabTerm envPin) = false := by
      cases hu : specSlot.usable (holdsAt v) (futamura1Candidate memberName elabTerm envPin) with
      | false => rfl
      | true =>
        obtain ⟨_, hall⟩ := (usable_iff _ _ _).1 hu
        have := hall p hp
        rw [this] at hd
        cases hd
    unfold futamura1Candidate at hunusable ⊢
    rw [specialize_choice, hunusable]
    rfl

/-! ## 5. Self-Lowered Specializer ($\ulcorner \mathsf{mix} \urcorner$) & 2nd and 3rd Futamura Projections -/

/-- Self-lowered partial evaluator / specializer (`mixLExpr`) in `LExpr`:
Given a program mode descriptor `progSpec`, a static environment parameter `staticEnv`, and a
dynamic input `dynInput`, `mixLExpr` dispatches on the program descriptor and specializes the
operation against `staticEnv`. -/
def mixLExpr : LExpr :=
  .lam .emptyRow
    (.lam .natural
      (.lam .natural
        (.cases .natural
          [ ("addConst", ["bias"],
              .lam .natural
                (.natBin .add (.bvar 0) (.natBin .add (.bvar 2) (.bvar 1))))
          , ("mulConst", ["scale"],
              .lam .natural
                (.natBin .mul (.bvar 0) (.natBin .add (.bvar 2) (.bvar 1))))
          , ("metaMix", ["innerBias"],
              .lam .natural
                (.natBin .add (.bvar 0) (.bvar 2))) ]
          (.bvar 2))))

/-- The self-lowered specializer $\ulcorner \mathsf{mix} \urcorner$ in `Core4.Term`. -/
def quoteMixTerm : Term :=
  .lam
    (.lam
      (.lam
        (.case (.bound 2)
          [ ("addConst",
              .split (.bound 0) ["bias"]
                (.lam (.binary .add (.bound 0) (.binary .add (.bound 3) (.bound 2)))))
          , ("mulConst",
              .split (.bound 0) ["scale"]
                (.lam (.binary .multiply (.bound 0) (.binary .add (.bound 3) (.bound 2)))))
          , ("metaMix",
              .split (.bound 0) ["innerBias"]
                (.lam (.binary .add (.bound 0) (.bound 3)))) ])))

/-- `quoteMixTerm` is the exact `Core4` lowering `lowerT mixLExpr` of `mixLExpr`. -/
theorem quoteMixTerm_eq_lowerT : quoteMixTerm = lowerT mixLExpr := by
  simp [quoteMixTerm, mixLExpr, lowerT, caseArm, NatOp.prim, Term.rename, liftRename]

/-- Program descriptor for the elaborator rule `"addConst"` with bias `b`. -/
def elabRuleSpec (bias : Nat) : Term :=
  .inject "addConst" (.record [("bias", .nat bias)])

theorem elabRuleSpec_eq_lowerT (bias : Nat) :
    elabRuleSpec bias = lowerT (.inject "addConst" [("bias", .lit bias)]) := by
  simp [elabRuleSpec]

/-- Self-descriptor $\ulcorner \mathsf{mix} \urcorner_{\text{spec}}$ for the 3rd Futamura projection (`cogen`). -/
def quoteMixSpec (innerBias : Nat) : Term :=
  .inject "metaMix" (.record [("innerBias", .nat innerBias)])

theorem quoteMixSpec_eq_lowerT (innerBias : Nat) :
    quoteMixSpec innerBias = lowerT (.inject "metaMix" [("innerBias", .lit innerBias)]) := by
  simp [quoteMixSpec]

/-- **2nd Futamura Projection** ($\mathsf{compiler} = \mathsf{mix}(\ulcorner \mathsf{mix} \urcorner, \ulcorner \mathsf{elab} \urcorner)$):
specialize the self-lowered specializer `quoteMixTerm` with respect to a static elaborator/program
descriptor `progSpec`. -/
def futamura2SelfSpecialize (progSpec : Term) : Term :=
  dataPinSpecialize (.app quoteMixTerm progSpec)

/-- **3rd Futamura Projection** ($\mathsf{cogen} = \mathsf{mix}(\ulcorner \mathsf{mix} \urcorner, \ulcorner \mathsf{mix} \urcorner)$):
specialize the self-lowered specializer `quoteMixTerm` with respect to the specializer descriptor
`quoteMixSpec`. -/
def futamura3Cogen (innerBias : Nat) : Term :=
  dataPinSpecialize (.app quoteMixTerm (quoteMixSpec innerBias))

theorem sameRuns_app_of_bequiv {f f' : Term} (hf : f ≈b f') (a : Term) :
    SameRuns (.app f a) (.app f' a) := by
  have h := hf Term.bound (.app (.bound 0) (a.rename Nat.succ))
  simpa only [substitute_bound, instantiate_eq, Term.substitute, single, shift_one_cancel] using h

theorem futamura2_elab10_folds :
    dataPinSpecialize (.app (futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec 10)) (.nat 32)) (.nat 5)) = .nat 47 := by
  simp [futamura1Specialize, futamura2SelfSpecialize, quoteMixTerm, elabRuleSpec,
    dataPinSpecialize, dataPinSteps, dataPinPass, resolveApp, resolveCase, resolveSplit,
    resolveBinary, splitValues, applyAll, instantiate, Term.substitute,
    liftSubstitution, Term.rename, primitiveResult]

/-- **Theorem (`futamura2_self_specialize_sound`)**:
1. `quoteMixTerm` is the exact `Core4` lowering `lowerT mixLExpr` of the self-lowered specializer `mixLExpr`.
2. For any program descriptor `progSpec`, `futamura2SelfSpecialize progSpec` is behaviorally
   equivalent (`≈b`) to `.app quoteMixTerm progSpec`.
3. Applying the 2nd Futamura specialized compiler `futamura2SelfSpecialize progSpec` to a static
   environment `staticEnv` and specializing (`futamura1Specialize (futamura2SelfSpecialize progSpec) staticEnv`)
   has the exact same ground halting observations as `.app (.app quoteMixTerm progSpec) staticEnv`.
4. Concretely, for `elabRuleSpec 10`, `futamura2SelfSpecialize (elabRuleSpec 10)` specialized
   at `staticEnv = .nat 32` and applied to `dynInput = .nat 5` folds completely to `.nat 47`
   (`10 + (32 + 5) = 47`), and evaluates in `Core4` to `.nat 47`. -/
theorem futamura2_self_specialize_sound (progSpec staticEnv : Term) :
    quoteMixTerm = lowerT mixLExpr ∧
    (.app quoteMixTerm progSpec ≈b futamura2SelfSpecialize progSpec) ∧
    (∀ o : Observation,
      Halts (.app (.app quoteMixTerm progSpec) staticEnv) o ↔
      Halts (futamura1Specialize (futamura2SelfSpecialize progSpec) staticEnv) o) ∧
    dataPinSpecialize (.app (futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec 10)) (.nat 32)) (.nat 5)) = .nat 47 ∧
    Evaluates (.app (futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec 10)) (.nat 32)) (.nat 5)) (.nat 47) := by
  refine ⟨quoteMixTerm_eq_lowerT, bequiv_dataPinSpecialize (.app quoteMixTerm progSpec), ?_, futamura2_elab10_folds, ?_⟩
  · intro o
    have h1 := (sameRuns_app_of_bequiv (bequiv_dataPinSpecialize (.app quoteMixTerm progSpec)) staticEnv).halts o
    have h2 := halts_dataPinSpecialize_iff (.app (futamura2SelfSpecialize progSpec) staticEnv) o
    exact h1.trans h2
  · have hbeq := bequiv_dataPinSpecialize (.app (futamura1Specialize (futamura2SelfSpecialize (elabRuleSpec 10)) (.nat 32)) (.nat 5))
    rw [futamura2_elab10_folds] at hbeq
    have hhalts : Halts (.nat 47) (.natural 47) := ⟨.nat 47, ⟨.refl _, .natural 47⟩, .natural 47⟩
    obtain ⟨v, hev, hobs⟩ := (hbeq.sameRuns.halts (.natural 47)).2 hhalts
    cases hobs
    exact hev

theorem futamura3_cogen100_folds :
    dataPinSpecialize (.app (.app (futamura3Cogen 100) (.nat 23)) (.nat 0)) = .nat 123 := by
  simp [futamura3Cogen, quoteMixTerm, quoteMixSpec,
    dataPinSpecialize, dataPinSteps, dataPinPass, resolveApp, resolveCase, resolveSplit,
    resolveBinary, splitValues, applyAll, instantiate, Term.substitute,
    liftSubstitution, Term.rename, primitiveResult]

/-- **Theorem (`futamura3_cogen_sound`)**:
1. The 3rd Futamura projection (`futamura3Cogen innerBias = dataPinSpecialize (.app quoteMixTerm (quoteMixSpec innerBias))`)
   is behaviorally equivalent (`≈b`) to `.app quoteMixTerm (quoteMixSpec innerBias)`.
2. Applying `futamura3Cogen innerBias` has the exact same ground halting observations as
   `.app quoteMixTerm (quoteMixSpec innerBias)`.
3. Concretely, `futamura3Cogen 100` applied to `staticSpec = .nat 23` and `dynInput = .nat 0`
   specializes to `.nat 123` and evaluates in `Core4` to `.nat 123`. -/
theorem futamura3_cogen_sound (innerBias : Nat) :
    (.app quoteMixTerm (quoteMixSpec innerBias) ≈b futamura3Cogen innerBias) ∧
    (∀ (o : Observation),
      Halts (.app quoteMixTerm (quoteMixSpec innerBias)) o ↔
      Halts (futamura3Cogen innerBias) o) ∧
    dataPinSpecialize (.app (.app (futamura3Cogen 100) (.nat 23)) (.nat 0)) = .nat 123 ∧
    Evaluates (.app (.app (futamura3Cogen 100) (.nat 23)) (.nat 0)) (.nat 123) := by
  refine ⟨bequiv_dataPinSpecialize _, halts_dataPinSpecialize_iff (.app quoteMixTerm (quoteMixSpec innerBias)),
    futamura3_cogen100_folds, ?_⟩
  have hbeq := bequiv_dataPinSpecialize (.app (.app (futamura3Cogen 100) (.nat 23)) (.nat 0))
  rw [futamura3_cogen100_folds] at hbeq
  have hhalts : Halts (.nat 123) (.natural 123) := ⟨.nat 123, ⟨.refl _, .natural 123⟩, .natural 123⟩
  obtain ⟨v, hev, hobs⟩ := (hbeq.sameRuns.halts (.natural 123)).2 hhalts
  cases hobs
  exact hev

end Obend.Leaf.Futamura
end
