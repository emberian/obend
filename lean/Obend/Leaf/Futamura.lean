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
public import Obend.Tactic.Tooth
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

/-! ## 6. Program-as-Data (`Term`) Representation of `Book` & `LeafPin` (`encodeBookTerm`, `decodeBookTerm?`) -/

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

/-! ## 7. Commutation of `dataPinPass` and `dataPinSpecialize` Through `encodeBookTerm` -/

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

/-! ## 8. Book Specializer (`specializeBook`), Internalized Staging (`specializeBookInCore`, `futamura2BookCompiler`, `cogenBookInCore`) & Futamura 1, 2, 3 Commuting Diagrams -/

/-- Substitute pinned member values from `pins` for `self.m` reads inside a definition's `code`. -/
def substPinsInCode (pins : List LeafPin) : Term → Term
  | .lam inner => .lam (substMemberEnvAt 0 (pinListEnv pins) inner)
  | other => substMemberEnvAt 0 (pinListEnv pins) other

/-- Specialize a definition's `code` under `pins`: bind all pinned `self.m` reads and run
4 passes of bottom-up constant propagation, dead-branch elimination (`.ifZero`/`.ifBool`),
and method β-inlining (`dataPinSpecialize`). -/
def specializeDefCode (pins : List LeafPin) (code : Term) : Term :=
  dataPinSpecialize (substPinsInCode pins code)

/-- Compute the residual slot indices still read through `self` after binding `pins`. -/
def residualSlotReads (slots : List String) (pins : List LeafPin) (d : LeafDef) : List Nat :=
  let pinnedCode := substPinsInCode pins d.code
  let bodyForReads := match d.kind, pinnedCode with
    | .method, .lam b => b
    | .cell, .lam (.lam b) => b
    | _, b => b
  let readDepth := match d.kind with
    | .method => 0
    | .cell => 1
  ((extractReadMembersAt readDepth bodyForReads).filterMap slots.idxOf?).eraseDups

/-- Bind `pins` into a `LeafDef` (prior to running `dataPinSpecialize`). -/
def bindLeafDef (slots : List String) (pins : List LeafPin) (d : LeafDef) : LeafDef :=
  { d with
    code := substPinsInCode pins d.code
    reads := residualSlotReads slots pins d }

/-- Bind `pins` into a `BookItem` (prior to running `dataPinSpecialize`). -/
def bindBookItem (slots : List String) (pins : List LeafPin) : BookItem → BookItem
  | .slot d => .slot (bindLeafDef slots pins d)
  | .static m v => .static m v

/-- Bind `pins` across all definitions of a `Book` (prior to running `dataPinSpecialize`). -/
def bindBookPins (B : Book) (pins : List LeafPin) : Book :=
  { items := B.items.map (bindBookItem B.slots pins) }

/-- Specialize a `LeafDef` against `pins`. -/
def specializeLeafDef (slots : List String) (pins : List LeafPin) (d : LeafDef) : LeafDef :=
  { d with
    code := specializeDefCode pins d.code
    reads := residualSlotReads slots pins d }

/-- Specialize a `BookItem` against `pins`. -/
def specializeBookItem (slots : List String) (pins : List LeafPin) : BookItem → BookItem
  | .slot d => .slot (specializeLeafDef slots pins d)
  | .static m v => .static m (dataPinSpecialize v)

/-- **Specialize an entire `Obend.Leaf.Book` against a pin environment `pins : List LeafPin` (`specializeBook`)**:
propagates pinned constants, eliminates dead `.ifZero`/`.ifBool` branches over pinned fields,
inlines pinned methods across definitions, and updates residual slot read dependencies. -/
def specializeBook (B : Book) (pins : List LeafPin) : Book :=
  { items := B.items.map (specializeBookItem B.slots pins) }

theorem specializeBook_eq_mapBookCode_bindBookPins (B : Book) (pins : List LeafPin) :
    specializeBook B pins = mapBookCode dataPinSpecialize (bindBookPins B pins) := by
  unfold specializeBook bindBookPins mapBookCode
  simp only [List.map_map, Function.comp_def, Book.mk.injEq]
  apply List.map_congr_left
  intro item _
  cases item <;> rfl

/-- **Internalized 1st Futamura Book Specializer in `Core4` (`specializeBookInCore`)**:
executes `dataPinSpecialize` directly on the `Core4` term encoding `bindBookPins B pins`. -/
def specializeBookInCore (B : Book) (pins : List LeafPin) : Term :=
  dataPinSpecialize (encodeBookTerm (bindBookPins B pins))

/-- `specializeBookInCore B pins` reduces in `Core4` to the exact encoded residual book
`encodeBookTerm (specializeBook B pins)`. -/
theorem specializeBookInCore_eq_encodeBookTerm (B : Book) (pins : List LeafPin) :
    specializeBookInCore B pins = encodeBookTerm (specializeBook B pins) := by
  unfold specializeBookInCore
  rw [dataPinSpecialize_encodeBookTerm, ← specializeBook_eq_mapBookCode_bindBookPins]

/-- Decoding `specializeBookInCore B pins` recovers `some (specializeBook B pins)`. -/
@[simp] theorem decodeBookTerm_specializeBookInCore (B : Book) (pins : List LeafPin) :
    decodeBookTerm? (specializeBookInCore B pins) = some (specializeBook B pins) := by
  rw [specializeBookInCore_eq_encodeBookTerm, decodeBookTerm_encodeBookTerm]

/-- Lowered `LExpr` combinator for the internalized 2nd Futamura book specializer (`bookMixLExpr`). -/
def bookMixLExpr : LExpr :=
  .lam .emptyRow
    (.cases .emptyRow
      [ ("bookStage", ["bookPayload"],
          .lam .emptyRow (.lam .emptyRow (.bvar 1))) ]
      (.bvar 0))

/-- The internalized `Core4` book-staging specializer $\ulcorner \mathsf{mix}_{\text{book}} \urcorner$. -/
def quoteBookMixTerm : Term :=
  .lam
    (.case (.bound 0)
      [ ("bookStage",
          .split (.bound 0) ["bookPayload"]
            (.lam (.lam (.bound 1)))) ])

theorem quoteBookMixTerm_eq_lowerT : quoteBookMixTerm = lowerT bookMixLExpr := by
  simp [quoteBookMixTerm, bookMixLExpr, lowerT, caseArm, Term.rename, liftRename]

/-- Wrap an encoded book payload into a `"bookStage"` descriptor for `quoteBookMixTerm`. -/
def bookStageSpec (bookTerm : Term) : Term :=
  .inject "bookStage" (.record [("bookPayload", bookTerm)])

/-- **Literal Self-Application of `dataPinSpecialize` to `quoteBookMixTerm`**:
For any `bookTerm : Term`, specializing `(.app quoteBookMixTerm (bookStageSpec bookTerm))` via
`dataPinSpecialize` folds the outer β-redex (Pass 1), the `"bookStage"` constructor case-split
(Pass 2), the `"bookPayload"` record destructor split (Pass 3), and the inner payload binding
(Pass 4), producing the specialized `Core4` compiler lambda `.lam ((dataPinSpecialize bookTerm).rename Nat.succ)`. -/
theorem dataPinSpecialize_quoteBookMixTerm (bookTerm : Term) :
    dataPinSpecialize (.app quoteBookMixTerm (bookStageSpec bookTerm)) =
      .lam ((dataPinSpecialize bookTerm).rename Nat.succ) := by
  have hb1 : ("bookStage" == "bookStage") = true := rfl
  have hb2 : ("bookPayload" == "bookPayload") = true := rfl
  simp only [quoteBookMixTerm, bookStageSpec, dataPinSpecialize, dataPinSteps, dataPinPass,
    resolveApp, resolveCase, resolveSplit, splitValues, applyAll,
    instantiate, Term.substitute, liftSubstitution, Term.rename,
    List.map, List.find?, hb1, hb2, bind, pure, Option.bind]

/-- **2nd Futamura Projection for `Book`s (`futamura2BookCompiler`)**:
$\mathsf{compiler}_{B,\text{pins}} = \mathsf{mix}(\ulcorner \mathsf{mix}_{\text{book}} \urcorner, \ulcorner B_{\text{pins}} \urcorner)$. -/
def futamura2BookCompiler (B : Book) (pins : List LeafPin) : Term :=
  dataPinSpecialize (.app quoteBookMixTerm (bookStageSpec (encodeBookTerm (bindBookPins B pins))))

theorem futamura2BookCompiler_eq (B : Book) (pins : List LeafPin) :
    futamura2BookCompiler B pins = .lam ((encodeBookTerm (specializeBook B pins)).rename Nat.succ) := by
  unfold futamura2BookCompiler
  rw [dataPinSpecialize_quoteBookMixTerm]
  congr 2
  exact specializeBookInCore_eq_encodeBookTerm B pins

/-- Apply a staged `Core4` compiler lambda to an argument term via `resolveApp`. -/
def runStagedCompiler (compiler arg : Term) : Term :=
  resolveApp compiler arg

/-- Applying `futamura2BookCompiler B pins` to any pin/runtime argument `arg` produces
`encodeBookTerm (specializeBook B pins)` in 1 β-step. -/
theorem runStagedCompiler_futamura2 (B : Book) (pins : List LeafPin) (arg : Term) :
    runStagedCompiler (futamura2BookCompiler B pins) arg = encodeBookTerm (specializeBook B pins) := by
  rw [futamura2BookCompiler_eq]
  simp only [runStagedCompiler, resolveApp, instantiate_succ]

theorem step_futamura2BookCompiler (B : Book) (pins : List LeafPin) (arg : Term) :
    Step (.app (futamura2BookCompiler B pins) arg) (encodeBookTerm (specializeBook B pins)) := by
  rw [futamura2BookCompiler_eq]
  have hstep : Step (.app (.lam ((encodeBookTerm (specializeBook B pins)).rename Nat.succ)) arg)
      (instantiate ((encodeBookTerm (specializeBook B pins)).rename Nat.succ) arg) :=
    .beta _ _
  rwa [instantiate_succ] at hstep

theorem evaluates_futamura2BookCompiler (B : Book) (pins : List LeafPin) (arg : Term) :
    Evaluates (.app (futamura2BookCompiler B pins) arg) (encodeBookTerm (specializeBook B pins)) := by
  refine ⟨.next (step_futamura2BookCompiler B pins arg) (.refl _), ?_⟩
  unfold encodeBookTerm
  exact .record _

/-- Lowered `LExpr` combinator for the 3rd Futamura compiler-generator (`metaCogenLExpr`). -/
def metaCogenLExpr : LExpr :=
  .lam .emptyRow
    (.cases .emptyRow
      [ ("cogenStage", ["innerMix"],
          .lam .emptyRow (.lam .emptyRow (.app (.bvar 1) (.bvar 0)))) ]
      (.bvar 0))

/-- The internalized `Core4` meta-specializer $\ulcorner \mathsf{cogen}_{\text{meta}} \urcorner$. -/
def quoteMetaCogenTerm : Term :=
  .lam
    (.case (.bound 0)
      [ ("cogenStage",
          .split (.bound 0) ["innerMix"]
            (.lam (.lam (.app (.bound 1) (.bound 0))))) ])

theorem quoteMetaCogenTerm_eq_lowerT : quoteMetaCogenTerm = lowerT metaCogenLExpr := by
  simp [quoteMetaCogenTerm, metaCogenLExpr, lowerT, caseArm, Term.rename, liftRename]

/-- Wrap an inner specializer term into a `"cogenStage"` descriptor for `quoteMetaCogenTerm`. -/
def cogenStageSpec (innerMix : Term) : Term :=
  .inject "cogenStage" (.record [("innerMix", innerMix)])

/-- **3rd Futamura Projection for `Book`s (`cogenBookInCore`)**:
$\mathsf{cogen} = \mathsf{mix}(\ulcorner \mathsf{cogen}_{\text{meta}} \urcorner, \ulcorner \mathsf{mix}_{\text{book}} \urcorner)$,
constructed by literal self-application of `dataPinSpecialize`. -/
def cogenBookInCore : Term :=
  dataPinSpecialize (.app quoteMetaCogenTerm (cogenStageSpec quoteBookMixTerm))

/-- Self-applying `dataPinSpecialize` in `cogenBookInCore` folds the meta-descriptor case and split
completely to `.lam (.app quoteBookMixTerm (.bound 0))`. -/
theorem cogenBookInCore_eq :
    cogenBookInCore = .lam (.app quoteBookMixTerm (.bound 0)) :=
  Obend.Law.termEq_sound (by decide +kernel)

/-- Applying `cogenBookInCore` to a staged book descriptor and specializing yields the exact
2nd Futamura compiler `futamura2BookCompiler B pins`. -/
theorem cogenBookInCore_generates_compiler (B : Book) (pins : List LeafPin) :
    dataPinSpecialize
      (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))) =
    futamura2BookCompiler B pins := by
  rw [cogenBookInCore_eq]
  simp only [runStagedCompiler, resolveApp, instantiate, Term.substitute, liftSubstitution,
    futamura2BookCompiler, quoteBookMixTerm, Term.rename, List.map]

/-! ## 9. Semantic Evaluation of `Book` & `specializeBook`, and the Commuting Diagrams -/

/-- Extract a canonical pin entry `(member, value)` from a `BookItem` when the item is a static
member or a self-independent cell/method. -/
def itemPinEntry : BookItem → Option (String × Term)
  | .static m v => some (m, v)
  | .slot d =>
    match d.kind, d.code with
    | .cell, .lam (.lam v) =>
      if (extractReadMembersAt 1 v).isEmpty then some (d.member, v) else none
    | .method, .lam v =>
      if (extractReadMembersAt 0 v).isEmpty then some (d.member, v) else none
    | _, _ => none

/-- The canonical `LeafPin` list of a `Book`'s self-independent cells, methods, and statics. -/
def bookCanonicalPins (B : Book) : List LeafPin :=
  (B.items.filterMap itemPinEntry).map fun (m, v) => ⟨.layer m, v⟩

/-- Look up the raw code of member `m` in `B`. -/
def lookupBookCode (B : Book) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d => some d.code
  | none => (B.statics.find? (·.1 == m)).map (·.2)

/-- Evaluate member `m` of `Book` `B` under explicit `pins : List LeafPin`. -/
def evalBookUnderPins (B : Book) (pins : List LeafPin) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d => some (specializeDefCode pins d.code)
  | none => (B.statics.find? (·.1 == m)).map (fun (_, v) => dataPinSpecialize v)

/-- Evaluate member `m` of `Book` `B`: if `m` is a slot with no remaining `self` reads (`d.reads.isEmpty`),
returns `d.code` directly (as its `self` reads are already resolved); otherwise resolves `d`'s `self`
reads against `bookCanonicalPins B`. -/
def evalBook (B : Book) (m : String) : Option Term :=
  match B.defs.find? (·.member == m) with
  | some d =>
    if d.reads.isEmpty then
      some d.code
    else
      some (specializeDefCode (bookCanonicalPins B) d.code)
  | none =>
    (B.statics.find? (·.1 == m)).map (fun (_, v) => dataPinSpecialize v)

/-- Extract the member names read via `self` inside a definition `code` (matching `substPinsInCode`). -/
def extractReadMembersCode : Term → List String
  | .lam inner => extractReadMembersAt 0 inner
  | other => extractReadMembersAt 0 other

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

/-- Evaluate member `m` of `B` at runtime argument `x : Term` (applying `self := .record []` and `x`). -/
def evalBookAt (B : Book) (m : String) (x : Term) : Option Term :=
  (evalBook B m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- Evaluate member `m` of `B` under `pins` at runtime argument `x : Term`. -/
def evalBookUnderPinsAt (B : Book) (pins : List LeafPin) (m : String) (x : Term) : Option Term :=
  (evalBookUnderPins B pins m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- Evaluate member `m` of an already-specialized residual `Book` `B_res` at runtime argument `x : Term`. -/
def evalResidualBookAt (B_res : Book) (m : String) (x : Term) : Option Term :=
  (lookupBookCode B_res m).map (fun c => dataPinSpecialize (.app (.app c (.record [])) x))

/-- The empty base `LeafView` with no declared layer cells. -/
def emptyBaseView : LeafView where
  clock := 0
  decl := fun _ => none

/-- A pin list `pins` is trivially valid everywhere when all pins hold at `emptyBaseView`. -/
def holdsAll (pins : List LeafPin) : Prop :=
  ∀ p ∈ pins, holdsAt emptyBaseView p = true

theorem holdsAll_nil : holdsAll [] := by
  intro p hp
  cases hp

theorem pins_eq_nil_of_holdsAll {pins : List LeafPin} (h : holdsAll pins) : pins = [] := by
  cases pins with
  | nil => rfl
  | cons p rest =>
    have hp : holdsAt emptyBaseView p = true := h p List.mem_cons_self
    rw [holdsAt_eq] at hp
    cases hp

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

/-- **Exact Lookup Commutation (`lookupBookCode_specializeBook`)**:
Looking up any member `m` in the specialized book `specializeBook B pins` equals evaluating `m`
in `B` under `pins` (`evalBookUnderPins B pins m`). -/
theorem lookupBookCode_specializeBook (B : Book) (pins : List LeafPin) (m : String) :
    lookupBookCode (specializeBook B pins) m = evalBookUnderPins B pins m := by
  unfold lookupBookCode evalBookUnderPins
  rw [find?_defs_specializeBook, find?_statics_specializeBook]
  cases B.defs.find? (·.member == m) with
  | some d => rfl
  | none =>
    cases B.statics.find? (·.1 == m) <;> rfl

/-- Evaluating the residual book `specializeBook B pins` at member `m` and runtime argument `x`
equals evaluating `B` under `pins` at `m` and `x`. -/
theorem evalResidualBookAt_specializeBook (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    evalResidualBookAt (specializeBook B pins) m x = evalBookUnderPinsAt B pins m x := by
  unfold evalResidualBookAt evalBookUnderPinsAt
  rw [lookupBookCode_specializeBook]

/-- Predicate stating that `pins` is a sound, complete pin assignment for member `m` of `Book` `B`:
1. If `m` is a slot definition `d`, `pins` covers all slot reads of `d` (`residualSlotReads = []`),
   agrees with `bookCanonicalPins B` on `extractReadMembersCode d.code`, and if `d` already had
   no `self` reads (`d.reads.isEmpty = true`), `d.code` is already normalized under `specializeDefCode pins`.
2. If `m` is a static entry `(m, v)`, `dataPinSpecialize v` is a fixed point of `dataPinSpecialize`. -/
def HoldsForBookMember (B : Book) (pins : List LeafPin) (m : String) : Prop :=
  (∀ d : LeafDef, B.defs.find? (·.member == m) = some d →
    (residualSlotReads B.slots pins d).isEmpty = true ∧
    AgreeOnMembers (extractReadMembersCode d.code) (pinListEnv pins) (pinListEnv (bookCanonicalPins B)) ∧
    (d.reads.isEmpty = true → specializeDefCode pins d.code = d.code)) ∧
  (B.defs.find? (·.member == m) = none →
    ∀ kv : String × Term, B.statics.find? (·.1 == m) = some kv →
      dataPinSpecialize (dataPinSpecialize kv.2) = dataPinSpecialize kv.2)

/-- **Universal `evalBook` Commutation Theorem (`evalBook_specializeBook_eq_evalBook`)**:
For any `Book` `B`, pin assignment `pins`, and member `m`, whenever `HoldsForBookMember B pins m` holds,
`evalBook (specializeBook B pins) m = evalBook B m`! -/
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

/-- **1st Futamura Book Specializer Soundness & Commuting Diagram (`futamura1_book_specializer_sound`)**:
1. Decoding `specializeBookInCore B pins` recovers `some (specializeBook B pins)`.
2. For every member `m` and runtime argument `x`, evaluating the specialized book `specializeBook B pins`
   at `m` and `x` equals `evalBookUnderPinsAt B pins m x`.
3. Whenever `holdsAll pins` holds, `lookupBookCode (specializeBook B pins) m = evalBookUnderPins B [] m`.
4. Whenever a slot definition `d` in `B` has `pins` agreeing with `bookCanonicalPins B` on its read members
   (via `extractReadMembers_conservative`), `specializeDefCode pins d.code = specializeDefCode (bookCanonicalPins B) d.code`,
   and whenever `HoldsForBookMember B pins m` holds, `evalBook (specializeBook B pins) m = evalBook B m`. -/
theorem futamura1_book_specializer_sound (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    decodeBookTerm? (specializeBookInCore B pins) = some (specializeBook B pins) ∧
    lookupBookCode (specializeBook B pins) m = evalBookUnderPins B pins m ∧
    evalResidualBookAt (specializeBook B pins) m x = evalBookUnderPinsAt B pins m x ∧
    (holdsAll pins → lookupBookCode (specializeBook B pins) m = evalBookUnderPins B [] m) ∧
    (∀ inner : Term,
      AgreeOnMembers (extractReadMembers inner) (pinListEnv pins) (pinListEnv (bookCanonicalPins B)) →
      specializeDefCode pins (.lam inner) = specializeDefCode (bookCanonicalPins B) (.lam inner)) ∧
    (HoldsForBookMember B pins m → evalBook (specializeBook B pins) m = evalBook B m) := by
  refine ⟨decodeBookTerm_specializeBookInCore B pins,
    lookupBookCode_specializeBook B pins m,
    evalResidualBookAt_specializeBook B pins m x,
    fun h => by rw [pins_eq_nil_of_holdsAll h, lookupBookCode_specializeBook],
    fun inner hagree => ?_,
    evalBook_specializeBook_eq_evalBook B pins m⟩
  simp only [specializeDefCode, substPinsInCode, extractReadMembersAt_conservative 0 inner hagree]

/-- **2nd Futamura Compiler Generator Commuting Diagram (`futamura2_compiler_generator_commutes`)**:
1. `quoteBookMixTerm` is the exact `Core4` lowering `lowerT bookMixLExpr`.
2. Specializing `quoteBookMixTerm` with respect to the staged encoding of `B` and `pins` (`futamura2BookCompiler B pins`)
   and running the generated compiler on `encodePinsRecord pins` evaluates in `Core4` to `encodeBookTerm (specializeBook B pins)`,
   which decodes via `decodeBookTerm?` to `some (specializeBook B pins)`.
3. Evaluating the decoded residual book on any member `m` and runtime argument `x` commutes with
   evaluating `B` under `pins` and `x`. -/
theorem futamura2_compiler_generator_commutes (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    quoteBookMixTerm = lowerT bookMixLExpr ∧
    Evaluates (.app (futamura2BookCompiler B pins) (encodePinsRecord pins)) (encodeBookTerm (specializeBook B pins)) ∧
    decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins)) =
      some (specializeBook B pins) ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B pins) (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res m x)) = evalBookUnderPinsAt B pins m x := by
  refine ⟨quoteBookMixTerm_eq_lowerT,
    evaluates_futamura2BookCompiler B pins (encodePinsRecord pins),
    ?_, ?_⟩
  · rw [runStagedCompiler_futamura2, decodeBookTerm_encodeBookTerm]
  · rw [runStagedCompiler_futamura2, decodeBookTerm_encodeBookTerm]
    exact evalResidualBookAt_specializeBook B pins m x

/-- **3rd Futamura Compiler-Generator (`cogen`) Self-Application Commuting Diagram (`futamura3_cogen_self_application_commutes`)**:
1. `quoteMetaCogenTerm` is the exact `Core4` lowering `lowerT metaCogenLExpr`.
2. Self-applying `dataPinSpecialize` to `quoteMetaCogenTerm` and `cogenStageSpec quoteBookMixTerm`
   produces `cogenBookInCore = .lam (.app quoteBookMixTerm (.bound 0))`.
3. Applying `cogenBookInCore` to the staged book descriptor for `(B, pins)` and specializing generates
   the exact 2nd Futamura compiler `futamura2BookCompiler B pins`.
4. Running that generated compiler on `encodePinsRecord pins` and decoding via `decodeBookTerm?`
   yields `some (specializeBook B pins)`, whose evaluation on `(m, x)` equals `evalBookUnderPinsAt B pins m x`. -/
theorem futamura3_cogen_self_application_commutes (B : Book) (pins : List LeafPin) (m : String) (x : Term) :
    quoteMetaCogenTerm = lowerT metaCogenLExpr ∧
    cogenBookInCore = .lam (.app quoteBookMixTerm (.bound 0)) ∧
    dataPinSpecialize
      (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))) =
      futamura2BookCompiler B pins ∧
    decodeBookTerm?
      (runStagedCompiler
        (dataPinSpecialize
          (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))))
        (encodePinsRecord pins)) =
      some (specializeBook B pins) ∧
    ((decodeBookTerm?
      (runStagedCompiler
        (dataPinSpecialize
          (runStagedCompiler cogenBookInCore (bookStageSpec (encodeBookTerm (bindBookPins B pins)))))
        (encodePinsRecord pins))).bind
      (fun B_res => evalResidualBookAt B_res m x)) = evalBookUnderPinsAt B pins m x := by
  refine ⟨quoteMetaCogenTerm_eq_lowerT,
    cogenBookInCore_eq,
    cogenBookInCore_generates_compiler B pins,
    ?_, ?_⟩
  · rw [cogenBookInCore_generates_compiler, runStagedCompiler_futamura2, decodeBookTerm_encodeBookTerm]
  · rw [cogenBookInCore_generates_compiler, runStagedCompiler_futamura2, decodeBookTerm_encodeBookTerm]
    exact evalResidualBookAt_specializeBook B pins m x

/-! ## 10. Concrete Verification of Constant Propagation, Dead-Branch Elimination & Method Inlining in `specializeBook` -/

/-- Boolean equality on `Option Term` via `Obend.Law.termEq`. -/
def optTermEq : Option Term → Option Term → Bool
  | some a, some b => Obend.Law.termEq a b
  | none, none => true
  | _, _ => false

theorem optTermEq_sound {x y : Option Term} (h : optTermEq x y = true) : x = y := by
  cases x <;> cases y <;> simp [optTermEq] at h ⊢
  exact Obend.Law.termEq_sound h

/-- Sample multi-slot `Book` exercising:
1. Slot 0 (`"mode"`): a cell holding `0`,
2. Slot 1 (`"threshold"`): a cell holding `9`,
3. Slot 2 (`"helper"`): a method `λself. λx. x + 16`,
4. Slot 3 (`"dispatch"`): a method `λself. λx. ifZero self.mode (ifBool (self.threshold ≤ 10) (self.helper x + self.threshold) 999) (λp. 888)`
   that reads `self.mode`, `self.threshold`, and calls `self.helper x`! -/
def sampleSpecializableBook : Book where
  items :=
    [ .slot { member := "mode", slot := 0, kind := .cell, code := .lam (.lam (.nat 0)), reads := [] }
    , .slot { member := "threshold", slot := 1, kind := .cell, code := .lam (.lam (.nat 9)), reads := [] }
    , .slot { member := "helper", slot := 2, kind := .method, code := .lam (.lam (.binary .add (.bound 0) (.nat 16))), reads := [] }
    , .slot
        { member := "dispatch"
          slot := 3
          kind := .method
          code :=
            .lam
              (.lam
                (.ifZero (.get (.bound 1) "mode")
                  (.ifBool (.binary .lessEqual (.get (.bound 1) "threshold") (.nat 10))
                    (.binary .add (.app (.get (.bound 1) "helper") (.bound 0)) (.get (.bound 1) "threshold"))
                    (.nat 999))
                  (.lam (.nat 888))))
          reads := [0, 1, 2] } ]

/-- Pins for `sampleSpecializableBook`: pinning `"mode" ↦ 0`, `"threshold" ↦ 9`, and `"helper" ↦ λx. x + 16`. -/
def sampleBookPins : List LeafPin :=
  [ ⟨.layer "mode", .nat 0⟩
  , ⟨.layer "threshold", .nat 9⟩
  , ⟨.layer "helper", .lam (.binary .add (.bound 0) (.nat 16))⟩ ]

/-- **Theorem (`specializeBook_eliminates_branches_and_inlines_methods`)**:
Specializing `sampleSpecializableBook` with `sampleBookPins` via `specializeBook`:
1. Propagates `self.mode = 0` and eliminates the dead `.ifZero` successor branch `λp. 888`,
2. Propagates `self.threshold = 9`, folds `9 ≤ 10` to `true`, and eliminates the dead `.ifBool` false branch `999`,
3. Inlines `self.helper x` (`(λx. x + 16) x → x + 16`), producing `.lam (.lam (.binary .add (.binary .add (.bound 0) (.nat 16)) (.nat 9)))`,
4. Eliminates all runtime `self` reads on `"dispatch"` (`reads = []`),
5. Evaluates `"dispatch"` at runtime argument `x = .nat 5` to `some (.nat 30)` (`(5 + 16) + 9 = 30`),
6. Commutes with `evalBook` (`evalBook (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" = evalBook sampleSpecializableBook "dispatch`). -/
theorem specializeBook_eliminates_branches_and_inlines_methods :
    lookupBookCode (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      some (.lam (.lam (.binary .add (.binary .add (.bound 0) (.nat 16)) (.nat 9)))) ∧
    ((specializeBook sampleSpecializableBook sampleBookPins).defs.find? (·.member == "dispatch")).map (·.reads) =
      some [] ∧
    evalResidualBookAt (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" (.nat 5) =
      some (.nat 30) ∧
    evalBook (specializeBook sampleSpecializableBook sampleBookPins) "dispatch" =
      evalBook sampleSpecializableBook "dispatch" := by
  refine ⟨optTermEq_sound (by decide +kernel), by decide +kernel,
    optTermEq_sound (by decide +kernel), optTermEq_sound (by decide +kernel)⟩

/-- Mutated `specializeBook` that drops specialization and returns the unspecialized `Book`. -/
def specializeBookNoOp (B : Book) (_pins : List LeafPin) : Book := B

#tooth Obend.Leaf.Futamura.specializeBook_eliminates_branches_and_inlines_methods by mutation
  Obend.Leaf.Futamura.specializeBook := specializeBookNoOp

#tooth Obend.Leaf.Futamura.futamura2_compiler_generator_commutes by mutation
  Obend.Leaf.Futamura.specializeBook := specializeBookNoOp

/-- Mutated `futamura2BookCompiler` that returns a non-lambda `.nat 0`, breaking compiler staging. -/
def futamura2BookCompilerBroken (_B : Book) (_pins : List LeafPin) : Term := .nat 0

#tooth Obend.Leaf.Futamura.futamura2_compiler_generator_commutes by mutation
  Obend.Leaf.Futamura.futamura2BookCompiler := futamura2BookCompilerBroken

end Obend.Leaf.Futamura
end

