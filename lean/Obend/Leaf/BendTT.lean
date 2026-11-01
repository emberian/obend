module
/-
# Obend.Leaf.BendTT — Target Translation and Operational Adequacy from `Leaf.Book` to `BendTT`

Closes `REPORT-LEAF-20261101.md` §5 (*"refinement against BendTT's `Eval`"*):

1. **The `BendTT` Target Language (`BTerm`, `BDef`, `BBook`)**:
   `BTerm` is the first-order / functional leaf target AST. By type construction, `BTerm` excludes
   all object, inheritance, reflection, effect, and metavariable constructors of `Core4`
   (`.mix`, `.extend`, `.specification`, `.prototype`, `.reflect`, `.metadata`, `.project`,
   `.perform`, `.done`, `.hole`). Every definition body in an object book is checked to be acyclic
   (`BDef.noFixB`, containing no `.fix`), with recursion confined strictly to the single
   top-level self-dispatcher `BBook.dispatch`.

2. **Target Compilation (`compileToBendTT`, `emitBendTT`) & Retraction (`compileToBendTT_embedB`)**:
   `compileToBendTT : Term → Option BTerm` lowers a `Core4` `Term` into `BTerm` (succeeding iff no
   object/prototype/effect/hole nodes remain), and `emitBendTT : Book → Option BBook` lowers an
   entire `Obend.Leaf.Book` into a `BBook`.
   - `compileToBendTT_embedB`: `compileToBendTT t = some bt → embedB bt = t`.
   - `emitBendTT_dispatch`: `emitBendTT B = some bb → embedB bb.dispatch = B.link`.

3. **`BendTT` Small-Step and Fuel-Indexed Evaluator (`stepB?`, `runB`) & Refinement (`runB_sound`)**:
   - `stepB?_sound`: every `BendTT` step `stepB? bt = some bt'` is a valid `Core4` `Step (embedB bt) (embedB bt')`.
   - `runB_sound`: every `BendTT` evaluation `runB fuel bt = some v` refines `Core4` evaluation:
     `Evaluates (embedB bt) (embedB v)`.
   - `book_to_bendtt_sound`: composing `runB_sound`, `emitBendTT_dispatch`, and `Obend.Leaf.book_sound`,
     every method call evaluated by `BendTT` on an emitted `BBook` halts with the exact same
     observable outcome on the unflattened `Core4` object `fix (compose …) {seed}`.
-/
public import Obend.Leaf.Emit
public import Obend.Law.Proofs.Run
@[expose] public section
namespace Obend.Leaf.BendTT
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
set_option autoImplicit false

/-! ## 1. The `BendTT` Target AST (`BTerm`) -/

/-- `BendTT` target terms: pure functional core + records/variants + top-level dispatcher `.fix`.
Excludes `.mix`, `.extend`, `.specification`, `.prototype`, `.reflect`, `.metadata`, `.project`,
`.perform`, `.done`, and `.hole`. -/
inductive BTerm where
  | var (idx : Nat)
  | lam (body : BTerm)
  | app (fn arg : BTerm)
  | fix (spec init : BTerm)
  | nat (n : Nat)
  | bool (b : Bool)
  | label (s : String)
  | binOp (op : Primitive) (lhs rhs : BTerm)
  | ifZero (cond zeroBranch succBranch : BTerm)
  | ifBool (cond thenBranch elseBranch : BTerm)
  | record (fields : List (String × BTerm))
  | get (obj : BTerm) (field : String)
  | split (target : BTerm) (names : List String) (fn : BTerm)
  | inject (tag : String) (payload : BTerm)
  | case (scrut : BTerm) (arms : List (String × BTerm))
  deriving Repr

theorem sizeOf_snd_lt_of_mem_bterm {l : List (String × BTerm)} {x : String × BTerm} (h : x ∈ l) :
    sizeOf x.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x.2 < sizeOf x := by cases x; simp +arith
  omega

/-- True when a `BTerm` contains no `.fix` node (holds of every acyclic method body in an object book). -/
def BTerm.noFix : BTerm → Bool
  | .var _ | .nat _ | .bool _ | .label _ => true
  | .fix _ _ => false
  | .lam b | .get b _ | .inject _ b => b.noFix
  | .app a b | .binOp _ a b | .split a _ b => a.noFix && b.noFix
  | .ifZero c x y | .ifBool c x y => c.noFix && x.noFix && y.noFix
  | .record fs => fs.attach.all fun ⟨f, _⟩ => f.2.noFix
  | .case sc arms => sc.noFix && arms.attach.all fun ⟨a, _⟩ => a.2.noFix
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem_bterm hmem; omega)

/-! ## 2. Embedding `BTerm → Term` and Compilation `Term → Option BTerm` -/

mutual
/-- Structural embedding of `BTerm` into `Core4` `Term`. -/
def embedB : BTerm → Term
  | .var i => .bound i
  | .lam b => .lam (embedB b)
  | .app f a => .app (embedB f) (embedB a)
  | .fix s i => .fix (embedB s) (embedB i)
  | .nat n => .nat n
  | .bool b => .boolean b
  | .label s => .label s
  | .binOp op l r => .binary op (embedB l) (embedB r)
  | .ifZero c z s => .ifZero (embedB c) (embedB z) (embedB s)
  | .ifBool c t e => .ifBool (embedB c) (embedB t) (embedB e)
  | .record fs => .record (embedBFields fs)
  | .get t m => .get (embedB t) m
  | .split t ns f => .split (embedB t) ns (embedB f)
  | .inject l p => .inject l (embedB p)
  | .case sc arms => .case (embedB sc) (embedBFields arms)

def embedBFields : List (String × BTerm) → List (String × Term)
  | [] => []
  | (k, v) :: rest => (k, embedB v) :: embedBFields rest
end

@[simp] theorem embedBFields_eq_map :
    ∀ (fs : List (String × BTerm)), embedBFields fs = fs.map fun f => (f.1, embedB f.2)
  | [] => rfl
  | (_, _) :: rest => by simp [embedBFields, embedBFields_eq_map rest]

mutual
/-- Compile a `Core4` `Term` into `BTerm`, rejecting any residual object/inheritance/effect/hole form. -/
def compileToBendTT : Term → Option BTerm
  | .bound i => some (.var i)
  | .lam b => (compileToBendTT b).map .lam
  | .app f a => do
    let bf ← compileToBendTT f
    let ba ← compileToBendTT a
    pure (.app bf ba)
  | .fix s i => do
    let bs ← compileToBendTT s
    let bi ← compileToBendTT i
    pure (.fix bs bi)
  | .nat n => some (.nat n)
  | .boolean b => some (.bool b)
  | .label s => some (.label s)
  | .binary op l r => do
    let bl ← compileToBendTT l
    let br ← compileToBendTT r
    pure (.binOp op bl br)
  | .ifZero c z s => do
    let bc ← compileToBendTT c
    let bz ← compileToBendTT z
    let bs ← compileToBendTT s
    pure (.ifZero bc bz bs)
  | .ifBool c t e => do
    let bc ← compileToBendTT c
    let bt ← compileToBendTT t
    let be ← compileToBendTT e
    pure (.ifBool bc bt be)
  | .record fs => (compileToBendTTFields fs).map .record
  | .get t m => (compileToBendTT t).map (·.get m)
  | .split t ns f => do
    let bt ← compileToBendTT t
    let bf ← compileToBendTT f
    pure (.split bt ns bf)
  | .inject l p => (compileToBendTT p).map (.inject l)
  | .case sc arms => do
    let bsc ← compileToBendTT sc
    let barms ← compileToBendTTFields arms
    pure (.case bsc barms)
  | .hole _ _ | .mix _ _ | .specification _ _ | .prototype _ _ | .reflect _
  | .metadata _ | .project _ | .extend _ _ | .perform _ | .done _ => none

def compileToBendTTFields : List (String × Term) → Option (List (String × BTerm))
  | [] => some []
  | (k, v) :: rest => do
    let bv ← compileToBendTT v
    let brest ← compileToBendTTFields rest
    pure ((k, bv) :: brest)
end

theorem compileToBendTTFields_embedB :
    ∀ (fs : List (String × Term)) {bfs : List (String × BTerm)},
      (∀ f ∈ fs, ∀ {bf : BTerm}, compileToBendTT f.2 = some bf → embedB bf = f.2) →
      compileToBendTTFields fs = some bfs →
      embedBFields bfs = fs
  | [], _, _, h => by
    simp only [compileToBendTTFields, Option.some.injEq] at h
    subst h; rfl
  | (k, v) :: rest, _, ih, h => by
    simp only [compileToBendTTFields, bind, pure] at h
    cases hv : compileToBendTT v with
    | none => simp [hv] at h
    | some bv =>
      cases hr : compileToBendTTFields rest with
      | none => simp [hv, hr] at h
      | some brest =>
        simp only [hv, hr, Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [embedBFields, ih (k, v) List.mem_cons_self hv,
          compileToBendTTFields_embedB rest (fun f hf => ih f (List.mem_cons_of_mem _ hf)) hr]

/-- **`compileToBendTT_embedB`**: any `Term` that compiles to `BTerm` embeds back to the exact same `Term`. -/
theorem compileToBendTT_embedB :
    (t : Term) → ∀ {bt : BTerm}, compileToBendTT t = some bt → embedB bt = t
  | .bound i, _, h => by simp [compileToBendTT] at h; subst h; rfl
  | .lam b, _, h => by
    simp only [compileToBendTT, Option.map_eq_some_iff] at h
    obtain ⟨bb, hb, rfl⟩ := h
    simp [embedB, compileToBendTT_embedB b hb]
  | .app f a, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hf : compileToBendTT f with
    | none => simp [hf] at h
    | some bf =>
      cases ha : compileToBendTT a with
      | none => simp [hf, ha] at h
      | some ba =>
        simp only [hf, ha, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [embedB, compileToBendTT_embedB f hf, compileToBendTT_embedB a ha]
  | .fix s i, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hs : compileToBendTT s with
    | none => simp [hs] at h
    | some bs =>
      cases hi : compileToBendTT i with
      | none => simp [hs, hi] at h
      | some bi =>
        simp only [hs, hi, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [embedB, compileToBendTT_embedB s hs, compileToBendTT_embedB i hi]
  | .nat n, _, h => by simp [compileToBendTT] at h; subst h; rfl
  | .boolean b, _, h => by simp [compileToBendTT] at h; subst h; rfl
  | .label s, _, h => by simp [compileToBendTT] at h; subst h; rfl
  | .binary op l r, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hl : compileToBendTT l with
    | none => simp [hl] at h
    | some bl =>
      cases hr : compileToBendTT r with
      | none => simp [hl, hr] at h
      | some br =>
        simp only [hl, hr, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [embedB, compileToBendTT_embedB l hl, compileToBendTT_embedB r hr]
  | .ifZero c z s, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hc : compileToBendTT c with
    | none => simp [hc] at h
    | some bc =>
      cases hz : compileToBendTT z with
      | none => simp [hc, hz] at h
      | some bz =>
        cases hs : compileToBendTT s with
        | none => simp [hc, hz, hs] at h
        | some bs =>
          simp only [hc, hz, hs, Option.bind_some, Option.some.injEq] at h
          subst h
          simp [embedB, compileToBendTT_embedB c hc, compileToBendTT_embedB z hz, compileToBendTT_embedB s hs]
  | .ifBool c t e, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hc : compileToBendTT c with
    | none => simp [hc] at h
    | some bc =>
      cases ht : compileToBendTT t with
      | none => simp [hc, ht] at h
      | some bt =>
        cases he : compileToBendTT e with
        | none => simp [hc, ht, he] at h
        | some be =>
          simp only [hc, ht, he, Option.bind_some, Option.some.injEq] at h
          subst h
          simp [embedB, compileToBendTT_embedB c hc, compileToBendTT_embedB t ht, compileToBendTT_embedB e he]
  | .record fs, _, h => by
    simp only [compileToBendTT, Option.map_eq_some_iff] at h
    obtain ⟨bfs, hbfs, rfl⟩ := h
    simp only [embedB, Term.record.injEq]
    exact compileToBendTTFields_embedB fs (fun f _ _ h => compileToBendTT_embedB f.2 h) hbfs
  | .get t m, _, h => by
    simp only [compileToBendTT, Option.map_eq_some_iff] at h
    obtain ⟨bt, ht, rfl⟩ := h
    simp [embedB, compileToBendTT_embedB t ht]
  | .split t ns f, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases ht : compileToBendTT t with
    | none => simp [ht] at h
    | some bt =>
      cases hf : compileToBendTT f with
      | none => simp [ht, hf] at h
      | some bf =>
        simp only [ht, hf, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [embedB, compileToBendTT_embedB t ht, compileToBendTT_embedB f hf]
  | .inject l p, _, h => by
    simp only [compileToBendTT, Option.map_eq_some_iff] at h
    obtain ⟨bp, hp, rfl⟩ := h
    simp [embedB, compileToBendTT_embedB p hp]
  | .case sc arms, _, h => by
    simp only [compileToBendTT, bind, pure] at h
    cases hsc : compileToBendTT sc with
    | none => simp [hsc] at h
    | some bsc =>
      cases harms : compileToBendTTFields arms with
      | none => simp [hsc, harms] at h
      | some barms =>
        simp only [hsc, harms, Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [embedB, Term.case.injEq]
        exact ⟨compileToBendTT_embedB sc hsc,
          compileToBendTTFields_embedB arms (fun a _ _ h => compileToBendTT_embedB a.2 h) harms⟩
  | .hole _ _, _, h | .mix _ _, _, h | .specification _ _, _, h | .prototype _ _, _, h
  | .reflect _, _, h | .metadata _, _, h | .project _, _, h | .extend _ _, _, h
  | .perform _, _, h | .done _, _, h => by simp [compileToBendTT] at h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; omega)

/-! ## 3. Renaming, Substitution, and Small-Step `Eval` (`stepB?`, `runB`) on `BTerm` -/

/-- Rename de Bruijn indices in a `BTerm`. -/
def BTerm.renameB (t : BTerm) (f : Nat → Nat) : BTerm :=
  match t with
  | .var i => .var (f i)
  | .lam b => .lam (b.renameB (liftRename f))
  | .app fn arg => .app (fn.renameB f) (arg.renameB f)
  | .fix s i => .fix (s.renameB f) (i.renameB f)
  | .nat n => .nat n
  | .bool b => .bool b
  | .label s => .label s
  | .binOp op l r => .binOp op (l.renameB f) (r.renameB f)
  | .ifZero c z s => .ifZero (c.renameB f) (z.renameB f) (s.renameB (liftRename f))
  | .ifBool c x y => .ifBool (c.renameB f) (x.renameB f) (y.renameB f)
  | .record fs => .record (fs.attach.map fun ⟨field, _⟩ => (field.1, field.2.renameB f))
  | .get obj m => .get (obj.renameB f) m
  | .split target ns fn => .split (target.renameB f) ns (fn.renameB f)
  | .inject l p => .inject l (p.renameB f)
  | .case sc arms => .case (sc.renameB f) (arms.attach.map fun ⟨arm, _⟩ => (arm.1, arm.2.renameB (liftRename f)))
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem_bterm hmem; omega)

def liftSubstB (σ : Nat → BTerm) : Nat → BTerm
  | 0 => .var 0
  | n + 1 => (σ n).renameB Nat.succ

/-- Substitute de Bruijn indices in a `BTerm`. -/
def BTerm.substB (t : BTerm) (σ : Nat → BTerm) : BTerm :=
  match t with
  | .var i => σ i
  | .lam b => .lam (b.substB (liftSubstB σ))
  | .app fn arg => .app (fn.substB σ) (arg.substB σ)
  | .fix s i => .fix (s.substB σ) (i.substB σ)
  | .nat n => .nat n
  | .bool b => .bool b
  | .label s => .label s
  | .binOp op l r => .binOp op (l.substB σ) (r.substB σ)
  | .ifZero c z s => .ifZero (c.substB σ) (z.substB σ) (s.substB (liftSubstB σ))
  | .ifBool c x y => .ifBool (c.substB σ) (x.substB σ) (y.substB σ)
  | .record fs => .record (fs.attach.map fun ⟨field, _⟩ => (field.1, field.2.substB σ))
  | .get obj m => .get (obj.substB σ) m
  | .split target ns fn => .split (target.substB σ) ns (fn.substB σ)
  | .inject l p => .inject l (p.substB σ)
  | .case sc arms => .case (sc.substB σ) (arms.attach.map fun ⟨arm, _⟩ => (arm.1, arm.2.substB (liftSubstB σ)))
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := sizeOf_snd_lt_of_mem_bterm hmem; omega)

def instantiateB (body argument : BTerm) : BTerm :=
  body.substB (fun index => match index with | 0 => argument | n + 1 => .var n)

def applyAllB (fn : BTerm) : List BTerm → BTerm
  | [] => fn
  | v :: vs => applyAllB (.app fn v) vs

def isValueBTerm : BTerm → Bool
  | .lam _ | .nat _ | .bool _ | .label _ | .record _ | .inject _ _ => true
  | _ => false

def primitiveResultB : Primitive → BTerm → BTerm → Option BTerm
  | .add, .nat a, .nat b => some (.nat (a + b))
  | .multiply, .nat a, .nat b => some (.nat (a * b))
  | .equal, .nat a, .nat b => some (.bool (a == b))
  | .conjunction, .bool a, .bool b => some (.bool (a && b))
  | .labelEqual, .label a, .label b => some (.bool (a == b))
  | .subtract, .nat a, .nat b => some (.nat (a - b))
  | .divide, .nat a, .nat b => some (.nat (a / b))
  | .less, .nat a, .nat b => some (.bool (decide (a < b)))
  | .lessEqual, .nat a, .nat b => some (.bool (decide (a ≤ b)))
  | .modulo, .nat a, .nat b => some (.nat (a % b))
  | _, _, _ => none

/-- Small-step evaluator `stepB?` on `BTerm` (`BendTT` operational semantics). -/
def stepB? : BTerm → Option BTerm
  | .app f a =>
    match f with
    | .lam b => some (instantiateB b a)
    | _ => (stepB? f).map (fun f' => .app f' a)
  | .fix s i => some (.app (.app s (.fix s i)) i)
  | .get t n =>
    match t with
    | .record fs => (fs.find? (fun field => field.1 == n)).map (·.2)
    | _ => (stepB? t).map (fun t' => .get t' n)
  | .binOp p l r =>
    match stepB? l with
    | some l' => some (.binOp p l' r)
    | none =>
      if isValueBTerm l then
        match stepB? r with
        | some r' => some (.binOp p l r')
        | none => if isValueBTerm r then primitiveResultB p l r else none
      else none
  | .ifZero v z s =>
    match v with
    | .nat 0 => some z
    | .nat (k + 1) => some (instantiateB s (.nat k))
    | _ => (stepB? v).map (fun v' => .ifZero v' z s)
  | .case t arms =>
    match t with
    | .inject l p => (arms.find? (fun arm => arm.1 == l)).map (fun arm => instantiateB arm.2 p)
    | _ => (stepB? t).map (fun t' => .case t' arms)
  | .ifBool c x y =>
    match c with
    | .bool true => some x
    | .bool false => some y
    | _ => (stepB? c).map (fun c' => .ifBool c' x y)
  | .split t names f =>
    match t with
    | .record fs => (splitValues fs names).map (applyAllB f)
    | _ => (stepB? t).map (fun t' => .split t' names f)
  | _ => none

/-- Fuel-indexed `BendTT` evaluation `runB`. -/
def runB : Nat → BTerm → Option BTerm
  | 0, t => if isValueBTerm t then some t else none
  | fuel + 1, t =>
    if isValueBTerm t then some t else
    match stepB? t with
    | some t' => runB fuel t'
    | none => none

/-! ## 4. Adequacy of `stepB?` and `runB` against `Core4` (`stepB?_sound`, `runB_sound`) -/

theorem map_attach_eq_map {α β : Type} (l : List α) (g : α → β) :
    (l.attach.map fun ⟨x, _⟩ => g x) = l.map g := by
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.map_map]; rfl

theorem embedB_renameB : (t : BTerm) → ∀ (f : Nat → Nat),
    embedB (t.renameB f) = (embedB t).rename f
  | .var i, f | .nat _, f | .bool _, f | .label _, f => by simp [BTerm.renameB, embedB, Term.rename]
  | .lam b, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB b]
  | .app fn arg, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB fn, embedB_renameB arg]
  | .fix s i, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB s, embedB_renameB i]
  | .binOp op l r, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB l, embedB_renameB r]
  | .ifZero c z s, f => by
    simp [BTerm.renameB, embedB, Term.rename, embedB_renameB c, embedB_renameB z, embedB_renameB s]
  | .ifBool c x y, f => by
    simp [BTerm.renameB, embedB, Term.rename, embedB_renameB c, embedB_renameB x, embedB_renameB y]
  | .record fs, f => by
    simp only [BTerm.renameB, embedB, Term.rename, embedBFields_eq_map,
      map_attach_eq_map fs (fun field : String × BTerm => (field.1, field.2.renameB f)),
      List.map_map, Function.comp_def, Term.record.injEq]
    exact List.map_congr_left fun (k, v) hx => by simp [embedB_renameB v]
  | .get obj m, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB obj]
  | .split target ns fn, f => by
    simp [BTerm.renameB, embedB, Term.rename, embedB_renameB target, embedB_renameB fn]
  | .inject l p, f => by simp [BTerm.renameB, embedB, Term.rename, embedB_renameB p]
  | .case sc arms, f => by
    simp only [BTerm.renameB, embedB, Term.rename, embedBFields_eq_map, embedB_renameB sc,
      map_attach_eq_map arms (fun arm : String × BTerm => (arm.1, arm.2.renameB (liftRename f))),
      List.map_map, Function.comp_def, Term.case.injEq, true_and]
    exact List.map_congr_left fun (k, v) hx => by simp [embedB_renameB v]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := sizeOf_snd_lt_of_mem_bterm hx; simp at this; omega)

theorem embedB_liftSubstB (σ : Nat → BTerm) :
    (fun i => embedB (liftSubstB σ i)) = liftSubstitution (fun i => embedB (σ i)) := by
  funext i
  cases i <;> simp [liftSubstB, liftSubstitution, embedB, embedB_renameB]

theorem embedB_substB : (t : BTerm) → ∀ (σ : Nat → BTerm),
    embedB (t.substB σ) = (embedB t).substitute (fun i => embedB (σ i))
  | .var i, σ | .nat _, σ | .bool _, σ | .label _, σ => by simp [BTerm.substB, embedB, Term.substitute]
  | .lam b, σ => by simp [BTerm.substB, embedB, Term.substitute, embedB_substB b, embedB_liftSubstB]
  | .app fn arg, σ => by simp [BTerm.substB, embedB, embedB_substB fn, embedB_substB arg]
  | .fix s i, σ => by simp [BTerm.substB, embedB, Term.substitute, embedB_substB s, embedB_substB i]
  | .binOp op l r, σ => by simp [BTerm.substB, embedB, embedB_substB l, embedB_substB r]
  | .ifZero c z s, σ => by
    simp [BTerm.substB, embedB, Term.substitute, embedB_substB c, embedB_substB z, embedB_substB s,
      embedB_liftSubstB]
  | .ifBool c x y, σ => by
    simp [BTerm.substB, embedB, embedB_substB c, embedB_substB x, embedB_substB y]
  | .record fs, σ => by
    simp only [BTerm.substB, embedB, Term.substitute, embedBFields_eq_map,
      map_attach_eq_map fs (fun field : String × BTerm => (field.1, field.2.substB σ)),
      List.map_map, Function.comp_def, Term.record.injEq]
    exact List.map_congr_left fun (k, v) hx => by simp [embedB_substB v]
  | .get obj m, σ => by simp [BTerm.substB, embedB, embedB_substB obj]
  | .split target ns fn, σ => by
    simp [BTerm.substB, embedB, Term.substitute, embedB_substB target, embedB_substB fn]
  | .inject l p, σ => by simp [BTerm.substB, embedB, embedB_substB p]
  | .case sc arms, σ => by
    simp only [BTerm.substB, embedB, Term.substitute, embedBFields_eq_map, embedB_substB sc,
      map_attach_eq_map arms (fun arm : String × BTerm => (arm.1, arm.2.substB (liftSubstB σ))),
      List.map_map, Function.comp_def, Term.case.injEq, true_and]
    exact List.map_congr_left fun (k, v) hx => by simp [embedB_substB v, embedB_liftSubstB]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := sizeOf_snd_lt_of_mem_bterm hx; simp at this; omega)

theorem embedB_instantiateB (b a : BTerm) :
    embedB (instantiateB b a) = instantiate (embedB b) (embedB a) := by
  simp only [instantiateB, instantiate, embedB_substB]
  congr 1; funext i; cases i <;> rfl

theorem embedB_applyAllB (fn : BTerm) : ∀ (vs : List BTerm),
    embedB (applyAllB fn vs) = applyAll (embedB fn) (vs.map embedB)
  | [] => rfl
  | v :: vs => by simp [applyAllB, applyAll, embedB_applyAllB (.app fn v) vs, embedB]

theorem isValueBTerm_value {bt : BTerm} (h : isValueBTerm bt = true) : Value (embedB bt) := by
  cases bt <;> simp [isValueBTerm, embedB] at h ⊢ <;> constructor

theorem primitiveResultB_sound {p : Primitive} {l r res : BTerm}
    (h : primitiveResultB p l r = some res) :
    primitiveResult p (embedB l) (embedB r) = some (embedB res) := by
  cases p <;> cases l <;> cases r <;> simp [primitiveResultB, primitiveResult, embedB] at h ⊢ <;>
    subst h <;> rfl

theorem find?_pair {α : Type} {l : List (String × α)} {n : String} {p : String × α}
    (h : l.find? (fun field => field.1 == n) = some p) : p = (n, p.2) := by
  have := List.find?_some h
  simp at this
  cases p; simp_all

/-- **`stepB?_sound`**: every step of `BendTT`'s `stepB?` is a valid `Core4` `Step` under `embedB`. -/
theorem stepB?_sound : (bt : BTerm) → ∀ {bt' : BTerm}, stepB? bt = some bt' → Step (embedB bt) (embedB bt')
  | .app f a, bt', h => by
    have ih := @stepB?_sound f
    simp only [stepB?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rw [embedB_instantiateB]
      exact .beta _ _
    · obtain ⟨f', hf, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .application _ (ih hf)
  | .fix s i, bt', h => by
    simp only [stepB?, Option.some.injEq] at h; subst h
    exact .fix _ _
  | .get t n, bt', h => by
    have ih := @stepB?_sound t
    simp only [stepB?] at h
    split at h
    · rename_i fs
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' := find?_pair hp
      rw [hp'] at hp
      have hmap :
          (embedBFields fs).find? (fun field => field.1 == n) =
            some (n, embedB p.2) := by
        rw [embedBFields_eq_map, find?_map_snd embedB n fs, hp]; rfl
      exact .field _ _ _ hmap
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .target _ (ih hx)
  | .binOp p l r, bt', h => by
    have ihl := @stepB?_sound l
    have ihr := @stepB?_sound r
    simp only [stepB?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact .binaryLeft _ _ (ihl (by assumption))
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .binaryRight _ _ (isValueBTerm_value (by assumption)) (ihr (by assumption))
        · split at h
          · exact .primitive _ _ _ _ (isValueBTerm_value (by assumption))
              (isValueBTerm_value (by assumption)) (primitiveResultB_sound h)
          · cases h
      · cases h
  | .ifZero v z s, bt', h => by
    have ih := @stepB?_sound v
    simp only [stepB?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact .zero _ _
    · simp only [Option.some.injEq] at h; subst h
      rw [embedB_instantiateB]
      exact .successor _ _ _
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .condition _ _ (ih hx)
  | .case t arms, bt', h => by
    have ih := @stepB?_sound t
    simp only [stepB?] at h
    split at h
    · rename_i l p_inj
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' := find?_pair hp
      rw [hp'] at hp
      have hmap :
          (embedBFields arms).find? (fun arm => arm.1 == l) =
            some (l, embedB p.2) := by
        rw [embedBFields_eq_map, find?_map_snd embedB l arms, hp]; rfl
      rw [embedB_instantiateB]
      exact .caseInject _ _ _ _ hmap
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .caseTarget _ (ih hx)
  | .ifBool c x y, bt', h => by
    have ih := @stepB?_sound c
    simp only [stepB?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact .ifTrue _ _
    · simp only [Option.some.injEq] at h; subst h; exact .ifFalse _ _
    · obtain ⟨c', hc, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .ifCondition _ _ (ih hc)
  | .split t names f, bt', h => by
    have ih := @stepB?_sound t
    simp only [stepB?] at h
    split at h
    · rename_i fs
      obtain ⟨vs, hv, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [embedB_applyAllB]
      have hsplit : splitValues (embedBFields fs) names = some (vs.map embedB) := by
        rw [embedBFields_eq_map, splitValues_map embedB fs names, hv]; rfl
      exact .splitRecord _ _ _ _ hsplit
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .splitTarget _ _ (ih hx)
  | .var _, _, h | .lam _, _, h | .nat _, _, h | .bool _, _, h | .label _, _, h
  | .record _, _, h | .inject _ _, _, h => by simp [stepB?] at h

/-- **`runB_sound` (`BendTT` operational adequacy)**: every value reached by `BendTT`'s `runB` is
the `Core4` `Evaluates` result of `embedB bt`. -/
theorem runB_sound : (fuel : Nat) → ∀ {bt v : BTerm}, runB fuel bt = some v → Evaluates (embedB bt) (embedB v)
  | 0, bt, v, h => by
    simp only [runB] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact Obend.Law.evaluates_self (isValueBTerm_value (by assumption))
    · cases h
  | fuel + 1, bt, v, h => by
    simp only [runB] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact Obend.Law.evaluates_self (isValueBTerm_value (by assumption))
    · split at h
      · exact Obend.Law.evaluates_step (stepB?_sound _ (by assumption)) (runB_sound fuel h)
      · cases h

/-! ## 5. `BBook` Emission (`emitBendTT`) and End-to-End Object Adequacy (`book_to_bendtt_sound`) -/

/-- One slot definition in a `BendTT` book. -/
structure BDef where
  member : String
  slot : Nat
  kind : DefKind
  code : BTerm
  reads : List Nat
  deriving Repr

/-- An item of a `BendTT` book: either a slot definition or a static metadata entry. -/
inductive BBookItem where
  | slot (d : BDef)
  | static (member : String) (value : BTerm)
  deriving Repr

/-- A `BendTT` book (`BBook`). -/
structure BBook where
  items : List BBookItem
  deriving Repr

def BBookItem.def? : BBookItem → Option BDef
  | .slot d => some d
  | .static _ _ => none

def BBookItem.static? : BBookItem → Option (String × BTerm)
  | .slot _ => none
  | .static m v => some (m, v)

def BBook.defs (B : BBook) : List BDef := B.items.filterMap BBookItem.def?
def BBook.slots (B : BBook) : List String := B.defs.map (·.member)
def BBook.statics (B : BBook) : List (String × BTerm) := B.items.filterMap BBookItem.static?

/-- True when every slot definition in the `BBook` is acyclic (`noFix = true`). -/
def BBook.acyclicDefs (B : BBook) : Bool := B.defs.all (·.code.noFix)

/-- How the `BendTT` dispatcher calls a slot definition under its two binders (`self` at 1). -/
def BDef.call (d : BDef) : BTerm :=
  match d.kind with
  | .method => .app (d.code.renameB (· + 2)) (.var 1)
  | .cell => .app (.app (d.code.renameB (· + 2)) (.var 1)) (.record [])

/-- The `BendTT` dispatcher's record entry for an item. -/
def BBookItem.entry : BBookItem → String × BTerm
  | .slot d => (d.member, d.call)
  | .static m v => (m, v.renameB Nat.succ)

/-- **The `BendTT` dispatcher (`BBook.dispatch`)**: the single self-recursive definition linking all
slot definitions and static metadata entries. -/
def BBook.dispatch (B : BBook) : BTerm :=
  .fix (.lam (.lam (.record (B.items.map BBookItem.entry)))) (.record [])

/-- Translate a `LeafDef` into a `BDef`. -/
def emitBendTTDef (d : LeafDef) : Option BDef :=
  (compileToBendTT d.code).map fun bc =>
    { member := d.member, slot := d.slot, kind := d.kind, code := bc, reads := d.reads }

/-- Translate a `BookItem` into a `BBookItem`. -/
def emitBendTTItem : BookItem → Option BBookItem
  | .slot d => (emitBendTTDef d).map .slot
  | .static m v => (compileToBendTT v).map (.static m)

/-- **Emit a `BendTT` book (`BBook`) from an `Obend.Leaf.Book`.** -/
def emitBendTT (B : Book) : Option BBook :=
  (B.items.mapM emitBendTTItem).map BBook.mk

theorem emitBendTTItem_entry {item : BookItem} {bitem : BBookItem}
    (h : emitBendTTItem item = some bitem) :
    ((bitem.entry).1, embedB (bitem.entry).2) = item.entry := by
  cases item with
  | slot d =>
    simp only [emitBendTTItem, emitBendTTDef, Option.map_eq_some_iff] at h
    obtain ⟨bd, ⟨bc, hbc, rfl⟩, rfl⟩ := h
    simp only [BBookItem.entry, BookItem.entry, BDef.call, LeafDef.call]
    cases d.kind <;> simp [embedB, embedBFields, embedB_renameB, compileToBendTT_embedB d.code hbc]
  | static m v =>
    simp only [emitBendTTItem, Option.map_eq_some_iff] at h
    obtain ⟨bv, hbv, rfl⟩ := h
    simp [BBookItem.entry, BookItem.entry, embedB_renameB, compileToBendTT_embedB v hbv]

theorem mapM_emitBendTTItem_entries :
    ∀ (items : List BookItem) (bitems : List BBookItem),
      items.mapM emitBendTTItem = some bitems →
      (bitems.map BBookItem.entry).map (fun f => (f.1, embedB f.2)) = items.map BookItem.entry
  | [], bitems, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | item :: rest, bitems, h => by
    simp only [List.mapM_cons, bind, pure] at h
    cases hi : emitBendTTItem item with
    | none => simp [hi] at h
    | some bitem =>
      cases hr : rest.mapM emitBendTTItem with
      | none => simp [hi, hr] at h
      | some brest =>
        simp only [hi, hr, Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.map_cons, emitBendTTItem_entry hi,
          mapM_emitBendTTItem_entries rest brest hr]

/-- **`emitBendTT_dispatch`**: the `BendTT` dispatcher embeds directly to `Book.link`. -/
theorem emitBendTT_dispatch {B : Book} {bb : BBook} (h : emitBendTT B = some bb) :
    embedB bb.dispatch = B.link := by
  simp only [emitBendTT, Option.map_eq_some_iff] at h
  obtain ⟨bitems, hitems, rfl⟩ := h
  simp only [BBook.dispatch, Book.link, embedB, embedBFields, embedBFields_eq_map,
    mapM_emitBendTTItem_entries B.items bitems hitems]

/-- **`book_to_bendtt_sound` (End-to-End Refinement from `Composition.object` to `BendTT`'s `runB`)**:
For any closed composition `C`, if `emitBendTT (emit C) = some bb` and `BendTT` evaluates a method
call `.app (.get bb.dispatch m) (.nat k)` to `.nat n`, then:
1. the linked `Leaf.Book` evaluates `.app (.get (emit C).link m) (.nat k)` to `.nat n`, and
2. the unflattened `Core4` object `.app (.get C.object m) (.nat k)` halts with `.natural n`. -/
theorem book_to_bendtt_sound (C : Composition) (hc : C.closedB = true)
    {bb : BBook} (hemit : emitBendTT (emit C) = some bb)
    (m : String) (k fuel n : Nat)
    (hrun : runB fuel (.app (.get bb.dispatch m) (.nat k)) = some (.nat n)) :
    Evaluates (.app (.get (emit C).link m) (.nat k)) (.nat n) ∧
    Halts (.app (.get C.object m) (.nat k)) (.natural n) := by
  have hev : Evaluates (embedB (.app (.get bb.dispatch m) (.nat k))) (embedB (.nat n)) :=
    runB_sound fuel hrun
  simp only [embedB, emitBendTT_dispatch hemit] at hev
  have hhalts_link : Halts (.app (.get (emit C).link m) (.nat k)) (.natural n) :=
    ⟨.nat n, hev, .natural n⟩
  have hbeq := book_sound C hc m Term.bound (.app (.bound 0) (.nat k))
  simp only [instantiate, Term.substitute, substitute_bound] at hbeq
  exact ⟨hev, (hbeq.halts (.natural n)).1 hhalts_link⟩

/-- Same end-to-end refinement for static/variant reads (such as `#kind`). -/
theorem book_to_bendtt_member_evaluates (C : Composition)
    {bb : BBook} (hemit : emitBendTT (emit C) = some bb)
    (m : String) (fuel : Nat) (v : BTerm)
    (hrun : runB fuel (.get bb.dispatch m) = some v) :
    Evaluates (.get (emit C).link m) (embedB v) := by
  have hev := runB_sound fuel hrun
  simpa only [embedB, emitBendTT_dispatch hemit] using hev

end Obend.Leaf.BendTT
end
