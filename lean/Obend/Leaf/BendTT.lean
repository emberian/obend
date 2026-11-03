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
  | .bitAnd, .nat a, .nat b => some (.nat ((Obend.Core.Term.word64 a &&& Obend.Core.Term.word64 b).toNat))
  | .bitOr, .nat a, .nat b => some (.nat ((Obend.Core.Term.word64 a ||| Obend.Core.Term.word64 b).toNat))
  | .bitXor, .nat a, .nat b => some (.nat ((Obend.Core.Term.word64 a ^^^ Obend.Core.Term.word64 b).toNat))
  | .shl, .nat a, .nat b => some (.nat ((Obend.Core.Term.word64 a <<< ((Obend.Core.Term.word64 b).toNat % 64)).toNat))
  | .lshr, .nat a, .nat b => some (.nat ((Obend.Core.Term.word64 a >>> ((Obend.Core.Term.word64 b).toNat % 64)).toNat))
  | .ashr, .nat a, .nat b => some (.nat ((BitVec.sshiftRight (Obend.Core.Term.word64 a) ((Obend.Core.Term.word64 b).toNat % 64)).toNat))
  | .slt, .nat a, .nat b => some (.bool (BitVec.slt (Obend.Core.Term.word64 a) (Obend.Core.Term.word64 b)))
  | .qmul32, .nat a, .nat b => some (.nat ((Obend.Core.Term.qmul32Bv (Obend.Core.Term.word64 a) (Obend.Core.Term.word64 b)).toNat))
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

/-! ## 6. Affine Resource Discipline & Interaction-Net Port Wiring Validation (`countVarUses`, `isAffineBendTerm`, `affine_bendTerm_subst_preserves`) -/

open Obend.Core.Ty (Quantity safeQuantity)

/-- Canonical alias `BendTerm` for the `BendTT` target AST `BTerm`. -/
abbrev BendTerm := BTerm

@[simp] theorem renameB_record (fs : List (String × BendTerm)) (f : Nat → Nat) :
    (BTerm.record fs).renameB f = .record (fs.map fun field => (field.1, field.2.renameB f)) := by
  simp only [BTerm.renameB,
    map_attach_eq_map fs (fun field : String × BendTerm => (field.1, field.2.renameB f))]

@[simp] theorem renameB_case (sc : BendTerm) (arms : List (String × BendTerm)) (f : Nat → Nat) :
    (BTerm.case sc arms).renameB f =
      .case (sc.renameB f) (arms.map fun arm => (arm.1, arm.2.renameB (liftRename f))) := by
  simp only [BTerm.renameB,
    map_attach_eq_map arms (fun arm : String × BendTerm => (arm.1, arm.2.renameB (liftRename f)))]

@[simp] theorem substB_record (fs : List (String × BendTerm)) (σ : Nat → BendTerm) :
    (BTerm.record fs).substB σ = .record (fs.map fun field => (field.1, field.2.substB σ)) := by
  simp only [BTerm.substB,
    map_attach_eq_map fs (fun field : String × BendTerm => (field.1, field.2.substB σ))]

@[simp] theorem substB_case (sc : BendTerm) (arms : List (String × BendTerm)) (σ : Nat → BendTerm) :
    (BTerm.case sc arms).substB σ =
      .case (sc.substB σ) (arms.map fun arm => (arm.1, arm.2.substB (liftSubstB σ))) := by
  simp only [BTerm.substB,
    map_attach_eq_map arms (fun arm : String × BendTerm => (arm.1, arm.2.substB (liftSubstB σ)))]

mutual
/-- Count uses of de Bruijn variable `idx` in a `BendTerm`, using additive (`max`) counting across
mutually exclusive branch arms (`.ifZero`, `.ifBool`, `.case`) and multiplicative (`+`) counting
across simultaneous subterms (`.app`, `.fix`, `.binOp`, `.record`, `.split`), matching `Core4`'s
`addUses` and `joinUses` resource discipline. -/
def countVarUses (idx : Nat) : BendTerm → Nat
  | .var i => if i == idx then 1 else 0
  | .nat _ | .bool _ | .label _ => 0
  | .lam b => countVarUses (idx + 1) b
  | .app f a | .fix f a | .binOp _ f a | .split f _ a =>
    countVarUses idx f + countVarUses idx a
  | .get t _ | .inject _ t => countVarUses idx t
  | .ifZero c z s =>
    countVarUses idx c + Nat.max (countVarUses idx z) (countVarUses (idx + 1) s)
  | .ifBool c t e =>
    countVarUses idx c + Nat.max (countVarUses idx t) (countVarUses idx e)
  | .record fs => countFieldUses idx fs
  | .case sc arms => countVarUses idx sc + countArmUses idx arms

def countFieldUses (idx : Nat) : List (String × BendTerm) → Nat
  | [] => 0
  | (_, v) :: rest => countVarUses idx v + countFieldUses idx rest

def countArmUses (idx : Nat) : List (String × BendTerm) → Nat
  | [] => 0
  | (_, body) :: rest => Nat.max (countVarUses (idx + 1) body) (countArmUses idx rest)
end

/-- True when a recursive `.fix` specification has the required 2-port shape `.lam (.lam _)`
so that unfolding `.fix spec init ↦ .app (.app spec (.fix spec init)) init` saturates both
input ports (`self` and `init`) and preserves principal output port arity 1. -/
def isFixSpecPortBalanced : BendTerm → Bool
  | .lam (.lam _) => true
  | _ => false

theorem isFixSpecPortBalanced_substB {s : BendTerm} (σ : Nat → BendTerm)
    (h : isFixSpecPortBalanced s = true) :
    isFixSpecPortBalanced (s.substB σ) = true := by
  cases s with
  | lam b =>
    cases b <;> simp [isFixSpecPortBalanced, BTerm.substB] at h ⊢
  | _ => simp [isFixSpecPortBalanced] at h

mutual
/-- **Affine Resource & Interaction-Net Port-Wiring Checker (`isAffineBendTerm`)**:
Verifies that:
1. Every bound variable introduced by `.lam b`, `.ifZero c z s` (the successor binder in `s`),
   and `.case sc arms` (the payload binder in each arm) is used at most once (`countVarUses 0 … ≤ 1`)
   without implicit duplication, and
2. Every recursive `.fix spec init` node has a 2-port balanced specification (`isFixSpecPortBalanced spec`),
   ensuring that recursive unfolds `.fix spec init ↦ .app (.app spec (.fix spec init)) init` preserve port arity. -/
def isAffineBendTerm : BendTerm → Bool
  | .var _ | .nat _ | .bool _ | .label _ => true
  | .lam b => decide (countVarUses 0 b ≤ 1) && isAffineBendTerm b
  | .app f a | .binOp _ f a | .split f _ a =>
    isAffineBendTerm f && isAffineBendTerm a
  | .fix s i =>
    isFixSpecPortBalanced s && isAffineBendTerm s && isAffineBendTerm i
  | .get t _ | .inject _ t => isAffineBendTerm t
  | .ifZero c z s =>
    decide (countVarUses 0 s ≤ 1) && isAffineBendTerm c && isAffineBendTerm z && isAffineBendTerm s
  | .ifBool c t e =>
    isAffineBendTerm c && isAffineBendTerm t && isAffineBendTerm e
  | .record fs => isAffineBendTermFields fs
  | .case sc arms => isAffineBendTerm sc && isAffineBendTermArms arms

def isAffineBendTermFields : List (String × BendTerm) → Bool
  | [] => true
  | (_, v) :: rest => isAffineBendTerm v && isAffineBendTermFields rest

def isAffineBendTermArms : List (String × BendTerm) → Bool
  | [] => true
  | (_, body) :: rest =>
    decide (countVarUses 0 body ≤ 1) && isAffineBendTerm body && isAffineBendTermArms rest
end

mutual
/-- True when all free de Bruijn variables in a `BendTerm` have index `< d`. -/
def closedAtB (d : Nat) : BendTerm → Bool
  | .var i => decide (i < d)
  | .nat _ | .bool _ | .label _ => true
  | .lam b => closedAtB (d + 1) b
  | .app f a | .fix f a | .binOp _ f a | .split f _ a =>
    closedAtB d f && closedAtB d a
  | .get t _ | .inject _ t => closedAtB d t
  | .ifZero c z s =>
    closedAtB d c && closedAtB d z && closedAtB (d + 1) s
  | .ifBool c t e =>
    closedAtB d c && closedAtB d t && closedAtB d e
  | .record fs => closedAtBFields d fs
  | .case sc arms => closedAtB d sc && closedAtBArms d arms

def closedAtBFields (d : Nat) : List (String × BendTerm) → Bool
  | [] => true
  | (_, v) :: rest => closedAtB d v && closedAtBFields d rest

def closedAtBArms (d : Nat) : List (String × BendTerm) → Bool
  | [] => true
  | (_, body) :: rest => closedAtB (d + 1) body && closedAtBArms d rest
end

mutual
theorem closedAtB_renameB_id :
    (t : BendTerm) → ∀ {d : Nat} {f : Nat → Nat},
      closedAtB d t = true → (∀ i < d, f i = i) → t.renameB f = t
  | .var i, _, f, hc, hf => by
    simp only [closedAtB, decide_eq_true_eq] at hc
    simp [BTerm.renameB, hf i hc]
  | .nat _, _, _, _, _ | .bool _, _, _, _, _ | .label _, _, _, _, _ => by
    simp [BTerm.renameB]
  | .lam b, d, f, hc, hf => by
    simp only [closedAtB] at hc
    have hf' : ∀ i < d + 1, liftRename f i = i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ k => simp [liftRename, hf k (by omega)]
    simp [BTerm.renameB, closedAtB_renameB_id b hc hf']
  | .app fn arg, _, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [BTerm.renameB, closedAtB_renameB_id fn hc.1 hf, closedAtB_renameB_id arg hc.2 hf]
  | .fix s i, _, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [BTerm.renameB, closedAtB_renameB_id s hc.1 hf, closedAtB_renameB_id i hc.2 hf]
  | .binOp op l r, _, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [BTerm.renameB, closedAtB_renameB_id l hc.1 hf, closedAtB_renameB_id r hc.2 hf]
  | .get obj m, _, f, hc, hf => by
    simp only [closedAtB] at hc
    simp [BTerm.renameB, closedAtB_renameB_id obj hc hf]
  | .inject l p, _, f, hc, hf => by
    simp only [closedAtB] at hc
    simp [BTerm.renameB, closedAtB_renameB_id p hc hf]
  | .split target ns fn, _, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [BTerm.renameB, closedAtB_renameB_id target hc.1 hf, closedAtB_renameB_id fn hc.2 hf]
  | .ifZero c z s, d, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    have hf' : ∀ i < d + 1, liftRename f i = i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ k => simp [liftRename, hf k (by omega)]
    simp [BTerm.renameB, closedAtB_renameB_id c hc.1.1 hf,
      closedAtB_renameB_id z hc.1.2 hf, closedAtB_renameB_id s hc.2 hf']
  | .ifBool c x y, _, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [BTerm.renameB, closedAtB_renameB_id c hc.1.1 hf,
      closedAtB_renameB_id x hc.1.2 hf, closedAtB_renameB_id y hc.2 hf]
  | .record fs, _, f, hc, hf => by
    simp only [closedAtB] at hc
    simp only [renameB_record, BTerm.record.injEq]
    exact closedAtBFields_renameB_id fs hc hf
  | .case sc arms, d, f, hc, hf => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    have hf' : ∀ i < d + 1, liftRename f i = i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ k => simp [liftRename, hf k (by omega)]
    simp only [renameB_case, BTerm.case.injEq]
    exact ⟨closedAtB_renameB_id sc hc.1 hf, closedAtBArms_renameB_id arms hc.2 hf'⟩

theorem closedAtBFields_renameB_id :
    (fs : List (String × BendTerm)) → ∀ {d : Nat} {f : Nat → Nat},
      closedAtBFields d fs = true → (∀ i < d, f i = i) →
      (fs.map fun field => (field.1, field.2.renameB f)) = fs
  | [], _, _, _, _ => rfl
  | (k, v) :: rest, _, f, hc, hf => by
    simp only [closedAtBFields, Bool.and_eq_true] at hc
    simp [closedAtB_renameB_id v hc.1 hf, closedAtBFields_renameB_id rest hc.2 hf]

theorem closedAtBArms_renameB_id :
    (arms : List (String × BendTerm)) → ∀ {d : Nat} {f : Nat → Nat},
      closedAtBArms d arms = true → (∀ i < d + 1, f i = i) →
      (arms.map fun arm => (arm.1, arm.2.renameB f)) = arms
  | [], _, _, _, _ => rfl
  | (k, v) :: rest, _, f, hc, hf => by
    simp only [closedAtBArms, Bool.and_eq_true] at hc
    simp [closedAtB_renameB_id v hc.1 hf, closedAtBArms_renameB_id rest hc.2 hf]
end

theorem closedAtB_zero_renameB (t : BendTerm) (f : Nat → Nat) (hc : closedAtB 0 t = true) :
    t.renameB f = t :=
  closedAtB_renameB_id t hc (fun i hi => by omega)

mutual
theorem countVarUses_eq_zero_of_closedAtB :
    (t : BendTerm) → ∀ {d idx : Nat},
      closedAtB d t = true → d ≤ idx → countVarUses idx t = 0
  | .var i, _, idx, hc, hle => by
    simp only [closedAtB, decide_eq_true_eq] at hc
    have hne : (i == idx) = false := beq_false_of_ne (by omega)
    simp [countVarUses, hne]
  | .nat _, _, _, _, _ | .bool _, _, _, _, _ | .label _, _, _, _, _ => by
    simp [countVarUses]
  | .lam b, d, idx, hc, hle => by
    simp only [closedAtB] at hc
    have hle' : d + 1 ≤ idx + 1 := by omega
    simpa [countVarUses] using countVarUses_eq_zero_of_closedAtB b hc hle'
  | .app f a, _, idx, hc, hle | .fix f a, _, idx, hc, hle
  | .binOp _ f a, _, idx, hc, hle | .split f _ a, _, idx, hc, hle => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [countVarUses, countVarUses_eq_zero_of_closedAtB f hc.1 hle,
      countVarUses_eq_zero_of_closedAtB a hc.2 hle]
  | .get obj _, _, idx, hc, hle | .inject _ obj, _, idx, hc, hle => by
    simp only [closedAtB] at hc
    simpa [countVarUses] using countVarUses_eq_zero_of_closedAtB obj hc hle
  | .ifZero c z s, d, idx, hc, hle => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    have hle' : d + 1 ≤ idx + 1 := by omega
    simp [countVarUses, countVarUses_eq_zero_of_closedAtB c hc.1.1 hle,
      countVarUses_eq_zero_of_closedAtB z hc.1.2 hle,
      countVarUses_eq_zero_of_closedAtB s hc.2 hle']
  | .ifBool c x y, _, idx, hc, hle => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [countVarUses, countVarUses_eq_zero_of_closedAtB c hc.1.1 hle,
      countVarUses_eq_zero_of_closedAtB x hc.1.2 hle,
      countVarUses_eq_zero_of_closedAtB y hc.2 hle]
  | .record fs, _, idx, hc, hle => by
    simp only [closedAtB, countVarUses] at hc ⊢
    exact countFieldUses_eq_zero_of_closedAtB fs hc hle
  | .case sc arms, _, idx, hc, hle => by
    simp only [closedAtB, Bool.and_eq_true] at hc
    simp [countVarUses, countVarUses_eq_zero_of_closedAtB sc hc.1 hle,
      countArmUses_eq_zero_of_closedAtB arms hc.2 hle]

theorem countFieldUses_eq_zero_of_closedAtB :
    (fs : List (String × BendTerm)) → ∀ {d idx : Nat},
      closedAtBFields d fs = true → d ≤ idx → countFieldUses idx fs = 0
  | [], _, _, _, _ => rfl
  | (_, v) :: rest, _, idx, hc, hle => by
    simp only [closedAtBFields, Bool.and_eq_true] at hc
    simp [countFieldUses, countVarUses_eq_zero_of_closedAtB v hc.1 hle,
      countFieldUses_eq_zero_of_closedAtB rest hc.2 hle]

theorem countArmUses_eq_zero_of_closedAtB :
    (arms : List (String × BendTerm)) → ∀ {d idx : Nat},
      closedAtBArms d arms = true → d ≤ idx → countArmUses idx arms = 0
  | [], _, _, _, _ => rfl
  | (_, v) :: rest, d, idx, hc, hle => by
    simp only [closedAtBArms, Bool.and_eq_true] at hc
    have hle' : d + 1 ≤ idx + 1 := by omega
    simp [countArmUses, countVarUses_eq_zero_of_closedAtB v hc.1 hle',
      countArmUses_eq_zero_of_closedAtB rest hc.2 hle]
end

/-- Substitution invariant at binder depth `d`: variables `< d` are identity-mapped, while
variables `≥ d` map either to variables `≥ d` or to closed affine `BendTerm`s. -/
def SubstPreservesBelow (d : Nat) (σ : Nat → BendTerm) : Prop :=
  ∀ k,
    (k < d → σ k = .var k) ∧
    (d ≤ k →
      (∃ k', d ≤ k' ∧ σ k = .var k') ∨
      (closedAtB 0 (σ k) = true ∧ isAffineBendTerm (σ k) = true))

theorem SubstPreservesBelow.lift {d : Nat} {σ : Nat → BendTerm}
    (h : SubstPreservesBelow d σ) :
    SubstPreservesBelow (d + 1) (liftSubstB σ) := by
  intro k
  cases k with
  | zero =>
    refine ⟨fun _ => rfl, fun hle => False.elim (Nat.not_succ_le_zero d hle)⟩
  | succ i =>
    refine ⟨fun hlt => ?_, fun hle => ?_⟩
    · have hi : σ i = .var i := (h i).1 (Nat.lt_of_succ_lt_succ hlt)
      simp only [liftSubstB, hi, BTerm.renameB]
    · rcases (h i).2 (Nat.le_of_succ_le_succ hle) with ⟨k', hk', hi⟩ | ⟨hc, haff⟩
      · left
        refine ⟨k' + 1, Nat.succ_le_succ hk', ?_⟩
        simp only [liftSubstB, hi, BTerm.renameB]
      · right
        have hren : (σ i).renameB Nat.succ = σ i := closedAtB_zero_renameB (σ i) Nat.succ hc
        simp only [liftSubstB, hren]
        exact ⟨hc, haff⟩

theorem countVarUses_substPreservesBelow_var {d idx : Nat} {σ : Nat → BendTerm}
    (hσ : SubstPreservesBelow d σ) (hidx : idx < d) (k : Nat) :
    countVarUses idx (σ k) ≤ countVarUses idx (.var k) := by
  cases Nat.lt_or_ge k d with
  | inl hk =>
    rw [(hσ k).1 hk]
    exact Nat.le_refl _
  | inr hle =>
    rcases (hσ k).2 hle with ⟨k', hk', heq⟩ | ⟨hc, _⟩
    · rw [heq]
      have hne : (k' == idx) = false := beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hidx hk'))
      simp [countVarUses, hne]
    · have hz : countVarUses idx (σ k) = 0 :=
        countVarUses_eq_zero_of_closedAtB (σ k) hc (Nat.zero_le idx)
      rw [hz]
      exact Nat.zero_le _

theorem max_le_max_of_le {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.max a b ≤ Nat.max a' b' :=
  Nat.max_le.2 ⟨Nat.le_trans ha (Nat.le_max_left a' b'), Nat.le_trans hb (Nat.le_max_right a' b')⟩

theorem add_max_le_add_max {a a' b b' c c' : Nat} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    a + Nat.max b c ≤ a' + Nat.max b' c' :=
  Nat.add_le_add ha (max_le_max_of_le hb hc)

mutual
theorem countVarUses_substB_le :
    (t : BendTerm) → ∀ {d idx : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ → idx < d →
      countVarUses idx (t.substB σ) ≤ countVarUses idx t
  | .var k, _, _, _, hσ, hidx => by
    simpa [BTerm.substB] using countVarUses_substPreservesBelow_var hσ hidx k
  | .nat _, _, _, _, _, _ | .bool _, _, _, _, _, _ | .label _, _, _, _, _, _ => by
    simp [BTerm.substB, countVarUses]
  | .lam b, _, idx, σ, hσ, hidx => by
    simp only [BTerm.substB, countVarUses]
    exact countVarUses_substB_le b hσ.lift (Nat.succ_lt_succ hidx)
  | .app f a, _, idx, σ, hσ, hidx | .fix f a, _, idx, σ, hσ, hidx
  | .binOp _ f a, _, idx, σ, hσ, hidx | .split f _ a, _, idx, σ, hσ, hidx => by
    simp only [BTerm.substB, countVarUses]
    exact Nat.add_le_add (countVarUses_substB_le f hσ hidx) (countVarUses_substB_le a hσ hidx)
  | .get obj _, _, idx, σ, hσ, hidx | .inject _ obj, _, idx, σ, hσ, hidx => by
    simp only [BTerm.substB, countVarUses]
    exact countVarUses_substB_le obj hσ hidx
  | .ifZero c z s, _, idx, σ, hσ, hidx => by
    simp only [BTerm.substB, countVarUses]
    exact add_max_le_add_max
      (countVarUses_substB_le c hσ hidx)
      (countVarUses_substB_le z hσ hidx)
      (countVarUses_substB_le s hσ.lift (Nat.succ_lt_succ hidx))
  | .ifBool c x y, _, idx, σ, hσ, hidx => by
    simp only [BTerm.substB, countVarUses]
    exact add_max_le_add_max
      (countVarUses_substB_le c hσ hidx)
      (countVarUses_substB_le x hσ hidx)
      (countVarUses_substB_le y hσ hidx)
  | .record fs, _, idx, σ, hσ, hidx => by
    simp only [substB_record, countVarUses]
    exact countFieldUses_substB_le fs hσ hidx
  | .case sc arms, _, idx, σ, hσ, hidx => by
    simp only [substB_case, countVarUses]
    exact Nat.add_le_add
      (countVarUses_substB_le sc hσ hidx)
      (countArmUses_substB_le arms hσ hidx)

theorem countFieldUses_substB_le :
    (fs : List (String × BendTerm)) → ∀ {d idx : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ → idx < d →
      countFieldUses idx (fs.map fun field => (field.1, field.2.substB σ)) ≤
        countFieldUses idx fs
  | [], _, _, _, _, _ => Nat.le_refl 0
  | (_, v) :: rest, _, _, _, hσ, hidx => by
    simp only [List.map_cons, countFieldUses]
    exact Nat.add_le_add
      (countVarUses_substB_le v hσ hidx)
      (countFieldUses_substB_le rest hσ hidx)

theorem countArmUses_substB_le :
    (arms : List (String × BendTerm)) → ∀ {d idx : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ → idx < d →
      countArmUses idx (arms.map fun arm => (arm.1, arm.2.substB (liftSubstB σ))) ≤
        countArmUses idx arms
  | [], _, _, _, _, _ => Nat.le_refl 0
  | (_, v) :: rest, _, _, _, hσ, hidx => by
    simp only [List.map_cons, countArmUses]
    exact max_le_max_of_le
      (countVarUses_substB_le v hσ.lift (Nat.succ_lt_succ hidx))
      (countArmUses_substB_le rest hσ hidx)
end

mutual
theorem isAffineBendTerm_substB :
    (t : BendTerm) → ∀ {d : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ →
      isAffineBendTerm t = true →
      isAffineBendTerm (t.substB σ) = true
  | .var k, d, σ, hσ, _ => by
    simp only [BTerm.substB]
    cases Nat.lt_or_ge k d with
    | inl hk =>
      rw [(hσ k).1 hk]; rfl
    | inr hle =>
      rcases (hσ k).2 hle with ⟨k', _, heq⟩ | ⟨_, haff⟩
      · rw [heq]; rfl
      · exact haff
  | .nat _, _, _, _, _ | .bool _, _, _, _, _ | .label _, _, _, _, _ => by
    simp [BTerm.substB, isAffineBendTerm]
  | .lam b, d, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true, decide_eq_true_eq] at haff
    simp only [BTerm.substB, isAffineBendTerm, Bool.and_eq_true, decide_eq_true_eq]
    have hle := countVarUses_substB_le b hσ.lift (Nat.zero_lt_succ d)
    exact ⟨Nat.le_trans hle haff.1, isAffineBendTerm_substB b hσ.lift haff.2⟩
  | .app f a, _, σ, hσ, haff | .binOp _ f a, _, σ, hσ, haff | .split f _ a, _, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true] at haff
    simp only [BTerm.substB, isAffineBendTerm, Bool.and_eq_true]
    exact ⟨isAffineBendTerm_substB f hσ haff.1, isAffineBendTerm_substB a hσ haff.2⟩
  | .fix s i, _, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true] at haff
    simp only [BTerm.substB, isAffineBendTerm, Bool.and_eq_true]
    exact ⟨⟨isFixSpecPortBalanced_substB σ haff.1.1, isAffineBendTerm_substB s hσ haff.1.2⟩,
      isAffineBendTerm_substB i hσ haff.2⟩
  | .get obj _, _, σ, hσ, haff | .inject _ obj, _, σ, hσ, haff => by
    simp only [isAffineBendTerm] at haff
    simp only [BTerm.substB, isAffineBendTerm]
    exact isAffineBendTerm_substB obj hσ haff
  | .ifZero c z s, d, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true, decide_eq_true_eq] at haff
    simp only [BTerm.substB, isAffineBendTerm, Bool.and_eq_true, decide_eq_true_eq]
    have hle := countVarUses_substB_le s hσ.lift (Nat.zero_lt_succ d)
    exact ⟨⟨⟨Nat.le_trans hle haff.1.1.1, isAffineBendTerm_substB c hσ haff.1.1.2⟩,
      isAffineBendTerm_substB z hσ haff.1.2⟩,
      isAffineBendTerm_substB s hσ.lift haff.2⟩
  | .ifBool c x y, _, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true] at haff
    simp only [BTerm.substB, isAffineBendTerm, Bool.and_eq_true]
    exact ⟨⟨isAffineBendTerm_substB c hσ haff.1.1, isAffineBendTerm_substB x hσ haff.1.2⟩,
      isAffineBendTerm_substB y hσ haff.2⟩
  | .record fs, _, σ, hσ, haff => by
    simp only [isAffineBendTerm, substB_record] at haff ⊢
    exact isAffineBendTermFields_substB fs hσ haff
  | .case sc arms, _, σ, hσ, haff => by
    simp only [isAffineBendTerm, Bool.and_eq_true] at haff
    simp only [substB_case, isAffineBendTerm, Bool.and_eq_true]
    exact ⟨isAffineBendTerm_substB sc hσ haff.1, isAffineBendTermArms_substB arms hσ haff.2⟩

theorem isAffineBendTermFields_substB :
    (fs : List (String × BendTerm)) → ∀ {d : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ →
      isAffineBendTermFields fs = true →
      isAffineBendTermFields (fs.map fun field => (field.1, field.2.substB σ)) = true
  | [], _, _, _, _ => rfl
  | (_, v) :: rest, _, _, hσ, haff => by
    simp only [isAffineBendTermFields, Bool.and_eq_true] at haff
    simp only [List.map_cons, isAffineBendTermFields, Bool.and_eq_true]
    exact ⟨isAffineBendTerm_substB v hσ haff.1, isAffineBendTermFields_substB rest hσ haff.2⟩

theorem isAffineBendTermArms_substB :
    (arms : List (String × BendTerm)) → ∀ {d : Nat} {σ : Nat → BendTerm},
      SubstPreservesBelow d σ →
      isAffineBendTermArms arms = true →
      isAffineBendTermArms (arms.map fun arm => (arm.1, arm.2.substB (liftSubstB σ))) = true
  | [], _, _, _, _ => rfl
  | (_, v) :: rest, d, _, hσ, harms => by
    simp only [isAffineBendTermArms, Bool.and_eq_true, decide_eq_true_eq] at harms
    simp only [List.map_cons, isAffineBendTermArms, Bool.and_eq_true, decide_eq_true_eq]
    have hle := countVarUses_substB_le v hσ.lift (Nat.zero_lt_succ d)
    exact ⟨⟨Nat.le_trans hle harms.1.1, isAffineBendTerm_substB v hσ.lift harms.1.2⟩,
      isAffineBendTermArms_substB rest hσ harms.2⟩
end

theorem substPreservesBelow_instantiate (arg : BendTerm)
    (hclosed : closedAtB 0 arg = true) (haff : isAffineBendTerm arg = true) :
    SubstPreservesBelow 0 (fun index => match index with | 0 => arg | n + 1 => .var n) := by
  intro k
  refine ⟨fun hlt => False.elim (Nat.not_lt_zero k hlt), fun _ => ?_⟩
  cases k with
  | zero => exact .inr ⟨hclosed, haff⟩
  | succ n => exact .inl ⟨n, Nat.zero_le n, rfl⟩

/-- **`affine_bendTerm_subst_preserves`**:
Substituting any closed affine `BendTerm` `arg` (`closedAtB 0 arg = true`, `isAffineBendTerm arg = true`)
into any affine `BendTerm` `body` (`isAffineBendTerm body = true`) via `instantiateB` preserves
both the affine resource discipline (`countVarUses 0 ≤ 1` at every binder) and `.fix` port-wiring balance! -/
theorem affine_bendTerm_subst_preserves (body arg : BendTerm)
    (hbody : isAffineBendTerm body = true)
    (harg : isAffineBendTerm arg = true)
    (hclosed : closedAtB 0 arg = true) :
    isAffineBendTerm (instantiateB body arg) = true :=
  isAffineBendTerm_substB body (substPreservesBelow_instantiate arg hclosed harg) hbody

/-- **`affine_bendTerm_fix_unfold_preserves`**:
For any affine recursive node `.fix s i` (`isAffineBendTerm (.fix s i) = true`):
1. `s` is 2-port balanced (`isFixSpecPortBalanced s = true`, i.e., `∃ body, s = .lam (.lam body)`),
2. The 1-step unfold `stepB? (.fix s i) = some (.app (.app s (.fix s i)) i)` preserves `isAffineBendTerm`, and
3. When `.fix (.lam (.lam body)) i` is closed (`closedAtB 0 (.fix (.lam (.lam body)) i) = true`),
   saturating both `self` and `init` ports via β-reduction preserves `isAffineBendTerm`! -/
theorem affine_bendTerm_fix_unfold_preserves (s i : BendTerm)
    (hfix : isAffineBendTerm (.fix s i) = true) :
    isFixSpecPortBalanced s = true ∧
    (∃ body, s = .lam (.lam body)) ∧
    isAffineBendTerm (.app (.app s (.fix s i)) i) = true ∧
    (∀ body, s = .lam (.lam body) → closedAtB 0 (.fix s i) = true →
      isAffineBendTerm (instantiateB (.lam body) (.fix s i)) = true) := by
  have hfix' := hfix
  simp only [isAffineBendTerm, Bool.and_eq_true] at hfix'
  obtain ⟨⟨hbal, hs⟩, hi⟩ := hfix'
  have hshape : ∃ body, s = .lam (.lam body) := by
    cases s with
    | lam b =>
      cases b with
      | lam body => exact ⟨body, rfl⟩
      | _ => simp [isFixSpecPortBalanced] at hbal
    | _ => simp [isFixSpecPortBalanced] at hbal
  refine ⟨hbal, hshape, ?_, ?_⟩
  · simp only [isAffineBendTerm, Bool.and_eq_true]
    exact ⟨⟨hs, ⟨⟨hbal, hs⟩, hi⟩⟩, hi⟩
  · intro body hseq hclosed
    have hlam1 : isAffineBendTerm (.lam body) = true := by
      rw [hseq] at hs
      simp only [isAffineBendTerm, Bool.and_eq_true] at hs ⊢
      exact hs.2
    exact affine_bendTerm_subst_preserves (.lam body) (.fix s i) hlam1 hfix hclosed

/-! ### Refinement Relating `Core4` `Ty.Quantity.affine` / `Ty.Quantity.linear` to `isAffineBendTerm` -/

mutual
/-- Variable occurrence count on `Core4` `Term` matching `Obend.Core.Proofs.BidirectionalCompleteness.occurrences`. -/
def termVarUses (idx : Nat) : Term → Nat
  | .bound i => if i == idx then 1 else 0
  | .nat _ | .boolean _ | .label _ | .hole _ _ => 0
  | .lam b => termVarUses (idx + 1) b
  | .app f a | .fix f a | .binary _ f a | .split f _ a
  | .specification f a | .prototype f a | .mix f a =>
    termVarUses idx f + termVarUses idx a
  | .get t _ | .inject _ t | .reflect t | .metadata t
  | .project t | .perform t | .done t =>
    termVarUses idx t
  | .ifZero c z s =>
    termVarUses idx c + Nat.max (termVarUses idx z) (termVarUses (idx + 1) s)
  | .ifBool c t e =>
    termVarUses idx c + Nat.max (termVarUses idx t) (termVarUses idx e)
  | .record fs => termFieldUses idx fs
  | .extend i fs => termVarUses idx i + termFieldUses idx fs
  | .case sc arms => termVarUses idx sc + termArmUses idx arms

def termFieldUses (idx : Nat) : List (String × Term) → Nat
  | [] => 0
  | (_, v) :: rest => termVarUses idx v + termFieldUses idx rest

def termArmUses (idx : Nat) : List (String × Term) → Nat
  | [] => 0
  | (_, body) :: rest => Nat.max (termVarUses (idx + 1) body) (termArmUses idx rest)
end

/-- True when a `Core4` `.fix` specification has the 2-port shape `.lam (.lam _)`. -/
def isCoreFixSpecPortBalanced : Term → Bool
  | .lam (.lam _) => true
  | _ => false

mutual
/-- `Core4` affine/port-balanced predicate corresponding to `isAffineBendTerm`. -/
def isAffineCoreTerm : Term → Bool
  | .bound _ | .nat _ | .boolean _ | .label _ => true
  | .lam b => safeQuantity .affine (termVarUses 0 b) && isAffineCoreTerm b
  | .app f a | .binary _ f a | .split f _ a =>
    isAffineCoreTerm f && isAffineCoreTerm a
  | .fix s i =>
    isCoreFixSpecPortBalanced s && isAffineCoreTerm s && isAffineCoreTerm i
  | .get t _ | .inject _ t => isAffineCoreTerm t
  | .ifZero c z s =>
    safeQuantity .affine (termVarUses 0 s) && isAffineCoreTerm c && isAffineCoreTerm z && isAffineCoreTerm s
  | .ifBool c t e =>
    isAffineCoreTerm c && isAffineCoreTerm t && isAffineCoreTerm e
  | .record fs => isAffineCoreTermFields fs
  | .case sc arms => isAffineCoreTerm sc && isAffineCoreTermArms arms
  | .hole _ _ | .mix _ _ | .specification _ _ | .prototype _ _ | .reflect _
  | .metadata _ | .project _ | .extend _ _ | .perform _ | .done _ => false

def isAffineCoreTermFields : List (String × Term) → Bool
  | [] => true
  | (_, v) :: rest => isAffineCoreTerm v && isAffineCoreTermFields rest

def isAffineCoreTermArms : List (String × Term) → Bool
  | [] => true
  | (_, body) :: rest =>
    safeQuantity .affine (termVarUses 0 body) && isAffineCoreTerm body && isAffineCoreTermArms rest
end

mutual
@[simp] theorem termVarUses_embedB :
    (bt : BendTerm) → ∀ (idx : Nat), termVarUses idx (embedB bt) = countVarUses idx bt
  | .var i, idx | .nat _, idx | .bool _, idx | .label _, idx => by
    simp [embedB, termVarUses, countVarUses]
  | .lam b, idx => by
    simp [embedB, termVarUses, countVarUses, termVarUses_embedB b (idx + 1)]
  | .app f a, idx | .fix f a, idx | .binOp _ f a, idx | .split f _ a, idx => by
    simp [embedB, termVarUses, countVarUses, termVarUses_embedB f idx, termVarUses_embedB a idx]
  | .get t _, idx | .inject _ t, idx => by
    simp [embedB, termVarUses, countVarUses, termVarUses_embedB t idx]
  | .ifZero c z s, idx => by
    simp [embedB, termVarUses, countVarUses,
      termVarUses_embedB c idx, termVarUses_embedB z idx, termVarUses_embedB s (idx + 1)]
  | .ifBool c t e, idx => by
    simp [embedB, termVarUses, countVarUses,
      termVarUses_embedB c idx, termVarUses_embedB t idx, termVarUses_embedB e idx]
  | .record fs, idx => by
    simp only [embedB, termVarUses, countVarUses]
    exact termFieldUses_embedB fs idx
  | .case sc arms, idx => by
    simp only [embedB, termVarUses, countVarUses, termVarUses_embedB sc idx, termArmUses_embedB arms idx]

theorem termFieldUses_embedB :
    (fs : List (String × BendTerm)) → ∀ (idx : Nat),
      termFieldUses idx (embedBFields fs) = countFieldUses idx fs
  | [], _ => rfl
  | (_, v) :: rest, idx => by
    simp only [embedBFields, termFieldUses, countFieldUses,
      termVarUses_embedB v idx, termFieldUses_embedB rest idx]

theorem termArmUses_embedB :
    (arms : List (String × BendTerm)) → ∀ (idx : Nat),
      termArmUses idx (embedBFields arms) = countArmUses idx arms
  | [], _ => rfl
  | (_, v) :: rest, idx => by
    simp only [embedBFields, termArmUses, countArmUses,
      termVarUses_embedB v (idx + 1), termArmUses_embedB rest idx]
end

theorem isCoreFixSpecPortBalanced_embedB (bt : BendTerm) :
    isCoreFixSpecPortBalanced (embedB bt) = isFixSpecPortBalanced bt := by
  cases bt with
  | lam b =>
    cases b <;> rfl
  | _ => rfl

mutual
@[simp] theorem isAffineCoreTerm_embedB :
    (bt : BendTerm) → isAffineCoreTerm (embedB bt) = isAffineBendTerm bt
  | .var _ | .nat _ | .bool _ | .label _ => rfl
  | .lam b => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm, safeQuantity,
      termVarUses_embedB, isAffineCoreTerm_embedB b]
  | .app f a | .binOp _ f a | .split f _ a => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm,
      isAffineCoreTerm_embedB f, isAffineCoreTerm_embedB a]
  | .fix s i => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm, isCoreFixSpecPortBalanced_embedB,
      isAffineCoreTerm_embedB s, isAffineCoreTerm_embedB i]
  | .get t _ | .inject _ t => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm, isAffineCoreTerm_embedB t]
  | .ifZero c z s => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm, safeQuantity, termVarUses_embedB,
      isAffineCoreTerm_embedB c, isAffineCoreTerm_embedB z, isAffineCoreTerm_embedB s]
  | .ifBool c t e => by
    simp [embedB, isAffineCoreTerm, isAffineBendTerm,
      isAffineCoreTerm_embedB c, isAffineCoreTerm_embedB t, isAffineCoreTerm_embedB e]
  | .record fs => by
    simp only [embedB, isAffineCoreTerm, isAffineBendTerm]
    exact isAffineCoreTermFields_embedB fs
  | .case sc arms => by
    simp only [embedB, isAffineCoreTerm, isAffineBendTerm,
      isAffineCoreTerm_embedB sc, isAffineCoreTermArms_embedB arms]

theorem isAffineCoreTermFields_embedB :
    (fs : List (String × BendTerm)) →
      isAffineCoreTermFields (embedBFields fs) = isAffineBendTermFields fs
  | [] => rfl
  | (_, v) :: rest => by
    simp only [embedBFields, isAffineCoreTermFields, isAffineBendTermFields,
      isAffineCoreTerm_embedB v, isAffineCoreTermFields_embedB rest]

theorem isAffineCoreTermArms_embedB :
    (arms : List (String × BendTerm)) →
      isAffineCoreTermArms (embedBFields arms) = isAffineBendTermArms arms
  | [] => rfl
  | (_, v) :: rest => by
    simp only [embedBFields, isAffineCoreTermArms, isAffineBendTermArms, safeQuantity,
      termVarUses_embedB, isAffineCoreTerm_embedB v, isAffineCoreTermArms_embedB rest]
end

/-- **Refinement Theorem Relating `Ty.Quantity.affine` / `Ty.Quantity.linear` in `Core4` to `isAffineBendTerm` (`quantity_affine_linear_refines_bendTerm`)**:
For any `Core4` term `t : Term` that lowers via `compileToBendTT t = some bt` and any resource
quantity `q : Quantity` that is `.affine` or `.linear`:
1. Variable usage counts are preserved identically (`countVarUses idx bt = termVarUses idx t`).
2. `Core4`'s `safeQuantity q (termVarUses 0 t) = true` holds iff `countVarUses 0 bt ≤ 1`.
3. `Core4`'s binder discharge `q.fits (termVarUses 0 t) = true` (required by `PartialTyping.lambda`)
   implies `countVarUses 0 bt ≤ 1`, so when `isAffineBendTerm bt = true`, the lowered lambda
   `.lam bt` satisfies `isAffineBendTerm (.lam bt) = true`.
4. Globally, `isAffineBendTerm bt = isAffineCoreTerm t`. -/
theorem quantity_affine_linear_refines_bendTerm
    {t : Term} {bt : BendTerm} (hcomp : compileToBendTT t = some bt)
    (q : Quantity) (hq : q = .affine ∨ q = .linear) :
    (∀ idx : Nat, countVarUses idx bt = termVarUses idx t) ∧
    (safeQuantity q (termVarUses 0 t) = true ↔ countVarUses 0 bt ≤ 1) ∧
    (q.fits (termVarUses 0 t) = true → isAffineBendTerm bt = true → isAffineBendTerm (.lam bt) = true) ∧
    (isAffineBendTerm bt = isAffineCoreTerm t) := by
  have hemb : embedB bt = t := compileToBendTT_embedB t hcomp
  subst hemb
  refine ⟨fun idx => (termVarUses_embedB bt idx).symm, ?_, ?_, (isAffineCoreTerm_embedB bt).symm⟩
  · rcases hq with rfl | rfl <;> simp [safeQuantity, termVarUses_embedB]
  · intro hfits haff
    have hle : countVarUses 0 bt ≤ 1 := by
      rcases hq with rfl | rfl
      · simpa [Quantity.fits, termVarUses_embedB] using hfits
      · have heq : countVarUses 0 bt = 1 := by
          simpa [Quantity.fits, termVarUses_embedB] using hfits
        omega
    simp [isAffineBendTerm, hle, haff]

end Obend.Leaf.BendTT
end
