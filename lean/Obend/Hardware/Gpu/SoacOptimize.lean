module
public import Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.ArraySource
public section
namespace Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArraySource
set_option autoImplicit false

/-! Lexical SOAC transformations. Index tables are pullbacks: the consumer
indexes the producer table. Scalar arithmetic has the source's 64-bit semantics. -/

deriving instance DecidableEq for Rhs

/-- Lift a variable substitution underneath one lexical binder. -/
def liftRename (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => f i + 1

def renameRhs (f : Nat → Nat) : Rhs → Rhs
  | .map n op args => .map n op (args.map f)
  | .gather ix a => .gather ix (f a)
  | .concat a b => .concat (f a) (f b)
  | .literal vs => .literal vs
  | .fold op shape a => .fold op shape (f a)

def renameProgram (f : Nat → Nat) : Program → Program
  | .ret xs => .ret (xs.map f)
  | .letE r p => .letE (renameRhs f r) (renameProgram (liftRename f) p)

theorem renameRhs_eval (r : Rhs) (f : Nat → Nat) (env : Env) :
    (renameRhs f r).eval env = r.eval (fun i => env (f i)) := by
  cases r <;> simp [renameRhs, Rhs.eval, List.map_map, Function.comp_def]

theorem renameProgram_eval (p : Program) (f : Nat → Nat) (env : Env) :
    (renameProgram f p).eval env = p.eval (fun i => env (f i)) := by
  induction p generalizing f env with
  | ret xs => simp [renameProgram, Program.eval, List.map_map, Function.comp_def]
  | letE r p ih =>
    simp only [renameProgram, Program.eval, ih, renameRhs_eval]
    congr 1
    funext i
    cases i <;> rfl

/-- Free occurrences, expressed in the environment outside the program. -/
def freeVars : Program → List Nat
  | .ret xs => xs
  | .letE r p => r.vars ++ (freeVars p).filterMap (fun i => match i with
      | 0 => none | j + 1 => some j)

theorem rhs_congr (r : Rhs) (a b : Env)
    (h : ∀ i ∈ r.vars, a i = b i) : r.eval a = r.eval b := by
  cases r with
  | literal vs => rfl
  | map n op args =>
    simp only [Rhs.eval]
    apply List.map_congr_left
    intro i _
    congr 1
    exact List.map_congr_left fun v hv => congrArg (fun xs : Vec => xs.getD i 0#64) (h v hv)
  | gather ix v => simp [Rhs.eval, h v (by simp [Rhs.vars])]
  | concat x y => simp [Rhs.eval, h x (by simp [Rhs.vars]), h y (by simp [Rhs.vars])]
  | fold op shape v => simp [Rhs.eval, h v (by simp [Rhs.vars])]

theorem program_congr (p : Program) (a b : Env)
    (h : ∀ i ∈ freeVars p, a i = b i) : p.eval a = p.eval b := by
  induction p generalizing a b with
  | ret xs => exact List.map_congr_left h
  | letE r p ih =>
    have hr : r.eval a = r.eval b := rhs_congr r a b (fun i hi => h i (List.mem_append_left _ hi))
    apply ih
    intro i hi
    cases i with
    | zero => exact hr
    | succ i =>
      exact h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩))

def dropBinder (replacement : Nat) : Nat → Nat
  | 0 => replacement
  | i + 1 => i

def substitute (v : Nat) (p : Program) : Program := renameProgram (dropBinder v) p

theorem substitute_eval (p : Program) (v : Nat) (env : Env) :
    (substitute v p).eval env = p.eval (push (env v) env) := by
  rw [substitute, renameProgram_eval]
  congr 1
  funext i
  cases i <;> rfl

def dceProgram : Program → Program
  | .ret xs => .ret xs
  | .letE r p =>
    let q := dceProgram p
    if 0 ∈ freeVars q then .letE r q else renameProgram Nat.pred q

theorem dceProgram_sound (p : Program) (env : Env) :
    (dceProgram p).eval env = p.eval env := by
  induction p generalizing env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [dceProgram]
    split
    · simp only [Program.eval, ih]
    · rename_i h
      rw [renameProgram_eval]
      change _ = p.eval (push (r.eval env) env)
      rw [← ih (push (r.eval env) env)]
      apply program_congr
      intro i hi
      cases i with
      | zero => exact False.elim (h hi)
      | succ i => rfl

def letCount : Program → Nat
  | .ret _ => 0
  | .letE _ p => letCount p + 1

theorem renameProgram_count (p : Program) (f : Nat → Nat) :
    letCount (renameProgram f p) = letCount p := by
  induction p generalizing f with
  | ret xs => rfl
  | letE r p ih => simp [renameProgram, letCount, ih]

theorem dceProgram_count_le (p : Program) : letCount (dceProgram p) ≤ letCount p := by
  induction p with
  | ret xs => exact Nat.le_refl _
  | letE r p ih => simp only [dceProgram]; split <;> simp [letCount, renameProgram_count] <;> omega

theorem edges_length (p : Program) (next : Nat) : (p.edges next).length = letCount p := by
  induction p generalizing next with
  | ret xs => rfl
  | letE r p ih => simp [Program.edges, letCount, ih]

/-- Available expressions are expressed in the *current* lexical context. -/
def extendAvailable (r : Rhs) (ctx : List Rhs) : List Rhs :=
  (r :: ctx).map (renameRhs Nat.succ)

def findRhs (r : Rhs) : List Rhs → Option Nat
  | [] => none
  | s :: ss => if r = s then some 0 else (findRhs r ss).map Nat.succ

def Available (ctx : List Rhs) (env : Env) : Prop :=
  ∀ i r, ctx[i]? = some r → r.eval env = env i

theorem findRhs_sound (r : Rhs) (ctx : List Rhs) (i : Nat)
    (h : findRhs r ctx = some i) : ctx[i]? = some r := by
  induction ctx generalizing i with
  | nil => simp [findRhs] at h
  | cons s ss ih =>
    simp only [findRhs] at h
    split at h
    · rename_i he; subst s; cases h; rfl
    · cases hh : findRhs r ss with
      | none => simp [hh] at h
      | some j => simp [hh] at h; subst i; exact ih j hh

theorem extendAvailable_sound (r : Rhs) (ctx : List Rhs) (env : Env)
    (h : Available ctx env) : Available (extendAvailable r ctx) (push (r.eval env) env) := by
  intro i s hs
  cases i with
  | zero =>
    simp [extendAvailable] at hs
    subst s
    rw [renameRhs_eval]
    rfl
  | succ i =>
    simp only [extendAvailable, List.map_cons, List.getElem?_cons_succ, List.getElem?_map] at hs
    cases hi : ctx[i]? with
    | none => simp [hi] at hs
    | some t =>
      simp [hi] at hs
      subst s
      rw [renameRhs_eval]
      exact h i t hi

def cseWith (ctx : List Rhs) : Program → Program
  | .ret xs => .ret xs
  | .letE r p =>
    let q := cseWith (extendAvailable r ctx) p
    match findRhs r ctx with
    | none => .letE r q
    | some i => substitute i q

def cseProgram (p : Program) : Program := cseWith [] p

theorem cseWith_sound (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    (cseWith ctx p).eval env = p.eval env := by
  induction p generalizing ctx env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [cseWith]
    cases hf : findRhs r ctx with
    | none => exact ih _ _ (extendAvailable_sound r ctx env h)
    | some i =>
      rw [substitute_eval, ← h i r (findRhs_sound r ctx i hf)]
      exact ih _ _ (extendAvailable_sound r ctx env h)

theorem cseProgram_sound (p : Program) (env : Env) :
    (cseProgram p).eval env = p.eval env :=
  cseWith_sound p [] env (by intro i r h; simp at h)

theorem cseWith_count_le (p : Program) (ctx : List Rhs) :
    letCount (cseWith ctx p) ≤ letCount p := by
  induction p generalizing ctx with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    have h := ih (extendAvailable r ctx)
    simp only [cseWith]
    cases findRhs r ctx <;> simp [letCount, substitute, renameProgram_count] <;> omega

/-- Consumer-first pullback. Its admission guard excludes producer-table misses. -/
def composeIndexFn (f g : FiniteFunction) : FiniteFunction :=
  ⟨g.source, f.target, g.table.map (fun i => f.table.getD i 0)⟩

theorem getD_map_inBounds {α β : Type} (xs : List α) (f : α → β)
    (i : Nat) (a : α) (b : β) (h : i < xs.length) :
    (xs.map f).getD i b = f (xs.getD i a) := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using h)

theorem composeIndexFn_sound (f g : FiniteFunction) (xs : Vec)
    (h : ∀ i ∈ g.table, i < f.table.length) :
    (composeIndexFn f g).table.map (fun i => xs.getD i 0#64) =
      g.table.map (fun i => (f.table.map (fun j => xs.getD j 0#64)).getD i 0#64) := by
  simp only [composeIndexFn, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact (getD_map_inBounds f.table (fun j => xs.getD j 0#64) i 0 0#64 (h i hi)).symm

/-- Rewrite gathers through known immutable bindings. No bounds facts are assumed. -/
def simplifyRhs (ctx : List Rhs) (r : Rhs) : Rhs :=
  match r with
  | .gather g a => match ctx[a]? with
    | some (.literal vs) => .literal (g.table.map (fun i => vs.getD i 0#64))
    | some (.gather f x) =>
      if g.table.all (· < f.table.length) then .gather (composeIndexFn f g) x else r
    | _ => r
  | _ => r

theorem simplifyRhs_sound (r : Rhs) (ctx : List Rhs) (env : Env)
    (h : Available ctx env) : (simplifyRhs ctx r).eval env = r.eval env := by
  cases r with
  | gather g a =>
    simp only [simplifyRhs]
    cases hc : ctx[a]? with
    | none => rfl
    | some s =>
      have hs := h a s hc
      cases s with
      | literal vs => simpa [Rhs.eval] using congrArg (fun xs : Vec => g.table.map (fun i => xs.getD i 0#64)) hs
      | gather f x =>
        simp only
        split
        · rename_i hb
          simp only [Rhs.eval] at hs ⊢
          rw [← hs]
          exact composeIndexFn_sound f g (env x) (by simpa [List.all_eq_true] using hb)
        · rfl
      | map n op args => rfl
      | concat x y => rfl
      | fold op shape x => rfl
  | map n op args => rfl
  | concat x y => rfl
  | literal vs => rfl
  | fold op shape x => rfl

def simplifyWith (ctx : List Rhs) : Program → Program
  | .ret xs => .ret xs
  | .letE r p =>
    let s := simplifyRhs ctx r
    .letE s (simplifyWith (extendAvailable s ctx) p)

theorem simplifyWith_sound (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    (simplifyWith ctx p).eval env = p.eval env := by
  induction p generalizing ctx env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [simplifyWith, Program.eval]
    rw [ih _ _ (extendAvailable_sound _ ctx env h), simplifyRhs_sound r ctx env h]

theorem simplifyWith_count (p : Program) (ctx : List Rhs) :
    letCount (simplifyWith ctx p) = letCount p := by
  induction p generalizing ctx with
  | ret xs => rfl
  | letE r p ih => simp [simplifyWith, letCount, ih]

/-- Static shapes for newly bound arrays; unknown external shapes stay unknown. -/
def staticLength : Rhs → Option Nat
  | .map n _ _ => some n
  | .gather f _ => some f.table.length
  | .literal vs => some vs.length
  | .fold _ shape _ => some shape.outLen
  | .concat _ _ => none

theorem staticLength_sound (r : Rhs) (env : Env) (n : Nat) (h : staticLength r = some n) :
    (r.eval env).length = n := by
  cases r <;> simp_all [staticLength, Rhs.eval, evalFold, FoldShape.outLen]

def knownShape (ctx : List Rhs) (a : Nat) : Option Nat := ctx[a]?.bind staticLength

theorem knownShape_sound (ctx : List Rhs) (env : Env) (a n : Nat)
    (h : Available ctx env) (hn : knownShape ctx a = some n) : (env a).length = n := by
  unfold knownShape at hn
  cases hc : ctx[a]? with
  | none => simp [hc] at hn
  | some r =>
    rw [← h a r hc]
    exact staticLength_sound r env n (by simpa [hc] using hn)

def aliasRhs (ctx : List Rhs) : Rhs → Option Nat
  | .gather f a => if knownShape ctx a = some f.table.length ∧ f.table = List.range f.table.length then some a else none
  | .map n (.scalar (.scale 1)) [a] => if knownShape ctx a = some n then some a else none
  | _ => none

theorem range_getD (xs : Vec) : (List.range xs.length).map (fun i => xs.getD i 0#64) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem aliasRhs_sound (r : Rhs) (ctx : List Rhs) (env : Env) (a : Nat)
    (h : Available ctx env) (ha : aliasRhs ctx r = some a) : r.eval env = env a := by
  unfold aliasRhs at ha
  split at ha
  · rename_i f v
    split at ha
    · rename_i hh
      cases ha
      have hl := knownShape_sound ctx env a f.table.length h hh.1
      change f.table.map (fun i => (env a).getD i 0#64) = env a
      rw [hh.2, ← hl]
      exact range_getD (env a)
    · contradiction
  · rename_i n v
    split at ha
    · rename_i hh
      cases ha
      have hl := knownShape_sound ctx env a n h hh
      simp only [Rhs.eval, List.map_cons, List.map_nil, evalElemOp, evalHypergraphOpBv]
      have hone : BitVec.ofInt 64 1 = 1#64 := rfl
      simp only [List.getD_cons_zero, hone, BitVec.one_mul, ← hl]
      exact range_getD (env a)
    · contradiction
  · contradiction

theorem aliasRhs_var (r : Rhs) (ctx : List Rhs) (a : Nat) (h : aliasRhs ctx r = some a) : a ∈ r.vars := by
  unfold aliasRhs at h
  split at h
  · split at h <;> simp_all [Rhs.vars]
  · split at h <;> simp_all [Rhs.vars]
  · contradiction

def aliasWith (ctx : List Rhs) : Program → Program
  | .ret xs => .ret xs
  | .letE r p =>
    let q := aliasWith (extendAvailable r ctx) p
    match aliasRhs ctx r with
    | some a => substitute a q
    | none => .letE r q

theorem aliasWith_sound (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    (aliasWith ctx p).eval env = p.eval env := by
  induction p generalizing ctx env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [aliasWith]
    cases ha : aliasRhs ctx r with
    | none => exact ih _ _ (extendAvailable_sound r ctx env h)
    | some a =>
      rw [substitute_eval, ← aliasRhs_sound r ctx env a h ha]
      exact ih _ _ (extendAvailable_sound r ctx env h)

theorem aliasWith_count_le (p : Program) (ctx : List Rhs) : letCount (aliasWith ctx p) ≤ letCount p := by
  induction p generalizing ctx with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    have h := ih (extendAvailable r ctx)
    simp only [aliasWith]
    cases aliasRhs ctx r <;> simp only [substitute, renameProgram_count, letCount] <;> omega

def normalizeProgram (p : Program) : Program := dceProgram (cseProgram (aliasWith [] (simplifyWith [] p)))

theorem normalizeProgram_sound (p : Program) (env : Env) :
    (normalizeProgram p).eval env = p.eval env := by
  rw [normalizeProgram, dceProgram_sound, cseProgram_sound]
  rw [aliasWith_sound _ [] env (by intro i r h; simp at h)]
  exact simplifyWith_sound p [] env (by intro i r h; simp at h)

theorem normalizeProgram_letCount_le (p : Program) :
    letCount (normalizeProgram p) ≤ letCount p := by
  apply Nat.le_trans (dceProgram_count_le _)
  apply Nat.le_trans (cseWith_count_le _ [])
  apply Nat.le_trans (aliasWith_count_le _ [])
  rw [simplifyWith_count]
  exact Nat.le_refl _

theorem normalizeProgram_edges_le (p : Program) (next : Nat) :
    ((normalizeProgram p).edges next).length ≤ (p.edges next).length := by
  simpa only [edges_length] using normalizeProgram_letCount_le p

/-- Scalar DAG syntax. Repeated subexpressions may be shared by a code generator;
all source primitives read at most three operands. -/
inductive ScalarExpr where
  | input (slot : Nat)
  | const (value : Word)
  | prim (op : ElemOp) (a b c : ScalarExpr)
  deriving Repr, DecidableEq

def ScalarExpr.eval (slots : Nat → Word) : ScalarExpr → Word
  | .input i => slots i
  | .const w => w
  | .prim op a b c => evalElemOp op [a.eval slots, b.eval slots, c.eval slots]

def ScalarExpr.subst (f : Nat → ScalarExpr) : ScalarExpr → ScalarExpr
  | .input i => f i
  | .const w => .const w
  | .prim op a b c => .prim op (a.subst f) (b.subst f) (c.subst f)

theorem ScalarExpr.subst_sound (e : ScalarExpr) (f : Nat → ScalarExpr) (slots : Nat → Word) :
    (e.subst f).eval slots = e.eval (fun i => (f i).eval slots) := by
  induction e <;> simp_all [ScalarExpr.subst, ScalarExpr.eval]

def scalarPrimitive (op : ElemOp) : ScalarExpr :=
  .prim op (.input 0) (.input 1) (.input 2)

theorem scalarPrimitive_sound (op : ElemOp) (xs : Vec) :
    (scalarPrimitive op).eval (fun i => xs.getD i 0#64) = evalElemOp op xs := by
  cases op with
  | scalar op => cases op <;> rfl
  | ult | band | bor | shr | shl => rfl


/-- Scalar stream code: bounds and pullback nodes retain exact zero padding.
A `prim` is register arithmetic; only `var` issues a global word read. -/
inductive KernelInput where
  | var (array : Nat)
  | const (word : Word)
  | literal (values : Vec)
  | prim (op : ElemOp) (a b c : KernelInput)
  | gather (indices : FiniteFunction) (input : KernelInput)
  | bounded (length : Nat) (input : KernelInput)
  deriving Repr

def KernelInput.eval (env : Env) (i : Nat) : KernelInput → Word
  | .var a => (env a).getD i 0#64
  | .const w => w
  | .literal vs => vs.getD i 0#64
  | .prim op a b c => evalElemOp op [a.eval env i, b.eval env i, c.eval env i]
  | .gather f a => if i < f.table.length then a.eval env (f.table.getD i 0) else 0#64
  | .bounded n a => if i < n then a.eval env i else 0#64

def KernelInput.bind (f : Nat → KernelInput) : KernelInput → KernelInput
  | .var a => f a
  | .const w => .const w
  | .literal vs => .literal vs
  | .prim op a b c => .prim op (a.bind f) (b.bind f) (c.bind f)
  | .gather ix a => .gather ix (a.bind f)
  | .bounded n a => .bounded n (a.bind f)

def KernelInput.vars : KernelInput → List Nat
  | .var a => [a]
  | .const _ | .literal _ => []
  | .prim _ a b c => a.vars ++ b.vars ++ c.vars
  | .gather _ a | .bounded _ a => a.vars

def KernelInput.rename (f : Nat → Nat) (e : KernelInput) : KernelInput := e.bind (fun a => .var (f a))

theorem KernelInput.bind_sound (e : KernelInput) (f : Nat → KernelInput) (env other : Env)
    (h : ∀ v i, (f v).eval env i = (other v).getD i 0#64) (i : Nat) :
    (e.bind f).eval env i = e.eval other i := by
  induction e generalizing i with
  | var a => exact h a i
  | const w => rfl
  | literal vs => rfl
  | prim op a b c ha hb hc => simp only [bind, eval, ha, hb, hc]
  | gather ix a ih => simp only [bind, eval]; split <;> simp_all
  | bounded n a ih => simp only [bind, eval]; split <;> simp_all

theorem KernelInput.rename_sound (e : KernelInput) (f : Nat → Nat) (env : Env) (i : Nat) :
    (e.rename f).eval env i = e.eval (fun v => env (f v)) i :=
  e.bind_sound _ _ _ (fun _ _ => rfl) i

theorem KernelInput.congr (e : KernelInput) (env other : Env)
    (h : ∀ v ∈ e.vars, env v = other v) (i : Nat) : e.eval env i = e.eval other i := by
  induction e generalizing i with
  | var a => simp [eval, h a (by simp [vars])]
  | const w => rfl
  | literal vs => rfl
  | prim op a b c ha hb hc =>
    have h1 := ha (fun v hv => h v (by simp [vars, hv])) i
    have h2 := hb (fun v hv => h v (by simp [vars, hv])) i
    have h3 := hc (fun v hv => h v (by simp [vars, hv])) i
    simp only [eval, h1, h2, h3]
  | gather ix a ih => simp only [eval]; split <;> simp_all [vars]
  | bounded n a ih => simp only [eval]; split <;> simp_all [vars]

/-- Scalar slot substitution generates register code, not an array binding. -/
def ScalarExpr.instantiate (inputs : Nat → KernelInput) : ScalarExpr → KernelInput
  | .input i => inputs i
  | .const w => .const w
  | .prim op a b c => .prim op (a.instantiate inputs) (b.instantiate inputs) (c.instantiate inputs)

theorem ScalarExpr.instantiate_sound (e : ScalarExpr) (inputs : Nat → KernelInput)
    (env : Env) (i : Nat) :
    (e.instantiate inputs).eval env i = e.eval (fun v => (inputs v).eval env i) := by
  induction e <;> simp_all [ScalarExpr.instantiate, ScalarExpr.eval, KernelInput.eval]

inductive FusedRhs where
  | mapKernel (n : Nat) (body : KernelInput)
  | foldKernel (op : ReduceOp) (shape : FoldShape) (init : Word) (body : KernelInput)
  | source (rhs : Rhs)
  deriving Repr

def mapKernel (n : Nat) (inputs : List KernelInput) (e : ScalarExpr) : FusedRhs :=
  .mapKernel n (e.instantiate (fun i => inputs.getD i (.const 0#64)))

def foldMapKernel (op : ReduceOp) (init : Word) (n : Nat)
    (inputs : List KernelInput) (e : ScalarExpr) : FusedRhs :=
  .foldKernel op (.reduce n) init (e.instantiate (fun i => inputs.getD i (.const 0#64)))

def scanMapKernel (op : ReduceOp) (init : Word) (n : Nat) (mode : ScanMode)
    (inputs : List KernelInput) (e : ScalarExpr) : FusedRhs :=
  .foldKernel op (.scan n mode) init (e.instantiate (fun i => inputs.getD i (.const 0#64)))

def FusedRhs.eval (env : Env) : FusedRhs → Vec
  | .mapKernel n body => (List.range n).map (body.eval env)
  | .foldKernel op shape init body => shape.ranges.map fun r => foldRange op (body.eval env) r.1 r.2 init
  | .source r => r.eval env

def FusedRhs.vars : FusedRhs → List Nat
  | .mapKernel _ body | .foldKernel _ _ _ body => body.vars
  | .source r => r.vars

def FusedRhs.rename (f : Nat → Nat) : FusedRhs → FusedRhs
  | .mapKernel n body => .mapKernel n (body.rename f)
  | .foldKernel op shape init body => .foldKernel op shape init (body.rename f)
  | .source r => .source (renameRhs f r)

theorem FusedRhs.rename_sound (r : FusedRhs) (f : Nat → Nat) (env : Env) :
    (r.rename f).eval env = r.eval (fun i => env (f i)) := by
  cases r <;> simp [rename, eval, KernelInput.rename_sound, renameRhs_eval]

theorem FusedRhs.congr (r : FusedRhs) (env other : Env)
    (h : ∀ i ∈ r.vars, env i = other i) : r.eval env = r.eval other := by
  cases r with
  | source r => exact rhs_congr r env other h
  | mapKernel n e => simp only [eval, e.congr env other h]
  | foldKernel op shape init e => simp only [eval, e.congr env other h]

inductive FusedProgram where
  | ret (arrays : List Nat)
  | letE (value : FusedRhs) (body : FusedProgram)
  deriving Repr

def evalFused (env : Env) : FusedProgram → List Vec
  | .ret arrays => arrays.map env
  | .letE r p => evalFused (push (r.eval env) env) p

def liftRhs : Rhs → FusedRhs
  | .literal vs => .mapKernel vs.length (.literal vs)
  | .map n op args => mapKernel n (args.map KernelInput.var) (scalarPrimitive op)
  | .gather ix a => .mapKernel ix.table.length (.gather ix (.var a))
  | .fold op shape a => .foldKernel op shape op.identity (.var a)
  | r => .source r

theorem inputSlots (args : List Nat) (env : Env) (i j : Nat) :
    ((args.map KernelInput.var).getD j (.const 0#64)).eval env i =
      (args.map (fun v => (env v).getD i 0#64)).getD j 0#64 := by
  induction args generalizing j with
  | nil => rfl
  | cons a args ih => cases j with
    | zero => rfl
    | succ j => exact ih j

theorem liftRhs_sound (r : Rhs) (env : Env) : (liftRhs r).eval env = r.eval env := by
  cases r with
  | literal vs => exact range_getD vs
  | concat a b => rfl
  | fold op shape a => rfl
  | map n op args =>
    simp only [liftRhs, mapKernel, FusedRhs.eval, Rhs.eval]
    apply List.map_congr_left
    intro i _
    rw [ScalarExpr.instantiate_sound]
    simp only [inputSlots, scalarPrimitive_sound]
  | gather ix a =>
    simp only [liftRhs, FusedRhs.eval, Rhs.eval]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, KernelInput.eval]
      have h : i < ix.table.length := by simpa using hi
      simp [h, List.getD_eq_getElem?_getD]

def liftArraySource : Program → FusedProgram
  | .ret arrays => .ret arrays
  | .letE r p => .letE (liftRhs r) (liftArraySource p)

theorem liftArraySource_sound (p : Program) (env : Env) :
    evalFused env (liftArraySource p) = p.eval env := by
  induction p generalizing env with
  | ret xs => rfl
  | letE r p ih => simp only [liftArraySource, evalFused, Program.eval, ih, liftRhs_sound]

def FusedProgram.rename (f : Nat → Nat) : FusedProgram → FusedProgram
  | .ret xs => .ret (xs.map f)
  | .letE r p => .letE (r.rename f) (p.rename (liftRename f))

def FusedProgram.freeVars : FusedProgram → List Nat
  | .ret xs => xs
  | .letE r p => r.vars ++ p.freeVars.filterMap (fun i => match i with | 0 => none | j+1 => some j)

theorem FusedProgram.rename_sound (p : FusedProgram) (f : Nat → Nat) (env : Env) :
    evalFused env (p.rename f) = evalFused (fun v => env (f v)) p := by
  induction p generalizing f env with
  | ret xs => simp [rename, evalFused, List.map_map, Function.comp_def]
  | letE r p ih =>
    simp only [rename, evalFused, FusedRhs.rename_sound, ih]
    congr 1
    funext i
    cases i <;> rfl

theorem FusedProgram.congr (p : FusedProgram) (env other : Env)
    (h : ∀ v ∈ p.freeVars, env v = other v) : evalFused env p = evalFused other p := by
  induction p generalizing env other with
  | ret xs => exact List.map_congr_left h
  | letE r p ih =>
    apply ih
    intro i hi
    cases i with
    | zero => exact r.congr env other (fun v hv => h v (List.mem_append_left _ hv))
    | succ i => exact h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩))

def dceFused : FusedProgram → FusedProgram
  | .ret xs => .ret xs
  | .letE r p =>
    let q := dceFused p
    if 0 ∈ q.freeVars then .letE r q else q.rename Nat.pred

theorem dceFused_sound (p : FusedProgram) (env : Env) : evalFused env (dceFused p) = evalFused env p := by
  induction p generalizing env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [dceFused]
    split
    · simp only [evalFused, ih]
    · rename_i h
      rw [FusedProgram.rename_sound]
      change _ = evalFused (push (r.eval env) env) p
      rw [← ih]
      apply FusedProgram.congr
      intro i hi
      cases i with
      | zero => exact False.elim (h hi)
      | succ i => rfl

/-- The environment invariant for stream substitution includes every index,
including misses. Therefore gather/shape mismatches require no semantic oracle. -/
def StreamAvailable (f : Nat → KernelInput) (env : Env) : Prop :=
  ∀ v i, (f v).eval env i = (env v).getD i 0#64

def FusedRhs.inline (f : Nat → KernelInput) : FusedRhs → FusedRhs
  | .mapKernel n e => .mapKernel n (e.bind f)
  | .foldKernel op shape init e => .foldKernel op shape init (e.bind f)
  | .source r => .source r

theorem FusedRhs.inline_sound (r : FusedRhs) (f : Nat → KernelInput) (env : Env)
    (h : StreamAvailable f env) : (r.inline f).eval env = r.eval env := by
  cases r <;> simp [inline, eval, KernelInput.bind_sound _ f env env h]

/-- Keep an exact finite length around every inlined producer. -/
def producerStream : FusedRhs → Option KernelInput
  | .mapKernel n e => some (.bounded n e)
  | _ => none

theorem producerStream_sound (r : FusedRhs) (e : KernelInput)
    (h : producerStream r = some e) (env : Env) (i : Nat) :
    e.eval env i = (r.eval env).getD i 0#64 := by
  cases r with
  | mapKernel n body =>
    simp [producerStream] at h
    subst e
    simp only [KernelInput.eval, FusedRhs.eval]
    by_cases hi : i < n
    · simp [hi]
    · rw [ite_eq_right hi]
      symm
      exact getD_of_le_length _ i _ (by simp; omega)
  | foldKernel op shape init body => simp [producerStream] at h
  | source r => simp [producerStream] at h

def extendStreams (r : FusedRhs) (f : Nat → KernelInput) : Nat → KernelInput
  | 0 => match producerStream r with
    | some e => e.rename Nat.succ
    | none => .var 0
  | i+1 => (f i).rename Nat.succ

theorem extendStreams_sound (r : FusedRhs) (f : Nat → KernelInput) (env : Env)
    (h : StreamAvailable f env) : StreamAvailable (extendStreams r f) (push (r.eval env) env) := by
  intro v i
  cases v with
  | zero =>
    simp only [extendStreams]
    cases he : producerStream r with
    | none => rfl
    | some e =>
      rw [KernelInput.rename_sound]
      exact producerStream_sound r e he env i
  | succ v =>
    simp only [extendStreams, KernelInput.rename_sound]
    exact h v i

def inlineFused (f : Nat → KernelInput) : FusedProgram → FusedProgram
  | .ret xs => .ret xs
  | .letE r p =>
    let s := r.inline f
    .letE s (inlineFused (extendStreams s f) p)

theorem inlineFused_sound (p : FusedProgram) (f : Nat → KernelInput) (env : Env)
    (h : StreamAvailable f env) : evalFused env (inlineFused f p) = evalFused env p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [inlineFused, evalFused]
    rw [ih _ _ (extendStreams_sound _ f env h), FusedRhs.inline_sound r f env h]

/-- Global input requests in the executable scalar stream, per element.
Register arithmetic and bounds/table lookups do not access array HBM. -/
def KernelInput.reads (i : Nat) : KernelInput → Nat
  | .var _ => 1
  | .const _ | .literal _ => 0
  | .prim _ a b c => a.reads i + b.reads i + c.reads i
  | .gather f a => if i < f.table.length then a.reads (f.table.getD i 0) else 0
  | .bounded n a => if i < n then a.reads i else 0

def FusedRhs.fixedTraffic : FusedRhs → Nat
  | .mapKernel n e => ((List.range n).map e.reads).sum + n
  | .foldKernel _ shape _ e => ((List.range shape.inputLen).map e.reads).sum + shape.outLen
  | .source (.map n _ args) => n*args.length+n
  | .source (.gather f _) => 2*f.table.length
  | .source (.literal vs) => vs.length
  | .source (.fold _ shape _) => shape.inputLen+shape.outLen
  | .source (.concat _ _) => 0

def FusedRhs.dynamicTraffic (env : Env) : FusedRhs → Nat
  | .source (.concat a b) => 2*((env a).length+(env b).length)
  | _ => 0

def fixedTraffic : FusedProgram → Nat
  | .ret _ => 0
  | .letE r p => r.fixedTraffic + fixedTraffic p

def dynamicTraffic (env : Env) : FusedProgram → Nat
  | .ret _ => 0
  | .letE r p => r.dynamicTraffic env + dynamicTraffic (push (r.eval env) env) p

/-- Exact reads plus writes for the scalar-stream schedule; shaped collectives
use a cached streaming fold/scan, so each input is fetched once. -/
def hbmTrafficWords (p : FusedProgram) (env : Env) : Nat := fixedTraffic p + dynamicTraffic env p

def verticalCandidate (p : FusedProgram) : FusedProgram := dceFused (inlineFused KernelInput.var p)

/-- Reject a candidate if duplicated input streams outweigh removed arrays. -/
def fuseVertical (p : FusedProgram) : FusedProgram :=
  let q := verticalCandidate p
  if fixedTraffic q ≤ fixedTraffic p then q else p

theorem fuseVertical_sound (p : FusedProgram) (env : Env) :
    evalFused env (fuseVertical p) = evalFused env p := by
  simp only [fuseVertical]
  split
  · rw [verticalCandidate, dceFused_sound, inlineFused_sound p _ env (fun _ _ => rfl)]
  · rfl


theorem FusedRhs.dynamicTraffic_congr (r : FusedRhs) (env other : Env)
    (h : ∀ i ∈ r.vars, env i = other i) : r.dynamicTraffic env = r.dynamicTraffic other := by
  cases r with
  | mapKernel n e => rfl
  | foldKernel op shape init e => rfl
  | source r => cases r with
    | concat a b => simp [dynamicTraffic, h a (by simp [vars, Rhs.vars]), h b (by simp [vars, Rhs.vars])]
    | map n op args | gather f a | literal vs | fold op shape a => rfl

theorem dynamicTraffic_congr (p : FusedProgram) (env other : Env)
    (h : ∀ i ∈ p.freeVars, env i = other i) : dynamicTraffic env p = dynamicTraffic other p := by
  induction p generalizing env other with
  | ret xs => rfl
  | letE r p ih =>
    have hr : ∀ i ∈ r.vars, env i = other i := fun i hi => h i (List.mem_append_left _ hi)
    simp only [dynamicTraffic, r.dynamicTraffic_congr env other hr]
    congr 1
    apply ih
    intro i hi
    cases i with
    | zero => exact r.congr env other hr
    | succ i => exact h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩))

theorem FusedRhs.dynamicTraffic_rename (r : FusedRhs) (f : Nat → Nat) (env : Env) :
    (r.rename f).dynamicTraffic env = r.dynamicTraffic (fun v => env (f v)) := by
  cases r with
  | mapKernel n e => rfl
  | foldKernel op shape init e => rfl
  | source r => cases r <;> rfl

theorem dynamicTraffic_rename (p : FusedProgram) (f : Nat → Nat) (env : Env) :
    dynamicTraffic env (p.rename f) = dynamicTraffic (fun v => env (f v)) p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [FusedProgram.rename, dynamicTraffic, FusedRhs.dynamicTraffic_rename, ih, FusedRhs.rename_sound]
    congr 2
    funext i
    cases i <;> rfl

theorem dceFused_dynamic_le (p : FusedProgram) (env : Env) :
    dynamicTraffic env (dceFused p) ≤ dynamicTraffic env p := by
  induction p generalizing env with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    simp only [dceFused]
    split
    · simp only [dynamicTraffic]
      exact Nat.add_le_add_left (ih _) _
    · rename_i h
      rw [dynamicTraffic_rename]
      have he : dynamicTraffic (fun i => env i.pred) (dceFused p) =
          dynamicTraffic (push (r.eval env) env) (dceFused p) := by
        apply dynamicTraffic_congr
        intro i hi
        cases i with
        | zero => exact False.elim (h hi)
        | succ i => rfl
      rw [he]
      exact Nat.le_trans (ih _) (Nat.le_add_left _ _)

theorem FusedRhs.inline_dynamic (r : FusedRhs) (f : Nat → KernelInput) (env : Env) :
    (r.inline f).dynamicTraffic env = r.dynamicTraffic env := by cases r <;> rfl

theorem inlineFused_dynamic (p : FusedProgram) (f : Nat → KernelInput) (env : Env)
    (h : StreamAvailable f env) : dynamicTraffic env (inlineFused f p) = dynamicTraffic env p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [inlineFused, dynamicTraffic, FusedRhs.inline_dynamic]
    rw [ih _ _ (extendStreams_sound _ f env h), FusedRhs.inline_sound r f env h]

theorem hbmTraffic_fuseVertical_le (p : FusedProgram) (env : Env) :
    hbmTrafficWords (fuseVertical p) env ≤ hbmTrafficWords p env := by
  simp only [fuseVertical]
  split
  · rename_i h
    apply Nat.add_le_add h
    exact Nat.le_trans (dceFused_dynamic_le _ env)
      (by rw [inlineFused_dynamic p KernelInput.var env (fun _ _ => rfl)]; exact Nat.le_refl _)
  · exact Nat.le_refl _

set_option genSizeOfSpec false in
/-- Two independent kernels with identical iteration domains and input streams. -/
inductive TupleMode where
  | maps
  | mapFold (op : ReduceOp) (init : Word)
  deriving Repr

structure TupleKernel where
  count : Nat
  input : KernelInput
  left : ScalarExpr
  right : ScalarExpr
  mode : TupleMode

def unarySlots (w : Word) : Nat → Word
  | 0 => w
  | _+1 => 0#64

def tupleValues (k : TupleKernel) (env : Env) (i : Nat) : Word × Word :=
  let slots := unarySlots (k.input.eval env i)
  (k.left.eval slots, k.right.eval slots)

/-- Tail-recursive accumulator order is the same as the source left fold.
The left output is constructed once, while the right result stays in registers. -/
def mapFoldLoop (op : ReduceOp) (f : Nat → Word × Word) : List Nat → Word → Vec × Word
  | [], acc => ([], acc)
  | i::is, acc =>
    let pair := f i
    let rest := mapFoldLoop op f is (op.combine acc pair.2)
    (pair.1 :: rest.1, rest.2)

theorem mapFoldLoop_sound (op : ReduceOp) (f : Nat → Word × Word) (is : List Nat) (acc : Word) :
    mapFoldLoop op f is acc =
      (is.map (fun i => (f i).1), (is.map (fun i => (f i).2)).foldl op.combine acc) := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih => simp [mapFoldLoop, ih]

def evalSeparate (k : TupleKernel) (env : Env) : Vec × Vec :=
  let a := (List.range k.count).map fun i => k.left.eval (unarySlots (k.input.eval env i))
  let b := (List.range k.count).map fun i => k.right.eval (unarySlots (k.input.eval env i))
  match k.mode with
  | .maps => (a,b)
  | .mapFold op init => (a,[b.foldl op.combine init])

def evalTuple (k : TupleKernel) (env : Env) : Vec × Vec :=
  match k.mode with
  | .maps =>
    let pairs := (List.range k.count).map (tupleValues k env)
    (pairs.map Prod.fst, pairs.map Prod.snd)
  | .mapFold op init =>
    let result := mapFoldLoop op (tupleValues k env) (List.range k.count) init
    (result.1, [result.2])

inductive TupleKernelProgram where
  | separate (kernel : TupleKernel)
  | lockstep (kernel : TupleKernel)

def TupleKernelProgram.eval (env : Env) : TupleKernelProgram → Vec × Vec
  | .separate k => evalSeparate k env
  | .lockstep k => evalTuple k env

def fuseHorizontal : TupleKernelProgram → TupleKernelProgram
  | .separate k | .lockstep k => .lockstep k

theorem tupleKernel_sound (k : TupleKernel) (env : Env) : evalTuple k env = evalSeparate k env := by
  cases hm : k.mode <;> simp [evalTuple, evalSeparate, hm, List.map_map,
    tupleValues, Function.comp_def, mapFoldLoop_sound]

theorem fuseHorizontal_sound (p : TupleKernelProgram) (env : Env) :
    (fuseHorizontal p).eval env = p.eval env := by
  cases p with
  | separate k => exact tupleKernel_sound k env
  | lockstep k => rfl

def tupleInputReads (k : TupleKernel) : Nat := ((List.range k.count).map k.input.reads).sum

def horizontalReads : TupleKernelProgram → Nat
  | .separate k => 2*tupleInputReads k
  | .lockstep k => tupleInputReads k

theorem horizontal_shared_reads (k : TupleKernel) :
    horizontalReads (.separate k) = horizontalReads (fuseHorizontal (.separate k)) + tupleInputReads k := by
  simp [horizontalReads, fuseHorizontal, Nat.two_mul]

theorem horizontal_reads_le (p : TupleKernelProgram) :
    horizontalReads (fuseHorizontal p) ≤ horizontalReads p := by
  cases p <;> simp [horizontalReads, fuseHorizontal, Nat.two_mul]


theorem renameRhs_vars (r : Rhs) (f : Nat → Nat) : (renameRhs f r).vars = r.vars.map f := by
  cases r <;> rfl

theorem scoped_freeVars (p : Program) (d : Nat) :
    p.Scoped d ↔ ∀ i ∈ freeVars p, i < d := by
  induction p generalizing d with
  | ret xs => rfl
  | letE r p ih =>
    simp only [Program.Scoped, ih]
    constructor
    · intro ⟨hr,hp⟩ i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hr i hi
      · obtain ⟨j,hj,hji⟩ := List.mem_filterMap.mp hi
        cases j with
        | zero => simp at hji
        | succ j => simp at hji; subst i; have := hp (j+1) hj; omega
    · intro h
      refine ⟨fun i hi => h i (List.mem_append_left _ hi), ?_⟩
      intro i hi
      cases i with
      | zero => omega
      | succ i => have := h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1,hi,rfl⟩)); omega

theorem rename_scoped (p : Program) (f : Nat → Nat) (d : Nat)
    (h : ∀ i ∈ freeVars p, f i < d) : (renameProgram f p).Scoped d := by
  induction p generalizing f d with
  | ret xs =>
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact h j hj
  | letE r p ih =>
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [renameRhs_vars] at hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      exact h j (List.mem_append_left _ hj)
    · apply ih
      intro i hi
      cases i with
      | zero => simp [liftRename]
      | succ i =>
        have := h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1,hi,rfl⟩))
        simp only [liftRename]
        omega

theorem dceProgram_scoped (p : Program) (d : Nat) (h : p.Scoped d) : (dceProgram p).Scoped d := by
  induction p generalizing d with
  | ret xs => exact h
  | letE r p ih =>
    have hp := ih (d+1) h.2
    simp only [dceProgram]
    split
    · exact ⟨h.1,hp⟩
    · rename_i hn
      apply rename_scoped
      intro i hi
      have := (scoped_freeVars _ _).mp hp i hi
      have : i ≠ 0 := by intro he; subst i; exact hn hi
      cases i <;> simp_all

def ContextScoped (ctx : List Rhs) (d : Nat) : Prop := ∀ r ∈ ctx, r.Scoped d

theorem extendAvailable_scoped (r : Rhs) (ctx : List Rhs) (d : Nat)
    (hr : r.Scoped d) (hc : ContextScoped ctx d) : ContextScoped (extendAvailable r ctx) (d+1) := by
  intro s hs i hi
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  rw [renameRhs_vars] at hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hb : t.Scoped d := by
    rcases List.mem_cons.mp ht with he | hm
    · subst t; exact hr
    · exact hc t hm
  have := hb j hj
  omega

theorem simplifyRhs_scoped (r : Rhs) (ctx : List Rhs) (d : Nat)
    (hr : r.Scoped d) (hc : ContextScoped ctx d) : (simplifyRhs ctx r).Scoped d := by
  cases r with
  | gather g a =>
    simp only [simplifyRhs]
    cases hh : ctx[a]? with
    | none => exact hr
    | some s =>
      have hs := hc s (List.mem_of_getElem? hh)
      cases s with
      | literal vs => intro i hi; simp [Rhs.vars] at hi
      | gather f x =>
        simp only
        split
        · exact hs
        · exact hr
      | map n op args => exact hr
      | concat x y => exact hr
      | fold op shape x => exact hr
  | map n op args => exact hr
  | concat x y => exact hr
  | literal vs => exact hr
  | fold op shape x => exact hr

theorem simplifyWith_scoped (p : Program) (ctx : List Rhs) (d : Nat)
    (hp : p.Scoped d) (hc : ContextScoped ctx d) : (simplifyWith ctx p).Scoped d := by
  induction p generalizing ctx d with
  | ret xs => exact hp
  | letE r p ih =>
    have hs := simplifyRhs_scoped r ctx d hp.1 hc
    exact ⟨hs, ih _ (d+1) hp.2 (extendAvailable_scoped _ ctx d hs hc)⟩

theorem cseWith_scoped (p : Program) (ctx : List Rhs) (d : Nat)
    (hp : p.Scoped d) (hlen : ctx.length ≤ d) : (cseWith ctx p).Scoped d := by
  induction p generalizing ctx d with
  | ret xs => exact hp
  | letE r p ih =>
    have hq := ih (extendAvailable r ctx) (d+1) hp.2 (by simp [extendAvailable]; omega)
    simp only [cseWith]
    cases hf : findRhs r ctx with
    | none => exact ⟨hp.1,hq⟩
    | some v =>
      have hv : v < ctx.length := (List.getElem_of_getElem? (findRhs_sound r ctx v hf)).choose
      apply rename_scoped
      intro i hi
      have := (scoped_freeVars _ _).mp hq i hi
      cases i <;> simp only [dropBinder] <;> omega

theorem scopedB_complete (p : Program) (d : Nat) (h : p.Scoped d) : p.scopedB d = true := by
  induction p generalizing d with
  | ret xs => simpa [Program.scopedB, Program.Scoped, List.all_eq_true] using h
  | letE r p ih =>
    simp only [Program.scopedB, Bool.and_eq_true]
    exact ⟨by simpa [List.all_eq_true, Rhs.Scoped] using h.1, ih (d+1) h.2⟩

theorem aliasWith_scoped (p : Program) (ctx : List Rhs) (d : Nat) (hp : p.Scoped d) :
    (aliasWith ctx p).Scoped d := by
  induction p generalizing ctx d with
  | ret xs => exact hp
  | letE r p ih =>
    have hq := ih (extendAvailable r ctx) (d+1) hp.2
    simp only [aliasWith]
    cases ha : aliasRhs ctx r with
    | none => exact ⟨hp.1,hq⟩
    | some a =>
      have hv := hp.1 a (aliasRhs_var r ctx a ha)
      apply rename_scoped
      intro i hi
      have := (scoped_freeVars _ _).mp hq i hi
      cases i <;> simp only [dropBinder] <;> omega

theorem normalizeProgram_scopedB (p : Program) (d : Nat) (h : p.scopedB d = true) :
    (normalizeProgram p).scopedB d = true := by
  apply scopedB_complete
  apply dceProgram_scoped
  apply cseWith_scoped _ [] d
  · apply aliasWith_scoped
    exact simplifyWith_scoped p [] d (p.scopedB_sound d h) (by intro r hr; simp at hr)
  · simp


/-- Sum of arrays actually allocated by the source evaluator; inputs are excluded. -/
def arenaWords (env : Env) : Program → Nat
  | .ret _ => 0
  | .letE r p => (r.eval env).length + arenaWords (push (r.eval env) env) p

theorem arenaWords_congr (p : Program) (env other : Env)
    (h : ∀ i ∈ freeVars p, env i = other i) : arenaWords env p = arenaWords other p := by
  induction p generalizing env other with
  | ret xs => rfl
  | letE r p ih =>
    have hr := rhs_congr r env other (fun i hi => h i (List.mem_append_left _ hi))
    simp only [arenaWords, hr]
    congr 1
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1,hi,rfl⟩))

theorem arenaWords_rename (p : Program) (f : Nat → Nat) (env : Env) :
    arenaWords env (renameProgram f p) = arenaWords (fun i => env (f i)) p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [renameProgram, arenaWords, renameRhs_eval, ih]
    congr 2
    funext i
    cases i <;> rfl

theorem arenaWords_substitute (p : Program) (v : Nat) (env : Env) :
    arenaWords env (substitute v p) = arenaWords (push (env v) env) p := by
  rw [substitute, arenaWords_rename]
  congr 1
  funext i
  cases i <;> rfl

theorem dceProgram_arena_le (p : Program) (env : Env) : arenaWords env (dceProgram p) ≤ arenaWords env p := by
  induction p generalizing env with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    simp only [dceProgram]
    split
    · exact Nat.add_le_add_left (ih _) _
    · rename_i h
      rw [arenaWords_rename]
      have he : arenaWords (fun i => env i.pred) (dceProgram p) = arenaWords (push (r.eval env) env) (dceProgram p) := by
        apply arenaWords_congr
        intro i hi
        cases i with
        | zero => exact False.elim (h hi)
        | succ i => rfl
      rw [he]
      exact Nat.le_trans (ih _) (Nat.le_add_left _ _)

theorem cseWith_arena_le (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    arenaWords env (cseWith ctx p) ≤ arenaWords env p := by
  induction p generalizing ctx env with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    have hb := ih _ _ (extendAvailable_sound r ctx env h)
    simp only [cseWith]
    cases hf : findRhs r ctx with
    | none => exact Nat.add_le_add_left hb _
    | some i =>
      rw [arenaWords_substitute, ← h i r (findRhs_sound r ctx i hf)]
      exact Nat.le_trans hb (Nat.le_add_left _ _)

theorem aliasWith_arena_le (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    arenaWords env (aliasWith ctx p) ≤ arenaWords env p := by
  induction p generalizing ctx env with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    have hb := ih _ _ (extendAvailable_sound r ctx env h)
    simp only [aliasWith]
    cases hf : aliasRhs ctx r with
    | none => exact Nat.add_le_add_left hb _
    | some i =>
      rw [arenaWords_substitute, ← aliasRhs_sound r ctx env i h hf]
      exact Nat.le_trans hb (Nat.le_add_left _ _)

theorem simplifyWith_arena (p : Program) (ctx : List Rhs) (env : Env) (h : Available ctx env) :
    arenaWords env (simplifyWith ctx p) = arenaWords env p := by
  induction p generalizing ctx env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [simplifyWith, arenaWords]
    rw [ih _ _ (extendAvailable_sound _ ctx env h), simplifyRhs_sound r ctx env h]

theorem normalizeProgram_arenaWords_le (p : Program) (env : Env) :
    arenaWords env (normalizeProgram p) ≤ arenaWords env p := by
  apply Nat.le_trans (dceProgram_arena_le _ env)
  apply Nat.le_trans (cseWith_arena_le _ [] env (by intro i r h; simp at h))
  apply Nat.le_trans (aliasWith_arena_le _ [] env (by intro i r h; simp at h))
  rw [simplifyWith_arena p [] env (by intro i r h; simp at h)]
  exact Nat.le_refl _

/-- A chain compiler composes scalar bodies before creating a single SOAC.
The initial source stream is fetched once per element. -/
def chainExpr : List ScalarExpr → ScalarExpr
  | [] => .input 0
  | e::es => e.subst (fun i => match i with | 0 => chainExpr es | _+1 => .const 0#64)

def runPointwiseChain : List ScalarExpr → Vec → Vec
  | [], xs => xs
  | e::es, xs => (runPointwiseChain es xs).map (fun w => e.eval (unarySlots w))

theorem chainExpr_sound (es : List ScalarExpr) (xs : Vec) :
    xs.map (fun w => (chainExpr es).eval (unarySlots w)) = runPointwiseChain es xs := by
  induction es with
  | nil => simp [chainExpr, runPointwiseChain, ScalarExpr.eval, unarySlots]
  | cons e es ih =>
    simp only [chainExpr, ScalarExpr.subst_sound, runPointwiseChain, ← ih, List.map_map]
    apply List.map_congr_left
    intro w _
    congr 1
    funext i
    cases i <;> rfl

/-- Materialized writes before fusion: each nonempty stage writes its entire array. -/
def chainWrites (es : List ScalarExpr) (n : Nat) : Nat := (es.map (fun _ => n)).sum

def compilePointwiseChain (n : Nat) (es : List ScalarExpr) : FusedProgram :=
  .letE (mapKernel n [.var 0] (chainExpr es)) (.ret [0])

theorem compilePointwiseChain_sound (n : Nat) (es : List ScalarExpr) (env : Env) :
    evalFused env (compilePointwiseChain n es) =
      [runPointwiseChain es ((List.range n).map (fun i => (env 0).getD i 0#64))] := by
  simp only [compilePointwiseChain, evalFused, FusedRhs.eval, mapKernel,
    List.map_cons, List.map_nil, push]
  congr 1
  rw [← chainExpr_sound, List.map_map]
  apply List.map_congr_left
  intro i _
  rw [ScalarExpr.instantiate_sound]
  congr 1
  funext v
  cases v <;> rfl

/-- Every nonempty k-stage pointwise chain has k*N materialized writes and its
compiled kernel writes N words, independently of the scalar operators. -/
theorem pointwise_chain_writes (e : ScalarExpr) (es : List ScalarExpr) (n : Nat) (env : Env) :
    chainWrites (e::es) n = (es.length+1)*n ∧
      ((mapKernel n [.var 0] (chainExpr (e::es))).eval env).length = n := by
  constructor
  · simp [chainWrites, List.map_const', List.sum_replicate_nat, Nat.add_mul, Nat.add_comm]
  · simp [mapKernel, FusedRhs.eval]


theorem findRhs_complete (r : Rhs) (ctx : List Rhs) : findRhs r (r::ctx) = some 0 := by simp [findRhs]

example : Available [.literal [1#64,2#64]] (fun _ => [1#64,2#64]) := by
  intro i r h
  cases i with
  | zero => simp at h; subst r; rfl
  | succ i => simp at h

theorem Available_inhabited (r : Rhs) (env : Env) :
    ∃ ctx, ctx ≠ [] ∧ Available ctx (push (r.eval env) env) := by
  refine ⟨extendAvailable r [], by simp [extendAvailable], ?_⟩
  exact extendAvailable_sound r [] env (by intro i s hs; simp at hs)

theorem staticLength_complete (n : Nat) (op : ElemOp) (args : List Nat) :
    staticLength (.map n op args) = some n := by simp [staticLength]

theorem knownShape_complete (xs : Vec) : knownShape [.literal xs] 0 = some xs.length := by simp [knownShape, staticLength]

theorem aliasRhs_complete (xs : Vec) :
    aliasRhs [.literal xs] (.map xs.length (.scalar (.scale 1)) [0]) = some 0 := by
  simp [aliasRhs, knownShape, staticLength]

theorem StreamAvailable_inhabited (env : Env) : ∃ f, StreamAvailable f env := ⟨KernelInput.var, fun _ _ => rfl⟩

theorem producerStream_complete (n : Nat) (e : KernelInput) :
    producerStream (.mapKernel n e) = some (.bounded n e) := by simp [producerStream]

/-- Writes are separate from reads: duplication of arithmetic never creates a
hidden intermediate global array. -/
def globalWrites (env : Env) : FusedProgram → Nat
  | .ret _ => 0
  | .letE r p => (r.eval env).length + globalWrites (push (r.eval env) env) p

theorem globalWrites_congr (p : FusedProgram) (env other : Env)
    (h : ∀ i ∈ p.freeVars, env i = other i) : globalWrites env p = globalWrites other p := by
  induction p generalizing env other with
  | ret xs => rfl
  | letE r p ih =>
    have hr := r.congr env other (fun i hi => h i (List.mem_append_left _ hi))
    simp only [globalWrites, hr]
    congr 1
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_append_right _ (List.mem_filterMap.mpr ⟨i+1,hi,rfl⟩))

theorem globalWrites_rename (p : FusedProgram) (f : Nat → Nat) (env : Env) :
    globalWrites env (p.rename f) = globalWrites (fun i => env (f i)) p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [FusedProgram.rename, globalWrites, FusedRhs.rename_sound, ih]
    congr 2
    funext i
    cases i <;> rfl

theorem dceFused_writes_le (p : FusedProgram) (env : Env) : globalWrites env (dceFused p) ≤ globalWrites env p := by
  induction p generalizing env with
  | ret xs => exact Nat.le_refl _
  | letE r p ih =>
    simp only [dceFused]
    split
    · exact Nat.add_le_add_left (ih _) _
    · rename_i h
      rw [globalWrites_rename]
      have he : globalWrites (fun i => env i.pred) (dceFused p) = globalWrites (push (r.eval env) env) (dceFused p) := by
        apply globalWrites_congr
        intro i hi
        cases i with
        | zero => exact False.elim (h hi)
        | succ i => rfl
      rw [he]
      exact Nat.le_trans (ih _) (Nat.le_add_left _ _)

theorem inlineFused_writes (p : FusedProgram) (f : Nat → KernelInput) (env : Env)
    (h : StreamAvailable f env) : globalWrites env (inlineFused f p) = globalWrites env p := by
  induction p generalizing f env with
  | ret xs => rfl
  | letE r p ih =>
    simp only [inlineFused, globalWrites]
    rw [ih _ _ (extendStreams_sound _ f env h), FusedRhs.inline_sound r f env h]

theorem fuseVertical_writes_le (p : FusedProgram) (env : Env) :
    globalWrites env (fuseVertical p) ≤ globalWrites env p := by
  simp only [fuseVertical]
  split
  · exact Nat.le_trans (dceFused_writes_le _ env)
      (by rw [inlineFused_writes p KernelInput.var env (fun _ _ => rfl)]; exact Nat.le_refl _)
  · exact Nat.le_refl _

theorem compiled_chain_writes (n : Nat) (e : ScalarExpr) (es : List ScalarExpr) (env : Env) :
    globalWrites env (compilePointwiseChain n (e::es)) = n ∧ chainWrites (e::es) n = (es.length+1)*n := by
  exact ⟨by simp [compilePointwiseChain, globalWrites, mapKernel, FusedRhs.eval],
    (pointwise_chain_writes e es n env).1⟩


def unaryStream (op : ElemOp) (input : KernelInput) : KernelInput :=
  .prim op input (.const 0#64) (.const 0#64)

def twoStageMaps (n : Nat) (producer consumer : ElemOp) : FusedProgram :=
  .letE (.mapKernel n (unaryStream producer (.var 0)))
    (.letE (.mapKernel n (unaryStream consumer (.var 0))) (.ret [0]))

def composedMap (n : Nat) (producer consumer : ElemOp) : FusedProgram :=
  .letE (.mapKernel n (unaryStream consumer (.bounded n (unaryStream producer (.var 0))))) (.ret [0])

theorem twoStage_candidate (n : Nat) (producer consumer : ElemOp) :
    verticalCandidate (twoStageMaps n producer consumer) = composedMap n producer consumer := by
  simp [verticalCandidate, twoStageMaps, composedMap, unaryStream, inlineFused, FusedRhs.inline,
    KernelInput.bind, extendStreams, producerStream, KernelInput.rename, dceFused,
    FusedProgram.freeVars, FusedRhs.vars, KernelInput.vars, FusedProgram.rename, FusedRhs.rename,
    liftRename]

theorem composedMap_traffic (n : Nat) (producer consumer : ElemOp) :
    fixedTraffic (composedMap n producer consumer) = 2*n := by
  have hm : ((List.range n).map (fun i => if i < n then 1 else 0)).sum = n := by
    have he : (List.range n).map (fun i => if i < n then 1 else 0) = (List.range n).map (fun _ => 1) := by
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range.mp hi, ite_true]
    rw [he]
    simp [List.map_const', List.sum_replicate_nat]
  simpa [composedMap, unaryStream, fixedTraffic, FusedRhs.fixedTraffic, KernelInput.reads, Nat.two_mul] using
    congrArg (fun k => k+n) hm

theorem twoStage_traffic (n : Nat) (producer consumer : ElemOp) :
    fixedTraffic (twoStageMaps n producer consumer) = 4*n := by
  simp [twoStageMaps, unaryStream, fixedTraffic, FusedRhs.fixedTraffic, KernelInput.reads,
    List.map_const', List.sum_replicate_nat]
  omega

/-- A single-use unary producer removes exactly one N-word store and its
consumer's N-word load. This is the actual guarded optimizer's result. -/
theorem singleUseFusion_saves (n : Nat) (producer consumer : ElemOp) (env : Env) :
    hbmTrafficWords (fuseVertical (twoStageMaps n producer consumer)) env + 2*n =
      hbmTrafficWords (twoStageMaps n producer consumer) env := by
  have h : fixedTraffic (verticalCandidate (twoStageMaps n producer consumer)) ≤
      fixedTraffic (twoStageMaps n producer consumer) := by
    rw [twoStage_candidate, composedMap_traffic, twoStage_traffic]
    omega
  rw [fuseVertical, ite_eq_left h, twoStage_candidate]
  simp only [hbmTrafficWords, composedMap_traffic, twoStage_traffic]
  simp [dynamicTraffic, composedMap, twoStageMaps, FusedRhs.dynamicTraffic]
  omega

end Obend.Hardware.Gpu.SoacOptimize
