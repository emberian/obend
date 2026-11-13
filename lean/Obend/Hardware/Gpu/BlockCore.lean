module
public import Obend.Hardware.Gpu.ArraySourceCore
public import Obend.Hardware.ArrayKernel
public import Obend.Hardware.Gpu.PhaseSemantics
public section

section
/-! A bounded higher-order Core4 loop. The state may be an array function or a
register environment; it is never encoded by evaluating the source in Lean.
The recursive body and its source step occur once in the syntax. -/
namespace Obend.Hardware.Gpu.BlockCoreLoop
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- self, super, step, count, state. The successor branch binds count-1. -/
def loopSpec : Term :=
  .lam (.lam (.lam (.lam (.lam
    (.ifZero (.bound 1) (.bound 0)
      (.app (.app (.bound 3) (.bound 0))
        (.app (.app (.app (.bound 5) (.bound 3)) (.bound 0)) (.bound 1))))))))

def loop : Term := .fix loopSpec (.nat 0)
def call (step count state : Term) : Term := .app (.app (.app loop step) count) state

@[simp] theorem loopSpec_substitute (σ : Nat → Term) : loopSpec.substitute σ = loopSpec := by
  simp [loopSpec, Term.substitute, liftSubstitution, Term.rename]
@[simp] theorem loop_substitute (σ : Nat → Term) : loop.substitute σ = loop := by
  simp [loop, Term.substitute]
@[simp] theorem call_substitute (step count state : Term) (σ : Nat → Term) :
    (call step count state).substitute σ =
      call (step.substitute σ) (count.substitute σ) (state.substitute σ) := by
  simp [call]

theorem unfold_vars :
    Steps (call (.bound 0) (.bound 1) (.bound 2))
      (.ifZero (.bound 1) (.bound 2)
        (.app (.app (.bound 1) (.bound 0))
          (call (.bound 1) (.bound 0) (.bound 3)))) := by
  unfold call loop
  refine .next (.application _ (.application _ (.application _ (.fix _ _)))) ?_
  simp only [loopSpec]
  repeat first
    | exact Steps.refl _
    | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _))))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename])
    | (apply Steps.next (Step.application _ (Step.application _ (Step.application _ (Step.beta _ _)))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.application _ (Step.application _ (Step.beta _ _))); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.application _ (Step.beta _ _)); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])
    | (apply Steps.next (Step.beta _ _); simp only [instantiate, Term.substitute, liftSubstitution, Term.rename])

def subst (step count state : Term) : Nat → Term
  | 0 => step | 1 => count | _ => state

theorem zero (step state : Term) : Steps (call step (.nat 0) state) state := by
  have h := steps_substitute (subst step (.nat 0) state) unfold_vars
  simp only [call_substitute, Term.substitute, subst, liftSubstitution, Term.rename] at h
  exact steps_trans h (.next (.zero _ _) (.refl _))

theorem succ_vars (n : Nat) :
    Steps (call (.bound 0) (.nat (n+1)) (.bound 1))
      (.app (.app (.bound 0) (.nat n)) (call (.bound 0) (.nat n) (.bound 1))) := by
  have h := steps_substitute (subst (.bound 0) (.nat (n+1)) (.bound 1)) unfold_vars
  simp only [call_substitute, Term.substitute, subst, liftSubstitution, Term.rename] at h
  apply steps_trans h
  refine .next (.successor n _ _) ?_
  simp only [instantiate, call_substitute, Term.substitute]
  exact .refl _

theorem succ (step state : Term) (n : Nat) :
    Steps (call step (.nat (n+1)) state)
      (.app (.app step (.nat n)) (call step (.nat n) state)) := by
  have h := steps_substitute (subst step state state) (succ_vars n)
  simpa only [call_substitute, Term.substitute, subst] using h

/-- Any observation semantics closed under Core4 steps and the source body
lifts through the bounded loop, for every count and initial state. -/
theorem denotes {α : Type} (D : Term → α → Prop) (step : Term)
    (advance : Nat → α → α)
    (hsteps : ∀ t u value, Steps t u → D u value → D t value)
    (hstep : ∀ i t value, D t value → D (.app (.app step (.nat i)) t) (advance i value))
    (state : Term) (value : α) (hstate : D state value) (n : Nat) :
    D (call step (.nat n) state) ((List.range n).foldl (fun v i => advance i v) value) := by
  induction n with
  | zero => simpa using hsteps _ _ _ (zero step state) hstate
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact hsteps _ _ _ (succ step state n) (hstep n _ _ ih)

/-- Bounded source admission only needs the body invariant for indices actually
visited by this loop. No condition on unreachable logical lanes is required. -/
theorem denotes_bounded {α : Type} (D : Term → α → Prop) (step : Term)
    (advance : Nat → α → α)
    (hsteps : ∀ t u value, Steps t u → D u value → D t value)
    (n : Nat)
    (hstep : ∀ i < n, ∀ t value, D t value → D (.app (.app step (.nat i)) t) (advance i value))
    (state : Term) (value : α) (hstate : D state value) :
    D (call step (.nat n) state) ((List.range n).foldl (fun v i => advance i v) value) := by
  induction n with
  | zero => simpa using hsteps _ _ _ (zero step state) hstate
  | succ n ih =>
    rw [List.range_succ,List.foldl_append]
    exact hsteps _ _ _ (succ step state n)
      (hstep n (by omega) _ _ (ih (fun i hi => hstep i (by omega))))

end Obend.Hardware.Gpu.BlockCoreLoop
end

section
namespace Obend.Hardware.Gpu.BlockCoreIndex
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- General literal-result congruence, also for unbounded natural indices. -/
theorem ahead_nat {t u : Term} (n : Nat) (h : Ahead t u)
    (hs : Steps u (.nat n)) : Steps t (.nat n) := by
  obtain ⟨r, hr, ha⟩ := evaluates_ahead h ⟨hs, .natural _⟩
  exact steps_trans hr.1 (inv_literal_ahead (.nat _) ha)

theorem primitive_nat (op : Primitive) (a b : Term) (x y z : Nat)
    (ha : Steps a (.nat x)) (hb : Steps b (.nat y))
    (hv : primitiveResult op (.nat x) (.nat y) = some (.nat z)) :
    Steps (.binary op a b) (.nat z) := by
  apply ahead_nat z (.binary op (.run ha (.nat _)) (.run hb (.nat _)))
  exact .next (.primitive op _ _ _ (.natural _) (.natural _) hv) (.refl _)

/-- Symbolic indexed maps retain their workgroup and lane variables. Constants
and descriptor tables are literal data, never evaluations of a kernel/input. -/
def term (group lane : Term) : Ix → Term
  | .lit n => .nat n
  | .group => group
  | .lane => lane
  | .add a b => .binary .add (term group lane a) (term group lane b)
  | .mul a b => .binary .multiply (term group lane a) (term group lane b)
  | .div a n => .binary .divide (term group lane a) (.nat n)
  | .mod a n => .binary .modulo (term group lane a) (.nat n)
  | .lookup values i => .app (encodeNats values.toList) (term group lane i)

theorem term_substitute (ix : Ix) (g l : Term) (σ : Nat → Term) :
    (term g l ix).substitute σ = term (g.substitute σ) (l.substitute σ) ix := by
  induction ix <;> simp [term, Term.substitute, *, encodeNats_substitute]

theorem term_sound (ix : Ix) (g l : Term) (group lane : Nat)
    (hg : Steps g (.nat group)) (hl : Steps l (.nat lane)) :
    Steps (term g l ix) (.nat (ix.eval group lane)) := by
  induction ix with
  | lit n => exact .refl _
  | group => exact hg
  | lane => exact hl
  | add a b ha hb => exact primitive_nat .add _ _ _ _ _ ha hb rfl
  | mul a b ha hb => exact primitive_nat .multiply _ _ _ _ _ ha hb rfl
  | div a n ha => exact primitive_nat .divide _ _ _ _ _ ha (.refl _) rfl
  | mod a n ha => exact primitive_nat .modulo _ _ _ _ _ ha (.refl _) rfl
  | lookup values i hi =>
    apply ahead_nat _ (.app (.refl _) (.run hi (.nat _)))
    simpa only [Ix.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList] using
      encodeNats_apply values.toList (i.eval group lane)

end Obend.Hardware.Gpu.BlockCoreIndex
end

section
namespace Obend.Hardware.Gpu.BlockCoreRegisters
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu.Source
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Functional environment update. The old environment and new value are bound
once; the resulting index function uses their lexical variables. -/
def updateSpec (key : Nat) : Term :=
  .lam (.lam (.lam (.ifBool (.binary .equal (.bound 0) (.nat key))
    (.bound 1) (.app (.bound 2) (.bound 0)))))

def update (env : Term) (key : Nat) (value : Term) : Term :=
  .app (.app (updateSpec key) env) value

@[simp] theorem updateSpec_substitute (key : Nat) (σ : Nat → Term) :
    (updateSpec key).substitute σ = updateSpec key := by
  simp [updateSpec, Term.substitute, liftSubstitution, Term.rename]
@[simp] theorem update_substitute (env value : Term) (key : Nat) (σ : Nat → Term) :
    (update env key value).substitute σ = update (env.substitute σ) key (value.substitute σ) := by
  simp [update]

theorem update_apply_vars (key i : Nat) :
    Steps (.app (update (.bound 0) key (.bound 1)) (.nat i))
      (if i = key then .bound 1 else .app (.bound 0) (.nat i)) := by
  unfold update updateSpec
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  simp only [instantiate, Term.substitute, liftSubstitution, Term.rename]
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute, liftSubstitution, Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.ifCondition _ _ (.primitive .equal _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases h : i = key
  · simp only [primitiveResult, h, beq_self_eq_true, ↓reduceIte]
    exact .next (.ifTrue _ _) (.refl _)
  · simp only [primitiveResult, beq_eq_false_iff_ne.mpr h, h, ↓reduceIte]
    exact .next (.ifFalse _ _) (.refl _)

def pairSub (first second : Term) : Nat → Term
  | 0 => first | _ => second

theorem update_apply (env value : Term) (key i : Nat) :
    Steps (.app (update env key value) (.nat i))
      (if i = key then value else .app env (.nat i)) := by
  have h := steps_substitute (pairSub env value) (update_apply_vars key i)
  by_cases hi : i = key <;>
    simpa only [hi, ↓reduceIte, update_substitute, Term.substitute, pairSub] using h

/-- A register file is an ordinary Core4 function from register numbers to words. -/
def Denotes (term : Term) (env : Nat → Word) : Prop :=
  ∀ i, Steps (.app term (.nat i)) (.nat (env i).toNat)

theorem denotes_steps (a b : Term) (env : Nat → Word) (h : Steps a b)
    (hb : Denotes b env) : Denotes a env :=
  fun i => steps_trans (steps_app (.nat i) h) (hb i)

theorem update_sound (env value : Term) (rho : Nat → Word) (key : Nat) (v : Word)
    (he : Denotes env rho) (hv : Steps value (.nat v.toNat)) :
    Denotes (update env key value) (fun i => if i = key then v else rho i) := by
  intro i
  apply steps_trans (update_apply env value key i)
  by_cases hi : i = key
  · simpa only [hi, ↓reduceIte] using hv
  · simpa only [hi, ↓reduceIte] using he i

/-- Register-resident source let: each scalar body refers to the preceding file
through its binder, so source syntax does not duplicate producers. -/
def instruction (i : Instr) : Term :=
  .lam (update (.bound 0) i.dst (elemTerm i.op (i.args.map fun a => .app (.bound 0) (.nat a))))

theorem instruction_apply_vars (i : Instr) :
    Steps (.app (instruction i) (.bound 0))
      (update (.bound 0) i.dst (elemTerm i.op (i.args.map fun a => .app (.bound 0) (.nat a)))) := by
  refine .next (.beta _ _) ?_
  simp only [instruction, instantiate, update_substitute, Term.substitute,
    elemTerm_substitute, List.map_map, Function.comp_def]
  exact .refl _

@[simp] theorem instruction_substitute (i : Instr) (σ : Nat → Term) :
    (instruction i).substitute σ = instruction i := by
  simp [instruction, Term.substitute, update_substitute, elemTerm_substitute,
    List.map_map, Function.comp_def, liftSubstitution]

theorem instruction_apply (i : Instr) (env : Term) :
    Steps (.app (instruction i) env)
      (update env i.dst (elemTerm i.op (i.args.map fun a => .app env (.nat a)))) := by
  have h := steps_substitute (fun _ => env) (instruction_apply_vars i)
  simpa only [Term.substitute, instruction_substitute, update_substitute,
    elemTerm_substitute, List.map_map, Function.comp_def] using h

theorem arguments_sound (args : List Nat) (env : Term) (rho : Nat → Word)
    (h : Denotes env rho) (j : Nat) :
    Steps ((args.map fun a => .app env (.nat a)).getD j (.nat 0))
      (.nat ((args.map rho).getD j 0#64).toNat) := by
  induction args generalizing j with
  | nil => simp; exact .refl _
  | cons a args ih => cases j with
    | zero => exact h a
    | succ j => exact ih j

theorem instruction_sound (i : Instr) (env : Term) (rho : Nat → Word)
    (h : Denotes env rho) : Denotes (.app (instruction i) env) (stepInstr rho i) := by
  apply denotes_steps _ _ _ (instruction_apply i env)
  have hv := elemTerm_sound i.op _ _ (arguments_sound i.args env rho h)
  have hs := update_sound env _ rho i.dst _ h hv
  simpa only [stepInstr, beq_iff_eq] using hs

/-- General register networks, including the NTT's radix-4 butterflies, become
ordinary lexical Core4 lets. No transform-specific primitive is introduced. -/
def code (is : List Instr) (env : Term) : Term :=
  is.foldl (fun t i => .app (instruction i) t) env

theorem code_sound (is : List Instr) (env : Term) (rho : Nat → Word)
    (h : Denotes env rho) : Denotes (code is env) (runCode rho is) := by
  induction is generalizing env rho with
  | nil => exact h
  | cons i is ih => exact ih _ _ (instruction_sound i env rho h)

end Obend.Hardware.Gpu.BlockCoreRegisters
end

section
namespace Obend.Hardware.Gpu.BlockCoreMemory
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Source memory is a Core4 function of array number, then element index.
This denotes all out-of-bounds reads too, with the source evaluator's zero. -/
@[expose] def Denotes (term : Term) (mem : Memory) : Prop :=
  ∀ a i, Steps (.app (.app term (.nat a)) (.nat i))
    (.nat (((mem.getD a #[]).getD i 0#64).toNat))

theorem denotes_steps (a b : Term) (mem : Memory) (h : Steps a b)
    (hb : Denotes b mem) : Denotes a mem :=
  fun array i => steps_trans (steps_app (.nat i) (steps_app (.nat array) h)) (hb array i)

def read (source group lane : Term) (r : Read) : Term :=
  .app (.app source (.nat r.array)) (BlockCoreIndex.term group lane r.index)

theorem read_substitute (source group lane : Term) (r : Read) (σ : Nat → Term) :
    (read source group lane r).substitute σ =
      read (source.substitute σ) (group.substitute σ) (lane.substitute σ) r := by
  simp [read, Term.substitute, BlockCoreIndex.term_substitute]

theorem read_sound (source g l : Term) (r : Read) (mem : Memory) (group lane : Nat)
    (hm : Denotes source mem) (hg : Steps g (.nat group)) (hl : Steps l (.nat lane)) :
    Steps (read source g l r)
      (.nat (((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64).toNat)) := by
  apply BlockCoreIndex.ahead_nat _ (.app (.refl _)
    (.run (BlockCoreIndex.term_sound r.index g l group lane hg hl) (.nat _)))
  exact hm r.array _

/-- Indexed input values are lexical register bindings; every load reads the
same phase snapshot, independent of the progressively constructed register file. -/
def loads (source group lane : Term) (rs : List Read) (regs : Term) : Term :=
  rs.foldl (fun env r => BlockCoreRegisters.update env r.dst (read source group lane r)) regs

theorem loads_sound (source g l regs : Term) (rs : List Read) (mem : Memory)
    (group lane : Nat) (rho : Registers) (hm : Denotes source mem)
    (hg : Steps g (.nat group)) (hl : Steps l (.nat lane))
    (hr : BlockCoreRegisters.Denotes regs (fun a => rho.getD a 0#64)) :
    BlockCoreRegisters.Denotes (loads source g l rs regs)
      (fun a => (rs.foldl (fun m r => m.insert r.dst
        ((mem.getD r.array #[]).getD (r.index.eval group lane) 0#64)) rho).getD a 0#64) := by
  induction rs generalizing regs rho with
  | nil => exact hr
  | cons r rs ih =>
    apply ih
    have hs := BlockCoreRegisters.update_sound regs (read source g l r)
      (fun a => rho.getD a 0#64) r.dst _ hr (read_sound source g l r mem group lane hm hg hl)
    intro a
    have hv := hs a
    by_cases ha : a = r.dst
    · subst a
      simpa using hv
    · simpa [Std.HashMap.getD_insert, beq_iff_eq, ha, Ne.symm ha] using hv

def zeroRegisters : Term := .lam (.nat 0)

theorem zeroRegisters_sound : BlockCoreRegisters.Denotes zeroRegisters (fun _ => 0#64) := by
  intro i
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute]
  exact .refl _

def registers (ph : Phase) (source group lane : Term) : Term :=
  BlockCoreRegisters.code ph.code (loads source group lane ph.reads zeroRegisters)

/-- Every register in every indexed tile is the actual source register-network
value. The term consists of lexical lets and ordinary scalar Core4 operations. -/
theorem registers_sound (ph : Phase) (source g l : Term) (mem : Memory) (group lane : Nat)
    (hm : Denotes source mem) (hg : Steps g (.nat group)) (hl : Steps l (.nat lane)) :
    BlockCoreRegisters.Denotes (registers ph source g l)
      (fun a => (runRegisters ph.code (loadRegisters ph mem group lane)).getD a 0#64) := by
  have hz : BlockCoreRegisters.Denotes zeroRegisters (fun a => (∅ : Registers).getD a 0#64) := by
    simpa using zeroRegisters_sound
  have hs := loads_sound source g l zeroRegisters ph.reads mem group lane ∅ hm hg hl hz
  have hc := BlockCoreRegisters.code_sound ph.code _ _ hs
  intro a
  simpa only [registers, loadRegisters, runRegisters_sound] using hc a

end Obend.Hardware.Gpu.BlockCoreMemory
end

section
namespace Obend.Hardware.Gpu.BlockCoreEncoding
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Literal input memory only. The source program is a separate symbolic term;
no output evaluator is used to construct this encoding. -/
def rows : List (List Nat) → Term
  | [] => .lam (.lam (.nat 0))
  | r::rs => .lam (.ifZero (.bound 0) (encodeNats r) (.app (rows rs) (.bound 0)))

@[simp] theorem rows_substitute (rs : List (List Nat)) (σ : Nat → Term) :
    (rows rs).substitute σ = rows rs := by
  induction rs generalizing σ with
  | nil => simp [rows, Term.substitute]
  | cons r rs ih => simp [rows, Term.substitute, encodeNats_substitute, ih,
      liftSubstitution]

theorem rows_apply (rs : List (List Nat)) (a i : Nat) :
    Steps (.app (.app (rows rs) (.nat a)) (.nat i)) (.nat ((rs.getD a []).getD i 0)) := by
  induction rs generalizing a with
  | nil =>
    refine .next (.application _ (.beta _ _)) ?_
    simp only [rows, instantiate, Term.substitute]
    refine .next (.beta _ _) ?_
    simp only [instantiate, Term.substitute, List.getD_nil]
    exact .refl _
  | cons r rs ih =>
    refine .next (.application _ (.beta _ _)) ?_
    simp only [rows, instantiate, Term.substitute, encodeNats_substitute, rows_substitute, liftSubstitution]
    cases a with
    | zero =>
      refine .next (.application _ (.zero _ _)) ?_
      exact encodeNats_apply r i
    | succ a =>
      refine .next (.application _ (.successor a _ _)) ?_
      simp only [instantiate, Term.substitute, rows_substitute, List.getD_cons_succ, liftSubstitution]
      exact ih a

theorem map_getD {α β : Type} (f : α → β) (xs : List α) (d : α) (i : Nat) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

def memory (mem : Memory) : Term := rows (mem.toList.map fun row => row.toList.map (·.toNat))

theorem memory_sound (mem : Memory) : BlockCoreMemory.Denotes (memory mem) mem := by
  intro a i
  have h := rows_apply (mem.toList.map fun row => row.toList.map (·.toNat)) a i
  have outer := map_getD (fun row : Array Word => row.toList.map (·.toNat)) mem.toList #[] a
  have inner := map_getD (fun w : Word => w.toNat) (mem.toList.getD a #[]).toList 0#64 i
  simp only [Array.toList_empty, List.map_nil] at outer
  change (List.map (fun w : Word => w.toNat) (mem.toList.getD a #[]).toList).getD i 0 = _ at inner
  rw [outer, inner] at h
  simpa only [memory, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?] using h

end Obend.Hardware.Gpu.BlockCoreEncoding
end

section
/-! Dynamic indexed stores in ordinary Core4. The memory state, index, and value
are lexical arguments; neither source memory nor source results are encoded. -/
namespace Obend.Hardware.Gpu.BlockCoreStore
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core Obend.Hardware.Gpu.BlockCoreMemory
open Obend.Hardware.Gpu.BlockLower Obend.Hardware.Gpu.PhaseSemantics
set_option autoImplicit false

/-- old memory, write index, value, queried array, queried index. -/
def storeSpec (array : Nat) : Term :=
  .lam (.lam (.lam (.lam (.lam
    (.ifBool (.binary .equal (.bound 1) (.nat array))
      (.ifBool (.binary .equal (.bound 0) (.bound 3)) (.bound 2)
        (.app (.app (.bound 4) (.bound 1)) (.bound 0)))
      (.app (.app (.bound 4) (.bound 1)) (.bound 0)))))))

def store (array : Nat) (state index value : Term) : Term :=
  .app (.app (.app (storeSpec array) state) index) value

@[simp] theorem storeSpec_substitute (array : Nat) (σ : Nat → Term) :
    (storeSpec array).substitute σ = storeSpec array := by
  simp [storeSpec,Term.substitute,liftSubstitution,Term.rename]

@[simp] theorem store_substitute (array : Nat) (state index value : Term) (σ : Nat → Term) :
    (store array state index value).substitute σ =
      store array (state.substitute σ) (index.substitute σ) (value.substitute σ) := by
  simp [store]

theorem store_apply_vars (array index a i : Nat) :
    Steps (.app (.app (store array (.bound 0) (.nat index) (.bound 1)) (.nat a)) (.nat i))
      (if array = a ∧ index = i then .bound 1 else .app (.app (.bound 0) (.nat a)) (.nat i)) := by
  unfold store storeSpec
  refine .next (.application _ (.application _ (.application _ (.application _ (.beta _ _))))) ?_
  simp only [instantiate,Term.substitute,liftSubstitution,Term.rename]
  refine .next (.application _ (.application _ (.application _ (.beta _ _)))) ?_
  simp only [instantiate,Term.substitute,liftSubstitution,Term.rename]
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  simp only [instantiate,Term.substitute,liftSubstitution,Term.rename]
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate,Term.substitute,liftSubstitution,Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate,Term.substitute]
  refine .next (.ifCondition _ _ (.primitive .equal _ _ _ (.natural _) (.natural _) rfl)) ?_
  by_cases ha : array = a
  · subst a
    simp only [primitiveResult,beq_self_eq_true]
    refine .next (.ifTrue _ _) ?_
    refine .next (.ifCondition _ _ (.primitive .equal _ _ _ (.natural _) (.natural _) rfl)) ?_
    by_cases hi : index = i
    · subst i
      simp only [primitiveResult,beq_self_eq_true, true_and, and_self, ite_true]
      exact .next (.ifTrue _ _) (.refl _)
    · simp only [primitiveResult,beq_eq_false_iff_ne.mpr (Ne.symm hi),hi,true_and,ite_false]
      exact .next (.ifFalse _ _) (.refl _)
  · simp only [primitiveResult,beq_eq_false_iff_ne.mpr (Ne.symm ha),ha,false_and,ite_false]
    exact .next (.ifFalse _ _) (.refl _)

theorem store_apply (array index a i : Nat) (state value : Term) :
    Steps (.app (.app (store array state (.nat index) value) (.nat a)) (.nat i))
      (if array = a ∧ index = i then value else .app (.app state (.nat a)) (.nat i)) := by
  have h := steps_substitute (BlockCoreRegisters.pairSub state value) (store_apply_vars array index a i)
  by_cases he : array = a ∧ index = i <;>
    simpa [he,store_substitute,Term.substitute,BlockCoreRegisters.pairSub] using h

/-- An admitted store denotes Array.applyWrite at every observation, including
out-of-bounds observations. Good/Valid only constrain the actual write. -/
theorem store_sound (p : Program) (array index : Nat) (word : Word)
    (state ix value : Term) (mem : Memory) (hg : Obend.Hardware.Gpu.BlockLower.Good p mem) (hv : Valid p array index)
    (hm : Denotes state mem) (hi : Steps ix (.nat index)) (hvalue : Steps value (.nat word.toNat)) :
    Denotes (store array state ix value) (applyWrite mem (array,index,word)) := by
  intro a i
  rw [show (((applyWrite mem (array,index,word)).getD a #[]).getD i 0#64) =
      (if array = a ∧ index = i then word else (mem.getD a #[]).getD i 0#64) by
    simpa [writeLoc] using applyWrite_value p mem (array,index,word) hg hv a i]
  apply BlockCoreIndex.ahead_nat _
    (.app (.app (.app (.app (.app (.refl _) (.refl _)) (.run hi (.nat _))) (.refl _)) (.refl _)) (.refl _))
  apply steps_trans (store_apply array index a i state value)
  by_cases he : array = a ∧ index = i
  · simpa [he] using hvalue
  · simpa [he] using hm a i

end Obend.Hardware.Gpu.BlockCoreStore
end

section
/-! A phase is a compact Core4 map with a lexical immutable source snapshot.
Its logical-lane loop updates a separate state; scalar register code occurs once
in the lane body and every write observes that body's computed registers. -/
namespace Obend.Hardware.Gpu.BlockCorePhase
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core Obend.Hardware.Gpu.BlockCoreMemory
open Obend.Hardware.Gpu.BlockCoreStore Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

def stores (ws : List Write) (group lane regs state : Term) : Term :=
  ws.foldl (fun mem w => store w.array mem (BlockCoreIndex.term group lane w.index)
    (.app regs (.nat w.value))) state

theorem stores_substitute (ws : List Write) (group lane regs state : Term) (σ : Nat → Term) :
    (stores ws group lane regs state).substitute σ =
      stores ws (group.substitute σ) (lane.substitute σ) (regs.substitute σ) (state.substitute σ) := by
  induction ws generalizing state with
  | nil => rfl
  | cons w ws ih => simpa only [stores,List.foldl_cons,store_substitute,
      BlockCoreIndex.term_substitute,Term.substitute] using (ih
        (store w.array state (BlockCoreIndex.term group lane w.index) (.app regs (.nat w.value))))

theorem code_substitute (is : List Instr) (regs : Term) (σ : Nat → Term) :
    (BlockCoreRegisters.code is regs).substitute σ = BlockCoreRegisters.code is (regs.substitute σ) := by
  induction is generalizing regs with
  | nil => rfl
  | cons i is ih => simpa only [BlockCoreRegisters.code,List.foldl_cons,Term.substitute,
      BlockCoreRegisters.instruction_substitute] using ih (.app (BlockCoreRegisters.instruction i) regs)

theorem loads_substitute (rs : List Read) (source group lane regs : Term) (σ : Nat → Term) :
    (loads source group lane rs regs).substitute σ =
      loads (source.substitute σ) (group.substitute σ) (lane.substitute σ) rs (regs.substitute σ) := by
  induction rs generalizing regs with
  | nil => rfl
  | cons r rs ih => simpa only [loads,List.foldl_cons,BlockCoreRegisters.update_substitute,
      read_substitute] using ih (BlockCoreRegisters.update regs r.dst (read source group lane r))

theorem registers_substitute (ph : Phase) (source group lane : Term) (σ : Nat → Term) :
    (registers ph source group lane).substitute σ =
      registers ph (source.substitute σ) (group.substitute σ) (lane.substitute σ) := by
  simp [registers,code_substitute,loads_substitute,zeroRegisters,Term.substitute]

theorem stores_sound (p : Program) (ws : List Write) (g l regs state : Term)
    (group lane : Nat) (rho : Nat → Word) (mem : Memory) (hm : Denotes state mem)
    (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem) (hg : Steps g (.nat group)) (hl : Steps l (.nat lane))
    (hr : BlockCoreRegisters.Denotes regs rho)
    (hb : ∀ w ∈ ws, Valid p w.array (w.index.eval group lane)) :
    Denotes (stores ws g l regs state)
      ((ws.map fun w => (w.array,w.index.eval group lane,rho w.value)).foldl applyWrite mem) := by
  induction ws generalizing state mem with
  | nil => exact hm
  | cons w ws ih =>
    exact ih _ _
      (store_sound p w.array (w.index.eval group lane) (rho w.value) state _ _ mem hgood
        (hb w (by simp)) hm (BlockCoreIndex.term_sound w.index g l group lane hg hl) (hr w.value))
      (applyWrite_good p mem _ hgood) (fun w hw => hb w (by simp [hw]))

/-- snapshot, group, logical lane, evolving output state; the register result
is then a lexical let shared by all static stores of this invocation. -/
def laneSpec (ph : Phase) : Term :=
  .lam (.lam (.lam (.lam
    (.app (.lam (stores ph.writes (.bound 3) (.bound 2) (.bound 0) (.bound 1)))
      (registers ph (.bound 3) (.bound 2) (.bound 1))))))

def laneCall (ph : Phase) (snapshot group lane state : Term) : Term :=
  .app (.app (.app (.app (laneSpec ph) snapshot) group) lane) state

@[simp] theorem laneSpec_substitute (ph : Phase) (σ : Nat → Term) :
    (laneSpec ph).substitute σ = laneSpec ph := by
  simp [laneSpec,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]

@[simp] theorem laneCall_substitute (ph : Phase) (snapshot group lane state : Term) (σ : Nat → Term) :
    (laneCall ph snapshot group lane state).substitute σ = laneCall ph
      (snapshot.substitute σ) (group.substitute σ) (lane.substitute σ) (state.substitute σ) := by
  simp [laneCall]

theorem laneCall_unfold_vars (ph : Phase) :
    Steps (laneCall ph (.bound 0) (.bound 1) (.bound 2) (.bound 3))
      (stores ph.writes (.bound 1) (.bound 2)
        (registers ph (.bound 0) (.bound 1) (.bound 2)) (.bound 3)) := by
  unfold laneCall laneSpec
  refine .next (.application _ (.application _ (.application _ (.beta _ _)))) ?_
  simp only [instantiate,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  simp only [instantiate,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate,Term.substitute,stores_substitute,registers_substitute,liftSubstitution,Term.rename]
  exact .refl _

def subst4 (a b c d : Term) : Nat → Term
  | 0 => a | 1 => b | 2 => c | _ => d

theorem laneCall_unfold (ph : Phase) (snapshot group lane state : Term) :
    Steps (laneCall ph snapshot group lane state)
      (stores ph.writes group lane (registers ph snapshot group lane) state) := by
  have h := steps_substitute (subst4 snapshot group lane state) (laneCall_unfold_vars ph)
  simpa only [laneCall_substitute,stores_substitute,registers_substitute,Term.substitute,subst4] using h

theorem laneCall_sound (p : Program) (ph : Phase) (snapshot g l state : Term)
    (source mem : Memory) (group lane : Nat) (hs : Denotes snapshot source) (hm : Denotes state mem)
    (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem) (hg : Steps g (.nat group)) (hl : Steps l (.nat lane))
    (hb : ∀ w ∈ ph.writes, Valid p w.array (w.index.eval group lane)) :
    Denotes (laneCall ph snapshot g l state) ((laneWrites ph source group lane).foldl applyWrite mem) := by
  apply denotes_steps _ _ _ (laneCall_unfold ph snapshot g l state)
  exact stores_sound p ph.writes g l (registers ph snapshot g l) state group lane
    (fun a => (runRegisters ph.code (loadRegisters ph source group lane)).getD a 0#64)
    mem hm hgood hg hl (registers_sound ph snapshot g l source group lane hs hg hl) hb

/-- The loop body retains the one immutable snapshot as a lexical closure.
Only its output-state argument changes between logical lanes. -/
def phaseSpec (ph : Phase) : Term :=
  .lam (.lam (BlockCoreLoop.call (.app (.app (laneSpec ph) (.bound 1)) (.bound 0))
    (.nat ph.lanes) (.bound 1)))

def phase (ph : Phase) (snapshot group : Term) : Term :=
  .app (.app (phaseSpec ph) snapshot) group

@[simp] theorem phaseSpec_substitute (ph : Phase) (σ : Nat → Term) :
    (phaseSpec ph).substitute σ = phaseSpec ph := by
  simp [phaseSpec,Term.substitute,BlockCoreLoop.call_substitute,liftSubstitution,Term.rename]

@[simp] theorem phase_substitute (ph : Phase) (snapshot group : Term) (σ : Nat → Term) :
    (phase ph snapshot group).substitute σ = phase ph (snapshot.substitute σ) (group.substitute σ) := by
  simp [phase]

theorem phase_unfold_vars (ph : Phase) :
    Steps (phase ph (.bound 0) (.bound 1))
      (BlockCoreLoop.call (.app (.app (laneSpec ph) (.bound 0)) (.bound 1)) (.nat ph.lanes) (.bound 0)) := by
  unfold phase phaseSpec
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate,Term.substitute,BlockCoreLoop.call_substitute,laneSpec_substitute,liftSubstitution,Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate,Term.substitute,BlockCoreLoop.call_substitute,laneSpec_substitute,liftSubstitution,Term.rename]
  exact .refl _

theorem phase_unfold (ph : Phase) (snapshot group : Term) :
    Steps (phase ph snapshot group)
      (BlockCoreLoop.call (.app (.app (laneSpec ph) snapshot) group) (.nat ph.lanes) snapshot) := by
  have h := steps_substitute (BlockCoreRegisters.pairSub snapshot group) (phase_unfold_vars ph)
  simpa only [phase_substitute,BlockCoreLoop.call_substitute,laneSpec_substitute,Term.substitute,
    BlockCoreRegisters.pairSub] using h

theorem lane_fold_eq (ph : Phase) (source mem : Memory) (group : Nat) (lanes : List Nat) :
    ((lanes.flatMap (laneWrites ph source group)).foldl applyWrite mem) =
      lanes.foldl (fun m l => (laneWrites ph source group l).foldl applyWrite m) mem := by
  induction lanes generalizing mem with
  | nil => rfl
  | cons l ls ih => simp only [List.flatMap_cons,List.foldl_append,List.foldl_cons,ih]

/-- Every symbolic Core4 phase denotes its actual simultaneous-source evaluator.
The invariant reads the original snapshot in every lane; it never encodes an
already evaluated output array. Bounds are supplied by source admission. -/
theorem phase_sound (p : Program) (ph : Phase) (snapshot g : Term) (mem : Memory) (group : Nat)
    (hm : Denotes snapshot mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hg : Steps g (.nat group)) (hb : PhaseInBounds p ph group) :
    Denotes (phase ph snapshot g) (evalPhase ph group mem) := by
  apply denotes_steps _ _ _ (phase_unfold ph snapshot g)
  let D := fun t m => Obend.Hardware.Gpu.BlockLower.Good p m ∧ Denotes t m
  have hloop := BlockCoreLoop.denotes_bounded D (.app (.app (laneSpec ph) snapshot) g)
    (fun lane state => (laneWrites ph mem group lane).foldl applyWrite state)
    (by intro t u value h hu; exact ⟨hu.1,denotes_steps t u value h hu.2⟩) ph.lanes
    (by
      intro lane hl t current ht
      exact ⟨foldWrites_good p current _ ht.1,
        laneCall_sound p ph snapshot g (.nat lane) t mem current group lane hm ht.2 ht.1 hg
          (.refl _) (hb.2 lane hl)⟩) snapshot mem ⟨hgood,hm⟩
  simpa only [evalPhase,← lane_fold_eq] using hloop.2

end Obend.Hardware.Gpu.BlockCorePhase
end

section
/-! Compact Core4 interpretation of the existing ArrayKernel source language.
Phase and dispatch lists are source syntax; logical lanes and workgroups remain
bounded loops. The constructor never evaluates source outputs in Lean. -/
namespace Obend.Hardware.Gpu.BlockCoreProgram
open Obend.Core.Term Obend.Equiv Obend.Core.TermTraverse
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core Obend.Hardware.Gpu.BlockCoreMemory
open Obend.Hardware.Gpu.BlockCorePhase Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

def phases (ps : List Phase) (state group : Term) : Term :=
  ps.foldl (fun mem ph => phase ph mem group) state

theorem phases_substitute (ps : List Phase) (state group : Term) (σ : Nat → Term) :
    (phases ps state group).substitute σ = phases ps (state.substitute σ) (group.substitute σ) := by
  induction ps generalizing state with
  | nil => rfl
  | cons ph ps ih => simpa only [phases,List.foldl_cons,phase_substitute] using ih (phase ph state group)

theorem phases_sound (p : Program) (ps : List Phase) (state g : Term) (mem : Memory) (group : Nat)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hg : Steps g (.nat group)) (hb : ∀ ph ∈ ps, PhaseInBounds p ph group) :
    Denotes (phases ps state g) (ps.foldl (fun m ph => evalPhase ph group m) mem) := by
  induction ps generalizing state mem with
  | nil => exact hm
  | cons ph ps ih =>
    exact ih _ _ (phase_sound p ph state g mem group hm hgood hg (hb ph (by simp)))
      (foldWrites_good p mem _ hgood) (fun ph hp => hb ph (by simp [hp]))

/-- A workgroup body binds its group number and state. -/
def groupSpec (d : Dispatch) : Term := .lam (.lam (phases d.phases (.bound 0) (.bound 1)))
def groupCall (d : Dispatch) (group state : Term) : Term := .app (.app (groupSpec d) group) state

@[simp] theorem groupSpec_substitute (d : Dispatch) (σ : Nat → Term) :
    (groupSpec d).substitute σ = groupSpec d := by
  simp [groupSpec,Term.substitute,phases_substitute,liftSubstitution,Term.rename]

@[simp] theorem groupCall_substitute (d : Dispatch) (group state : Term) (σ : Nat → Term) :
    (groupCall d group state).substitute σ = groupCall d (group.substitute σ) (state.substitute σ) := by
  simp [groupCall]

theorem groupCall_unfold_vars (d : Dispatch) :
    Steps (groupCall d (.bound 0) (.bound 1)) (phases d.phases (.bound 1) (.bound 0)) := by
  unfold groupCall groupSpec
  refine .next (.application _ (.beta _ _)) ?_
  simp only [instantiate,Term.substitute,phases_substitute,liftSubstitution,Term.rename]
  refine .next (.beta _ _) ?_
  simp only [instantiate,Term.substitute,phases_substitute,liftSubstitution,Term.rename]
  exact .refl _

theorem groupCall_unfold (d : Dispatch) (group state : Term) :
    Steps (groupCall d group state) (phases d.phases state group) := by
  have h := steps_substitute (BlockCoreRegisters.pairSub group state) (groupCall_unfold_vars d)
  simpa only [groupCall_substitute,phases_substitute,Term.substitute,BlockCoreRegisters.pairSub] using h

theorem groupCall_sound (p : Program) (d : Dispatch) (g state : Term) (mem : Memory) (group : Nat)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hg : Steps g (.nat group)) (hb : ∀ ph ∈ d.phases, PhaseInBounds p ph group) :
    Denotes (groupCall d g state) (evalGroup d group mem) := by
  exact denotes_steps _ _ _ (groupCall_unfold d g state)
    (phases_sound p d.phases state g mem group hm hgood hg hb)

def dispatch (d : Dispatch) (state : Term) : Term :=
  BlockCoreLoop.call (groupSpec d) (.nat d.groups) state

@[simp] theorem dispatch_substitute (d : Dispatch) (state : Term) (σ : Nat → Term) :
    (dispatch d state).substitute σ = dispatch d (state.substitute σ) := by
  simp [dispatch,BlockCoreLoop.call_substitute,Term.substitute]

theorem dispatch_sound (p : Program) (d : Dispatch) (state : Term) (mem : Memory)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hb : DispatchInBounds p d) : Denotes (dispatch d state) (evalDispatch d mem) := by
  let D := fun t m => Obend.Hardware.Gpu.BlockLower.Good p m ∧ Denotes t m
  exact (BlockCoreLoop.denotes_bounded D (groupSpec d) (evalGroup d)
    (by intro t u value h hu; exact ⟨hu.1,denotes_steps t u value h hu.2⟩) d.groups
    (by
      intro group hg t current ht
      exact ⟨evalGroup_good p d group current ht.1,
        groupCall_sound p d (.nat group) t current group ht.2 ht.1 (.refl _) (hb group hg)⟩)
    state mem ⟨hgood,hm⟩).2

def program (p : Program) (state : Term) : Term :=
  p.dispatches.foldl (fun mem d => dispatch d mem) state

theorem program_substitute (p : Program) (state : Term) (σ : Nat → Term) :
    (program p state).substitute σ = program p (state.substitute σ) := by
  unfold program
  induction p.dispatches generalizing state with
  | nil => rfl
  | cons d ds ih => simpa only [List.foldl_cons,dispatch_substitute] using ih (dispatch d state)

theorem dispatch_good (p : Program) (d : Dispatch) (mem : Memory)
    (hg : Obend.Hardware.Gpu.BlockLower.Good p mem) :
    Obend.Hardware.Gpu.BlockLower.Good p (evalDispatch d mem) := by
  unfold evalDispatch
  induction List.range d.groups generalizing mem with
  | nil => exact hg
  | cons g gs ih => exact ih _ (evalGroup_good p d g mem hg)

theorem dispatches_sound (p : Program) (ds : List Dispatch) (state : Term) (mem : Memory)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hb : ∀ d ∈ ds, DispatchInBounds p d) :
    Denotes (ds.foldl (fun t d => dispatch d t) state) (ds.foldl (fun m d => evalDispatch d m) mem) := by
  induction ds generalizing state mem with
  | nil => exact hm
  | cons d ds ih =>
    exact ih _ _ (dispatch_sound p d state mem hm hgood (hb d (by simp)))
      (dispatch_good p d mem hgood) (fun d hd => hb d (by simp [hd]))

/-- The actual admitted source program denotes its actual evaluator for every
input memory, with no arithmetic, transform, or output-equality premise. -/
theorem program_sound (p : Program) (state : Term) (mem : Memory)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hc : p.check = .ok ()) : Denotes (program p state) (evalProgram p mem) :=
  dispatches_sound p p.dispatches state mem hm hgood (boundsSafe_sound p (p.check_boundsSafe hc))

/-- Closed, compact Core4 source term taking one encoded input memory argument. -/
def source (p : Program) : Term := .lam (program p (.bound 0))

@[simp] theorem source_substitute (p : Program) (σ : Nat → Term) :
    (source p).substitute σ = source p := by
  simp [source,Term.substitute,program_substitute,liftSubstitution]

theorem source_apply (p : Program) (state : Term) :
    Steps (.app (source p) state) (program p state) := by
  refine .next (.beta _ _) ?_
  simp only [source,instantiate,program_substitute,Term.substitute]
  exact .refl _

theorem source_sound (p : Program) (state : Term) (mem : Memory)
    (hm : Denotes state mem) (hgood : Obend.Hardware.Gpu.BlockLower.Good p mem)
    (hc : p.check = .ok ()) : Denotes (.app (source p) state) (evalProgram p mem) :=
  denotes_steps _ _ _ (source_apply p state) (program_sound p state mem hm hgood hc)

end Obend.Hardware.Gpu.BlockCoreProgram
end

end
