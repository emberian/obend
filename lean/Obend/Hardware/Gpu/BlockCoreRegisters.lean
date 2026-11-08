module
public import Obend.Hardware.Gpu.BlockCoreIndex
@[expose] public section
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
