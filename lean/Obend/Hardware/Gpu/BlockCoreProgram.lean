module
public import Obend.Hardware.Gpu.BlockCorePhase
@[expose] public section

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
