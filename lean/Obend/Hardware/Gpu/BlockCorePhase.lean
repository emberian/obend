module
public import Obend.Hardware.Gpu.BlockCoreStore
@[expose] public section

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
