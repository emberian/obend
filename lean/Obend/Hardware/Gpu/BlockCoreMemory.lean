module
public import Obend.Hardware.Gpu.BlockCoreRegisters
@[expose] public section
namespace Obend.Hardware.Gpu.BlockCoreMemory
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Source memory is a Core4 function of array number, then element index.
This denotes all out-of-bounds reads too, with the source evaluator's zero. -/
def Denotes (term : Term) (mem : Memory) : Prop :=
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
