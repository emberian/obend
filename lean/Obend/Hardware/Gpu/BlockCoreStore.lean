module
public import Obend.Hardware.Gpu.BlockCoreMemory
public import Obend.Hardware.Gpu.PhaseSemantics
@[expose] public section

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
