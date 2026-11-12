module
public import Obend.Hardware.Gpu.Ntt
public import Obend.Hardware.Gpu.GoldilocksSourceCorrect
@[expose] public section
namespace Obend.Hardware.Gpu.NttFieldCorrect
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.GoldilocksSource Obend.Hardware.Gpu.GoldilocksSourceCorrect
open Obend.Hardware.Gpu.Ntt.BlockNtt Obend.Apps.ZkNtt
set_option autoImplicit false

/-- A canonical field value in an allocated register of the actual builder. -/
structure FieldValue (st : Build) (env : Nat → Word) (r value : Nat) : Prop where
  bound : r < st.lengths.size
  value_eq : (evalBuild st env r).toNat = value
  canonical : value < goldilocksPrime

theorem FieldValue.mono {st after : Build} {env : Nat → Word} {r value : Nat}
    (h : FieldValue st env r value) (he : BuildExtends st after) : FieldValue after env r value := by
  exact ⟨Nat.lt_of_lt_of_le h.bound he.size_le,
    congrArg BitVec.toNat (he.frame env r h.bound) |>.trans h.value_eq,h.canonical⟩

theorem add_field (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (glAdd 1 k a b).run st
    FieldValue out.2 env out.1 ((av+bv)%goldilocksPrime) := by
  have hs := glAdd_sound st env 1 k a b ha.bound hb.bound hk
    (by rw [ha.value_eq]; exact ha.canonical) (by rw [hb.value_eq]; exact hb.canonical)
  have hc := glAdd_coordinates st 1 k a b
  dsimp only at hs ⊢
  rw [ha.value_eq,hb.value_eq] at hs
  exact ⟨by omega,hs.2,hs.2 ▸ hs.1⟩

theorem sub_field (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (glSub 1 k a b).run st
    FieldValue out.2 env out.1 ((av+goldilocksPrime-bv)%goldilocksPrime) := by
  have hs := glSub_sound st env 1 k a b ha.bound hb.bound hk
    (by rw [ha.value_eq]; exact ha.canonical) (by rw [hb.value_eq]; exact hb.canonical)
  have hc := glSub_coordinates st 1 k a b
  dsimp only at hs ⊢
  rw [ha.value_eq,hb.value_eq] at hs
  exact ⟨by omega,hs.2,hs.2 ▸ hs.1⟩

/-- The unit-twiddle branch executes the actual field add/sub builders. -/
theorem butterfly_none (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (butterfly k a b none).run st
    BuildExtends st out.2 ∧ out.1.read = none ∧
      FieldValue out.2 env out.1.sum ((av+bv)%goldilocksPrime) ∧
      FieldValue out.2 env out.1.high ((av+goldilocksPrime-bv)%goldilocksPrime) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  have hs := add_field st env k a b av bv hk ha hb
  have hd := sub_field sum.2 env k a b av bv (hk.mono he) (ha.mono he) (hb.mono he)
  simp only [butterfly,bind_run,pure_run]
  change BuildExtends st diff.2 ∧ _ ∧ _ ∧ _
  exact ⟨he.trans hf,True.intro,hs.mono hf,hd⟩

/-- A non-unit twiddle is a fresh source load; it may contain any 64-bit word. -/
theorem butterfly_some (st : Build) (env : Nat → Word) (k : GlConsts) (a b av bv : Nat)
    (index : Ix) (hstart : BuildExtends {} st)
    (hk : ConstsAt st env k) (ha : FieldValue st env a av) (hb : FieldValue st env b bv) :
    let out := (butterfly k a b (some index)).run st
    BuildExtends st out.2 ∧
      out.1.read = some ⟨st.lengths.size+10,4,index⟩ ∧
      FieldValue out.2 env out.1.sum ((av+bv)%goldilocksPrime) ∧
      FieldValue out.2 env out.1.high
        ((((av+goldilocksPrime-bv)%goldilocksPrime)*(env (st.lengths.size+10)).toNat)%goldilocksPrime) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  let tw := (newWire 1).run diff.2
  let high := (glMul 1 k diff.1 tw.1).run tw.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  have ht := newWire_extends diff.2 1
  have hm := glMul_extends tw.2 1 k diff.1 tw.1
  have hs := add_field st env k a b av bv hk ha hb
  have hd := sub_field sum.2 env k a b av bv (hk.mono he) (ha.mono he) (hb.mono he)
  have hdc := glSub_coordinates sum.2 1 k a b
  have hsc := glAdd_coordinates st 1 k a b
  have htw : tw.1 = st.lengths.size+10 := by
    dsimp only [tw]; rw [newWire_run]
    have hdsize : diff.2.lengths.size = sum.2.lengths.size+5 := hdc.2
    have hssize : sum.2.lengths.size = st.lengths.size+5 := hsc.2
    rw [hdsize,hssize]
  have htb : tw.1 < tw.2.lengths.size := by simp [tw,newWire_run]
  have htv : evalBuild tw.2 env tw.1 = env (st.lengths.size+10) := by
    change evalBuild diff.2 env tw.1 = _
    rw [(hstart.trans (he.trans hf)).fresh_value env tw.1 (by change diff.2.lengths.size ≤ diff.2.lengths.size; exact Nat.le_refl _)]
    rw [htw]
  have hdm := hd.mono ht
  have hval := glMul_sound tw.2 env 1 k diff.1 tw.1 hdm.bound htb
    (((hk.mono he).mono hf).mono ht)
  have hmc := glMul_coordinates tw.2 1 k diff.1 tw.1
  dsimp only at hval
  rw [hdm.value_eq,htv] at hval
  have hhigh : FieldValue high.2 env high.1
      ((((av+goldilocksPrime-bv)%goldilocksPrime)*(env (st.lengths.size+10)).toNat)%goldilocksPrime) :=
    ⟨by dsimp only [high]; omega,hval.2,hval.2 ▸ hval.1⟩
  simp only [butterfly,bind_run,pure_run]
  change BuildExtends st high.2 ∧ _ ∧ _ ∧ _
  exact ⟨((he.trans hf).trans ht).trans hm,by rw [htw],((hs.mono hf).mono ht).mono hm,hhigh⟩

/-- The source loop invariant may mention both the loop accumulator and the
actual register-builder state; every iteration is interpreted, including exit. -/
theorem forIn_state_preserves {α β : Type} (xs : List α)
    (body : α → β → BuildM (ForInStep β)) (P : β → Build → Prop)
    (step : ∀ a b st, P b st → P ((body a b).run st).1.value ((body a b).run st).2)
    (b : β) (st : Build) (hb : P b st) :
    P ((forIn xs b body).run st).1 ((forIn xs b body).run st).2 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using hb
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st hb
    cases he : (body a b).run st with
    | mk result after =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact ih out after hp

theorem forIn_extends {α β : Type} (xs : List α)
    (body : α → β → BuildM (ForInStep β))
    (step : ∀ a b st, BuildExtends st ((body a b).run st).2)
    (b : β) (st : Build) : BuildExtends st ((forIn xs b body).run st).2 := by
  induction xs generalizing b st with
  | nil => simpa only [List.forIn_nil,pure_run] using BuildExtends.refl st
  | cons a xs ih =>
    rw [List.forIn_cons,bind_run]
    have hp := step a b st
    cases he : (body a b).run st with
    | mk result after =>
      rw [he] at hp
      cases result with
      | done out => exact hp
      | yield out => exact hp.trans (ih out after)

/-- Both actual butterfly branches allocate fresh destinations only. -/
theorem butterfly_extends (st : Build) (k : GlConsts) (a b : Nat) (twiddle : Option Ix) :
    BuildExtends st ((butterfly k a b twiddle).run st).2 := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have he := glAdd_extends st 1 k a b
  have hf := glSub_extends sum.2 1 k a b
  cases twiddle with
  | none =>
    simp only [butterfly,bind_run,pure_run]
    exact he.trans hf
  | some index =>
    let tw := (newWire 1).run diff.2
    simp only [butterfly,bind_run,pure_run]
    exact ((he.trans hf).trans (newWire_extends diff.2 1)).trans
      (glMul_extends tw.2 1 k diff.1 tw.1)

/-- Exact allocation and load metadata of both real butterfly branches. -/
theorem butterfly_coordinates (st : Build) (k : GlConsts) (a b : Nat) (twiddle : Option Ix) :
    let out := (butterfly k a b twiddle).run st
    out.1.sum = st.lengths.size+4 ∧
      out.1.high = st.lengths.size+(if twiddle.isSome then 50 else 9) ∧
      out.2.lengths.size = st.lengths.size+(if twiddle.isSome then 51 else 10) ∧
      out.1.read = twiddle.map (fun index => ⟨st.lengths.size+10,4,index⟩) := by
  let sum := (glAdd 1 k a b).run st
  let diff := (glSub 1 k a b).run sum.2
  have hs := glAdd_coordinates st 1 k a b
  have hd := glSub_coordinates sum.2 1 k a b
  change sum.1 = st.lengths.size+4 ∧ sum.2.lengths.size = st.lengths.size+5 at hs
  change diff.1 = sum.2.lengths.size+4 ∧ diff.2.lengths.size = sum.2.lengths.size+5 at hd
  cases twiddle with
  | none =>
    simp only [butterfly,bind_run,pure_run,Option.isSome_none,Bool.false_eq_true,ite_false,Option.map_none]
    change sum.1 = _ ∧ diff.1 = _ ∧ diff.2.lengths.size = _ ∧ _
    exact ⟨hs.1,by omega,by omega,True.intro⟩
  | some index =>
    let tw := (newWire 1).run diff.2
    let high := (glMul 1 k diff.1 tw.1).run tw.2
    have ht : tw.1 = diff.2.lengths.size ∧ tw.2.lengths.size = diff.2.lengths.size+1 := by
      simp [tw,newWire_run]
    have hm := glMul_coordinates tw.2 1 k diff.1 tw.1
    change high.1 = tw.2.lengths.size+39 ∧ high.2.lengths.size = tw.2.lengths.size+40 at hm
    have htw : tw.1 = st.lengths.size+10 := by omega
    simp only [butterfly,bind_run,pure_run,Option.isSome_some,ite_true,Option.map_some]
    change sum.1 = _ ∧ high.1 = _ ∧ high.2.lengths.size = _ ∧ _
    exact ⟨hs.1,by omega,by omega,by rw [htw]⟩

end Obend.Hardware.Gpu.NttFieldCorrect
end
