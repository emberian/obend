/-
# Obend.Hardware.Gpu.Rdna2.Sym — a symbolic run of the model says what every concrete run computes

`SymMem` is memory as a symbolic run sees it: the dwords the wave has stored, over a base view of what
memory held when the wave started (a term per readable dword). `RV env` is a pair of a word and a term
that evaluates to it when memory holds `env`; `RM env m0` a pair of a concrete memory and a symbolic one
that agree on every word the symbolic one can load, and agree with `m0` (the memory the wave started
from) on every word the wave has not stored. Both are a `Dom`/`MemDom` instance, built from the
evaluation laws of `Term`; projecting to the word is a homomorphism to the concrete model, projecting to
the term one to the symbolic run that also reflects unknown values. `run_hom` (`Natural`) then gives
`wave_sound`: if the symbolic run of a wave succeeds, the concrete run from any memory the base view
describes succeeds too, ends in the same control state, holds `eval env u` wherever the symbolic run
holds `u`, and leaves every other dword as it found it.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Natural
public import Obend.Hardware.Gpu.Rdna2.Term
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. Symbolic memory -/

structure SymMem where
  stores : Std.HashMap UInt64 Tm
  base : UInt64 → Option Tm

def SymMem.load (m : SymMem) (a : UInt64) : Option Tm :=
  match m.stores.get? a with
  | some t => some t
  | none => m.base a

instance : MemDom SymMem Tm where
  load := SymMem.load
  store m a v := { m with stores := m.stores.insert a v }

abbrev SymWave := GWave Tm SymMem

/-! ## 2. Pairs of a value and a term that evaluates to it -/

section
variable (env : UInt64 → UInt32)

structure RV where
  c : UInt32
  t : Tm
  ok : t.eval env = c

open Tm in
instance : Dom (RV env) where
  lit c := ⟨c, Dom.lit c, eval_lit' env c⟩
  conc x := Dom.conc x.t
  add a b := ⟨Dom.add a.c b.c, Dom.add a.t b.t, by rw [eval_add, a.ok, b.ok]⟩
  sub a b := ⟨Dom.sub a.c b.c, Dom.sub a.t b.t, by rw [eval_sub, a.ok, b.ok]⟩
  mul a b := ⟨Dom.mul a.c b.c, Dom.mul a.t b.t, by rw [eval_mul, a.ok, b.ok]⟩
  mulHi a b := ⟨Dom.mulHi a.c b.c, Dom.mulHi a.t b.t, by rw [eval_mulHi, a.ok, b.ok]⟩
  band a b := ⟨Dom.band a.c b.c, Dom.band a.t b.t, by rw [eval_and, a.ok, b.ok]⟩
  bor a b := ⟨Dom.bor a.c b.c, Dom.bor a.t b.t, by rw [eval_or, a.ok, b.ok]⟩
  shl a b := ⟨Dom.shl a.c b.c, Dom.shl a.t b.t, by rw [eval_shl, a.ok, b.ok]⟩
  ite c a b := ⟨Dom.ite c.c a.c b.c, Dom.ite c.t a.t b.t, by rw [eval_ite, c.ok, a.ok, b.ok]⟩
  carry a b := ⟨Dom.carry a.c b.c, Dom.carry a.t b.t, by rw [eval_carry, a.ok, b.ok]⟩
  borrow a b := ⟨Dom.borrow a.c b.c, Dom.borrow a.t b.t, by rw [eval_borrow, a.ok, b.ok]⟩
  addc a b c := ⟨Dom.addc a.c b.c c.c, Dom.addc a.t b.t c.t, by rw [eval_addc, a.ok, b.ok, c.ok]⟩
  carryc a b c := ⟨Dom.carryc a.c b.c c.c, Dom.carryc a.t b.t c.t, by rw [eval_carryc, a.ok, b.ok, c.ok]⟩
  subc a b c := ⟨Dom.subc a.c b.c c.c, Dom.subc a.t b.t c.t, by rw [eval_subc, a.ok, b.ok, c.ok]⟩
  borrowc a b c := ⟨Dom.borrowc a.c b.c c.c, Dom.borrowc a.t b.t c.t, by rw [eval_borrowc, a.ok, b.ok, c.ok]⟩
  ule a b := ⟨Dom.ule a.c b.c, Dom.ule a.t b.t, by rw [eval_ule, a.ok, b.ok]⟩
  ugt a b := ⟨Dom.ugt a.c b.c, Dom.ugt a.t b.t, by rw [eval_ugt, a.ok, b.ok]⟩
  ult64 a0 a1 b0 b1 := ⟨Dom.ult64 a0.c a1.c b0.c b1.c, Dom.ult64 a0.t a1.t b0.t b1.t,
    by rw [eval_ult64, a0.ok, a1.ok, b0.ok, b1.ok]⟩
  ne64 a0 a1 b0 b1 := ⟨Dom.ne64 a0.c a1.c b0.c b1.c, Dom.ne64 a0.t a1.t b0.t b1.t,
    by rw [eval_ne64, a0.ok, a1.ok, b0.ok, b1.ok]⟩
  bit x k := ⟨Dom.bit x.c k, Dom.bit x.t k, by rw [eval_bit, x.ok]⟩
  pack l := ⟨Dom.pack (l.map RV.c), Dom.pack (l.map RV.t), by
    rw [eval_pack, List.map_map]; congr 1; apply List.map_congr_left; intro x _; exact x.ok⟩
  shl64 c a b :=
    have e := eval_shl64 env c.t a.t b.t
    (⟨(Dom.shl64 c.c a.c b.c).1, (Dom.shl64 c.t a.t b.t).1, by rw [c.ok, a.ok, b.ok] at e; exact congrArg Prod.fst e⟩,
     ⟨(Dom.shl64 c.c a.c b.c).2, (Dom.shl64 c.t a.t b.t).2, by rw [c.ok, a.ok, b.ok] at e; exact congrArg Prod.snd e⟩)
  lshr64 c a b :=
    have e := eval_lshr64 env c.t a.t b.t
    (⟨(Dom.lshr64 c.c a.c b.c).1, (Dom.lshr64 c.t a.t b.t).1, by rw [c.ok, a.ok, b.ok] at e; exact congrArg Prod.fst e⟩,
     ⟨(Dom.lshr64 c.c a.c b.c).2, (Dom.lshr64 c.t a.t b.t).2, by rw [c.ok, a.ok, b.ok] at e; exact congrArg Prod.snd e⟩)
  nez64 a b := ⟨Dom.nez64 a.c b.c, Dom.nez64 a.t b.t, by rw [eval_nez64, a.ok, b.ok]⟩

/-- A concrete and a symbolic memory that agree on every word the symbolic one loads, and with `m0`
on every word not stored since. -/
structure RM (m0 : Memory) where
  c : Memory
  t : SymMem
  ok : ∀ a u, t.load a = some u → c.get? a = some (u.eval env)
  frame : ∀ a, t.stores.get? a = none → c.get? a = m0.get? a

variable {env} {m0 : Memory}

def RM.load (m : RM env m0) (a : UInt64) : Option (RV env) :=
  match m.t.load a with
  | some u => some ⟨u.eval env, u, rfl⟩
  | none => none

def RM.store (m : RM env m0) (a : UInt64) (v : RV env) : RM env m0 where
  c := m.c.insert a v.c
  t := { m.t with stores := m.t.stores.insert a v.t }
  ok := by
    intro a' u hu
    simp only [SymMem.load, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hu ⊢
    by_cases ha : a = a'
    · subst ha; simp at hu ⊢; rw [← hu, v.ok]
    · have hb : (a == a') = false := by simpa using ha
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hu ⊢
      exact m.ok a' u (by simpa [SymMem.load, Std.HashMap.get?_eq_getElem?] using hu)
  frame := by
    intro a' hs
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hs ⊢
    by_cases ha : a = a'
    · subst ha; simp at hs
    · have hb : (a == a') = false := by simpa using ha
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact m.frame a' (by simpa [Std.HashMap.get?_eq_getElem?] using hs)

instance : MemDom (RM env m0) (RV env) where
  load := RM.load
  store := RM.store

/-! ## 3. The two projections -/

def fstHom : DomHom (RV env) UInt32 where
  f := RV.c
  lit _ := rfl
  conc x c hc := by
    have := Tm.eval_of_litVal env x.t c hc
    show some x.c = some c; rw [← x.ok, this]
  add _ _ := rfl
  sub _ _ := rfl
  mul _ _ := rfl
  mulHi _ _ := rfl
  band _ _ := rfl
  bor _ _ := rfl
  shl _ _ := rfl
  ite _ _ _ := rfl
  carry _ _ := rfl
  borrow _ _ := rfl
  addc _ _ _ := rfl
  carryc _ _ _ := rfl
  subc _ _ _ := rfl
  borrowc _ _ _ := rfl
  ule _ _ := rfl
  ugt _ _ := rfl
  ult64 _ _ _ _ := rfl
  ne64 _ _ _ _ := rfl
  bit _ _ := rfl
  pack _ := rfl
  shl64 _ _ _ := rfl
  lshr64 _ _ _ := rfl
  nez64 _ _ := rfl

def fstMem : MemHom (RM env m0) Memory (fstHom (env := env)) where
  g := RM.c
  load m a v hv := by
    show m.c.get? a = some v.c
    simp only [MemDom.load, RM.load] at hv
    split at hv
    · rename_i u hu; simp at hv; subst hv; exact m.ok a u hu
    · simp at hv
  store _ _ _ := rfl

def sndHom : DomHom (RV env) Tm where
  f := RV.t
  lit _ := rfl
  conc _ _ hc := hc
  add _ _ := rfl
  sub _ _ := rfl
  mul _ _ := rfl
  mulHi _ _ := rfl
  band _ _ := rfl
  bor _ _ := rfl
  shl _ _ := rfl
  ite _ _ _ := rfl
  carry _ _ := rfl
  borrow _ _ := rfl
  addc _ _ _ := rfl
  carryc _ _ _ := rfl
  subc _ _ _ := rfl
  borrowc _ _ _ := rfl
  ule _ _ := rfl
  ugt _ _ := rfl
  ult64 _ _ _ _ := rfl
  ne64 _ _ _ _ := rfl
  bit _ _ := rfl
  pack _ := rfl
  shl64 _ _ _ := rfl
  lshr64 _ _ _ := rfl
  nez64 _ _ := rfl

def sndMem : MemHom (RM env m0) SymMem (sndHom (env := env)) where
  g := RM.t
  load m a v hv := by
    show m.t.load a = some v.t
    simp only [MemDom.load, RM.load] at hv
    split at hv
    · rename_i u hu; simp at hv; subst hv; exact hu
    · simp at hv
  store _ _ _ := rfl

theorem snd_reflects : Reflects (sndHom (env := env)) (sndMem (env := env) (m0 := m0)) := by
  constructor
  · intro x hx; exact hx
  · intro m a ha
    show m.t.load a = none
    simp only [MemDom.load, RM.load] at ha
    split at ha
    · simp at ha
    · assumption

/-! ## 4. A symbolic wave, sound for every concrete one it describes -/

/-- If the symbolic run of a wave from the base view `base` succeeds, then from every concrete memory
`m0` that `base` describes (`m0` holds `eval env u` wherever `base` gives `u`), the concrete run succeeds,
halts when the symbolic one does, holds `eval env u` wherever the symbolic run's memory holds `u`, and
holds what `m0` held on every dword the symbolic run did not store. -/
theorem wave_sound (prog : Program) (n : Nat) (m0 : Memory) (base : UInt64 → Option Tm)
    (hbase : ∀ a u, base a = some u → m0.get? a = some (u.eval env)) (setLo : UInt32) (g : Nat)
    (hsym : (run prog n (initWave (⟨{}, base⟩ : SymMem) setLo g : SymWave)).err = none) :
    let sc := run prog n (initWave m0 setLo g : WaveState)
    let st := run prog n (initWave (⟨{}, base⟩ : SymMem) setLo g : SymWave)
    sc.err = none ∧ sc.halted = st.halted ∧
      (∀ a u, st.mem.load a = some u → sc.mem.get? a = some (u.eval env)) ∧
      (∀ a, st.mem.stores.get? a = none → sc.mem.get? a = m0.get? a) := by
  let rm : RM env m0 := ⟨m0, ⟨{}, base⟩, by
    intro a u hu
    simp only [SymMem.load, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hu
    exact hbase a u hu, fun _ _ => rfl⟩
  let sr : GWave (RV env) (RM env m0) := initWave rm setLo g
  have h2 := run_hom (sndHom (env := env)) (sndMem (env := env) (m0 := m0)) True (fun _ => snd_reflects) prog n sr
    (Or.inr trivial)
  have hsnd : mapW sndHom sndMem sr = (initWave (⟨{}, base⟩ : SymMem) setLo g : SymWave) := initWave_hom _ _ rm setLo g
  have hfst : mapW fstHom fstMem sr = (initWave m0 setLo g : WaveState) := initWave_hom _ _ rm setLo g
  rw [hsnd] at h2
  have herr : (run prog n sr).err = none := by
    have := congrArg GWave.err h2; simp only [mapW_err] at this; rw [← this]; exact hsym
  have h1 := run_hom (fstHom (env := env)) (fstMem (env := env) (m0 := m0)) False (fun h => h.elim) prog n sr
    (Or.inl herr)
  rw [hfst] at h1
  simp only []
  rw [h1, h2]
  refine ⟨by simpa using herr, by simp, ?_, ?_⟩
  · intro a u hu; exact (run prog n sr).mem.ok a u hu
  · intro a ha; exact (run prog n sr).mem.frame a ha

end
end Obend.Hardware.Gpu.Rdna2
