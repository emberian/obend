/-
# Obend.Hardware.Gpu.Rdna2.Join — a symbolic run across a branch on an EXEC it does not know

`S_CBRANCH_EXECZ` jumps over a region when EXEC is zero (manual 4.4, 12.5). When the mask a compare
computed from data is a term, the symbolic run cannot decide the jump, and the concrete runs it stands
for take both ways. LLVM inserts these branches to skip work and keeps or drops them by whether the
region is harmless when EXEC is zero (`SIPreEmitPeephole::mustRetainExeczBranch`,
`SIInstrInfo::hasUnwantedEffectsWhenEXECEmpty`): the region's vector writes and stores are masked off,
so running it is the jump, but for its scalar effects. `srun` takes that reading as a checked step, with
the state merge of symbolic execution at the join (Kuznetsov, Kinder, Bucur and Candea, "Efficient
State Merging in Symbolic Execution", PLDI 2012): it runs the region to the branch target once with the
symbolic EXEC (`fall`) and once with EXEC zero (`zero`); if the second leaves every VGPR and every stored
dword as they were, the merged state takes the first's vector registers and memory, and every scalar
register the region changed becomes the select, on EXECZ, of its value before the branch and after the
region. A region that does not reach the target, a nested branch on an unknown EXEC, or a region that
writes under EXEC zero is refused.

`srun_sound` says the concrete model's run agrees with it: for every memory, the concrete run (which
takes the branch or not, by its own EXEC) ends where the merged run's evaluation says, up to the
representation of memory (`Agree`: the same dword at every address).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Sym
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. Running to a program counter -/

section
variable {V M : Type} [Dom V] [MemDom M V]

/-- Steps until the wave is at `T`, halts or fails, with the number of steps taken. -/
def runTo (prog : Program) (T : Nat) : Nat → GWave V M → GWave V M × Nat
  | 0, s => (s, 0)
  | n + 1, s =>
    if s.halted || s.err.isSome || s.pc == T then (s, 0)
    else let p := runTo prog T n (step prog s); (p.1, p.2 + 1)

theorem runTo_err (prog : Program) (T : Nat) : ∀ (n : Nat) (s : GWave V M),
    (runTo prog T n s).1.err = none → s.err = none
  | 0, s, h => h
  | n + 1, s, h => by
    unfold runTo at h; split at h
    · exact h
    · rename_i hl
      cases hs : s.err with
      | none => rfl
      | some e => simp [hs] at hl

theorem runTo_le (prog : Program) (T : Nat) : ∀ (n : Nat) (s : GWave V M), (runTo prog T n s).2 ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, s => by
    unfold runTo; split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (runTo_le prog T n _)

/-- A run that reaches `T` without halting or failing is that many steps of the run. -/
theorem run_runTo (prog : Program) (T : Nat) : ∀ (n : Nat) (s : GWave V M),
    (runTo prog T n s).1.halted = false → (runTo prog T n s).1.err = none →
    run prog n s = run prog (n - (runTo prog T n s).2) (runTo prog T n s).1
  | 0, s, _, _ => rfl
  | n + 1, s, hh, he => by
    unfold runTo at hh he ⊢
    by_cases hc : (s.halted || s.err.isSome || s.pc == T) = true
    · simp only [hc, ↓reduceIte, Nat.sub_zero]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hh he ⊢
      have hs : (s.halted || s.err.isSome) = false := by
        simp only [Bool.or_eq_true, not_or] at hc
        simp [hc.1.1, hc.1.2]
      rw [run, if_neg (by simp [hs]), run_runTo prog T n _ hh he]
      congr 1; omega

/-- More fuel changes nothing for a run that ended without failing. -/
theorem run_mono (prog : Program) : ∀ (m d : Nat) (s : GWave V M), (run prog m s).err = none →
    run prog (m + d) s = run prog m s
  | 0, d, s, h => by
    unfold run at h
    by_cases hl : (s.halted || s.err.isSome) = true
    · cases d with
      | zero => rfl
      | succ d => simp only [Nat.zero_add, run, hl, ↓reduceIte]
    · rw [if_neg hl] at h; exact absurd h (fail_err s _)
  | m + 1, d, s, h => by
    rw [show m + 1 + d = (m + d) + 1 by omega]
    unfold run at h ⊢
    by_cases hl : (s.halted || s.err.isSome) = true
    · simp only [hl, ↓reduceIte]
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact run_mono prog m d _ h

end

section
variable {V₁ V₂ M₁ M₂ : Type} [Dom V₁] [Dom V₂] [MemDom M₁ V₁] [MemDom M₂ V₂]
variable (h : DomHom V₁ V₂) (hm : MemHom M₁ M₂ h)

theorem runTo_hom (hL : IteLawful V₂) (R : Prop) (hR : R → Reflects h hm) (prog : Program) (T : Nat) :
    ∀ (n : Nat) (s : GWave V₁ M₁), (runTo prog T n s).1.err = none ∨ R →
      runTo prog T n (mapW h hm s) = (mapW h hm (runTo prog T n s).1, (runTo prog T n s).2)
  | 0, s, _ => rfl
  | n + 1, s, hres => by
    unfold runTo at hres ⊢
    by_cases hc : (s.halted || s.err.isSome || s.pc == T) = true
    · simp only [hc, ↓reduceIte]
      rw [if_pos (show ((mapW h hm s).halted || (mapW h hm s).err.isSome || (mapW h hm s).pc == T) = true from hc)]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hres ⊢
      rw [if_neg (show ¬ ((mapW h hm s).halted || (mapW h hm s).err.isSome || (mapW h hm s).pc == T) = true from hc)]
      have hstep : (step prog s).err = none ∨ R := hres.imp_left (runTo_err prog T n _)
      rw [step_hom h hm hL R hR prog s hstep, runTo_hom hL R hR prog T n _ hres]

end

/-! ## 2. Concrete states that hold the same dwords -/

/-- Memory as the function from an address to its dword. -/
abbrev FMem := UInt64 → Option UInt32

instance : MemDom FMem UInt32 where
  load m a := m a
  store m a v := fun a' => if a' = a then some v else m a'

def idHom : DomHom UInt32 UInt32 where
  f := id
  lit _ := rfl
  conc _ _ h := h
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
  pack _ := by simp
  shl64 _ _ _ := rfl
  lshr64 _ _ _ := rfl
  nez64 _ _ := rfl

def funMem : MemHom Memory FMem idHom where
  g m := fun a => m.get? a
  load _ _ _ hv := hv
  store m a v := by
    funext a'
    show (m.insert a v).get? a' = if a' = a then some v else m.get? a'
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    by_cases ha : a' = a
    · subst ha; simp
    · have : (a == a') = false := beq_false_of_ne (Ne.symm ha)
      simp only [this, Bool.false_eq_true, ↓reduceIte, if_neg ha]

theorem id_reflects : Reflects idHom funMem := ⟨fun _ h => h, fun _ _ h => h⟩

/-- Two concrete states that differ at most in how their memory is represented. -/
def Agree (c₁ c₂ : WaveState) : Prop := mapW idHom funMem c₁ = mapW idHom funMem c₂

theorem step_agree (prog : Program) {c₁ c₂ : WaveState} (h : Agree c₁ c₂) : Agree (step prog c₁) (step prog c₂) := by
  unfold Agree at *
  rw [← step_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog c₁ (Or.inr trivial),
    ← step_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog c₂ (Or.inr trivial), h]

theorem run_agree (prog : Program) (n : Nat) {c₁ c₂ : WaveState} (h : Agree c₁ c₂) : Agree (run prog n c₁) (run prog n c₂) := by
  unfold Agree at *
  rw [← run_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog n c₁ (Or.inr trivial),
    ← run_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog n c₂ (Or.inr trivial), h]

theorem runTo_agree (prog : Program) (T n : Nat) {c₁ c₂ : WaveState} (h : Agree c₁ c₂) :
    Agree (runTo prog T n c₁).1 (runTo prog T n c₂).1 ∧ (runTo prog T n c₁).2 = (runTo prog T n c₂).2 := by
  have e₁ := runTo_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog T n c₁ (Or.inr trivial)
  have e₂ := runTo_hom idHom funMem u32_iteLawful True (fun _ => id_reflects) prog T n c₂ (Or.inr trivial)
  unfold Agree at *
  rw [h] at e₁; rw [e₁] at e₂
  simp only [Prod.mk.injEq] at e₂
  exact e₂

theorem Agree.symm {c₁ c₂ : WaveState} (h : Agree c₁ c₂) : Agree c₂ c₁ := Eq.symm h
theorem Agree.trans {c₁ c₂ c₃ : WaveState} (h : Agree c₁ c₂) (h' : Agree c₂ c₃) : Agree c₁ c₃ := Eq.trans h h'

theorem agree_iff (c₁ c₂ : WaveState) : Agree c₁ c₂ ↔
    c₁.sgpr = c₂.sgpr ∧ c₁.exec = c₂.exec ∧ c₁.scc = c₂.scc ∧ c₁.m0 = c₂.m0 ∧ c₁.vgpr = c₂.vgpr ∧ c₁.pc = c₂.pc ∧
      (∀ a, c₁.mem.get? a = c₂.mem.get? a) ∧ c₁.halted = c₂.halted ∧ c₁.err = c₂.err ∧ c₁.ldsBase = c₂.ldsBase ∧
      c₁.ldsDwords = c₂.ldsDwords := by
  unfold Agree mapW
  constructor
  · intro h
    simp only [GWave.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    simp only [idHom, Array.map_id_fun, id_eq, Prod.mk.injEq] at h1 h2 h3 h4 h5
    exact ⟨h1, Prod.ext h2.1 h2.2, h3, h4, h5, h6, fun a => congrFun h7 a, h8, h9, h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    simp only [GWave.mk.injEq]
    exact ⟨by rw [h1], by rw [h2], by rw [h3], by rw [h4], by rw [h5], h6, funext h7, h8, h9, h10, h11⟩

/-! ## 3. The merge at the join -/

section
variable {V M : Type} [Dom V] [MemDom M V]

/-- The state after the region `fall`, with each scalar register that differs (by `eqv`) from the state
`snap` before the branch replaced by the select, on EXECZ `z`, of the two. -/
def mergeG (eqv : V → V → Bool) (z : V) (snap fall : GWave V M) (T : Nat) : GWave V M :=
  let mv (a b : V) : V := if eqv a b then a else Dom.ite z a b
  { fall with
    sgpr := Array.zipWith mv snap.sgpr fall.sgpr
    scc := mv snap.scc fall.scc
    m0 := mv snap.m0 fall.m0
    exec := (mv snap.exec.1 fall.exec.1, mv snap.exec.2 fall.exec.2)
    pc := T }

end

/-- The two term maps hold the same entries. -/
def storesEq (a b : Std.HashMap UInt64 Tm) : Bool :=
  a.toList.all (fun p => b.get? p.1 == some p.2) && b.toList.all (fun p => a.get? p.1 == some p.2)

theorem storesEq_get (a b : Std.HashMap UInt64 Tm) (h : storesEq a b = true) (k : UInt64) : a.get? k = b.get? k := by
  unfold storesEq at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases ha : a.get? k with
  | none =>
    cases hb : b.get? k with
    | none => rfl
    | some t =>
      have := h2 (k, t) (by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact hb)
      simp only at this; rw [ha] at this; cases this
  | some t =>
    have := h1 (k, t) (by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact ha)
    simp only at this; rw [this]

/-- The branch target when the instruction at the pc is `S_CBRANCH_EXECZ` and EXEC is not known. -/
def joinTarget (prog : Program) (s : SymWave) : Option Nat :=
  match prog[s.pc]? with
  | some (some i) =>
    if instOp i.name == .s_cbranch_execz && modifiersClear i && i.words.length == 1 && (Dom.conc (execzV s)).isNone then
      some (Int.ofNat (s.pc + 1) + signed16 (i.field "SIMM16")).toNat
    else none
  | _ => none

/-- The region is a join: both runs reached the target, neither halted nor failed, and with EXEC zero it
wrote no VGPR and stored no dword. -/
def joinOk (T : Nat) (s fall zero : SymWave) : Bool :=
  fall.pc == T && zero.pc == T && fall.err.isNone && zero.err.isNone && !fall.halted && !zero.halted &&
    zero.vgpr == s.vgpr && storesEq zero.mem.stores s.mem.stores && fall.sgpr.size == s.sgpr.size &&
    fall.ldsBase == s.ldsBase && fall.ldsDwords == s.ldsDwords

/-- The symbolic run with joins: `run`, but a branch on an unknown EXEC is a merged region. -/
def srun (prog : Program) : Nat → SymWave → SymWave
  | 0, s => run prog 0 s
  | n + 1, s =>
    if s.halted || s.err.isSome then s else
    match joinTarget prog s with
    | none => srun prog n (step prog s)
    | some T =>
      let s1 : SymWave := { s with pc := s.pc + 1 }
      let fall := runTo prog T n s1
      let zero := runTo prog T n { s1 with exec := (Dom.lit 0, Dom.lit 0) }
      if joinOk T s fall.1 zero.1 then
        srun prog (n - fall.2) (mergeG (fun a b => decide (a = b)) (execzV s) s fall.1 T)
      else s.fail "S_CBRANCH_EXECZ on an unknown EXEC: the region does not join, or writes with EXEC zero"
termination_by n => n
decreasing_by all_goals omega

theorem srun_err_some (prog : Program) : ∀ (n : Nat) (s : SymWave), s.err.isSome → (srun prog n s).err.isSome
  | 0, s, h => by
    unfold srun run; simp [h]
  | n + 1, s, h => by
    unfold srun; simp [h]

/-! ## 4. Soundness -/

section
variable {env : UInt64 → UInt32} {m0 : Memory}

local notation "RW" => GWave (RV env) (RM env m0)
local notation "SND" => mapW (sndHom (env := env)) (sndMem (env := env) (m0 := m0))
local notation "FST" => mapW (fstHom (env := env)) (fstMem (env := env) (m0 := m0))

def eqvRV (a b : RV env) : Bool := decide (a.t = b.t)

theorem rv_c_eq (a b : RV env) (h : a.t = b.t) : a.c = b.c := by rw [← a.ok, ← b.ok, h]

theorem map_c_of_map_t (A B : Array (RV env)) (h : A.map RV.t = B.map RV.t) : A.map RV.c = B.map RV.c := by
  have hs : A.size = B.size := by simpa using congrArg Array.size h
  apply Array.ext (by simpa using hs)
  intro i h1 h2
  simp only [Array.getElem_map]
  apply rv_c_eq
  have := congrArg (fun X => X[i]?) h
  simpa [Array.getElem?_map, Array.getElem?_eq_getElem (by simpa using h1 : i < A.size),
    Array.getElem?_eq_getElem (by simpa using h2 : i < B.size)] using this

theorem merge_snd (z : RV env) (r f : RW) (T : Nat) :
    SND (mergeG eqvRV z r f T) = mergeG (fun a b => decide (a = b)) z.t (SND r) (SND f) T := by
  have hmv : ∀ a b : RV env, (if eqvRV a b then a else Dom.ite z a b).t =
      if decide (a.t = b.t) then a.t else Dom.ite z.t a.t b.t := by
    intro a b; unfold eqvRV; split <;> rfl
  simp only [mergeG, mapW, GWave.mk.injEq]
  constructor
  · simp only [sndHom]
    rw [Array.map_zipWith, Array.zipWith_map]
    congr 1; funext a b; exact hmv a b
  · simp only [sndHom, hmv, and_self, and_true]
    exact ⟨rfl, rfl, rfl⟩

theorem merge_c (z : RV env) (a b : RV env) :
    (if eqvRV a b then a else Dom.ite z a b).c = if z.c != 0 then a.c else b.c := by
  unfold eqvRV
  by_cases h : a.t = b.t
  · simp only [h, decide_true, ↓reduceIte]; have := rv_c_eq a b h; split <;> simp [this]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    show Dom.ite z.c a.c b.c = _
    simp [Dom.ite, w2b]

theorem merge_fst_arr (z : RV env) (A B : Array (RV env)) (hs : B.size = A.size) :
    (Array.zipWith (fun a b => if eqvRV a b then a else Dom.ite z a b) A B).map RV.c =
      if z.c != 0 then A.map RV.c else B.map RV.c := by
  split
  · rename_i hz
    apply Array.ext (by simp [hs])
    intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_zipWith, merge_c, hz, ↓reduceIte]
  · rename_i hz
    apply Array.ext (by simp [hs])
    intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_zipWith, merge_c, hz, Bool.false_eq_true, ↓reduceIte]

theorem execz_zero (c : WaveState) (h : (execzV c) ≠ 0) : c.exec = (0, 0) := by
  unfold execzV at h
  simp only [Dom.ite, Dom.nez64, Dom.lit, w2b, b2w] at h
  by_cases hl : c.exec.1 = 0 <;> by_cases hh : c.exec.2 = 0 <;> simp_all [Prod.ext_iff]

theorem execz_c (r : RW) : (execzV r).c = execzV (FST r) := by
  have := execzV_hom (fstHom (env := env)) (fstMem (env := env) (m0 := m0)) r
  exact this


theorem exec_self (s : WaveState) (e : UInt32 × UInt32) (h : s.exec = e) : { s with exec := e } = s := by
  cases s; simp_all

theorem fst_mem_get (x : RW) (a : UInt64) : (FST x).mem.get? a = x.mem.c.get? a := rfl

/-- What the memory of a pair of runs holds at an address is fixed by the term stores. -/
theorem mem_c_of_stores (x y : RW) (h : ∀ a, x.mem.t.stores.get? a = y.mem.t.stores.get? a) (a : UInt64) :
    x.mem.c.get? a = y.mem.c.get? a := by
  cases hx : x.mem.t.stores.get? a with
  | none =>
    have hy : y.mem.t.stores.get? a = none := by rw [← h a, hx]
    rw [x.mem.frame a hx, y.mem.frame a hy]
  | some u =>
    have hy : y.mem.t.stores.get? a = some u := by rw [← h a, hx]
    rw [x.mem.ok a u (by show SymMem.load _ a = some u; unfold SymMem.load; rw [hx]),
      y.mem.ok a u (by show SymMem.load _ a = some u; unfold SymMem.load; rw [hy])]

/-- The scalar fields of the merge, under the concrete EXECZ. -/
theorem merge_fst (z : RV env) (r f : RW) (T : Nat) (hs : f.sgpr.size = r.sgpr.size) :
    let rm := mergeG eqvRV z r f T
    (FST rm).sgpr = (if z.c != 0 then (FST r).sgpr else (FST f).sgpr) ∧
    (FST rm).exec = (if z.c != 0 then (FST r).exec else (FST f).exec) ∧
    (FST rm).scc = (if z.c != 0 then (FST r).scc else (FST f).scc) ∧
    (FST rm).m0 = (if z.c != 0 then (FST r).m0 else (FST f).m0) ∧
    (FST rm).vgpr = (FST f).vgpr ∧ (FST rm).pc = T ∧ (FST rm).mem = (FST f).mem ∧ (FST rm).halted = f.halted ∧
    (FST rm).err = f.err ∧ (FST rm).ldsBase = f.ldsBase ∧ (FST rm).ldsDwords = f.ldsDwords := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [mergeG, mapW, fstHom]; rw [merge_fst_arr z _ _ hs]
  · simp only [mergeG, mapW, fstHom]; rw [merge_c, merge_c]; split <;> rfl
  · simp only [mergeG, mapW, fstHom]; rw [merge_c]; try (split <;> rfl)
  · simp only [mergeG, mapW, fstHom]; rw [merge_c]; try (split <;> rfl)

/-- The symbolic run with joins describes the concrete run from every state it describes. -/
theorem srun_sound (prog : Program) : ∀ (n : Nat) (r : RW) (c : WaveState), Agree c (FST r) →
    (srun prog n (SND r)).err = none →
    ∃ r' : RW, SND r' = srun prog n (SND r) ∧ Agree (run prog n c) (FST r') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro r c hc herr
  have hcf := (agree_iff _ _).mp hc
  cases n with
  | zero =>
    refine ⟨run prog 0 r, ?_, ?_⟩
    · rw [srun, run_hom sndHom sndMem tm_iteLawful True (fun _ => snd_reflects) prog 0 r (Or.inr trivial)]
    · have he : (run prog 0 r).err = none := by
        have := congrArg GWave.err (run_hom sndHom sndMem tm_iteLawful True (fun _ => snd_reflects) prog 0 r (Or.inr trivial))
        simp only [mapW_err] at this; rw [← this]; unfold srun at herr; exact herr
      rw [← run_hom fstHom fstMem u32_iteLawful False (fun h => h.elim) prog 0 r (Or.inl he)]
      exact run_agree prog 0 hc
  | succ n =>
    rw [srun] at herr ⊢
    by_cases hl : ((SND r).halted || (SND r).err.isSome) = true
    · simp only [hl, ↓reduceIte] at herr ⊢
      refine ⟨r, rfl, ?_⟩
      have hl' : (c.halted || c.err.isSome) = true := by rw [hcf.2.2.2.2.2.2.2.1, hcf.2.2.2.2.2.2.2.2.1]; exact hl
      rw [run, if_pos hl']; exact hc
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at herr ⊢
    have hl' : ¬ (c.halted || c.err.isSome) = true := by rw [hcf.2.2.2.2.2.2.2.1, hcf.2.2.2.2.2.2.2.2.1]; exact hl
    have hrun : run prog (n + 1) c = run prog n (step prog c) := by rw [run, if_neg hl']
    rw [hrun]
    cases hj : joinTarget prog (SND r) with
    | none =>
      simp only [hj] at herr ⊢
      have hs : step prog (SND r) = SND (step prog r) :=
        step_hom sndHom sndMem tm_iteLawful True (fun _ => snd_reflects) prog r (Or.inr trivial)
      rw [hs] at herr ⊢
      have hse : (step prog r).err = none := by
        cases e : (step prog r).err with
        | none => rfl
        | some x =>
          have := srun_err_some prog n (SND (step prog r)) (by simp [e])
          rw [herr] at this; cases this
      have hf := step_hom fstHom fstMem u32_iteLawful False (fun h => h.elim) prog r (Or.inl hse)
      obtain ⟨r', h1, h2⟩ := ih n (Nat.lt_succ_self n) (step prog r) (step prog c)
        (by rw [← hf]; exact step_agree prog hc) herr
      exact ⟨r', h1, h2⟩
    | some T =>
      simp only [hj] at herr ⊢
      -- the instruction at the pc
      unfold joinTarget at hj
      split at hj
      case h_2 => cases hj
      rename_i i hpc
      split at hj
      case isFalse => cases hj
      rename_i hcond
      simp only [Option.some.injEq] at hj
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨hop, hmod⟩, hw⟩, _⟩ := hcond
      -- the two region runs, as runs of pairs
      let r1 : RW := { r with pc := r.pc + 1 }
      let r1z : RW := { r1 with exec := (Dom.lit 0, Dom.lit 0) }
      have hF := runTo_hom sndHom sndMem tm_iteLawful True (fun _ => snd_reflects) prog T n r1 (Or.inr trivial)
      have hZ := runTo_hom sndHom sndMem tm_iteLawful True (fun _ => snd_reflects) prog T n r1z (Or.inr trivial)
      have eF : runTo prog T n ({ SND r with pc := (SND r).pc + 1 } : SymWave) =
          (SND (runTo prog T n r1).1, (runTo prog T n r1).2) := hF
      have eZ : runTo prog T n ({ { SND r with pc := (SND r).pc + 1 } with exec := (Dom.lit 0, Dom.lit 0) } : SymWave) =
          (SND (runTo prog T n r1z).1, (runTo prog T n r1z).2) := hZ
      rw [eF, eZ] at herr ⊢
      have ez : execzV (SND r) = (execzV r).t := (execzV_hom sndHom sndMem r).symm
      rw [ez] at herr ⊢
      generalize hfr : runTo prog T n r1 = fr at herr ⊢
      generalize hzr : runTo prog T n r1z = zr at herr ⊢
      by_cases hok : joinOk T (SND r) (SND fr.1) (SND zr.1) = true
      case neg => rw [if_neg hok] at herr; exact absurd herr (fail_err _ _)
      rw [if_pos hok] at herr ⊢
      rw [← merge_snd] at herr ⊢
      unfold joinOk at hok
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfpc, hzpc⟩, hferr⟩, hzerr⟩, hfh⟩, hzh⟩, hzv⟩, hst⟩, hsz⟩, hlb⟩, hld⟩ := hok
      simp only [mapW_pc, mapW_err, mapW_halted] at hfpc hzpc hferr hzerr hfh hzh
      have hsz' : fr.1.sgpr.size = r.sgpr.size := by simpa [mapW] using hsz
      have hk : fr.2 ≤ n := by rw [← hfr]; exact runTo_le prog T n r1
      -- the region's runs on the concrete side
      have hFf := runTo_hom fstHom fstMem u32_iteLawful False (fun h => h.elim) prog T n r1
        (Or.inl (by rw [hfr]; exact hferr))
      have hZf := runTo_hom fstHom fstMem u32_iteLawful False (fun h => h.elim) prog T n r1z
        (Or.inl (by rw [hzr]; exact hzerr))
      rw [hfr] at hFf; rw [hzr] at hZf
      -- the concrete step at the branch
      have hcpc : c.pc = (SND r).pc := hcf.2.2.2.2.2.1
      have hch : c.halted = false := by
        have := hl'; simp only [Bool.or_eq_true, not_or] at this; simpa using this.1
      have hce : c.err = none := by
        have := hl'; simp only [Bool.or_eq_true, not_or] at this; simpa using this.2
      let c1 : WaveState := { c with pc := c.pc + 1 }
      have hstep : step prog c = if execzV c != 0 then { c1 with pc := T } else c1 := by
        have hpc' : prog[c.pc]? = some (some i) := by rw [hcpc]; exact hpc
        unfold step
        rw [if_neg hl', hpc']
        simp only []
        rw [hw]
        unfold execInst
        rw [if_neg (by simp [hmod]), hop]
        simp only [GWave.withSome, Dom.conc]
        rw [← hj, ← hcpc]
        rfl
      have hzc : execzV c = (execzV r).c := by
        rw [execz_c]; unfold execzV; rw [hcf.2.1]
      rw [hstep, hzc]
      have hagree1 : Agree c1 (FST r1) := by
        refine (agree_iff _ _).mpr ⟨hcf.1, hcf.2.1, hcf.2.2.1, hcf.2.2.2.1, hcf.2.2.2.2.1, ?_, hcf.2.2.2.2.2.2.1,
          hcf.2.2.2.2.2.2.2.1, hcf.2.2.2.2.2.2.2.2.1, hcf.2.2.2.2.2.2.2.2.2.1, hcf.2.2.2.2.2.2.2.2.2.2⟩
        show c.pc + 1 = r.pc + 1; rw [hcpc]; rfl
      have hmf := merge_fst (execzV r) r fr.1 T hsz'
      simp only [] at hmf
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := hmf
      by_cases hzv0 : ((execzV r).c != 0) = true
      · -- EXEC is zero: the branch is taken, and the region left the vector state alone
        rw [if_pos hzv0]
        rw [if_pos hzv0] at m1 m2 m3 m4
        have hc0 : c.exec = (0, 0) := execz_zero c (by rw [hzc]; simpa using hzv0)
        have hr1z : FST r1z = FST r1 := by
          show { FST r1 with exec := ((Dom.lit 0 : RV env).c, (Dom.lit 0 : RV env).c) } = FST r1
          apply exec_self
          show (FST r).exec = _
          rw [← hcf.2.1, hc0]; rfl
        rw [hr1z, hFf] at hZf
        simp only [Prod.mk.injEq] at hZf
        have hvz : (FST zr.1).vgpr = (FST r).vgpr :=
          map_c_of_map_t _ _ hzv
        have hmz : ∀ a, (FST zr.1).mem.get? a = (FST r).mem.get? a := fun a =>
          mem_c_of_stores zr.1 r (fun a => storesEq_get _ _ hst a) a
        have hag : Agree { c1 with pc := T } (FST (mergeG eqvRV (execzV r) r fr.1 T)) := by
          refine (agree_iff _ _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [m1]; exact hcf.1
          · rw [m2]; exact hcf.2.1
          · rw [m3]; exact hcf.2.2.1
          · rw [m4]; exact hcf.2.2.2.1
          · rw [m5]; show c.vgpr = (FST fr.1).vgpr
            rw [hZf.1, hvz]; exact hcf.2.2.2.2.1
          · rw [m6]
          · intro a; rw [m7]; show c.mem.get? a = (FST fr.1).mem.get? a
            rw [hZf.1, hmz a]; exact hcf.2.2.2.2.2.2.1 a
          · rw [m8]; show c.halted = _; rw [hch, hfh]
          · rw [m9]; show c.err = _; rw [hce, hferr]
          · rw [m10]; show c.ldsBase = _; rw [hcf.2.2.2.2.2.2.2.2.2.1]; simpa [mapW] using hlb.symm
          · rw [m11]; show c.ldsDwords = _; rw [hcf.2.2.2.2.2.2.2.2.2.2]; simpa [mapW] using hld.symm
        obtain ⟨r', h1, h2⟩ := ih (n - fr.2) (by omega) _ _ hag herr
        refine ⟨r', h1, ?_⟩
        have he' : (run prog (n - fr.2) { c1 with pc := T }).err = none := by
          have := ((agree_iff _ _).mp h2).2.2.2.2.2.2.2.2.1
          rw [this]; show r'.err = none
          have := congrArg GWave.err h1; simp only [mapW_err] at this; rw [this]; exact herr
        have := run_mono prog (n - fr.2) fr.2 { c1 with pc := T } he'
        rw [show n - fr.2 + fr.2 = n by omega] at this
        rw [this]; exact h2
      · -- EXEC is not zero: the region runs
        rw [if_neg hzv0]
        rw [if_neg hzv0] at m1 m2 m3 m4
        obtain ⟨ha, hk2⟩ := runTo_agree prog T n hagree1
        rw [hFf] at ha hk2
        simp only [] at ha hk2
        have haf := (agree_iff _ _).mp ha
        have hrr := run_runTo prog T n c1 (by rw [haf.2.2.2.2.2.2.2.1]; exact hfh)
          (by rw [haf.2.2.2.2.2.2.2.2.1]; exact hferr)
        rw [hrr, hk2]
        have hag : Agree (runTo prog T n c1).1 (FST (mergeG eqvRV (execzV r) r fr.1 T)) := by
          refine ha.trans ((agree_iff _ _).mpr ⟨m1.symm, m2.symm, m3.symm, m4.symm, m5.symm, ?_, fun a => by rw [m7],
            m8.symm, m9.symm, m10.symm, m11.symm⟩)
          rw [m6]; exact hfpc
        obtain ⟨r', h1, h2⟩ := ih (n - fr.2) (by omega) _ _ hag herr
        exact ⟨r', h1, h2⟩
end

/-- `wave_sound` for the run with joins: if the symbolic run of a wave succeeds, then from every
concrete memory the base view describes the concrete run succeeds, halts when the symbolic one does,
holds `eval env u` wherever the symbolic run's memory holds `u`, and holds what `m0` held on every dword
the symbolic run did not store. -/
theorem swave_sound (env : UInt64 → UInt32) (prog : Program) (n : Nat) (m0 : Memory) (base : UInt64 → Option Tm)
    (hbase : ∀ a u, base a = some u → m0.get? a = some (u.eval env)) (setLo : UInt32) (g : Nat) (lb : UInt64) (ln : Nat)
    (hsym : (srun prog n (initWave (⟨{}, base⟩ : SymMem) setLo g lb ln : SymWave)).err = none) :
    let sc := run prog n (initWave m0 setLo g lb ln : WaveState)
    let st := srun prog n (initWave (⟨{}, base⟩ : SymMem) setLo g lb ln : SymWave)
    sc.err = none ∧ sc.halted = st.halted ∧
      (∀ a u, st.mem.load a = some u → sc.mem.get? a = some (u.eval env)) ∧
      (∀ a, st.mem.stores.get? a = none → sc.mem.get? a = m0.get? a) := by
  let rm : RM env m0 := ⟨m0, ⟨{}, base⟩, by
    intro a u hu
    simp only [SymMem.load, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hu
    exact hbase a u hu, fun _ _ => rfl⟩
  let sr : GWave (RV env) (RM env m0) := initWave rm setLo g lb ln
  have hsnd : mapW sndHom sndMem sr = (initWave (⟨{}, base⟩ : SymMem) setLo g lb ln : SymWave) := initWave_hom _ _ rm setLo g lb ln
  have hfst : mapW fstHom fstMem sr = (initWave m0 setLo g lb ln : WaveState) := initWave_hom _ _ rm setLo g lb ln
  rw [← hsnd] at hsym
  obtain ⟨r', h1, h2⟩ := srun_sound prog n sr (initWave m0 setLo g lb ln) (by rw [hfst]; rfl) hsym
  rw [← hsnd, ← h1]
  have ha := (agree_iff _ _).mp h2
  simp only []
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha.2.2.2.2.2.2.2.2.1]; show r'.err = none
    have := congrArg GWave.err h1; simp only [mapW_err] at this; rw [this]; exact hsym
  · rw [ha.2.2.2.2.2.2.2.1]; rfl
  · intro a u hu; rw [ha.2.2.2.2.2.2.1 a]; exact r'.mem.ok a u hu
  · intro a hn; rw [ha.2.2.2.2.2.2.1 a]; exact r'.mem.frame a hn

end Obend.Hardware.Gpu.Rdna2
