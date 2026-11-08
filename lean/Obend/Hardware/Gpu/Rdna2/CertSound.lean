/-
# Obend.Hardware.Gpu.Rdna2.CertSound — what an accepted certificate means

`certify_sound`: if `certify p progs rs` accepts and every residual in `rs` holds, then for every content
of the wire buffer, running the decoded programs on the wave model as the host dispatches them succeeds
and leaves in every word of the buffer what `runStages` says the plan computes. The proof follows the
check: a stage's start memory is the environment every symbolic term is read in (`viewStart` describes
it), each wave of the dispatch is related to its symbolic run by `wave_sound`, and each stored dword is
the plan's by `storeOk_sound` (`pKernel_sound`, `residual_sound`).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Cert
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Tm

/-! ## 1. Addresses -/

theorem wDw_toNat : wDw.toNat = 2 ^ 30 := by decide

theorem dwLo_toNat (j : Nat) (hj : j < 2 ^ 29) : (dwLo j).toNat = 2 ^ 30 + 2 * j := by
  simp only [dwLo, UInt64.toNat_add, wDw_toNat, UInt64.toNat_ofNat']
  omega

theorem dwLo1_toNat (j : Nat) (hj : j < 2 ^ 29) : (dwLo j + 1).toNat = 2 ^ 30 + 2 * j + 1 := by
  simp only [UInt64.toNat_add, dwLo_toNat j hj, UInt64.toNat_one]
  omega

theorem inW_iff (words : Nat) (hw : words < 2 ^ 29) (a : UInt64) :
    inW words a = true ↔ 2 ^ 30 ≤ a.toNat ∧ a.toNat < 2 ^ 30 + 2 * words := by
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_add, wDw_toNat, UInt64.toNat_ofNat']
  omega

/-- A dword of the buffer is the low or high half of word `(a - wDw) / 2`. -/
theorem inW_split (words : Nat) (hw : words < 2 ^ 29) (a : UInt64) (h : inW words a = true) :
    let off := (a - wDw).toNat
    off / 2 < words ∧ (off % 2 = 0 → a = dwLo (off / 2)) ∧ (off % 2 = 1 → a = dwLo (off / 2) + 1) := by
  rw [inW_iff words hw] at h
  have hoff : (a - wDw).toNat = a.toNat - 2 ^ 30 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, wDw_toNat]; omega), wDw_toNat]
  simp only [hoff]
  refine ⟨by omega, fun h0 => ?_, fun h1 => ?_⟩
  · apply UInt64.toNat_inj.mp; rw [dwLo_toNat _ (by omega)]; omega
  · apply UInt64.toNat_inj.mp; rw [dwLo1_toNat _ (by omega)]; omega

theorem off_dwLo (j : Nat) (hj : j < 2 ^ 29) : (dwLo j - wDw).toNat = 2 * j := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, wDw_toNat, dwLo_toNat j hj]; omega),
    wDw_toNat, dwLo_toNat j hj]; omega

theorem off_dwLo1 (j : Nat) (hj : j < 2 ^ 29) : (dwLo j + 1 - wDw).toNat = 2 * j + 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, wDw_toNat, dwLo1_toNat j hj]; omega),
    wDw_toNat, dwLo1_toNat j hj]; omega

theorem inW_dwLo (words j : Nat) (hw : words < 2 ^ 29) (hj : j < words) :
    inW words (dwLo j) = true ∧ inW words (dwLo j + 1) = true := by
  rw [inW_iff words hw, inW_iff words hw, dwLo_toNat j (by omega), dwLo1_toNat j (by omega)]; omega

theorem dwLo_ne (j : Nat) (hj : j < 2 ^ 29) : dwLo j ≠ dwLo j + 1 := by
  intro h; have := congrArg UInt64.toNat h; rw [dwLo_toNat j hj, dwLo1_toNat j hj] at this; omega

/-! ## 2. A dispatch's start memory, and what the check reads of it -/

/-- Memory as the environment terms are read in (an absent dword reads `0`; the invariant makes every
dword the check reads present). -/
def menv (m : Memory) : UInt64 → UInt32 := fun a => (m.get? a).getD 0

/-- The memory at the start of a dispatch: the wire buffer holds `E` word by word (every dword present),
`E` is `0` past the buffer, the rest of memory is the layout, and the known constants are what it holds. -/
structure StartOk (p : GpuProgram) (lay : Memory) (known : Known) (m : Memory) (E : Nat → Word) : Prop where
  word : ∀ j, j < p.words → ∃ lo hi, m.get? (dwLo j) = some lo ∧ m.get? (dwLo j + 1) = some hi ∧
    (join64 lo hi).toBitVec = E j
  past : ∀ j, p.words ≤ j → E j = 0
  out : ∀ a, inW p.words a = false → m.get? a = lay.get? a
  known : ∀ a v, known.get? a = some v → inW p.words a = true → m.get? a = some v

theorem StartOk.present {p : GpuProgram} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk p lay known m E) (hw : p.words < 2 ^ 29) (a : UInt64) (ha : inW p.words a = true) :
    ∃ v, m.get? a = some v := by
  obtain ⟨hj, h0, h1⟩ := inW_split p.words hw a ha
  obtain ⟨lo, hi, hlo, hhi, -⟩ := h.word _ hj
  rcases Nat.mod_two_eq_zero_or_one (a - wDw).toNat with e | e
  · exact ⟨lo, by rw [h0 e]; exact hlo⟩
  · exact ⟨hi, by rw [h1 e]; exact hhi⟩

theorem viewStart_ok {p : GpuProgram} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk p lay known m E) (hw : p.words < 2 ^ 29) (a : UInt64) (u : Tm)
    (hv : viewStart p lay known a = some u) : m.get? a = some (u.eval (menv m)) := by
  unfold viewStart at hv
  split at hv
  · rename_i ha
    obtain ⟨v, hmv⟩ := h.present hw a ha
    simp only [Option.some.injEq] at hv
    split at hv
    · rename_i v' hk
      subst hv; rw [eval_lit]; exact h.known a v' hk ha
    · subst hv; rw [eval_var, menv, hmv]; rfl
  · rename_i ha
    simp only [Option.map_eq_some_iff] at hv
    obtain ⟨v, hl, rfl⟩ := hv
    rw [eval_lit, h.out a (by simpa using ha), hl]

theorem join64_zero : join64 0 0 = 0 := by decide

theorem readWord_ev {p : GpuProgram} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk p lay known m E) (hw : p.words < 2 ^ 29) (j : Nat) :
    (readWord p lay known j).ev (menv m) = E j := by
  unfold readWord
  split
  · rename_i hj
    obtain ⟨lo, hi, hlo, hhi, he⟩ := h.word j hj
    obtain ⟨i0, i1⟩ := inW_dwLo p.words j hw hj
    have v0 : ∃ u, viewStart p lay known (dwLo j) = some u := by
      unfold viewStart; rw [ite_eq_left i0]; exact ⟨_, rfl⟩
    have v1 : ∃ u, viewStart p lay known (dwLo j + 1) = some u := by
      unfold viewStart; rw [ite_eq_left i1]; exact ⟨_, rfl⟩
    obtain ⟨u0, hu0⟩ := v0
    obtain ⟨u1, hu1⟩ := v1
    have e0 := viewStart_ok h hw _ u0 hu0
    have e1 := viewStart_ok h hw _ u1 hu1
    rw [hlo] at e0; rw [hhi] at e1
    simp only [Option.some.injEq] at e0 e1
    simp only [TP.ev, hu0, hu1, Option.getD_some, ← e0, ← e1, he]
  · rename_i hj
    simp only [TP.ev, eval_lit, join64_zero]
    rw [h.past j (by omega)]; rfl

/-! ## 3. One stored dword -/

/-- Dword `r` (0 low, 1 high) of a word. -/
def dwHalf (r : Nat) (w : Word) : UInt32 :=
  if r = 0 then (UInt64.ofBitVec w).toUInt32 else ((UInt64.ofBitVec w) >>> 32).toUInt32

theorem join64_lo (lo hi : UInt32) : (join64 lo hi).toUInt32 = lo := by unfold join64; bv_decide
theorem join64_hi (lo hi : UInt32) : ((join64 lo hi) >>> 32).toUInt32 = hi := by unfold join64; bv_decide

theorem dwHalf_ev (env : UInt64 → UInt32) (sp : TP) (r : Nat) :
    dwHalf r (sp.ev env) = (if r = 0 then sp.1 else sp.2).eval env := by
  unfold dwHalf TP.ev
  by_cases h : r = 0
  · simp only [h, ite_true, UInt64.ofBitVec_toBitVec, join64_lo]
  · simp only [h, ite_false, UInt64.ofBitVec_toBitVec, join64_hi]

/-- A dword the check accepts: in the buffer, in a word a kernel of the dispatch owns, and holding that
word's half of what the dispatch computes, read in the start memory. -/
theorem storeOk_sound {p : GpuProgram} {lay : Memory} {cs : Array Word} {ix : Array Nat} {known : Known}
    {m : Memory} {E : Nat → Word} (h : StartOk p lay known m E) (hw : p.words < 2 ^ 29)
    (hcs : cs.toList = p.consts) (hix : ix.toList = p.tables) (s : GpuStage) (a : UInt64) (t : Tm)
    (r? : Option Residual) (hs : storeOk p lay cs ix s known a t = some r?) (hr : ∀ r, r? = some r → r.Holds) :
    inW p.words a = true ∧ (∃ k, s.kernels.find? (·.owns ((a - wDw).toNat / 2)) = some k) ∧
      t.eval (menv m) = dwHalf ((a - wDw).toNat % 2) (runStage p.consts p.tables E s ((a - wDw).toNat / 2)) := by
  unfold storeOk at hs
  split at hs
  · simp at hs
  · rename_i hin
    have hin' : inW p.words a = true := by simpa using hin
    simp only at hs
    split at hs
    · simp at hs
    · rename_i k hk
      simp only [Option.bind_eq_some_iff] at hs
      obtain ⟨sp, hsp, hq⟩ := hs
      refine ⟨hin', ⟨k, hk⟩, ?_⟩
      have hkv := pKernel_sound (menv m) _ _ _ k _ sp hsp
      rw [hcs, hix] at hkv
      have hrd : (fun j => (readWord p lay known j).ev (menv m)) = E := funext (readWord_ev h hw)
      rw [hrd] at hkv
      have hrun : runStage p.consts p.tables E s ((a - wDw).toNat / 2)
          = kernelValue p.consts p.tables E k ((a - wDw).toNat / 2 - k.dstBase) := by
        unfold runStage; rw [hk]
      rw [hrun, ← hkv, dwHalf_ev _ _ _]
      have hsel : (if (a - wDw).toNat % 2 == 0 then sp.1 else sp.2)
          = (if (a - wDw).toNat % 2 = 0 then sp.1 else sp.2) := by
        by_cases e : (a - wDw).toNat % 2 = 0 <;> simp [e]
      rw [shareCommon_eq, hsel] at hq
      generalize (if (a - wDw).toNat % 2 = 0 then sp.1 else sp.2) = x at hq ⊢
      by_cases heq : (t == x) = true
      · rw [eq_of_beq heq]
      · rw [ite_eq_right heq, Option.map_eq_some_iff] at hq
        obtain ⟨r, hres, hr?⟩ := hq
        apply residual_sound _ _ _ r hres
        by_cases e : r.lhs = r.rhs
        · exact Or.inl e
        · right; apply hr; rw [← hr?]; simp [e]

/-! ## 4. The stores of one wave -/

theorem contains_insert64 (s : Std.HashSet UInt64) (k a : UInt64) :
    (s.insert k).contains a = true ↔ k = a ∨ s.contains a = true := by
  rw [Std.HashSet.contains_insert]; simp

theorem contains_insertR (s : Std.HashSet Residual) (k a : Residual) :
    (s.insert k).contains a = true ↔ k = a ∨ s.contains a = true := by
  rw [Std.HashSet.contains_insert]; simp

/-- What `checkStores` establishes about a list of stores: each was free and accepted (its residual kept),
the stored set grows by exactly their addresses, every update is an old one or one of theirs, and the
residuals only grow. -/
theorem checkStores_spec (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (s : GpuStage) (known : Known) :
    ∀ (L : List (UInt64 × Tm)) (acc acc' : Acc), checkStores p lay cs ix s known L acc = some acc' →
      (∀ a, acc'.stored.contains a = true ↔ acc.stored.contains a = true ∨ a ∈ L.map Prod.fst) ∧
      (∀ a t, (a, t) ∈ L → acc.stored.contains a = false ∧ ∃ r?, storeOk p lay cs ix s known a t = some r? ∧
        ∀ r, r? = some r → acc'.needed.contains r = true) ∧
      (∀ x ∈ acc'.updates, x ∈ acc.updates ∨ ∃ t, (x.1, t) ∈ L ∧ x.2 = t.litVal?) ∧
      (∀ r, acc.needed.contains r = true → acc'.needed.contains r = true) ∧
      (∀ x ∈ acc.updates, x ∈ acc'.updates) ∧
      (∀ a t, (a, t) ∈ L → (a, t.litVal?) ∈ acc'.updates)
  | [], acc, acc', h => by
    simp only [checkStores, Option.some.injEq] at h; subst h
    simp
  | (a, t) :: rest, acc, acc', h => by
    unfold checkStores at h
    split at h
    · simp at h
    · rename_i hfree
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨r?, hok, hrest⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := checkStores_spec p lay cs ix s known rest _ acc' hrest
      have hfree' : acc.stored.contains a = false := by simpa using hfree
      have hneed : ∀ r, r? = some r → acc'.needed.contains r = true := by
        intro r hr; apply h4; subst hr; simp only; rw [contains_insertR]; exact Or.inl rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b; rw [h1, contains_insert64]; simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro ((e | e) | e)
          · exact Or.inr (Or.inl e.symm)
          · exact Or.inl e
          · exact Or.inr (Or.inr e)
        · rintro (e | e | e)
          · exact Or.inl (Or.inr e)
          · exact Or.inl (Or.inl e.symm)
          · exact Or.inr e
      · intro b u hb
        rcases List.mem_cons.mp hb with e | e
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨hfree', r?, hok, hneed⟩
        · obtain ⟨hf, hrest'⟩ := h2 b u e
          refine ⟨?_, hrest'⟩
          have := hf; rw [Bool.eq_false_iff] at this ⊢; intro hc; apply this
          rw [contains_insert64]; exact Or.inr hc
      · intro x hx
        rcases h3 x hx with e | ⟨u, hu, hx2⟩
        · rcases List.mem_cons.mp e with e | e
          · right; exact ⟨t, by rw [e]; exact List.mem_cons_self .., by rw [e]⟩
          · exact Or.inl e
        · right; exact ⟨u, List.mem_cons_of_mem _ hu, hx2⟩
      · intro r hr; apply h4
        split
        · rw [contains_insertR]; exact Or.inr hr
        · exact hr
      · intro x hx; exact h5 x (List.mem_cons_of_mem _ hx)
      · intro b u hb
        rcases List.mem_cons.mp hb with e | e
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact h5 _ List.mem_cons_self
        · exact h6 b u e

/-! ## 5. The waves of one dispatch -/

/-- During a dispatch whose start memory is `m0`: dwords not yet stored hold what they held at the start;
stored ones lie in the buffer, in an owned word, and hold the plan's half of it; every stored dword has
an update, and an update with a value is what memory holds. -/
structure WInv (p : GpuProgram) (m0 : Memory) (E : Nat → Word) (s : GpuStage) (m : Memory) (acc : Acc) : Prop where
  free : ∀ a, acc.stored.contains a = false → m.get? a = m0.get? a
  stored : ∀ a, acc.stored.contains a = true → inW p.words a = true ∧
    (∃ k, s.kernels.find? (·.owns ((a - wDw).toNat / 2)) = some k) ∧
    m.get? a = some (dwHalf ((a - wDw).toNat % 2) (runStage p.consts p.tables E s ((a - wDw).toNat / 2)))
  upd : ∀ x ∈ acc.updates, acc.stored.contains x.1 = true ∧ ∀ v, x.2 = some v → m.get? x.1 = some v
  upd_of : ∀ a, acc.stored.contains a = true → ∃ x ∈ acc.updates, x.1 = a

theorem checkWaves_mono (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) (s : GpuStage) (prog : Program) (known : Known) :
    ∀ (gs : List Nat) (acc acc' : Acc), checkWaves p lay cs ix s prog known gs acc = some acc' →
      ∀ r, acc.needed.contains r = true → acc'.needed.contains r = true
  | [], acc, acc', h => by simp only [checkWaves, Option.some.injEq] at h; subst h; exact fun _ h => h
  | g :: gs, acc, acc', h => by
    unfold checkWaves at h
    dsimp only at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨acc1, h1, h2⟩ := h
      intro r hr
      exact checkWaves_mono p lay cs ix s prog known gs acc1 acc' h2 r ((checkStores_spec p lay cs ix s known _ acc acc1 h1).2.2.2.1 r hr)
    · simp at h

theorem checkWaves_sound {p : GpuProgram} {lay : Memory} {cs : Array Word} {ix : Array Nat} {known : Known}
    {m0 : Memory} {E : Nat → Word} (h0 : StartOk p lay known m0 E) (hw : p.words < 2 ^ 29)
    (hcs : cs.toList = p.consts) (hix : ix.toList = p.tables) (s : GpuStage) (prog : Program) :
    ∀ (gs : List Nat) (acc acc' : Acc), checkWaves p lay cs ix s prog known gs acc = some acc' →
      (∀ r, acc'.needed.contains r = true → r.Holds) →
      ∀ m, WInv p m0 E s m acc → ∃ m', runWaves prog gs m = some m' ∧ WInv p m0 E s m' acc'
  | [], acc, acc', h, _, m, hm => by
    simp only [checkWaves, Option.some.injEq] at h; subst h; exact ⟨m, rfl, hm⟩
  | g :: gs, acc, acc', h, hneed, m, hm => by
    unfold checkWaves at h
    dsimp only [symWave] at h
    simp only [runWaves]
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨herr, hhalt⟩ := hok
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨acc1, h1, h2⟩ := h
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := checkStores_spec p lay cs ix s known _ acc acc1 h1
      have hneed1 : ∀ r, acc1.needed.contains r = true → r.Holds :=
        fun r hr => hneed r (checkWaves_mono p lay cs ix s prog known gs acc1 acc' h2 r hr)
      have hbase : ∀ a u, baseView p lay known acc.stored a = some u → m.get? a = some (u.eval (menv m0)) := by
        intro a u hu
        unfold baseView at hu
        split at hu
        · simp at hu
        · rename_i hc
          rw [hm.free a (by simpa using hc)]
          exact viewStart_ok h0 hw a u hu
      have hw' := wave_sound (env := menv m0) prog (fuelOf prog) m _ hbase descSetLo g herr
      dsimp only at hw'
      obtain ⟨serr, shalt, sload, sframe⟩ := hw'
      generalize (run prog (fuelOf prog) (initWave (⟨{}, baseView p lay known acc.stored⟩ : SymMem) descSetLo g) : SymWave) = st
        at herr hhalt h1 h2 c1 c2 c3 c4 c5 c6 shalt sload sframe
      generalize run prog (fuelOf prog) (initWave m descSetLo g : WaveState) = sc at serr shalt sload sframe ⊢
      have hkey : ∀ a, a ∈ st.mem.stores.toList.map Prod.fst ↔ ∃ t, st.mem.stores.get? a = some t := by
        intro a
        simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
          Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.get?_eq_getElem?]
      have hst : ∀ a t, st.mem.stores.get? a = some t → sc.mem.get? a = some (t.eval (menv m0)) := by
        intro a t ht; apply sload; simp only [SymMem.load, ht]
      have hnot : ∀ a, (¬ ∃ t, st.mem.stores.get? a = some t) → sc.mem.get? a = m.get? a := by
        intro a ha; apply sframe
        cases e : st.mem.stores.get? a with
        | none => rfl
        | some t => exact absurd ⟨t, e⟩ ha
      -- the wave's own stores were free before it
      have hown : ∀ a t, st.mem.stores.get? a = some t → acc.stored.contains a = false := by
        intro a t ht
        exact (c2 a t (by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact ht)).1
      have hinv1 : WInv p m0 E s sc.mem acc1 := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a ha
          have := c1 a; rw [ha] at this
          have hn : acc.stored.contains a = false ∧ ¬ ∃ t, st.mem.stores.get? a = some t := by
            rw [← hkey]; constructor
            · cases e : acc.stored.contains a <;> simp_all
            · intro hm'; simp_all
          rw [hnot a hn.2]; exact hm.free a hn.1
        · intro a ha
          rcases (c1 a).mp ha with ho | hn
          · have hn : ¬ ∃ t, st.mem.stores.get? a = some t := by
              rintro ⟨t, ht⟩; have := hown a t ht; simp_all
            obtain ⟨i1, i2, i3⟩ := hm.stored a ho
            exact ⟨i1, i2, by rw [hnot a hn]; exact i3⟩
          · obtain ⟨t, ht⟩ := (hkey a).mp hn
            have hmem : (a, t) ∈ st.mem.stores.toList := by
              rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact ht
            obtain ⟨-, r?, hok', hr?⟩ := c2 a t hmem
            obtain ⟨i1, i2, i3⟩ := storeOk_sound h0 hw hcs hix s a t r? hok' (fun r hr => hneed1 r (hr? r hr))
            exact ⟨i1, i2, by rw [hst a t ht, i3]⟩
        · intro x hx
          rcases c3 x hx with ho | ⟨t, hmem, hx2⟩
          · obtain ⟨u1, u2⟩ := hm.upd x ho
            have hn : ¬ ∃ t, st.mem.stores.get? x.1 = some t := by
              rintro ⟨t, ht⟩; have := hown x.1 t ht; simp_all
            exact ⟨(c1 x.1).mpr (Or.inl u1), fun v hv => by rw [hnot x.1 hn]; exact u2 v hv⟩
          · have ht : st.mem.stores.get? x.1 = some t := by
              rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.mem_toList_iff_getElem?_eq_some]; exact hmem
            refine ⟨(c1 x.1).mpr (Or.inr ((hkey x.1).mpr ⟨t, ht⟩)), fun v hv => ?_⟩
            rw [hst x.1 t ht, eval_of_litVal _ t v (hx2 ▸ hv)]
        · intro a ha
          rcases (c1 a).mp ha with ho | hn
          · obtain ⟨x, hx, hx1⟩ := hm.upd_of a ho
            exact ⟨x, c5 x hx, hx1⟩
          · obtain ⟨t, ht⟩ := (hkey a).mp hn
            exact ⟨(a, t.litVal?), c6 a t (by
              rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact ht), rfl⟩
      obtain ⟨m', hrun, hinv'⟩ := checkWaves_sound h0 hw hcs hix s prog gs acc1 acc' h2 hneed sc.mem hinv1
      refine ⟨m', ?_, hinv'⟩
      rw [serr, shalt, hhalt]
      simpa using hrun
    · simp at h

/-! ## 6. One dispatch -/

theorem dwHalf_join (w : Word) : (join64 (dwHalf 0 w) (dwHalf 1 w)).toBitVec = w := by
  simp only [dwHalf, ite_true, Nat.one_ne_zero, ite_false, split_join, UInt64.toBitVec_ofBitVec]

theorem applyUpdates_get (known : Known) (a : UInt64) (v : UInt32) :
    ∀ us : List (UInt64 × Option UInt32), (applyUpdates known us).get? a = some v →
      (∃ x ∈ us, x.1 = a ∧ x.2 = some v) ∨ ((∀ x ∈ us, x.1 ≠ a) ∧ known.get? a = some v)
  | [], h => Or.inr ⟨by simp, by simpa [applyUpdates] using h⟩
  | x :: us, h => by
    have ih := applyUpdates_get known a v us
    simp only [applyUpdates, List.foldr_cons] at h ih
    obtain ⟨b, o⟩ := x
    cases o with
    | some w =>
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq] at h
      by_cases hb : b = a
      · simp only [hb, ite_true, Option.some.injEq] at h
        exact Or.inl ⟨(b, some w), List.mem_cons_self, hb, by rw [h]⟩
      · simp only [hb, ite_false] at h
        rcases ih (by simpa [Std.HashMap.get?_eq_getElem?] using h) with ⟨y, hy, e⟩ | ⟨hn, hk⟩
        · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, e⟩
        · refine Or.inr ⟨?_, hk⟩
          intro y hy; rcases List.mem_cons.mp hy with e | e
          · rw [e]; exact hb
          · exact hn y e
    | none =>
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase, beq_iff_eq] at h
      by_cases hb : b = a
      · simp [hb] at h
      · simp only [hb, ite_false] at h
        rcases ih (by simpa [Std.HashMap.get?_eq_getElem?] using h) with ⟨y, hy, e⟩ | ⟨hn, hk⟩
        · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, e⟩
        · refine Or.inr ⟨?_, hk⟩
          intro y hy; rcases List.mem_cons.mp hy with e | e
          · rw [e]; exact hb
          · exact hn y e

theorem mem_ownedDwords (s : GpuStage) (k : Kernel) (hk : k ∈ s.kernels) (j : Nat) (hj : k.owns j = true) :
    dwLo j ∈ ownedDwords s ∧ dwLo j + 1 ∈ ownedDwords s := by
  simp only [Kernel.owns, decide_eq_true_eq] at hj
  have he : j = k.dstBase + (j - k.dstBase) := by omega
  constructor <;>
  · simp only [ownedDwords, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨k, hk, j - k.dstBase, by omega, by rw [← he]; simp⟩

theorem checkStage_sound {p : GpuProgram} {lay : Memory} {cs : Array Word} {ix : Array Nat} {known : Known}
    {m0 : Memory} {E : Nat → Word} (h0 : StartOk p lay known m0 E) (hw : p.words < 2 ^ 29)
    (hcs : cs.toList = p.consts) (hix : ix.toList = p.tables) (s : GpuStage)
    (hks : ∀ k ∈ s.kernels, k.dstBase + k.count ≤ p.words) (prog : Program)
    (known' : Known) (n : Std.HashSet Residual) (hc : checkStage p lay cs ix s prog known = some (known', n))
    (hn : ∀ r, n.contains r = true → r.Holds) :
    ∃ m', runWaves prog (List.range (groupsOf s.threads)) m0 = some m' ∧
      StartOk p lay known' m' (runStage p.consts p.tables E s) := by
  unfold checkStage at hc
  simp only [Option.bind_eq_some_iff] at hc
  obtain ⟨acc, hw', hall⟩ := hc
  split at hall
  · rename_i hown
    simp only [Option.some.injEq, Prod.mk.injEq] at hall
    obtain ⟨rfl, rfl⟩ := hall
    have hinit : WInv p m0 E s m0 ⟨{}, [], {}⟩ :=
      ⟨fun _ _ => rfl, fun a ha => by simp at ha, fun x hx => by simp at hx, fun a ha => by simp at ha⟩
    obtain ⟨m', hrun, hi⟩ := checkWaves_sound h0 hw hcs hix s prog _ _ acc hw' hn m0 hinit
    refine ⟨m', hrun, ?_⟩
    have hstored : ∀ a, a ∈ ownedDwords s → acc.stored.contains a = true :=
      fun a ha => (List.all_eq_true.mp hown) a ha
    -- a dword of an unowned word was never stored
    have hfree : ∀ j, j < p.words → s.kernels.find? (·.owns j) = none →
        acc.stored.contains (dwLo j) = false ∧ acc.stored.contains (dwLo j + 1) = false := by
      intro j hj hnone
      constructor <;>
      · rw [Bool.eq_false_iff]; intro hc
        obtain ⟨-, ⟨k, hk⟩, -⟩ := hi.stored _ hc
        first
          | rw [off_dwLo j (by omega), Nat.mul_div_cancel_left _ (by decide)] at hk
          | rw [off_dwLo1 j (by omega), show (2 * j + 1) / 2 = j by omega] at hk
        rw [hnone] at hk; simp at hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      cases hf : s.kernels.find? (·.owns j) with
      | some k =>
        have hkm := List.mem_of_find?_eq_some hf
        have hko := List.find?_some hf
        obtain ⟨d0, d1⟩ := mem_ownedDwords s k hkm j hko
        obtain ⟨-, -, v0⟩ := hi.stored _ (hstored _ d0)
        obtain ⟨-, -, v1⟩ := hi.stored _ (hstored _ d1)
        rw [off_dwLo j (by omega)] at v0
        rw [off_dwLo1 j (by omega)] at v1
        refine ⟨_, _, v0, v1, ?_⟩
        rw [show 2 * j % 2 = 0 by omega, show 2 * j / 2 = j by omega,
          show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
        exact dwHalf_join _
      | none =>
        obtain ⟨f0, f1⟩ := hfree j hj hf
        obtain ⟨lo, hi', e0, e1, e⟩ := h0.word j hj
        refine ⟨lo, hi', by rw [hi.free _ f0]; exact e0, by rw [hi.free _ f1]; exact e1, ?_⟩
        unfold runStage; rw [hf]; exact e
    · intro j hj
      unfold runStage
      cases hf : s.kernels.find? (·.owns j) with
      | some k =>
        have hko := List.find?_some hf
        simp only [Kernel.owns, decide_eq_true_eq] at hko
        have := hks k (List.mem_of_find?_eq_some hf); omega
      | none => exact h0.past j hj
    · intro a ha
      have hc : acc.stored.contains a = false := by
        rw [Bool.eq_false_iff]; intro hc; have := (hi.stored a hc).1; rw [ha] at this; exact Bool.false_ne_true this
      rw [hi.free a hc]; exact h0.out a ha
    · intro a v hk ha
      rcases applyUpdates_get known a v _ hk with ⟨x, hx, hx1, hx2⟩ | ⟨hn', hk'⟩
      · rw [← hx1]; exact (hi.upd x hx).2 v hx2
      · have hc : acc.stored.contains a = false := by
          rw [Bool.eq_false_iff]; intro hc
          obtain ⟨x, hx, hx1⟩ := hi.upd_of a hc
          exact hn' x hx hx1
        rw [hi.free a hc]; exact h0.known a v hk' ha
  · simp at hall

/-! ## 7. Every dispatch -/

theorem foldl_insert_contains (r : Residual) :
    ∀ (l : List Residual) (acc : Std.HashSet Residual),
      (l.foldl (·.insert ·) acc).contains r = true ↔ acc.contains r = true ∨ r ∈ l
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_insert_contains r l, contains_insertR]
    simp only [List.mem_cons]
    constructor
    · rintro ((e | e) | e)
      · exact Or.inr (Or.inl e.symm)
      · exact Or.inl e
      · exact Or.inr (Or.inr e)
    · rintro (e | e | e)
      · exact Or.inl (Or.inr e)
      · exact Or.inl (Or.inl e.symm)
      · exact Or.inr e

theorem fold_insert_contains (n acc : Std.HashSet Residual) (r : Residual) :
    (n.fold (·.insert ·) acc).contains r = true ↔ acc.contains r = true ∨ n.contains r = true := by
  rw [Std.HashSet.fold_eq_foldl_toList, foldl_insert_contains, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]

theorem checkProgram_mono (p : GpuProgram) (lay : Memory) (cs : Array Word) (ix : Array Nat) :
    ∀ (ss : List GpuStage) (progs : List Program) (known : Known) (need fin : Std.HashSet Residual),
      checkProgram p lay cs ix ss progs known need = some fin → ∀ r, need.contains r = true → fin.contains r = true
  | [], [], _, need, fin, h => by simp only [checkProgram, Option.some.injEq] at h; subst h; exact fun _ h => h
  | s :: ss, prog :: progs, known, need, fin, h => by
    simp only [checkProgram, Option.bind_eq_some_iff] at h
    obtain ⟨⟨known', n⟩, _, h2⟩ := h
    intro r hr
    exact checkProgram_mono p lay cs ix ss progs known' _ fin h2 r ((fold_insert_contains n need r).mpr (Or.inl hr))
  | [], _ :: _, _, _, _, h => by simp [checkProgram] at h
  | _ :: _, [], _, _, _, h => by simp [checkProgram] at h

theorem checkProgram_sound {p : GpuProgram} {lay : Memory} {cs : Array Word} {ix : Array Nat}
    (hw : p.words < 2 ^ 29) (hcs : cs.toList = p.consts) (hix : ix.toList = p.tables) :
    ∀ (ss : List GpuStage) (progs : List Program) (known : Known) (need fin : Std.HashSet Residual)
      (m : Memory) (E : Nat → Word),
      (∀ s ∈ ss, ∀ k ∈ s.kernels, k.dstBase + k.count ≤ p.words) →
      checkProgram p lay cs ix ss progs known need = some fin → (∀ r, fin.contains r = true → r.Holds) →
      StartOk p lay known m E →
      ∃ m' known', runDispatch (progs.zip (ss.map GpuStage.threads)) m = some m' ∧
        StartOk p lay known' m' (ss.foldl (runStage p.consts p.tables) E)
  | [], [], known, _, _, m, E, _, _, _, h0 => ⟨m, known, rfl, h0⟩
  | s :: ss, prog :: progs, known, need, fin, m, E, hks, h, hfin, h0 => by
    simp only [checkProgram, Option.bind_eq_some_iff] at h
    obtain ⟨⟨known', n⟩, h1, h2⟩ := h
    have hn : ∀ r, n.contains r = true → r.Holds := fun r hr =>
      hfin r (checkProgram_mono p lay cs ix ss progs known' _ fin h2 r ((fold_insert_contains n need r).mpr (Or.inr hr)))
    obtain ⟨m1, hrun, h1'⟩ := checkStage_sound h0 hw hcs hix s (hks s List.mem_cons_self) prog known' n h1 hn
    obtain ⟨m', known'', hrest, hend⟩ := checkProgram_sound hw hcs hix ss progs known' _ fin m1 _
      (fun s' hs' => hks s' (List.mem_cons_of_mem _ hs')) h2 hfin h1'
    refine ⟨m', known'', ?_, hend⟩
    simp only [List.map_cons, List.zip_cons_cons, runDispatch, hrun, Option.bind_some, hrest]
  | [], _ :: _, _, _, _, _, _, _, h, _, _ => by simp [checkProgram] at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => by simp [checkProgram] at h

/-! ## 8. The memory the host starts from -/

theorem shift_wAddr (i : Nat) (hi : i < 2 ^ 29) : (wAddr + UInt64.ofNat (8 * i)) >>> 2 = dwLo i := by
  apply UInt64.toNat_inj.mp
  rw [dwLo_toNat i hi, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [show wAddr.toNat = 2 ^ 32 by decide, show (2 : UInt64).toNat % 64 = 2 by decide, Nat.shiftRight_eq_div_pow]
  omega

theorem writeWord (m : Memory) (i : Nat) (hi : i < 2 ^ 29) (w : Word) :
    writeDwords m (wAddr + UInt64.ofNat (8 * i)) (wordDwords w)
      = (m.insert (dwLo i) (dwHalf 0 w)).insert (dwLo i + 1) (dwHalf 1 w) := by
  simp only [writeDwords, wordDwords, shift_wAddr i hi, dwHalf, ite_true, Nat.one_ne_zero, ite_false]
  rw [← Array.foldl_toList, Array.toList_zipIdx]
  simp [List.zipIdx]

theorem dwLo_inj (i j : Nat) (hi : i < 2 ^ 29) (hj : j < 2 ^ 29) (b c : Nat) (hb : b < 2) (hc : c < 2)
    (h : dwLo i + UInt64.ofNat b = dwLo j + UInt64.ofNat c) : i = j ∧ b = c := by
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, dwLo_toNat i hi, dwLo_toNat j hj, UInt64.toNat_ofNat'] at this
  omega

/-- The buffer's first `n` words written over the layout. -/
theorem memOf_prefix (words : Nat) (consts : List Word) (tables : List Nat) (flat : Nat → Word) :
    ∀ n, n < 2 ^ 29 →
      let m := (List.range n).foldl (fun m i => writeDwords m (wAddr + UInt64.ofNat (8 * i)) (wordDwords (flat i)))
        (layoutMem words consts tables)
      (∀ i, i < n → m.get? (dwLo i) = some (dwHalf 0 (flat i)) ∧ m.get? (dwLo i + 1) = some (dwHalf 1 (flat i))) ∧
      (∀ a, (∀ i, i < n → a ≠ dwLo i ∧ a ≠ dwLo i + 1) → m.get? a = (layoutMem words consts tables).get? a)
  | 0, _ => by simp
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := memOf_prefix words consts tables flat n (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [writeWord _ n (by omega)]
    generalize (List.range n).foldl _ _ = m at ih1 ih2
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq] at ih1 ih2 ⊢
    have hne := dwLo_ne n (by omega)
    refine ⟨fun i hi => ?_, fun a ha => ?_⟩
    · by_cases e : i = n
      · subst e; simp
      · have h1 : dwLo n ≠ dwLo i := fun h => e (dwLo_inj n i (by omega) (by omega) 0 0 (by decide) (by decide)
          (by simpa using h)).1.symm
        have h2 : dwLo n + 1 ≠ dwLo i := fun h => e (dwLo_inj n i (by omega) (by omega) 1 0 (by decide) (by decide)
          (by simpa using h)).1.symm
        have h3 : dwLo n ≠ dwLo i + 1 := fun h => e (dwLo_inj n i (by omega) (by omega) 0 1 (by decide) (by decide)
          (by simpa using h)).1.symm
        have h4 : dwLo n + 1 ≠ dwLo i + 1 := fun h => e (dwLo_inj n i (by omega) (by omega) 1 1 (by decide) (by decide)
          (by simpa using h)).1.symm
        simp only [h1, h2, h3, h4, ite_false]
        exact ih1 i (by omega)
    · obtain ⟨a1, a2⟩ := ha n (by omega)
      simp only [Ne.symm a1, Ne.symm a2, ite_false]
      exact ih2 a (fun i hi => ha i (by omega))

theorem memOf_start (p : GpuProgram) (hw : p.words < 2 ^ 29) (flat : Nat → Word) :
    StartOk p (layoutOf p) {} (memOf p.words p.consts p.tables flat) (fun j => if j < p.words then flat j else 0) := by
  obtain ⟨h1, h2⟩ := memOf_prefix p.words p.consts p.tables flat p.words hw
  refine ⟨fun j hj => ⟨_, _, h1 j hj |>.1, h1 j hj |>.2, ?_⟩, fun j hj => ?_, fun a ha => ?_, fun a v hk _ => ?_⟩
  · simp only [hj, ite_true]; exact dwHalf_join _
  · simp only [show ¬ j < p.words by omega, ite_false]
  · apply h2
    intro i hi
    obtain ⟨i0, i1⟩ := inW_dwLo p.words i hw hi
    exact ⟨fun e => by rw [e, i0] at ha; exact Bool.false_ne_true ha.symm,
      fun e => by rw [e, i1] at ha; exact Bool.false_ne_true ha.symm⟩
  · simp at hk

/-! ## 9. The certificate -/

/-- If the certificate is accepted and every residual it names holds, then for every content `flat` of the
wire buffer, the decoded programs, run on the model as the host dispatches them, succeed and leave in
every word of the buffer what the plan's stages compute from `flat`. -/
theorem certify_sound (p : GpuProgram) (progs : List Program) (rs : List Residual)
    (hc : certify p progs rs = true) (hrs : ∀ r ∈ rs, r.Holds) (flat : Nat → Word) :
    ∃ m, runDispatch (progs.zip (p.stages.map GpuStage.threads)) (memOf p.words p.consts p.tables flat) = some m ∧
      ∀ i, i < p.words →
        wordAt m i = runStages p.consts p.tables (fun j => if j < p.words then flat j else 0) p.stages i := by
  unfold certify at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hw, hks⟩, hcp⟩ := hc
  split at hcp
  · rename_i need hneed
    have hfin : ∀ r, need.contains r = true → r.Holds := by
      intro r hr
      apply hrs
      have := List.all_eq_true.mp hcp r (by rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]; exact hr)
      simpa using this
    obtain ⟨m, known', hrun, hend⟩ := checkProgram_sound (lay := layoutOf p) hw List.toList_toArray List.toList_toArray p.stages progs {} {} need _ _
      (fun s hs k hk => hks s hs k hk) hneed hfin (memOf_start p hw flat)
    refine ⟨m, hrun, fun i hi => ?_⟩
    obtain ⟨lo, hi', e0, e1, e⟩ := hend.word i hi
    have a0 : wDw + UInt64.ofNat (2 * i) = dwLo i := rfl
    unfold wordAt
    rw [a0, e0, e1]
    exact e
  · simp at hcp

/-! ## 10. The graph's outputs -/

open Obend.Hardware.OpenHypergraph in
theorem foldl_add_init : ∀ (ls : List Nat) (a : Nat), ls.foldl (· + ·) a = a + ls.foldl (· + ·) 0
  | [], a => by simp
  | l :: ls, a => by
    simp only [List.foldl_cons]
    rw [foldl_add_init ls (a + l), foldl_add_init ls (0 + l)]; omega

open Obend.Hardware.OpenHypergraph in
theorem sumNatList_cons (l : Nat) (ls : List Nat) : sumNatList (l :: ls) = l + sumNatList ls := by
  simp only [sumNatList, List.foldl_cons]; rw [foldl_add_init]; omega

open Obend.Hardware.OpenHypergraph in
theorem base_add_lt : ∀ (ls : List Nat) (w e : Nat), w < ls.length → e < ls.getD w 0 → base ls w + e < sumNatList ls
  | [], _, _, h, _ => by simp at h
  | l :: ls, 0, e, _, he => by
    simp only [base, List.getD_cons_zero] at he ⊢; rw [sumNatList_cons]; omega
  | l :: ls, w + 1, e, hw, he => by
    simp only [base, List.getD_cons_succ, List.length_cons] at he hw ⊢
    have := base_add_lt ls w e (by omega) he
    rw [sumNatList_cons]; omega

/-- The certificate composed with rung G1: for a well-formed graph whose lowering the certificate accepts,
for every input `env` and every buffer `flat` that lays it out, the decoded programs run on the model
succeed, and the output wires read from the final memory are `evalGraph`'s. -/
theorem certified_outputs (g : ArrayGraph) (hWf : g.wf = true) (progs : List Program) (rs : List Residual)
    (hc : certify (lowerArrayToGpu g) progs rs = true) (hrs : ∀ r ∈ rs, r.Holds)
    (env : Nat → Vec) (flat : Nat → Word) (hGood : Good g.lengths env) (hFlat : Flat g.lengths env flat) :
    let p := lowerArrayToGpu g
    ∃ m, runDispatch (progs.zip (p.stages.map GpuStage.threads)) (memOf p.words p.consts p.tables flat) = some m ∧
      p.outputs.map (fun w => (List.range (p.wireLen.getD w 0)).map fun e => wordAt m (p.wireBase.getD w 0 + e))
        = evalGraph g env := by
  intro p
  obtain ⟨m, hrun, hw⟩ := certify_sound p progs rs hc hrs flat
  refine ⟨m, hrun, ?_⟩
  let flatW : Nat → Word := fun j => if j < p.words then flat j else 0
  have hFlatW : Flat g.lengths env flatW := by
    intro w e hw' he
    have hlt := base_add_lt g.lengths w e hw' he
    simp only [flatW, p, lowerArrayToGpu, hlt, ite_true]
    exact hFlat w e hw' he
  rw [← lowerArrayToGpu_sound g hWf env flatW hGood hFlatW]
  unfold runProgram
  apply List.map_congr_left
  intro w _
  apply List.map_congr_left
  intro e he
  rw [List.mem_range] at he
  have hwl : w < g.lengths.length := by
    apply Nat.lt_of_not_le; intro hn
    simp only [p, lowerArrayToGpu, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : g.lengths.length ≤ w),
      Option.getD_none] at he
    omega
  have hb : p.wireBase.getD w 0 = base g.lengths w := by
    simp [p, lowerArrayToGpu, List.getD_eq_getElem?_getD, hwl]
  have hl : p.wireLen.getD w 0 = g.lengths.getD w 0 := rfl
  rw [hl] at he
  rw [hb]
  exact hw _ (base_add_lt g.lengths w e hwl he)

end Obend.Hardware.Gpu.Rdna2
