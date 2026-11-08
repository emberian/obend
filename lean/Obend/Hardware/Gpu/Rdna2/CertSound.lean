/-
# Obend.Hardware.Gpu.Rdna2.CertSound — what an accepted certificate means

`checkProgram_sound`: if `checkProgram` accepts a list of stages each keeping its promise (`Spec.Sound`) and
every residual it names holds, then from every start memory holding the wire buffer, running the decoded
programs on the wave model as the host dispatches them succeeds and leaves in every word of the buffer what
the stages' meanings compose to. The proof follows the check: a stage's start memory is the environment
every symbolic term is read in (`viewStart` describes it), each wave of the dispatch is related to its
symbolic run by `wave_sound`, and each stored dword is the table's by `storeOk_sound` (`residual_sound`).
`memOf_start` is the host's memory as such a start.
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

theorem inW_lds (words : Nat) (hw : words < 2 ^ 29) (a : UInt64) (h : inW words a = true) : inLds a = false := by
  rw [inW_iff words hw] at h
  have : ¬ (0x10000000000 : UInt64) ≤ a := by
    rw [UInt64.le_iff_toNat_le, show (0x10000000000 : UInt64).toNat = 2 ^ 40 by decide]; omega
  simp [inLds, this]

/-! ## 2. The memory at the start of a dispatch -/

/-- Memory as the environment terms are read in (an absent dword reads `0`; the invariant makes every
dword the check reads present). -/
def menv (m : Memory) : UInt64 → UInt32 := fun a => (m.get? a).getD 0

/-- The memory at the start of a dispatch: the wire buffer holds `E` word by word (every dword present),
`E` is `0` past the buffer, the rest of memory outside the LDS regions is the layout, and the known
constants are what it holds. -/
structure StartOk (words : Nat) (lay : Memory) (known : Known) (m : Memory) (E : Nat → Word) : Prop where
  word : ∀ j, j < words → ∃ lo hi, m.get? (dwLo j) = some lo ∧ m.get? (dwLo j + 1) = some hi ∧
    (join64 lo hi).toBitVec = E j
  past : ∀ j, words ≤ j → E j = 0
  out : ∀ a, inW words a = false → inLds a = false → m.get? a = lay.get? a
  known : ∀ a v, known.get? a = some v → inW words a = true → m.get? a = some v

theorem StartOk.present {words : Nat} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk words lay known m E) (hw : words < 2 ^ 29) (a : UInt64) (ha : inW words a = true) :
    ∃ v, m.get? a = some v := by
  obtain ⟨hj, h0, h1⟩ := inW_split words hw a ha
  obtain ⟨lo, hi, hlo, hhi, -⟩ := h.word _ hj
  rcases Nat.mod_two_eq_zero_or_one (a - wDw).toNat with e | e
  · exact ⟨lo, by rw [h0 e]; exact hlo⟩
  · exact ⟨hi, by rw [h1 e]; exact hhi⟩

theorem viewStart_lds {words : Nat} {lay : Memory} {known : Known} (hw : words < 2 ^ 29) (a : UInt64) (u : Tm)
    (hv : viewStart words lay known a = some u) : inLds a = false := by
  unfold viewStart at hv
  split at hv
  · next ha => exact inW_lds words hw a ha
  · split at hv
    · simp at hv
    · next hl => simpa using hl

theorem viewStart_ok {words : Nat} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk words lay known m E) (hw : words < 2 ^ 29) (a : UInt64) (u : Tm)
    (hv : viewStart words lay known a = some u) : m.get? a = some (u.eval (menv m)) := by
  have hl := viewStart_lds hw a u hv
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
    rw [ite_eq_right (by simp [hl])] at hv
    simp only [Option.map_eq_some_iff] at hv
    obtain ⟨v, hl', rfl⟩ := hv
    rw [eval_lit, h.out a (by simpa using ha) hl, hl']

theorem join64_zero : join64 0 0 = 0 := by decide

theorem readWord_ev {words : Nat} {lay : Memory} {known : Known} {m : Memory} {E : Nat → Word}
    (h : StartOk words lay known m E) (hw : words < 2 ^ 29) (j : Nat) :
    (readWord words lay known j).ev (menv m) = E j := by
  unfold readWord
  split
  · rename_i hj
    obtain ⟨lo, hi, hlo, hhi, he⟩ := h.word j hj
    obtain ⟨i0, i1⟩ := inW_dwLo words j hw hj
    have v0 : ∃ u, viewStart words lay known (dwLo j) = some u := by
      unfold viewStart; rw [ite_eq_left i0]; exact ⟨_, rfl⟩
    have v1 : ∃ u, viewStart words lay known (dwLo j + 1) = some u := by
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

/-- A dword the check accepts: in the buffer, in a word of the table, and holding that word's half of what
the table's terms mean. -/
theorem storeOk_sound {words : Nat} {T : Std.HashMap Nat TP} {env : UInt64 → UInt32} {V : Nat → Word}
    (hT : ∀ i t, T[i]? = some t → t.ev env = V i) (a : UInt64) (t : Tm)
    (r? : Option Residual) (hs : storeOk words T a t = some r?) (hr : ∀ r, r? = some r → r.Holds) :
    inW words a = true ∧ (∃ sp, T[(a - wDw).toNat / 2]? = some sp) ∧
      t.eval env = dwHalf ((a - wDw).toNat % 2) (V ((a - wDw).toNat / 2)) := by
  unfold storeOk at hs
  split at hs
  · simp at hs
  · rename_i hin
    have hin' : inW words a = true := by simpa using hin
    simp only at hs
    split at hs
    · simp at hs
    · rename_i sp hk
      refine ⟨hin', ⟨sp, hk⟩, ?_⟩
      rw [← hT _ _ hk, dwHalf_ev _ _ _]
      have hsel : (if (a - wDw).toNat % 2 == 0 then sp.1 else sp.2)
          = (if (a - wDw).toNat % 2 = 0 then sp.1 else sp.2) := by
        by_cases e : (a - wDw).toNat % 2 = 0 <;> simp [e]
      rw [shareCommon_eq, hsel] at hs
      generalize (if (a - wDw).toNat % 2 = 0 then sp.1 else sp.2) = x at hs ⊢
      by_cases heq : (t == x) = true
      · rw [eq_of_beq heq]
      · rw [ite_eq_right heq, Option.map_eq_some_iff] at hs
        obtain ⟨r, hres, hr?⟩ := hs
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

/-- What `checkStores` establishes about a list of stores: each outside the LDS regions was free and
accepted (its residual kept), the stored set grows by exactly their addresses, every update is an old one
or one of theirs, and the residuals only grow. -/
theorem checkStores_spec (words : Nat) (T : Std.HashMap Nat TP) :
    ∀ (L : List (UInt64 × Tm)) (acc acc' : Acc), checkStores words T L acc = some acc' →
      (∀ a, acc'.stored.contains a = true ↔ acc.stored.contains a = true ∨ ∃ t, (a, t) ∈ L ∧ inLds a = false) ∧
      (∀ a t, (a, t) ∈ L → inLds a = false → acc.stored.contains a = false ∧ ∃ r?, storeOk words T a t = some r? ∧
        ∀ r, r? = some r → acc'.needed.contains r = true) ∧
      (∀ x ∈ acc'.updates, x ∈ acc.updates ∨ ∃ t, (x.1, t) ∈ L ∧ inLds x.1 = false ∧ x.2 = t.litVal?) ∧
      (∀ r, acc.needed.contains r = true → acc'.needed.contains r = true) ∧
      (∀ x ∈ acc.updates, x ∈ acc'.updates) ∧
      (∀ a t, (a, t) ∈ L → inLds a = false → (a, t.litVal?) ∈ acc'.updates)
  | [], acc, acc', h => by
    simp only [checkStores, Option.some.injEq] at h; subst h
    simp
  | (a, t) :: rest, acc, acc', h => by
    unfold checkStores at h
    split at h
    · rename_i hl
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := checkStores_spec words T rest acc acc' h
      have nohead : ∀ b u, (b, u) = (a, t) → inLds b = false → False := by
        intro b u e hb; simp only [Prod.mk.injEq] at e; rw [e.1, hl] at hb; exact Bool.noConfusion hb
      refine ⟨?_, ?_, ?_, h4, h5, ?_⟩
      · intro b; rw [h1]; constructor
        · rintro (e | ⟨u, hu, hb⟩)
          · exact Or.inl e
          · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hb⟩
        · rintro (e | ⟨u, hu, hb⟩)
          · exact Or.inl e
          · rcases List.mem_cons.mp hu with e | e
            · exact (nohead b u e hb).elim
            · exact Or.inr ⟨u, e, hb⟩
      · intro b u hb hbl
        rcases List.mem_cons.mp hb with e | e
        · exact (nohead b u e hbl).elim
        · exact h2 b u e hbl
      · intro x hx; rcases h3 x hx with e | ⟨u, hu, hl', hx2⟩
        · exact Or.inl e
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hl', hx2⟩
      · intro b u hb hbl
        rcases List.mem_cons.mp hb with e | e
        · exact (nohead b u e hbl).elim
        · exact h6 b u e hbl
    · rename_i hl
      have hl' : inLds a = false := by simpa using hl
      split at h
      · simp at h
      · rename_i hfree
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨r?, hok, hrest⟩ := h
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := checkStores_spec words T rest _ acc' hrest
        have hfree' : acc.stored.contains a = false := by simpa using hfree
        have hneed : ∀ r, r? = some r → acc'.needed.contains r = true := by
          intro r hr; apply h4; subst hr; simp only; rw [contains_insertR]; exact Or.inl rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro b; rw [h1, contains_insert64]; constructor
          · rintro ((e | e) | ⟨u, hu, hb⟩)
            · subst e; exact Or.inr ⟨t, List.mem_cons_self, hl'⟩
            · exact Or.inl e
            · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hb⟩
          · rintro (e | ⟨u, hu, hb⟩)
            · exact Or.inl (Or.inr e)
            · rcases List.mem_cons.mp hu with e | e
              · simp only [Prod.mk.injEq] at e; exact Or.inl (Or.inl e.1.symm)
              · exact Or.inr ⟨u, e, hb⟩
        · intro b u hb hbl
          rcases List.mem_cons.mp hb with e | e
          · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
            exact ⟨hfree', r?, hok, hneed⟩
          · obtain ⟨hf, hrest'⟩ := h2 b u e hbl
            refine ⟨?_, hrest'⟩
            have := hf; rw [Bool.eq_false_iff] at this ⊢; intro hc; apply this
            rw [contains_insert64]; exact Or.inr hc
        · intro x hx
          rcases h3 x hx with e | ⟨u, hu, hul, hx2⟩
          · rcases List.mem_cons.mp e with e | e
            · right; exact ⟨t, by rw [e]; exact List.mem_cons_self, by rw [e]; exact hl', by rw [e]⟩
            · exact Or.inl e
          · right; exact ⟨u, List.mem_cons_of_mem _ hu, hul, hx2⟩
        · intro r hr; apply h4
          split
          · rw [contains_insertR]; exact Or.inr hr
          · exact hr
        · intro x hx; exact h5 x (List.mem_cons_of_mem _ hx)
        · intro b u hb hbl
          rcases List.mem_cons.mp hb with e | e
          · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
            exact h5 _ List.mem_cons_self
          · exact h6 b u e hbl

/-! ## 5. The waves of one dispatch -/

/-- During a dispatch whose start memory is `m0`: dwords outside the LDS regions not yet stored hold what
they held at the start; stored ones lie in the buffer, in a word of the table, and hold their half of `V`
there; every stored dword has an update, and an update with a value is what memory holds. -/
structure WInv (words : Nat) (m0 : Memory) (T : Std.HashMap Nat TP) (V : Nat → Word) (m : Memory) (acc : Acc) : Prop where
  free : ∀ a, acc.stored.contains a = false → inLds a = false → m.get? a = m0.get? a
  stored : ∀ a, acc.stored.contains a = true → inW words a = true ∧
    (∃ sp, T[(a - wDw).toNat / 2]? = some sp) ∧
    m.get? a = some (dwHalf ((a - wDw).toNat % 2) (V ((a - wDw).toNat / 2)))
  upd : ∀ x ∈ acc.updates, acc.stored.contains x.1 = true ∧ ∀ v, x.2 = some v → m.get? x.1 = some v
  upd_of : ∀ a, acc.stored.contains a = true → ∃ x ∈ acc.updates, x.1 = a

theorem checkWaves_mono (words : Nat) (lay : Memory) (T : Std.HashMap Nat TP) (prog : Program) (lds : Nat) (known : Known) :
    ∀ (gs : List Nat) (acc acc' : Acc), checkWaves words lay T prog lds known gs acc = some acc' →
      ∀ r, acc.needed.contains r = true → acc'.needed.contains r = true
  | [], acc, acc', h => by simp only [checkWaves, Option.some.injEq] at h; subst h; exact fun _ h => h
  | g :: gs, acc, acc', h => by
    unfold checkWaves at h
    dsimp only at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨acc1, h1, h2⟩ := h
      intro r hr
      exact checkWaves_mono words lay T prog lds known gs acc1 acc' h2 r ((checkStores_spec words T _ acc acc1 h1).2.2.2.1 r hr)
    · simp at h

theorem checkWaves_sound {words : Nat} {lay : Memory} {known : Known} {T : Std.HashMap Nat TP} {V : Nat → Word}
    {m0 : Memory} {E : Nat → Word} (h0 : StartOk words lay known m0 E) (hw : words < 2 ^ 29)
    (hT : ∀ i t, T[i]? = some t → t.ev (menv m0) = V i) (prog : Program) (lds : Nat) :
    ∀ (gs : List Nat) (acc acc' : Acc), checkWaves words lay T prog lds known gs acc = some acc' →
      (∀ r, acc'.needed.contains r = true → r.Holds) →
      ∀ m, WInv words m0 T V m acc → ∃ m', runWaves prog lds gs m = some m' ∧ WInv words m0 T V m' acc'
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
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := checkStores_spec words T _ acc acc1 h1
      have hneed1 : ∀ r, acc1.needed.contains r = true → r.Holds :=
        fun r hr => hneed r (checkWaves_mono words lay T prog lds known gs acc1 acc' h2 r hr)
      have hbase : ∀ a u, baseView words lay known acc.stored a = some u → m.get? a = some (u.eval (menv m0)) := by
        intro a u hu
        unfold baseView at hu
        split at hu
        · simp at hu
        · rename_i hc
          rw [hm.free a (by simpa using hc) (viewStart_lds hw a u hu)]
          exact viewStart_ok h0 hw a u hu
      have hw' := swave_sound (menv m0) prog (fuelOf prog) m _ hbase descSetLo g (ldsBaseOf g) lds herr
      dsimp only at hw'
      obtain ⟨serr, shalt, sload, sframe⟩ := hw'
      generalize (srun prog (fuelOf prog) (initWave (⟨{}, baseView words lay known acc.stored⟩ : SymMem) descSetLo g
          (ldsBaseOf g) lds) : SymWave) = st
        at herr hhalt h1 h2 c1 c2 c3 c4 c5 c6 shalt sload sframe
      generalize run prog (fuelOf prog) (initWave m descSetLo g (ldsBaseOf g) lds : WaveState) = sc
        at serr shalt sload sframe ⊢
      have hmem : ∀ a t, (a, t) ∈ st.mem.stores.toList ↔ st.mem.stores.get? a = some t := by
        intro a t
        rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
      have hst : ∀ a t, st.mem.stores.get? a = some t → sc.mem.get? a = some (t.eval (menv m0)) := by
        intro a t ht; apply sload; simp only [SymMem.load, ht]
      have hnot : ∀ a, (¬ ∃ t, st.mem.stores.get? a = some t) → sc.mem.get? a = m.get? a := by
        intro a ha; apply sframe
        cases e : st.mem.stores.get? a with
        | none => rfl
        | some t => exact absurd ⟨t, e⟩ ha
      -- the wave's own stores outside its LDS were free before it
      have hown : ∀ a t, st.mem.stores.get? a = some t → inLds a = false → acc.stored.contains a = false := by
        intro a t ht hl
        exact (c2 a t ((hmem a t).mpr ht) hl).1
      have hold : ∀ a, acc.stored.contains a = true → ¬ ∃ t, st.mem.stores.get? a = some t := by
        rintro a ha ⟨t, ht⟩
        have := hown a t ht (inW_lds words hw a (hm.stored a ha).1)
        rw [ha] at this; exact Bool.noConfusion this
      have hinv1 : WInv words m0 T V sc.mem acc1 := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a ha hl
          have hc := c1 a; rw [ha] at hc
          have h1' : acc.stored.contains a = false := by
            cases e : acc.stored.contains a
            · rfl
            · exact absurd (hc.mpr (Or.inl e)) Bool.false_ne_true
          have h2' : ¬ ∃ t, st.mem.stores.get? a = some t := by
            rintro ⟨t, ht⟩; exact Bool.false_ne_true (hc.mpr (Or.inr ⟨t, (hmem a t).mpr ht, hl⟩))
          rw [hnot a h2']; exact hm.free a h1' hl
        · intro a ha
          rcases (c1 a).mp ha with ho | ⟨t, hmt, hl⟩
          · obtain ⟨i1, i2, i3⟩ := hm.stored a ho
            exact ⟨i1, i2, by rw [hnot a (hold a ho)]; exact i3⟩
          · have ht := (hmem a t).mp hmt
            obtain ⟨-, r?, hok', hr?⟩ := c2 a t hmt hl
            obtain ⟨i1, i2, i3⟩ := storeOk_sound hT a t r? hok' (fun r hr => hneed1 r (hr? r hr))
            exact ⟨i1, i2, by rw [hst a t ht, i3]⟩
        · intro x hx
          rcases c3 x hx with ho | ⟨t, hmt, hl, hx2⟩
          · obtain ⟨u1, u2⟩ := hm.upd x ho
            exact ⟨(c1 x.1).mpr (Or.inl u1), fun v hv => by rw [hnot x.1 (hold x.1 u1)]; exact u2 v hv⟩
          · have ht := (hmem x.1 t).mp hmt
            refine ⟨(c1 x.1).mpr (Or.inr ⟨t, hmt, hl⟩), fun v hv => ?_⟩
            rw [hst x.1 t ht, eval_of_litVal _ t v (hx2 ▸ hv)]
        · intro a ha
          rcases (c1 a).mp ha with ho | ⟨t, hmt, hl⟩
          · obtain ⟨x, hx, hx1⟩ := hm.upd_of a ho
            exact ⟨x, c5 x hx, hx1⟩
          · exact ⟨(a, t.litVal?), c6 a t hmt hl, rfl⟩
      obtain ⟨m', hrun, hinv'⟩ := checkWaves_sound h0 hw hT prog lds gs acc1 acc' h2 hneed sc.mem hinv1
      refine ⟨m', ?_, hinv'⟩
      rw [serr, shalt, hhalt]
      simpa using hrun
    · simp at h

/-! ## 6. One dispatch -/

/-- A stage's promise: for any state `x` (satisfying `Inv`) whose wire buffer `proj x` the start's words
`rd` describe in `env`, an accepted table lists words inside the buffer, each meaning what the stage
leaves there (`proj (den x)`), and the stage leaves every other word as it was; `den` keeps `Inv`. -/
def Spec.Sound {σ : Type} (words : Nat) (proj : σ → Nat → Word) (Inv : σ → Prop) (s : Spec σ) : Prop :=
  ∀ (rd : Nat → TP) (env : UInt64 → UInt32) (x : σ) (T : Std.HashMap Nat TP),
    Inv x → (∀ j, (rd j).ev env = proj x j) → s.table rd = some T →
      Inv (s.den x) ∧ (∀ i t, T[i]? = some t → i < words ∧ t.ev env = proj (s.den x) i) ∧
        (∀ i, T[i]? = none → proj (s.den x) i = proj x i)

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

theorem checkStage_sound {σ : Type} {words : Nat} {lay : Memory} {known : Known} {proj : σ → Nat → Word}
    {Inv : σ → Prop} {s : Spec σ} (hs : s.Sound words proj Inv)
    {m0 : Memory} {x : σ} (h0 : StartOk words lay known m0 (proj x)) (hx : Inv x) (hw : words < 2 ^ 29)
    (prog : Program) (known' : Known) (n : Std.HashSet Residual)
    (hc : checkStage words lay s prog known = some (known', n)) (hn : ∀ r, n.contains r = true → r.Holds) :
    ∃ m', runWaves prog s.lds (List.range (groupsOf s.threads)) m0 = some m' ∧
      StartOk words lay known' m' (proj (s.den x)) ∧ Inv (s.den x) := by
  unfold checkStage at hc
  simp only [Option.bind_eq_some_iff] at hc
  obtain ⟨T, hT, acc, hw', hall⟩ := hc
  obtain ⟨hInv, hTv, hTn⟩ := hs _ (menv m0) x T hx (readWord_ev h0 hw) hT
  split at hall
  · rename_i hown
    simp only [Option.some.injEq, Prod.mk.injEq] at hall
    obtain ⟨rfl, rfl⟩ := hall
    have hinit : WInv words m0 T (proj (s.den x)) m0 ⟨{}, [], {}⟩ :=
      ⟨fun _ _ _ => rfl, fun a ha => by simp at ha, fun x hx => by simp at hx, fun a ha => by simp at ha⟩
    obtain ⟨m', hrun, hi⟩ := checkWaves_sound h0 hw (fun i t h => (hTv i t h).2) prog s.lds _ _ acc hw' hn m0 hinit
    refine ⟨m', hrun, ?_, hInv⟩
    have hstored : ∀ i sp, T[i]? = some sp →
        acc.stored.contains (dwLo i) = true ∧ acc.stored.contains (dwLo i + 1) = true := by
      intro i sp h
      unfold tableStored at hown
      have := List.all_eq_true.mp hown (i, sp) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h)
      simpa using this
    -- a dword of a word outside the table was never stored
    have hfree : ∀ j, j < words → T[j]? = none →
        acc.stored.contains (dwLo j) = false ∧ acc.stored.contains (dwLo j + 1) = false := by
      intro j hj hnone
      constructor <;>
      · rw [Bool.eq_false_iff]; intro hc
        obtain ⟨-, ⟨sp, hk⟩, -⟩ := hi.stored _ hc
        first
          | rw [off_dwLo j (by omega), Nat.mul_div_cancel_left _ (by decide)] at hk
          | rw [off_dwLo1 j (by omega), show (2 * j + 1) / 2 = j by omega] at hk
        rw [hnone] at hk; simp at hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      cases hf : T[j]? with
      | some sp =>
        obtain ⟨d0, d1⟩ := hstored j sp hf
        obtain ⟨-, -, v0⟩ := hi.stored _ d0
        obtain ⟨-, -, v1⟩ := hi.stored _ d1
        rw [off_dwLo j (by omega)] at v0
        rw [off_dwLo1 j (by omega)] at v1
        refine ⟨_, _, v0, v1, ?_⟩
        rw [show 2 * j % 2 = 0 by omega, show 2 * j / 2 = j by omega,
          show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
        exact dwHalf_join _
      | none =>
        obtain ⟨f0, f1⟩ := hfree j hj hf
        obtain ⟨lo, hi', e0, e1, e⟩ := h0.word j hj
        obtain ⟨i0, i1⟩ := inW_dwLo words j hw hj
        refine ⟨lo, hi', by rw [hi.free _ f0 (inW_lds words hw _ i0)]; exact e0,
          by rw [hi.free _ f1 (inW_lds words hw _ i1)]; exact e1, ?_⟩
        rw [hTn j hf]; exact e
    · intro j hj
      have hnone : T[j]? = none := by
        cases hf : T[j]? with
        | none => rfl
        | some t => have := (hTv j t hf).1; omega
      rw [hTn j hnone]; exact h0.past j hj
    · intro a ha hl
      have hc : acc.stored.contains a = false := by
        rw [Bool.eq_false_iff]; intro hc; have := (hi.stored a hc).1; rw [ha] at this; exact Bool.false_ne_true this
      rw [hi.free a hc hl]; exact h0.out a ha hl
    · intro a v hk ha
      rcases applyUpdates_get known a v _ hk with ⟨x, hx, hx1, hx2⟩ | ⟨hn', hk'⟩
      · rw [← hx1]; exact (hi.upd x hx).2 v hx2
      · have hc : acc.stored.contains a = false := by
          rw [Bool.eq_false_iff]; intro hc
          obtain ⟨x, hx, hx1⟩ := hi.upd_of a hc
          exact hn' x hx hx1
        rw [hi.free a hc (inW_lds words hw a ha)]; exact h0.known a v hk' ha
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

theorem checkProgram_mono {σ : Type} (words : Nat) (lay : Memory) :
    ∀ (ss : List (Spec σ)) (progs : List Program) (known : Known) (need fin : Std.HashSet Residual),
      checkProgram words lay ss progs known need = some fin → ∀ r, need.contains r = true → fin.contains r = true
  | [], [], _, need, fin, h => by simp only [checkProgram, Option.some.injEq] at h; subst h; exact fun _ h => h
  | s :: ss, prog :: progs, known, need, fin, h => by
    simp only [checkProgram, Option.bind_eq_some_iff] at h
    obtain ⟨⟨known', n⟩, _, h2⟩ := h
    intro r hr
    exact checkProgram_mono words lay ss progs known' _ fin h2 r ((fold_insert_contains n need r).mpr (Or.inl hr))
  | [], _ :: _, _, _, _, h => by simp [checkProgram] at h
  | _ :: _, [], _, _, _, h => by simp [checkProgram] at h

/-- Every dispatch: the model run of the certified programs succeeds and leaves the wire buffer as the
stages' meanings say, from any start state whose buffer the start memory holds. -/
theorem checkProgram_sound {σ : Type} {words : Nat} {lay : Memory} {proj : σ → Nat → Word} {Inv : σ → Prop}
    (hw : words < 2 ^ 29) :
    ∀ (ss : List (Spec σ)) (progs : List Program) (known : Known) (need fin : Std.HashSet Residual)
      (m : Memory) (x : σ),
      (∀ s ∈ ss, s.Sound words proj Inv) →
      checkProgram words lay ss progs known need = some fin → (∀ r, fin.contains r = true → r.Holds) →
      StartOk words lay known m (proj x) → Inv x →
      ∃ m' known', runDispatch (dispatchesOf ss progs) m = some m' ∧
        StartOk words lay known' m' (proj (ss.foldl (fun x s => s.den x) x)) ∧ Inv (ss.foldl (fun x s => s.den x) x)
  | [], [], known, _, _, m, x, _, _, _, h0, hx => ⟨m, known, rfl, h0, hx⟩
  | s :: ss, prog :: progs, known, need, fin, m, x, hss, h, hfin, h0, hx => by
    simp only [checkProgram, Option.bind_eq_some_iff] at h
    obtain ⟨⟨known', n⟩, h1, h2⟩ := h
    have hn : ∀ r, n.contains r = true → r.Holds := fun r hr =>
      hfin r (checkProgram_mono words lay ss progs known' _ fin h2 r ((fold_insert_contains n need r).mpr (Or.inr hr)))
    obtain ⟨m1, hrun, h1', hx1⟩ := checkStage_sound (hss s List.mem_cons_self) h0 hx hw prog known' n h1 hn
    obtain ⟨m', known'', hrest, hend, hxe⟩ := checkProgram_sound hw ss progs known' _ fin m1 _
      (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs')) h2 hfin h1' hx1
    refine ⟨m', known'', ?_, hend, hxe⟩
    simp only [dispatchesOf, List.map_cons, List.zip_cons_cons, runDispatch, hrun, Option.bind_some] at hrest ⊢
    exact hrest
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _ => by simp [checkProgram] at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _ => by simp [checkProgram] at h

/-! ## 8. A stage of a plan -/

theorem kvOf_sound {cs : Array Word} {ix : Array Nat} {rd : Nat → TP} {kc : List (Kernel × Array TP)}
    (hkc : ∀ k arr, (k, arr) ∈ kc → foldValues rd k = some arr) (k : Kernel) (e : Nat) (r : TP)
    (h : kvOf cs ix rd kc k e = some r) : pKernel cs ix rd k e = some r := by
  unfold kvOf at h
  split at h
  · rename_i k' arr hf
    have hm := List.mem_of_find?_eq_some hf
    have heq := List.find?_some hf
    simp only [beq_iff_eq] at heq
    subst heq
    exact foldValues_get cs ix rd _ arr (hkc _ _ hm) e r h
  · exact h

theorem foldCache_mem (rd : Nat → TP) (s : GpuStage) :
    ∀ k arr, (k, arr) ∈ foldCache rd s → foldValues rd k = some arr := by
  intro k arr h
  unfold foldCache at h
  rw [List.mem_filterMap] at h
  obtain ⟨k', _, h'⟩ := h
  cases hf : foldValues rd k' with
  | none => rw [hf] at h'; simp at h'
  | some arr' =>
    rw [hf] at h'; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'; exact hf

theorem gpuTableUpTo_spec (cs : Array Word) (ix : Array Nat) (stage : GpuStage) (rd : Nat → TP)
    (kc : List (Kernel × Array TP)) :
    ∀ n T, gpuTableUpTo cs ix stage rd kc n = some T → ∀ i,
      (∀ t, T[i]? = some t → i < n ∧ ∃ k, stage.kernels.find? (·.owns i) = some k ∧
        kvOf cs ix rd kc k (i - k.dstBase) = some t) ∧
      (T[i]? = none → i < n → stage.kernels.find? (·.owns i) = none)
  | 0, T, h => by
    simp only [gpuTableUpTo, Option.some.injEq] at h; subst h
    intro i; simp
  | n + 1, T, h => by
    simp only [gpuTableUpTo, Option.bind_eq_some_iff] at h
    obtain ⟨T0, h0, h1⟩ := h
    have ih := gpuTableUpTo_spec cs ix stage rd kc n T0 h0
    intro i
    split at h1
    · rename_i hf
      simp only [Option.some.injEq] at h1; subst h1
      refine ⟨fun t ht => ?_, fun hn hi => ?_⟩
      · obtain ⟨a, b⟩ := (ih i).1 t ht; exact ⟨by omega, b⟩
      · by_cases e : i = n
        · subst e; exact hf
        · exact (ih i).2 hn (by omega)
    · rename_i k hf
      simp only [Option.map_eq_some_iff] at h1
      obtain ⟨v, hv, rfl⟩ := h1
      rw [Std.HashMap.getElem?_insert]
      by_cases e : n = i
      · subst e
        simp only [beq_self_eq_true, ite_true, Option.some.injEq, reduceCtorEq, false_implies, and_true]
        intro t ht; subst ht; exact ⟨by omega, k, hf, hv⟩
      · simp only [beq_iff_eq, e, ite_false]
        refine ⟨fun t ht => ?_, fun hn hi => (ih i).2 hn (by omega)⟩
        obtain ⟨a, b⟩ := (ih i).1 t ht; exact ⟨by omega, b⟩

/-! ## 9. The memory the host starts from -/

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

theorem memOf_start (words : Nat) (consts : List Word) (tables : List Nat) (hw : words < 2 ^ 29) (flat : Nat → Word) :
    StartOk words (layoutMem words consts tables) {} (memOf words consts tables flat)
      (fun j => if j < words then flat j else 0) := by
  obtain ⟨h1, h2⟩ := memOf_prefix words consts tables flat words hw
  refine ⟨fun j hj => ⟨_, _, h1 j hj |>.1, h1 j hj |>.2, ?_⟩, fun j hj => ?_, fun a ha _ => ?_, fun a v hk _ => ?_⟩
  · simp only [hj, ite_true]; exact dwHalf_join _
  · simp only [show ¬ j < words by omega, ite_false]
  · apply h2
    intro i hi
    obtain ⟨i0, i1⟩ := inW_dwLo words i hw hi
    exact ⟨fun e => by rw [e, i0] at ha; exact Bool.false_ne_true ha.symm,
      fun e => by rw [e, i1] at ha; exact Bool.false_ne_true ha.symm⟩
  · simp at hk

end Obend.Hardware.Gpu.Rdna2
