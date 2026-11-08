/-
# Obend.Hardware.Gpu.Rdna2.Natural — the wave model commutes with every homomorphism of its domain

`Semantics` is written once over a domain `Dom V` and a memory `MemDom M V`. A `DomHom` maps one domain
to another preserving every operation and every known value; a `MemHom` maps memories preserving loads
and stores. `run_hom` says: running the model in the first domain and mapping the result is running it
in the second on the mapped state, provided the first run did not fail, or the homomorphism also
reflects unknown values and failed loads (then failures correspond too). It is proved once, for the one
definition of the model; the instances it is used at are the concrete model (`UInt32`), the symbolic
terms (`Tm`) and the pairs of a value and a term that evaluates to it (`Obend.Hardware.Gpu.Rdna2.Sym`),
which is how a symbolic run says something about every concrete run (the shape of LNSym's
`stepi`/`run` theorems, here derived from naturality rather than proved per instruction).
-/
module
public import Obend.Hardware.Gpu.Rdna2.Semantics
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2

structure DomHom (V₁ V₂ : Type) [Dom V₁] [Dom V₂] where
  f : V₁ → V₂
  lit : ∀ c, f (Dom.lit c) = Dom.lit c
  conc : ∀ x c, Dom.conc x = some c → Dom.conc (f x) = some c
  add : ∀ a b, f (Dom.add a b) = Dom.add (f a) (f b)
  sub : ∀ a b, f (Dom.sub a b) = Dom.sub (f a) (f b)
  mul : ∀ a b, f (Dom.mul a b) = Dom.mul (f a) (f b)
  mulHi : ∀ a b, f (Dom.mulHi a b) = Dom.mulHi (f a) (f b)
  band : ∀ a b, f (Dom.band a b) = Dom.band (f a) (f b)
  bor : ∀ a b, f (Dom.bor a b) = Dom.bor (f a) (f b)
  shl : ∀ a b, f (Dom.shl a b) = Dom.shl (f a) (f b)
  ite : ∀ c a b, f (Dom.ite c a b) = Dom.ite (f c) (f a) (f b)
  carry : ∀ a b, f (Dom.carry a b) = Dom.carry (f a) (f b)
  borrow : ∀ a b, f (Dom.borrow a b) = Dom.borrow (f a) (f b)
  addc : ∀ a b c, f (Dom.addc a b c) = Dom.addc (f a) (f b) (f c)
  carryc : ∀ a b c, f (Dom.carryc a b c) = Dom.carryc (f a) (f b) (f c)
  subc : ∀ a b c, f (Dom.subc a b c) = Dom.subc (f a) (f b) (f c)
  borrowc : ∀ a b c, f (Dom.borrowc a b c) = Dom.borrowc (f a) (f b) (f c)
  ule : ∀ a b, f (Dom.ule a b) = Dom.ule (f a) (f b)
  ugt : ∀ a b, f (Dom.ugt a b) = Dom.ugt (f a) (f b)
  ult64 : ∀ a0 a1 b0 b1, f (Dom.ult64 a0 a1 b0 b1) = Dom.ult64 (f a0) (f a1) (f b0) (f b1)
  ne64 : ∀ a0 a1 b0 b1, f (Dom.ne64 a0 a1 b0 b1) = Dom.ne64 (f a0) (f a1) (f b0) (f b1)
  bit : ∀ x k, f (Dom.bit x k) = Dom.bit (f x) k
  pack : ∀ l, f (Dom.pack l) = Dom.pack (l.map f)
  shl64 : ∀ c a b, Prod.map f f (Dom.shl64 c a b) = Dom.shl64 (f c) (f a) (f b)
  lshr64 : ∀ c a b, Prod.map f f (Dom.lshr64 c a b) = Dom.lshr64 (f c) (f a) (f b)
  nez64 : ∀ a b, f (Dom.nez64 a b) = Dom.nez64 (f a) (f b)

structure MemHom {V₁ V₂ : Type} (M₁ M₂ : Type) [Dom V₁] [Dom V₂] [MemDom M₁ V₁] [MemDom M₂ V₂]
    (h : DomHom V₁ V₂) where
  g : M₁ → M₂
  load : ∀ m a v, MemDom.load m a = some v → MemDom.load (g m) a = some (h.f v)
  store : ∀ m a v, g (MemDom.store m a v) = MemDom.store (g m) a (h.f v)

section
variable {V₁ V₂ M₁ M₂ : Type} [Dom V₁] [Dom V₂] [MemDom M₁ V₁] [MemDom M₂ V₂]
variable (h : DomHom V₁ V₂) (hm : MemHom M₁ M₂ h)

/-- The homomorphism also maps unknown values to unknown values and missing words to missing words. -/
def Reflects : Prop :=
  (∀ x : V₁, Dom.conc x = none → Dom.conc (h.f x) = none) ∧
    (∀ (m : M₁) (a : UInt64), (MemDom.load m a : Option V₁) = none → (MemDom.load (hm.g m) a : Option V₂) = none)

def mapW (s : GWave V₁ M₁) : GWave V₂ M₂ :=
  { sgpr := s.sgpr.map h.f, exec := s.exec, scc := h.f s.scc, m0 := h.f s.m0, vgpr := s.vgpr.map h.f,
    pc := s.pc, mem := hm.g s.mem, halted := s.halted, err := s.err, ldsBase := s.ldsBase,
    ldsDwords := s.ldsDwords }

/-! ## 1. Options related by a map -/

/-- `o₂` is `o₁` mapped by `φ` whenever `o₁` answers, and also when it does not if `R` holds. -/
def ORel {α β : Type} (R : Prop) (φ : α → β) (o₁ : Option α) (o₂ : Option β) : Prop :=
  (∀ v, o₁ = some v → o₂ = some (φ v)) ∧ (R → o₁ = none → o₂ = none)

theorem ORel.of_map {α β : Type} (R : Prop) (φ : α → β) (o : Option α) : ORel R φ o (o.map φ) :=
  ⟨fun v hv => by simp [hv], fun _ hn => by simp [hn]⟩

theorem ORel.some' {α β : Type} (R : Prop) (φ : α → β) (v : α) : ORel R φ (some v) (some (φ v)) :=
  ⟨fun w hw => by simp at hw; subst hw; rfl, fun _ hn => by simp at hn⟩

theorem ORel.none' {α β : Type} (R : Prop) (φ : α → β) : ORel R φ (none : Option α) (none : Option β) :=
  ⟨fun _ hw => by simp at hw, fun _ _ => rfl⟩

theorem ORel.bind {α β γ δ : Type} {R : Prop} {φ : α → β} {ψ : γ → δ} {o₁ : Option α} {o₂ : Option β}
    {g₁ : α → Option γ} {g₂ : β → Option δ} (ho : ORel R φ o₁ o₂) (hg : ∀ v, ORel R ψ (g₁ v) (g₂ (φ v))) :
    ORel R ψ (o₁.bind g₁) (o₂.bind g₂) := by
  constructor
  · intro w hw
    cases h1 : o₁ with
    | none => simp [h1] at hw
    | some v => simp [h1] at hw; rw [ho.1 v h1]; simpa using (hg v).1 w hw
  · intro hR hn
    cases h1 : o₁ with
    | none => rw [ho.2 hR h1]; rfl
    | some v => simp [h1] at hn; rw [ho.1 v h1]; simpa using (hg v).2 hR hn

theorem ORel.map {α β γ δ : Type} {R : Prop} {φ : α → β} {ψ : γ → δ} {o₁ : Option α} {o₂ : Option β}
    {g₁ : α → γ} {g₂ : β → δ} (ho : ORel R φ o₁ o₂) (hg : ∀ v, g₂ (φ v) = ψ (g₁ v)) :
    ORel R ψ (o₁.map g₁) (o₂.map g₂) := by
  constructor
  · intro w hw
    cases h1 : o₁ with
    | none => simp [h1] at hw
    | some v => simp [h1] at hw; rw [ho.1 v h1]; simp [← hw, hg]
  · intro hR hn
    cases h1 : o₁ with
    | none => rw [ho.2 hR h1]; rfl
    | some v => simp [h1] at hn

theorem ORel.mapM {α γ δ : Type} {R : Prop} {ψ : γ → δ} (l : List α)
    {g₁ : α → Option γ} {g₂ : α → Option δ} (hg : ∀ x, ORel R ψ (g₁ x) (g₂ x)) :
    ORel R (List.map ψ) (l.mapM g₁) (l.mapM g₂) := by
  induction l with
  | nil => simpa using ORel.some' R (List.map ψ) []
  | cons x xs ih =>
    simp only [List.mapM_cons]
    refine ORel.bind (hg x) fun v => ?_
    refine ORel.bind ih fun vs => ?_
    simpa using ORel.some' R (List.map ψ) (v :: vs)

theorem ORel.ite {α β : Type} {R : Prop} {φ : α → β} (c : Prop) [Decidable c] {o₁ o₁' : Option α} {o₂ o₂' : Option β}
    (h1 : ORel R φ o₁ o₂) (h2 : ORel R φ o₁' o₂') : ORel R φ (if c then o₁ else o₁') (if c then o₂ else o₂') := by
  split <;> assumption

/-! ## 2. The state map commutes with reading and writing registers -/

theorem f_getD (a : Array V₁) (n : Nat) : h.f (a.getD n (Dom.lit 0)) = (a.map h.f).getD n (Dom.lit 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[n]? <;> simp [h.lit]

theorem readSgpr_hom (s : GWave V₁ M₁) (n : Nat) : h.f (readSgpr s n) = readSgpr (mapW h hm s) n := by
  unfold readSgpr mapW; exact f_getD h _ _

theorem readVgpr_hom (s : GWave V₁ M₁) (r l : Nat) : h.f (readVgpr s r l) = readVgpr (mapW h hm s) r l := by
  unfold readVgpr mapW; exact f_getD h _ _

theorem writeSgpr_hom (s : GWave V₁ M₁) (n : Nat) (v : V₁) :
    mapW h hm (writeSgpr s n v) = writeSgpr (mapW h hm s) n (h.f v) := by
  unfold writeSgpr; split <;> simp [mapW, Array.set!, Array.map_setIfInBounds]

theorem writeVgpr_hom (s : GWave V₁ M₁) (r l : Nat) (v : V₁) :
    mapW h hm (writeVgpr s r l v) = writeVgpr (mapW h hm s) r l (h.f v) := by
  unfold writeVgpr; split <;> simp [mapW, Array.set!, Array.map_setIfInBounds]

@[simp] theorem mapW_exec (s : GWave V₁ M₁) : (mapW h hm s).exec = s.exec := rfl
@[simp] theorem mapW_err (s : GWave V₁ M₁) : (mapW h hm s).err = s.err := rfl
@[simp] theorem mapW_pc (s : GWave V₁ M₁) : (mapW h hm s).pc = s.pc := rfl
@[simp] theorem mapW_halted (s : GWave V₁ M₁) : (mapW h hm s).halted = s.halted := rfl

theorem execBit_hom (s : GWave V₁ M₁) (l : Nat) : execBit (mapW h hm s) l = execBit s l := rfl
theorem activeLanes_hom (s : GWave V₁ M₁) : activeLanes (mapW h hm s) = activeLanes s := rfl

theorem fail_hom (s : GWave V₁ M₁) (msg : String) : mapW h hm (s.fail msg) = (mapW h hm s).fail msg := by
  unfold GWave.fail; split <;> simp_all [mapW]

omit [Dom V₁] [MemDom M₁ V₁] in
theorem fail_err (s : GWave V₁ M₁) (msg : String) : (s.fail msg).err ≠ none := by
  unfold GWave.fail; split
  · rename_i hs; intro he; simp [he] at hs
  · simp

/-- The workhorse: continue with the value, or fail. -/
theorem withSome_hom {α β : Type} {R : Prop} {φ : α → β} {o₁ : Option α} {o₂ : Option β} (hr : ORel R φ o₁ o₂)
    (s : GWave V₁ M₁) (msg : String) (k₁ : α → GWave V₁ M₁) (k₂ : β → GWave V₂ M₂)
    (hk : ∀ v, (k₁ v).err = none ∨ R → k₂ (φ v) = mapW h hm (k₁ v))
    (hres : (s.withSome o₁ msg k₁).err = none ∨ R) :
    (mapW h hm s).withSome o₂ msg k₂ = mapW h hm (s.withSome o₁ msg k₁) := by
  unfold GWave.withSome at hres ⊢
  cases h1 : o₁ with
  | some v => rw [hr.1 v h1]; simp only [h1] at hres; exact hk v hres
  | none =>
    simp only [h1] at hres
    rcases hres with hres | hR
    · exact absurd hres (fail_err s msg)
    · rw [hr.2 hR h1]; exact (fail_hom h hm s msg).symm

theorem ORel.refl {α : Type} (R : Prop) (o : Option α) : ORel R id o o :=
  ⟨fun v hv => by simp [hv], fun _ hn => hn⟩

/-! ## 3. Operand sources -/

theorem conc_rel (R : Prop) (hR : R → Reflects h hm) (x : V₁) : ORel R id (Dom.conc x) (Dom.conc (h.f x)) :=
  ⟨fun c hc => by simpa using h.conc x c hc, fun hr hn => (hR hr).1 x hn⟩

theorem lit_map (o : Option UInt32) : (o.map Dom.lit).map h.f = o.map Dom.lit := by
  cases o <;> simp [h.lit]

theorem scalarSource_rel (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (lit : Option UInt32) :
    ORel R h.f (scalarSource s code lit) (scalarSource (mapW h hm s) code lit) := by
  unfold scalarSource
  cases srcKind code with
  | sgpr n => dsimp only; rw [← readSgpr_hom h hm]; exact ORel.some' R h.f _
  | m0 => dsimp only; exact ORel.some' R h.f _
  | lit v => dsimp only; rw [← h.lit]; exact ORel.some' R h.f _
  | execLo => dsimp only; rw [mapW_exec, ← h.lit]; exact ORel.some' R h.f _
  | execHi => dsimp only; rw [mapW_exec, ← h.lit]; exact ORel.some' R h.f _
  | vccz =>
    dsimp only
    rw [← readSgpr_hom h hm, ← readSgpr_hom h hm]
    refine ORel.bind (conc_rel h hm R hR _) fun lo => ?_
    refine ORel.map (conc_rel h hm R hR _) fun hi => ?_
    simp [h.lit]
  | execz => dsimp only; rw [mapW_exec, ← h.lit]; exact ORel.some' R h.f _
  | scc => dsimp only; exact ORel.some' R h.f _
  | literal => dsimp only; rw [← lit_map h]; exact ORel.of_map R h.f _
  | none => dsimp only; exact ORel.none' R h.f

theorem vectorSource_rel (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (lit : Option UInt32) (lane : Nat) :
    ORel R h.f (vectorSource s code lit lane) (vectorSource (mapW h hm s) code lit lane) := by
  unfold vectorSource; split
  · rw [← readVgpr_hom h hm]; exact ORel.some' R h.f _
  · exact scalarSource_rel h hm R hR s code lit

def pmap (p : V₁ × V₁) : V₂ × V₂ := (h.f p.1, h.f p.2)

theorem resolve64_rel (R : Prop) (s : GWave V₁ M₁) (k : Src64Kind) (lane : Nat) :
    ORel R (pmap h) (resolve64 s k lane) (resolve64 (mapW h hm s) k lane) := by
  cases k with
  | sgprPair n => simp only [resolve64, ← readSgpr_hom h hm]; exact ORel.some' R (pmap h) _
  | exec => simp only [resolve64, mapW_exec, ← h.lit]; exact ORel.some' R (pmap h) _
  | lit lo hi => simp only [resolve64, ← h.lit]; exact ORel.some' R (pmap h) _
  | vgprPair r => simp only [resolve64, ← readVgpr_hom h hm]; exact ORel.some' R (pmap h) _
  | none => exact ORel.none' R (pmap h)

theorem source64_rel (R : Prop) (s : GWave V₁ M₁) (code lane : Nat) :
    ORel R (pmap h) (source64 s code lane) (source64 (mapW h hm s) code lane) := resolve64_rel h hm R s _ lane

theorem maskSource_rel (R : Prop) (s : GWave V₁ M₁) (code : Nat) :
    ORel R (pmap h) (maskSource s code) (maskSource (mapW h hm s) code) := resolve64_rel h hm R s _ 0

/-! ## 4. Writes -/

theorem writeExec_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (lo hi : V₁)
    (hres : (writeExec s lo hi).err = none ∨ R) :
    writeExec (mapW h hm s) (h.f lo) (h.f hi) = mapW h hm (writeExec s lo hi) := by
  unfold writeExec at hres ⊢
  refine withSome_hom h hm (φ := id) ?_ s _ (fun e => { s with exec := e }) (fun e => { mapW h hm s with exec := e })
    (fun e _ => rfl) hres
  refine ORel.bind (conc_rel h hm R hR lo) fun l => ?_
  exact ORel.map (conc_rel h hm R hR hi) fun _ => rfl

theorem writeScalarDst_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (v : V₁)
    (hres : (writeScalarDst s code v).err = none ∨ R) :
    writeScalarDst (mapW h hm s) code (h.f v) = mapW h hm (writeScalarDst s code v) := by
  unfold writeScalarDst at hres ⊢
  cases hk : dstKind code with
  | sgpr n => simp only [hk] at hres ⊢; exact (writeSgpr_hom h hm s n v).symm
  | m0 => simp only; rfl
  | null => simp only
  | execLo =>
    simp only [hk] at hres ⊢
    have := writeExec_hom h hm R hR s v (Dom.lit (s.exec >>> 32).toUInt32) hres
    rw [h.lit] at this; exact this
  | execHi =>
    simp only [hk] at hres ⊢
    have := writeExec_hom h hm R hR s (Dom.lit s.exec.toUInt32) v hres
    rw [h.lit] at this; exact this
  | none => simp only; exact (fail_hom h hm s _).symm

theorem writeScalarDst64_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (v : V₁ × V₁)
    (hres : (writeScalarDst64 s code v).err = none ∨ R) :
    writeScalarDst64 (mapW h hm s) code (pmap h v) = mapW h hm (writeScalarDst64 s code v) := by
  unfold writeScalarDst64 at hres ⊢
  split
  · rename_i n hk; simp only [hk] at hres
    simp [pmap, writeSgpr_hom]
  · simp only
  · rename_i hk; simp only [hk] at hres; exact writeExec_hom h hm R hR s v.1 v.2 hres
  · exact (fail_hom h hm s _).symm

/-! ## 5. Lanes -/

theorem laneSources_rel (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (n lane : Nat) :
    ORel R (List.map h.f) (laneSources i s n lane) (laneSources i (mapW h hm s) n lane) :=
  ORel.mapM _ fun _ => vectorSource_rel h hm R hR s _ _ lane

theorem writeLanes_hom (s : GWave V₁ M₁) (dst : Nat) (rs : List (Nat × V₁)) :
    writeLanes (mapW h hm s) dst (rs.map fun p => (p.1, h.f p.2)) = mapW h hm (writeLanes s dst rs) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp only [writeLanes, List.map_cons, List.foldl_cons] at ih ⊢; rw [← writeVgpr_hom, ih]

theorem f_src (src : List V₁) (k : Nat) : h.f (src.getD k (Dom.lit 0)) = (src.map h.f).getD k (Dom.lit 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases src[k]? <;> simp [h.lit]

theorem lshrV_hom (x k : V₁) : h.f (lshrV x k) = lshrV (h.f x) (h.f k) := by
  unfold lshrV
  rw [show h.f (Dom.lshr64 k x (Dom.lit 0)).1 = (Prod.map h.f h.f (Dom.lshr64 k x (Dom.lit 0))).1 from rfl, h.lshr64, h.lit]

theorem sdwaSelV_hom (x : V₁) (sel : Nat) : h.f (sdwaSelV x sel) = sdwaSelV (h.f x) sel := by
  unfold sdwaSelV
  simp only [apply_ite h.f]
  by_cases a : sel < 4
  · rw [if_pos a, if_pos a, h.band, lshrV_hom, h.lit, h.lit]
  · rw [if_neg a, if_neg a]
    by_cases b : (sel == 4) = true
    · rw [if_pos b, if_pos b, h.band, h.lit]
    · rw [if_neg b, if_neg b]
      by_cases c : (sel == 5) = true
      · rw [if_pos c, if_pos c, lshrV_hom, h.lit]
      · rw [if_neg c, if_neg c]

theorem sdwaDst_hom (r : V₁) (sel : Nat) : h.f (sdwaDst r sel) = sdwaDst (h.f r) sel := by
  unfold sdwaDst
  simp only [apply_ite h.f]
  by_cases a : sel < 4
  · rw [if_pos a, if_pos a, h.shl, h.band, h.lit, h.lit]
  · rw [if_neg a, if_neg a]
    by_cases b : (sel == 4) = true
    · rw [if_pos b, if_pos b, h.band, h.lit]
    · rw [if_neg b, if_neg b]
      by_cases c : (sel == 5) = true
      · rw [if_pos c, if_pos c, h.shl, h.band, h.lit, h.lit]
      · rw [if_neg c, if_neg c]

theorem sdwaLift_hom (i : Inst) (f₁ : List V₁ → Nat → V₁) (f₂ : List V₂ → Nat → V₂)
    (hf : ∀ src lane, h.f (f₁ src lane) = f₂ (src.map h.f) lane) (src : List V₁) (lane : Nat) :
    h.f (sdwaLift i f₁ src lane) = sdwaLift i f₂ (src.map h.f) lane := by
  unfold sdwaLift
  rw [sdwaDst_hom, hf]
  simp only [List.map, sdwaSelV_hom, f_src]

theorem valuLanes_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (n : Nat)
    (f₁ : List V₁ → Nat → V₁) (f₂ : List V₂ → Nat → V₂) (hf : ∀ src lane, h.f (f₁ src lane) = f₂ (src.map h.f) lane)
    (hres : (valuLanes i s n f₁).err = none ∨ R) :
    valuLanes i (mapW h hm s) n f₂ = mapW h hm (valuLanes i s n f₁) := by
  unfold valuLanes at hres ⊢
  by_cases hc : (isSdwa i && !sdwaClear i) = true
  · rw [if_pos hc, if_pos hc]; exact (fail_hom h hm s _).symm
  rw [if_neg hc] at hres; rw [if_neg hc, if_neg hc]
  dsimp only at hres ⊢
  have hg : ∀ src lane, h.f ((if isSdwa i = true then sdwaLift i f₁ else f₁) src lane) =
      (if isSdwa i = true then sdwaLift i f₂ else f₂) (src.map h.f) lane := by
    intro src lane
    by_cases hs : isSdwa i = true
    · rw [if_pos hs, if_pos hs]; exact sdwaLift_hom h i f₁ f₂ hf src lane
    · rw [if_neg hs, if_neg hs]; exact hf src lane
  rw [activeLanes_hom]
  refine withSome_hom h hm (φ := List.map fun p => (p.1, h.f p.2)) ?_ s _ _ _ (fun rs _ => writeLanes_hom h hm s _ rs) hres
  exact ORel.mapM _ fun lane => ORel.map (laneSources_rel h hm R hR i s n lane) fun src => by simp only [hg]

theorem maskOf_hom (s : GWave V₁ M₁) (bits : Nat → V₁) :
    pmap h (maskOf s bits) = maskOf (mapW h hm s) (fun l => h.f (bits l)) := by
  have key : ∀ l, h.f (if execBit s l = true then bits l else Dom.lit 0) =
      (if execBit (mapW h hm s) l = true then h.f (bits l) else Dom.lit 0) := by
    intro l; by_cases hb : execBit s l = true
    · rw [ite_eq_left hb, ite_eq_left (show execBit (mapW h hm s) l = true from hb)]
    · rw [ite_eq_right hb, ite_eq_right (show ¬ execBit (mapW h hm s) l = true from hb), h.lit]
  simp only [maskOf, pmap, h.pack, List.map_map, Prod.mk.injEq]
  constructor <;> congr 1 <;> apply List.map_congr_left <;> intro l _ <;> exact key _

theorem find_map_fst {α β : Type} (rs : List (Nat × α)) (g : α → β) (lane : Nat) :
    (rs.map fun p => (p.1, g p.2)).find? (·.1 == lane) = (rs.find? (·.1 == lane)).map fun p => (p.1, g p.2) := by
  rw [List.find?_map]; rfl

theorem pick_hom {α β : Type} (rs : List (Nat × α)) (sel : α → V₁) (g : α → β) (sel' : β → V₂)
    (hsel : ∀ a, sel' (g a) = h.f (sel a)) (lane : Nat) :
    (((rs.map fun p => (p.1, g p.2)).find? (·.1 == lane)).map fun p => sel' p.2).getD (Dom.lit 0) =
      h.f (((rs.find? (·.1 == lane)).map fun p => sel p.2).getD (Dom.lit 0)) := by
  induction rs with
  | nil => simp [h.lit]
  | cons p ps ih => simp only [List.map_cons, List.find?_cons]; split <;> simp_all

theorem valuLanesCarry_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁)
    (f₁ : V₁ → V₁ → Nat → V₁ × V₁) (f₂ : V₂ → V₂ → Nat → V₂ × V₂) (hf : ∀ a b lane, pmap h (f₁ a b lane) = f₂ (h.f a) (h.f b) lane)
    (hres : (valuLanesCarry i s f₁).err = none ∨ R) :
    valuLanesCarry i (mapW h hm s) f₂ = mapW h hm (valuLanesCarry i s f₁) := by
  unfold valuLanesCarry at hres ⊢
  by_cases hc : isSdwa i = true
  · rw [if_pos hc, if_pos hc]; exact (fail_hom h hm s _).symm
  rw [if_neg hc] at hres; rw [if_neg hc, if_neg hc]
  rw [activeLanes_hom]
  refine withSome_hom h hm (φ := List.map fun p => (p.1, pmap h p.2)) ?_ s _ _ _ ?_ hres
  · exact ORel.mapM _ fun lane => ORel.map (laneSources_rel h hm R hR i s 2 lane) fun src => by
      rw [← f_src h src 0, ← f_src h src 1, ← hf]
  · intro rs hrs
    have hw : (rs.map fun p => (p.1, pmap h p.2)).map (fun x => (x.1, x.2.1)) =
        (rs.map fun x => (x.1, x.2.1)).map fun p => (p.1, h.f p.2) := by
      simp [List.map_map, pmap]
    have hmask : maskOf (mapW h hm s) (fun lane =>
          (((rs.map fun p => (p.1, pmap h p.2)).find? (·.1 == lane)).map fun p => p.2.2).getD (Dom.lit 0)) =
        pmap h (maskOf s fun lane => ((rs.find? (·.1 == lane)).map fun p => p.2.2).getD (Dom.lit 0)) := by
      rw [maskOf_hom h hm]; congr 1; funext lane
      exact pick_hom h rs (fun p => p.2) (pmap h) (fun p => p.2) (fun a => rfl) lane
    simp only [] at hrs ⊢
    rw [show (List.map (fun x => match x with | (l, r) => (l, r.1)) (List.map (fun p => (p.1, pmap h p.2)) rs)) =
        (rs.map fun x => (x.1, x.2.1)).map fun p => (p.1, h.f p.2) from by simp [List.map_map, pmap]]
    rw [writeLanes_hom, hmask]
    refine writeScalarDst64_hom h hm R hR _ _ _ ?_
    simpa using hrs

theorem valuCompare_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (wide : Bool)
    (t₁ : List V₁ → V₁) (t₂ : List V₂ → V₂) (ht : ∀ src, h.f (t₁ src) = t₂ (src.map h.f))
    (hres : (valuCompare i s wide t₁).err = none ∨ R) :
    valuCompare i (mapW h hm s) wide t₂ = mapW h hm (valuCompare i s wide t₁) := by
  unfold valuCompare at hres ⊢
  by_cases hc : isSdwa i = true
  · rw [if_pos hc, if_pos hc]; exact (fail_hom h hm s _).symm
  rw [if_neg hc] at hres; rw [if_neg hc, if_neg hc]
  rw [activeLanes_hom]
  refine withSome_hom h hm (φ := List.map fun p => (p.1, h.f p.2)) ?_ s _ _ _ ?_ hres
  · refine ORel.mapM _ fun lane => ?_
    refine ORel.map (φ := List.map h.f) ?_ fun src => by simp [ht]
    split
    · refine ORel.bind (source64_rel h hm R s _ lane) fun a => ?_
      exact ORel.map (source64_rel h hm R s _ lane) fun b => by simp [pmap]
    · exact laneSources_rel h hm R hR i s 2 lane
  · intro rs hrs
    have hmask : maskOf (mapW h hm s) (fun lane =>
          (((rs.map fun p => (p.1, h.f p.2)).find? (·.1 == lane)).map fun p => p.2).getD (Dom.lit 0)) =
        pmap h (maskOf s fun lane => ((rs.find? (·.1 == lane)).map fun p => p.2).getD (Dom.lit 0)) := by
      rw [maskOf_hom h hm]; congr 1; funext lane
      exact pick_hom h rs (fun p => p) h.f (fun p => p) (fun a => rfl) lane
    simp only [] at hrs ⊢
    rw [hmask]
    split
    · exact writeExec_hom h hm R hR s _ _ (by simpa [*] using hrs)
    · exact writeScalarDst64_hom h hm R hR s _ _ (by simpa [*] using hrs)

theorem valuShift64_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁)
    (f₁ : V₁ → V₁ → V₁ → V₁ × V₁) (f₂ : V₂ → V₂ → V₂ → V₂ × V₂)
    (hf : ∀ c a b, pmap h (f₁ c a b) = f₂ (h.f c) (h.f a) (h.f b))
    (hres : (valuShift64 i s f₁).err = none ∨ R) :
    valuShift64 i (mapW h hm s) f₂ = mapW h hm (valuShift64 i s f₁) := by
  unfold valuShift64 at hres ⊢
  rw [activeLanes_hom]
  refine withSome_hom h hm (φ := List.map fun p => (p.1, pmap h p.2)) ?_ s _ _ _ ?_ hres
  · refine ORel.mapM _ fun lane => ?_
    refine ORel.bind (vectorSource_rel h hm R hR s _ _ lane) fun c => ?_
    exact ORel.map (source64_rel h hm R s _ lane) fun p => by simp [← hf, pmap]
  · intro rs _
    simp only []
    rw [show (List.map (fun x => match x with | (l, r) => (l, r.1)) (List.map (fun p => (p.1, pmap h p.2)) rs)) =
        (rs.map fun x => (x.1, x.2.1)).map fun p => (p.1, h.f p.2) from by simp [List.map_map, pmap]]
    rw [show (List.map (fun x => match x with | (l, r) => (l, r.2)) (List.map (fun p => (p.1, pmap h p.2)) rs)) =
        (rs.map fun x => (x.1, x.2.2)).map fun p => (p.1, h.f p.2) from by simp [List.map_map, pmap]]
    rw [writeLanes_hom, writeLanes_hom]

/-! ## 6. Memory -/

theorem readResource_rel (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (n : Nat) :
    ORel R id (readResource s n) (readResource (mapW h hm s) n) := by
  unfold readResource
  simp only [← readSgpr_hom h hm]
  refine ORel.bind (conc_rel h hm R hR _) fun _ => ?_
  refine ORel.bind (conc_rel h hm R hR _) fun _ => ?_
  refine ORel.bind (conc_rel h hm R hR _) fun _ => ?_
  exact ORel.map (conc_rel h hm R hR _) fun _ => rfl

theorem load_rel (R : Prop) (hR : R → Reflects h hm) (m : M₁) (a : UInt64) :
    ORel R h.f (MemDom.load m a : Option V₁) (MemDom.load (hm.g m) a : Option V₂) :=
  ⟨fun v hv => hm.load m a v hv, fun hr hn => (hR hr).2 m a hn⟩

theorem mubufLaneAddrs_rel (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (r : BufferResource)
    (soff : UInt32) (n : Nat) :
    ORel R id (mubufLaneAddrs i s r soff n) (mubufLaneAddrs i (mapW h hm s) r soff n) := by
  unfold mubufLaneAddrs
  rw [activeLanes_hom]
  have := ORel.mapM (R := R) (ψ := id) (activeLanes s)
    (g₁ := fun lane => if i.field "OFFEN" == 1 then
      (Dom.conc (readVgpr s (i.field "VADDR") lane)).map fun v => (lane, mubufAddrs i r soff v.toNat n)
      else some (lane, mubufAddrs i r soff 0 n))
    (g₂ := fun lane => if i.field "OFFEN" == 1 then
      (Dom.conc (readVgpr (mapW h hm s) (i.field "VADDR") lane)).map fun v => (lane, mubufAddrs i r soff v.toNat n)
      else some (lane, mubufAddrs i r soff 0 n))
    (fun lane => by
      split
      · rw [← readVgpr_hom h hm]; exact ORel.map (conc_rel h hm R hR _) fun _ => rfl
      · exact ORel.some' R id _)
  simpa using this

theorem storeAll_hom (s : GWave V₁ M₁) (ws : List (UInt64 × V₁)) :
    storeAll (mapW h hm s) (ws.map fun p => (p.1, h.f p.2)) = mapW h hm (storeAll s ws) := by
  simp only [storeAll, mapW]
  congr 1
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← hm.store]
    exact ih { s with mem := MemDom.store s.mem w.1 w.2 }

theorem writeRegs_hom (s : GWave V₁ M₁) (ws : List (Nat × Nat × V₁)) :
    writeRegs (mapW h hm s) (ws.map fun p => (p.1, p.2.1, h.f p.2.2)) = mapW h hm (writeRegs s ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => simp only [writeRegs, List.map_cons, List.foldl_cons] at ih ⊢; rw [← writeVgpr_hom, ih]

theorem writeSgprs_hom (s : GWave V₁ M₁) (ws : List (Nat × V₁)) :
    writeSgprs (mapW h hm s) (ws.map fun p => (p.1, h.f p.2)) = mapW h hm (writeSgprs s ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => simp only [writeSgprs, List.map_cons, List.foldl_cons] at ih ⊢; rw [← writeSgpr_hom, ih]

theorem soff_rel (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) :
    ORel R id ((scalarSource s code none).bind Dom.conc) ((scalarSource (mapW h hm s) code none).bind Dom.conc) :=
  ORel.bind (scalarSource_rel h hm R hR s code none) fun v => conc_rel h hm R hR v

theorem execMubuf_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (isStore : Bool)
    (hres : (execMubuf i s isStore).err = none ∨ R) :
    execMubuf i (mapW h hm s) isStore = mapW h hm (execMubuf i s isStore) := by
  unfold execMubuf at hres ⊢
  refine withSome_hom h hm (ORel.refl R _) s _ _ _ ?_ hres
  intro vdata hv
  refine withSome_hom h hm (readResource_rel h hm R hR s _) s _ _ _ ?_ hv
  intro r hr
  simp only [id] at hr ⊢
  split
  · exact (fail_hom h hm s _).symm
  refine withSome_hom h hm (soff_rel h hm R hR s _) s _ _ _ ?_ (by simpa [*] using hr)
  intro soff hsoff
  refine withSome_hom h hm (mubufLaneAddrs_rel h hm R hR i s r soff _) s _ _ _ ?_ hsoff
  intro las hlas
  simp only [id] at hlas ⊢
  split
  · rw [← storeAll_hom h hm]
    congr 1
    simp only [List.map_flatMap, List.map_filterMap]
    congr 1; funext p
    congr 1; funext q
    cases q.1 <;> simp [readVgpr_hom h hm]
  · refine withSome_hom h hm (φ := List.map fun p => (p.1, p.2.1, h.f p.2.2)) ?_ s _ _ _
      (fun ws _ => writeRegs_hom h hm s ws) (by simpa [*] using hlas)
    refine ORel.mapM _ fun ⟨reg, lane, a⟩ => ?_
    cases a with
    | none => simp only []; rw [← h.lit]; exact ORel.some' R _ _
    | some a => exact ORel.map (load_rel h hm R hR s.mem a) fun v => rfl

theorem execSmem_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁)
    (hres : (execSmem i s).err = none ∨ R) :
    execSmem i (mapW h hm s) = mapW h hm (execSmem i s) := by
  unfold execSmem at hres ⊢
  refine withSome_hom h hm (ORel.refl R _) s _ _ _ ?_ hres
  intro sdata hv
  simp only [id] at hv ⊢
  split
  · exact (fail_hom h hm s _).symm
  rename_i hal
  simp only [hal] at hv
  refine withSome_hom h hm (φ := id) ?_ s _ _ _ ?_ (by simpa using hv)
  · split
    · exact ORel.refl R _
    · exact ORel.map (soff_rel h hm R hR s _) fun _ => rfl
  intro soff hsoff
  simp only [id] at hsoff ⊢
  split
  · refine withSome_hom h hm (readResource_rel h hm R hR s _) s _ _ _ ?_ (by simpa [*] using hsoff)
    intro r hr
    simp only [id] at hr ⊢
    split
    · exact (fail_hom h hm s _).symm
    split
    · exact (fail_hom h hm s _).symm
    refine withSome_hom h hm (φ := List.map fun p => (p.1, h.f p.2)) ?_ s _ _ _
      (fun ws _ => writeSgprs_hom h hm s ws) (by simpa [*] using hr)
    refine ORel.mapM _ fun k => ?_
    split
    · exact ORel.map (load_rel h hm R hR s.mem _) fun v => rfl
    · rw [← h.lit]; exact ORel.some' R _ _
  · refine withSome_hom h hm (φ := id) ?_ s _ _ _ ?_ (by simpa [*] using hsoff)
    · simp only [← readSgpr_hom h hm]
      refine ORel.bind (conc_rel h hm R hR _) fun _ => ?_
      exact ORel.map (conc_rel h hm R hR _) fun _ => rfl
    intro base hb
    refine withSome_hom h hm (φ := List.map fun p => (p.1, h.f p.2)) ?_ s _ _ _
      (fun ws _ => writeSgprs_hom h hm s ws) hb
    exact ORel.mapM _ fun k => ORel.map (load_rel h hm R hR s.mem _) fun v => rfl

/-! ## 7. One instruction, one step, a run -/

theorem ssrc_rel (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (k : Nat) :
    ORel R h.f (ssrc i s k) (ssrc i (mapW h hm s) k) := scalarSource_rel h hm R hR s _ _

theorem ssrc64_rel (R : Prop) (i : Inst) (s : GWave V₁ M₁) (k : Nat) :
    ORel R (pmap h) (ssrc64 i s k) (ssrc64 i (mapW h hm s) k) := by
  unfold ssrc64; dsimp only
  exact ORel.ite _ (ORel.none' R _) (source64_rel h hm R s _ 0)

theorem maskBit_hom (m : V₁ × V₁) (lane : Nat) : h.f (maskBit m lane) = maskBit (pmap h m) lane := by
  unfold maskBit; split <;> simp [h.bit, pmap]

theorem src_hom (src : List V₁) : h.f (src0 src) = src0 (src.map h.f) ∧ h.f (src1 src) = src1 (src.map h.f) ∧
    h.f (src2 src) = src2 (src.map h.f) ∧ h.f (src.getD 3 (Dom.lit 0)) = (src.map h.f).getD 3 (Dom.lit 0) :=
  ⟨f_src h src 0, f_src h src 1, f_src h src 2, f_src h src 3⟩

theorem andB64_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (d0 d1 : V₁)
    (hres : (andB64 s code d0 d1).err = none ∨ R) :
    andB64 (mapW h hm s) code (h.f d0) (h.f d1) = mapW h hm (andB64 s code d0 d1) := by
  unfold andB64 at hres ⊢
  dsimp only at hres ⊢
  have hw := writeScalarDst64_hom h hm R hR s code (d0, d1)
    (by by_cases he : (writeScalarDst64 s code (d0, d1)).err.isSome = true
        · rw [ite_eq_left he] at hres; exact hres
        · rw [ite_eq_right he] at hres; exact hres)
  rw [show ((h.f d0, h.f d1) : V₂ × V₂) = pmap h (d0, d1) from rfl, hw]
  by_cases he : (writeScalarDst64 s code (d0, d1)).err.isSome = true
  · rw [ite_eq_left he, ite_eq_left (show (mapW h hm (writeScalarDst64 s code (d0, d1))).err.isSome = true from he)]
  · rw [ite_eq_right he, ite_eq_right (show ¬ (mapW h hm (writeScalarDst64 s code (d0, d1))).err.isSome = true from he)]
    simp [mapW, h.nez64]

theorem saveexecB64_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (a : V₁ × V₁)
    (hres : (saveexecB64 s code a).err = none ∨ R) :
    saveexecB64 (mapW h hm s) code (pmap h a) = mapW h hm (saveexecB64 s code a) := by
  unfold saveexecB64 at hres ⊢
  try dsimp only at hres ⊢
  generalize hs1 : writeExec s (Dom.band a.1 (Dom.lit s.exec.toUInt32)) (Dom.band a.2 (Dom.lit (s.exec >>> 32).toUInt32)) = s1 at hres
  have e1 : writeExec (mapW h hm s) (Dom.band (pmap h a).1 (Dom.lit (mapW h hm s).exec.toUInt32))
      (Dom.band (pmap h a).2 (Dom.lit ((mapW h hm s).exec >>> 32).toUInt32)) = mapW h hm s1 := by
    rw [← hs1, mapW_exec]
    have := writeExec_hom h hm R hR s (Dom.band a.1 (Dom.lit s.exec.toUInt32)) (Dom.band a.2 (Dom.lit (s.exec >>> 32).toUInt32))
      (by rw [hs1]; by_cases he : s1.err.isSome = true
          · rw [ite_eq_left he] at hres; exact hres
          · left; simpa using he)
    rw [h.band, h.band, h.lit, h.lit] at this
    exact this
  rw [e1, mapW_exec]
  by_cases he : s1.err.isSome = true
  · rw [ite_eq_left he, ite_eq_left (show (mapW h hm s1).err.isSome = true from he)]
  · rw [ite_eq_right he, ite_eq_right (show ¬ (mapW h hm s1).err.isSome = true from he)]
    rw [ite_eq_right he] at hres
    try dsimp only at hres
    generalize hs2 : writeScalarDst64 s1 code (Dom.lit s.exec.toUInt32, Dom.lit (s.exec >>> 32).toUInt32) = s2 at hres
    have e2 : writeScalarDst64 (mapW h hm s1) code (Dom.lit s.exec.toUInt32, Dom.lit (s.exec >>> 32).toUInt32)
        = mapW h hm s2 := by
      rw [← hs2]
      have := writeScalarDst64_hom h hm R hR s1 code (Dom.lit s.exec.toUInt32, Dom.lit (s.exec >>> 32).toUInt32)
        (by rw [hs2]; by_cases he2 : s2.err.isSome = true
            · rw [ite_eq_left he2] at hres; exact hres
            · left; simpa using he2)
      simp only [pmap, h.lit] at this
      exact this
    rw [e2]
    by_cases he2 : s2.err.isSome = true
    · rw [ite_eq_left he2, ite_eq_left (show (mapW h hm s2).err.isSome = true from he2)]
    · rw [ite_eq_right he2, ite_eq_right (show ¬ (mapW h hm s2).err.isSome = true from he2)]
      simp [mapW, h.lit]

theorem sop32_hom (R : Prop) (hR : R → Reflects h hm) (s : GWave V₁ M₁) (code : Nat) (d c : V₁)
    (hres : (sop32 s code d c).err = none ∨ R) :
    sop32 (mapW h hm s) code (h.f d) (h.f c) = mapW h hm (sop32 s code d c) := by
  unfold sop32 at hres ⊢
  dsimp only at hres ⊢
  have hw := writeScalarDst_hom h hm R hR s code d
    (by by_cases he : (writeScalarDst s code d).err.isSome = true
        · rw [ite_eq_left he] at hres; exact hres
        · rw [ite_eq_right he] at hres; exact hres)
  rw [hw]
  by_cases he : (writeScalarDst s code d).err.isSome = true
  · rw [ite_eq_left he, ite_eq_left (show (mapW h hm (writeScalarDst s code d)).err.isSome = true from he)]
  · rw [ite_eq_right he, ite_eq_right (show ¬ (mapW h hm (writeScalarDst s code d)).err.isSome = true from he)]
    rfl

theorem xorV_hom (a b : V₁) : h.f (xorV a b) = xorV (h.f a) (h.f b) := by
  unfold xorV; rw [h.sub, h.bor, h.band]

theorem mbcntV_hom (a b : V₁) (n : Nat) : h.f (mbcntV a b n) = mbcntV (h.f a) (h.f b) n := by
  unfold mbcntV
  generalize List.range n = l
  induction l generalizing b with
  | nil => rfl
  | cons k l ih => simp only [List.foldl]; rw [ih, h.add, h.bit]

theorem dsLaneAddrs_rel (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (n lane : Nat) :
    ORel R id (dsLaneAddrs i s n lane) (dsLaneAddrs i (mapW h hm s) n lane) := by
  unfold dsLaneAddrs
  rw [← readVgpr_hom h hm]
  exact ORel.bind (conc_rel h hm R hR _) fun a => ORel.refl R _

theorem execDs_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁) (n : Nat) (isStore : Bool)
    (hres : (execDs i s n isStore).err = none ∨ R) :
    execDs i (mapW h hm s) n isStore = mapW h hm (execDs i s n isStore) := by
  unfold execDs at hres ⊢
  by_cases hg : (i.field "GDS" != 0) = true
  · rw [if_pos hg, if_pos hg]; exact (fail_hom h hm s _).symm
  rw [if_neg hg] at hres; rw [if_neg hg, if_neg hg]
  rw [activeLanes_hom]
  have hrel : ORel R id ((activeLanes s).mapM fun lane => (dsLaneAddrs i s n lane).map fun as => (lane, as))
      ((activeLanes s).mapM fun lane => (dsLaneAddrs i (mapW h hm s) n lane).map fun as => (lane, as)) := by
    have := ORel.mapM (R := R) (ψ := id) (activeLanes s)
      (g₁ := fun lane => (dsLaneAddrs i s n lane).map fun as => (lane, as))
      (g₂ := fun lane => (dsLaneAddrs i (mapW h hm s) n lane).map fun as => (lane, as))
      (fun lane => ORel.map (dsLaneAddrs_rel h hm R hR i s n lane) fun _ => rfl)
    simpa using this
  refine withSome_hom h hm hrel s _ _ _ ?_ hres
  intro las hlas
  simp only [id] at hlas ⊢
  cases isStore
  · simp only [Bool.false_eq_true, ↓reduceIte] at hlas ⊢
    refine withSome_hom h hm (φ := List.map fun p => (p.1, p.2.1, h.f p.2.2)) ?_ s _ _ _
      (fun ws _ => writeRegs_hom h hm s ws) hlas
    refine ORel.mapM _ fun ⟨reg, lane, a⟩ => ?_
    exact ORel.map (load_rel h hm R hR s.mem a) fun v => rfl
  · simp only [↓reduceIte] at hlas ⊢
    by_cases hd : (!decide (las.flatMap (·.2)).Nodup) = true
    · rw [if_pos hd, if_pos hd]; exact (fail_hom h hm s _).symm
    · rw [if_neg hd, if_neg hd, ← storeAll_hom h hm]
      congr 1
      simp only [List.map_flatMap, List.map_map]
      congr 1; funext p
      congr 1; funext q
      simp [readVgpr_hom h hm]

theorem execInst_hom (R : Prop) (hR : R → Reflects h hm) (i : Inst) (s : GWave V₁ M₁)
    (hres : (execInst i s).err = none ∨ R) :
    execInst i (mapW h hm s) = mapW h hm (execInst i s) := by
  unfold execInst at hres ⊢
  split
  · exact (fail_hom h hm s _).symm
  rename_i hmod
  simp only [hmod, Bool.false_eq_true, ↓reduceIte] at hres
  have hs := fun src => src_hom h src
  cases hop : instOp i.name <;> simp only [hop] at hres ⊢
  case s_mov_b32 =>
    exact withSome_hom h hm (ssrc_rel h hm R hR i s 0) s _ _ _
      (fun v hv => writeScalarDst_hom h hm R hR s _ v hv) hres
  case s_mov_b64 =>
    exact withSome_hom h hm (ssrc64_rel h hm R i s 0) s _ _ _
      (fun v hv => writeScalarDst64_hom h hm R hR s _ v hv) hres
  case s_movk_i32 =>
    have := writeScalarDst_hom h hm R hR s (i.field "SDST") (Dom.lit (movkValue (i.field "SIMM16"))) hres
    rw [h.lit] at this; exact this
  case s_and_b64 =>
    refine withSome_hom h hm (φ := fun ab => (pmap h ab.1, pmap h ab.2)) ?_ s _ _ _ ?_ hres
    · refine ORel.bind (ssrc64_rel h hm R i s 0) fun a => ?_
      exact ORel.map (ssrc64_rel h hm R i s 1) fun b => rfl
    · intro ab hab
      simp only [pmap]
      rw [← h.band, ← h.band]
      exact andB64_hom h hm R hR s _ _ _ hab
  case s_cbranch_execz =>
    by_cases he : (s.exec == 0) = true
    · rw [ite_eq_left (show ((mapW h hm s).exec == 0) = true from he), ite_eq_left he]; rfl
    · rw [ite_eq_right (show ¬ ((mapW h hm s).exec == 0) = true from he), ite_eq_right he]
  case smem => exact execSmem_hom h hm R hR i s hres
  case mubuf_load => exact execMubuf_hom h hm R hR i s false hres
  case mubuf_store => exact execMubuf_hom h hm R hR i s true hres
  case v_mov_b32 => exact valuLanes_hom h hm R hR i s 1 _ _ (fun src _ => (hs src).1) hres
  case v_add_nc_u32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.add, (hs src).1, (hs src).2.1]) hres
  case v_and_b32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.band, (hs src).1, (hs src).2.1]) hres
  case v_or_b32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.bor, (hs src).1, (hs src).2.1]) hres
  case v_lshlrev_b32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.shl, (hs src).1, (hs src).2.1]) hres
  case v_lshl_add_u32 =>
    exact valuLanes_hom h hm R hR i s 3 _ _ (fun src _ => by rw [h.add, h.shl, (hs src).1, (hs src).2.1, (hs src).2.2.1]) hres
  case v_add3_u32 =>
    exact valuLanes_hom h hm R hR i s 3 _ _ (fun src _ => by rw [h.add, h.add, (hs src).1, (hs src).2.1, (hs src).2.2.1]) hres
  case v_and_or_b32 =>
    exact valuLanes_hom h hm R hR i s 3 _ _ (fun src _ => by rw [h.bor, h.band, (hs src).1, (hs src).2.1, (hs src).2.2.1]) hres
  case v_mul_lo_u32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.mul, (hs src).1, (hs src).2.1]) hres
  case v_mul_hi_u32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.mulHi, (hs src).1, (hs src).2.1]) hres
  case v_cndmask_b32 =>
    exact withSome_hom h hm (maskSource_rel h hm R s _) s _ _ _
      (fun m hmk => valuLanes_hom h hm R hR i s 2 _ _
        (fun src lane => by rw [h.ite, maskBit_hom, (hs src).1, (hs src).2.1]) hmk) hres
  case v_add_co_u32 =>
    exact valuLanesCarry_hom h hm R hR i s _ _ (fun a b _ => by simp [pmap, h.add, h.carry]) hres
  case v_sub_co_u32 =>
    exact valuLanesCarry_hom h hm R hR i s _ _ (fun a b _ => by simp [pmap, h.sub, h.borrow]) hres
  case v_add_co_ci_u32 =>
    exact withSome_hom h hm (maskSource_rel h hm R s _) s _ _ _
      (fun m hmk => valuLanesCarry_hom h hm R hR i s _ _
        (fun a b lane => by simp [pmap, h.addc, h.carryc, maskBit_hom]) hmk) hres
  case v_sub_co_ci_u32 =>
    exact withSome_hom h hm (maskSource_rel h hm R s _) s _ _ _
      (fun m hmk => valuLanesCarry_hom h hm R hR i s _ _
        (fun a b lane => by simp [pmap, h.subc, h.borrowc, maskBit_hom]) hmk) hres
  case v_lshlrev_b64 => exact valuShift64_hom h hm R hR i s _ _ (fun c a b => h.shl64 c a b) hres
  case v_lshrrev_b64 => exact valuShift64_hom h hm R hR i s _ _ (fun c a b => h.lshr64 c a b) hres
  case v_cmp_le_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ule, (hs src).1, (hs src).2.1]) hres
  case v_cmp_gt_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ugt, (hs src).1, (hs src).2.1]) hres
  case v_cmpx_gt_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ugt, (hs src).1, (hs src).2.1]) hres
  case v_cmp_lt_u64 =>
    exact valuCompare_hom h hm R hR i s true _ _
      (fun src => by rw [h.ult64, (hs src).1, (hs src).2.1, (hs src).2.2.1, (hs src).2.2.2]) hres
  case v_cmp_ne_i64 =>
    exact valuCompare_hom h hm R hR i s true _ _
      (fun src => by rw [h.ne64, (hs src).1, (hs src).2.1, (hs src).2.2.1, (hs src).2.2.2]) hres
  case s_or_b64 =>
    refine withSome_hom h hm (φ := fun ab => (pmap h ab.1, pmap h ab.2)) ?_ s _ _ _ ?_ hres
    · refine ORel.bind (ssrc64_rel h hm R i s 0) fun a => ?_
      exact ORel.map (ssrc64_rel h hm R i s 1) fun b => rfl
    · intro ab hab
      simp only [pmap]
      rw [← h.bor, ← h.bor]
      exact andB64_hom h hm R hR s _ _ _ hab
  case s_andn2_b64 =>
    refine withSome_hom h hm (φ := fun ab => (pmap h ab.1, pmap h ab.2)) ?_ s _ _ _ ?_ hres
    · refine ORel.bind (ssrc64_rel h hm R i s 0) fun a => ?_
      exact ORel.map (ssrc64_rel h hm R i s 1) fun b => rfl
    · intro ab hab
      simp only [pmap]
      rw [← h.lit, ← h.sub, ← h.sub, ← h.band, ← h.band]
      exact andB64_hom h hm R hR s _ _ _ hab
  case s_nor_b64 =>
    refine withSome_hom h hm (φ := fun ab => (pmap h ab.1, pmap h ab.2)) ?_ s _ _ _ ?_ hres
    · refine ORel.bind (ssrc64_rel h hm R i s 0) fun a => ?_
      exact ORel.map (ssrc64_rel h hm R i s 1) fun b => rfl
    · intro ab hab
      simp only [pmap]
      rw [← h.bor, ← h.bor, ← h.lit, ← h.sub, ← h.sub]
      exact andB64_hom h hm R hR s _ _ _ hab
  case s_and_saveexec_b64 =>
    exact withSome_hom h hm (ssrc64_rel h hm R i s 0) s _ _ _
      (fun a ha => saveexecB64_hom h hm R hR s _ a ha) hres
  case s_mulk_i32 =>
    have := writeScalarDst_hom h hm R hR s (i.field "SDST")
      (Dom.mul (readSgpr s (i.field "SDST")) (Dom.lit (movkValue (i.field "SIMM16")))) hres
    rw [h.mul, h.lit, readSgpr_hom h hm] at this; exact this
  case v_cmp_lt_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ugt, (hs src).1, (hs src).2.1]) hres
  case v_cmp_eq_i32 =>
    exact valuCompare_hom h hm R hR i s false _ _
      (fun src => by rw [h.ite, h.ne64, h.lit, h.lit, (hs src).1, (hs src).2.1]) hres
  case v_cmp_ne_i32 =>
    exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ne64, h.lit, (hs src).1, (hs src).2.1]) hres
  case v_cmpx_eq_i32 =>
    exact valuCompare_hom h hm R hR i s false _ _
      (fun src => by rw [h.ite, h.ne64, h.lit, h.lit, (hs src).1, (hs src).2.1]) hres
  case v_cmpx_le_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ule, (hs src).1, (hs src).2.1]) hres
  case v_cmpx_ne_i32 =>
    exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ne64, h.lit, (hs src).1, (hs src).2.1]) hres
  case v_lshl_or_b32 =>
    exact valuLanes_hom h hm R hR i s 3 _ _ (fun src _ => by rw [h.bor, h.shl, (hs src).1, (hs src).2.1, (hs src).2.2.1]) hres
  case v_add_lshl_u32 =>
    exact valuLanes_hom h hm R hR i s 3 _ _ (fun src _ => by rw [h.shl, h.add, (hs src).1, (hs src).2.1, (hs src).2.2.1]) hres
  case v_mul_u32_u24 =>
    exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.mul, h.band, h.band, h.lit, (hs src).1, (hs src).2.1]) hres
  case v_subrev_co_ci_u32 =>
    exact withSome_hom h hm (maskSource_rel h hm R s _) s _ _ _
      (fun m hmk => valuLanesCarry_hom h hm R hR i s _ _
        (fun a b lane => by simp [pmap, h.subc, h.borrowc, maskBit_hom]) hmk) hres
  case v_max_u32 =>
    exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.ite, h.ugt, (hs src).1, (hs src).2.1]) hres
  case v_min_u32 =>
    exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.ite, h.ugt, (hs src).1, (hs src).2.1]) hres
  case v_sub_nc_u32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.sub, (hs src).1, (hs src).2.1]) hres
  case v_lshrrev_b32 =>
    exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by
      rw [show ∀ p : V₁ × V₁, h.f p.1 = (Prod.map h.f h.f p).1 from fun _ => rfl, h.lshr64, h.band, h.lit, h.lit,
        (hs src).1, (hs src).2.1]) hres
  case s_add_u32 | s_sub_i32 | s_xor_b32 | s_max_u32 | s_lshl_b32 | s_lshl2_add_u32 | s_lshl3_add_u32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab hab
      dsimp only at hab ⊢
      have := sop32_hom h hm R hR s _ _ _ hab
      simp only [h.add, h.sub, h.band, h.bor, h.shl, h.ite, h.ugt, h.carry, h.nez64, h.bit, h.lit, xorV_hom,
        lshrV_hom] at this
      exact this
  case s_bfm_b32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab hab
      have := writeScalarDst_hom h hm R hR s _ _ hab
      simp only [h.shl, h.sub, h.lit] at this
      exact this
  case s_cselect_b64 =>
    refine withSome_hom h hm (φ := fun ab => (pmap h ab.1, pmap h ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc64_rel h hm R i s 0) fun a => ORel.map (ssrc64_rel h hm R i s 1) fun b => rfl
    · intro ab hab
      have := writeScalarDst64_hom h hm R hR s _ _ hab
      simp only [pmap, h.ite] at this
      exact this
  case s_cmp_eq_i32 | s_cmp_lt_u32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab _
      simp only [mapW, h.sub, h.ne64, h.ugt, h.lit]
  case s_cmpk_lt_u32 =>
    refine withSome_hom h hm (scalarSource_rel h hm R hR s _ _) s _ _ _ ?_ hres
    intro a _
    simp only [mapW, h.ugt, h.lit]
  case s_cbranch_scc0 =>
    refine withSome_hom h hm (conc_rel h hm R hR s.scc) s _ _ _ ?_ hres
    intro c _
    simp only [id]
    split <;> rfl
  case v_mbcnt_lo_u32_b32 | v_mbcnt_hi_u32_b32 =>
    exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [mbcntV_hom, (hs src).1, (hs src).2.1]) hres
  case ds_read_b64 => exact execDs_hom h hm R hR i s 2 false hres
  case ds_write_b64 => exact execDs_hom h hm R hR i s 2 true hres
  case ds_write_b128 => exact execDs_hom h hm R hR i s 4 true hres
  case s_and_b32 | s_addc_u32 | s_or_b32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab hab
      have := sop32_hom h hm R hR s _ _ _ hab
      simp only [h.addc, h.carryc, h.bor, h.band, h.nez64, h.lit] at this
      exact this
  case s_mul_i32 | s_mul_hi_u32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab hab
      have := writeScalarDst_hom h hm R hR s _ _ hab
      simp only [h.mul, h.mulHi] at this
      exact this
  case s_bfm_b64 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab hab
      dsimp only at hab ⊢
      have := writeScalarDst64_hom h hm R hR s _ _ hab
      have e := h.shl64 ab.1 (Dom.lit 1) (Dom.lit 0)
      simp only [Prod.map, h.lit] at e
      have e2 := h.shl64 ab.2 (Dom.sub (Dom.shl64 ab.1 (Dom.lit 1) (Dom.lit 0)).1 (Dom.lit 1))
        (Dom.subc (Dom.shl64 ab.1 (Dom.lit 1) (Dom.lit 0)).2 (Dom.lit 0) (Dom.borrow (Dom.shl64 ab.1 (Dom.lit 1) (Dom.lit 0)).1 (Dom.lit 1)))
      simp only [Prod.map, h.sub, h.subc, h.borrow, h.lit] at e2
      rw [← e, ← e2]
      simpa [pmap] using this
  case s_cmp_lg_i32 | s_cmp_ge_u32 =>
    refine withSome_hom h hm (φ := fun ab => (h.f ab.1, h.f ab.2)) ?_ s _ _ _ ?_ hres
    · exact ORel.bind (ssrc_rel h hm R hR i s 0) fun a => ORel.map (ssrc_rel h hm R hR i s 1) fun b => rfl
    · intro ab _
      simp only [mapW, h.ne64, h.ule, h.lit]
  case s_getpc_b64 =>
    have := writeScalarDst64_hom h hm R hR s _ _ hres
    simp only [pmap, h.lit] at this
    exact this
  case s_cbranch_scc1 =>
    refine withSome_hom h hm (conc_rel h hm R hR s.scc) s _ _ _ ?_ hres
    intro c _
    simp only [id]
    split <;> rfl
  case s_inst_prefetch =>
    split
    · rfl
    · exact (fail_hom h hm s _).symm
  case v_readfirstlane_b32 =>
    try dsimp only at hres ⊢
    by_cases hc : (isSdwa i || srcCode i 0 < 256 || srcCode i 0 > 511) = true
    · rw [if_pos hc, if_pos hc]; exact (fail_hom h hm s _).symm
    · rw [if_neg hc] at hres; rw [if_neg hc, if_neg hc]
      rw [← readVgpr_hom h hm]
      exact writeScalarDst_hom h hm R hR s _ _ hres
  case v_subrev_co_u32 =>
    exact valuLanesCarry_hom h hm R hR i s _ _ (fun a b _ => by simp [pmap, h.sub, h.borrow]) hres
  case v_subrev_nc_u32 => exact valuLanes_hom h hm R hR i s 2 _ _ (fun src _ => by rw [h.sub, (hs src).1, (hs src).2.1]) hres
  case v_cmp_ge_u32 => exact valuCompare_hom h hm R hR i s false _ _ (fun src => by rw [h.ule, (hs src).1, (hs src).2.1]) hres
  case v_cmp_gt_u64 =>
    exact valuCompare_hom h hm R hR i s true _ _
      (fun src => by rw [h.ult64, (hs src).1, (hs src).2.1, (hs src).2.2.1, (hs src).2.2.2]) hres
  case unknown => exact (fail_hom h hm s _).symm
  all_goals rfl

theorem step_hom (R : Prop) (hR : R → Reflects h hm) (prog : Program) (s : GWave V₁ M₁)
    (hres : (step prog s).err = none ∨ R) :
    step prog (mapW h hm s) = mapW h hm (step prog s) := by
  unfold step at hres ⊢
  by_cases hl : (s.halted || s.err.isSome) = true
  · rw [ite_eq_left hl, ite_eq_left (show ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
  · rw [ite_eq_right hl] at hres
    rw [ite_eq_right hl, ite_eq_right (show ¬ ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
    simp only [mapW_pc]
    split
    · exact (fail_hom h hm s _).symm
    · exact (fail_hom h hm s _).symm
    · rename_i i hi
      simp only [hi] at hres
      exact execInst_hom h hm R hR i { s with pc := s.pc + i.words.length } hres

theorem run_err_none (prog : Program) : ∀ (n : Nat) (s : GWave V₁ M₁), (run prog n s).err = none → s.err = none
  | 0, s, h0 => by
    unfold run at h0; split at h0
    · exact h0
    · exact absurd h0 (fail_err s _)
  | n + 1, s, h0 => by
    unfold run at h0; split at h0
    · exact h0
    · rename_i hl
      have := run_err_none prog n _ h0
      cases hs : s.err with
      | none => rfl
      | some e => simp [hs] at hl

theorem step_err_none (prog : Program) (s : GWave V₁ M₁) (h0 : (step prog s).err = none) : s.err = none := by
  unfold step at h0; split at h0
  · exact h0
  · rename_i hl; cases hs : s.err with
    | none => rfl
    | some e => simp [hs] at hl

theorem init_hom (m : M₁) : mapW h hm (GWave.init m : GWave V₁ M₁) = GWave.init (hm.g m) := by
  simp [mapW, GWave.init, Array.map_replicate, h.lit]

theorem initWave_hom (m : M₁) (setLo : UInt32) (g : Nat) :
    mapW h hm (initWave m setLo g : GWave V₁ M₁) = initWave (hm.g m) setLo g := by
  unfold initWave
  simp only
  generalize List.range lanes = ls
  have base : mapW h hm (writeSgpr (writeSgpr (GWave.init m : GWave V₁ M₁) 2 (Dom.lit setLo)) 3 (Dom.lit (UInt32.ofNat g))) =
      writeSgpr (writeSgpr (GWave.init (hm.g m)) 2 (Dom.lit setLo)) 3 (Dom.lit (UInt32.ofNat g)) := by
    rw [writeSgpr_hom, writeSgpr_hom, init_hom, h.lit, h.lit]
  revert base
  generalize writeSgpr (writeSgpr (GWave.init m : GWave V₁ M₁) 2 (Dom.lit setLo)) 3 (Dom.lit (UInt32.ofNat g)) = s₁
  generalize writeSgpr (writeSgpr (GWave.init (hm.g m) : GWave V₂ M₂) 2 (Dom.lit setLo)) 3 (Dom.lit (UInt32.ofNat g)) = s₂
  intro base
  induction ls generalizing s₁ s₂ with
  | nil => simpa using base
  | cons l ls ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [writeVgpr_hom, base, h.lit]

/-- The theorem: running the model commutes with the homomorphism, whenever the source run did not fail,
or always when the homomorphism reflects unknown values and missing words. -/
theorem run_hom (R : Prop) (hR : R → Reflects h hm) (prog : Program) :
    ∀ (n : Nat) (s : GWave V₁ M₁), (run prog n s).err = none ∨ R →
      run prog n (mapW h hm s) = mapW h hm (run prog n s)
  | 0, s, _ => by
    unfold run
    by_cases hl : (s.halted || s.err.isSome) = true
    · rw [ite_eq_left hl, ite_eq_left (show ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
    · rw [ite_eq_right hl, ite_eq_right (show ¬ ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
      exact (fail_hom h hm s _).symm
  | n + 1, s, hres => by
    unfold run at hres ⊢
    by_cases hl : (s.halted || s.err.isSome) = true
    · rw [ite_eq_left hl, ite_eq_left (show ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
    · rw [ite_eq_right hl] at hres
      rw [ite_eq_right hl, ite_eq_right (show ¬ ((mapW h hm s).halted || (mapW h hm s).err.isSome) = true from hl)]
      have hstep : (step prog s).err = none ∨ R := hres.imp_left (run_err_none prog n _)
      rw [step_hom h hm R hR prog s hstep]
      exact run_hom R hR prog n _ hres

end
end Obend.Hardware.Gpu.Rdna2
