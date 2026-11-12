module
/-
# Obend.OS.Sel4MicrokitKernelCore — a capability kernel in the seL4 / Microkit shape

The kernel state is a capability space with its derivation tree, one table of address
translations (CPU address spaces and SMMU stream tables alike), physical memory, one scheduling
context per protection domain, and a clock. `kstep` is total: a refused system call is a no-op,
so a trace is any list of events and no theorem here filters the environment.

1. **Capabilities and the derivation tree.** A capability is an object, a rights mask and a
   badge; `Cap.le` is the attenuation order. A slot holds a `CapNode` with its parent slot.
   `mintCap` appends a child that attenuates its parent, `deleteCap` leaves a tombstone that keeps
   the lineage, and `revokeCap` erases every descendant in one forward pass: parents precede
   children, so a slot is doomed exactly when its parent is the revoked slot or was erased earlier
   in the same pass (`revokeCap_severs_all_descendants`).
2. **Translation.** A `Mapping` names the capabilities that back it. `delete` and `revoke` tear
   down every mapping whose backing died, so a store through any address space reaches only
   frames a live write capability names (`smmu_dma_write_confined_to_writable_pd_frames`,
   `trace_mem_confined`).
3. **Scheduling contexts.** A sporadic server: one unit charged now returns one period later.
   `charge_some` is the accounting identity the temporal bound rests on.
`Obend.OS.Sel4MicrokitKernel` proves temporal isolation and the copy-before-verify ingress over
this kernel and welds the ingress to the outbox and the powerbox.

Two things this model does not do. Endpoint and notification capabilities are typed and
attenuate, but message transfer is not modelled. Retyping does not consume untyped memory, so two
retypes of one untyped may name the same frame: a frame is private to a domain only when no other
domain holds an untyped capability over it, and `Exclusive` says so.
-/
public import Obend.Digest.Cshake256.Seam

public section
namespace Obend.OS.Sel4MicrokitKernel

open Obend.Digest.Cshake256.Native (bytesOfList)

set_option autoImplicit false

/-! ## 1. Rights, objects, capabilities and the attenuation order -/

abbrev PdId := Nat
abbrev SlotId := Nat

structure Rights where
  read : Bool
  write : Bool
  grant : Bool
  deriving DecidableEq, Repr

/-- `a ⊆ b`. -/
def Rights.sub (a b : Rights) : Bool :=
  (!a.read || b.read) && (!a.write || b.write) && (!a.grant || b.grant)

theorem Rights.sub_iff {a b : Rights} : a.sub b = true ↔
    (a.read = true → b.read = true) ∧ (a.write = true → b.write = true) ∧
      (a.grant = true → b.grant = true) := by
  obtain ⟨ar, aw, ag⟩ := a
  cases ar <;> cases aw <;> cases ag <;> simp [Rights.sub, and_assoc]

/-- Kernel objects. An untyped capability covers the frames `[base, base + size)`; every other
object is created at boot, as in a static Microkit system. -/
inductive CapObj where
  | untypedCap (base size : Nat)
  | frameCap (pfn : Nat)
  | pageTableCap (asid : Nat)
  | endpointCap (ep : Nat)
  | notificationCap (ntfn : Nat)
  | smmuStreamCap (sid : Nat)
  | schedControlCap (core : Nat)
  deriving DecidableEq, Repr

/-- The object gives access to physical frame `f`. -/
def CapObj.touches : CapObj → Nat → Bool
  | .untypedCap b s, f => decide (b ≤ f ∧ f < b + s)
  | .frameCap g, f => g == f
  | _, _ => false

/-- `c` is `p`, or memory retyped out of the untyped `p`. -/
def CapObj.within (c p : CapObj) : Bool :=
  c == p ||
  match p, c with
  | .untypedCap b s, .untypedCap b' s' => decide (b ≤ b' ∧ b' + s' ≤ b + s)
  | .untypedCap b s, .frameCap f => decide (b ≤ f ∧ f < b + s)
  | _, _ => false

theorem CapObj.within_refl (c : CapObj) : c.within c = true := by simp [CapObj.within]

theorem CapObj.within_trans {a b c : CapObj} (h₁ : a.within b = true) (h₂ : b.within c = true) :
    a.within c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [CapObj.within] <;> omega

theorem CapObj.touches_mono {c p : CapObj} {f : Nat} (hw : c.within p = true)
    (ht : c.touches f = true) : p.touches f = true := by
  cases c <;> cases p <;> simp_all [CapObj.within, CapObj.touches] <;> omega

structure Cap where
  obj : CapObj
  rights : Rights
  badge : Nat
  deriving DecidableEq, Repr

/-- `c` attenuates `p`: an object within `p`'s, no more rights, and a badge that is `p`'s unless
`p` is unbadged. -/
def Cap.le (c p : Cap) : Bool :=
  c.obj.within p.obj && c.rights.sub p.rights && (p.badge == 0 || c.badge == p.badge)

theorem Cap.le_iff {c p : Cap} : c.le p = true ↔
    c.obj.within p.obj = true ∧ c.rights.sub p.rights = true ∧
      (p.badge = 0 ∨ c.badge = p.badge) := by
  simp [Cap.le, and_assoc]

theorem Cap.le_refl (c : Cap) : c.le c = true := by
  rw [Cap.le_iff, Rights.sub_iff]
  exact ⟨CapObj.within_refl _, ⟨id, id, id⟩, .inr rfl⟩

theorem Cap.le_trans {a b c : Cap} (h₁ : a.le b = true) (h₂ : b.le c = true) :
    a.le c = true := by
  rw [Cap.le_iff, Rights.sub_iff] at *
  obtain ⟨o₁, ⟨r₁, w₁, g₁⟩, b₁⟩ := h₁
  obtain ⟨o₂, ⟨r₂, w₂, g₂⟩, b₂⟩ := h₂
  exact ⟨CapObj.within_trans o₁ o₂, ⟨fun h => r₂ (r₁ h), fun h => w₂ (w₁ h), fun h => g₂ (g₁ h)⟩,
    by omega⟩

/-! ## 2. The capability space and its derivation tree -/

/-- A slot's content. A deleted capability stays as a tombstone (`live = false`) so that its
descendants keep their lineage. -/
structure CapNode where
  owner : PdId
  cap : Cap
  parent : Option SlotId
  live : Bool
  deriving DecidableEq, Repr

/-- Slot ids index the array. `none` is a slot erased by a revocation. -/
abbrev CSpace := Array (Option CapNode)

/-- The lineage node in slot `i`, live or tombstone. -/
def nodeAt (cs : CSpace) (i : SlotId) : Option CapNode :=
  match cs[i]? with
  | some slot => slot
  | none => none

/-- The capability a domain can invoke through slot `i`. -/
def capAt (cs : CSpace) (i : SlotId) : Option CapNode :=
  match nodeAt cs i with
  | some n => if n.live then some n else none
  | none => none

theorem capAt_eq_some {cs : CSpace} {i : SlotId} {n : CapNode} :
    capAt cs i = some n ↔ nodeAt cs i = some n ∧ n.live = true := by
  unfold capAt
  split
  · rename_i m hm
    split
    · rename_i hl
      constructor
      · intro h; cases h; exact ⟨hm, hl⟩
      · rintro ⟨h, -⟩; rw [hm] at h; exact h
    · rename_i hl
      constructor
      · intro h; cases h
      · rintro ⟨h, hl'⟩; rw [hm] at h; cases h; exact absurd hl' hl
  · rename_i hn
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; rw [hn] at h; cases h

theorem nodeAt_lt {cs : CSpace} {i : SlotId} {n : CapNode} (h : nodeAt cs i = some n) :
    i < cs.size := by
  unfold nodeAt at h
  split at h
  · rename_i slot hs
    obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp hs
    exact hi
  · cases h

theorem nodeAt_ge {cs : CSpace} {i : SlotId} (h : cs.size ≤ i) : nodeAt cs i = none := by
  unfold nodeAt
  rw [Array.getElem?_eq_none h]

theorem nodeAt_push (cs : CSpace) (x : Option CapNode) (j : SlotId) :
    nodeAt (cs.push x) j = if j = cs.size then x else nodeAt cs j := by
  unfold nodeAt
  rw [Array.getElem?_push]
  by_cases h : j = cs.size <;> simp [h]

theorem nodeAt_set (cs : CSpace) (i j : SlotId) (x : Option CapNode) (hi : i < cs.size) :
    nodeAt (cs.setIfInBounds i x) j = if j = i then x else nodeAt cs j := by
  unfold nodeAt
  rw [Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hi]
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h']

/-- `i` is a strict descendant of `anc` along parent pointers. -/
inductive Descends (cs : CSpace) (anc : SlotId) : SlotId → Prop where
  | child {i : SlotId} {n : CapNode} :
      nodeAt cs i = some n → n.parent = some anc → Descends cs anc i
  | step {i p : SlotId} {n : CapNode} :
      nodeAt cs i = some n → n.parent = some p → Descends cs anc p → Descends cs anc i

theorem Descends.node {cs : CSpace} {a i : SlotId} (h : Descends cs a i) :
    ∃ n, nodeAt cs i = some n := by
  cases h with
  | child h1 _ => exact ⟨_, h1⟩
  | step h1 _ _ => exact ⟨_, h1⟩

/-- The derivation tree is well formed: a parent sits in an earlier slot (so the tree is acyclic),
its lineage node is present, and the child attenuates it. -/
def CdtInv (cs : CSpace) : Prop :=
  ∀ i n, nodeAt cs i = some n → ∀ p, n.parent = some p →
    p < i ∧ ∃ m, nodeAt cs p = some m ∧ n.cap.le m.cap = true

theorem descends_lt {cs : CSpace} (hInv : CdtInv cs) {a i : SlotId} (h : Descends cs a i) :
    a < i := by
  induction h with
  | child h1 h2 => exact (hInv _ _ h1 _ h2).1
  | step h1 h2 _ ih => exact Nat.lt_trans ih (hInv _ _ h1 _ h2).1

/-- **Acyclicity.** No slot descends from itself. -/
theorem cdt_acyclic {cs : CSpace} (hInv : CdtInv cs) (i : SlotId) : ¬ Descends cs i i :=
  fun h => Nat.lt_irrefl _ (descends_lt hInv h)

/-- A child attenuating the live capability in `src`. -/
def mintCap (cs : CSpace) (src : SlotId) (dst : PdId) (cap : Cap) : CSpace :=
  cs.push (some ⟨dst, cap, some src, true⟩)

/-- Delete the capability in `slot`, keeping its lineage node. -/
def deleteCap (cs : CSpace) (slot : SlotId) (n : CapNode) : CSpace :=
  cs.setIfInBounds slot (some { n with live := false })

/-- What the revocation pass writes for one slot. `done` holds the slots already processed. -/
def scanKeep (s : SlotId) (done : CSpace) (slot : Option CapNode) : Option CapNode :=
  match slot with
  | none => none
  | some n =>
    match n.parent with
    | none => some n
    | some p => if p == s || (nodeAt done p).isNone then none else some n

def revokeScan (cs : CSpace) (s : SlotId) : Nat → CSpace → CSpace
  | 0, done => done
  | fuel + 1, done => revokeScan cs s fuel (done.push (scanKeep s done (nodeAt cs done.size)))

/-- Erase every descendant of slot `s`: one pass, one array read per slot. -/
def revokeCap (cs : CSpace) (s : SlotId) : CSpace := revokeScan cs s cs.size #[]

/-- The processed prefix is exact: descendants erased, everything else untouched. -/
def ScanOk (cs : CSpace) (s : SlotId) (done : CSpace) : Prop :=
  ∀ j, j < done.size →
    (Descends cs s j ∧ nodeAt done j = none) ∨ (¬ Descends cs s j ∧ nodeAt done j = nodeAt cs j)

theorem scanKeep_ok {cs : CSpace} {s : SlotId} (hInv : CdtInv cs) {done : CSpace}
    (hOk : ScanOk cs s done) :
    ScanOk cs s (done.push (scanKeep s done (nodeAt cs done.size))) := by
  intro j hj
  rw [Array.size_push] at hj
  rw [nodeAt_push]
  by_cases hjs : j = done.size
  · subst hjs
    simp only [↓reduceIte]
    cases hn : nodeAt cs done.size with
    | none =>
      right
      refine ⟨fun hd => ?_, by simp [scanKeep]⟩
      obtain ⟨n, hn'⟩ := hd.node
      rw [hn] at hn'; cases hn'
    | some n =>
      cases hp : n.parent with
      | none =>
        right
        refine ⟨fun hd => ?_, by simp [scanKeep, hp]⟩
        cases hd with
        | child h1 h2 => rw [hn] at h1; cases h1; rw [hp] at h2; cases h2
        | step h1 h2 _ => rw [hn] at h1; cases h1; rw [hp] at h2; cases h2
      | some p =>
        obtain ⟨hlt, m, hm, -⟩ := hInv _ n hn p hp
        by_cases hps : p = s
        · left
          exact ⟨.child hn (hps ▸ hp), by simp [scanKeep, hp, hps]⟩
        · rcases hOk p hlt with ⟨hd, hnone⟩ | ⟨hnd, hsame⟩
          · left
            exact ⟨.step hn hp hd, by simp [scanKeep, hp, hnone]⟩
          · right
            refine ⟨fun hd => ?_, by simp [scanKeep, hp, hps, hsame, hm]⟩
            cases hd with
            | child h1 h2 => rw [hn] at h1; cases h1; rw [hp] at h2; cases h2; exact hps rfl
            | step h1 h2 h3 => rw [hn] at h1; cases h1; rw [hp] at h2; cases h2; exact hnd h3
  · simp only [hjs, ↓reduceIte]
    exact hOk j (by omega)

theorem revokeScan_ok {cs : CSpace} {s : SlotId} (hInv : CdtInv cs) (fuel : Nat) :
    ∀ done : CSpace, ScanOk cs s done →
      ScanOk cs s (revokeScan cs s fuel done) ∧
        (revokeScan cs s fuel done).size = done.size + fuel := by
  induction fuel with
  | zero => intro done h; exact ⟨h, rfl⟩
  | succ f ih =>
    intro done h
    simp only [revokeScan]
    obtain ⟨h1, h2⟩ := ih _ (scanKeep_ok hInv h)
    refine ⟨h1, ?_⟩
    rw [h2, Array.size_push]; omega

/-- Slot by slot: a descendant of `s` is erased, and any other slot is left exactly as it was. -/
theorem revokeCap_spec {cs : CSpace} (hInv : CdtInv cs) (s i : SlotId) :
    (Descends cs s i ∧ nodeAt (revokeCap cs s) i = none) ∨
      (¬ Descends cs s i ∧ nodeAt (revokeCap cs s) i = nodeAt cs i) := by
  obtain ⟨hOk, hSize⟩ :=
    revokeScan_ok (s := s) hInv cs.size #[] (fun j hj => absurd hj (by simp))
  have hSize' : (revokeCap cs s).size = cs.size := by
    unfold revokeCap; rw [hSize]; simp
  by_cases hi : cs.size ≤ i
  · right
    have h2 : nodeAt cs i = none := nodeAt_ge hi
    have h1 : nodeAt (revokeCap cs s) i = none := nodeAt_ge (hSize'.symm ▸ hi)
    refine ⟨fun hd => ?_, h1.trans h2.symm⟩
    obtain ⟨n, hn⟩ := hd.node
    rw [h2] at hn; cases hn
  · exact hOk i (by omega)

/-- **Transitive revocation.** One `revokeCap s` erases every descendant of `s` at any depth and
in any domain, leaves every other slot (the revoked slot, its ancestors, its siblings) exactly as
it was, and leaves `s` with no descendant. -/
theorem revokeCap_severs_all_descendants {cs : CSpace} (hInv : CdtInv cs) (s : SlotId) :
    (∀ i, Descends cs s i → nodeAt (revokeCap cs s) i = none) ∧
      (∀ i, ¬ Descends cs s i → nodeAt (revokeCap cs s) i = nodeAt cs i) ∧
      (∀ i, ¬ Descends (revokeCap cs s) s i) := by
  have sub : ∀ j n, nodeAt (revokeCap cs s) j = some n →
      nodeAt cs j = some n ∧ ¬ Descends cs s j := by
    intro j n hj
    rcases revokeCap_spec hInv s j with ⟨-, h⟩ | ⟨hnd, h⟩
    · rw [h] at hj; cases hj
    · exact ⟨h ▸ hj, hnd⟩
  refine ⟨fun i hd => ?_, fun i hnd => ?_, fun i hd => ?_⟩
  · rcases revokeCap_spec hInv s i with ⟨-, h⟩ | ⟨hn, -⟩
    · exact h
    · exact absurd hd hn
  · rcases revokeCap_spec hInv s i with ⟨hd, -⟩ | ⟨-, h⟩
    · exact absurd hd hnd
    · exact h
  · induction hd with
    | child h1 h2 => exact (sub _ _ h1).2 (.child (sub _ _ h1).1 h2)
    | step _ _ _ ih => exact ih

theorem revokeCap_cdtInv {cs : CSpace} (hInv : CdtInv cs) (s : SlotId) :
    CdtInv (revokeCap cs s) := by
  intro i n hn p hp
  rcases revokeCap_spec hInv s i with ⟨-, h⟩ | ⟨hnd, h⟩
  · rw [h] at hn; cases hn
  · rw [h] at hn
    obtain ⟨hlt, m, hm, hle⟩ := hInv i n hn p hp
    refine ⟨hlt, m, ?_, hle⟩
    rcases revokeCap_spec hInv s p with ⟨hd, -⟩ | ⟨-, h'⟩
    · exact absurd (.step hn hp hd) hnd
    · rw [h']; exact hm

/-- `cs'` has no live capability that `cs` lacks. -/
def Shrinks (cs cs' : CSpace) : Prop := ∀ j f, capAt cs' j = some f → capAt cs j = some f

theorem revokeCap_shrinks {cs : CSpace} (hInv : CdtInv cs) (s : SlotId) :
    Shrinks cs (revokeCap cs s) := by
  intro j f hf
  rw [capAt_eq_some] at hf ⊢
  rcases revokeCap_spec hInv s j with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h] at hf; cases hf.1
  · exact ⟨h ▸ hf.1, hf.2⟩

theorem nodeAt_deleteCap {cs : CSpace} {slot : SlotId} {n : CapNode}
    (hn : nodeAt cs slot = some n) (j : SlotId) :
    nodeAt (deleteCap cs slot n) j =
      if j = slot then some { n with live := false } else nodeAt cs j :=
  nodeAt_set cs slot j _ (nodeAt_lt hn)

theorem deleteCap_shrinks {cs : CSpace} {slot : SlotId} {n : CapNode}
    (hn : nodeAt cs slot = some n) : Shrinks cs (deleteCap cs slot n) := by
  intro j f hf
  rw [capAt_eq_some] at hf ⊢
  rw [nodeAt_deleteCap hn] at hf
  by_cases hj : j = slot
  · simp only [hj, ↓reduceIte] at hf
    obtain ⟨h1, h2⟩ := hf
    cases h1; cases h2
  · simp only [hj, ↓reduceIte] at hf
    exact hf

theorem deleteCap_cdtInv {cs : CSpace} (hInv : CdtInv cs) {slot : SlotId} {n : CapNode}
    (hn : nodeAt cs slot = some n) : CdtInv (deleteCap cs slot n) := by
  have key : ∀ i x, nodeAt (deleteCap cs slot n) i = some x →
      ∃ y, nodeAt cs i = some y ∧ x.cap = y.cap ∧ x.parent = y.parent := by
    intro i x hx
    rw [nodeAt_deleteCap hn] at hx
    by_cases hi : i = slot
    · simp only [hi, ↓reduceIte] at hx
      cases hx
      exact ⟨n, hi ▸ hn, rfl, rfl⟩
    · simp only [hi, ↓reduceIte] at hx
      exact ⟨x, hx, rfl, rfl⟩
  have back : ∀ p m, nodeAt cs p = some m →
      ∃ m', nodeAt (deleteCap cs slot n) p = some m' ∧ m'.cap = m.cap := by
    intro p m hm
    rw [nodeAt_deleteCap hn]
    by_cases hp : p = slot
    · simp only [hp, ↓reduceIte]
      rw [hp, hn] at hm
      cases hm
      exact ⟨_, rfl, rfl⟩
    · simp only [hp, ↓reduceIte]
      exact ⟨m, hm, rfl⟩
  intro i x hx p hp
  obtain ⟨y, hy, hc, hpar⟩ := key i x hx
  obtain ⟨hlt, m, hm, hle⟩ := hInv i y hy p (hpar ▸ hp)
  obtain ⟨m', hm', hc'⟩ := back p m hm
  exact ⟨hlt, m', hm', by rw [hc, hc']; exact hle⟩

theorem capAt_mintCap {cs : CSpace} {src : SlotId} {dst : PdId} {cap : Cap} {i : SlotId}
    {x : CapNode} (h : capAt (mintCap cs src dst cap) i = some x) :
    capAt cs i = some x ∨ x = ⟨dst, cap, some src, true⟩ := by
  rw [capAt_eq_some] at h
  unfold mintCap at h
  rw [nodeAt_push] at h
  by_cases hi : i = cs.size
  · simp only [hi, ↓reduceIte] at h
    exact .inr (Option.some.inj h.1).symm
  · simp only [hi, ↓reduceIte] at h
    exact .inl (capAt_eq_some.mpr h)

theorem capAt_mintCap_of_some {cs : CSpace} {src : SlotId} {dst : PdId} {cap : Cap} {i : SlotId}
    {x : CapNode} (h : capAt cs i = some x) : capAt (mintCap cs src dst cap) i = some x := by
  rw [capAt_eq_some] at h ⊢
  unfold mintCap
  rw [nodeAt_push]
  have hi : ¬ i = cs.size := Nat.ne_of_lt (nodeAt_lt h.1)
  simp only [hi, ↓reduceIte]
  exact h

theorem mintCap_cdtInv {cs : CSpace} (hInv : CdtInv cs) {src : SlotId} {n : CapNode}
    (hn : capAt cs src = some n) (dst : PdId) {cap : Cap} (hle : cap.le n.cap = true) :
    CdtInv (mintCap cs src dst cap) := by
  have hsrc := (capAt_eq_some.mp hn).1
  intro i x hx p hp
  unfold mintCap at hx ⊢
  rw [nodeAt_push] at hx
  by_cases hi : i = cs.size
  · simp only [hi, ↓reduceIte] at hx
    cases hx
    cases hp
    refine ⟨hi ▸ nodeAt_lt hsrc, n, ?_, hle⟩
    rw [nodeAt_push]
    simp only [Nat.ne_of_lt (nodeAt_lt hsrc), ↓reduceIte]
    exact hsrc
  · simp only [hi, ↓reduceIte] at hx
    obtain ⟨hlt, m, hm, hle'⟩ := hInv i x hx p hp
    refine ⟨hlt, m, ?_, hle'⟩
    rw [nodeAt_push]
    simp only [Nat.ne_of_lt (nodeAt_lt hm), ↓reduceIte]
    exact hm

/-! ## 3. Address translation: CPU address spaces and SMMU stream tables -/

/-- An address space: a protection domain's, or the stage-2 table of a device stream. -/
inductive Space where
  | cpu (pd : PdId)
  | dev (sid : Nat)
  deriving DecidableEq, Repr

/-- The object whose capability authorizes editing the space. -/
def Space.authObj : Space → CapObj
  | .cpu pd => .pageTableCap pd
  | .dev sid => .smmuStreamCap sid

/-- One page of one space, and the two slots whose capabilities back it. -/
structure Mapping where
  space : Space
  vpage : Nat
  pfn : Nat
  writable : Bool
  owner : PdId
  frameSlot : SlotId
  authSlot : SlotId
  deriving DecidableEq, Repr

abbrev pageSize : Nat := 4096

theorem page_of_addr (pfn off : Nat) (h : off < pageSize) :
    (pfn * pageSize + off) / pageSize = pfn := by
  unfold pageSize at *; omega

def lookupMap (maps : List Mapping) (sp : Space) (vpage : Nat) : Option Mapping :=
  maps.find? fun e => e.space == sp && e.vpage == vpage

theorem lookupMap_some {maps : List Mapping} {sp : Space} {vp : Nat} {e : Mapping}
    (h : lookupMap maps sp vp = some e) : e ∈ maps ∧ e.space = sp ∧ e.vpage = vp := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2.1, h2.2⟩

/-- The physical address behind `va`, refused when a store meets a read-only page. -/
def translate (maps : List Mapping) (sp : Space) (va : Nat) (write : Bool) : Option Nat :=
  match lookupMap maps sp (va / pageSize) with
  | some e => if write && !e.writable then none else some (e.pfn * pageSize + va % pageSize)
  | none => none

theorem translate_some {maps : List Mapping} {sp : Space} {va : Nat} {w : Bool} {pa : Nat}
    (h : translate maps sp va w = some pa) :
    ∃ e, lookupMap maps sp (va / pageSize) = some e ∧ (w = true → e.writable = true) ∧
      pa = e.pfn * pageSize + va % pageSize := by
  unfold translate at h
  split at h
  · rename_i e he
    split at h
    · cases h
    · rename_i hw
      cases h
      refine ⟨e, he, fun hwt => ?_, rfl⟩
      cases hew : e.writable
      · simp [hwt, hew] at hw
      · rfl
  · cases h

/-- No space maps one page twice. -/
def VUnique (maps : List Mapping) : Prop :=
  ∀ a ∈ maps, ∀ b ∈ maps, a.space = b.space → a.vpage = b.vpage → a = b

theorem lookupMap_of_mem {maps : List Mapping} (hU : VUnique maps) {e : Mapping}
    (he : e ∈ maps) : lookupMap maps e.space e.vpage = some e := by
  unfold lookupMap
  cases hf : maps.find? (fun x => x.space == e.space && x.vpage == e.vpage) with
  | none => exact absurd (by simp) (List.find?_eq_none.mp hf e he)
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    rw [hU x hx e he hk.1 hk.2]

/-- The mapping is backed: its owner holds a live frame capability for the frame (with the write
right if the page is writable) and a live capability for the space. -/
def BackedBy (cs : CSpace) (e : Mapping) : Prop :=
  ∃ f a, capAt cs e.frameSlot = some f ∧ f.owner = e.owner ∧ f.cap.obj = .frameCap e.pfn ∧
    (e.writable = true → f.cap.rights.write = true) ∧
    capAt cs e.authSlot = some a ∧ a.owner = e.owner ∧ a.cap.obj = e.space.authObj

/-- Drop every mapping one of whose backing slots is no longer live. -/
def teardown (cs : CSpace) (maps : List Mapping) : List Mapping :=
  maps.filter fun e => (capAt cs e.frameSlot).isSome && (capAt cs e.authSlot).isSome

/-! ## 4. Scheduling contexts: a sporadic server -/

structure Refill where
  time : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure SchedContext where
  budget : Nat
  period : Nat
  refills : List Refill
  deriving DecidableEq, Repr

/-- The budget that becomes usable strictly before time `h`. -/
def availBefore (h : Nat) : List Refill → Nat
  | [] => 0
  | r :: rs => (if r.time < h then r.amount else 0) + availBefore h rs

/-- Append a refill, merging it into the last one when they fall due together. -/
def pushRefill : List Refill → Refill → List Refill
  | [], r => [r]
  | x :: xs, r =>
    if xs.isEmpty && x.time == r.time then [⟨x.time, x.amount + r.amount⟩]
    else x :: pushRefill xs r

theorem availBefore_pushRefill (h : Nat) (q : List Refill) (r : Refill) :
    availBefore h (pushRefill q r) = availBefore h q + (if r.time < h then r.amount else 0) := by
  induction q with
  | nil => simp [pushRefill, availBefore]
  | cons x xs ih =>
    simp only [pushRefill]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hc
      obtain ⟨hxs, ht⟩ := hc
      subst hxs
      by_cases hlt : r.time < h <;> simp [availBefore, ht, hlt]
    · simp only [availBefore, ih]; omega

/-- Take one unit from the head refill. -/
def decHead (r : Refill) (rest : List Refill) : List Refill :=
  if r.amount ≤ 1 then rest else ⟨r.time, r.amount - 1⟩ :: rest

theorem availBefore_decHead (h : Nat) (r : Refill) (rest : List Refill) (hpos : 0 < r.amount) :
    availBefore h (decHead r rest) + (if r.time < h then 1 else 0) =
      availBefore h (r :: rest) := by
  unfold decHead
  by_cases hlt : r.time < h <;> by_cases h1 : r.amount ≤ 1 <;>
    simp [availBefore, hlt, h1] <;> omega

/-- Run for one tick at time `now`: the head refill must be due and non-empty; the unit it gives
up returns one period later. `none` when the context has no usable budget. -/
def SchedContext.charge (sc : SchedContext) (now : Nat) : Option SchedContext :=
  match sc.refills with
  | [] => none
  | r :: rest =>
    if r.time ≤ now ∧ 0 < r.amount then
      some { sc with refills := pushRefill (decHead r rest) ⟨now + sc.period, 1⟩ }
    else none

theorem charge_some {sc sc' : SchedContext} {now : Nat} (h : sc.charge now = some sc') :
    sc'.budget = sc.budget ∧ sc'.period = sc.period ∧ ∃ t, t ≤ now ∧ ∀ hz,
      availBefore hz sc'.refills + (if t < hz then 1 else 0) =
        availBefore hz sc.refills + (if now + sc.period < hz then 1 else 0) := by
  unfold SchedContext.charge at h
  split at h
  · cases h
  · rename_i r rest hq
    split at h
    · rename_i hc
      cases h
      refine ⟨rfl, rfl, r.time, hc.1, fun hz => ?_⟩
      have h2 := availBefore_decHead hz r rest hc.2
      simp only [availBefore_pushRefill, hq]
      by_cases h3 : r.time < hz <;> by_cases h4 : now + sc.period < hz <;>
        simp [h3, h4] at h2 ⊢ <;> omega
    · cases h

/-- A context never holds more than its budget, and its period is positive. -/
def SchedOk (sc : SchedContext) : Prop :=
  0 < sc.period ∧ ∀ hz, availBefore hz sc.refills ≤ sc.budget

theorem charge_schedOk {sc sc' : SchedContext} {now : Nat} (hok : SchedOk sc)
    (h : sc.charge now = some sc') : SchedOk sc' := by
  obtain ⟨hb, hp, t, ht, heq⟩ := charge_some h
  refine ⟨hp ▸ hok.1, fun hz => ?_⟩
  have h1 := heq hz
  have h2 := hok.2 hz
  rw [hb]
  by_cases h3 : t < hz <;> by_cases h4 : now + sc.period < hz <;> simp [h3, h4] at h1 <;> omega

/-! ## 5. Kernel state, system calls and events -/

structure KState where
  cspace : CSpace
  maps : List Mapping
  mem : Nat → UInt8
  /-- One scheduling context per protection domain, indexed by `PdId`. -/
  scs : Array SchedContext
  now : Nat

inductive Syscall where
  | mint (src : SlotId) (dst : PdId) (cap : Cap)
  | delete (slot : SlotId)
  | revoke (slot : SlotId)
  | map (sp : Space) (authSlot frameSlot : SlotId) (vpage pfn : Nat) (writable : Bool)
  | unmap (sp : Space) (vpage : Nat)
  | schedConfigure (ctl : SlotId) (target : PdId) (budget period : Nat)

/-- The invoker owns the source, the child attenuates it, and handing it to another domain needs
the grant right. -/
def mintOk (n : CapNode) (pd dst : PdId) (cap : Cap) : Bool :=
  n.owner == pd && cap.le n.cap && (dst == pd || n.cap.rights.grant)

/-- The invoker owns a capability for the space with the write right and a readable frame
capability for exactly this frame, with the write right if the page is to be writable. -/
def mapOk (a f : CapNode) (pd : PdId) (sp : Space) (pfn : Nat) (w : Bool) : Bool :=
  a.owner == pd && f.owner == pd && a.cap.obj == sp.authObj && a.cap.rights.write &&
    f.cap.obj == .frameCap pfn && f.cap.rights.read && (!w || f.cap.rights.write)

def CapObj.isSchedControl : CapObj → Bool
  | .schedControlCap _ => true
  | _ => false

/-- One system call by domain `pd`. `none` is a refusal. -/
def ksyscall (k : KState) (pd : PdId) : Syscall → Option KState
  | .mint src dst cap =>
    match capAt k.cspace src with
    | some n =>
      if mintOk n pd dst cap then some { k with cspace := mintCap k.cspace src dst cap }
      else none
    | none => none
  | .delete slot =>
    match capAt k.cspace slot with
    | some n =>
      if n.owner == pd then
        some { k with cspace := deleteCap k.cspace slot n,
                      maps := teardown (deleteCap k.cspace slot n) k.maps }
      else none
    | none => none
  | .revoke slot =>
    match capAt k.cspace slot with
    | some n =>
      if n.owner == pd then
        some { k with cspace := revokeCap k.cspace slot,
                      maps := teardown (revokeCap k.cspace slot) k.maps }
      else none
    | none => none
  | .map sp authSlot frameSlot vpage pfn w =>
    match capAt k.cspace authSlot, capAt k.cspace frameSlot with
    | some a, some f =>
      if mapOk a f pd sp pfn w && (lookupMap k.maps sp vpage).isNone then
        some { k with maps := ⟨sp, vpage, pfn, w, pd, frameSlot, authSlot⟩ :: k.maps }
      else none
    | _, _ => none
  | .unmap sp vpage =>
    some { k with maps := k.maps.filter fun e =>
      !(e.space == sp && e.vpage == vpage && e.owner == pd) }
  | .schedConfigure ctl target budget period =>
    match capAt k.cspace ctl with
    | some c =>
      if c.owner == pd && c.cap.obj.isSchedControl && decide (0 < period) &&
          decide (budget ≤ period) then
        some { k with scs := k.scs.setIfInBounds target ⟨budget, period, [⟨k.now, budget⟩]⟩ }
      else none
    | none => none

inductive KEvent where
  | syscall (pd : PdId) (call : Syscall)
  /-- A store by code running in domain `pd`. -/
  | pdWrite (pd : PdId) (va : Nat) (val : UInt8)
  /-- A block copy inside domain `pd`'s address space. -/
  | pdCopy (pd : PdId) (srcV dstV len : Nat)
  /-- One beat of a device's DMA burst, translated by the stream's SMMU table. -/
  | dma (sid : Nat) (iova : Nat) (val : UInt8)
  /-- A timer tick. The scheduler offers the processor to `run`. -/
  | tick (run : Option PdId)

def storeVia (k : KState) (sp : Space) (va : Nat) (val : UInt8) : KState :=
  match translate k.maps sp va true with
  | some pa => { k with mem := fun a => if a = pa then val else k.mem a }
  | none => k

def copyVia (k : KState) (pd : PdId) (srcV dstV len : Nat) : KState :=
  if srcV % pageSize + len ≤ pageSize ∧ dstV % pageSize + len ≤ pageSize then
    match translate k.maps (.cpu pd) srcV false, translate k.maps (.cpu pd) dstV true with
    | some sa, some da =>
      { k with mem := fun a => if da ≤ a ∧ a < da + len then k.mem (sa + (a - da)) else k.mem a }
    | _, _ => k
  else k

/-- Offer the processor to domain `p` for this tick: charge its context if it can pay. -/
def tickSched (k : KState) (p : PdId) : Array SchedContext :=
  match (k.scs[p]?).bind (·.charge k.now) with
  | some sc' => k.scs.setIfInBounds p sc'
  | none => k.scs

/-- One event. Total: a refused system call, a faulting store and an exhausted budget change
nothing but the clock. -/
def kstep (k : KState) : KEvent → KState
  | .syscall pd call => (ksyscall k pd call).getD k
  | .pdWrite pd va val => storeVia k (.cpu pd) va val
  | .pdCopy pd srcV dstV len => copyVia k pd srcV dstV len
  | .dma sid iova val => storeVia k (.dev sid) iova val
  | .tick run => { k with now := k.now + 1, scs := (run.map (tickSched k)).getD k.scs }

def runK (k : KState) : List KEvent → KState
  | [] => k
  | ev :: evs => runK (kstep k ev) evs

/-- The address space an event stores through. -/
def KEvent.space : KEvent → Option Space
  | .pdWrite pd _ _ => some (.cpu pd)
  | .pdCopy pd _ _ _ => some (.cpu pd)
  | .dma sid _ _ => some (.dev sid)
  | _ => none

/-- The domain whose code an event runs. Devices and the timer are no domain. -/
def KEvent.actor : KEvent → Option PdId
  | .syscall pd _ => some pd
  | .pdWrite pd _ _ => some pd
  | .pdCopy pd _ _ _ => some pd
  | _ => none

theorem space_actor {ev : KEvent} {pd : PdId} (h : ev.space = some (.cpu pd)) :
    ev.actor = some pd := by
  cases ev <;> simp_all [KEvent.space, KEvent.actor]

/-! ## 6. What a system call can do -/

/-- The four shapes of a successful system call: a mint, a shrink of the capability space with
its teardown, one new backed mapping, or a change that adds neither capability nor mapping. -/
def SysEffect (pd : PdId) (k k' : KState) : Prop :=
  k'.mem = k.mem ∧ k'.now = k.now ∧
  ((∃ src n dst cap, capAt k.cspace src = some n ∧ n.owner = pd ∧ cap.le n.cap = true ∧
      k'.cspace = mintCap k.cspace src dst cap ∧ k'.maps = k.maps) ∨
   ((CdtInv k.cspace → Shrinks k.cspace k'.cspace ∧ CdtInv k'.cspace) ∧
      k'.maps = teardown k'.cspace k.maps) ∨
   (k'.cspace = k.cspace ∧ ∃ e, k'.maps = e :: k.maps ∧ e.owner = pd ∧
      lookupMap k.maps e.space e.vpage = none ∧ BackedBy k.cspace e) ∨
   (k'.cspace = k.cspace ∧ ∀ e ∈ k'.maps, e ∈ k.maps))

theorem ksyscall_effect {k k' : KState} {pd : PdId} {call : Syscall}
    (h : ksyscall k pd call = some k') : SysEffect pd k k' := by
  cases call with
  | mint src dst cap =>
    simp only [ksyscall] at h
    split at h
    · rename_i n hn
      split at h
      · rename_i hok
        cases h
        simp only [mintOk, Bool.and_eq_true, beq_iff_eq] at hok
        exact ⟨rfl, rfl, .inl ⟨src, n, dst, cap, hn, hok.1.1, hok.1.2, rfl, rfl⟩⟩
      · cases h
    · cases h
  | delete slot =>
    simp only [ksyscall] at h
    split at h
    · rename_i n hn
      split at h
      · cases h
        have hnode := (capAt_eq_some.mp hn).1
        exact ⟨rfl, rfl, .inr (.inl ⟨fun hInv =>
          ⟨deleteCap_shrinks hnode, deleteCap_cdtInv hInv hnode⟩, rfl⟩)⟩
      · cases h
    · cases h
  | revoke slot =>
    simp only [ksyscall] at h
    split at h
    · split at h
      · cases h
        exact ⟨rfl, rfl, .inr (.inl ⟨fun hInv =>
          ⟨revokeCap_shrinks hInv slot, revokeCap_cdtInv hInv slot⟩, rfl⟩)⟩
      · cases h
    · cases h
  | map sp authSlot frameSlot vpage pfn w =>
    simp only [ksyscall] at h
    split at h
    · rename_i a f ha hf
      split at h
      · rename_i hok
        cases h
        simp only [mapOk, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
          Bool.or_eq_true, Bool.not_eq_true'] at hok
        obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, -⟩, h7⟩, h8⟩ := hok
        refine ⟨rfl, rfl, .inr (.inr (.inl ⟨rfl, _, rfl, rfl, h8, f, a, hf, h2, h5, ?_, ha, h1,
          h3⟩))⟩
        intro hw
        rcases h7 with h7 | h7
        · rw [h7] at hw; cases hw
        · exact h7
      · cases h
    · cases h
  | unmap sp vpage =>
    simp only [ksyscall] at h
    cases h
    exact ⟨rfl, rfl, .inr (.inr (.inr ⟨rfl, fun e he => (List.mem_filter.mp he).1⟩))⟩
  | schedConfigure ctl target budget period =>
    simp only [ksyscall] at h
    split at h
    · split at h
      · cases h
        exact ⟨rfl, rfl, .inr (.inr (.inr ⟨rfl, fun _ he => he⟩))⟩
      · cases h
    · cases h

/-- The kernel invariant: a well-formed derivation tree, every mapping backed by live
capabilities of its owner, and no page mapped twice. -/
def KInv (k : KState) : Prop :=
  CdtInv k.cspace ∧ (∀ e ∈ k.maps, BackedBy k.cspace e) ∧ VUnique k.maps

theorem kinv_syscall {k k' : KState} {pd : PdId} (hInv : KInv k) (hE : SysEffect pd k k') :
    KInv k' := by
  obtain ⟨hC, hB, hU⟩ := hInv
  obtain ⟨-, -, hE⟩ := hE
  rcases hE with ⟨src, n, dst, cap, hn, -, hle, hcs, hm⟩ | ⟨hS, hm⟩ | ⟨hcs, e, hm, -, hfresh, hbk⟩ |
    ⟨hcs, hsub⟩
  · refine ⟨hcs ▸ mintCap_cdtInv hC hn dst hle, ?_, hm ▸ hU⟩
    intro e he
    rw [hm] at he
    obtain ⟨f, a, h1, h2, h3, h4, h5, h6, h7⟩ := hB e he
    rw [hcs]
    exact ⟨f, a, capAt_mintCap_of_some h1, h2, h3, h4, capAt_mintCap_of_some h5, h6, h7⟩
  · obtain ⟨hSh, hC'⟩ := hS hC
    refine ⟨hC', ?_, ?_⟩
    · intro e he
      rw [hm] at he
      obtain ⟨he, hlive⟩ := List.mem_filter.mp he
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hlive
      obtain ⟨⟨f', hf'⟩, ⟨a', ha'⟩⟩ := hlive
      obtain ⟨f, a, h1, h2, h3, h4, h5, h6, h7⟩ := hB e he
      have ef : f' = f := Option.some.inj ((hSh _ _ hf').symm.trans h1)
      have ea : a' = a := Option.some.inj ((hSh _ _ ha').symm.trans h5)
      exact ⟨f, a, ef ▸ hf', h2, h3, h4, ea ▸ ha', h6, h7⟩
    · intro a ha b hb
      rw [hm] at ha hb
      exact hU a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1
  · refine ⟨hcs ▸ hC, ?_, ?_⟩
    · intro x hx
      rw [hm] at hx
      rw [hcs]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hbk
      · exact hB x hx
    · have hno : ∀ x ∈ k.maps, x.space = e.space → x.vpage = e.vpage → False := by
        intro x hx h1 h2
        exact List.find?_eq_none.mp hfresh x hx (by simp [h1, h2])
      intro a ha b hb h1 h2
      rw [hm] at ha hb
      rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
      · rw [ha, hb]
      · exact (hno b hb (ha ▸ h1).symm (ha ▸ h2).symm).elim
      · exact (hno a ha (hb ▸ h1) (hb ▸ h2)).elim
      · exact hU a ha b hb h1 h2
  · refine ⟨hcs ▸ hC, fun e he => hcs ▸ hB e (hsub e he), ?_⟩
    intro a ha b hb
    exact hU a (hsub a ha) b (hsub b hb)

theorem storeVia_frame (k : KState) (sp : Space) (va : Nat) (val : UInt8) :
    (storeVia k sp va val).cspace = k.cspace ∧ (storeVia k sp va val).maps = k.maps ∧
      (storeVia k sp va val).scs = k.scs ∧ (storeVia k sp va val).now = k.now := by
  unfold storeVia
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem copyVia_frame (k : KState) (pd : PdId) (s d len : Nat) :
    (copyVia k pd s d len).cspace = k.cspace ∧ (copyVia k pd s d len).maps = k.maps ∧
      (copyVia k pd s d len).scs = k.scs ∧ (copyVia k pd s d len).now = k.now := by
  unfold copyVia
  split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- An event is a successful system call, or it leaves capabilities and mappings alone. -/
theorem kstep_frame (k : KState) (ev : KEvent) :
    (∃ pd call k', ev = .syscall pd call ∧ ksyscall k pd call = some k' ∧ kstep k ev = k') ∨
      ((kstep k ev).cspace = k.cspace ∧ (kstep k ev).maps = k.maps) := by
  cases ev with
  | syscall pd call =>
    cases h : ksyscall k pd call with
    | some k' => exact .inl ⟨pd, call, k', rfl, h, by simp [kstep, h]⟩
    | none => exact .inr (by simp [kstep, h])
  | pdWrite pd va val => exact .inr ⟨(storeVia_frame ..).1, (storeVia_frame ..).2.1⟩
  | pdCopy pd s d len => exact .inr ⟨(copyVia_frame ..).1, (copyVia_frame ..).2.1⟩
  | dma sid iova val => exact .inr ⟨(storeVia_frame ..).1, (storeVia_frame ..).2.1⟩
  | tick run => exact .inr ⟨rfl, rfl⟩

theorem kstep_inv {k : KState} (hInv : KInv k) (ev : KEvent) : KInv (kstep k ev) := by
  rcases kstep_frame k ev with ⟨pd, call, k', -, hk, hstep⟩ | ⟨hc, hm⟩
  · rw [hstep]; exact kinv_syscall hInv (ksyscall_effect hk)
  · unfold KInv; rw [hc, hm]; exact hInv

theorem runK_inv {k : KState} (hInv : KInv k) (evs : List KEvent) : KInv (runK k evs) := by
  induction evs generalizing k with
  | nil => exact hInv
  | cons ev evs ih => exact ih (kstep_inv hInv ev)

/-! ## 7. No authority amplification -/

/-- Every live capability of `cs` attenuates a live capability of `cs₀`. -/
def Bounded (cs₀ cs : CSpace) : Prop :=
  ∀ i n, capAt cs i = some n → ∃ j r, capAt cs₀ j = some r ∧ n.cap.le r.cap = true

theorem kstep_bounded {cs₀ : CSpace} {k : KState} (hInv : KInv k) (hB : Bounded cs₀ k.cspace)
    (ev : KEvent) : Bounded cs₀ (kstep k ev).cspace := by
  rcases kstep_frame k ev with ⟨pd, call, k', -, hk, hstep⟩ | ⟨hc, -⟩
  · rw [hstep]
    obtain ⟨-, -, hE⟩ := ksyscall_effect hk
    rcases hE with ⟨src, n, dst, cap, hn, -, hle, hcs, -⟩ | ⟨hS, -⟩ | ⟨hcs, -⟩ | ⟨hcs, -⟩
    · intro i x hx
      rw [hcs] at hx
      rcases capAt_mintCap hx with hx | rfl
      · exact hB i x hx
      · obtain ⟨j, r, hr, hle'⟩ := hB src n hn
        exact ⟨j, r, hr, Cap.le_trans hle hle'⟩
    · exact fun i x hx => hB i x ((hS hInv.1).1 i x hx)
    · rw [hcs]; exact hB
    · rw [hcs]; exact hB
  · rw [hc]; exact hB

/-- **No authority amplification.** Over any trace of system calls, stores, DMA and ticks, every
capability any domain holds at the end attenuates a capability that was live at the start: its
object is that object or memory inside it, its rights are a subset, and a badge once set is
kept. -/
theorem no_authority_amplification_across_syscalls {k : KState} (hInv : KInv k)
    (evs : List KEvent) (i : SlotId) (n : CapNode)
    (hn : capAt (runK k evs).cspace i = some n) :
    ∃ j r, capAt k.cspace j = some r ∧ n.cap.le r.cap = true := by
  have key : ∀ (evs : List KEvent) (k' : KState), KInv k' → Bounded k.cspace k'.cspace →
      Bounded k.cspace (runK k' evs).cspace := by
    intro evs
    induction evs with
    | nil => intro k' _ hB; exact hB
    | cons ev evs ih => intro k' hI hB; exact ih _ (kstep_inv hI ev) (kstep_bounded hI hB ev)
  exact key evs k hInv (fun i n hn => ⟨i, n, hn, Cap.le_refl _⟩) i n hn

/-! ## 8. Stores are confined to mapped writable frames -/

theorem storeVia_mem_changed {k : KState} {sp : Space} {va : Nat} {val : UInt8} {a : Nat}
    (h : (storeVia k sp va val).mem a ≠ k.mem a) :
    ∃ e ∈ k.maps, e.space = sp ∧ e.writable = true ∧ e.pfn = a / pageSize := by
  unfold storeVia at h
  split at h
  · rename_i pa hpa
    obtain ⟨e, hl, hw, rfl⟩ := translate_some hpa
    obtain ⟨hmem, hsp, -⟩ := lookupMap_some hl
    by_cases ha : a = e.pfn * pageSize + va % pageSize
    · refine ⟨e, hmem, hsp, hw rfl, ?_⟩
      rw [ha, page_of_addr _ _ (Nat.mod_lt _ (by decide))]
    · simp [ha] at h
  · exact absurd rfl h

theorem copyVia_mem_changed {k : KState} {pd : PdId} {s d len : Nat} {a : Nat}
    (h : (copyVia k pd s d len).mem a ≠ k.mem a) :
    ∃ e ∈ k.maps, e.space = .cpu pd ∧ e.writable = true ∧ e.pfn = a / pageSize := by
  unfold copyVia at h
  split at h
  · rename_i hfit
    split at h
    · rename_i sa da hsa hda
      obtain ⟨e, hl, hw, rfl⟩ := translate_some hda
      obtain ⟨hmem, hsp, -⟩ := lookupMap_some hl
      by_cases ha : e.pfn * pageSize + d % pageSize ≤ a ∧
          a < e.pfn * pageSize + d % pageSize + len
      · refine ⟨e, hmem, hsp, hw rfl, ?_⟩
        have := hfit.2
        unfold pageSize at *
        omega
      · simp [ha] at h
    · exact absurd rfl h
  · exact absurd rfl h

theorem ksyscall_mem {k k' : KState} {pd : PdId} {call : Syscall}
    (h : ksyscall k pd call = some k') : k'.mem = k.mem := (ksyscall_effect h).1

/-- A byte changes only under a store through a space that maps its frame writable. -/
theorem kstep_mem_changed {k : KState} {ev : KEvent} {a : Nat}
    (h : (kstep k ev).mem a ≠ k.mem a) :
    ∃ sp e, ev.space = some sp ∧ e ∈ k.maps ∧ e.space = sp ∧ e.writable = true ∧
      e.pfn = a / pageSize := by
  cases ev with
  | syscall pd call =>
    cases hk : ksyscall k pd call with
    | some k' =>
      simp only [kstep, hk, Option.getD_some] at h
      exact absurd (congrFun (ksyscall_mem hk) a) h
    | none =>
      simp only [kstep, hk, Option.getD_none] at h
      exact absurd rfl h
  | pdWrite pd va val =>
    obtain ⟨e, h1, h2, h3, h4⟩ := storeVia_mem_changed (sp := .cpu pd) h
    exact ⟨_, e, rfl, h1, h2, h3, h4⟩
  | pdCopy pd s d len =>
    obtain ⟨e, h1, h2, h3, h4⟩ := copyVia_mem_changed h
    exact ⟨_, e, rfl, h1, h2, h3, h4⟩
  | dma sid iova val =>
    obtain ⟨e, h1, h2, h3, h4⟩ := storeVia_mem_changed (sp := .dev sid) h
    exact ⟨_, e, rfl, h1, h2, h3, h4⟩
  | tick run => exact absurd rfl h

/-- The events of one DMA burst by the device behind stream `sid`. -/
def dmaBurst (sid : Nat) (burst : List (Nat × UInt8)) : List KEvent :=
  burst.map fun w => .dma sid w.1 w.2

/-- **SMMU confinement.** Whatever addresses and values an untrusted device drives in a burst, a
byte changes only in a frame its stream table maps writable, and behind that mapping one domain
holds both a live capability for the stream and a live frame capability with the write right.
Kernel memory and the frames of every other domain are out of reach. -/
theorem smmu_dma_write_confined_to_writable_pd_frames {k : KState} (hInv : KInv k) (sid : Nat)
    (burst : List (Nat × UInt8)) (a : Nat)
    (hne : (runK k (dmaBurst sid burst)).mem a ≠ k.mem a) :
    ∃ e ∈ k.maps, e.space = .dev sid ∧ e.writable = true ∧ e.pfn = a / pageSize ∧
      ∃ f s, capAt k.cspace e.frameSlot = some f ∧ f.owner = e.owner ∧
        f.cap.obj = .frameCap (a / pageSize) ∧ f.cap.rights.write = true ∧
        capAt k.cspace e.authSlot = some s ∧ s.owner = e.owner ∧
        s.cap.obj = .smmuStreamCap sid := by
  have key : ∀ (burst : List (Nat × UInt8)) (k' : KState), k'.maps = k.maps →
      (runK k' (dmaBurst sid burst)).mem a ≠ k'.mem a →
      ∃ e ∈ k.maps, e.space = .dev sid ∧ e.writable = true ∧ e.pfn = a / pageSize := by
    intro burst
    induction burst with
    | nil => intro k' _ h; exact absurd rfl h
    | cons w ws ih =>
      intro k' hm h
      simp only [dmaBurst, List.map_cons, runK] at h
      by_cases h1 : (kstep k' (.dma sid w.1 w.2)).mem a = k'.mem a
      · have hf : (kstep k' (.dma sid w.1 w.2)).maps = k'.maps :=
          (storeVia_frame k' (.dev sid) w.1 w.2).2.1
        exact ih _ (hf.trans hm) (by rw [h1]; exact h)
      · obtain ⟨sp, e, hsp, he, hes, hw, hp⟩ := kstep_mem_changed h1
        cases hsp
        exact ⟨e, hm ▸ he, hes, hw, hp⟩
  obtain ⟨e, he, hes, hw, hp⟩ := key burst k rfl hne
  obtain ⟨f, s, h1, h2, h3, h4, h5, h6, h7⟩ := hInv.2.1 e he
  exact ⟨e, he, hes, hw, hp, f, s, h1, h2, hp ▸ h3, h4 hw, h5, h6, by rw [h7, hes]; rfl⟩

/-- **Memory confinement over a whole trace.** If any event of any trace changes a byte, then a
capability live at the start already gave write access to that byte's frame. -/
theorem trace_mem_confined {k : KState} (hInv : KInv k) (evs : List KEvent) (a : Nat)
    (hne : (runK k evs).mem a ≠ k.mem a) :
    ∃ j r, capAt k.cspace j = some r ∧ r.cap.obj.touches (a / pageSize) = true ∧
      r.cap.rights.write = true := by
  have key : ∀ (evs : List KEvent) (k' : KState), KInv k' → Bounded k.cspace k'.cspace →
      (runK k' evs).mem a ≠ k'.mem a →
      ∃ j r, capAt k.cspace j = some r ∧ r.cap.obj.touches (a / pageSize) = true ∧
        r.cap.rights.write = true := by
    intro evs
    induction evs with
    | nil => intro k' _ _ h; exact absurd rfl h
    | cons ev evs ih =>
      intro k' hI hB h
      simp only [runK] at h
      by_cases h1 : (kstep k' ev).mem a = k'.mem a
      · exact ih _ (kstep_inv hI ev) (kstep_bounded hI hB ev) (by rw [h1]; exact h)
      · obtain ⟨sp, e, -, he, -, hw, hp⟩ := kstep_mem_changed h1
        obtain ⟨f, s, hf, -, hobj, hwr, -⟩ := hI.2.1 e he
        obtain ⟨j, r, hr, hle⟩ := hB _ f hf
        obtain ⟨ho, hrs, -⟩ := Cap.le_iff.mp hle
        refine ⟨j, r, hr, CapObj.touches_mono ho ?_, (Rights.sub_iff.mp hrs).2.1 (hwr hw)⟩
        rw [hobj, ← hp]
        simp [CapObj.touches]
  exact key evs k hInv (fun i n hn => ⟨i, n, hn, Cap.le_refl _⟩) hne

/-- **Kernel memory is immutable.** A frame no initial capability names with the write right
keeps its contents under every trace. -/
theorem unowned_frame_immutable {k : KState} (hInv : KInv k) (f : Nat)
    (hNone : ∀ j r, capAt k.cspace j = some r → r.cap.rights.write = true →
      r.cap.obj.touches f = false)
    (evs : List KEvent) (a : Nat) (ha : a / pageSize = f) : (runK k evs).mem a = k.mem a := by
  by_cases h : (runK k evs).mem a = k.mem a
  · exact h
  · obtain ⟨j, r, hr, ht, hw⟩ := trace_mem_confined hInv evs a h
    rw [ha, hNone j r hr hw] at ht
    cases ht

/-! ## Multi-page ingress and SMMU revocation -/

/-- Translate every byte, including bytes beyond a page boundary. No partial success. -/
def spanAddresses (maps : List Mapping) (sp : Space) (write : Bool) : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | va, n + 1 => do
    let pa ← translate maps sp va write
    let rest ← spanAddresses maps sp write (va + 1) n
    pure (pa :: rest)

theorem spanAddresses_length {maps : List Mapping} {sp : Space} {write : Bool}
    {va len : Nat} {addresses : List Nat}
    (h : spanAddresses maps sp write va len = some addresses) : addresses.length = len := by
  induction len generalizing va addresses with
  | zero => simp [spanAddresses] at h; subst h; rfl
  | succ n ih =>
    cases ht : translate maps sp va write with
    | none => simp [spanAddresses, ht] at h
    | some pa =>
      cases hr : spanAddresses maps sp write (va + 1) n with
      | none => simp [spanAddresses, ht, hr] at h
      | some rest =>
        simp [spanAddresses, ht, hr] at h
        subst h
        simp [ih hr]

def readMultiPageVia (k : KState) (pd : PdId) (va len : Nat) : Option (List UInt8) :=
  (spanAddresses k.maps (.cpu pd) false va len).map (List.map k.mem)

/-- Resolve both spans before writing; snapshot the source before any destination write.
Overlapping spans have memmove semantics; a missing page refuses the entire copy. -/
def copyMultiPageVia (k : KState) (pd : PdId) (src dst len : Nat) : Option KState := do
  let srcs ← spanAddresses k.maps (.cpu pd) false src len
  let dsts ← spanAddresses k.maps (.cpu pd) true dst len
  let writes := dsts.zip (srcs.map k.mem)
  pure { k with mem := fun a => (writes.reverse.lookup a).getD (k.mem a) }

/-- Revoke every device alias to protected frames, across all stream IDs. CPU mappings
remain. This models completed SMMU invalidation, including the device translation cache. -/
def smmuUnmapRingFrames (k : KState) (frames : List Nat) : KState :=
  { k with maps := k.maps.filter fun e => match e.space with
    | .cpu _ => true
    | .dev _ => !(frames.contains e.pfn) }

def deviceDmaWrite (k : KState) (sid va : Nat) (value : UInt8) : KState :=
  storeVia k (.dev sid) va value

def DmaExcluded (k : KState) (frames : List Nat) : Prop :=
  ∀ e ∈ k.maps, ∀ sid, e.space = .dev sid → e.pfn ∉ frames

theorem smmuUnmapRingFrames_excludes (k : KState) (frames : List Nat) :
    DmaExcluded (smmuUnmapRingFrames k frames) frames := by
  intro e he sid hs
  have hf := (List.mem_filter.mp he).2
  simp [hs] at hf
  exact hf

theorem deviceDmaWrite_maps (k : KState) (sid va : Nat) (value : UInt8) :
    (deviceDmaWrite k sid va value).maps = k.maps := by
  unfold deviceDmaWrite storeVia
  split <;> rfl

theorem deviceDmaWrite_frozen {k : KState} {frames : List Nat}
    (excluded : DmaExcluded k frames) (sid va : Nat) (value : UInt8)
    (a : Nat) (ha : a / pageSize ∈ frames) :
    (deviceDmaWrite k sid va value).mem a = k.mem a := by
  unfold deviceDmaWrite storeVia
  split
  · rename_i pa hp
    have ne : a ≠ pa := by
      intro eq
      obtain ⟨e, he, _, hpa⟩ := translate_some hp
      obtain ⟨hm, hs, _⟩ := lookupMap_some he
      have page : pa / pageSize = e.pfn := by
        rw [hpa]; exact page_of_addr _ _ (Nat.mod_lt _ (by decide))
      rw [eq, page] at ha
      exact excluded e hm sid hs ha
    simp [ne]
  · rfl

/-- Unbounded traces; the environment chooses every stream, address and byte. -/
def runDeviceDma : KState → List (Nat × Nat × UInt8) → KState
  | k, [] => k
  | k, (sid, va, value) :: rest => runDeviceDma (deviceDmaWrite k sid va value) rest

theorem runDeviceDma_frozen {k : KState} {frames : List Nat}
    (excluded : DmaExcluded k frames) (writes : List (Nat × Nat × UInt8)) :
    (runDeviceDma k writes).maps = k.maps ∧
      ∀ a, a / pageSize ∈ frames → (runDeviceDma k writes).mem a = k.mem a := by
  induction writes generalizing k with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons w ws ih =>
    obtain ⟨sid, va, value⟩ := w
    have hm := deviceDmaWrite_maps k sid va value
    have hx : DmaExcluded (deviceDmaWrite k sid va value) frames := by
      simpa only [DmaExcluded, hm] using excluded
    obtain ⟨hm', hf⟩ := ih hx
    exact ⟨hm'.trans hm, fun a ha => (hf a ha).trans (deviceDmaWrite_frozen excluded sid va value a ha)⟩

end Obend.OS.Sel4MicrokitKernel

end
