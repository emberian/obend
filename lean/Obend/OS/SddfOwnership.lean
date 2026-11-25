module
public import Obend.Lower.Pancake.BorrowedTurn
public import Obend.OS.SmmuDmaConfinement
import all Obend.Lower.Pancake.BorrowedTurn
import all Obend.Lower.Pancake.DragonStyleShard

public section
namespace Obend.OS.SddfOwnership

open Obend.Lower.Pancake.DragonStyleShard
open Obend.Lower.Pancake.BorrowedTurn
open Sel4MicrokitKernel
open SmmuDmaConfinement

set_option autoImplicit false

inductive Port | rx | tx | storage deriving DecidableEq, Repr

/-- Parameterized sDDF queue of capacity `N` (`0 < N` witnessed by `ring.head : Fin N`).
Producer and consumer counts live in the proof; physical ring slots stay bounded. -/
structure Queue (N : Nat) where
  ring : Ring N UInt16
  consumed : Nat
  produced : Nat
  headAligned : ring.head.val = consumed % N
  liveCount : consumed + ring.count.val = produced

def Queue.pop {N : Nat} (q : Queue N) (h : 0 < q.ring.count.val) : Queue N where
  ring := q.ring.take h
  consumed := q.consumed + 1
  produced := q.produced
  headAligned := by
    change (q.ring.head.val + 1) % N = (q.consumed + 1) % N
    rw [q.headAligned, Nat.mod_add_mod]
  liveCount := by
    change q.consumed + 1 + (q.ring.count.val - 1) = q.produced
    have := q.liveCount
    omega

def Queue.push {N : Nat} (q : Queue N) (id : UInt16) (h : q.ring.count.val < N) : Queue N where
  ring := q.ring.put id h
  consumed := q.consumed
  produced := q.produced + 1
  headAligned := q.headAligned
  liveCount := by
    change q.consumed + (q.ring.count.val + 1) = q.produced + 1
    have := q.liveCount
    omega

/-- Any power-of-two ring capacity (`N ∣ 2^64`) preserves exact hardware head alignment across 64-bit wraparound. -/
theorem machine_head {N : Nat} (hDiv : N ∣ 2 ^ 64) (q : Queue N) :
    (UInt64.ofNat q.consumed).toNat % N = q.ring.head.val := by
  rw [q.headAligned]
  change (q.consumed % 2 ^ 64) % N = q.consumed % N
  exact Nat.mod_mod_of_dvd q.consumed hDiv

structure Pair (N : Nat) where
  available : Queue N
  used : Queue N

def Pair.swap {N : Nat} (p : Pair N) : Pair N := ⟨p.used, p.available⟩

def Pair.move {N : Nat} (p : Pair N) (ready : 0 < p.available.ring.count.val)
    (room : p.used.ring.count.val < N) : Pair N :=
  ⟨p.available.pop ready, p.used.push p.available.ring.peek room⟩

def copies {N : Nat} (p : Pair N) (id : UInt16) : Nat :=
  p.available.ring.view.count id + p.used.ring.view.count id

theorem move_conserves {N : Nat} (p : Pair N) (ready : 0 < p.available.ring.count.val)
    (room : p.used.ring.count.val < N) (id : UInt16) :
    copies (p.move ready room) id = copies p id := by
  simp only [copies, Pair.move, Queue.pop, Queue.push, ring_put_fifo, List.count_append]
  rw [ring_take_fifo p.available.ring ready]
  simp [List.count_cons]
  omega

abbrev Pools (N : Nat) := Port → Pair N

def replace {N : Nat} (s : Pools N) (port : Port) (p : Pair N) : Pools N :=
  fun k => if k = port then p else s k

structure DevicePools (N : Nat) where
  queues : Pools N
  leases : Port → UInt16 → Option Lease

def submit {N : Nat} (s : DevicePools N) (k : Port) (ready : 0 < (s.queues k).available.ring.count.val)
    (room : (s.queues k).used.ring.count.val < N) : DevicePools N :=
  { s with queues := replace s.queues k ((s.queues k).move ready room) }

def complete {N : Nat} (s : DevicePools N) (k : Port) (ready : 0 < (s.queues k).used.ring.count.val)
    (room : (s.queues k).available.ring.count.val < N) : DevicePools N :=
  let p := s.queues k
  { queues := replace s.queues k ((p.swap.move ready room).swap)
    leases := fun port id => if port = k ∧ id = p.used.ring.peek then
      (s.leases port id).bind recycle else s.leases port id }

inductive Run {N : Nat} (initial : DevicePools N) : DevicePools N → Prop
  | boot : Run initial initial
  | submitOne {s} : Run initial s → (k : Port) →
      (ready : 0 < (s.queues k).available.ring.count.val) →
      (room : (s.queues k).used.ring.count.val < N) →
      (s.leases k (s.queues k).available.ring.peek).isSome = true →
      Run initial (submit s k ready room)
  | completeOne {s} : Run initial s → (k : Port) →
      (ready : 0 < (s.queues k).used.ring.count.val) →
      (room : (s.queues k).available.ring.count.val < N) →
      Run initial (complete s k ready room)

/-- **Ring slot conservation for arbitrary capacity `N`**:
every unbounded history of submissions and completions across RX, TX, and storage
preserves the exact multiplicity of every buffer ID. -/
theorem ring_ownership {N : Nat} {s f : DevicePools N} (h : Run s f) (k : Port) (id : UInt16) :
    copies (f.queues k) id = copies (s.queues k) id := by
  have swap (p : Pair N) : copies p.swap id = copies p id := Nat.add_comm _ _
  induction h with
  | boot => rfl
  | submitOne _ j ready room _ ih =>
    by_cases e : k = j
    · subst j; simpa [submit, replace, move_conserves] using ih
    · simpa [submit, replace, e] using ih
  | @completeOne prior _ j ready room ih =>
    by_cases e : k = j
    · subst j
      change copies (replace _ k _ k) id = _
      simp only [replace, ite_true, swap, move_conserves (prior.queues k).swap ready room, ih]
    · simpa [complete, replace, e] using ih

def resolve {N : Nat} (s : DevicePools N) (k : Port) (frame : ByteArray) (v : View) (i : Nat) : Option UInt8 := do
  guard ((s.queues k).used.ring.view.contains v.slot)
  let current ← s.leases k v.slot
  readByte frame current v i

private theorem clocks_mono {N : Nat} {s f : DevicePools N} (h : Run s f) (k : Port) (id : UInt16) {last : Lease}
    (live : f.leases k id = some last) :
    ∃ first, s.leases k id = some first ∧ serial first ≤ serial last := by
  induction h generalizing last with
  | boot => exact ⟨_, live, Nat.le_refl _⟩
  | submitOne _ _ _ _ _ ih => exact ih live
  | completeOne _ j ready room ih =>
    simp only [complete] at live
    split at live
    · obtain ⟨prev, before, after⟩ := Option.bind_eq_some_iff.mp live
      obtain ⟨first, init, hth⟩ := ih before
      exact ⟨_, init, by rw [recycle_advances after]; omega⟩
    · exact ih live

/-- After ownership returns to the available queue, even a later re-submission
of the same physical slot cannot revalidate the old slice. -/
theorem released_view_stays_stale {N : Nat} (s : DevicePools N) (k : Port)
    (ready : 0 < (s.queues k).used.ring.count.val)
    (room : (s.queues k).available.ring.count.val < N) (v : View)
    (slot : v.slot = (s.queues k).used.ring.peek) (old : s.leases k v.slot = some v.toLease)
    {f : DevicePools N} (run : Run (complete s k ready room) f) (frame : ByteArray) (i : Nat) :
    resolve f k frame v i = none := by
  cases eq : f.leases k v.slot with
  | none => simp [resolve, eq, guard, bind, Option.bind]; split <;> rfl
  | some current =>
    obtain ⟨prev, after, le⟩ := clocks_mono run k v.slot eq
    simp only [complete, slot.symm, and_self, ite_true, old, Option.bind_some] at after
    have advances := recycle_advances after
    have ne : v.toLease ≠ current := by
      intro same
      have e := congrArg serial same
      omega
    simp [resolve, eq, readByte, ne, guard, bind, Option.bind]
    split <;> rfl

/-! ## Unified CPU Page-Table + `.dev` SMMU Stream Confinement -/

/-- Full system address-space confinement policy covering BOTH CPU PDs and `.dev` SMMU streams. -/
structure Layout where
  drivers : List PdId
  verifier : PdId
  descriptors : List Nat
  ingress : List Nat
  privateData : List Nat
  kernelCode : List Nat
  persistWal : List Nat
  egressOutbox : List Nat
  smmuManifest : SmmuManifest

/-- Every `.dev sid` kernel mapping MUST belong to an authorized, non-wildcard stream in
`smmuManifest`, translate inside a declared `Stage2DmaRegion` with matching write permission,
target only DMA-permitted descriptor/ring/WAL/egress frames, and NEVER touch verifier-private
or kernel-code frames. -/
def devMappingAuthorized (l : Layout) (sid : Nat) (m : Mapping) : Bool :=
  l.smmuManifest.defaultDeny &&
  decide (sid ≠ 0 ∧ sid ≠ wildcardStreamId.toNat) &&
  !l.privateData.contains m.pfn &&
  !l.kernelCode.contains m.pfn &&
  (!l.egressOutbox.contains m.pfn || !m.writable) &&
  (l.descriptors.contains m.pfn || l.ingress.contains m.pfn ||
    l.persistWal.contains m.pfn || l.egressOutbox.contains m.pfn) &&
  l.smmuManifest.streams.any fun pt =>
    pt.streamId.toNat == sid &&
    pt.regions.any fun reg =>
      decide (reg.iova.toNat ≤ m.vpage * pageSize ∧
        (m.vpage + 1) * pageSize ≤ reg.iova.toNat + reg.size.toNat ∧
        reg.paddr.toNat + (m.vpage * pageSize - reg.iova.toNat) = m.pfn * pageSize) &&
      (!m.writable || reg.perm.allowsWrite)

/-- Unified CPU + SMMU `.dev` mapping confinement check (zero `.dev` bypasses!). -/
def systemLayout (l : Layout) (maps : List Mapping) : Bool :=
  maps.all fun m => match m.space with
    | .dev sid => devMappingAuthorized l sid m
    | .cpu pd =>
      (!l.drivers.contains pd || (l.descriptors.contains m.pfn &&
        !l.ingress.contains m.pfn && !l.privateData.contains m.pfn && !l.kernelCode.contains m.pfn)) &&
      (!l.ingress.contains m.pfn || (pd == l.verifier && !m.writable)) &&
      (!l.privateData.contains m.pfn || pd == l.verifier) &&
      (!l.kernelCode.contains m.pfn || !m.writable)

theorem driver_descriptor_only {l : Layout} {maps : List Mapping} {pd : PdId} {va : Nat} {wr : Bool} {pa : Nat}
    (ok : systemLayout l maps = true) (driver : pd ∈ l.drivers)
    (access : translate maps (.cpu pd) va wr = some pa) :
    pa / pageSize ∈ l.descriptors ∧ pa / pageSize ∉ l.ingress ∧
    pa / pageSize ∉ l.privateData ∧ pa / pageSize ∉ l.kernelCode := by
  obtain ⟨m, look, _, rfl⟩ := translate_some access
  obtain ⟨mem, space, _⟩ := lookupMap_some look
  have hm := List.all_eq_true.mp ok m mem
  simp [space, driver] at hm
  simpa [and_assoc, page_of_addr _ _ (Nat.mod_lt va (by decide : 0 < pageSize))] using hm.1.1.1

theorem ingress_readonly {l : Layout} {maps : List Mapping} {pd : PdId} {va : Nat} {wr : Bool} {pa : Nat}
    (ok : systemLayout l maps = true) (access : translate maps (.cpu pd) va wr = some pa)
    (data : pa / pageSize ∈ l.ingress) : pd = l.verifier ∧ wr = false := by
  obtain ⟨m, look, write, rfl⟩ := translate_some access
  obtain ⟨mem, space, _⟩ := lookupMap_some look
  rw [page_of_addr _ _ (Nat.mod_lt va (by decide : 0 < pageSize))] at data
  have hm := List.all_eq_true.mp ok m mem
  simp [space, data] at hm
  exact ⟨hm.1.1.2.1, by cases wr <;> simp_all⟩

/-- **SMMU `.dev` stream DMA confinement**:
every physical translation performed by ANY `.dev sid` device stream in the kernel mapping table
belongs to an authorized `SmmuDmaConfinement` stream & region with matching write permission,
targets only authorized DMA frames, and NEVER aliases verifier-private or kernel-code frames. -/
theorem dev_dma_confined {l : Layout} {maps : List Mapping} {sid va : Nat} {wr : Bool} {pa : Nat}
    (ok : systemLayout l maps = true)
    (access : translate maps (.dev sid) va wr = some pa) :
    l.smmuManifest.defaultDeny = true ∧
    sid ≠ 0 ∧ sid ≠ wildcardStreamId.toNat ∧
    pa / pageSize ∉ l.privateData ∧ pa / pageSize ∉ l.kernelCode ∧
    (wr = true → pa / pageSize ∉ l.egressOutbox) ∧
    (pa / pageSize ∈ l.descriptors ∨ pa / pageSize ∈ l.ingress ∨
      pa / pageSize ∈ l.persistWal ∨ pa / pageSize ∈ l.egressOutbox) ∧
    ∃ pt ∈ l.smmuManifest.streams, pt.streamId.toNat = sid ∧
      ∃ reg ∈ pt.regions,
        reg.iova.toNat ≤ va ∧ va < reg.iova.toNat + reg.size.toNat ∧
        reg.paddr.toNat + (va - reg.iova.toNat) = pa ∧
        (wr = true → reg.perm.allowsWrite = true) := by
  obtain ⟨m, look, hwr, rfl⟩ := translate_some access
  obtain ⟨mem, space, hvp⟩ := lookupMap_some look
  have hm := List.all_eq_true.mp ok m mem
  rw [space] at hm
  simp only [devMappingAuthorized, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨hdeny, hsid0, hsidW⟩, hnotPriv⟩, hnotKern⟩, hegress⟩, hallowed⟩,
    pt, hptMem, hptSid, reg, hregMem, ⟨hlo, hhi, hpa⟩, hperm⟩ := hm
  have hnp : m.pfn ∉ l.privateData := fun h => by
    rw [List.contains_iff_mem.mpr h] at hnotPriv; cases hnotPriv
  have hnk : m.pfn ∉ l.kernelCode := fun h => by
    rw [List.contains_iff_mem.mpr h] at hnotKern; cases hnotKern
  have hmod : va % pageSize < pageSize := Nat.mod_lt va (by decide : 0 < pageSize)
  have hdiv : (m.pfn * pageSize + va % pageSize) / pageSize = m.pfn := page_of_addr m.pfn _ hmod
  have hva : va = m.vpage * pageSize + va % pageSize := by
    rw [hvp, Nat.mul_comm]; exact (Nat.div_add_mod va pageSize).symm
  rw [Nat.add_mul, Nat.one_mul] at hhi
  refine ⟨hdeny, hsid0, hsidW, by rw [hdiv]; exact hnp, by rw [hdiv]; exact hnk,
    fun hw => ?_, ?_, pt, hptMem, hptSid, reg, hregMem, by omega, by omega, by omega, fun hw => ?_⟩
  · rw [hdiv]
    rcases hegress with hne | hnw
    · intro hm; rw [List.contains_iff_mem.mpr hm] at hne; cases hne
    · have := hwr hw; rw [this] at hnw; cases hnw
  · rw [hdiv]
    rcases hallowed with ((h | h) | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · rcases hperm with hnw | haw
    · have := hwr hw; rw [this] at hnw; cases hnw
    · exact haw

/-- Refusal witness: any `.dev` mapping targeting a verifier-private frame is rejected by `systemLayout`. -/
theorem systemLayout_refuses_dev_private {l : Layout} {maps : List Mapping} {m : Mapping} {sid : Nat}
    (hm : m ∈ maps) (hdev : m.space = .dev sid) (hpriv : m.pfn ∈ l.privateData) :
    systemLayout l maps = false := by
  cases h : systemLayout l maps with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp h m hm
    rw [hdev] at hall
    simp [devMappingAuthorized, hpriv] at hall

/-- Refusal witness: any `.dev` mapping for an undeclared SMMU stream is rejected by `systemLayout`. -/
theorem systemLayout_refuses_unmapped_stream {l : Layout} {maps : List Mapping} {m : Mapping} {sid : Nat}
    (hm : m ∈ maps) (hdev : m.space = .dev sid)
    (hunmapped : ∀ pt ∈ l.smmuManifest.streams, pt.streamId.toNat ≠ sid) :
    systemLayout l maps = false := by
  cases h : systemLayout l maps with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp h m hm
    rw [hdev] at hall
    simp only [devMappingAuthorized, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hall
    obtain ⟨pt, hpt, hsid, _⟩ := hall.2
    exact absurd hsid (hunmapped pt hpt)

/-- Inhabited multi-capacity (`N = 16`) queue witness proving arbitrary-`N` ring wraparound & conservation. -/
private def fullQueue16 : Queue 16 :=
  ⟨⟨Vector.ofFn (fun i : Fin 16 => UInt16.ofNat i.val), ⟨0, by decide⟩, ⟨16, by decide⟩⟩,
    2 ^ 64, 2 ^ 64 + 16, by decide, by decide⟩
private def emptyQueue16 : Queue 16 :=
  ⟨⟨Vector.replicate 16 0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩, 0, 0, rfl, rfl⟩
private def bootPools16 : DevicePools 16 :=
  ⟨fun _ => ⟨fullQueue16, emptyQueue16⟩, fun _ id => some ⟨7, 9, id, 0xffffffffffffffff⟩⟩

theorem ring_pools16_inhabited :
    ∃ s f : DevicePools 16, Run s f ∧
      (f.queues .storage).used.ring.peek = 1 ∧ (f.queues .rx).used.ring.peek = 0 := by
  let a := submit bootPools16 .storage (by decide) (by decide)
  let b := submit a .storage (by decide) (by decide)
  let c := complete b .storage (by decide) (by decide)
  have ha : Run bootPools16 a := .submitOne .boot .storage _ _ (by decide)
  have hb : Run bootPools16 b := .submitOne ha .storage _ _ (by decide)
  have hc : Run bootPools16 c := .completeOne hb .storage _ _
  exact ⟨bootPools16, _, .submitOne hc .rx (by decide) (by decide) (by decide), by decide, by decide⟩

end Obend.OS.SddfOwnership
