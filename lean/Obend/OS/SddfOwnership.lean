module
public import Obend.Lower.Pancake.BorrowedTurn
public import Obend.OS.SmmuDmaConfinement
import all Obend.Lower.Pancake.BorrowedTurn
import all Obend.Lower.Pancake.DragonStyleShard
import Obend.Tactic.Tooth

public section
namespace Obend.OS.SddfOwnership

open Obend.Lower.Pancake.DragonStyleShard
open Obend.Lower.Pancake.BorrowedTurn
open Sel4MicrokitKernel
open SmmuDmaConfinement

inductive Port | rx | tx | storage deriving DecidableEq, Repr

/-- The producer and consumer sequence numbers live in the proof. Only four cells
and bounded indices are needed on the shared-memory side. -/
structure Queue where
  ring : Ring UInt16
  consumed : Nat
  produced : Nat
  headAligned : ring.head.val = consumed % 4
  liveCount : consumed + ring.count.val = produced

def Queue.pop (q : Queue) (h : 0 < q.ring.count.val) : Queue where
  ring := q.ring.take h
  consumed := q.consumed+1
  produced := q.produced
  headAligned := by change (q.ring.head.val + 1) % 4 = _; rw [q.headAligned]; omega
  liveCount := by change q.consumed+1+(q.ring.count.val-1) = _; have := q.liveCount; omega

def Queue.push (q : Queue) (id : UInt16) (h : q.ring.count.val < 4) : Queue where
  ring := q.ring.put id h
  consumed := q.consumed
  produced := q.produced+1
  headAligned := q.headAligned
  liveCount := by change q.consumed+(q.ring.count.val+1) = _; have := q.liveCount; omega

theorem machine_head (q : Queue) : (UInt64.ofNat q.consumed).toNat % 4 = q.ring.head.val := by
  rw [q.headAligned]
  change (q.consumed % (2^64)) % 4 = _
  omega

structure Pair where
  available : Queue
  used : Queue

def Pair.swap (p : Pair) : Pair := ⟨p.used,p.available⟩
def Pair.move (p : Pair) (ready : 0 < p.available.ring.count.val)
    (room : p.used.ring.count.val < 4) : Pair :=
  ⟨p.available.pop ready,p.used.push p.available.ring.peek room⟩

def copies (p : Pair) (id : UInt16) :=
  p.available.ring.view.count id + p.used.ring.view.count id

theorem move_conserves (p : Pair) (ready room) (id : UInt16) :
    copies (p.move ready room) id = copies p id := by
  simp only [copies, Pair.move, Queue.pop, Queue.push, ring_put_fifo, List.count_append]
  rw [ring_take_fifo p.available.ring ready]
  simp [List.count_cons]
  omega

abbrev Pools := Port → Pair
def replace (s : Pools) (port : Port) (p : Pair) : Pools :=
  fun k => if k = port then p else s k

structure DevicePools where
  queues : Pools
  leases : Port → UInt16 → Option Lease

def submit (s : DevicePools) (k : Port) (ready : 0 < (s.queues k).available.ring.count.val)
    (room : (s.queues k).used.ring.count.val < 4) : DevicePools :=
  {s with queues := replace s.queues k ((s.queues k).move ready room)}

def complete (s : DevicePools) (k : Port) (ready : 0 < (s.queues k).used.ring.count.val)
    (room : (s.queues k).available.ring.count.val < 4) : DevicePools :=
  let p := s.queues k
  { queues := replace s.queues k ((p.swap.move ready room).swap)
    leases := fun port id => if port = k ∧ id = p.used.ring.peek then
      (s.leases port id).bind recycle else s.leases port id }

inductive Run (initial : DevicePools) : DevicePools → Prop
  | boot : Run initial initial
  | submitOne {s} : Run initial s → (k : Port) → (ready : _) → (room : _) →
      (s.leases k (s.queues k).available.ring.peek).isSome = true → Run initial (submit s k ready room)
  | completeOne {s} : Run initial s → (k : Port) → (ready : _) → (room : _) → Run initial (complete s k ready room)

theorem ring_ownership {s f} (h : Run s f) (k : Port) (id : UInt16) :
    copies (f.queues k) id = copies (s.queues k) id := by
  have swap (p : Pair) : copies p.swap id = copies p id := Nat.add_comm _ _
  induction h with
  | boot => rfl
  | submitOne _ j ready room _ ih =>
    by_cases e : k = j
    · subst j; simpa [submit,replace, move_conserves] using ih
    · simpa [submit,replace,e] using ih
  | @completeOne prior _ j ready room ih =>
    by_cases e : k = j
    · subst j
      change copies (replace _ k _ k) id = _
      simp only [replace,ite_true,swap,move_conserves (prior.queues k).swap ready room,ih]
    · simpa [complete,replace,e] using ih

def resolve (s : DevicePools) (k : Port) (frame : ByteArray) (v : View) (i : Nat) : Option UInt8 := do
  guard ((s.queues k).used.ring.view.contains v.slot)
  let current ← s.leases k v.slot
  readByte frame current v i

private theorem clocks_mono {s f} (h : Run s f) (k : Port) (id : UInt16) {last}
    (live : f.leases k id = some last) :
    ∃ first, s.leases k id = some first ∧ serial first ≤ serial last := by
  induction h generalizing last with
  | boot => exact ⟨_,live,Nat.le_refl _⟩
  | submitOne _ _ _ _ _ ih => exact ih live
  | completeOne _ j ready room ih =>
    simp only [complete] at live
    split at live
    · obtain ⟨prev,before,after⟩ := Option.bind_eq_some_iff.mp live
      obtain ⟨first,init,hth⟩ := ih before
      exact ⟨_,init,by rw [recycle_advances after]; omega⟩
    · exact ih live

/-- After ownership returns to the available queue, even a later re-submission
of the same physical slot cannot revalidate the old slice. A permanently
retired slot remains accounted for and cannot be submitted. -/
theorem released_view_stays_stale (s : DevicePools) (k : Port) (ready room) (v : View)
    (slot : v.slot = (s.queues k).used.ring.peek) (old : s.leases k v.slot = some v.toLease)
    {f} (run : Run (complete s k ready room) f) (frame : ByteArray) (i : Nat) :
    resolve f k frame v i = none := by
  cases eq : f.leases k v.slot with
  | none => simp [resolve,eq,guard,bind,Option.bind]; split <;> rfl
  | some current =>
    obtain ⟨prev,after,le⟩ := clocks_mono run k v.slot eq
    simp only [complete,slot.symm,and_self,ite_true,old,Option.bind_some] at after
    have advances := recycle_advances after
    have ne : v.toLease ≠ current := by
      intro same
      have e := congrArg serial same
      omega
    simp [resolve,eq,readByte,ne,guard,bind,Option.bind]
    split <;> rfl

/-- Validate actual CPU page-table entries. Driver data apertures and virtual
aliases of payload pages are forbidden even if a driver has a descriptor cap. -/
structure Layout where
  drivers : List PdId
  verifier : PdId
  descriptors : List Nat
  ingress : List Nat
  privateData : List Nat

def cpuLayout (l : Layout) (maps : List Mapping) : Bool :=
  maps.all fun m => match m.space with
    | .dev _ => true
    | .cpu pd =>
      (!l.drivers.contains pd || (l.descriptors.contains m.pfn &&
        !l.ingress.contains m.pfn && !l.privateData.contains m.pfn)) &&
      (!l.ingress.contains m.pfn || (pd == l.verifier && !m.writable)) &&
      (!l.privateData.contains m.pfn || pd == l.verifier)

theorem driver_descriptor_only {l maps pd va wr pa}
    (ok : cpuLayout l maps = true) (driver : pd ∈ l.drivers)
    (access : translate maps (.cpu pd) va wr = some pa) :
    pa / pageSize ∈ l.descriptors ∧ pa / pageSize ∉ l.ingress ∧ pa / pageSize ∉ l.privateData := by
  obtain ⟨m,look,_,rfl⟩ := translate_some access
  obtain ⟨mem,space,_⟩ := lookupMap_some look
  have hm := List.all_eq_true.mp ok m mem
  simp [space,driver] at hm
  simpa [and_assoc, page_of_addr _ _ (Nat.mod_lt va (by decide : 0 < pageSize))] using hm.1.1

theorem ingress_readonly {l maps pd va wr pa}
    (ok : cpuLayout l maps = true) (access : translate maps (.cpu pd) va wr = some pa)
    (data : pa / pageSize ∈ l.ingress) : pd = l.verifier ∧ wr = false := by
  obtain ⟨m,look,write,rfl⟩ := translate_some access
  obtain ⟨mem,space,_⟩ := lookupMap_some look
  rw [page_of_addr _ _ (Nat.mod_lt va (by decide : 0 < pageSize))] at data
  have hm := List.all_eq_true.mp ok m mem
  simp [space,data] at hm
  exact ⟨hm.1.2.1,by cases wr <;> simp_all⟩

private def fullQueue : Queue :=
  ⟨⟨#v[0,1,2,3],0,4⟩,2^64,2^64+4,by decide,by decide⟩
private def emptyQueue : Queue := ⟨⟨#v[0,0,0,0],0,0⟩,0,0,rfl,rfl⟩
private def bootPools : DevicePools :=
  ⟨fun _ => ⟨fullQueue,emptyQueue⟩,fun _ id => some ⟨7,9,id,0xffffffffffffffff⟩⟩

private example : ∃ f, Run bootPools f ∧ (f.queues .storage).used.ring.peek = 1 ∧
    (f.queues .rx).used.ring.peek = 0 := by
  let a := submit bootPools .storage (by decide) (by decide)
  let b := submit a .storage (by decide) (by decide)
  let c := complete b .storage (by decide) (by decide)
  have ha : Run bootPools a := .submitOne .boot .storage _ _ (by decide)
  have hb : Run bootPools b := .submitOne ha .storage _ _ (by decide)
  have hc : Run bootPools c := .completeOne hb .storage _ _
  exact ⟨_, .submitOne hc .rx (by decide) (by decide) (by decide), by decide, by decide⟩

#tooth move_conserves by mutation Pair.move := fun p ready _ => {p with available := p.available.pop ready}
#tooth driver_descriptor_only by mutation cpuLayout := fun _ _ => true

end Obend.OS.SddfOwnership
