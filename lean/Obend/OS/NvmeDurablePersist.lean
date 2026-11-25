module
import Obend.Tactic.Tooth
public section
namespace Obend.OS.NvmeDurablePersist

structure Record where
  principal : Nat
  nonce : Nat
  nullifier : Nat
  cost : Nat
  payload : ByteArray
  deriving DecidableEq, Inhabited

def spent (xs : List Record) (principal : Nat) :=
  ((xs.filter (fun r => r.principal == principal)).map Record.cost).sum

def remaining (xs : List Record) (principal : Nat) := 20 - spent xs principal

inductive Decision | refuse | fresh | cached (generation : Nat) deriving DecidableEq

/-- Receipts are one-based generation numbers in this single namespace. The
authenticated channel principal is checked before any cached receipt is disclosed. -/
def request (xs : List Record) (principal : Nat) (r : Record) : Decision :=
  if r.principal ≠ principal then .refuse
  else if r ∈ xs then .cached (xs.idxOf r + 1)
  else if xs.length < 8 ∧ 0 < r.cost ∧ r.cost ≤ remaining xs principal ∧
    xs.all (fun p => p.nullifier < r.nullifier && !(p.principal == principal && p.nonce == r.nonce))
    ∧ 0 < r.nullifier then .fresh else .refuse

theorem replay (xs : List Record) {r : Record} (h : r ∈ xs) :
    request xs r.principal r = .cached (xs.idxOf r + 1) := by simp [request,h]

structure Header where
  generation : UInt64
  complement : UInt64
  crc32c : UInt32
  deriving DecidableEq

private def crcOctet (crc : UInt32) (byte : UInt8) : UInt32 := Id.run do
  let mut c := crc ^^^ byte.toUInt32
  for _ in [:8] do
    c := (c >>> 1) ^^^ (if c &&& 1 = 1 then 0x82f63b78 else 0)
  return c

/-- CRC-32C over little-endian generation and complement, with the standard
all-ones initialization and final xor. -/
private def headerCrc (g comp : UInt64) : UInt32 := Id.run do
  let mut c : UInt32 := 0xffffffff
  for w in #[g,comp] do
    for i in [:8] do
      c := crcOctet c (w >>> (8*i).toUInt64).toUInt8
  return c ^^^ 0xffffffff

def mkHeader (g : UInt64) : Header :=
  let comp := g ^^^ 0xffffffffffffffff
  ⟨g,comp,headerCrc g comp⟩

/-- Namespace-relative LBAs. The controller's zero-based AWUPF field is
decoded before the appliance opens the namespace. The header always occupies
one whole logical block, so it cannot cross a namespace atomic boundary. -/
structure Geometry where
  sectors : Nat
  bytesPerLba : Nat
  awupf : UInt16
  ctrlLba : Nat
  walBase : Nat
  deriving DecidableEq

def Geometry.usable (g : Geometry) : Bool :=
  decide (512 ≤ g.bytesPerLba ∧ 1 ≤ g.awupf.toNat+1 ∧ g.ctrlLba < g.sectors ∧
    g.walBase + 16 ≤ g.sectors ∧ (g.ctrlLba < g.walBase ∨ g.walBase + 16 ≤ g.ctrlLba))

def walLba (g : Geometry) (i : Nat) (block : Fin 2) := g.walBase + 2*i + block.val

theorem wal_confined {g : Geometry} (ok : g.usable = true) (i : Fin 8) (block : Fin 2) :
    walLba g i block < g.sectors ∧ walLba g i block ≠ g.ctrlLba := by
  simp only [Geometry.usable,decide_eq_true_eq] at ok
  unfold walLba
  have := i.isLt
  have := block.isLt
  omega

def hostedGeometry : Geometry := ⟨17,512,0,0,1⟩

/-- Each WAL index denotes two separately writable DMA blocks. A torn pair
may decode to arbitrary metadata and payload. Only the frontier is writable.
The header occupies one aligned LBA within the advertised power-fail atomic unit. -/
structure Disk where
  ctrl : Header
  wal : Nat → Record
  geometry : Geometry := hostedGeometry

def Disk.image (d : Disk) : List Record :=
  List.ofFn (n := d.ctrl.generation.toNat) fun i => d.wal i.val

def recover (d : Disk) : Option (List Record) :=
  if d.ctrl = mkHeader d.ctrl.generation ∧ d.ctrl.generation.toNat ≤ 8 then some d.image else none

def writeFrontier (d : Disk) (r : Record) : Disk :=
  { d with wal := fun i => if i = d.ctrl.generation.toNat then r else d.wal i }

def install (d : Disk) : Disk := {d with ctrl := mkHeader (d.ctrl.generation + 1)}

theorem frontier_invisible (d : Disk) (r : Record) : (writeFrontier d r).image = d.image := by
  unfold Disk.image
  apply congrArg List.ofFn
  funext i
  have h : i.val < d.ctrl.generation.toNat := i.isLt
  simp [writeFrontier, Nat.ne_of_lt h]

theorem install_extends (d : Disk) (room : d.ctrl.generation.toNat < 8) :
    (install d).image = d.image ++ [d.wal d.ctrl.generation.toNat] := by
  have e : (d.ctrl.generation+1).toNat = d.ctrl.generation.toNat+1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  change (List.ofFn (n := (d.ctrl.generation+1).toNat) fun i => d.wal i.val) = _
  rw [e, List.ofFn_succ_last]
  rfl

inductive Phase
  | idle
  | dma (r : Record) (metaComplete dataComplete : Bool)
  | flushed (r : Record)
  | waitFuaCompletion (r : Record)
  | dispatchable (r : Record)

inductive Opcode | write | flush deriving DecidableEq, Repr

/-- Descriptor fields consumed by the storage virtualiser. NLB is zero-based.
FLUSH has no data transfer. Unused fields are canonical zero in this interface. -/
structure Command where
  opcode : Opcode
  nsid : UInt32
  slba : Nat
  nlb : UInt16
  fua : Bool
  deriving DecidableEq, Repr

inductive Action | metadata | data | barrier | commit deriving DecidableEq, Repr

def commandFor (d : Disk) : Action → Command
  | .metadata => ⟨.write,1,walLba d.geometry d.ctrl.generation.toNat 0,0,false⟩
  | .data => ⟨.write,1,walLba d.geometry d.ctrl.generation.toNat 1,0,false⟩
  | .barrier => ⟨.flush,1,0,0,false⟩
  | .commit => ⟨.write,1,d.geometry.ctrlLba,0,true⟩

/-- The queue owner couples the actual completion descriptor to its phase.
The data and metadata commands may complete in either order. -/
def classify (d : Disk) (p : Phase) (q : Command) : Option Action :=
  match p with
  | .dma _ a b =>
    if !a && q == commandFor d .metadata then some .metadata
    else if !b && q == commandFor d .data then some .data
    else if a && b && q == commandFor d .barrier then some .barrier else none
  | .flushed _ => if q == commandFor d .commit then some .commit else none
  | _ => none

theorem classification_exact {d p q act} (h : classify d p q = some act) :
    q = commandFor d act ∧
    (act = .commit → ∃ r, p = .flushed r) ∧
    (act = .barrier → ∃ r, p = .dma r true true) := by
  cases p <;> simp only [classify] at h <;> try contradiction
  all_goals repeat' split at h <;> try contradiction
  all_goals cases h <;> simp_all

/-- WAL-DMA completions concern the volatile cache. Eviction or a power cut can
expose any torn contents at the frontier before a successful FLUSH. The FUA
linearization point and observation of its completion are separate events. -/
inductive Run (permit : List Record → Record → Prop) :
    Disk → Phase → List Record → List (Nat × Record) → List Nat → Prop
  | boot (g : Geometry) : g.usable = true → (junk : Nat → Record) →
      Run permit ⟨mkHeader 0,junk,g⟩ .idle [] [] []
  | beginTurn {d xs tx issues r} : Run permit d .idle xs tx issues →
      request d.image r.principal r = .fresh → permit d.image r →
      Run permit d (.dma r false false) xs tx issues
  | metaDone {d xs tx issues r b} : Run permit d (.dma r false b) xs tx issues →
      (q : Command) → classify d (.dma r false b) q = some .metadata →
      Run permit d (.dma r true b) xs tx issues
  | dataDone {d xs tx issues r b} : Run permit d (.dma r b false) xs tx issues →
      (q : Command) → classify d (.dma r b false) q = some .data →
      Run permit d (.dma r b true) xs tx issues
  | evict {d xs tx issues r a b} : Run permit d (.dma r a b) xs tx issues → (torn : Record) →
      Run permit (writeFrontier d torn) (.dma r a b) xs tx issues
  | flush {d xs tx issues r} : Run permit d (.dma r true true) xs tx issues →
      (q : Command) → classify d (.dma r true true) q = some .barrier →
      Run permit (writeFrontier d r) (.flushed r) xs tx issues
  | fua {d xs tx issues r} : Run permit d (.flushed r) xs tx issues →
      (q : Command) → classify d (.flushed r) q = some .commit →
      Run permit (install d) (.waitFuaCompletion r) (xs ++ [r]) tx issues
  | completion {d xs tx issues r} : Run permit d (.waitFuaCompletion r) xs tx issues →
      Run permit d (.dispatchable r) xs tx issues
  | dispatch {d xs tx issues r} : Run permit d (.dispatchable r) xs tx issues →
      Run permit d .idle xs tx (r.nullifier :: issues)
  | rejectedCommand {d p xs tx issues} : Run permit d p xs tx issues →
      (q : Command) → classify d p q = none → Run permit d p xs tx issues
  | powerCut {d p xs tx issues} : Run permit d p xs tx issues → Run permit d .idle xs tx issues
  | send {d xs tx issues caller r i} : Run permit d .idle xs tx issues →
      request d.image caller r = .cached (i+1) → Run permit d .idle xs ((i,r)::tx) issues
  | refused {d xs tx issues caller r} : Run permit d .idle xs tx issues →
      request d.image caller r = .refuse → Run permit d .idle xs tx issues

inductive Accepted (permit : List Record → Record → Prop) : List Record → Prop
  | nil : Accepted permit []
  | snoc {xs r} : Accepted permit xs → permit xs r → request xs r.principal r = .fresh →
      Accepted permit (xs ++ [r])

private def pending (permit : List Record → Record → Prop) (d : Disk) (xs : List Record) (issues : List Nat) :
    Phase → Prop
  | .idle => True
  | .waitFuaCompletion r | .dispatchable r => r ∈ xs ∧ r.nullifier ∉ issues
  | .dma r _ _ => permit xs r ∧ request xs r.principal r = .fresh
  | .flushed r => (permit xs r ∧ request xs r.principal r = .fresh) ∧ d.wal xs.length = r

private theorem fresh_room {xs p r} (h : request xs p r = .fresh) : xs.length < 8 := by
  unfold request at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all

private theorem fresh_after {xs p r} (h : request xs p r = .fresh) :
    ∀ old ∈ xs, old.nullifier < r.nullifier := by
  unfold request at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i fresh
  intro old mem
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp fresh.2.2.2.1 old mem)).1

theorem accepted_nodup {permit xs} (h : Accepted permit xs) :
    (xs.map Record.nullifier).Nodup ∧ xs.Nodup := by
  induction h with
  | nil => simp
  | @snoc xs r _ _ fresh ih =>
    have prior := fresh_after fresh
    have absent : ∀ a ∈ xs, a.nullifier ≠ r.nullifier := fun a ha => Nat.ne_of_lt (prior a ha)
    have newId : r.nullifier ∉ xs.map Record.nullifier := by
      rintro mem
      obtain ⟨a, ha, eq⟩ := List.mem_map.mp mem
      exact absent a ha eq
    have newRecord : r ∉ xs := fun mem => absent r mem rfl
    simp_all [List.nodup_append]
    rintro a ha rfl
    exact newRecord ha

private theorem fresh_cost {xs p r} (h : request xs p r = .fresh) :
    r.cost ≤ remaining xs p := by
  unfold request at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i fresh
  exact fresh.2.2.1

theorem accepted_budget {permit xs} (h : Accepted permit xs) (p : Nat) : spent xs p ≤ 20 := by
  induction h with
  | nil => simp [spent]
  | @snoc xs r _ _ fresh ih =>
    by_cases eq : r.principal = p
    · subst p
      have cost := fresh_cost fresh
      unfold remaining at cost
      have sum : spent (xs ++ [r]) r.principal = spent xs r.principal + r.cost := by simp [spent]
      omega
    · simpa [spent,eq] using ih

/-- Rebuild a principal's latest receipt generation by scanning the immutable
prefix backwards. Zero denotes the genesis head. -/
def receiptHead (xs : List Record) (p : Nat) :=
  (xs.zipIdx.reverse.find? (fun e => e.1.principal == p)).map (fun e => e.2+1)

private theorem cached_at {xs p r i} (h : request xs p r = .cached (i+1)) :
    xs[i]? = some r := by
  unfold request at h
  split at h <;> try contradiction
  split at h
  next hr =>
    injection h with eq
    have hi : xs.idxOf r = i := by omega
    subst i
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hr)]
    exact congrArg some (List.getElem_idxOf _)
  next => split at h <;> contradiction

private structure Good (permit : List Record → Record → Prop) (d : Disk) (p : Phase)
    (xs : List Record) (tx : List (Nat × Record)) (issues : List Nat) : Prop where
  geometry : d.geometry.usable = true
  ctrl : d.ctrl = mkHeader d.ctrl.generation
  bound : d.ctrl.generation.toNat ≤ 8
  image : d.image = xs
  authorized : Accepted permit xs
  inflight : pending permit d xs issues p
  uniqueIssues : issues.Nodup
  issued : ∀ id ∈ issues, id ∈ xs.map Record.nullifier
  transmitted : ∀ z ∈ tx, xs[z.1]? = some z.2

private theorem run_good {permit d p xs tx issues} (trace : Run permit d p xs tx issues) :
    Good permit d p xs tx issues := by
  induction trace with
  | boot g ok junk => exact ⟨ok,rfl, by change 0 ≤ 8; decide, rfl, .nil, trivial, by simp, by simp, by simp⟩
  | beginTurn _ fresh auth ih =>
    exact {ih with inflight := ⟨ih.image ▸ auth, ih.image ▸ fresh⟩}
  | metaDone _ _ _ ih | dataDone _ _ _ ih => exact {ih with inflight := ih.inflight}
  | evict _ torn ih => exact {ih with image := (frontier_invisible _ _).trans ih.image}
  | @flush d xs tx issues r _ _ _ ih =>
    have len := congrArg List.length ih.image
    simp [Disk.image] at len
    exact {ih with
      image := (frontier_invisible _ _).trans ih.image
      inflight := ⟨ih.inflight, by simp [writeFrontier, len]⟩}
  | @fua d xs tx issues r _ _ _ ih =>
    obtain ⟨⟨auth, fresh⟩, wal⟩ := ih.inflight
    have room := fresh_room fresh
    have len := congrArg List.length ih.image
    simp [Disk.image] at len
    have small : d.ctrl.generation.toNat < 8 := by omega
    refine ⟨ih.geometry,rfl, ?_, ?_, .snoc ih.authorized auth fresh, ?_, ih.uniqueIssues, ?_, ?_⟩
    · simp [install,mkHeader,UInt64.toNat_add,Nat.mod_eq_of_lt (show d.ctrl.generation.toNat+1 < 2^64 by omega)]
      omega
    · rw [install_extends _ small, ih.image, len, wal]
    · refine ⟨by simp, ?_⟩
      intro mem
      obtain ⟨prior, hp, eq⟩ := List.mem_map.mp (ih.issued _ mem)
      exact (Nat.ne_of_lt (fresh_after fresh prior hp)) eq
    · intro id mem
      simp [ih.issued id mem]
    · intro z hz
      have prev := ih.transmitted z hz
      rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp prev).1), prev]
  | completion _ ih => exact {ih with inflight := ih.inflight}
  | dispatch _ ih =>
    refine {ih with inflight := trivial, uniqueIssues := List.nodup_cons.mpr ⟨ih.inflight.2,ih.uniqueIssues⟩,
                    issued := ?_}
    intro id mem
    rcases List.mem_cons.mp mem with rfl | old
    · exact List.mem_map.mpr ⟨_,ih.inflight.1,rfl⟩
    · exact ih.issued id old
  | powerCut _ ih => exact {ih with inflight := trivial}
  | send _ h ih =>
    refine {ih with transmitted := ?_}
    intro z hz
    rcases List.mem_cons.mp hz with rfl | old
    · exact ih.image ▸ cached_at h
    · exact ih.transmitted z old
  | refused _ _ ih | rejectedCommand _ _ _ ih => exact ih

/-- After every finite interleaving, including repeated cold resets, the decoded
physical WAL equals the authorized FUA prefix. Every historical TX receipt still
indexes its original record. Replaying that request selects the cached branch. -/
theorem durable_appliance {permit d p xs tx issues} (trace : Run permit d p xs tx issues) :
    recover d = some xs ∧ Accepted permit xs ∧ issues.Nodup ∧ (xs.map Record.nullifier).Nodup ∧
    ∀ z ∈ tx, xs[z.1]? = some z.2 ∧
      request d.image z.2.principal z.2 = .cached (z.1 + 1) := by
  have h := run_good trace
  refine ⟨by unfold recover; split; exact congrArg some h.image; exact False.elim (by rename_i bad; exact bad ⟨h.ctrl,h.bound⟩),
    h.authorized, h.uniqueIssues, (accepted_nodup h.authorized).1, ?_⟩
  intro z hz
  have atIndex := h.transmitted z hz
  refine ⟨atIndex, ?_⟩
  rw [h.image, replay xs (List.mem_of_getElem? atIndex)]
  obtain ⟨lt,eq⟩ := List.getElem?_eq_some_iff.mp atIndex
  rw [← eq, (accepted_nodup h.authorized).2.idxOf_getElem]

theorem cold_account {permit d p xs tx issues} (h : Run permit d p xs tx issues) (who : Nat) :
    (recover d).map (fun log => (log.map Record.nullifier, receiptHead log who, remaining log who)) =
      some (xs.map Record.nullifier, receiptHead xs who, 20-spent xs who) ∧ spent xs who ≤ 20 := by
  obtain ⟨cold,accepted,_⟩ := durable_appliance h
  exact ⟨by rw [cold]; rfl, accepted_budget accepted who⟩

theorem live_wal_confined {permit d r a b xs tx issues}
    (h : Run permit d (.dma r a b) xs tx issues) (block : Fin 2) :
    walLba d.geometry d.ctrl.generation.toNat block < d.geometry.sectors ∧
      walLba d.geometry d.ctrl.generation.toNat block ≠ d.geometry.ctrlLba := by
  have good := run_good h
  have room := fresh_room good.inflight.2
  have len := congrArg List.length good.image
  simp [Disk.image] at len
  exact wal_confined good.geometry ⟨d.ctrl.generation.toNat,by omega⟩ block

/-- A nonempty trace goes through both DMA completions, flush, atomic header
installation, a reset before the CQ entry, and a successful cold retry. -/
example (r : Record) (permit : List Record → Record → Prop) (auth : permit [] r)
    (fresh : request [] r.principal r = .fresh) :
    ∃ d, Run permit d .idle [r] [(0,r)] [] := by
  let d : Disk := ⟨mkHeader 0,fun _ => default,hostedGeometry⟩
  have boot : Run permit d .idle [] [] [] := .boot hostedGeometry (by decide) _
  have start := Run.beginTurn boot fresh auth
  have data := Run.dataDone start (commandFor d .data) (by simp [classify,commandFor,walLba,d,hostedGeometry,mkHeader])
  have metadata := Run.metaDone data (commandFor d .metadata) (by simp [classify])
  have flushed := Run.flush metadata (commandFor d .barrier) (by simp [classify])
  have installed := Run.fua flushed (commandFor (writeFrontier d r) .commit) (by simp [classify])
  have good := run_good installed
  refine ⟨_, Run.send (Run.powerCut installed) (caller := r.principal) ?_⟩
  rw [good.image]
  simp [request]

theorem fresh_fits (xs : List Record) (r : Record) (h : request xs r.principal r = .fresh) :
    spent xs r.principal + r.cost ≤ 20 := by
  have cost := fresh_cost h
  unfold remaining at cost
  have positive : 0 < r.cost := by
    unfold request at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i fresh
    exact fresh.2.1
  omega

#tooth classification_exact by mutation classify := fun _ _ _ => some .commit
#tooth fresh_fits by mutation remaining := fun _ _ => 20
#tooth frontier_invisible by mutation writeFrontier := fun d r => {d with wal := fun _ => r}
#tooth install_extends by mutation install := id

end Obend.OS.NvmeDurablePersist
