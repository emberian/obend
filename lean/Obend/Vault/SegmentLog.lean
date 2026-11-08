module

/-
# Byte-addressed log segments

The logical log is unchanged: the same records, checksums and receipt chain. Its bytes occupy
64 KiB files, with every file except the last full. The index is the byte address itself: division
selects a segment and remainder selects its byte. A checksummed index names the active segment.
Rollover clears the next block before publishing its index, then writes its payload; the preceding
segment is flushed first. An interrupted append leaves exactly a prefix, including a torn record.

`.obend/log` selects a generation atomically. Migration and compaction publish a complete new generation;
ordinary appends retain the generation and advance its active index only at segment boundaries. Old monolithic logs are read for migration.
`split_join`, `split_drop_join`, `holds_window` and `parse_window` connect the segmented byte windows
to the existing record/checkpoint semantics; no checksum or receipt check is bypassed.
-/

public import Obend.Vault.LogBytes
public import Obend.Vault.Cost

@[expose] public section
namespace Obend.Vault.SegmentLog
open Obend.Vault.Log Obend.Vault.LogBytes
set_option autoImplicit false

def capacity : Nat := 65536

/-- The specification of the physical segmentation, valid for every positive block size. -/
def split (n : Nat) (positive : 0 < n) (bs : Bytes) : List Bytes :=
  if bs.isEmpty then [] else bs.take n :: split n positive (bs.drop n)
termination_by bs.length
decreasing_by
  rename_i h
  have hn : bs ≠ [] := by simpa using h
  have hl := List.length_pos_iff.mpr hn
  simp only [List.length_drop]
  omega

theorem split_join (n : Nat) (positive : 0 < n) (bs : Bytes) :
    (split n positive bs).flatten = bs := by
  rw [split]
  split
  · rename_i h
    simpa using (List.isEmpty_iff.mp h).symm
  · simp only [List.flatten_cons, split_join n positive (bs.drop n), List.take_append_drop]
termination_by bs.length
decreasing_by
  rename_i h
  have hn : bs ≠ [] := by simpa using h
  have hl := List.length_pos_iff.mpr hn
  simp only [List.length_drop]
  omega

/-- Dropping whole files is dropping exactly that many block widths of logical bytes. -/
theorem split_drop_join (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    ((split n positive bs).drop k).flatten = bs.drop (k * n) := by
  induction k generalizing bs with
  | zero => simpa using split_join n positive bs
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e]
    · simp only [List.drop_succ_cons, ih, List.drop_drop]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

theorem split_take_join (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    ((split n positive bs).take k).flatten = bs.take (k * n) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e]
    · simp only [List.take_succ_cons, List.flatten_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm, List.take_add]

theorem split_drop (n : Nat) (positive : 0 < n) (bs : Bytes) (k : Nat) :
    (split n positive bs).drop k = split n positive (bs.drop (k * n)) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    rw [split]
    split
    · rename_i h
      have e := List.isEmpty_iff.mp h
      simp [e, split]
    · simp only [List.drop_succ_cons, ih, List.drop_drop]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

/-- Concatenate the selected disk blocks with a unique byte-array accumulator. -/
def joinFrom (acc : ByteArray) : List ByteArray → ByteArray
  | [] => acc
  | b :: bs => joinFrom (acc ++ b) bs

theorem joinFrom_eq (acc : ByteArray) (bs : List ByteArray) :
    (joinFrom acc bs).data.toList = acc.data.toList ++ (bs.map (·.data.toList)).flatten := by
  induction bs generalizing acc with
  | nil => simp [joinFrom]
  | cons b bs ih => simp [joinFrom, ih, List.append_assoc]

/-- The deployed assembler: load only the selected blocks, then clip their two boundary pieces. -/
def assemble (blocks : List ByteArray) (skip count : Nat) : ByteArray :=
  (joinFrom .empty blocks).extract skip (skip + count)

theorem assemble_eq (blocks : List ByteArray) (skip count : Nat) :
    (assemble blocks skip count).data.toList =
      ((blocks.map (·.data.toList)).flatten.drop skip).take count := by
  simp [assemble, List.extract, joinFrom_eq]

/-- Assembling a window of physical segments gives exactly the corresponding logical byte slice,
including short final blocks. This is the pure function used by `readRangeOf`. -/
theorem assemble_split (n : Nat) (positive : 0 < n) (bs : Bytes)
    (first blocks skip count : Nat) (covers : skip + count ≤ blocks * n) :
    (assemble (((split n positive bs).drop first).take blocks |>.map
      (fun b => (⟨b.toArray⟩ : ByteArray))) skip count).data.toList =
        (bs.drop (first * n + skip)).take count := by
  rw [assemble_eq]
  simp only [List.map_map, Function.comp_def]
  change (((((split n positive bs).drop first).take blocks).map (fun x => x)).flatten.drop skip).take count = _
  have identity : (((split n positive bs).drop first).take blocks).map (fun x : Bytes => x) =
      ((split n positive bs).drop first).take blocks := by
    induction ((split n positive bs).drop first).take blocks with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, ih]
  rw [identity]
  rw [split_drop, split_take_join, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-- The exact segment bounds used by `readRangeOf` cover and reconstruct every nonempty range. -/
theorem assemble_range (bs : Bytes) (start stop : Nat) (nonempty : start < stop) :
    (assemble (((split capacity (by decide) bs).drop (start / capacity)).take
      ((stop - 1) / capacity + 1 - start / capacity) |>.map
        (fun b => (⟨b.toArray⟩ : ByteArray))) (start % capacity) (stop - start)).data.toList =
      (bs.drop start).take (stop - start) := by
  have a := Nat.div_add_mod start capacity
  have b := Nat.div_add_mod (stop - 1) capacity
  have am := Nat.mod_lt start (show 0 < capacity by decide)
  have bm := Nat.mod_lt (stop - 1) (show 0 < capacity by decide)
  have cover : start % capacity + (stop - start) ≤
      ((stop - 1) / capacity + 1 - start / capacity) * capacity := by
    unfold capacity at *
    omega
  rw [assemble_split _ _ _ _ _ _ _ cover]
  congr 2
  simpa [Nat.mul_comm] using a

/-- Rebasing the checkpoint into a loaded suffix preserves its check against the whole log. -/
def localCheckpoint (ck : Checkpoint) (offset : Nat) : Checkpoint :=
  { ck with start := ck.start - offset, stop := ck.stop - offset }

theorem holds_window {W : Type} (Hb : Bytes → Bytes) (dec : Bytes → Option W)
    (ck : Checkpoint) (bs : Bytes) (offset : Nat) (ha : offset ≤ ck.start)
    (hb : ck.start ≤ ck.stop) :
    (localCheckpoint ck offset).holds Hb dec (bs.drop offset) = ck.holds Hb dec bs := by
  unfold Checkpoint.holds localCheckpoint
  simp only [List.drop_drop]
  have h1 : offset + (ck.start - offset) = ck.start := by omega
  have h2 : ck.stop - offset - (ck.start - offset) = ck.stop - ck.start := by omega
  rw [h1, h2]

/-- The deployed parser on the loaded suffix is exactly the old parser at its logical address. -/
theorem parse_window (Hb : Bytes → Bytes) (prev : Nat) (bs : Bytes) (offset : Nat)
    (window : ByteArray) (h : window.data.toList = bs.drop offset) :
    parseFrom Hb prev (bs.drop offset) =
      ((parseFromAt Hb prev window 0).1,
        bs.drop (offset + (parseFromAt Hb prev window 0).2.1),
        (parseFromAt Hb prev window 0).2.2) := by
  have e := parseFromAt_eq Hb prev window 0
  simp only [h, List.drop_drop] at e
  exact e

def root (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log-segments"
def selector (dir : System.FilePath) : System.FilePath := dir / ".obend" / "log"
def block (dir : System.FilePath) (generation index : Nat) : System.FilePath :=
  root dir / toString generation / toString index

structure Index where
  generation : Nat
  active : Nat

def indexText (Hb : Bytes → Bytes) (idx : Index) : String :=
  let body := "obend-segments 1 " ++ toString idx.generation ++ " " ++ toString idx.active
  body ++ " " ++ toString (dig Hb body.toUTF8.toList) ++ "\n"

/-- A selector is checksummed; malformed selectors fail rather than silently selecting another log.
A legacy log starts with OBL1 (or a torn prefix of it); only it may use the migration path. -/
def index (Hb : Bytes → Bytes) (dir : System.FilePath) : IO (Option Index) := do
  if !(← (selector dir).pathExists) then return none
  let h ← IO.FS.Handle.mk (selector dir) .read
  let b ← h.read 256
  Obend.Vault.Cost.addRead b.size
  if (b.extract 0 (min b.size 4)).data.toList == magic.take (min b.size 4) then return none
  let some txt := String.fromUTF8? b | throw (IO.userError "invalid segmented log selector")
  match txt.trimAscii.toString.splitOn " " with
  | ["obend-segments", "1", g, a, _] =>
    let some n := g.toNat? | throw (IO.userError "invalid log generation")
    let some k := a.toNat? | throw (IO.userError "invalid active log segment")
    let idx : Index := ⟨n, k⟩
    if indexText Hb idx != txt then throw (IO.userError "segmented log selector checksum does not hold")
    return some idx
  | _ => throw (IO.userError "invalid log selector (neither OBL1 nor obend-segments 1)")

def sizeOf (dir : System.FilePath) (idx : Index) : IO Nat := do
  let f := block dir idx.generation idx.active
  if ← f.pathExists then
    let last := (← f.metadata).byteSize.toNat
    if last > capacity then throw (IO.userError "log segment exceeds its block width")
    return idx.active * capacity + last
  -- A rollover published its new index but had not yet created the new block. Only a complete
  -- predecessor can justify that boundary; a missing/short predecessor is corruption.
  if idx.active == 0 then return 0
  let prior := block dir idx.generation (idx.active - 1)
  if !(← prior.pathExists) || (← prior.metadata).byteSize.toNat != capacity then
    throw (IO.userError "active log segment and its complete predecessor are missing")
  return idx.active * capacity

def size (Hb : Bytes → Bytes) (dir : System.FilePath) : IO Nat := do
  match ← index Hb dir with
  | some idx => sizeOf dir idx
  | none =>
    if !(← (selector dir).pathExists) then return 0
    return (← (selector dir).metadata).byteSize.toNat

/-- Load exactly the blocks meeting [start, stop); at most two partial blocks are read in excess.
Every interior block must be full, otherwise recovery stops rather than joining over missing bytes. -/
def readRangeOf (dir : System.FilePath) (g start stop : Nat) : IO ByteArray := do
  if stop ≤ start then return .empty
  let mut selected : Array ByteArray := #[]
  for i in [start / capacity : (stop - 1) / capacity + 1] do
    let b ← Obend.Vault.Cost.readBinFile (block dir g i)
    if b.size > capacity || (i < (stop - 1) / capacity && b.size != capacity) then
      throw (IO.userError "log segment is truncated before the end of the log")
    selected := selected.push b
  return assemble selected.toList (start % capacity) (stop - start)

def readRange (Hb : Bytes → Bytes) (dir : System.FilePath) (start stop : Nat) : IO ByteArray := do
  match ← index Hb dir with
  | some idx => readRangeOf dir idx.generation start stop
  | none =>
    if !(← (selector dir).pathExists) then return .empty
    return (← Obend.Vault.Cost.readBinFile (selector dir)).extract start stop

def readAll (Hb : Bytes → Bytes) (dir : System.FilePath) : IO ByteArray := do
  readRange Hb dir 0 (← size Hb dir)

/-- Publish a checksummed index with an atomic rename. -/
def publish (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index) : IO Unit := do
  let tmp := dir / ".obend" / "log.index-new"
  Obend.Vault.Cost.writeFile tmp (indexText Hb idx)
  IO.FS.rename tmp (selector dir)

/-- Prepare a boundary block before making it reachable. A prior interrupted truncation may have
left an orphan here: empty and flush it while it is still unselected, then publish the index.
A crash before publication sees the old prefix; after publication sees an empty next block. -/
def prepareBoundary (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index)
    (bi : Nat) (publishing : Bool) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk (block dir idx.generation bi) .write
  h.flush
  if publishing && bi > idx.active then publish Hb dir ⟨idx.generation, bi⟩
  return h

/-- Append at a known logical end. Boundary blocks are cleared before publication, then written;
a crash at publication is the full predecessor. Blocks are flushed before proceeding. `publishing = false`
builds an unselected generation for migration or compaction. -/
def appendAt (Hb : Bytes → Bytes) (dir : System.FilePath) (idx : Index) (start : Nat)
    (b : ByteArray) (publishing : Bool) : IO Unit := do
  let mut off := 0
  while off < b.size do
    let pos := start + off
    let bi := pos / capacity
    let len := min (capacity - pos % capacity) (b.size - off)
    let h ← if pos % capacity == 0 then prepareBoundary Hb dir idx bi publishing
      else IO.FS.Handle.mk (block dir idx.generation bi) .append
    Obend.Vault.Cost.write h (b.extract off (off + len))
    h.flush
    off := off + len

def fresh (dir : System.FilePath) : IO Nat := do
  let mut g ← IO.monoNanosNow
  while ← (root dir / toString g).pathExists do g := g + 1
  IO.FS.createDirAll (root dir / toString g)
  return g

def lastBlock (size : Nat) : Nat := (size - 1) / capacity

/-- A legacy byte file is migrated once, before the next append. Publication is last. -/
def ensure (Hb : Bytes → Bytes) (dir : System.FilePath) : IO Index := do
  if let some idx ← index Hb dir then return idx
  let b ← if ← (selector dir).pathExists then Obend.Vault.Cost.readBinFile (selector dir) else pure .empty
  let g ← fresh dir
  let idx : Index := ⟨g, lastBlock b.size⟩
  appendAt Hb dir idx 0 b false
  publish Hb dir idx
  return idx

def append (Hb : Bytes → Bytes) (dir : System.FilePath) (b : ByteArray) : IO Unit := do
  let idx ← ensure Hb dir
  appendAt Hb dir idx (← sizeOf dir idx) b true

/-- Atomic replacement, used by compaction. The previously selected generation is removed only
after publication; an interrupted publication therefore preserves a complete log. -/
def replace (Hb : Bytes → Bytes) (dir : System.FilePath) (b : ByteArray) : IO Unit := do
  let old ← index Hb dir
  let g ← fresh dir
  let idx : Index := ⟨g, lastBlock b.size⟩
  appendAt Hb dir idx 0 b false
  publish Hb dir idx
  if let some previous := old then
    IO.FS.removeDirAll (root dir / toString previous.generation)

/-- Remove a rejected tail. Publish the retained last block before deleting later files; an
interrupted truncation can leave only rejected bytes or orphan files, never lose prefix bytes. -/
def truncate (Hb : Bytes → Bytes) (dir : System.FilePath) (stop : Nat) : IO Unit := do
  let idx ← ensure Hb dir
  let keep := (stop + capacity - 1) / capacity
  publish Hb dir ⟨idx.generation, lastBlock stop⟩
  if keep > 0 && stop % capacity != 0 then
    let f := block dir idx.generation (keep - 1)
    let b ← Obend.Vault.Cost.readBinFile f
    let tmp := f.withExtension "tmp"
    Obend.Vault.Cost.writeBinFile tmp (b.extract 0 (stop % capacity))
    IO.FS.rename tmp f
  for j in [keep : idx.active + 1] do
    let f := block dir idx.generation j
    if ← f.pathExists then IO.FS.removeFile f

end Obend.Vault.SegmentLog
end
