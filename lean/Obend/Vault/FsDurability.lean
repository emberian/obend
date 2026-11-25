module
public import Obend.Vault.Log
import all Obend.Vault.Log

public section
namespace Obend.Vault.FsDurability

/-! Crash-consistency model for a locked Vault segment-log and checkpoint replace.
A fresh generation cannot alias a selected one. Old and new selector inodes are
distinguished even while both names of the rename may be in flight. -/

abbrev Bytes := List UInt8

structure Data where
  seen : Bytes
  kept : Bytes
  high : Nat
  trusted : Bool

def Data.stable (xs : Bytes) : Data := ⟨xs, xs, xs.length, true⟩
def Data.append (d : Data) (xs : Bytes) : Data :=
  { d with seen := d.seen ++ xs, high := max d.high (d.seen.length + xs.length) }
def Data.sync (d : Data) : Data := if d.trusted then .stable d.seen else d
def Data.untrust (d : Data) : Data := { d with trusted := false }
def Data.Leaves (d : Data) (xs : Bytes) := d.kept <+: xs ∧ xs.length ≤ d.high

private theorem stable_exact {xs ys : Bytes} (h : (Data.stable xs).Leaves ys) : ys = xs := by
  obtain ⟨hp, hl⟩ := h
  exact (hp.eq_of_length (Nat.le_antisymm hp.length_le hl)).symm

/-- A pending append can tear or acquire junk, even of the right length.
A successful barrier fixes the entire byte string on disk. -/
theorem repaired_append_crash_prefix (acked pending cut : Bytes) :
    (((Data.stable acked).append pending).Leaves cut →
      ∃ tail, cut = acked ++ tail ∧ tail.length ≤ pending.length) ∧
    (((Data.stable acked).append pending).sync.Leaves cut → cut = acked ++ pending) := by
  constructor
  · rintro ⟨⟨tail, rfl⟩, hl⟩
    exact ⟨tail, rfl, by simpa [Data.append, Data.stable] using hl⟩
  · exact stable_exact

/-- Failure is sticky for this writer until recovery establishes trust. -/
def finishAppend (d : Data) (bytes : Bytes) (barrierOK : Bool) : Data × Option Nat :=
  let w := d.append bytes
  if barrierOK && w.trusted then (w.sync, some w.seen.length) else (w.untrust, none)

theorem failed_sync_refuses_retry (d : Data) (a b : Bytes) (ok : Bool) :
    (finishAppend d a false).2 = none ∧
    (finishAppend (finishAppend d a false).1 b ok).2 = none := by
  cases ok <;> exact ⟨rfl, rfl⟩

/-- History of a directory entry since its parent directory's last barrier. -/
structure Name where
  settled : Bool
  held : List Bool := []

def Name.bind (n : Name) (b : Bool) : Name := { n with held := b :: n.held }
def Name.sync (n : Name) : Name := ⟨n.held.headD n.settled, []⟩
def Name.Leaves (n : Name) (b : Bool) := b = n.settled ∨ b ∈ n.held

/-- Rollover clears an old orphan before appending at offset zero. A truncate
changes the visible length immediately, but does not lower the crash high-water
mark until a successful same-inode barrier. -/
def Data.clear (d : Data) : Data := { d with seen := [], kept := [] }

structure Boundary where
  active : Name -- false selects the full predecessor, true includes the next block
  nextName : Name
  nextData : Data

structure BoundaryCut where
  active : Bool
  nextPresent : Bool
  nextBytes : Bytes

def Boundary.Crash (s : Boundary) (c : BoundaryCut) : Prop :=
  s.active.Leaves c.active ∧ s.nextName.Leaves c.nextPresent ∧ s.nextData.Leaves c.nextBytes

def BoundaryCut.readAll (c : BoundaryCut) (fullPrefix : Bytes) : Bytes :=
  if c.active && c.nextPresent then fullPrefix ++ c.nextBytes else fullPrefix

def rollover (old : Data) (wasPresent repair : Bool) : Boundary :=
  let name := (Name.mk wasPresent []).bind true
  let data := old.clear
  ⟨(Name.mk false []).bind true, if repair then name.sync else name,
    if repair then data.sync else data⟩

theorem unrepaired_rollover_resurrects_orphan (full : Bytes) :
    let c : BoundaryCut := ⟨true, true, [99]⟩
    (rollover (.stable [99]) true false).Crash c ∧ c.readAll full = full ++ [99] := by
  exact ⟨⟨Or.inr (by decide), Or.inl rfl, ⟨⟨[99], rfl⟩, by decide⟩⟩, rfl⟩

theorem repaired_rollover_crash_prefix (full : Bytes) (old : Data) (ht : old.trusted = true)
    (present : Bool) (c : BoundaryCut) (h : (rollover old present true).Crash c) :
    c.readAll full = full := by
  have hd := h.2.2
  have e : c.nextBytes = [] := stable_exact (by simpa [rollover, Data.clear, Data.sync, ht] using hd)
  simp [BoundaryCut.readAll, e]

/-- Once the empty next block and the selector's name are settled, a completed
block write retains all preceding blocks as well as its acknowledged payload. -/
def writeBoundary (old : Data) (present : Bool) (bytes : Bytes) (ack : Bool) : Boundary :=
  let s := rollover old present true
  let d := s.nextData.append bytes
  { s with active := s.active.sync, nextData := if ack then d.sync else d }

theorem boundary_write_crash (full bs : Bytes) (old : Data) (ht : old.trusted = true)
    (present ack : Bool) (c : BoundaryCut) (h : (writeBoundary old present bs ack).Crash c) :
    (∃ tail, c.readAll full = full ++ tail ∧ tail.length ≤ bs.length) ∧
    (ack = true → c.readAll full = full ++ bs) := by
  obtain ⟨ha, hn, hd⟩ := h
  have sel : c.active = true := by
    simpa [writeBoundary, rollover, Name.sync, Name.bind, Name.Leaves] using ha
  have target : c.nextPresent = true := by
    simpa [writeBoundary, rollover, Name.sync, Name.bind, Name.Leaves] using hn
  have readback : c.readAll full = full ++ c.nextBytes := by simp [BoundaryCut.readAll, sel, target]
  cases ack
  · have bound := hd.2
    exact ⟨⟨c.nextBytes, readback, by simpa [writeBoundary, rollover, Data.append,
      Data.clear, Data.sync, Data.stable, ht] using bound⟩, by intro h; contradiction⟩
  · have same : c.nextBytes = bs := stable_exact (by
      simpa [writeBoundary, rollover, Data.clear, Data.append, Data.sync, Data.stable, ht] using hd)
    exact ⟨⟨bs, by simpa [same] using readback, Nat.le_refl _⟩, fun _ => by simpa [same] using readback⟩

structure Block where
  name : Name
  data : Data

def Block.write (xs : Bytes) : Block := ⟨(Name.mk false []).bind true, (Data.stable []).append xs⟩
def Block.syncFile (b : Block) : Block := { b with data := b.data.sync }
def Block.syncName (b : Block) : Block := { b with name := b.name.sync }

structure Gen where
  name : Name
  blocks : List Block

def Gen.build (xs : List Bytes) : Gen :=
  ⟨(Name.mk false []).bind true, xs.map Block.write⟩
def Gen.syncFiles (g : Gen) : Gen := { g with blocks := g.blocks.map Block.syncFile }
def Gen.syncDir (g : Gen) : Gen := { g with blocks := g.blocks.map Block.syncName }
def Gen.syncParent (g : Gen) : Gen := { g with name := g.name.sync }
def Gen.prune (g : Gen) : Gen := { g with name := g.name.bind false }

private def complete (xs : List Bytes) := (Gen.build xs).syncFiles.syncDir.syncParent

structure ColdBlock where
  present : Bool
  bytes : Bytes

inductive BlockCuts : List Block → List ColdBlock → Prop
  | nil : BlockCuts [] []
  | cons {b : Block} {c : ColdBlock} {bs cs} : b.name.Leaves c.present → b.data.Leaves c.bytes →
      BlockCuts bs cs → BlockCuts (b :: bs) (c :: cs)

structure ColdGen where
  present : Bool
  blocks : List ColdBlock

def Gen.Crash (g : Gen) (c : ColdGen) := g.name.Leaves c.present ∧ BlockCuts g.blocks c.blocks

private def readBlocks : List ColdBlock → Option Bytes
  | [] => some []
  | b :: bs => if b.present then (readBlocks bs).map (b.bytes ++ ·) else none

/-- Missing active zero is treated as empty in SegmentLog.sizeOf. A missing
generation with an interior block is unreadable. -/
def ColdGen.readAll (g : ColdGen) : Option Bytes :=
  if g.present then
    match g.blocks with
    | [b] => some (if b.present then b.bytes else [])
    | bs => readBlocks bs
  else if g.blocks.length ≤ 1 then some [] else none

private theorem exact_blocks (xs : List Bytes) (cs : List ColdBlock)
    (h : BlockCuts (complete xs).blocks cs) :
    cs = xs.map (fun b => ⟨true, b⟩) := by
  induction xs generalizing cs with
  | nil => cases h; rfl
  | cons b bs ih =>
    cases h with
    | cons hn hd hs =>
      rename_i c cs
      have hp : c.present = true := by simpa [complete, Gen.build, Gen.syncFiles, Gen.syncDir,
        Block.write, Block.syncName, Block.syncFile, Name.bind, Name.sync, Name.Leaves] using hn
      have hb := stable_exact (xs := b) hd
      have ht := ih cs hs
      cases c
      simp_all

private theorem read_present (xs : List Bytes) :
    readBlocks (xs.map fun b => ⟨true, b⟩) = some xs.flatten := by
  induction xs <;> simp [readBlocks, *]

private theorem complete_reads {xs : List Bytes} {c : ColdGen} (h : (complete xs).Crash c) :
    c.readAll = some xs.flatten := by
  have hp : c.present = true := by simpa [complete, Gen.syncParent, Gen.syncDir, Gen.syncFiles,
    Gen.build, Name.bind, Name.sync, Name.Leaves] using h.1
  have hb := exact_blocks _ _ h.2
  simp only [ColdGen.readAll, hp, ite_true, hb]
  cases xs with
  | nil => rfl
  | cons x xs => cases xs with
    | nil => simp
    | cons y ys => exact read_present (x :: y :: ys)

structure Fs where
  selector : Name -- false = previously selected inode, true = renamed temp inode
  tmpData : Data
  old : Gen
  fresh : Gen

structure Cold where
  inode : Bool
  indexBytes : Bytes -- data of the temp inode, including after rename
  old : ColdGen
  fresh : ColdGen

structure Crash (s : Fs) (c : Cold) : Prop where
  selector : s.selector.Leaves c.inode
  tmpData : s.tmpData.Leaves c.indexBytes
  old : s.old.Crash c.old
  fresh : s.fresh.Crash c.fresh

/-- Project valid checksummed selectors to a tag for the selected generation. -/
def Cold.readAll (c : Cold) : Option Bytes :=
  if c.inode then
    if c.indexBytes == [1] then c.fresh.readAll else none
  else c.old.readAll

def stage (old : List Bytes) (g : Gen) : Fs :=
  ⟨⟨false, []⟩, (Data.stable []).append [1], complete old, g⟩
private def syncTmp (s : Fs) := { s with tmpData := s.tmpData.sync }
private def rename (s : Fs) := { s with selector := s.selector.bind true }
private def syncParent (s : Fs) := { s with selector := s.selector.sync }
private def retire (s : Fs) := { s with old := s.old.prune }

def unbarriered := retire (rename (stage [[7]] (Gen.build [[9]])))
def lost : Cold := ⟨false, [1], ⟨false, [⟨true,[7]⟩]⟩, ⟨true,[⟨true,[9]⟩]⟩⟩
def dangling : Cold := ⟨true, [1], ⟨true, [⟨true,[7]⟩]⟩, ⟨false,[⟨false,[]⟩]⟩⟩

-- fixture kept: concrete power-cut counterexample showing data loss without sync barriers
theorem unrepaired_replace_can_lose_committed : Crash unbarriered lost ∧ lost.readAll = some [] := by
  refine ⟨⟨Or.inl rfl, ⟨⟨[1], rfl⟩, by decide⟩, ?_, ?_⟩, rfl⟩
  · exact ⟨Or.inr (by decide), .cons (Or.inl rfl) ⟨⟨[], rfl⟩, by decide⟩ .nil⟩
  · exact ⟨Or.inr (by decide), .cons (Or.inr (by decide)) ⟨⟨[9], rfl⟩, by decide⟩ .nil⟩

-- fixture kept: concrete power-cut counterexample showing dangling selector without sync barriers
theorem unrepaired_publish_dangles : Crash unbarriered dangling ∧ dangling.readAll = some [] := by
  refine ⟨⟨Or.inr (by decide), ⟨⟨[1], rfl⟩, by decide⟩, ?_, ?_⟩, rfl⟩
  · exact ⟨Or.inl rfl, .cons (Or.inl rfl) ⟨⟨[], rfl⟩, by decide⟩ .nil⟩
  · exact ⟨Or.inl rfl, .cons (Or.inl rfl) ⟨⟨[], rfl⟩, by decide⟩ .nil⟩

/-- Covers every prefix before rename, including arbitrary partial work on
the unselected hierarchy and temp file. -/
theorem before_rename_safe (old : List Bytes) (g : Gen) (d : Data) (c : Cold)
    (h : Crash { stage old g with tmpData := d } c) : c.readAll = some old.flatten := by
  have ho : c.inode = false := by simpa [stage, Name.Leaves] using h.selector
  simpa [Cold.readAll, ho] using (complete_reads (xs := old) h.old)

inductive Phase | renamed | settled | pruned

def replaceAt (old new : List Bytes) (p : Phase) : Fs :=
  let swapped := rename (syncTmp (stage old (complete new)))
  match p with
  | .renamed => swapped
  | .settled => syncParent swapped
  | .pruned => retire (syncParent swapped)

theorem repaired_replace_crash_safe (old new : List Bytes) (p : Phase) (c : Cold)
    (h : Crash (replaceAt old new p) c) :
    (c.readAll = some old.flatten ∨ c.readAll = some new.flatten) ∧
    (p ≠ .renamed → c.readAll = some new.flatten) := by
  cases p <;> have ht : c.indexBytes = [1] := stable_exact h.tmpData <;>
    have hn := complete_reads (xs := new) h.fresh
  · cases hi : c.inode <;> simp [Cold.readAll, hi, ht, hn, complete_reads h.old]
  all_goals
    have hi : c.inode = true := by simpa [replaceAt, retire, syncParent, rename, syncTmp,
      stage, Name.Leaves, Name.sync, Name.bind] using h.selector
    simp [Cold.readAll, hi, ht, hn]

/-- removeDirAll may cut through any subset of the old blocks before the
old directory itself disappears. After the selector barrier even an arbitrary
old subtree has no influence on recovery. -/
theorem pruning_crash_safe (old new : List Bytes) (partialOld : Gen) (c : Cold)
    (h : Crash { replaceAt old new .settled with old := partialOld } c) :
    c.readAll = some new.flatten := by
  have hi : c.inode = true := by
    simpa [replaceAt, syncParent, rename, syncTmp, stage, Name.Leaves, Name.sync, Name.bind] using h.selector
  have hs : c.indexBytes = [1] := stable_exact h.tmpData
  simp [Cold.readAll, hi, hs, complete_reads (xs := new) h.fresh]

private def presentBlocks (xs : List Bytes) : List ColdBlock := xs.map fun x => ⟨true,x⟩

def Cold.selected (c : Cold) : Option ColdGen :=
  if c.inode then if c.indexBytes == [1] then some c.fresh else none else some c.old

def physicalImage (b : Bytes) : ColdGen :=
  ⟨true, presentBlocks (SegmentLog.split SegmentLog.capacity (by decide) b)⟩

private theorem complete_image {xs : List Bytes} {c : ColdGen} (h : (complete xs).Crash c) :
    c = ⟨true, presentBlocks xs⟩ := by
  have hp : c.present = true := by simpa [complete, Gen.syncParent, Gen.syncDir, Gen.syncFiles,
    Gen.build, Name.bind, Name.sync, Name.Leaves] using h.1
  have hb := exact_blocks xs c.blocks h.2
  cases c
  simp_all [presentBlocks]

/-- Use the deployed module's split and capacity. The selected directory and
every one of its block entries and byte strings agree, even for a reader
which independently checks physical widths and selector bounds. -/
theorem segmented_replace_selected_image (old new : Bytes) (p : Phase) (c : Cold)
    (h : Crash (replaceAt (SegmentLog.split SegmentLog.capacity (by decide) old)
      (SegmentLog.split SegmentLog.capacity (by decide) new) p) c) :
    (c.selected = some (physicalImage old) ∨ c.selected = some (physicalImage new)) ∧
    (p ≠ .renamed → c.selected = some (physicalImage new)) := by
  cases p <;> have hs : c.indexBytes = [1] := stable_exact h.tmpData <;>
    have hn : c.fresh = physicalImage new := complete_image h.fresh
  · have ho : c.old = physicalImage old := complete_image h.old
    cases hi : c.inode <;> simp [Cold.selected, hi, hs, hn, ho]
  all_goals
    have hi : c.inode = true := by simpa [replaceAt, retire, syncParent, rename, syncTmp,
      stage, Name.Leaves, Name.sync, Name.bind] using h.selector
    simp [Cold.selected, hi, hs, hn]

private theorem complete_cut (xs : List Bytes) :
    BlockCuts (complete xs).blocks (presentBlocks xs) := by
  induction xs with
  | nil => exact .nil
  | cons b _ ih => exact .cons (Or.inl rfl) ⟨⟨[], by simp [Block.write,
      Block.syncFile, Block.syncName, Data.sync, Data.stable, Data.append]⟩, Nat.le_refl _⟩ ih

theorem physicalImage_readAll (b : Bytes) : (physicalImage b).readAll = some b := by
  let bs := SegmentLog.split SegmentLog.capacity (by decide) b
  have image := complete_reads (xs := bs) (c := physicalImage b)
  have cut : (complete bs).Crash (physicalImage b) := ⟨Or.inl rfl, complete_cut bs⟩
  simpa [bs, SegmentLog.split_join] using image cut

theorem repaired_replace_inhabited (old new : List Bytes) (p : Phase) :
    ∃ c, Crash (replaceAt old new p) c ∧ c.readAll = some new.flatten := by
  let c : Cold := ⟨true, [1], ⟨true, presentBlocks old⟩, ⟨true, presentBlocks new⟩⟩
  have fresh : (complete new).Crash c.fresh := ⟨Or.inl rfl, complete_cut new⟩
  refine ⟨c, ?_, ?_⟩
  · cases p
    · exact ⟨Or.inr (List.mem_cons_self ..), ⟨⟨[], rfl⟩, Nat.le_refl _⟩, ⟨Or.inl rfl, complete_cut old⟩, fresh⟩
    all_goals exact ⟨Or.inl rfl, ⟨⟨[], rfl⟩, Nat.le_refl _⟩, ⟨Or.inl rfl, complete_cut old⟩, fresh⟩
  · exact complete_reads fresh

end Obend.Vault.FsDurability
