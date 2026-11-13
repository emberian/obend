import all Obend.Polis.BlumRam
import all Obend.Vault.Log
import Obend.Vault.Log

open Obend.Vault.SegmentLog

def hashBytes (b : List UInt8) : List UInt8 :=
  Obend.Digest.Cshake256.cshake256Bytes "obend-log".toUTF8.toList b

def expect (b : Bool) (msg : String) : IO Unit :=
  unless b do throw (IO.userError msg)

def main (args : List String) : IO Unit := do
  let some name := args.head? | throw (IO.userError "pass a fresh fixture directory")
  let dir : System.FilePath := name
  if ← dir.pathExists then throw (IO.userError "fixture directory must not already exist")
  IO.FS.createDirAll (dir / ".obend")
  let bytes : ByteArray := ⟨(Array.range (capacity * 3 + 17)).map Nat.toUInt8⟩
  replace hashBytes dir bytes
  expect ((← size hashBytes dir) == bytes.size) "size after replace"
  expect ((← readAll hashBytes dir) == bytes) "whole stream after split"
  for (a, b) in [(0, 9), (capacity - 7, capacity + 13), (capacity + 4, 2 * capacity + 2),
      (3 * capacity + 8, bytes.size)] do
    expect ((← readRange hashBytes dir a b) == bytes.extract a b) "cross-boundary range"
  Obend.Vault.Cost.counts.set {}
  let _ ← readRange hashBytes dir (3 * capacity + 8) bytes.size
  let cost ← Obend.Vault.Cost.counts.get
  expect (cost.read < 512) "tail read included old blocks"
  let extra := bytes.extract 0 (capacity + 29)
  append hashBytes dir extra
  expect ((← readAll hashBytes dir) == bytes ++ extra) "append across block boundaries"
  truncate hashBytes dir (capacity + 5)
  expect ((← readAll hashBytes dir) == bytes.extract 0 (capacity + 5)) "truncate suffix"
  append hashBytes dir extra
  expect ((← readAll hashBytes dir) == bytes.extract 0 (capacity + 5) ++ extra) "append after truncation"
  -- The rollover index is durable before its target exists. This is a complete prior boundary,
  -- and the next append must create the selected block without duplicating anything.
  replace hashBytes dir (bytes.extract 0 capacity)
  let some idx ← index hashBytes dir | throw (IO.userError "missing index")
  publish hashBytes dir ⟨idx.generation, 1⟩
  expect ((← size hashBytes dir) == capacity) "interrupted rollover length"
  append hashBytes dir extra
  expect ((← readAll hashBytes dir) == bytes.extract 0 capacity ++ extra) "resume interrupted rollover"
  let some old ← index hashBytes dir | throw (IO.userError "missing index")
  replace hashBytes dir extra
  expect (!(← (root dir / toString old.generation).pathExists)) "compaction left forgotten generation"
  -- An interrupted truncate can leave an orphan next block. It must be replaced at rollover.
  let some idx ← index hashBytes dir | throw (IO.userError "missing index")
  IO.FS.writeBinFile (block dir idx.generation 2) (bytes.extract 0 19)
  append hashBytes dir bytes
  expect ((← readAll hashBytes dir) == extra ++ bytes) "orphan was appended instead of replaced"
  -- A valid old receipt in an orphan must never become visible during rollover. Stop at the
  -- actual boundary helper's return (index published, no new payload written), as a crash would.
  let payload := (bytes.extract 0 (capacity - 168)).data.toList
  let first : Obend.Vault.Log.Record :=
    ⟨⟨Obend.Vault.Rehydration.genesisSentinel, 0, 0, Obend.Vault.Log.dig hashBytes payload⟩, payload⟩
  let later : Obend.Vault.Log.Record :=
    ⟨⟨Obend.Vault.Log.Hr hashBytes first.receipt, 0, 0, Obend.Vault.Log.dig hashBytes [7]⟩, [7]⟩
  let firstBytes := Obend.Vault.LogBytes.encodeRecordBytes hashBytes first
  let laterBytes := Obend.Vault.LogBytes.encodeRecordBytes hashBytes later
  expect (firstBytes.size == capacity) "record fixture does not meet boundary"
  replace hashBytes dir firstBytes
  let some idx ← index hashBytes dir | throw (IO.userError "missing index")
  IO.FS.writeBinFile (block dir idx.generation 1) laterBytes
  let _ ← prepareBoundary hashBytes dir idx 1 true
  let stopped ← readAll hashBytes dir
  expect (stopped == firstBytes) "rollover publication resurrected valid orphan receipt"
  let parsed := Obend.Vault.LogBytes.parseFromAt hashBytes
    Obend.Vault.Rehydration.genesisSentinel stopped 0
  expect (parsed.1.length == 1 && parsed.2.2.isNone) "crashed rollover changed receipt prefix"
  replace hashBytes dir (extra ++ bytes)
  -- Every interior block is required, and full: no joining across missing or short bytes.
  let some idx ← index hashBytes dir | throw (IO.userError "missing index")
  let interior := block dir idx.generation 1
  let saved ← IO.FS.readBinFile interior
  IO.FS.removeFile interior
  let missing ← try let _ ← readAll hashBytes dir; pure false catch _ => pure true
  expect missing "missing interior block silently skipped"
  IO.FS.writeBinFile interior (saved.extract 0 7)
  let short ← try let _ ← readAll hashBytes dir; pure false catch _ => pure true
  expect short "truncated interior block silently joined"
  IO.FS.writeBinFile interior saved
  truncate hashBytes dir capacity
  expect ((← size hashBytes dir) == capacity) "truncate exactly on a boundary"
  append hashBytes dir extra
  expect ((← size hashBytes dir) == capacity + extra.size) "append after boundary truncate"
  truncate hashBytes dir 0
  expect ((← size hashBytes dir) == 0) "truncate to zero"
  expect ((← readAll hashBytes dir).isEmpty) "zero truncation kept bytes"
  append hashBytes dir extra
  expect ((← readAll hashBytes dir) == extra) "append after zero truncation"
  -- A corrupted selected block remains subject to the original record codec, while corruption of
  -- the index itself is a hard error, not a silent empty log.
  let txt ← IO.FS.readFile (selector dir)
  IO.FS.writeFile (selector dir) (txt ++ "bad")
  let refused ← try let _ ← index hashBytes dir; pure false catch _ => pure true
  expect refused "corrupted index accepted"
  IO.FS.writeFile (selector dir) txt
  IO.println s!"segmented bytes: boundary reads, append, truncation, interrupted rollover, orphan replacement, index checksum; tail read {cost.read} bytes"
