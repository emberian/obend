module

public import Obend.Tactic.Tooth
public import Obend.Digest.HashBytes
public import Obend.Digest.Cshake256.Spec
public import Obend.Digest.Cshake256.Fast
public import Obend.Digest.Cshake256.Seam
public import Obend.Digest.Kmac256
public import Obend.Codec.Hex
public import Obend.Doc.Graph
public import Obend.Doc.Patch
public import Obend.Doc.Merge
public import Obend.Doc.Render
public import Obend.Judge.SymbolicRegexBisim
public import Obend.Judge.VpaComplementAndJson
public import Obend.Judge.TranscriptPolicy
public import Obend.Judge.Lrat
public import Obend.Judge.Netting

import all Obend.Tactic.Tooth
import all Obend.Digest.HashBytes
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Kmac256
import all Obend.Codec.Hex
import all Obend.Doc.Graph
import all Obend.Doc.Patch
import all Obend.Doc.Merge
import all Obend.Doc.Render
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.TranscriptPolicy
import all Obend.Judge.Lrat
import all Obend.Judge.Netting

meta import Obend.Digest.HashBytes
meta import Obend.Digest.Cshake256.Spec
meta import Obend.Digest.Cshake256.Fast
meta import Obend.Digest.Cshake256.Seam
meta import Obend.Digest.Kmac256
meta import Obend.Codec.Hex
meta import Obend.Doc.Graph
meta import Obend.Doc.Patch
meta import Obend.Doc.Merge
meta import Obend.Doc.Render
meta import Obend.Judge.SymbolicRegexBisim
meta import Obend.Judge.VpaComplementAndJson
meta import Obend.Judge.TranscriptPolicy
meta import Obend.Judge.Lrat
meta import Obend.Judge.Netting

/-!
# `tests/metasystem/CarrierExecRefinementTest.lean` — Teeth & Guards for `Spec ↔ Exec` Refinements

Kernel mutation probes (`#tooth`) and runtime `#guard` witnesses covering the `ByteArray`, `UInt64`,
`BitVec 256`, and `Array` `Exec` refinements across `Digest`, `Codec`, `Doc`, and `Judge`:

1. **`Obend.Digest.HashBytes`** — 64-bit limb `beExec` / `ofBEExec` (`@[csimp]`) and zero-`List`
   `beByteArray` / `ofBEByteArray` / `be256ByteArray` / `ofBE256ByteArray`.
2. **`Obend.Digest.Cshake256` & `Obend.Digest.Kmac256`** — unboxed `natBytesLEFast` (`@[csimp]`),
   zero-copy `namedByteArrayFast` / `namedBytes_eq_fast` (`@[csimp]`), and zero-copy
   `kmac256ByteArrayFast` / `kmac256Bytes_eq_fast` (`@[csimp]`).
3. **`Obend.Codec.Hex`** — tail-recursive `@[csimp]` encoders/decoders and zero-`List`
   `byteArrayToHexAscii` / `hexByteArrayStrict?`.
4. **`Obend.Doc.{Graph,Patch,Merge,Render}`** — $O(V + E)$ `Array`+bitset `beforeBFast` (`@[csimp]`),
   $O(N)$ `GraphArrays` `applyExec` (`@[csimp]`), $O(N \log N)$ sorted-`Array` `dedupStringKeysExec`,
   `diffKeyedCellsExec`, `mergeKeyedCells3Exec` (`@[csimp]`), tail-recursive `lexExec` (`@[csimp]`),
   pre-indexed `Vault.readExec` (`@[csimp]`), and sharpened `[[Page|alias]]` / `[[Page\|alias]]`
   and malformed `[[` / `[[]]` handling.
5. **`Obend.Judge.{SymbolicRegexBisim,VpaComplementAndJson,TranscriptPolicy,Lrat,Netting}`** —
   zero-`List` `cshakeHashExec`, `checkJsonRedactionExec`, `leafMsgExec`, `pairMsgExec`,
   `skeletonRunExec`, `slotsConfinedExec`, `spansAlignedExec`, linear-time `Array`+sparse-trail
   `Lrat.checkExec`, and $O(M \log M)$ sorted-`Array` `Netting.checkNettingExec`.
-/

public section

namespace Obend.Tests.Metasystem.CarrierExecRefinementTest

-- ============================================================================
-- 1. Digest (`HashBytes`, `Cshake256`, `Kmac256`)
-- ============================================================================

#tooth Obend.Digest.HashBytes.be_eq_beExec by mutation
  Obend.Digest.HashBytes.beExec := fun w _ => List.replicate w 0

#tooth Obend.Digest.HashBytes.ofBE_eq_ofBEExec by mutation
  Obend.Digest.HashBytes.ofBEExec := fun _ => 0

#tooth Obend.Digest.HashBytes.beByteArray_toList by mutation
  Obend.Digest.HashBytes.beByteArray := fun _ _ => ByteArray.empty

#tooth Obend.Digest.HashBytes.ofBEByteArray_eq by mutation
  Obend.Digest.HashBytes.ofBEByteArray := fun _ => 0

#tooth Obend.Digest.Cshake256.Fast.pushU64BytesLE_eq by mutation
  Obend.Digest.Cshake256.Fast.pushU64BytesLE := fun _ _ tail => tail

#tooth Obend.Digest.Cshake256.Fast.namedByteArrayFast_eq by mutation
  Obend.Digest.Cshake256.Fast.namedByteArrayFast := fun _ _ _ => ByteArray.empty

#tooth Obend.Digest.Cshake256.namedBytesFast_eq by mutation
  Obend.Digest.Cshake256.namedBytesFast := fun _ _ _ => []

#tooth Obend.Digest.Kmac256.kmac256ByteArrayFast_eq by mutation
  Obend.Digest.Kmac256.kmac256ByteArrayFast := fun _ custom input =>
    Obend.Digest.Cshake256.Fast.cshake256ByteArrayFast custom input

#tooth Obend.Digest.Kmac256.kmac256Bytes_eq_fast by mutation
  Obend.Digest.Kmac256.kmac256Fast := fun _ custom input =>
    Obend.Digest.Cshake256.cshake256Bytes custom input

-- Multi-limb (> 64-bit) big-endian round-trip & NIST KMAC256 ByteArray check:
#guard Obend.Digest.HashBytes.ofBEByteArray
    (Obend.Digest.HashBytes.beByteArray 32 (2 ^ 200 + 2 ^ 97 + 0xdeadbeefcafe1234)) ==
  2 ^ 200 + 2 ^ 97 + 0xdeadbeefcafe1234

#guard Obend.Digest.Cshake256.Fast.natBytesLEFast (2 ^ 130 + 0x123456789abcdef0) ==
  Obend.Digest.Cshake256.natBytesLE (2 ^ 130 + 0x123456789abcdef0)

#guard (Obend.Digest.Kmac256.kmac256ByteArrayFast
    "key".toUTF8 "OBEND.KMAC/v1".toUTF8 "message".toUTF8).data.toList ==
  Obend.Digest.Kmac256.kmac256Bytes
    "key".toUTF8.data.toList "OBEND.KMAC/v1".toUTF8.data.toList "message".toUTF8.data.toList

-- ============================================================================
-- 2. Codec (`Hex`)
-- ============================================================================

#tooth Obend.Codec.Hex.bytesToHexChars_eq_exec by mutation
  Obend.Codec.Hex.bytesToHexCharsExec := fun _ => []

#tooth Obend.Codec.Hex.byteArrayToHexAscii_toList by mutation
  Obend.Codec.Hex.byteArrayToHexAscii := fun _ => ByteArray.empty

#tooth Obend.Codec.Hex.hexByteArrayStrict?_toList by mutation
  Obend.Codec.Hex.hexByteArrayStrict? := fun _ => none

#guard Obend.Codec.Hex.hexByteArrayStrict?
    (Obend.Codec.Hex.byteArrayToHexAscii (ByteArray.mk #[0x00, 0x5a, 0xa5, 0xff])) ==
  some (ByteArray.mk #[0x00, 0x5a, 0xa5, 0xff])

-- Uppercase hex bytes must be refused by the strict lowercase ByteArray decoder:
#guard Obend.Codec.Hex.hexByteArrayStrict? "0A".toUTF8 == none

-- ============================================================================
-- 3. Doc (`Graph`, `Patch`, `Merge`, `Render`)
-- ============================================================================

#tooth Obend.Doc.Graph.beforeB_eq_fast by mutation
  Obend.Doc.Graph.beforeBFast := fun _ _ _ => false

#tooth Obend.Doc.Graph.apply_eq_exec by mutation
  Obend.Doc.Graph.applyExec := fun G _ => G

#tooth Obend.Doc.dedupStringKeys_eq_exec by mutation
  Obend.Doc.dedupStringKeysExec := fun _ => []

#tooth Obend.Doc.diffKeyedCells_eq_exec by mutation
  Obend.Doc.diffKeyedCellsExec := fun _ _ => []

#tooth Obend.Doc.mergeKeyedCells3_eq_exec by mutation
  Obend.Doc.mergeKeyedCells3Exec := fun _ _ _ => ⟨[], []⟩

#tooth Obend.Doc.lex_eq_exec by mutation
  Obend.Doc.lexExec := fun _ _ _ => []

#tooth Obend.Doc.Vault.read_eq_exec by mutation
  Obend.Doc.Vault.readExec := fun _ _ _ => []

-- Obsidian Markdown-table escaped alias `[[Beta\|table alias]]`, empty `[[]]`, and unclosed `[[`:
#guard Obend.Doc.target false "Beta\\|table alias".toList == ("Beta".toList, .identity)
#guard Obend.Doc.target false "Beta#^ans\\|table alias".toList == ("Beta".toList, .block "ans")
#guard Obend.Doc.tokens "empty [[]] and broken [[unclosed [[Beta]]\n" ==
  [.text "empty [[]] and broken [[unclosed ".toList, .link "Beta".toList, .text "\n".toList]

-- ============================================================================
-- 4. Judge (`SymbolicRegexBisim`, `VpaComplementAndJson`, `TranscriptPolicy`, `Lrat`, `Netting`)
-- ============================================================================

#tooth Obend.Judge.Commit.cshakeHash_eq_exec by mutation
  Obend.Judge.Commit.cshakeHashExec := fun _ _ => ByteArray.mk (Array.replicate 32 0)

#tooth Obend.Judge.VpaJson.checkJsonRedaction_eq_exec by mutation
  Obend.Judge.VpaJson.checkJsonRedactionExec := fun _ _ _ _ => false

#tooth Obend.Judge.VpaJson.leafMsg_eq_exec by mutation
  Obend.Judge.VpaJson.leafMsgExec := fun span => span

#tooth Obend.Judge.VpaJson.pairMsg_eq_exec by mutation
  Obend.Judge.VpaJson.pairMsgExec := fun _ l r => l ++ r

#tooth Obend.Judge.skeletonRun_eq_exec by mutation
  Obend.Judge.skeletonRunExec := fun st _ => st

#tooth Obend.Judge.slotsConfined_eq_exec by mutation
  Obend.Judge.slotsConfinedExec := fun _ _ => false

#tooth Obend.Judge.spansAligned_eq_exec by mutation
  Obend.Judge.spansAlignedExec := fun _ _ _ => false

#tooth Obend.Judge.Lrat.check_eq_exec by mutation
  Obend.Judge.Lrat.checkExec := fun _ _ _ => .uncovered

#tooth Obend.Judge.lookupPos_buildPosArray by mutation
  Obend.Judge.lookupPos := fun _ _ _ => 0

#tooth Obend.Judge.checkNetting_eq_exec by mutation
  Obend.Judge.checkNettingExec := fun _ _ => .uncovered

end Obend.Tests.Metasystem.CarrierExecRefinementTest

end
