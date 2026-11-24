module
public import Obend.Codec.Hex
public import Obend.Core.SortedArray
import all Obend.Codec.Hex
import all Obend.Core.SortedArray
import Obend.Tactic.Tooth

/-!
# Teeth for the tree's one hex codec and its one sorted `UInt64` set

Each tooth swaps a definition for a plausible wrong one; the named theorem must stop checking.
The strict decoder's canonicity rests on refusing `A`–`F`; the round trip on the nibble
arithmetic; the fixed-width spelling on its digit order; the sorted set's lookup law on the binary
search, and its order on the insertion.
-/

namespace Obend.Tests.CodecHexAndSortedArray

-- A strict decoder that also reads `A`–`F` gives a byte string a second spelling.
#tooth Obend.Codec.Hex.bytesToHexChars_of_hexCharsToBytes? by mutation
  Obend.Codec.Hex.decodeHexNibble? := fun c =>
    if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
    else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
    else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
    else none

-- Writing `a`–`f` one code point low breaks the round trip.
#tooth Obend.Codec.Hex.hexCharsToBytes?_bytesToHexChars by mutation
  Obend.Codec.Hex.hexNibbleChar := fun n =>
    if n % 16 < 10 then Char.ofNat (48 + n % 16) else Char.ofNat (86 + n % 16)

-- Least significant digit first is not the spelling `hexCharsToNat?` reads.
#tooth Obend.Codec.Hex.hexCharsToNat?_natToHexChars by mutation
  Obend.Codec.Hex.natToHexChars := fun w n =>
    (List.range w).map fun i => Obend.Codec.Hex.hexNibbleChar (n >>> (4 * i))

-- A search that finds nothing is not the list lookup.
#tooth Obend.Core.SortedArray.SortedU64Set.contains_eq_spec by mutation
  Obend.Core.SortedArray.search := fun _ _ _ _ _ _ => none

-- Appending instead of inserting loses the strict order.
#tooth Obend.Core.SortedArray.insertKey_sorted by mutation
  Obend.Core.SortedArray.insertKey := fun k xs => xs ++ [k]

end Obend.Tests.CodecHexAndSortedArray
