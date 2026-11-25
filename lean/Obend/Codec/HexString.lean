module
public import Obend.Codec.Hex
import all Obend.Codec.Hex
public section
namespace Obend.Codec.Hex
private theorem pushHex_valid {dst : ByteArray} (h : dst.IsValidUTF8) (n : Nat) :
    (dst.push (hexNibbleByte n)).IsValidUTF8 := by
  have allDigits : ∀ d : Fin 16, (hexNibbleChar d.val).toUInt8 = hexNibbleByte d.val ∧
      (hexNibbleChar d.val).utf8Size = 1 := by decide
  have hd := allDigits ⟨n % 16, Nat.mod_lt _ (by decide)⟩
  simp only [hexNibbleChar_mod, hexNibbleByte_mod] at hd
  rw [← hd.1]
  exact h.push hd.2

private theorem hexAscii_valid (src : ByteArray) : (byteArrayToHexAscii src).IsValidUTF8 := by
  have loop (fuel i : Nat) (dst : ByteArray) (hd : dst.IsValidUTF8) :
      (byteArrayToHexAsciiLoop src fuel i dst).IsValidUTF8 := by
    induction fuel generalizing i dst with
    | zero => exact hd
    | succ fuel ih =>
      rw [byteArrayToHexAsciiLoop]
      split
      · exact ih _ _ (pushHex_valid (pushHex_valid hd _) _)
      · exact hd
  exact loop _ _ _ ⟨[], rfl⟩

/-- Strict text encoder over native byte buffers, including its UTF-8 validity proof. -/
def hexString (src : ByteArray) : String :=
  String.fromUTF8 (byteArrayToHexAscii src) (hexAscii_valid src)

theorem hexByteArrayStrict?_hexString (src : ByteArray) :
    hexByteArrayStrict? (hexString src).toUTF8 = some src := by
  have h := hexByteArrayStrict?_toList (byteArrayToHexAscii src)
  rw [byteArrayToHexAscii_toList, hexAsciiToBytes?_bytesToHexAscii] at h
  rw [String.toUTF8_eq_toByteArray]
  change hexByteArrayStrict? (byteArrayToHexAscii src) = some src
  cases hd : hexByteArrayStrict? (byteArrayToHexAscii src) with
  | none => simp [hd] at h
  | some b =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    exact congrArg some (ByteArray.ext (Array.toList_inj.mp h))

end Obend.Codec.Hex
