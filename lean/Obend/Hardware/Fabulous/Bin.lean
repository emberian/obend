module
/-
# Obend.Hardware.Fabulous.Bin — a FABulous bitstream as data the kernel reads

A bitstream's bytes as one natural number, little-endian (`byte i` is `(bin >>> 8i) % 256`), so the kernel
reads any bit with one shift. `binBits` is `bit_gen`'s frame layout (the one `decodeBin` follows): after a
20-byte sync header, column by column and frame by frame, a frame-select word and then one 32-bit word
per interior row, bottom row last, most significant byte first; tile `(x, y)`'s configuration bit `p` is
bit `p % 32` of frame `p / 32`'s word for row `y`. `binFramed` checks the header and every frame-select
word, so a bitstream that `binBits` reads is laid out as that layout says.
-/
public import Obend.Hardware.Fabulous.Readback
@[expose] public section

namespace Obend.Hardware.Fabulous

/-- Byte `i` of a bitstream held as a little-endian number. -/
def binByte (bin i : Nat) : Nat := (bin >>> (8 * i)) % 256

/-- Bit `k` of byte `i`. -/
def binBit (bin i k : Nat) : Bool := bin.testBit (8 * i + k)

/-- The 32-bit word at byte `o`, most significant byte first. -/
def binWord (bin o : Nat) : Nat :=
  binByte bin o * 2 ^ 24 + binByte bin (o + 1) * 2 ^ 16 + binByte bin (o + 2) * 2 ^ 8 + binByte bin (o + 3)

/-- **The frame layout**: tile `(x, y)`'s configuration bit `p` of a bitstream for a fabric of `rows` rows. -/
def binBits (rows bin : Nat) : Bits := fun x y p =>
  binBit bin (20 + (x * 20 + p / 32) * (4 + 4 * (rows - 2)) + 4 + 4 * (rows - 2 - y) + (3 - p % 32 / 8)) (p % 32 % 8)

def syncHeaderBytes : List Nat :=
  [0x00, 0xAA, 0xFF, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0xFA, 0xB0, 0xFA, 0xB1]

/-- The sync header, every frame-select word (column `x`, frame `f`: `x << 27 | 1 << f`), and the length. -/
def binFramed (cols rows bin size : Nat) : Bool :=
  bin < 2 ^ (8 * size) && size == 20 + cols * 20 * (4 + 4 * (rows - 2)) + 4 &&
  (List.range 20).all (fun i => binByte bin i == syncHeaderBytes.getD i 0) &&
  (List.range cols).all fun x => (List.range 20).all fun f =>
    binWord bin (20 + (x * 20 + f) * (4 + 4 * (rows - 2))) == x * 2 ^ 27 + 2 ^ f

/-- The Lean text of a bitstream: its bytes as one hexadecimal literal. -/
def binLean (name : String) (cols rows : Nat) (b : ByteArray) (source : String) : String :=
  let hex (n : Nat) : String := let d := Nat.toDigits 16 n; String.ofList (List.replicate (2 - d.length) '0' ++ d)
  let body := String.join (b.toList.reverse.map (hex ·.toNat))
  s!"module\n/-\n# Generated Bitstream Literal — `{source}` as data\n\nGenerated on demand by `obend fabric binlit`; do not edit.\n-/\npublic import Obend.Hardware.Fabulous.Bin\n" ++
  s!"@[expose] public section\n\nnamespace Obend.Hardware.Fabulous\n\ndef {name}Cols : Nat := {cols}\ndef {name}Rows : Nat := {rows}\n" ++
  s!"def {name}Size : Nat := {b.size}\n\n/-- The {b.size} bytes, little-endian. -/\ndef {name} : Nat :=\n  0x{body}\n\nend Obend.Hardware.Fabulous\n"

end Obend.Hardware.Fabulous
