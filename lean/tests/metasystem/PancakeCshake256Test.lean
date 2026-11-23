module
import Obend.Lower.Pancake.PancakeCshake256
import Obend.Tactic.Tooth
import all Obend.Lower.Pancake.PancakeCshake256
import all Obend.Digest.Cshake256.Spec
import all Obend.Lower.Pancake.SpongeFrame
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer

public section
open Obend.Lower.Pancake Obend.Digest
namespace PancakeCshakeTest

#tooth Sponge.pancakeCshake256_correct by mutation Sponge.customSuffix := 0x1f
#tooth Sponge.pancakeCshake256_correct by mutation Sponge.shakeSuffix := 0x04
#tooth Sponge.pancakeCshake256_correct by mutation Sponge.finalBit := 0
#tooth Sponge.pancakeCshake256_correct by mutation Sponge.rateWords := 16

#print axioms Sponge.pancakeCshake256_correct

-- Realize the ABI on a named, two-message-block input. Descriptor words are
-- below address 48. The raw slices and state lie below the workspace at 8192.
private def exampleLayout : Sponge.Layout where
  base := 1024
  table := 0
  frame := 8192
  name := ⟨256,[0]⟩
  custom := ⟨512,[]⟩
  message := ⟨768,List.replicate 137 0⟩
  domain := fun _ => true
  memory := fun a => ([256,1,512,0,768,137] : List Word).getD (a.toNat/8) 0

private theorem validExample : Sponge.Valid exampleLayout := by
  have away (w : Word) (h : w.toNat < 4096) : ¬exampleLayout.inFrame w := by
    rintro ⟨i,hi,eq⟩
    simp only [Sponge.Layout.capacity, exampleLayout, List.length_replicate, List.length_cons, List.length_nil] at hi
    have a := congrArg BitVec.toNat eq
    simp only [ByteMemory.align_nat, ByteMemory.offset, BitVec.toNat_add, BitVec.toNat_ofNat] at a
    change (8192 + i % 2^64) % 2^64 / 8 * 8 = w.toNat at a
    omega
  refine ⟨by simp [Sponge.Layout.capacity, exampleLayout], by decide, by decide, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro i
    exact ⟨rfl, away _ ((by decide : ∀ i : Fin 25, (WordBuffer.address 1024 i).toNat < 4096) i)⟩
  · intro i
    refine ⟨rfl, away _ ((by decide : ∀ i : Fin 6, (WordBuffer.address 0 i).toNat < 4096) i), ?_⟩
    have args : exampleLayout.args = [256,1,512,0,768,137] := by simp [Sponge.Layout.args, exampleLayout]
    rw [args]
    exact (by decide : ∀ j : Fin 6, exampleLayout.memory (WordBuffer.address 0 j) = ([256,1,512,0,768,137] : List Word)[j.val]!) i
  · intro x hx i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · change i < 1 at hi
      have : i = 0 := by omega
      subst i; exact ⟨rfl, away _ (by decide), rfl⟩
    · exact False.elim (Nat.not_lt_zero _ hi)
    · let j : Fin 137 := ⟨i, by simpa [exampleLayout] using hi⟩
      have addr : ∀ k : Fin 137, (byte_align (ByteMemory.offset 768 k)).toNat < 4096 := by decide
      have val : ∀ k : Fin 137, ByteMemory.read exampleLayout.memory (ByteMemory.offset 768 k) = 0 := by decide
      exact ⟨rfl, away _ (addr j), (val j).trans (by simp only [exampleLayout, List.getElem_replicate]; rfl)⟩


private def rangeBytes (n : Nat) := (List.range n).map UInt8.ofNat
private def email := "Email Signature".toUTF8.toList

-- NIST's cSHAKE samples 3 and 4 request 512 bits. This ABI returns the first 256.
#guard Cshake256.namedBytes [] email (rangeBytes 4) ==
  [0xd0,0x08,0x82,0x8e,0x2b,0x80,0xac,0x9d,0x22,0x18,0xff,0xee,0x1d,0x07,0x0c,0x48,
   0xb8,0xe4,0xc8,0x7b,0xff,0x32,0xc9,0x69,0x9d,0x5b,0x68,0x96,0xee,0xe0,0xed,0xd1]
#guard Cshake256.namedBytes [] email (rangeBytes 200) ==
  [0x07,0xdc,0x27,0xb1,0x1e,0x51,0xfb,0xac,0x75,0xbc,0x7b,0x3c,0x1d,0x98,0x3e,0x8b,
   0x4b,0x85,0xfb,0x1d,0xef,0xaf,0x21,0x89,0x12,0xac,0x86,0x43,0x02,0x73,0x09,0x17]

/-- Re-emit the checked AST and exercise a separately linked Linux executable.
    Input files and stdout comparisons use raw bytes, including embedded NULs. -/
def verifyNative (exe dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let some src := emitPnkFun Sponge.kernel | throw (IO.userError "cSHAKE emission failed")
  unless (← IO.FS.readFile "Obend/Lower/Pancake/cshake256.pnk") == src do
    throw (IO.userError "cshake256.pnk differs from the Lean emitter")
  let domains := [([], []), ([], email), ("KMAC".toUTF8.toList, []),
    (rangeBytes 32, rangeBytes 130), (rangeBytes 128, []), ([], rangeBytes 129)]
  for (name, custom) in domains do
    for n in [0, 3, 4, 135, 136, 137, 200, 409] do
      let msg := if n == 3 then "abc".toUTF8.toList else rangeBytes n
      let paths := #[(dir / "name").toString, (dir / "custom").toString, (dir / "input").toString]
      for (path, data) in paths.toList.zip [name, custom, msg] do
        IO.FS.writeBinFile path ⟨data.toArray⟩
      let child ← IO.Process.spawn {cmd := exe.toString, args := paths, stdout := .piped}
      let digest ← child.stdout.readBinToEnd
      unless (← child.wait) == 0 && digest.toList == Cshake256.namedBytes name custom msg do
        throw (IO.userError s!"native mismatch for |N|={name.length}, |S|={custom.length}, |X|={n}")
  IO.println "48 native digests match the Lean specification"

end PancakeCshakeTest

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit", path] =>
    let some src := emitPnkFun Sponge.kernel | throw (IO.userError "cSHAKE emission failed")
    IO.FS.writeFile path src
  | [exe, dir] => PancakeCshakeTest.verifyNative exe dir
  | _ => throw (IO.userError "expected --emit PATH or EXECUTABLE SCRATCH_DIRECTORY")
