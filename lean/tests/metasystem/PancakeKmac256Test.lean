module
import Obend.Lower.Pancake.PancakeKmac256
import Obend.Tactic.Tooth
import all Obend.Lower.Pancake.PancakeKmac256
import all Obend.Lower.Pancake.PancakeCshake256
import all Obend.Lower.Pancake.EmitPnk
import all Obend.Digest.Kmac256
import all Obend.Digest.Cshake256.Spec
import all Obend.Lower.Pancake.SpongeFrame
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer

public section
open Obend.Lower.Pancake Obend.Digest Obend.Digest.Kmac256
namespace PancakeKmacTest

-- A wrong `right_encode(256)` byte.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.Kmac.outputField := [1, 0, 3]
-- A wrong ASCII byte in the function name.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.Kmac.nameField :=
  [1, 32, 75, 77, 65, 68]
-- SHAKE's domain suffix in place of cSHAKE's.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.customSuffix := 0x1f
-- A 16-word rate.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.rateWords := 16
-- No final padding bit.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.finalBit := 0
-- A wrong `bytepad` width in both static blocks.
#tooth Sponge.Kmac.pancakeKmac256_correct by mutation Sponge.Kmac.rateField := [1, 137]

-- The resumed tail takes the same trailer, suffix and rate.
#tooth Sponge.Kmac.pancakeResume_correct by mutation Sponge.Kmac.outputField := [1, 0, 3]
#tooth Sponge.Kmac.pancakeResume_correct by mutation Sponge.customSuffix := 0x1f
#tooth Sponge.Kmac.pancakeResume_correct by mutation Sponge.rateWords := 16
-- The KMAC arm forgets `right_encode(256)`.
#tooth Sponge.Kmac.pancakeResume_correct by mutation Sponge.Kmac.writeTrailedTail :=
  Sponge.Kmac.writeTail

#print axioms Sponge.Kmac.pancakeKmac256_correct
#print axioms Sponge.Kmac.pancakeResume_correct
#print axioms Sponge.Kmac.pancakeKmacResume_correct
#print axioms Sponge.Kmac.pancakeCshakeResume_correct

/-! ## The premises are inhabited -/

private def exampleLayout : Sponge.Layout where
  base := 1024
  table := 0
  frame := 8192
  name := ⟨256, [0]⟩
  custom := ⟨512, []⟩
  message := ⟨768, List.replicate 137 0⟩
  domain := fun _ => true
  memory := fun a => ([256, 1, 512, 0, 768, 137] : List Word).getD (a.toNat / 8) 0
  headroom := 146

private theorem validExample : Sponge.Valid exampleLayout := by
  have away (w : Word) (h : w.toNat < 4096) : ¬exampleLayout.inFrame w := by
    rintro ⟨i, hi, eq⟩
    simp only [Sponge.Layout.capacity, exampleLayout, List.length_replicate, List.length_cons,
      List.length_nil] at hi
    have a := congrArg BitVec.toNat eq
    simp only [ByteMemory.align_nat, ByteMemory.offset, BitVec.toNat_add, BitVec.toNat_ofNat] at a
    change (8192 + i % 2^64) % 2^64 / 8 * 8 = w.toNat at a
    omega
  refine ⟨by simp [Sponge.Layout.capacity, exampleLayout], by decide, by decide, fun _ _ => rfl,
    ?_, ?_, ?_⟩
  · intro i
    exact ⟨rfl, away _ ((by decide : ∀ i : Fin 25, (WordBuffer.address 1024 i).toNat < 4096) i)⟩
  · intro i
    refine ⟨rfl, away _ ((by decide : ∀ i : Fin 6, (WordBuffer.address 0 i).toNat < 4096) i), ?_⟩
    have args : exampleLayout.args = [256, 1, 512, 0, 768, 137] := by
      simp [Sponge.Layout.args, exampleLayout]
    rw [args]
    exact (by decide : ∀ j : Fin 6, exampleLayout.memory (WordBuffer.address 0 j) =
      ([256, 1, 512, 0, 768, 137] : List Word)[j.val]!) i
  · intro x hx i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · change i < 1 at hi
      have : i = 0 := by omega
      subst i
      exact ⟨rfl, away _ (by decide), rfl⟩
    · exact False.elim (Nat.not_lt_zero _ hi)
    · let j : Fin 137 := ⟨i, by simpa [exampleLayout] using hi⟩
      have addr : ∀ k : Fin 137, (byte_align (ByteMemory.offset 768 k)).toNat < 4096 := by decide
      have val : ∀ k : Fin 137,
          ByteMemory.read exampleLayout.memory (ByteMemory.offset 768 k) = 0 := by decide
      exact ⟨rfl, away _ (addr j),
        (val j).trans (by simp only [exampleLayout, List.getElem_replicate]; rfl)⟩

example : ∃ c : Sponge.Layout, Sponge.Valid c ∧ 146 ≤ c.headroom :=
  ⟨exampleLayout, validExample, Nat.le_refl _⟩

example : ∃ (c : Sponge.Layout) (src : Cshake256.State), Sponge.Valid c ∧
    ∀ i : Fin 25, c.memory (WordBuffer.address c.base i) = Keccak.lanes src i :=
  ⟨exampleLayout, Cshake256.zeroState, validExample, by decide +kernel⟩

/-! ## Vectors -/

private def rangeBytes (n : Nat) : List UInt8 := (List.range n).map UInt8.ofNat

private def messageOf (n : Nat) : List UInt8 :=
  if n == 3 then "abc".toUTF8.toList else rangeBytes n

private def customs : List (List UInt8) := [[], "OBEND.KMAC/v1".toUTF8.toList, rangeBytes 140]

private def vectorKey : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (0x40 + i)

/-- NIST ACVP-Server, KMAC-256-1.0 internalProjection.json at b633d3fd5fab,
    tgId 4, tcId 307. Byte-aligned inputs, binary customization, XOF disabled, L = 256. -/
private def nistVector : List UInt8 × List UInt8 × List UInt8 :=
  ([
    0xe2, 0x2e, 0x3b, 0x59, 0x2d, 0x75, 0x70, 0x5e, 0x11, 0x5e, 0xb5, 0x9d, 0x10, 0xdb, 0x68,
    0x76, 0xae, 0xbd, 0x4c, 0xdb, 0x41, 0x9e, 0x1a, 0x7f, 0x0f, 0xaf, 0x25, 0x32, 0xdf, 0x86,
    0x9c, 0xf5, 0xae, 0x80, 0x8a, 0x80, 0xb6, 0x3c, 0x3d, 0xdd, 0xf9, 0x29, 0xba, 0x14, 0xdc,
    0x6b, 0x9b, 0x56, 0x50, 0x9b, 0xdf, 0x7f, 0x50, 0xe9, 0x8f, 0x6c, 0xaf, 0xf2, 0x96, 0x6b,
    0x53, 0x69, 0x88, 0xcb, 0x73, 0x92, 0x08, 0xab, 0x31, 0xb8, 0x11, 0x8e, 0x3c, 0x9d, 0xc4,
    0xd1, 0x0b, 0xc9, 0x71, 0xa5, 0x1b, 0x78, 0x9c, 0x67, 0x51, 0x0f, 0x87, 0xb6, 0x2c, 0xbc,
    0x39, 0xc8, 0xca, 0x7a, 0x7a, 0xbe, 0xfa, 0xc6, 0xde, 0x4e, 0x10, 0xb6, 0xcf, 0xec, 0x02,
    0x31, 0x8f, 0xd7, 0xa0, 0xbb, 0x29, 0xe8, 0xba, 0x60, 0xe6, 0xcd, 0x28, 0x83, 0x91, 0x51,
    0xe0, 0x19, 0x61, 0x01, 0xa5, 0x14, 0xbf, 0xcc, 0x74, 0x65, 0x8d, 0x35, 0xb2, 0x2c, 0x05,
    0x01, 0x46, 0xc4, 0xeb, 0xe3, 0x61, 0x67, 0xd0, 0x8e, 0xbe, 0xde, 0xdc, 0x89, 0x47, 0xef,
    0x24, 0x87, 0xfb, 0x90, 0x7b, 0x16, 0xb7, 0x16, 0xb0, 0xee, 0x15, 0xf0, 0x3f, 0x70, 0x4a,
    0xe7, 0xc7, 0x97, 0xea, 0x2d, 0xbd, 0x4c, 0x0b, 0x8d, 0xe2, 0x5b, 0x2f, 0x19, 0x17, 0x56,
    0x02, 0xd4, 0xbd, 0xb4, 0xd6, 0xd7, 0x1c, 0x79, 0xc3, 0xef, 0x2f, 0x04, 0x10, 0xf6, 0x70,
    0x44, 0xc3, 0xff, 0xa7, 0xd5, 0x34, 0xde, 0x5e, 0x04, 0xa4, 0xfa, 0x5f, 0x17, 0x0a, 0x3f,
    0x06, 0xe6, 0x1a, 0xc1, 0xe4, 0x86, 0x35, 0x03, 0x70, 0xf1, 0xbd, 0xfb, 0x75, 0x48, 0x31,
    0x62, 0x46, 0x6a, 0xa5, 0xec, 0x9a, 0x36, 0x00, 0x32, 0x18, 0xe6, 0x5a, 0xf2, 0xb8, 0x47,
    0xc8, 0xd9, 0x75, 0x39, 0x38, 0x60, 0x66, 0x57, 0x60, 0x15, 0x30, 0x5e, 0x36, 0xa8, 0x08,
    0x4c, 0xc5, 0xb9, 0xf6, 0x5c, 0x41, 0x27, 0xf1, 0x7f, 0x78, 0x3f, 0x47, 0x81, 0x19, 0x45,
    0x9c, 0x66, 0x62, 0xa6, 0x99, 0xc5, 0x48, 0x3a, 0x02, 0x28, 0xbe, 0x87, 0x92, 0x96, 0x6c,
    0x13, 0x75, 0x47, 0xb3, 0x31, 0x2c, 0xf7, 0x58, 0x1a, 0xed, 0x62, 0x9f, 0xbd, 0x74, 0x3b,
    0x88, 0x25, 0xdf, 0xf3, 0xac, 0x9d, 0x72, 0xab, 0xf0, 0xbb, 0x7e, 0xf1, 0xb0, 0x4e, 0x76,
    0x2f, 0x8a, 0x90, 0x3d, 0xec, 0x7a, 0xd0, 0xa6, 0xf9, 0x38, 0x48, 0x03, 0xd4, 0x52, 0x8a,
    0x81, 0xc6, 0x2b, 0xb3, 0x76, 0x35, 0xb7, 0x1d, 0x27, 0xa9, 0x00, 0xef, 0x18, 0x5a, 0x2a,
    0x64, 0x3f, 0x5b, 0xee, 0x3f, 0xec, 0x20, 0x84, 0xa0, 0xee, 0xff, 0x5b, 0x96, 0x10, 0xd4,
    0x46, 0x72, 0x9b, 0x08, 0x16, 0xa9, 0x55, 0xf0, 0xaa, 0x65, 0x6e, 0x77, 0xb1, 0xc2, 0x8c,
    0x69, 0xd0, 0x02, 0x8f, 0x49, 0x1c, 0x49, 0x47, 0xed, 0x92, 0x97, 0x6f, 0x81, 0xa3, 0x21,
    0x9b, 0x26, 0x94, 0xd8, 0x6b, 0x8d, 0x59, 0xe8, 0x5c, 0xba, 0xad, 0x5c, 0xa4, 0x35, 0x2d,
    0x7f, 0xb8, 0xf4, 0x21, 0x92, 0x21, 0xf7, 0xbc, 0xa5, 0xad, 0xb1, 0x00, 0xf4, 0xf1, 0x72,
    0x63, 0x03, 0x4d, 0x4f, 0x9b, 0x9c, 0xf6, 0x69, 0xb6, 0xae, 0xfb, 0xf1, 0xf9, 0x4c, 0xee,
    0xc9, 0xfb, 0x47, 0xe1, 0x83, 0x0a, 0xd3, 0x85, 0xf1, 0x70, 0x37, 0xc2, 0x8b, 0x42, 0x22,
    0x3c, 0x55, 0xda, 0x55, 0x07, 0x9b, 0x26, 0xa0, 0x7d, 0x0f, 0x03, 0xc3, 0xc8, 0xa7, 0x83,
    0x91, 0x2e, 0x7f, 0x30, 0xef, 0xd4, 0x3d, 0x49, 0xcb, 0xc8, 0x6a, 0x9f, 0x73, 0xef, 0x19,
    0xab, 0xfa, 0x2c, 0x7f, 0x55, 0x7f, 0x82, 0x27, 0xcb, 0x1f, 0xb9, 0xcf, 0x84, 0x2b, 0x4f,
    0xd3, 0x3e, 0x24, 0x64, 0x5f, 0x50, 0x6d, 0x85, 0x6f, 0xa1, 0x92, 0xd4, 0x5c, 0x7d, 0xd2,
    0xba, 0xe0], [
    0x51, 0x76, 0xf5, 0x63, 0x57, 0x42, 0x25, 0xa9, 0x4a, 0xba, 0x54, 0xdb, 0xf2, 0x9f, 0x32,
    0xbc, 0xec, 0x43, 0xb5, 0x82, 0xb0, 0xc2, 0x80, 0x75, 0x3e, 0x40, 0x10, 0x6f, 0xaf, 0x18,
    0x40, 0x8d, 0x80, 0x90, 0x1e, 0xe8, 0x1b, 0xfa, 0x5d, 0x5b, 0xeb], [
    0x31, 0x1d, 0xbb, 0x59, 0xe2, 0x5a, 0x3b, 0x0f])

/-- Key lengths 0, 32, 128, 136, 200 by the three customizations by message lengths 0, 3, 133,
    134, 136, 409, then the two vectors of minidregg's `Compiler.Sp800185Kmac256Conformance`.
    The final three cases cover a single padding byte for KMAC and cSHAKE, and a NIST answer.
    The name block spans two rate blocks under the 140-byte customization. -/
private def vectors : List (List UInt8 × List UInt8 × List UInt8) :=
  ([0, 32, 128, 136, 200].flatMap fun k => customs.flatMap fun s =>
    [0, 3, 133, 134, 136, 409].map fun n => (rangeBytes k, s, messageOf n)) ++
  [(vectorKey, "My Tagged Application".toUTF8.toList, [0, 1, 2, 3]),
   (vectorKey, "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList, "abc".toUTF8.toList),
   (rangeBytes 32, [], rangeBytes 132), (rangeBytes 32, [], rangeBytes 135), nistVector]

/-- 32-byte known answers in vector order, from PyCryptodome and the NIST ACVP fixture. -/
private def golden : List String := [
  "0b002c51ec240a9ae0e9399cecb6a6a136452522342f7e6c17c62b8cd51f583b", "a558b720b74c2e632c153198d3a5da4d9a9b68c00f4c95988dab72c51d413b05",
  "936ffb948a7ea2f781a5b68cbf7e5b00a4fd452cc4926ba7ac01ab4f1c000eb2", "8d84530c97fd7d90fead63f1eb6e3b22b461d2ee624ea918640c8d2fcbc885ed",
  "25b0f1878b952a8121fe3cc126bae06b17fc0970921a98ef202afcc97c872548", "65eebc9ad4667a067a7f094289379d0d4c7e8c25706cdf77a9610fcca0fb1831",
  "2585fc199af00d4bd69ef1df1eff9c7a118ef5cb9f5fbe3fb4a6659408f6e768", "7c379cb99d7114d800605e050e08dc00bb81a815f6a56e82acb48d64e47eafc1",
  "d5db01540c8a02faf94d00d1d6c497ebf5d428683c589df06afa44fbdbd16e31", "9cbe9e1671e51d5b691e7b841e1430881c56857f057545af4b934fd9cab6823c",
  "5fed460421e704adba6c52256e65b92f52d31b866f1ff1cdbde5f732ac6c054c", "5c6f59c6b33e6d3dfbda9422701fdb3d42fa768e29ab1eed5121335085b62746",
  "a19aed568ad119c10907cf305075a26756bfaed9d5dabf6ee992528df48dafe7", "93b6c4be2e44e39bf882495e41086c71c272f4a72805946ee3cfb355d93ddbc2",
  "f137da0036208d6047ef51bb6e3df3f5b745903cb62bc5c5a001733cbd486ae9", "354048f253bb27b1ee63eccb91932b4f853a09d7429b6f9b8c70f1edffac7cac",
  "1bdb22e40a57d8ee566d8557c789c86b142fdcbaab4045456033bcbbf1c224bd", "e3a1186abc93c7eaf14cabb85c002a5ccc089ea9a91cc2850460df3b391e163c",
  "eec22ac14d8df76636e1b7d82efe3417120cdcb57d10420b16a714dd6caf1210", "bfab42767f2fb55c1fd6d23db8c98d205e253035962f249dbe5531afd20d0406",
  "f06b0f6940edff2ead0bd0cf86a02745e73123e47e2cbf28af5913f5665fc524", "5a8f643fe4a4a4e5518cc8f56af50edeb869269bcb20e33e3cf05bee8d5f39dd",
  "6cfa0d684f84365a9cadca8bada217ed1326875065e93e3e2d081f0221e264fe", "0ba4b85c8a287b20ff7f3460e440655c0c3335fb2eec69ddfee47c0b58f45e12",
  "8e37d5488c01ccf6dd445adffa9041ead98f52da05c5cb414bd05bd95f9234fc", "c8d4d01c6d52555cfe35a6a2ab56e186b599558ed30fcbbf147ee05070dcf98c",
  "0b942aeb059992b4de20f6052825f4f8aa526a0ddd0ca31fd8e1fc57fc002b3b", "90e5934c95c7399f56e91f5276d874d251fd1736600baeecac8a1ca2b9c9f510",
  "625a3bd9ece77af07c167ffe71abeb36dee8201510a7eeb22085fd76644a470b", "89278e1ee7b6f7a6c738e9a6dc6009902f0d8fa8e986cef8160df1877e71f528",
  "6d36da5a554f115d50f7761871d34c59c4b1f6bd41f1f5a8ad3d4a0db71517c8", "b8f42e2de876db8306934fca147a066f6f3bad63b2a68adcbf2c1c49c957bdb6",
  "18548fba010aaa753a28ac63b627f4d576fcb8d5f0c4fca1dbd3aa6b8e18003f", "36477643396273368c90fc18857e821ce62a20716e216dfab6dcc6dbeacd6acf",
  "d98de8831bcc76594359c321aa6ba535ce850036265b1d3cede7c6a1de144a22", "27a1d2cd1e199d1c03dec24c882eeacf14476c9ebf3c0fc32afe984756e13aaf",
  "34894abde93f47ccdd3dc2f0b18a914715eb901e117a93d81aa15e923ac757af", "d94bd108a0820b2b4ce2de9d8820bee57909c5f0ca2da5756c978bc665186b06",
  "6bc1425d5fed0e9c4c9c4b3eafd7924308b5a98b6969ae02b6982fd2fa170d82", "6c9e54241ee0f58c63513a3c8bab6db4ea5d4cc2c7ecc2abd2dc1cd153014306",
  "de92eb90a6a77509e0170c359cbb195ab3b05929624cf38ddd63c8abe525061d", "02bd27852b25bb2a552f9a7be71ed389e85c83a659abb2c698598efd26345dc5",
  "75ff825cc29291b163dc549aec390fc371fc399ae4bf687d522ffb1f0e68717b", "75e917c1f6684e16e3e8e742d4fd7731aa427917f431dc2abfda61609a27b795",
  "f0f7aeb2a47e065af7c808a5c2eb4fe10a4d0432ff88e9da38b9da01b7e438d5", "e023947085cd9da489989b438bd29d1f48162eff171620678f8ccb8278a2fd7c",
  "03956c7923a730b6c76ba9278aabff82348678cb3fb907b148d91af6feed1cf0", "9dd9316f0d4fd1c8259b7fa3cff733299378aac8da3b62a85400fa2d66172dde",
  "b1d1e1ce99417a0cb1082a8d449f90b0d8cf94f87419d05ed39c9b079b67cb59", "50ec93f59c0d735e3eee58b713e361ffe3bf7f69ceeab7c1154b4f3ceff0202a",
  "43c130354add5ef4e8064e006e636fadf3b9e0e6e902e24818c9a1710ce64583", "d93a48411f8f4156f89fcd91bb5d3d10a5dfcbf8bbd27155bed3e62dbac6c81c",
  "bafd4341dd44b69749196d474f102cec5a03e38605feac68745313a5412d3f78", "5fa79a700f214a1c3c77574256b2460c94b56633ae9fcc093138513800b8c737",
  "af418e7f0824c3dcb08a5215f381c0174468a485f03d05523365c7b835e16ef5", "233c8a06a4f5802699b5938e5c99285a4a2509a82099f14e1fd28cc938b11029",
  "e1056e0cfbf5fd82c817e61272c29ca2aebe7c5e336f1d285408717a240e14cc", "3e0cc4e7c8c6e302348adfeb5b53fc6fa94cb24427253ce07ea1461717d23bcf",
  "2a74ec0ec7aa37c4e8850ea567c65dc29bded260eb9ae16f6a9749c5eb9a15f2", "0a629633b72bb2b45a59168f4c6d5fd7f0914bfc83fb3b01bf2e4a433016647e",
  "a184c859121f141a9f381e613b45689baeed67c54f3a7655bbd1bd5564a15347", "7e5f3402966b79a3c7d7fe95ba2db5a4fae03a9932c57df89d014da450885390",
  "54918506942ee5a85b5356b6cf6d52a04440e7f6c96768af45fb99fb51834f4e", "bd184a1649ba40d54fd4704d8bc9132e785ee02c4281c1ba8c73e3eb42343b46",
  "bdf1c6355a3f3c308d72f9a9e8824d488f4886370b52ebb0893d982ceac08e30", "c7a0f4cf113566f96c369abcbc94a64a5d796b729af39dba301a5330d057adfa",
  "ecc918c609b06bbe76c20b5c820734b83e92d77c8b1ebdb76d5205745a34eceb", "f87d47569df2765bb3a2e5498f7d6df9cd9a703268ef7b759a045a9d574ad040",
  "1cc948855898422f9817c071c1a7012612a9f25b5ce99166149ae3b1bbef9117", "d3c3685f1cd51417097fe2589c6aca724fcbd9f10659a3049818338ea543faf2",
  "a911309c61e5393c1ad88b87f4568ae38d2118aee8f745d111095c7dcf93d7a2", "7318d8abaf50c05fbfcb0b0a895be9ce5c58dce7b74f8fd9b3bd7a1d8211932c",
  "1b69f08c1e047e548d3e9a5e99364a1642f237613d8b81d16f5c6c5deeae61e9", "14d098d10b8656eea9c5c7a65da44e68e5df98524da7550e431b011f04daf8c5",
  "33616c8f7a32552f9301cf0b1beb040bf0291c9cca0b2347818ea2b9993359ee", "7cd80ffe4320b3fdd32ab20589c0a0898e4d7b4720ce63c855b9d6039f7d0e14",
  "fe90505be2e7e7f8a305ba743f988564c2d14b4e0703270bf1bb24d101de4c5d", "742cac1f54bf0a92d526e2d8df066cbf2236b7252d7f371d53141030257495dd",
  "5937790c7a518f697f2800cfe96f2fcc7082c68b30779c7162740d549f631b1f", "867efa4a2d7a1e9a0aa332d71c598373d101197543e01d5447cec9fe5a02aac2",
  "51aec0728b15eb188ea07c2c379b41855d596bfbfd5c5b3bb14e6ae3e054423a", "7373067007769fc6d15779d44b930f3a30d2c904597816d5ea1806dbe4acd560",
  "aa4951f001aaf3dafe904cd68328f445c943706a0557fb2a1874403f5edfce1a", "ea10c3a3a7dce341a6568505d2786662ed4822f71eca0d3f1a2319b8414e2ff0",
  "1e1366c5464b129c3b82d98237a23f43023b41cd145d48dea9a37f3f13aed53c", "c4d89886713df14ff4d4d1163e3667428e91c99d26a3bc1b349e42205f5cd832",
  "02b3880079304b0f14c0526919bb583c16de86df27897a9ffab9812b975fb408", "cb5bc55669a7e32f003b5e10a46428ba4ecc3285d87c14762cb5cbd8808e18c2",
  "c7a17986d2b67377531defdd8b71c257484e6504b54bd82a1a958e921f7a2c7c", "b4806feb9a9340cf1e5f5c170e60d7dd7beba9f41f570f3b129f57e02faab1ec",
  "f2d95c33c9a201eb10c524b9084b4bacae0092f869122df7d7870b92c842e05b", "b1862dc66901cf8ad0de93235e93a487ec110f46a668a9b5122e0dcb1efa711f",
  "5c815971f6b8c5d63569e9776db8e2ccac8f867d07b93914d67d5cf5c6f7e726",
  "a99de128ff00bea9a8ca8dd1d51003c29a514a0d534ebc9f37ad8c7bcd003e53",
  "b557ec7607c18d826f7e08cb61065d6149abf54d6fb8160a736823fc0b905451"]

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

private def hex (bs : List UInt8) : String :=
  bs.foldl (fun acc b => (acc.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

-- Check the known answers in the ordinary Lean test build as well as in the native differential.
#guard golden.length == 95 && vectors.length == golden.length
#guard (vectors.zip golden).all fun ((key, custom, msg), tag) =>
  hex (kmac256Bytes key custom msg) == tag
#guard hex (kmac256Bytes (vectorKey.map (· + 1)) "My Tagged Application".toUTF8.toList
    [0, 1, 2, 3]) != "f2d95c33c9a201eb10c524b9084b4bacae0092f869122df7d7870b92c842e05b"
#guard functionName == "KMAC".toUTF8.toList

/-! ## The native program -/

private def emitted : Option String :=
  emitPnkProg [Sponge.Kmac.kernel, Sponge.Kmac.resumeKernel]

/-- Twenty-five words, least significant byte first. -/
private def stateBytes (st : Cshake256.State) : ByteArray :=
  ⟨((List.range 25).flatMap fun i =>
    let w := st.getD i Cshake256.zeroLane
    (List.range 8).map fun j => UInt8.ofBitVec ((w >>> (8*j)).setWidth 8)).toArray⟩

private def runNative (exe : System.FilePath) (args : Array String) : IO (Option (List UInt8)) := do
  let child ← IO.Process.spawn {cmd := exe.toString, args, stdout := .piped}
  let out ← child.stdout.readBinToEnd
  return if (← child.wait) == 0 then some out.toList else none

/-- Every vector agrees four ways: the Lean specification against PyCryptodome, the native
    one-shot against the specification, the native KMAC resume from the Lean midstate against
    the specification, and the native cSHAKE resume against the named digest. -/
def verifyNative (exe dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let some src := emitted | throw (IO.userError "KMAC emission failed")
  unless (← IO.FS.readBinFile "Obend/Lower/Pancake/kmac256.pnk") == src.toUTF8 do
    throw (IO.userError "kmac256.pnk differs from the Lean emitter")
  let path (name : String) := (dir / name).toString
  let mut count := 0
  for ((key, custom, msg), tag) in vectors.zip golden do
    let label := s!"|K|={key.length}, |S|={custom.length}, |X|={msg.length}"
    let spec := kmac256Bytes key custom msg
    unless hex spec == tag do throw (IO.userError s!"specification differs from golden: {label}")
    IO.FS.writeBinFile (dir / "key") ⟨key.toArray⟩
    IO.FS.writeBinFile (dir / "custom") ⟨custom.toArray⟩
    IO.FS.writeBinFile (dir / "message") ⟨msg.toArray⟩
    unless (← runNative exe #[path "key", path "custom", path "message"]) == some spec do
      throw (IO.userError s!"native one-shot mismatch: {label}")
    IO.FS.writeBinFile (dir / "state") (stateBytes (kmacMidstate key custom))
    unless (← runNative exe #["--resume", path "state", "1", path "message"]) == some spec do
      throw (IO.userError s!"native KMAC resume mismatch: {label}")
    IO.FS.writeBinFile (dir / "state") (stateBytes (cshakeMidstate functionName custom))
    unless (← runNative exe #["--resume", path "state", "0", path "message"]) ==
        some (Cshake256.namedBytes functionName custom msg) do
      throw (IO.userError s!"native cSHAKE resume mismatch: {label}")
    count := count + 1
  IO.println s!"{count} vectors: specification, PyCryptodome, native one-shot and both resumes agree"

end PancakeKmacTest

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit", path] =>
    let some src := emitPnkProg [Sponge.Kmac.kernel, Sponge.Kmac.resumeKernel]
      | throw (IO.userError "KMAC emission failed")
    IO.FS.writeFile path src
  | [exe, dir] => PancakeKmacTest.verifyNative exe dir
  | _ => throw (IO.userError "expected --emit PATH or EXECUTABLE SCRATCH_DIRECTORY")
