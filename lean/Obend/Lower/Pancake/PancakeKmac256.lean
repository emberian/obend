module
public import Obend.Lower.Pancake.PancakeCshake256
public import Obend.Digest.Kmac256
import all Obend.Lower.Pancake.PancakeCshake256
import all Obend.Lower.Pancake.SpongeFrame
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.PanSem
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Kmac256

/-!
KMAC256 in Pancake with no Lean runtime, in two exported functions over the sponge frame of
`PancakeCshake256`.

`kmac256` takes raw key, customization and message slices in the six-word descriptor. It builds
the whole SP 800-185 frame, zeroes the state and absorbs. `kmacResume` starts instead from a
25-word state that already absorbed the rate-aligned prefix, so a caller with a fixed key pays
for the two static blocks once. It frames only the message, with `right_encode(256)` when
`trailer` is nonzero (KMAC) and without it when `trailer` is zero (cSHAKE256). Its descriptor has
the same six words, and only the message slice is read.

Both kernels leave the framed bytes and the full permuted state in caller-owned memory.
Callers should clear these buffers after copying the digest. Treat a saved keyed midstate as
secret key material.
-/

public section
namespace Obend.Lower.Pancake.Sponge.Kmac
open Obend.Digest Obend.Digest.Kmac256 WordBuffer ByteMemory
set_option autoImplicit false

/-- `left_encode(136)`, the `bytepad` width. -/
def rateField : List Nat := [1, 136]

/-- `encode_string("KMAC")`. -/
def nameField : List Nat := [1, 32, 75, 77, 65, 67]

/-- `right_encode(256)`. -/
def outputField : List Nat := [1, 0, 2]

private def writeField (bs : List Nat) : PStmt :=
  seqs (bs.map fun b => writeByte (lit b)) .skip

/-- `bytepad(head ‖ encode_string(x), 136)`, written from a rate boundary. -/
private def bytepadSection (head : List Nat) (ptr len : PExp) : PStmt :=
  seqs [writeField rateField, writeField head, writeLength len, copySlice ptr len] alignFrame

/-- Name block, key block, message, `right_encode(256)` and the final padding. -/
def writeFrame : PStmt := seqs [
  bytepadSection nameField (desc 2) (desc 3),
  bytepadSection [] (desc 0) (desc 1),
  copySlice (desc 4) (desc 5),
  writeField outputField] finishFrame

def writeTail : PStmt := .seq (copySlice (desc 4) (desc 5)) finishFrame

def writeTrailedTail : PStmt :=
  seqs [copySlice (desc 4) (desc 5), writeField outputField] finishFrame

private def withLocals (body : PStmt) : PStmt :=
  .dec "used" .One (lit 0) <| .dec "limit" .One (lit 0) <|
  .dec "blocks" .One (lit 0) <| .dec "suffix" .One (.const customSuffix) <|
  .dec "input" .One (v "frame") <| .dec "i" .One (lit 0) body

private def oneShot : PStmt :=
  seqs [writeFrame, lowerStage "base" (fun _ => .lit 0), absorbLoop] (.ret (lit 0))

private def resumed : PStmt :=
  seqs [.ite (v "trailer") writeTrailedTail writeTail, absorbLoop] (.ret (lit 0))

/-- SysV arguments: a writable 25-word state, an aligned workspace of
    `|K|+|S|+|X|+440` bytes, and the descriptor (key, customization, message pointer and length
    pairs). On return, the first 32 bytes of the state are the tag. -/
def kernel : PFun :=
  ⟨"kmac256", [("base", .One), ("frame", .One), ("slices", .One)], withLocals oneShot, true⟩

/-- SysV arguments: the absorbed 25-word state, an aligned workspace of `|X|+294` bytes, the
    descriptor (only the message pair is read) and the trailer flag. -/
def resumeKernel : PFun :=
  ⟨"kmacResume", [("base", .One), ("frame", .One), ("slices", .One), ("trailer", .One)],
    withLocals resumed, true⟩

/-- The bytes a resumed call absorbs before padding. -/
def resumeTail (trailer : Word) (message : List UInt8) : List UInt8 :=
  if trailer = 0 then message else message ++ rightEncode 256

/-! ## Frame contents -/

private def start : Cursor := {suffix := customSuffix}

private theorem byte_lit (n : Nat) : byteOf (word n) = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  change ((word n).setWidth 8).toNat = (BitVec.ofNat 8 n).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem suffix_byte : byteOf customSuffix = 4 := by decide

private theorem output_bytes : outputField.map UInt8.ofNat = rightEncode 256 := by decide +kernel

private theorem name_bytes :
    nameField.map UInt8.ofNat = Cshake256.encodeString functionName := by decide +kernel

private theorem field_correct {c} (ok : Valid c) (bs : List Nat) (u : Cursor)
    (space : u.bytes.length + bs.length ≤ c.capacity) :
    Runs c (writeField bs) u {u with bytes := u.bytes ++ bs.map UInt8.ofNat} := by
  let items := bs.map fun b => ((lit b : PExp), word b)
  have go := emit_words ok items (by
    intro i hi z
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hi
    exact reads_lit _) u (by simpa [items] using space)
  simpa [writeField, items, List.map_map, Function.comp_def, byte_lit] using go

private def rawSection (head : List Nat) (x : List UInt8) : List UInt8 :=
  [1, 136] ++ head.map UInt8.ofNat ++ Cshake256.encodeString x

private abbrev padBlock (head : List Nat) (x : List UInt8) : List UInt8 :=
  Cshake256.bytepad (head.map UInt8.ofNat ++ Cshake256.encodeString x) 136

private theorem section_eq (head : List Nat) (x : List UInt8) :
    padBlock head x =
      rawSection head x ++ List.replicate ((136 - (rawSection head x).length % 136) % 136) 0 := by
  have h : Cshake256.leftEncode 136 = [1, 136] := rfl
  simp [Cshake256.bytepad, rawSection, h, List.append_assoc]

private theorem section_length (head : List Nat) (x : List UInt8) (bound : x.length < 2^64) :
    (padBlock head x).length ≤ head.length + x.length + 147 := by
  have n := leftEncode_bound bound
  rw [section_eq, List.length_append, List.length_replicate]
  simp only [rawSection, Cshake256.encodeString, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

private theorem section_correct {c} (ok : Valid c) (head : List Nat) (x : Slice)
    (hx : x ∈ [c.name, c.custom, c.message]) (ptr len : PExp)
    (hp : ∀ u, Reads c u ptr x.ptr) (hl : ∀ u, Reads c u len (word x.bytes.length))
    (u : Cursor) (aligned : u.bytes.length = 136 * u.blocks)
    (space : u.bytes.length + head.length + x.bytes.length + 147 ≤ c.capacity) :
    Runs c (bytepadSection head ptr len) u
      {u with
        bytes := u.bytes ++ padBlock head x.bytes
        blocks := u.blocks + (padBlock head x.bytes).length / 136
        index := x.bytes.length} := by
  have size := ok.size
  have bound : x.bytes.length < 2^64 := by omega
  have henc := leftEncode_bound bound
  let u1 : Cursor := {u with bytes := u.bytes ++ rateField.map UInt8.ofNat}
  let u2 : Cursor := {u1 with bytes := u1.bytes ++ head.map UInt8.ofNat}
  let u3 : Cursor := {u2 with bytes := u2.bytes ++ Cshake256.leftEncode (8 * x.bytes.length)}
  let u4 : Cursor := {u3 with bytes := u3.bytes ++ x.bytes, index := x.bytes.length}
  have l1 : u1.bytes.length = u.bytes.length + 2 := by simp [u1, rateField]
  have l2 : u2.bytes.length = u.bytes.length + 2 + head.length := by
    simp [u2, l1]
  have l3 : u3.bytes.length =
      u.bytes.length + 2 + head.length + (Cshake256.leftEncode (8 * x.bytes.length)).length := by
    simp [u3, l2]
  have l4 : u4.bytes.length = u3.bytes.length + x.bytes.length := by simp [u4]
  have a1 : Runs c (writeField rateField) u u1 :=
    field_correct ok _ u (by simp only [rateField, List.length_cons, List.length_nil]; omega)
  have a2 : Runs c (writeField head) u1 u2 := field_correct ok _ u1 (by omega)
  have a3 : Runs c (writeLength len) u2 u3 := length_correct ok hl bound u2 (by omega)
  have a4 : Runs c (copySlice ptr len) u3 u4 := copy_slice ok x hx ptr len hp hl u3 (by omega)
  have a5 := align_correct ok u4 (by change 136 * u.blocks ≤ _; omega) (by omega)
  have raw : u4.bytes = u.bytes ++ rawSection head x.bytes := by
    simp [u4, u3, u2, u1, rawSection, rateField, Cshake256.encodeString, List.append_assoc]
  have hlen : u4.bytes.length = 136 * u.blocks + (rawSection head x.bytes).length := by
    rw [raw, List.length_append, aligned]
  have count : (136 - u4.bytes.length % 136) % 136 =
      (136 - (rawSection head x.bytes).length % 136) % 136 := by omega
  have bytes : u4.bytes ++ List.replicate ((136 - u4.bytes.length % 136) % 136) 0 =
      u.bytes ++ padBlock head x.bytes := by
    rw [count, raw, section_eq, List.append_assoc]
  have blocks : (u4.bytes.length + 135) / 136 =
      u.blocks + (padBlock head x.bytes).length / 136 := by
    rw [section_eq, hlen, List.length_append, List.length_replicate]
    omega
  have final : ({u4 with
      bytes := u4.bytes ++ List.replicate ((136 - u4.bytes.length % 136) % 136) 0
      blocks := (u4.bytes.length + 135) / 136} : Cursor) =
      {u with
        bytes := u.bytes ++ padBlock head x.bytes
        blocks := u.blocks + (padBlock head x.bytes).length / 136
        index := x.bytes.length} := by
    rw [bytes, blocks]
  exact final ▸ a1.seq (a2.seq (a3.seq (a4.seq a5)))

private theorem prefix_section (custom : List UInt8) :
    padBlock nameField custom = kmacPrefix custom := by
  simp only [padBlock, kmacPrefix, name_bytes, Cshake256.rateBytes]

private theorem key_section (key : List UInt8) : padBlock [] key = kmacKeyBlock key := by
  simp [padBlock, kmacKeyBlock, Cshake256.rateBytes]

private theorem section_aligned (head : List Nat) (x : List UInt8) :
    (padBlock head x).length % 136 = 0 := by
  simpa only [Cshake256.rateBytes] using
    bytepad_length_mod (head.map UInt8.ofNat ++ Cshake256.encodeString x)

/-- The padded KMAC stream before absorption. -/
private def framed (c : Layout) : List UInt8 :=
  Cshake256.padForRate (kmacPrefix c.custom.bytes ++
    (kmacKeyBlock c.name.bytes ++ c.message.bytes ++ rightEncode 256)) 4

private def frameCursor (c : Layout) : Cursor :=
  ⟨framed c, (framed c).length / 136, c.message.bytes.length, customSuffix⟩

private theorem frame_correct {c} (ok : Valid c) (room : 146 ≤ c.headroom) :
    Runs c writeFrame start (frameCursor c) ∧ (framed c).length ≤ c.capacity := by
  have cap : c.capacity = c.name.bytes.length + c.custom.bytes.length +
      c.message.bytes.length + 294 + c.headroom := rfl
  have size := ok.size
  let pre := padBlock nameField c.custom.bytes
  let key := padBlock [] c.name.bytes
  have hpre : pre.length ≤ 6 + c.custom.bytes.length + 147 :=
    section_length nameField c.custom.bytes (by omega)
  have hkey : key.length ≤ 0 + c.name.bytes.length + 147 :=
    section_length [] c.name.bytes (by omega)
  have apre : pre.length % 136 = 0 := section_aligned _ _
  have akey : key.length % 136 = 0 := section_aligned _ _
  let u1 : Cursor := {start with
    bytes := start.bytes ++ pre, blocks := start.blocks + pre.length / 136
    index := c.custom.bytes.length}
  let u2 : Cursor := {u1 with
    bytes := u1.bytes ++ key, blocks := u1.blocks + key.length / 136
    index := c.name.bytes.length}
  let u3 : Cursor := {u2 with
    bytes := u2.bytes ++ c.message.bytes, index := c.message.bytes.length}
  let u4 : Cursor := {u3 with bytes := u3.bytes ++ outputField.map UInt8.ofNat}
  have b1 : u1.bytes.length = pre.length := by simp [u1, start]
  have c1 : u1.blocks = pre.length / 136 := by simp [u1, start]
  have b2 : u2.bytes.length = pre.length + key.length := by simp [u2, b1]
  have c2 : u2.blocks = pre.length / 136 + key.length / 136 := by simp [u2, c1]
  have b3 : u3.bytes.length = pre.length + key.length + c.message.bytes.length := by
    simp [u3, b2]
  have b4 : u4.bytes.length = pre.length + key.length + c.message.bytes.length + 3 := by
    simp [u4, b3, outputField]
  have s1 : Runs c (bytepadSection nameField (desc 2) (desc 3)) start u1 :=
    section_correct ok nameField c.custom (by simp) (desc 2) (desc 3)
      (fun _ => reads_desc ok 2) (fun _ => reads_desc ok 3) start (by simp [start])
      (by simp [start, nameField]; omega)
  have s2 : Runs c (bytepadSection [] (desc 0) (desc 1)) u1 u2 :=
    section_correct ok [] c.name (by simp) (desc 0) (desc 1)
      (fun _ => reads_desc ok 0) (fun _ => reads_desc ok 1) u1 (by rw [b1, c1]; omega)
      (by simp only [b1, List.length_nil]; omega)
  have s3 : Runs c (copySlice (desc 4) (desc 5)) u2 u3 :=
    copy_slice ok c.message (by simp) (desc 4) (desc 5)
      (fun _ => reads_desc ok 4) (fun _ => reads_desc ok 5) u2 (by omega)
  have s4 : Runs c (writeField outputField) u3 u4 :=
    field_correct ok _ u3 (by simp only [outputField, List.length_cons, List.length_nil]; omega)
  have s5 := finish_correct ok u4 (by change 136 * u2.blocks ≤ _; omega) (by omega)
  have stream : u4.bytes = kmacPrefix c.custom.bytes ++
      (kmacKeyBlock c.name.bytes ++ c.message.bytes ++ rightEncode 256) := by
    simp [u4, u3, u2, u1, start, pre, key, prefix_section, key_section, output_bytes,
      List.append_assoc]
  have hframed : Cshake256.padForRate u4.bytes (byteOf u4.suffix) = framed c := by
    rw [stream]
    change Cshake256.padForRate _ (byteOf customSuffix) = _
    rw [suffix_byte]
    rfl
  have hlen : (framed c).length = 136 * ((u4.bytes.length + 136) / 136) := by
    rw [← hframed, padded_blocks]
  have final : ({u4 with
      bytes := Cshake256.padForRate u4.bytes (byteOf u4.suffix)
      blocks := (u4.bytes.length + 136) / 136} : Cursor) = frameCursor c := by
    have count : (u4.bytes.length + 136) / 136 = (framed c).length / 136 := by omega
    rw [hframed, count]
    rfl
  refine ⟨final ▸ s1.seq (s2.seq (s3.seq (s4.seq s5))), ?_⟩
  omega

/-! ## Executing the kernels -/

private theorem dec_word {τ} {p : PStmt} {e : PExp} {x : String} {a : PanState τ} {w b : Word}
    {out : List UInt8} (he : eval a e = some (.word w))
    (h : ∃ t, evaluate p {a with locals := FUPDATE a.locals (x, .word w)} = (.ret (.word 0), t) ∧
      digestAt t.memory b = out) :
    ∃ t, evaluate (.dec x .One e p) a = (.ret (.word 0), t) ∧ digestAt t.memory b = out := by
  obtain ⟨t, ht, rt⟩ := h
  rw [evaluate_dec, he]
  simp only [shape_of_word, BEq.rfl, ite_true, ht]
  exact ⟨_, rfl, rt⟩

/-- The six scratch locals, then `body` from the start cursor. Other locals and the clock are
    unchanged when `body` begins. -/
private theorem locals_correct {c : Layout} {τ} (s : PanState τ) (body : PStmt) (out : List UInt8)
    (base : s.locals "base" = some (.word c.base)) (frame : s.locals "frame" = some (.word c.frame))
    (table : s.locals "slices" = some (.word c.table)) (mem : s.memory = c.memory)
    (dm : s.memaddrs = c.domain) (le : s.be = false)
    (run : ∀ r : PanState τ, Rep c start r → r.clock = s.clock →
      (∀ x, x ∉ ["used", "limit", "blocks", "suffix", "input", "i"] → r.locals x = s.locals x) →
      ∃ t, evaluate body r = (.ret (.word 0), t) ∧ digestAt t.memory c.base = out) :
    ∃ t, evaluate (withLocals body) s = (.ret (.word 0), t) ∧ digestAt t.memory c.base = out := by
  change ∃ t, evaluate (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
    (.dec _ _ _ body)))))) s = _ ∧ _
  apply dec_word (w := 0) rfl
  apply dec_word (w := 0) rfl
  apply dec_word (w := 0) rfl
  apply dec_word (w := customSuffix) rfl
  apply dec_word (w := c.frame) (by simp [FUPDATE, frame])
  apply dec_word (w := 0) rfl
  apply run
  · exact ⟨fun reg => by
      cases reg <;> simp [Reg.name, Reg.val, FUPDATE, base, frame, table, start], dm, le,
      fun a _ => congrFun mem a, fun _ h => by cases h⟩
  · rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [FUPDATE, hx]

private theorem oneShot_correct {c} (ok : Valid c) (room : 146 ≤ c.headroom) :
    ∃ fuel, ∀ {τ} (s : PanState τ), Rep c start s → fuel ≤ s.clock →
      ∃ t, evaluate oneShot s = (.ret (.word 0), t) ∧
        digestAt t.memory c.base = kmac256Bytes c.name.bytes c.custom.bytes c.message.bytes := by
  obtain ⟨⟨f, hp⟩, size⟩ := frame_correct ok room
  let u := frameCursor c
  refine ⟨f + u.blocks, fun s rep hclk => ?_⟩
  obtain ⟨r, hframe, hr, cf⟩ := hp s rep (by omega)
  have base : r.locals "base" = some (.word c.base) := hr.regs .base
  have mapped : Mapped r c.base := by intro i; rw [hr.domain]; exact (ok.base i).1
  obtain ⟨m, hz, rz, fz⟩ := lowerStage_correct r "base" c.base base mapped (fun _ => .lit 0)
  let z := {r with memory := m}
  have hb := holds_packed ok hr.bytes size
  have packed : Packed z.memaddrs z.memory c.base c.frame u.blocks u.bytes := by
    intro k hk i
    obtain ⟨hd, hv, away⟩ := hb k hk i
    exact ⟨hr.domain ▸ hd, (fz _ away).trans hv, away⟩
  have cap := ok.size
  obtain ⟨t, ht, rt, _⟩ := absorbLoop_correct u.blocks z c.base c.frame Cshake256.zeroState u.bytes
    (by change (framed c).length / 136 < _; omega) (by change u.blocks ≤ r.clock; omega)
    base (hr.regs .input) (hr.regs .blocks) mapped (by
      intro i
      rw [show z.memory = m from rfl, rz i]
      simp [runStage, Expr.value, Keccak.lanes, Cshake256.zeroState, Cshake256.zeroLane,
        Array.getD_eq_getD_getElem?, i.isLt]) packed
  refine ⟨empty_locals t, ?_, digest_lanes ok rt⟩
  have seqEval {τ} {p q : PStmt} {a b : PanState τ} (h : evaluate p a = (.normal, b)) :
      evaluate (.seq p q) a = evaluate q b := by rw [evaluate_seq, h]; rfl
  change evaluate (.seq _ (.seq _ (.seq _ _))) s = _
  rw [seqEval hframe, seqEval hz, seqEval ht]
  exact evaluate_ret _ _

/-- End-to-end execution of the exported one-shot function over raw key, customization and
    message slices. A valid layout with at least 146 bytes of headroom supplies their contents,
    the mapped workspace and its separation from the reads. The state and work buffer may hold
    arbitrary initial words. Fuel depends only on the input layout. -/
theorem pancakeKmac256_correct (c : Layout) (ok : Valid c) (room : 146 ≤ c.headroom) :
    ∃ fuel, ∀ {τ} (s : PanState τ), fuel ≤ s.clock →
      s.locals "base" = some (.word c.base) → s.locals "frame" = some (.word c.frame) →
      s.locals "slices" = some (.word c.table) → s.memory = c.memory →
      s.memaddrs = c.domain → s.be = false →
      ∃ t, evaluate kernel.body s = (.ret (.word 0), t) ∧
        digestAt t.memory c.base = kmac256Bytes c.name.bytes c.custom.bytes c.message.bytes := by
  obtain ⟨f, run⟩ := oneShot_correct ok room
  refine ⟨f, fun s fuel base frame table mem dm le => ?_⟩
  exact locals_correct s oneShot _ base frame table mem dm le
    fun r rep clock _ => run r rep (by omega)

private def tailCursor (c : Layout) (trailer : Word) : Cursor :=
  let bytes := Cshake256.padForRate (resumeTail trailer c.message.bytes) 4
  ⟨bytes, bytes.length / 136, c.message.bytes.length, customSuffix⟩

private theorem tail_correct {c} (ok : Valid c) (trailer : Word) :
    Runs c (if trailer = 0 then writeTail else writeTrailedTail) start (tailCursor c trailer) ∧
      (tailCursor c trailer).bytes.length ≤ c.capacity := by
  have cap : c.capacity = c.name.bytes.length + c.custom.bytes.length +
      c.message.bytes.length + 294 + c.headroom := rfl
  let u1 : Cursor := {start with
    bytes := start.bytes ++ c.message.bytes, index := c.message.bytes.length}
  have l1 : u1.bytes.length = c.message.bytes.length := by simp [u1, start]
  have copy : Runs c (copySlice (desc 4) (desc 5)) start u1 :=
    copy_slice ok c.message (by simp) (desc 4) (desc 5)
      (fun _ => reads_desc ok 4) (fun _ => reads_desc ok 5) start
      (by simp only [start, List.length_nil]; omega)
  by_cases zero : trailer = 0
  · have hb : u1.bytes = resumeTail trailer c.message.bytes := by
      rw [resumeTail, ite_eq_left zero]
      simp [u1, start]
    have s2 := finish_correct ok u1 (by change 0 ≤ _; omega) (by omega)
    have pad : Cshake256.padForRate u1.bytes (byteOf u1.suffix) =
        (tailCursor c trailer).bytes := by
      rw [hb]
      change Cshake256.padForRate _ (byteOf customSuffix) = _
      rw [suffix_byte]
      rfl
    have hlen : (tailCursor c trailer).bytes.length = 136 * ((u1.bytes.length + 136) / 136) := by
      rw [← pad, padded_blocks]
    have final : ({u1 with
        bytes := Cshake256.padForRate u1.bytes (byteOf u1.suffix)
        blocks := (u1.bytes.length + 136) / 136} : Cursor) = tailCursor c trailer := by
      have count : (u1.bytes.length + 136) / 136 = (tailCursor c trailer).bytes.length / 136 := by
        omega
      rw [pad, count]
      rfl
    rw [ite_eq_left zero]
    exact ⟨final ▸ copy.seq s2, by omega⟩
  · let u2 : Cursor := {u1 with bytes := u1.bytes ++ outputField.map UInt8.ofNat}
    have l2 : u2.bytes.length = c.message.bytes.length + 3 := by simp [u2, l1, outputField]
    have field : Runs c (writeField outputField) u1 u2 :=
      field_correct ok _ u1 (by simp only [outputField, List.length_cons, List.length_nil]; omega)
    have hb : u2.bytes = resumeTail trailer c.message.bytes := by
      rw [resumeTail, ite_eq_right zero]
      simp [u2, u1, start, output_bytes]
    have s3 := finish_correct ok u2 (by change 0 ≤ _; omega) (by omega)
    have pad : Cshake256.padForRate u2.bytes (byteOf u2.suffix) =
        (tailCursor c trailer).bytes := by
      rw [hb]
      change Cshake256.padForRate _ (byteOf customSuffix) = _
      rw [suffix_byte]
      rfl
    have hlen : (tailCursor c trailer).bytes.length = 136 * ((u2.bytes.length + 136) / 136) := by
      rw [← pad, padded_blocks]
    have final : ({u2 with
        bytes := Cshake256.padForRate u2.bytes (byteOf u2.suffix)
        blocks := (u2.bytes.length + 136) / 136} : Cursor) = tailCursor c trailer := by
      have count : (u2.bytes.length + 136) / 136 = (tailCursor c trailer).bytes.length / 136 := by
        omega
      rw [pad, count]
      rfl
    rw [ite_eq_right zero]
    exact ⟨final ▸ copy.seq (field.seq s3), by omega⟩

private theorem resumed_correct {c} (ok : Valid c) (src : Cshake256.State) (trailer : Word)
    (state : ∀ i : Fin 25, c.memory (address c.base i) = Keccak.lanes src i) :
    ∃ fuel, ∀ {τ} (s : PanState τ), Rep c start s → s.locals "trailer" = some (.word trailer) →
      fuel ≤ s.clock → ∃ t, evaluate resumed s = (.ret (.word 0), t) ∧ digestAt t.memory c.base =
        Cshake256.squeeze32 (resumeFromState src (resumeTail trailer c.message.bytes) 4) := by
  obtain ⟨⟨f, hp⟩, size⟩ := tail_correct ok trailer
  let u := tailCursor c trailer
  refine ⟨f + u.blocks, fun s rep flag hclk => ?_⟩
  have branch : evaluate (.ite (v "trailer") writeTrailedTail writeTail) s =
      evaluate (if trailer = 0 then writeTail else writeTrailedTail) s := by
    rw [evaluate_ite, eval_lvar, flag]
    dsimp only
    by_cases zero : trailer = 0
    · have h0 : trailer = 0#64 := zero
      rw [ite_eq_left zero, h0]
      rfl
    · have hne : trailer ≠ 0#64 := zero
      simp only [bne_iff_ne.mpr hne, ite_true]
      rw [ite_eq_right zero]
  have sized : u.bytes.length ≤ c.capacity := size
  obtain ⟨r, hframe, hr, cf⟩ := hp s rep (by omega)
  have base : r.locals "base" = some (.word c.base) := hr.regs .base
  have mapped : Mapped r c.base := by intro i; rw [hr.domain]; exact (ok.base i).1
  have packed : Packed r.memaddrs r.memory c.base c.frame u.blocks u.bytes := by
    have hb := holds_packed ok hr.bytes size
    intro k hk i
    obtain ⟨hd, hv, away⟩ := hb k hk i
    exact ⟨hr.domain ▸ hd, hv, away⟩
  have cap := ok.size
  obtain ⟨t, ht, rt, _⟩ := absorbLoop_correct u.blocks r c.base c.frame src u.bytes
    (by change u.bytes.length / 136 < _; omega) (by omega)
    base (hr.regs .input) (hr.regs .blocks) mapped
    (fun i => (hr.outside _ (ok.base i).2).trans (state i)) packed
  refine ⟨empty_locals t, ?_, digest_lanes ok rt⟩
  have seqEval {τ} {p q : PStmt} {a b : PanState τ} (h : evaluate p a = (.normal, b)) :
      evaluate (.seq p q) a = evaluate q b := by rw [evaluate_seq, h]; rfl
  change evaluate (.seq _ (.seq _ _)) s = _
  rw [seqEval (branch.trans hframe), seqEval ht]
  exact evaluate_ret _ _

/-- End-to-end execution of the exported resume function from an arbitrary absorbed state. The
    state words are read in place, the message slice is framed with the trailer selected by the
    flag, and the first 32 bytes of the state are the squeezed result. -/
theorem pancakeResume_correct (c : Layout) (ok : Valid c) (src : Cshake256.State) (trailer : Word)
    (state : ∀ i : Fin 25, c.memory (address c.base i) = Keccak.lanes src i) :
    ∃ fuel, ∀ {τ} (s : PanState τ), fuel ≤ s.clock →
      s.locals "base" = some (.word c.base) → s.locals "frame" = some (.word c.frame) →
      s.locals "slices" = some (.word c.table) → s.locals "trailer" = some (.word trailer) →
      s.memory = c.memory → s.memaddrs = c.domain → s.be = false →
      ∃ t, evaluate resumeKernel.body s = (.ret (.word 0), t) ∧ digestAt t.memory c.base =
        Cshake256.squeeze32 (resumeFromState src (resumeTail trailer c.message.bytes) 4) := by
  obtain ⟨f, run⟩ := resumed_correct ok src trailer state
  refine ⟨f, fun s fuel base frame table flag mem dm le => ?_⟩
  exact locals_correct s resumed _ base frame table mem dm le fun r rep clock same =>
    run r rep ((same "trailer" (by simp)).trans flag) (by omega)

/-- Resuming with the KMAC trailer from the state after the name and key blocks is the one-shot
    tag, for every message. -/
theorem pancakeKmacResume_correct (c : Layout) (ok : Valid c) (key custom : List UInt8)
    (trailer : Word) (nonzero : trailer ≠ 0)
    (state : ∀ i : Fin 25, c.memory (address c.base i) = Keccak.lanes (kmacMidstate key custom) i) :
    ∃ fuel, ∀ {τ} (s : PanState τ), fuel ≤ s.clock →
      s.locals "base" = some (.word c.base) → s.locals "frame" = some (.word c.frame) →
      s.locals "slices" = some (.word c.table) → s.locals "trailer" = some (.word trailer) →
      s.memory = c.memory → s.memaddrs = c.domain → s.be = false →
      ∃ t, evaluate resumeKernel.body s = (.ret (.word 0), t) ∧
        digestAt t.memory c.base = kmac256Bytes key custom c.message.bytes := by
  have tail : resumeTail trailer c.message.bytes = c.message.bytes ++ rightEncode 256 := by
    rw [resumeTail, ite_eq_right nonzero]
  rw [kmac256Bytes_resume]
  simpa only [tail] using pancakeResume_correct c ok _ trailer state

/-- Resuming without a trailer from a cSHAKE256 prefix state is the named digest. -/
theorem pancakeCshakeResume_correct (c : Layout) (ok : Valid c) (name custom : List UInt8)
    (named : ¬(name = [] ∧ custom = []))
    (state : ∀ i : Fin 25, c.memory (address c.base i) = Keccak.lanes (cshakeMidstate name custom) i) :
    ∃ fuel, ∀ {τ} (s : PanState τ), fuel ≤ s.clock →
      s.locals "base" = some (.word c.base) → s.locals "frame" = some (.word c.frame) →
      s.locals "slices" = some (.word c.table) → s.locals "trailer" = some (.word 0) →
      s.memory = c.memory → s.memaddrs = c.domain → s.be = false →
      ∃ t, evaluate resumeKernel.body s = (.ret (.word 0), t) ∧
        digestAt t.memory c.base = Cshake256.namedBytes name custom c.message.bytes := by
  have tail : resumeTail 0 c.message.bytes = c.message.bytes := by simp [resumeTail]
  rw [namedBytes_resume _ _ _ named]
  simpa only [tail] using pancakeResume_correct c ok _ 0 state

end Obend.Lower.Pancake.Sponge.Kmac
