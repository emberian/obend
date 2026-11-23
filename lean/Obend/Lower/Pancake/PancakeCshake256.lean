module
public import Obend.Lower.Pancake.SpongeFrame
import all Obend.Lower.Pancake.SpongeFrame
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Digest.Cshake256.Fast
public import Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.PanSem
import all Obend.Digest.Cshake256.Spec

public section
namespace Obend.Lower.Pancake.Sponge
open Obend.Digest WordBuffer ByteMemory

private def field (i : Fin 25) : PExp :=
  let old := loadAt "base" (8*i.val)
  if i.val < rateWords then .binop .Xor [old, loadAt "input" (8*i.val)] else old

def xorBlock := PStmt.store (v "base") (.rstruct ((List.finRange 25).map field))

private def advance := PStmt.seq (bump "input" (8*rateWords))
  (.lassign "blocks" (sub (v "blocks") (lit 1)))

/-- The state occupies 25 aligned words. Each iteration consumes 17 little-endian
    input words and applies all 24 rounds. The first four state words are the digest. -/
def absorbLoop := PStmt.while_ (v "blocks") (.seq xorBlock
  (Keccak.roundsThen "base" advance Cshake256.roundConstants))

/-- SysV arguments are a writable 25-word state, aligned frame workspace, and
    six words (N pointer/length, S pointer/length, X pointer/length). The three
    input slices are read-only. Reserve |N|+|S|+|X|+294 bytes in the frame.
    On return, the first 32 bytes of the state are the digest. -/
def kernel : PFun := ⟨"cshake256", [("base", .One), ("frame", .One), ("slices", .One)],
  .dec "used" .One (lit 0) <| .dec "limit" .One (lit 0) <|
  .dec "blocks" .One (lit 0) <| .dec "suffix" .One (.const shakeSuffix) <|
  .dec "input" .One (v "frame") <| .dec "i" .One (lit 0) <| seqs [
    prepareFrame, lowerStage "base" (fun _ => .lit 0), absorbLoop] (.ret (lit 0)), true⟩

/-- A read-only packed frame, disjoint from the 25 state words. Each word is
    related directly to the eight bytes that the list specification absorbs. -/
def Packed (dm : Word → Bool) (m : Word → Word) (base input : Word)
    (count : Nat) (bytes : List UInt8) : Prop :=
  ∀ k, k < count → ∀ i : Fin 17,
    let a := address (input + BitVec.ofNat 64 (136*k)) i
    dm a = true ∧ m a = Cshake256.laneFromBlock
      ((bytes.drop (136*k)).take 136) i ∧ ∀ j : Fin 25, a ≠ address base j

private theorem loadAt_eval {τ} (s : PanState τ) (p : String) (ptr : Word) (i : Nat)
    (hp : s.locals p = some (.word ptr)) (hm : s.memaddrs (address ptr i) = true) :
    eval s (loadAt p (8*i)) = some (.word (s.memory (address ptr i))) := by
  simpa [loadAt, atOffset, add, lit, eval, evalList, extractWords, word_op,
    hp, mem_load, address] using hm

private theorem xorBlock_correct {τ} (s : PanState τ) (b p : Word) (state : Cshake256.State)
    (bytes : List UInt8) (hp : s.locals "base" = some (.word b))
    (hi : s.locals "input" = some (.word p)) (hm : Mapped s b)
    (hr : ∀ i : Fin 25, s.memory (address b i) = Keccak.lanes state i)
    (hb : ∀ i : Fin 17, s.memaddrs (address p i) = true ∧
      s.memory (address p i) = Cshake256.laneFromBlock bytes i) :
    ∃ m, evaluate xorBlock s = (.normal, {s with memory := m}) ∧
      (∀ i : Fin 25, m (address b i) = Keccak.lanes (Cshake256.xorRateBlock state bytes) i) ∧
      ∀ a, (∀ j : Fin 25, a ≠ address b j) → m a = s.memory a := by
  apply storeFields_correct s "base" b hp hm
  intro i
  have old := loadAt_eval s "base" b i hp (hm i)
  simp only [Cshake256.xorRateBlock, Keccak.read_ofFn]
  by_cases h : i.val < 17
  · obtain ⟨ha, hv⟩ := hb ⟨i,h⟩
    have src := loadAt_eval s "input" p i hi ha
    simp [field, rateWords, Cshake256.rateLanes, h, old, src, word_op, hr, hv, Keccak.lanes]
  · simp [field, rateWords, Cshake256.rateLanes, h, old, hr, Keccak.lanes]

private theorem packed_tail {dm m m' b p n bs}
    (hp : Packed dm m b p (n+1) bs)
    (hf : ∀ a, (∀ j : Fin 25, a ≠ address b j) → m' a = m a) :
    Packed dm m' b (p+136) n (bs.drop 136) := by
  intro k hk i
  have h := hp (k+1) (by omega) i
  dsimp only at h ⊢
  rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_comm _ (136#64),
    ← BitVec.add_assoc] at h
  rw [List.drop_drop, Nat.add_comm 136, ← Nat.mul_succ]
  exact ⟨h.1, (hf _ h.2.2).trans h.2.1, h.2.2⟩

private theorem advance_eval {τ} (s : PanState τ) (p n : Word)
    (hi : s.locals "input" = some (.word p)) (hn : s.locals "blocks" = some (.word n)) :
    evaluate advance s = (.normal, set_var "blocks" (.word (n-1))
      (set_var "input" (.word (p+136)) s)) := by
  simp [advance, bump, atOffset, rateWords, lit, add, sub, evaluate_seq, evaluate_assign,
    word_op, hi, hn, is_valid_value_local, set_kvar, set_var, FUPDATE]

/-- Arbitrary-block refinement of the actual Pancake while statement, including
    its clock, pointer advances, state accumulation, and memory frame. -/
theorem absorbLoop_correct {τ} (count : Nat) (s : PanState τ) (b p : Word)
    (src : Cshake256.State) (bytes : List UInt8) (bound : count < 2^64)
    (fuel : count ≤ s.clock) (hp : s.locals "base" = some (.word b))
    (hi : s.locals "input" = some (.word p))
    (hn : s.locals "blocks" = some (.word (BitVec.ofNat 64 count)))
    (hm : Mapped s b) (reads : ∀ i : Fin 25, s.memory (address b i) = Keccak.lanes src i)
    (packed : Packed s.memaddrs s.memory b p count bytes) :
    ∃ t, evaluate absorbLoop s = (.normal, t) ∧
      (∀ i : Fin 25, t.memory (address b i) = Keccak.lanes (Cshake256.absorbFrom count src bytes) i) ∧
      ∀ a, (∀ j : Fin 25, a ≠ address b j) → t.memory a = s.memory a := by
  induction count generalizing s p src bytes with
  | zero =>
    refine ⟨s, ?_, reads, fun _ _ => rfl⟩
    rw [absorbLoop, evaluate_while, eval_lvar, hn]
    rfl
  | succ n ih =>
    let w := BitVec.ofNat 64 (n+1)
    have hw : w ≠ 0 := by
      intro h
      have e := congrArg BitVec.toNat h
      simp [w, Nat.mod_eq_of_lt bound] at e
    have hclk : s.clock ≠ 0 := by omega
    let block := bytes.take 136
    obtain ⟨mx, hx, rx, fx⟩ := xorBlock_correct (dec_clock s) b p src block hp hi hm reads (by
      intro i
      have h := packed 0 (Nat.zero_lt_succ _) i
      simpa [block, dec_clock] using And.intro h.1 h.2.1)
    let sx := {dec_clock s with memory := mx}
    obtain ⟨mk, hk, rk, fk⟩ := Keccak.roundsThen_correct Cshake256.roundConstants sx "base"
      advance b hp hm (Cshake256.xorRateBlock src block) rx
    let sk := {sx with memory := mk}
    let t := set_var "blocks" (.word (w-1)) (set_var "input" (.word (p+136)) sk)
    have ha : evaluate advance sk = (.normal,t) := advance_eval sk p w hi hn
    have hf (a : Word) (h : ∀ j : Fin 25, a ≠ address b j) :
        t.memory a = s.memory a := (fk a h).trans (fx a h)
    have hsub : w - 1 = BitVec.ofNat 64 n := by rw [show w = BitVec.ofNat 64 n + 1 from BitVec.ofNat_add .., BitVec.add_sub_cancel]
    obtain ⟨u, hu, ru, fu⟩ := ih t (p+136) (Cshake256.keccakF1600 (Cshake256.xorRateBlock src block))
      (bytes.drop 136) (by omega) (by change n ≤ s.clock-1; omega)
      (by simpa [t, sk, sx, dec_clock, set_var, FUPDATE] using hp)
      (by simp [t, set_var, FUPDATE]) (by simpa [t, set_var, FUPDATE] using hsub) hm rk
      (packed_tail packed hf)
    refine ⟨u, ?_, ru, fun a away => (fu a away).trans (hf a away)⟩
    have hbody : evaluate (.seq xorBlock (Keccak.roundsThen "base" advance Cshake256.roundConstants))
        (dec_clock s) = (.normal,t) := by
      rw [evaluate_seq, hx]
      exact hk.trans ha
    conv => lhs; rw [absorbLoop, evaluate_while, eval_lvar, hn]
    simp only [show (BitVec.ofNat 64 (n+1) != 0#64) = true from bne_iff_ne.mpr hw,
      ite_true, beq_eq_false_iff_ne.mpr hclk, Bool.false_eq_true, ite_false, hbody]
    exact hu

private theorem byte_from_memory (m : Memory) (p : Word) (aligned : p.toNat%8=0) (q : Nat) :
    read m (offset p q) =
      ((m (address p (q/8))) >>> (8*(q%8))).setWidth 8 := by
  have idx : byte_index (offset p q) false = 8*(q%8) := by
    simp only [byte_index, Bool.false_eq_true, ↓reduceIte, offset, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [ByteMemory.read, get_byte, idx, align_offset p q aligned]
  simp only [offset, address, Nat.mul_comm 8]

private theorem holds_packed {c m xs} (ok : Valid c) (h : Holds m c.frame xs)
    (space : xs.length ≤ c.capacity) : Packed c.domain m c.base c.frame (xs.length/136) xs := by
  intro k hk i
  let q := 136*k+8*i.val
  have hi := i.isLt
  have ha : address (c.frame + word (136*k)) i = offset c.frame q := by
    simp [address, offset, q, BitVec.ofNat_add, BitVec.add_assoc]
  have he : c.inFrame (offset c.frame q) := by
    refine ⟨q, by dsimp [q]; omega, ?_⟩
    rw [align_offset _ _ ok.aligned, show q/8*8 = q by dsimp [q]; omega]
  rw [ha]
  refine ⟨ok.frame _ he, ?_, fun j hj => (ok.base j).2 (hj ▸ he)⟩
  symm
  apply lane_eq
  intro j hj
  have bound : 136*k + (8*i.val+j) < xs.length := by omega
  rw [Cshake256.Fast.getD_take_drop _ _ _ (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem bound, Option.getD_some, ← h _ bound, byte_from_memory _ _ ok.aligned]
  have index : (136*k+(8*i.val+j))/8 = q/8 := by dsimp [q]; omega
  have rem : (136*k+(8*i.val+j))%8 = j := by omega
  rw [index, rem]
  simp [address, offset, show 8*(q/8) = q by dsimp [q]; omega]

/-- Read the 32-byte result in the native ABI's little-endian order. -/
def digestAt (m : Memory) (base : Word) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofBitVec (read m (offset base i))

private theorem digest_lanes {c m state} (ok : Valid c)
    (reads : ∀ i : Fin 25, m (address c.base i) = Keccak.lanes state i) :
    digestAt m c.base = Cshake256.squeeze32 state := by
  apply List.map_congr_left
  intro i hi
  have bound : i/8 < 25 := by have := List.mem_range.mp hi; omega
  have hr := reads ⟨i/8,bound⟩
  rw [byte_from_memory _ _ ok.stateAligned]
  change m (address c.base (i/8)) = state.getD (i/8) Cshake256.zeroLane at hr
  rw [hr]
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp [Cshake256.stateByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem message_size {c} (ok : Valid c) : (finalCursor c).bytes.length ≤ c.capacity := by
  obtain ⟨_, h⟩ := prefix_bounds ok
  simp only [finalCursor, Cshake256.paddedMessage]
  split
  · rw [padded_blocks]
    unfold Layout.capacity
    omega
  · rw [padded_blocks, List.length_append]
    change 136 * (((prefixBytes c).length+c.message.bytes.length+136)/136) ≤ _
    omega

private def inner := seqs [prepareFrame, lowerStage "base" (fun _ => .lit 0), absorbLoop] (.ret (lit 0))

private theorem inner_correct {c} (ok : Valid c) :
    ∃ fuel, ∀ {τ} (s : PanState τ), Rep c {} s → fuel ≤ s.clock →
      ∃ t, evaluate inner s = (.ret (.word 0),t) ∧ digestAt t.memory c.base =
        Cshake256.namedBytes c.name.bytes c.custom.bytes c.message.bytes := by
  obtain ⟨f, hp⟩ := prepare_correct ok
  let u := finalCursor c
  refine ⟨f+u.blocks, fun s rep hclk => ?_⟩
  obtain ⟨r,frame,hr,cf⟩ := hp s rep (by omega)
  have base : r.locals "base" = some (.word c.base) := hr.regs .base
  have mapped : Mapped r c.base := by intro i; rw [hr.domain]; exact (ok.base i).1
  obtain ⟨m, hz, rz, fz⟩ := lowerStage_correct r "base" c.base base mapped (fun _ => .lit 0)
  let z := {r with memory := m}
  have hb := holds_packed ok hr.bytes (message_size ok)
  have packed : Packed z.memaddrs z.memory c.base c.frame u.blocks u.bytes := by
    intro k hk i
    obtain ⟨hd,hv,away⟩ := hb k hk i
    exact ⟨hr.domain ▸ hd, (fz _ away).trans hv, away⟩
  have bound := message_size ok
  have size := ok.size
  obtain ⟨t,ht,rt,_⟩ := absorbLoop_correct u.blocks z c.base c.frame Cshake256.zeroState u.bytes
    (by change (finalCursor c).bytes.length / 136 < _; omega) (by change u.blocks ≤ r.clock; omega)
    base (hr.regs .input) (hr.regs .blocks) mapped (by
      intro i
      rw [show z.memory = m from rfl, rz i]
      simp [runStage, Expr.value, Keccak.lanes, Cshake256.zeroState,Cshake256.zeroLane,
        Array.getD_eq_getD_getElem?, i.isLt]) packed
  refine ⟨empty_locals t, ?_, digest_lanes ok rt⟩
  have seqEval {τ} {p q : PStmt} {a b : PanState τ} (h : evaluate p a = (.normal,b)) :
      evaluate (.seq p q) a = evaluate q b := by rw [evaluate_seq,h]; rfl
  change evaluate (.seq _ (.seq _ (.seq _ _))) s = _
  rw [seqEval frame, seqEval hz, seqEval ht]
  exact evaluate_ret _ _

/-- End-to-end execution of the exported function over three raw input slices.
    A valid layout supplies their byte contents, the mapped workspace and its
    separation from the reads. The work buffer and state may contain arbitrary
    initial words. Fuel depends only on the input layout. -/
theorem pancakeCshake256_correct (c : Layout) (ok : Valid c) :
    ∃ fuel, ∀ {τ} (s : PanState τ), fuel ≤ s.clock →
      s.locals "base" = some (.word c.base) → s.locals "frame" = some (.word c.frame) →
      s.locals "slices" = some (.word c.table) → s.memory = c.memory →
      s.memaddrs = c.domain → s.be = false →
      ∃ t, evaluate kernel.body s = (.ret (.word 0),t) ∧ digestAt t.memory c.base =
        Cshake256.namedBytes c.name.bytes c.custom.bytes c.message.bytes := by
  obtain ⟨f,run⟩ := inner_correct ok
  refine ⟨f, ?_⟩
  intro τ s fuel base frame table mem dm le
  have bindLocal {p : PStmt} {e : PExp} {v : String} {a : PanState τ} {w : Word}
      (he : eval a e = some (.word w))
      (h : ∃ t, evaluate p {a with locals := FUPDATE a.locals (v,.word w)} = (.ret (.word 0),t) ∧
        digestAt t.memory c.base = Cshake256.namedBytes c.name.bytes c.custom.bytes c.message.bytes) :
      ∃ t, evaluate (.dec v .One e p) a = (.ret (.word 0),t) ∧
        digestAt t.memory c.base = Cshake256.namedBytes c.name.bytes c.custom.bytes c.message.bytes := by
    obtain ⟨t,ht,rt⟩ := h
    rw [evaluate_dec, he]
    simp only [shape_of_word, BEq.rfl, ite_true, ht]
    exact ⟨_,rfl,rt⟩
  change ∃ t, evaluate (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ inner)))))) s = _ ∧ _
  apply bindLocal (w := 0) rfl
  apply bindLocal (w := 0) rfl
  apply bindLocal (w := 0) rfl
  apply bindLocal (w := shakeSuffix) rfl
  apply bindLocal (w := c.frame) (by simp [FUPDATE, frame])
  apply bindLocal (w := 0) rfl
  apply run
  · exact ⟨fun reg => by cases reg <;> simp [Reg.name,Reg.val,FUPDATE,base,frame,table], dm, le,
    fun a _ => congrFun mem a, fun _ h => by cases h⟩
  · exact fuel

end Obend.Lower.Pancake.Sponge
