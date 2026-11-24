module
public import Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Digest.Cshake256.Spec

public section
namespace Obend.Lower.Pancake.Sponge
open Obend.Digest WordBuffer ByteMemory

private abbrev v := PExp.lvar
private def lit (n : Nat) := PExp.const (BitVec.ofNat 64 n)
private def add (a b : PExp) := PExp.binop .Add [a,b]
private def sub (a b : PExp) := PExp.binop .Sub [a,b]
private def atOffset (p : String) (n : Nat) := add (v p) (lit n)
private def loadAt (p : String) (n : Nat) := PExp.load .One (atOffset p n)
private def bump (p : String) (n : Nat) := PStmt.lassign p (atOffset p n)
private def seqs (ss : List PStmt) (endStmt : PStmt) := ss.foldr PStmt.seq endStmt

def rateWords : Nat := 17
def customSuffix : Word := 4
def shakeSuffix : Word := 31
def finalBit : Word := 128

private def writeByte (e : PExp) : PStmt :=
  .seq (.storeByte (add (v "frame") (v "used")) e) (bump "used" 1)

private def copySlice (ptr len : PExp) : PStmt :=
  .seq (.lassign "i" (lit 0)) <| .while_ (.cmp .Lower (v "i") len)
    (.seq (writeByte (.loadByte (add ptr (v "i")))) (bump "i" 1))

/-- Emit left_encode(8*len), including the ninth digit when the bit length
    exceeds a word. Each shift in the emitted program is an immediate below 64. -/
private def writeLength (len : PExp) : PStmt := go 8 where
  digit (i : Nat) : PExp :=
    if i = 0 then .shift .Lsl len 3 else .shift .Lsr len (8*i-3)
  digits (i : Nat) := seqs (writeByte (lit (i+1)) ::
    ((List.range (i+1)).reverse.map fun j => writeByte (digit j))) .skip
  go : Nat → PStmt
    | 0 => digits 0
    | i+1 => .ite (digit (i+1)) (digits (i+1)) (go i)

private def desc (i : Nat) := loadAt "slices" (8*i)

/-- Move the next block boundary up to or past the cursor, then write the zeros.
    The output block count is accumulated along with the boundary. -/
private def grow (needed : PExp) : PStmt :=
  (.while_ (.cmp .Lower (v "limit") needed)
    (.seq (bump "limit" (8*rateWords)) (bump "blocks" 1)))

private def fillTo (endPos : PExp) : PStmt :=
  .while_ (.cmp .Lower (v "used") endPos) (writeByte (lit 0))

private def alignFrame := PStmt.seq (grow (v "used")) (fillTo (v "limit"))

private def finishFrame : PStmt := .seq (grow (atOffset "used" 1)) <|
  .ite (.cmp .Equal (atOffset "used" 1) (v "limit"))
    (writeByte (.binop .Xor [v "suffix", .const finalBit]))
    (seqs [writeByte (v "suffix"), fillTo (sub (v "limit") (lit 1))] (writeByte (.const finalBit)))

private def writePrefix : PStmt :=
  seqs [writeByte (lit 1), writeByte (lit (8*rateWords)),
    writeLength (desc 1), copySlice (desc 0) (desc 1),
    writeLength (desc 3), copySlice (desc 2) (desc 3), alignFrame]
    (.lassign "suffix" (.const customSuffix))

def prepareFrame := seqs [
  .ite (.binop .Or [desc 1, desc 3]) writePrefix .skip,
  copySlice (desc 4) (desc 5)] finishFrame

structure Slice where
  ptr : Word
  bytes : List UInt8

/-- The three input slices and the caller's mapped workspace on x86-64. -/
structure Layout where
  base : Word
  frame : Word
  table : Word
  name : Slice
  custom : Slice
  message : Slice
  memory : ByteMemory.Memory
  domain : Word → Bool
  /-- Workspace reserved past the cSHAKE bound, for a caller whose frame holds more. -/
  headroom : Nat := 0

def Layout.capacity (c : Layout) :=
  c.name.bytes.length + c.custom.bytes.length + c.message.bytes.length + 294 + c.headroom

def Layout.inFrame (c : Layout) (a : Word) :=
  ∃ i, i < c.capacity ∧ byte_align (offset c.frame i) = a

def Layout.args (c : Layout) : List Word :=
  [c.name.ptr, BitVec.ofNat 64 c.name.bytes.length, c.custom.ptr,
   BitVec.ofNat 64 c.custom.bytes.length, c.message.ptr, BitVec.ofNat 64 c.message.bytes.length]

/-- Aligned writable workspaces, readable slices and descriptor. Read-only
    slices may overlap each other. Separation is stated at machine-word addresses. -/
structure Valid (c : Layout) : Prop where
  size : c.capacity < 2^64
  stateAligned : c.base.toNat % 8 = 0
  aligned : c.frame.toNat % 8 = 0
  frame : ∀ a, c.inFrame a → c.domain a = true
  base : ∀ i : Fin 25, c.domain (address c.base i) = true ∧ ¬c.inFrame (address c.base i)
  descriptor : ∀ i : Fin 6, let a := address c.table i
    c.domain a = true ∧ ¬c.inFrame a ∧ c.memory a = c.args[i.val]!
  slices : ∀ x ∈ [c.name, c.custom, c.message], ∀ i (hi : i < x.bytes.length),
    let a := offset x.ptr i
    c.domain (byte_align a) = true ∧ ¬c.inFrame (byte_align a) ∧
      read c.memory a = x.bytes[i].toBitVec

private structure Cursor where
  bytes : List UInt8 := []
  blocks : Nat := 0
  index : Nat := 0
  suffix : Word := shakeSuffix
  deriving Inhabited

private inductive Reg where
  | base | frame | slices | input | used | limit | blocks | i | suffix

private def Reg.name : Reg → String
  | .base => "base" | .frame => "frame" | .slices => "slices" | .input => "input"
  | .used => "used" | .limit => "limit" | .blocks => "blocks" | .i => "i" | .suffix => "suffix"

private abbrev word (n : Nat) := BitVec.ofNat 64 n

private def Reg.val (c : Layout) (u : Cursor) : Reg → Word
  | .base => c.base | .frame | .input => c.frame | .slices => c.table
  | .used => word u.bytes.length | .limit => word (136*u.blocks) | .blocks => word u.blocks
  | .i => word u.index | .suffix => u.suffix

private structure Rep {τ} (c : Layout) (u : Cursor) (s : PanState τ) : Prop where
  regs : ∀ r : Reg, s.locals r.name = some (.word (r.val c u))
  domain : s.memaddrs = c.domain
  little : s.be = false
  outside : ∀ a, ¬c.inFrame a → s.memory a = c.memory a
  bytes : Holds s.memory c.frame u.bytes

private def Reads (c : Layout) (u : Cursor) (e : PExp) (w : Word) :=
  ∀ (τ) (s : PanState τ), Rep c u s → eval s e = some (.word w)

private def Runs (c : Layout) (op : PStmt) (u t : Cursor) : Prop :=
  ∃ fuel, ∀ {τ} (s : PanState τ), Rep c u s → fuel ≤ s.clock →
    ∃ dst, evaluate op s = (.normal,dst) ∧ Rep c t dst ∧ dst.clock = s.clock-fuel

private theorem runs_skip (c : Layout) (u : Cursor) : Runs c .skip u u :=
  ⟨0, fun s r _ => ⟨s, evaluate_skip _, r, rfl⟩⟩

private theorem Runs.seq {c p q a b d} (hp : Runs c p a b) (hq : Runs c q b d) :
    Runs c (.seq p q) a d := by
  obtain ⟨f, h⟩ := hp
  obtain ⟨g, k⟩ := hq
  refine ⟨f+g, fun s r hf => ?_⟩
  obtain ⟨t, ht, rt, ct⟩ := h s r (by omega)
  obtain ⟨u, hu, ru, cu⟩ := k t rt (by omega)
  refine ⟨u, ?_, ru, by omega⟩
  rw [evaluate_seq, ht]
  exact hu

private theorem run_while_done {c u cond body} (hg : Reads c u cond 0) :
    Runs c (.while_ cond body) u u := by
  refine ⟨0, fun s r _ => ⟨s, ?_, r, rfl⟩⟩
  rw [evaluate_while, hg _ s r]
  rfl

private theorem run_while_step {c u t z cond body w} (hg : Reads c u cond w) (hn : w ≠ 0#64)
    (hb : Runs c body u t) (hr : Runs c (.while_ cond body) t z) :
    Runs c (.while_ cond body) u z := by
  obtain ⟨f, h⟩ := hb
  obtain ⟨g, k⟩ := hr
  refine ⟨1+f+g, fun s r hf => ?_⟩
  have hpos : s.clock ≠ 0 := by omega
  have rd : Rep c u (dec_clock s) := ⟨r.regs,r.domain,r.little,r.outside,r.bytes⟩
  obtain ⟨t, ht, rt, ct⟩ := h (dec_clock s) rd (by simp [dec_clock]; omega)
  simp only [dec_clock_clock] at ct
  obtain ⟨z, hz, rz, cz⟩ := k t rt (by omega)
  refine ⟨z, ?_, rz, by omega⟩
  conv => lhs; rw [evaluate_while, hg _ s r]
  simp only [bne_iff_ne.mpr hn, ite_true, beq_eq_false_iff_ne.mpr hpos,
    Bool.false_eq_true, ite_false, ht]
  exact hz

private theorem if_yes {c u t e p q w} (h : Reads c u e w) (hw : w ≠ 0#64) (r : Runs c p u t) :
    Runs c (.ite e p q) u t := by
  obtain ⟨f, run⟩ := r
  refine ⟨f, fun s rep fuel => ?_⟩
  simp only [evaluate_ite, h _ s rep, bne_iff_ne.mpr hw, ite_true]
  exact run s rep fuel

private theorem if_no {c u t e p q} (h : Reads c u e 0) (r : Runs c q u t) :
    Runs c (.ite e p q) u t := by
  obtain ⟨f, run⟩ := r
  refine ⟨f, fun s rep fuel => ?_⟩
  rw [evaluate_ite, h _ s rep]
  exact run s rep fuel

private theorem reads_lit {c u} (w : Word) : Reads c u (.const w) w := fun _ _ _ => rfl

private theorem reads_reg {c u} (k : Reg) : Reads c u (v k.name) (k.val c u) :=
  fun _ _ r => r.regs k

private theorem reads_desc {c u} (ok : Valid c) (i : Fin 6) : Reads c u (desc i) c.args[i.val]! := by
  intro τ s r
  obtain ⟨dm, away, val⟩ := ok.descriptor i
  have p := r.regs .slices
  change s.locals "slices" = some (.word c.table) at p
  simp [desc, loadAt, atOffset, add, lit, eval, mem_load, evalList, extractWords, word_op, p,
    r.domain]
  exact ⟨dm, (r.outside _ away).trans (by simpa using val)⟩

private theorem runs_write {c u e w} (ok : Valid c) (h : Reads c u e w)
    (space : u.bytes.length < c.capacity) :
    Runs c (writeByte e) u {u with bytes := u.bytes ++ [(UInt8.ofBitVec (w.setWidth 8))]} := by
  refine ⟨0, fun s r _ => ?_⟩
  let a := offset c.frame u.bytes.length
  let m := put s.memory a (UInt8.ofBitVec (w.setWidth 8))
  let dst := set_var "used" (.word (word u.bytes.length + 1)) {s with memory := m}
  have ha : c.inFrame (byte_align a) := ⟨_, space, rfl⟩
  have fr : s.locals "frame" = some (.word c.frame) := r.regs .frame
  have us : s.locals "used" = some (.word (word u.bytes.length)) := r.regs .used
  refine ⟨dst, ?_, ⟨?_, r.domain, r.little, ?_, ?_⟩, rfl⟩
  · simp [writeByte, evaluate_seq, evaluate_storeByte, h _ s r, evaluate_assign, add,
      bump, atOffset, lit, word_op, fr, us, is_valid_value_local, mem_store_byte,
      r.little, r.domain, show c.domain (byte_align (c.frame + word u.bytes.length)) = true from ok.frame _ ha,
      dst, m, a, put, offset, set_kvar]
  · intro reg
    cases reg <;> first | exact r.regs _ | simp [dst, Reg.name, Reg.val, set_var, FUPDATE, BitVec.ofNat_add]
  · intro z hz
    have ne : byte_align a ≠ z := fun eq => hz (eq ▸ ha)
    change put s.memory a (UInt8.ofBitVec (w.setWidth 8)) z = _
    simp [put, UPDATE, ne, r.outside z hz]
  · exact holds_push r.bytes _ (Nat.lt_trans space ok.size)

private abbrev byteOf (w : Word) := UInt8.ofBitVec (w.setWidth 8)

private theorem read_add {c u a b x y} (ha : Reads c u a x) (hb : Reads c u b y) :
    Reads c u (add a b) (x+y) := by
  intro τ s r
  simp [add, ha _ s r, hb _ s r, word_op]

private theorem read_sub {c u a b x y} (ha : Reads c u a x) (hb : Reads c u b y) :
    Reads c u (sub a b) (x-y) := by
  intro τ s r
  simp [sub, ha _ s r, hb _ s r, word_op]

private theorem read_lt {c u a b x y} (ha : Reads c u a (word x)) (hb : Reads c u b (word y))
    (hx : x < 2^64) (hy : y < 2^64) :
    Reads c u (.cmp .Lower a b) (if x < y then 1 else 0) := by
  intro τ s r
  simp [eval, ha _ s r, hb _ s r, word_cmp, BitVec.ult, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private theorem set_index {c u e n} (h : Reads c u e (word n)) :
    Runs c (.lassign "i" e) u {u with index := n} := by
  refine ⟨0, fun s r _ => ?_⟩
  let t := set_var "i" (.word (word n)) s
  have hi : s.locals "i" = some (.word (word u.index)) := r.regs .i
  refine ⟨t, ?_, ⟨?_, r.domain,r.little,r.outside,r.bytes⟩, rfl⟩
  · simp [evaluate_assign, h _ s r, is_valid_value_local, hi, set_kvar, t]
  · intro reg
    cases reg <;> first | exact r.regs _ | simp [t, Reg.name, Reg.val, set_var, FUPDATE]

private theorem set_custom {c u} :
    Runs c (.lassign "suffix" (.const customSuffix)) u {u with suffix := customSuffix} := by
  refine ⟨0, fun s r _ => ?_⟩
  let t := set_var "suffix" (.word customSuffix) s
  have hs : s.locals "suffix" = some (.word u.suffix) := r.regs .suffix
  refine ⟨t, ?_, ⟨?_, r.domain,r.little,r.outside,r.bytes⟩, rfl⟩
  · simp [evaluate_assign, is_valid_value_local, hs, set_kvar, t]
  · intro reg
    cases reg <;> first | exact r.regs _ | simp [t, Reg.name, Reg.val, set_var, FUPDATE]

private theorem grow_one {c u} :
    Runs c (.seq (bump "limit" (8*rateWords)) (bump "blocks" 1)) u {u with blocks := u.blocks+1} := by
  refine ⟨0, fun s r _ => ?_⟩
  let t := set_var "blocks" (.word (word u.blocks + 1)) (set_var "limit" (.word (word (136*u.blocks) + 136)) s)
  have hl : s.locals "limit" = some (.word (word (136*u.blocks))) := r.regs .limit
  have hb : s.locals "blocks" = some (.word (word u.blocks)) := r.regs .blocks
  refine ⟨t, ?_, ⟨?_, r.domain,r.little,r.outside,r.bytes⟩, rfl⟩
  · simp [bump, atOffset, add, lit, rateWords, evaluate_seq, evaluate_assign, hl, hb, word_op,
      is_valid_value_local, set_kvar, t, set_var, FUPDATE]
  · intro reg
    cases reg <;> first | exact r.regs _ | simp [t, Reg.name, Reg.val, set_var, FUPDATE,
      Nat.mul_add, BitVec.ofNat_add]

private theorem copy_loop {c} (ok : Valid c) (x : Slice) (hx : x ∈ [c.name,c.custom,c.message])
    (ptr len : PExp) (hp : ∀ u, Reads c u ptr x.ptr) (hl : ∀ u, Reads c u len (word x.bytes.length))
    (rem : Nat) (u : Cursor) (eq : u.index+rem = x.bytes.length)
    (space : u.bytes.length+rem ≤ c.capacity) (hlen : x.bytes.length < 2^64) :
    Runs c (.while_ (.cmp .Lower (v "i") len)
      (.seq (writeByte (.loadByte (add ptr (v "i")))) (bump "i" 1))) u
      {u with bytes := u.bytes ++ x.bytes.drop u.index, index := x.bytes.length} := by
  induction rem generalizing u with
  | zero =>
    have hi : u.index = x.bytes.length := by omega
    have z := read_lt (reads_reg (c := c) (u := u) .i) (hl u) (by change u.index < _; omega) hlen
    simp [hi] at z
    rw [List.drop_of_length_le (by omega : x.bytes.length ≤ u.index), List.append_nil, ← hi]
    exact run_while_done (body := (.seq (writeByte (.loadByte (add ptr (v "i")))) (bump "i" 1))) z
  | succ n ih =>
    have hi : u.index < x.bytes.length := by omega
    let ch := x.bytes[u.index]
    let t := {u with bytes := u.bytes ++ [ch], index := u.index+1}
    have rd : Reads c u (.loadByte (add ptr (v "i"))) (ch.toBitVec.setWidth 64) := by
      intro τ s r
      have addr := read_add (hp u) (reads_reg (c := c) (u := u) .i) _ s r
      obtain ⟨hd, ha, hv⟩ := ok.slices x hx u.index hi
      change eval s (add ptr (v "i")) = some (.word (offset x.ptr u.index)) at addr
      rw [show eval s (.loadByte (add ptr (v "i"))) = _ from eval_loadByte .., addr]
      simp only [mem_load_byte, r.little, r.domain]
      simp only [hd, ite_true, r.outside _ ha, Option.map_some]
      exact congrArg (fun b : Byte => some (PanVal.word (b.setWidth 64))) hv
    have emit := runs_write ok rd (by omega)
    have chEq : byteOf (ch.toBitVec.setWidth 64) = ch := by
      apply UInt8.toBitVec_inj.mp
      simp [BitVec.setWidth_setWidth_of_le]
    rw [show UInt8.ofBitVec ((ch.toBitVec.setWidth 64).setWidth 8) = ch from chEq] at emit
    have inc : Runs c (bump "i" 1) {u with bytes := u.bytes ++ [ch]} t := by
      apply set_index
      simp only [word, BitVec.ofNat_add]
      exact read_add (reads_reg .i) (reads_lit _)
    have cond := read_lt (reads_reg (c := c) (u := u) .i) (hl u) (by change u.index < _; omega) hlen
    simp [hi] at cond
    have rest := ih t (by change u.index+1+n = _; omega) (by simp [t]; omega)
    have split := List.drop_eq_getElem_cons hi
    rw [split]
    simpa [Reg.name, t, ch, List.append_assoc] using run_while_step cond (by decide) (emit.seq inc) rest

private theorem copy_slice {c} (ok : Valid c) (x : Slice) (hx : x ∈ [c.name,c.custom,c.message])
    (ptr len : PExp) (hp : ∀ u, Reads c u ptr x.ptr) (hl : ∀ u, Reads c u len (word x.bytes.length))
    (u : Cursor) (space : u.bytes.length+x.bytes.length ≤ c.capacity) :
    Runs c (copySlice ptr len) u {u with bytes := u.bytes ++ x.bytes, index := x.bytes.length} := by
  have init := set_index (u := u) (n := 0) (reads_lit (c := c) _)
  have hlen := ok.size
  have run := copy_loop ok x hx ptr len hp hl x.bytes.length {u with index := 0} (by simp) space (by omega)
  simpa [copySlice, lit] using init.seq run

private theorem grow_to {c} (ok : Valid c) (need : PExp) (extra : Nat)
    (he : ∀ u, Reads c u need (word (u.bytes.length+extra)))
    (rem : Nat) (u : Cursor) (target : Nat) (eq : u.blocks + rem = target)
    (endOk : u.bytes.length+extra ≤ 136*target)
    (minimal : ∀ k, k < target → 136*k < u.bytes.length+extra)
    (space : 136*target ≤ c.capacity) :
    Runs c (grow need) u {u with blocks := target} := by
  induction rem generalizing u with
  | zero =>
    have hg := read_lt (reads_reg (c := c) (u := u) .limit) (he u) (by change 136*u.blocks < _; have := ok.size; omega) (by have := ok.size; omega)
    change Reads c u (.cmp .Lower (v "limit") need) (if 136*u.blocks < u.bytes.length+extra then 1 else 0) at hg
    have e : target = u.blocks := by omega
    subst target
    rw [ite_eq_right (by omega)] at hg
    exact run_while_done hg
  | succ n ih =>
    have hg := read_lt (reads_reg (c := c) (u := u) .limit) (he u) (by change 136*u.blocks < _; have := ok.size; omega) (by have := ok.size; omega)
    change Reads c u (.cmp .Lower (v "limit") need) (if 136*u.blocks < u.bytes.length+extra then 1 else 0) at hg
    rw [ite_eq_left (minimal _ (by omega))] at hg
    exact run_while_step hg (by decide) grow_one
      (ih {u with blocks := u.blocks+1} (by change u.blocks+1+n = target; omega) endOk minimal)

private theorem fill_n {c} (ok : Valid c) (endPos : PExp) (f : Nat → Nat)
    (he : ∀ u, Reads c u endPos (word (f u.blocks)))
    (rem : Nat) (u : Cursor) (eq : u.bytes.length+rem = f u.blocks)
    (space : f u.blocks ≤ c.capacity) :
    Runs c (fillTo endPos) u {u with bytes := u.bytes ++ List.replicate rem 0} := by
  induction rem generalizing u with
  | zero =>
    have hg := read_lt (reads_reg (c := c) (u := u) .used) (he u)
      (by change u.bytes.length < _; have := ok.size; omega) (by have := ok.size; omega)
    simp [show ¬u.bytes.length < f u.blocks by omega] at hg
    simpa [fillTo, Reg.name] using (run_while_done (body := writeByte (lit 0)) hg)
  | succ n ih =>
    have hg := read_lt (reads_reg (c := c) (u := u) .used) (he u)
      (by change u.bytes.length < _; have := ok.size; omega) (by have := ok.size; omega)
    simp [show u.bytes.length < f u.blocks by omega] at hg
    let t := {u with bytes := u.bytes ++ [0]}
    have push : Runs c (writeByte (lit 0)) u t :=
      runs_write ok (reads_lit _) (by omega)
    have rest := ih t (by simp [t]; omega) space
    simpa [fillTo, Reg.name, t, List.append_assoc, List.replicate_succ] using run_while_step hg (by decide) push rest

private theorem align_correct {c} (ok : Valid c) (u : Cursor)
    (prev : 136*u.blocks ≤ u.bytes.length) (space : u.bytes.length+135 ≤ c.capacity) :
    Runs c alignFrame u {u with
      bytes := u.bytes ++ List.replicate ((136-u.bytes.length%136)%136) 0
      blocks := (u.bytes.length+135)/136} := by
  let target := (u.bytes.length+135)/136
  have growOk := grow_to ok (v "used") 0 (fun _ => reads_reg .used)
    (target-u.blocks) u target (by dsimp [target]; omega) (by dsimp [target]; omega)
    (by intro k hk; dsimp [target] at hk; omega) (by dsimp [target]; omega)
  let t := {u with blocks := target}
  have fillOk := fill_n ok (v "limit") (136*·) (fun _ => reads_reg .limit)
    ((136-u.bytes.length%136)%136) t (by dsimp [t,target]; omega) (by dsimp [t,target]; omega)
  exact growOk.seq fillOk

private theorem finish_correct {c} (ok : Valid c) (u : Cursor)
    (prev : 136*u.blocks ≤ u.bytes.length) (space : u.bytes.length+136 ≤ c.capacity) :
    Runs c finishFrame u {u with
      bytes := Cshake256.padForRate u.bytes (byteOf u.suffix)
      blocks := (u.bytes.length+136)/136} := by
  let n := u.bytes.length
  let target := (n+136)/136
  let t := {u with blocks := target}
  have growOk := grow_to ok (atOffset "used" 1) 1 (fun u => by
    simp only [word, BitVec.ofNat_add]
    exact read_add (reads_reg .used) (reads_lit _))
    (target-u.blocks) u target (by dsimp [target,n]; omega) (by dsimp [target,n]; omega)
    (by intro k hk; dsimp [target,n] at hk; omega) (by dsimp [target,n]; omega)
  apply growOk.seq
  have cond : Reads c t (.cmp .Equal (atOffset "used" 1) (v "limit"))
      (if n+1 = 136*target then 1 else 0) := by
    intro τ s r
    have h := r.regs .used
    have l := r.regs .limit
    change s.locals "used" = some (.word (word n)) at h
    change s.locals "limit" = some (.word (word (136*target))) at l
    have hn : n+1 < 2^64 := by have := ok.size; dsimp [n]; omega
    have ht : 136*target < 2^64 := by dsimp [target,n]; have := ok.size; omega
    have e : word n + 1#64 = word (n+1) := (BitVec.ofNat_add ..).symm
    have iff : word (n+1) = word (136*target) ↔ n+1 = 136*target := by
      constructor
      · intro q
        simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt ht] using congrArg BitVec.toNat q
      · exact congrArg word
    simp [atOffset, add, lit, eval, word_op, word_cmp, h, l, e, iff]
  by_cases one : 136-n%136 = 1
  · have eq : n+1 = 136*target := by dsimp [target]; omega
    rw [ite_eq_left eq] at cond
    apply if_yes cond (by decide)
    have x : Reads c t (.binop .Xor [v "suffix", .const finalBit]) (u.suffix ^^^ 128) := by
      intro τ s r
      have hs : s.locals "suffix" = some (.word u.suffix) := r.regs .suffix
      simp [hs, word_op, finalBit]
    have emit := runs_write ok x (by dsimp [t]; omega)
    simpa [Cshake256.padForRate, Cshake256.rateBytes, ← show u.bytes.length = n from rfl,
      t, target, n, show 136-u.bytes.length%136 = 1 from one, byteOf, UInt8.xor] using emit
  · have ne : n+1 ≠ 136*target := by dsimp [target]; omega
    rw [ite_eq_right ne] at cond
    apply if_no cond
    let a := {t with bytes := t.bytes ++ [byteOf u.suffix]}
    have push : Runs c (writeByte (v "suffix")) t a := runs_write ok (reads_reg .suffix) (by dsimp [t]; omega)
    let gap := 136-n%136-2
    -- The counter stays positive after growing for the suffix.
    have pos : 0 < target := by dsimp [target]; omega
    have fillOk : Runs c (fillTo (sub (v "limit") (lit 1))) a
        {a with bytes := a.bytes ++ List.replicate gap 0} := by
      -- Only positive limits occur here; at zero, word subtraction wraps.
      let last := fun blocks => if blocks = 0 then 2^64-1 else 136*blocks-1
      apply fill_n ok _ last
      · intro z
        have h := read_sub (reads_reg (c := c) (u := z) .limit) (reads_lit (1#64))
        by_cases hz : z.blocks = 0
        · simpa [Reg.val, Reg.name, hz, last, lit, word] using h
        · have eq : 136*z.blocks = (136*z.blocks-1)+1 := by omega
          have hw : word (136*z.blocks)-1#64 = word (136*z.blocks-1) := by
            conv => lhs; rw [eq, word, BitVec.ofNat_add]
            exact BitVec.add_sub_cancel ..
          simpa [Reg.val, Reg.name, last, hz, hw, lit] using h
      · simp [a,t,gap,last,n,target]; omega
      · dsimp [a,t,last]; rw [ite_eq_right (Nat.ne_of_gt pos)]; dsimp [target,n]; omega
    have tailOk := runs_write (u := {a with bytes := a.bytes ++ List.replicate gap 0}) ok
      (reads_lit finalBit) (by simp [a,t,gap,n]; omega)
    simpa [seqs, Cshake256.padForRate, Cshake256.rateBytes, show ¬136-u.bytes.length%136=1 from one,
      a, t, target, n, gap, finalBit, byteOf] using push.seq (fillOk.seq tailOk)

private def digitsLE (n k : Nat) := (List.range k).map fun j => UInt8.ofNat (n / 256^j)

private theorem digitsLE_succ (n k : Nat) :
    digitsLE n (k+1) = UInt8.ofNat n :: digitsLE (n/256) k := by
  simp [digitsLE, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.pow_succ,
    Nat.div_div_eq_div_mul, Nat.mul_comm 256]

private theorem aux_digits (k fuel n : Nat) (hf : k+1 ≤ fuel)
    (lo : 256^k ≤ n) (hi : n < 256^(k+1)) :
    Cshake256.natBytesLEAux fuel n = digitsLE n (k+1) := by
  have hn : n ≠ 0 := by have : 0 < 256^k := Nat.pow_pos (by decide); omega
  induction k generalizing fuel n with
  | zero =>
    cases fuel with
    | zero => omega
    | succ f =>
      have h : n/256 = 0 := by simp at hi; omega
      rw [Cshake256.natBytesLEAux, ite_eq_right hn, h, digitsLE_succ]
      cases f <;> simp [Cshake256.natBytesLEAux, digitsLE, Nat.mod_eq_of_lt (by simpa using hi : n < 256)]
  | succ k ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      have lo' : 256^k ≤ n/256 := (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa [Nat.pow_succ] using lo)
      have hi' : n/256 < 256^(k+1) := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using hi)
      rw [Cshake256.natBytesLEAux, ite_eq_right hn, digitsLE_succ, ih f _ (by omega) lo' hi'
        (by have : 0 < 256^k := Nat.pow_pos (by decide); omega)]
      congr 1
      apply UInt8.toNat_inj.mp
      simp

private theorem width_le (k : Nat) : k+1 ≤ 256^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

private theorem encoded_digits (n k : Nat) (lo : k=0 ∨ 256^k ≤ n) (hi : n < 256^(k+1)) :
    Cshake256.leftEncode n = UInt8.ofNat (k+1) :: (digitsLE n (k+1)).reverse := by
  by_cases hz : n = 0
  · subst n
    have : k = 0 := by have : 0 < 256^k := Nat.pow_pos (by decide); omega
    subst k; rfl
  · have low : 256^k ≤ n := by
      rcases lo with h|h
      · subst k; simp; omega
      · exact h
    have h := aux_digits k n n (Nat.le_trans (width_le k) low) low hi
    simp [Cshake256.leftEncode, Cshake256.natBytesBE, Cshake256.natBytesLE, h, digitsLE]

private theorem digit_read {c u len n} (hr : Reads c u len (word n)) (bound : n < 2^64)
    (j : Nat) (hj : j ≤ 8) :
    Reads c u (writeLength.digit len j) (word (8*n / 256^j)) := by
  intro τ s r
  by_cases eq : j = 0
  · subst j
    simp only [writeLength.digit, ↓reduceIte, eval, hr _ s r, word_sh, Nat.pow_zero, Nat.div_one]
    apply congrArg (fun w => some (PanVal.word w))
    change word n <<< 3 = word (8*n)
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  · have shift : 8*j-3 < 64 := by omega
    have power : ∀ i : Fin 9, i.val ≠ 0 → 256^i.val = 8 * 2^(8*i.val-3) := by decide
    rw [show 256^j = 8*2^(8*j-3) from power ⟨j,by omega⟩ eq,
      Nat.mul_div_mul_left _ _ (by decide : 0 < 8)]
    simp [writeLength.digit, eq, eval, hr _ s r, word_sh, show ¬64 ≤ 8*j-3 by omega]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt bound,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) bound)]

private theorem emit_words {c} (ok : Valid c) (items : List (PExp × Word))
    (he : ∀ i ∈ items, ∀ u, Reads c u i.1 i.2) (u : Cursor)
    (space : u.bytes.length+items.length ≤ c.capacity) :
    Runs c (seqs (items.map (fun i => writeByte i.1)) .skip) u
      {u with bytes := u.bytes ++ items.map (fun i => byteOf i.2)} := by
  induction items generalizing u with
  | nil => simpa [seqs] using runs_skip c u
  | cons a as ih =>
    simp only [List.length_cons] at space
    have head := runs_write ok (he a (by simp) u) (by omega)
    have tail := ih (fun i hi => he i (by simp [hi])) {u with bytes := u.bytes ++ [byteOf a.2]}
      (by simp; omega)
    simpa [seqs, List.append_assoc, byteOf] using head.seq tail

private theorem write_digits {c len n} (ok : Valid c) (hr : ∀ u, Reads c u len (word n))
    (bound : n < 2^64) (k : Nat) (hk : k ≤ 8) (u : Cursor)
    (space : u.bytes.length+10 ≤ c.capacity) :
    Runs c (writeLength.digits len k) u
      {u with bytes := u.bytes ++ (UInt8.ofNat (k+1) :: (digitsLE (8*n) (k+1)).reverse)} := by
  let pair := fun j => (writeLength.digit len j, word (8*n/256^j))
  let items := (lit (k+1),word (k+1)) :: (List.range (k+1)).reverse.map pair
  have go := emit_words ok items (by
    intro a ha z
    simp [items] at ha
    rcases ha with rfl | ⟨j,hj,rfl⟩
    · exact reads_lit _
    · exact digit_read (hr z) bound j (by omega)) u (by simp [items]; omega)
  have bv (v : Nat) : byteOf (word v) = UInt8.ofNat v := by
    apply UInt8.toNat_inj.mp
    change ((word v).setWidth 8).toNat = (BitVec.ofNat 8 v).toNat
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  simpa [items, pair, List.map_map, Function.comp_def, writeLength.digits, digitsLE,
    List.map_reverse, bv] using go

private theorem length_correct {c len n} (ok : Valid c) (hr : ∀ u, Reads c u len (word n))
    (bound : n < 2^64) (u : Cursor) (space : u.bytes.length+10 ≤ c.capacity) :
    Runs c (writeLength len) u {u with bytes := u.bytes ++ Cshake256.leftEncode (8*n)} := by
  suffices go : ∀ k, k ≤ 8 → 8*n < 256^(k+1) →
      Runs c (writeLength.go len k) u {u with bytes := u.bytes ++ Cshake256.leftEncode (8*n)} by
    exact go 8 (by decide) (by omega)
  intro k
  induction k with
  | zero =>
    intro _ hi
    rw [encoded_digits _ 0 (Or.inl rfl) hi]
    exact write_digits ok hr bound 0 (by decide) u space
  | succ k ih =>
    intro hk hi
    have cond := digit_read (hr u) bound (k+1) hk
    have hd : 8*n / 256^(k+1) < 2^64 := by
      have p : 256 ≤ 256^(k+1) := by rw [Nat.pow_succ]; have : 0 < 256^k := Nat.pow_pos (by decide); omega
      exact Nat.lt_of_le_of_lt (Nat.div_le_div_left p (by decide)) (by omega)
    by_cases low : 256^(k+1) ≤ 8*n
    · apply if_yes cond
      · intro eq
        have h0 := congrArg BitVec.toNat eq
        simp [Nat.mod_eq_of_lt hd] at h0
        have := Nat.div_pos low (Nat.pow_pos (by decide : 0 < 256))
        omega
      · rw [encoded_digits _ (k+1) (Or.inr low) hi]
        exact write_digits ok hr bound _ hk u space
    · rw [Nat.div_eq_of_lt (by omega : 8*n < 256^(k+1))] at cond
      exact if_no cond (ih (by omega) (by omega))

private theorem leftEncode_bound {n : Nat} (bound : n < 2^64) :
    (Cshake256.leftEncode (8*n)).length ≤ 10 := by
  suffices ∀ k, 8*n < 256^(k+1) → (Cshake256.leftEncode (8*n)).length ≤ k+2 from
    this 8 (by omega)
  intro k
  induction k with
  | zero =>
    intro hi
    simp [encoded_digits _ 0 (.inl rfl) hi, digitsLE]
  | succ k ih =>
    intro hi
    by_cases low : 256^(k+1) ≤ 8*n
    · simp [encoded_digits _ (k+1) (.inr low) hi, digitsLE]
    · have := ih (by omega)
      omega

private def prefixBytes (c : Layout) :=
  Cshake256.bytepad (Cshake256.encodeString c.name.bytes ++ Cshake256.encodeString c.custom.bytes) 136

private def rawPrefix (c : Layout) :=
  [1,136] ++ Cshake256.encodeString c.name.bytes ++ Cshake256.encodeString c.custom.bytes

private theorem prefix_eq (c : Layout) :
    prefixBytes c = rawPrefix c ++ List.replicate ((136-(rawPrefix c).length%136)%136) 0 := by
  have h : Cshake256.leftEncode 136 = [1,136] := rfl
  simp [prefixBytes, rawPrefix, Cshake256.bytepad, h, List.append_assoc]

private theorem prefix_bounds {c} (ok : Valid c) :
    (prefixBytes c).length % 136 = 0 ∧
    (prefixBytes c).length + c.message.bytes.length + 136 ≤ c.capacity := by
  have a := ok.size
  unfold Layout.capacity at *
  have n := leftEncode_bound (n := c.name.bytes.length) (by omega)
  have s := leftEncode_bound (n := c.custom.bytes.length) (by omega)
  simp [prefix_eq, rawPrefix, Cshake256.encodeString]
  omega

private def prefixCursor (c : Layout) : Cursor :=
  ⟨prefixBytes c, (prefixBytes c).length / 136, c.custom.bytes.length, customSuffix⟩

private theorem prefix_correct {c} (ok : Valid c) : Runs c writePrefix {} (prefixCursor c) := by
  let n := c.name.bytes
  let s := c.custom.bytes
  let ne := Cshake256.leftEncode (8*n.length)
  let se := Cshake256.leftEncode (8*s.length)
  have cap := ok.size
  have sizes : c.capacity = n.length+s.length+c.message.bytes.length+294+c.headroom := rfl
  have hn := leftEncode_bound (n := n.length) (by omega)
  have hs := leftEncode_bound (n := s.length) (by omega)
  let a : Cursor := {bytes := [1]}
  let b : Cursor := {bytes := [1,136]}
  let d : Cursor := {bytes := b.bytes ++ ne}
  let e : Cursor := {bytes := d.bytes ++ n, index := n.length}
  let f := {e with bytes := e.bytes ++ se}
  let g := {f with bytes := f.bytes ++ s, index := s.length}
  have a1 : Runs c (writeByte (lit 1)) {} a := runs_write ok (reads_lit _) (by change 0 < _; omega)
  have a2 : Runs c (writeByte (lit (8*rateWords))) a b :=
    runs_write ok (reads_lit _) (by change 1 < _; omega)
  have a3 : Runs c (writeLength (desc 1)) b d := length_correct ok (fun _ => reads_desc ok 1)
    (by change n.length < _; omega) b (by change 2+10 ≤ _; omega)
  have a4 : Runs c (copySlice (desc 0) (desc 1)) d e :=
    copy_slice ok c.name (by simp) _ _ (fun _ => reads_desc ok 0) (fun _ => reads_desc ok 1) d
      (by simp [d,b,ne]; change _ + n.length ≤ _; omega)
  have a5 : Runs c (writeLength (desc 3)) e f :=
    length_correct ok (fun _ => reads_desc ok 3) (by change s.length < _; omega) e
      (by simp [e,d,b,ne]; omega)
  have a6 : Runs c (copySlice (desc 2) (desc 3)) f g :=
    copy_slice ok c.custom (by simp) _ _ (fun _ => reads_desc ok 2) (fun _ => reads_desc ok 3) f
      (by simp [f,e,d,b,ne,se]; change _ + s.length ≤ _; omega)
  have a7 := align_correct ok g (by simp [g,f,e]) (by simp [g,f,e,d,b,ne,se]; omega)
  have all := a1.seq (a2.seq (a3.seq (a4.seq (a5.seq (a6.seq (a7.seq set_custom))))))
  have id : g.bytes = rawPrefix c := by simp [g,f,e,d,b,rawPrefix,Cshake256.encodeString,ne,se,n,s,List.append_assoc]
  have bl : (g.bytes.length+135)/136 = (prefixBytes c).length/136 := by
    rw [id, prefix_eq]; simp; omega
  rw [id] at bl
  simpa only [writePrefix, seqs, List.foldr_cons, List.foldr_nil, prefixCursor, id, bl,
    ← prefix_eq] using all

private theorem padded_blocks (xs : List UInt8) (suffix : UInt8) :
    (Cshake256.padForRate xs suffix).length = 136*((xs.length+136)/136) := by
  unfold Cshake256.padForRate
  simp only [Cshake256.rateBytes]
  by_cases h : 136 - xs.length % 136 = 1 <;> simp [h] <;> omega

private def finalCursor (c : Layout) : Cursor :=
  let bytes := Cshake256.paddedMessage c.name.bytes c.custom.bytes c.message.bytes
  ⟨bytes, bytes.length/136, c.message.bytes.length,
    if c.name.bytes = [] ∧ c.custom.bytes = [] then shakeSuffix else customSuffix⟩

private theorem prepare_correct {c} (ok : Valid c) : Runs c prepareFrame {} (finalCursor c) := by
  let cond := PExp.binop .Or [desc 1, desc 3]
  let nw := word c.name.bytes.length
  let sw := word c.custom.bytes.length
  have cap := ok.size
  unfold Layout.capacity at cap
  have rd : Reads c {} cond (nw ||| sw) := by
    intro τ s r
    have hn : eval s (desc 1) = some (.word nw) := reads_desc ok 1 _ s r
    have hs : eval s (desc 3) = some (.word sw) := reads_desc ok 3 _ s r
    simp [cond, hn, hs, word_op]
  have msg (u : Cursor) (space : u.bytes.length+c.message.bytes.length ≤ c.capacity) :=
    copy_slice ok c.message (by simp) (desc 4) (desc 5) (fun _ => reads_desc ok 4)
      (fun _ => reads_desc ok 5) u space
  by_cases empty : c.name.bytes = [] ∧ c.custom.bytes = []
  · have z : nw ||| sw = 0 := by simp [nw,sw,empty.1,empty.2]
    rw [z] at rd
    have branch := if_no (p := writePrefix) rd (runs_skip c {})
    have space : c.message.bytes.length+136 ≤ c.capacity := by unfold Layout.capacity; omega
    have copy := msg {} (by change 0+_ ≤ _; omega)
    let t : Cursor := {bytes := ([] : List UInt8) ++ c.message.bytes, index := c.message.bytes.length}
    have finish := finish_correct ok t (by simp [t]) (by simpa [t])
    have all := branch.seq (copy.seq finish)
    simpa [prepareFrame, seqs, cond, finalCursor, Cshake256.paddedMessage, empty, t,
      padded_blocks, shakeSuffix, byteOf] using all
  · have nz : nw ||| sw ≠ 0#64 := by
      intro eq
      have both := BitVec.or_eq_zero_iff.mp eq
      apply empty
      have h1 := congrArg BitVec.toNat both.1
      have h2 := congrArg BitVec.toNat both.2
      simp [nw,sw,Nat.mod_eq_of_lt (by omega : c.name.bytes.length < 2^64),
        Nat.mod_eq_of_lt (by omega : c.custom.bytes.length < 2^64)] at h1 h2
      exact ⟨h1,h2⟩
    have branch := if_yes (q := .skip) rd nz (prefix_correct ok)
    obtain ⟨mult, space⟩ := prefix_bounds ok
    let u := prefixCursor c
    have copy := msg u (by change (prefixBytes c).length+_ ≤ _; omega)
    let t := {u with bytes := u.bytes ++ c.message.bytes, index := c.message.bytes.length}
    have finish := finish_correct ok t (by simp [t,u,prefixCursor]; omega)
      (by simpa [t,u,prefixCursor] using space)
    have all := branch.seq (copy.seq finish)
    simpa [prepareFrame, seqs, cond, finalCursor, Cshake256.paddedMessage, empty, t, u, prefixCursor,
      prefixBytes, Cshake256.rateBytes, padded_blocks, customSuffix, byteOf] using all

end Obend.Lower.Pancake.Sponge
