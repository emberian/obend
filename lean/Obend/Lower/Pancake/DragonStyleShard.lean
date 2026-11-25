module
public import Obend.Lower.Pancake.RefinesClkPan
public import Obend.Lower.Pancake.ByteMemory
public import Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.ByteMemory

public section
namespace Obend.Lower.Pancake.DragonStyleShard

set_option autoImplicit false

abbrev word (n : Nat) : Word := BitVec.ofNat 64 n
private abbrev varE := PExp.lvar
private def plus (a b : PExp) : PExp := .binop .Add [a, b]
private def ptr (name : String) := plus (varE name) (varE "i")
private def copyByte : PStmt := .storeByte (ptr "dst") (.loadByte (ptr "src"))
private def bump : PStmt := .lassign "i" (plus (varE "i") (.const 1))
private def copyLoop : PStmt :=
  .while_ (.cmp .Lower (varE "i") (varE "len")) (.seq copyByte bump)
private def reject : PStmt := .ret (.const 4294967295)
private def guardLt (c : Cmp) (a b : PExp) (next : PStmt) : PStmt :=
  .ite (.cmp c a b) reject next

def echo : PFun := {
  name := "dn_echo", params := ["src", "dst", "len", "cap"].map (·, .One), exported := true
  body := guardLt .Less (varE "len") (.const 0) <|
    guardLt .Less (varE "cap") (.const 0) <|
    guardLt .Lower (.const 4096) (varE "cap") <|
    guardLt .Lower (varE "cap") (varE "len") <|
    .seq (.dec "i" .One (.const 0) copyLoop) (.ret (varE "len")) }

def echoSource := emitPnkFun echo

/-- Forward byte copy, including its precise behavior on overlapping buffers. -/
def copyOne (m : ByteMemory.Memory) (a b : Word) : ByteMemory.Memory :=
  ByteMemory.put m b (UInt8.ofBitVec (ByteMemory.read m a))

def copyMem (src dst : Word) (i : Nat) : Nat → ByteMemory.Memory → ByteMemory.Memory
  | 0, m => m
  | n + 1, m => copyMem src dst (i + 1) n (copyOne m (src + word i) (dst + word i))
termination_by structural n => n

theorem copyMem_frame (src dst z : Word) (i n : Nat) (m : ByteMemory.Memory)
    (outside : ∀ j, i ≤ j → j < i + n → dst + word j ≠ z) :
    ByteMemory.read (copyMem src dst i n m) z = ByteMemory.read m z := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    rw [copyMem, ih (i + 1) _ (fun j lo hi => outside j (by omega) (by omega))]
    simp [copyOne, ByteMemory.read_put, outside i (by omega) (by omega)]

private theorem index_ne (p : Word) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ne : a ≠ b) : p + word a ≠ p + word b := by
  intro h
  have e : word a = word b := by simpa using h
  have := congrArg BitVec.toNat e
  simp [word, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, ne] at this

theorem copyMem_payload (src dst : Word) (i n j : Nat) (m : ByteMemory.Memory)
    (bound : i + n < 2 ^ 64) (lo : i ≤ j) (hi : j < i + n)
    (disjoint : ∀ a b, i ≤ a → a < i + n → i ≤ b → b < i + n → dst + word a ≠ src + word b) :
    ByteMemory.read (copyMem src dst i n m) (dst + word j) = ByteMemory.read m (src + word j) := by
  induction n generalizing i m with
  | zero => omega
  | succ n ih =>
    rw [copyMem]
    by_cases e : i = j
    · subst j
      rw [copyMem_frame _ _ _ _ _ _ (fun k hk hi => index_ne dst k i (by omega) (by omega) (by omega))]
      simp [copyOne, ByteMemory.read_put]
    · rw [ih (i + 1) _ (by omega) (by omega) (by omega)
        (fun a b ha hb hc hd => disjoint a b (by omega) (by omega) (by omega) (by omega))]
      simp [copyOne, ByteMemory.read_put, disjoint i j (by omega) (by omega) lo hi]

theorem copyMem_word_frame (src dst a : Word) (i n : Nat) (m : ByteMemory.Memory)
    (outside : ∀ j, i ≤ j → j < i + n → byte_align (dst + word j) ≠ a) :
    copyMem src dst i n m a = m a := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    rw [copyMem, ih (i + 1) _ (fun j lo hi => outside j (by omega) (by omega))]
    simp [copyOne, ByteMemory.put, UPDATE, outside i (by omega) (by omega)]

structure Buffers {θ : Type} (s : PanState θ) (src dst : Word) (len : Nat) : Prop where
  srcPtr : s.locals "src" = some (.word src)
  dstPtr : s.locals "dst" = some (.word dst)
  length : s.locals "len" = some (.word (word len))
  little : s.be = false
  mapped : ∀ i, i < len →
    s.memaddrs (byte_align (src + word i)) = true ∧ s.memaddrs (byte_align (dst + word i)) = true

private theorem smallNat (n : Nat) (h : n ≤ 4096) : (word n).toNat = n :=
  Nat.mod_eq_of_lt (by omega)

private theorem cmp_nat (a b : Nat) (ha : a ≤ 4096) (hb : b ≤ 4096) :
    word_cmp .Lower (word a) (word b) = decide (a < b) := by
  simp only [word_cmp, BitVec.ult, smallNat _ ha, smallNat _ hb]

private theorem nonneg (a : Nat) (h : a ≤ 4096) : word_cmp .Less (word a) 0#64 = false := by
  simp [word_cmp, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide, smallNat _ h]
  omega

private def afterByte {θ : Type} (s : PanState θ) (src dst : Word) (i : Nat) : PanState θ :=
  { s with
    clock := s.clock - 1
    locals := FUPDATE s.locals ("i", .word (word (i + 1)))
    memory := copyOne s.memory (src + word i) (dst + word i) }

private theorem body_runs {θ : Type} (s : PanState θ) {src dst : Word} {i len : Nat}
    (hs : Buffers s src dst len) (hi : s.locals "i" = some (.word (word i))) (lt : i < len) :
    evaluate (.seq copyByte bump) (dec_clock s) = (.normal, afterByte s src dst i) := by
  obtain ⟨ha, hb⟩ := hs.mapped _ lt
  simp [evaluate_seq, copyByte, ptr, plus, bump, evaluate_storeByte, evaluate_assign,
    dec_clock, word_op, hs.srcPtr, hs.dstPtr, hi, hs.little, mem_load_byte, ha,
    mem_store_byte_eq hb, is_valid_value_local, set_kvar, set_var, afterByte,
    copyOne, ByteMemory.put, ByteMemory.read, BitVec.ofNat_add]

private theorem loop_runs {θ : Type} (src dst : Word) (len : Nat) (bound : len ≤ 4096) (rem : Nat) :
    ∀ i (s : PanState θ), i + rem = len → Buffers s src dst len →
    s.locals "i" = some (.word (word i)) → rem ≤ s.clock →
    ∃ t, evaluate copyLoop s = (.normal, t) ∧ t.clock + rem = s.clock ∧
      t.memory = copyMem src dst i rem s.memory ∧ t.locals "len" = s.locals "len" ∧
      t.ffi = s.ffi ∧ t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
      t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals := by
  induction rem with
  | zero =>
    intro i s hl hs hi _
    have he : i = len := by omega
    refine ⟨s, ?_, by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [copyLoop, evaluate_while]
    simp [hi, hs.length, he, cmp_nat len len bound bound]
  | succ n ih =>
    intro i s hl hs hi hc
    have lt : i < len := by omega
    let u := afterByte s src dst i
    have clk : u.clock = s.clock - 1 := rfl
    have hu : Buffers u src dst len :=
      ⟨by simpa [u, afterByte, FUPDATE] using hs.srcPtr,
       by simpa [u, afterByte, FUPDATE] using hs.dstPtr,
       by simpa [u, afterByte, FUPDATE] using hs.length, hs.little, hs.mapped⟩
    obtain ⟨t, ht, htclk, hm, hv, hffi, hdm, hcd, hbe, hba, hta, hgl⟩ := ih (i + 1) u (by omega) hu
      (by simp [u, afterByte, FUPDATE]) (by omega)
    refine ⟨t, ?_, by omega, hm, hv.trans (by simp [u, afterByte, FUPDATE]),
      hffi, hdm, hcd, hbe, hba, hta, hgl⟩
    conv => lhs; rw [copyLoop, evaluate_while]
    have nz : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [eval_cmp, eval_lvar, hi, hs.length, cmp_nat i len (by omega) bound,
      decide_eq_true lt, ite_true, nz, body_runs s hs hi lt]
    exact ht

structure EchoEntry {θ : Type} (src dst : Word) (n cap : Nat) (s : PanState θ) : Prop where
  buffers : Buffers s src dst n
  capacity : s.locals "cap" = some (.word (word cap))
  fits : n ≤ cap
  bounded : cap ≤ 4096

theorem echo_eval_ok {θ : Type} (s : PanState θ) {src dst : Word} {n cap : Nat}
    (h : EchoEntry src dst n cap s) (hc : n ≤ s.clock) :
    ∃ t, evaluate echo.body s = (.ret (.word (word n)), empty_locals t) ∧
      t.clock + n = s.clock ∧
      t.memory = copyMem src dst 0 n s.memory ∧
      t.ffi = s.ffi ∧ t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
      t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals := by
  obtain ⟨hs, hv, hn, hb⟩ := h
  let u := { s with locals := FUPDATE s.locals ("i", .word 0#64) }
  have hu : Buffers u src dst n :=
    ⟨by simpa [u, FUPDATE] using hs.srcPtr, by simpa [u, FUPDATE] using hs.dstPtr,
      by simpa [u, FUPDATE] using hs.length, hs.little, hs.mapped⟩
  obtain ⟨t, ht, htclk, hm, hl, hffi, hdm, hcd, hbe, hba, hta, hgl⟩ :=
    loop_runs src dst n (by omega) n 0 u (by omega) hu (by simp [u, FUPDATE]) hc
  let t' := { t with locals := res_var t.locals ("i", s.locals "i") }
  have lend : res_var t.locals ("i", s.locals "i") "len" = some (.word (word n)) := by
    have key := hl.trans hu.length
    cases hx : s.locals "i" <;> simp [res_var, FUPDATE, DOMSUB, key]
  refine ⟨t', ?_, htclk, hm, hffi, hdm, hcd, hbe, hba, hta, hgl⟩
  simp [echo, guardLt, evaluate_ite, hs.length, hv, nonneg n (by omega), nonneg cap hb,
    cmp_nat 4096 cap (by decide) hb, cmp_nat cap n hb (by omega),
    Nat.not_lt.mpr hb, Nat.not_lt.mpr hn, evaluate_seq, evaluate_dec,
    show evaluate copyLoop { s with locals := FUPDATE s.locals ("i", .word 0#64) } = (.normal, t) from ht,
    evaluate_ret, lend, t']

theorem echo_refinesClkTight {θ : Type} (src dst : Word) (n cap : Nat) :
    RefinesClkTight (θ := θ) (EchoEntry src dst n cap) echo.body n (fun s r t =>
      r = .ret (.word (word n)) ∧ t.clock + n = s.clock ∧
      t.memory = copyMem src dst 0 n s.memory ∧ t.ffi = s.ffi) := by
  intro s h hc
  obtain ⟨t, ev, htclk, hm, hffi, _⟩ := echo_eval_ok s h.2 hc
  have wf := evaluate_preserves_stateWF echo.body s h.1
  rw [ev] at wf
  exact ⟨_, _, ev, PanResult.noConfusion, PanResult.noConfusion, by change s.clock ≤ t.clock + n; omega,
    wf, rfl, htclk, hm, hffi⟩

private def regs (src dst : Word) (n cap : Nat) : FMap String PanVal :=
  FUPDATE (FUPDATE (FUPDATE (FUPDATE FEMPTY ("src", .word src)) ("dst", .word dst))
    ("len", .word (word n))) ("cap", .word (word cap))

theorem echo_entry_inhabited (src dst : Word) (n cap : Nat) (hn : n ≤ cap) (hc : cap ≤ 4096) :
    ∃ s : PanState Unit, EntryWF (EchoEntry src dst n cap) s ∧ s.clock ≥ n := by
  let s := { emptyPanState () n with locals := regs src dst n cap, memaddrs := fun _ => true }
  exact ⟨s, ⟨emptyPanState_wf () n,
    ⟨⟨by simp [s, regs, FUPDATE], by simp [s, regs, FUPDATE], by simp [s, regs, FUPDATE],
      rfl, fun _ _ => ⟨rfl, rfl⟩⟩, by simp [s, regs, FUPDATE], hn, hc⟩⟩, Nat.le_refl _⟩

theorem echo_rejects {θ : Type} (s : PanState θ) (n cap : Word)
    (hn : s.locals "len" = some (.word n)) (hc : s.locals "cap" = some (.word cap))
    (invalid : n.slt 0 ∨ cap.slt 0 ∨ 4096 < cap.toNat ∨ cap.toNat < n.toNat) :
    evaluate echo.body s = (.ret (.word 4294967295), empty_locals s) := by
  simp only [echo, guardLt, evaluate_ite, eval_cmp, eval_lvar, eval_const, hn, hc, word_cmp]
  rcases invalid with h | h | h | h
  all_goals simp_all [BitVec.ult, reject, evaluate_ret] <;> repeat' split <;> simp_all

/-- Parameterized fixed-capacity circular ring buffer of `N` physical cells (`0 < N` witnessed by `head : Fin N`). -/
structure Ring (N : Nat) (α : Type) where
  slots : Vector α N
  head : Fin N
  count : Fin (N + 1)

theorem Ring.capPos {N : Nat} {α : Type} (q : Ring N α) : 0 < N :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) q.head.isLt

private def cell {N : Nat} (hN : 0 < N) (head offset : Nat) : Fin N :=
  ⟨(head + offset) % N, Nat.mod_lt _ hN⟩

def Ring.view {N : Nat} {α : Type} (q : Ring N α) : List α :=
  List.ofFn (n := q.count.val) fun i => q.slots.get (cell q.capPos q.head.val i.val)

def Ring.peek {N : Nat} {α : Type} (q : Ring N α) : α :=
  q.slots.get q.head

def Ring.take {N : Nat} {α : Type} (q : Ring N α) (ready : 0 < q.count.val) : Ring N α :=
  { q with head := cell q.capPos q.head.val 1, count := ⟨q.count.val - 1, by have := q.count.isLt; omega⟩ }

def Ring.put {N : Nat} {α : Type} (q : Ring N α) (v : α) (room : q.count.val < N) : Ring N α :=
  { q with
    slots := q.slots.set (cell q.capPos q.head.val q.count.val).val v (cell q.capPos q.head.val q.count.val).isLt
    count := ⟨q.count.val + 1, by omega⟩ }

theorem ring_take_fifo {N : Nat} {α : Type} (q : Ring N α) (ready : 0 < q.count.val) :
    q.view = q.peek :: (q.take ready).view := by
  obtain ⟨slots, head, ⟨n, hn⟩⟩ := q
  cases n with
  | zero => contradiction
  | succ n =>
    simp only [Ring.view, Ring.take, Ring.peek, List.ofFn_succ, Nat.add_one_sub_one]
    congr 1
    · congr 1; apply Fin.ext; simp [cell, Nat.mod_eq_of_lt head.isLt]
    · congr 1; funext i; congr 1; apply Fin.ext
      dsimp [cell]
      rw [Nat.mod_add_mod]
      congr 1
      omega

theorem ring_put_fifo {N : Nat} {α : Type} (q : Ring N α) (v : α) (room : q.count.val < N) :
    (q.put v room).view = q.view ++ [v] := by
  simp only [Ring.view, Ring.put, List.ofFn_succ_last]
  congr 1
  · congr 1; funext i
    change (q.slots.set _ v _)[(cell q.capPos q.head.val i.val).val] = q.slots[(cell q.capPos q.head.val i.val).val]
    apply Vector.getElem_set_ne
    dsimp [cell]
    have hN := q.capPos
    have hi : i.val < q.count.val := i.isLt
    intro heq
    have hdiv1 := Nat.div_add_mod (q.head.val + q.count.val) N
    have hdiv2 := Nat.div_add_mod (q.head.val + i.val) N
    rw [Nat.mul_comm] at hdiv1 hdiv2
    have hle : (q.head.val + i.val) / N ≤ (q.head.val + q.count.val) / N :=
      Nat.div_le_div_right (by omega)
    have hmul : ((q.head.val + q.count.val) / N - (q.head.val + i.val) / N) * N = q.count.val - i.val := by
      rw [Nat.sub_mul]; omega
    rcases Nat.eq_zero_or_pos ((q.head.val + q.count.val) / N - (q.head.val + i.val) / N) with h0 | hp
    · rw [h0, Nat.zero_mul] at hmul; omega
    · have hge : N ≤ ((q.head.val + q.count.val) / N - (q.head.val + i.val) / N) * N :=
        Nat.le_mul_of_pos_left N hp
      omega
  · congr 1
    exact Vector.getElem_set_self _

theorem ring_view_length {N : Nat} {α : Type} (q : Ring N α) : q.view.length = q.count.val := by
  simp [Ring.view]

/-- A snapshot of the four driver/shard ownership queues. Slot numbers name
boot-allocated buffers, independent of the packet lengths stored in them. -/
structure Packet where
  slot : UInt16
  length : Nat
  deriving DecidableEq

structure Shard where
  rxActive : List Packet
  rxFree : List UInt16
  txFree : List UInt16
  txActive : List Packet
  observed : UInt64
  memory : ByteMemory.Memory

structure Layout where
  rx : UInt16 → Word
  tx : UInt16 → Word
  capacity : Nat

inductive Stop | budget | idle | backpressure | invalid
  deriving DecidableEq, Repr

private def publishPacket (s : Shard) (rx : Packet) (rs : List Packet) (tx : UInt16)
    (ts : List UInt16) (m : ByteMemory.Memory) : Shard :=
  ⟨rs, s.rxFree ++ [rx.slot], ts, s.txActive ++ [⟨tx, rx.length⟩], s.observed + 1, m⟩

/-- One owner, one wake. Reserve TX before consuming RX or advancing observation.
The persistent result is the next wake's entry. Queues are the FIFO specification
of the fixed circular buffers in dragonstyle_shard.c. -/
def stepBoundedBatch (layout : Layout) : Nat → Shard → Stop × Shard
  | 0, s => (.budget, s)
  | b + 1, s =>
    match s.rxActive, s.txFree with
    | [], _ => (.idle, s)
    | _ :: _, [] => (.backpressure, s)
    | rx :: rs, tx :: ts =>
      if rx.length ≤ layout.capacity ∧ layout.capacity ≤ 4096 then
        let m := copyMem (layout.rx rx.slot) (layout.tx tx) 0 rx.length s.memory
        stepBoundedBatch layout b (publishPacket s rx rs tx ts m)
      else (.invalid, s)
termination_by structural b => b

structure FixedShard where
  rxActive : Ring 4 Packet
  rxFree : Ring 4 UInt16
  txFree : Ring 4 UInt16
  txActive : Ring 4 Packet
  observed : UInt64
  memory : ByteMemory.Memory
  rxPool : rxActive.count.val + rxFree.count.val ≤ 4
  txPool : txFree.count.val + txActive.count.val ≤ 4

def FixedShard.project (s : FixedShard) : Shard :=
  ⟨s.rxActive.view, s.rxFree.view, s.txFree.view, s.txActive.view, s.observed, s.memory⟩

private def transfer (l : Layout) (s : FixedShard)
    (rx : 0 < s.rxActive.count.val) (tx : 0 < s.txFree.count.val) : FixedShard :=
  let p := s.rxActive.peek
  let id := s.txFree.peek
  let rroom : s.rxFree.count.val < 4 := by have := s.rxPool; omega
  let troom : s.txActive.count.val < 4 := by have := s.txPool; omega
  { rxActive := s.rxActive.take rx
    rxFree := s.rxFree.put p.slot rroom
    txFree := s.txFree.take tx
    txActive := s.txActive.put ⟨id, p.length⟩ troom
    observed := s.observed + 1
    memory := copyMem (l.rx p.slot) (l.tx id) 0 p.length s.memory
    rxPool := by dsimp [Ring.take, Ring.put]; have := s.rxPool; omega
    txPool := by dsimp [Ring.take, Ring.put]; have := s.txPool; omega }

def fixedBatch (l : Layout) : Nat → FixedShard → Stop × FixedShard
  | 0, s => (.budget, s)
  | b + 1, s =>
    if rx : 0 < s.rxActive.count.val then
      if tx : 0 < s.txFree.count.val then
        if s.rxActive.peek.length ≤ l.capacity ∧ l.capacity ≤ 4096 then
          fixedBatch l b (transfer l s rx tx)
        else (.invalid, s)
      else (.backpressure, s)
    else (.idle, s)
termination_by structural b => b

private theorem empty_ring {N : Nat} {α : Type} (q : Ring N α) (h : ¬ 0 < q.count.val) : q.view = [] := by
  apply List.eq_nil_of_length_eq_zero
  simpa [Ring.view] using Nat.eq_zero_of_not_pos h

theorem fixedBatch_refines (l : Layout) (b : Nat) (s : FixedShard) :
    Prod.map id FixedShard.project (fixedBatch l b s) = stepBoundedBatch l b s.project := by
  induction b generalizing s with
  | zero => rfl
  | succ b ih =>
    rw [fixedBatch, stepBoundedBatch]
    by_cases rx : 0 < s.rxActive.count.val
    · by_cases tx : 0 < s.txFree.count.val
      · simp only [rx, tx, dite_true, FixedShard.project, ring_take_fifo _ rx, ring_take_fifo _ tx]
        split
        · rw [ih]
          simp [transfer, FixedShard.project, publishPacket, ring_put_fifo]
        · simp [FixedShard.project, ring_take_fifo _ rx, ring_take_fifo _ tx]
      · simp [rx, tx, FixedShard.project, ring_take_fifo _ rx, empty_ring _ tx]
    · simp [rx, FixedShard.project, empty_ring _ rx]

def owners (s : Shard) (id : UInt16) : Nat × Nat :=
  ((s.rxActive.map Packet.slot ++ s.rxFree).count id,
   (s.txActive.map Packet.slot ++ s.txFree).count id)

theorem bounded_ring_conservation (layout : Layout) (b : Nat) (s : Shard) :
    let t := (stepBoundedBatch layout b s).2
    ∃ k, k ≤ b ∧ t.rxActive = s.rxActive.drop k ∧
      t.txFree = s.txFree.drop k ∧ t.txActive.length = s.txActive.length + k ∧
      t.observed = s.observed + UInt64.ofNat k ∧ ∀ id, owners t id = owners s id := by
  induction b generalizing s with
  | zero => exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, by simp [stepBoundedBatch], fun _ => rfl⟩
  | succ b ih =>
    unfold stepBoundedBatch
    split
    · exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, by simp, fun _ => rfl⟩
    · exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, by simp, fun _ => rfl⟩
    next rx rs tx ts hr ht =>
      split
      · obtain ⟨k, hk, ha, hf, hp, ho, hw⟩ := ih (publishPacket s rx rs tx ts _)
        refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hr, publishPacket] using ha
        · simpa [ht, publishPacket] using hf
        · simpa [publishPacket, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
        · simpa [publishPacket, UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm] using ho
        · intro id
          rw [hw]
          simp [owners, publishPacket, hr, ht, List.count_append, List.count_cons]
          omega
      · exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, by simp, fun _ => rfl⟩

theorem tx_full_preserves_rx (l : Layout) (s : Shard) (b : Nat)
    (rx : s.rxActive ≠ []) (tx : s.txFree = []) :
    stepBoundedBatch l (b + 1) s = (.backpressure, s) := by
  cases h : s.rxActive <;> simp_all [stepBoundedBatch]

/-- Relate a complete batch to a sequence of calls to the actual echo AST.
The boot arena maps both pools; the proof budgets exactly the sum of RX lengths
in the serviced prefix. Each host export invocation starts with its four locals. -/
private def enter (m : ByteMemory.Memory) (a d : Word) (n cap fuel : Nat) : PanState Unit :=
  { emptyPanState () fuel with
    locals := regs a d n cap
    memaddrs := fun _ => true
    memory := m }

def runBatch (l : Layout) : Nat → Nat → Shard → Option (Stop × Shard × Nat)
  | 0, fuel, s => some (.budget, s, fuel)
  | b + 1, fuel, s =>
    match s.rxActive, s.txFree with
    | [], _ => some (.idle, s, fuel)
    | _ :: _, [] => some (.backpressure, s, fuel)
    | rx :: rs, tx :: ts =>
      if rx.length ≤ l.capacity ∧ l.capacity ≤ 4096 then
        let arg := enter s.memory (l.rx rx.slot) (l.tx tx) rx.length l.capacity fuel
        let (result, t) := evaluate echo.body arg
        if result == .ret (.word (word rx.length)) then
          runBatch l b t.clock (publishPacket s rx rs tx ts t.memory)
        else none
      else some (.invalid, s, fuel)
termination_by structural b => b

private theorem enoughFuel (prior width fuel left used cap : Nat) (hf : prior + width ≤ fuel)
    (hc : left + used = fuel) (hu : used ≤ cap) (hb : cap ≤ width) : prior ≤ left := by omega

theorem batch_exec_refines (l : Layout) (b fuel : Nat) (s : Shard) (hf : b * 4096 ≤ fuel) :
    ∃ remaining, runBatch l b fuel s =
      some ((stepBoundedBatch l b s).1, (stepBoundedBatch l b s).2, remaining) ∧
      remaining ≤ fuel ∧ fuel ≤ remaining + b * 4096 := by
  induction b generalizing s fuel with
  | zero => exact ⟨fuel, rfl, Nat.le_refl _, by simp⟩
  | succ b ih =>
    rw [Nat.succ_mul] at hf
    simp only [runBatch, stepBoundedBatch]
    split
    · exact ⟨fuel, rfl, Nat.le_refl _, by omega⟩
    · exact ⟨fuel, rfl, Nat.le_refl _, by omega⟩
    next rx rs tx ts _ _ =>
      split
      next valid =>
        let arg := enter s.memory (l.rx rx.slot) (l.tx tx) rx.length l.capacity fuel
        have entry : EntryWF (EchoEntry (l.rx rx.slot) (l.tx tx) rx.length l.capacity) arg :=
          ⟨emptyPanState_wf () fuel, ⟨⟨by simp [arg, enter, regs, FUPDATE],
            by simp [arg, enter, regs, FUPDATE], by simp [arg, enter, regs, FUPDATE],
            rfl, fun _ _ => ⟨rfl, rfl⟩⟩, by simp [arg, enter, regs, FUPDATE], valid.1, valid.2⟩⟩
        obtain ⟨r, t, ev, _, _, _, _, hr, hclk, hm, _hffi⟩ :=
          echo_refinesClkTight _ _ _ _ arg entry (by change rx.length ≤ fuel; omega)
        change t.clock + rx.length = fuel at hclk
        subst r
        dsimp only [arg] at ev
        simp only [ite_true, ev, BEq.rfl, hm]
        obtain ⟨rest, he, hle, hge⟩ := ih t.clock
          (publishPacket s rx rs tx ts (copyMem (l.rx rx.slot) (l.tx tx) 0 rx.length s.memory))
          (enoughFuel _ _ _ _ _ _ hf hclk valid.1 valid.2)
        exact ⟨rest, he, by omega, by rw [Nat.succ_mul]; omega⟩
      · exact ⟨fuel, rfl, Nat.le_refl _, by omega⟩

/-- Per-ID conservation for the clocked evaluator, including stopped batches. -/
theorem batch_execution_conserves (l : Layout) (b fuel : Nat) (s : Shard) (hf : b * 4096 ≤ fuel) :
    ∃ stop t left k, runBatch l b fuel s = some (stop, t, left) ∧ k ≤ b ∧
      fuel ≤ left + b * 4096 ∧ t.rxActive = s.rxActive.drop k ∧
      t.observed = s.observed + UInt64.ofNat k ∧ ∀ id, owners t id = owners s id := by
  obtain ⟨left, ev, _, cost⟩ := batch_exec_refines l b fuel s hf
  obtain ⟨k, hk, rx, _, _, count, allIds⟩ := bounded_ring_conservation l b s
  exact ⟨_, _, left, k, ev, hk, cost, rx, count, allIds⟩

/-- Between wakes the driver may fill a free RX buffer or drain an active TX.
Each action moves the very descriptor it held; finite traces may mix them
with arbitrary bounded wakes. -/
inductive Reach (l : Layout) (start : Shard) : Shard → Prop
  | boot : Reach l start start
  | wake {s} : Reach l start s → (b : Nat) → Reach l start (stepBoundedBatch l b s).2
  | receive {s id rest} : Reach l start s → s.rxFree = id :: rest → (n : Nat) →
      (m : ByteMemory.Memory) → Reach l start
        { s with rxFree := rest, rxActive := s.rxActive ++ [⟨id, n⟩], memory := m }
  | drain {s packet rest} : Reach l start s → s.txActive = packet :: rest →
      Reach l start { s with txActive := rest, txFree := s.txFree ++ [packet.slot] }

theorem wake_trace_ownership {l start s} (trace : Reach l start s) (id : UInt16) :
    owners s id = owners start id := by
  induction trace with
  | boot => rfl
  | @wake s _ b ih =>
    obtain ⟨_, _, _, _, _, _, ids⟩ := bounded_ring_conservation l b s
    exact (ids id).trans ih
  | receive _ head _ _ ih =>
    rw [← ih]
    simp [owners, head, List.count_cons, List.count_append] <;> omega
  | drain _ head ih =>
    rw [← ih]
    simp [owners, head, List.count_cons, List.count_append] <;> omega

end Obend.Lower.Pancake.DragonStyleShard
