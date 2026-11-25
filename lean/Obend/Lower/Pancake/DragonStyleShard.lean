module
public import Obend.Lower.Pancake.RefinesClkPan
public import Obend.Lower.Pancake.ByteMemory
public import Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.ByteMemory
import Obend.Tactic.Tooth

public section
namespace Obend.Lower.Pancake.DragonStyleShard

abbrev word (n : Nat) : Word := BitVec.ofNat 64 n
private abbrev varE := PExp.lvar
private def plus (a b : PExp) : PExp := .binop .Add [a,b]
private def ptr (name : String) := plus (varE name) (varE "i")
private def copyByte : PStmt := .storeByte (ptr "dst") (.loadByte (ptr "src"))
private def bump : PStmt := .lassign "i" (plus (varE "i") (.const 1))
private def copyLoop : PStmt :=
  .while_ (.cmp .Lower (varE "i") (varE "len")) (.seq copyByte bump)
private def reject : PStmt := .ret (.const 4294967295)
private def guardLt (c : Cmp) (a b : PExp) (next : PStmt) : PStmt :=
  .ite (.cmp c a b) reject next

def echo : PFun := {
  name := "dn_echo", params := ["src","dst","len","cap"].map (·, .One), exported := true
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
  | n+1, m => copyMem src dst (i+1) n (copyOne m (src + word i) (dst + word i))
termination_by structural n => n

theorem copyMem_frame (src dst z : Word) (i n : Nat) (m : ByteMemory.Memory)
    (outside : ∀ j, i ≤ j → j < i+n → dst + word j ≠ z) :
    ByteMemory.read (copyMem src dst i n m) z = ByteMemory.read m z := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    rw [copyMem, ih (i+1) _ (fun j lo hi => outside j (by omega) (by omega))]
    simp [copyOne, ByteMemory.read_put, outside i (by omega) (by omega)]

private theorem index_ne (p : Word) (a b : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (ne : a ≠ b) : p + word a ≠ p + word b := by
  intro h
  have e : word a = word b := by simpa using h
  have := congrArg BitVec.toNat e
  simp [word, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, ne] at this

theorem copyMem_payload (src dst : Word) (i n j : Nat) (m : ByteMemory.Memory)
    (bound : i+n < 2^64) (lo : i ≤ j) (hi : j < i+n)
    (disjoint : ∀ a b, i ≤ a → a < i+n → i ≤ b → b < i+n → dst+word a ≠ src+word b) :
    ByteMemory.read (copyMem src dst i n m) (dst+word j) = ByteMemory.read m (src+word j) := by
  induction n generalizing i m with
  | zero => omega
  | succ n ih =>
    rw [copyMem]
    by_cases e : i = j
    · subst j
      rw [copyMem_frame _ _ _ _ _ _ (fun k hk hi => index_ne dst k i (by omega) (by omega) (by omega))]
      simp [copyOne, ByteMemory.read_put]
    · rw [ih (i+1) _ (by omega) (by omega) (by omega)
        (fun a b ha hb hc hd => disjoint a b (by omega) (by omega) (by omega) (by omega))]
      simp [copyOne, ByteMemory.read_put, disjoint i j (by omega) (by omega) lo hi]

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

private def afterByte {θ} (s : PanState θ) (src dst : Word) (i : Nat) : PanState θ :=
  { s with
    clock := s.clock - 1
    locals := FUPDATE s.locals ("i", .word (word (i+1)))
    memory := copyOne s.memory (src + word i) (dst + word i) }

private theorem body_runs {θ} (s : PanState θ) {src dst : Word} {i len : Nat}
    (hs : Buffers s src dst len) (hi : s.locals "i" = some (.word (word i))) (lt : i < len) :
    evaluate (.seq copyByte bump) (dec_clock s) = (.normal, afterByte s src dst i) := by
  obtain ⟨ha, hb⟩ := hs.mapped _ lt
  simp [evaluate_seq, copyByte, ptr, plus, bump, evaluate_storeByte, evaluate_assign,
    dec_clock, word_op, hs.srcPtr, hs.dstPtr, hi, hs.little, mem_load_byte, ha,
    mem_store_byte_eq hb, is_valid_value_local, set_kvar, set_var, afterByte,
    copyOne, ByteMemory.put, ByteMemory.read, BitVec.ofNat_add]

private theorem loop_runs {θ} (src dst : Word) (len : Nat) (bound : len ≤ 4096) (rem : Nat) :
    ∀ i (s : PanState θ), i + rem = len → Buffers s src dst len →
    s.locals "i" = some (.word (word i)) → rem ≤ s.clock →
    ∃ t, evaluate copyLoop s = (.normal, t) ∧ t.clock + rem = s.clock ∧
      t.memory = copyMem src dst i rem s.memory ∧ t.locals "len" = s.locals "len" := by
  induction rem with
  | zero =>
    intro i s hl hs hi _
    have he : i = len := by omega
    refine ⟨s, ?_, by omega, rfl, rfl⟩
    rw [copyLoop, evaluate_while]
    simp [hi, hs.length, he, cmp_nat len len bound bound]
  | succ n ih =>
    intro i s hl hs hi hc
    have lt : i < len := by omega
    let u := afterByte s src dst i
    have hu : Buffers u src dst len :=
      ⟨by simpa [u, afterByte, FUPDATE] using hs.srcPtr,
       by simpa [u, afterByte, FUPDATE] using hs.dstPtr,
       by simpa [u, afterByte, FUPDATE] using hs.length, hs.little, hs.mapped⟩
    have clk : u.clock = s.clock - 1 := rfl
    obtain ⟨t, ht, htclk, hm, hv⟩ := ih (i+1) u (by omega) hu
      (by simp [u, afterByte, FUPDATE]) (by omega)
    refine ⟨t, ?_, by omega, hm, hv.trans (by simp [u, afterByte, FUPDATE])⟩
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

theorem echo_refinesClkTight {θ} (src dst : Word) (n cap : Nat) :
    RefinesClkTight (θ := θ) (EchoEntry src dst n cap) echo.body n (fun s r t =>
      r = .ret (.word (word n)) ∧ t.clock + n = s.clock ∧
      t.memory = copyMem src dst 0 n s.memory) := by
  intro s h hc
  obtain ⟨hs, hv, hn, hb⟩ := h.2
  let u := { s with locals := FUPDATE s.locals ("i", .word 0#64) }
  have hu : Buffers u src dst n :=
    ⟨by simpa [u, FUPDATE] using hs.srcPtr, by simpa [u, FUPDATE] using hs.dstPtr,
      by simpa [u, FUPDATE] using hs.length, hs.little, hs.mapped⟩
  obtain ⟨t, ht, htclk, hm, hl⟩ := loop_runs src dst n (by omega) n 0 u (by omega)
    hu (by simp [u, FUPDATE]) hc
  let out := empty_locals { t with locals := res_var t.locals ("i", s.locals "i") }
  have lend : res_var t.locals ("i", s.locals "i") "len" = some (.word (word n)) := by
    have key := hl.trans hu.length
    cases hx : s.locals "i" <;> simp [res_var, FUPDATE, DOMSUB, key]
  have ev : evaluate echo.body s = (.ret (.word (word n)), out) := by
    simp [echo, guardLt, evaluate_ite, hs.length, hv, nonneg n (by omega), nonneg cap hb,
      cmp_nat 4096 cap (by decide) hb, cmp_nat cap n hb (by omega),
      Nat.not_lt.mpr hb, Nat.not_lt.mpr hn, evaluate_seq, evaluate_dec,
      show evaluate copyLoop {s with locals := FUPDATE s.locals ("i", .word 0#64)} = (.normal,t) from ht,
      evaluate_ret, lend, out]
  have wf := evaluate_preserves_stateWF echo.body s h.1
  rw [ev] at wf
  change t.clock + n = s.clock at htclk
  exact ⟨_, _, ev, PanResult.noConfusion, PanResult.noConfusion, by change s.clock ≤ t.clock + n; omega,
    wf, rfl, htclk, hm⟩

private def regs (src dst : Word) (n cap : Nat) : FMap String PanVal :=
  FUPDATE (FUPDATE (FUPDATE (FUPDATE FEMPTY ("src", .word src)) ("dst", .word dst))
    ("len", .word (word n))) ("cap", .word (word cap))

theorem echo_entry_inhabited (src dst : Word) (n cap : Nat) (hn : n ≤ cap) (hc : cap ≤ 4096) :
    ∃ s : PanState Unit, EntryWF (EchoEntry src dst n cap) s ∧ s.clock ≥ n := by
  let s := { emptyPanState () n with locals := regs src dst n cap, memaddrs := fun _ => true }
  exact ⟨s, ⟨emptyPanState_wf () n,
    ⟨⟨by simp [s, regs, FUPDATE], by simp [s, regs, FUPDATE], by simp [s, regs, FUPDATE],
      rfl, fun _ _ => ⟨rfl,rfl⟩⟩, by simp [s, regs, FUPDATE], hn, hc⟩⟩, Nat.le_refl _⟩

theorem echo_rejects {θ} (s : PanState θ) (n cap : Word)
    (hn : s.locals "len" = some (.word n)) (hc : s.locals "cap" = some (.word cap))
    (invalid : n.slt 0 ∨ cap.slt 0 ∨ 4096 < cap.toNat ∨ cap.toNat < n.toNat) :
    evaluate echo.body s = (.ret (.word 4294967295), empty_locals s) := by
  simp only [echo, guardLt, evaluate_ite, eval_cmp, eval_lvar, eval_const, hn, hc, word_cmp]
  rcases invalid with h | h | h | h
  all_goals simp_all [BitVec.ult, reject, evaluate_ret] <;> repeat' split <;> simp_all

/-- Four physical cells, including when only two TX leases circulate. Head
and count are the bounded counterparts of the hosted fixture's ring fields. -/
structure Ring (α : Type) where
  slots : Vector α 4
  head : Fin 4
  count : Fin 5

private def cell (head offset : Nat) : Fin 4 := ⟨(head+offset)%4, by omega⟩

def Ring.view {α} (q : Ring α) : List α :=
  List.ofFn (n := q.count.val) fun i => q.slots.get (cell q.head i)

def Ring.peek {α} (q : Ring α) := q.slots.get q.head

def Ring.take {α} (q : Ring α) (_ : 0 < q.count.val) : Ring α :=
  {q with head := cell q.head 1, count := ⟨q.count-1, by have := q.count.isLt; omega⟩}

def Ring.put {α} (q : Ring α) (v : α) (room : q.count.val < 4) : Ring α :=
  {q with
    slots := q.slots.set (cell q.head q.count).val v (cell q.head q.count).isLt
    count := ⟨q.count+1, by omega⟩}

theorem ring_take_fifo {α} (q : Ring α) (ready : 0 < q.count.val) :
    q.view = q.peek :: (q.take ready).view := by
  obtain ⟨slots, head, ⟨n,hn⟩⟩ := q
  cases n with
  | zero => contradiction
  | succ n =>
    simp only [Ring.view, Ring.take, Ring.peek, List.ofFn_succ, Nat.add_one_sub_one]
    congr 1
    · congr 1; apply Fin.ext; simp [cell, Nat.mod_eq_of_lt head.isLt]
    · congr 1; funext i; congr 1; apply Fin.ext
      dsimp [cell]
      omega

theorem ring_put_fifo {α} (q : Ring α) (v : α) (room : q.count.val < 4) :
    (q.put v room).view = q.view ++ [v] := by
  simp only [Ring.view, Ring.put, List.ofFn_succ_last]
  congr 1
  · congr 1; funext i
    change (q.slots.set _ v _)[(cell q.head i.val).val] = q.slots[(cell q.head i.val).val]
    apply Vector.getElem_set_ne
    dsimp [cell]
    have := i.isLt
    omega
  · congr 1
    exact Vector.getElem_set_self _

end Obend.Lower.Pancake.DragonStyleShard
