module
public import Obend.Lower.Pancake.BorrowedTurn
public import Obend.Lower.Pancake.FfiTrace
import all Obend.Lower.Pancake.BorrowedTurn
import all Obend.Lower.Pancake.DragonStyleShard
import all Obend.Lower.Pancake.FfiTrace
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.ByteMemory

public section
namespace Obend.Lower.Pancake.DurableTurn

set_option autoImplicit false

abbrev word (x : Nat) : Word := BitVec.ofNat 64 x
private abbrev v := PExp.lvar
private def n (i : Nat) : PExp := .const (word i)
private def add (a b : PExp) : PExp := .binop .Add [a, b]
private def sub (a b : PExp) : PExp := .binop .Sub [a, b]
private def mul (a b : PExp) : PExp := .panop .Mul [a, b]
private def band (a b : PExp) : PExp := .binop .And [a, b]
private def byte (p off : PExp) : PExp := .loadByte (add p off)
private def wordAt (p : PExp) (off : Nat) : PExp := .load .One (add p (n off))
private def storeWord (p : PExp) (off : Nat) (val : PExp) : PStmt := .store (add p (n off)) val
private def ret (i : Nat) : PStmt := .ret (n i)
private def seqs : List PStmt → PStmt
  | [] => .skip
  | [x] => x
  | x :: xs => .seq x (seqs xs)
private def failIf (c : Cmp) (a b : PExp) (code : Nat) : PStmt :=
  .ite (.cmp c a b) (ret code) .skip
private def localVar (name : String) (init : PExp) (body : PStmt) := PStmt.dec name .One init body
private def inc (name : String) := PStmt.lassign name (add (v name) (n 1))

/-! ## 1. Compact Packed-Word Byte Matching & `parseFrame` (`0..4096`B Bodies) -/

private def byteAt (ba : ByteArray) (i : Nat) : UInt8 :=
  if h : i < ba.size then ba[i] else 0

/-- Pack `k` bytes (`k ≤ 8`) from `pat[start .. start+k)` little-endian into one 64-bit word. -/
def packBytes (pat : ByteArray) (start : Nat) : Nat → Word
  | 0 => 0#64
  | k + 1 =>
    let b : Word := BitVec.ofNat 64 (byteAt pat start).toNat
    b ||| (packBytes pat (start + 1) k <<< 8)

private theorem packBytes_low (pat : ByteArray) (start k : Nat) :
    (packBytes pat start (k + 1) &&& 255#64) = word (byteAt pat start).toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [packBytes, word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · have h255 : (255 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [h8, h255]
  · have h255 : (255 : Nat).testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hb : (byteAt pat start).toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (byteAt pat start).toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h255, hb]

private theorem packBytes_high_zero (pat : ByteArray) (start k i : Nat) (hk : k ≤ 7) (hi : 8 * k ≤ i) :
    (packBytes pat start k).getLsbD i = false := by
  induction k generalizing start i with
  | zero => simp [packBytes]
  | succ k ih =>
    simp only [packBytes, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft]
    have hb : (byteAt pat start).toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (byteAt pat start).toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    by_cases h64 : i < 64
    · simp [hb, h64, show ¬i < 8 by omega, ih (start + 1) (i - 8) (by omega) (by omega)]
    · simp [h64]

private theorem packBytes_shr8 (pat : ByteArray) (start k : Nat) (hk : k ≤ 7) :
    (packBytes pat start (k + 1) >>> 8) = packBytes pat (start + 1) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [packBytes, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_shiftLeft]
  by_cases h56 : 8 + i < 64
  · have hb : (byteAt pat start).toNat.testBit (8 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (byteAt pat start).toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h56, hb, show ¬8 + i < 8 by omega]
  · have hr : (packBytes pat (start + 1) k).getLsbD i = false :=
      packBytes_high_zero pat (start + 1) k i hk (by omega)
    simp [h56, hr]

/-- Loop matching `cnt ≤ 8` bytes at `src + off` against the little-endian packed word `w`.
Returns `0` early on any mismatch; leaves memory and FFI untouched. -/
private def matchPackLoop (off : PExp) : PStmt :=
  .while_ (.cmp .Lower (v "k") (v "cnt")) (seqs [
    failIf .NotEqual (byte (v "src") (add off (v "k"))) (band (v "w") (n 255)) 0,
    .lassign "w" (.shift .Lsr (v "w") 8),
    inc "k"])

private def matchPack (off : PExp) (w : Word) (count : Nat) : PStmt :=
  localVar "w" (.const w) <| localVar "cnt" (n count) <| localVar "k" (n 0) <|
    matchPackLoop off

/-- Scan 1..4 ASCII decimal digits at `src + 54` into `(d, val)`. -/
private def scanDigitsLoop : PStmt :=
  .while_ (.cmp .Lower (v "d") (n 4)) <|
    localVar "ch" (byte (v "src") (add (n 54) (v "d"))) (seqs [
      .ite (.cmp .Lower (v "ch") (n 48)) .break_ .skip,
      .ite (.cmp .Lower (n 57) (v "ch")) .break_ .skip,
      .lassign "val" (add (mul (v "val") (n 10)) (sub (v "ch") (n 48))),
      inc "d"])

/-- Match the 54-byte HTTP request-line & header prefix as seven packed 64-bit word checks
(6 × 8B + 1 × 6B), avoiding 54-way unrolled byte branches. -/
private def matchHeader : PStmt := seqs [
  matchPack (n 0)  (packBytes BorrowedTurn.header 0  8) 8,
  matchPack (n 8)  (packBytes BorrowedTurn.header 8  8) 8,
  matchPack (n 16) (packBytes BorrowedTurn.header 16 8) 8,
  matchPack (n 24) (packBytes BorrowedTurn.header 24 8) 8,
  matchPack (n 32) (packBytes BorrowedTurn.header 32 8) 8,
  matchPack (n 40) (packBytes BorrowedTurn.header 40 8) 8,
  matchPack (n 48) (packBytes BorrowedTurn.header 48 6) 6]

private def parseBody : PStmt := seqs [
  failIf .Lower (v "len") (n 59) 0,
  failIf .Lower (n 4158) (v "len") 0,
  matchHeader,
  localVar "d" (n 0) <| localVar "val" (n 0) <| seqs [
    scanDigitsLoop,
    failIf .Equal (v "d") (n 0) 0,
    .ite (.cmp .Lower (n 1) (v "d")) (failIf .Equal (byte (v "src") (n 54)) (n 48) 0) .skip,
    failIf .Lower (n 4096) (v "val") 0,
    localVar "off" (add (n 58) (v "d")) <| seqs [
      failIf .NotEqual (v "len") (add (v "off") (v "val")) 0,
      matchPack (add (n 54) (v "d")) (packBytes BorrowedTurn.delimiter 0 4) 4,
      .ret (v "off")]]]

def parseFrame : PFun := {
  name := "parseFrame", params := ["src", "len"].map (·, .One), exported := true
  body := parseBody }

/-- Tight clock budget for `parseFrame`: 54 header byte checks + ≤4 digit loop steps + 4 delimiter checks. -/
def parseFrameClk : Nat := 62

/-- A verifier-owned RX lease supplies a pointer, the descriptor length, and a
mapped byte at every offset below that length. -/
structure RxFrame {θ : Type} (s : PanState θ) (src : Word) (frame : ByteArray) : Prop where
  pointer : s.locals "src" = some (.word src)
  length : s.locals "len" = some (.word (word frame.size))
  fits : frame.size < 2 ^ 64
  bytes : ∀ i, i < frame.size → mem_load_byte s.memory s.memaddrs s.be
    (src + word i) = some frame[i]!.toBitVec

private theorem eval_n {θ : Type} (s : PanState θ) (i : Nat) :
    eval s (n i) = some (.word (word i)) := rfl

private theorem load_at {θ : Type} {s : PanState θ} {src : Word} {frame : ByteArray}
    (rx : RxFrame s src frame) (i : Nat) (h : i < frame.size) :
    eval s (byte (v "src") (n i)) = some (.word (word frame[i]!.toNat)) := by
  simp [byte, add, n, rx.pointer, word_op, rx.bytes i h, word]
  apply BitVec.eq_of_toNat_eq
  simp

private theorem load_at_expr {θ : Type} {s : PanState θ} {src : Word} {frame : ByteArray}
    (rx : RxFrame s src frame) (e : PExp) (i : Nat) (he : eval s e = some (.word (word i)))
    (h : i < frame.size) :
    eval s (byte (v "src") e) = some (.word (word frame[i]!.toNat)) := by
  simp [byte, add, rx.pointer, he, word_op, rx.bytes i h, word]
  apply BitVec.eq_of_toNat_eq
  simp

private theorem cmp_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    word_cmp .Lower (word a) (word b) = decide (a < b) := by
  simp only [word_cmp, BitVec.ult, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem eq_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (word a == word b) = decide (a = b) := by
  cases h : decide (a = b) with
  | true =>
    have hab := of_decide_eq_true h
    subst hab; simp
  | false =>
    have hne := of_decide_eq_false h
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp [word, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact hne this

private theorem failIf_eval {θ : Type} (s : PanState θ) (c : Cmp) (a b : PExp) (x y : Word)
    (ha : eval s a = some (.word x)) (hb : eval s b = some (.word y)) :
    evaluate (failIf c a b 0) s =
      if word_cmp c x y then (.ret (.word 0), empty_locals s) else (.normal, s) := by
  cases h : word_cmp c x y <;> simp [failIf, evaluate_ite, evaluate_ret, evaluate_skip, ha, hb, h, ret, n]

private theorem pack_loop_runs {θ : Type} {src : Word} {frame pat : ByteArray}
    (offE : PExp) (off start cnt : Nat) (hcnt : cnt ≤ 8)
    (hoff_in : off + cnt ≤ frame.size) (hpat_in : start + cnt ≤ pat.size)
    (rem : Nat) :
    ∀ (k : Nat) (s : PanState θ), k + rem = cnt →
      RxFrame s src frame →
      (∀ s' : PanState θ, s'.locals "d" = s.locals "d" → eval s' offE = some (.word (word off))) →
      s.locals "k" = some (.word (word k)) →
      s.locals "cnt" = some (.word (word cnt)) →
      s.locals "w" = some (.word (packBytes pat (start + k) rem)) →
      rem ≤ s.clock →
      (∀ i, k ≤ i → i < cnt → frame[off + i]? = pat[start + i]?) →
      ∃ t, evaluate (matchPackLoop offE) s = (.normal, t) ∧
        t.clock + rem = s.clock ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals ∧
        (∀ x, x ≠ "k" → x ≠ "w" → t.locals x = s.locals x) := by
  induction rem with
  | zero =>
    intro k s hkr _ _ hk hct _ _ _
    have he : k = cnt := by omega
    refine ⟨s, ?_, by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
    rw [matchPackLoop, evaluate_while]
    simp [hk, hct, he, cmp_small cnt cnt (by omega) (by omega)]
  | succ r ih =>
    intro k s hkr rx hoffE hk hct hw hclk hmatch
    have hklt : k < cnt := by omega
    have hfi : off + k < frame.size := by omega
    have hpi : start + k < pat.size := by omega
    have hmeq : frame[off + k]! = pat[start + k]! := by
      have hm := hmatch k (Nat.le_refl _) hklt
      simp only [getElem?_pos, hfi, hpi, Option.some.injEq] at hm
      simpa [getElem!_pos, hfi, hpi] using hm
    have hpatget : byteAt pat (start + k) = pat[start + k]! := by
      simp [byteAt, hpi, getElem!_pos]
    have hdec_off : eval (dec_clock s) (add offE (v "k")) = some (.word (word (off + k))) := by
      have ho := hoffE (dec_clock s) rfl
      rw [add, eval_binop2, ho]
      simp [dec_clock, hk, word_op, word, BitVec.ofNat_add]
    have hdec_rx : RxFrame (dec_clock s) src frame := ⟨rx.pointer, rx.length, rx.fits, rx.bytes⟩
    have hbyte := load_at_expr hdec_rx (add offE (v "k")) (off + k) hdec_off hfi
    have hmask : eval (dec_clock s) (band (v "w") (n 255)) = some (.word (word frame[off + k]!.toNat)) := by
      rw [band, eval_binop2, eval_lvar, eval_n]
      simp only [dec_clock, hw, word_op, List.foldr, Option.map_some, Option.some.injEq, PanVal.word.injEq]
      have h255 : (word 255 &&& ~~~0#64) = 255#64 := by decide
      rw [h255, packBytes_low, hpatget, hmeq]
    have hfail : evaluate (failIf .NotEqual (byte (v "src") (add offE (v "k"))) (band (v "w") (n 255)) 0)
        (dec_clock s) = (.normal, dec_clock s) := by
      rw [failIf_eval _ _ _ _ _ _ hbyte hmask]
      simp [word_cmp]
    have hsh : word_sh .Lsr (packBytes pat (start + k) (r + 1)) 8 =
        some (packBytes pat (start + (k + 1)) r) := by
      simp only [word_sh, show (8 != 0 && decide (8 ≥ 64)) = false by decide,
        Bool.false_eq_true, ↓reduceIte, packBytes_shr8 pat (start + k) r (by omega), Nat.add_assoc]
    let u : PanState θ :=
      { dec_clock s with
        locals := FUPDATE (FUPDATE s.locals ("w", .word (packBytes pat (start + (k + 1)) r)))
          ("k", .word (word (k + 1))) }
    have hbody : evaluate (seqs [
        failIf .NotEqual (byte (v "src") (add offE (v "k"))) (band (v "w") (n 255)) 0,
        .lassign "w" (.shift .Lsr (v "w") 8),
        inc "k"]) (dec_clock s) = (.normal, u) := by
      simp only [seqs]
      rw [evaluate_seq, hfail]
      simp [evaluate_seq, evaluate_assign, eval, evalList, extractWords, dec_clock, hw, hsh,
        is_valid_value_local, set_kvar, set_var, inc, add, eval_n, FUPDATE, hk, word_op,
        word, BitVec.ofNat_add, u]
    have hurx : RxFrame u src frame :=
      ⟨by simp [u, FUPDATE, rx.pointer], by simp [u, FUPDATE, rx.length], rx.fits, rx.bytes⟩
    have huoff : ∀ s' : PanState θ, s'.locals "d" = u.locals "d" → eval s' offE = some (.word (word off)) := by
      intro s' hd; apply hoffE s'; simpa [u, FUPDATE] using hd
    obtain ⟨t, ht, htclk, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl, hloc⟩ :=
      ih (k + 1) u (by omega) hurx huoff (by simp [u, FUPDATE]) (by simp [u, FUPDATE, hct])
        (by simp [u, FUPDATE]) (by simp [u, dec_clock]; omega) (fun i h1 h2 => hmatch i (by omega) h2)
    refine ⟨t, ?_, by simp [u, dec_clock] at htclk; omega, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl,
      fun x hxk hxw => (hloc x hxk hxw).trans (by simp [u, FUPDATE, hxk, hxw])⟩
    conv => lhs; rw [matchPackLoop, evaluate_while]
    have hnz : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [eval_cmp, eval_lvar, hk, hct, cmp_small k cnt (by omega) (by omega),
      decide_eq_true hklt, ite_true, hnz, hbody]
    exact ht

private theorem pack_loop_fails {θ : Type} {src : Word} {frame pat : ByteArray}
    (offE : PExp) (off start cnt : Nat) (hcnt : cnt ≤ 8)
    (hoff_in : off + cnt ≤ frame.size) (hpat_in : start + cnt ≤ pat.size)
    (rem : Nat) :
    ∀ (k : Nat) (s : PanState θ), k + rem = cnt →
      RxFrame s src frame →
      (∀ s' : PanState θ, s'.locals "d" = s.locals "d" → eval s' offE = some (.word (word off))) →
      s.locals "k" = some (.word (word k)) →
      s.locals "cnt" = some (.word (word cnt)) →
      s.locals "w" = some (.word (packBytes pat (start + k) rem)) →
      rem ≤ s.clock →
      (∃ i, k ≤ i ∧ i < cnt ∧ frame[off + i]? ≠ pat[start + i]?) →
      ∃ t, evaluate (matchPackLoop offE) s = (.ret (.word 0), empty_locals t) ∧
        s.clock ≤ t.clock + rem ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals := by
  induction rem with
  | zero =>
    intro k s hkr _ _ _ _ _ _ ⟨i, h1, h2, _⟩
    omega
  | succ r ih =>
    intro k s hkr rx hoffE hk hct hw hclk ⟨j, hj1, hj2, hjne⟩
    have hklt : k < cnt := by omega
    have hfi : off + k < frame.size := by omega
    have hpi : start + k < pat.size := by omega
    have hpatget : byteAt pat (start + k) = pat[start + k]! := by
      simp [byteAt, hpi, getElem!_pos]
    have hdec_off : eval (dec_clock s) (add offE (v "k")) = some (.word (word (off + k))) := by
      have ho := hoffE (dec_clock s) rfl
      rw [add, eval_binop2, ho]
      simp [dec_clock, hk, word_op, word, BitVec.ofNat_add]
    have hdec_rx : RxFrame (dec_clock s) src frame := ⟨rx.pointer, rx.length, rx.fits, rx.bytes⟩
    have hbyte := load_at_expr hdec_rx (add offE (v "k")) (off + k) hdec_off hfi
    have hmask : eval (dec_clock s) (band (v "w") (n 255)) = some (.word (word pat[start + k]!.toNat)) := by
      rw [band, eval_binop2, eval_lvar, eval_n]
      simp only [dec_clock, hw, word_op, List.foldr, Option.map_some, Option.some.injEq, PanVal.word.injEq]
      have h255 : (word 255 &&& ~~~0#64) = 255#64 := by decide
      rw [h255, packBytes_low, hpatget]
    have hnz : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    if hEq : frame[off + k]! = pat[start + k]! then
      have hjgt : k + 1 ≤ j := by
        if hjk : j = k then
          subst hjk
          exfalso; apply hjne
          simp [getElem?_pos, hfi, hpi]
          simpa [getElem!_pos, hfi, hpi] using hEq
        else omega
      have hfail : evaluate (failIf .NotEqual (byte (v "src") (add offE (v "k"))) (band (v "w") (n 255)) 0)
          (dec_clock s) = (.normal, dec_clock s) := by
        rw [failIf_eval _ _ _ _ _ _ hbyte hmask, hEq]
        simp [word_cmp]
      have hsh : word_sh .Lsr (packBytes pat (start + k) (r + 1)) 8 =
          some (packBytes pat (start + (k + 1)) r) := by
        simp only [word_sh, show (8 != 0 && decide (8 ≥ 64)) = false by decide,
          Bool.false_eq_true, ↓reduceIte, packBytes_shr8 pat (start + k) r (by omega), Nat.add_assoc]
      let u : PanState θ :=
        { dec_clock s with
          locals := FUPDATE (FUPDATE s.locals ("w", .word (packBytes pat (start + (k + 1)) r)))
            ("k", .word (word (k + 1))) }
      have hbody : evaluate (seqs [
          failIf .NotEqual (byte (v "src") (add offE (v "k"))) (band (v "w") (n 255)) 0,
          .lassign "w" (.shift .Lsr (v "w") 8),
          inc "k"]) (dec_clock s) = (.normal, u) := by
        simp only [seqs]
        rw [evaluate_seq, hfail]
        simp [evaluate_seq, evaluate_assign, eval, evalList, extractWords, dec_clock, hw, hsh,
          is_valid_value_local, set_kvar, set_var, inc, add, eval_n, FUPDATE, hk, word_op,
          word, BitVec.ofNat_add, u]
      have hurx : RxFrame u src frame :=
        ⟨by simp [u, FUPDATE, rx.pointer], by simp [u, FUPDATE, rx.length], rx.fits, rx.bytes⟩
      have huoff : ∀ s' : PanState θ, s'.locals "d" = u.locals "d" → eval s' offE = some (.word (word off)) := by
        intro s' hd; apply hoffE s'; simpa [u, FUPDATE] using hd
      obtain ⟨t, ht, htclk, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl⟩ :=
        ih (k + 1) u (by omega) hurx huoff (by simp [u, FUPDATE]) (by simp [u, FUPDATE, hct])
          (by simp [u, FUPDATE]) (by simp [u, dec_clock]; omega) ⟨j, hjgt, hj2, hjne⟩
      refine ⟨t, ?_, by simp [u, dec_clock] at htclk; omega, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl⟩
      conv => lhs; rw [matchPackLoop, evaluate_while]
      simp only [eval_cmp, eval_lvar, hk, hct, cmp_small k cnt (by omega) (by omega),
        decide_eq_true hklt, ite_true, hnz, hbody]
      exact ht
    else
      have hwne : word frame[off + k]!.toNat ≠ word pat[start + k]!.toNat := by
        intro heq
        apply hEq
        apply UInt8.toNat_inj.mp
        have h1 := frame[off + k]!.toNat_lt
        have h2 := pat[start + k]!.toNat_lt
        simpa [word, Nat.mod_eq_of_lt (show frame[off + k]!.toNat < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show pat[start + k]!.toNat < 2 ^ 64 by omega)] using congrArg BitVec.toNat heq
      have hfail : evaluate (failIf .NotEqual (byte (v "src") (add offE (v "k"))) (band (v "w") (n 255)) 0)
          (dec_clock s) = (.ret (.word 0), empty_locals (dec_clock s)) := by
        rw [failIf_eval _ _ _ _ _ _ hbyte hmask]
        simp [word_cmp, hwne]
      refine ⟨dec_clock s, ?_, by simp [dec_clock]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      conv => lhs; rw [matchPackLoop, evaluate_while]
      simp [eval_cmp, eval_lvar, hk, hct, cmp_small k cnt (by omega) (by omega),
        decide_eq_true hklt, hnz, seqs, evaluate_seq, hfail]

private theorem matchPack_refines {θ : Type} {s : PanState θ} {src : Word} {frame pat : ByteArray}
    (rx : RxFrame s src frame) (offE : PExp) (off start cnt : Nat) (hcnt : cnt ≤ 8)
    (hoff_in : off + cnt ≤ frame.size) (hpat_in : start + cnt ≤ pat.size) (hclk : cnt ≤ s.clock)
    (hoffE : ∀ s' : PanState θ, s'.locals "d" = s.locals "d" → eval s' offE = some (.word (word off))) :
    (∀ i < cnt, frame[off + i]? = pat[start + i]?) →
      ∃ t, evaluate (matchPack offE (packBytes pat start cnt) cnt) s = (.normal, t) ∧
        t.clock + cnt = s.clock ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals ∧
        t.locals = s.locals := by
  intro hmatch
  let s1 := { s with locals := FUPDATE s.locals ("w", .word (packBytes pat start cnt)) }
  let s2 := { s1 with locals := FUPDATE s1.locals ("cnt", .word (word cnt)) }
  let s3 := { s2 with locals := FUPDATE s2.locals ("k", .word (word 0)) }
  have hrx3 : RxFrame s3 src frame :=
    ⟨by simp [s3, s2, s1, FUPDATE, rx.pointer], by simp [s3, s2, s1, FUPDATE, rx.length], rx.fits, rx.bytes⟩
  have hoff3 : ∀ s' : PanState θ, s'.locals "d" = s3.locals "d" → eval s' offE = some (.word (word off)) := by
    intro s' hd; apply hoffE s'; simpa [s3, s2, s1, FUPDATE] using hd
  obtain ⟨t, ht, htclk, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl, hloc⟩ :=
    pack_loop_runs offE off start cnt hcnt hoff_in hpat_in cnt 0 s3 (by omega) hrx3 hoff3
      (by simp [s3, FUPDATE]) (by simp [s3, s2, FUPDATE]) (by simp [s3, s2, s1, FUPDATE])
      hclk (fun i _ h2 => hmatch i h2)
  have hres : res_var (res_var (res_var t.locals ("k", s2.locals "k")) ("cnt", s1.locals "cnt"))
      ("w", s.locals "w") = s.locals := by
    funext x
    by_cases hxw : x = "w"
    · subst hxw; cases hsw : s.locals "w" <;> simp [res_var, FUPDATE, DOMSUB]
    · by_cases hxc : x = "cnt"
      · subst hxc
        have hs1c : s1.locals "cnt" = s.locals "cnt" := by simp [s1, FUPDATE]
        rw [hs1c]
        cases hsw : s.locals "w" <;> cases hsc : s.locals "cnt" <;>
          simp [res_var, FUPDATE, DOMSUB]
      · by_cases hxk : x = "k"
        · subst hxk
          have hs2k : s2.locals "k" = s.locals "k" := by simp [s2, s1, FUPDATE]
          rw [hs2k]
          cases hsw : s.locals "w" <;> cases hsc : s1.locals "cnt" <;> cases hsk : s.locals "k" <;>
            simp [res_var, FUPDATE, DOMSUB]
        · have hx := hloc x hxk hxw
          cases hsw : s.locals "w" <;> cases hsc : s1.locals "cnt" <;> cases hsk : s2.locals "k" <;>
            simp [res_var, FUPDATE, DOMSUB, hxw, hxc, hxk, hx, s3, s2, s1]
  refine ⟨{ t with locals := s.locals }, ?_, htclk, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl, rfl⟩
  simp only [matchPack, localVar, evaluate_dec, eval_const, shape_of_word, beq_self_eq_true, ↓reduceIte, n]
  change (let r := evaluate (matchPackLoop offE) s3;
    (r.1, { r.2 with locals := res_var (res_var (res_var r.2.locals ("k", s2.locals "k"))
      ("cnt", s1.locals "cnt")) ("w", s.locals "w") })) = _
  rw [ht]; dsimp only; rw [hres]

private theorem matchPack_refuses {θ : Type} {s : PanState θ} {src : Word} {frame pat : ByteArray}
    (rx : RxFrame s src frame) (offE : PExp) (off start cnt : Nat) (hcnt : cnt ≤ 8)
    (hoff_in : off + cnt ≤ frame.size) (hpat_in : start + cnt ≤ pat.size) (hclk : cnt ≤ s.clock)
    (hoffE : ∀ s' : PanState θ, s'.locals "d" = s.locals "d" → eval s' offE = some (.word (word off)))
    (hbad : ∃ i, i < cnt ∧ frame[off + i]? ≠ pat[start + i]?) :
    ∃ t, evaluate (matchPack offE (packBytes pat start cnt) cnt) s = (.ret (.word 0), t) ∧
      s.clock ≤ t.clock + cnt ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
      t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be := by
  let s1 := { s with locals := FUPDATE s.locals ("w", .word (packBytes pat start cnt)) }
  let s2 := { s1 with locals := FUPDATE s1.locals ("cnt", .word (word cnt)) }
  let s3 := { s2 with locals := FUPDATE s2.locals ("k", .word (word 0)) }
  have hrx3 : RxFrame s3 src frame :=
    ⟨by simp [s3, s2, s1, FUPDATE, rx.pointer], by simp [s3, s2, s1, FUPDATE, rx.length], rx.fits, rx.bytes⟩
  have hoff3 : ∀ s' : PanState θ, s'.locals "d" = s3.locals "d" → eval s' offE = some (.word (word off)) := by
    intro s' hd; apply hoffE s'; simpa [s3, s2, s1, FUPDATE] using hd
  obtain ⟨i, hi, hne⟩ := hbad
  obtain ⟨t, ht, htclk, hmem, hffi, hdm, hcd, hbe, _⟩ :=
    pack_loop_fails offE off start cnt hcnt hoff_in hpat_in cnt 0 s3 (by omega) hrx3 hoff3
      (by simp [s3, FUPDATE]) (by simp [s3, s2, FUPDATE]) (by simp [s3, s2, s1, FUPDATE])
      hclk ⟨i, Nat.zero_le _, hi, hne⟩
  let outLoc := res_var (res_var (res_var (empty_locals t).locals ("k", s2.locals "k"))
    ("cnt", s1.locals "cnt")) ("w", s.locals "w")
  refine ⟨{ empty_locals t with locals := outLoc }, ?_, htclk, hmem, hffi, hdm, hcd, hbe⟩
  simp only [matchPack, localVar, evaluate_dec, eval_const, shape_of_word, beq_self_eq_true, ↓reduceIte, n]
  change (let r := evaluate (matchPackLoop offE) s3;
    (r.1, { r.2 with locals := res_var (res_var (res_var r.2.locals ("k", s2.locals "k"))
      ("cnt", s1.locals "cnt")) ("w", s.locals "w") })) = _
  rw [ht]

private theorem decide_chunk_match (frame pat : ByteArray) (off start cnt : Nat) :
    (∀ i < cnt, frame[off + i]? = pat[start + i]?) ∨
    (∃ i, i < cnt ∧ frame[off + i]? ≠ pat[start + i]?) := by
  induction cnt with
  | zero => exact .inl (fun _ h => by omega)
  | succ c ih =>
    rcases ih with hok | ⟨i, hi, hne⟩
    · if heq : frame[off + c]? = pat[start + c]? then
        refine .inl (fun i hi => ?_)
        if hlt : i < c then exact hok i hlt
        else
          have hic : i = c := by omega
          rw [hic]; exact heq
      else
        exact .inr ⟨c, by omega, heq⟩
    · exact .inr ⟨i, by omega, hne⟩

private theorem matchPack_branch {θ : Type} {s : PanState θ} {src : Word} {frame pat : ByteArray}
    (rx : RxFrame s src frame) (offE : PExp) (off start cnt : Nat) (hcnt : cnt ≤ 8)
    (hoff_in : off + cnt ≤ frame.size) (hpat_in : start + cnt ≤ pat.size) (hclk : cnt ≤ s.clock)
    (hoffE : ∀ s' : PanState θ, s'.locals "d" = s.locals "d" → eval s' offE = some (.word (word off))) :
    ((∀ i < cnt, frame[off + i]? = pat[start + i]?) ∧
      ∃ t, evaluate (matchPack offE (packBytes pat start cnt) cnt) s = (.normal, t) ∧
        t.clock + cnt = s.clock ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals ∧
        t.locals = s.locals) ∨
    ((∃ i, i < cnt ∧ frame[off + i]? ≠ pat[start + i]?) ∧
      ∃ t, evaluate (matchPack offE (packBytes pat start cnt) cnt) s = (.ret (.word 0), t) ∧
        s.clock ≤ t.clock + cnt ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be) := by
  rcases decide_chunk_match frame pat off start cnt with hok | hbad
  · exact .inl ⟨hok, matchPack_refines rx offE off start cnt hcnt hoff_in hpat_in hclk hoffE hok⟩
  · exact .inr ⟨hbad, matchPack_refuses rx offE off start cnt hcnt hoff_in hpat_in hclk hoffE hbad⟩

private theorem matchHeader_refines {θ : Type} {s : PanState θ} {src : Word} {frame : ByteArray}
    (rx : RxFrame s src frame) (hmin : 59 ≤ frame.size) (hclk : 54 ≤ s.clock) :
    (BorrowedTurn.matchBytes frame BorrowedTurn.header 0 BorrowedTurn.header.size = true ∧
      ∃ t, evaluate matchHeader s = (.normal, t) ∧
        t.clock + 54 = s.clock ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals ∧
        t.locals = s.locals) ∨
    (BorrowedTurn.matchBytes frame BorrowedTurn.header 0 BorrowedTurn.header.size = false ∧
      ∃ t, evaluate matchHeader s = (.ret (.word 0), t) ∧
        s.clock ≤ t.clock + 54 ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be) := by
  have hsz : BorrowedTurn.header.size = 54 := BorrowedTurn.header_size_eq
  have stepChunk : ∀ (st : PanState θ) (base cnt : Nat),
      RxFrame st src frame → base + cnt ≤ 54 → cnt ≤ 8 → cnt ≤ st.clock →
      ((∀ i < cnt, frame[base + i]? = BorrowedTurn.header[base + i]?) ∧
        ∃ t, evaluate (matchPack (n base) (packBytes BorrowedTurn.header base cnt) cnt) st = (.normal, t) ∧
          t.clock + cnt = st.clock ∧ t.memory = st.memory ∧ t.ffi = st.ffi ∧
          t.memaddrs = st.memaddrs ∧ t.code = st.code ∧ t.be = st.be ∧
          t.base_addr = st.base_addr ∧ t.top_addr = st.top_addr ∧ t.globals = st.globals ∧
          t.locals = st.locals) ∨
      ((∃ i, i < cnt ∧ frame[base + i]? ≠ BorrowedTurn.header[base + i]?) ∧
        ∃ t, evaluate (matchPack (n base) (packBytes BorrowedTurn.header base cnt) cnt) st = (.ret (.word 0), t) ∧
          st.clock ≤ t.clock + cnt ∧ t.memory = st.memory ∧ t.ffi = st.ffi ∧
          t.memaddrs = st.memaddrs ∧ t.code = st.code ∧ t.be = st.be) := by
    intro st base cnt hrx hb hc hcl
    exact matchPack_branch hrx (n base) base base cnt hc (by omega) (by omega) hcl (fun _ _ => rfl)
  have mkFail : ∀ (base i : Nat), base + i < 54 →
      frame[base + i]? ≠ BorrowedTurn.header[base + i]? →
      BorrowedTurn.matchBytes frame BorrowedTurn.header 0 BorrowedTurn.header.size = false := by
    intro base i hlt hne
    cases hm : BorrowedTurn.matchBytes frame BorrowedTurn.header 0 BorrowedTurn.header.size with
    | false => rfl
    | true =>
      have hall := (BorrowedTurn.matchBytes_iff ..).mp hm (base + i) (by omega)
      simp at hall; exact absurd hall hne
  have mkRx : ∀ (st1 st2 : PanState θ), RxFrame st1 src frame →
      st2.locals = st1.locals → st2.memory = st1.memory → st2.memaddrs = st1.memaddrs → st2.be = st1.be →
      RxFrame st2 src frame := by
    intro st1 st2 h hl hm hd hb
    exact ⟨hl ▸ h.pointer, hl ▸ h.length, h.fits, fun i hi => by rw [hm, hd, hb]; exact h.bytes i hi⟩
  simp only [matchHeader, seqs]
  rw [evaluate_seq]; dsimp only
  rcases stepChunk s 0 8 rx (by omega) (by decide) (by omega) with ⟨h0, t0, e0, c0, m0, f0, d0, cd0, b0, ba0, ta0, g0, l0⟩ | ⟨⟨i, hi, hne⟩, t0, e0, c0, m0, f0, d0, cd0, b0⟩
  · rw [e0]; simp only [beq_self_eq_true, ↓reduceIte]
    have rx0 := mkRx s t0 rx l0 m0 d0 b0
    rw [evaluate_seq]; dsimp only
    rcases stepChunk t0 8 8 rx0 (by omega) (by decide) (by omega) with ⟨h1, t1, e1, c1, m1, f1, d1, cd1, b1, ba1, ta1, g1, l1⟩ | ⟨⟨i, hi, hne⟩, t1, e1, c1, m1, f1, d1, cd1, b1⟩
    · rw [e1]; simp only [beq_self_eq_true, ↓reduceIte]
      have rx1 := mkRx t0 t1 rx0 l1 m1 d1 b1
      rw [evaluate_seq]; dsimp only
      rcases stepChunk t1 16 8 rx1 (by omega) (by decide) (by omega) with ⟨h2, t2, e2, c2, m2, f2, d2, cd2, b2, ba2, ta2, g2, l2⟩ | ⟨⟨i, hi, hne⟩, t2, e2, c2, m2, f2, d2, cd2, b2⟩
      · rw [e2]; simp only [beq_self_eq_true, ↓reduceIte]
        have rx2 := mkRx t1 t2 rx1 l2 m2 d2 b2
        rw [evaluate_seq]; dsimp only
        rcases stepChunk t2 24 8 rx2 (by omega) (by decide) (by omega) with ⟨h3, t3, e3, c3, m3, f3, d3, cd3, b3, ba3, ta3, g3, l3⟩ | ⟨⟨i, hi, hne⟩, t3, e3, c3, m3, f3, d3, cd3, b3⟩
        · rw [e3]; simp only [beq_self_eq_true, ↓reduceIte]
          have rx3 := mkRx t2 t3 rx2 l3 m3 d3 b3
          rw [evaluate_seq]; dsimp only
          rcases stepChunk t3 32 8 rx3 (by omega) (by decide) (by omega) with ⟨h4, t4, e4, c4, m4, f4, d4, cd4, b4, ba4, ta4, g4, l4⟩ | ⟨⟨i, hi, hne⟩, t4, e4, c4, m4, f4, d4, cd4, b4⟩
          · rw [e4]; simp only [beq_self_eq_true, ↓reduceIte]
            have rx4 := mkRx t3 t4 rx3 l4 m4 d4 b4
            rw [evaluate_seq]; dsimp only
            rcases stepChunk t4 40 8 rx4 (by omega) (by decide) (by omega) with ⟨h5, t5, e5, c5, m5, f5, d5, cd5, b5, ba5, ta5, g5, l5⟩ | ⟨⟨i, hi, hne⟩, t5, e5, c5, m5, f5, d5, cd5, b5⟩
            · rw [e5]; simp only [beq_self_eq_true, ↓reduceIte]
              have rx5 := mkRx t4 t5 rx4 l5 m5 d5 b5
              rcases stepChunk t5 48 6 rx5 (by omega) (by decide) (by omega) with ⟨h6, t6, e6, c6, m6, f6, d6, cd6, b6, ba6, ta6, g6, l6⟩ | ⟨⟨i, hi, hne⟩, t6, e6, c6, m6, f6, d6, cd6, b6⟩
              · left
                refine ⟨(BorrowedTurn.matchBytes_iff ..).mpr fun idx hidx => ?_, t6, e6, by omega,
                  m6.trans (m5.trans (m4.trans (m3.trans (m2.trans (m1.trans m0))))),
                  f6.trans (f5.trans (f4.trans (f3.trans (f2.trans (f1.trans f0))))),
                  d6.trans (d5.trans (d4.trans (d3.trans (d2.trans (d1.trans d0))))),
                  cd6.trans (cd5.trans (cd4.trans (cd3.trans (cd2.trans (cd1.trans cd0))))),
                  b6.trans (b5.trans (b4.trans (b3.trans (b2.trans (b1.trans b0))))),
                  ba6.trans (ba5.trans (ba4.trans (ba3.trans (ba2.trans (ba1.trans ba0))))),
                  ta6.trans (ta5.trans (ta4.trans (ta3.trans (ta2.trans (ta1.trans ta0))))),
                  g6.trans (g5.trans (g4.trans (g3.trans (g2.trans (g1.trans g0))))),
                  l6.trans (l5.trans (l4.trans (l3.trans (l2.trans (l1.trans l0)))))⟩
                rw [Nat.zero_add]
                if hlt : idx < 8 then simpa using h0 idx hlt
                else if hlt : idx < 16 then simpa [show 8 + (idx - 8) = idx by omega] using h1 (idx - 8) (by omega)
                else if hlt : idx < 24 then simpa [show 16 + (idx - 16) = idx by omega] using h2 (idx - 16) (by omega)
                else if hlt : idx < 32 then simpa [show 24 + (idx - 24) = idx by omega] using h3 (idx - 24) (by omega)
                else if hlt : idx < 40 then simpa [show 32 + (idx - 32) = idx by omega] using h4 (idx - 32) (by omega)
                else if hlt : idx < 48 then simpa [show 40 + (idx - 40) = idx by omega] using h5 (idx - 40) (by omega)
                else simpa [show 48 + (idx - 48) = idx by omega] using h6 (idx - 48) (by omega)
              · exact .inr ⟨mkFail 48 i (by omega) hne, t6, e6, by omega,
                  m6.trans (m5.trans (m4.trans (m3.trans (m2.trans (m1.trans m0))))),
                  f6.trans (f5.trans (f4.trans (f3.trans (f2.trans (f1.trans f0))))),
                  d6.trans (d5.trans (d4.trans (d3.trans (d2.trans (d1.trans d0))))),
                  cd6.trans (cd5.trans (cd4.trans (cd3.trans (cd2.trans (cd1.trans cd0))))),
                  b6.trans (b5.trans (b4.trans (b3.trans (b2.trans (b1.trans b0)))))⟩
            · rw [e5]; exact .inr ⟨mkFail 40 i (by omega) hne, t5, rfl, by omega,
                m5.trans (m4.trans (m3.trans (m2.trans (m1.trans m0)))),
                f5.trans (f4.trans (f3.trans (f2.trans (f1.trans f0)))),
                d5.trans (d4.trans (d3.trans (d2.trans (d1.trans d0)))),
                cd5.trans (cd4.trans (cd3.trans (cd2.trans (cd1.trans cd0)))),
                b5.trans (b4.trans (b3.trans (b2.trans (b1.trans b0))))⟩
          · rw [e4]; exact .inr ⟨mkFail 32 i (by omega) hne, t4, rfl, by omega,
              m4.trans (m3.trans (m2.trans (m1.trans m0))),
              f4.trans (f3.trans (f2.trans (f1.trans f0))),
              d4.trans (d3.trans (d2.trans (d1.trans d0))),
              cd4.trans (cd3.trans (cd2.trans (cd1.trans cd0))),
              b4.trans (b3.trans (b2.trans (b1.trans b0)))⟩
        · rw [e3]; exact .inr ⟨mkFail 24 i (by omega) hne, t3, rfl, by omega,
            m3.trans (m2.trans (m1.trans m0)), f3.trans (f2.trans (f1.trans f0)),
            d3.trans (d2.trans (d1.trans d0)), cd3.trans (cd2.trans (cd1.trans cd0)),
            b3.trans (b2.trans (b1.trans b0))⟩
      · rw [e2]; exact .inr ⟨mkFail 16 i (by omega) hne, t2, rfl, by omega,
          m2.trans (m1.trans m0), f2.trans (f1.trans f0), d2.trans (d1.trans d0),
          cd2.trans (cd1.trans cd0), b2.trans (b1.trans b0)⟩
    · rw [e1]; exact .inr ⟨mkFail 8 i (by omega) hne, t1, rfl, by omega,
        m1.trans m0, f1.trans f0, d1.trans d0, cd1.trans cd0, b1.trans b0⟩
  · rw [e0]; exact .inr ⟨mkFail 0 i (by omega) hne, t0, rfl, by omega, m0, f0, d0, cd0, b0⟩

private theorem scanDigitsLoop_runs {θ : Type} {src : Word} {frame : ByteArray} (hmin : 59 ≤ frame.size)
    (rem : Nat) :
    ∀ (d val : Nat) (s : PanState θ), d + rem = 4 → val < 10 ^ d →
      RxFrame s src frame →
      s.locals "d" = some (.word (word d)) →
      s.locals "val" = some (.word (word val)) →
      rem ≤ s.clock →
      let res := BorrowedTurn.scanDigits frame 54 rem d val
      res.2 < 10 ^ res.1 ∧
      ∃ t, evaluate scanDigitsLoop s = (.normal, t) ∧
        s.clock ≤ t.clock + rem ∧ t.memory = s.memory ∧ t.ffi = s.ffi ∧
        t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be ∧
        t.base_addr = s.base_addr ∧ t.top_addr = s.top_addr ∧ t.globals = s.globals ∧
        t.locals "d" = some (.word (word res.1)) ∧
        t.locals "val" = some (.word (word res.2)) ∧
        (∀ x, x ≠ "d" → x ≠ "val" → t.locals x = s.locals x) := by
  induction rem with
  | zero =>
    intro d val s hdr hval _ hd hv _
    have h4 : d = 4 := by omega
    refine ⟨by simpa [BorrowedTurn.scanDigits] using hval, s, ?_, by omega,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa [BorrowedTurn.scanDigits] using hd,
      by simpa [BorrowedTurn.scanDigits] using hv, fun _ _ _ => rfl⟩
    rw [scanDigitsLoop, evaluate_while]
    simp [hd, h4, eval_n, cmp_small 4 4 (by decide) (by decide)]
  | succ r ih =>
    intro d val s hdr hval rx hd hv hclk
    have hdlt : d < 4 := by omega
    have hfi : 54 + d < frame.size := by omega
    let b := frame[54 + d]!
    have hblt : b.toNat < 256 := b.toNat_lt
    have hval10 : val < 10000 := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by decide : 0 < 10) (show d ≤ 4 by omega))
    have hnz : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    have hdec_rx : RxFrame (dec_clock s) src frame := ⟨rx.pointer, rx.length, rx.fits, rx.bytes⟩
    have hload : eval (dec_clock s) (byte (v "src") (add (n 54) (v "d"))) = some (.word (word b.toNat)) := by
      have hidx : eval (dec_clock s) (add (n 54) (v "d")) = some (.word (word (54 + d))) := by
        simp [add, eval_n, dec_clock, hd, word_op, word, BitVec.ofNat_add]
      exact load_at_expr hdec_rx (add (n 54) (v "d")) (54 + d) hidx hfi
    have hget : frame[54 + d]? = some b := by simp [getElem?_pos, getElem!_pos, hfi, b]
    if hlo : b.toNat < 48 then
      have hnotd : BorrowedTurn.isAsciiDigit b = false := by
        simp [BorrowedTurn.isAsciiDigit]; omega
      have hres : BorrowedTurn.scanDigits frame 54 (r + 1) d val = (d, val) := by
        simp [BorrowedTurn.scanDigits, hget, hnotd]
      rw [hres]
      refine ⟨hval, dec_clock s, ?_, by simp [dec_clock]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [dec_clock, hd], by simp [dec_clock, hv], fun _ _ _ => rfl⟩
      conv => lhs; rw [scanDigitsLoop, evaluate_while]
      simp only [eval_cmp, eval_lvar, eval_n, hd, cmp_small d 4 (by omega) (by decide),
        decide_eq_true hdlt, ite_true, hnz, localVar, evaluate_dec, hload, shape_of_word,
        beq_self_eq_true, seqs, evaluate_seq, evaluate_ite, FUPDATE,
        cmp_small b.toNat 48 (by omega) (by decide), decide_eq_true hlo]
      rw [evaluate_eq_step .break_]; simp only [evaluateStep]
      have hrestore : res_var (FUPDATE s.locals ("ch", .word (word b.toNat))) ("ch", s.locals "ch") = s.locals := by
        funext x; by_cases hx : x = "ch"
        · subst hx; cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB]
        · cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, hx]
      simp [dec_clock, hrestore]
    else if hhi : 57 < b.toNat then
      have hnotd : BorrowedTurn.isAsciiDigit b = false := by
        simp [BorrowedTurn.isAsciiDigit]; omega
      have hres : BorrowedTurn.scanDigits frame 54 (r + 1) d val = (d, val) := by
        simp [BorrowedTurn.scanDigits, hget, hnotd]
      rw [hres]
      refine ⟨hval, dec_clock s, ?_, by simp [dec_clock]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [dec_clock, hd], by simp [dec_clock, hv], fun _ _ _ => rfl⟩
      conv => lhs; rw [scanDigitsLoop, evaluate_while]
      simp only [eval_cmp, eval_lvar, eval_n, hd, cmp_small d 4 (by omega) (by decide),
        decide_eq_true hdlt, hnz, localVar, evaluate_dec, hload, shape_of_word,
        beq_self_eq_true, seqs, evaluate_seq, evaluate_ite, evaluate_skip, FUPDATE,
        cmp_small b.toNat 48 (by omega) (by decide), decide_eq_false hlo,
        cmp_small 57 b.toNat (by decide) (by omega), decide_eq_true hhi,
        show (0#64 != 0#64) = false by decide, show (1#64 != 0#64) = true by decide,
        Bool.false_eq_true, ↓reduceIte]
      rw [evaluate_eq_step .break_]; simp only [evaluateStep]
      have hrestore : res_var (FUPDATE s.locals ("ch", .word (word b.toNat))) ("ch", s.locals "ch") = s.locals := by
        funext x; by_cases hx : x = "ch"
        · subst hx; cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB]
        · cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, hx]
      simp [dec_clock, hrestore]
    else
      have hisd : BorrowedTurn.isAsciiDigit b = true := by
        simp [BorrowedTurn.isAsciiDigit]; omega
      have hnextval : val * 10 + (b.toNat - 48) < 10 ^ (d + 1) := by
        rw [Nat.pow_succ]; omega
      have hres : BorrowedTurn.scanDigits frame 54 (r + 1) d val =
          BorrowedTurn.scanDigits frame 54 r (d + 1) (val * 10 + (b.toNat - 48)) := by
        simp [BorrowedTurn.scanDigits, hget, hisd]
      let uLoc := FUPDATE (FUPDATE s.locals ("val", .word (word (val * 10 + (b.toNat - 48)))))
        ("d", .word (word (d + 1)))
      let u : PanState θ := { dec_clock s with locals := uLoc }
      have hstep : evaluate (localVar "ch" (byte (v "src") (add (n 54) (v "d"))) (seqs [
          .ite (.cmp .Lower (v "ch") (n 48)) .break_ .skip,
          .ite (.cmp .Lower (n 57) (v "ch")) .break_ .skip,
          .lassign "val" (add (mul (v "val") (n 10)) (sub (v "ch") (n 48))),
          inc "d"])) (dec_clock s) = (.normal, u) := by
        have harith : (word val * word 10 + (word b.toNat - word 48)) =
            word (val * 10 + (b.toNat - 48)) := by
          rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
            BitVec.ofNat_add_ofNat]
        have hresLoc : res_var (FUPDATE (FUPDATE (FUPDATE s.locals ("ch", .word (word b.toNat)))
            ("val", .word (word (val * 10 + (b.toNat - 48))))) ("d", .word (word (d + 1))))
            ("ch", s.locals "ch") = uLoc := by
          funext x
          by_cases hxd : x = "d"
          · subst hxd; cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, uLoc]
          · by_cases hxv : x = "val"
            · subst hxv; cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, uLoc]
            · by_cases hxch : x = "ch"
              · subst hxch; cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, uLoc, hch]
              · cases hch : s.locals "ch" <;> simp [res_var, FUPDATE, DOMSUB, uLoc, hxd, hxv, hxch]
        let sd := dec_clock s
        have hstep1 : evaluate (localVar "ch" (byte (v "src") (add (n 54) (v "d"))) (seqs [
            .ite (.cmp .Lower (v "ch") (n 48)) .break_ .skip,
            .ite (.cmp .Lower (n 57) (v "ch")) .break_ .skip,
            .lassign "val" (add (mul (v "val") (n 10)) (sub (v "ch") (n 48))),
            inc "d"])) sd =
          (.normal, { sd with locals := res_var (FUPDATE (FUPDATE (FUPDATE s.locals ("ch", .word (word b.toNat)))
            ("val", .word (word val * word 10 + (word b.toNat - word 48))))
            ("d", .word (word d + word 1))) ("ch", s.locals "ch") }) := by
          rw [localVar, evaluate_dec, show sd = dec_clock s from rfl, hload]
          simp [shape_of_word, seqs, evaluate_seq, evaluate_ite,
            eval_n, FUPDATE,
            cmp_small b.toNat 48 (by omega) (by decide), decide_eq_false hlo,
            cmp_small 57 b.toNat (by decide) (by omega), decide_eq_false hhi,
            evaluate_skip, evaluate_assign, eval, evalList, extractWords,
            hv, hd, word_op, pan_op, List.foldr, BitVec.add_zero, Option.map_some,
            is_valid_value_local, set_kvar, set_var, inc, add, sub, mul, dec_clock]
        rw [hstep1, harith, ← BitVec.ofNat_add, hresLoc]
      have hurx : RxFrame u src frame :=
        ⟨by simp [u, uLoc, FUPDATE, rx.pointer], by simp [u, uLoc, FUPDATE, rx.length], rx.fits, rx.bytes⟩
      have hih := ih (d + 1) (val * 10 + (b.toNat - 48)) u (by omega) hnextval hurx
        (by simp [u, uLoc, FUPDATE]) (by simp [u, uLoc, FUPDATE]) (by simp [u, dec_clock]; omega)
      rw [hres]
      obtain ⟨hbound, t, ht, htclk, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl, htd, htv, htloc⟩ := hih
      refine ⟨hbound, t, ?_, by simp [u, dec_clock] at htclk; omega, hmem, hffi, hdm, hcd, hbe, hba, hta, hgl,
        htd, htv, fun x hxd hxv => (htloc x hxd hxv).trans (by simp [u, uLoc, FUPDATE, hxd, hxv])⟩
      conv => lhs; rw [scanDigitsLoop, evaluate_while]
      simp only [eval_cmp, eval_lvar, eval_n, hd, cmp_small d 4 (by omega) (by decide),
        decide_eq_true hdlt, ite_true, hnz, hstep]
      exact ht

/-- **Exact `PanSem.evaluate` refinement for `parseFrame`**:
on any mapped `RxFrame` with `clock ≥ parseFrameClk`, `parseFrame.body` returns the exact
borrowed body offset (`59..62`, with `f.size - off = v.length ≤ 4096`) when `BorrowedTurn.parse`
accepts, or `0` when it refuses — with zero memory writes and zero FFI events. -/
theorem parseFrame_refines {θ : Type} {s : PanState θ} {src : Word} {f : ByteArray}
    (rx : RxFrame s src f) (l : BorrowedTurn.Lease) (hclk : parseFrameClk ≤ s.clock) :
    ∃ t, evaluate parseFrame.body s =
      (.ret (.word (word (((BorrowedTurn.parse f l).map BorrowedTurn.View.offset).getD 0))), t) ∧
      s.clock ≤ t.clock + parseFrameClk ∧
      t.memory = s.memory ∧ t.ffi = s.ffi ∧
      t.memaddrs = s.memaddrs ∧ t.code = s.code ∧ t.be = s.be := by
  have hlen : eval s (v "len") = some (.word (word f.size)) := rx.length
  have h59 : BorrowedTurn.minFrameSize = 59 := BorrowedTurn.minFrameSize_eq
  have h4158 : BorrowedTurn.maxFrameSize BorrowedTurn.maxPayload = 4158 := BorrowedTurn.maxFrameSize_4096
  have hhs : BorrowedTurn.header.size = 54 := BorrowedTurn.header_size_eq
  have hds : BorrowedTurn.delimiter.size = 4 := BorrowedTurn.delimiter_size_eq
  simp only [parseFrame, parseBody, seqs]
  rw [evaluate_seq]; dsimp only
  rw [failIf_eval s .Lower (v "len") (n 59) _ _ hlen rfl, cmp_small f.size 59 rx.fits (by decide)]
  if hshort : f.size < 59 then
    have hp : BorrowedTurn.parse f l = none := BorrowedTurn.parseWith_rejects_short (by omega)
    refine ⟨empty_locals s, ?_, by simp [empty_locals], rfl, rfl, rfl, rfl, rfl⟩
    simp [hshort, hp]
  else
    simp only [decide_eq_false hshort, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [evaluate_seq]; dsimp only
    rw [failIf_eval s .Lower (n 4158) (v "len") _ _ rfl hlen, cmp_small 4158 f.size (by decide) rx.fits]
    if hlong : 4158 < f.size then
      have hp : BorrowedTurn.parse f l = none := BorrowedTurn.parseWith_rejects_oversize (by omega)
      refine ⟨empty_locals s, ?_, by simp [empty_locals], rfl, rfl, rfl, rfl, rfl⟩
      simp [hlong, hp]
    else
      simp only [decide_eq_false hlong, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      rw [evaluate_seq]; dsimp only
      rcases matchHeader_refines rx (by omega) (by unfold parseFrameClk at hclk; omega) with
        ⟨hhdr, tH, eH, cH, mH, fH, dH, cdH, bH, baH, taH, gH, lH⟩ |
        ⟨hbadHdr, tH, eH, cH, mH, fH, dH, cdH, bH⟩
      · rw [eH]; simp only [beq_self_eq_true, ↓reduceIte]
        have rxH : RxFrame tH src f :=
          ⟨lH ▸ rx.pointer, lH ▸ rx.length, rx.fits, fun i hi => by rw [mH, dH, bH]; exact rx.bytes i hi⟩
        let sD := { tH with locals := FUPDATE tH.locals ("d", .word (word 0)) }
        let sV := { sD with locals := FUPDATE sD.locals ("val", .word (word 0)) }
        have rxV : RxFrame sV src f :=
          ⟨by simp [sV, sD, FUPDATE, rxH.pointer], by simp [sV, sD, FUPDATE, rxH.length], rxH.fits, rxH.bytes⟩
        have hscan := scanDigitsLoop_runs (src := src) (frame := f) (by omega) 4 0 0 sV
          (by decide) (by decide) rxV (by simp [sV, sD, FUPDATE]) (by simp [sV, FUPDATE])
          (by unfold parseFrameClk at hclk; simp [sV, sD]; omega)
        obtain ⟨hvalB, tS, eS, cS, mS, fS, dS, cdS, bS, baS, taS, gS, lSd, lSv, lSother⟩ := hscan
        have htSclk : s.clock ≤ tS.clock + 58 := by
          have cS' : tH.clock ≤ tS.clock + 4 := cS
          omega
        let res := BorrowedTurn.scanDigits f 54 4 0 0
        have hdb := BorrowedTurn.scanDigits_bounds f 54 4 0 0
        have hd4 : res.1 ≤ 4 := by simpa [res] using hdb.2
        have hval10k : res.2 < 10000 :=
          Nat.lt_of_lt_of_le hvalB (Nat.pow_le_pow_right (by decide : 0 < 10) hd4)
        have rxS : RxFrame tS src f :=
          ⟨(lSother "src" (by decide) (by decide)).trans (by simp [sV, sD, FUPDATE, rxH.pointer]),
           (lSother "len" (by decide) (by decide)).trans (by simp [sV, sD, FUPDATE, rxH.length]),
           rxH.fits, fun i hi => by rw [mS, dS, bS]; exact rxH.bytes i hi⟩
        have unwrapDec : ∀ (k : PStmt),
            evaluate (localVar "d" (n 0) (localVar "val" (n 0) k)) tH =
            let r := evaluate k sV
            (r.1, { r.2 with locals := res_var (res_var r.2.locals ("val", sD.locals "val")) ("d", tH.locals "d") }) := by
          intro k
          simp [localVar, evaluate_dec, n, sV, sD]
        rw [unwrapDec]
        dsimp only
        rw [evaluate_seq]; dsimp only
        rw [eS]; simp only [beq_self_eq_true, ↓reduceIte]
        rw [evaluate_seq]; dsimp only
        rw [failIf_eval tS .Equal (v "d") (n 0) (word res.1) (word 0) lSd rfl]
        simp only [word_cmp, eq_small res.1 0 (by omega) (by decide)]
        have hret0NeNorm : (PanResult.ret (.word 0) == .normal) = false := rfl
        if hd0 : res.1 = 0 then
          have hp : BorrowedTurn.parse f l = none := by
            cases hq : BorrowedTurn.parse f l with
            | none => rfl
            | some v =>
              have hiff := (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l v).mp hq
              rw [hhs] at hiff
              dsimp only [BorrowedTurn.maxDigits] at hiff
              have hpos : 1 ≤ res.1 := hiff.2.2.2.1
              omega
          simp only [decide_eq_true hd0, ↓reduceIte, hret0NeNorm, Bool.false_eq_true,
            hp, Option.map_none, Option.getD_none]
          refine ⟨_, rfl, by dsimp only [empty_locals]; unfold parseFrameClk; exact Nat.le_trans htSclk (by omega),
            mS.trans mH, fS.trans fH, dS.trans dH, cdS.trans cdH, bS.trans bH⟩
        else
          simp only [decide_eq_false hd0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
          rw [evaluate_seq]; dsimp only
          have hcmp1 : word_cmp .Lower (word 1) (word res.1) = decide (1 < res.1) :=
            cmp_small 1 res.1 (by decide) (by omega)
          have hiteLead : evaluate (.ite (.cmp .Lower (n 1) (v "d"))
              (failIf .Equal (byte (v "src") (n 54)) (n 48) 0) .skip) tS =
              if decide (1 < res.1) && (f[54]! == 48) then (.ret (.word 0), empty_locals tS) else (.normal, tS) := by
            rw [evaluate_ite]
            simp only [eval_cmp, eval_n, eval_lvar, lSd]
            change (if ((if word_cmp .Lower (word 1) (word res.1) = true then 1#64 else 0#64) != 0#64) = true
              then evaluate (failIf .Equal (byte (v "src") (n 54)) (n 48) 0) tS else evaluate .skip tS) = _
            rw [hcmp1]
            if hgt1 : 1 < res.1 then
              simp only [decide_eq_true hgt1, ↓reduceIte, Bool.true_and,
                show (1#64 != 0#64) = true by decide]
              have h54 := load_at rxS 54 (by omega)
              rw [failIf_eval tS .Equal _ _ _ _ h54 rfl]
              simp only [word_cmp, eq_small f[54]!.toNat 48 (by have := f[54]!.toNat_lt; omega) (by decide)]
              by_cases hz : f[54]! = 48
              · simp [hz]
              · have hne : f[54]!.toNat ≠ 48 := fun e => hz (UInt8.toNat_inj.mp e)
                simp [hz, hne]
            else
              simp only [decide_eq_false hgt1, Bool.false_eq_true, ↓reduceIte,
                show (0#64 != 0#64) = false by decide, Bool.false_and, evaluate_skip]
          rw [hiteLead]
          if hlead : (decide (1 < res.1) && (f[54]! == 48)) = true then
            simp only [hlead, ↓reduceIte, hret0NeNorm, Bool.false_eq_true]
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlead
            have hp : BorrowedTurn.parse f l = none := by
              cases hq : BorrowedTurn.parse f l with
              | none => rfl
              | some v =>
                have hiff := (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l v).mp hq
                rw [hhs] at hiff
                dsimp only [BorrowedTurn.maxDigits] at hiff
                rcases hiff.2.2.2.2.2.2.2.1 with h1 | hne
                · change res.1 = 1 at h1; omega
                · exact absurd hlead.2 hne
            simp only [hp, Option.map_none, Option.getD_none]
            refine ⟨_, rfl, by dsimp only [empty_locals]; unfold parseFrameClk; exact Nat.le_trans htSclk (by omega),
              mS.trans mH, fS.trans fH, dS.trans dH, cdS.trans cdH, bS.trans bH⟩
          else
            have hleadF : (decide (1 < res.1) && (f[54]! == 48)) = false :=
              Bool.eq_false_iff.mpr hlead
            simp only [hleadF, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
            have hleadOk : res.1 = 1 ∨ f[54]! ≠ 48 := by
              by_cases h1 : res.1 = 1
              · exact .inl h1
              · right; intro h48
                have hgt : 1 < res.1 := by omega
                simp [hgt, h48] at hleadF
            rw [evaluate_seq]; dsimp only
            rw [failIf_eval tS .Lower (n 4096) (v "val") (word 4096) (word res.2) rfl lSv]
            have hcmp4096 : word_cmp .Lower (word 4096) (word res.2) = decide (4096 < res.2) :=
              cmp_small 4096 res.2 (by decide) (by omega)
            rw [hcmp4096]
            if hover : 4096 < res.2 then
              have hp : BorrowedTurn.parse f l = none := by
                cases hq : BorrowedTurn.parse f l with
                | none => rfl
                | some v =>
                  have hiff := (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l v).mp hq
                  rw [hhs] at hiff
                  have hle : res.2 ≤ BorrowedTurn.maxPayload := hiff.2.2.2.2.2.1
                  unfold BorrowedTurn.maxPayload at hle; omega
              simp only [decide_eq_true hover, ↓reduceIte, hret0NeNorm, Bool.false_eq_true,
                hp, Option.map_none, Option.getD_none]
              refine ⟨_, rfl, by dsimp only [empty_locals]; unfold parseFrameClk; exact Nat.le_trans htSclk (by omega),
                mS.trans mH, fS.trans fH, dS.trans dH, cdS.trans cdH, bS.trans bH⟩
            else
              simp only [decide_eq_false hover, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
              have hoffEval : eval tS (add (n 58) (v "d")) = some (.word (word (58 + res.1))) := by
                rw [add, eval_binop2, eval_n, eval_lvar, lSd]
                simp [word_op, word, BitVec.add_zero, BitVec.ofNat_add]; rfl
              let sOff := { tS with locals := FUPDATE tS.locals ("off", .word (word (58 + res.1))) }
              have hsumEval : eval sOff (add (v "off") (v "val")) = some (.word (word (58 + res.1 + res.2))) := by
                rw [add, eval_binop2, eval_lvar, eval_lvar]
                simp [sOff, FUPDATE, lSv, word_op, word, BitVec.add_zero, BitVec.ofNat_add]; rfl
              have hlenOff : eval sOff (v "len") = some (.word (word f.size)) := by
                simp [sOff, FUPDATE, rxS.length]
              have rxOff : RxFrame sOff src f :=
                ⟨by simp [sOff, FUPDATE, rxS.pointer], by simp [sOff, FUPDATE, rxS.length], rxS.fits, rxS.bytes⟩
              have hdecOff : evaluate (localVar "off" (add (n 58) (v "d"))
                  (.seq (failIf .NotEqual (v "len") (add (v "off") (v "val")) 0)
                    (.seq (matchPack (add (n 54) (v "d")) (packBytes BorrowedTurn.delimiter 0 4) 4)
                      (.ret (v "off"))))) tS =
                  let r := evaluate (.seq (failIf .NotEqual (v "len") (add (v "off") (v "val")) 0)
                    (.seq (matchPack (add (n 54) (v "d")) (packBytes BorrowedTurn.delimiter 0 4) 4)
                      (.ret (v "off")))) sOff
                  (r.1, { r.2 with locals := res_var r.2.locals ("off", tS.locals "off") }) := by
                simp only [localVar, evaluate_dec, hoffEval, shape_of_word, beq_self_eq_true, ↓reduceIte, sOff]
              rw [hdecOff]; dsimp only
              rw [evaluate_seq]; dsimp only
              rw [failIf_eval sOff .NotEqual (v "len") (add (v "off") (v "val")) _ _ hlenOff hsumEval]
              have hcmpSz : word_cmp .NotEqual (word f.size) (word (58 + res.1 + res.2)) =
                  !decide (f.size = 58 + res.1 + res.2) := by
                simp only [word_cmp, bne, eq_small f.size (58 + res.1 + res.2) rx.fits (by omega)]
              rw [hcmpSz]
              if hszEq : f.size = 58 + res.1 + res.2 then
                simp only [decide_eq_true hszEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
                rw [evaluate_seq]; dsimp only
                have hdelOff : ∀ s' : PanState θ, s'.locals "d" = sOff.locals "d" →
                    eval s' (add (n 54) (v "d")) = some (.word (word (54 + res.1))) := by
                  intro s' hd'
                  rw [add, eval_binop2, eval_n, eval_lvar, hd']
                  simp [sOff, FUPDATE, lSd, word_op, word, BitVec.add_zero, BitVec.ofNat_add]; rfl
                have hdelClk : 4 ≤ sOff.clock := by
                  change 4 ≤ tS.clock; unfold parseFrameClk at hclk; omega
                have hdelFit : 54 + res.1 + 4 ≤ f.size := by omega
                rcases matchPack_branch rxOff (add (n 54) (v "d")) (54 + res.1) 0 4 (by decide)
                    hdelFit (by rw [hds]; omega) hdelClk hdelOff with
                  ⟨hdelOk, tD, eD, cD, mD, fD, dD, cdD, bD, baD, taD, gD, lD⟩ |
                  ⟨⟨j, hj, hjne⟩, tD, eD, cD, mD, fD, dD, cdD, bD⟩
                · rw [eD]
                  have hp : BorrowedTurn.parse f l = some ⟨l, 58 + res.1, res.2⟩ := by
                    apply (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l _).mpr
                    rw [h59, h4158, hhs, hds]
                    change 59 ≤ f.size ∧ f.size ≤ 4158 ∧
                      (∀ i < 54, f[i]? = BorrowedTurn.header[i]?) ∧
                      1 ≤ res.1 ∧ res.1 ≤ BorrowedTurn.maxDigits ∧ res.2 ≤ BorrowedTurn.maxPayload ∧
                      f.size = 54 + res.1 + 4 + res.2 ∧ (res.1 = 1 ∨ f[54]! ≠ 48) ∧
                      (∀ i < 4, f[54 + res.1 + i]? = BorrowedTurn.delimiter[i]?) ∧
                      (⟨l, 58 + res.1, res.2⟩ : BorrowedTurn.View) = ⟨l, 54 + res.1 + 4, res.2⟩
                    refine ⟨by omega, by omega, ?_, by omega,
                      by unfold BorrowedTurn.maxDigits; exact hd4,
                      by unfold BorrowedTurn.maxPayload; omega,
                      by omega, hleadOk, fun i hi => by simpa using hdelOk i hi,
                      by congr 1; omega⟩
                    intro i hi
                    have hm := (BorrowedTurn.matchBytes_iff ..).mp hhdr i (by rw [hhs]; exact hi)
                    simpa using hm
                  have hoffD : tD.locals "off" = some (.word (word (58 + res.1))) := by
                    rw [lD]; simp [sOff, FUPDATE]
                  simp only [beq_self_eq_true, ↓reduceIte, evaluate_ret, eval_lvar, hoffD, shape_of_word,
                    size_of_shape_one, show decide (1 ≤ 32) = true by decide, hp, Option.map_some,
                    Option.getD_some]
                  refine ⟨_, rfl, by dsimp only [empty_locals]; unfold parseFrameClk; change tD.clock + 4 = tS.clock at cD; omega,
                    mD.trans (mS.trans mH), fD.trans (fS.trans fH), dD.trans (dS.trans dH),
                    cdD.trans (cdS.trans cdH), bD.trans (bS.trans bH)⟩
                · rw [eD]
                  have hp : BorrowedTurn.parse f l = none := by
                    cases hq : BorrowedTurn.parse f l with
                    | none => rfl
                    | some v =>
                      have hiff := (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l v).mp hq
                      rw [hhs, hds] at hiff
                      have hdl : f[54 + res.1 + j]? = BorrowedTurn.delimiter[j]? := hiff.2.2.2.2.2.2.2.2.1 j hj
                      rw [Nat.zero_add] at hjne
                      exact absurd hdl hjne
                  simp only [hret0NeNorm, Bool.false_eq_true, ↓reduceIte, hp, Option.map_none, Option.getD_none]
                  refine ⟨_, rfl, by dsimp only [empty_locals]; unfold parseFrameClk; change tS.clock ≤ tD.clock + 4 at cD; omega,
                    mD.trans (mS.trans mH), fD.trans (fS.trans fH), dD.trans (dS.trans dH),
                    cdD.trans (cdS.trans cdH), bD.trans (bS.trans bH)⟩
              else
                have hp : BorrowedTurn.parse f l = none := by
                  cases hq : BorrowedTurn.parse f l with
                  | none => rfl
                  | some v =>
                    have hiff := (BorrowedTurn.parseWith_eq_some_iff BorrowedTurn.maxPayload f l v).mp hq
                    rw [hhs, hds] at hiff
                    have hsz := hiff.2.2.2.2.2.2.1
                    change f.size = 54 + res.1 + 4 + res.2 at hsz
                    omega
                simp only [decide_eq_false hszEq, Bool.not_false, ↓reduceIte, hret0NeNorm, Bool.false_eq_true,
                  hp, Option.map_none, Option.getD_none]
                refine ⟨_, rfl, by
                    dsimp only [empty_locals, sOff]; unfold parseFrameClk
                    exact Nat.le_trans htSclk (by omega),
                  mS.trans mH, fS.trans fH, dS.trans dH, cdS.trans cdH, bS.trans bH⟩
      · rw [eH]
        have hp : BorrowedTurn.parse f l = none := by
          simp [BorrowedTurn.parse, BorrowedTurn.parseWith, hbadHdr]
        refine ⟨tH, by simp [hp, word], by unfold parseFrameClk; omega, mH, fH, dH, cdH, bH⟩

/-- **Tight clocked refinement (`RefinesClkTight`) for `parseFrame`**:
valid frames return exact borrowed slice offset `v.offset` (with `frame.size - v.offset = v.length ≤ 4096`),
invalid frames return `0`, memory and FFI are strictly unchanged, and `clock` consumption is `≤ parseFrameClk`. -/
theorem parseFrame_refinesClkTight {θ : Type} (src : Word) (f : ByteArray) (l : BorrowedTurn.Lease) :
    RefinesClkTight (θ := θ) (fun s => RxFrame s src f) parseFrame.body parseFrameClk
      (fun s r t =>
        r = .ret (.word (word (((BorrowedTurn.parse f l).map BorrowedTurn.View.offset).getD 0))) ∧
        (∀ v, BorrowedTurn.parse f l = some v → f.size - v.offset = v.length ∧ v.length ≤ BorrowedTurn.maxPayload) ∧
        t.memory = s.memory ∧ t.ffi = s.ffi) := by
  intro s hE hclk
  obtain ⟨t, ev, htclk, hmem, hffi, _⟩ := parseFrame_refines hE.2 l hclk
  have wf := evaluate_preserves_stateWF parseFrame.body s hE.1
  rw [ev] at wf
  refine ⟨_, t, ev, PanResult.noConfusion, PanResult.noConfusion, htclk, wf, rfl, fun v hv => ?_, hmem, hffi⟩
  have hs := BorrowedTurn.parse_sound hv
  exact ⟨by omega, hs.2.2.2.1⟩

/-- Constructive inhabitedness witness for `parseFrame`'s entry contract. -/
theorem parseFrame_entry_inhabited (f : ByteArray) (hf : f.size < 2 ^ 64) :
    ∃ s : PanState Unit, EntryWF (fun st => RxFrame st 0#64 f) s ∧ s.clock ≥ parseFrameClk := by
  let writeAll : Nat → ByteMemory.Memory → ByteMemory.Memory :=
    Nat.rec (fun m => m) (fun k ih m => ByteMemory.put (ih m) (word k) f[k]!)
  have hread : ∀ n (hn : n ≤ f.size) (i : Nat), i < n →
      ByteMemory.read (writeAll n (fun _ => 0#64)) (word i) = f[i]!.toBitVec := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ k ih =>
      intro hk i hi
      change ByteMemory.read (ByteMemory.put (writeAll k (fun _ => 0#64)) (word k) f[k]!) (word i) = _
      rw [ByteMemory.read_put]
      if hik : k = i then
        subst hik; simp
      else
        have hne : word k ≠ word i := by
          intro e
          have := congrArg BitVec.toNat e
          simp [word, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)] at this
          exact hik this
        simp [hne, ih (by omega) i (by omega)]
  let s : PanState Unit :=
    { emptyPanState () parseFrameClk with
      locals := FUPDATE (FUPDATE FEMPTY ("src", .word 0#64)) ("len", .word (word f.size))
      memaddrs := fun _ => true
      memory := writeAll f.size (fun _ => 0#64) }
  refine ⟨s, ⟨emptyPanState_wf () parseFrameClk,
    ⟨by simp [s, FUPDATE], by simp [s, FUPDATE], hf, fun i hi => ?_⟩⟩, Nat.le_refl _⟩
  simpa [s, emptyPanState, mem_load_byte, ByteMemory.read, BitVec.zero_add] using
    congrArg some (hread f.size (Nat.le_refl _) i hi)

/-! ## 2. `turnIntake` (64-bit Parameterized `maxTurns`, `budgetCap`, `0..4096`B Payloads) -/

/-- Memory layout constants (all 8-byte aligned):
- `state + 0`: `count`, `+8`: `channelPrincipal`, `+16`: `maxTurns`, `+24`: `budgetCap`, `+32`: `lastCheckpointNullifier`.
- Entry `i` at `state + 40 + i * 4136`: `+0`: `payloadLen`, `+8`: `principal`, `+16`: `nonce`, `+24`: `nullifier`, `+32`: `cost`, `+40..`: payload (`0..4096`B).
- `scratch + 0`: `status`, `+8`: `generation`, `+16`: `req.principal`, `+24`: `req.nonce`, `+32`: `req.nullifier`, `+40`: `req.cost`, `+48`: `req.payloadLen`, `+56`: `baseGen`, `+64..`: copied body (`0..4096`B). -/
def stateHeaderBytes : Nat := 40
def entryHeaderBytes : Nat := 40
def entryStride : Nat := 4136
def scratchCtrlBytes : Nat := 64

private def bodyPtr : PExp := add (v "scratch") (n scratchCtrlBytes)
private def reqPrincipal : PExp := wordAt (v "scratch") 16
private def reqNonce : PExp := wordAt (v "scratch") 24
private def reqNullifier : PExp := wordAt (v "scratch") 32
private def reqCost : PExp := wordAt (v "scratch") 40
private def baseGen : PExp := wordAt (v "scratch") 56

private def io (name : String) : PStmt :=
  PStmt.extCall name bodyPtr (v "width") (v "scratch") (n scratchCtrlBytes)

private def command (name : String) : PStmt := seqs [
  storeWord (v "scratch") 0 (n 255),
  io name,
  failIf .NotEqual (wordAt (v "scratch") 0) (n 0) 0]

private def reply (generation : PExp) : PStmt :=
  PStmt.seq (PStmt.seq (storeWord (v "scratch") 8 generation) (command "reply")) (.ret generation)

private def checkRecord : PStmt :=
  localVar "entry" (add (v "state") (add (n stateHeaderBytes) (mul (v "i") (n entryStride)))) <| seqs [
    .ite (.cmp .Lower (v "lastId") (wordAt (v "entry") 24))
      (.lassign "lastId" (wordAt (v "entry") 24)) .skip,
    .ite (.cmp .Equal reqPrincipal (wordAt (v "entry") 8)) (seqs [
      .lassign "spent" (add (v "spent") (wordAt (v "entry") 32)),
      .ite (.cmp .Equal reqNonce (wordAt (v "entry") 16)) (seqs [
        failIf .NotEqual reqNullifier (wordAt (v "entry") 24) 0,
        failIf .NotEqual reqCost (wordAt (v "entry") 32) 0,
        failIf .NotEqual (v "width") (wordAt (v "entry") 0) 0,
        localVar "j" (n 0) (.while_ (.cmp .Lower (v "j") (v "width")) (seqs [
          failIf .NotEqual (byte bodyPtr (v "j"))
            (byte (v "entry") (add (n entryHeaderBytes) (v "j"))) 0,
          inc "j"])),
        reply (add baseGen (add (v "i") (n 1)))]) .skip]) .skip,
    inc "i"]

private def commands : List String → PStmt
  | [] => .skip
  | name :: names => .seq (command name) (commands names)

private def publish (generation : PExp) : PStmt :=
  PStmt.seq (storeWord (v "scratch") 8 generation)
    (.seq (commands ["authorize", "wal", "flush", "fua", "dispatch"])
      (.seq (storeWord (v "scratch") 8 generation) (command "reply")))

def freshCommit (generation : PExp) : PStmt := .seq (publish generation) (.ret generation)

def admit : PStmt :=
  localVar "count" (wordAt (v "state") 0) <|
  localVar "maxTurns" (wordAt (v "state") 16) <|
  localVar "budgetCap" (wordAt (v "state") 24) <|
  localVar "lastId" (wordAt (v "state") 32) <|
  localVar "spent" (n 0) <|
  localVar "i" (n 0) <| seqs [
    failIf .Lower (v "maxTurns") (v "count") 0,
    failIf .NotEqual reqPrincipal (wordAt (v "state") 8) 0,
    .while_ (.cmp .Lower (v "i") (v "count")) checkRecord,
    failIf .NotLower (v "count") (v "maxTurns") 0,
    failIf .NotLower (v "lastId") reqNullifier 0,
    failIf .Equal reqCost (n 0) 0,
    failIf .Lower (add (v "spent") reqCost) (v "spent") 0,
    failIf .Lower (v "budgetCap") (add (v "spent") reqCost) 0,
    freshCommit (add baseGen (add (v "count") (n 1)))]

def intake : PFun := {
  name := "turnIntake", params := ["src", "len", "state", "scratch"].map (·, .One), exported := true
  body := .decCall "off" .One "parseFrame" [v "src", v "len"] <| seqs [
    failIf .Equal (v "off") (n 0) 0,
    localVar "width" (sub (v "len") (v "off")) <|
    .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <| seqs [
      failIf .NotEqual (v "copied") (v "width") 0,
      storeWord (v "scratch") 48 (v "width"),
      admit]] }

def source : Option String := emitPnkProg [DragonStyleShard.echo, parseFrame, intake]

/-! ## 3. Real `PanSem.evaluate` & `RefinesClkTight` Theorems on `turnIntake` -/

/-- Installed code table binding `parseFrame` and `dn_echo` to their certified ASTs. -/
def CodeLoaded {θ : Type} (s : PanState θ) : Prop :=
  s.code "parseFrame" = some (parseFrame.params, parseFrame.body) ∧
  s.code "dn_echo" = some (DragonStyleShard.echo.params, DragonStyleShard.echo.body)

private theorem io_trace (name : String) (named : name ≠ "") : CommandTrace (io name) [name] :=
  extCall_trace name named _ _ _ _

private theorem command_trace (name : String) (named : name ≠ "") :
    CommandTrace (command name) [name] :=
  seq_trace (store_trace _ _) (seq_trace (io_trace name named) (status_trace _))

private theorem commands_trace (names : List String) (named : "" ∉ names) :
    CommandTrace (commands names) names := by
  induction names with
  | nil => exact skip_trace
  | cons x xs ih =>
    exact seq_trace (command_trace x (by intro e; subst x; simp at named))
      (ih (fun h => named (List.mem_cons_of_mem _ h)))

/-- A positive return from `freshCommit` executes the exact FFI sequence
`authorize → wal → flush → fua → dispatch → reply`. -/
theorem fresh_commit_order {θ : Type} (s f : PanState θ) (g : PExp) (w : Word) (positive : w ≠ 0)
    (run : evaluate (freshCommit g) s = (.ret (.word w), f)) :
    events f = events s ++ ["authorize", "wal", "flush", "fua", "dispatch", "reply"] := by
  have contract : CommandTrace (publish g) ["authorize", "wal", "flush", "fua", "dispatch", "reply"] :=
    seq_trace (store_trace _ _) (seq_trace (commands_trace _ (by decide))
      (seq_trace (store_trace _ _) (command_trace "reply" (by decide))))
  exact positive_return_trace s f _ _ _ w positive contract run

/-- Valid FFI outcomes of any positive return from `turnIntake`:
either a verified replay (`["reply"]`) or a full durable commit sequence. -/
abbrev AllowedIntakeTrace (before after : List String) : Prop :=
  after = before ++ ["reply"] ∨
  after = before ++ ["authorize", "wal", "flush", "fua", "dispatch", "reply"]

private theorem reply_positiveTrace (g : PExp) : PositiveTrace (reply g) AllowedIntakeTrace := by
  intro θ s
  unfold reply
  have hc : CommandTrace (.seq (storeWord (v "scratch") 8 g) (command "reply")) ["reply"] :=
    seq_trace (store_trace _ _) (command_trace "reply" (by decide))
  exact positiveTrace_seq_ret (g := g) (P := AllowedIntakeTrace) hc (fun _ => Or.inl rfl) s

private theorem freshCommit_positiveTrace (g : PExp) : PositiveTrace (freshCommit g) AllowedIntakeTrace := by
  intro θ s
  unfold freshCommit
  have hc : CommandTrace (publish g) ["authorize", "wal", "flush", "fua", "dispatch", "reply"] :=
    seq_trace (store_trace _ _) (seq_trace (commands_trace _ (by decide))
      (seq_trace (store_trace _ _) (command_trace "reply" (by decide))))
  exact positiveTrace_seq_ret (g := g) (P := AllowedIntakeTrace) hc (fun _ => Or.inr rfl) s

private theorem checkRecord_positiveTrace : PositiveTrace checkRecord AllowedIntakeTrace := by
  unfold checkRecord seqs failIf localVar inc
  exact positiveTrace_dec <|
    positiveTrace_seq (positiveTrace_ite (positiveTrace_assign AllowedIntakeTrace _ _ _) (positiveTrace_skip _)) <|
    positiveTrace_seq
      (positiveTrace_ite
        (positiveTrace_seq (positiveTrace_assign AllowedIntakeTrace _ _ _)
          (positiveTrace_ite
            (positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
             positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
             positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
             positiveTrace_seq
               (positiveTrace_dec <| positiveTrace_while <|
                 positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) (positiveTrace_assign AllowedIntakeTrace _ _ _))
               (reply_positiveTrace _))
            (positiveTrace_skip _)))
        (positiveTrace_skip _))
      (positiveTrace_assign AllowedIntakeTrace _ _ _)

private theorem admit_positiveTrace : PositiveTrace admit AllowedIntakeTrace := by
  unfold admit seqs failIf localVar
  exact positiveTrace_dec <| positiveTrace_dec <| positiveTrace_dec <|
    positiveTrace_dec <| positiveTrace_dec <| positiveTrace_dec <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_while checkRecord_positiveTrace) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
    freshCommit_positiveTrace _

private theorem parseFrame_noFfi : NoFfiStmt parseFrame.body = true := rfl
private theorem echo_noFfi : NoFfiStmt DragonStyleShard.echo.body = true := rfl

/-- **Whole-function FFI trace soundness for `turnIntake`**:
for ANY initial state with `parseFrame` and `dn_echo` loaded, ANY positive return `w ≠ 0`
from `evaluate intake.body s` emits EITHER `["reply"]` (verified replay) OR
`["authorize", "wal", "flush", "fua", "dispatch", "reply"]` (fresh durable commit). -/
theorem turnIntake_positive_trace {θ : Type} (s f : PanState θ) (w : Word) (hcode : CodeLoaded s)
    (positive : w ≠ 0) (run : evaluate intake.body s = (.ret (.word w), f)) :
    AllowedIntakeTrace (events s) (events f) := by
  unfold intake at run
  rw [evaluate_decCall] at run
  rw [hcode.1] at run
  cases hargs1 : evalList s [v "src", v "len"] with
  | none => rw [hargs1] at run; cases run
  | some argVals1 =>
    rw [hargs1] at run; dsimp only at run
    split at run
    · split at run
      · cases run
      · let cSt1 := { dec_clock s with locals := mkCalleeLocals parseFrame.params argVals1 }
        have hEv1 : events (evaluate parseFrame.body cSt1).2 = events s :=
          noFfi_preserves_events parseFrame_noFfi cSt1
        cases hr1 : (evaluate parseFrame.body cSt1).1 with
        | ret rv1 =>
          rw [hr1] at run; dsimp only at run
          split at run
          · let s1 := { (evaluate parseFrame.body cSt1).2 with locals := FUPDATE s.locals ("off", rv1) }
            have hEvS1 : events s1 = events s := hEv1
            have hCodeS1 : s1.code = s.code := by
              simpa [s1, cSt1, dec_clock] using (evaluate_clock_and_config parseFrame.body cSt1).2.2.1
            injection run with hres1 hf1
            have hsub : (evaluate (seqs [failIf .Equal (v "off") (n 0) 0,
                localVar "width" (sub (v "len") (v "off")) <|
                .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <| seqs [
                  failIf .NotEqual (v "copied") (v "width") 0,
                  storeWord (v "scratch") 48 (v "width"),
                  admit]]) s1).1 = .ret (.word w) := hres1
            have hEvEq : events f = events (evaluate (seqs [failIf .Equal (v "off") (n 0) 0,
                localVar "width" (sub (v "len") (v "off")) <|
                .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <| seqs [
                  failIf .NotEqual (v "copied") (v "width") 0,
                  storeWord (v "scratch") 48 (v "width"),
                  admit]]) s1).2 := by rw [← hf1]; rfl
            rw [hEvEq, ← hEvS1]
            simp only [seqs] at hsub ⊢
            rw [evaluate_seq] at hsub ⊢; dsimp only at hsub ⊢
            split at hsub
            · rename_i hnorm1
              simp only [hnorm1, ↓reduceIte]
              have hF1 : (evaluate (failIf .Equal (v "off") (n 0) 0) s1).1 = .normal := eq_of_beq hnorm1
              have hEvF1 : events (evaluate (failIf .Equal (v "off") (n 0) 0) s1).2 = events s1 :=
                (positiveTrace_failZero AllowedIntakeTrace _ s1).1 (.inl hF1)
              have hCodeF1 : (evaluate (failIf .Equal (v "off") (n 0) 0) s1).2.code = s.code :=
                ((evaluate_clock_and_config _ s1).2.2.1).trans hCodeS1
              let s2 := (evaluate (failIf .Equal (v "off") (n 0) 0) s1).2
              rw [← hEvF1]
              change AllowedIntakeTrace (events s2) (events (evaluate _ s2).2)
              change (evaluate _ s2).1 = .ret (.word w) at hsub
              rw [localVar, evaluate_dec] at hsub ⊢
              cases hwv : eval s2 (sub (v "len") (v "off")) with
              | none => rw [hwv] at hsub; cases hsub
              | some wval =>
                rw [hwv] at hsub; dsimp only at hsub ⊢
                split at hsub
                · rename_i hshw
                  simp only [hshw, ↓reduceIte]
                  let s3 := { s2 with locals := FUPDATE s2.locals ("width", wval) }
                  change AllowedIntakeTrace (events s3) (events (evaluate _ s3).2)
                  rw [evaluate_decCall] at hsub ⊢
                  rw [show s3.code "dn_echo" = some (DragonStyleShard.echo.params, DragonStyleShard.echo.body)
                    from hCodeF1.symm ▸ hcode.2] at hsub ⊢
                  cases hargs2 : evalList s3 [add (v "src") (v "off"), bodyPtr, v "width", n 4096] with
                  | none => rw [hargs2] at hsub; cases hsub
                  | some argVals2 =>
                    rw [hargs2] at hsub; dsimp only at hsub ⊢
                    split at hsub
                    · rename_i hsm2
                      simp only [hsm2, ↓reduceIte]
                      split at hsub
                      · cases hsub
                      · rename_i hclk2
                        have hclk2' : (s3.clock == 0) = false := Bool.eq_false_iff.mpr hclk2
                        simp only [hclk2', Bool.false_eq_true, ↓reduceIte]
                        let cSt2 := { dec_clock s3 with locals := mkCalleeLocals DragonStyleShard.echo.params argVals2 }
                        have hEv2 : events (evaluate DragonStyleShard.echo.body cSt2).2 = events s3 :=
                          noFfi_preserves_events echo_noFfi cSt2
                        cases hr2 : (evaluate DragonStyleShard.echo.body cSt2).1 with
                        | ret rv2 =>
                          rw [hr2] at hsub; dsimp only at hsub ⊢
                          split at hsub
                          · rename_i hshr2
                            simp only [hshr2, ↓reduceIte]
                            let s4 := { (evaluate DragonStyleShard.echo.body cSt2).2 with
                              locals := FUPDATE s3.locals ("copied", rv2) }
                            rw [← hEv2]
                            have hpt : PositiveTrace (seqs [failIf .NotEqual (v "copied") (v "width") 0,
                                storeWord (v "scratch") 48 (v "width"), admit]) AllowedIntakeTrace := by
                              unfold seqs failIf storeWord
                              exact positiveTrace_seq (positiveTrace_failZero AllowedIntakeTrace _) <|
                                positiveTrace_seq (positiveTrace_store AllowedIntakeTrace _ _) admit_positiveTrace
                            exact (hpt s4).2 w positive hsub
                          · cases hsub
                        | normal | break_ | continue_ | TimeOut | Error | finalFFI _ =>
                          rw [hr2] at hsub; cases hsub
                    · cases hsub
                · cases hsub
            · exfalso
              exact positive ((status_trace _ s1).2.2.2 w hsub)
          · cases run
        | normal | break_ | continue_ | TimeOut | Error | finalFFI _ =>
          rw [hr1] at run; cases run
    · cases run

/-- **Refusal refinement (`RefinesClkTight`) for `turnIntake` on malformed/truncated frames**:
when `BorrowedTurn.parse f l = none`, `turnIntake` refuses with `0` immediately after `parseFrame`,
performing ZERO copies (`dn_echo` never runs), ZERO memory writes, and ZERO FFI calls! -/
theorem turnIntake_refinesClkTight_invalid {θ : Type} (src : Word) (f : ByteArray) (l : BorrowedTurn.Lease)
    (hbad : BorrowedTurn.parse f l = none) :
    RefinesClkTight (θ := θ) (fun s => RxFrame s src f ∧ CodeLoaded s) intake.body (parseFrameClk + 1)
      (fun s r t => r = .ret (.word 0) ∧ t.memory = s.memory ∧ events t = events s) := by
  intro s hE hclk
  obtain ⟨rx, hcode⟩ := hE.2
  have hnz : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  let cSt := { dec_clock s with
    locals := mkCalleeLocals parseFrame.params [.word src, .word (word f.size)] }
  have hcrx : RxFrame cSt src f :=
    ⟨by simp [cSt, mkCalleeLocals, parseFrame, FUPDATE_LIST, FUPDATE],
     by simp [cSt, mkCalleeLocals, parseFrame, FUPDATE_LIST, FUPDATE],
     rx.fits, rx.bytes⟩
  obtain ⟨t1, e1, c1, m1, f1, _⟩ := parseFrame_refines hcrx l (by simp [cSt, dec_clock]; omega)
  simp only [hbad, Option.map_none, Option.getD_none] at e1
  let s1 := { t1 with locals := FUPDATE s.locals ("off", .word (word 0)) }
  have hfail : evaluate (failIf .Equal (v "off") (n 0) 0) s1 = (.ret (.word 0), empty_locals s1) := by
    rw [failIf_eval s1 .Equal (v "off") (n 0) (word 0) (word 0) (by simp [s1, FUPDATE]) rfl]
    simp [word_cmp]
  have hpar : parseFrame.params = [("src", .One), ("len", .One)] := rfl
  have hev : evaluate intake.body s =
      (.ret (.word 0), { empty_locals s1 with locals := res_var (empty_locals s1).locals ("off", s.locals "off") }) := by
    unfold intake
    rw [evaluate_decCall]
    simp only [evalList_cons, evalList_nil, eval_lvar, rx.pointer, rx.length, hcode.1,
      hpar, shapesMatch, shape_of_word, beq_self_eq_true, Bool.and_self,
      hnz, Bool.false_eq_true, ↓reduceIte]
    have e1' : evaluate parseFrame.body
        { locals := mkCalleeLocals [("src", Shape.One), ("len", Shape.One)] [.word src, .word (word f.size)],
          globals := (dec_clock s).globals, code := (dec_clock s).code, memory := (dec_clock s).memory,
          memaddrs := (dec_clock s).memaddrs, clock := (dec_clock s).clock, be := (dec_clock s).be,
          ffi := (dec_clock s).ffi, base_addr := (dec_clock s).base_addr, top_addr := (dec_clock s).top_addr } =
        (.ret (.word (word 0)), t1) := e1
    rw [e1']
    simp only [shape_of_word, beq_self_eq_true, ↓reduceIte, seqs]
    have hcont : evaluate (.seq (failIf .Equal (v "off") (n 0) 0)
        (localVar "width" (sub (v "len") (v "off")) <|
        .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <|
          .seq (failIf .NotEqual (v "copied") (v "width") 0)
            (.seq (storeWord (v "scratch") 48 (v "width")) admit)))
        { locals := FUPDATE s.locals ("off", .word (word 0)),
          globals := t1.globals, code := t1.code, memory := t1.memory, memaddrs := t1.memaddrs,
          clock := t1.clock, be := t1.be, ffi := t1.ffi, base_addr := t1.base_addr, top_addr := t1.top_addr } =
        (.ret (.word 0), empty_locals s1) := by
      rw [evaluate_seq, show evaluate (failIf .Equal (v "off") (n 0) 0) _ = (.ret (.word 0), empty_locals s1) from hfail]; rfl
    rw [hcont]
  have wf := evaluate_preserves_stateWF intake.body s hE.1
  rw [hev] at wf
  refine ⟨.ret (.word 0), _, hev, PanResult.noConfusion, PanResult.noConfusion, ?_, wf, rfl, m1, ?_⟩
  · simp only [s1, empty_locals]
    simp only [cSt, dec_clock] at c1
    omega
  · unfold events
    simpa only [empty_locals, s1, cSt, dec_clock] using congrArg (fun x => x.io_events.map IOEvent.name) f1

/-- Entry condition for `turnIntake` on a valid frame with mapped scratch buffer and code loaded. -/
structure ValidIntakeEntry {θ : Type} (src scratch : Word) (f : ByteArray) (l : BorrowedTurn.Lease)
    (v : BorrowedTurn.View) (s : PanState θ) : Prop where
  rx : RxFrame s src f
  code : CodeLoaded s
  parsed : BorrowedTurn.parse f l = some v
  scratchPtr : s.locals "scratch" = some (.word scratch)
  little : s.be = false
  srcMapped : ∀ i, i < v.length → s.memaddrs (byte_align (src + word v.offset + word i)) = true
  scratchMapped : ∀ i, i < v.length → s.memaddrs (byte_align (scratch + word scratchCtrlBytes + word i)) = true
  scratchLenWord : s.memaddrs (scratch + word 48) = true

/-- **Valid-frame `PanSem.evaluate` decomposition for `turnIntake`**:
when `BorrowedTurn.parse f l = some v`, `turnIntake` calls `parseFrame` (returning exact offset `v.offset`),
computes `width = f.size - v.offset = v.length ≤ 4096`, calls `dn_echo` to copy the exact `v.length`
borrowed payload bytes into verifier-private `scratch + 64`, writes `v.length` to `scratch + 48`,
and hands the exact copied memory to `admit` with zero prior FFI events! -/
theorem turnIntake_valid_frame_copies_borrowed_body {θ : Type} {s : PanState θ}
    {src scratch : Word} {f : ByteArray} {l : BorrowedTurn.Lease} {vw : BorrowedTurn.View}
    (h : ValidIntakeEntry src scratch f l vw s)
    (hclk : parseFrameClk + vw.length + 2 ≤ s.clock) :
    ∃ tCopy : PanState θ,
      tCopy.memory = UPDATE (scratch + word 48) (word vw.length)
        (DragonStyleShard.copyMem (src + word vw.offset) (scratch + word scratchCtrlBytes) 0 vw.length s.memory) ∧
      tCopy.clock + (parseFrameClk + vw.length + 2) ≥ s.clock ∧
      events tCopy = events s ∧
      tCopy.locals = FUPDATE (FUPDATE (FUPDATE s.locals ("off", .word (word vw.offset)))
        ("width", .word (word vw.length))) ("copied", .word (word vw.length)) ∧
      (evaluate intake.body s).1 = (evaluate admit tCopy).1 ∧
      (evaluate intake.body s).2.memory = (evaluate admit tCopy).2.memory ∧
      events (evaluate intake.body s).2 = events (evaluate admit tCopy).2 := by
  have hps := BorrowedTurn.parse_sound h.parsed
  have hOffPos : vw.offset ≠ 0 := by omega
  have hWidth : f.size - vw.offset = vw.length := by omega
  have hLenLe : vw.length ≤ 4096 := hps.2.2.2.1
  have hnz1 : (s.clock == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  let cSt1 := { dec_clock s with
    locals := mkCalleeLocals parseFrame.params [.word src, .word (word f.size)] }
  have hcrx1 : RxFrame cSt1 src f :=
    ⟨by simp [cSt1, mkCalleeLocals, parseFrame, FUPDATE_LIST, FUPDATE],
     by simp [cSt1, mkCalleeLocals, parseFrame, FUPDATE_LIST, FUPDATE],
     h.rx.fits, h.rx.bytes⟩
  obtain ⟨t1, e1, c1, m1, f1, dm1, cd1, be1⟩ :=
    parseFrame_refines hcrx1 l (by simp [cSt1, dec_clock]; omega)
  simp only [h.parsed, Option.map_some, Option.getD_some] at e1
  let s1 := { t1 with locals := FUPDATE s.locals ("off", .word (word vw.offset)) }
  have hfail1 : evaluate (failIf .Equal (v "off") (n 0) 0) s1 = (.normal, s1) := by
    rw [failIf_eval s1 .Equal (v "off") (n 0) (word vw.offset) (word 0) (by simp [s1, FUPDATE]) rfl]
    simp [word_cmp, eq_small vw.offset 0 (by omega) (by decide), hOffPos]
  have hsubW : eval s1 (sub (v "len") (v "off")) = some (.word (word vw.length)) := by
    simp only [sub, eval_binop2, eval_lvar, s1, FUPDATE, show ("len" = "off") = False by decide,
      ↓reduceIte, h.rx.length, word_op, Option.map_some, Option.some.injEq, PanVal.word.injEq]
    change word f.size - word vw.offset = word vw.length
    rw [BitVec.ofNat_sub_ofNat_of_le f.size vw.offset (by omega) (by omega), hWidth]
  let s2 := { s1 with locals := FUPDATE s1.locals ("width", .word (word vw.length)) }
  have hnz2 : (s2.clock == 0) = false := by
    simp only [cSt1, dec_clock] at c1
    exact beq_eq_false_iff_ne.mpr (by simp only [s2, s1]; omega)
  let cSt2 := { dec_clock s2 with
    locals := mkCalleeLocals DragonStyleShard.echo.params
      [.word (src + word vw.offset), .word (scratch + word scratchCtrlBytes),
       .word (word vw.length), .word (word 4096)] }
  have heEntry : DragonStyleShard.EchoEntry (src + word vw.offset) (scratch + word scratchCtrlBytes)
      vw.length 4096 cSt2 :=
    ⟨⟨by simp [cSt2, mkCalleeLocals, DragonStyleShard.echo, FUPDATE_LIST, FUPDATE],
      by simp [cSt2, mkCalleeLocals, DragonStyleShard.echo, FUPDATE_LIST, FUPDATE],
      by simp [cSt2, mkCalleeLocals, DragonStyleShard.echo, FUPDATE_LIST, FUPDATE],
      be1.trans h.little,
      fun i hi => by
        simp only [cSt2, dec_clock, s2, s1, dm1]
        exact ⟨h.srcMapped i hi, h.scratchMapped i hi⟩⟩,
     by simp [cSt2, mkCalleeLocals, DragonStyleShard.echo, FUPDATE_LIST, FUPDATE],
     hLenLe, Nat.le_refl _⟩
  obtain ⟨t2, e2, c2, m2, f2, dm2, cd2, be2, _⟩ :=
    DragonStyleShard.echo_eval_ok cSt2 heEntry (by simp only [cSt2, dec_clock, s2, s1]; simp only [cSt1, dec_clock] at c1; omega)
  let s3 := { empty_locals t2 with locals := FUPDATE s2.locals ("copied", .word (word vw.length)) }
  have hfail2 : evaluate (failIf .NotEqual (v "copied") (v "width") 0) s3 = (.normal, s3) := by
    rw [failIf_eval s3 .NotEqual (v "copied") (v "width") (word vw.length) (word vw.length)
      (by simp [s3, FUPDATE]) (by simp [s3, s2, FUPDATE])]
    simp [word_cmp]
  have hstore : evaluate (storeWord (v "scratch") 48 (v "width")) s3 =
      (.normal, { s3 with memory := UPDATE (scratch + word 48) (word vw.length) s3.memory }) := by
    have hscr : s3.locals "scratch" = some (.word scratch) := by
      simp [s3, s2, s1, FUPDATE, h.scratchPtr]
    have hdm48 : s3.memaddrs (scratch + word 48) = true := by
      simpa [s3, empty_locals, dm2, cSt2, dec_clock, s2, s1, dm1, cSt1] using h.scratchLenWord
    rw [storeWord, evaluate_store]
    have haddr48 : eval s3 (add (v "scratch") (n 48)) = some (.word (scratch + word 48)) := by
      simp [add, eval_n, hscr, word_op]
    have hwid3 : eval s3 (v "width") = some (.word (word vw.length)) := by
      simp [s3, s2, FUPDATE]
    rw [haddr48, hwid3]
    simp [mem_stores, mem_store, hdm48]
  let tCopy := { s3 with memory := UPDATE (scratch + word 48) (word vw.length) s3.memory }
  have hmCopy : tCopy.memory = UPDATE (scratch + word 48) (word vw.length)
      (DragonStyleShard.copyMem (src + word vw.offset) (scratch + word scratchCtrlBytes) 0 vw.length s.memory) := by
    simp only [tCopy, s3, empty_locals, m2, cSt2, dec_clock, s2, s1, m1, cSt1]
  have hclkCopy : tCopy.clock + (parseFrameClk + vw.length + 2) ≥ s.clock := by
    simp only [tCopy, s3, empty_locals]
    simp only [cSt2, dec_clock, s2, s1] at c2
    simp only [cSt1, dec_clock] at c1
    omega
  have hevCopy : events tCopy = events s := by
    unfold events
    simp [tCopy, s3, empty_locals, f2, cSt2, dec_clock, s2, s1, f1, cSt1]
  have hstep : evaluate intake.body s =
      let r := evaluate admit tCopy
      (r.1, { r.2 with locals := res_var (res_var (res_var r.2.locals ("copied", s2.locals "copied"))
        ("width", s1.locals "width")) ("off", s.locals "off") }) := by
    have htail : evaluate (seqs [failIf .NotEqual (v "copied") (v "width") 0,
        storeWord (v "scratch") 48 (v "width"), admit]) s3 = evaluate admit tCopy := by
      simp only [seqs]
      rw [evaluate_seq, hfail2]
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [evaluate_seq, hstore]
      rfl
    have hmid : evaluate (seqs [failIf .Equal (v "off") (n 0) 0,
        localVar "width" (sub (v "len") (v "off")) <|
        .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <| seqs [
          failIf .NotEqual (v "copied") (v "width") 0,
          storeWord (v "scratch") 48 (v "width"),
          admit]]) s1 =
        let r := evaluate admit tCopy
        (r.1, { r.2 with locals := res_var (res_var r.2.locals ("copied", s2.locals "copied")) ("width", s1.locals "width") }) := by
      simp only [seqs]
      rw [evaluate_seq, hfail1]
      simp only [beq_self_eq_true, ↓reduceIte, localVar, evaluate_dec, hsubW, shape_of_word]
      change (let r3 := evaluate (.decCall "copied" .One "dn_echo" _ _) s2;
        (r3.1, { r3.2 with locals := res_var r3.2.locals ("width", s1.locals "width") })) = _
      have hargs2 : evalList s2 [add (v "src") (v "off"), bodyPtr, v "width", n 4096] =
          some [.word (src + word vw.offset), .word (scratch + word scratchCtrlBytes),
                .word (word vw.length), .word (word 4096)] := by
        simp [evalList_cons, evalList_nil, add, bodyPtr, eval_n, s2, s1, FUPDATE, h.rx.pointer, h.scratchPtr, word_op]
      have hcd2 : s2.code "dn_echo" = some (DragonStyleShard.echo.params, DragonStyleShard.echo.body) := by
        simpa [s2, s1, cd1, cSt1, dec_clock] using h.code.2
      have hcall2 : evaluate (.decCall "copied" .One "dn_echo"
          [add (v "src") (v "off"), bodyPtr, v "width", n 4096]
          (seqs [failIf .NotEqual (v "copied") (v "width") 0,
            storeWord (v "scratch") 48 (v "width"), admit])) s2 =
          let r := evaluate admit tCopy
          (r.1, { r.2 with locals := res_var r.2.locals ("copied", s2.locals "copied") }) := by
        have hepar : DragonStyleShard.echo.params = [("src", .One), ("dst", .One), ("len", .One), ("cap", .One)] := rfl
        rw [evaluate_decCall, hargs2, hcd2]
        simp only [hepar, shapesMatch, shape_of_word, beq_self_eq_true,
          Bool.and_self, hnz2, Bool.false_eq_true, ↓reduceIte]
        have e2' : evaluate DragonStyleShard.echo.body
            { locals := mkCalleeLocals [("src", Shape.One), ("dst", Shape.One), ("len", Shape.One), ("cap", Shape.One)]
                [.word (src + word vw.offset), .word (scratch + word scratchCtrlBytes),
                 .word (word vw.length), .word (word 4096)],
              globals := (dec_clock s2).globals, code := (dec_clock s2).code, memory := (dec_clock s2).memory,
              memaddrs := (dec_clock s2).memaddrs, clock := (dec_clock s2).clock, be := (dec_clock s2).be,
              ffi := (dec_clock s2).ffi, base_addr := (dec_clock s2).base_addr, top_addr := (dec_clock s2).top_addr } =
            (.ret (.word (word vw.length)), empty_locals t2) := e2
        rw [e2']
        simp only [shape_of_word, beq_self_eq_true, ↓reduceIte]
        have htail' : evaluate (seqs [failIf .NotEqual (v "copied") (v "width") 0,
            storeWord (v "scratch") 48 (v "width"), admit])
            { locals := FUPDATE s2.locals ("copied", .word (word vw.length)),
              globals := (empty_locals t2).globals, code := (empty_locals t2).code, memory := (empty_locals t2).memory,
              memaddrs := (empty_locals t2).memaddrs, clock := (empty_locals t2).clock, be := (empty_locals t2).be,
              ffi := (empty_locals t2).ffi, base_addr := (empty_locals t2).base_addr, top_addr := (empty_locals t2).top_addr } =
            evaluate admit tCopy := htail
        rw [htail']
      simp only [seqs] at hcall2
      rw [hcall2]
    have hpar : parseFrame.params = [("src", .One), ("len", .One)] := rfl
    unfold intake
    rw [evaluate_decCall]
    simp only [evalList_cons, evalList_nil, eval_lvar, h.rx.pointer, h.rx.length, h.code.1,
      hpar, shapesMatch, shape_of_word, beq_self_eq_true, Bool.and_self,
      hnz1, Bool.false_eq_true, ↓reduceIte]
    have e1' : evaluate parseFrame.body
        { locals := mkCalleeLocals [("src", Shape.One), ("len", Shape.One)] [.word src, .word (word f.size)],
          globals := (dec_clock s).globals, code := (dec_clock s).code, memory := (dec_clock s).memory,
          memaddrs := (dec_clock s).memaddrs, clock := (dec_clock s).clock, be := (dec_clock s).be,
          ffi := (dec_clock s).ffi, base_addr := (dec_clock s).base_addr, top_addr := (dec_clock s).top_addr } =
        (.ret (.word (word vw.offset)), t1) := e1
    rw [e1']
    simp only [shape_of_word, beq_self_eq_true, ↓reduceIte]
    have hmid' : evaluate (seqs [failIf .Equal (v "off") (n 0) 0,
        localVar "width" (sub (v "len") (v "off")) <|
        .decCall "copied" .One "dn_echo" [add (v "src") (v "off"), bodyPtr, v "width", n 4096] <| seqs [
          failIf .NotEqual (v "copied") (v "width") 0,
          storeWord (v "scratch") 48 (v "width"),
          admit]])
        { locals := FUPDATE s.locals ("off", .word (word vw.offset)),
          globals := t1.globals, code := t1.code, memory := t1.memory, memaddrs := t1.memaddrs,
          clock := t1.clock, be := t1.be, ffi := t1.ffi, base_addr := t1.base_addr, top_addr := t1.top_addr } =
        let r := evaluate admit tCopy
        (r.1, { r.2 with locals := res_var (res_var r.2.locals ("copied", s2.locals "copied")) ("width", s1.locals "width") }) := hmid
    rw [hmid']
  refine ⟨tCopy, hmCopy, hclkCopy, hevCopy, rfl, ?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · rw [hstep]; rfl

end Obend.Lower.Pancake.DurableTurn
