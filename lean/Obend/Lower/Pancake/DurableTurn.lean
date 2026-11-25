module
public import Obend.Lower.Pancake.BorrowedTurn
public import Obend.Lower.Pancake.FfiTrace
import all Obend.Lower.Pancake.BorrowedTurn
import all Obend.Lower.Pancake.PanSem
import Obend.Tactic.Tooth

public section
namespace Obend.Lower.Pancake.DurableTurn

private abbrev v := PExp.lvar
private def n (i : Nat) : PExp := .const (BitVec.ofNat 64 i)
private def add (a b : PExp) : PExp := .binop .Add [a,b]
private def sub (a b : PExp) : PExp := .binop .Sub [a,b]
private def mul (a b : PExp) : PExp := .panop .Mul [a,b]
private def byte (p off : PExp) : PExp := .loadByte (add p off)
private def ret (i : Nat) : PStmt := .ret (n i)
private def seqs : List PStmt → PStmt
  | [] => .skip
  | [x] => x
  | x :: xs => .seq x (seqs xs)
private def failIf (c : Cmp) (a b : PExp) (code : Nat) : PStmt :=
  .ite (.cmp c a b) (ret code) .skip
private def localVar (name : String) (init : PExp) (body : PStmt) := PStmt.dec name .One init body
private def inc (name : String) := PStmt.lassign name (add (v name) (n 1))

private def rejectIf (op : Cmp) (a b : PExp) (next : PStmt) :=
  PStmt.ite (.cmp op a b) (ret 0) next

/-- Compile the fixed grammar to byte loads. The counter is consumed during
emission. No parser-side table or loop is needed in the machine code. -/
def expectBytes (pat : ByteArray) (off : Nat) (next : PStmt) : Nat → PStmt
  | 0 => next
  | i+1 => rejectIf .NotEqual (byte (v "src") (n (off+i))) (n pat[i]!.toNat)
      (expectBytes pat off next i)

private def digits : PStmt :=
  let a := byte (v "src") (n BorrowedTurn.header.size)
  let b := byte (v "src") (n (BorrowedTurn.header.size+1))
  rejectIf .Lower a (n 49) <| rejectIf .Lower (n 57) a <|
  rejectIf .Lower b (n 48) <| rejectIf .Lower (n 57) b <|
  rejectIf .NotEqual (sub (v "len") (n BorrowedTurn.bodyOffset))
    (add (mul (sub a (n 48)) (n 10)) (sub b (n 48))) (ret BorrowedTurn.bodyOffset)

def parseFrame : PFun := {
  name := "parseFrame", params := ["src","len"].map (·, .One), exported := true
  body := rejectIf .Lower (v "len") (n (BorrowedTurn.bodyOffset+10)) <|
    rejectIf .Lower (n (BorrowedTurn.bodyOffset+99)) (v "len") <|
    expectBytes BorrowedTurn.header 0
      (expectBytes BorrowedTurn.delimiter (BorrowedTurn.header.size+2) digits BorrowedTurn.delimiter.size)
      BorrowedTurn.header.size }

private abbrev word (x : Nat) := BitVec.ofNat 64 x

/-- A verifier-owned RX lease supplies a pointer, the descriptor length, and a
mapped byte at every offset below that length. -/
structure RxFrame {θ} (s : PanState θ) (src : Word) (frame : ByteArray) : Prop where
  pointer : s.locals "src" = some (.word src)
  length : s.locals "len" = some (.word (BitVec.ofNat 64 frame.size))
  fits : frame.size < 2^64
  bytes : ∀ i, i < frame.size → mem_load_byte s.memory s.memaddrs s.be
    (src + BitVec.ofNat 64 i) = some frame[i]!.toBitVec

private theorem load_at {θ s src frame} (rx : RxFrame (θ := θ) s src frame) (i : Nat)
    (h : i < frame.size) : eval s (byte (v "src") (n i)) = some (.word (word frame[i]!.toNat)) := by
  simp [byte,add,n,rx.pointer,word_op,rx.bytes i h,word]
  apply BitVec.eq_of_toNat_eq
  simp

private theorem eval_n {θ} (s : PanState θ) (i : Nat) : eval s (n i) = some (.word (word i)) := rfl

private theorem reject_eval {θ} (s : PanState θ) (op : Cmp) (a b : PExp) (x y : Word)
    (ha : eval s a = some (.word x)) (hb : eval s b = some (.word y)) (next : PStmt) :
    evaluate (rejectIf op a b next) s =
      if word_cmp op x y then (.ret (.word 0),empty_locals s) else evaluate next s := by
  cases cond : word_cmp op x y <;>
    simp [rejectIf, evaluate_ite,ha,hb,cond,ret,n,evaluate_ret]

theorem literal_bytes_refine {θ s src frame} (rx : RxFrame (θ := θ) s src frame)
    (pat : ByteArray) (off : Nat) (next : PStmt) (k : Nat)
    (inside : off+k ≤ frame.size) (valid : k ≤ pat.size) :
    evaluate (expectBytes pat off next k) s =
      if BorrowedTurn.matchBytes frame pat off k then evaluate next s else (.ret (.word 0),empty_locals s) := by
  induction k with
  | zero => simp [expectBytes,BorrowedTurn.matchBytes]
  | succ k ih =>
    have h₁ : off+k < frame.size := by omega
    have h₂ : k < pat.size := by omega
    rw [expectBytes, reject_eval _ _ _ _ _ _ (load_at rx _ h₁) (eval_n s _) _,
      ih (by omega) (by omega)]
    simp only [BorrowedTurn.matchBytes, getElem?_pos, getElem!_pos,
      h₁,h₂,word_cmp,Option.some_beq_some]
    by_cases eq : frame[off+k] = pat[k]
    · simp [eq,word]
    · have ne : word frame[off+k].toNat ≠ word pat[k].toNat := by
        intro h
        apply eq
        apply UInt8.toNat_inj.mp
        have ha := frame[off+k].toNat_lt
        have hb := pat[k].toNat_lt
        simpa [word,Nat.mod_eq_of_lt (show frame[off+k].toNat < 2^64 by omega),
          Nat.mod_eq_of_lt (show pat[k].toNat < 2^64 by omega)] using congrArg BitVec.toNat h
      simp [eq,ne]

private theorem lower_eval {θ} (s : PanState θ) (a b : PExp) (x y : Nat)
    (ha : eval s a = some (.word (word x))) (hb : eval s b = some (.word (word y)))
    (hx : x < 2^64) (hy : y < 2^64) (next : PStmt) :
    evaluate (rejectIf .Lower a b next) s =
      if x < y then (.ret (.word 0),empty_locals s) else evaluate next s := by
  rw [reject_eval _ _ _ _ _ _ ha hb]
  simp [word_cmp,BitVec.ult,word,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]

private theorem digits_refine {θ s src f} (rx : RxFrame (θ := θ) s src f)
    (lo : BorrowedTurn.bodyOffset+10 ≤ f.size) (hi : f.size ≤ BorrowedTurn.bodyOffset+99) :
    evaluate digits s = (.ret (.word (if BorrowedTurn.validLength f then word BorrowedTurn.bodyOffset else 0)),
      empty_locals s) := by
  let a := f[BorrowedTurn.header.size]!.toNat
  let b := f[BorrowedTurn.header.size+1]!.toNat
  have offset : BorrowedTurn.bodyOffset = 60 := by unfold BorrowedTurn.bodyOffset BorrowedTurn.header BorrowedTurn.delimiter; simp only [String.toUTF8_eq_toByteArray]; rfl
  have headerWidth : BorrowedTurn.header.size = 54 := by unfold BorrowedTurn.header; simp only [String.toUTF8_eq_toByteArray]; rfl
  have ha := load_at rx BorrowedTurn.header.size (by omega)
  have hb := load_at rx (BorrowedTurn.header.size+1) (by omega)
  have smallA : a < 256 := UInt8.toNat_lt _
  have smallB : b < 256 := UInt8.toNat_lt _
  unfold digits
  rw [lower_eval _ _ _ a 49 ha (eval_n _ _) (by omega) (by decide),
    lower_eval _ _ _ 57 a (eval_n _ _) ha (by decide) (by omega),
    lower_eval _ _ _ b 48 hb (eval_n _ _) (by omega) (by decide),
    lower_eval _ _ _ 57 b (eval_n _ _) hb (by decide) (by omega)]
  change _ = (PanResult.ret (PanVal.word (if decide (49 ≤ a ∧ a ≤ 57 ∧ 48 ≤ b ∧ b ≤ 57 ∧
    f.size = BorrowedTurn.bodyOffset + ((a-48)*10+(b-48))) then word BorrowedTurn.bodyOffset else 0)),empty_locals s)
  split <;> rename_i hA
  · simp [show ¬49 ≤ a by omega]
  split <;> rename_i hAA
  · simp [show ¬a ≤ 57 by omega]
  split <;> rename_i hB
  · simp [show ¬48 ≤ b by omega]
  split <;> rename_i hBB
  · simp [show ¬b ≤ 57 by omega]
  have hw : eval s (sub (v "len") (n BorrowedTurn.bodyOffset)) =
      some (.word (word (f.size-BorrowedTurn.bodyOffset))) := by
    simp [sub,rx.length,n,word_op,word,BitVec.ofNat_sub_ofNat_of_le f.size BorrowedTurn.bodyOffset (by omega : BorrowedTurn.bodyOffset < 2^64) (by omega)]
  have hd : eval s (add (mul (sub (byte (v "src") (n BorrowedTurn.header.size)) (n 48)) (n 10))
      (sub (byte (v "src") (n (BorrowedTurn.header.size+1))) (n 48))) =
      some (.word (word ((a-48)*10+(b-48)))) := by
    simp only [add,mul,sub,eval_binop2,eval_panop2,ha,hb,eval_n,word_op,pan_op,List.foldr,
      BitVec.add_zero,Option.map_some]
    change some (PanVal.word ((word a - word 48) * word 10 + (word b - word 48))) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
      BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat]
  rw [reject_eval _ _ _ _ _ _ hw hd]
  have decoded : (a-48)*10+(b-48) < 2^64 := by omega
  have width : f.size-BorrowedTurn.bodyOffset < 2^64 := by omega
  have eq : word (f.size-BorrowedTurn.bodyOffset) = word ((a-48)*10+(b-48)) ↔
      f.size = BorrowedTurn.bodyOffset + ((a-48)*10+(b-48)) := by
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      simp only [word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt width,Nat.mod_eq_of_lt decoded] at this
      omega
    · intro e
      congr 1
      omega
  by_cases exactWidth : f.size = BorrowedTurn.bodyOffset + ((a-48)*10+(b-48))
  all_goals simp_all [word_cmp,ret,evaluate_ret,n,word]

/-- The emitted parser executes at any fuel. Its sole result is the borrowed
body offset or zero, and both return paths preserve the entire input memory. -/
theorem parseFrame_refines {θ s src f} (rx : RxFrame (θ := θ) s src f) (l : BorrowedTurn.Lease) :
    evaluate parseFrame.body s = (.ret (.word (BitVec.ofNat 64
      (((BorrowedTurn.parse f l).map BorrowedTurn.View.offset).getD 0))), empty_locals s) := by
  have offset : BorrowedTurn.bodyOffset = 60 := by
    unfold BorrowedTurn.bodyOffset BorrowedTurn.header BorrowedTurn.delimiter
    simp only [String.toUTF8_eq_toByteArray]
    rfl
  have hHeader : BorrowedTurn.header.size + 2 + BorrowedTurn.delimiter.size = BorrowedTurn.bodyOffset := rfl
  have length : eval s (v "len") = some (.word (word f.size)) := by simpa using rx.length
  simp only [parseFrame]
  rw [lower_eval _ _ _ f.size (BorrowedTurn.bodyOffset+10) length (eval_n _ _) rx.fits (by omega),
    lower_eval _ _ _ (BorrowedTurn.bodyOffset+99) f.size (eval_n _ _) length (by omega) rx.fits]
  split
  next tooShort =>
    simp [BorrowedTurn.parse,show ¬BorrowedTurn.bodyOffset + 10 ≤ f.size by omega]
  next validMin =>
    split
    next tooLong =>
      simp [BorrowedTurn.parse,show ¬ f.size ≤ BorrowedTurn.bodyOffset + 99 by omega]
    next validMax =>
      have lo : BorrowedTurn.bodyOffset+10 ≤ f.size := by omega
      have hi : f.size ≤ BorrowedTurn.bodyOffset+99 := by omega
      rw [literal_bytes_refine rx _ _ _ _ (by omega) (Nat.le_refl _),
        literal_bytes_refine rx _ _ _ _ (by omega) (Nat.le_refl _), digits_refine rx lo hi]
      cases a : BorrowedTurn.matchBytes f BorrowedTurn.header 0 BorrowedTurn.header.size <;>
        cases b : BorrowedTurn.matchBytes f BorrowedTurn.delimiter
          (BorrowedTurn.header.size+2) BorrowedTurn.delimiter.size <;>
        cases c : BorrowedTurn.validLength f <;> simp [BorrowedTurn.parse,lo,hi,a,b,c,word]

#tooth parseFrame_refines by mutation parseFrame := ⟨"parseFrame", [], .ret (.const 0), true⟩

/-- The cold view starts with generation and authenticated channel principal.
Each 100-byte entry holds a length and up to 99 canonical body bytes.
The private scratch has an eight-byte control prefix followed by the copy. -/
private def body := add (v "scratch") (n 8)
private def field (offset : Nat) := byte body (n offset)
private def control (off : Nat) (e : PExp) := PStmt.storeByte (add (v "scratch") (n off)) e
private def io (name : String) := PStmt.extCall name body (v "width") (v "scratch") (n 8)
private def command (name : String) := seqs [
  control 0 (n 255), io name, failIf .NotEqual (byte (v "scratch") (n 0)) (n 0) 0]
private def reply (generation : PExp) := seqs [
  control 1 generation, command "reply", .ret generation]

private def checkRecord : PStmt :=
  localVar "entry" (add (v "state") (add (n 2) (mul (v "i") (n 100)))) <| seqs [
    .lassign "lastId" (byte (v "entry") (n 3)),
    .ite (.cmp .Equal (field 0) (byte (v "entry") (n 1))) (seqs [
      .lassign "spent" (add (v "spent") (byte (v "entry") (n 4))),
      .ite (.cmp .Equal (field 1) (byte (v "entry") (n 2))) (seqs [
        failIf .NotEqual (v "width") (byte (v "entry") (n 0)) 0,
        localVar "j" (n 0) (.while_ (.cmp .Lower (v "j") (v "width")) (seqs [
          failIf .NotEqual (byte body (v "j")) (byte (v "entry") (add (n 1) (v "j"))) 0, inc "j"])),
        reply (add (v "i") (n 1))]) .skip]) .skip,
    inc "i"]

private theorem io_trace (name : String) (named : name ≠ "") : CommandTrace (io name) [name] :=
  extCall_trace name named _ _ _ _

private theorem command_trace (name : String) (named : name ≠ "") :
    CommandTrace (command name) [name] :=
  seq_trace (store_trace _ _) (seq_trace (io_trace name named) (status_trace _))

private def commands : List String → PStmt
  | [] => .skip
  | name :: names => .seq (command name) (commands names)

private theorem commands_trace (names : List String) (named : "" ∉ names) :
    CommandTrace (commands names) names := by
  induction names with
  | nil => exact skip_trace
  | cons x xs ih =>
    exact seq_trace (command_trace x (by intro e; subst x; simp at named))
      (ih (fun h => named (List.mem_cons_of_mem _ h)))

private def publish (generation : PExp) :=
  PStmt.seq (control 1 generation)
    (.seq (commands ["authorize","wal","flush","fua","dispatch"])
      (.seq (control 1 generation) (command "reply")))

def freshCommit (generation : PExp) : PStmt := .seq (publish generation) (.ret generation)

/-- A positive return from the emitted fresh-turn path requires these exact
PanSem oracle calls in order, regardless of the oracle or initial machine state. -/
theorem fresh_commit_order {θ} (s f : PanState θ) (g : PExp) (w : Word) (positive : w ≠ 0)
    (run : evaluate (freshCommit g) s = (.ret (.word w),f)) :
    events f = events s ++ ["authorize","wal","flush","fua","dispatch","reply"] := by
  have contract : CommandTrace (publish g) ["authorize","wal","flush","fua","dispatch","reply"] :=
    seq_trace (store_trace _ _) (seq_trace (commands_trace _ (by decide))
      (seq_trace (store_trace _ _) (command_trace "reply" (by decide))))
  exact positive_return_trace s f _ _ _ w positive contract run

#tooth fresh_commit_order by mutation freshCommit := fun g => .ret g

private def admit : PStmt :=
  localVar "count" (byte (v "state") (n 0)) <|
  localVar "lastId" (n 0) <| localVar "spent" (n 0) <| localVar "i" (n 0) <| seqs [
    failIf .Lower (n 8) (v "count") 0,
    failIf .NotEqual (field 0) (byte (v "state") (n 1)) 0,
    .while_ (.cmp .Lower (v "i") (v "count")) checkRecord,
    failIf .Equal (v "count") (n 8) 0, failIf .NotLower (v "lastId") (field 2) 0,
    failIf .Equal (field 3) (n 0) 0, failIf .Lower (n 20) (add (v "spent") (field 3)) 0,
    freshCommit (add (v "count") (n 1))]

def intake : PFun := {
  name := "turnIntake", params := ["src","len","state","scratch"].map (·, .One), exported := true
  body := .decCall "off" .One "parseFrame" [v "src",v "len"] <| seqs [
    failIf .Equal (v "off") (n 0) 0,
    localVar "width" (sub (v "len") (v "off")) <|
    .decCall "copied" .One "dn_echo" [add (v "src") (v "off"),body,v "width",n 99] <|
    seqs [failIf .NotEqual (v "copied") (v "width") 0, admit]] }

def source := emitPnkProg [DragonStyleShard.echo, parseFrame, intake]

end Obend.Lower.Pancake.DurableTurn
