module
public import Obend.Lower.Pancake.EmitPnk
public import Obend.Lower.Pancake.PancakeKeccak
public import Obend.Digest.Cshake256.Spec
import all Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Digest.Cshake256.Spec

/-! Attenuated capability tokens (macaroons) checked by one Pancake function with no
Lean runtime. A token's tag is a cSHAKE256 chain: `mac root nonce`, then one link per
caveat keyed by the previous tag. With the customization fixed and every input 64
bytes, a link absorbs one constant prefix block and one message block, so the kernel
starts each permutation from the precomputed prefix state.

The verifier constructs the call buffer with its trusted root key and request context.
Only the nonce, caveats and claimed tag come from the token holder. The 25-word
workspace must be disjoint from the call buffer. The tag
comparison accumulates the four limb differences before its single branch, and the
workspace is cleared on every in-range count. An oversized count leaves memory untouched. -/

public section
namespace Obend.Lower.Pancake.Macaroon
open Obend.Digest WordBuffer
set_option autoImplicit false

/-- Four words, least significant byte first: a key, nonce, caveat body or tag. -/
structure Digest where
  w0 : Word
  w1 : Word
  w2 : Word
  w3 : Word
  deriving DecidableEq, Repr, Inhabited

def Digest.words (d : Digest) : List Word := [d.w0, d.w1, d.w2, d.w3]

/-- Eight little-endian bytes per word. -/
def leBytes (ws : List Word) : List UInt8 :=
  ws.flatMap fun (w : Word) => (List.range 8).map fun i => UInt8.ofBitVec ((w >>> (8*i)).setWidth 8)

/-- The first four little-endian words of a byte string. -/
def Digest.ofBytes (bs : List UInt8) : Digest :=
  ⟨Cshake256.laneFromBlock bs 0, Cshake256.laneFromBlock bs 1,
   Cshake256.laneFromBlock bs 2, Cshake256.laneFromBlock bs 3⟩

/-- ASCII `OBEND.PANCAKE.MACAROON/v1`, the SP 800-185 customization of every link. -/
def domain : List UInt8 :=
  [79, 66, 69, 78, 68, 46, 80, 65, 78, 67, 65, 75, 69, 46, 77, 65, 67, 65, 82, 79, 79, 78,
   47, 118, 49]

/-- One link: cSHAKE256 of a 32-byte key followed by a 32-byte message. -/
def mac (key msg : Digest) : Digest :=
  Digest.ofBytes (Cshake256.cshake256Bytes domain (leBytes (key.words ++ msg.words)))

structure Caveat where
  opMask : Word
  seat : Word
  maxSpend : Word
  minEpoch : Word
  deriving DecidableEq, Repr

def Caveat.body (c : Caveat) : Digest := ⟨c.opMask, c.seat, c.maxSpend, c.minEpoch⟩

structure Token where
  rootKey : Digest
  nonce : Digest
  caveats : List Caveat
  claimed : Digest
  deriving DecidableEq, Repr

structure Request where
  op : Word
  seat : Word
  spend : Word
  epoch : Word
  deriving DecidableEq, Repr

inductive Status where
  | accepted | malformed | forged | opDenied | wrongSeat | overSpend | tooEarly
  deriving DecidableEq, Repr

def Status.code : Status → Word
  | .accepted => 0 | .malformed => 1 | .forged => 2 | .opDenied => 3
  | .wrongSeat => 4 | .overSpend => 5 | .tooEarly => 6

/-- `tag₀ = mac root nonce`, `tagᵢ₊₁ = mac tagᵢ caveatᵢ`. -/
def Token.tag (t : Token) : Digest :=
  (t.nonce :: t.caveats.map Caveat.body).foldl mac t.rootKey

/-- Every requested operation is in the mask, the seat is the caller's, and spend and
    epoch are within bounds. Comparisons are unsigned. -/
def Caveat.verdict (c : Caveat) (r : Request) : Status :=
  if c.opMask &&& r.op = r.op then
    if c.seat = r.seat then
      if r.spend ≤ c.maxSpend then
        if c.minEpoch ≤ r.epoch then .accepted else .tooEarly
      else .overSpend
    else .wrongSeat
  else .opDenied

/-- The first refusing caveat decides. -/
def admit (r : Request) : List Caveat → Status
  | [] => .accepted
  | c :: cs => if c.verdict r = .accepted then admit r cs else c.verdict r

def maxCaveats : Nat := 8

/-- A forged tag is reported before any caveat is consulted. -/
def verifyMacaroon (t : Token) (r : Request) : Status :=
  if t.caveats.length ≤ maxCaveats then
    if t.tag = t.claimed then admit r t.caveats else .forged
  else .malformed

/-- An attenuated token, extended by its holder without the root key. -/
def Token.attenuate (t : Token) (c : Caveat) : Token :=
  {t with caveats := t.caveats ++ [c], claimed := mac t.claimed c.body}

theorem attenuate_tag (t : Token) (c : Caveat) (h : t.tag = t.claimed) :
    (t.attenuate c).tag = (t.attenuate c).claimed := by
  have extend : (t.attenuate c).tag = mac t.tag c.body := by
    simp [Token.attenuate, Token.tag, List.foldl_append]
  rw [extend, h]
  rfl

/-- A caveat added by attenuation can only narrow what is admitted. -/
theorem admit_append (r : Request) (cs : List Caveat) (c : Caveat) :
    admit r (cs ++ [c]) = .accepted ↔ admit r cs = .accepted ∧ c.verdict r = .accepted := by
  induction cs with
  | nil => by_cases h : c.verdict r = .accepted <;> simp [admit, h]
  | cons d ds ih => by_cases h : d.verdict r = .accepted <;> simp [admit, h, ih]

/-! ## Memory image -/

/-- Root key, nonce, `n` caveats, claimed tag and request: `16 + 4n` words. -/
def tokenWords (n : Nat) : Nat := 16 + 4*n

/-- Four consecutive words at `p`. -/
def quad (m : Word → Word) (p : Word) : Digest :=
  ⟨m (address p 0), m (address p 1), m (address p 2), m (address p 3)⟩

def readCaveat (m : Word → Word) (p : Word) : Caveat :=
  ⟨m (address p 0), m (address p 1), m (address p 2), m (address p 3)⟩

/-- `n` caveats from `p` on, as the kernel walks them. -/
def readCaveats (m : Word → Word) : Word → Nat → List Caveat
  | _, 0 => []
  | p, n+1 => readCaveat m p :: readCaveats m (address p 4) n

def readToken (m : Word → Word) (b : Word) (n : Nat) : Token :=
  ⟨quad m b, quad m (address b 4), readCaveats m (address b 8) n, quad m (address b (8+4*n))⟩

def readRequest (m : Word → Word) (b : Word) (n : Nat) : Request :=
  let r := quad m (address b (12+4*n))
  ⟨r.w0, r.w1, r.w2, r.w3⟩

/-- The workspace's 25 words read as zero; nothing else changes. -/
def wipe (m : Word → Word) (b : Word) : Word → Word :=
  fun a => if a ∈ (List.finRange 25).map (fun j => address b j.val) then 0 else m a

/-! ## The kernel -/

/-- State after the single prefix block of `domain`, shared by every link. -/
@[irreducible] def prefixState : Cshake256.State :=
  Cshake256.keccakF1600 (Cshake256.xorRateBlock Cshake256.zeroState
    (Cshake256.customizationPrefix domain))

/-- Lanes 8-16 of each message block: the cSHAKE suffix after the 64 message bytes and the
    final bit of the 136-byte rate. -/
def padWords : List Word := [4, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000]

private def at_ (p : String) (i : Nat) : PExp :=
  .binop .Add [.lvar p, .const (BitVec.ofNat 64 (8*i))]
private def load (p : String) (i : Nat) : PExp := .load .One (at_ p i)
private def word (n : Nat) : PExp := .const (BitVec.ofNat 64 n)
private def finish (v : Status) : PStmt := .ret (.const v.code)

/-- The root key becomes the first link's key. -/
def loadKey : PStmt := .store (.lvar "state") (.rstruct ((List.finRange 25).map fun i =>
  if i.val < 4 then load "token" i.val else .const 0))

/-- Lane `i` of `prefixState` xor the next block: the previous tag in lanes 0-3, the
    message at `msg`, then the padding. -/
def absorbField (i : Fin 25) : PExp :=
  let c := Keccak.lanes prefixState i
  if i.val < 4 then .binop .Xor [.const c, load "state" i.val]
  else if i.val < 8 then .binop .Xor [.const c, load "msg" (i.val - 4)]
  else .const (c ^^^ padWords.getD (i.val - 8) 0)

def absorbBlock : PStmt := .store (.lvar "state") (.rstruct ((List.finRange 25).map absorbField))

def advance : PStmt := .seq (.lassign "msg" (.binop .Add [.lvar "msg", word 32]))
  (.lassign "left" (.binop .Sub [.lvar "left", word 1]))

/-- One link per iteration: the nonce first, then each caveat body. -/
def chainLoop : PStmt := .while_ (.lvar "left")
  (.seq absorbBlock (Keccak.roundsThen "state" advance Cshake256.roundConstants))

private def limbDiff (i : Nat) : PExp := .binop .Xor [load "state" i, load "msg" i]

/-- `(((t₀ ^ c₀) | (t₁ ^ c₁)) | (t₂ ^ c₂)) | (t₃ ^ c₃)`, compared once. -/
def tagDiff : PExp :=
  .binop .Or [.binop .Or [.binop .Or [limbDiff 0, limbDiff 1], limbDiff 2], limbDiff 3]

def scrub : PStmt := .store (.lvar "state") (.rstruct ((List.finRange 25).map fun _ => .const 0))

def nextCaveat : PStmt := .seq (.lassign "cav" (.binop .Add [.lvar "cav", word 32]))
  (.lassign "left" (.binop .Sub [.lvar "left", word 1]))

/-- `Caveat.verdict` of the caveat at `cav`, test by test. -/
def caveatCheck : PStmt :=
  .ite (.cmp .Equal (.binop .And [load "cav" 0, .lvar "op"]) (.lvar "op"))
    (.ite (.cmp .Equal (load "cav" 1) (.lvar "seat"))
      (.ite (.cmp .NotLower (load "cav" 2) (.lvar "spend"))
        (.ite (.cmp .NotLower (.lvar "epoch") (load "cav" 3)) nextCaveat (finish .tooEarly))
        (finish .overSpend))
      (finish .wrongSeat))
    (finish .opDenied)

def caveatLoop : PStmt := .while_ (.lvar "left") caveatCheck

/-- The request follows the claimed tag, where `msg` points after the chain. -/
def admitStage : PStmt :=
  .dec "op" .One (load "msg" 4) <| .dec "seat" .One (load "msg" 5) <|
  .dec "spend" .One (load "msg" 6) <| .dec "epoch" .One (load "msg" 7) <|
  .dec "cav" .One (at_ "token" 8) <|
  .seq (.lassign "left" (.lvar "count")) (.seq caveatLoop (finish .accepted))

/-- Mismatch path after the scrub. -/
def refuseForged : PStmt := finish .forged

def verifyBody : PStmt :=
  .seq loadKey <|
  .dec "msg" .One (at_ "token" 4) <|
  .dec "left" .One (.binop .Add [.lvar "count", word 1]) <|
  .seq chainLoop <|
  .dec "diff" .One tagDiff <|
  .seq scrub <|
  .ite (.cmp .Equal (.lvar "diff") (word 0)) admitStage refuseForged

/-- SysV arguments: the token words, the caveat count and the workspace. -/
def kernel : PFun := ⟨"macaroonVerify", [("token", .One), ("count", .One), ("state", .One)],
  .ite (.cmp .Lower (.lvar "count") (word (maxCaveats + 1))) verifyBody (finish .malformed), true⟩

/-! ## A link is one permutation from the prefix state -/

private theorem leBytes_cons (w : Word) (ws : List Word) :
    leBytes (w :: ws) =
      (List.range 8).map (fun i => UInt8.ofBitVec ((w >>> (8*i)).setWidth 8)) ++ leBytes ws := by
  simp [leBytes]

theorem leBytes_length (ws : List Word) : (leBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [leBytes_cons, List.length_append, ih, List.length_map, List.length_range, List.length_cons]
    omega

theorem leBytes_append (xs ys : List Word) : leBytes (xs ++ ys) = leBytes xs ++ leBytes ys := by
  simp [leBytes, List.flatMap_append]

private theorem leBytes_getD (ws : List Word) (i o : Nat) (ho : o < 8) :
    ((leBytes ws).getD (8*i+o) 0).toBitVec = ((ws.getD i 0) >>> (8*o)).setWidth 8 := by
  induction ws generalizing i with
  | nil => simp [leBytes]
  | cons w ws ih =>
    rw [leBytes_cons]
    cases i with
    | zero =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
      simp [ho]
    | succ j =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
        ← List.getD_eq_getElem?_getD]
      simp only [List.length_map, List.length_range, List.getD_cons_succ]
      rw [show 8 * (j+1) + o - 8 = 8*j+o by omega]
      exact ih j

/-- Reading a block of little-endian words lane by lane returns the words. -/
theorem laneFromBlock_leBytes (ws : List Word) (i : Nat) :
    Cshake256.laneFromBlock (leBytes ws) i = ws.getD i 0 :=
  ByteMemory.lane_eq _ _ _ fun j hj => leBytes_getD ws i j hj

private theorem squeeze_byte (st : Cshake256.State) (i o : Nat) (hi : i < 4) (ho : o < 8) :
    ((Cshake256.squeeze32 st).getD (8*i+o) 0).toBitVec =
      ((st.getD i Cshake256.zeroLane) >>> (8*o)).setWidth 8 := by
  have hx : 8*i+o < 32 := by omega
  rw [List.getD_eq_getElem?_getD]
  simp only [Cshake256.squeeze32, Cshake256.outputBytes, List.getElem?_map, List.getElem?_range hx,
    Option.map_some, Option.getD_some, Cshake256.stateByte,
    show (8*i+o)/8 = i by omega, show (8*i+o)%8 = o by omega]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The first 32 squeezed bytes are the state's first four lanes. -/
theorem ofBytes_squeeze (st : Cshake256.State) :
    Digest.ofBytes (Cshake256.squeeze32 st) =
      ⟨Keccak.lanes st 0, Keccak.lanes st 1, Keccak.lanes st 2, Keccak.lanes st 3⟩ := by
  have lane (i : Nat) (hi : i < 4) :
      Cshake256.laneFromBlock (Cshake256.squeeze32 st) i = st.getD i Cshake256.zeroLane :=
    ByteMemory.lane_eq _ _ _ fun j hj => squeeze_byte st i j hi hj
  simp only [Digest.ofBytes, lane 0 (by decide), lane 1 (by decide), lane 2 (by decide),
    lane 3 (by decide), Keccak.lanes]
  rfl

private theorem domain_ne : domain ≠ [] := by simp [domain]

private theorem prefix_length : (Cshake256.customizationPrefix domain).length = 136 := by
  decide +kernel

private theorem padWords_bytes : leBytes padWords = [4] ++ List.replicate 70 0 ++ [128] := by
  decide +kernel

/-- cSHAKE256 of a 64-byte input under `domain`: the prefix block is already absorbed. -/
theorem cshake_link (ws : List Word) (hw : ws.length = 8) :
    Cshake256.cshake256Bytes domain (leBytes ws) = Cshake256.squeeze32 (Cshake256.keccakF1600
      (Cshake256.xorRateBlock prefixState (leBytes (ws ++ padWords)))) := by
  have hx : (leBytes ws).length = 64 := by rw [leBytes_length, hw]
  have hy : (leBytes (ws ++ padWords)).length = 136 := by
    rw [leBytes_length, List.length_append, hw]; rfl
  have pad : Cshake256.padForRate (Cshake256.customizationPrefix domain ++ leBytes ws) 4 =
      Cshake256.customizationPrefix domain ++ leBytes (ws ++ padWords) := by
    unfold Cshake256.padForRate
    simp only [List.length_append, prefix_length, hx, Cshake256.rateBytes]
    simp [leBytes_append, padWords_bytes, List.append_assoc]
  have absorb (y : List UInt8) (h : y.length = 136) :
      Cshake256.absorbPadded (Cshake256.customizationPrefix domain ++ y) =
        Cshake256.keccakF1600 (Cshake256.xorRateBlock prefixState y) := by
    have len : (Cshake256.customizationPrefix domain ++ y).length / Cshake256.rateBytes = 2 := by
      simp [prefix_length, h, Cshake256.rateBytes]
    unfold Cshake256.absorbPadded
    rw [len]
    simp only [Cshake256.absorbFrom, Cshake256.rateBytes, List.take_left' prefix_length,
      List.drop_left' prefix_length, List.take_of_length_le (Nat.le_of_eq h)]
    unfold prefixState
    rfl
  simp only [Cshake256.cshake256Bytes, domain_ne, ↓reduceIte]
  rw [pad, absorb _ hy]

/-- The block a link absorbs: key, message, padding. -/
def linkInput (key msg : Digest) : Cshake256.State :=
  Cshake256.xorRateBlock prefixState (leBytes (key.words ++ msg.words ++ padWords))

/-- `mac` is the first four lanes of one Keccak-f[1600] from `linkInput`. -/
theorem mac_lanes (key msg : Digest) :
    let out := Cshake256.keccakF1600 (linkInput key msg)
    mac key msg = ⟨Keccak.lanes out 0, Keccak.lanes out 1, Keccak.lanes out 2, Keccak.lanes out 3⟩ := by
  intro out
  rw [mac, cshake_link _ (by simp [Digest.words]), ofBytes_squeeze]
  rfl

/-- Lane `i` of `linkInput`: rate lanes take the block word. -/
theorem linkInput_lane (key msg : Digest) (i : Fin 25) :
    Keccak.lanes (linkInput key msg) i =
      if i.val < 17 then Keccak.lanes prefixState i ^^^ (key.words ++ msg.words ++ padWords).getD i.val 0
      else Keccak.lanes prefixState i := by
  simp only [linkInput, Cshake256.xorRateBlock, Keccak.read_ofFn, Cshake256.rateLanes,
    laneFromBlock_leBytes]
  rfl

/-! ## Execution -/

/-- Everything but memory, locals and clock is as in `s`. -/
structure Agrees {τ : Type} (s t : PanState τ) : Prop where
  globals : t.globals = s.globals
  code : t.code = s.code
  memaddrs : t.memaddrs = s.memaddrs
  be : t.be = s.be
  ffi : t.ffi = s.ffi
  base : t.base_addr = s.base_addr
  top : t.top_addr = s.top_addr

private theorem Agrees.refl {τ : Type} (s : PanState τ) : Agrees s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem Agrees.trans {τ : Type} {s t u : PanState τ} (h : Agrees s t) (k : Agrees t u) :
    Agrees s u :=
  ⟨k.globals.trans h.globals, k.code.trans h.code, k.memaddrs.trans h.memaddrs, k.be.trans h.be,
   k.ffi.trans h.ffi, k.base.trans h.base, k.top.trans h.top⟩

private theorem Agrees.eq {τ : Type} {s t : PanState τ} (h : Agrees s t) :
    t = {s with memory := t.memory, locals := t.locals, clock := t.clock} := by
  obtain ⟨g, c, d, b, f, ba, tp⟩ := h
  cases s; cases t
  simp_all

theorem address_address (p : Word) (i j : Nat) : address (address p i) j = address p (i + j) := by
  simp [address, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

private theorem mapped_at {τ : Type} {s : PanState τ} {b : Word} (hm : Mapped s b) (i : Nat)
    (hi : i < 25) : s.memaddrs (address b i) = true := hm ⟨i, hi⟩

private theorem eval_at {τ : Type} {s : PanState τ} {p : String} {b : Word}
    (hp : s.locals p = some (.word b)) (i : Nat) :
    eval s (at_ p i) = some (.word (address b i)) := by
  simp [at_, address, hp, word_op]

private theorem eval_load {τ : Type} {s : PanState τ} {p : String} {b : Word}
    (hp : s.locals p = some (.word b)) {i : Nat} (hm : s.memaddrs (address b i) = true) :
    eval s (load p i) = some (.word (s.memory (address b i))) := by
  simp [load, eval, eval_at hp, mem_load, hm]

private theorem evaluate_test {τ : Type} {s : PanState τ} {e : PExp} {P : Prop} [Decidable P]
    (he : eval s e = some (.word (if P then 1#64 else 0#64))) (a b : PStmt) :
    evaluate (.ite e a b) s = if P then evaluate a s else evaluate b s := by
  rw [evaluate_ite, he]
  by_cases h : P <;> simp [h]

private theorem evaluate_finish {τ : Type} (s : PanState τ) (v : Status) :
    evaluate (finish v) s = (.ret (.word v.code), empty_locals s) := by
  rw [finish, evaluate_ret]; rfl

private theorem evaluate_decWord {τ : Type} (v : String) (e : PExp) (body : PStmt) (s : PanState τ)
    {w : Word} (he : eval s e = some (.word w)) :
    evaluate (.dec v .One e body) s =
      ((evaluate body {s with locals := FUPDATE s.locals (v, .word w)}).1,
       {(evaluate body {s with locals := FUPDATE s.locals (v, .word w)}).2 with
          locals := res_var (evaluate body {s with locals := FUPDATE s.locals (v, .word w)}).2.locals
            (v, s.locals v)}) := by
  rw [evaluate_dec, he]
  simp only [shape_of_word, BEq.rfl, ite_true]

private theorem while_normal {τ : Type} {s t : PanState τ} {cond : PExp} {body : PStmt} {w : Word}
    (hc : eval s cond = some (.word w)) (hw : w ≠ 0#64) (hclk : s.clock ≠ 0)
    (hb : evaluate body (dec_clock s) = (.normal, t)) :
    evaluate (.while_ cond body) s = evaluate (.while_ cond body) t := by
  conv => lhs; rw [evaluate_while, hc]
  simp only [bne_iff_ne.mpr hw, ite_true, beq_eq_false_iff_ne.mpr hclk, Bool.false_eq_true,
    ite_false, hb]

private theorem while_ret {τ : Type} {s t : PanState τ} {cond : PExp} {body : PStmt} {w : Word}
    {v : PanVal} (hc : eval s cond = some (.word w)) (hw : w ≠ 0#64) (hclk : s.clock ≠ 0)
    (hb : evaluate body (dec_clock s) = (.ret v, t)) :
    evaluate (.while_ cond body) s = (.ret v, t) := by
  conv => lhs; rw [evaluate_while, hc]
  simp only [bne_iff_ne.mpr hw, ite_true, beq_eq_false_iff_ne.mpr hclk, Bool.false_eq_true,
    ite_false, hb]

private theorem while_done {τ : Type} {s : PanState τ} {cond : PExp} {body : PStmt}
    (hc : eval s cond = some (.word 0#64)) : evaluate (.while_ cond body) s = (.normal, s) := by
  rw [evaluate_while, hc]
  rfl

private theorem count_ne (n : Nat) (bound : n + 1 < 2^64) : BitVec.ofNat 64 (n+1) ≠ 0#64 := by
  intro h
  have e := congrArg BitVec.toNat h
  simp [Nat.mod_eq_of_lt bound] at e

private theorem count_pred (n : Nat) : BitVec.ofNat 64 (n+1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- Four-word records from `p` on, readable and apart from the workspace at `b`. -/
def Records {τ : Type} (s : PanState τ) (b : Word) : Word → List Digest → Prop
  | _, [] => True
  | p, d :: ds => (∀ i, i < 4 → s.memaddrs (address p i) = true ∧
      s.memory (address p i) = d.words.getD i 0 ∧ ∀ j : Fin 25, address p i ≠ address b j) ∧
    Records s b (address p 4) ds

private theorem Records.frame {τ : Type} {s t : PanState τ} {b : Word}
    (dm : t.memaddrs = s.memaddrs)
    (same : ∀ a, (∀ j : Fin 25, a ≠ address b j) → t.memory a = s.memory a) (ds : List Digest) :
    ∀ p, Records s b p ds → Records t b p ds := by
  induction ds with
  | nil => intro _ _; trivial
  | cons d ds ih =>
    rintro p ⟨h, rest⟩
    refine ⟨fun i hi => ?_, ih _ rest⟩
    obtain ⟨m, v, a⟩ := h i hi
    exact ⟨by rw [dm]; exact m, (same _ a).trans v, a⟩

private theorem quad_words (m : Word → Word) (p : Word) (i : Nat) (hi : i < 4) :
    (quad m p).words.getD i 0 = m (address p i) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

private theorem block_key (key msg : Digest) {i : Nat} (h : i < 4) :
    (key.words ++ msg.words ++ padWords).getD i 0 = key.words.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simp [Digest.words]; omega)]

private theorem block_msg (key msg : Digest) {i : Nat} (h1 : 4 ≤ i) (h2 : i < 8) :
    (key.words ++ msg.words ++ padWords).getD i 0 = msg.words.getD (i-4) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp [Digest.words]; omega),
    List.getElem?_append_left (by simp [Digest.words]; omega)]
  rfl

private theorem block_pad (key msg : Digest) {i : Nat} (h1 : 8 ≤ i) :
    (key.words ++ msg.words ++ padWords).getD i 0 = padWords.getD (i-8) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp [Digest.words]; omega),
    List.getElem?_append_right (by simp [Digest.words]; omega)]
  simp only [Digest.words, List.length_cons, List.length_nil]
  congr 2

private theorem eval_absorbField {τ : Type} {s : PanState τ} {b p : Word} {key msg : Digest}
    (hb : s.locals "state" = some (.word b)) (hp : s.locals "msg" = some (.word p))
    (hm : Mapped s b) (hk : quad s.memory b = key)
    (hq : ∀ i, i < 4 → s.memaddrs (address p i) = true ∧ s.memory (address p i) = msg.words.getD i 0)
    (i : Fin 25) :
    eval s (absorbField i) = some (.word (Keccak.lanes (linkInput key msg) i)) := by
  rw [linkInput_lane]
  have hi := i.isLt
  by_cases h4 : i.val < 4
  · have e := eval_load (i := i.val) hb (mapped_at hm _ hi)
    rw [← quad_words s.memory b _ h4, hk] at e
    rw [block_key key msg h4]
    simp [absorbField, h4, e, word_op, show i.val < 17 by omega]
  by_cases h8 : i.val < 8
  · have e := eval_load (i := i.val - 4) hp (hq _ (by omega)).1
    rw [(hq _ (by omega)).2] at e
    rw [block_msg key msg (Nat.le_of_not_lt h4) h8]
    simp [absorbField, h4, h8, e, word_op, show i.val < 17 by omega]
  by_cases h17 : i.val < 17
  · rw [block_pad key msg (Nat.le_of_not_lt h8)]
    simp [absorbField, h4, h8, h17]
  · have none : padWords[i.val - 8]? = none := List.getElem?_eq_none (by simp [padWords]; omega)
    simp [absorbField, h4, h8, h17, none]

private theorem seq_normal {τ : Type} {p q : PStmt} {a b : PanState τ}
    (h : evaluate p a = (.normal, b)) : evaluate (.seq p q) a = evaluate q b := by
  rw [evaluate_seq, h]
  rfl

private theorem advance_eval {τ : Type} (s : PanState τ) (p n : Word)
    (hp : s.locals "msg" = some (.word p)) (hn : s.locals "left" = some (.word n)) :
    evaluate advance s =
      (.normal, set_var "left" (.word (n-1#64)) (set_var "msg" (.word (address p 4)) s)) := by
  simp [advance, word, address, evaluate_seq, evaluate_assign, word_op, hp, hn,
    is_valid_value_local, set_kvar, set_var, FUPDATE]

/-- One link per remaining message, keyed by the tag so far, for any clock that suffices. -/
private theorem chainLoop_correct {τ : Type} (ms : List Digest) :
    ∀ (s : PanState τ) (key : Digest) (b p : Word), ms.length ≤ s.clock → ms.length < 2^63 →
    s.locals "state" = some (.word b) → s.locals "msg" = some (.word p) →
    s.locals "left" = some (.word (BitVec.ofNat 64 ms.length)) →
    Mapped s b → quad s.memory b = key → Records s b p ms →
    ∃ t, evaluate chainLoop s = (.normal, t) ∧ Agrees s t ∧ t.clock = s.clock - ms.length ∧
      t.locals "msg" = some (.word (address p (4*ms.length))) ∧
      t.locals "left" = some (.word 0#64) ∧
      (∀ x, x ≠ "msg" → x ≠ "left" → t.locals x = s.locals x) ∧
      quad t.memory b = ms.foldl mac key ∧
      ∀ a, (∀ j : Fin 25, a ≠ address b j) → t.memory a = s.memory a := by
  induction ms with
  | nil =>
    intro s key b p _ _ _ hp hn _ hk _
    refine ⟨s, while_done hn, Agrees.refl s, by simp, by simpa [address] using hp,
      by simpa using hn, fun _ _ _ => rfl, hk, fun _ _ => rfl⟩
  | cons m rest ih =>
    rintro s key b p fuel bound hb hp hn hm hk ⟨head, tail⟩
    simp only [List.length_cons] at fuel bound hn
    have hclk : s.clock ≠ 0 := by omega
    obtain ⟨mx, hx, rx, fx⟩ := storeFields_correct (dec_clock s) "state" b hb hm absorbField
      (Keccak.lanes (linkInput key m))
      (eval_absorbField hb hp hm hk fun i hi => ⟨(head i hi).1, (head i hi).2.1⟩)
    let sx := {dec_clock s with memory := mx}
    obtain ⟨mk, hk', rk, fk⟩ := Keccak.roundsThen_correct Cshake256.roundConstants sx "state"
      advance b hb hm (linkInput key m) rx
    let sk := {sx with memory := mk}
    let t := set_var "left" (.word (BitVec.ofNat 64 (rest.length+1) - 1#64))
      (set_var "msg" (.word (address p 4)) sk)
    have ha : evaluate advance sk = (.normal, t) := advance_eval sk p _ hp hn
    have hbody : evaluate (.seq absorbBlock (Keccak.roundsThen "state" advance Cshake256.roundConstants))
        (dec_clock s) = (.normal, t) := (seq_normal hx).trans (hk'.trans ha)
    have hf (a : Word) (h : ∀ j : Fin 25, a ≠ address b j) : t.memory a = s.memory a :=
      (fk a h).trans (fx a h)
    have r (i : Nat) (hi : i < 25) : mk (address b i) =
        Keccak.lanes (Cshake256.keccakF1600 (linkInput key m)) ⟨i, hi⟩ := rk ⟨i, hi⟩
    have key' : quad t.memory b = mac key m := by
      rw [mac_lanes]
      simp only [quad, t, sk, set_var]
      rw [r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide)]
      rfl
    obtain ⟨u, hu, au, cu, mu, lu, ou, qu, fu⟩ := ih t (mac key m) b (address p 4)
      (by simp [t, sk, sx, set_var, dec_clock]; omega) (by omega)
      (by simpa [t, sk, sx, set_var, dec_clock, FUPDATE] using hb) (by simp [t, set_var, FUPDATE])
      (by simp [t, set_var, FUPDATE, count_pred]) hm key'
      (Records.frame (s := s) (t := t) rfl hf rest _ tail)
    refine ⟨u, ?_, (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Agrees s t).trans au, ?_, ?_, lu,
      fun x h1 h2 => (ou x h1 h2).trans (by simp [t, sk, sx, set_var, dec_clock, FUPDATE, h1, h2]), ?_,
      fun a h => (fu a h).trans (hf a h)⟩
    · rw [chainLoop, while_normal (by rw [eval_lvar, hn]) (count_ne _ (by omega)) hclk hbody]
      exact hu
    · rw [cu]; simp [t, sk, sx, set_var, dec_clock]; omega
    · rw [mu, address_address]; congr 3; simp; omega
    · rw [qu]; rfl

/-- Workspace zero, all else as in `m`: the memory after every complete verdict. -/
private theorem wipe_eq {m m' : Word → Word} {b : Word} (zero : ∀ j : Fin 25, m' (address b j) = 0)
    (same : ∀ a, (∀ j : Fin 25, a ≠ address b j) → m' a = m a) : m' = wipe m b := by
  funext a
  unfold wipe
  split
  · rename_i ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    exact zero j
  · rename_i ha
    exact same a fun j hj => ha (List.mem_map.mpr ⟨j, List.mem_finRange j, hj.symm⟩)

private theorem eval_tagDiff {τ : Type} {s : PanState τ} {b q : Word}
    (hb : s.locals "state" = some (.word b)) (hq : s.locals "msg" = some (.word q)) (hm : Mapped s b)
    (hqm : ∀ i, i < 4 → s.memaddrs (address q i) = true) :
    ∃ d, eval s tagDiff = some (.word d) ∧ (d = 0#64 ↔ quad s.memory b = quad s.memory q) := by
  have l (i : Nat) (hi : i < 4) : eval s (limbDiff i) =
      some (.word (s.memory (address b i) ^^^ s.memory (address q i))) := by
    simp [limbDiff, eval_load (i := i) hb (mapped_at hm i (by omega)), eval_load (i := i) hq (hqm i hi),
      word_op]
  refine ⟨(((s.memory (address b 0) ^^^ s.memory (address q 0)) |||
      (s.memory (address b 1) ^^^ s.memory (address q 1))) |||
      (s.memory (address b 2) ^^^ s.memory (address q 2))) |||
      (s.memory (address b 3) ^^^ s.memory (address q 3)), ?_, ?_⟩
  · simp [tagDiff, l 0 (by decide), l 1 (by decide), l 2 (by decide), l 3 (by decide), word_op]
  · simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, quad, Digest.mk.injEq, and_assoc]

private theorem not_ult (a b : Word) : (!(BitVec.ult a b)) = decide (b ≤ a) := by
  by_cases h : a.toNat < b.toNat <;> simp [BitVec.ult_eq_decide, BitVec.le_def, h] <;> omega

private theorem and2 (a b : Word) : word_op .And [a, b] = some (a &&& b) := by
  simp only [word_op, List.foldr_cons, List.foldr_nil, BitVec.not_zero, BitVec.and_allOnes]

private theorem caveatCheck_eval {τ : Type} {s : PanState τ} {p n : Word} {c : Caveat} {r : Request}
    (hc : s.locals "cav" = some (.word p)) (hn : s.locals "left" = some (.word n))
    (ho : s.locals "op" = some (.word r.op)) (hs : s.locals "seat" = some (.word r.seat))
    (hsp : s.locals "spend" = some (.word r.spend)) (he : s.locals "epoch" = some (.word r.epoch))
    (hm : ∀ i, i < 4 → s.memaddrs (address p i) = true ∧ s.memory (address p i) = c.body.words.getD i 0) :
    evaluate caveatCheck s = if c.verdict r = .accepted
      then (.normal, set_var "left" (.word (n - 1#64)) (set_var "cav" (.word (address p 4)) s))
      else (.ret (.word (c.verdict r).code), empty_locals s) := by
  have l (i : Nat) (hi : i < 4) : eval s (load "cav" i) = some (.word (c.body.words.getD i 0)) := by
    rw [eval_load hc (hm i hi).1, (hm i hi).2]
  have l0 := l 0 (by decide)
  have l1 := l 1 (by decide)
  have l2 := l 2 (by decide)
  have l3 := l 3 (by decide)
  simp only [Caveat.body, Digest.words, List.getD_cons_zero, List.getD_cons_succ] at l0 l1 l2 l3
  have c1 : eval s (.cmp .Equal (.binop .And [load "cav" 0, .lvar "op"]) (.lvar "op")) =
      some (.word (if c.opMask &&& r.op = r.op then 1#64 else 0#64)) := by
    simp [l0, ho, and2, word_cmp]
  have c2 : eval s (.cmp .Equal (load "cav" 1) (.lvar "seat")) =
      some (.word (if c.seat = r.seat then 1#64 else 0#64)) := by
    simp [l1, hs, word_cmp]
  have c3 : eval s (.cmp .NotLower (load "cav" 2) (.lvar "spend")) =
      some (.word (if r.spend ≤ c.maxSpend then 1#64 else 0#64)) := by
    simp [l2, hsp, word_cmp, not_ult]
  have c4 : eval s (.cmp .NotLower (.lvar "epoch") (load "cav" 3)) =
      some (.word (if c.minEpoch ≤ r.epoch then 1#64 else 0#64)) := by
    simp [l3, he, word_cmp, not_ult]
  have next : evaluate nextCaveat s =
      (.normal, set_var "left" (.word (n - 1#64)) (set_var "cav" (.word (address p 4)) s)) := by
    simp [nextCaveat, word, address, evaluate_seq, evaluate_assign, word_op, hc, hn,
      is_valid_value_local, set_kvar, set_var, FUPDATE]
  delta caveatCheck
  rw [evaluate_test c1, evaluate_test c2, evaluate_test c3, evaluate_test c4, next,
    evaluate_finish, evaluate_finish, evaluate_finish, evaluate_finish]
  unfold Caveat.verdict
  by_cases h1 : c.opMask &&& r.op = r.op <;> by_cases h2 : c.seat = r.seat <;>
    by_cases h3 : r.spend ≤ c.maxSpend <;> by_cases h4 : c.minEpoch ≤ r.epoch <;>
    simp [h1, h2, h3, h4]

/-- The caveat walk returns the first refusal, or falls through when every caveat admits. -/
private theorem caveatLoop_correct {τ : Type} (r : Request) (b : Word) (cs : List Caveat) :
    ∀ (s : PanState τ) (p : Word), cs.length ≤ s.clock → cs.length < 2^63 →
    s.locals "cav" = some (.word p) → s.locals "left" = some (.word (BitVec.ofNat 64 cs.length)) →
    s.locals "op" = some (.word r.op) → s.locals "seat" = some (.word r.seat) →
    s.locals "spend" = some (.word r.spend) → s.locals "epoch" = some (.word r.epoch) →
    Records s b p (cs.map Caveat.body) →
    ∃ t, evaluate caveatLoop s =
        ((if admit r cs = .accepted then .normal else .ret (.word (admit r cs).code)), t) ∧
      Agrees s t ∧ t.memory = s.memory := by
  induction cs with
  | nil =>
    intro s p _ _ _ hn _ _ _ _ _
    exact ⟨s, by rw [caveatLoop, while_done (cond := .lvar "left") hn]; rfl, Agrees.refl s, rfl⟩
  | cons c rest ih =>
    rintro s p fuel bound hp hn ho hs hsp he ⟨head, tail⟩
    simp only [List.length_cons] at fuel bound hn
    have hclk : s.clock ≠ 0 := by omega
    have hcheck := caveatCheck_eval (s := dec_clock s) (c := c) (r := r) hp hn ho hs hsp he
      fun i hi => ⟨(head i hi).1, (head i hi).2.1⟩
    by_cases hv : c.verdict r = .accepted
    · simp only [hv, ↓reduceIte] at hcheck
      let t := set_var "left" (.word (BitVec.ofNat 64 (rest.length+1) - 1#64))
        (set_var "cav" (.word (address p 4)) (dec_clock s))
      obtain ⟨u, hu, au, mu⟩ := ih t (address p 4) (by simp [t, set_var, dec_clock]; omega) (by omega)
        (by simp [t, set_var, FUPDATE]) (by simp [t, set_var, FUPDATE, count_pred])
        (by simpa [t, set_var, dec_clock, FUPDATE] using ho)
        (by simpa [t, set_var, dec_clock, FUPDATE] using hs)
        (by simpa [t, set_var, dec_clock, FUPDATE] using hsp)
        (by simpa [t, set_var, dec_clock, FUPDATE] using he)
        (Records.frame (s := s) (t := t) rfl (fun _ _ => rfl) _ _ tail)
      refine ⟨u, ?_, (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Agrees s t).trans au, mu⟩
      rw [caveatLoop, while_normal (by rw [eval_lvar, hn]) (count_ne _ (by omega)) hclk hcheck]
      simp only [admit, hv, ↓reduceIte]
      exact hu
    · simp only [hv, ↓reduceIte] at hcheck
      refine ⟨empty_locals (dec_clock s), ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      rw [caveatLoop, while_ret (by rw [eval_lvar, hn]) (count_ne _ (by omega)) hclk hcheck]
      simp [admit, hv]

theorem readCaveats_length (m : Word → Word) (n : Nat) : ∀ p, (readCaveats m p n).length = n := by
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro p; simp [readCaveats, ih]

private theorem records_read {τ : Type} (s : PanState τ) (b : Word) (n : Nat) :
    ∀ p, (∀ i, i < 4*n → s.memaddrs (address p i) = true ∧ ∀ j : Fin 25, address p i ≠ address b j) →
    Records s b p ((readCaveats s.memory p n).map Caveat.body) := by
  induction n with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro p hp
    refine ⟨fun i hi => ⟨(hp i (by omega)).1, ?_, (hp i (by omega)).2⟩, ih _ fun i hi => ?_⟩
    · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rfl
    · rw [address_address]
      exact hp (4 + i) (by omega)

/-- The exported function's arguments, the memory they reach and enough fuel for any count. -/
structure Frame {τ : Type} (s : PanState τ) (t c w : Word) : Prop where
  token : s.locals "token" = some (.word t)
  count : s.locals "count" = some (.word c)
  state : s.locals "state" = some (.word w)
  workspace : Mapped s w
  mapped : c.toNat ≤ maxCaveats → ∀ i, i < tokenWords c.toNat → s.memaddrs (address t i) = true
  apart : c.toNat ≤ maxCaveats → ∀ i, i < tokenWords c.toNat → ∀ j : Fin 25, address t i ≠ address w j
  fuel : 2 * maxCaveats + 1 ≤ s.clock

/-- Returns `code` in a state that agrees with `s` and holds memory `M`. -/
private def Returns {τ : Type} (s : PanState τ) (code : Word) (M : Word → Word)
    (r : PanResult × PanState τ) : Prop :=
  r.1 = .ret (.word code) ∧ Agrees s r.2 ∧ r.2.memory = M

private theorem Returns.dec {τ : Type} {s a : PanState τ} {v : String} {e : PExp} {body : PStmt}
    {w code : Word} {M : Word → Word} (he : eval a e = some (.word w))
    (hb : Returns s code M (evaluate body {a with locals := FUPDATE a.locals (v, .word w)})) :
    Returns s code M (evaluate (.dec v .One e body) a) := by
  rw [evaluate_decWord v e body a he]
  exact ⟨hb.1, ⟨hb.2.1.globals, hb.2.1.code, hb.2.1.memaddrs, hb.2.1.be, hb.2.1.ffi, hb.2.1.base,
    hb.2.1.top⟩, hb.2.2⟩

private theorem Returns.seq {τ : Type} {s a a' : PanState τ} {p q : PStmt} {code : Word}
    {M : Word → Word} (hp : evaluate p a = (.normal, a')) (hq : Returns s code M (evaluate q a')) :
    Returns s code M (evaluate (.seq p q) a) := by
  rw [seq_normal hp]
  exact hq

private theorem Returns.finish {τ : Type} {s a : PanState τ} (v : Status) (ag : Agrees s a) :
    Returns s v.code a.memory (evaluate (finish v) a) := by
  rw [evaluate_finish]
  exact ⟨rfl, ⟨ag.globals, ag.code, ag.memaddrs, ag.be, ag.ffi, ag.base, ag.top⟩, rfl⟩

private theorem seq_ret {τ : Type} {p q : PStmt} {a b : PanState τ} {v : PanVal}
    (h : evaluate p a = (.ret v, b)) : evaluate (.seq p q) a = (.ret v, b) := by
  rw [evaluate_seq, h]
  rfl

private theorem evaluate_lassign {τ : Type} {s : PanState τ} {x : String} {e : PExp} {w old : Word}
    (he : eval s e = some (.word w)) (hx : s.locals x = some (.word old)) :
    evaluate (.lassign x e) s = (.normal, set_var x (.word w) s) := by
  simp [evaluate_assign, he, is_valid_value_local, hx, set_kvar]

private theorem wipe_apart {m : Word → Word} {b a : Word} (ha : ∀ j : Fin 25, a ≠ address b j) :
    wipe m b a = m a := by
  unfold wipe
  split
  · rename_i hm
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hm
    exact absurd hj.symm (ha j)
  · rfl

/-- The caveat walk and the acceptance after it, from any state with the request in locals. -/
private theorem admit_returns {τ : Type} {s a : PanState τ} {r : Request} {b p : Word}
    {cs : List Caveat} {M : Word → Word} (fuel : cs.length ≤ a.clock) (bound : cs.length < 2^63)
    (hp : a.locals "cav" = some (.word p))
    (hn : a.locals "left" = some (.word (BitVec.ofNat 64 cs.length)))
    (ho : a.locals "op" = some (.word r.op)) (hs : a.locals "seat" = some (.word r.seat))
    (hsp : a.locals "spend" = some (.word r.spend)) (he : a.locals "epoch" = some (.word r.epoch))
    (rec : Records a b p (cs.map Caveat.body)) (ag : Agrees s a) (mem : a.memory = M) :
    Returns s (admit r cs).code M (evaluate (.seq caveatLoop (finish .accepted)) a) := by
  obtain ⟨w, hw, aw, mw⟩ := caveatLoop_correct r b cs a p fuel bound hp hn ho hs hsp he rec
  by_cases hv : admit r cs = .accepted
  · simp only [hv, ↓reduceIte] at hw
    rw [seq_normal hw, hv, ← mem, ← mw]
    exact Returns.finish .accepted (ag.trans aw)
  · simp only [hv, ↓reduceIte] at hw
    rw [seq_ret hw]
    exact ⟨rfl, ag.trans aw, mw.trans mem⟩

private theorem verifyBody_correct {τ : Type} {s : PanState τ} {token count state : Word}
    (h : Frame s token count state) (hn : count.toNat ≤ maxCaveats) :
    Returns s (verifyMacaroon (readToken s.memory token count.toNat)
        (readRequest s.memory token count.toNat)).code (wipe s.memory state)
      (evaluate verifyBody s) := by
  obtain ⟨n, hN⟩ : ∃ n, count.toNat = n := ⟨_, rfl⟩
  rw [hN] at hn ⊢
  have hc : count = BitVec.ofNat 64 n := by rw [← hN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have mapped := h.mapped (hN ▸ hn)
  have apart := h.apart (hN ▸ hn)
  rw [hN] at mapped apart
  have bound : n ≤ 8 := hn
  have fuel : 17 ≤ s.clock := h.fuel
  simp only [tokenWords] at mapped apart
  let T := readToken s.memory token n
  let R := readRequest s.memory token n
  -- The root key becomes the first key.
  obtain ⟨m1, e1, k1, f1⟩ := storeFields_correct s "state" state h.state h.workspace
    (fun i => if i.val < 4 then load "token" i.val else .const 0)
    (fun i => if i.val < 4 then s.memory (address token i.val) else 0) (fun i => by
      by_cases hi : i.val < 4
      · simp only [hi, ↓reduceIte]
        exact eval_load h.token (mapped _ (by omega))
      · simp only [hi, ↓reduceIte]
        rfl)
  let s1 := {s with memory := m1}
  have root : quad m1 state = T.rootKey := by
    have r (i : Nat) (hi : i < 4) : m1 (address state i) = s.memory (address token i) := by
      have := k1 ⟨i, by omega⟩
      simpa [hi] using this
    simp only [quad, T, readToken, r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide)]
  -- Message records: the nonce, then the caveat bodies.
  let cs := readCaveats s.memory (address token 8) n
  let ms := T.nonce :: cs.map Caveat.body
  have msLen : ms.length = n + 1 := by simp [ms, cs, readCaveats_length]
  have rec0 : Records s state (address token 4) ms := by
    refine ⟨fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [address_address]; exact mapped _ (by omega)
    · exact (quad_words _ _ _ hi).symm
    · rw [address_address]; exact apart _ (by omega)
    · rw [address_address]
      exact records_read s state n _ fun i hi => by
        rw [address_address]; exact ⟨mapped _ (by omega), apart _ (by omega)⟩
  -- Pointers after the chain.
  let q := address token (8 + 4*n)
  have hq : address (address token 4) (4 * ms.length) = q := by
    rw [address_address, msLen]; simp only [q]; congr 1; omega
  have qa (i : Nat) : address q i = address token (8 + 4*n + i) := address_address _ _ _
  have keep1 (a : Word) (ha : ∀ j : Fin 25, a ≠ address state j) : s1.memory a = s.memory a := f1 a ha
  apply Returns.seq e1
  apply Returns.dec (eval_at (s := s1) (b := token) h.token 4)
  apply Returns.dec (w := BitVec.ofNat 64 (n+1)) (by
    simp [word, word_op, FUPDATE, s1, h.count, hc, BitVec.ofNat_add])
  -- The chain.
  let s3 : PanState τ := {{s1 with locals := FUPDATE s1.locals ("msg", .word (address token 4))} with
    locals := FUPDATE (FUPDATE s1.locals ("msg", .word (address token 4))) ("left", .word (BitVec.ofNat 64 (n+1)))}
  obtain ⟨u, hu, au, cu, mu, lu, ou, qu, fu⟩ := chainLoop_correct ms s3 T.rootKey state (address token 4)
    (by simp [s3, s1, msLen]; omega) (by rw [msLen]; omega)
    (by simp [s3, s1, FUPDATE, h.state]) (by simp [s3, FUPDATE])
    (by simp [s3, FUPDATE, msLen]) h.workspace root
    (Records.frame (s := s) (t := s3) rfl keep1 ms _ rec0)
  apply Returns.seq hu
  rw [hq] at mu
  have keepU (a : Word) (ha : ∀ j : Fin 25, a ≠ address state j) : u.memory a = s.memory a :=
    (fu a ha).trans (keep1 a ha)
  have uState : u.locals "state" = some (.word state) := by
    rw [ou _ (by decide) (by decide)]; simp [s3, s1, FUPDATE, h.state]
  have uMapped : Mapped u state := fun j => by rw [au.memaddrs]; exact h.workspace j
  have qMapped (i : Nat) (hi : i < 8) : u.memaddrs (address q i) = true := by
    rw [au.memaddrs, qa]; exact mapped _ (by omega)
  have qKeep (i : Nat) (hi : i < 8) : u.memory (address q i) = s.memory (address q i) :=
    keepU _ fun j => by rw [qa]; exact apart _ (by omega) j
  have claimed : quad u.memory q = T.claimed := by
    simp only [quad, T, readToken, qKeep 0 (by decide), qKeep 1 (by decide), qKeep 2 (by decide),
      qKeep 3 (by decide)]
    rfl
  have tagged : quad u.memory state = T.tag := by
    rw [qu]; rfl
  obtain ⟨d, ed, hd⟩ := eval_tagDiff uState mu uMapped fun i hi => qMapped i (by omega)
  rw [claimed, tagged] at hd
  apply Returns.dec ed
  -- The scrub.
  let u2 := {u with locals := FUPDATE u.locals ("diff", .word d)}
  obtain ⟨m4, e4, z4, f4⟩ := storeFields_correct u2 "state" state
    (by simpa [u2, FUPDATE] using uState) uMapped (fun _ => .const 0) (fun _ => 0) (fun _ => rfl)
  have wiped : m4 = wipe s.memory state := wipe_eq z4 fun a ha => (f4 a ha).trans (keepU a ha)
  apply Returns.seq e4
  let u3 := {u2 with memory := m4}
  have agU3 : Agrees s u3 :=
    (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Agrees s s3).trans (au.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have cond : eval u3 (.cmp .Equal (.lvar "diff") (word 0)) = some (.word (if d = 0#64 then 1#64 else 0#64)) := by
    simp [u3, u2, FUPDATE, word, word_cmp]
  rw [evaluate_test cond]
  have verdict : verifyMacaroon T R = if T.tag = T.claimed then admit R cs else .forged := by
    simp [verifyMacaroon, T, readToken, readCaveats_length, bound, maxCaveats, cs]
  by_cases hdz : d = 0#64
  · simp only [hdz, ↓reduceIte]
    have ht : T.tag = T.claimed := hd.mp hdz
    change Returns s (verifyMacaroon T R).code (wipe s.memory state) _
    rw [verdict]
    simp only [ht, ↓reduceIte]
    -- Request words follow the claimed tag.
    have qKeep4 (i : Nat) (hi : i < 4) : m4 (address q (4+i)) = s.memory (address q (4+i)) := by
      rw [wiped]
      exact wipe_apart fun j => by rw [qa]; exact apart _ (by omega) j
    have req (a : PanState τ) (hmsg : a.locals "msg" = some (.word q)) (hmem : a.memory = m4)
        (hdm : a.memaddrs = s.memaddrs) (i : Nat) (hi : i < 4) : eval a (load "msg" (4+i)) =
          some (.word (s.memory (address (address token (12 + 4*n)) i))) := by
      rw [eval_load hmsg (by rw [hdm, qa]; exact mapped _ (by omega)), hmem, qKeep4 i hi, qa,
        address_address, show 8 + 4*n + (4+i) = 12 + 4*n + i by omega]
    have uMsg : u3.locals "msg" = some (.word q) := by simpa [u3, u2, FUPDATE] using mu
    have uDm : u3.memaddrs = s.memaddrs := au.memaddrs
    apply Returns.dec (req _ (by simpa [FUPDATE] using uMsg) (by rfl) (by exact uDm) 0 (by decide))
    apply Returns.dec (req _ (by simpa [FUPDATE] using uMsg) (by rfl) (by exact uDm) 1 (by decide))
    apply Returns.dec (req _ (by simpa [FUPDATE] using uMsg) (by rfl) (by exact uDm) 2 (by decide))
    apply Returns.dec (req _ (by simpa [FUPDATE] using uMsg) (by rfl) (by exact uDm) 3 (by decide))
    apply Returns.dec (eval_at (b := token) (by simp [u3, u2, FUPDATE, ou, s3, s1, h.token]) 8)
    have recS : Records s state (address token 8) (cs.map Caveat.body) :=
      records_read s state n _ fun i hi => by
        rw [address_address]; exact ⟨mapped _ (by omega), apart _ (by omega)⟩
    apply Returns.seq (evaluate_lassign (w := count) (old := 0#64)
      (by simp [u3, u2, FUPDATE, ou, s3, s1, h.count]) (by simp [u3, u2, FUPDATE, lu]))
    apply admit_returns (r := R) (b := state) (p := address token 8) (cs := cs)
    · simp [set_var, u3, u2, cu, s3, s1, msLen, cs, readCaveats_length]; omega
    · simp [cs, readCaveats_length]; omega
    · simp [set_var, FUPDATE]
    · simp [set_var, FUPDATE, cs, readCaveats_length, hc]
    · simp [set_var, FUPDATE, R, readRequest, quad]
    · simp [set_var, FUPDATE, R, readRequest, quad]
    · simp [set_var, FUPDATE, R, readRequest, quad]
    · simp [set_var, FUPDATE, R, readRequest, quad]
    · refine Records.frame (s := s) (by exact uDm) (fun a ha => ?_) _ _ recS
      · show m4 a = s.memory a
        rw [wiped]
        exact wipe_apart ha
    · exact agU3.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact wiped
  · simp only [hdz, ↓reduceIte]
    have ht : T.tag ≠ T.claimed := fun e => hdz (hd.mpr e)
    change Returns s (verifyMacaroon T R).code (wipe s.memory state) _
    rw [verdict]
    simp only [ht, ↓reduceIte]
    rw [← wiped]
    exact Returns.finish .forged agU3

/-- Exact return, memory and machine frame of the exported function, for every count, mapped
    token and workspace, and the fuel of eight caveats. Only locals and clock are left free. -/
theorem pancakeMacaroonVerify_correct {τ : Type} {s : PanState τ} {t c w : Word} (h : Frame s t c w) :
    let n := c.toNat
    let v := verifyMacaroon (readToken s.memory t n) (readRequest s.memory t n)
    ∃ u, evaluate kernel.body s = (.ret (.word v.code), u) ∧
      u = {s with memory := if n ≤ maxCaveats then wipe s.memory w else s.memory,
                  locals := u.locals, clock := u.clock} := by
  intro n v
  have lower : BitVec.ult c (BitVec.ofNat 64 (maxCaveats + 1)) = decide (n ≤ maxCaveats) := by
    rw [BitVec.ult_eq_decide]
    simp only [maxCaveats, n, BitVec.toNat_ofNat]
    exact decide_eq_decide.mpr (by omega)
  have cond : eval s (.cmp .Lower (.lvar "count") (word (maxCaveats + 1))) =
      some (.word (if n ≤ maxCaveats then 1#64 else 0#64)) := by
    simp [h.count, word, word_cmp, lower]
  by_cases hn : n ≤ maxCaveats
  · obtain ⟨ret, ag, mem⟩ := verifyBody_correct h hn
    refine ⟨(evaluate verifyBody s).2, ?_, ?_⟩
    · change evaluate (.ite _ verifyBody (finish .malformed)) s = _
      rw [evaluate_test cond]
      simp only [hn, ↓reduceIte]
      exact Prod.ext ret rfl
    · simp only [hn, ↓reduceIte]
      rw [← mem]
      exact ag.eq
  · refine ⟨empty_locals s, ?_, ?_⟩
    · change evaluate (.ite _ verifyBody (finish .malformed)) s = _
      rw [evaluate_test cond]
      simp only [hn, ↓reduceIte]
      have malformed : v = .malformed := by
        simp [v, verifyMacaroon, readToken, readCaveats_length, hn]
      rw [malformed, evaluate_finish]
    · simp only [hn, ↓reduceIte]
      rfl

/-- No word outside the 25-word workspace changes: token, request and all other memory. -/
theorem pancakeMacaroonVerify_frame {τ : Type} {s : PanState τ} {t c w : Word} (h : Frame s t c w)
    (a : Word) (away : ∀ j : Fin 25, a ≠ address w j) :
    (evaluate kernel.body s).2.memory a = s.memory a := by
  obtain ⟨u, hu, hs⟩ := pancakeMacaroonVerify_correct h
  rw [hu, hs]
  dsimp only
  split
  · exact wipe_apart away
  · rfl

/-- Whatever the verdict, a well-formed call leaves the workspace zero: all 25 caller-provided
    workspace words are cleared, including the four derived tag limbs. -/
theorem pancakeMacaroonVerify_scrubs {τ : Type} {s : PanState τ} {t c w : Word} (h : Frame s t c w)
    (hn : c.toNat ≤ maxCaveats) (j : Fin 25) :
    (evaluate kernel.body s).2.memory (address w j) = 0 := by
  obtain ⟨u, hu, hs⟩ := pancakeMacaroonVerify_correct h
  rw [hu, hs]
  dsimp only
  simp only [hn, ↓reduceIte]
  unfold wipe
  simp only [List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, ↓reduceIte]

/-- The function returns zero exactly when the token verifies for the request. -/
theorem pancakeMacaroonVerify_accepts_iff {τ : Type} {s : PanState τ} {t c w : Word}
    (h : Frame s t c w) :
    (evaluate kernel.body s).1 = .ret (.word 0) ↔
      verifyMacaroon (readToken s.memory t c.toNat) (readRequest s.memory t c.toNat) = .accepted := by
  obtain ⟨u, hu, -⟩ := pancakeMacaroonVerify_correct h
  rw [hu]
  generalize verifyMacaroon (readToken s.memory t c.toNat) (readRequest s.memory t c.toNat) = v
  cases v <;> simp [Status.code]

end Obend.Lower.Pancake.Macaroon
