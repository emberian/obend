module
public import Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer

/-! A serialized custody transition over caller-owned word buffers. The native
caller provisions the genesis, owns the state exclusively during a call, and
supplies the outcome of persistence. The checked update covers one epoch and
four digest limbs. Return clears callee locals in PanSem. -/

public section
namespace Obend.Lower.Pancake.BeltLatch
open WordBuffer (address)
set_option autoImplicit false

structure Digest where
  w0 : Word
  w1 : Word
  w2 : Word
  w3 : Word
  deriving DecidableEq, Repr

structure State where
  initialized : Word
  genesis : Digest
  epoch : Word
  digest : Digest
  policy : Digest
  deriving DecidableEq, Repr

structure Request where
  genesis : Digest
  parentEpoch : Word
  nextEpoch : Word
  parent : Digest
  nextDigest : Digest
  policy : Digest
  persistAck : Word
  deriving DecidableEq, Repr

inductive Status where
  | accepted | genesisMismatch | staleParent | nonIncreasing | parentFork | policyDrift | missingAck
  deriving DecidableEq, Repr

def Status.code : Status → Word
  | .accepted => 0 | .genesisMismatch => 1 | .staleParent => 2 | .nonIncreasing => 3
  | .parentFork => 4 | .policyDrift => 5 | .missingAck => 6

/-- Both flags are canonical ABI words. Provisioning the genesis is external to this transition. -/
def stepBeltLatch (s : State) (r : Request) : Status × State :=
  if s.initialized = 1 ∧ s.genesis = r.genesis then
    if s.epoch = r.parentEpoch then
      if s.epoch < r.nextEpoch then
        if s.digest = r.parent then
          if s.policy = r.policy then
            if r.persistAck = 1 then (.accepted, {s with epoch := r.nextEpoch, digest := r.nextDigest})
            else (.missingAck, s)
          else (.policyDrift, s)
        else (.parentFork, s)
      else (.nonIncreasing, s)
    else (.staleParent, s)
  else (.genesisMismatch, s)

private def digestAt (w : Nat → Word) (i : Nat) : Digest :=
  ⟨w i, w (i+1), w (i+2), w (i+3)⟩

def readState (m : Word → Word) (b : Word) : State :=
  let w i := m (address b i)
  ⟨w 0, digestAt w 1, w 5, digestAt w 6, digestAt w 10⟩

def readRequest (m : Word → Word) (b : Word) : Request :=
  let w i := m (address b i)
  ⟨digestAt w 0, w 4, w 5, digestAt w 6, digestAt w 10, digestAt w 14, w 18⟩

structure Mapped {τ : Type} (s : PanState τ) (p : String) (b : Word) (n : Nat) : Prop where
  ptr : s.locals p = some (.word b)
  slots : ∀ i, i < n → s.memaddrs (address b i) = true

private def addr (p : String) (i : Nat) : PExp :=
  .binop .Add [.lvar p, .const (BitVec.ofNat 64 (8*i))]
private def load (p : String) (i : Nat) : PExp := .load .One (addr p i)
private abbrev cur := load "current"
private abbrev req := load "candidate"
private def finish (v : Status) : PStmt := .ret (.const v.code)
private def eqGuard (a b : PExp) (yes no : PStmt) := PStmt.ite (.cmp .Equal a b) yes no

def digestGuard (i j : Nat) (yes no : PStmt) : PStmt :=
  eqGuard (cur i) (req j)
    (eqGuard (cur (i+1)) (req (j+1))
      (eqGuard (cur (i+2)) (req (j+2))
        (eqGuard (cur (i+3)) (req (j+3)) yes no) no) no) no

def epochTest : PExp := .cmp .Lower (cur 5) (req 5)

/-- Read the entire new head before the single structured store. -/
def storeHead : PStmt := .store (addr "current" 5)
  (.rstruct [req 5, req 10, req 11, req 12, req 13])

def commitIfAcknowledged : PStmt :=
  eqGuard (req 18) (.const 1) (.seq storeHead (finish .accepted)) (finish .missingAck)

def kernel : PFun :=
  ⟨"stepBeltLatch", [("current", .One), ("candidate", .One)],
    eqGuard (cur 0) (.const 1)
      (digestGuard 1 0
        (eqGuard (cur 5) (req 4)
          (.ite epochTest
            (digestGuard 6 6
              (digestGuard 10 14 commitIfAcknowledged (finish .policyDrift))
              (finish .parentFork))
            (finish .nonIncreasing))
          (finish .staleParent))
        (finish .genesisMismatch))
      (finish .genesisMismatch), true⟩

private theorem eval_addr {τ p b n} {s : PanState τ} (h : Mapped s p b n) (i : Nat) :
    eval s (addr p i) = some (.word (address b i)) := by
  simp [addr, address, h.ptr, word_op]

private theorem eval_load {τ p b n} {s : PanState τ} (h : Mapped s p b n) (i : Nat) (hi : i < n) :
    eval s (load p i) = some (.word (s.memory (address b i))) := by
  simp [load, eval, eval_addr h, mem_load, h.slots i hi]

private theorem eval_finish {τ} (s : PanState τ) (v : Status) :
    evaluate (finish v) s = (.ret (.word v.code), empty_locals s) := by
  rw [finish, evaluate_ret]; rfl

private theorem eval_eqGuard {τ} {s : PanState τ} {a b : PExp} {x y : Word}
    (ha : eval s a = some (.word x)) (hb : eval s b = some (.word y)) (yes no : PStmt) :
    evaluate (eqGuard a b yes no) s = if x = y then evaluate yes s else evaluate no s := by
  by_cases h : x = y <;> simp [eqGuard, evaluate_ite, ha, hb, word_cmp, h]

private theorem eval_digestGuard {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19)
    (i j : Nat) (hi : i+3 < 14) (hj : j+3 < 19) (yes no : PStmt) :
    evaluate (digestGuard i j yes no) s =
      if digestAt (fun k => s.memory (address b k)) i = digestAt (fun k => s.memory (address c k)) j
      then evaluate yes s else evaluate no s := by
  simp only [digestGuard, cur, req,
    eval_eqGuard (eval_load hs i (by omega)) (eval_load hr j (by omega)),
    eval_eqGuard (eval_load hs (i+1) (by omega)) (eval_load hr (j+1) (by omega)),
    eval_eqGuard (eval_load hs (i+2) (by omega)) (eval_load hr (j+2) (by omega)),
    eval_eqGuard (eval_load hs (i+3) (by omega)) (eval_load hr (j+3) (by omega))]
  simp only [digestAt, Digest.mk.injEq]
  repeat' split <;> simp_all

/-- Complete memory image after the five-word commit, including all caller-owned words. -/
def install (m : Word → Word) (b : Word) (r : Request) : Word → Word :=
  let m := UPDATE (address b 5) r.nextEpoch m
  let m := UPDATE (address b 6) r.nextDigest.w0 m
  let m := UPDATE (address b 7) r.nextDigest.w1 m
  let m := UPDATE (address b 8) r.nextDigest.w2 m
  UPDATE (address b 9) r.nextDigest.w3 m

private theorem eval_storeHead {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19) :
    evaluate storeHead s = (.normal, {s with memory := install s.memory b (readRequest s.memory c)}) := by
  have succ (i : Nat) : address b i + 8#64 = address b (i+1) := by
    simp [address, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  simp (disch := decide) only [storeHead, evaluate_store, eval_addr hs, eval_rstruct, evalList_cons, evalList_nil,
    req, eval_load hr, Option.map_some, flatten, flatten_list, List.cons_append,
    List.nil_append, mem_stores, mem_store, succ, hs.slots, ite_true]
  rfl

private theorem eval_epoch {τ b c} {s : PanState τ} (hs : Mapped s "current" b 14)
    (hr : Mapped s "candidate" c 19) (yes no : PStmt) :
    evaluate (.ite epochTest yes no) s =
      if (readState s.memory b).epoch < (readRequest s.memory c).nextEpoch
      then evaluate yes s else evaluate no s := by
  simp only [epochTest, evaluate_ite, eval_cmp, cur, req, eval_load hs 5 (by decide),
    eval_load hr 5 (by decide), word_cmp, readState, readRequest]
  by_cases h : s.memory (address b 5) < s.memory (address c 5) <;> simp_all [BitVec.ult, BitVec.lt_def] <;> omega

/-- Exact return, memory and machine frame for every mapped pair of buffers and any clock.
    In particular all reads use the incoming snapshot, even for overlapping views. -/
theorem pancakeBeltLatch_correct {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19) :
    let r := readRequest s.memory c
    let v := (stepBeltLatch (readState s.memory b) r).1
    let m := if v = .accepted then install s.memory b r else s.memory
    evaluate kernel.body s = (.ret (.word v.code), empty_locals {s with memory := m}) := by
  have commit := eval_storeHead hs hr
  simp (disch := decide) only [kernel, commitIfAcknowledged, eval_epoch hs hr, eval_digestGuard hs hr,
    cur, req, eval_eqGuard (eval_load hs 0 (by decide)) (eval_const s 1),
    eval_eqGuard (eval_load hs 5 (by decide)) (eval_load hr 4 (by decide)),
    eval_eqGuard (eval_load hr 18 (by decide)) (eval_const s 1), evaluate_seq, commit,
    eval_finish, BEq.rfl, ite_true, stepBeltLatch, readState, readRequest]
  by_cases h0 : s.memory (address b 0) = 1
  case neg => simp_all
  by_cases h1 : digestAt (fun k => s.memory (address b k)) 1 = digestAt (fun k => s.memory (address c k)) 0
  case neg => simp_all
  by_cases h2 : s.memory (address b 5) = s.memory (address c 4)
  case neg => simp_all
  by_cases h3 : s.memory (address b 5) < s.memory (address c 5)
  case neg =>
    rw [h2] at h3
    simp [h0, h1, h2, h3]
  by_cases h4 : digestAt (fun k => s.memory (address b k)) 6 = digestAt (fun k => s.memory (address c k)) 6
  case neg => simp_all
  by_cases h5 : digestAt (fun k => s.memory (address b k)) 10 = digestAt (fun k => s.memory (address c k)) 14
  case neg => simp_all
  by_cases h6 : s.memory (address c 18) = 1
  case neg => simp_all
  simp_all

theorem pancakeBeltLatch_refusal_preserves_state {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19)
    (h : (stepBeltLatch (readState s.memory b) (readRequest s.memory c)).1 ≠ .accepted) :
    evaluate kernel.body s =
      (.ret (.word (stepBeltLatch (readState s.memory b) (readRequest s.memory c)).1.code), empty_locals s) := by
  simpa [h] using pancakeBeltLatch_correct hs hr

private theorem step_result (s : State) (r : Request) :
    let (v, t) := stepBeltLatch s r
    if v = .accepted then
      t = {s with epoch := r.nextEpoch, digest := r.nextDigest} ∧
      s.epoch = r.parentEpoch ∧ s.epoch < r.nextEpoch
    else t = s := by
  cases e : stepBeltLatch s r with
  | mk v t =>
    unfold stepBeltLatch at e
    repeat' (split at e)
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj e <;> simp_all

private theorem read_install (m : Word → Word) (b : Word) (r : Request) :
    readState (install m b r) b = {readState m b with epoch := r.nextEpoch, digest := r.nextDigest} := by
  simp +decide [readState, install, digestAt, UPDATE, address]

/-- Decoding the resulting machine state recovers the structured successor. -/
theorem pancakeBeltLatch_state {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19) :
    readState (evaluate kernel.body s).2.memory b =
      (stepBeltLatch (readState s.memory b) (readRequest s.memory c)).2 := by
  rw [pancakeBeltLatch_correct hs hr]
  have result := step_result (readState s.memory b) (readRequest s.memory c)
  cases h : stepBeltLatch (readState s.memory b) (readRequest s.memory c) with
  | mk v t =>
    rw [h] at result
    by_cases ok : v = .accepted
    · simp [ok] at result
      simpa [ok, empty_locals, read_install] using result.1.symm
    · simpa [ok, empty_locals] using (show t = _ by simpa [ok] using result).symm

/-- No word outside the mutable epoch and four digest limbs changes, even on acceptance. -/
theorem pancakeBeltLatch_frame {τ b c} {s : PanState τ}
    (hs : Mapped s "current" b 14) (hr : Mapped s "candidate" c 19) (a : Word)
    (away : ∀ i, 5 ≤ i → i ≤ 9 → address b i ≠ a) :
    (evaluate kernel.body s).2.memory a = s.memory a := by
  rw [pancakeBeltLatch_correct hs hr]
  dsimp only [empty_locals]
  split <;> simp (disch := decide) [install, UPDATE, away]

private theorem epoch_mono (s : State) (r : Request) : s.epoch ≤ (stepBeltLatch s r).2.epoch := by
  have h := step_result s r
  cases e : stepBeltLatch s r with
  | mk v t =>
    rw [e] at h
    by_cases ok : v = .accepted
    · simp [ok] at h
      rw [h.1]
      exact BitVec.le_of_lt h.2.2
    · simp [show t = s by simpa [ok] using h]

theorem trace_epoch_mono (s : State) (rs : List Request) :
    s.epoch ≤ (rs.foldl (fun t r => (stepBeltLatch t r).2) s).epoch := by
  induction rs generalizing s with
  | nil => exact BitVec.le_refl _
  | cons r rs ih => exact BitVec.le_trans (epoch_mono s r) (ih _)

/-- Once a parent has advanced, no competing child of that parent can be accepted,
    including after arbitrarily many intervening successes and refusals. -/
theorem accepted_parent_consumed (s : State) (r competitor : Request) (later : List Request)
    (ok : (stepBeltLatch s r).1 = .accepted) (same : competitor.parentEpoch = r.parentEpoch) :
    let t := later.foldl (fun t q => (stepBeltLatch t q).2) (stepBeltLatch s r).2
    (stepBeltLatch t competitor).1 ≠ .accepted := by
  dsimp only
  have h := step_result s r
  simp only [ok, ↓reduceIte] at h
  have hm := trace_epoch_mono (stepBeltLatch s r).2 later
  intro accepted
  have hc := step_result (later.foldl (fun t q => (stepBeltLatch t q).2) (stepBeltLatch s r).2) competitor
  simp only [accepted, ↓reduceIte] at hc
  have newer : s.epoch < (stepBeltLatch s r).2.epoch := by rw [h.1]; exact h.2.2
  rw [hc.2.1, same, ← h.2.1] at hm
  exact Nat.not_lt_of_ge hm newer

end Obend.Lower.Pancake.BeltLatch
