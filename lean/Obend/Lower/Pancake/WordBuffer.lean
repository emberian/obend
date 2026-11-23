module
public import Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.PanSem

public section
namespace Obend.Lower.Pancake.WordBuffer
set_option autoImplicit false

/-- Byte address of lane i in a 200-byte buffer, using target word arithmetic. -/
def address (base : Word) (i : Nat) := base + BitVec.ofNat 64 (8*i)

private theorem address_succ (b : Word) (i : Nat) : address b (i+1) = address b i + 8#64 := by
  simp [address, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

private theorem address_inj (b : Word) (i j : Fin 25) :
    address b i = address b j ↔ i = j := by

  have hi : 8*i.val < 2^64 := by have := i.isLt; omega
  have hj : 8*j.val < 2^64 := by have := j.isLt; omega
  constructor
  · intro h
    simp [address] at h
    have hn := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hn
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

abbrev Lanes := Fin 25 → Word

/-- A pure word formula can read any lane of the input snapshot. -/
inductive Expr where
  | lane (i : Fin 25)
  | lit (w : Word)
  | xor (a b : Expr)
  | and (a b : Expr)
  | rot (a : Expr) (left : Fin 64)
  deriving Inhabited

def Expr.value (v : Lanes) : Expr → Word
  | .lane i => v i
  | .lit w => w
  | .xor a b => a.value v ^^^ b.value v
  | .and a b => a.value v &&& b.value v
  | .rot a n => (a.value v).rotateLeft n

def Expr.lower (param : String) : Expr → PExp
  | .lane i => .load .One (.binop .Add [.lvar param, .const (BitVec.ofNat 64 (8*i.val))])
  | .lit w => .const w
  | .xor a b => .binop .Xor [a.lower param, b.lower param]
  | .and a b => .binop .And [a.lower param, b.lower param]
  | .rot a n => if n.val = 0 then a.lower param else
      .shift .Ror (a.lower param) (64 - n.val)

def Mapped {τ : Type} (s : PanState τ) (b : Word) := ∀ i : Fin 25, s.memaddrs (address b i) = true

theorem eval_lower {τ : Type} (s : PanState τ) (param : String) (b : Word)
    (hp : s.locals param = some (.word b)) (hm : Mapped s b) (e : Expr) :
    eval s (e.lower param) = some (.word (e.value (fun i => s.memory (address b i)))) := by
  induction e with
  | lane i =>
    simp [Expr.lower, Expr.value, eval, evalList, extractWords, word_op, hp,
      mem_load, address, show s.memaddrs (b + BitVec.ofNat 64 (8*i.val)) = true from hm i]
  | lit w => rfl
  | xor a b ha hb => simp [Expr.lower, Expr.value, ha, hb, word_op]
  | and a b ha hb =>
    simp [Expr.lower, Expr.value, ha, hb, word_op]
    exact congrArg _ (@BitVec.and_allOnes 64 _)
  | rot a n ha =>
    have hn := n.isLt
    by_cases hz : n.val = 0
    · simp [Expr.lower, Expr.value, hz, ha, BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]
    · have hj : 64 - n.val < 64 := by omega
      simp [Expr.lower, Expr.value, hz, eval, ha, word_sh, Nat.not_le.mpr hj,
        BitVec.rotateLeft_def, BitVec.rotateRight_def, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt hj, show 64 - (64 - n.val) = n.val by omega, BitVec.or_comm]

abbrev Stage := Fin 25 → Expr

def lowerStage (param : String) (f : Stage) : PStmt :=
  .store (.lvar param) (.rstruct ((List.finRange 25).map fun i => (f i).lower param))

def runStage (f : Stage) (v : Lanes) : Lanes := fun i => (f i).value v

private theorem fields_eval {τ : Type} (s : PanState τ) (p : String) (b : Word)
    (hp : s.locals p = some (.word b)) (hm : Mapped s b) (f : Stage) (xs : List (Fin 25)) :
    evalList s (xs.map fun i => (f i).lower p) =
      some (xs.map fun i => .word (runStage f (fun j => s.memory (address b j)) i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [eval_lower s p b hp hm, ih, runStage]

private theorem flatten_words (ws : List Word) :
    flatten_list (ws.map PanVal.word) = ws := by
  induction ws <;> simp [flatten_list, flatten, *]

private def write (b : Word) (m : Word → Word) (n : Nat) : List Word → Word → Word
  | [] => m
  | w :: ws => write b (UPDATE (address b n) w m) (n+1) ws

private theorem stores_write (b : Word) (dm : Word → Bool) (hm : ∀ i : Fin 25, dm (address b i))
    (ws : List Word) (n : Nat) (m : Word → Word) (h : n + ws.length ≤ 25) :
    mem_stores (address b n) ws dm m = some (write b m n ws) := by
  induction ws generalizing n m with
  | nil => rfl
  | cons w ws ih =>
    have hn : n < 25 := by simp at h; omega
    simp only [mem_stores, mem_store, hm ⟨n, hn⟩, ite_true, write, ← address_succ]
    apply ih
    simp at h; omega

private theorem write_at (b : Word) (ws : List Word) (n : Nat) (m : Word → Word)
    (h : n + ws.length ≤ 25) (i : Fin 25) :
    write b m n ws (address b i) =
      if n ≤ i.val then ws[i.val-n]?.getD (m (address b i)) else m (address b i) := by
  induction ws generalizing n m with
  | nil => simp [write]
  | cons w ws ih =>
    have hn : n < 25 := by simp at h; omega
    have ht : n+1 + ws.length ≤ 25 := by simp at h; omega
    have he : address b i = address b n ↔ i.val = n :=
      (address_inj b i ⟨n,hn⟩).trans Fin.ext_iff
    have hr : address b n = address b i ↔ i.val = n := eq_comm.trans he
    rw [write, ih _ _ ht]
    by_cases eq : i.val = n
    · simp [UPDATE, eq, show ¬n+1 ≤ n by omega]
    · by_cases lt : i.val < n
      · simp [UPDATE, hr, eq, show ¬n ≤ i.val by omega, show ¬n+1 ≤ i.val by omega]
      · have hd : i.val-n = (i.val-(n+1))+1 := by omega
        simp [UPDATE, hr, eq, hd, show n ≤ i.val by omega, show n+1 ≤ i.val by omega]

private theorem write_outside (b a : Word) (ws : List Word) (n : Nat) (m : Word → Word)
    (h : n + ws.length ≤ 25) (away : ∀ i : Fin 25, a ≠ address b i) :
    write b m n ws a = m a := by
  induction ws generalizing n m with
  | nil => rfl
  | cons w ws ih =>
    have hn : n < 25 := by simp at h; omega
    rw [write, ih _ _ (by simp at h; omega)]
    simp [UPDATE, Ne.symm (away ⟨n, hn⟩)]

/-- Simultaneous assignment of all lanes. Every RHS observes the same pre-store state. -/
theorem lowerStage_correct {τ : Type} (s : PanState τ) (p : String) (b : Word)
    (hp : s.locals p = some (.word b)) (hm : Mapped s b) (f : Stage) :
    ∃ m, evaluate (lowerStage p f) s = (.normal, {s with memory := m}) ∧
      (∀ i : Fin 25, m (address b i) = runStage f (fun j => s.memory (address b j)) i) ∧
      ∀ a, (∀ i : Fin 25, a ≠ address b i) → m a = s.memory a := by
  let out := runStage f (fun j => s.memory (address b j))
  let ws := (List.finRange 25).map out
  have len : ws.length = 25 := by simp [ws]
  refine ⟨write b s.memory 0 ws, ?_, ?_, ?_⟩
  · have hf : flatten (.rstruct ((List.finRange 25).map fun i => PanVal.word (out i))) = ws := by
      change flatten_list _ = ws
      rw [← flatten_words ws]
      simp [ws, List.map_map, Function.comp_def]
    have hs := stores_write b s.memaddrs hm ws 0 s.memory (by omega)
    simp [address] at hs
    simp only [lowerStage, evaluate_store, eval_lvar, hp, eval_rstruct, fields_eval s p b hp hm, Option.map_some]
    rw [hf, hs]
  · intro i
    rw [write_at _ _ _ _ (by omega)]
    simp [ws, out, i.isLt]

  · intro a away
    exact write_outside b a ws 0 _ (by omega) away

end Obend.Lower.Pancake.WordBuffer
