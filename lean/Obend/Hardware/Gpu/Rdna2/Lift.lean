/-
# Obend.Hardware.Gpu.Rdna2.Lift — residuals that are 64-bit ring identities in 32-bit limbs

Some residuals are the high (or low) dword of two 64-bit sums and products written in 32-bit limbs:
`hi(a·(y+y))` against `hi(a·y + a·y)`, where the compiler and the plan grouped a product differently.
SAT decides limb multipliers badly; as 64-bit words the two sides are one ring identity, which `grind`'s
commutative-ring solver proves at once. `W` is that 64-bit expression language over pairs of leaf
variables; `W.lower` writes an expression in limbs with `Lower`'s own pair operations, so `lower_ev` is
their evaluation laws, and `holds_hi`/`holds_lo` turn a 64-bit identity into the residual over the
lowered halves. Which `W` a residual is, is found by an unverified parse in `obend-rdna2`, which emits
this form only when the lowered terms are the residual's, term for term.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Lower
public import Obend.Hardware.Gpu.Rdna2.Equiv
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Tm Obend.Hardware.ArrayHypergraph

/-- A 64-bit expression over pairs of leaf variables (`leaf lo hi`: the word `hi:lo`). -/
inductive W where
  | leaf (lo hi : UInt64)
  | add (a b : W)
  | sub (a b : W)
  | mul (a b : W)
  deriving Repr

namespace W

def eval (env : UInt64 → UInt32) : W → Word
  | leaf lo hi => (join64 (env lo) (env hi)).toBitVec
  | add a b => a.eval env + b.eval env
  | sub a b => a.eval env - b.eval env
  | mul a b => a.eval env * b.eval env

/-- The expression in 32-bit limbs, by `Lower`'s pair operations. -/
def lower : W → TP
  | leaf lo hi => (var lo, var hi)
  | add a b => pAdd a.lower b.lower
  | sub a b => pSub a.lower b.lower
  | mul a b => pMul a.lower b.lower

theorem lower_ev (env : UInt64 → UInt32) : ∀ w : W, w.lower.ev env = w.eval env
  | leaf lo hi => by simp [lower, eval, TP.ev]
  | add a b => by rw [lower, ev_add, lower_ev env a, lower_ev env b, eval]
  | sub a b => by rw [lower, ev_sub, lower_ev env a, lower_ev env b, eval]
  | mul a b => by rw [lower, ev_mul, lower_ev env a, lower_ev env b, eval]

theorem lo_of_ev (env : UInt64 → UInt32) (p : TP) : p.1.eval env = (UInt64.ofBitVec (p.ev env)).toUInt32 := by
  simp only [TP.ev, UInt64.ofBitVec_toBitVec]; unfold join64; bv_decide

theorem hi_of_ev (env : UInt64 → UInt32) (p : TP) :
    p.2.eval env = ((UInt64.ofBitVec (p.ev env)) >>> 32).toUInt32 := by
  simp only [TP.ev, UInt64.ofBitVec_toBitVec]; unfold join64; bv_decide

/-- Equal 64-bit expressions have equal high dwords: the residual over the lowered high halves holds. -/
theorem holds_hi (e1 e2 : W) (h : ∀ env, e1.eval env = e2.eval env) :
    Residual.Holds ⟨e1.lower.2, e2.lower.2⟩ := by
  intro env
  simp only [hi_of_ev env, lower_ev, h env]

/-- Equal 64-bit expressions have equal low dwords. -/
theorem holds_lo (e1 e2 : W) (h : ∀ env, e1.eval env = e2.eval env) :
    Residual.Holds ⟨e1.lower.1, e2.lower.1⟩ := by
  intro env
  simp only [lo_of_ev env, lower_ev, h env]

end W
end Obend.Hardware.Gpu.Rdna2
