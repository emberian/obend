module
public import Obend.Hardware.Gpu.BlockCoreLoop
public import Obend.Hardware.ArrayKernel
@[expose] public section
namespace Obend.Hardware.Gpu.BlockCoreIndex
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- General literal-result congruence, also for unbounded natural indices. -/
theorem ahead_nat {t u : Term} (n : Nat) (h : Ahead t u)
    (hs : Steps u (.nat n)) : Steps t (.nat n) := by
  obtain ⟨r, hr, ha⟩ := evaluates_ahead h ⟨hs, .natural _⟩
  exact steps_trans hr.1 (inv_literal_ahead (.nat _) ha)

theorem primitive_nat (op : Primitive) (a b : Term) (x y z : Nat)
    (ha : Steps a (.nat x)) (hb : Steps b (.nat y))
    (hv : primitiveResult op (.nat x) (.nat y) = some (.nat z)) :
    Steps (.binary op a b) (.nat z) := by
  apply ahead_nat z (.binary op (.run ha (.nat _)) (.run hb (.nat _)))
  exact .next (.primitive op _ _ _ (.natural _) (.natural _) hv) (.refl _)

/-- Symbolic indexed maps retain their workgroup and lane variables. Constants
and descriptor tables are literal data, never evaluations of a kernel/input. -/
def term (group lane : Term) : Ix → Term
  | .lit n => .nat n
  | .group => group
  | .lane => lane
  | .add a b => .binary .add (term group lane a) (term group lane b)
  | .mul a b => .binary .multiply (term group lane a) (term group lane b)
  | .div a n => .binary .divide (term group lane a) (.nat n)
  | .mod a n => .binary .modulo (term group lane a) (.nat n)
  | .lookup values i => .app (encodeNats values.toList) (term group lane i)

theorem term_substitute (ix : Ix) (g l : Term) (σ : Nat → Term) :
    (term g l ix).substitute σ = term (g.substitute σ) (l.substitute σ) ix := by
  induction ix <;> simp [term, Term.substitute, *, encodeNats_substitute]

theorem term_sound (ix : Ix) (g l : Term) (group lane : Nat)
    (hg : Steps g (.nat group)) (hl : Steps l (.nat lane)) :
    Steps (term g l ix) (.nat (ix.eval group lane)) := by
  induction ix with
  | lit n => exact .refl _
  | group => exact hg
  | lane => exact hl
  | add a b ha hb => exact primitive_nat .add _ _ _ _ _ ha hb rfl
  | mul a b ha hb => exact primitive_nat .multiply _ _ _ _ _ ha hb rfl
  | div a n ha => exact primitive_nat .divide _ _ _ _ _ ha (.refl _) rfl
  | mod a n ha => exact primitive_nat .modulo _ _ _ _ _ ha (.refl _) rfl
  | lookup values i hi =>
    apply ahead_nat _ (.app (.refl _) (.run hi (.nat _)))
    simpa only [Ix.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList] using
      encodeNats_apply values.toList (i.eval group lane)

end Obend.Hardware.Gpu.BlockCoreIndex
end
