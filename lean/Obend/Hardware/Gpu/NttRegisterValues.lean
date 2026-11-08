module
public import Obend.Hardware.Gpu.NttLayers
@[expose] public section
namespace Obend.Hardware.Gpu.Ntt.RegisterValues
open GoldilocksSource

/-- A mathematical register-value update, used to state the refinement of the
actual phase source loop. It creates no graph, code, phase, or dispatch. -/
def update (v : Nat → Nat) (i value : Nat) : Nat → Nat := fun j => if j=i then value else v j

/-- Field denotation of one source butterfly pair. -/
def pairStep (bit twiddle j : Nat) (values : Nat → Nat) : Nat → Nat :=
  let i0 := 2*j-j%bit
  let i1 := i0+bit
  update (update values i0 ((values i0+values i1)%goldilocksP)) i1
    ((((values i0+goldilocksP-values i1)%goldilocksP)*twiddle)%goldilocksP)

/-- Denotation of the source's sequential pair loop, preserving operand order. -/
def roundValues (pairs bit : Nat) (twiddle : Nat → Nat) (values : Nat → Nat) : Nat → Nat :=
  (List.range pairs).foldl (fun v j => pairStep bit (twiddle j) j v) values

end Obend.Hardware.Gpu.Ntt.RegisterValues
end
