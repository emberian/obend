module
public import Obend.Hardware.ArrayTyping
@[expose] public section
namespace Obend.Teeth.Hardware.ArrayTyping
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayTyping

private def addGraph : ArrayGraph :=
  ⟨[6,6,6], [0,1], [2], [⟨0, .map 6 (.single (.scalar .add) [0,1] 2), [0,1], 2⟩]⟩

-- Equal flattened lengths do not justify a shape-changing pointwise operation.
example : GraphTyping [⟨[2,3],.word⟩, ⟨[2,3],.word⟩, ⟨[2,3],.word⟩] addGraph := by decide
example : ¬ GraphTyping [⟨[2,3],.word⟩, ⟨[6],.word⟩, ⟨[2,3],.word⟩] addGraph := by decide

-- The fixed-point scale is part of the type, even though all storage has width 64.
example : elemSignature (.scalar .mul) [.fixed 8,.fixed 8] (.fixed 16) = true := rfl
example : elemSignature (.scalar .mul) [.fixed 8,.fixed 8] (.fixed 8) = false := rfl
example : elemSignature (.scalar .add) [.fixed 8,.fixed 16] (.fixed 8) = false := rfl

-- Legacy wf admits a read of an uninitialized scratch wire; typing refuses it.
private def missingProducer : ArrayGraph := { addGraph with inputs := [0] }
example : missingProducer.wf = true := by decide
example : ¬ GraphTyping (wordTypes missingProducer) missingProducer := by decide

-- Canonical Boolean constants and element signatures cannot be confused with words.
example : elemSignature (.scalar (.const 2)) [] .predicate = false := rfl
example : elemSignature .ult [.word,.word] .predicate = true := rfl

end Obend.Teeth.Hardware.ArrayTyping
