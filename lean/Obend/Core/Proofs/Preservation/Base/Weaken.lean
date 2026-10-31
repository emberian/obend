module
/- Typing is preserved by extending the address assignment. -/
public import Obend.Core.MachineTyping
public import Obend.Core.RuntimeOrigins
public import Obend.Core.EquiRecursiveLookup
public import Obend.Core.TypeGraphHead
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Tactic.Cases
namespace Obend.Core.Proofs.Preservation
open Obend.Core.Ty Obend.Core.Check Obend.Core.Term Obend.Core.Machine Obend.Core.MachineTyping
set_option autoImplicit false

@[expose] public def ClosureTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {closure : Closure} {type : Ty} (extension : TypeExtension before after)
    (typed : Obend.Core.MachineTyping.ClosureTyping assumptions before closure type) :
    Obend.Core.MachineTyping.ClosureTyping assumptions after closure type :=
  ⟨typed.context,typed.uses,typed.environment.weaken extension,typed.source,typed.safe,typed.contextValid⟩

public theorem ValueTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {value : RuntimeValue} {type : Ty} (extension : TypeExtension before after)
    (typed : ValueTyping assumptions before value type) : ValueTyping assumptions after value type := by
  induction typed with
  | natural value => exact .natural value
  | boolean value => exact .boolean value
  | label value => exact .label value
  | closure environment body safe valid captures =>
      exact .closure (environment.weaken extension) body safe valid captures
  | record row members =>
      refine .record row ?_
      intro fuel name member lookup
      obtain ⟨address,actual,found,assigned,path⟩ := members fuel name member lookup
      exact ⟨address,actual,found,extension address actual assigned,path⟩
  | specification metadata ext => exact .specification (extension _ _ metadata) (extension _ _ ext)
  | prototype spec target => exact .prototype (extension _ _ spec) (extension _ _ target)
  | conversion prior agreement ih => exact .conversion ih agreement
  | variant lookup assigned path => exact .variant lookup (extension _ _ assigned) path

public theorem CellTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {cell : Cell} {type : Ty} (extension : TypeExtension before after)
    (typed : CellTyping assumptions before cell type) : CellTyping assumptions after cell type := by
  cases typed with
  | suspended origin pure => exact .suspended (ClosureTyping.weaken extension origin) pure
  | evaluating origin pure => exact .evaluating (ClosureTyping.weaken extension origin) pure
  | cached origin value pure =>
      exact .cached (ClosureTyping.weaken extension origin) (ValueTyping.weaken extension value) pure

public theorem FrameTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {frame : Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : FrameTyping assumptions before frame input output) :
    FrameTyping assumptions after frame input output := by
  cases typed with
  | argument argument callable copyAllowed => exact .argument (ClosureTyping.weaken extension argument) callable copyAllowed
  | update assigned pure => exact .update (extension _ _ assigned) pure
  | field found => exact .field found
  | reflect => exact .reflect _ _
  | metadata => exact .metadata _ _
  | project => exact .project _ _
  | extend environment fields safe valid row => exact .extend (environment.weaken extension) fields safe valid row
  | condition zero environment successor safe valid =>
      exact .condition (ClosureTyping.weaken extension zero) (environment.weaken extension) successor safe valid
  | binaryLeft right => exact .binaryLeft (ClosureTyping.weaken extension right)
  | binaryRight left => exact .binaryRight (ValueTyping.weaken extension left)
  | case environment arms valid => exact .case (environment.weaken extension) arms valid
  | ifBool whenTrue whenFalse =>
      exact .ifBool (ClosureTyping.weaken extension whenTrue) (ClosureTyping.weaken extension whenFalse)
  | effectCase environment arms valid pure => exact .effectCase (environment.weaken extension) arms valid pure

public theorem StackTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {stack : List Frame} {input output : Ty} (extension : TypeExtension before after)
    (typed : StackTyping assumptions before stack input output) :
    StackTyping assumptions after stack input output := by
  induction typed with
  | nil type => exact .nil type
  | cons frame rest ih => exact .cons (FrameTyping.weaken extension frame) ih
  | conversion agreement rest ih => exact .conversion agreement ih
  | returns pure rest ih => exact .returns pure ih

public theorem ControlTyping.weaken {assumptions : Assumptions} {before after : AddressTypes}
    {control : Control} {type : Ty} (extension : TypeExtension before after)
    (typed : ControlTyping assumptions before control type) :
    ControlTyping assumptions after control type := by
  cases typed with
  | evaluate closure => exact .evaluate (ClosureTyping.weaken extension closure)
  | enter assigned => exact .enter (extension _ _ assigned)
  | returned value => exact .returned (ValueTyping.weaken extension value)
  | complete value => exact .complete (ValueTyping.weaken extension value)
  | blackhole assigned => exact .blackhole (extension _ _ assigned)
  | yielded assigned plan response => exact .yielded (extension _ _ assigned) plan response

/-- Address identity is conserved through arbitrary allocation extensions. -/
public theorem type_extension_append (before additions : AddressTypes) :
    TypeExtension before (before ++ additions) := by
  intro address type assigned
  have bound : address < before.length := (List.getElem?_eq_some_iff.mp assigned).1
  simpa [List.getElem?_append,bound] using assigned

end Obend.Core.Proofs.Preservation
