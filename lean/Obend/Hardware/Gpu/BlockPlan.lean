module
public import Obend.Hardware.Gpu.BlockCoreProgram
public import Obend.Hardware.Gpu.BlockCoreEncoding
public import Obend.Hardware.Gpu.SourceProtocol
public import Obend.Hardware.Gpu
@[expose] public section

/-! The block-level source fragment of Core4.

Lift's mapWrg/mapLcl hierarchy is represented by ArrayKernel dispatches/phases;
toLocal/toGlobal are the checked shared/device buffer classes, while a phase's
lexical scalar network is a register-resident tile (toPrivate). Split/join and
layout changes are symbolic group/lane index expressions. Uniform barriers divide
shared phases, and ordered dispatches provide communication between workgroups.
Futhark's intra-group parallelism motivates retaining these bounded nested maps.

The existing block source AST is reused. BlockCoreProgram elaborates it into
ordinary Core4 lexical lets and bounded loops; neither a second source AST nor a
transform-specific Core primitive is introduced. Its term is built from source
operations, not from evaluated outputs. This receipt composes that elaboration
with the admitted general indexed-array lowering and G4 protocol.

References:
https://lift-project.readthedocs.io/en/latest/lift-overview/
https://futhark-lang.org/publications/ppopp19.pdf
-/
namespace Obend.Hardware.Gpu.BlockPlan
open Obend.Core.Term Obend.Equiv
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.BlockLower
set_option autoImplicit false

/-- Boundary arrays are device word vectors; literal buffers have their exact
static shape. Per-phase SSA, bounds, ownership and initialization come from check. -/
def interfaceOk (p : Program) : Bool :=
  (p.inputs ++ p.outputs).all (fun a => a < p.buffers.length &&
    (p.buffers.getD a default).storage == .device) &&
  p.buffers.all (fun b => b.storage != .constant || b.values.length == b.size)

structure Plan where
  source : Program
  interfaceChecked : interfaceOk source = true
  checked : source.check = .ok ()
  protocolChecked : SourceProtocol.checkProgram source workgroupSize = true

/-- One admission route for the block source fragment. Runtime checks inspect
static program structure, never an input-dependent answer. -/
def check (p : Program) : Except String Plan :=
  if hi : interfaceOk p = true then
    match hc : p.check with
    | .error message => .error message
    | .ok () =>
      if hp : SourceProtocol.checkProgram p workgroupSize = true then .ok ⟨p,hi,hc,hp⟩
      else .error "block source: physical workgroup protocol rejected"
  else .error "block source: boundary or literal buffer shape rejected"

theorem check_source (p : Program) (plan : Plan) (h : check p = .ok plan) : plan.source = p := by
  unfold check at h
  split at h
  · split at h
    · contradiction
    · split at h
      · cases h; rfl
      · contradiction
  · contradiction

def Plan.term (p : Plan) : Term := BlockCoreProgram.source p.source

def observe (program memory : Term) (array index : Nat) : Term :=
  .app (.app (.app program memory) (.nat array)) (.nat index)

/-- Source Core4 observation and actual indexed GPU lowering coincide for every
shape-correct initial memory and every valid source cell. The general block
fragment includes indexed register tiles, shared phases and barriers. -/
theorem Plan.source_to_gpu (p : Plan) (state : Term) (mem : Memory) (flat : FlatMemory)
    (hs : BlockCoreMemory.Denotes state mem) (hg : BlockLower.Good p.source mem)
    (hf : Represents p.source mem flat) (array index : Nat) (hv : Valid p.source array index) :
    Steps (observe p.term state array index)
      (.nat ((lowerProgram p.source flat) (address p.source array index)).toNat) := by
  have hc := BlockCoreProgram.source_sound p.source state mem hs hg p.checked
  have hl := checkedProgram_sound p.source mem flat hg hf p.checked
  have hread := hc array index
  rw [← hl array index hv] at hread
  exact hread

/-- Encoded inputs, rather than a supplied Core4 evaluation premise. Encoding
contains only initial memory data; the source term remains symbolic. -/
theorem Plan.source_to_gpu_encoded (p : Plan) (mem : Memory) (flat : FlatMemory)
    (hg : BlockLower.Good p.source mem) (hf : Represents p.source mem flat)
    (array index : Nat) (hv : Valid p.source array index) :
    Steps (observe p.term (BlockCoreEncoding.memory mem) array index)
      (.nat ((lowerProgram p.source flat) (address p.source array index)).toNat) :=
  p.source_to_gpu _ mem flat (BlockCoreEncoding.memory_sound mem) hg hf array index hv

/-- The same source receipt certifies its actual workgroup trace in the existing
Vulkan G4 model; no second memory model is attached to the Core4 interpretation. -/
theorem Plan.not_racy (p : Plan) (d : Dispatch) (hd : d ∈ p.source.dispatches)
    (group : Nat) (hg : group < d.groups) (mem : Memory) :
    (Workgroup.sourceTrace p.source d mem group workgroupSize).static.racy = false :=
  SourceProtocol.checkProgram_not_racy p.source workgroupSize p.protocolChecked d hd group hg mem

end Obend.Hardware.Gpu.BlockPlan
end
