module
/- Leaf composition members whose method bodies are the compact Core4 encoding of
lexical array programs. Acceptance checks syntax and scope, never the desired output.
The theorem composes the existing book theorem, Core4 observation semantics, lexical
array compilation, and GPU dispatch semantics. -/
public import Obend.Hardware.Gpu.ArraySourceCore
public import Obend.Leaf.Emit
public import Obend.Hardware.ArrayTyping
@[expose] public section
namespace Obend.Hardware.Gpu.ArrayMember
open Obend.Core.Term Obend.Core.TermTraverse Obend.Equiv Obend.Leaf
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayTyping
open Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.Gpu.ArraySource.Core
set_option autoImplicit false

/-- Input bundle components retain the public left-to-right input order; source variables use
lexical indices, most recently bound first. Outside the input context the value is empty. -/
def inputProjection (n : Nat) (bundle : Term) (i : Nat) : Term :=
  if i < n then nth bundle (wire n i) else encodeNats []

def lexicalLens (ls : List Nat) : Nat → Nat := fun i => ls.reverse.getD i 0

def body (p : Program) (ls : List Nat) : Term :=
  (p.term (lexicalLens ls)).substitute (inputProjection ls.length (.bound 0))

theorem projection_substitute (n : Nat) (bundle : Term) (i : Nat) (σ : Nat → Term) :
    (inputProjection n bundle i).substitute σ = inputProjection n (bundle.substitute σ) i := by
  simp only [inputProjection]
  split <;> simp [nth_substitute, encodeNats_substitute]

theorem body_substitute (p : Program) (ls : List Nat) (σ : Nat → Term) :
    (body p ls).substitute σ = (p.term (lexicalLens ls)).substitute
      (inputProjection ls.length (σ 0)) := by
  simp only [body, substitute_comp]
  congr 1
  funext i
  simp [projection_substitute, Term.substitute]

theorem method_closed (p : Program) (ls : List Nat) (self : Term) :
    instantiate (.lam (body p ls)) self = .lam (body p ls) := by
  simp only [instantiate_eq, Term.substitute, body_substitute]
  rfl

theorem method_apply (p : Program) (ls : List Nat) (input : Term) :
    Steps (.app (.lam (body p ls)) input)
      ((p.term (lexicalLens ls)).substitute (inputProjection ls.length input)) := by
  refine .next (.beta _ _) ?_
  rw [instantiate_eq, body_substitute]
  exact .refl _

structure Plan (C : Obend.Logic.Composition) (m : String) where
  program : Program
  inputLengths : List Nat
  closed : C.closedB = true
  scope : program.Scoped inputLengths.length
  types : List TensorType
  typing : GraphTyping types (compile inputLengths program)
  layout : layoutOk (compile inputLengths program) = true
  member : C.vtable.find? (·.1 == m) = some (m, .lam (body program inputLengths))

def Plan.graph {C : Obend.Logic.Composition} {m : String} (p : Plan C m) : ArrayGraph :=
  compile p.inputLengths p.program

def Plan.typed {C : Obend.Logic.Composition} {m : String} (p : Plan C m) : TypedGraph :=
  ⟨p.graph, p.types, p.typing, p.layout⟩

def Plan.lower {C : Obend.Logic.Composition} {m : String} (p : Plan C m) : GpuProgram :=
  p.typed.lower

/-- Translation validation against an actual source member. The candidate is lexical source
syntax, independently interpreted in Core4, rather than a graph or a semantic certificate. -/
def checkMember (C : Obend.Logic.Composition) (m : String) (p : Program) (ls : List Nat) :
    Except String (Plan C m) := do
  if hc : C.closedB = true then
    if hs : p.scopedB ls.length = true then
      match hm : C.vtable.find? (·.1 == m) with
      | none => throw s!"unknown array member {m}"
      | some (name, code) =>
        if hn : name = m then
          if ht : Obend.Law.termEq code (.lam (body p ls)) = true then
            match hg : checkTypedGraph (wordTypes (compile ls p)) (compile ls p) with
            | .error e => throw e
            | .ok typed =>
              pure ⟨p, ls, hc, p.scopedB_sound ls.length hs, wordTypes (compile ls p),
                checkTypedGraph_typing _ _ _ hg, checkTypedGraph_layout _ _ _ hg,
                by rw [hm, hn, Obend.Law.termEq_sound ht]⟩
          else throw s!"member {m} differs from the candidate array source syntax"
        else throw "selected array member name differs"
    else throw "array program reads an out-of-scope input or let variable"
  else throw "array source composition is not closed"

theorem Plan.flat_apply {C : Obend.Logic.Composition} {m : String} (p : Plan C m) (input : Term) :
    Steps (.app (.get (flatObject C.vtable) m) input)
      ((p.program.term (lexicalLens p.inputLengths)).substitute
        (inputProjection p.inputLengths.length input)) := by
  obtain ⟨mid, first, rest⟩ := flatObject_unfold C.vtable
  have lookup := find_mapFields (instantiate · (flatObject C.vtable)) p.member
  rw [method_closed] at lookup
  have hs : Steps (.get (flatObject C.vtable) m) (.lam (body p.program p.inputLengths)) :=
    steps_trans (steps_get m (.next first rest)) (.next (.field _ _ _ lookup) (.refl _))
  exact steps_trans (steps_app input hs) (method_apply p.program p.inputLengths input)

/-- Universal source-to-GPU theorem. `hinput` relates the *input representation* to the supplied
arrays; it does not assume any output computation. `boundary` is the input-wire relation and
`shape` the static input shape. There is no semantic certificate parameter. -/
theorem Plan.source_to_gpu {C : Obend.Logic.Composition} {m : String} (p : Plan C m)
    (input : Term) (source target : Env) (flat : Nat → Word)
    (shape : ∀ i, lexicalLens p.inputLengths i = (source i).length)
    (hinput : ∀ i, ArrayDenotes (inputProjection p.inputLengths.length input i) (source i))
    (boundary : Represents p.inputLengths.length source target)
    (good : Good p.graph.lengths target)
    (hflat : Flat p.graph.lengths (gpuLayout p.graph).base
      (liveAt (layerGraph (fuseGraph p.graph)) p.graph.outputs) target flat) :
    runProgram p.lower flat = p.program.eval source ∧
    ∀ output, output < (p.program.eval source).length → ∀ index,
      Halts (.app (nth (.app (.get C.object m) input) output) (.nat index))
        (.natural (((p.program.eval source).getD output []).getD index 0#64).toNat) := by
  refine ⟨?_, ?_⟩
  · rw [show p.lower = p.typed.lower from rfl, p.typed.lower_sound target flat good hflat]
    exact compile_sound p.inputLengths p.program source target p.scope boundary
  · intro output ho index
    have run := p.program.term_sound (lexicalLens p.inputLengths)
      (inputProjection p.inputLengths.length input) source shape hinput output ho index
    have frun := steps_trans (steps_app _ (nth_steps output (p.flat_apply input))) run
    have hf : Halts (.app (nth (.app (.get (flatObject C.vtable) m) input) output) (.nat index))
        (.natural (((p.program.eval source).getD output []).getD index 0#64).toNat) :=
      ⟨_, ⟨frun, .natural _⟩, .natural _⟩
    have eq := (book_sound C p.closed m).symm.trans
      (bequiv_of_ahead (.get m (link_ahead C.vtable)))
    have he := eq Term.bound (.app (nth (.app (.bound 0) (input.rename Nat.succ)) output) (.nat index))
    have hr : SameRuns
        (.app (nth (.app (.get C.object m) input) output) (.nat index))
        (.app (nth (.app (.get (flatObject C.vtable) m) input) output) (.nat index)) := by
      simpa [instantiate_eq, nth_substitute, Term.substitute, substitute_bound, single, shift_one_cancel] using he
    exact (hr.halts _).mpr hf

/-- Canonical data input: a finite product of total array-index functions. -/
def encodeVec (xs : Vec) : Term := encodeNats (xs.map (·.toNat))

def encodeInputs (inputs : List Vec) : Term := pack (inputs.map encodeVec)

def inputValues (inputs : List Vec) : Env :=
  fun i => if i < inputs.length then inputs.getD (wire inputs.length i) [] else []

theorem encodeVec_denotes (xs : Vec) : ArrayDenotes (encodeVec xs) xs := by
  intro i
  have heq : (xs.map (·.toNat)).getD i 0 = (xs.getD i 0#64).toNat := by
    induction xs generalizing i with
    | nil => cases i <;> rfl
    | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
  simpa only [encodeVec, heq] using encodeNats_apply (xs.map (·.toNat)) i

theorem encodeInputs_denotes (inputs : List Vec) (i : Nat) :
    ArrayDenotes (inputProjection inputs.length (encodeInputs inputs) i) (inputValues inputs i) := by
  intro index
  by_cases hi : i < inputs.length
  · have hw : wire inputs.length i < inputs.length := by unfold wire; omega
    have hp := nth_pack (inputs.map encodeVec) (wire inputs.length i) (by simpa using hw)
    rw [getD_map_lt inputs encodeVec (wire inputs.length i) [] (.nat 0) hw] at hp
    simpa [inputProjection, inputValues, hi, encodeInputs] using
      steps_trans (steps_app (.nat index) hp)
        (encodeVec_denotes (inputs.getD (wire inputs.length i) []) index)
  · simpa [inputProjection, inputValues, hi] using encodeNats_apply [] index

/-- The concrete input-encoding corollary: no input semantics certificate is needed when callers
supply ordinary word arrays. Shape and boundary relations describe only host buffer loading. -/
theorem Plan.source_to_gpu_encoded {C : Obend.Logic.Composition} {m : String} (p : Plan C m)
    (inputs : List Vec) (target : Env) (flat : Nat → Word)
    (count : p.inputLengths.length = inputs.length)
    (shape : ∀ i, lexicalLens p.inputLengths i = (inputValues inputs i).length)
    (boundary : Represents p.inputLengths.length (inputValues inputs) target)
    (good : Good p.graph.lengths target)
    (hflat : Flat p.graph.lengths (gpuLayout p.graph).base
      (liveAt (layerGraph (fuseGraph p.graph)) p.graph.outputs) target flat) :
    runProgram p.lower flat = p.program.eval (inputValues inputs) ∧
    ∀ output, output < (p.program.eval (inputValues inputs)).length → ∀ index,
      Halts (.app (nth (.app (.get C.object m) (encodeInputs inputs)) output) (.nat index))
        (.natural (((p.program.eval (inputValues inputs)).getD output []).getD index 0#64).toNat) := by
  apply p.source_to_gpu (encodeInputs inputs) (inputValues inputs) target flat shape
  · intro i
    rw [count]
    exact encodeInputs_denotes inputs i
  · exact boundary
  · exact good
  · exact hflat

end Obend.Hardware.Gpu.ArrayMember
end
