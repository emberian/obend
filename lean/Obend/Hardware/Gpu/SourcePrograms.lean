module
/- Concrete source-language gates. These are executable tests; the universal theorem is
MemberPlan.source_to_gpu. Every graph comes from a selected Core4 method of a composition,
and every expected vector below is computed independently of the compiler and graph evaluator. -/
public import Obend.Hardware.Gpu.Source
@[expose] public section
namespace Obend.Hardware.Gpu.SourcePrograms
open Obend.Core.Term Obend.Logic
open Obend.Hardware.ArrayHypergraph Obend.Hardware.Gpu.Source
set_option autoImplicit false

structure Case where
  name : String
  body : Term
  reference : Word → Word
  vectors : List Vec

def composition (body : Term) : Composition :=
  { top := { name := "GpuSource", metadata := .record [], fields := [("run", body)], flat := true }
    below := [], seed := [] }

def wordPool : Vec :=
  [0#64, 1#64, 2#64, 63#64, 64#64, 65#64, 255#64, 65535#64,
   0xFFFFFFFF#64, 0x8000000000000000#64, 0xFFFFFFFFFFFFFFFF#64]

def shiftPool : Vec :=
  [0#64, 1#64, 31#64, 32#64, 63#64, 64#64, 65#64,
   0x100000000#64, 0x8000000000000000#64, 0xFFFFFFFFFFFFFFFF#64]

/-- Integer numerators of Q8 inputs; the square has Q16 scale. No rescaling or rounding. -/
def fixedPool : Vec :=
  [-512, -256, -128, -1, 0, 1, 64, 128, 256, 384, 512].map (BitVec.ofInt 64)

def affineBody : Term :=
  Binary.term .add (Binary.term .mul (.bound 0) (.nat 3)) (.nat 5)

def muxBody : Term :=
  muxTerm (Binary.term .ult (.bound 0) (.nat 64)) affineBody
    (Binary.term .sub (.bound 0) (.nat 7))

def cases : List Case :=
  [ ⟨"source-leaf-affine", .lam affineBody, (fun x => x * 3#64 + 5#64), [wordPool, wordPool.reverse]⟩
  , ⟨"source-leaf-mux", .lam muxBody,
      (fun x => if x.toNat < 64 then x * 3#64 + 5#64 else x - 7#64), [wordPool, wordPool.reverse]⟩
  , ⟨"source-leaf-shl", .lam (Binary.term .shl (.nat 1) (.bound 0)),
      (fun x => if x.toNat < 64 then BitVec.ofNat 64 (2 ^ x.toNat) else 0#64),
      [shiftPool, shiftPool.reverse]⟩
  , ⟨"source-leaf-shr", .lam (Binary.term .shr (.nat (2^64 - 1)) (.bound 0)),
      (fun x => if x.toNat < 64 then BitVec.ofNat 64 ((2^64 - 1) / 2 ^ x.toNat) else 0#64),
      [shiftPool, shiftPool.reverse]⟩
  , ⟨"source-leaf-fixed-square", .lam (Binary.term .mul (.bound 0) (.bound 0)),
      (fun x => BitVec.ofInt 64 (x.toInt * x.toInt)), [fixedPool, fixedPool.reverse]⟩ ]

def Case.size (c : Case) : Nat := (c.vectors.headD []).length

def Case.compile (c : Case) : Except String (MemberPlan (composition c.body) "run") := do
  unless (composition c.body).closedB do throw s!"{c.name}: source composition is not closed"
  compileMember (composition c.body) "run" c.size

/-- No failed compilation is filtered out or replaced by a graph. -/
def sourceGraphs : Except String (List (String × ArrayGraph)) :=
  cases.mapM fun c => do
    let p ← c.compile
    pure (c.name, p.plan.graph)

def sourceVectors? (name : String) : Option (List (List Vec)) := do
  let c ← cases.find? (·.name == name)
  pure (c.vectors.map fun xs => [xs])

def checkSourceExpected (name : String) (inputs outputs : List Vec) : Bool :=
  match cases.find? (·.name == name) with
  | none => true
  | some c => outputs == [(inputs.getD 0 []).map c.reference]

def refusalCases : List (String × Term) :=
  [ ("unbounded-add", .lam (.binary .add (.bound 0) (.nat 1)))
  , ("wrong-modulus", .lam (.binary .modulo (.binary .add (.bound 0) (.nat 1)) (.nat 13)))
  , ("oversized-literal", .lam (.nat (2^64)))
  , ("self-read", .lam (.get (.bound 2) "run"))
  , ("unsupported-divide", .lam (.binary .divide (.bound 0) (.nat 2)))
  , ("not-a-method", .nat 7) ]

/-- Refusals are executed during emission; names and actual compiler diagnostics are retained. -/
def refusalResults : List (String × Except String Unit) :=
  refusalCases.map fun (name, body) =>
    (name, (compileMember (composition body) "run" 4).map (fun _ => ()))

def checkRefusals : Except String Unit := do
  for (name, result) in refusalResults do
    match result with
    | .error _ => pure ()
    | .ok _ => throw s!"source compiler incorrectly accepted {name}"

end Obend.Hardware.Gpu.SourcePrograms
end
