module
/- A user-supplied `obend emit` / `obend lower` book file reaches the GPU through its
pinned composition. We re-emit that composition, as `obend specialize` does; printed
book definitions are not a second authority. The selected member must pass the
Core4 scalar fragment recognizer. Input vectors are JSON signed integer arrays. -/
public import Obend.Hardware.Gpu.Source
public import Obend.Hardware.ArrayTyping
public import Obend.Hardware.Gpu.ArrayEmit
public import Obend.Logic.Obligation
@[expose] public section
namespace Obend.Hardware.Gpu.BookImport
open Lean Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayTyping
open Obend.Hardware.Gpu.Source
set_option autoImplicit false

/-- Read the existing book wire format, without inventing a parallel source parser. -/
def compositionOfJson (j : Json) : Except String Obend.Logic.Composition := do
  let code ← Obend.Logic.termOf (← j.getObjVal? "composition")
  let some C := Obend.Leaf.compositionOfCode code
    | throw "book's pinned composition does not decode"
  unless C.closedB do throw "book's pinned composition is not closed"
  return C

def textVec (xs : Vec) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.map fun v => toString v.toInt)

/-- Each row is a test vector for the selected unary member, mapped over that array.
All rows must share the compiled shape. -/
def readInputs (j : Json) : Except String (List Vec) := do
  let values ← fromJson? (α := List (List Int)) j
  unless !values.isEmpty do throw "inputs require at least one array argument"
  let n := (values.headD []).length
  unless values.all (fun xs => xs.length == n) do throw "input array shapes differ"
  return values.map (List.map (BitVec.ofInt 64))

/-- Reusable file workflow: compile the selected pinned member, check typing once,
and emit expected values from the source evaluator, checking the graph evaluator too. -/
def writeFile (book : System.FilePath) (member : String) (inputs out : System.FilePath)
    (plant : Plant := .none) : IO Unit := do
  let C ← IO.ofExcept (compositionOfJson (← IO.ofExcept (Json.parse (← IO.FS.readFile book))))
  let vectors ← IO.ofExcept (readInputs (← IO.ofExcept (Json.parse (← IO.FS.readFile inputs))))
  let size := (vectors.headD []).length
  let source ← IO.ofExcept (compileMember C member size)
  let typed ← IO.ofExcept (checkTypedGraph (wordTypes source.plan.graph) source.plan.graph)
  let g := typed.graph
  let mut lines : Array String := #[]
  for (xs, i) in vectors.zipIdx do
    let expected := (evalMapExec source.plan.scalar size #[xs.toArray]).toList
    let env := mkEnv g.lengths g.inputs [xs]
    let observed := evalGraphArr g ((List.range g.lengths.length).map fun w => (env w).toArray).toArray
    unless observed == [expected] do
      throw <| IO.userError s!"source/graph disagreement for member {member}, vector {i}"
    lines := lines.push s!"{i}\t{textVec xs}\t{textVec expected}"
  let p := typed.lower
  let _ ← ArrayEmit.write member p out plant
  IO.FS.writeFile (out / "expected.tsv") (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"compiled Leaf member {member} for arrays of length {size}"

/-- Export a small book in the same wire format as `obend emit`, for the file-workflow gate. -/
def writeExample (out : System.FilePath) : IO Unit := do
  let body := Binary.term .add (Binary.term .mul (.bound 0) (.nat 3)) (.nat 5)
  let C : Obend.Logic.Composition :=
    { top := { name := "GpuAffine", metadata := .record [], fields := [("run", .lam body)], flat := true }
      below := [], seed := [] }
  let B := Obend.Leaf.emit C
  let defs := B.defs.map fun d => Json.mkObj
    [("member", toJson d.member), ("slot", toJson d.slot), ("kind", toJson "method"),
     ("reads", toJson d.reads), ("code", Obend.Logic.termJson d.code)]
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "example.book.json") ((Json.mkObj
    [("object", toJson "GpuAffine"), ("composition", Obend.Logic.termJson C.code),
     ("slots", toJson B.slots), ("defs", Json.arr defs.toArray), ("statics", Json.arr #[])]).pretty ++ "\n")
  IO.FS.writeFile (out / "inputs.json") "[[0,1,2,63,64,255,-1,-9223372036854775808],[5,10,17,31,65,65535,-2,9223372036854775807]]\n"

end Obend.Hardware.Gpu.BookImport
