module
/-
SOAC gate programs. These are tests, not specialized theorem statements. Every graph
composes an elementwise producer, all four monoids, both scan conventions and segmented
variants, then a gather consumer. Expected outputs are independently recomputed with
`List.foldl`, `List.scanl` and splitting input lists at segment boundaries.
-/
public import Obend.Hardware.Gpu.ArrayPrograms
@[expose] public section
namespace Obend.Hardware.Gpu.SoacPrograms
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArrayPrograms
set_option autoImplicit false

def descriptors (lengths : List Nat) : List (ReduceOp × FoldShape) :=
  [.add, .mul, .band, .bor].flatMap fun op =>
    [(.reduce lengths.sum), (.scan lengths.sum .inclusive), (.scan lengths.sum .exclusive),
     (.segReduce lengths), (.segScan lengths .inclusive), (.segScan lengths .exclusive)].map (op, ·)

/-- Source lets, including the producer and gather consumer, are compiled together. -/
def source (lengths : List Nat) : ArraySource.Program :=
  let n := lengths.sum
  sourceBuild (fun inputs => do
    let x := inputs.getD 0 0
    let doubled ← map2 n (.scalar .add) x x
    let folds ← (descriptors lengths).mapM fun (op, shape) => bindSource (.fold op shape doubled)
    let reversed ← gather ⟨n, n, (List.range n).reverse⟩ (folds.getD 1 0)
    pure (folds ++ [reversed])) [n]

def graph (lengths : List Nat) : ArrayGraph := ArraySource.compile [lengths.sum] (source lengths)

def cases : List (String × List Nat) :=
  [("soac-boundaries", [0, 1, 3, 0, 2, 2, 0]),
   ("soac-empty", [0, 0, 0]),
   ("soac-no-segments", []),
   ("soac-single-65536", [65536]),
   ("soac-segments-64x1024", List.replicate 64 1024)]

def soacSources : List (String × List Nat × ArraySource.Program) :=
  cases.map fun (name, ns) => (name, [ns.sum], source ns)

def soacGraphs : List (String × ArrayGraph) := cases.map fun (name, ns) => (name, graph ns)

/-- An independent, ordinary list reference; not the prefix-range model or its cached executor. -/
def reference (op : ReduceOp) (mode : Option ScanMode) (xs : Vec) : Vec :=
  match mode with
  | none => [xs.foldl op.combine op.identity]
  | some .inclusive => (xs.scanl op.combine op.identity).drop 1
  | some .exclusive => (xs.scanl op.combine op.identity).take xs.length

def segmentedReference (op : ReduceOp) (mode : Option ScanMode) : List Nat → Vec → Vec
  | [], _ => []
  | n :: ns, xs => reference op mode (xs.take n) ++ segmentedReference op mode ns (xs.drop n)

def expected (lengths : List Nat) (input : Vec) : List Vec :=
  let xs := input.map fun x => x + x
  let outputs := descriptors lengths |>.map fun (op, shape) =>
    match shape with
    | .reduce _ => reference op none xs
    | .scan _ mode => reference op (some mode) xs
    | .segReduce ns => segmentedReference op none ns xs
    | .segScan ns mode => segmentedReference op (some mode) ns xs
  outputs ++ [(reference .add (some .inclusive) xs).reverse]

def checkSoacExpected (name : String) (inputs outputs : List Vec) : Bool :=
  match cases.find? (·.1 == name) with
  | none => true
  | some (_, ns) => outputs == expected ns (inputs.getD 0 [])

end Obend.Hardware.Gpu.SoacPrograms
