module
/-
Executable regression checks for GPU buffer allocation. These are small examples and planted faults,
not universal claims: `Gpu.lowerArrayToGpu_sound` and the stage race theorems carry those claims.
The emitter's `check-layout` command runs these checks before device verification.
-/
public import Obend.Hardware.Gpu
@[expose] public section

namespace Obend.Hardware.Gpu
open Obend.Hardware.ArrayHypergraph

namespace LayoutChecks

def mapEdge (id dst : Nat) : ArrayEdge :=
  ⟨id, .map 4 (ElemProg.single (.scalar .add) [0, 0] dst), [0, 0], dst⟩

/-- An unused logical wire must not consume physical storage. -/
def lastMap : ArrayGraph :=
  ⟨[4, 4, 1024], [0], [1], [mapEdge 0 1]⟩

def lastGather : ArrayGraph :=
  ⟨[4, 4], [0], [1], [⟨0, .gather ⟨4, 4, [3, 2, 1, 0]⟩, [0], 1⟩]⟩

def sharedSource : ArrayGraph :=
  ⟨[4, 4, 4], [0], [1, 2], [mapEdge 0 1, mapEdge 1 2]⟩

def lastConcat : ArrayGraph :=
  ⟨[2, 2, 4], [0, 1], [2], [⟨0, .concat, [0, 1], 2⟩]⟩

/-- Old input storage becomes available after a gather finishes, even when the next operation is
also a gather; neither individual gather may overwrite its own source. -/
def gatherChain : ArrayGraph :=
  ⟨[4, 4, 4], [0], [2],
    [⟨0, .gather ⟨4, 4, [3, 2, 1, 0]⟩, [0], 1⟩,
     ⟨1, .gather ⟨4, 4, [3, 2, 1, 0]⟩, [1], 2⟩]⟩

end LayoutChecks
open LayoutChecks

/-- Names are retained so a failed check reports its actual allocation obligation. -/
def layoutCheckResults : List (String × Bool) :=
  let m := gpuLayout lastMap
  let g := gpuLayout lastGather
  let s := gpuLayout sharedSource
  let c := gpuLayout lastConcat
  let chain := gpuLayout gatherChain
  [ ("sole final map consumer reuses source", lastMap.wf && layoutOk lastMap && m.base 0 == m.base 1)
  , ("dead logical wire has no allocation", m.words == 4)
  , ("gather cannot overwrite source", lastGather.wf && layoutOk lastGather && g.base 0 != g.base 1 && g.words == 8)
  , ("same-stage reader prevents takeover", sharedSource.wf && layoutOk sharedSource &&
      s.base 0 != s.base 1 && s.base 0 != s.base 2 && s.base 1 != s.base 2)
  , ("concat cannot overwrite either source", lastConcat.wf && layoutOk lastConcat &&
      c.base 2 != c.base 0 && c.base 2 != c.base 1)
  , ("dead buffer reused by later gather", gatherChain.wf && layoutOk gatherChain &&
      chain.base 0 == chain.base 2 && chain.words == 8)
  , ("poisoned gather overlap refused", !(checkLayout lastGather ⟨#[0, 0], 4⟩))
  , ("poisoned shared reader overlap refused", !(checkLayout sharedSource ⟨#[0, 0, 4], 8⟩))
  , ("poisoned undersized allocation refused", !(checkLayout lastMap { m with words := 3 }))
  ]

def layoutCheckFixtures : Bool := layoutCheckResults.all (·.2)

end Obend.Hardware.Gpu
