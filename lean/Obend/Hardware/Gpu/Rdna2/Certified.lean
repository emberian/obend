/-
# Obend.Hardware.Gpu.Rdna2.Certified — a dumped graph, certified

`certifyDump g isa` is the check run once per artifact: the graph is well formed, every stage of the
dump `isa` (`hardware/gpu/isa/<graph>.txt`, RADV's machine code) decodes, every load is waited for before
its destination is touched (`Waitcnt`), and `certify` accepts the decoded programs against the lowering of
`g` with the residuals of `Residuals` (generated, each proved). `certifyDump_sound` is what an accepted
check means, for every input: the programs, run on the model as the host dispatches them, succeed and
leave on the output wires what `evalGraph` computes. The waitcnt conjunct is what lets that be read as
the device's behaviour: the model completes a load when it issues, which is the device's only once every
consumer waits for it (manual 4.4; `Waitcnt`'s header). It is a hypothesis about the device, checked;
everything else is proved.
-/
module
public import Obend.Hardware.Gpu.Rdna2.CertSound
public import Obend.Hardware.Gpu.Rdna2.Residuals
public import Obend.Hardware.Gpu.Rdna2.Check
public import Obend.Hardware.Gpu.Rdna2.Waitcnt
public import Obend.Hardware.SquareGraphs
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Tm

/-- Every stage of a dump, decoded; `none` if one does not decode. -/
def progsOf (isa : String) : Option (List Program) :=
  (parseDump isa).toList.mapM fun ws => (decodeProgram (ws.flatMap id)).toOption

/-- The check of one dumped graph. -/
def certifyDump (g : ArrayGraph) (isa : String) : Bool :=
  g.wf && layoutOk g && boundsOk g && checkWaitcntDump isa &&
    match progsOf isa with
    | some progs => certify (lowerArrayToGpu g) progs Residuals.all
    | none => false

theorem certifyDump_sound (g : ArrayGraph) (isa : String) (h : certifyDump g isa = true) :
    checkWaitcntDump isa = true ∧ ∃ progs, progsOf isa = some progs ∧
      ∀ (env : Nat → Vec) (flat : Nat → Word), Good g.lengths env →
        Flat g.lengths (gpuLayout g).base (liveAt (layerGraph (fuseGraph g)) g.outputs) env flat →
        let p := lowerArrayToGpu g
        ∃ m, runDispatch (progs.zip (p.stages.map GpuStage.threads)) (memOf p.words p.consts p.tables flat) = some m ∧
          p.outputs.map (fun w => (List.range (p.wireLen.getD w 0)).map fun e => wordAt m (p.wireBase.getD w 0 + e))
            = evalGraph g env := by
  unfold certifyDump at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf, hlay⟩, hbd⟩, hwait⟩, hc⟩ := h
  refine ⟨hwait, ?_⟩
  split at hc
  · rename_i progs hp
    exact ⟨progs, hp, fun env flat hGood hFlat =>
      certified_outputs g hwf hlay hbd progs _ hc Residuals.all_hold env flat hGood hFlat⟩
  · simp at hc

/-- The check of a graph of `SquareGraphs.graphs` by name (what the pins and the gate run). -/
def certifyNamed (name : String) (isa : String) : Bool :=
  match Obend.Hardware.SquareGraphs.graphs.find? (·.1 == name) with
  | some (_, g, _) => certifyDump g isa
  | none => false

theorem certifyNamed_sound (name isa : String) (h : certifyNamed name isa = true) :
    ∃ g k, Obend.Hardware.SquareGraphs.graphs.find? (·.1 == name) = some (name, g, k) ∧ certifyDump g isa = true := by
  unfold certifyNamed at h
  split at h
  · rename_i n g k hf
    have := List.find?_some hf
    simp only [beq_iff_eq] at this
    subst this
    exact ⟨g, k, hf, h⟩
  · simp at h

end Obend.Hardware.Gpu.Rdna2
