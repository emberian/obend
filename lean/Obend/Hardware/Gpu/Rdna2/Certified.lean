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

A block program (the NTT) is checked the same way by `certifyBlockDump`: its admission check
(`ArrayKernel.Program.check`), the waits, the decode, and `Block.certifyBlock` with each dispatch's LDS as
RADV allocated it (the dump's `LDS:` line); `certifyBlockDump_sound` says the model's final wire buffer
holds every device array element `evalProgram` computes, for every memory the host binds.
-/
module
public import Obend.Hardware.Gpu.Rdna2.CertSound
public import Obend.Hardware.Gpu.Rdna2.Residuals
public import Obend.Hardware.Gpu.Rdna2.Check
public import Obend.Hardware.Gpu.Rdna2.Waitcnt
public import Obend.Hardware.SquareGraphs
public import Obend.Hardware.Gpu.Rdna2.Block
public import Obend.Hardware.Gpu.Ntt
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
        ∃ m, runDispatch (progs.zip (p.stages.map fun s => (s.threads, 0))) (memOf p.words p.consts p.tables flat) = some m ∧
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

/-- The check of a graph of `SquareGraphs.graphs` by name (what the pins and the gate run): its typed
graph, built as the emitter builds it, certified against the dump. -/
def certifyNamed (name : String) (isa : String) : Bool :=
  match Obend.Hardware.SquareGraphs.graphs.find? (·.name == name) with
  | some c => match c.build () with
    | .ok tg => certifyDump tg.graph isa
    | .error _ => false
  | none => false

theorem certifyNamed_sound (name isa : String) (h : certifyNamed name isa = true) :
    ∃ c tg, Obend.Hardware.SquareGraphs.graphs.find? (·.name == name) = some c ∧ c.build () = .ok tg ∧
      certifyDump tg.graph isa = true := by
  unfold certifyNamed at h
  split at h
  · rename_i c hf
    split at h
    · rename_i tg hb; exact ⟨c, tg, hf, hb, h⟩
    · simp at h
  · simp at h

/-! ## Block programs -/

open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower Block in
/-- The check of one dumped block program: admitted, waited for, decoded, certified with each dispatch's
LDS (the dump's resource line, in dwords). -/
def certifyBlockDump (p : ArrayKernel.Program) (isa : String) : Bool :=
  (match p.check with | .ok () => true | .error _ => false) && checkWaitcntDump isa &&
    match progsOf isa with
    | some progs => certifyBlock p ((parseDumpLds isa).toList.map (· / 4)) progs Residuals.all
    | none => false

open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower Block in
theorem certifyBlockDump_sound (p : ArrayKernel.Program) (isa : String) (h : certifyBlockDump p isa = true) :
    checkWaitcntDump isa = true ∧ ∃ progs, progsOf isa = some progs ∧
      ∀ (mem : ArrayKernel.Memory) (flat : FlatMemory), BlockLower.Good p mem → Represents p mem flat →
        ConstsOk (BlockEmit.constWords p).toArray flat →
        ∃ m, runDispatch (dispatchesOf (blockSpecs p ((parseDumpLds isa).toList.map (· / 4))) progs)
            (memOf (blockWords p) (BlockEmit.constWords p) [] (fun j => flat (.device, j))) = some m ∧
          ∀ a i, Valid p a i → (buffer p a).storage = .device →
            wordAt m (bufferBase p a + i) = ((evalProgram p mem).getD a #[]).getD i 0#64 := by
  unfold certifyBlockDump at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hchk, hw⟩, hc⟩ := h
  have hchk' : p.check = .ok () := by
    revert hchk; cases p.check with
    | ok u => intro _; rfl
    | error e => intro h; simp at h
  refine ⟨hw, ?_⟩
  split at hc
  · rename_i progs hp
    exact ⟨progs, hp, fun mem flat hg hf hk =>
      certifyBlock_eval p hchk' _ progs _ hc Residuals.all_hold mem flat hg hf hk⟩
  · simp at hc

/-- A block graph by name (`SquareGraphs.blockGraphs`): `Ntt.nttBlockProgram`, the emitter's sole NTT. -/
def certifyBlockNamed (name : String) (isa : String) : Bool :=
  match Obend.Hardware.SquareGraphs.blockGraphs.find? (·.1 == name) with
  | some (_, n) => certifyBlockDump (Obend.Hardware.Gpu.Ntt.nttBlockProgram n) isa
  | none => false

end Obend.Hardware.Gpu.Rdna2
