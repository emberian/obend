module
/-
# Obend.Hardware.Fabulous.Mac8 — the bitstream `hardware/fabulous/obend_ice40_mac8.bin` realizes `iceStickMac8`

`mac8Net` is the logic `obend fabric check` reads back from the bitstream FABulous's own flow builds
for `iceStickMac8` on the fabric of `hardware/fabulous/fabric.csv`. The two bit-level obligations of
`Obend.Hardware.Fabulous.Mac8Net`, instantiated here, are `StepRealizes` and `ResetRealizes` for it;
`fabric_realizes_module` turns them into agreement on every trace.
-/
public import Obend.Hardware.Fabulous.Mac8Net
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware Obend.Hardware.HDL

theorem mac8Net_topo : mac8Net.topo = true := by decide

theorem mac8_inputs_fit (c : Bool × (Nat → BitVec 64)) (h : InputsFit iceStickMac8 c) :
    (∃ a : BitVec 8, c.2 0 = a.setWidth 64) ∧ (∃ b : BitVec 8, c.2 1 = b.setWidth 64) ∧
      (∃ cc : BitVec 16, c.2 2 = cc.setWidth 64) :=
  ⟨exists_setWidth_of_lt _ (h 0), exists_setWidth_of_lt _ (h 1), exists_setWidth_of_lt _ (h 2)⟩

theorem mac8_regs_fit (regs : Nat → BitVec 64) (h : RegsFit iceStickMac8 regs) :
    (∃ r : BitVec 16, regs 0 = r.setWidth 64) ∧ (∃ r : BitVec 16, regs 1 = r.setWidth 64) ∧
      (∃ r : BitVec 16, regs 2 = r.setWidth 64) :=
  ⟨exists_setWidth_of_lt _ (h 0), exists_setWidth_of_lt _ (h 1), exists_setWidth_of_lt _ (h 2)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- One edge: the fabric's flops follow the module's registers through `mac8FlopMap`, and its output
pins show `mac_out`, for every in-width state and input. -/
theorem mac8_step_realizes : StepRealizes mac8Net iceStickMac8 mac8Pins (projOf mac8FlopMap) := by
  intro regs c hR hI
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨cc, hc⟩⟩ := mac8_inputs_fit c hI
  obtain ⟨⟨r0, hr0⟩, ⟨r1, hr1⟩, ⟨r2, hr2⟩⟩ := mac8_regs_fit regs hR
  have h := mac8_step_bv a b cc r0 r1 r2 c.1 (pinValues mac8Pins c) (projOf mac8FlopMap regs)
    (fun i => (mac8Net.gateVals (pinValues mac8Pins c) (projOf mac8FlopMap regs)).getD i false)
    (outPinValue mac8Pins (evalModuleOutputsW iceStickMac8 c.2 regs))
    (stepModuleRegs iceStickMac8 c.1 c.2 regs)
    (mac8_pins c a b cc ha hb hc) (mac8_proj regs r0 r1 r2 hr0 hr1 hr2)
    (mac8_module_step c.2 regs c.1 a b cc r0 r1 ha hb hc hr0 hr1)
    (mac8_outs c.2 regs r2 hr2)
    (by have hG := mac8Net.gatesHold_gateVals mac8Net_topo (pinValues mac8Pins c) (projOf mac8FlopMap regs)
        simp only [gatesHold, mac8Net, Lit.evalF, Nat.reduceAdd] at hG
        exact hG)
  refine ⟨mac8Net.step_eq_projOf mac8FlopMap _ _ _ rfl ?_, ?_⟩
  · have h1 := h.1
    simp only [mac8Net, mac8FlopMap, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      Flop.next, Lit.eval, Nat.reduceAdd] at h1 ⊢
    exact h1
  · have h2 := h.2
    simp only [Net.outputs, mac8Net, List.map_cons, List.map_nil, Lit.eval] at h2 ⊢
    exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A reset edge, from any flop state, leaves the flops holding the module's reset registers. -/
theorem mac8_reset_realizes : ResetRealizes mac8Net iceStickMac8 mac8Pins (projOf mac8FlopMap) := by
  intro q regs ins hI
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨cc, hc⟩⟩ := mac8_inputs_fit (true, ins) hI
  have h := mac8_reset_bv a b cc (pinValues mac8Pins (true, ins)) q
    (fun i => (mac8Net.gateVals (pinValues mac8Pins (true, ins)) q).getD i false)
    (stepModuleRegs iceStickMac8 true ins regs)
    (mac8_pins (true, ins) a b cc ha hb hc) (mac8_module_reset ins regs)
    (by have hG := mac8Net.gatesHold_gateVals mac8Net_topo (pinValues mac8Pins (true, ins)) (q)
        simp only [gatesHold, mac8Net, Lit.evalF, Nat.reduceAdd] at hG
        exact hG)
  refine mac8Net.step_eq_projOf mac8FlopMap _ _ _ rfl ?_
  have h1 := h
  simp only [mac8Net, mac8FlopMap, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    Flop.next, Lit.eval, Nat.reduceAdd] at h1 ⊢
  exact h1

theorem iceStickMac8_checkWidths : checkWidths iceStickMac8 = true := by decide

/-- **The bitstream realizes the module.** On every trace of in-width cycles, from any in-width
register file, the configured fabric (`mac8Net`, with its flops holding the registers through
`mac8FlopMap`) shows `iceStickMac8`'s `mac_out` on every cycle and ends holding its final registers. -/
theorem mac8_fabric_realizes_module :
    ∀ (tr : List (Bool × (Nat → BitVec 64))) (regs : Nat → BitVec 64),
      RegsFit iceStickMac8 regs → (∀ c ∈ tr, InputsFit iceStickMac8 c) →
      mac8Net.run (projOf mac8FlopMap regs) (tr.map (pinValues mac8Pins)) =
        ((moduleRun iceStickMac8 regs tr).1.map fun outs =>
            mac8Net.outs.map fun (p, _) => (p, outPinValue mac8Pins outs p),
         projOf mac8FlopMap (runModuleTrace iceStickMac8 regs tr)) :=
  fabric_realizes_module mac8Net iceStickMac8 mac8Pins (projOf mac8FlopMap) iceStickMac8_checkWidths
    mac8_step_realizes

theorem mac8_reset_fits (ins regs : Nat → BitVec 64) :
    RegsFit iceStickMac8 (stepModuleRegs iceStickMac8 true ins regs) := by
  intro i
  obtain ⟨h0, h1, h2⟩ := mac8_module_reset ins regs
  rcases i with _ | _ | _ | i
  · rw [h0]; exact Nat.two_pow_pos _
  · rw [h1]; exact Nat.two_pow_pos _
  · rw [h2]; exact Nat.two_pow_pos _
  · have : regWidthOf iceStickMac8 (i + 3) = 64 := by simp [regWidthOf, iceStickMac8]
    rw [this]; exact BitVec.isLt _

/-- From power-up: whatever the flops hold, after a first reset cycle the fabric shows the module's
outputs on every later cycle. -/
theorem mac8_fabric_realizes_module_from_reset (q : Nat → Bool) (regs ins : Nat → BitVec 64)
    (tr : List (Bool × (Nat → BitVec 64))) (hIn0 : InputsFit iceStickMac8 (true, ins))
    (hIn : ∀ c ∈ tr, InputsFit iceStickMac8 c) :
    (mac8Net.run q (pinValues mac8Pins (true, ins) :: tr.map (pinValues mac8Pins))).1.tail =
      (moduleRun iceStickMac8 (stepModuleRegs iceStickMac8 true ins regs) tr).1.map
        (fun outs => mac8Net.outs.map fun (p, _) => (p, outPinValue mac8Pins outs p)) :=
  fabric_realizes_module_from_reset mac8Net iceStickMac8 mac8Pins (projOf mac8FlopMap)
    iceStickMac8_checkWidths mac8_step_realizes mac8_reset_realizes
    (fun regs ins _ => mac8_reset_fits ins regs)
    q regs ins tr hIn0 hIn

end Obend.Hardware.Fabulous
