module
/-
# Obend.Hardware.Fabulous.Mac8Tiles — the MAC bitstream realizes `iceStickMac8`, from the tile models

`Obend.Hardware.Fabulous.Mac8` proves that `mac8Net`, the logic `obend fabric check` decodes from the
bitstream, realizes `iceStickMac8`. This file removes the decoder from that statement:
`mac8_fabric_tiles_realize_module` is about any fabric whose tiles are the LEC'd tile models
(`lut4abModel`, `wioModel`), which carries the wires and pads of `mac8Cert`, and whose configuration
has the bits `mac8Cert.required mac8Net`. On every run of such a fabric (`FabricRun`: on each cycle the
wire values are consistent with the tile models, and the cells' flops follow `lut4cModule`), the output
pins show `iceStickMac8`'s `mac_out`. `mac8Cert_check` is decided by the kernel.

What `obend fabric check` still establishes outside Lean, and `verify_fabric.sh` runs: that the
bitstream's decoded frame bits are `mac8Cert.required mac8Net`, that `mac8Cert.wiresUsed` are wires of
FABulous's `pips.txt`, and that the tiles of `mac8Cert` have the types `fabric.csv` gives them.
-/
public import Obend.Hardware.Fabulous.Mac8
public import Obend.Hardware.Fabulous.Mac8Cert
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware Obend.Hardware.HDL

set_option maxRecDepth 100000 in
theorem mac8Cert_check : mac8Cert.check mac8Net = true := by decide +kernel

theorem mac8Cert_flops_length : mac8Cert.flops.length = mac8FlopMap.length := by decide

theorem mac8Cert_q (Q : Node → Bool) (regs : Nat → BitVec 64)
    (hQ : ∀ k < mac8Cert.flops.length, Q (mac8Cert.flopNode k) = projOf mac8FlopMap regs k) :
    mac8Cert.q Q = projOf mac8FlopMap regs := by
  funext k
  by_cases hk : k < mac8Cert.flops.length
  · simp only [Cert.q, hk, ite_true]; exact hQ k hk
  · have : mac8FlopMap[k]? = none := List.getElem?_eq_none (by rw [← mac8Cert_flops_length]; omega)
    simp [Cert.q, hk, projOf, this]

/-- **The fabric, from its tile models, realizes the module.** On a grid with `mac8Cert`'s tile models,
wires and pads, configured with the bits it requires, every run whose cells' flops start holding an
in-width register file shows `iceStickMac8`'s outputs on every cycle of every in-width trace. -/
theorem mac8_fabric_tiles_realize_module (G : Grid) (b : Bits)
    (hT : ∀ e ∈ mac8Cert.tiles, G.tile e.1.1 e.1.2 = mac8Cert.models[e.2]?)
    (hWires : ∀ e ∈ mac8Cert.wiresUsed, e ∈ G.wires) (hPads : ∀ e ∈ mac8Cert.pads, e ∈ G.pads)
    (hBits : ∀ r ∈ mac8Cert.required mac8Net, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    (tr : List (Bool × (Nat → BitVec 64))) (regs : Nat → BitVec 64)
    (hR : RegsFit iceStickMac8 regs) (hI : ∀ c ∈ tr, InputsFit iceStickMac8 c)
    (Q : Node → Bool) (hQ : ∀ k < mac8Cert.flops.length, Q (mac8Cert.flopNode k) = projOf mac8FlopMap regs k)
    (σs : List (Node → Bool)) (hLen : σs.length = tr.length)
    (hRun : FabricRun G b Q ((tr.map (pinValues mac8Pins)).zip σs)) :
    ((tr.map (pinValues mac8Pins)).zip σs).map (fun c => mac8Cert.observe c.2) =
      (moduleRun iceStickMac8 regs tr).1.map fun outs =>
        mac8Net.outs.map fun (p, _) => (p, outPinValue mac8Pins outs p) := by
  rw [fabric_run_eq mac8Cert mac8Net G b mac8Cert_check mac8Net_topo hT hWires hPads hBits _ Q hRun,
    List.map_fst_zip (by simp [hLen]), mac8Cert_q Q regs hQ, mac8_fabric_realizes_module tr regs hR hI]

/-- From power-up: whatever the cells' flops hold, after a first reset cycle the fabric shows the
module's outputs on every later cycle. -/
theorem mac8_fabric_tiles_realize_module_from_reset (G : Grid) (b : Bits)
    (hT : ∀ e ∈ mac8Cert.tiles, G.tile e.1.1 e.1.2 = mac8Cert.models[e.2]?)
    (hWires : ∀ e ∈ mac8Cert.wiresUsed, e ∈ G.wires) (hPads : ∀ e ∈ mac8Cert.pads, e ∈ G.pads)
    (hBits : ∀ r ∈ mac8Cert.required mac8Net, b r.1 r.2.1 r.2.2.1 = r.2.2.2)
    (Q : Node → Bool) (regs ins : Nat → BitVec 64) (tr : List (Bool × (Nat → BitVec 64)))
    (hIn0 : InputsFit iceStickMac8 (true, ins)) (hIn : ∀ c ∈ tr, InputsFit iceStickMac8 c)
    (σ0 : Node → Bool) (σs : List (Node → Bool)) (hLen : σs.length = tr.length)
    (hRun : FabricRun G b Q ((pinValues mac8Pins (true, ins), σ0) :: (tr.map (pinValues mac8Pins)).zip σs)) :
    (((tr.map (pinValues mac8Pins)).zip σs).map fun c => mac8Cert.observe c.2) =
      (moduleRun iceStickMac8 (stepModuleRegs iceStickMac8 true ins regs) tr).1.map
        (fun outs => mac8Net.outs.map fun (p, _) => (p, outPinValue mac8Pins outs p)) := by
  have h := fabric_run_eq mac8Cert mac8Net G b mac8Cert_check mac8Net_topo hT hWires hPads hBits _ Q hRun
  have h' := congrArg List.tail h
  simp only [List.map_cons, List.tail_cons] at h'
  rw [h', List.map_fst_zip (by simp [hLen])]
  exact mac8_fabric_realizes_module_from_reset (mac8Cert.q Q) regs ins tr hIn0 hIn

end Obend.Hardware.Fabulous
