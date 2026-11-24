module
import Lean
import all Aeneas
import all Aeneas.Std.Types
import all Aeneas.Std.Containers
import all Aeneas.Elab.Attrs
import all ObendKeccak
import all ObendKeccak.Types
import all ObendKeccak.Funs
import all ObendKeccakMirProofs
import all ObendKeccakSpecWeld

/-!
# `AuditMirAxioms` — Compile-Time Kernel Axiom & Theorem Anchor Gate for `ObendKeccak`

Audits the entire transitive dependency closure of every definition and theorem in `Aeneas`,
`ObendKeccak`, `ObendKeccakMirProofs`, and `ObendKeccakSpecWeld`:
- Negative control: verifies `Classical.choice` is rejected;
- Theorem anchors: verifies every core MIR assurance & spec-weld theorem is present as a `.thmInfo`;
- Strict allowlist `{propext, Quot.sound}`: rejects `sorryAx`, `Classical.choice`,
  `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, and any custom `axiom`.
-/

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "MIR axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  let requiredTheorems : List Name := [
    ``ObendKeccak.MirProofs.keccak_f1600_total,
    ``ObendKeccak.MirProofs.zero_lanes_spec,
    ``ObendKeccak.MirProofs.keccak_sponge_scrub_spec,
    ``ObendKeccak.MirProofs.keccak_sponge_drop_zeroizes,
    ``ObendKeccak.MirProofs.midstate_drop_zeroizes,
    ``ObendKeccak.MirProofs.valid_rate_iff,
    ``ObendKeccak.MirProofs.valid_rate_refusal_witnesses,
    ``ObendKeccak.MirProofs.keccak_sponge_new_zero_suffix_fails,
    ``ObendKeccak.MirProofs.keccak_sponge_absorb_after_squeeze_fails,
    ``ObendKeccak.MirProofs.xof_absorb_after_squeeze_fails,
    ``ObendKeccak.MirProofs.keccak_sponge_from_midstate_roundtrip,
    ``ObendKeccak.MirProofs.bit_length_spec,
    ``ObendKeccak.SpecWeld.roundConstants_weld,
    ``ObendKeccak.SpecWeld.rotationOffsets_weld,
    ``ObendKeccak.SpecWeld.keccak_loop_body_eq_roundS,
    ``ObendKeccak.SpecWeld.keccak_f1600_eq_keccakS,
    ``ObendKeccak.SpecWeld.keccak_f1600_refines_spec,
    ``ObendKeccak.SpecWeld.encoded_width_refines_spec,
    ``ObendKeccak.SpecWeld.left_encode_refines_spec,
    ``ObendKeccak.SpecWeld.right_encode_refines_spec,
    ``ObendKeccak.SpecWeld.cshake256_empty_eq_shake256_mir,
    ``ObendKeccak.SpecWeld.squeeze_loop_32_refines_spec
  ]
  for name in requiredTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "MIR axiom audit missing theorem target: {name}"
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if owner.startsWith "Aeneas.Elab." &&
          (isDeclMeta env name || isDeclMeta env name.getPrefix) then continue
      if owner == "Aeneas" || owner.startsWith "Aeneas." ||
          owner == "ObendKeccak" || owner.startsWith "ObendKeccak." ||
          owner == "ObendKeccakMirProofs" || owner == "ObendKeccakSpecWeld" then
        checked := checked + 1
        let axioms ← withEnv env <| Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  if checked == 0 then
    throwError "MIR axiom audit has empty coverage"
  if rejected > 0 then
    throwError "MIR axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"MIR axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
