module
import Lean
import all Aeneas.Elab.Attrs
import all Lean.Util.CollectAxioms

open Lean

/-- Runtime census of the `ObendKeccak` MIR + `Obend.Digest` spec-weld import-all environment. -/
public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../lean/.lake/build/lib/lean"]
  let imported ← importModules #[
    { module := `AuditMirAxioms, importAll := true },
    { module := `ObendKeccakSpecWeld, importAll := true }
  ] {}
  let env := imported.setExporting false
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negative, checked, theorems, modules, failures) := CollectAxioms.runM (env.setExporting false) do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut theorems := 0
    let mut modules : Array Name := #[]
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if owner.startsWith "Aeneas.Elab." &&
          (isDeclMeta env name || isDeclMeta env name.getPrefix) then continue
        if owner == "Aeneas" || owner.startsWith "Aeneas." ||
            owner == "ObendKeccak" || owner.startsWith "ObendKeccak." ||
            owner == "ObendKeccakMirProofs" || owner == "ObendKeccakSpecWeld" then
          checked := checked + 1
          if let some (.thmInfo _) := env.find? name then theorems := theorems + 1
          let ownerName := env.header.moduleNames[idx.toNat]!
          if !modules.contains ownerName then modules := modules.push ownerName
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then
            failures := failures.push (name, forbidden)
    return (negative, checked, theorems, modules, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "MIR axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  IO.println s!"MIR axiom audit: {checked} declarations, {theorems} theorems, {modules.size} modules; {failures.size} rejected"
  return if checked > 0 && failures.isEmpty then 0 else 1
