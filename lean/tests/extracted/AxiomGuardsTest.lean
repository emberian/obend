/-
# Extracted Choice-Free Axiom Guards (`AxiomGuardsTest`)

Compile-time `#guard_msgs ... #print axioms` checks evicted from Tier-1 library modules
(`Obend.Core.Data`, `Obend.Core.MachineFast`, `Obend.Digest.Cshake256.Fast`) so Tier-1 builds
stay free of `#guard_msgs` commands while still pinning exact choice-free axiom footprints
(`[propext, Quot.sound]`, or zero axioms) across the full transitive proof closure.
-/
import Obend.Core.Data
import Obend.Core.MachineFast
import Obend.Digest.Cshake256.Fast

/--
info: 'Obend.Core.Data.forceWith_eq_fast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.Data.forceWith_eq_fast

/--
info: 'Obend.Core.MachineFast.allocateFieldsFast_eq' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.allocateFieldsFast_eq

/--
info: 'Obend.Core.MachineFast.stepRawFast_eq_stepRaw' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.stepRawFast_eq_stepRaw

/--
info: 'Obend.Core.MachineFast.stepRaw_eq_fast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.stepRaw_eq_fast

/--
info: 'Obend.Core.MachineFast.allocateFields_size' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.allocateFields_size

/--
info: 'Obend.Core.MachineFast.sizesAfter_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.sizesAfter_eq

/--
info: 'Obend.Core.MachineFast.stepFast_eq_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.stepFast_eq_step

/--
info: 'Obend.Core.MachineFast.step_eq_fast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.step_eq_fast

/--
info: 'Obend.Core.MachineFast.runFrom_eq_runBounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.runFrom_eq_runBounded

/--
info: 'Obend.Core.MachineFast.runBounded_eq_fast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.runBounded_eq_fast

/--
info: 'Obend.Core.MachineFast.step_of_moving' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.step_of_moving

/--
info: 'Obend.Core.MachineFast.runBounded_zero_of_moving' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.runBounded_zero_of_moving

/--
info: 'Obend.Core.MachineFast.runBounded_zero_of_stopped' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.runBounded_zero_of_stopped

/--
info: 'Obend.Core.MachineFast.forceWithFast_unique' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Core.MachineFast.forceWithFast_unique

/-- info: 'Obend.Digest.Cshake256.Fast.squeeze_fast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Obend.Digest.Cshake256.Fast.squeeze_fast_eq
