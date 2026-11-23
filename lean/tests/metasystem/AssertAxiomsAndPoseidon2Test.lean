import Obend.AssertAxioms
import Obend.Crypto.Poseidon2Goldilocks

open Lean Elab Command

-- Place each fixture in a temporary package module and discard its environment
-- after the command, including any synthetic declaration.
elab "#in_census_fixture " cmd:command : command => withoutModifyingEnv do
  modifyEnv (·.setMainModule `Obend.CensusFixture)
  elabCommand cmd

theorem genuineOracle : (List.range 17).length = 17 := by native_decide
#guard_msgs (drop info) in
#in_census_fixture #assert_axioms_tree

elab "#check_oracle_fixture " id:ident ty:term : command => withoutModifyingEnv do
  let type ← liftTermElabM do
    let e ← Term.elabType ty
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  liftCoreM <| addDecl (.axiomDecl { name := id.getId, levelParams := [], type, isUnsafe := false })
  elabCommand (← `(#assert_axioms_tree))

/-- error: Obend._native.badType does not assert a closed Bool equal to true -/
#guard_msgs in
#in_census_fixture #check_oracle_fixture Obend._native.badType False

/-- error: Obend._native.badValue evaluates to false -/
#guard_msgs in
#in_census_fixture #check_oracle_fixture Obend._native.badValue (false = true)

namespace Obend.Crypto.Poseidon2Regression
open Obend.Apps.ZkNtt Obend.Crypto.Fast

private def state12Scale (c : Goldilocks) (v : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Scale c v.b0, lane4Scale c v.b1, lane4Scale c v.b2⟩

/-- Superseded internal diffusion matrix `diag(-2, 1, 2, 4, ..., 1024) + 1·1ᵀ` (first diagonal entry
    `-2`; the deployed `applyMI` uses `-64`). Kept only as the object of the tooth below. -/
private def applyMIFirstEntryNegTwo (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) st.b0.x0) s,
    Goldilocks.add st.b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) s⟩⟩

/-- Explicit 12-lane Goldilocks eigenvector of `applyMIFirstEntryNegTwo` for eigenvalue
    `λ₀ = 8914261387277420341`. -/
private def miRationalEigvec0 : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 8415733694666260766, Goldilocks.ofNat 10081604446170657914,
    Goldilocks.ofNat 13429757962329074280, Goldilocks.ofNat 7212905167159261059⟩,
   ⟨Goldilocks.ofNat 7177536167446655380, Goldilocks.ofNat 16173559831921257667,
    Goldilocks.ofNat 11410676009809774369, Goldilocks.ofNat 263994636750658321⟩,
   ⟨Goldilocks.ofNat 11338638786567724180, Goldilocks.ofNat 17416777037312523837,
    Goldilocks.ofNat 8867871345638664998, Goldilocks.ofNat 17338153400129577477⟩⟩

/-- `#tooth` **The superseded `V[0] = -2` internal matrix has a rational eigenvector over Goldilocks**:
    `applyMIFirstEntryNegTwo miRationalEigvec0 = λ₀ · miRationalEigvec0` with `miRationalEigvec0 ≠ 0`, so
    `diag(-2, 1, 2, ..., 1024) + 1·1ᵀ` has a reducible characteristic polynomial over `𝔽_p`. The same
    vector is not an eigenvector of the deployed `applyMI` for `λ₀`. -/
theorem oldEigenlineRegression :
    miRationalEigvec0 ≠ ⟨lane4Zero, lane4Zero, lane4Zero⟩ ∧
    applyMIFirstEntryNegTwo miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0 ∧
    ¬ (applyMI miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0) := by decide +kernel

/-- The new matrix sends the old eigenvector outside its entire line. The first
two coordinates already give a nonzero two-by-two minor. -/
theorem newMatrixBreaksOldEigenline (c : Goldilocks) :
    applyMI miRationalEigvec0 ≠ state12Scale c miRationalEigvec0 := by
  let v := miRationalEigvec0
  have minor : Goldilocks.mul (applyMI v).b0.x0 v.b0.x1 ≠
      Goldilocks.mul (applyMI v).b0.x1 v.b0.x0 := by decide +kernel
  intro h
  apply minor
  change applyMI v = state12Scale c v at h
  rw [h]
  change CommRingOps.mul (CommRingOps.mul c v.b0.x0) v.b0.x1 =
    CommRingOps.mul (CommRingOps.mul c v.b0.x1) v.b0.x0
  rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm v.b0.x0]

end Obend.Crypto.Poseidon2Regression
