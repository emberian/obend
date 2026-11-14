module
/-
# `Obend/Teeth/Hardware/CliffordKernel.lean` — the Clifford theorems decided by the kernel (tier 2)

Three theorems of `Obend/Hardware/QuantumMatter.lean`, moved here on 2026-11-04 with their names and
statements unchanged: the spinor representation is an algebra homomorphism on all 256 blade pairs, the
braid gates commute with parity, and the Artin braid relation holds for every distinct triple of
Majorana modes. Each is a universal statement over `Fin 4` or `Fin 16`, proved by `decide +kernel`
over every case: 29 s, 13 s and 10 s of kernel type checking on bb2, which put the module at 102 s
against the 60 s tier-1 budget (review/DECISIONS-20261031.md). They are theorems, not fixtures, and
keep their names; they build with the teeth (`lake build Teeth`) until a structural proof exists. The
physics lane owns the mathematics; `tests/metasystem/QuantumCliffordClementsTest.lean` imports this
module for them. A `module`, so a module
may import it.
-/
public import Obend.Hardware.QuantumMatter

-- The theorems are the module's interface: a `module`'s plain `theorem` is private to it.
public section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Obend.Hardware.QuantumMatter
open Obend.Hardware.Photonics
open Obend.Hardware.OpenHypergraph
open Obend.Leaf
open Obend.Slot
open Obend.Slot.World
open Obend.Core.Term
open Obend.Analysis

/-- **Theorem (`cliffordToSpinorMatrix_algebra_hom`)**:
**Exact $4 \times 4$ Spinor Algebra Homomorphism Theorem for $Cl_4$ over $\mathbb{Z}[i]$**:
1. For ALL 16 basis blades $m \in \text{Fin } 16$, `cliffordToSpinorMatrix (cliffordBasisBlade m.val) = cliffordBladeSpinorMatrix m.val`.
2. For ALL $16 \times 16 = 256$ basis blade pairs $a, b \in \text{Fin } 16$, the spinor representation
   strictly respects the Koszul-signed Clifford product:
   $$\rho_{\mathbb{Z}[i]}(e_a) \cdot \rho_{\mathbb{Z}[i]}(e_b) = \operatorname{cliffordSign}(a, b) \cdot \rho_{\mathbb{Z}[i]}(e_{a \oplus b}).$$
3. For ALL $4 \times 4 = 16$ Majorana generator pairs $a, b \in \text{Fin } 4$,
   `cliffordToSpinorMatrix (cliffordMul (cliffordGamma a) (cliffordGamma b)) = (cliffordToSpinorMatrix (cliffordGamma a)).mul (cliffordToSpinorMatrix (cliffordGamma b))`.
4. $\rho_{\mathbb{Z}[i]}(1) = I_4$, and $\rho_{\mathbb{Z}[i]}(P) = \operatorname{diag}(1, 1, -1, -1)$
   (separating the $+1$ parity eigenspace $C_{\text{even}} = \{0, 1\}$ from the $-1$ parity eigenspace
   $C_{\text{odd}} = \{2, 3\}$)! -/
theorem cliffordToSpinorMatrix_algebra_hom :
    (∀ m : Fin 16,
      cliffordToSpinorMatrix (cliffordBasisBlade m.val) = cliffordBladeSpinorMatrix m.val) ∧
    (∀ a b : Fin 16,
      (cliffordBladeSpinorMatrix (a.val ^^^ b.val)).scale (cliffordSign a.val b.val) =
        (cliffordBladeSpinorMatrix a.val).mul (cliffordBladeSpinorMatrix b.val)) ∧
    (∀ a b : Fin 4,
      cliffordToSpinorMatrix (cliffordMul (cliffordGamma a) (cliffordGamma b)) =
        (cliffordToSpinorMatrix (cliffordGamma a)).mul
          (cliffordToSpinorMatrix (cliffordGamma b))) ∧
    cliffordToSpinorMatrix cliffordOne = GaussianMatrix.identity 4 ∧
    cliffordToSpinorMatrix cliffordParity =
      { dim := 4
      , rows :=
          [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] ] } := by
  have h1 : (List.range 16).all (fun m =>
      GaussianMatrix.beq (cliffordToSpinorMatrix (cliffordBasisBlade m))
                         (cliffordBladeSpinorMatrix m)) = true := by
    decide +kernel
  have h2 : (List.range 16).all (fun a =>
      (List.range 16).all (fun b =>
        GaussianMatrix.beq ((cliffordBladeSpinorMatrix (a ^^^ b)).scale (cliffordSign a b))
                           ((cliffordBladeSpinorMatrix a).mul (cliffordBladeSpinorMatrix b)))) = true := by
    decide +kernel
  have h3 : (List.range 4).all (fun a =>
      (List.range 4).all (fun b =>
        GaussianMatrix.beq (cliffordToSpinorMatrix (cliffordMul (cliffordBasisBlade (1 <<< a)) (cliffordBasisBlade (1 <<< b))))
          ((cliffordToSpinorMatrix (cliffordBasisBlade (1 <<< a))).mul
            (cliffordToSpinorMatrix (cliffordBasisBlade (1 <<< b)))))) = true := by
    decide +kernel
  rw [list_all_iff_forall] at h1 h2 h3
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro m
    exact GaussianMatrix.eq_of_beq (h1 m.val (List.mem_range.mpr m.isLt))
  · intro a b
    have hRow := (list_all_iff_forall _ (List.range 16)).mp (h2 a.val (List.mem_range.mpr a.isLt))
    exact GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))
  · intro a b
    have hRow := (list_all_iff_forall _ (List.range 4)).mp (h3 a.val (List.mem_range.mpr a.isLt))
    exact GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))

/-- **Theorem (`majoranaBraid_preserves_parity`)**:
For all Majorana modes $a, b \in \text{Fin } 4$, the braid gate $T_{a,b}$ commutes with total fermion
parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$ both in $Cl_4$ and in the $4 \times 4$ spinor representation:
$$\text{commutesWithParity}(T_{a,b}) = \text{true} \;\wedge\; \rho(T_{a,b}) \rho(P) = \rho(P) \rho(T_{a,b}).$$ -/
theorem majoranaBraid_preserves_parity (a b : Fin 4) :
    commutesWithParity (majoranaBraidElem a b) = true ∧
    commutesWithParity (majoranaBraidAdjElem a b) = true ∧
    (spinorBraidGate a b).mul spinorChiralParity = spinorChiralParity.mul (spinorBraidGate a b) := by
  revert a b
  decide +kernel

/-- **Theorem (`majoranaBraid_artin_relation`)**:
**Non-Abelian Artin Braid Group Relation ($T_{a,b} T_{b,c} T_{a,b} = T_{b,c} T_{a,b} T_{b,c}$)**:
For all pairwise distinct Majorana zero modes $a, b, c \in \text{Fin } 4$ ($a \neq b$, $b \neq c$, $a \neq c$),
the braiding generators satisfy the non-Abelian Artin braid relation in both $Cl_4$ and $M_4(\mathbb{Z}[i])$,
while failing to commute ($T_{a,b} T_{b,c} \neq T_{b,c} T_{a,b}$)! -/
theorem majoranaBraid_artin_relation (a b c : Fin 4) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cliffordMul (cliffordMul (majoranaBraidElem a b) (majoranaBraidElem b c)) (majoranaBraidElem a b) =
      cliffordMul (cliffordMul (majoranaBraidElem b c) (majoranaBraidElem a b)) (majoranaBraidElem b c) ∧
    ((spinorBraidGate a b).mul (spinorBraidGate b c)).mul (spinorBraidGate a b) =
      ((spinorBraidGate b c).mul (spinorBraidGate a b)).mul (spinorBraidGate b c) ∧
    cliffordMul (majoranaBraidElem a b) (majoranaBraidElem b c) ≠
      cliffordMul (majoranaBraidElem b c) (majoranaBraidElem a b) := by
  revert a b c hab hbc hac
  decide +kernel

end Obend.Hardware.QuantumMatter

end
