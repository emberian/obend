module
/-
# Obend.Hardware.Device.DriftDiffusion — the 1D drift-diffusion system on a fabricated profile, as a judged certificate
The device is a 1D diode: the net doping `N(x)` is the output of a recipe (`Device/Wafer.lean`), the
unknowns are `ψ, n, p` at the nodes of a mesh, and the equations are Poisson and the two continuity
equations in the finite-volume Scharfetter–Gummel form (Scharfetter–Gummel 1969; Selberherr 1984
§6.1, eqs. 6.1-39…43), Boltzmann statistics, Caughey–Thomas mobility, SRH recombination, ohmic
contacts. The external producer is devsim 2.11.2 (`apps/sky130-diode/devsim/run_diode.py`): it solves. The
kernel checks the residual of every equation at every node, the contact conditions, that the doping
on the mesh is the recipe's, and that the reported terminal current is the discrete solution's.
**Discretisation** (nodes `0…M−1` at depths `x_i`, edges `e = (i, i+1)`, `h_e = x_{i+1} − x_i`,
`V_i = (h_{i−1} + h_i)/2`, devsim's node volumes and unit edge couple):
* `Δ_e = (ψ_i − ψ_{i+1})/V_t`, `B_e = B(Δ_e)`, and `B(−Δ_e) = B_e + Δ_e` (the identity devsim uses).
* `Jn_e = q µn_e V_t/h_e · (n_{i+1}(B_e + Δ_e) − n_i B_e)`,
  `Jp_e = −q µp_e V_t/h_e · (p_{i+1} B_e − p_i (B_e + Δ_e))`, `µ_e` the mean of the node mobilities.
* `D_e = ε (ψ_i − ψ_{i+1})/h_e`.
* Poisson at `i`: `F_ψ(i) = (D_i − D_{i−1}) − q (p_i − n_i + N_i) V_i`.
* Electrons: `F_n(i) = (Jn_i − Jn_{i−1}) − q U_i V_i`; holes: `F_p(i) = (Jp_i − Jp_{i−1}) + q U_i V_i`,
  `U_i = (n_i p_i − n_i²)/(τ_p (n_i + n_i) + τ_n (p_i + n_i))` (SRH, mid-gap trap).
* Contacts (`i = 0` at `V = bias`, `i = M−1` at `0`): `n p = n_i²`, `n − p = N`, `n = n_i e^{(ψ − V)/V_t}`.
**Where the transcendental functions enter and how.** `B_e` is never computed: each residual is a
`RealExpr` (`Analysis.RealAnalysis`) in the variables `b_e`, evaluated by `evalInterval` over the
environment `b_e ↦ bernEnclosure? Δ_e`; `evalInterval_sound` turns the one interval evaluation into the
statement for every table of Bernoulli values inside the enclosures (`Meaning.residuals`). The exponential
at the contacts and in `n_i` is `expEnclosure`. The mobility's fractional power is bracketed
(`CaugheyThomas.ratioOk`). So the certificate is the triple `(ψ, n, p)` plus the bracket witnesses
`r_n, r_p` and the recipe's step data; the checker's arithmetic is rational throughout and the two assumed
facts are those of `Device/Enclosure.lean`.
**Tolerances are the object's, not the checker's.** A residual `F` is accepted when `|F| ≤ tol · S`
with `S` the sum of the magnitudes of the terms that cancel in `F` (the residual of a converged double-
precision solution is `~10⁻¹⁶ S` from rounding alone; `tol = 10⁻⁷` is the value the sky130 fixtures
use and the planted certificates fail by eight orders).
**The theorems.** `Judge.sound` (`ddJudge`): an accepted certificate has `Meaning`. `terminal_current_bound`:
under `Meaning`, for every Bernoulli table in the enclosures and every edge `e`, the reported current
is within `tol · A · (S_J + Σ_{i ≤ e}(S_n(i) + S_p(i)))` of `A · J_e`: the terminal current is the
discrete solution's and is conserved along the device up to the residual budget, with every material
and process parameter free. `residual_sum_telescopes` is the exact identity behind it:
`F_n(i) + F_p(i) = J_i − J_{i−1}` for all values.
**Format `devsim-dd1d@1`**: object `DdSpec` (constants, recipe, mesh, bias, tolerances), certificate
`DdSolution`; planted bad certificate `badSpec`/`badSolution`: a uniform substrate whose certificate
claims a different doping at node 1, refused as `.doping 1` before any residual is looked at. The dose-
change test of the brief is the same clause at the sky130 recipe (`Obend/Teeth/Hardware/DeviceFixtures.lean`).
`slabSolution` is the same substrate's equilibrium solution, accepted by the kernel (`slab_accepted`).
**The judge's fields.** `refutes` is `.mesh` alone: the mesh belongs to the object, so that refusal
holds against every certificate. `Fragment` is the reference slab, where an accepted certificate is
exhibited; the interval evaluation over-approximates the residual's range, so no wider completeness
is claimed.
**The quasi-Fermi form (§8).** `DdQuasiFermiSolution` adds `φ_n, φ_p`; `checkDdQuasiFermi` checks the
same discrete system with every flux written as one product proportional to a quasi-Fermi increment
(`jnQuasiFermi_eq_jn`, `jpQuasiFermi_eq_jp`: equal to the Scharfetter–Gummel fluxes under the Bernoulli
laws), and `terminal_current_bound_quasiFermi` is the current theorem without the contact
cancellation. The variable names are built by `natName`, a structural decimal numeral, so that the
kernel can evaluate the checkers (`decide +kernel` on the slab here and on a 23-node diode in the
fixtures).
-/
public import Obend.Hardware.Device.Wafer
public import Obend.Judge.Class
public import Lean.Data.Json
public import Obend.Analysis.SosLyapunov
import all Obend.Hardware.Device.Constants
public section
namespace Obend.Hardware.Device
open Obend.Analysis Obend.Judge
set_option autoImplicit false
/-! ## 1. Object and certificate -/
/-- The device as the checker sees it. Lengths in cm, bias in V, area in cm². `tolRel` is the residual
and value tolerance, `mobDelta` the mobility bracket's relative width, `dealGroveTol` the oxidation
residual's. -/
structure DdSpec where
  si : SiliconConstants
  ctN : CaugheyThomas
  ctP : CaugheyThomas
  tauN : CanonicalRat
  tauP : CanonicalRat
  background : CanonicalRat
  recipe : List ProcessStep
  xCm : List CanonicalRat
  areaCm2 : CanonicalRat
  biasV : CanonicalRat
  tolRel : CanonicalRat
  mobDelta : CanonicalRat
  dealGroveTol : CanonicalRat
  deriving @[expose] DecidableEq, Repr
/-- The producer's output: the recipe's step data, `n_i`, the doping it put on the mesh (net and
total), the solution, the mobility bracket witnesses, and the terminal current (A) at node 0. -/
structure DdSolution where
  recipeCert : List StepCert
  ni : CanonicalRat
  doping : List CanonicalRat
  total : List CanonicalRat
  psi : List CanonicalRat
  n : List CanonicalRat
  p : List CanonicalRat
  rN : List CanonicalRat
  rP : List CanonicalRat
  currentA : CanonicalRat
  deriving @[expose] DecidableEq, Repr
namespace DdSpec
@[expose] def nodes (o : DdSpec) : Nat := o.xCm.length
def x (o : DdSpec) (i : Nat) : CanonicalRat := o.xCm.getD i 0
def h (o : DdSpec) (e : Nat) : CanonicalRat := o.x (e + 1) - o.x e
/-- `V_i = (h_{i−1} + h_i)/2` for an interior node. -/
def vol (o : DdSpec) (i : Nat) : CanonicalRat := (o.h (i - 1) + o.h i) / 2
def vt (o : DdSpec) : CanonicalRat := o.si.vt
def q (o : DdSpec) : CanonicalRat := o.si.q
def eps (o : DdSpec) : CanonicalRat := o.si.eps
/-- At least three nodes, strictly increasing. -/
def meshOk (o : DdSpec) : Bool :=
  decide (3 ≤ o.nodes) &&
  (List.range (o.nodes - 1)).all fun e => decide (0 < o.h e)
end DdSpec
namespace DdSolution
def psiAt (c : DdSolution) (i : Nat) : CanonicalRat := c.psi.getD i 0
def nAt (c : DdSolution) (i : Nat) : CanonicalRat := c.n.getD i 0
def pAt (c : DdSolution) (i : Nat) : CanonicalRat := c.p.getD i 0
def dopingAt (c : DdSolution) (i : Nat) : CanonicalRat := c.doping.getD i 0
def totalAt (c : DdSolution) (i : Nat) : CanonicalRat := c.total.getD i 0
def rNAt (c : DdSolution) (i : Nat) : CanonicalRat := c.rN.getD i 0
def rPAt (c : DdSolution) (i : Nat) : CanonicalRat := c.rP.getD i 0
/-- Every per-node list has the mesh's length. -/
def lengthsOk (c : DdSolution) (m : Nat) : Bool :=
  decide (c.doping.length = m) && decide (c.total.length = m) && decide (c.psi.length = m) &&
  decide (c.n.length = m) && decide (c.p.length = m) && decide (c.rN.length = m) && decide (c.rP.length = m)
end DdSolution
/-! ## 2. The discrete equations as `RealExpr`s in the Bernoulli variables -/
/-- One decimal digit. -/
def digitStr : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
/-- The decimal numeral of `n` by structural recursion on fuel (core's `Nat.repr` has no body the
kernel can unfold from a `module` file, and the certificates are checked by the kernel). -/
def decStr : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n => if n < 10 then digitStr n else decStr fuel (n / 10) ++ digitStr (n % 10)
def natName (n : Nat) : String := decStr (n + 1) n
/-- The name of edge `e`'s Bernoulli variable. -/
def bName (e : Nat) : String := "b" ++ natName e
/-- `Δ_e = (ψ_i − ψ_{i+1})/V_t`. -/
def delta (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat :=
  (c.psiAt e - c.psiAt (e + 1)) / o.vt
/-- `B(Δ_e)` and `B(−Δ_e) = B(Δ_e) + Δ_e`. -/
def bPos (e : Nat) : RealExpr := .var (bName e)
def bNeg (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr := .add (bPos e) (.const (delta o c e))
/-- Node mobilities from the bracketed ratios, and the edge mean. -/
def muN (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat := o.ctN.muOf (c.rNAt i)
def muP (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat := o.ctP.muOf (c.rPAt i)
def muNEdge (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := (muN o c e + muN o c (e + 1)) / 2
def muPEdge (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := (muP o c e + muP o c (e + 1)) / 2
/-- `q µ V_t / h_e`. -/
def cN (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := o.q * muNEdge o c e * o.vt / o.h e
def cP (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := o.q * muPEdge o c e * o.vt / o.h e
/-- `Jn_e = cN_e (n_{i+1} B(−Δ) − n_i B(Δ))`. -/
def jn (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr :=
  .mul (.const (cN o c e)) (.sub (.mul (.const (c.nAt (e + 1))) (bNeg o c e)) (.mul (.const (c.nAt e)) (bPos e)))
/-- `Jp_e = −cP_e (p_{i+1} B(Δ) − p_i B(−Δ))`. -/
def jp (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr :=
  .mul (.const (-(cP o c e))) (.sub (.mul (.const (c.pAt (e + 1))) (bPos e)) (.mul (.const (c.pAt e)) (bNeg o c e)))
/-- Total current on edge `e`. -/
def jTot (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr := .add (jn o c e) (jp o c e)
/-- `D_e = ε (ψ_i − ψ_{i+1})/h_e`. -/
def dFlux (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat :=
  o.eps * (c.psiAt e - c.psiAt (e + 1)) / o.h e
/-- SRH net recombination at node `i` (mid-gap trap, `n₁ = p₁ = n_i`). -/
def srhU (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat :=
  (c.nAt i * c.pAt i - c.ni * c.ni) / (o.tauP * (c.nAt i + c.ni) + o.tauN * (c.pAt i + c.ni))
/-- Poisson's residual at an interior node. -/
def fPsi (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
  .const ((dFlux o c i - dFlux o c (i - 1)) - o.q * (c.pAt i - c.nAt i + c.dopingAt i) * o.vol i)
/-- The electron continuity residual. -/
def fN (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
  .sub (.sub (jn o c i) (jn o c (i - 1))) (.const (o.q * srhU o c i * o.vol i))
/-- The hole continuity residual. -/
def fP (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
  .add (.sub (jp o c i) (jp o c (i - 1))) (.const (o.q * srhU o c i * o.vol i))
/-- **The exact identity**: `F_n(i) + F_p(i) = J_i − J_{i−1}` for every assignment. -/
theorem residual_sum_telescopes (o : DdSpec) (c : DdSolution) (i : Nat) (rho : String → CanonicalRat) :
    evalExpr rho (fN o c i) + evalExpr rho (fP o c i) = evalExpr rho (jTot o c i) - evalExpr rho (jTot o c (i - 1)) := by
  simp only [fN, fP, jTot, evalExpr]
  grind
/-! ## 3. Magnitude scales -/
end Obend.Hardware.Device
namespace Obend.Analysis.Interval
open Obend.Hardware.Device
/-- `max |lo| |hi|`. -/
def absMax (I : Interval) : CanonicalRat := max (ratAbs I.lo) (ratAbs I.hi)
/-- `[lo − tol·|lo|, hi + tol·|hi|]`. -/
def widenRel (I : Interval) (tol : CanonicalRat) : Interval :=
  ⟨I.lo - tol * ratAbs I.lo, I.hi + tol * ratAbs I.hi⟩
end Obend.Analysis.Interval
namespace Obend.Hardware.Device
open Obend.Analysis Obend.Judge
/-- The environment `b_e ↦ bernEnclosure? Δ_e`, `none` if any enclosure is unavailable. -/
def bernEnv? (o : DdSpec) (c : DdSolution) : Option (List (String × Interval)) :=
  (List.range (o.nodes - 1)).foldr (fun e acc => do
      let env ← acc
      let B ← bernEnclosure? (delta o c e)
      pure ((bName e, B) :: env))
    (some [])
/-- The magnitude of edge `e`'s electron-current terms under `env`. -/
def scaleJn (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  match env.lookup (bName e) with
  | some B => ratAbs (cN o c e) * (ratAbs (c.nAt (e + 1)) * Interval.absMax (Interval.add B (Interval.ofPoint (delta o c e)))
      + ratAbs (c.nAt e) * Interval.absMax B)
  | none => 0
def scaleJp (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  match env.lookup (bName e) with
  | some B => ratAbs (cP o c e) * (ratAbs (c.pAt (e + 1)) * Interval.absMax B
      + ratAbs (c.pAt e) * Interval.absMax (Interval.add B (Interval.ofPoint (delta o c e))))
  | none => 0
def scalePsi (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat :=
  ratAbs (dFlux o c i) + ratAbs (dFlux o c (i - 1)) +
  ratAbs (o.q * o.vol i) * (ratAbs (c.pAt i) + ratAbs (c.nAt i) + ratAbs (c.dopingAt i))
def scaleN (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJn o c env i + scaleJn o c env (i - 1) + ratAbs (o.q * srhU o c i * o.vol i)
def scaleP (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJp o c env i + scaleJp o c env (i - 1) + ratAbs (o.q * srhU o c i * o.vol i)
/-! ## 4. The checks -/
/-- The mesh doping is the recipe's: net and total at every node, within `tolRel`. -/
def dopingOk (o : DdSpec) (c : DdSolution) (w : WaferState) (i : Nat) : Bool :=
  (match w.dopingEnclosure? (o.x i) with
   | some I => decide (c.dopingAt i ∈ I.widenRel o.tolRel)
   | none => false) &&
  (match w.totalDopingEnclosure? (o.x i) with
   | some I => decide (c.totalAt i ∈ I.widenRel o.tolRel)
   | none => false)
/-- The mobility bracket witnesses at node `i`. -/
def mobilityOk (o : DdSpec) (c : DdSolution) (i : Nat) : Bool :=
  o.ctN.ratioOk (c.totalAt i) (c.rNAt i) o.mobDelta && o.ctP.ratioOk (c.totalAt i) (c.rPAt i) o.mobDelta
/-- An ohmic contact at node `i` held at `v`: `n, p > 0`, `np = n_i²`, `n − p = N`, `n = n_i e^{(ψ−v)/V_t}`,
each to `tolRel`. -/
def contactOk (o : DdSpec) (c : DdSolution) (i : Nat) (v : CanonicalRat) : Bool :=
  let n := c.nAt i
  let p := c.pAt i
  let N := c.dopingAt i
  decide (0 < n) && decide (0 < p) &&
  decide (ratAbs (n * p - c.ni * c.ni) ≤ o.tolRel * (c.ni * c.ni)) &&
  decide (ratAbs (n - p - N) ≤ o.tolRel * (ratAbs N + n + p)) &&
  decide (n ∈ (Interval.scale c.ni (expEnclosure ((c.psiAt i - v) / o.vt))).widenRel o.tolRel)
/-- The three residuals at interior node `i`, by interval evaluation. -/
def nodeOk (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : Bool :=
  match evalInterval env (fPsi o c i), evalInterval env (fN o c i), evalInterval env (fP o c i) with
  | some a, some b, some d =>
    a.within (o.tolRel * scalePsi o c i) && b.within (o.tolRel * scaleN o c env i) && d.within (o.tolRel * scaleP o c env i)
  | _, _, _ => false
/-- The reported current is `A · J_0` to `tolRel · A · S_J`. -/
def currentOk (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) : Bool :=
  match evalInterval env (jTot o c 0) with
  | some J =>
    (Interval.sub (Interval.ofPoint c.currentA) (Interval.scale o.areaCm2 J)).within
      (o.tolRel * o.areaCm2 * (scaleJn o c env 0 + scaleJp o c env 0))
  | none => false
/-- The refusal vocabulary. -/
inductive DdClause where
  | mesh
  | lengths
  | recipe
  | doping (i : Nat)
  | intrinsic
  | mobility (i : Nat)
  | bernoulli
  | contact (i : Nat)
  | poisson (i : Nat)
  | residual (i : Nat)
  | current
  | boltzmann (i : Nat)
  deriving DecidableEq, Repr
/-- First failing index of a per-node check. -/
def firstFailing (m : Nat) (f : Nat → Bool) : Option Nat :=
  (List.range m).find? fun i => !f i
/-- **The checker.** Mesh, lengths, the recipe, the doping, `n_i`, the mobility brackets, the Bernoulli
environment, the two contacts, every interior node, the current; the first failure names its clause. -/
def checkDd (o : DdSpec) (c : DdSolution) : Verdict DdClause :=
  let m := o.nodes
  if !o.meshOk then .refused .mesh [] else
  if !c.lengthsOk m then .refused .lengths [] else
  match runRecipe o.si.kBEv o.dealGroveTol (WaferState.bare o.background) o.recipe c.recipeCert with
  | none => .refused .recipe []
  | some w =>
    match firstFailing m (dopingOk o c w) with
    | some i => .refused (.doping i) [i]
    | none =>
    if !o.si.niOk c.ni then .refused .intrinsic [] else
    match firstFailing m (mobilityOk o c) with
    | some i => .refused (.mobility i) [i]
    | none =>
    match bernEnv? o c with
    | none => .refused .bernoulli []
    | some env =>
      if !contactOk o c 0 o.biasV then .refused (.contact 0) [0] else
      if !contactOk o c (m - 1) 0 then .refused (.contact (m - 1)) [m - 1] else
      match firstFailing (m - 2) (fun k => nodeOk o c env (k + 1)) with
      | some k => .refused (.residual (k + 1)) [k + 1]
      | none =>
        if !currentOk o c env then .refused .current [] else .ok
/-! ## 5. What an acceptance means -/
/-- `rho` is a table of Bernoulli values inside the enclosures. -/
@[expose] def BernTable (env : List (String × Interval)) (rho : String → CanonicalRat) : Prop :=
  ∀ v I, env.lookup v = some I → rho v ∈ I
/-- `−b ≤ a ∧ a ≤ b`. -/
@[expose] def AbsLe (a b : CanonicalRat) : Prop := -b ≤ a ∧ a ≤ b
/-- **The meaning of an accepted certificate.** -/
structure DdMeaning (o : DdSpec) (c : DdSolution) : Prop where
  mesh : o.meshOk = true
  lengths : c.lengthsOk o.nodes = true
  wafer : ∃ w, runRecipe o.si.kBEv o.dealGroveTol (WaferState.bare o.background) o.recipe c.recipeCert = some w ∧
    ∀ i < o.nodes, dopingOk o c w i = true
  intrinsic : o.si.niOk c.ni = true
  mobility : ∀ i < o.nodes, mobilityOk o c i = true
  env : ∃ env, bernEnv? o c = some env ∧
    contactOk o c 0 o.biasV = true ∧ contactOk o c (o.nodes - 1) 0 = true ∧
    (∀ rho, BernTable env rho →
      (∀ i, 1 ≤ i → i + 1 < o.nodes →
        AbsLe (evalExpr rho (fPsi o c i)) (o.tolRel * scalePsi o c i) ∧
        AbsLe (evalExpr rho (fN o c i)) (o.tolRel * scaleN o c env i) ∧
        AbsLe (evalExpr rho (fP o c i)) (o.tolRel * scaleP o c env i)) ∧
      AbsLe (c.currentA - o.areaCm2 * evalExpr rho (jTot o c 0))
        (o.tolRel * o.areaCm2 * (scaleJn o c env 0 + scaleJp o c env 0)))
theorem firstFailing_none {m : Nat} {f : Nat → Bool} (h : firstFailing m f = none) : ∀ i < m, f i = true := by
  intro i hi
  unfold firstFailing at h
  have := List.find?_eq_none.1 h i (List.mem_range.2 hi)
  simpa using this
theorem nodeOk_sound {o : DdSpec} {c : DdSolution} {env : List (String × Interval)} {i : Nat}
    (h : nodeOk o c env i = true) (rho : String → CanonicalRat) (hrho : BernTable env rho) :
    AbsLe (evalExpr rho (fPsi o c i)) (o.tolRel * scalePsi o c i) ∧
    AbsLe (evalExpr rho (fN o c i)) (o.tolRel * scaleN o c env i) ∧
    AbsLe (evalExpr rho (fP o c i)) (o.tolRel * scaleP o c env i) := by
  unfold nodeOk at h
  split at h
  · rename_i a b d ha hb hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨Interval.within_sound (evalInterval_sound env rho hrho _ _ ha) h1,
           Interval.within_sound (evalInterval_sound env rho hrho _ _ hb) h2,
           Interval.within_sound (evalInterval_sound env rho hrho _ _ hd) h3⟩
  · cases h
theorem currentOk_sound {o : DdSpec} {c : DdSolution} {env : List (String × Interval)}
    (h : currentOk o c env = true) (rho : String → CanonicalRat) (hrho : BernTable env rho) :
    AbsLe (c.currentA - o.areaCm2 * evalExpr rho (jTot o c 0))
      (o.tolRel * o.areaCm2 * (scaleJn o c env 0 + scaleJp o c env 0)) := by
  unfold currentOk at h
  split at h
  · rename_i J hJ
    have hmem := evalInterval_sound env rho hrho _ _ hJ
    exact Interval.within_sound (Interval.sub_mem (Interval.ofPoint_mem _) (Interval.scale_mem _ hmem)) h
  · cases h
/-- **Soundness of the checker.** -/
theorem checkDd_sound {o : DdSpec} {c : DdSolution} (h : checkDd o c = .ok) : DdMeaning o c := by
  unfold checkDd at h
  simp only at h
  split at h
  · cases h
  rename_i hmesh
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i w hw
  split at h
  · cases h
  rename_i hdop
  split at h
  · cases h
  rename_i hni
  split at h
  · cases h
  rename_i hmob
  split at h
  · cases h
  rename_i env henv
  split at h
  · cases h
  rename_i hc0
  split at h
  · cases h
  rename_i hc1
  split at h
  · cases h
  rename_i hnodes
  split at h
  · cases h
  rename_i hcur
  refine ⟨by simpa using hmesh, by simpa using hlen, ⟨w, hw, firstFailing_none hdop⟩, by simpa using hni,
    firstFailing_none hmob, env, henv, by simpa using hc0, by simpa using hc1, ?_⟩
  intro rho hrho
  refine ⟨?_, currentOk_sound (by simpa using hcur) rho hrho⟩
  intro i hi1 hi2
  have := firstFailing_none hnodes (i - 1) (by omega)
  have hi : i - 1 + 1 = i := by omega
  rw [hi] at this
  exact nodeOk_sound this rho hrho
/-! ## 6. The theorem that matters: the terminal current -/
/-- The residual budget of the first `e` interior nodes. -/
def currentBudget (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) : Nat → CanonicalRat
  | 0 => 0
  | e + 1 => currentBudget o c env e + o.tolRel * (scaleN o c env (e + 1) + scaleP o c env (e + 1))
theorem absLe_add {a b x y : CanonicalRat} (ha : AbsLe a x) (hb : AbsLe b y) : AbsLe (a + b) (x + y) := by
  unfold AbsLe at *
  grind
theorem absLe_sub {a b x y : CanonicalRat} (ha : AbsLe a x) (hb : AbsLe b y) : AbsLe (a - b) (x + y) := by
  unfold AbsLe at *
  grind
/-- Along the device: `|J_e − J_0| ≤ Σ_{i=1}^{e} tol (S_n(i) + S_p(i))`. -/
theorem current_conserved {o : DdSpec} {c : DdSolution} {env : List (String × Interval)} (rho : String → CanonicalRat)
    (hres : ∀ i, 1 ≤ i → i + 1 < o.nodes →
      AbsLe (evalExpr rho (fN o c i)) (o.tolRel * scaleN o c env i) ∧
      AbsLe (evalExpr rho (fP o c i)) (o.tolRel * scaleP o c env i)) :
    ∀ e, e + 1 < o.nodes → AbsLe (evalExpr rho (jTot o c e) - evalExpr rho (jTot o c 0)) (currentBudget o c env e)
  | 0, _ => by unfold AbsLe currentBudget; grind
  | e + 1, he => by
    have ih := current_conserved rho hres e (by omega)
    obtain ⟨hn, hp⟩ := hres (e + 1) (by omega) he
    have hsum := residual_sum_telescopes o c (e + 1) rho
    simp only [Nat.add_sub_cancel] at hsum
    have hstep : AbsLe (evalExpr rho (jTot o c (e + 1)) - evalExpr rho (jTot o c e))
        (o.tolRel * scaleN o c env (e + 1) + o.tolRel * scaleP o c env (e + 1)) := by
      rw [← hsum]; exact absLe_add hn hp
    have hboth := absLe_add ih hstep
    clear hres ih hstep hsum hn hp
    unfold AbsLe at hboth ⊢
    unfold currentBudget
    grind
/-- **The terminal current is the discrete solution's, at every edge, up to the residual budget**: under
`DdMeaning`, for every Bernoulli table in the enclosures and every edge `e`,
`|I − A J_e| ≤ tol · A · S_J + A · Σ_{i ≤ e} tol (S_n(i) + S_p(i))`. Every material and process
parameter (`ε, q, T, µ, τ, N_c, N_v, E_g`, the recipe) is free: they are fields of `o`. -/
theorem terminal_current_bound {o : DdSpec} {c : DdSolution} (hm : DdMeaning o c) (hA : 0 ≤ o.areaCm2) :
    ∃ env, bernEnv? o c = some env ∧ ∀ rho, BernTable env rho → ∀ e, e + 1 < o.nodes →
      AbsLe (c.currentA - o.areaCm2 * evalExpr rho (jTot o c e))
        (o.tolRel * o.areaCm2 * (scaleJn o c env 0 + scaleJp o c env 0) + o.areaCm2 * currentBudget o c env e) := by
  obtain ⟨env, henv, _, _, hall⟩ := hm.env
  refine ⟨env, henv, ?_⟩
  intro rho hrho e he
  obtain ⟨hres, hcur⟩ := hall rho hrho
  have hcons := current_conserved rho (fun i h1 h2 => (hres i h1 h2).2) e he
  unfold AbsLe at *
  obtain ⟨c1, c2⟩ := hcur
  obtain ⟨d1, d2⟩ := hcons
  have h1 := Rat.mul_le_mul_of_nonneg_left d1 hA
  have h2 := Rat.mul_le_mul_of_nonneg_left d2 hA
  grind
/-! ## 7. The reference slab, the planted bad certificate, the judge -/
/-- A uniform `10¹⁶ cm⁻³` n-type substrate, no process steps, three nodes. The object of both the
planted bad certificate and the reference equilibrium solution. -/
def badSpec : DdSpec where
  si := silicon300K
  ctN := caugheyThomasElectrons1967
  ctP := caugheyThomasHoles1967
  tauN := 1.0e-5
  tauP := 1.0e-5
  background := 1.0e16
  recipe := []
  xCm := [0, 1.0e-5, 2.0e-5]
  areaCm2 := 1
  biasV := 0
  tolRel := 1.0e-7
  mobDelta := 1.0e-6
  dealGroveTol := 1.0e-9
/-- A certificate whose doping at node 1 is `2·10¹⁶`: not this substrate. -/
def badSolution : DdSolution where
  recipeCert := []
  ni := 1.0e10
  doping := [1.0e16, 2.0e16, 1.0e16]
  total := [1.0e16, 1.0e16, 1.0e16]
  psi := [0, 0, 0]
  n := [1.0e16, 1.0e16, 1.0e16]
  p := [1.0e4, 1.0e4, 1.0e4]
  rN := [0, 0, 0]
  rP := [0, 0, 0]
  currentA := 0
/-- The equilibrium solution of `badSpec`: flat bands at `ψ = V_t ln(n/n_i)`, `n − p = N` exactly,
`n p = n_i²` to thirteen digits, `n_i` Green's derived value, the mobility ratios `(N/N_ref)^α`, no
current. (mpmath at 50 digits; the kernel checks every clause below.) -/
def slabSolution : DdSolution where
  recipeCert := []
  ni := 10739881022.332188
  doping := [1.0e16, 1.0e16, 1.0e16]
  total := [1.0e16, 1.0e16, 1.0e16]
  psi := [0.3553132882203481, 0.3553132882203481, 0.3553132882203481]
  n := [10000000000011534.50443737, 10000000000011534.50443737, 10000000000011534.50443737]
  p := [11534.50443737, 11534.50443737, 11534.50443737]
  rN := [0.21419946091307978, 0.21419946091307978, 0.21419946091307978]
  rP := [0.2468886826717447, 0.2468886826717447, 0.2468886826717447]
  currentA := 0
/-- Verdict predicates as `Bool`s (kernel-reducible without `DecidableEq (Verdict _)`). -/
@[expose] def isOk : Verdict DdClause → Bool
  | .ok => true
  | _ => false
@[expose] def isRefusedDoping (i : Nat) : Verdict DdClause → Bool
  | .refused (.doping j) _ => j == i
  | _ => false
theorem isOk_eq {v : Verdict DdClause} (h : isOk v = true) : v = .ok := by
  unfold isOk at h
  split at h
  · rfl
  · cases h
theorem isRefusedDoping_exists {v : Verdict DdClause} {i : Nat} (h : isRefusedDoping i v = true) :
    ∃ k p, v = .refused k p := by
  unfold isRefusedDoping at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h
theorem bad_refused_doping : isRefusedDoping 1 (checkDd badSpec badSolution) = true := by
  decide +kernel
theorem bad_refused : ∃ k p, checkDd badSpec badSolution = .refused k p :=
  isRefusedDoping_exists bad_refused_doping
/-- The reference slab's equilibrium certificate is accepted: every clause of `checkDd`. -/
theorem slab_accepted : checkDd badSpec slabSolution = .ok :=
  isOk_eq (by decide +kernel)
/-- Every enclosure of an environment has its endpoints in order. -/
def envWf (env : List (String × Interval)) : Bool :=
  env.all fun p => decide (p.2.lo ≤ p.2.hi)
/-- The table of lower endpoints. -/
def loTable (env : List (String × Interval)) (v : String) : CanonicalRat :=
  ((env.lookup v).map (·.lo)).getD 0
theorem lookup_wf {env : List (String × Interval)} (h : envWf env = true) {v : String} {I : Interval}
    (hl : env.lookup v = some I) : I.lo ≤ I.hi := by
  induction env with
  | nil => cases hl
  | cons hd tl ih =>
    rcases hd with ⟨k, J⟩
    simp only [envWf, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.lookup] at hl
    split at hl
    · cases hl; exact h.1
    · exact ih h.2 hl
/-- A well-formed environment has a table: its lower endpoints. -/
theorem loTable_table {env : List (String × Interval)} (h : envWf env = true) : BernTable env (loTable env) := by
  intro v I hl
  have hwf := lookup_wf h hl
  simp only [loTable, hl, Option.map_some, Option.getD_some, Interval.mem_iff]
  exact ⟨Rat.le_refl, hwf⟩
/-- The slab's Bernoulli environment: flat bands, so both enclosures are the point `B(0) = 1`. -/
def slabEnv : List (String × Interval) := (bernEnv? badSpec slabSolution).getD []
-- the premises of `nodeOk_sound`, `currentOk_sound` and `terminal_current_bound` are inhabited on the slab
example : envWf slabEnv = true ∧ slabEnv.length = 2 := by decide +kernel
example : BernTable slabEnv (loTable slabEnv) := loTable_table (by decide +kernel)
example : nodeOk badSpec slabSolution slabEnv 1 = true := by decide +kernel
example : currentOk badSpec slabSolution slabEnv = true := by decide +kernel
example : DdMeaning badSpec slabSolution := checkDd_sound slab_accepted
/-- The clauses whose refusal refutes the object: the mesh is no part of the certificate. -/
def refutesClause : DdClause → Bool
  | .mesh => true
  | _ => false
/-- `checkDd` refuses by `.mesh` only when the object's mesh fails. -/
theorem checkDd_refused_mesh {o : DdSpec} {c : DdSolution} {p : List Nat}
    (h : checkDd o c = .refused .mesh p) : o.meshOk = false := by
  cases hm : o.meshOk with
  | false => rfl
  | true =>
    exfalso
    unfold checkDd at h
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    repeat' split at h
    all_goals cases h
/-- **The judge.** A refusal by `.mesh` is a refutation (`DdMeaning.mesh` fails for every certificate).
Completeness is claimed on the reference slab only, by its accepted certificate: the residual clause of
`DdMeaning` is the bound for every Bernoulli table, and `checkDd` decides it by interval evaluation,
which over-approximates the range of an expression in which `b_e` occurs twice, so a certificate with
`DdMeaning` can be refused and no wider fragment is claimed. -/
instance ddJudge : Obend.Judge DdSpec DdSolution where
  Clause := DdClause
  Meaning := DdMeaning
  check _ := checkDd
  sound := checkDd_sound
  refutes := refutesClause
  refuted := by
    intro _ o c k p h hk c' hm
    cases k <;> first | cases hk | skip
    have hmesh := checkDd_refused_mesh h
    rw [hm.mesh] at hmesh
    cases hmesh
  Fragment o := o = badSpec
  complete := by
    intro o h _
    subst h
    exact ⟨slabSolution, 0, slab_accepted⟩
  mono := by intro _ _ _ _ _ _; rfl
/-! ### JSON wire -/
/-- Scientific decimal exponents are normalized exactly, including signed exponents. -/
private def ddParseNumber (cs : List Char) : Option ((Int × Nat) × List Char) := do
  let ((m, e), rest) ← sosJsonParseNum cs
  match rest with
  | 'e' :: tail | 'E' :: tail =>
    let (neg, tail) := match tail with | '-' :: t => (true, t) | '+' :: t => (false, t) | t => (false, t)
    let (n, has, tail) := sosJsonParseDigits tail 0 false
    if !has then none else
      if neg then some ((m, e+n), tail)
      else if n ≤ e then some ((m, e-n), tail)
      else some ((m * (10 : Int)^(n-e), 0), tail)
  | _ => some ((m, e), rest)
private def ddParseAux : Nat → List Char → Option (SosJson × List Char)
  | 0, _ => none
  | n+1, cs =>
    match sosJsonSkipWs cs with
    | '[' :: tail => do
      match sosJsonSkipWs tail with
      | ']' :: rest => some (.arr [], rest)
      | tail =>
        let (xs, rest) ← sosJsonParseArrAux (ddParseAux n) 1024 tail []
        some (.arr xs, rest)
    | '{' :: tail => do
      match sosJsonSkipWs tail with
      | '}' :: rest => some (.obj [], rest)
      | tail =>
        let (xs, rest) ← sosJsonParseObjAux (ddParseAux n) 1024 tail []
        some (.obj xs, rest)
    | '"' :: tail => do
      let (s, rest) ← sosJsonParseStrBody tail []
      some (.str s, rest)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | cs => do
      let ((m, e), rest) ← ddParseNumber cs
      some (.num m e, rest)
/-- Character-level wire parser, shared by the public string decoders. -/
private def ddParseChars (cs : List Char) : Except String SosJson :=
  match ddParseAux 24 cs with
  | some (j, rest) => if (sosJsonSkipWs rest).isEmpty then .ok j else .error "trailing JSON data"
  | none => .error "invalid device JSON"
/-- A JSON number as the exact rational it denotes. -/
private def ddRatOfSosJson : SosJson → Except String CanonicalRat
  | .num m e => .ok ((m : CanonicalRat) / ratPow 10 e)
  | j => do
    let n ← j.getObjInt? "num"
    let d ← j.getObjNat? "den"
    if d = 0 then .error "zero rational denominator" else return CanonicalRat.mk n d
private def ddRatsOfSosJson (j : SosJson) : Except String (List CanonicalRat) := do
  (← j.getArr?).mapM ddRatOfSosJson
private def ddRatField (j : SosJson) (k : String) : Except String CanonicalRat := do ddRatOfSosJson (← j.getObjVal? k)
private def ddRatsField (j : SosJson) (k : String) : Except String (List CanonicalRat) := do ddRatsOfSosJson (← j.getObjVal? k)
def speciesOf : String → Except String Species
  | "B" => .ok .boron
  | "P" => .ok .phosphorus
  | "As" => .ok .arsenic
  | "Sb" => .ok .antimony
  | s => .error s!"unknown species {s}"
def ambientOf : String → Except String OxidationAmbient
  | "dry" => .ok .dryO2
  | "wet" => .ok .wetO2
  | s => .error s!"unknown ambient {s}"
def filmOf : String → Except String FilmMaterial
  | "oxide" => .ok .oxide
  | "nitride" => .ok .nitride
  | "poly" => .ok .polysilicon
  | "metal" => .ok .metal
  | s => .error s!"unknown film {s}"
private def ddStepOfSosJson (j : SosJson) : Except String ProcessStep := do
  match ← j.getObjStr? "op" with
  | "implant" => return .implant (← speciesOf (← j.getObjStr? "species")) (← ddRatField j "keV") (← ddRatField j "dose")
  | "anneal" => return .anneal (← ddRatField j "tempK") (← ddRatField j "timeS")
  | "oxidize" => return .oxidize (← ambientOf (← j.getObjStr? "ambient")) (← ddRatField j "tempK") (← ddRatField j "timeS")
  | "deposit" => return .deposit (← filmOf (← j.getObjStr? "film")) (← ddRatField j "thicknessCm")
  | "etch" => return .etch (← filmOf (← j.getObjStr? "film")) (← ddRatField j "depthCm")
  | "strip" => return .strip (← filmOf (← j.getObjStr? "film"))
  | "etchSilicon" => return .etchSilicon (← ddRatField j "depthCm")
  | op => throw s!"unknown op {op}"
private def ddDiffusivitiesOfSosJson (j : SosJson) : Except String Diffusivities := do
  return ⟨← ddRatField j "B", ← ddRatField j "P", ← ddRatField j "As", ← ddRatField j "Sb"⟩
private def ddStepCertOfSosJson (j : SosJson) : Except String StepCert := do
  match ← j.getObjStr? "kind" with
  | "none" => return .none
  | "anneal" => return .anneal (← ddDiffusivitiesOfSosJson (← j.getObjVal? "D"))
  | "oxidize" => return .oxidize ⟨← ddRatField j "B", ← ddRatField j "BA", ← ddRatField j "xNewCm",
      ← ddDiffusivitiesOfSosJson (← j.getObjVal? "D")⟩
  | k => throw s!"unknown step certificate {k}"
private def ddSiliconOfSosJson (j : SosJson) : Except String SiliconConstants := do
  return ⟨← ddRatField j "tempK", ← ddRatField j "epsR", ← ddRatField j "eps0", ← ddRatField j "q", ← ddRatField j "kB",
    ← ddRatField j "nc", ← ddRatField j "nv", ← ddRatField j "egEv"⟩
private def ddCaugheyThomasOfSosJson (j : SosJson) : Except String CaugheyThomas := do
  return ⟨← ddRatField j "muMin", ← ddRatField j "muMax", ← ddRatField j "nRef",
    ← j.getObjNat? "alphaNum", ← j.getObjNat? "alphaDen"⟩
-- Preserve the public Lean.Json value API; wire proofs use the structural reader above.
open Lean in
def ratOfJson : Json → Except String CanonicalRat
  | .num n => .ok ((n.mantissa : CanonicalRat) / ratPow 10 n.exponent)
  | j => .error s!"expected a number, got {j.compress}"
open Lean in
def ratsOfJson (j : Json) : Except String (List CanonicalRat) := do
  (← j.getArr?).toList.mapM ratOfJson
open Lean in
def ratField (j : Json) (k : String) : Except String CanonicalRat := do ratOfJson (← j.getObjVal? k)
open Lean in
def ratsField (j : Json) (k : String) : Except String (List CanonicalRat) := do ratsOfJson (← j.getObjVal? k)
open Lean in
def stepOfJson (j : Json) : Except String ProcessStep := do
  match ← j.getObjValAs? String "op" with
  | "implant" => return .implant (← speciesOf (← j.getObjValAs? String "species")) (← ratField j "keV") (← ratField j "dose")
  | "anneal" => return .anneal (← ratField j "tempK") (← ratField j "timeS")
  | "oxidize" => return .oxidize (← ambientOf (← j.getObjValAs? String "ambient")) (← ratField j "tempK") (← ratField j "timeS")
  | "deposit" => return .deposit (← filmOf (← j.getObjValAs? String "film")) (← ratField j "thicknessCm")
  | "etch" => return .etch (← filmOf (← j.getObjValAs? String "film")) (← ratField j "depthCm")
  | "strip" => return .strip (← filmOf (← j.getObjValAs? String "film"))
  | "etchSilicon" => return .etchSilicon (← ratField j "depthCm")
  | op => throw s!"unknown op {op}"
open Lean in
def diffusivitiesOfJson (j : Json) : Except String Diffusivities := do
  return ⟨← ratField j "B", ← ratField j "P", ← ratField j "As", ← ratField j "Sb"⟩
open Lean in
def stepCertOfJson (j : Json) : Except String StepCert := do
  match ← j.getObjValAs? String "kind" with
  | "none" => return .none
  | "anneal" => return .anneal (← diffusivitiesOfJson (← j.getObjVal? "D"))
  | "oxidize" => return .oxidize ⟨← ratField j "B", ← ratField j "BA", ← ratField j "xNewCm",
      ← diffusivitiesOfJson (← j.getObjVal? "D")⟩
  | k => throw s!"unknown step certificate {k}"
open Lean in
def siliconOfJson (j : Json) : Except String SiliconConstants := do
  return ⟨← ratField j "tempK", ← ratField j "epsR", ← ratField j "eps0", ← ratField j "q", ← ratField j "kB",
    ← ratField j "nc", ← ratField j "nv", ← ratField j "egEv"⟩
open Lean in
def caugheyThomasOfJson (j : Json) : Except String CaugheyThomas := do
  return ⟨← ratField j "muMin", ← ratField j "muMax", ← ratField j "nRef",
    ← j.getObjValAs? Nat "alphaNum", ← j.getObjValAs? Nat "alphaDen"⟩
/-- The object wire: `{"si": {...}, "ctN": {...}, "ctP": {...}, "tauN", "tauP", "background",
"recipe": [steps], "xCm": [...], "areaCm2", "biasV", "tolRel", "mobDelta", "dealGroveTol"}`. -/
def decodeDdSpecChars (cs : List Char) : Except String DdSpec := do
  let j ← ddParseChars cs
  let recipe ← (← (← j.getObjVal? "recipe").getArr?).mapM ddStepOfSosJson
  return ⟨← ddSiliconOfSosJson (← j.getObjVal? "si"), ← ddCaugheyThomasOfSosJson (← j.getObjVal? "ctN"),
    ← ddCaugheyThomasOfSosJson (← j.getObjVal? "ctP"), ← ddRatField j "tauN", ← ddRatField j "tauP",
    ← ddRatField j "background", recipe, ← ddRatsField j "xCm", ← ddRatField j "areaCm2", ← ddRatField j "biasV",
    ← ddRatField j "tolRel", ← ddRatField j "mobDelta", ← ddRatField j "dealGroveTol"⟩
/-- String boundary; the character equation avoids quadratic UTF-8 reconstruction in proofs. -/
def decodeDdSpec (s : String) : Except String DdSpec := decodeDdSpecChars s.toList
theorem decodeDdSpec_ofList (cs : List Char) :
    decodeDdSpec (String.ofList cs) = decodeDdSpecChars cs := by
  simp only [decodeDdSpec, String.toList_ofList]
/-- The certificate wire: `{"recipeCert": [...], "ni", "doping": [...], "total": [...], "psi": [...],
"n": [...], "p": [...], "rN": [...], "rP": [...], "currentA"}`. -/
private def ddSolutionOfJson (j : SosJson) : Except String DdSolution := do
  let certs ← (← (← j.getObjVal? "recipeCert").getArr?).mapM ddStepCertOfSosJson
  return ⟨certs, ← ddRatField j "ni", ← ddRatsField j "doping", ← ddRatsField j "total", ← ddRatsField j "psi",
    ← ddRatsField j "n", ← ddRatsField j "p", ← ddRatsField j "rN", ← ddRatsField j "rP", ← ddRatField j "currentA"⟩
def decodeDdSolutionChars (cs : List Char) : Except String DdSolution := ddParseChars cs >>= ddSolutionOfJson
def decodeDdSolution (s : String) : Except String DdSolution := decodeDdSolutionChars s.toList
theorem decodeDdSolution_ofList (cs : List Char) :
    decodeDdSolution (String.ofList cs) = decodeDdSolutionChars cs := by
  simp only [decodeDdSolution, String.toList_ofList]
/-- The registered classical drift-diffusion format; fixtures are kernel checked. -/
def ddFormat : Judge.Format where
  name := "devsim-dd1d"
  version := "1"
  Obj := DdSpec
  Cert := DdSolution
  judge := ddJudge
  decodeObj := decodeDdSpec
  decodeCert := decodeDdSolution
  trust := .compiled
  regime := .decidable
  bad := (badSpec, badSolution)
  badGrade := 0
  bad_refused := bad_refused
theorem ddFormat_sound {r : Nat} {obj cert : String} (h : ddFormat.checkBytes r obj cert = .ok) :
    ∃ o c, decodeDdSpec obj = .ok o ∧ decodeDdSolution cert = .ok c ∧ DdMeaning o c :=
  ddFormat.checkBytes_sound h
/-! ## 8. The quasi-Fermi formulation: the same discrete currents without the contact cancellation
`Jn_e = cN_e (n_{i+1} B(−Δ_e) − n_i B(Δ_e))` at a neutral `10²⁰ cm⁻³` contact is a difference of two
terms of `3·10¹⁰ A/cm²`, so a residual accepted to `tolRel` of its term scale pins the current to
`tolRel · 3·10¹⁰ A/cm²` and no better (`terminal_current_bound`). The terms cancel because the
densities are Boltzmann in the quasi-Fermi potentials: with `n_i = n_int e^{(ψ_i − φ_{n,i})/V_t}`,
`δ_{n,e} = (φ_{n,i+1} − φ_{n,i})/V_t` and `Δ_e = (ψ_i − ψ_{i+1})/V_t`, `n_{i+1} = n_i e^{−Δ_e} e^{−δ_{n,e}}`,
and the two laws of the Bernoulli function, `e^{−x} B(−x) = B(x)` (`bernoulli_exp`) and
`e^{−x} − 1 = −x/B(−x)`, give
  `n_{i+1} B(−Δ_e) − n_i B(Δ_e) = −n_i B(Δ_e) δ_{n,e} / B(−δ_{n,e})`,
  `p_{i+1} B(Δ_e) − p_i B(−Δ_e) = p_i B(−Δ_e) δ_{p,e} / B(δ_{p,e})`
(`jnQuasiFermi_eq_jn`, `jpQuasiFermi_eq_jp`: identities of rational arithmetic under those laws, so
they hold for every table of values that obeys them). The right-hand sides are single products. Their
magnitude is proportional to `|δ|` (`scaleJnQ_eq_zero_of_flat`: a flat quasi-Fermi level has scale `0`
at any density), and `δ` is `J h/(q µ n V_t)` in a neutral region, so the term scale of the quasi-Fermi
residual is of the order of the current itself.
The certificate `DdQuasiFermiSolution` extends a `DdSolution` by `φ_n, φ_p` at the nodes. The checker
`checkDdQuasiFermi` checks the mesh, the recipe, the doping, `n_i` and the mobilities as `checkDd` does,
then: the classical densities are the Boltzmann densities of the quasi-Fermi potentials (`boltzmannOk`);
at an ohmic contact `φ_n = φ_p = V` exactly and the charge is neutral; at every interior node Poisson
and the two continuity equations in the product form, with the densities, the recombination rate and the
fluxes all evaluated over the enclosures of `e^{(ψ−φ_n)/V_t}`, `e^{(φ_p−ψ)/V_t}`, `B(Δ)`, `1/B(−δ_n)`,
`1/B(δ_p)` and `1/(τ_p(eⁿ+1) + τ_n(eᵖ+1))`. `terminal_current_bound_quasiFermi` is the current theorem
with the product scales. The fixtures (`Obend/Teeth/Hardware/DeviceFixtures.lean`) evaluate both bounds
on one device.
-/
/-- **`B(−x) = B(x) + x`**, for the stand-in `bernOf x e` with `e` standing for `eˣ`. -/
theorem bernOf_neg_add {x e : CanonicalRat} (he : 0 < e) (h0 : x = 0 → e = 1) (hne : x ≠ 0 → e ≠ 1) :
    bernOf (-x) e⁻¹ = bernOf x e + x := by
  have hee : e * e⁻¹ = 1 := Rat.mul_inv_cancel e (Rat.ne_of_gt he)
  by_cases hpos : 0 < x
  · have hx : x ≠ 0 := Rat.ne_of_gt hpos
    have h1 : ¬ (0 < -x) := by grind
    have h2 : -x < 0 := by grind
    have hd : e - 1 ≠ 0 := by have := hne hx; grind
    have hd' : 1 - e⁻¹ ≠ 0 := by
      intro hz
      have : e * (1 - e⁻¹) = 0 := by rw [hz]; grind
      grind
    simp only [bernOf, hpos, h1, h2, ↓reduceIte]
    have ha : x / (e - 1) * (e - 1) = x := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (e - 1)⁻¹, Rat.mul_inv_cancel _ hd, Rat.mul_one]
    have hb : -(-x) / (1 - e⁻¹) * (1 - e⁻¹) = -(-x) := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (1 - e⁻¹)⁻¹, Rat.mul_inv_cancel _ hd', Rat.mul_one]
    grind
  · by_cases hneg : x < 0
    · have hx : x ≠ 0 := Rat.ne_of_lt hneg
      have h1 : 0 < -x := by grind
      have hd : 1 - e ≠ 0 := by have := hne hx; grind
      have hd' : e⁻¹ - 1 ≠ 0 := by
        intro hz
        have : e * (e⁻¹ - 1) = 0 := by rw [hz]; grind
        grind
      simp only [bernOf, hpos, hneg, h1, ↓reduceIte]
      have ha : -x / (1 - e) * (1 - e) = -x := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (1 - e)⁻¹, Rat.mul_inv_cancel _ hd, Rat.mul_one]
      have hb : -x / (e⁻¹ - 1) * (e⁻¹ - 1) = -x := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (e⁻¹ - 1)⁻¹, Rat.mul_inv_cancel _ hd', Rat.mul_one]
      grind
    · have hx : x = 0 := by grind
      subst hx
      simp [bernOf]
      grind
/-- **`e^{−x} B(−x) = B(x)`**, in the form `B(−x) = eˣ B(x)`, for `bernOf` with `e` standing for `eˣ`. -/
theorem bernoulli_exp {x e : CanonicalRat} (he : 0 < e) (h0 : x = 0 → e = 1) (hne : x ≠ 0 → e ≠ 1) :
    bernOf (-x) e⁻¹ = e * bernOf x e := by
  rw [bernOf_neg_add he h0 hne]
  by_cases hpos : 0 < x
  · have hd : e - 1 ≠ 0 := by have := hne (Rat.ne_of_gt hpos); grind
    simp only [bernOf, hpos, ↓reduceIte]
    have ha : x / (e - 1) * (e - 1) = x := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (e - 1)⁻¹, Rat.mul_inv_cancel _ hd, Rat.mul_one]
    grind
  · by_cases hneg : x < 0
    · have hd : 1 - e ≠ 0 := by have := hne (Rat.ne_of_lt hneg); grind
      simp only [bernOf, hpos, hneg, ↓reduceIte]
      have ha : -x / (1 - e) * (1 - e) = -x := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm (1 - e)⁻¹, Rat.mul_inv_cancel _ hd, Rat.mul_one]
      grind
    · have hx : x = 0 := by grind
      subst hx
      rw [h0 rfl]
      simp [bernOf]
      grind
/-- The quasi-Fermi extension of a certificate: the electron and hole quasi-Fermi potentials (V) at
the nodes. `base` keeps the recipe's step data, `n_i`, the doping, `ψ`, the classical densities, the
mobility brackets and the terminal current. -/
structure DdQuasiFermiSolution where
  base : DdSolution
  phiN : List CanonicalRat
  phiP : List CanonicalRat
  deriving DecidableEq, Repr
namespace DdQuasiFermiSolution
def phiNAt (c : DdQuasiFermiSolution) (i : Nat) : CanonicalRat := c.phiN.getD i 0
def phiPAt (c : DdQuasiFermiSolution) (i : Nat) : CanonicalRat := c.phiP.getD i 0
def lengthsOk (c : DdQuasiFermiSolution) (m : Nat) : Bool :=
  c.base.lengthsOk m && decide (c.phiN.length = m) && decide (c.phiP.length = m)
end DdQuasiFermiSolution
/-- Variable names: `e^{(ψ_i−φ_{n,i})/V_t}`, `e^{(φ_{p,i}−ψ_i)/V_t}`, the recombination denominator's
reciprocal at node `i`; `1/B(−δ_{n,e})`, `1/B(δ_{p,e})` on edge `e`. -/
def enName (i : Nat) : String := "en" ++ natName i
def epName (i : Nat) : String := "ep" ++ natName i
def rdName (i : Nat) : String := "rd" ++ natName i
def gnName (e : Nat) : String := "gn" ++ natName e
def gpName (e : Nat) : String := "gp" ++ natName e
/-- `(ψ_i − φ_{n,i})/V_t` and `(φ_{p,i} − ψ_i)/V_t`: the exponents of the two densities. -/
def etaN (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : CanonicalRat :=
  (c.base.psiAt i - c.phiNAt i) / o.vt
def etaP (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : CanonicalRat :=
  (c.phiPAt i - c.base.psiAt i) / o.vt
/-- `δ_{n,e} = (φ_{n,i+1} − φ_{n,i})/V_t`, `δ_{p,e} = (φ_{p,i+1} − φ_{p,i})/V_t`. -/
def deltaN (o : DdSpec) (c : DdQuasiFermiSolution) (e : Nat) : CanonicalRat :=
  (c.phiNAt (e + 1) - c.phiNAt e) / o.vt
def deltaP (o : DdSpec) (c : DdQuasiFermiSolution) (e : Nat) : CanonicalRat :=
  (c.phiPAt (e + 1) - c.phiPAt e) / o.vt
/-- `τ_p (eⁿ + 1) + τ_n (eᵖ + 1)` over the exponentials' enclosures (the SRH denominator over `n_i`). -/
def srhDenEnclosure (o : DdSpec) (En Ep : Interval) : Interval :=
  Interval.add (Interval.scale o.tauP (Interval.add En (Interval.ofPoint 1)))
    (Interval.scale o.tauN (Interval.add Ep (Interval.ofPoint 1)))
/-- The node part of the environment; `none` when a recombination denominator is not enclosed above `0`. -/
def qfNodeEnv? (o : DdSpec) (c : DdQuasiFermiSolution) : Option (List (String × Interval)) :=
  (List.range o.nodes).foldr (fun i acc => do
      let env ← acc
      let En := expEnclosure (etaN o c i)
      let Ep := expEnclosure (etaP o c i)
      let D := srhDenEnclosure o En Ep
      if 0 < D.lo then pure ((enName i, En) :: (epName i, Ep) :: (rdName i, D.invPos) :: env) else none)
    (some [])
/-- The environment of the quasi-Fermi residuals: the node part, and on every edge `B(Δ_e)`,
`1/B(−δ_{n,e})`, `1/B(δ_{p,e})`; `none` when an enclosure is unavailable or not above `0`. -/
def qfEnv? (o : DdSpec) (c : DdQuasiFermiSolution) : Option (List (String × Interval)) :=
  (List.range (o.nodes - 1)).foldr (fun e acc => do
      let env ← acc
      let B ← bernEnclosure? (delta o c.base e)
      let Gn ← bernEnclosure? (-(deltaN o c e))
      let Gp ← bernEnclosure? (deltaP o c e)
      if 0 < Gn.lo ∧ 0 < Gp.lo then
        pure ((bName e, B) :: (gnName e, Gn.invPos) :: (gpName e, Gp.invPos) :: env)
      else none)
    (qfNodeEnv? o c)
/-- `n_i = n_int e^{(ψ_i−φ_{n,i})/V_t}`, `p_i = n_int e^{(φ_{p,i}−ψ_i)/V_t}`. -/
def nQ (c : DdQuasiFermiSolution) (i : Nat) : RealExpr := .mul (.const c.base.ni) (.var (enName i))
def pQ (c : DdQuasiFermiSolution) (i : Nat) : RealExpr := .mul (.const c.base.ni) (.var (epName i))
/-- `Jn_e = −cN_e δ_{n,e} · n_i B(Δ_e) / B(−δ_{n,e})`: one product. -/
def jnQ (o : DdSpec) (c : DdQuasiFermiSolution) (e : Nat) : RealExpr :=
  .mul (.const (-(cN o c.base e) * deltaN o c e)) (.mul (nQ c e) (.mul (bPos e) (.var (gnName e))))
/-- `Jp_e = −cP_e δ_{p,e} · p_i B(−Δ_e) / B(δ_{p,e})`: one product. -/
def jpQ (o : DdSpec) (c : DdQuasiFermiSolution) (e : Nat) : RealExpr :=
  .mul (.const (-(cP o c.base e) * deltaP o c e)) (.mul (pQ c e) (.mul (bNeg o c.base e) (.var (gpName e))))
def jTotQ (o : DdSpec) (c : DdQuasiFermiSolution) (e : Nat) : RealExpr := .add (jnQ o c e) (jpQ o c e)
/-- SRH: `U_i = n_int (eⁿ eᵖ − 1) / (τ_p (eⁿ + 1) + τ_n (eᵖ + 1))`. -/
def srhQ (c : DdQuasiFermiSolution) (i : Nat) : RealExpr :=
  .mul (.const c.base.ni)
    (.mul (.sub (.mul (.var (enName i)) (.var (epName i))) (.const 1)) (.var (rdName i)))
def fPsiQ (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : RealExpr :=
  .sub (.const (dFlux o c.base i - dFlux o c.base (i - 1)))
    (.mul (.const (o.q * o.vol i)) (.add (.sub (pQ c i) (nQ c i)) (.const (c.base.dopingAt i))))
def fNQ (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : RealExpr :=
  .sub (.sub (jnQ o c i) (jnQ o c (i - 1))) (.mul (.const (o.q * o.vol i)) (srhQ c i))
def fPQ (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : RealExpr :=
  .add (.sub (jpQ o c i) (jpQ o c (i - 1))) (.mul (.const (o.q * o.vol i)) (srhQ c i))
/-- `F_n(i) + F_p(i) = J_i − J_{i−1}` in the product form, for every assignment. -/
theorem residual_sum_telescopes_quasiFermi (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat)
    (rho : String → CanonicalRat) :
    evalExpr rho (fNQ o c i) + evalExpr rho (fPQ o c i) =
      evalExpr rho (jTotQ o c i) - evalExpr rho (jTotQ o c (i - 1)) := by
  simp only [fNQ, fPQ, jTotQ, evalExpr]
  grind
/-- **The electron flux identity.** For a table whose edge values obey the Bernoulli laws at `Δ_e`
(`eΔ` standing for `e^{−Δ_e}`: `eΔ · B(−Δ_e) = B(Δ_e)`) and at `δ_{n,e}` (`eδ` standing for
`e^{−δ_{n,e}}`: `eδ − 1 = −δ_{n,e}/B(−δ_{n,e})`), and whose densities are Boltzmann along the edge
(`e^{η_{i+1}} = e^{η_i} eΔ eδ`), the product form is the Scharfetter–Gummel flux of those densities. -/
theorem jnQuasiFermi_eq_jn {o : DdSpec} {c : DdQuasiFermiSolution} {e : Nat} {rho : String → CanonicalRat}
    {eΔ eδ : CanonicalRat}
    (hn0 : c.base.nAt e = c.base.ni * rho (enName e))
    (hn1 : c.base.nAt (e + 1) = c.base.ni * rho (enName (e + 1)))
    (hBern : eΔ * (rho (bName e) + delta o c.base e) = rho (bName e))
    (hInc : eδ - 1 = -(deltaN o c e) * rho (gnName e))
    (hBoltz : rho (enName (e + 1)) = rho (enName e) * eΔ * eδ) :
    evalExpr rho (jnQ o c e) = evalExpr rho (jn o c.base e) := by
  simp only [jnQ, jn, nQ, bPos, bNeg, evalExpr]
  rw [hn0, hn1, hBoltz]
  have h1 : rho (enName e) * eΔ * eδ * (rho (bName e) + delta o c.base e) =
      rho (enName e) * eδ * (eΔ * (rho (bName e) + delta o c.base e)) := by grind
  have h2 : c.base.ni * (rho (enName e) * eΔ * eδ) * (rho (bName e) + delta o c.base e) =
      c.base.ni * (rho (enName e) * eδ * rho (bName e)) := by
    rw [Rat.mul_assoc, h1, hBern]
  rw [h2]
  have h3 : eδ = 1 + -(deltaN o c e) * rho (gnName e) := by grind
  rw [h3]
  grind
/-- **The hole flux identity.** `EΔ` stands for `e^{Δ_e}` (`EΔ · B(Δ_e) = B(−Δ_e)`), `eδ` for
`e^{δ_{p,e}}` (`eδ − 1 = δ_{p,e}/B(δ_{p,e})`), and `e^{η_{p,i+1}} = e^{η_{p,i}} EΔ eδ`. -/
theorem jpQuasiFermi_eq_jp {o : DdSpec} {c : DdQuasiFermiSolution} {e : Nat} {rho : String → CanonicalRat}
    {EΔ eδ : CanonicalRat}
    (hp0 : c.base.pAt e = c.base.ni * rho (epName e))
    (hp1 : c.base.pAt (e + 1) = c.base.ni * rho (epName (e + 1)))
    (hBern : EΔ * rho (bName e) = rho (bName e) + delta o c.base e)
    (hInc : eδ - 1 = deltaP o c e * rho (gpName e))
    (hBoltz : rho (epName (e + 1)) = rho (epName e) * EΔ * eδ) :
    evalExpr rho (jpQ o c e) = evalExpr rho (jp o c.base e) := by
  simp only [jpQ, jp, pQ, bPos, bNeg, evalExpr]
  rw [hp0, hp1, hBoltz]
  have h1 : c.base.ni * (rho (epName e) * EΔ * eδ) * rho (bName e) =
      c.base.ni * (rho (epName e) * eδ * (EΔ * rho (bName e))) := by grind
  rw [h1, hBern]
  have h3 : eδ = 1 + deltaP o c e * rho (gpName e) := by grind
  rw [h3]
  grind
/-- The magnitude of an expression over the environment: `max |lo| |hi|` of its interval. -/
def magOf (env : List (String × Interval)) (e : RealExpr) : CanonicalRat :=
  match evalInterval env e with
  | some I => I.absMax
  | none => 0
/-- The flux scales: the magnitude of the one product each flux is. Proportional to `|δ|`. -/
def scaleJnQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  magOf env (jnQ o c e)
def scaleJpQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  magOf env (jpQ o c e)
/-- The magnitude of the two terms that cancel in `q U_i V_i` (`eⁿ eᵖ` against `1`). -/
def scaleSrhQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  ratAbs (o.q * o.vol i * c.base.ni) *
    ((magOf env (.mul (.var (enName i)) (.var (epName i))) + 1) * magOf env (.var (rdName i)))
def scalePsiQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  ratAbs (dFlux o c.base i) + ratAbs (dFlux o c.base (i - 1)) +
  ratAbs (o.q * o.vol i) * (magOf env (pQ c i) + magOf env (nQ c i) + ratAbs (c.base.dopingAt i))
def scaleNQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJnQ o c env i + scaleJnQ o c env (i - 1) + scaleSrhQ o c env i
def scalePQ (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJpQ o c env i + scaleJpQ o c env (i - 1) + scaleSrhQ o c env i
theorem absMax_mul_zero (I : Interval) : (Interval.mul (Interval.ofPoint 0) I).absMax = 0 := by
  simp [Interval.mul, Interval.ofPoint, Interval.min4, Interval.max4, Interval.absMax, ratAbs, Rat.zero_mul]
  decide +kernel
/-- **A flat electron quasi-Fermi level has flux scale `0`**, whatever the density on the edge. -/
theorem scaleJnQ_eq_zero_of_flat {o : DdSpec} {c : DdQuasiFermiSolution} (env : List (String × Interval))
    {e : Nat} (h : deltaN o c e = 0) : scaleJnQ o c env e = 0 := by
  unfold scaleJnQ magOf jnQ
  rw [h, Rat.mul_zero]
  simp only [evalInterval, bind, Option.bind, pure]
  split
  · rename_i I hI
    split at hI
    · cases hI
    · cases hI; exact absMax_mul_zero _
  · rfl
theorem scaleJpQ_eq_zero_of_flat {o : DdSpec} {c : DdQuasiFermiSolution} (env : List (String × Interval))
    {e : Nat} (h : deltaP o c e = 0) : scaleJpQ o c env e = 0 := by
  unfold scaleJpQ magOf jpQ
  rw [h, Rat.mul_zero]
  simp only [evalInterval, bind, Option.bind, pure]
  split
  · rename_i I hI
    split at hI
    · cases hI
    · cases hI; exact absMax_mul_zero _
  · rfl
/-- The classical densities are the Boltzmann densities of the quasi-Fermi potentials, to `tolRel`. -/
def boltzmannOk (o : DdSpec) (c : DdQuasiFermiSolution) (i : Nat) : Bool :=
  decide (c.base.nAt i ∈ (Interval.scale c.base.ni (expEnclosure (etaN o c i))).widenRel o.tolRel) &&
  decide (c.base.pAt i ∈ (Interval.scale c.base.ni (expEnclosure (etaP o c i))).widenRel o.tolRel)
/-- An ohmic contact at node `i` held at `v`: both quasi-Fermi potentials are the metal's, exactly,
and the charge is neutral to `tolRel` of its terms. -/
def qfContactOk (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat)
    (v : CanonicalRat) : Bool :=
  decide (c.phiNAt i = v) && decide (c.phiPAt i = v) &&
  match evalInterval env (.sub (.sub (nQ c i) (pQ c i)) (.const (c.base.dopingAt i))) with
  | some I => I.within (o.tolRel * (ratAbs (c.base.dopingAt i) + magOf env (nQ c i) + magOf env (pQ c i)))
  | none => false
/-- The three residuals at interior node `i` in the product form. -/
def qfNodeOk (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) : Bool :=
  match evalInterval env (fPsiQ o c i), evalInterval env (fNQ o c i), evalInterval env (fPQ o c i) with
  | some a, some b, some d =>
    a.within (o.tolRel * scalePsiQ o c env i) && b.within (o.tolRel * scaleNQ o c env i) &&
      d.within (o.tolRel * scalePQ o c env i)
  | _, _, _ => false
/-- The reported current is `A · J_0` to `tolRel · A` of the two product scales. -/
def qfCurrentOk (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) : Bool :=
  match evalInterval env (jTotQ o c 0) with
  | some J =>
    (Interval.sub (Interval.ofPoint c.base.currentA) (Interval.scale o.areaCm2 J)).within
      (o.tolRel * o.areaCm2 * (scaleJnQ o c env 0 + scaleJpQ o c env 0))
  | none => false
/-- **The quasi-Fermi checker.** -/
def checkDdQuasiFermi (o : DdSpec) (c : DdQuasiFermiSolution) : Verdict DdClause :=
  let m := o.nodes
  if !o.meshOk then .refused .mesh [] else
  if !c.lengthsOk m then .refused .lengths [] else
  match runRecipe o.si.kBEv o.dealGroveTol (WaferState.bare o.background) o.recipe c.base.recipeCert with
  | none => .refused .recipe []
  | some w =>
    match firstFailing m (dopingOk o c.base w) with
    | some i => .refused (.doping i) [i]
    | none =>
    if !o.si.niOk c.base.ni then .refused .intrinsic [] else
    match firstFailing m (mobilityOk o c.base) with
    | some i => .refused (.mobility i) [i]
    | none =>
    match qfEnv? o c with
    | none => .refused .bernoulli []
    | some env =>
      match firstFailing m (boltzmannOk o c) with
      | some i => .refused (.boltzmann i) [i]
      | none =>
      if !qfContactOk o c env 0 o.biasV then .refused (.contact 0) [0] else
      if !qfContactOk o c env (m - 1) 0 then .refused (.contact (m - 1)) [m - 1] else
      match firstFailing (m - 2) (fun k => qfNodeOk o c env (k + 1)) with
      | some k => .refused (.residual (k + 1)) [k + 1]
      | none =>
        if !qfCurrentOk o c env then .refused .current [] else .ok
/-- **The meaning of an accepted quasi-Fermi certificate.** -/
structure DdQuasiFermiMeaning (o : DdSpec) (c : DdQuasiFermiSolution) : Prop where
  mesh : o.meshOk = true
  lengths : c.lengthsOk o.nodes = true
  wafer : ∃ w, runRecipe o.si.kBEv o.dealGroveTol (WaferState.bare o.background) o.recipe c.base.recipeCert = some w ∧
    ∀ i < o.nodes, dopingOk o c.base w i = true
  intrinsic : o.si.niOk c.base.ni = true
  mobility : ∀ i < o.nodes, mobilityOk o c.base i = true
  env : ∃ env, qfEnv? o c = some env ∧
    (∀ i < o.nodes, boltzmannOk o c i = true) ∧
    qfContactOk o c env 0 o.biasV = true ∧ qfContactOk o c env (o.nodes - 1) 0 = true ∧
    (∀ rho, BernTable env rho →
      (∀ i, 1 ≤ i → i + 1 < o.nodes →
        AbsLe (evalExpr rho (fPsiQ o c i)) (o.tolRel * scalePsiQ o c env i) ∧
        AbsLe (evalExpr rho (fNQ o c i)) (o.tolRel * scaleNQ o c env i) ∧
        AbsLe (evalExpr rho (fPQ o c i)) (o.tolRel * scalePQ o c env i)) ∧
      AbsLe (c.base.currentA - o.areaCm2 * evalExpr rho (jTotQ o c 0))
        (o.tolRel * o.areaCm2 * (scaleJnQ o c env 0 + scaleJpQ o c env 0)))
theorem qfNodeOk_sound {o : DdSpec} {c : DdQuasiFermiSolution} {env : List (String × Interval)} {i : Nat}
    (h : qfNodeOk o c env i = true) (rho : String → CanonicalRat) (hrho : BernTable env rho) :
    AbsLe (evalExpr rho (fPsiQ o c i)) (o.tolRel * scalePsiQ o c env i) ∧
    AbsLe (evalExpr rho (fNQ o c i)) (o.tolRel * scaleNQ o c env i) ∧
    AbsLe (evalExpr rho (fPQ o c i)) (o.tolRel * scalePQ o c env i) := by
  unfold qfNodeOk at h
  split at h
  · rename_i a b d ha hb hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨Interval.within_sound (evalInterval_sound env rho hrho _ _ ha) h1,
           Interval.within_sound (evalInterval_sound env rho hrho _ _ hb) h2,
           Interval.within_sound (evalInterval_sound env rho hrho _ _ hd) h3⟩
  · cases h
theorem qfCurrentOk_sound {o : DdSpec} {c : DdQuasiFermiSolution} {env : List (String × Interval)}
    (h : qfCurrentOk o c env = true) (rho : String → CanonicalRat) (hrho : BernTable env rho) :
    AbsLe (c.base.currentA - o.areaCm2 * evalExpr rho (jTotQ o c 0))
      (o.tolRel * o.areaCm2 * (scaleJnQ o c env 0 + scaleJpQ o c env 0)) := by
  unfold qfCurrentOk at h
  split at h
  · rename_i J hJ
    have hmem := evalInterval_sound env rho hrho _ _ hJ
    exact Interval.within_sound (Interval.sub_mem (Interval.ofPoint_mem _) (Interval.scale_mem _ hmem)) h
  · cases h
/-- **Soundness of the quasi-Fermi checker.** -/
theorem checkDdQuasiFermi_sound {o : DdSpec} {c : DdQuasiFermiSolution} (h : checkDdQuasiFermi o c = .ok) :
    DdQuasiFermiMeaning o c := by
  unfold checkDdQuasiFermi at h
  simp only at h
  split at h
  · cases h
  rename_i hmesh
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i w hw
  split at h
  · cases h
  rename_i hdop
  split at h
  · cases h
  rename_i hni
  split at h
  · cases h
  rename_i hmob
  split at h
  · cases h
  rename_i env henv
  split at h
  · cases h
  rename_i hboltz
  split at h
  · cases h
  rename_i hc0
  split at h
  · cases h
  rename_i hc1
  split at h
  · cases h
  rename_i hnodes
  split at h
  · cases h
  rename_i hcur
  refine ⟨by simpa using hmesh, by simpa using hlen, ⟨w, hw, firstFailing_none hdop⟩, by simpa using hni,
    firstFailing_none hmob, env, henv, firstFailing_none hboltz, by simpa using hc0, by simpa using hc1, ?_⟩
  intro rho hrho
  refine ⟨?_, qfCurrentOk_sound (by simpa using hcur) rho hrho⟩
  intro i hi1 hi2
  have := firstFailing_none hnodes (i - 1) (by omega)
  have hi : i - 1 + 1 = i := by omega
  rw [hi] at this
  exact qfNodeOk_sound this rho hrho
/-- `Σ_{i=1}^{e} S(i)`. -/
def budgetSum (S : Nat → CanonicalRat) : Nat → CanonicalRat
  | 0 => 0
  | e + 1 => budgetSum S e + S (e + 1)
/-- A sequence whose steps are bounded stays within the summed bounds of its start. -/
theorem telescoped_within_budget {m : Nat} (J S : Nat → CanonicalRat)
    (hstep : ∀ i, 1 ≤ i → i + 1 < m → AbsLe (J i - J (i - 1)) (S i)) :
    ∀ e, e + 1 < m → AbsLe (J e - J 0) (budgetSum S e)
  | 0, _ => by unfold AbsLe budgetSum; grind
  | e + 1, he => by
    have ih := telescoped_within_budget J S hstep e (by omega)
    have hs := hstep (e + 1) (by omega) he
    simp only [Nat.add_sub_cancel] at hs
    unfold AbsLe at ih hs ⊢
    unfold budgetSum
    grind
/-- The residual budget of the first `e` interior nodes, in the product scales. -/
def qfCurrentBudget (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) : Nat → CanonicalRat :=
  budgetSum fun i => o.tolRel * (scaleNQ o c env i + scalePQ o c env i)
/-- The certified current bound at edge `e`, quasi-Fermi form (A). -/
def qfCurrentBound (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  o.tolRel * o.areaCm2 * (scaleJnQ o c env 0 + scaleJpQ o c env 0) + o.areaCm2 * qfCurrentBudget o c env e
/-- The certified current bound at edge `e`, `(n, p, ψ)` form (A): the right-hand side of
`terminal_current_bound`. -/
def classicalCurrentBound (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  o.tolRel * o.areaCm2 * (scaleJn o c env 0 + scaleJp o c env 0) + o.areaCm2 * currentBudget o c env e
/-- **The terminal current in the quasi-Fermi form.** Under `DdQuasiFermiMeaning`, for every table in
the enclosures and every edge `e`, the reported current is within `qfCurrentBound` of `A · J_e`, with
`J_e` the product-form current and every scale in the bound the magnitude of a product proportional to
a quasi-Fermi increment or of the recombination terms. -/
theorem terminal_current_bound_quasiFermi {o : DdSpec} {c : DdQuasiFermiSolution}
    (hm : DdQuasiFermiMeaning o c) (hA : 0 ≤ o.areaCm2) :
    ∃ env, qfEnv? o c = some env ∧ ∀ rho, BernTable env rho → ∀ e, e + 1 < o.nodes →
      AbsLe (c.base.currentA - o.areaCm2 * evalExpr rho (jTotQ o c e)) (qfCurrentBound o c env e) := by
  obtain ⟨env, henv, _, _, _, hall⟩ := hm.env
  refine ⟨env, henv, ?_⟩
  intro rho hrho e he
  obtain ⟨hres, hcur⟩ := hall rho hrho
  have hstep : ∀ i, 1 ≤ i → i + 1 < o.nodes →
      AbsLe (evalExpr rho (jTotQ o c i) - evalExpr rho (jTotQ o c (i - 1)))
        (o.tolRel * (scaleNQ o c env i + scalePQ o c env i)) := by
    intro i h1 h2
    obtain ⟨_, hn, hp⟩ := hres i h1 h2
    rw [← residual_sum_telescopes_quasiFermi o c i rho]
    have := absLe_add hn hp
    unfold AbsLe at this ⊢
    grind
  have hcons := telescoped_within_budget (fun i => evalExpr rho (jTotQ o c i))
    (fun i => o.tolRel * (scaleNQ o c env i + scalePQ o c env i)) hstep e he
  unfold qfCurrentBound qfCurrentBudget
  unfold AbsLe at *
  obtain ⟨c1, c2⟩ := hcur
  obtain ⟨d1, d2⟩ := hcons
  have h1 := Rat.mul_le_mul_of_nonneg_left d1 hA
  have h2 := Rat.mul_le_mul_of_nonneg_left d2 hA
  grind
theorem absMax_nonneg (I : Interval) : 0 ≤ I.absMax := by
  unfold Interval.absMax
  have := ratAbs_nonneg I.lo
  grind
theorem magOf_nonneg (env : List (String × Interval)) (e : RealExpr) : 0 ≤ magOf env e := by
  unfold magOf
  split
  · exact absMax_nonneg _
  · exact Rat.le_refl
theorem scaleSrhQ_nonneg (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval)) (i : Nat) :
    0 ≤ scaleSrhQ o c env i := by
  unfold scaleSrhQ
  have h1 := magOf_nonneg env (.mul (.var (enName i)) (.var (epName i)))
  exact Rat.mul_nonneg (ratAbs_nonneg _) (Rat.mul_nonneg (by grind) (magOf_nonneg _ _))
theorem budgetSum_mono {S : Nat → CanonicalRat} (hS : ∀ i, 0 ≤ S i) {e e' : Nat} (h : e ≤ e') :
    budgetSum S e ≤ budgetSum S e' := by
  induction h with
  | refl => exact Rat.le_refl
  | step _ ih =>
    rename_i m _
    have := hS (m + 1)
    show budgetSum S e ≤ budgetSum S m + S (m + 1)
    grind
/-- The bound grows along the device: the far contact's budget covers every edge. -/
theorem qfCurrentBound_mono (o : DdSpec) (c : DdQuasiFermiSolution) (env : List (String × Interval))
    (hA : 0 ≤ o.areaCm2) (ht : 0 ≤ o.tolRel) {e e' : Nat} (h : e ≤ e') :
    qfCurrentBound o c env e ≤ qfCurrentBound o c env e' := by
  unfold qfCurrentBound qfCurrentBudget
  have hS : ∀ i, 0 ≤ o.tolRel * (scaleNQ o c env i + scalePQ o c env i) := by
    intro i
    apply Rat.mul_nonneg ht
    have h1 := magOf_nonneg env (jnQ o c i)
    have h2 := magOf_nonneg env (jnQ o c (i - 1))
    have h3 := magOf_nonneg env (jpQ o c i)
    have h4 := magOf_nonneg env (jpQ o c (i - 1))
    have h5 := scaleSrhQ_nonneg o c env i
    unfold scaleNQ scalePQ scaleJnQ scaleJpQ
    grind
  have := Rat.mul_le_mul_of_nonneg_left (budgetSum_mono hS h) hA
  grind
/-- **One bound for every edge**: the reported current is within the far contact's `qfCurrentBound`
of `A · J_e` on every edge `e`. -/
theorem terminal_current_bound_quasiFermi_uniform {o : DdSpec} {c : DdQuasiFermiSolution}
    (hm : DdQuasiFermiMeaning o c) (hA : 0 ≤ o.areaCm2) (ht : 0 ≤ o.tolRel) :
    ∃ env, qfEnv? o c = some env ∧ ∀ rho, BernTable env rho → ∀ e, e + 1 < o.nodes →
      AbsLe (c.base.currentA - o.areaCm2 * evalExpr rho (jTotQ o c e)) (qfCurrentBound o c env (o.nodes - 2)) := by
  obtain ⟨env, henv, h⟩ := terminal_current_bound_quasiFermi hm hA
  refine ⟨env, henv, fun rho hrho e he => ?_⟩
  have hb := h rho hrho e he
  have hmono := qfCurrentBound_mono o c env hA ht (show e ≤ o.nodes - 2 by omega)
  unfold AbsLe at hb ⊢
  grind
/-- `checkDdQuasiFermi` refuses by `.mesh` only when the object's mesh fails. -/
theorem checkDdQuasiFermi_refused_mesh {o : DdSpec} {c : DdQuasiFermiSolution} {p : List Nat}
    (h : checkDdQuasiFermi o c = .refused .mesh p) : o.meshOk = false := by
  cases hm : o.meshOk with
  | false => rfl
  | true =>
    exfalso
    unfold checkDdQuasiFermi at h
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    repeat' split at h
    all_goals cases h
/-- The reference slab at equilibrium: both quasi-Fermi levels flat at the contacts' `0 V`. -/
def slabQuasiFermi : DdQuasiFermiSolution := ⟨slabSolution, [0, 0, 0], [0, 0, 0]⟩
theorem slabQuasiFermi_accepted : checkDdQuasiFermi badSpec slabQuasiFermi = .ok :=
  isOk_eq (by decide +kernel)
/-- A quasi-Fermi certificate whose electron level at the biased contact is `10 mV` off the metal's. -/
def badQuasiFermi : DdQuasiFermiSolution := ⟨slabSolution, [0.01, 0, 0], [0, 0, 0]⟩
def isRefusedBoltzmann (i : Nat) : Verdict DdClause → Bool
  | .refused (.boltzmann j) _ => j == i
  | _ => false
/-- The planted quasi-Fermi certificate is refused at node 0: its density is not the Boltzmann density
of its quasi-Fermi potential. -/
theorem badQuasiFermi_refused : isRefusedBoltzmann 0 (checkDdQuasiFermi badSpec badQuasiFermi) = true := by
  decide +kernel
/-- The slab's quasi-Fermi environment. -/
def slabQfEnv : List (String × Interval) := (qfEnv? badSpec slabQuasiFermi).getD []
-- the premises of `qfNodeOk_sound`, `qfCurrentOk_sound`, `terminal_current_bound_quasiFermi` and of the
-- two flux identities are inhabited
example : envWf slabQfEnv = true ∧ slabQfEnv.length = 15 := by decide +kernel
example : BernTable slabQfEnv (loTable slabQfEnv) := loTable_table (by decide +kernel)
example : qfNodeOk badSpec slabQuasiFermi slabQfEnv 1 = true := by decide +kernel
example : qfCurrentOk badSpec slabQuasiFermi slabQfEnv = true := by decide +kernel
example : DdQuasiFermiMeaning badSpec slabQuasiFermi := checkDdQuasiFermi_sound slabQuasiFermi_accepted
example : ∃ (x e : CanonicalRat), 0 < e ∧ (x = 0 → e = 1) ∧ (x ≠ 0 → e ≠ 1) ∧ bernOf (-x) e⁻¹ = e * bernOf x e :=
  ⟨1, 2, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
/-- **The quasi-Fermi judge.** `.mesh` refutes; completeness is claimed on the reference slab, by its
accepted certificate (the interval evaluation over-approximates, as for `ddJudge`). -/
instance ddQuasiFermiJudge : Obend.Judge DdSpec DdQuasiFermiSolution where
  Clause := DdClause
  Meaning := DdQuasiFermiMeaning
  check _ := checkDdQuasiFermi
  sound := checkDdQuasiFermi_sound
  refutes := refutesClause
  refuted := by
    intro _ o c k p h hk c' hm
    cases k <;> first | cases hk | skip
    have hmesh := checkDdQuasiFermi_refused_mesh h
    rw [hm.mesh] at hmesh
    cases hmesh
  Fragment o := o = badSpec
  complete := by
    intro o h _
    subst h
    exact ⟨slabQuasiFermi, 0, slabQuasiFermi_accepted⟩
  mono := by intro _ _ _ _ _ _; rfl
private def ddStr (s : String) : SosJson := .str s.toList
private def ddVec (v : List CanonicalRat) : SosJson := .arr (v.map sosJsonEncodeRat)
private def ddDiffJson (d : Diffusivities) : SosJson := SosJson.mkObj
  [("B", sosJsonEncodeRat d.boron), ("P", sosJsonEncodeRat d.phosphorus),
   ("As", sosJsonEncodeRat d.arsenic), ("Sb", sosJsonEncodeRat d.antimony)]
private def ddStepCertJson : StepCert → SosJson
  | .none => SosJson.mkObj [("kind", ddStr "none")]
  | .anneal d => SosJson.mkObj [("kind", ddStr "anneal"), ("D", ddDiffJson d)]
  | .oxidize c => SosJson.mkObj [("kind", ddStr "oxidize"), ("D", ddDiffJson c.diff),
      ("B", sosJsonEncodeRat c.bCm2PerS), ("BA", sosJsonEncodeRat c.baCmPerS),
      ("xNewCm", sosJsonEncodeRat c.xNewCm)]
/-- Binary digit length bounds decimal writer fuel: arbitrary rational numerators are not truncated. -/
private def ddJsonWrite : Nat → SosJson → List Char → List Char
  | 0, _, acc => 'n' :: 'u' :: 'l' :: 'l' :: acc
  | _+1, .num m e, acc =>
    let tail := if e = 0 then acc else 'e' :: '-' :: sosJsonNatWrite (e.log2+1) e acc
    match m with
    | .ofNat n => sosJsonNatWrite (n.log2+1) n tail
    | .negSucc n => '-' :: sosJsonNatWrite ((n+1).log2+1) (n+1) tail
  | n+1, .arr xs, acc => '[' :: sosJsonWriteArrElems (ddJsonWrite n) xs (']' :: acc)
  | n+1, .obj fs, acc => '{' :: sosJsonWriteObjFields (ddJsonWrite n) fs ('}' :: acc)
  | _+1, j, acc => sosJsonWriteAux 1 j acc
private def ddBaseJson (c : DdSolution) : SosJson := SosJson.mkObj
  [("recipeCert", .arr (c.recipeCert.map ddStepCertJson)), ("ni", sosJsonEncodeRat c.ni),
   ("doping", ddVec c.doping), ("total", ddVec c.total), ("psi", ddVec c.psi),
   ("n", ddVec c.n), ("p", ddVec c.p), ("rN", ddVec c.rN), ("rP", ddVec c.rP),
   ("currentA", sosJsonEncodeRat c.currentA)]
private def ddSpecies : Species → SosJson
  | .boron => ddStr "B" | .phosphorus => ddStr "P" | .arsenic => ddStr "As" | .antimony => ddStr "Sb"
private def ddFilm : FilmMaterial → SosJson
  | .oxide => ddStr "oxide" | .nitride => ddStr "nitride" | .polysilicon => ddStr "poly" | .metal => ddStr "metal"
private def ddStepJson : ProcessStep → SosJson
  | .implant sp keV dose => SosJson.mkObj [("op", ddStr "implant"), ("species", ddSpecies sp),
      ("keV", sosJsonEncodeRat keV), ("dose", sosJsonEncodeRat dose)]
  | .anneal t dt => SosJson.mkObj [("op", ddStr "anneal"), ("tempK", sosJsonEncodeRat t), ("timeS", sosJsonEncodeRat dt)]
  | .oxidize amb t dt => SosJson.mkObj [("op", ddStr "oxidize"),
      ("ambient", match amb with | .dryO2 => ddStr "dry" | .wetO2 => ddStr "wet"),
      ("tempK", sosJsonEncodeRat t), ("timeS", sosJsonEncodeRat dt)]
  | .deposit m t => SosJson.mkObj [("op", ddStr "deposit"), ("film", ddFilm m), ("thicknessCm", sosJsonEncodeRat t)]
  | .etch m d => SosJson.mkObj [("op", ddStr "etch"), ("film", ddFilm m), ("depthCm", sosJsonEncodeRat d)]
  | .strip m => SosJson.mkObj [("op", ddStr "strip"), ("film", ddFilm m)]
  | .etchSilicon d => SosJson.mkObj [("op", ddStr "etchSilicon"), ("depthCm", sosJsonEncodeRat d)]
private def ddSiliconJson (c : SiliconConstants) : SosJson := SosJson.mkObj
  [("tempK", sosJsonEncodeRat c.tempK), ("epsR", sosJsonEncodeRat c.epsR), ("eps0", sosJsonEncodeRat c.eps0),
   ("q", sosJsonEncodeRat c.q), ("kB", sosJsonEncodeRat c.kB), ("nc", sosJsonEncodeRat c.nc),
   ("nv", sosJsonEncodeRat c.nv), ("egEv", sosJsonEncodeRat c.egEv)]
private def ddMobilityJson (c : CaugheyThomas) : SosJson := SosJson.mkObj
  [("muMin", sosJsonEncodeRat c.muMin), ("muMax", sosJsonEncodeRat c.muMax), ("nRef", sosJsonEncodeRat c.nRef),
   ("alphaNum", .ofNat c.alphaNum), ("alphaDen", .ofNat c.alphaDen)]
private def ddSpecJson (o : DdSpec) : SosJson := SosJson.mkObj
  [("si", ddSiliconJson o.si), ("ctN", ddMobilityJson o.ctN), ("ctP", ddMobilityJson o.ctP),
   ("tauN", sosJsonEncodeRat o.tauN), ("tauP", sosJsonEncodeRat o.tauP), ("background", sosJsonEncodeRat o.background),
   ("recipe", .arr (o.recipe.map ddStepJson)), ("xCm", ddVec o.xCm), ("areaCm2", sosJsonEncodeRat o.areaCm2),
   ("biasV", sosJsonEncodeRat o.biasV), ("tolRel", sosJsonEncodeRat o.tolRel),
   ("mobDelta", sosJsonEncodeRat o.mobDelta), ("dealGroveTol", sosJsonEncodeRat o.dealGroveTol)]
def encodeDdSpecChars (o : DdSpec) : List Char := ddJsonWrite 24 (ddSpecJson o) []
def encodeDdSpec (o : DdSpec) : String := String.ofList (encodeDdSpecChars o)
theorem decodeDdSpec_encode_eq (o : DdSpec) : decodeDdSpec (encodeDdSpec o) =
    decodeDdSpecChars (encodeDdSpecChars o) := by
  simp only [encodeDdSpec, decodeDdSpec_ofList]
private def ddQuasiFermiJson (c : DdQuasiFermiSolution) : SosJson := SosJson.mkObj
  [("base", ddBaseJson c.base), ("phiN", ddVec c.phiN), ("phiP", ddVec c.phiP)]
def decodeDdQuasiFermiChars (cs : List Char) : Except String DdQuasiFermiSolution := do
  let j ← ddParseChars cs
  return ⟨← ddSolutionOfJson (← j.getObjVal? "base"), ← ddRatsField j "phiN", ← ddRatsField j "phiP"⟩
def encodeDdQuasiFermiChars (c : DdQuasiFermiSolution) : List Char := ddJsonWrite 24 (ddQuasiFermiJson c) []
def encodeDdQuasiFermiSolution (c : DdQuasiFermiSolution) : String := String.ofList (encodeDdQuasiFermiChars c)
def decodeDdQuasiFermiSolution (s : String) : Except String DdQuasiFermiSolution := decodeDdQuasiFermiChars s.toList
theorem decodeDdQuasiFermi_encode_eq (c : DdQuasiFermiSolution) :
    decodeDdQuasiFermiSolution (encodeDdQuasiFermiSolution c) =
      decodeDdQuasiFermiChars (encodeDdQuasiFermiChars c) := by
  simp only [decodeDdQuasiFermiSolution, encodeDdQuasiFermiSolution, String.toList_ofList]
/-- Kernel-checked product-form drift-diffusion certificates, with exact rational wire fields. -/
def devsimQfermiFormat : Judge.Format where
  name := "devsim-qfermi"; version := "1"; Obj := DdSpec; Cert := DdQuasiFermiSolution
  judge := ddQuasiFermiJudge; decodeObj := decodeDdSpec; decodeCert := decodeDdQuasiFermiSolution
  trust := .kernel; regime := .decidable
  bad := (badSpec, badQuasiFermi); badGrade := 0
  bad_refused := by
    have h := badQuasiFermi_refused
    cases hv : checkDdQuasiFermi badSpec badQuasiFermi <;> simp [hv, isRefusedBoltzmann] at h
    case refused k p => exact ⟨k, p, hv⟩
end Obend.Hardware.Device
end
