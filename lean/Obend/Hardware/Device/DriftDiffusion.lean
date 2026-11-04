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
-/
public import Obend.Hardware.Device.Wafer
public import Obend.Judge.Class
public import Lean.Data.Json
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
@[expose] def x (o : DdSpec) (i : Nat) : CanonicalRat := o.xCm.getD i 0
@[expose] def h (o : DdSpec) (e : Nat) : CanonicalRat := o.x (e + 1) - o.x e
/-- `V_i = (h_{i−1} + h_i)/2` for an interior node. -/
@[expose] def vol (o : DdSpec) (i : Nat) : CanonicalRat := (o.h (i - 1) + o.h i) / 2
@[expose] def vt (o : DdSpec) : CanonicalRat := o.si.vt
@[expose] def q (o : DdSpec) : CanonicalRat := o.si.q
@[expose] def eps (o : DdSpec) : CanonicalRat := o.si.eps

/-- At least three nodes, strictly increasing. -/
@[expose] def meshOk (o : DdSpec) : Bool :=
  decide (3 ≤ o.nodes) &&
  (List.range (o.nodes - 1)).all fun e => decide (0 < o.h e)

end DdSpec

namespace DdSolution

@[expose] def psiAt (c : DdSolution) (i : Nat) : CanonicalRat := c.psi.getD i 0
@[expose] def nAt (c : DdSolution) (i : Nat) : CanonicalRat := c.n.getD i 0
@[expose] def pAt (c : DdSolution) (i : Nat) : CanonicalRat := c.p.getD i 0
@[expose] def dopingAt (c : DdSolution) (i : Nat) : CanonicalRat := c.doping.getD i 0
@[expose] def totalAt (c : DdSolution) (i : Nat) : CanonicalRat := c.total.getD i 0
@[expose] def rNAt (c : DdSolution) (i : Nat) : CanonicalRat := c.rN.getD i 0
@[expose] def rPAt (c : DdSolution) (i : Nat) : CanonicalRat := c.rP.getD i 0

/-- Every per-node list has the mesh's length. -/
@[expose] def lengthsOk (c : DdSolution) (m : Nat) : Bool :=
  decide (c.doping.length = m) && decide (c.total.length = m) && decide (c.psi.length = m) &&
  decide (c.n.length = m) && decide (c.p.length = m) && decide (c.rN.length = m) && decide (c.rP.length = m)

end DdSolution

/-! ## 2. The discrete equations as `RealExpr`s in the Bernoulli variables -/

/-- The name of edge `e`'s Bernoulli variable. -/
@[expose] def bName (e : Nat) : String := "b" ++ toString e

/-- `Δ_e = (ψ_i − ψ_{i+1})/V_t`. -/
@[expose] def delta (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat :=
  (c.psiAt e - c.psiAt (e + 1)) / o.vt

/-- `B(Δ_e)` and `B(−Δ_e) = B(Δ_e) + Δ_e`. -/
@[expose] def bPos (e : Nat) : RealExpr := .var (bName e)
@[expose] def bNeg (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr := .add (bPos e) (.const (delta o c e))

/-- Node mobilities from the bracketed ratios, and the edge mean. -/
@[expose] def muN (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat := o.ctN.muOf (c.rNAt i)
@[expose] def muP (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat := o.ctP.muOf (c.rPAt i)
@[expose] def muNEdge (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := (muN o c e + muN o c (e + 1)) / 2
@[expose] def muPEdge (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := (muP o c e + muP o c (e + 1)) / 2

/-- `q µ V_t / h_e`. -/
@[expose] def cN (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := o.q * muNEdge o c e * o.vt / o.h e
@[expose] def cP (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat := o.q * muPEdge o c e * o.vt / o.h e

/-- `Jn_e = cN_e (n_{i+1} B(−Δ) − n_i B(Δ))`. -/
@[expose] def jn (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr :=
  .mul (.const (cN o c e)) (.sub (.mul (.const (c.nAt (e + 1))) (bNeg o c e)) (.mul (.const (c.nAt e)) (bPos e)))

/-- `Jp_e = −cP_e (p_{i+1} B(Δ) − p_i B(−Δ))`. -/
@[expose] def jp (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr :=
  .mul (.const (-(cP o c e))) (.sub (.mul (.const (c.pAt (e + 1))) (bPos e)) (.mul (.const (c.pAt e)) (bNeg o c e)))

/-- Total current on edge `e`. -/
@[expose] def jTot (o : DdSpec) (c : DdSolution) (e : Nat) : RealExpr := .add (jn o c e) (jp o c e)

/-- `D_e = ε (ψ_i − ψ_{i+1})/h_e`. -/
@[expose] def dFlux (o : DdSpec) (c : DdSolution) (e : Nat) : CanonicalRat :=
  o.eps * (c.psiAt e - c.psiAt (e + 1)) / o.h e

/-- SRH net recombination at node `i` (mid-gap trap, `n₁ = p₁ = n_i`). -/
@[expose] def srhU (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat :=
  (c.nAt i * c.pAt i - c.ni * c.ni) / (o.tauP * (c.nAt i + c.ni) + o.tauN * (c.pAt i + c.ni))

/-- Poisson's residual at an interior node. -/
@[expose] def fPsi (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
  .const ((dFlux o c i - dFlux o c (i - 1)) - o.q * (c.pAt i - c.nAt i + c.dopingAt i) * o.vol i)

/-- The electron continuity residual. -/
@[expose] def fN (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
  .sub (.sub (jn o c i) (jn o c (i - 1))) (.const (o.q * srhU o c i * o.vol i))

/-- The hole continuity residual. -/
@[expose] def fP (o : DdSpec) (c : DdSolution) (i : Nat) : RealExpr :=
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
@[expose] def absMax (I : Interval) : CanonicalRat := max (ratAbs I.lo) (ratAbs I.hi)

/-- `[lo − tol·|lo|, hi + tol·|hi|]`. -/
@[expose] def widenRel (I : Interval) (tol : CanonicalRat) : Interval :=
  ⟨I.lo - tol * ratAbs I.lo, I.hi + tol * ratAbs I.hi⟩

end Obend.Analysis.Interval

namespace Obend.Hardware.Device
open Obend.Analysis Obend.Judge

/-- The environment `b_e ↦ bernEnclosure? Δ_e`, `none` if any enclosure is unavailable. -/
@[expose] def bernEnv? (o : DdSpec) (c : DdSolution) : Option (List (String × Interval)) :=
  (List.range (o.nodes - 1)).foldr (fun e acc => do
      let env ← acc
      let B ← bernEnclosure? (delta o c e)
      pure ((bName e, B) :: env))
    (some [])

/-- The magnitude of edge `e`'s electron-current terms under `env`. -/
@[expose] def scaleJn (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  match env.lookup (bName e) with
  | some B => ratAbs (cN o c e) * (ratAbs (c.nAt (e + 1)) * Interval.absMax (Interval.add B (Interval.ofPoint (delta o c e)))
      + ratAbs (c.nAt e) * Interval.absMax B)
  | none => 0

@[expose] def scaleJp (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (e : Nat) : CanonicalRat :=
  match env.lookup (bName e) with
  | some B => ratAbs (cP o c e) * (ratAbs (c.pAt (e + 1)) * Interval.absMax B
      + ratAbs (c.pAt e) * Interval.absMax (Interval.add B (Interval.ofPoint (delta o c e))))
  | none => 0

@[expose] def scalePsi (o : DdSpec) (c : DdSolution) (i : Nat) : CanonicalRat :=
  ratAbs (dFlux o c i) + ratAbs (dFlux o c (i - 1)) +
  ratAbs (o.q * o.vol i) * (ratAbs (c.pAt i) + ratAbs (c.nAt i) + ratAbs (c.dopingAt i))

@[expose] def scaleN (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJn o c env i + scaleJn o c env (i - 1) + ratAbs (o.q * srhU o c i * o.vol i)

@[expose] def scaleP (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : CanonicalRat :=
  scaleJp o c env i + scaleJp o c env (i - 1) + ratAbs (o.q * srhU o c i * o.vol i)

/-! ## 4. The checks -/

/-- The mesh doping is the recipe's: net and total at every node, within `tolRel`. -/
@[expose] def dopingOk (o : DdSpec) (c : DdSolution) (w : WaferState) (i : Nat) : Bool :=
  (match w.dopingEnclosure? (o.x i) with
   | some I => decide (c.dopingAt i ∈ I.widenRel o.tolRel)
   | none => false) &&
  (match w.totalDopingEnclosure? (o.x i) with
   | some I => decide (c.totalAt i ∈ I.widenRel o.tolRel)
   | none => false)

/-- The mobility bracket witnesses at node `i`. -/
@[expose] def mobilityOk (o : DdSpec) (c : DdSolution) (i : Nat) : Bool :=
  o.ctN.ratioOk (c.totalAt i) (c.rNAt i) o.mobDelta && o.ctP.ratioOk (c.totalAt i) (c.rPAt i) o.mobDelta

/-- An ohmic contact at node `i` held at `v`: `n, p > 0`, `np = n_i²`, `n − p = N`, `n = n_i e^{(ψ−v)/V_t}`,
each to `tolRel`. -/
@[expose] def contactOk (o : DdSpec) (c : DdSolution) (i : Nat) (v : CanonicalRat) : Bool :=
  let n := c.nAt i
  let p := c.pAt i
  let N := c.dopingAt i
  decide (0 < n) && decide (0 < p) &&
  decide (ratAbs (n * p - c.ni * c.ni) ≤ o.tolRel * (c.ni * c.ni)) &&
  decide (ratAbs (n - p - N) ≤ o.tolRel * (ratAbs N + n + p)) &&
  decide (n ∈ (Interval.scale c.ni (expEnclosure ((c.psiAt i - v) / o.vt))).widenRel o.tolRel)

/-- The three residuals at interior node `i`, by interval evaluation. -/
@[expose] def nodeOk (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) (i : Nat) : Bool :=
  match evalInterval env (fPsi o c i), evalInterval env (fN o c i), evalInterval env (fP o c i) with
  | some a, some b, some d =>
    a.within (o.tolRel * scalePsi o c i) && b.within (o.tolRel * scaleN o c env i) && d.within (o.tolRel * scaleP o c env i)
  | _, _, _ => false

/-- The reported current is `A · J_0` to `tolRel · A · S_J`. -/
@[expose] def currentOk (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) : Bool :=
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
  deriving DecidableEq, Repr

/-- First failing index of a per-node check. -/
@[expose] def firstFailing (m : Nat) (f : Nat → Bool) : Option Nat :=
  (List.range m).find? fun i => !f i

/-- **The checker.** Mesh, lengths, the recipe, the doping, `n_i`, the mobility brackets, the Bernoulli
environment, the two contacts, every interior node, the current; the first failure names its clause. -/
@[expose] def checkDd (o : DdSpec) (c : DdSolution) : Verdict DdClause :=
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
@[expose] def currentBudget (o : DdSpec) (c : DdSolution) (env : List (String × Interval)) : Nat → CanonicalRat
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

/-! ## 7. The judge and the format -/

instance ddJudge : Obend.Judge DdSpec DdSolution where
  Clause := DdClause
  Meaning := DdMeaning
  check _ := checkDd
  sound := checkDd_sound
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment _ := False
  complete := by intro _ h; exact h.elim
  mono := by intro _ _ _ _ _ _; rfl

/-! ### JSON wire -/

open Lean in
/-- A JSON number as the exact rational it denotes. -/
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
def speciesOf : String → Except String Species
  | "B" => .ok .boron
  | "P" => .ok .phosphorus
  | "As" => .ok .arsenic
  | "Sb" => .ok .antimony
  | s => .error s!"unknown species {s}"

open Lean in
def ambientOf : String → Except String OxidationAmbient
  | "dry" => .ok .dryO2
  | "wet" => .ok .wetO2
  | s => .error s!"unknown ambient {s}"

open Lean in
def filmOf : String → Except String FilmMaterial
  | "oxide" => .ok .oxide
  | "nitride" => .ok .nitride
  | "poly" => .ok .polysilicon
  | "metal" => .ok .metal
  | s => .error s!"unknown film {s}"

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

open Lean in
/-- The object wire: `{"si": {...}, "ctN": {...}, "ctP": {...}, "tauN", "tauP", "background",
"recipe": [steps], "xCm": [...], "areaCm2", "biasV", "tolRel", "mobDelta", "dealGroveTol"}`. -/
def decodeDdSpec (s : String) : Except String DdSpec := do
  let j ← Json.parse s
  let recipe ← (← (← j.getObjVal? "recipe").getArr?).toList.mapM stepOfJson
  return ⟨← siliconOfJson (← j.getObjVal? "si"), ← caugheyThomasOfJson (← j.getObjVal? "ctN"),
    ← caugheyThomasOfJson (← j.getObjVal? "ctP"), ← ratField j "tauN", ← ratField j "tauP",
    ← ratField j "background", recipe, ← ratsField j "xCm", ← ratField j "areaCm2", ← ratField j "biasV",
    ← ratField j "tolRel", ← ratField j "mobDelta", ← ratField j "dealGroveTol"⟩

open Lean in
/-- The certificate wire: `{"recipeCert": [...], "ni", "doping": [...], "total": [...], "psi": [...],
"n": [...], "p": [...], "rN": [...], "rP": [...], "currentA"}`. -/
def decodeDdSolution (s : String) : Except String DdSolution := do
  let j ← Json.parse s
  let certs ← (← (← j.getObjVal? "recipeCert").getArr?).toList.mapM stepCertOfJson
  return ⟨certs, ← ratField j "ni", ← ratsField j "doping", ← ratsField j "total", ← ratsField j "psi",
    ← ratsField j "n", ← ratsField j "p", ← ratsField j "rN", ← ratsField j "rP", ← ratField j "currentA"⟩

/-! ### The planted bad certificate -/

/-- A uniform `10¹⁶ cm⁻³` n-type substrate, no process steps, three nodes. -/
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

/-- Verdict predicates as `Bool`s (kernel-reducible without `DecidableEq (Verdict _)`). -/
@[expose] def isOk : Verdict DdClause → Bool
  | .ok => true
  | _ => false

@[expose] def isRefusedDoping (i : Nat) : Verdict DdClause → Bool
  | .refused (.doping j) _ => j == i
  | _ => false

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

/-- **The registered format `devsim-dd1d@1`.** Compiled trust: the sky130 checks run as `native_decide`
(a 1D device is a few hundred nodes of rational arithmetic with `10⁶⁰`-scale denominators). -/
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

end Obend.Hardware.Device
end
