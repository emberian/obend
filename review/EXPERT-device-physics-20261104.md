# Semiconductor device physics with real process numbers: one diode, fabrication first (2026-11-04)

Slug `device-physics`. Remit: `lean/Obend/Hardware/{Physics,TcadBridge,FabuBlox}.lean` (replaced in place)
and the new `lean/Obend/Hardware/Device/`; the external producer devsim 2.11.2 (`~/tools/devsim`); the
SkyWater sky130 PDK (`~/src/skywater-pdk`, `~/src/skywater-pdk-libs-sky130_fd_pr`, `~/src/open_pdks`) and
the literature in `~/paperbin/`. The design decision under test is the project's trust rule: the solver is
untrusted, the kernel checks a certificate, and a theorem is a theorem only if a device parameter's value can
change its truth. Tags: **READ** (opened, `path:line`), **MEASURED** (a number with the command that made
it), **INFERRED**, **PROPOSED**. Builds on bb2 (`~/lane-device`); nothing was built on the Mac.

## 0. Verdict

**MEASURED/INFERRED.** The trust rule survives contact with a real device, and it changes shape doing so.
A p-well/n⁺ diode is now fabricated by a recipe whose every step carries its parameters (boron 160 keV
`1.3·10¹³`, a 1000 °C drive, a Deal–Grove screen oxide, arsenic 50 keV `10¹⁵`, an anneal, a strip), solved
by devsim on a 180-node mesh, and checked by the kernel at every node: Poisson, both Scharfetter–Gummel
continuity equations, the ohmic contacts, the Caughey–Thomas mobilities, the intrinsic density, and that
the doping on the mesh is the recipe's. Doubling the p-well dose moves the −0.5 V forward current from
4.19 to 1.54 mA/cm² and the certificate of the first device is refused on the second at node 0, as
doping, before any residual is looked at (`DeviceFixtures.lean`). `terminal_current_bound` is the theorem
the brief asked for, with `ε, q, T, µ, τ, N_c, N_v, E_g` and the recipe free.

Two things the rule did not anticipate. First, *what the kernel can certify about a terminal current is
set by the arithmetic of the discretisation, not by the solver's accuracy*: the Scharfetter–Gummel flux at a
`10²⁰ cm⁻³` contact is a difference of terms of `3·10¹⁰ A/cm²`, so a residual tolerance at the measured
double-precision floor (`3·10⁻¹⁴` of the term scale; the fixtures use `10⁻¹²`) pins the current to
`0.030 A/cm²` — 0.3 % at −0.7 V, 15 % at −0.6 V, nothing at −0.5 V and below. The certificate is exact
about the equations and honest about this; a formulation in scaled variables is the first item of the next
brief. Second, the transcendental functions never enter the checker as functions: `exp` and the Bernoulli
function are rational enclosures built from `Analysis.Interval`, the mobility's fractional power and the
roots are *bracketed* (the producer finds the value, the kernel multiplies), and the two real-analysis
facts assumed are written once, as a degree-12 Taylor bound on `[−1/2, 1/2]` and a Bernoulli-series bound
on `[−1/8, 1/8]` (`Device/Enclosure.lean`). Everything above them is proved over `ℚ`.

What was there before is gone or renamed: the three-cell "drift-diffusion", the Rayleigh CD, the ALD
count, the four-point probe, the integer "Scharfetter–Gummel", the EOT/`V_th`/swing formulas, the
isqrt "Fickian depth", CMP dishing, step coverage and GAA release are deleted; the three integer quadratic-
form identities `Codec` uses live on as `Hardware/ThermalPassivity.lean` under that name; the facility-rules
flow of `FabuBlox` stays, its header now saying its steps carry no physics; `TcadBridge` keeps the corner
envelope `TapeoutPipeline` stage 7 reads, with the three formulas it needs labelled as what they are.

## 1. The chain, with the numbers

### 1.1 Fabrication (`Device/Wafer.lean`, `Device/Constants.lean`)

**READ** The wafer is a film stack, a substrate doping, and a list of Gaussian dopant distributions in depth
with the image term at the surface (`GaussianDopant`, `WaferState`). The representation is chosen because
Fick's law with constant `D` maps it to itself exactly: `σ² ↦ σ² + 2Dt` (`WaferState.anneal`), so the anneal
carries no discretisation and the only sampling in the chain is the device mesh, which is *checked*
(`dopingEnclosure?`: an interval the mesh value must lie in, `dopingOk`).

* Implant: `R_p`, `ΔR_p` from Plummer's table by energy (`rangeTable`, `rangeAt`; linear interpolation
  between rows; `none` outside 10–200 keV). The table is read from the publisher's chapter-8 slides
  (`~/paperbin/plummer-deal-griffin-silicon-vlsi-ch08-implantation-slides.pdf`), four species, 15 energies.
* Anneal: `D` per species supplied by the producer, accepted only inside `D₀ exp(−E_A/kT)`
  (`Arrhenius.ok`; `D₀, E_A` Plummer Table 7-5, intrinsic). `anneal_var_mono` (a positive `D` and `t`
  widen every profile) and `anneal_dose` (dose conserved) are the theorems; both false for `D ≤ 0`.
* Oxidation: Deal–Grove with Plummer's Arrhenius fits for (100) silicon (`dealGrove100`); the new thickness
  is a value checked against `x² + Ax = B(t + τ)` to a relative residual, with `τ` from the oxide present.
  `dealGrove_limits` (both the parabolic and the linear bound hold), `dealGrove_root_pinned` (two accepted
  thicknesses differ by at most `2ε/A`), `oxidize_consumes` (`0.44` of the oxide grown comes out of the
  silicon; the profiles shift by that much). The fit is checked against Deal–Grove's own 1965 Table II in
  tier 2: within 20 % at 1000 °C dry (`DeviceFixtures.lean`; the fit is 10 % under the measurement).
* Etch, strip, deposition: geometry on the stack; `etch_deposit` (etching what was deposited restores the
  stack, for any thickness).

**MEASURED** (`run_diode.py`, mirror of the operators in 50-digit arithmetic, cross-checked by the kernel
accepting the certificates): boron `R_p = 423.9 nm` (after 4.1 nm of silicon consumed by the screen oxide),
`σ = 128.2 nm` after the drive; arsenic `R_p = 26.9 nm` behind a 9.3 nm oxide, `σ = 16.0 nm`; junction at
97 nm (device A) and 95 nm (B); sky130 documents `0.1 µm`.

### 1.2 The device (`Device/DriftDiffusion.lean`)

**READ** `fPsi`, `fN`, `fP` are the finite-volume residuals (`:173-183`), written as `RealExpr`s in the
per-edge Bernoulli variables `b_e`; `jn`, `jp` are devsim's own edge currents (`Jn_e = cN_e (n_{i+1}(B_e + Δ_e)
− n_i B_e)`, the identity `B(−Δ) = B(Δ) + Δ` built in as in devsim's `simple_dd.py`). `nodeOk` evaluates
them by `evalInterval` over `b_e ↦ bernEnclosure? Δ_e` and requires `|F| ≤ tol · S` with `S` the sum of the
magnitudes of the terms (`scalePsi`, `scaleN`, `scaleP`). `contactOk`: `n p = n_i²`, `n − p = N`,
`n ∈ n_i · exp((ψ − V)/V_t)` by the enclosure. `mobilityOk`: `(N/N_ref)^α` bracketed to `10⁻⁹`
(`powBracket`, `α = 18/25` and `19/25`). `niOk`: `n_i² ∈ N_c N_v exp(−E_g/kT)` — the intrinsic density is
derived, and lands at Green's `1.074·10¹⁰`.

**READ** `checkDd_sound` (`:386`): an accepted certificate has `DdMeaning`, whose residual clause is
universally quantified over every table of Bernoulli values inside the enclosures (`BernTable`), by
`evalInterval_sound` from `Analysis/RealAnalysis.lean` — the sibling's theorem doing exactly the job it was
written for. `residual_sum_telescopes` (`:185`): `F_n(i) + F_p(i) = J_i − J_{i−1}` for every assignment, the
exact identity behind current conservation. `terminal_current_bound` (`:472`): under `DdMeaning`, for every
Bernoulli table and every edge `e`, `|I − A J_e| ≤ tol·A·S_J + A·Σ_{i≤e} tol (S_n(i) + S_p(i))`.

**MEASURED** (`~/tools/devsim/.venv/bin/python -I apps/sky130-diode/devsim/run_diode.py --tag a`;
`--tag b --pwell-dose 2.6e13`): worst `|F|/S` over all nodes and biases `3.3·10⁻¹⁴` (Poisson),
`2.3·10⁻¹⁵` (electrons), `1.5·10⁻¹⁵` (holes); `J_top = −J_bot` to six digits at every forward bias; the
exact recomputation of the edge-0 current from the 17-digit solution differs from devsim's reported contact
current by `≤ 1.2·10⁻⁷ A/cm²`, the rounding floor of a `3.6·10⁸ A/cm²` term scale.

| bias at n⁺ (V) | A, dose 1.3e13 (A/cm²) | B, dose 2.6e13 (A/cm²) | certified bound (A/cm²) |
|---|---|---|---|
| −0.30 | 1.85·10⁻⁶ | 8.80·10⁻⁷ | 0.030 |
| −0.50 | 4.19·10⁻³ | 1.54·10⁻³ | 0.030 |
| −0.60 | 2.00·10⁻¹ | 7.36·10⁻² | 0.030 |
| −0.70 | 9.51 | 3.51 | 0.030 |
| +1.00 (reverse) | −3.0·10⁻⁷ | +2.9·10⁻⁷ | 0.029 |

The ideality between −0.5 and −0.6 V is 1.00 (short-base diode, bottom contact 1 µm into the well). The
sky130 compact model of `diode_pw2nd_05v5` (`js = 2.75·10⁻⁷ A/cm²`, `n = 1.29`, `pb = 0.729 V`) gives
0.86 A/cm² at 0.5 V: 200× more, with an ideality that says its `js` carries generation and perimeter
components a 1D area model does not have. **INFERRED**: the comparison is a sanity check of magnitude, not
a fit; the reverse currents above are at the arithmetic floor and mean nothing.

### 1.3 The certificate as a format (`devsim-dd1d@1`)

**READ** `ddFormat` (`:651`): object `DdSpec` (constants, Caughey–Thomas parameters, lifetimes, recipe,
mesh, area, bias, tolerances), certificate `DdSolution` (the step data, `n_i`, the doping on the mesh, `ψ, n,
p`, the bracket witnesses, the current); decoders from JSON with exact decimal numbers (`ratOfJson`); trust
`.compiled`; planted bad certificate `badSpec`/`badSolution` — a uniform substrate whose certificate claims
`2·10¹⁶` at node 1 — refused as `.doping 1` by `decide +kernel` (`bad_refused_doping`, 1 s in the build).

**MEASURED** `DeviceFixtures.lean` (tier 2, 3.1 s): A at −0.5 V and −0.7 V accepted, B at −0.5 V accepted,
A's certificate on B's object refused `.doping 0`, A's −0.7 V certificate on the −0.5 V object refused
`.contact 0`, the objects' recipes equal `sky130DiodeRecipe` at each dose. The checker takes 0.78 s per
180-node certificate in the interpreter (`lake env lean`, `#eval`).

### 1.4 The numbers and where they come from

**READ** `Device/Constants.lean`: every value has its source in its docstring. SkyWater publishes
(`docs/rules/assumptions.rst` Tables 3a–3b, the BSIM card, the diode model) the p-well peak `4·10¹⁷` at
`0.42 µm` with `y.char 0.13 µm`, background `8·10¹⁴`, S/D `x_j 0.1 µm`, `toxe 4.148 nm`, `ndep 1.7·10¹⁷`,
`nsd 10²⁰`; it does not publish implant energies, doses or thermal budgets. `Sky130Diode.lean` derives each
step from those numbers through the model and says so: boron 160 keV because Plummer's `R_p` is 0.428 µm,
`1.3·10¹³` because that dose makes the peak `4·10¹⁷` at the drive's `σ`, 1000 °C 30 min because it gives
`σ = 0.124 µm` against `y.char 0.13` (1050 °C 60 min would give 0.21). **INFERRED**: the public profile
selects the lighter drive; this is the one place the public PDK constrains a thermal budget.

Caughey–Thomas 1967 and Scharfetter–Gummel 1969 are behind IEEE's paywall and Plummer's book is not online;
the mobility numbers are Selberherr's transcription (Tab. 4.1-1/2/3, rows `[4.21]`,
`~/paperbin/selberherr1984-analysis-and-simulation-of-semiconductor-devices.pdf`, open from TU Wien), the
SG form is Selberherr §6.1 (eqs. 6.1-39…43, which cite the 1969 paper), and Plummer's tables are read from
the publisher's lecture slides. Deal–Grove 1965 is in `~/paperbin/` in full. **Blocker for ember**: the
three originals (Scharfetter–Gummel, IEEE TED 16 (1969) 64; Caughey–Thomas, Proc. IEEE 55 (1967) 2192;
Plummer–Deal–Griffin chapters 6–8) if the docstrings are to cite pages.

## 2. Where the physics stops, said in the code

Each of these is in the header or docstring of the module it concerns (READ `Wafer.lean:1-40`,
`Constants.lean:205-212`, `Sky130Diode.lean:1-60`):

* The as-implanted boron profile is Gaussian, not Pearson IV; Plummer's slides give `R_p`, `ΔR_p` and no
  skewness; the sky130 well is deep enough that the tail matters less than the drive.
* Diffusivities are intrinsic; the `2.6·10²⁰` arsenic layer diffuses by concentration-enhanced mechanisms
  the table omits, which is why the recipe lands the junction by the implant alone (97 nm vs the public 100).
* No segregation into the growing oxide; no dose loss in the screen film (the image term folds it back,
  under 3 % here); no solubility or clustering limit on the active arsenic.
* The bottom contact is a 1D stand-in for a well tap at 1 µm; ohmic contacts are ideal.
* Convergence in `h` of the Scharfetter–Gummel scheme is not stated: the certificate is about the discrete
  system on the producer's mesh. What *is* stated across all parameters is residual boundedness, exact
  conservation (`residual_sum_telescopes`) and the current bound.

## 3. What the exercise says about the design decision

1. **The certificate's tolerance is a device parameter.** `tolRel` lives in the object, not the checker
   (`DdSpec.tolRel`), and `terminal_current_bound` makes the bound it buys explicit. At the measured
   floor the bound is `0.03 A/cm²` for this diode; whether that is enough is a question about the device
   (above −0.55 V) and the formulation (Slotboom variables would reduce `S` at the contact by the factor
   `e^{ψ/V_t}`), not about the solver. **PROPOSED**: the physics lane and this one share this finding: the
   same cancellation sits behind the motor loop's integer step (`CurrentLoop.lean` §7).
2. **Two assumed facts, each a one-liner about a real function on a short interval**, replace what would
   otherwise be an opaque dependence on `exp`; everything else (argument halving, squaring with outward
   rounding, the quotient for the Bernoulli function, the brackets for powers and roots) is proved
   (`expEnclosure_of_half`, `bernOf_mem`, `powBracket_agree`, `sqrtBracket_bounds`, `roundOut_mem`).
   A future `ℝ` in the library would discharge the two and nothing else needs to move.
3. **The planted refusal is kernel-checked and physical**: the format's `bad_refused` is a certificate for
   the wrong doping, decided by `decide +kernel` in a second, because the doping check comes before any
   enclosure is evaluated. The real certificates are `native_decide` (compiled trust), as the CAD lane's
   gouge check is; the interpreter time of 0.8 s per certificate says a kernel check is within reach for
   a 1D device and should be measured once.
4. **The producer is the right size.** `run_diode.py` is 330 lines, half of it a 50-digit mirror of the
   operators used only to choose the tolerance; devsim's equations are set up from its own `simple_physics`
   and `simple_dd` with node-wise mobility added. Nothing it computes is trusted, and it was wrong twice on
   the way (bias sign at the n⁺ contact, `n_i` without the `1/2`): the kernel's refusal found the second.
5. **Headline-free**: no `#print axioms`, no counts; the fixtures are `example`s with their reason, the
   constants carry their sources, and the one `#tooth` added mutates `WaferState.anneal` against
   `anneal_var_mono`.

## 4. What landed

| commit | what |
|---|---|
| `7549ffc` | `Obend/Hardware/Device/{Enclosure,Constants,Wafer,DriftDiffusion,Sky130Diode}.lean`; `apps/sky130-diode/devsim/{run_diode,emit_lean_fixtures}.py`; `apps/sky130-diode/certs/*.json` (two devices, five biases, I–V tables); `Obend/Teeth/Hardware/{DeviceCertificates,DeviceFixtures}.lean` |
| `0f87bd5` | `Physics.lean` → `ThermalPassivity.lean` (three sections kept, four deleted); `TcadBridge.lean` and `FabuBlox.lean` rewritten in place; importers, `SiliconTeeth` tooth 27, the two metasystem tests |
| (this commit) | this report; the handoff's adjudication section |

Built in `bb2:~/lane-device`: tier 1 `Obend.Hardware` (umbrella) green, every `Device/` module under 2 s;
tier 2 `Obend.Teeth.Hardware.{SiliconTeeth,DeviceFixtures}`, `metasystem.{SiliconSpineTest,
PhysicalSiliconSpineTest}` green; `Obend.Census` blocked by `Obend/Teeth/Analysis/Fixtures.lean:143`, red at
HEAD and not this lane's (handoff).

The dose-change test's numbers: device B (p-well `2.6·10¹³`) against A (`1.3·10¹³`): junction 95 vs 97 nm;
forward current at −0.5 V `1.54·10⁻³` vs `4.19·10⁻³ A/cm²` (×0.37), at −0.7 V `3.51` vs `9.51` (×0.37);
A's certificate on B's object: `refused (.doping 0) [0]` in 19 ms; both devices' own certificates: `ok`.

## 5. The next brief

1. **Scaled variables.** Rewrite `jn`/`jp` in Slotboom or quasi-Fermi form so `S` at a `10²⁰` contact is
   of the order of the current; then the bound bites at −0.3 V and reverse bias becomes certifiable.
   Measure the floor again; the tolerance may then go to `10⁻¹⁰` with margin.
2. **nMOS in 1D gradual-channel form** on the same recipe (the sky130 `toxe = 4.148 nm` gate, `ndep`,
   the BSIM `vth0 = 0.519 V` as the number to land near): the checker already supports a second Poisson
   region if the oxide is a node interval with `n = p = 0`; the gate contact is `contactOk` with a work
   function. The 2D mesh needs edge couples and node volumes from devsim in the object and nothing else new.
3. **Pearson IV implant** with Plummer's skewness/kurtosis table (needs the book, blocker above), or the
   two-sided Gaussian with the anneal done by a checked implicit step — the exact-Gaussian anneal does not
   survive either.
4. **Concentration-dependent diffusion and segregation**: `D(n/n_i)` per Plummer Table 7-?, which makes the
   anneal a checked PDE step rather than an exact map; the oxide's dopant pile-up/depletion with `m`.
5. **A kernel-checked real certificate**: measure `decide +kernel` on one 180-node pair; if under the tier-2
   budget, the format's trust can be `.kernel`.
6. **`TapeoutPipeline` stage 7 reads a device certificate**, retiring `TcadBridge` §0; and lift the
   `Interval` helpers into `RealAnalysis.lean` (physics lane).
7. Convergence in `h`: state the SG scheme's consistency as a checked Richardson pair (two meshes, one
   certificate each, the difference bounded) — the form Analysis can state without `ℝ`.
