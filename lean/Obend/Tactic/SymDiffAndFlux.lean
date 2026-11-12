module
public meta import Lean
public import Lean
public import Obend.Analysis.PdeSexprAndApprox
public meta import Obend.Analysis.PdeSexprAndApprox
public import Obend.Analysis.NonlinearMultiDPde
public meta import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.MultiDStencilTile
public meta import Obend.Hardware.MultiDStencilTile
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.MultiDStencilTile

/-!
# Symbolic Fréchet Differentiation, Reflective `CanonPoly` & S-Expression Parser (`Obend.Tactic.SymDiffAndFlux`)

Compile-time metaprogramming support and kernel-verified proof combinators for `#pde_solver`:
1. **Declarative Conservation-Law S-Expression Parser (`parseConservationLawSexpr`)**:
   - Quote-aware S-expression parser supporting arbitrary spatial/phase-space coordinates, state
     variables, rational parameters, strict positivity domain guards `(> rho 0)`, local `(let ...)`
     bindings, rational divisions `(/ a d)` / `(inv d)`, wave-speed / CFL bounds, and slope limiters,
     paired with `parseConservationLawSexpr_valid`.
2. **Reflective `CanonPoly` Conservation & Symmetrizer Proofs**:
   - `verifyFluctuationsReflective` & `fluctuationConservation_of_reflective` (discharging
     nonlinear rational Rusanov fluctuation conservation via `checkFluxEqReflective_sound`),
   - `checkSymmetrizerReflective` & `symmetrizerReflective_sound` (verifying `H(U) J(U)` symmetry
     entrywise via `CanonPoly` rational normalization).
3. **Bundled Kernel Soundness Combinators & Proof-Producing Tactics**:
   - `spec_jacobian_frechet_sound`, `spec_sweep_conserves_integral`, `spec_minmod_tvd_sound`,
     `spec_fusedGpuKernel_sound`, `spec_systolicRtl_ok`,
   - Meta expression quoters (`quoteConservationLawSpec`) and tactics `flux_eq_by_canon` /
     `sym_jacobian_frechet`.
-/

public section
namespace Obend.Tactic.SymDiffAndFlux
open Lean Elab Tactic Meta
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
open Obend.Hardware.MultiDStencilTile
set_option autoImplicit false

/-! ## 1. Declarative Conservation-Law S-Expression Parser & Validity Theorem -/

def parseDigitsAux : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if '0' ≤ c && c ≤ '9' then parseDigitsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

def parseNatChars : List Char → Option Nat
  | [] => none
  | cs => parseDigitsAux cs 0

def parseIntChars : List Char → Option Int
  | '-' :: cs => (parseNatChars cs).map fun n => -Int.ofNat n
  | cs => (parseNatChars cs).map Int.ofNat

def splitSlashChars : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '/' :: rest, revNum =>
    if rest.contains '/' then none else some (revNum.reverse, rest)
  | c :: rest, revNum => splitSlashChars rest (c :: revNum)

/-- Pure `List Char` rational literal parser (`"3"`, `"-7/5"`, `"1/10"`), avoiding `String.splitOn`. -/
def parseRatToken (s : String) : Option Rat :=
  let cs := s.toList
  match splitSlashChars cs [] with
  | none => (parseIntChars cs).map fun z => (z : Rat)
  | some (numCs, denCs) =>
    match parseIntChars numCs, parseNatChars denCs with
    | some num, some den => if den == 0 then none else some ((num : Rat) / (den : Rat))
    | _, _ => none

def evalParamOrRat (params : List (String × Rat)) : PdeSexpr → Option Rat
  | .atom tok =>
    match parseRatToken tok with
    | some q => some q
    | none => params.lookup tok
  | .list [.atom "-", x] => (evalParamOrRat params x).map (-·)
  | .list [.atom "+", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    some (a + b)
  | .list [.atom "*", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    some (a * b)
  | .list [.atom "/", x, y] => do
    let a ← evalParamOrRat params x
    let b ← evalParamOrRat params y
    if b == 0 then none else some (a / b)
  | _ => none

def findStringIdx : List String → String → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, target, k => if x == target then some k else findStringIdx xs target (k + 1)

def foldBinLeft (op : FluxExpr → FluxExpr → FluxExpr) : List FluxExpr → Option FluxExpr
  | [] => none
  | e :: es => some (es.foldl op e)

def parseLetBindings (fuel : Nat)
    (parseFn : List (String × FluxExpr) → PdeSexpr → Except String FluxExpr)
    (lets : List (String × FluxExpr)) : List PdeSexpr → Except String (List (String × FluxExpr))
  | [] => .ok lets
  | .list [.atom k, rhs] :: rest => do
    match fuel with
    | 0 => .error "expression fuel exhausted in let-binding"
    | f + 1 =>
      let e ← parseFn lets rhs
      parseLetBindings f parseFn ((k, e) :: lets) rest
  | _ => .error "malformed let-binding; expected (ident expr)"

def parseFluxExprWithFuel :
    Nat → List String → List String → List (String × FluxExpr) → PdeSexpr → Except String FluxExpr
  | 0, _, _, _, _ => .error "expression nesting depth exceeded fuel"
  | _ + 1, vars, params, lets, .atom tok =>
    match parseRatToken tok with
    | some q => .ok (.const q)
    | none =>
      match lets.lookup tok with
      | some bound => .ok bound
      | none =>
        match findStringIdx vars tok 0 with
        | some vi => .ok (.var vi)
        | none =>
          match findStringIdx params tok 0 with
          | some pi => .ok (.param pi)
          | none => .error s!"unknown state variable, parameter, or rational literal `{tok}`"
  | fuel + 1, vars, params, lets, .list items =>
    match items with
    | [.atom "neg", a] | [.atom "-", a] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      .ok (.neg ea)
    | [.atom "-", a, b] | [.atom "sub", a, b] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      let eb ← parseFluxExprWithFuel fuel vars params lets b
      .ok (.sub ea eb)
    | [.atom "inv", d] => do
      let ed ← parseFluxExprWithFuel fuel vars params lets d
      .ok (.invSafe ed)
    | [.atom "/", a, d] | [.atom "div", a, d] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      let ed ← parseFluxExprWithFuel fuel vars params lets d
      .ok (.mul ea (.invSafe ed))
    | [.atom "sq", a] => do
      let ea ← parseFluxExprWithFuel fuel vars params lets a
      .ok (.mul ea ea)
    | .atom "+" :: args | .atom "add" :: args => do
      let parsed ← args.mapM (parseFluxExprWithFuel fuel vars params lets)
      match foldBinLeft FluxExpr.add parsed with
      | some res => .ok res
      | none => .error "`+` requires at least one operand"
    | .atom "*" :: args | .atom "mul" :: args => do
      let parsed ← args.mapM (parseFluxExprWithFuel fuel vars params lets)
      match foldBinLeft FluxExpr.mul parsed with
      | some res => .ok res
      | none => .error "`*` requires at least one operand"
    | [.atom "let", .list binds, body] => do
      let lets' ← parseLetBindings fuel (parseFluxExprWithFuel fuel vars params) lets binds
      parseFluxExprWithFuel fuel vars params lets' body
    | _ => .error "unsupported flux S-expression form"

def parseDomainItem (vars params : List String) : PdeSexpr → Except String PosTarget
  | .list [.atom ">", .atom ident, .atom "0"]
  | .list [.atom "pos", .atom ident] =>
    match findStringIdx vars ident 0 with
    | some vi => .ok (.stateVar vi)
    | none =>
      match findStringIdx params ident 0 with
      | some pi => .ok (.paramVar pi)
      | none => .error s!"domain positivity target `{ident}` is neither a state variable nor a parameter"
  | _ => .error "malformed domain guard; expected (> ident 0) or (pos ident)"

def parseLimiterKind : PdeSexpr → Except String SlopeLimiterKind
  | .atom "minmod" => .ok .minmod
  | .atom "first-order" | .atom "firstOrder" | .atom "none" => .ok .firstOrder
  | _ => .error "unsupported slope limiter; expected `minmod` or `first-order`"

def findClause : List PdeSexpr → String → Option (List PdeSexpr)
  | [], _ => none
  | .list (.atom tag :: rest) :: cs, target =>
    if tag == target then some rest else findClause cs target
  | _ :: cs, target => findClause cs target

def parseAxisFluxRow (vars params : List String) (expectedCoord : String) (numVars : Nat) :
    PdeSexpr → Except String (List FluxExpr)
  | .list [.atom head, .list (.atom "let" :: .list binds :: bodyExprs)] => do
    if head == expectedCoord && bodyExprs.length == numVars then
      let lets ← parseLetBindings 64 (parseFluxExprWithFuel 64 vars params) [] binds
      bodyExprs.mapM (parseFluxExprWithFuel 64 vars params lets)
    else if head == expectedCoord && bodyExprs.length == 1 && numVars == 1 then
      let lets ← parseLetBindings 64 (parseFluxExprWithFuel 64 vars params) [] binds
      bodyExprs.mapM (parseFluxExprWithFuel 64 vars params lets)
    else if numVars == 2 && head != expectedCoord then
      [PdeSexpr.atom head, .list (.atom "let" :: .list binds :: bodyExprs)].mapM
        (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row let-block for coordinate `{expectedCoord}` has {bodyExprs.length} components, expected {numVars}"
  | .list (.atom head :: tail) =>
    if head == expectedCoord && tail.length == numVars then
      tail.mapM (parseFluxExprWithFuel 64 vars params [])
    else if (head :: tail.map (fun _ => "")).length == numVars then
      (PdeSexpr.atom head :: tail).mapM (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row for coordinate `{expectedCoord}` does not match variable count {numVars}"
  | .list raw =>
    if raw.length == numVars then
      raw.mapM (parseFluxExprWithFuel 64 vars params [])
    else
      .error s!"flux row for coordinate `{expectedCoord}` has length {raw.length}, expected {numVars}"
  | _ => .error s!"malformed flux row for coordinate `{expectedCoord}`"

def parseAxisFluxRows (vars params : List String) :
    List String → List PdeSexpr → Except String (List (List FluxExpr))
  | [], [] => .ok []
  | c :: cs, r :: rs => do
    let row ← parseAxisFluxRow vars params c vars.length r
    let rest ← parseAxisFluxRows vars params cs rs
    .ok (row :: rest)
  | _, _ => .error "number of directional flux rows does not match `(coords ...)` dimension"

def parseParamEntry : PdeSexpr → Except String (String × Rat)
  | .list [.atom k, .atom v] =>
    match parseRatToken v with
    | some q => .ok (k, q)
    | none => .error s!"invalid rational parameter value `{v}` for `{k}`"
  | _ => .error "malformed parameter entry; expected (name rational)"

def diagnoseSpecFailure (s : ConservationLawSpec) : String :=
  if s.coords.isEmpty then "coordinate list `(coords ...)` must be non-empty"
  else if s.vars.isEmpty then "state variable list `(vars ...)` must be non-empty"
  else if s.coords.eraseDups.length != s.coords.length then "duplicate coordinate names in `(coords ...)`"
  else if s.vars.eraseDups.length != s.vars.length then "duplicate state variable names in `(vars ...)`"
  else if (s.params.map Prod.fst).eraseDups.length != s.params.length then "duplicate parameter names in `(params ...)`"
  else if s.fluxes.length != s.coords.length then "directional flux row count does not match `(coords ...)`"
  else if !s.fluxes.all (fun row => row.length == s.vars.length) then "flux row width does not match `(vars ...)`"
  else if !s.fluxes.all (fun row => row.all (checkExprDomainSafe s.domain)) then
    "unguarded rational division `(inv d)` / `(/ a d)`: denominator is not certified strictly positive by `(domain ...)`"
  else "wave-speed / CFL violation: require `0 < aMax`, `0 ≤ cfl`, and `cfl * aMax ≤ 1`"

def parseConservationLawRaw (text : String) : Except String ConservationLawSpec := do
  let tree ← match parseSexpr text with
    | some t => .ok t
    | none => .error "malformed S-expression syntax"
  let clauses ← match tree with
    | .list (.atom "conservation-law" :: cs) => .ok cs
    | _ => .error "expected top-level `(conservation-law ...)` form"
  let name ← match findClause clauses "name" with
    | some [.atom n] => .ok n
    | _ => .error "missing or malformed `(name ...)` clause"
  let coordSexprs ← match findClause clauses "coords" with
    | some cs => .ok cs
    | none => .error "missing `(coords ...)` clause"
  let coords ← match coordSexprs.mapM atomText with
    | some cs => .ok cs
    | none => .error "`(coords ...)` entries must be bare or quoted identifiers"
  let varSexprs ← match findClause clauses "vars" with
    | some vs => .ok vs
    | none => .error "missing `(vars ...)` clause"
  let vars ← match varSexprs.mapM atomText with
    | some vs => .ok vs
    | none => .error "`(vars ...)` entries must be bare or quoted identifiers"
  let params ← match findClause clauses "params" with
    | some ps => ps.mapM parseParamEntry
    | none => .ok []
  let paramNames := params.map Prod.fst
  let domain ← match findClause clauses "domain" with
    | some ds => ds.mapM (parseDomainItem vars paramNames)
    | none => .ok []
  let fluxRowsSexpr ← match findClause clauses "fluxes" with
    | some fs => .ok fs
    | none => .error "missing `(fluxes ...)` clause"
  let fluxes ← parseAxisFluxRows vars paramNames coords fluxRowsSexpr
  let (aMax, cfl) ← match findClause clauses "wavespeed" with
    | some [spSx, cflSx] =>
      match evalParamOrRat params spSx, evalParamOrRat params cflSx with
      | some a, some nu => .ok (a, nu)
      | _, _ => .error "malformed `(wavespeed aMax cfl)` values"
    | _ => .error "missing or malformed `(wavespeed aMax cfl)` clause"
  let limiter ← match findClause clauses "limiter" with
    | some [limSx] => parseLimiterKind limSx
    | none => .ok .minmod
    | _ => .error "malformed `(limiter ...)` clause"
  .ok { name, coords, vars, params, domain, fluxes, aMax, cfl, limiter }

/-- Parse and statically validate a multi-dimensional nonlinear conservation-law S-expression,
returning descriptive diagnostics on syntax, domain-positivity, dimension, or CFL errors. -/
def parseConservationLawSexprWithDiag (text : String) : Except String ConservationLawSpec :=
  match parseConservationLawRaw text with
  | .error msg => .error msg
  | .ok raw => if raw.checkValid then .ok raw else .error (diagnoseSpecFailure raw)

def parseConservationLawSexpr (text : String) : Option ConservationLawSpec :=
  match parseConservationLawSexprWithDiag text with
  | .ok spec => some spec
  | .error _ => none

theorem parseConservationLawSexpr_valid (text : String) (spec : ConservationLawSpec)
    (h : parseConservationLawSexpr text = some spec) :
    spec.checkValid = true := by
  unfold parseConservationLawSexpr parseConservationLawSexprWithDiag at h
  cases hRaw : parseConservationLawRaw text with
  | error _ => simp [hRaw] at h
  | ok raw =>
    simp only [hRaw] at h
    by_cases hv : raw.checkValid = true
    · simp only [hv, ↓reduceIte, Option.some.injEq] at h; subst h; exact hv
    · simp [hv] at h

/-! ## 2. Certified Symbolic Jacobian, Reflective `CanonPoly` & Accelerator Lowering Theorems -/

/-- Exact symbolic Jacobian tensor `[J_0(U), …, J_{D-1}(U)]` across all spatial/phase-space axes. -/
@[expose] def specJacobians (spec : ConservationLawSpec) : List (List (List FluxExpr)) :=
  spec.fluxes.map (symJacobian spec.numVars)

theorem checkValid_flux_row_len (s : ConservationLawSpec) (hValid : s.checkValid = true)
    (d : Nat) (hd : d < s.numDims) :
    (getOr s.fluxes d []).length = s.numVars := by
  unfold ConservationLawSpec.checkValid at hValid
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hValid
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hFluxLen⟩, hRows⟩, _⟩ := hValid
  have hd' : d < s.fluxes.length := by unfold ConservationLawSpec.numDims at hd; omega
  exact (hRows (getOr s.fluxes d []) (getOr_mem_of_lt s.fluxes d [] hd')).1

theorem checkValid_cfl_bounds (s : ConservationLawSpec) (hValid : s.checkValid = true) :
    0 < s.aMax ∧ 0 ≤ s.cfl ∧ s.cfl * s.aMax ≤ 1 := by
  unfold ConservationLawSpec.checkValid at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
  exact hValid.2

theorem checkValid_fluxes_len (s : ConservationLawSpec) (hValid : s.checkValid = true) :
    s.fluxes.length = s.numDims := by
  unfold ConservationLawSpec.checkValid at hValid
  unfold ConservationLawSpec.numDims
  simp only [Bool.and_eq_true, beq_iff_eq] at hValid
  exact hValid.1.1.2

/-- **Directional Symbolic Jacobian Fréchet Soundness (`spec_jacobian_frechet_sound`)**:
For every coordinate axis `d < spec.numDims` and conserved component `i < spec.numVars`, row `d` of
`specJacobians spec` is the exact multivariable Fréchet derivative of `F_d(U)` with explicit
quadratic rational remainder `h² · R_{d,i}(U, V, h)` on `DomainValid spec.domain`. -/
theorem spec_jacobian_frechet_sound (spec : ConservationLawSpec) (hValid : spec.checkValid = true)
    (d i : Nat) (hd : d < spec.numDims) (hi : i < spec.numVars)
    (u V : Vec) (h : Rat)
    (hDom0 : DomainValid spec.domain ⟨u, spec.paramEnv⟩)
    (hDom1 : DomainValid spec.domain (shiftVecEnv spec.numVars ⟨u, spec.paramEnv⟩ h V)) :
    let fluxD := getOr spec.fluxes d []
    let jacD := getOr (specJacobians spec) d []
    evalFlux (getOr fluxD i (.const 0)) (shiftVecEnv spec.numVars ⟨u, spec.paramEnv⟩ h V) -
      evalFlux (getOr fluxD i (.const 0)) ⟨u, spec.paramEnv⟩ =
      h * mulVec spec.numVars (evalSymJacobianMat jacD ⟨u, spec.paramEnv⟩) V i +
      (h * h) * symDirectionalRem spec.numVars (getOr fluxD i (.const 0)) ⟨u, spec.paramEnv⟩ V h := by
  dsimp only [specJacobians]
  have hd' : d < spec.fluxes.length := by rw [checkValid_fluxes_len spec hValid]; exact hd
  rw [getOr_map_lt spec.fluxes (symJacobian spec.numVars) d [] [] hd']
  exact symJacobian_frechet_taylor spec.domain spec.numVars (getOr spec.fluxes d [])
    (checkValid_flux_row_len spec hValid d hd)
    (fun k hk => ConservationLawSpec.checkValid_flux_domainSafe spec hValid d k hd hk)
    ⟨u, spec.paramEnv⟩ V h hDom0 hDom1 i hi

/-- Interleave two state vectors `(uL, uR)` at even/odd variable slots and bind `.param 0 := aMax`
so two-state interface identities can be decided reflectively via `CanonPoly` / `RatCanon`. -/
def injLeftVars : FluxExpr → FluxExpr
  | .const q => .const q
  | .var k => .var (2 * k)
  | .param p => .param (p + 1)
  | .neg a => .neg (injLeftVars a)
  | .add a b => .add (injLeftVars a) (injLeftVars b)
  | .sub a b => .sub (injLeftVars a) (injLeftVars b)
  | .mul a b => .mul (injLeftVars a) (injLeftVars b)
  | .invSafe d => .invSafe (injLeftVars d)

def injRightVars : FluxExpr → FluxExpr
  | .const q => .const q
  | .var k => .var (2 * k + 1)
  | .param p => .param (p + 1)
  | .neg a => .neg (injRightVars a)
  | .add a b => .add (injRightVars a) (injRightVars b)
  | .sub a b => .sub (injRightVars a) (injRightVars b)
  | .mul a b => .mul (injRightVars a) (injRightVars b)
  | .invSafe d => .invSafe (injRightVars d)

def twoStateInterleavedEnv (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) : FluxEnv where
  state := fun idx => if idx % 2 == 0 then uL (idx / 2) else uR (idx / 2)
  params := fun p => if p == 0 then aMax else params (p - 1)

def twoStateInterleavedDom (dom : List PosTarget) : List PosTarget :=
  dom.flatMap fun
    | .stateVar k => [.stateVar (2 * k), .stateVar (2 * k + 1)]
    | .paramVar p => [.paramVar (p + 1)]

theorem evalFlux_injLeftVars (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) (e : FluxExpr) :
    evalFlux (injLeftVars e) (twoStateInterleavedEnv params aMax uL uR) =
      evalFlux e ⟨uL, params⟩ := by
  induction e with
  | const _ => rfl
  | var k =>
    simp [injLeftVars, evalFlux, twoStateInterleavedEnv,
      show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  | param p =>
    simp [injLeftVars, evalFlux, twoStateInterleavedEnv]
  | neg a iha => simp [injLeftVars, evalFlux, iha]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | invSafe a iha =>
    simp_all [injLeftVars, evalFlux]

theorem evalFlux_injRightVars (params : Nat → Rat) (aMax : Rat) (uL uR : Vec) (e : FluxExpr) :
    evalFlux (injRightVars e) (twoStateInterleavedEnv params aMax uL uR) =
      evalFlux e ⟨uR, params⟩ := by
  induction e with
  | const _ => rfl
  | var k =>
    simp [injRightVars, evalFlux, twoStateInterleavedEnv,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
  | param p =>
    simp [injRightVars, evalFlux, twoStateInterleavedEnv]
  | neg a iha => simp [injRightVars, evalFlux, iha]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | invSafe a iha =>
    simp_all [injRightVars, evalFlux]

theorem domainValid_twoStateInterleaved (dom : List PosTarget) (params : Nat → Rat) (aMax : Rat)
    (uL uR : Vec)
    (hL : DomainValid dom ⟨uL, params⟩) (hR : DomainValid dom ⟨uR, params⟩) :
    DomainValid (twoStateInterleavedDom dom) (twoStateInterleavedEnv params aMax uL uR) := by
  intro t ht
  unfold twoStateInterleavedDom at ht
  rw [List.mem_flatMap] at ht
  obtain ⟨src, hSrcMem, hTarget⟩ := ht
  cases src with
  | stateVar k =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTarget
    rcases hTarget with rfl | rfl
    · simpa [twoStateInterleavedEnv, show (2 * k) % 2 = 0 by omega,
        show (2 * k) / 2 = k by omega] using hL (.stateVar k) hSrcMem
    · simpa [twoStateInterleavedEnv, show (2 * k + 1) % 2 = 1 by omega,
        show (2 * k + 1) / 2 = k by omega] using hR (.stateVar k) hSrcMem
  | paramVar p =>
    simp only [List.mem_singleton] at hTarget
    subst hTarget
    simpa [twoStateInterleavedEnv] using hL (.paramVar p) hSrcMem

/-- Construct the reflective two-state `FluxExpr` pair `(A⁻ΔQ + A⁺ΔQ, F(U_R) - F(U_L))` for `(d, i)`. -/
def fluctReflectiveExprPair (spec : ConservationLawSpec) (d i : Nat) : FluxExpr × FluxExpr :=
  let fExpr := getOr (getOr spec.fluxes d []) i (.const 0)
  let fL := injLeftVars fExpr
  let fR := injRightVars fExpr
  let fHat : FluxExpr :=
    .sub (.mul (.const (1 / 2)) (.add fL fR))
         (.mul (.mul (.param 0) (.const (1 / 2))) (.sub (.var (2 * i + 1)) (.var (2 * i))))
  let amdq := .sub fHat fL
  let apdq := .sub fR fHat
  (.add amdq apdq, .sub fR fL)

/-- Reflective `CanonPoly` fluctuation conservation check across all `D` axes and `m` components. -/
def verifyFluctuationsReflective (spec : ConservationLawSpec) : Bool :=
  let dom2 := twoStateInterleavedDom spec.domain
  (List.range spec.numDims).all fun d =>
    (List.range spec.numVars).all fun i =>
      let (lhs, rhs) := fluctReflectiveExprPair spec d i
      checkFluxEqReflective dom2 lhs rhs

/-- **Reflective `CanonPoly` Fluctuation Conservation (`fluctuationConservation_of_reflective`)**:
Discharges nonlinear rational LeVeque fluctuation conservation `A⁻ΔQ + A⁺ΔQ = F(U_R) - F(U_L)` across
all axes `d < spec.numDims` and components `i < spec.numVars` via `checkFluxEqReflective_sound`! -/
theorem fluctuationConservation_of_reflective (spec : ConservationLawSpec)
    (hRefl : verifyFluctuationsReflective spec = true)
    (d i : Nat) (hd : d < spec.numDims) (hi : i < spec.numVars)
    (uL uR : Vec)
    (hDomL : DomainValid spec.domain ⟨uL, spec.paramEnv⟩)
    (hDomR : DomainValid spec.domain ⟨uR, spec.paramEnv⟩) :
    let fluxD := getOr spec.fluxes d []
    rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uR i +
      rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uR i =
      evalFlux (getOr fluxD i (.const 0)) ⟨uR, spec.paramEnv⟩ -
      evalFlux (getOr fluxD i (.const 0)) ⟨uL, spec.paramEnv⟩ ∧
    rusanovFluctMinus fluxD spec.paramEnv spec.aMax uL uL i = 0 ∧
    rusanovFluctPlus fluxD spec.paramEnv spec.aMax uL uL i = 0 := by
  unfold verifyFluctuationsReflective at hRefl
  simp only [List.all_eq_true] at hRefl
  have hPair := (hRefl d (List.mem_range.mpr hd)) i (List.mem_range.mpr hi)
  have hDom2 := domainValid_twoStateInterleaved spec.domain spec.paramEnv spec.aMax uL uR hDomL hDomR
  have hSound := checkFluxEqReflective_sound (twoStateInterleavedDom spec.domain)
    (fluctReflectiveExprPair spec d i).1 (fluctReflectiveExprPair spec d i).2 hPair
    (twoStateInterleavedEnv spec.paramEnv spec.aMax uL uR) hDom2
  dsimp only [fluctReflectiveExprPair] at hSound
  simp only [evalFlux, evalFlux_injLeftVars, evalFlux_injRightVars] at hSound
  simp only [twoStateInterleavedEnv, beq_self_eq_true, ↓reduceIte,
    show (2 * i + 1) % 2 = 1 by omega, show ¬ (1 == 0) = true by decide,
    Bool.false_eq_true, show (2 * i + 1) / 2 = i by omega,
    show (2 * i) % 2 = 0 by omega, show (2 * i) / 2 = i by omega] at hSound
  refine ⟨?_, (rusanovFluct_conservation _ _ _ uL uL i).2.1,
    (rusanovFluct_conservation _ _ _ uL uL i).2.2⟩
  dsimp only [rusanovFluctMinus, rusanovFluctPlus, rusanovNonlinearFlux]
  rw [show spec.aMax / 2 = spec.aMax * (1 / 2 : Rat) by grind]
  exact hSound

/-- Symbolic `m × m` matrix product `A · B` over `FluxExpr`. -/
def symMatMul (m : Nat) (A B : List (List FluxExpr)) : List (List FluxExpr) :=
  (List.range m).map fun i =>
    (List.range m).map fun j =>
      (List.range m).foldl (fun acc k =>
        .add acc (.mul (getOr (getOr A i []) k (.const 0))
                       (getOr (getOr B k []) j (.const 0)))) (.const 0)

/-- Reflective `CanonPoly` check for Friedrichs symmetrizer symmetry `(H(U) J(U))_{ij} = (H(U) J(U))_{ji}`. -/
def checkSymmetrizerReflective (dom : List PosTarget) (m : Nat)
    (H jac : List (List FluxExpr)) : Bool :=
  let HJ := symMatMul m H jac
  (List.range m).all fun i =>
    (List.range m).all fun j =>
      checkFluxEqReflective dom
        (getOr (getOr HJ i []) j (.const 0))
        (getOr (getOr HJ j []) i (.const 0))

theorem symmetrizerReflective_sound (dom : List PosTarget) (m : Nat)
    (H jac : List (List FluxExpr))
    (hSym : checkSymmetrizerReflective dom m H jac = true)
    (env : FluxEnv) (hDom : DomainValid dom env)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    let HJ := symMatMul m H jac
    evalFlux (getOr (getOr HJ i []) j (.const 0)) env =
      evalFlux (getOr (getOr HJ j []) i (.const 0)) env := by
  unfold checkSymmetrizerReflective at hSym
  simp only [List.all_eq_true] at hSym
  exact checkFluxEqReflective_sound dom _ _
    ((hSym i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)) env hDom

example : checkSymmetrizerReflective [] 1 [[.const 1]] [[.const 2]] = true := by decide +kernel

/-- **Multi-Dimensional Sweep & Rollout Conservation (`spec_sweep_conserves_integral`)**:
Bundles exact Lie splitting conservation, 2nd-order Strang splitting conservation, multi-turn
adaptive rollout conservation + monotone Courant time, and CFL violation refusal completeness. -/
theorem spec_sweep_conserves_integral (spec : ConservationLawSpec)
    (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N) :
    let axisFlux := fun d => rusanovNonlinearFlux (getOr spec.fluxes d []) spec.paramEnv spec.aMax
    (∀ ν : Rat, ∀ U : MultiDGrid, ∀ c : Nat,
      totalGridIntegral dims (evalMultiDSweep dims ν axisFlux U) c = totalGridIntegral dims U c ∧
      totalGridIntegral dims (evalStrangSweep dims ν axisFlux U) c = totalGridIntegral dims U c) ∧
    (∀ (st0 stF : PdeRolloutState) (turns : List PdeRolloutTurn),
      runPdeRolloutTrace spec dims st0 turns = some stF →
      (∀ c, totalGridIntegral dims stF.grid c = totalGridIntegral dims st0.grid c) ∧
      st0.elapsedCourant ≤ stF.elapsedCourant ∧
      stF.acceptedSteps = st0.acceptedSteps + turns.length) ∧
    (∀ (st : PdeRolloutState) (turn : PdeRolloutTurn),
      stepPdeRolloutTurn spec dims st turn = none ↔
        ¬ (0 ≤ turn.courant ∧ turn.courant * spec.aMax ≤ 1)) :=
  ⟨fun ν U c => multiDSweep_conserves_total_mass_momentum_energy dims hPos ν _ U c,
   fun st0 stF turns hRun => runPdeRolloutTrace_invariants spec dims hPos st0 stF turns hRun,
   fun st turn => stepPdeRolloutTurn_none_iff_cfl_violation spec dims st turn⟩

/-- **Nonlinear 2nd-Order MUSCL-`minmod` TVD Soundness (`spec_minmod_tvd_sound`)**:
Bundles 2nd-order affine reconstruction exactness (positive & negative slopes), mirror symmetry,
and nonlinear MUSCL-`minmod` Rusanov TVD non-increase under `2 * ν * spec.aMax ≤ 1`. -/
theorem spec_minmod_tvd_sound (spec : ConservationLawSpec) (hValid : spec.checkValid = true) :
    (∀ u0 s : Rat,
      musclReconstructLeft (u0 - s) u0 (u0 + s) = u0 - (1 / 2 : Rat) * s ∧
      musclReconstructRight (u0 - s) u0 (u0 + s) = u0 + (1 / 2 : Rat) * s) ∧
    (∀ uPrev uCurr uNext : Rat,
      musclReconstructLeft uNext uCurr uPrev = musclReconstructRight uPrev uCurr uNext) ∧
    (∀ (f : Rat → Rat) (ν : Rat),
      0 ≤ ν → 2 * ν * spec.aMax ≤ 1 →
      (∀ x y : Rat, ratAbs (f y - f x) ≤ spec.aMax * ratAbs (y - x)) →
      ∀ (N : Nat) (u : Nat → Rat),
        totalVariation1D N (musclMinmodRusanov1DStep f spec.aMax ν N u) ≤ totalVariation1D N u) := by
  have haPos := (checkValid_cfl_bounds spec hValid).1
  exact ⟨muscl_minmod_linear_exact, muscl_minmod_mirror_symm,
    fun f ν hν hcfl hLip N u =>
      tvd_rusanov_minmod_step_nonincreasing f spec.aMax ν (Rat.le_of_lt haPos) hν hcfl hLip N u⟩

/-- Default single-pass vertically fused multi-dimensional `minmod` + Rusanov GPU kernel for `spec`. -/
def buildSpecFusedGpuKernel (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims : List Nat) : FusedProgram :=
  let cNum : Int := spec.cfl.num
  let vNum : Int := spec.aMax.num
  compileMultiDSweepFused b dims 2 (multiDMinmodRusanovExpr dims.length cNum vNum)

/-- **Fused GPU Kernel & Multi-D Brick Halo Tiling Soundness (`spec_fusedGpuKernel_sound`)**:
Proves single-pass vertical SOAC fusion equivalence + `letCount` non-increase, exact `D`-dimensional
brick-tiling equivalence (including non-multiple tail bricks), and strict HBM read reduction! -/
theorem spec_fusedGpuKernel_sound (spec : ConservationLawSpec) (b : StencilBoundary)
    (dims brickDims : List Nat) (grid : List Word)
    (hNonEmpty : dims ≠ [])
    (hLen : brickDims.length = dims.length)
    (hB2 : ∀ B ∈ brickDims, 2 ≤ B)
    (hBN : ∀ d < dims.length, getOr brickDims d 0 ≤ getOr dims d 0) :
    let e := multiDMinmodRusanovExpr dims.length spec.cfl.num spec.aMax.num
    evalFused (fun _ => grid) (buildSpecFusedGpuKernel spec b dims) =
      [evalMultiDBrickTiled brickDims b dims 2 (scalarStencil e) grid] ∧
    evalMultiDBrickTiled brickDims b dims 2 (scalarStencil e) grid =
      evalStencilMultiD b dims 2 (scalarStencil e) grid ∧
    multiDBrickHbmReads brickDims 2 dims < (2 * 2 + 1) ^ dims.length * gridCellCount dims := by
  have hBPos : ∀ B ∈ brickDims, 0 < B := fun B hB => by have := hB2 B hB; omega
  have hDPos : ∀ N ∈ dims, 0 < N := by
    intro N hN
    obtain ⟨d, hd, rfl⟩ : ∃ d, d < dims.length ∧ getOr dims d 0 = N := by
      clear hNonEmpty hLen hBN
      induction dims with
      | nil => cases hN
      | cons M ds ih =>
        rcases List.mem_cons.mp hN with rfl | hRest
        · exact ⟨0, by simp, rfl⟩
        · obtain ⟨k, hk, hEq⟩ := ih hRest
          exact ⟨k + 1, by simp; omega, hEq⟩
    have hBd_ge2 : 2 ≤ getOr brickDims d 0 :=
      hB2 (getOr brickDims d 0) (getOr_mem_of_lt brickDims d 0 (by omega))
    have hLe := hBN d hd
    omega
  have hTile := multiDBrickTiled_eq_global_sweep brickDims b dims 2
    (scalarStencil (multiDMinmodRusanovExpr dims.length spec.cfl.num spec.aMax.num)) grid
    hLen hBPos hDPos
  have hFused := (compileMultiDSweepFused_sound b dims 2
    (multiDMinmodRusanovExpr dims.length spec.cfl.num spec.aMax.num) grid).1
  unfold buildSpecFusedGpuKernel
  dsimp only
  refine ⟨by rw [hFused, ← hTile], hTile,
    multiDBrickHbmReads_lt_global brickDims dims 2 hNonEmpty (by omega) hLen hB2 hBN⟩

/-- Synthesize the pipelined Q32.32 systolic `RtlModule` for directional flux `axis` of `spec`. -/
def buildSpecSystolicRtl (spec : ConservationLawSpec) (axis : Nat) : RtlModule :=
  let plan := specializeFluxSweep spec
  let dag := getOr plan.axisFluxDags axis ⟨[], []⟩
  emitSystolicFluxCellRtlModule s!"{spec.name}_flux_axis{axis}" spec.vars dag

theorem spec_systolicRtl_ok (spec : ConservationLawSpec) (axis : Nat) :
    checkRtlModule (buildSpecSystolicRtl spec axis) = true := by
  unfold buildSpecSystolicRtl
  dsimp only [specializeFluxSweep]
  by_cases hLt : axis < spec.fluxes.length
  · rw [getOr_map_lt spec.fluxes (compileFluxSsaDag (some spec.paramEnv)) axis [] ⟨[], []⟩ hLt]
    exact emitSystolicFluxCellRtlModule_ok _ spec.vars _
      (compileFluxSsaDag_sound (some spec.paramEnv) (getOr spec.fluxes axis [])).1
  · have hGe : (spec.fluxes.map (compileFluxSsaDag (some spec.paramEnv))).length ≤ axis := by
      simp; omega
    have hOut : ∀ (xs : List FluxSsaDag) (k : Nat), xs.length ≤ k →
        getOr xs k ⟨[], []⟩ = ⟨[], []⟩ := by
      intro xs; induction xs with
      | nil => intro _ _; rfl
      | cons _ rest ih =>
        intro k hk; cases k with | zero => simp at hk | succ k' => exact ih k' (by simpa using hk)
    rw [hOut _ axis hGe]
    exact emitSystolicFluxCellRtlModule_ok _ spec.vars ⟨[], []⟩ rfl

theorem domainValid_nil (env : FluxEnv) : DomainValid [] env := fun _ h => nomatch h

/-! ## 3. Meta `Lean.Expr` Quoters & Proof-Producing Tactics (`flux_eq_by_canon`, `sym_jacobian_frechet`) -/

meta def quoteRatExpr (q : Rat) : Lean.Expr :=
  let numExpr : Lean.Expr := ToExpr.toExpr q.num
  let denExpr : Lean.Expr := ToExpr.toExpr q.den
  mkApp2 (mkConst ``Rat.divInt) numExpr (mkApp (mkConst ``Int.ofNat) denExpr)

meta def quoteListExpr {α : Type} (elemTy : Lean.Expr) (quoteElem : α → Lean.Expr) : List α → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) elemTy
  | x :: xs =>
    mkApp3 (mkConst ``List.cons [Level.zero]) elemTy (quoteElem x) (quoteListExpr elemTy quoteElem xs)

meta def quoteFluxExpr : FluxExpr → Lean.Expr
  | .const q => mkApp (mkConst ``FluxExpr.const) (quoteRatExpr q)
  | .var i => mkApp (mkConst ``FluxExpr.var) (ToExpr.toExpr i)
  | .param p => mkApp (mkConst ``FluxExpr.param) (ToExpr.toExpr p)
  | .neg a => mkApp (mkConst ``FluxExpr.neg) (quoteFluxExpr a)
  | .add a b => mkApp2 (mkConst ``FluxExpr.add) (quoteFluxExpr a) (quoteFluxExpr b)
  | .sub a b => mkApp2 (mkConst ``FluxExpr.sub) (quoteFluxExpr a) (quoteFluxExpr b)
  | .mul a b => mkApp2 (mkConst ``FluxExpr.mul) (quoteFluxExpr a) (quoteFluxExpr b)
  | .invSafe d => mkApp (mkConst ``FluxExpr.invSafe) (quoteFluxExpr d)

meta def quotePosTarget : PosTarget → Lean.Expr
  | .stateVar idx => mkApp (mkConst ``PosTarget.stateVar) (ToExpr.toExpr idx)
  | .paramVar idx => mkApp (mkConst ``PosTarget.paramVar) (ToExpr.toExpr idx)

meta def quoteSlopeLimiter : SlopeLimiterKind → Lean.Expr
  | .firstOrder => mkConst ``SlopeLimiterKind.firstOrder
  | .minmod => mkConst ``SlopeLimiterKind.minmod

meta def quoteParamPair (p : String × Rat) : Lean.Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    (mkConst ``String) (mkConst ``Rat) (ToExpr.toExpr p.1) (quoteRatExpr p.2)

meta def quoteConservationLawSpec (s : ConservationLawSpec) : Lean.Expr :=
  let strTy := mkConst ``String
  let fluxExprTy := mkConst ``FluxExpr
  let fluxRowTy := mkApp (mkConst ``List [Level.zero]) fluxExprTy
  let paramPairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) strTy (mkConst ``Rat)
  let posTargetTy := mkConst ``PosTarget
  mkAppN (mkConst ``ConservationLawSpec.mk) #[
    ToExpr.toExpr s.name,
    quoteListExpr strTy ToExpr.toExpr s.coords,
    quoteListExpr strTy ToExpr.toExpr s.vars,
    quoteListExpr paramPairTy quoteParamPair s.params,
    quoteListExpr posTargetTy quotePosTarget s.domain,
    quoteListExpr fluxRowTy (quoteListExpr fluxExprTy quoteFluxExpr) s.fluxes,
    quoteRatExpr s.aMax,
    quoteRatExpr s.cfl,
    quoteSlopeLimiter s.limiter
  ]

theorem flux_eq_of_canon {dom : List PosTarget} {e1 e2 : FluxExpr} {env : FluxEnv}
    (hDom : DomainValid dom env) (hOk : checkFluxEqReflective dom e1 e2 = true) :
    evalFlux e1 env = evalFlux e2 env :=
  checkFluxEqReflective_sound dom e1 e2 hOk env hDom

/-- `by flux_eq_by_canon`: Discharges goals of the form `evalFlux e₁ env = evalFlux e₂ env` using
local hypothesis `hDom : DomainValid dom env` and reflective `CanonPoly` (`checkFluxEqReflective_sound`). -/
macro "flux_eq_by_canon" : tactic =>
  `(tactic| (
    try dsimp only
    first
      | refine flux_eq_of_canon (by assumption) (by decide +kernel)
      | refine flux_eq_of_canon (domainValid_nil _) (by decide +kernel)))

/-- `by sym_jacobian_frechet`: Discharges multivariable Fréchet Taylor remainder goals via
`symJacobian_frechet_taylor` or `symExpr_frechet_taylor` and `decide +kernel` domain-safety verification. -/
macro "sym_jacobian_frechet" : tactic =>
  `(tactic| (
    try dsimp only
    first
      | apply symJacobian_frechet_taylor <;> first | assumption | decide +kernel
      | apply symExpr_frechet_taylor <;>
          first
            | assumption
            | exact checkExprDomainSafe_implies_denomNonzero [] _ _ (by decide +kernel) (domainValid_nil _)))

end Obend.Tactic.SymDiffAndFlux
