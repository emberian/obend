module
public import Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.Diff
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.HyperbolicPdeCert

/-!
Linear conservation-law specifications and rational finite-volume error tubes.
The reference solution is the frozen-coefficient discrete Rusanov trajectory.
The parser accepts coefficient matrices with named rational parameters, verifies
all dimensions, and validates the supplied Friedrichs/eigensystem certificate.

The approximation judge certifies a declared conservative tube. Its meaning
includes both the tube ceiling and the true trajectory error; a refused tube
is not a claim that the true error must exceed that ceiling.
-/

public section
namespace Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.HyperbolicPde
set_option autoImplicit false

abbrev Grid := Nat → Vec

def gridSub (u v : Grid) : Grid := fun i c => u i c - v i c
def gridAdd (u v : Grid) : Grid := fun i c => u i c + v i c

def discreteHEnergy (m n : Nat) (H : Mat) (u : Grid) : Rat :=
  sumTo n fun i => dot m (u i) (mulVec m H (u i))

def form (m : Nat) (H : Mat) (u v : Vec) : Rat := dot m u (mulVec m H v)

theorem form_lin_right (m : Nat) (H : Mat) (u v w : Vec) (a b : Rat) :
    form m H u (fun c => a * v c + b * w c) = a * form m H u v + b * form m H u w := by
  simp only [form, dot, mulVec_lin]
  rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]
  exact sumTo_congr fun _ _ => by grind

theorem form_lin_left (m : Nat) (H : Mat) (u v w : Vec) (a b : Rat) :
    form m H (fun c => a * u c + b * v c) w = a * form m H u w + b * form m H v w := by
  simp only [form, dot]
  rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]
  exact sumTo_congr fun _ _ => by grind

/-- Exact linearity of the frozen-coefficient finite-volume operator. -/
theorem rusanovLinear_sub (m n : Nat) (A : Mat) (a ν : Rat) (u v : Grid) :
    gridSub (rusanovStep m A a ν n u) (rusanovStep m A a ν n v) =
      rusanovStep m A a ν n (gridSub u v) := by
  funext i c
  have e : (fun j => gridSub u v (nextCell n i) j - gridSub u v (prevCell n i) j) =
      (fun j => 1 * (u (nextCell n i) j - u (prevCell n i) j) +
        (-1) * (v (nextCell n i) j - v (prevCell n i) j)) := by
    funext j; simp only [gridSub]; grind
  simp only [gridSub, rusanovStep]
  have e' := congrArg (fun x => mulVec m A x c) e
  simp only [mulVec_lin] at e'
  simp only [gridSub] at e'
  rw [e']; grind

/-- Rational Peter–Paul inequality derived from positive semidefiniteness. -/
theorem form_peterPaul (m : Nat) (H : Mat) (u v : Vec) (η : Rat) (hη : 0 < η)
    (hs : ∀ x y, form m H x y = form m H y x)
    (hp : ∀ x, 0 ≤ form m H x x) :
    form m H (fun c => u c + v c) (fun c => u c + v c) ≤
      (1 + 1 / η) * form m H u u + (1 + η) * form m H v v := by
  have he : (1 / η) * η = (1 : Rat) := Rat.div_mul_cancel (by grind)
  have hi : 0 ≤ (1 / η : Rat) := by
    by_cases hn : (0 : Rat) ≤ 1 / η
    · grind
    · have := Rat.mul_le_mul_of_nonneg_right (by grind : (1 / η : Rat) ≤ 0) (Rat.le_of_lt hη)
      grind
  have h := hp (fun c => 1 * u c + (-η) * v c)
  rw [form_lin_left, form_lin_right, form_lin_right, hs v u] at h
  have hh := Rat.mul_nonneg hi h
  have e : (fun c => u c + v c) = (fun c => 1 * u c + 1 * v c) := by funext c; grind
  rw [e, form_lin_left, form_lin_right, form_lin_right, hs v u]
  have hid : (1 + 1 / η) * form m H u u + (1 + η) * form m H v v -
      (1 * (1 * form m H u u + 1 * form m H u v) +
        1 * (1 * form m H u v + 1 * form m H v v)) =
      (1 / η) * (1 * (1 * form m H u u + -η * form m H u v) +
        -η * (1 * form m H u v + -η * form m H v v)) := by grind
  rw [← hid] at hh
  grind

theorem discreteHEnergy_add_peterPaul (m n : Nat) (H : Mat) (u v : Grid)
    (η : Rat) (hη : 0 < η)
    (hs : ∀ x y, form m H x y = form m H y x)
    (hp : ∀ x, 0 ≤ form m H x x) :
    discreteHEnergy m n H (gridAdd u v) ≤
      (1 + 1 / η) * discreteHEnergy m n H u + (1 + η) * discreteHEnergy m n H v := by
  unfold discreteHEnergy
  rw [← sumTo_mul_left, ← sumTo_mul_left, ← sumTo_add]
  exact sumTo_le fun i _ => form_peterPaul m H (u i) (v i) η hη hs hp

/-- A posteriori bound, with independently measured defects at each step. -/
def defectTube (η initial : Rat) (defects : Nat → Rat) : Nat → Rat
  | 0 => initial
  | k + 1 => (1 + 1 / η) * defectTube η initial defects k + (1 + η) * defects k

def aprioriErrorTubeRec (η initial ε : Rat) (k : Nat) : Rat :=
  defectTube η initial (fun _ => ε) k

/-- Exact trajectory, indexed by time so the recurrence is available directly. -/
def exactTrajectory (step : Grid → Grid) (u : Grid) : Nat → Grid
  | 0 => u
  | k + 1 => step (exactTrajectory step u k)

def stepDefect (step : Grid → Grid) (fast : Nat → Grid) (k : Nat) : Grid :=
  gridSub (fast (k + 1)) (step (fast k))

theorem defect_decomposition (m n : Nat) (A : Mat) (a ν : Rat)
    (fast : Nat → Grid) (initial : Grid) (k : Nat) :
    gridSub (fast (k + 1)) (exactTrajectory (rusanovStep m A a ν n) initial (k + 1)) =
    gridAdd (rusanovStep m A a ν n
      (gridSub (fast k) (exactTrajectory (rusanovStep m A a ν n) initial k)))
      (stepDefect (rusanovStep m A a ν n) fast k) := by
  rw [← rusanovLinear_sub]
  funext i c
  simp only [gridSub, gridAdd, stepDefect, exactTrajectory]
  grind

/-- Arbitrary accelerator errors, propagated through the actual rational stencil. -/
theorem accelerated_rusanov_apriori_error_tube (m n : Nat) (A H : Mat) (a ν η ε : Rat)
    (hη : 0 < η) (initial : Grid) (fast : Nat → Grid)
    (hs : ∀ x y, form m H x y = form m H y x)
    (hp : ∀ x, 0 ≤ form m H x x)
    (hc : ∀ u, discreteHEnergy m n H (rusanovStep m A a ν n u) ≤ discreteHEnergy m n H u)
    (he : ∀ k, discreteHEnergy m n H (stepDefect (rusanovStep m A a ν n) fast k) ≤ ε)
    (K : Nat) :
    discreteHEnergy m n H (gridSub (fast K) (exactTrajectory (rusanovStep m A a ν n) initial K)) ≤
      aprioriErrorTubeRec η (discreteHEnergy m n H (gridSub (fast 0) initial)) ε K := by
  have hi : 0 ≤ (1 + 1 / η : Rat) := by
    have hh : (1 / η) * η = (1 : Rat) := Rat.div_mul_cancel (by grind)
    by_cases hn : (0 : Rat) ≤ 1 / η
    · grind
    · have := Rat.mul_le_mul_of_nonneg_right (by grind : (1 / η : Rat) ≤ 0) (Rat.le_of_lt hη)
      grind
  induction K with
  | zero => exact Rat.le_refl
  | succ k ih =>
    rw [defect_decomposition]
    have hpp := discreteHEnergy_add_peterPaul m n H
      (rusanovStep m A a ν n (gridSub (fast k) (exactTrajectory (rusanovStep m A a ν n) initial k)))
      (stepDefect (rusanovStep m A a ν n) fast k) η hη hs hp
    have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans (hc _) ih) hi
    have h2 := Rat.mul_le_mul_of_nonneg_left (he k) (by grind : (0 : Rat) ≤ 1 + η)
    change _ ≤ (1 + 1 / η) * aprioriErrorTubeRec η _ ε k + (1 + η) * ε
    exact Rat.le_trans hpp (by grind)

/-- Measured defects give a tighter tube than a uniform rounding budget. -/
theorem untrusted_surrogate_aposteriori_error_tube (m n : Nat) (A H : Mat) (a ν η : Rat)
    (hη : 0 < η) (initial : Grid) (fast : Nat → Grid)
    (hs : ∀ x y, form m H x y = form m H y x)
    (hp : ∀ x, 0 ≤ form m H x x)
    (hc : ∀ u, discreteHEnergy m n H (rusanovStep m A a ν n u) ≤ discreteHEnergy m n H u)
    (K : Nat) :
    discreteHEnergy m n H (gridSub (fast K) (exactTrajectory (rusanovStep m A a ν n) initial K)) ≤
      defectTube η (discreteHEnergy m n H (gridSub (fast 0) initial))
        (fun k => discreteHEnergy m n H (stepDefect (rusanovStep m A a ν n) fast k)) K := by
  have hi : 0 ≤ (1 + 1 / η : Rat) := by
    have hh : (1 / η) * η = (1 : Rat) := Rat.div_mul_cancel (by grind)
    by_cases hn : (0 : Rat) ≤ 1 / η
    · grind
    · have := Rat.mul_le_mul_of_nonneg_right (by grind : (1 / η : Rat) ≤ 0) (Rat.le_of_lt hη)
      grind
  induction K with
  | zero => exact Rat.le_refl
  | succ k ih =>
    rw [defect_decomposition]
    have hpp := discreteHEnergy_add_peterPaul m n H
      (rusanovStep m A a ν n (gridSub (fast k) (exactTrajectory (rusanovStep m A a ν n) initial k)))
      (stepDefect (rusanovStep m A a ν n) fast k) η hη hs hp
    have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans (hc _) ih) hi
    simp only [defectTube]
    exact Rat.le_trans hpp (by grind)


/-- Atoms may contain delimiters, quotes and whitespace; the lexer preserves them. -/
inductive PdeSexpr where
  | atom (value : String)
  | list (children : List PdeSexpr)
  deriving BEq, Repr

set_option genSizeOf false in
inductive SexprToken where
  | atom (value : String)
  | openParen
  | closeParen
  deriving DecidableEq, Repr

set_option genSizeOf false in
inductive LexMode where
  | between | bare | quoted | escaped | afterQuote
  deriving DecidableEq

/-- One input character is consumed in every recursive call. Escape state is
separate from delimiter state, including immediately after a quoted atom. -/
def lexChars : List Char → LexMode → List Char → List SexprToken → Option (List SexprToken)
  | [], .between, _, out => some out.reverse
  | [], .afterQuote, _, out => some out.reverse
  | [], .bare, acc, out => some (SexprToken.atom (String.ofList acc.reverse) :: out).reverse
  | [], _, _, _ => none
  | c :: cs, .escaped, acc, out => lexChars cs .quoted (c :: acc) out
  | c :: cs, .quoted, acc, out =>
      if c == '\\' then lexChars cs .escaped acc out
      else if c == '"' then lexChars cs .afterQuote [] (.atom (String.ofList acc.reverse) :: out)
      else lexChars cs .quoted (c :: acc) out
  | c :: cs, .afterQuote, _, out =>
      if c.isWhitespace then lexChars cs .between [] out
      else if c == '(' then lexChars cs .between [] (.openParen :: out)
      else if c == ')' then lexChars cs .between [] (.closeParen :: out)
      else none
  | c :: cs, .between, _, out =>
      if c.isWhitespace then lexChars cs .between [] out
      else if c == '(' then lexChars cs .between [] (.openParen :: out)
      else if c == ')' then lexChars cs .between [] (.closeParen :: out)
      else if c == '"' then lexChars cs .quoted [] out
      else if c == '\\' then none
      else lexChars cs .bare [c] out
  | c :: cs, .bare, acc, out =>
      let flushed := SexprToken.atom (String.ofList acc.reverse) :: out
      if c.isWhitespace then lexChars cs .between [] flushed
      else if c == '(' then lexChars cs .between [] (.openParen :: flushed)
      else if c == ')' then lexChars cs .between [] (.closeParen :: flushed)
      else if c == '"' || c == '\\' then none
      else lexChars cs .bare (c :: acc) out

def parseTokens : List SexprToken → List (List PdeSexpr) → List PdeSexpr → Option (List PdeSexpr)
  | [], [], current => some current.reverse
  | [], _ :: _, _ => none
  | .atom s :: ts, stack, current => parseTokens ts stack (.atom s :: current)
  | .openParen :: ts, stack, current => parseTokens ts (current :: stack) []
  | .closeParen :: ts, parent :: stack, current => parseTokens ts stack (.list current.reverse :: parent)
  | .closeParen :: _, [], _ => none

mutual
  def renderSexpr : PdeSexpr → List SexprToken
    | .atom s => [.atom s]
    | .list xs => .openParen :: renderSexprs xs ++ [.closeParen]
  termination_by structural x => x
  def renderSexprs : List PdeSexpr → List SexprToken
    | [] => []
    | x :: xs => renderSexpr x ++ renderSexprs xs
  termination_by structural xs => xs
end

mutual
  theorem parse_render_cont (x : PdeSexpr) (tail : List SexprToken)
      (stack : List (List PdeSexpr)) (cur : List PdeSexpr) :
      parseTokens (renderSexpr x ++ tail) stack cur = parseTokens tail stack (x :: cur) := by
    cases x with
    | atom s => rfl
    | list xs =>
      simp only [renderSexpr, List.cons_append, List.append_assoc, parseTokens]
      rw [parse_renders_cont]
      simp [parseTokens]
  termination_by structural x
  theorem parse_renders_cont (xs : List PdeSexpr) (tail : List SexprToken)
      (stack : List (List PdeSexpr)) (cur : List PdeSexpr) :
      parseTokens (renderSexprs xs ++ tail) stack cur =
        parseTokens tail stack (xs.reverse ++ cur) := by
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [renderSexprs, List.append_assoc]
      rw [parse_render_cont, parse_renders_cont]
      simp
  termination_by structural xs
end

/-- Roundtrip on canonical token streams, including arbitrary quoted atoms. -/
theorem parseSexpr_renderSexpr_roundtrip (x : PdeSexpr) :
    parseTokens (renderSexpr x) [] [] = some [x] := by
  have h := parse_render_cont x [] [] []
  simpa [parseTokens] using h

def parseSexpr (text : String) : Option PdeSexpr := do
  let ts ← lexChars text.toList .between [] []
  match ← parseTokens ts [] [] with
  | [x] => some x
  | _ => none

def escapeAtom : List Char → List Char
  | [] => []
  | c :: cs => if c == '"' || c == '\\' then '\\' :: c :: escapeAtom cs else c :: escapeAtom cs

def tokenChars : SexprToken → List Char
  | .openParen => ['(', ' ']
  | .closeParen => [')', ' ']
  | .atom s => '"' :: escapeAtom s.toList ++ ['"', ' ']

def renderPdeSpecSexpr (x : PdeSexpr) : String :=
  String.ofList ((renderSexpr x).flatMap tokenChars)

theorem lex_escaped_cont (chars tail acc : List Char) (out : List SexprToken) :
    lexChars (escapeAtom chars ++ ['"', ' '] ++ tail) .quoted acc out =
      lexChars tail .between [] (.atom (String.ofList (acc.reverse ++ chars)) :: out) := by
  induction chars generalizing acc with
  | nil => simp [escapeAtom, lexChars]
  | cons c cs ih =>
    by_cases hq : c = '"'
    · subst c; simpa [escapeAtom, lexChars, List.reverse_cons, List.append_assoc] using ih ('"' :: acc)
    · by_cases hb : c = '\\'
      · subst c; simpa [escapeAtom, lexChars, List.reverse_cons, List.append_assoc] using ih ('\\' :: acc)
      · simpa [escapeAtom, lexChars, hq, hb, List.reverse_cons, List.append_assoc] using ih (c :: acc)

theorem lex_tokens_cont (ts : List SexprToken) (tail : List Char) (out : List SexprToken) :
    lexChars (ts.flatMap tokenChars ++ tail) .between [] out =
      lexChars tail .between [] (ts.reverse ++ out) := by
  induction ts generalizing out with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | openParen => simpa [tokenChars, lexChars, List.reverse_cons, List.append_assoc] using ih (.openParen :: out)
    | closeParen => simpa [tokenChars, lexChars, List.reverse_cons, List.append_assoc] using ih (.closeParen :: out)
    | atom s =>
      have he := lex_escaped_cont s.toList (ts.flatMap tokenChars ++ tail) [] out
      have he' : lexChars (escapeAtom s.toList ++ ['"', ' '] ++ (ts.flatMap tokenChars ++ tail))
          .quoted [] out = lexChars tail .between [] ((SexprToken.atom s :: ts).reverse ++ out) := by
        rw [he]
        simpa [List.reverse_cons, List.append_assoc] using ih (.atom s :: out)
      simpa [List.flatMap_cons, tokenChars, List.append_assoc, lexChars] using he'

/-- String-level roundtrip includes delimiter and escape handling. -/
theorem parseSexpr_renderPdeSpecSexpr_roundtrip (x : PdeSexpr) :
    parseSexpr (renderPdeSpecSexpr x) = some x := by
  have h := lex_tokens_cont (renderSexpr x) [] []
  simp only [List.append_nil, lexChars, List.reverse_reverse] at h
  simp [parseSexpr, renderPdeSpecSexpr, h, parseSexpr_renderSexpr_roundtrip]

/-- Linear flux coefficients are symbolic parameter names or exact rational atoms. -/
structure PdeSymbolicSpec where
  name : String
  vars : List String
  params : List (String × Rat)
  fluxMatrix : List (List Rat)
  certificate : HyperbolicCert
  wavespeed : Rat
  courant : Rat

def atomText : PdeSexpr → Option String
  | .atom s => some s
  | _ => none

def rationalAtom (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [_] => (s.toInt?).map fun z => (z : Rat)
  | [a, b] => do
      let x ← a.toInt?
      let y ← b.toNat?
      if y = 0 then none else some ((x : Rat) / (y : Rat))
  | _ => none

def coefficient (params : List (String × Rat)) (x : PdeSexpr) : Option Rat := do
  let s ← atomText x
  match params.lookup s with
  | some r => some r
  | none => rationalAtom s

def parseRow (params : List (String × Rat)) : PdeSexpr → Option (List Rat)
  | .list xs => xs.mapM (coefficient params)
  | _ => none

def parseMatrix (params : List (String × Rat)) : PdeSexpr → Option (List (List Rat))
  | .list xs => xs.mapM (parseRow params)
  | _ => none

def parseParam : PdeSexpr → Option (String × Rat)
  | .list [.atom s, .atom v] => (rationalAtom v).map fun r => (s, r)
  | _ => none

def parsePdeSpecTree : PdeSexpr → Option PdeSymbolicSpec
  | .list [.atom "pde-spec", .list [.atom "name", .atom name],
      .list (.atom "vars" :: vs), .list (.atom "params" :: ps),
      .list [.atom "flux", flux], .list [.atom "symmetrizer", sym],
      .list [.atom "eigensystem", r, ri, lam, weights],
      .list [.atom "wavespeed", speed, courant]] => do
    let vars ← vs.mapM atomText
    let params ← ps.mapM parseParam
    if (vars.eraseDups.length != vars.length) || vars.isEmpty ||
        ((params.map Prod.fst).eraseDups.length != params.length) then none else do
      let jac ← parseMatrix params flux
      let eigVecs ← parseMatrix params r
      let eigInv ← parseMatrix params ri
      let eigVals ← parseRow params lam
      let weights ← parseRow params weights
      let sym ← parseMatrix params sym
      let a ← coefficient params speed
      let ν ← coefficient params courant
      let n := vars.length
      if [jac, eigVecs, eigInv, sym].all (fun m => m.length == n && m.all (fun row => row.length == n)) &&
          eigVals.length == n && weights.length == n then
        some ⟨name, vars, params, jac, ⟨jac, eigVecs, eigVals, eigInv, weights, sym⟩, a, ν⟩
      else none
  | _ => none

def parsePdeSpecSexpr (s : String) : Option PdeSymbolicSpec :=
  (parseSexpr s).bind parsePdeSpecTree

def linearFlux (vars : List String) (row : List Rat) : RealExpr :=
  (vars.zip row).foldr (fun p tail => .add (.mul (.const p.2) (.var p.1)) tail) (.const 0)

def PdeSymbolicSpec.system (s : PdeSymbolicSpec) : HyperbolicSystem where
  vars := s.vars
  flux := s.fluxMatrix.map (linearFlux s.vars)
  state := List.replicate s.vars.length 0
  left := List.replicate s.vars.length 0
  right := List.replicate s.vars.length 1
  aMax := s.wavespeed
  cfl := s.courant

/-- Invalid eigendata, symmetrizers and CFL parameters are rejected at compilation. -/
def compilePdeSpec (s : PdeSymbolicSpec) : Option (HyperbolicSystem × HyperbolicCert) :=
  if check s.system s.certificate = .ok then some (s.system, s.certificate) else none

theorem compilePdeSpec_sound (s : PdeSymbolicSpec) (o : HyperbolicSystem) (c : HyperbolicCert)
    (h : compilePdeSpec s = some (o, c)) : Certified o c := by
  unfold compilePdeSpec at h
  split at h
  · rename_i hc
    cases h
    exact check_sound hc
  · cases h

def compilePdeText (text : String) : Option (HyperbolicSystem × HyperbolicCert) :=
  (parsePdeSpecSexpr text).bind compilePdeSpec

theorem parsed_compilation_energy (text : String) (o : HyperbolicSystem) (c : HyperbolicCert)
    (hc : compilePdeText text = some (o, c)) (n K : Nat) (u : Grid) :
    symEnergy o c n (rusanovRun o.dim o.jacobian o.aMax o.cfl n K u) ≤ symEnergy o c n u := by
  unfold compilePdeText at hc
  cases hp : parsePdeSpecSexpr text with
  | none => simp [hp] at hc
  | some s =>
    simp only [hp, Option.bind_some] at hc
    exact (compilePdeSpec_sound s o c hc).energy n K u

def maxwell1DSpecSexpr : String :=
  "(pde-spec (name Maxwell1D) (vars Ey Bz) (params (c 3/2) (c2 9/4)) (flux ((0 c2) (1 0))) (symmetrizer ((1 0) (0 c2))) (eigensystem ((3/2 -3/2) (1 1)) ((1/3 1/2) (-1/3 1/2)) (3/2 -3/2) (9/2 9/2)) (wavespeed c 2/3))"

def munzPhmSpecSexpr : String :=
  "(pde-spec (name MunzPHM) (vars Ex Bx phi psi) (params (c 2) (chi 3/2)) (flux ((0 0 6 0) (0 0 0 5/4) (3/2 0 0 0) (0 5 0 0))) (symmetrizer ((1 0 0 0) (0 4 0 0) (0 0 4 0) (0 0 0 1))) (eigensystem ((2 -2 0 0) (0 0 1 -1) (1 1 0 0) (0 0 2 2)) ((1/4 0 1/2 0) (-1/4 0 1/2 0) (0 1/2 0 1/4) (0 -1/2 0 1/4)) (3 -3 5/2 -5/2) (8 8 8 8)) (wavespeed 3 1/3))"

def linearAdvectionSpecSexpr : String :=
  "(pde-spec (name LinearAdvection) (vars u) (params (a 1)) (flux ((a))) (symmetrizer ((1))) (eigensystem ((1)) ((1)) (1) (1)) (wavespeed a 1/2))"


def ratAbs (x : Rat) : Rat := if x < 0 then -x else x

theorem ratAbs_nonneg (x : Rat) : 0 ≤ ratAbs x := by unfold ratAbs; split <;> grind

theorem ratAbs_ge (x : Rat) : x ≤ ratAbs x := by unfold ratAbs; split <;> grind

theorem ratAbs_mul (x y : Rat) : ratAbs (x * y) = ratAbs x * ratAbs y := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · have h := Rat.mul_nonneg (show 0 ≤ -x by grind) (show 0 ≤ -y by grind)
    simp only [ratAbs, hx, hy, ↓reduceIte]; split <;> grind
  · have h := Rat.mul_nonneg (show 0 ≤ -x by grind) (show 0 ≤ y by grind)
    simp only [ratAbs, hx, hy, ↓reduceIte]; split <;> grind
  · have h := Rat.mul_nonneg (show 0 ≤ x by grind) (show 0 ≤ -y by grind)
    simp only [ratAbs, hx, hy, ↓reduceIte]; split <;> grind
  · have h := Rat.mul_nonneg (show 0 ≤ x by grind) (show 0 ≤ y by grind)
    simp only [ratAbs, hx, hy, ↓reduceIte]; split <;> grind

theorem sumTo_const (n : Nat) (a : Rat) : sumTo n (fun _ => a) = (n : Rat) * a := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; grind

/-- An entrywise perturbation budget and the absolute matrix mass bound the
quadratic energy without a spectral norm or square roots. -/
theorem discreteHEnergy_le_of_linf_bound (m n : Nat) (H : Mat) (e : Grid) (ε M : Rat)
    (hε : 0 ≤ ε) (he : ∀ i c, i < n → c < m → ratAbs (e i c) ≤ ε)
    (hM : sumTo m (fun r => sumTo m (fun c => ratAbs (H r c))) ≤ M) :
    discreteHEnergy m n H e ≤ (n : Rat) * M * (ε * ε) := by
  have cell : ∀ i, i < n → dot m (e i) (mulVec m H (e i)) ≤ M * (ε * ε) := by
    intro i hi
    have bound : ∀ r c, r < m → c < m →
        e i r * (H r c * e i c) ≤ (ε * ε) * ratAbs (H r c) := by
      intro r c hr hc
      have h1 := Rat.mul_le_mul_of_nonneg_left (he i c hi hc) (ratAbs_nonneg (H r c))
      have h2 := Rat.mul_le_mul_of_nonneg_left h1 (ratAbs_nonneg (e i r))
      have h3 := Rat.mul_le_mul_of_nonneg_right (he i r hi hr)
        (Rat.mul_nonneg (ratAbs_nonneg (H r c)) hε)
      have hh := ratAbs_ge (e i r * (H r c * e i c))
      rw [ratAbs_mul, ratAbs_mul] at hh
      exact Rat.le_trans hh (Rat.le_trans h2 (by grind))
    unfold dot mulVec
    have eq1 : sumTo m (fun r => e i r * sumTo m (fun c => H r c * e i c)) =
        sumTo m (fun r => sumTo m (fun c => e i r * (H r c * e i c))) :=
      sumTo_congr fun r _ => (sumTo_mul_left m (e i r) _).symm
    rw [eq1]
    have h := sumTo_le fun r hr => sumTo_le fun c hc => bound r c hr hc
    have eq2 : sumTo m (fun r => sumTo m (fun c => (ε * ε) * ratAbs (H r c))) =
        (ε * ε) * sumTo m (fun r => sumTo m (fun c => ratAbs (H r c))) := by
      simp only [sumTo_mul_left]
    rw [eq2] at h
    have hh := Rat.mul_le_mul_of_nonneg_left hM (Rat.mul_nonneg hε hε)
    exact Rat.le_trans h (by grind)
  have h := sumTo_le cell
  rw [sumTo_const] at h
  exact Rat.le_trans h (rat_le_of_eq (by grind))

/-- Certified positive definiteness includes zero vectors constructively. -/
theorem certified_psd (o : HyperbolicSystem) (c : HyperbolicCert) (h : Certified o c) (v : Vec) :
    0 ≤ form o.dim (matOf c.sym) v v := by
  rcases zero_or_ne v o.dim with hz | ⟨i, hi, hn⟩
  · have e : form o.dim (matOf c.sym) v v = 0 := by
      unfold form dot
      have hh := sumTo_congr (n := o.dim) (f := fun i => v i * mulVec o.dim (matOf c.sym) v i)
        (g := fun _ => 0) (fun i hi => by rw [hz i hi]; grind)
      rw [hh, sumTo_zero]
    rw [e]; exact Rat.le_refl
  · exact Rat.le_of_lt (h.spd v i hi hn)

theorem certified_step_contracts (o : HyperbolicSystem) (c : HyperbolicCert)
    (h : Certified o c) (n : Nat) (u : Grid) :
    discreteHEnergy o.dim n (matOf c.sym) (rusanovStep o.dim o.jacobian o.aMax o.cfl n u) ≤
      discreteHEnergy o.dim n (matOf c.sym) u :=
  h.energy n 1 u

/-- The a posteriori theorem connected to the actual hyperbolic checker. -/
theorem accepted_surrogate_tube (o : HyperbolicSystem) (c : HyperbolicCert)
    (h : check o c = .ok) (n K : Nat) (η tol : Rat) (hη : 0 < η)
    (initial : Grid) (fast : Nat → Grid)
    (ht : defectTube η (discreteHEnergy o.dim n (matOf c.sym) (gridSub (fast 0) initial))
      (fun k => discreteHEnergy o.dim n (matOf c.sym)
        (stepDefect (rusanovStep o.dim o.jacobian o.aMax o.cfl n) fast k)) K ≤ tol) :
    discreteHEnergy o.dim n (matOf c.sym)
      (gridSub (fast K) (exactTrajectory (rusanovStep o.dim o.jacobian o.aMax o.cfl n) initial K)) ≤ tol := by
  have cert := check_sound h
  exact Rat.le_trans (untrusted_surrogate_aposteriori_error_tube o.dim n o.jacobian (matOf c.sym)
    o.aMax o.cfl η hη initial fast cert.symm (certified_psd o c cert)
    (certified_step_contracts o c cert n) K) ht


/-- Semantic geometry also records that the supplied positive weights describe H. -/
structure CertificateGeometry (o : HyperbolicSystem) (c : HyperbolicCert) : Prop where
  certified : Certified o c
  weights : ∀ k, k < o.dim → 0 < vecOf c.weights k
  gram : ∀ i j, i < o.dim → j < o.dim →
    matOf c.sym i j = gram o.dim (vecOf c.weights) (matOf c.eigInv) i j

theorem geometry_of_check (o : HyperbolicSystem) (c : HyperbolicCert) (h : check o c = .ok) :
    CertificateGeometry o c :=
  ⟨check_sound h, (check_ok h).2.2.2.2.2.2.1, (check_ok h).2.2.2.2.2.2.2⟩

theorem check_of_geometry (o : HyperbolicSystem) (c : HyperbolicCert) (g : CertificateGeometry o c) :
    check o c = .ok := by
  have hc := g.certified
  have h1 : decide o.WellFormed = true := decide_eq_true hc.wf
  have h2 : cflB o = true := decide_eq_true hc.cfl
  have h3 : firstBad o.dim (conservB o) = none :=
    (firstBad_none _ _).mpr (fun i hi => decide_eq_true (hc.roe i hi))
  have h4 : firstBad2 o.dim (jacB o c) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.jac i j hi hj))
  have h5 : firstBad2 o.dim (eigB o c) = none :=
    (firstBad2_none _ _).mpr (fun i k hi hk => decide_eq_true (hc.eigen.eig i k hi hk))
  have h6 : firstBad2 o.dim (leftB o c) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.eigen.left i j hi hj))
  have h7 : firstBad2 o.dim (rightB o c) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (hc.eigen.right i j hi hj))
  have h8 : firstBad o.dim (speedB o c) = none :=
    (firstBad_none _ _).mpr (fun k hk => by
      obtain ⟨i, hi, hne⟩ := hc.eigen.eigenvector_ne k hk
      exact decide_eq_true (hc.eigenvalue_le (fun i => matOf c.eigVecs i k) (vecOf c.eigVals k)
        (fun i hi => hc.eigen.eigenvector k i hk hi) i hi hne))
  have h9 : firstBad o.dim (weightB c) = none :=
    (firstBad_none _ _).mpr (fun k hk => decide_eq_true (g.weights k hk))
  have h10 : firstBad2 o.dim (symB o c) = none :=
    (firstBad2_none _ _).mpr (fun i j hi hj => decide_eq_true (g.gram i j hi hj))
  unfold check
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; rfl

structure ApproxQuery where
  system : HyperbolicSystem
  certificate : HyperbolicCert
  cells : Nat
  steps : Nat
  eta : Rat
  tolerance : Rat
  initial : List (List Rat)
  trajectory : List (List (List Rat))

def listGrid (xs : List (List Rat)) : Grid := fun i => vecOf (getOr xs i [])
def ApproxQuery.fast (q : ApproxQuery) (k : Nat) : Grid := listGrid (getOr q.trajectory k [])

def ApproxQuery.shape (q : ApproxQuery) : Bool :=
  0 < q.cells && q.initial.length == q.cells &&
  q.initial.all (fun row => row.length == q.system.dim) &&
  q.trajectory.length == q.steps + 1 &&
  q.trajectory.all (fun g => g.length == q.cells && g.all (fun row => row.length == q.system.dim))

def ApproxQuery.tube (q : ApproxQuery) : Rat :=
  defectTube q.eta
    (discreteHEnergy q.system.dim q.cells (matOf q.certificate.sym)
      (gridSub (q.fast 0) (listGrid q.initial)))
    (fun k => discreteHEnergy q.system.dim q.cells (matOf q.certificate.sym)
      (stepDefect (rusanovStep q.system.dim q.system.jacobian q.system.aMax q.system.cfl q.cells) q.fast k)) q.steps

def ApproxQuery.actualError (q : ApproxQuery) : Rat :=
  discreteHEnergy q.system.dim q.cells (matOf q.certificate.sym)
    (gridSub (q.fast q.steps)
      (exactTrajectory (rusanovStep q.system.dim q.system.jacobian q.system.aMax q.system.cfl q.cells)
        (listGrid q.initial) q.steps))

/-- This is a claim about the declared conservative tube as well as the actual
trajectory. Rejection of a tube alone does not refute a smaller true error. -/
structure CertifiedApproximation (q : ApproxQuery) : Prop where
  geometry : CertificateGeometry q.system q.certificate
  shape : q.shape = true
  etaPositive : 0 < q.eta
  tubeWithin : q.tube ≤ q.tolerance
  trueErrorWithin : q.actualError ≤ q.tolerance

set_option genSizeOf false in
inductive ApproxClause where
  | geometry | shape | eta | tube
  deriving DecidableEq, Repr

def checkApprox (q : ApproxQuery) : Judge.Verdict ApproxClause :=
  if check q.system q.certificate != .ok then .refused .geometry []
  else if !q.shape then .refused .shape []
  else if q.eta ≤ 0 then .refused .eta []
  else if q.tube > q.tolerance then .refused .tube []
  else .ok

theorem checkApprox_sound (q : ApproxQuery) (h : checkApprox q = .ok) : CertifiedApproximation q := by
  unfold checkApprox at h
  split at h
  · cases h
  · rename_i hg
    have hg' : check q.system q.certificate = .ok := by simpa using hg
    split at h
    · cases h
    · rename_i hs
      have hs' : q.shape = true := by simpa using hs
      split at h
      · cases h
      · rename_i he
        have he' : 0 < q.eta := by grind
        split at h
        · cases h
        · rename_i ht
          have ht' : q.tube ≤ q.tolerance := by grind
          exact ⟨geometry_of_check _ _ hg', hs', he', ht',
            accepted_surrogate_tube _ _ hg' q.cells q.steps q.eta q.tolerance he'
              (listGrid q.initial) q.fast ht'⟩

theorem checkApprox_complete (q : ApproxQuery) (h : CertifiedApproximation q) : checkApprox q = .ok := by
  have hg := check_of_geometry _ _ h.geometry
  simp [checkApprox, hg, h.shape, show ¬q.eta ≤ 0 by have := h.etaPositive; grind,
    show ¬q.tube > q.tolerance by have := h.tubeWithin; grind]

theorem checkApprox_refuted (q : ApproxQuery) (k : ApproxClause) (path : List Nat)
    (h : checkApprox q = .refused k path) : ¬CertifiedApproximation q := by
  intro hc
  rw [checkApprox_complete q hc] at h
  cases h

def approxFormatName : String := "pde-approx-defect@1"

instance pdeApproxDefectJudge : Judge ApproxQuery Unit where
  Clause := ApproxClause
  Meaning := fun q _ => CertifiedApproximation q
  check := fun _ q _ => checkApprox q
  sound := fun h => checkApprox_sound _ h
  refutes := fun _ => true
  refuted := fun h _ _ => checkApprox_refuted _ _ _ h
  Fragment := fun q => q.shape = true
  complete := fun _ ⟨_, hc⟩ => ⟨(), 0, checkApprox_complete _ hc⟩
  mono := fun _ _ => rfl

example : ∃ s o c, compilePdeSpec s = some (o, c) := by
  let s : PdeSymbolicSpec := ⟨"LinearAdvection", ["u"], [], [[1]],
    ⟨[[1]], [[1]], [1], [[1]], [1], [[1]]⟩, 1, 1/2⟩
  have hc : check s.system s.certificate = .ok := by decide +kernel
  exact ⟨s, s.system, s.certificate, by simp [compilePdeSpec, hc]⟩


/-- Explicit geometric weights for the uniform per-step error budget. -/
theorem aprioriErrorTubeRec_closed (η initial ε : Rat) (K : Nat) :
    aprioriErrorTubeRec η initial ε K =
      (1 + 1 / η)^K * initial + (1 + η) * sumTo K (fun j => (1 + 1 / η)^j * ε) := by
  have shift : ∀ k, sumTo (k + 1) (fun j => (1 + 1 / η)^j * ε) =
      ε + (1 + 1 / η) * sumTo k (fun j => (1 + 1 / η)^j * ε) := by
    intro k
    rw [sumTo_succ_front]
    have h : sumTo k (fun j => (1 + 1 / η)^(j + 1) * ε) =
        (1 + 1 / η) * sumTo k (fun j => (1 + 1 / η)^j * ε) := by
      rw [← sumTo_mul_left]
      exact sumTo_congr fun j _ => by rw [Rat.pow_succ]; grind
    rw [h]; simp
  induction K with
  | zero => simp [aprioriErrorTubeRec, defectTube, sumTo]; grind
  | succ k ih =>
    change (1 + 1 / η) * aprioriErrorTubeRec η initial ε k + (1 + η) * ε = _
    rw [ih, shift, Rat.pow_succ]; grind

end Obend.Analysis.PdeSexprAndApprox
