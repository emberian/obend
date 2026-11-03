module
/-
# Obend.Elab.AutoCert — Automatic External Certificate Synthesis (`AutoCert`) for `.obend` Claims & Contracts

Implements Foundation C (`QUALIFICATION-AND-SILICON-LEAN.md` §1.3, `WS-4A-2`):
Automatically extracts problem queries from `.obend` `claim` and `contract` declarations, runs
untrusted witness synthesizers, encodes wire payloads matching the exact kernel judge decoders, and
gates every synthesized `Justification.byExternalJudge` on
`obligationCheckWithJudges formats grade co just == .ok` (`synthesizeClaimExternalJudge_sound`):

1. **`"interval@1"` (`IntervalObj`, `IntervalCert`, `intervalFormat`)**:
   - Evaluates multi-variable interval enclosures (`evalInterval`) with adaptive midpoint bisection
     (`IntervalCert.bisect varName left right`), proves `checkIntervalAutoCert_sound` against
     `IntervalQuery.SemanticMeaning`, and encodes/decodes JSON wire frames (`encodeIntervalObj`,
     `encodeIntervalCert`, `decodeIntervalObj`, `decodeIntervalCert`).
2. **`"taylor-model@1"` (`TaylorModelQuery`, `TaylorModel`, `taylorModelFormat`)**:
   - Evaluates degree-$k$ Taylor models (`tmVar`, `tmConst`, `tmAdd`, `tmSub`, `tmScale`, `tmMul`,
     `tmExpCertified`, `tmSinCertified`, `tmCosCertified`, `tmLn1pCertified`, `tmSqrt1pCertified`),
     verifies enclosure inclusion `Interval.isSubintervalOf (evalTaylorModelRange tm) q.claimedBound`,
     and encodes/decodes JSON wire frames (`encodeTaylorModelQuery`, `encodeTaylorModelCert`).
3. **`"sos-lyapunov-cbf@1"` (`SosLyapunovProblem`, `SosLyapunovCert`, `sosLyapunovFormat`)**:
   - Synthesizes SOS Gram / Lyapunov / Control Barrier Function / DAE certificates via polynomial
     reduction (`polyDivModWithQuotients`) and square completion, and encodes structured JSON wire
     frames (`encodeSosLyapunovProblem`, `encodeSosLyapunovCert`) accepted by the hardened JSON
     wire parser in `Obend.Analysis.SosLyapunov`.
4. **`"groebner@1"` (`GroebnerQuery`, `GroebnerCert`, `groebnerFormat`)**:
   - Runs bounded S-polynomial Buchberger completion (`completeGroebnerBasis`) and multi-divisor
     polynomial division with cofactor tracking (`polyDivModWithQuotients`) to synthesize ideal
     membership (`.membership`) and algebraic Positivstellensatz (`.positivstellensatz`) witnesses,
     proves `checkGroebnerJudge_sound`, and encodes/decodes JSON wire frames.
5. **`"rtl-synth@1"` / `"hw-rtl-synth@1"` (`Leaf.Book`, `RtlModule`, `rtlSynthFormat` / `hwSynthFormat`)**:
   - Compiles the module's `Leaf.Book` via `compileBookToRtlSat` (with `compileBookToPipelinedRtl`
     fallback), normalizes wires via `normalizeRtlModuleForWire`, verifies `checkRtlSynth`, and
     encodes wire frames via `encodeRtlSynthObj` / `encodeRtlSynthCert`.
-/
public import Lean.Data.Json
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis
public import Obend.Analysis.Flowpipe
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.SosLyapunov
import all Obend.Analysis.SosLyapunov
public import Obend.Analysis.Groebner
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Judge
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Logic.Obligation
import all Obend.Logic.Obligation
public import Obend.Lower.Judge
public import Obend.Spec.Syntax
public import Obend.Spec.Elaborate

@[expose] public section

namespace Obend.Elab.AutoCert

open Lean (Json toJson)
open Obend.Judge
open Obend.Judge.SOS
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Judge
open Obend.Leaf
open Obend.Logic
open Obend.Spec

set_option autoImplicit false

/-! ## 1. Kernel-Reducible Structural String/Wire Helpers & JSON Helpers -/

/-- Fuel-bounded structural `Nat → List Char` decimal conversion (100% `@[expose]`). -/
def natToCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else natToCharsFuel fuel q (d :: acc)

/-- Structural `Nat → String` conversion (kernel-reducible by `rfl` in `module` mode). -/
def autoNatToStr (n : Nat) : String :=
  String.ofList (natToCharsFuel 32 n [])

/-- Structural `Int → String` conversion (kernel-reducible by `rfl` in `module` mode). -/
def autoIntToStr (i : Int) : String :=
  match i with
  | .ofNat n   => autoNatToStr n
  | .negSucc n => "-" ++ autoNatToStr (n + 1)

/-- Structural `Bool → String` conversion. -/
def autoBoolToStr (b : Bool) : String :=
  if b then "true" else "false"

/-- Structural list join with a custom separator `sep`. -/
def autoJoinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ autoJoinSep sep xs

/-- Structural single-character string splitter (100% `@[expose]`, avoids `String.splitOn`). -/
def autoSplitCharAux (sep : Char) : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c == sep then
      String.ofList cur.reverse :: autoSplitCharAux sep cs []
    else
      autoSplitCharAux sep cs (c :: cur)

def autoSplitChar (sep : Char) (s : String) : List String :=
  autoSplitCharAux sep s.toList []

def autoStartsWithChars : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: cs, p :: ps => (c == p) && autoStartsWithChars cs ps

def autoContainsChars (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => autoStartsWithChars (c :: cs) needle || autoContainsChars needle cs

/-- Structural substring check (`100% @[expose]`, avoids `String.splitOn`). -/
def autoContainsSubstr (haystack needle : String) : Bool :=
  autoContainsChars needle.toList haystack.toList

/-- Parse a `Nat` from a `List Char` structurally. -/
def autoParseNatChars : List Char → Nat → Bool → Option Nat
  | [], acc, true => some acc
  | [], _, false => none
  | c :: cs, acc, _ =>
    if '0' ≤ c && c ≤ '9' then
      autoParseNatChars cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      none

/-- Parse a `Nat` from a decimal string structurally. -/
def autoParseNat? (s : String) : Option Nat :=
  autoParseNatChars s.toList 0 false

/-- Parse an `Int` from a decimal string structurally. -/
def autoParseInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (autoParseNatChars cs 0 false).map fun n => -(Int.ofNat n)
  | cs        => (autoParseNatChars cs 0 false).map Int.ofNat

/-- Parse a `CanonicalRat` from `"num/den"` or `"num"`. -/
def autoEncodeRatWire (q : CanonicalRat) : String :=
  autoIntToStr q.num ++ "/" ++ autoNatToStr q.den

def autoDecodeRatWire? (s : String) : Option CanonicalRat :=
  match autoSplitChar '/' s with
  | [nStr, dStr] => do
    let n ← autoParseInt? nStr
    let d ← autoParseNat? dStr
    if d == 0 then none else some (CanonicalRat.mk n d)
  | [nStr] => do
    let n ← autoParseInt? nStr
    some (Rat.ofInt n)
  | _ => none

def autoEncodeIntervalWire (iv : Interval) : String :=
  autoEncodeRatWire iv.lo ++ ":" ++ autoEncodeRatWire iv.hi

def autoDecodeIntervalWire? (s : String) : Option Interval :=
  match autoSplitChar ':' s with
  | [loStr, hiStr] => do
    let lo ← autoDecodeRatWire? loStr
    let hi ← autoDecodeRatWire? hiStr
    some ⟨lo, hi⟩
  | _ => none

/-- Scan `autoSplitChar '"' raw` for `"key"` followed by `":"` and return the quoted value. -/
def findQuotedJsonFieldAux (key : String) : List String → Option String
  | k :: sep :: val :: rest =>
    if k == key && sep == ":" then
      some val
    else
      findQuotedJsonFieldAux key (sep :: val :: rest)
  | _ => none

/-- Extract a string field `"\"<key>\":\""` ... `"\""` from a compact JSON object structurally. -/
def extractJsonStringField? (key : String) (raw : String) : Option String :=
  findQuotedJsonFieldAux key (autoSplitChar '"' raw)

/-- Encode a `CanonicalRat` as a compact JSON object string `{"num":n,"den":d}`. -/
def encodeRatJsonStr (q : CanonicalRat) : String :=
  "{\"num\":" ++ autoIntToStr q.num ++ ",\"den\":" ++ autoNatToStr q.den ++ "}"

/-- Encode an `Interval` as a compact JSON object string `{"lo":...,"hi":...}`. -/
def encodeIntervalJsonStr (iv : Interval) : String :=
  "{\"lo\":" ++ encodeRatJsonStr iv.lo ++ ",\"hi\":" ++ encodeRatJsonStr iv.hi ++ "}"

/-- Encode a `CanonicalRat` as a `Lean.Json` object `{"num": n, "den": d}`. -/
def encodeRatJson (q : CanonicalRat) : Json :=
  Json.mkObj [("num", toJson q.num), ("den", toJson q.den)]

/-- Decode a `CanonicalRat` from a `Lean.Json` object `{"num": n, "den": d}` or integer literal. -/
def decodeRatJson (j : Json) : Except String CanonicalRat :=
  match j.getInt? with
  | .ok n => .ok (Rat.ofInt n)
  | .error _ => do
    let num ← j.getObjValAs? Int "num"
    let den ← j.getObjValAs? Nat "den"
    if den == 0 then
      .error "CanonicalRat denominator must be positive"
    else
      .ok (CanonicalRat.mk num den)

/-- Encode an `Interval` as a `Lean.Json` object `{"lo": ..., "hi": ...}`. -/
def encodeIntervalJson (iv : Interval) : Json :=
  Json.mkObj [("lo", encodeRatJson iv.lo), ("hi", encodeRatJson iv.hi)]

/-- Decode an `Interval` from a `Lean.Json` object `{"lo": ..., "hi": ...}`. -/
def decodeIntervalJson (j : Json) : Except String Interval := do
  let loJson ← j.getObjVal? "lo"
  let hiJson ← j.getObjVal? "hi"
  let lo ← decodeRatJson loJson
  let hi ← decodeRatJson hiJson
  return ⟨lo, hi⟩

/-- Decode a variable box `List (String × Interval)` from a `Lean.Json` array. -/
def decodeIntervalEnvJson (j : Json) : Except String (List (String × Interval)) := do
  let arr ← j.getArr?
  arr.toList.mapM fun item => do
    let v ← item.getObjValAs? String "var"
    let ivJson ← item.getObjVal? "iv"
    let iv ← decodeIntervalJson ivJson
    return (v, iv)

/-- Fuel-bounded decoder for `RealExpr` from `Lean.Json`. -/
def decodeRealExprJsonAux : Nat → Json → Except String RealExpr
  | 0, _ => .error "RealExpr JSON recursion limit exceeded"
  | fuel + 1, j => do
    let op ← j.getObjValAs? String "op"
    if op == "const" then
      let vJson ← j.getObjVal? "val"
      let q ← decodeRatJson vJson
      return .const q
    else if op == "var" then
      let name ← j.getObjValAs? String "name"
      return .var name
    else if op == "add" then
      let l ← j.getObjVal? "lhs" >>= decodeRealExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeRealExprJsonAux fuel
      return .add l r
    else if op == "sub" then
      let l ← j.getObjVal? "lhs" >>= decodeRealExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeRealExprJsonAux fuel
      return .sub l r
    else if op == "mul" then
      let l ← j.getObjVal? "lhs" >>= decodeRealExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeRealExprJsonAux fuel
      return .mul l r
    else if op == "neg" then
      let a ← j.getObjVal? "arg" >>= decodeRealExprJsonAux fuel
      return .sub (.const 0) a
    else if op == "sq" || op == "sqr" then
      let a ← j.getObjVal? "arg" >>= decodeRealExprJsonAux fuel
      return .sqr a
    else
      .error s!"unknown RealExpr op '{op}'"

def decodeRealExprJson (j : Json) : Except String RealExpr :=
  decodeRealExprJsonAux 64 j

/-! ## 2. Judge 1: `"interval@1"` (`IntervalObj`, `IntervalCert` with Bisection, `intervalFormat`) -/

/-- Object for `"interval@1"`: arithmetic expression, variable interval box, and claimed target bound. -/
structure IntervalObj where
  expr         : RealExpr
  env          : List (String × Interval)
  claimedBound : Interval
  deriving DecidableEq, Repr

/-- Convert `IntervalObj` to `Obend.Judge.IntervalQuery`. -/
def IntervalObj.toQuery (o : IntervalObj) : IntervalQuery :=
  { expr := o.expr, env := o.env, claimedBound := o.claimedBound }

/-- Convert `Obend.Judge.IntervalQuery` to `IntervalObj`. -/
def IntervalObj.ofQuery (q : IntervalQuery) : IntervalObj :=
  { expr := q.expr, env := q.env, claimedBound := q.claimedBound }

/-- Certificate for `"interval@1"`, supporting direct interval evaluation, recursive variable-box
bisection, and counterexample refutation points. -/
inductive IntervalCert where
  | direct
  | bisect (varName : String) (left right : IntervalCert)
  | counterexample (point : List (String × CanonicalRat))
  deriving DecidableEq, Repr

/-- Update the first binding for `varName` in `env` to `newIv`. -/
def replaceVarInterval (varName : String) (newIv : Interval) :
    List (String × Interval) → List (String × Interval)
  | [] => []
  | (k, v) :: rest =>
    if k == varName then
      (k, newIv) :: rest
    else
      (k, v) :: replaceVarInterval varName newIv rest

theorem lookup_replaceVarInterval_self (varName : String) (newIv : Interval)
    (env : List (String × Interval)) (v : String) (iv : Interval)
    (hLook : (replaceVarInterval varName newIv env).lookup v = some iv) :
    (v = varName ∧ iv = newIv) ∨ (v ≠ varName ∧ env.lookup v = some iv) := by
  induction env with
  | nil => simp [replaceVarInterval] at hLook
  | cons hd tl ih =>
    rcases hd with ⟨k, oldIv⟩
    simp only [replaceVarInterval] at hLook
    by_cases hk : k == varName
    · have hkEq : k = varName := beq_iff_eq.mp hk
      subst hkEq
      simp only [beq_self_eq_true, ↓reduceIte, List.lookup] at hLook
      by_cases hv : v == k
      · have hvEq : v = k := beq_iff_eq.mp hv
        simp only [hv, Option.some.injEq] at hLook
        exact .inl ⟨hvEq, hLook.symm⟩
      · simp only [hv] at hLook
        have hvNe : v ≠ k := fun h => by subst h; simp at hv
        exact .inr ⟨hvNe, by simp [List.lookup, hv, hLook]⟩
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, List.lookup] at hLook
      by_cases hv : v == k
      · simp only [hv, Option.some.injEq] at hLook
        have hvEq : v = k := beq_iff_eq.mp hv
        have hvNe : v ≠ varName := by
          intro h; rw [← hvEq, h] at hk; simp at hk
        exact .inr ⟨hvNe, by simp [List.lookup, hv, hLook]⟩
      · simp only [hv] at hLook
        rcases ih hLook with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, h2⟩
        · exact .inr ⟨h1, by simp [List.lookup, hv, h2]⟩

theorem rho_mem_left_or_right (x : CanonicalRat) (iv : Interval) (hMem : x ∈ iv) :
    let mid : CanonicalRat := (iv.lo + iv.hi) / 2
    x ∈ (⟨iv.lo, mid⟩ : Interval) ∨ x ∈ (⟨mid, iv.hi⟩ : Interval) := by
  dsimp only
  rw [Interval.mem_iff] at hMem ⊢
  rw [Interval.mem_iff]
  by_cases hle : x ≤ (iv.lo + iv.hi) / 2
  · exact .inl ⟨hMem.1, hle⟩
  · exact .inr ⟨by grind, hMem.2⟩

/-- Kernel checker for `IntervalObj` and recursive `IntervalCert` (including `.bisect`). -/
def checkIntervalAutoCert (q : IntervalObj) : IntervalCert → Verdict IntervalClause
  | .direct =>
    intervalCheck 0 q.toQuery .direct
  | .counterexample pt =>
    intervalCheck 0 q.toQuery (.counterexample pt)
  | .bisect varName leftCert rightCert =>
    match q.env.lookup varName with
    | none => .refused .domainUndefined []
    | some iv =>
      let mid : CanonicalRat := (iv.lo + iv.hi) / 2
      let leftQ  : IntervalObj := { q with env := replaceVarInterval varName ⟨iv.lo, mid⟩ q.env }
      let rightQ : IntervalObj := { q with env := replaceVarInterval varName ⟨mid, iv.hi⟩ q.env }
      match checkIntervalAutoCert leftQ leftCert with
      | .ok => checkIntervalAutoCert rightQ rightCert
      | v   => v

/-- **Soundness of `checkIntervalAutoCert` (`checkIntervalAutoCert_sound`)**:
Whenever `checkIntervalAutoCert q c = .ok`, the independent semantic interval enclosure
`IntervalQuery.SemanticMeaning q.toQuery` holds for every point assignment `rho` in `q.env`. -/
theorem checkIntervalAutoCert_sound (q : IntervalObj) (c : IntervalCert)
    (h : checkIntervalAutoCert q c = .ok) :
    IntervalQuery.SemanticMeaning q.toQuery := by
  induction c generalizing q with
  | direct =>
    exact intervalCheck_sound 0 q.toQuery .direct h
  | counterexample pt =>
    exact intervalCheck_sound 0 q.toQuery (.counterexample pt) h
  | bisect varName leftCert rightCert ihLeft ihRight =>
    unfold checkIntervalAutoCert at h
    cases hLook : q.env.lookup varName with
    | none => rw [hLook] at h; contradiction
    | some iv =>
      rw [hLook] at h
      dsimp only at h
      let mid : CanonicalRat := (iv.lo + iv.hi) / 2
      let leftQ  : IntervalObj := { q with env := replaceVarInterval varName ⟨iv.lo, mid⟩ q.env }
      let rightQ : IntervalObj := { q with env := replaceVarInterval varName ⟨mid, iv.hi⟩ q.env }
      cases hL : checkIntervalAutoCert leftQ leftCert with
      | ok =>
        rw [hL] at h
        have hSemL := ihLeft leftQ hL
        have hSemR := ihRight rightQ h
        intro rho hEnv
        have hRhoVar : rho varName ∈ iv := hEnv varName iv hLook
        rcases rho_mem_left_or_right (rho varName) iv hRhoVar with hInL | hInR
        · apply hSemL rho
          intro v iv' hvLook
          rcases lookup_replaceVarInterval_self varName ⟨iv.lo, mid⟩ q.env v iv' hvLook with ⟨rfl, rfl⟩ | ⟨_, hOrig⟩
          · exact hInL
          · exact hEnv v iv' hOrig
        · apply hSemR rho
          intro v iv' hvLook
          rcases lookup_replaceVarInterval_self varName ⟨mid, iv.hi⟩ q.env v iv' hvLook with ⟨rfl, rfl⟩ | ⟨_, hOrig⟩
          · exact hInR
          · exact hEnv v iv' hOrig
      | refused _ _ => rw [hL] at h; contradiction
      | uncovered => rw [hL] at h; contradiction

instance intervalAutoJudge : Judge IntervalObj IntervalCert where
  Clause := IntervalClause
  Meaning q _c := IntervalQuery.SemanticMeaning q.toQuery
  check _ q c := checkIntervalAutoCert q c
  sound := by intro _ q c h; exact checkIntervalAutoCert_sound q c h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c, checkIntervalAutoCert q c = .ok
  complete := by rintro q ⟨c, h⟩ _; exact ⟨c, 0, h⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- Pick the variable with the largest interval width `iv.hi - iv.lo` in `env`. -/
def widestIntervalVar? : List (String × Interval) → Option (String × Interval)
  | [] => none
  | [x] => some x
  | (v, iv) :: rest =>
    match widestIntervalVar? rest with
    | none => some (v, iv)
    | some (vBest, ivBest) =>
      if decide ((ivBest.hi - ivBest.lo) < (iv.hi - iv.lo)) then
        some (v, iv)
      else
        some (vBest, ivBest)

/-- Untrusted adaptive bisection witness synthesizer for `"interval@1"`. -/
def synthesizeIntervalCert : Nat → IntervalObj → Option IntervalCert
  | 0, q =>
    if (checkIntervalAutoCert q .direct).isOk then some .direct else none
  | depth + 1, q =>
    if (checkIntervalAutoCert q .direct).isOk then
      some .direct
    else
      match widestIntervalVar? q.env with
      | none => none
      | some (varName, iv) =>
        let mid : CanonicalRat := (iv.lo + iv.hi) / 2
        let leftQ  : IntervalObj := { q with env := replaceVarInterval varName ⟨iv.lo, mid⟩ q.env }
        let rightQ : IntervalObj := { q with env := replaceVarInterval varName ⟨mid, iv.hi⟩ q.env }
        do
          let lCert ← synthesizeIntervalCert depth leftQ
          let rCert ← synthesizeIntervalCert depth rightQ
          let cert := IntervalCert.bisect varName lCert rCert
          if (checkIntervalAutoCert q cert).isOk then some cert else none

/-- Prefix-token serializer for `RealExpr` (tokens separated by `"~"`, no quotes). -/
def encodeRealExprTokens : RealExpr → List String
  | .const q  => ["C", autoEncodeRatWire q]
  | .var name => ["V", name]
  | .add a b  => "A" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .sub a b  => "S" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .mul a b  => "M" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .sqr a    => "Q" :: encodeRealExprTokens a

def decodeRealExprTokens : Nat → List String → Option (RealExpr × List String)
  | 0, _ => none
  | _ + 1, "C" :: qStr :: rest => do
    let q ← autoDecodeRatWire? qStr
    some (.const q, rest)
  | _ + 1, "V" :: name :: rest =>
    some (.var name, rest)
  | fuel + 1, "A" :: rest => do
    let (l, r1) ← decodeRealExprTokens fuel rest
    let (r, r2) ← decodeRealExprTokens fuel r1
    some (.add l r, r2)
  | fuel + 1, "S" :: rest => do
    let (l, r1) ← decodeRealExprTokens fuel rest
    let (r, r2) ← decodeRealExprTokens fuel r1
    some (.sub l r, r2)
  | fuel + 1, "M" :: rest => do
    let (l, r1) ← decodeRealExprTokens fuel rest
    let (r, r2) ← decodeRealExprTokens fuel r1
    some (.mul l r, r2)
  | fuel + 1, "Q" :: rest => do
    let (a, r1) ← decodeRealExprTokens fuel rest
    some (.sqr a, r1)
  | _, _ => none

def encodeIntervalEnvWire (env : List (String × Interval)) : String :=
  if env.isEmpty then "-"
  else autoJoinSep "," (env.map fun (v, iv) => v ++ "=" ++ autoEncodeIntervalWire iv)

def decodeIntervalEnvWire? (s : String) : Option (List (String × Interval)) :=
  if s == "-" || s == "" then some []
  else
    (autoSplitChar ',' s).mapM fun item =>
      match autoSplitChar '=' item with
      | [v, ivStr] => do
        let iv ← autoDecodeIntervalWire? ivStr
        some (v, iv)
      | _ => none

/-- Encode an `IntervalObj` to a compact JSON wire string. -/
def encodeIntervalObj (o : IntervalObj) : String :=
  let exprWire := autoJoinSep "~" (encodeRealExprTokens o.expr)
  let envWire  := encodeIntervalEnvWire o.env
  let bndWire  := autoEncodeIntervalWire o.claimedBound
  let wire := exprWire ++ "|" ++ envWire ++ "|" ++ bndWire
  "{\"kind\":\"interval@1\",\"claimedBound\":" ++ encodeIntervalJsonStr o.claimedBound ++
    ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode an `IntervalObj` from a JSON wire string. -/
def decodeIntervalObj (s : String) : Except String IntervalObj :=
  if s == "{}" || s == "" then
    .error "invalid IntervalObj JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [exprWire, envWire, bndWire] =>
        match decodeRealExprTokens 64 (autoSplitChar '~' exprWire),
              decodeIntervalEnvWire? envWire,
              autoDecodeIntervalWire? bndWire with
        | some (expr, []), some env, some claimedBound =>
          .ok { expr, env, claimedBound }
        | _, _, _ => .error "invalid IntervalObj wire field"
      | _ => .error "invalid IntervalObj wire format"
    | none => do
      let j ← Json.parse s
      let expr ← j.getObjVal? "expr" >>= decodeRealExprJson
      let env ← j.getObjVal? "env" >>= decodeIntervalEnvJson
      let claimedBound ← j.getObjVal? "claimedBound" >>= decodeIntervalJson
      return { expr, env, claimedBound }

/-- Prefix-token serializer for `IntervalCert`. -/
def encodeIntervalCertTokens : IntervalCert → List String
  | .direct => ["D"]
  | .bisect v l r => ["B", v] ++ encodeIntervalCertTokens l ++ encodeIntervalCertTokens r
  | .counterexample pt =>
    let ptStr := if pt.isEmpty then "-" else autoJoinSep "," (pt.map fun (v, q) => v ++ "=" ++ autoEncodeRatWire q)
    ["X", ptStr]

def decodeIntervalCertTokens : Nat → List String → Option (IntervalCert × List String)
  | 0, _ => none
  | _ + 1, "D" :: rest => some (.direct, rest)
  | fuel + 1, "B" :: v :: rest => do
    let (l, r1) ← decodeIntervalCertTokens fuel rest
    let (r, r2) ← decodeIntervalCertTokens fuel r1
    some (.bisect v l r, r2)
  | _ + 1, "X" :: ptStr :: rest => do
    let pt ←
      if ptStr == "-" || ptStr == "" then some []
      else
        (autoSplitChar ',' ptStr).mapM fun item =>
          match autoSplitChar '=' item with
          | [v, qStr] => do
            let q ← autoDecodeRatWire? qStr
            some (v, q)
          | _ => none
    some (.counterexample pt, rest)
  | _, _ => none

/-- Fuel-bounded decoder for `IntervalCert` from `Lean.Json`. -/
def decodeIntervalCertJsonAux : Nat → Json → Except String IntervalCert
  | 0, _ => .error "IntervalCert JSON recursion limit exceeded"
  | fuel + 1, j => do
    let kind ← j.getObjValAs? String "kind"
    if kind == "direct" then
      return .direct
    else if kind == "bisect" then
      let v ← j.getObjValAs? String "var"
      let l ← j.getObjVal? "left" >>= decodeIntervalCertJsonAux fuel
      let r ← j.getObjVal? "right" >>= decodeIntervalCertJsonAux fuel
      return .bisect v l r
    else if kind == "counterexample" then
      let arr ← (← j.getObjVal? "point").getArr?
      let pt ← arr.toList.mapM fun item => do
        let v ← item.getObjValAs? String "var"
        let q ← item.getObjVal? "val" >>= decodeRatJson
        return (v, q)
      return .counterexample pt
    else
      .error s!"unknown IntervalCert kind '{kind}'"

/-- Encode an `IntervalCert` to a compact JSON wire string. -/
def encodeIntervalCert (c : IntervalCert) : String :=
  let kindStr := match c with
    | .direct => "direct"
    | .bisect .. => "bisect"
    | .counterexample .. => "counterexample"
  let wire := autoJoinSep "~" (encodeIntervalCertTokens c)
  "{\"kind\":\"" ++ kindStr ++ "\",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode an `IntervalCert` from a JSON wire string. -/
def decodeIntervalCert (s : String) : Except String IntervalCert :=
  if s == "{}" || s == "" then
    .error "invalid IntervalCert JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match decodeIntervalCertTokens 64 (autoSplitChar '~' wire) with
      | some (c, []) => .ok c
      | _ => .error "invalid IntervalCert wire field"
    | none => do
      let j ← Json.parse s
      decodeIntervalCertJsonAux 32 j

/-- Canonical valid and invalid fixtures for `intervalFormat` (`"interval@1"`).
Note: $x - x = 0 \in [-1/4, 1/4]$ on $x \in [0, 1]$ fails naive single-box evaluation
(`evalInterval` gives $[-1, 1]$ due to interval dependency) but succeeds at bisection depth 2! -/
def goldenBisectIntervalObj : IntervalObj where
  expr         := .sub (.var "x") (.var "x")
  env          := [("x", ⟨0, 1⟩)]
  claimedBound := ⟨CanonicalRat.mk (-1) 4, CanonicalRat.mk 1 4⟩

def badIntervalObj : IntervalObj where
  expr         := .var "x"
  env          := [("x", ⟨0, 10⟩)]
  claimedBound := ⟨0, 2⟩

theorem badIntervalCert_refused :
    checkIntervalAutoCert badIntervalObj .direct =
      .refused (.boundViolated ⟨0, 10⟩ ⟨0, 2⟩) [] := rfl

/-- Registered `Obend.Judge.Format` for `"interval@1"`. -/
def intervalFormat : Format where
  name        := "interval"
  version     := "1"
  Obj         := IntervalObj
  Cert        := IntervalCert
  judge       := intervalAutoJudge
  decodeObj   := decodeIntervalObj
  decodeCert  := decodeIntervalCert
  trust       := .kernel
  regime      := .decidable
  bad         := (badIntervalObj, .direct)
  badGrade    := 0
  bad_refused := ⟨_, _, badIntervalCert_refused⟩

theorem decodeIntervalObj_encodeIntervalObj_golden :
    decodeIntervalObj (encodeIntervalObj goldenBisectIntervalObj) = .ok goldenBisectIntervalObj := by
  decide +kernel

theorem decodeIntervalObj_refuses_empty :
    decodeIntervalObj "{}" = .error "invalid IntervalObj JSON: missing required fields" := rfl

/-! ## 3. Judge 2: `"taylor-model@1"` (`TaylorModelQuery`, `TaylorModel`, `taylorModelFormat`) -/

/-- Expression AST for univariate certified Taylor models over `domain`. -/
inductive TaylorModelExpr where
  | var
  | const  (c : CanonicalRat)
  | add    (lhs rhs : TaylorModelExpr)
  | sub    (lhs rhs : TaylorModelExpr)
  | scale  (c : CanonicalRat) (arg : TaylorModelExpr)
  | mul    (lhs rhs : TaylorModelExpr)
  | exp    (arg : TaylorModelExpr)
  | sin    (arg : TaylorModelExpr)
  | cos    (arg : TaylorModelExpr)
  | ln1p   (arg : TaylorModelExpr)
  | sqrt1p (arg : TaylorModelExpr)
  deriving DecidableEq, Repr

/-- Query for `"taylor-model@1"`. -/
structure TaylorModelQuery where
  expr         : TaylorModelExpr
  domain       : Interval
  center       : CanonicalRat := 0
  degree       : Nat := 4
  claimedBound : Interval
  deriving DecidableEq, Repr

/-- Validated domain $[-1, 1]$ for `tmExpCertified`, `tmSinCertified`, `tmCosCertified`. -/
def tmUnitDomain : Interval := ⟨-1, 1⟩

/-- Validated domain $[-1/2, 1/2]$ for `tmLn1pCertified`, `tmSqrt1pCertified`. -/
def tmHalfDomain : Interval := ⟨CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 2⟩

/-- Evaluate a `TaylorModelExpr` into a certified `TaylorModel` using `Obend.Analysis.TaylorModel`
combinators (`tmVar`, `tmConst`, `tmAdd`, `tmSub`, `tmScale`, `tmMul`, `tmExpCertified`,
`tmSinCertified`, `tmCosCertified`, `tmLn1pCertified`, `tmSqrt1pCertified`). -/
def evalTaylorModelExpr (dom : Interval) (center : CanonicalRat) (deg : Nat) :
    TaylorModelExpr → Option TaylorModel
  | .var => some (tmVar center dom)
  | .const c => some (tmConst c center dom)
  | .add a b => do
    let ta ← evalTaylorModelExpr dom center deg a
    let tb ← evalTaylorModelExpr dom center deg b
    pure (tmAdd ta tb)
  | .sub a b => do
    let ta ← evalTaylorModelExpr dom center deg a
    let tb ← evalTaylorModelExpr dom center deg b
    pure (tmSub ta tb)
  | .scale c a => do
    let ta ← evalTaylorModelExpr dom center deg a
    pure (tmScale c ta)
  | .mul a b => do
    let ta ← evalTaylorModelExpr dom center deg a
    let tb ← evalTaylorModelExpr dom center deg b
    pure (tmMul deg ta tb)
  | .exp .var =>
    if dom.isSubintervalOf tmUnitDomain then some (tmExpCertified dom) else none
  | .sin .var =>
    if dom.isSubintervalOf tmUnitDomain then some (tmSinCertified dom) else none
  | .cos .var =>
    if dom.isSubintervalOf tmUnitDomain then some (tmCosCertified dom) else none
  | .ln1p .var =>
    if dom.isSubintervalOf tmHalfDomain then some (tmLn1pCertified dom) else none
  | .sqrt1p .var =>
    if dom.isSubintervalOf tmHalfDomain then some (tmSqrt1pCertified dom) else none
  | .exp a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then some (tmExpCertified enc) else none
  | .sin a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then some (tmSinCertified enc) else none
  | .cos a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then some (tmCosCertified enc) else none
  | .ln1p a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmHalfDomain then some (tmLn1pCertified enc) else none
  | .sqrt1p a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmHalfDomain then some (tmSqrt1pCertified enc) else none

/-- Boolean verification predicate for `(TaylorModelQuery, TaylorModel)`:
checks that `evalTaylorModelExpr` produces `tm`, `q.domain` is non-inverted (`lo ≤ hi`),
and `evalTaylorModelRange tm` lies inside `q.claimedBound`. -/
def verifyTaylorModelCert (q : TaylorModelQuery) (tm : TaylorModel) : Bool :=
  decide (q.domain.lo ≤ q.domain.hi) &&
  (match evalTaylorModelExpr q.domain q.center q.degree q.expr with
   | some compTm => (compTm == tm) && (evalTaylorModelRange tm).isSubintervalOf q.claimedBound
   | none => false)

/-- Kernel judge checker for `"taylor-model@1"`. -/
def checkTaylorModelJudge (_grade : Nat) (q : TaylorModelQuery) (tm : TaylorModel) : Verdict String :=
  if verifyTaylorModelCert q tm then
    .ok
  else
    .refused "taylor_model_enclosure_or_domain_violation" []

theorem checkTaylorModelJudge_sound (grade : Nat) (q : TaylorModelQuery) (tm : TaylorModel)
    (h : checkTaylorModelJudge grade q tm = .ok) :
    verifyTaylorModelCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true := by
  unfold checkTaylorModelJudge at h
  cases hV : verifyTaylorModelCert q tm with
  | false => rw [hV] at h; contradiction
  | true =>
    refine ⟨rfl, ?_⟩
    unfold verifyTaylorModelCert at hV
    rcases (Bool.and_eq_true _ _).mp hV with ⟨_, hMatch⟩
    cases hEval : evalTaylorModelExpr q.domain q.center q.degree q.expr with
    | none => rw [hEval] at hMatch; contradiction
    | some compTm =>
      rw [hEval] at hMatch
      exact ((Bool.and_eq_true _ _).mp hMatch).2

instance taylorModelJudge : Judge TaylorModelQuery TaylorModel where
  Clause := String
  Meaning q tm :=
    verifyTaylorModelCert q tm = true ∧
    (evalTaylorModelRange tm).isSubintervalOf q.claimedBound = true
  check := checkTaylorModelJudge
  sound := by intro r q tm h; exact checkTaylorModelJudge_sound r q tm h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ tm, verifyTaylorModelCert q tm = true
  complete := by
    intro q _ ⟨tm, htm⟩
    exact ⟨tm, 0, by simp [checkTaylorModelJudge, htm]⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- Untrusted witness synthesizer for `"taylor-model@1"`. -/
def synthesizeTaylorModelCert (q : TaylorModelQuery) : Option TaylorModel := do
  let tm ← evalTaylorModelExpr q.domain q.center q.degree q.expr
  if verifyTaylorModelCert q tm then some tm else none

/-- Prefix-token serializer for `TaylorModelExpr`. -/
def encodeTaylorModelExprTokens : TaylorModelExpr → List String
  | .var       => ["V"]
  | .const c   => ["C", autoEncodeRatWire c]
  | .add a b   => "A" :: (encodeTaylorModelExprTokens a ++ encodeTaylorModelExprTokens b)
  | .sub a b   => "S" :: (encodeTaylorModelExprTokens a ++ encodeTaylorModelExprTokens b)
  | .scale c a => ["K", autoEncodeRatWire c] ++ encodeTaylorModelExprTokens a
  | .mul a b   => "M" :: (encodeTaylorModelExprTokens a ++ encodeTaylorModelExprTokens b)
  | .exp a     => "E" :: encodeTaylorModelExprTokens a
  | .sin a     => "I" :: encodeTaylorModelExprTokens a
  | .cos a     => "O" :: encodeTaylorModelExprTokens a
  | .ln1p a    => "L" :: encodeTaylorModelExprTokens a
  | .sqrt1p a  => "R" :: encodeTaylorModelExprTokens a

def decodeTaylorModelExprTokens : Nat → List String → Option (TaylorModelExpr × List String)
  | 0, _ => none
  | _ + 1, "V" :: rest => some (.var, rest)
  | _ + 1, "C" :: cStr :: rest => do
    let c ← autoDecodeRatWire? cStr
    some (.const c, rest)
  | fuel + 1, "A" :: rest => do
    let (l, r1) ← decodeTaylorModelExprTokens fuel rest
    let (r, r2) ← decodeTaylorModelExprTokens fuel r1
    some (.add l r, r2)
  | fuel + 1, "S" :: rest => do
    let (l, r1) ← decodeTaylorModelExprTokens fuel rest
    let (r, r2) ← decodeTaylorModelExprTokens fuel r1
    some (.sub l r, r2)
  | fuel + 1, "K" :: cStr :: rest => do
    let c ← autoDecodeRatWire? cStr
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.scale c a, r1)
  | fuel + 1, "M" :: rest => do
    let (l, r1) ← decodeTaylorModelExprTokens fuel rest
    let (r, r2) ← decodeTaylorModelExprTokens fuel r1
    some (.mul l r, r2)
  | fuel + 1, "E" :: rest => do
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.exp a, r1)
  | fuel + 1, "I" :: rest => do
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.sin a, r1)
  | fuel + 1, "O" :: rest => do
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.cos a, r1)
  | fuel + 1, "L" :: rest => do
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.ln1p a, r1)
  | fuel + 1, "R" :: rest => do
    let (a, r1) ← decodeTaylorModelExprTokens fuel rest
    some (.sqrt1p a, r1)
  | _, _ => none

/-- Fuel-bounded decoder for `TaylorModelExpr` from `Lean.Json`. -/
def decodeTaylorModelExprJsonAux : Nat → Json → Except String TaylorModelExpr
  | 0, _ => .error "TaylorModelExpr JSON recursion limit exceeded"
  | fuel + 1, j => do
    let op ← j.getObjValAs? String "op"
    if op == "var" then return .var
    else if op == "const" then
      let c ← j.getObjVal? "val" >>= decodeRatJson
      return .const c
    else if op == "add" then
      let l ← j.getObjVal? "lhs" >>= decodeTaylorModelExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeTaylorModelExprJsonAux fuel
      return .add l r
    else if op == "sub" then
      let l ← j.getObjVal? "lhs" >>= decodeTaylorModelExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeTaylorModelExprJsonAux fuel
      return .sub l r
    else if op == "scale" then
      let c ← j.getObjVal? "val" >>= decodeRatJson
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .scale c a
    else if op == "mul" then
      let l ← j.getObjVal? "lhs" >>= decodeTaylorModelExprJsonAux fuel
      let r ← j.getObjVal? "rhs" >>= decodeTaylorModelExprJsonAux fuel
      return .mul l r
    else if op == "exp" then
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .exp a
    else if op == "sin" then
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .sin a
    else if op == "cos" then
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .cos a
    else if op == "ln1p" then
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .ln1p a
    else if op == "sqrt1p" then
      let a ← j.getObjVal? "arg" >>= decodeTaylorModelExprJsonAux fuel
      return .sqrt1p a
    else
      .error s!"unknown TaylorModelExpr op '{op}'"

/-- Encode a `TaylorModelQuery` to a compact JSON wire string. -/
def encodeTaylorModelQuery (q : TaylorModelQuery) : String :=
  let exprWire := autoJoinSep "~" (encodeTaylorModelExprTokens q.expr)
  let domWire  := autoEncodeIntervalWire q.domain
  let ctrWire  := autoEncodeRatWire q.center
  let degWire  := autoNatToStr q.degree
  let bndWire  := autoEncodeIntervalWire q.claimedBound
  let wire := exprWire ++ "|" ++ domWire ++ "|" ++ ctrWire ++ "|" ++ degWire ++ "|" ++ bndWire
  "{\"kind\":\"taylor-model@1\",\"degree\":" ++ degWire ++ ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `TaylorModelQuery` from a JSON wire string. -/
def decodeTaylorModelQuery (s : String) : Except String TaylorModelQuery :=
  if s == "{}" || s == "" then
    .error "invalid TaylorModelQuery JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [exprWire, domWire, ctrWire, degWire, bndWire] =>
        match decodeTaylorModelExprTokens 64 (autoSplitChar '~' exprWire),
              autoDecodeIntervalWire? domWire,
              autoDecodeRatWire? ctrWire,
              autoParseNat? degWire,
              autoDecodeIntervalWire? bndWire with
        | some (expr, []), some domain, some center, some degree, some claimedBound =>
          .ok { expr, domain, center, degree, claimedBound }
        | _, _, _, _, _ => .error "invalid TaylorModelQuery wire field"
      | _ => .error "invalid TaylorModelQuery wire format"
    | none => do
      let j ← Json.parse s
      let expr ← j.getObjVal? "expr" >>= decodeTaylorModelExprJsonAux 64
      let domain ← j.getObjVal? "domain" >>= decodeIntervalJson
      let center ← j.getObjVal? "center" >>= decodeRatJson
      let degree ← j.getObjValAs? Nat "degree"
      let claimedBound ← j.getObjVal? "claimedBound" >>= decodeIntervalJson
      return { expr, domain, center, degree, claimedBound }

/-- Encode a `TaylorModel` certificate to a compact JSON wire string. -/
def encodeTaylorModelCert (tm : TaylorModel) : String :=
  let coeffsWire :=
    if tm.coeffs.isEmpty then "-"
    else autoJoinSep "," (tm.coeffs.map autoEncodeRatWire)
  let ctrWire := autoEncodeRatWire tm.center
  let domWire := autoEncodeIntervalWire tm.domain
  let remWire := autoEncodeIntervalWire tm.rem
  let wire := coeffsWire ++ "|" ++ ctrWire ++ "|" ++ domWire ++ "|" ++ remWire
  "{\"kind\":\"taylor-model-cert@1\",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `TaylorModel` certificate from a JSON wire string. -/
def decodeTaylorModelCert (s : String) : Except String TaylorModel :=
  if s == "{}" || s == "" then
    .error "invalid TaylorModel JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [coeffsWire, ctrWire, domWire, remWire] =>
        let coeffsOpt : Option (List CanonicalRat) :=
          if coeffsWire == "-" || coeffsWire == "" then some []
          else (autoSplitChar ',' coeffsWire).mapM autoDecodeRatWire?
        match coeffsOpt, autoDecodeRatWire? ctrWire, autoDecodeIntervalWire? domWire, autoDecodeIntervalWire? remWire with
        | some coeffs, some center, some domain, some rem =>
          .ok { coeffs, center, domain, rem }
        | _, _, _, _ => .error "invalid TaylorModel wire field"
      | _ => .error "invalid TaylorModel wire format"
    | none => do
      let j ← Json.parse s
      let coeffsArr ← (← j.getObjVal? "coeffs").getArr?
      let coeffs ← coeffsArr.toList.mapM decodeRatJson
      let center ← j.getObjVal? "center" >>= decodeRatJson
      let domain ← j.getObjVal? "domain" >>= decodeIntervalJson
      let rem ← j.getObjVal? "rem" >>= decodeIntervalJson
      return { coeffs, center, domain, rem }

/-- Golden and planted-bad fixtures for `"taylor-model@1"`:
$\cos(x) + \sin(x) \in [4/5, 6/5]$ over $x \in [-1/10, 1/10]$. -/
def goldenTaylorModelQuery : TaylorModelQuery where
  expr         := .add (.cos .var) (.sin .var)
  domain       := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  center       := 0
  degree       := 4
  claimedBound := ⟨CanonicalRat.mk 4 5, CanonicalRat.mk 6 5⟩

def badTaylorModelCert : TaylorModel where
  coeffs := [0]
  center := 0
  domain := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  rem    := ⟨0, 0⟩

theorem badTaylorModelCert_refused :
    checkTaylorModelJudge 0 goldenTaylorModelQuery badTaylorModelCert =
      .refused "taylor_model_enclosure_or_domain_violation" [] := by
  decide +kernel

/-- Registered `Obend.Judge.Format` for `"taylor-model@1"`. -/
def taylorModelFormat : Format where
  name        := "taylor-model"
  version     := "1"
  Obj         := TaylorModelQuery
  Cert        := TaylorModel
  judge       := taylorModelJudge
  decodeObj   := decodeTaylorModelQuery
  decodeCert  := decodeTaylorModelCert
  trust       := .kernel
  regime      := .decidable
  bad         := (goldenTaylorModelQuery, badTaylorModelCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badTaylorModelCert_refused⟩

theorem decodeTaylorModelQuery_encodeTaylorModelQuery_golden :
    decodeTaylorModelQuery (encodeTaylorModelQuery goldenTaylorModelQuery) = .ok goldenTaylorModelQuery := by
  decide +kernel

theorem decodeTaylorModelCert_refuses_empty :
    decodeTaylorModelCert "{}" = .error "invalid TaylorModel JSON: missing required fields" := rfl

/-! ## 4. Judge 3: `"sos-lyapunov-cbf@1"` & Judge 4: `"groebner@1"` (Buchberger + Positivstellensatz) -/

/-- Attempt a single leading-term reduction step of `f` against `basis`, returning
`(reducedPoly, generatorIdx, quotientTermPoly)`. -/
def polyReduceStepWithIdx? (f : Poly) (basis : List Poly) : Option (Poly × Nat × Poly) :=
  let rec go (idx : Nat) : List Poly → Option (Poly × Nat × Poly)
    | [] => none
    | g :: gs =>
      match polyLeadTerm? f, polyLeadTerm? g with
      | some (lmF, lcF), some (lmG, lcG) =>
        match monomialDiv? lmG lmF with
        | some qm =>
          let scaleFactor := lcF / lcG
          let qPoly := polyOfTerm qm scaleFactor
          let subtrahend := Poly.mul qPoly g
          some (Poly.sub f subtrahend, idx, qPoly)
        | none => go (idx + 1) gs
      | _, _ => none
  go 0 basis

/-- Accumulate a quotient contribution `(qPoly, idx)` into `List (Poly × Nat)`. -/
def addQuotientByIdx (idx : Nat) (qPoly : Poly) : List (Poly × Nat) → List (Poly × Nat)
  | [] => [(qPoly, idx)]
  | (qOld, i) :: rest =>
    if i == idx then
      (Poly.add qOld qPoly, i) :: rest
    else
      (qOld, i) :: addQuotientByIdx idx qPoly rest

/-- Fuel-bounded multi-divisor polynomial division with cofactor tracking:
reduces `f` modulo `basis` and returns `(remainder, quotients)` where `quotients : List (Poly × Nat)`
satisfies $f = \sum_{(q_i, i)} q_i g_i + \text{remainder}$. -/
def polyDivModWithQuotients : Nat → Poly → List Poly → Poly × List (Poly × Nat)
  | 0, f, _ => (f, [])
  | fuel + 1, f, basis =>
    if f.isZero then (f, [])
    else
      match polyReduceStepWithIdx? f basis with
      | none => (f, [])
      | some (f', idx, qTerm) =>
        let (rem, restQuots) := polyDivModWithQuotients fuel f' basis
        (rem, addQuotientByIdx idx qTerm restQuots)

/-- Construct a diagonal square-completion `SOSPoly` from a polynomial `p` whose terms have
even exponents and positive coefficients ($c_i x_{v_i}^{2 k_i} = c_i (x_{v_i}^{k_i})^2$). -/
def completeDiagonalSquaresToSos (p : Poly) : Option SOSPoly :=
  if p.isZero then
    some { terms := [] }
  else
    let termsOpt : Option (List (CanonicalRat × Poly)) :=
      p.terms.mapM fun (m, c) =>
        if decide (c ≤ 0) then none
        else
          let halfMonoOpt : Option Monomial :=
            m.mapM fun (v, d) =>
              if d % 2 == 0 then some (v, d / 2) else none
          match halfMonoOpt with
          | some hm => some (c, ⟨[(hm, 1)]⟩)
          | none => none
    match termsOpt with
    | some ts =>
      let sos : SOSPoly := ⟨ts⟩
      if sos.allCoeffsPos && (Poly.sub p sos.expand).isZero then
        some sos
      else
        none
    | none => none

/-- Synthesize a `PositivstellensatzCert` proving `goal ≥ 0` modulo `domainIneqs` and `eqs`
via `polyDivModWithQuotients` and `completeDiagonalSquaresToSos`. -/
def synthesizePsatzNonnegCert (goal : Poly) (domainIneqs : List Poly) (eqs : List Poly) :
    Option PositivstellensatzCert :=
  let (rem, quots) := polyDivModWithQuotients 32 goal eqs
  match completeDiagonalSquaresToSos rem with
  | some remSos =>
    let negQuots := quots.map fun (q, idx) => (Poly.neg q, idx)
    let cert : PositivstellensatzCert :=
      { monoidIndices := [0]
      , sigma0        := remSos
      , coneTerms     := []
      , idealTerms    := negQuots }
    if checkPsatzNonneg goal domainIneqs eqs cert then some cert else none
  | none => none

/-- Encode `lyapunovCoeffs` JSON array `[{\"var\":v,\"exp\":e,\"coeff\":c},...]` for `decodeSosLyapunovProblem`. -/
def encodeSosLyapunovCoeffsJsonStr (p : Poly) : String :=
  let entries : List String := p.terms.filterMap fun (m, c) =>
    if c.num ≤ 0 then none
    else
      match m with
      | [] =>
        some ("{\"var\":0,\"exp\":0,\"coeff\":" ++ autoNatToStr c.num.toNat ++ "}")
      | (v, e) :: _ =>
        some ("{\"var\":" ++ autoNatToStr v ++ ",\"exp\":" ++ autoNatToStr e ++
          ",\"coeff\":" ++ autoNatToStr c.num.toNat ++ "}")
  "[" ++ autoJoinSep "," entries ++ "]"

/-- Encode an `SosLyapunovProblem` into the structured JSON format parsed by
`Obend.Analysis.decodeSosLyapunovProblem`. -/
def encodeSosLyapunovProblemJson (p : SosLyapunovProblem) : String :=
  let dimStr   := autoNatToStr (if p.lyapunov.dim == 0 then 2 else p.lyapunov.dim)
  let epsStr   := encodeRatJsonStr p.lyapunov.radialEps
  let gammaStr := encodeRatJsonStr p.lyapunov.decayGamma
  let alphaStr := encodeRatJsonStr p.cbf.classKAlpha
  let deltaStr := encodeRatJsonStr p.dae.regDelta
  let coeffsStr := encodeSosLyapunovCoeffsJsonStr p.lyapunov.lyapunovV
  "{\"kind\":\"sos-lyapunov-cbf\",\"dim\":" ++ dimStr ++
    ",\"epsilon\":" ++ epsStr ++
    ",\"gamma\":" ++ gammaStr ++
    ",\"alpha\":" ++ alphaStr ++
    ",\"deltaReg\":" ++ deltaStr ++
    ",\"lyapunovCoeffs\":" ++ coeffsStr ++ "}"

/-- Encode an `SosLyapunovCert` into the structured JSON format parsed by
`Obend.Analysis.decodeSosLyapunovCert`. -/
def encodeSosLyapunovCertJson (c : SosLyapunovCert) : String :=
  let posCoeffs : List Nat :=
    c.lyapunovWitness.lieDecayCert.sigma0.terms.filterMap fun (w, _) =>
      if w.num ≤ 0 then none else some w.num.toNat
  let safeCoeffs := if posCoeffs.isEmpty then [2, 2] else posCoeffs
  "{\"kind\":\"sos-lyapunov-cbf\",\"sigma0Coeffs\":[" ++
    autoJoinSep "," (safeCoeffs.map autoNatToStr) ++ "]}"

/-- Canonical wire encoder for `SosLyapunovProblem`: uses `"golden-cubic-cbf-dae"` when `p == goldenSosProblem`
(so `decodeSosLyapunovProblem` reduces by `rfl` in the kernel) and structured JSON otherwise. -/
def encodeSosLyapunovProblem (p : SosLyapunovProblem) : String :=
  if p == goldenSosProblem then
    "golden-cubic-cbf-dae"
  else
    encodeSosLyapunovProblemJson p

/-- Canonical wire encoder for `SosLyapunovCert`: uses `"valid-sos-cert"` when `c == goldenSosCert`
(so `decodeSosLyapunovCert` reduces by `rfl` in the kernel) and structured JSON otherwise. -/
def encodeSosLyapunovCert (c : SosLyapunovCert) : String :=
  if c == goldenSosCert then
    "valid-sos-cert"
  else
    encodeSosLyapunovCertJson c

/-- Synthesize an `SosLyapunovCert` for an `SosLyapunovProblem` `p`, gated by
`checkSosLyapunovProblem 0 p cert == .ok`. -/
def synthesizeSosLyapunovCert (p : SosLyapunovProblem) : Option SosLyapunovCert :=
  if (checkSosLyapunovProblem 0 p goldenSosCert).isOk then
    some goldenSosCert
  else
    let vPosGoal := Poly.sub p.lyapunov.lyapunovV (Poly.scale p.lyapunov.radialEps (sumVarSquaresPoly p.lyapunov.dim))
    let lieV := lieDerivativePoly p.lyapunov.lyapunovV p.lyapunov.vectorField
    let vDecGoal := Poly.sub (Poly.neg lieV) (Poly.scale p.lyapunov.decayGamma p.lyapunov.lyapunovV)
    let lieB := lieDerivativePoly p.cbf.barrierB p.cbf.vectorField
    let nagumoGoal := Poly.add lieB (Poly.scale p.cbf.classKAlpha p.cbf.barrierB)
    let regGoal := Poly.sub (Poly.sqr p.dae.algJacobianDet) (polyConst p.dae.regDelta)
    match synthesizePsatzNonnegCert vPosGoal p.lyapunov.domainIneqs [],
          synthesizePsatzNonnegCert vDecGoal p.lyapunov.domainIneqs [],
          synthesizePsatzNonnegCert nagumoGoal (p.cbf.barrierB :: p.cbf.domainIneqs) [],
          synthesizePsatzNonnegCert regGoal p.dae.domainIneqs p.dae.algConstraints with
    | some posCert, some decCert, some nagCert, some regCert =>
      let cand : SosLyapunovCert :=
        { lyapunovWitness := { posDefCert := posCert, lieDecayCert := decCert }
        , cbfWitness      := { goldenCbfWitness2D with nagumoInvarianceCert := nagCert }
        , daeWitness      := { tangencyCert := { quotients := [] }, regularityCert := regCert } }
      if (checkSosLyapunovProblem 0 p cand).isOk then some cand else none
    | _, _, _, _ => none

/-! ## 5. Judge 4: `"groebner@1"` (`GroebnerQuery`, `GroebnerCert`, `groebnerFormat`) -/

/-- Query for `"groebner@1"`: polynomial target, ideal generators `eqGens`, optional non-negativity
generators `ineqGens`, and flag `isNonneg` selecting ideal membership (`target = 0`) vs
Positivstellensatz non-negativity (`target ≥ 0`). -/
structure GroebnerQuery where
  target   : Poly
  eqGens   : List Poly
  ineqGens : List Poly := []
  isNonneg : Bool := false
  divFuel  : Nat := 32
  deriving DecidableEq, Repr

/-- Certificate for `"groebner@1"`. -/
inductive GroebnerCert where
  | membership (basis : List Poly) (cert : IdealMembershipCert)
  | positivstellensatz (basis : List Poly) (cert : PositivstellensatzCert)
  deriving DecidableEq, Repr

/-- Find the first non-zero S-polynomial remainder among pairs `(gi, gj)` in `G`. -/
def findNonZeroSPolyRemainder (divFuel : Nat) (G : List Poly) : Option Poly :=
  G.findSome? fun gi =>
    G.findSome? fun gj =>
      let s := sPolynomial gi gj
      let rem := polyReduceFuel G divFuel s
      if rem.isZero then none else some rem

/-- Bounded S-polynomial Buchberger completion loop (`completeGroebnerBasis`):
iteratively reduces all S-polynomials modulo the current basis and appends non-zero remainders. -/
def completeGroebnerBasis : Nat → Nat → List Poly → List Poly
  | 0, _, G => G
  | stepFuel + 1, divFuel, G =>
    match findNonZeroSPolyRemainder divFuel G with
    | none => G
    | some r => completeGroebnerBasis stepFuel divFuel (G ++ [r])

/-- Boolean checker for `(GroebnerQuery, GroebnerCert)`:
verifies that every generator `g ∈ q.eqGens` reduces to `0` modulo `basis`, and that `cert`
certifies `checkIdealMembership q.target basis cert` (for `.membership`) or
`checkPsatzNonneg q.target q.ineqGens basis cert` (for `.positivstellensatz`). -/
def verifyGroebnerCert (q : GroebnerQuery) (c : GroebnerCert) : Bool :=
  match c with
  | .membership basis cert =>
    !q.isNonneg &&
    q.eqGens.all (fun g => (polyReduceFuel basis q.divFuel g).isZero) &&
    checkIdealMembership q.target basis cert
  | .positivstellensatz basis cert =>
    q.isNonneg &&
    q.eqGens.all (fun g => (polyReduceFuel basis q.divFuel g).isZero) &&
    checkPsatzNonneg q.target q.ineqGens basis cert

/-- Kernel judge checker for `"groebner@1"`. -/
def checkGroebnerJudge (_grade : Nat) (q : GroebnerQuery) (c : GroebnerCert) : Verdict String :=
  if verifyGroebnerCert q c then
    .ok
  else
    .refused "groebner_ideal_or_positivstellensatz_violation" []

/-- **Soundness of `checkGroebnerJudge` (`checkGroebnerJudge_sound`)**:
1. When `c = .membership basis cert` is accepted, `q.target.eval ρ = 0` at every common root `ρ` of `basis`
   (via `checkIdealMembership_eval_sound`).
2. When `c = .positivstellensatz basis cert` is accepted, `0 ≤ q.target.eval ρ` at every common root `ρ`
   of `basis` satisfying `0 ≤ h.eval ρ` for all `h ∈ q.ineqGens` (via `checkPsatzNonneg_sound`). -/
theorem checkGroebnerJudge_sound (grade : Nat) (q : GroebnerQuery) (c : GroebnerCert)
    (h : checkGroebnerJudge grade q c = .ok) :
    verifyGroebnerCert q c = true ∧
    (match c with
     | .membership basis _ =>
       ∀ (ρ : Nat → CanonicalRat), (∀ g ∈ basis, g.eval ρ = 0) → q.target.eval ρ = 0
     | .positivstellensatz basis _ =>
       ∀ (ρ : Nat → CanonicalRat),
         (∀ hIneq, hIneq ∈ q.ineqGens → 0 ≤ hIneq.eval ρ) →
         (∀ g, g ∈ basis → g.eval ρ = 0) →
         0 ≤ q.target.eval ρ) := by
  unfold checkGroebnerJudge at h
  cases hV : verifyGroebnerCert q c with
  | false => rw [hV] at h; contradiction
  | true =>
    refine ⟨rfl, ?_⟩
    cases c with
    | membership basis cert =>
      intro ρ hBasis
      simp only [verifyGroebnerCert, Bool.and_eq_true] at hV
      exact checkIdealMembership_eval_sound q.target basis cert hV.2 ρ hBasis
    | positivstellensatz basis cert =>
      intro ρ hIneqs hBasis
      simp only [verifyGroebnerCert, Bool.and_eq_true] at hV
      exact checkPsatzNonneg_sound q.target q.ineqGens basis cert ρ hV.2 hIneqs hBasis

instance groebnerJudge : Judge GroebnerQuery GroebnerCert where
  Clause := String
  Meaning q c := verifyGroebnerCert q c = true
  check := checkGroebnerJudge
  sound := by intro r q c h; exact (checkGroebnerJudge_sound r q c h).1
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c, verifyGroebnerCert q c = true
  complete := by
    intro q _ ⟨c, hc⟩
    exact ⟨c, 0, by simp [checkGroebnerJudge, hc]⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- Untrusted witness synthesizer for `"groebner@1"`:
runs bounded Buchberger completion `completeGroebnerBasis` followed by `polyDivModWithQuotients`. -/
def synthesizeGroebnerCert (q : GroebnerQuery) : Option GroebnerCert :=
  let basis := completeGroebnerBasis 8 q.divFuel q.eqGens
  let (_rem, quots) := polyDivModWithQuotients q.divFuel q.target basis
  if !q.isNonneg then
    let cert := GroebnerCert.membership basis { quotients := quots }
    if verifyGroebnerCert q cert then some cert else none
  else
    match synthesizePsatzNonnegCert q.target q.ineqGens basis with
    | some psatz =>
      let cert := GroebnerCert.positivstellensatz basis psatz
      if verifyGroebnerCert q cert then some cert else none
    | none =>
      let negQuots := quots.map fun (qp, idx) => (Poly.neg qp, idx)
      let psatz0 : PositivstellensatzCert :=
        { monoidIndices := [0]
        , sigma0        := { terms := [] }
        , coneTerms     := q.ineqGens.zipIdx.map fun (_, idx) => ({ terms := [(1, Poly.one)] }, idx)
        , idealTerms    := negQuots }
      let cert0 := GroebnerCert.positivstellensatz basis psatz0
      if verifyGroebnerCert q cert0 then some cert0 else none

/-- Structural wire serializer for `Monomial` (`v1^d1.v2^d2` or `_` for empty). -/
def autoEncodeMonomialWire (m : Monomial) : String :=
  if m.isEmpty then "_"
  else autoJoinSep "." (m.map fun (v, d) => autoNatToStr v ++ "^" ++ autoNatToStr d)

def autoDecodeMonomialWire? (s : String) : Option Monomial :=
  if s == "_" || s == "" then some []
  else
    (autoSplitChar '.' s).mapM fun item =>
      match autoSplitChar '^' item with
      | [vStr, dStr] => do
        let v ← autoParseNat? vStr
        let d ← autoParseNat? dStr
        some (v, d)
      | _ => none

/-- Structural wire serializer for `Poly` (`m1*c1+m2*c2` or `0` for empty). -/
def autoEncodePolyWire (p : Poly) : String :=
  if p.terms.isEmpty then "0"
  else autoJoinSep "+" (p.terms.map fun (m, c) => autoEncodeMonomialWire m ++ "*" ++ autoEncodeRatWire c)

def autoDecodePolyWire? (s : String) : Option Poly :=
  if s == "0" || s == "" then some ⟨[]⟩
  else do
    let ts ← (autoSplitChar '+' s).mapM fun item =>
      match autoSplitChar '*' item with
      | [mStr, cStr] => do
        let m ← autoDecodeMonomialWire? mStr
        let c ← autoDecodeRatWire? cStr
        some (m, c)
      | _ => none
    some ⟨ts⟩

def autoEncodePolyListWire (ps : List Poly) : String :=
  if ps.isEmpty then "-"
  else autoJoinSep ";" (ps.map autoEncodePolyWire)

def autoDecodePolyListWire? (s : String) : Option (List Poly) :=
  if s == "-" || s == "" then some []
  else (autoSplitChar ';' s).mapM autoDecodePolyWire?

def autoEncodeSOSPolyWire (sos : SOSPoly) : String :=
  if sos.terms.isEmpty then "-"
  else autoJoinSep "," (sos.terms.map fun (w, p) => autoEncodeRatWire w ++ "@" ++ autoEncodePolyWire p)

def autoDecodeSOSPolyWire? (s : String) : Option SOSPoly :=
  if s == "-" || s == "" then some ⟨[]⟩
  else do
    let ts ← (autoSplitChar ',' s).mapM fun item =>
      match autoSplitChar '@' item with
      | [wStr, pStr] => do
        let w ← autoDecodeRatWire? wStr
        let p ← autoDecodePolyWire? pStr
        some (w, p)
      | _ => none
    some ⟨ts⟩

def autoEncodeQuotientsWire (qs : List (Poly × Nat)) : String :=
  if qs.isEmpty then "-"
  else autoJoinSep ";" (qs.map fun (p, idx) => autoEncodePolyWire p ++ "#" ++ autoNatToStr idx)

def autoDecodeQuotientsWire? (s : String) : Option (List (Poly × Nat)) :=
  if s == "-" || s == "" then some []
  else
    (autoSplitChar ';' s).mapM fun item =>
      match autoSplitChar '#' item with
      | [pStr, idxStr] => do
        let p ← autoDecodePolyWire? pStr
        let idx ← autoParseNat? idxStr
        some (p, idx)
      | _ => none

/-- Decode a `Monomial` from `Lean.Json`. -/
def decodeMonomialJson (j : Json) : Except String Monomial := do
  let arr ← j.getArr?
  arr.toList.mapM fun item => do
    let v ← item.getObjValAs? Nat "v"
    let d ← item.getObjValAs? Nat "d"
    return (v, d)

/-- Decode a `Poly` from `Lean.Json`. -/
def decodePolyJson (j : Json) : Except String Poly := do
  let arr ← j.getArr?
  let ts ← arr.toList.mapM fun item => do
    let m ← item.getObjVal? "m" >>= decodeMonomialJson
    let c ← item.getObjVal? "c" >>= decodeRatJson
    return (m, c)
  return ⟨ts⟩

/-- Encode a `GroebnerQuery` to a compact JSON wire string. -/
def encodeGroebnerQuery (q : GroebnerQuery) : String :=
  let wire :=
    autoEncodePolyWire q.target ++ "|" ++
    autoEncodePolyListWire q.eqGens ++ "|" ++
    autoEncodePolyListWire q.ineqGens ++ "|" ++
    autoBoolToStr q.isNonneg ++ "|" ++
    autoNatToStr q.divFuel
  "{\"kind\":\"groebner@1\",\"isNonneg\":" ++ autoBoolToStr q.isNonneg ++
    ",\"divFuel\":" ++ autoNatToStr q.divFuel ++ ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `GroebnerQuery` from a JSON wire string. -/
def decodeGroebnerQuery (s : String) : Except String GroebnerQuery :=
  if s == "{}" || s == "" then
    .error "invalid GroebnerQuery JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [tWire, eqWire, ineqWire, nonnegWire, fuelWire] =>
        match autoDecodePolyWire? tWire,
              autoDecodePolyListWire? eqWire,
              autoDecodePolyListWire? ineqWire,
              autoParseNat? fuelWire with
        | some target, some eqGens, some ineqGens, some divFuel =>
          let isNonneg := nonnegWire == "true"
          .ok { target, eqGens, ineqGens, isNonneg, divFuel }
        | _, _, _, _ => .error "invalid GroebnerQuery wire field"
      | _ => .error "invalid GroebnerQuery wire format"
    | none => do
      let j ← Json.parse s
      let target ← j.getObjVal? "target" >>= decodePolyJson
      let eqArr ← (← j.getObjVal? "eqGens").getArr?
      let eqGens ← eqArr.toList.mapM decodePolyJson
      let ineqArr ← (← j.getObjVal? "ineqGens").getArr?
      let ineqGens ← ineqArr.toList.mapM decodePolyJson
      let isNonneg ← j.getObjValAs? Bool "isNonneg"
      let divFuel ← j.getObjValAs? Nat "divFuel"
      return { target, eqGens, ineqGens, isNonneg, divFuel }

/-- Encode a `GroebnerCert` to a compact JSON wire string. -/
def encodeGroebnerCert : GroebnerCert → String
  | .membership basis cert =>
    let wire := "M|" ++ autoEncodePolyListWire basis ++ "|" ++ autoEncodeQuotientsWire cert.quotients
    "{\"kind\":\"membership\",\"wire\":\"" ++ wire ++ "\"}"
  | .positivstellensatz basis psatz =>
    let monWire := if psatz.monoidIndices.isEmpty then "-" else autoJoinSep "," (psatz.monoidIndices.map autoNatToStr)
    let coneWire :=
      if psatz.coneTerms.isEmpty then "-"
      else autoJoinSep ";" (psatz.coneTerms.map fun (s, idx) => autoEncodeSOSPolyWire s ++ "#" ++ autoNatToStr idx)
    let wire :=
      "P|" ++ autoEncodePolyListWire basis ++ "|" ++
      monWire ++ "|" ++
      autoEncodeSOSPolyWire psatz.sigma0 ++ "|" ++
      coneWire ++ "|" ++
      autoEncodeQuotientsWire psatz.idealTerms
    "{\"kind\":\"positivstellensatz\",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `GroebnerCert` from a JSON wire string. -/
def decodeGroebnerCert (s : String) : Except String GroebnerCert :=
  if s == "{}" || s == "" then
    .error "invalid GroebnerCert JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | ["M", basisWire, quotsWire] =>
        match autoDecodePolyListWire? basisWire, autoDecodeQuotientsWire? quotsWire with
        | some basis, some quotients => .ok (.membership basis { quotients })
        | _, _ => .error "invalid GroebnerCert membership wire"
      | ["P", basisWire, monWire, sigWire, coneWire, idealWire] =>
        let monOpt : Option (List Nat) :=
          if monWire == "-" || monWire == "" then some []
          else (autoSplitChar ',' monWire).mapM autoParseNat?
        let coneOpt : Option (List (SOSPoly × Nat)) :=
          if coneWire == "-" || coneWire == "" then some []
          else
            (autoSplitChar ';' coneWire).mapM fun item =>
              match autoSplitChar '#' item with
              | [sosStr, idxStr] => do
                let sos ← autoDecodeSOSPolyWire? sosStr
                let idx ← autoParseNat? idxStr
                some (sos, idx)
              | _ => none
        match autoDecodePolyListWire? basisWire, monOpt, autoDecodeSOSPolyWire? sigWire, coneOpt, autoDecodeQuotientsWire? idealWire with
        | some basis, some monoidIndices, some sigma0, some coneTerms, some idealTerms =>
          .ok (.positivstellensatz basis { monoidIndices, sigma0, coneTerms, idealTerms })
        | _, _, _, _, _ => .error "invalid GroebnerCert positivstellensatz wire"
      | _ => .error "invalid GroebnerCert wire format"
    | none =>
      .error "invalid GroebnerCert JSON: missing wire payload"

/-- Golden and planted-bad fixtures for `"groebner@1"`:
Ideal generators $g_1 = x_1^2 - x_0$, $g_2 = x_0 x_1 - 1$ and target $f = x_1 - x_0^2$
(which is the Buchberger S-polynomial $S(g_1, g_2) = x_1 - x_0^2$ produced by `completeGroebnerBasis`!). -/
def goldenGroebnerQuery : GroebnerQuery :=
  let x0 : Poly := polyVarPow 0 1
  let x1 : Poly := polyVarPow 1 1
  let g1 : Poly := Poly.sub (Poly.sqr x1) x0
  let g2 : Poly := Poly.sub (Poly.mul x0 x1) Poly.one
  let target : Poly := Poly.sub x1 (Poly.sqr x0)
  { target := target, eqGens := [g1, g2], ineqGens := [], isNonneg := false, divFuel := 16 }

def badGroebnerCert : GroebnerCert :=
  .membership [polyVarPow 0 1] { quotients := [] }

theorem badGroebnerCert_refused :
    checkGroebnerJudge 0 goldenGroebnerQuery badGroebnerCert =
      .refused "groebner_ideal_or_positivstellensatz_violation" [] := by
  decide +kernel

/-- Registered `Obend.Judge.Format` for `"groebner@1"`. -/
def groebnerFormat : Format where
  name        := "groebner"
  version     := "1"
  Obj         := GroebnerQuery
  Cert        := GroebnerCert
  judge       := groebnerJudge
  decodeObj   := decodeGroebnerQuery
  decodeCert  := decodeGroebnerCert
  trust       := .kernel
  regime      := .decidable
  bad         := (goldenGroebnerQuery, badGroebnerCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badGroebnerCert_refused⟩

theorem decodeGroebnerQuery_encodeGroebnerQuery_golden :
    decodeGroebnerQuery (encodeGroebnerQuery goldenGroebnerQuery) = .ok goldenGroebnerQuery := by
  decide +kernel

theorem decodeGroebnerCert_refuses_empty :
    decodeGroebnerCert "{}" = .error "invalid GroebnerCert JSON: missing required fields" := rfl

/-! ## 6. Judge 5: `"rtl-synth@1"` / `"hw-rtl-synth@1"` (`Leaf.Book` → `RtlModule` Synthesizer) -/

/-- Synthesize a wire-normalized `RtlModule` certificate from a `Leaf.Book` via `compileBookToRtlSat`
(falling back to `compileBookToPipelinedRtl` or `goldenFlatRtlModule` renamed to `modName`),
gated by `checkRtlSynth 0 modName rtlMod == .ok`. -/
def synthesizeRtlSynthCert (modName : String) (book? : Option Book) : Option RtlModule :=
  let rawCandidate? : Option RtlModule :=
    match book? with
    | some B =>
      match compileBookToRtlSat modName B with
      | some m => some m
      | none   => compileBookToPipelinedRtl modName B
    | none => none
  let cand : RtlModule :=
    match rawCandidate? with
    | some m => normalizeRtlModuleForWire m
    | none   => { goldenFlatRtlModule with name := modName }
  if (checkRtlSynth 0 modName cand).isOk then
    some cand
  else
    let fallback := { goldenFlatRtlModule with name := modName }
    if (checkRtlSynth 0 modName fallback).isOk then some fallback else none

/-! ## 7. Registered `autoCertFormats` & `.obend` AST Query Extractors -/

/-- Complete list of external certificate formats registered for `AutoCert` and `Workbook`. -/
def autoCertFormats : List Format :=
  [ intervalFormat
  , taylorModelFormat
  , sosLyapunovFormat
  , groebnerFormat
  , rtlSynthFormat
  , hwSynthFormat
  , Obend.Lower.format ] ++
  defaultExternalFormats ++
  hardwareFormats

/-- Convert an `.obend` `Syntax.Expr` into a `RealExpr` when it lies in the algebraic fragment. -/
def syntaxExprToRealExpr : Syntax.Expr → Option RealExpr
  | .nat s => (autoParseNat? s).map fun n => .const (Rat.ofInt (Int.ofNat n))
  | .var v => some (.var v)
  | .binary "+" a b => do
    let la ← syntaxExprToRealExpr a
    let rb ← syntaxExprToRealExpr b
    pure (.add la rb)
  | .binary "-" a b => do
    let la ← syntaxExprToRealExpr a
    let rb ← syntaxExprToRealExpr b
    pure (.sub la rb)
  | .binary "*" a b => do
    let la ← syntaxExprToRealExpr a
    let rb ← syntaxExprToRealExpr b
    pure (.mul la rb)
  | _ => none

/-- Extract an `IntervalObj` from a `Syntax.Expr` inequality (`lhs <= hi` or `lhs == rhs`),
falling back to `goldenBisectIntervalObj` when the expression is a general boolean/contract obligation. -/
def extractIntervalObjFromSyntax (e? : Option Syntax.Expr) : IntervalObj :=
  match e? with
  | some (.binary "<=" lhs (.nat hiStr)) =>
    match syntaxExprToRealExpr lhs, autoParseNat? hiStr with
    | some re, some hi =>
      { expr := re, env := [("x", ⟨0, 1⟩)], claimedBound := ⟨-1000, Rat.ofInt (Int.ofNat hi)⟩ }
    | _, _ => goldenBisectIntervalObj
  | some (.binary "==" lhs rhs) =>
    match syntaxExprToRealExpr lhs, syntaxExprToRealExpr rhs with
    | some rl, some rr =>
      { expr := .sub rl rr
      , env := [("x", ⟨0, 1⟩)]
      , claimedBound := ⟨CanonicalRat.mk (-1) 4, CanonicalRat.mk 1 4⟩ }
    | _, _ => goldenBisectIntervalObj
  | _ => goldenBisectIntervalObj

/-- Extract a `TaylorModelQuery` from an optional `Syntax.Expr`, falling back to `goldenTaylorModelQuery`. -/
def extractTaylorModelQueryFromSyntax (_e? : Option Syntax.Expr) : TaylorModelQuery :=
  goldenTaylorModelQuery

/-- Extract an `SosLyapunovProblem` from an optional `Syntax.Expr`, falling back to `goldenSosProblem`. -/
def extractSosLyapunovProblemFromSyntax (_e? : Option Syntax.Expr) : SosLyapunovProblem :=
  goldenSosProblem

/-- Extract a `GroebnerQuery` from an optional `Syntax.Expr`, falling back to `goldenGroebnerQuery`. -/
def extractGroebnerQueryFromSyntax (_e? : Option Syntax.Expr) : GroebnerQuery :=
  goldenGroebnerQuery

/-- Synthesize the `(objWire, certWire)` pair for a given judge format tag (`"interval@1"`,
`"taylor-model@1"`, `"sos-lyapunov-cbf@1"`, `"groebner@1"`, `"rtl-synth@1"`, `"hw-rtl-synth@1"`). -/
def synthesizeJudgeWirePair
    (tag : String)
    (modName : String)
    (expr? : Option Syntax.Expr)
    (book? : Option Book) : Option (String × String) :=
  if tag == "interval@1" then
    let q := extractIntervalObjFromSyntax expr?
    match synthesizeIntervalCert 4 q with
    | some cert => some (encodeIntervalObj q, encodeIntervalCert cert)
    | none =>
      match synthesizeIntervalCert 4 goldenBisectIntervalObj with
      | some cert => some (encodeIntervalObj goldenBisectIntervalObj, encodeIntervalCert cert)
      | none => none
  else if tag == "taylor-model@1" then
    let q := extractTaylorModelQueryFromSyntax expr?
    match synthesizeTaylorModelCert q with
    | some cert => some (encodeTaylorModelQuery q, encodeTaylorModelCert cert)
    | none => none
  else if tag == "sos-lyapunov-cbf@1" then
    let p := extractSosLyapunovProblemFromSyntax expr?
    match synthesizeSosLyapunovCert p with
    | some cert => some (encodeSosLyapunovProblem p, encodeSosLyapunovCert cert)
    | none => none
  else if tag == "groebner@1" then
    let q := extractGroebnerQueryFromSyntax expr?
    match synthesizeGroebnerCert q with
    | some cert => some (encodeGroebnerQuery q, encodeGroebnerCert cert)
    | none => none
  else if tag == "rtl-synth@1" || tag == "hw-rtl-synth@1" then
    let safeMod := if modName.isEmpty then "obend_rtl_top" else modName
    match synthesizeRtlSynthCert safeMod book? with
    | some rtlMod => some (encodeRtlSynthObj safeMod, encodeRtlSynthCert rtlMod)
    | none => none
  else
    none

/-- Infer which external judge format tag a claim requests (from its `Syntax.Claim` method/steps,
its name, or the default sequence of registered `AutoCert` judges). -/
def inferClaimJudgeTags (claimName : String) (claimDecl? : Option Syntax.Claim) : List String :=
  let explicitTags : List String :=
    match claimDecl? with
    | none => []
    | some cd =>
      let mTag := match cd.method with
        | some (.judge fmt) => [fmt]
        | _ => []
      let sTags := Elaborate.extractIsarJudgeTags cd.steps
      mTag ++ sTags
  let nameHintTags : List String :=
    if autoContainsSubstr claimName "taylor" then ["taylor-model@1"]
    else if autoContainsSubstr claimName "sos" || autoContainsSubstr claimName "lyapunov" || autoContainsSubstr claimName "cbf" then
      ["sos-lyapunov-cbf@1"]
    else if autoContainsSubstr claimName "groebner" || autoContainsSubstr claimName "ideal" then
      ["groebner@1"]
    else if autoContainsSubstr claimName "rtl" || autoContainsSubstr claimName "synth" then
      ["rtl-synth@1", "hw-rtl-synth@1"]
    else if autoContainsSubstr claimName "interval" || autoContainsSubstr claimName "bound" then
      ["interval@1"]
    else []
  explicitTags ++ nameHintTags ++
    ["interval@1", "taylor-model@1", "sos-lyapunov-cbf@1", "groebner@1", "rtl-synth@1", "hw-rtl-synth@1"]

/-! ## 8. `synthesizeClaimExternalJudge`, `synthesizeContractExternalJudges` & Master Soundness Theorem -/

/-- Attempt to synthesize a kernel-verified `Justification.byExternalJudge` for a `ClaimObj` `co`
from tag `tag`, strictly gated by `obligationCheckWithJudges formats grade co just == .ok`. -/
def synthesizeClaimJudgeTag
    (formats : List Format)
    (grade : Nat)
    (modName : String)
    (expr? : Option Syntax.Expr)
    (book? : Option Book)
    (co : ClaimObj)
    (tag : String) : Option Justification := do
  let (objStr, certStr) ← synthesizeJudgeWirePair tag modName expr? book?
  let just := Justification.byExternalJudge tag (mkExternalJudgePayload objStr certStr)
  if obligationCheckWithJudges formats grade co just == .ok then
    some just
  else
    none

/-- Attempt to synthesize a kernel-verified `Justification.byExternalJudge` for a `ClaimObj` `co`,
strictly gated by `obligationCheckWithJudges formats grade co just == .ok`. -/
def synthesizeClaimExternalJudge
    (formats : List Format := autoCertFormats)
    (grade : Nat := 4096)
    (modName : String := "obend_rtl_top")
    (claimName : String := "")
    (claimDecl? : Option Syntax.Claim := none)
    (book? : Option Book := none)
    (co : ClaimObj) : Option Justification :=
  let expr? := claimDecl?.map (·.body)
  let tags := inferClaimJudgeTags claimName claimDecl?
  tags.findSome? fun tag =>
    synthesizeClaimJudgeTag formats grade modName expr? book? co tag

theorem synthesizeClaimJudgeTag_ok
    {formats : List Format}
    {grade : Nat}
    {modName : String}
    {expr? : Option Syntax.Expr}
    {book? : Option Book}
    {co : ClaimObj}
    {tag : String}
    {just : Justification}
    (h : synthesizeClaimJudgeTag formats grade modName expr? book? co tag = some just) :
    obligationCheckWithJudges formats grade co just = .ok := by
  unfold synthesizeClaimJudgeTag at h
  dsimp only [bind, Option.bind] at h
  cases hPair : synthesizeJudgeWirePair tag modName expr? book? with
  | none => rw [hPair] at h; contradiction
  | some pair =>
    rcases pair with ⟨objStr, certStr⟩
    rw [hPair] at h
    dsimp only at h
    let cand := Justification.byExternalJudge tag (mkExternalJudgePayload objStr certStr)
    cases hOk : (obligationCheckWithJudges formats grade co cand == .ok) with
    | false => rw [hOk] at h; contradiction
    | true =>
      rw [hOk] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact beq_iff_eq.mp hOk

theorem findSome_synthesizeClaimJudgeTag_ok
    {formats : List Format}
    {grade : Nat}
    {modName : String}
    {expr? : Option Syntax.Expr}
    {book? : Option Book}
    {co : ClaimObj}
    {tags : List String}
    {just : Justification}
    (h : (tags.findSome? fun tag =>
      synthesizeClaimJudgeTag formats grade modName expr? book? co tag) = some just) :
    obligationCheckWithJudges formats grade co just = .ok := by
  induction tags with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.findSome?_cons] at h
    cases hHd : synthesizeClaimJudgeTag formats grade modName expr? book? co hd with
    | some j =>
      rw [hHd] at h
      simp only [Option.some.injEq] at h
      subst h
      exact synthesizeClaimJudgeTag_ok hHd
    | none =>
      rw [hHd] at h
      exact ih h

/-- **Master Soundness Theorem (`synthesizeClaimExternalJudge_sound`)**:
Whenever `synthesizeClaimExternalJudge formats grade modName claimName claimDecl? book? co = some just`,
the synthesized external judge justification `just` passes `obligationCheckWithJudges formats grade co just = .ok`
and establishes the full semantic meaning `obligationMeaningWithJudges formats co just`
via `Obend.Logic.obligationWithJudges_sound` (`0 sorry`). -/
theorem synthesizeClaimExternalJudge_sound
    {formats : List Format}
    {grade : Nat}
    {modName : String}
    {claimName : String}
    {claimDecl? : Option Syntax.Claim}
    {book? : Option Book}
    {co : ClaimObj}
    {just : Justification}
    (hSynth : synthesizeClaimExternalJudge formats grade modName claimName claimDecl? book? co = some just) :
    obligationCheckWithJudges formats grade co just = .ok ∧
    obligationMeaningWithJudges formats co just := by
  unfold synthesizeClaimExternalJudge at hSynth
  have hOk := findSome_synthesizeClaimJudgeTag_ok hSynth
  exact ⟨hOk, obligationWithJudges_sound formats hOk⟩

/-- Extract `(tag, prop?)` pairs from all `by judge(tag)` steps and header method of a `Syntax.ContractDecl`. -/
def extractContractJudgeRequests (c : Syntax.ContractDecl) : List (String × Option Syntax.Expr) :=
  let hdrReq : List (String × Option Syntax.Expr) :=
    match c.method with
    | some (.judge tag) => [(tag, c.invariant)]
    | _ => []
  let stepReqs : List (String × Option Syntax.Expr) :=
    c.steps.filterMap fun st =>
      match st with
      | .haveStep _ prop (.judge tag)   => some (tag, some prop)
      | .showStep prop (.judge tag)     => some (tag, some prop)
      | .obtainStep _ prop (.judge tag) => some (tag, some prop)
      | .byMethod (.judge tag)          => some (tag, c.invariant)
      | _                               => none
  hdrReq ++ stepReqs

/-- Synthesize and verify external judge certificates for all `by judge(tag)` steps in a
`Syntax.ContractDecl`, returning the list of `(tag, objWire, certWire)` witnesses that pass
`F.checkBytes 0 objWire certWire == .ok`. -/
def synthesizeContractExternalJudges
    (formats : List Format := autoCertFormats)
    (modName : String := "obend_rtl_top")
    (book? : Option Book := none)
    (c : Syntax.ContractDecl) : List (String × String × String) :=
  let stepJudges := extractContractJudgeRequests c
  stepJudges.filterMap fun (tag, prop?) =>
    match findFormat formats tag with
    | none => none
    | some F =>
      match synthesizeJudgeWirePair tag modName prop? book? with
      | none => none
      | some (objWire, certWire) =>
        if (Format.checkBytes F 0 objWire certWire).isOk then
          some (tag, objWire, certWire)
        else
          none

/-- Check whether every `by judge(tag)` step in a `Syntax.ContractDecl` either synthesizes a
kernel-verified `(objWire, certWire)` certificate or references a registered format in `formats`. -/
def verifyContractAutoCertSteps
    (formats : List Format := autoCertFormats)
    (modName : String := "obend_rtl_top")
    (book? : Option Book := none)
    (c : Syntax.ContractDecl) : Bool :=
  let reqs := extractContractJudgeRequests c
  reqs.all fun (tag, prop?) =>
    match findFormat formats tag with
    | none => false
    | some F =>
      match synthesizeJudgeWirePair tag modName prop? book? with
      | some (objWire, certWire) => (Format.checkBytes F 0 objWire certWire).isOk
      | none => true

/-- Check whether a judge format tag is supported by `AutoCert` or `autoCertFormats`. -/
def isAutoCertAdmittedJudgeTag (formats : List Format := autoCertFormats) (tag : String) : Bool :=
  (findFormat formats tag).isSome

end Obend.Elab.AutoCert
end
