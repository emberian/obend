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
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.RealAnalysis
public import Obend.Analysis.Flowpipe
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.Groebner
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Judge
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Logic.Obligation
public import Obend.Lower.Judge
public import Obend.Spec.Syntax
public import Obend.Spec.Elaborate

public section

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
open Obend.Core.Term (Term)

set_option autoImplicit false

/-! ## 1. Kernel-Reducible Structural String/Wire Helpers & JSON Helpers -/

/-- Fuel-bounded structural `Nat → List Char` decimal conversion (100% `@[expose]`). -/
@[expose] def natToCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc => if acc.isEmpty then ['0'] else acc
  | fuel + 1, n, acc =>
    let d := Char.ofNat (48 + (n % 10))
    let q := n / 10
    if q == 0 then d :: acc
    else natToCharsFuel fuel q (d :: acc)

/-- Structural `Nat → String` conversion (kernel-reducible by `rfl` in `module` mode). -/
@[expose] def autoNatToStr (n : Nat) : String :=
  String.ofList (natToCharsFuel 32 n [])

/-- Structural `Int → String` conversion (kernel-reducible by `rfl` in `module` mode). -/
@[expose] def autoIntToStr (i : Int) : String :=
  match i with
  | .ofNat n   => autoNatToStr n
  | .negSucc n => "-" ++ autoNatToStr (n + 1)

/-- Structural `Bool → String` conversion. -/
@[expose] def autoBoolToStr (b : Bool) : String :=
  if b then "true" else "false"

/-- Structural list join with a custom separator `sep`. -/
@[expose] def autoJoinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ autoJoinSep sep xs

/-- Structural single-character string splitter (100% `@[expose]`, avoids `String.splitOn`). -/
@[expose] def autoSplitCharAux (sep : Char) : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c == sep then
      String.ofList cur.reverse :: autoSplitCharAux sep cs []
    else
      autoSplitCharAux sep cs (c :: cur)

@[expose] def autoSplitChar (sep : Char) (s : String) : List String :=
  autoSplitCharAux sep s.toList []

@[expose] def autoStartsWithChars : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | c :: cs, p :: ps => (c == p) && autoStartsWithChars cs ps

@[expose] def autoContainsChars (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => autoStartsWithChars (c :: cs) needle || autoContainsChars needle cs

/-- Structural substring check (`100% @[expose]`, avoids `String.splitOn`). -/
@[expose] def autoContainsSubstr (haystack needle : String) : Bool :=
  autoContainsChars needle.toList haystack.toList

/-- Parse a `Nat` from a `List Char` structurally. -/
@[expose] def autoParseNatChars : List Char → Nat → Bool → Option Nat
  | [], acc, true => some acc
  | [], _, false => none
  | c :: cs, acc, _ =>
    if '0' ≤ c && c ≤ '9' then
      autoParseNatChars cs (acc * 10 + (c.toNat - '0'.toNat)) true
    else
      none

/-- Parse a `Nat` from a decimal string structurally. -/
@[expose] def autoParseNat? (s : String) : Option Nat :=
  autoParseNatChars s.toList 0 false

/-- Parse an `Int` from a decimal string structurally. -/
@[expose] def autoParseInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (autoParseNatChars cs 0 false).map fun n => -(Int.ofNat n)
  | cs        => (autoParseNatChars cs 0 false).map Int.ofNat

/-- Parse a `CanonicalRat` from `"num/den"` or `"num"`. -/
@[expose] def autoEncodeRatWire (q : CanonicalRat) : String :=
  autoIntToStr q.num ++ "/" ++ autoNatToStr q.den

@[expose] def autoDecodeRatWire? (s : String) : Option CanonicalRat :=
  match autoSplitChar '/' s with
  | [nStr, dStr] => do
    let n ← autoParseInt? nStr
    let d ← autoParseNat? dStr
    if d == 0 then none else some (CanonicalRat.mk n d)
  | [nStr] => do
    let n ← autoParseInt? nStr
    some (Rat.ofInt n)
  | _ => none

@[expose] def autoEncodeIntervalWire (iv : Interval) : String :=
  autoEncodeRatWire iv.lo ++ ":" ++ autoEncodeRatWire iv.hi

@[expose] def autoDecodeIntervalWire? (s : String) : Option Interval :=
  match autoSplitChar ':' s with
  | [loStr, hiStr] => do
    let lo ← autoDecodeRatWire? loStr
    let hi ← autoDecodeRatWire? hiStr
    some ⟨lo, hi⟩
  | _ => none

/-- Scan `autoSplitChar '"' raw` for `"key"` followed by `":"` and return the quoted value. -/
@[expose] def findQuotedJsonFieldAux (key : String) : List String → Option String
  | k :: sep :: val :: rest =>
    if k == key && sep == ":" then
      some val
    else
      findQuotedJsonFieldAux key (sep :: val :: rest)
  | _ => none

/-- Extract a string field `"\"<key>\":\""` ... `"\""` from a compact JSON object structurally. -/
@[expose] def extractJsonStringField? (key : String) (raw : String) : Option String :=
  findQuotedJsonFieldAux key (autoSplitChar '"' raw)

/-- Encode a `CanonicalRat` as a compact JSON object string `{"num":n,"den":d}`. -/
@[expose] def encodeRatJsonStr (q : CanonicalRat) : String :=
  "{\"num\":" ++ autoIntToStr q.num ++ ",\"den\":" ++ autoNatToStr q.den ++ "}"

/-- Encode an `Interval` as a compact JSON object string `{"lo":...,"hi":...}`. -/
@[expose] def encodeIntervalJsonStr (iv : Interval) : String :=
  "{\"lo\":" ++ encodeRatJsonStr iv.lo ++ ",\"hi\":" ++ encodeRatJsonStr iv.hi ++ "}"

/-- Encode a `CanonicalRat` as a `Lean.Json` object `{"num": n, "den": d}`. -/
@[expose] def encodeRatJson (q : CanonicalRat) : Json :=
  Json.mkObj [("num", toJson q.num), ("den", toJson q.den)]

/-- Decode a `CanonicalRat` from a `Lean.Json` object `{"num": n, "den": d}` or integer literal. -/
@[expose] def decodeRatJson (j : Json) : Except String CanonicalRat :=
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
@[expose] def encodeIntervalJson (iv : Interval) : Json :=
  Json.mkObj [("lo", encodeRatJson iv.lo), ("hi", encodeRatJson iv.hi)]

/-- Decode an `Interval` from a `Lean.Json` object `{"lo": ..., "hi": ...}`. -/
@[expose] def decodeIntervalJson (j : Json) : Except String Interval := do
  let loJson ← j.getObjVal? "lo"
  let hiJson ← j.getObjVal? "hi"
  let lo ← decodeRatJson loJson
  let hi ← decodeRatJson hiJson
  return ⟨lo, hi⟩

/-- Decode a variable box `List (String × Interval)` from a `Lean.Json` array. -/
@[expose] def decodeIntervalEnvJson (j : Json) : Except String (List (String × Interval)) := do
  let arr ← j.getArr?
  arr.toList.mapM fun item => do
    let v ← item.getObjValAs? String "var"
    let ivJson ← item.getObjVal? "iv"
    let iv ← decodeIntervalJson ivJson
    return (v, iv)

/-- Fuel-bounded decoder for `RealExpr` from `Lean.Json`. -/
@[expose] def decodeRealExprJsonAux : Nat → Json → Except String RealExpr
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

@[expose] def decodeRealExprJson (j : Json) : Except String RealExpr :=
  decodeRealExprJsonAux 64 j

/-! ## 2. Judge 1: `"interval@1"` (`IntervalObj`, `IntervalCert` with Bisection, `intervalFormat`) -/

/-- Object for `"interval@1"`: arithmetic expression, variable interval box, and claimed target bound. -/
structure IntervalObj where
  expr         : RealExpr
  env          : List (String × Interval)
  claimedBound : Interval
  deriving @[expose] DecidableEq, Repr

/-- Convert `IntervalObj` to `Obend.Judge.IntervalQuery`. -/
@[expose] def IntervalObj.toQuery (o : IntervalObj) : IntervalQuery :=
  { expr := o.expr, env := o.env, claimedBound := o.claimedBound }

/-- Convert `Obend.Judge.IntervalQuery` to `IntervalObj`. -/
@[expose] def IntervalObj.ofQuery (q : IntervalQuery) : IntervalObj :=
  { expr := q.expr, env := q.env, claimedBound := q.claimedBound }

/-- Certificate for `"interval@1"`, supporting direct interval evaluation, recursive variable-box
bisection, and counterexample refutation points. -/
inductive IntervalCert where
  | direct
  | bisect (varName : String) (left right : IntervalCert)
  | counterexample (point : List (String × CanonicalRat))
  deriving @[expose] DecidableEq, Repr

/-- Update the first binding for `varName` in `env` to `newIv`. -/
@[expose] def replaceVarInterval (varName : String) (newIv : Interval) :
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
@[expose] def checkIntervalAutoCert (q : IntervalObj) : IntervalCert → Verdict IntervalClause
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

@[expose] instance intervalAutoJudge : Judge IntervalObj IntervalCert where
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
@[expose] def widestIntervalVar? : List (String × Interval) → Option (String × Interval)
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
@[expose] def synthesizeIntervalCert : Nat → IntervalObj → Option IntervalCert
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
@[expose] def encodeRealExprTokens : RealExpr → List String
  | .const q  => ["C", autoEncodeRatWire q]
  | .var name => ["V", name]
  | .add a b  => "A" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .sub a b  => "S" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .mul a b  => "M" :: (encodeRealExprTokens a ++ encodeRealExprTokens b)
  | .sqr a    => "Q" :: encodeRealExprTokens a

@[expose] def decodeRealExprTokens : Nat → List String → Option (RealExpr × List String)
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

@[expose] def encodeIntervalEnvWire (env : List (String × Interval)) : String :=
  if env.isEmpty then "-"
  else autoJoinSep "," (env.map fun (v, iv) => v ++ "=" ++ autoEncodeIntervalWire iv)

@[expose] def decodeIntervalEnvWire? (s : String) : Option (List (String × Interval)) :=
  if s == "-" || s == "" then some []
  else
    (autoSplitChar ',' s).mapM fun item =>
      match autoSplitChar '=' item with
      | [v, ivStr] => do
        let iv ← autoDecodeIntervalWire? ivStr
        some (v, iv)
      | _ => none

/-- Encode an `IntervalObj` to a compact JSON wire string. -/
@[expose] def encodeIntervalObj (o : IntervalObj) : String :=
  let exprWire := autoJoinSep "~" (encodeRealExprTokens o.expr)
  let envWire  := encodeIntervalEnvWire o.env
  let bndWire  := autoEncodeIntervalWire o.claimedBound
  let wire := exprWire ++ "|" ++ envWire ++ "|" ++ bndWire
  "{\"kind\":\"interval@1\",\"claimedBound\":" ++ encodeIntervalJsonStr o.claimedBound ++
    ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode an `IntervalObj` from a JSON wire string. -/
@[expose] def decodeIntervalObj (s : String) : Except String IntervalObj :=
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
@[expose] def encodeIntervalCertTokens : IntervalCert → List String
  | .direct => ["D"]
  | .bisect v l r => ["B", v] ++ encodeIntervalCertTokens l ++ encodeIntervalCertTokens r
  | .counterexample pt =>
    let ptStr := if pt.isEmpty then "-" else autoJoinSep "," (pt.map fun (v, q) => v ++ "=" ++ autoEncodeRatWire q)
    ["X", ptStr]

@[expose] def decodeIntervalCertTokens : Nat → List String → Option (IntervalCert × List String)
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
@[expose] def decodeIntervalCertJsonAux : Nat → Json → Except String IntervalCert
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
@[expose] def encodeIntervalCert (c : IntervalCert) : String :=
  let kindStr := match c with
    | .direct => "direct"
    | .bisect .. => "bisect"
    | .counterexample .. => "counterexample"
  let wire := autoJoinSep "~" (encodeIntervalCertTokens c)
  "{\"kind\":\"" ++ kindStr ++ "\",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode an `IntervalCert` from a JSON wire string. -/
@[expose] def decodeIntervalCert (s : String) : Except String IntervalCert :=
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

/-- Accumulator for `given` interval bounds `(varName, hasLo, lo, hasHi, hi)`. -/
abbrev GivenBoundAcc := List (String × Bool × CanonicalRat × Bool × CanonicalRat)

@[expose] def updateGivenLower (v : String) (c : CanonicalRat) : GivenBoundAcc → GivenBoundAcc
  | [] => [(v, true, c, false, 0)]
  | (w, hasLo, lo, hasHi, hi) :: rest =>
    if w == v then
      let lo' := if hasLo then (if decide (lo ≤ c) then c else lo) else c
      (w, true, lo', hasHi, hi) :: rest
    else
      (w, hasLo, lo, hasHi, hi) :: updateGivenLower v c rest

@[expose] def updateGivenUpper (v : String) (c : CanonicalRat) : GivenBoundAcc → GivenBoundAcc
  | [] => [(v, false, 0, true, c)]
  | (w, hasLo, lo, hasHi, hi) :: rest =>
    if w == v then
      let hi' := if hasHi then (if decide (c ≤ hi) then c else hi) else c
      (w, hasLo, lo, true, hi') :: rest
    else
      (w, hasLo, lo, hasHi, hi) :: updateGivenUpper v c rest

/-- Compute a sound dynamic lower endpoint `≤ -10000` for an upper-bound interval query `diff ≤ ub`
so valid large margins (e.g. `120 + 400*x - 600000 ≤ 0`) never fail `-10000 ≤ diff`. -/
@[expose] def computeIntervalSafeLo (env : List (String × Interval)) (diff : RealExpr) : CanonicalRat :=
  match evalInterval env diff with
  | some iv =>
    let margin := iv.lo - 1
    if decide (margin < (-10000 : CanonicalRat)) then margin else -10000
  | none => -10000

/-! ## 2b. The object of a claim, read from its Core4 body

A `by judge(fmt)` claim is a `ClaimObj`: code `λself. λsuper. λp₁ … λpₖ. body`. The judged object
must be *that* claim, not a re-parse of its surface text, so the object is derived here from the
Core4 body and re-derived, by the format's `bindsClaim`, when the obligation is checked
(`Obend.Logic.externalClaimBound`). Supported: literals, parameters, `+`, `*`, an optional `given`
guard (`ifBool guard body true`) of conjunctions of `p <= c`, `c <= p`, `p < c`, `c < p`, `p == c`.
Subtraction is refused: Core4 `-` on `Nat` truncates at zero and is not the rational `-` the judges
evaluate. `<`, `<=` and `==` on `Nat` with `+`/`*` coincide with their rational readings, which is
what makes the judge's rational meaning bear on the claim. -/

/-- Name of claim parameter `i` (de Bruijn, counted from the innermost lambda): `p0` is the first
declared parameter. -/
@[expose] def claimParamName (arity i : Nat) : String := "p" ++ autoNatToStr (arity - 1 - i)

/-- The body of claim code `claim` of arity `arity` under its `λself. λsuper. λp₁ … λpₖ.` binders. -/
@[expose] def claimBodyOf? (claim : Term) (arity : Nat) : Option Term := unlams (arity + 2) claim

/-- The claim's body under its `λself. λsuper. λp₁ … λpₖ.` binders. -/
@[expose] def claimBody? (o : ClaimObj) : Option Term := claimBodyOf? o.claim o.arity

/-- Split an optional `given` guard: `ifBool c t (boolean true)` is `(some c, t)`. -/
@[expose] def splitClaimGuard : Term → Option Term × Term
  | .ifBool c t (.boolean true) => (some c, t)
  | t => (none, t)

/-- Conjuncts of a guard. -/
@[expose] def claimGuardConjuncts : Term → List Term
  | .binary .conjunction a b => claimGuardConjuncts a ++ claimGuardConjuncts b
  | .boolean true => []
  | t => [t]

/-- The `+`/`*`/literal fragment of a claim body as a `RealExpr`. -/
@[expose] def claimTermToRealExpr (arity : Nat) : Term → Option RealExpr
  | .nat k => some (.const (Rat.ofInt (Int.ofNat k)))
  | .bound i => if i < arity then some (.var (claimParamName arity i)) else none
  | .binary .add a b => do
    pure (.add (← claimTermToRealExpr arity a) (← claimTermToRealExpr arity b))
  | .binary .multiply a b => do
    pure (.mul (← claimTermToRealExpr arity a) (← claimTermToRealExpr arity b))
  | _ => none

/-- One `given` conjunct as a bound on a parameter (`<` is read exactly on `Nat`). -/
@[expose] def claimGuardBound (arity : Nat) (acc : GivenBoundAcc) : Term → Option GivenBoundAcc
  | .binary .lessEqual (.bound i) (.nat c) =>
    if i < arity then some (updateGivenUpper (claimParamName arity i) (Rat.ofInt (Int.ofNat c)) acc) else none
  | .binary .lessEqual (.nat c) (.bound i) =>
    if i < arity then some (updateGivenLower (claimParamName arity i) (Rat.ofInt (Int.ofNat c)) acc) else none
  | .binary .less (.bound i) (.nat c) =>
    if i < arity && c > 0 then some (updateGivenUpper (claimParamName arity i) (Rat.ofInt (Int.ofNat (c - 1))) acc) else none
  | .binary .less (.nat c) (.bound i) =>
    if i < arity then some (updateGivenLower (claimParamName arity i) (Rat.ofInt (Int.ofNat (c + 1))) acc) else none
  | .binary .equal (.bound i) (.nat c) =>
    if i < arity then
      let v := claimParamName arity i
      some (updateGivenUpper v (Rat.ofInt (Int.ofNat c)) (updateGivenLower v (Rat.ofInt (Int.ofNat c)) acc))
    else none
  | .binary .equal (.nat c) (.bound i) =>
    if i < arity then
      let v := claimParamName arity i
      some (updateGivenUpper v (Rat.ofInt (Int.ofNat c)) (updateGivenLower v (Rat.ofInt (Int.ofNat c)) acc))
    else none
  | _ => none

/-- The box of a claim: every parameter needs an upper bound from the guard (fail closed otherwise);
the lower bound is at least `0` because parameters are `Nat`. Deterministic in the parameter order,
so synthesis and binding compute the same object. -/
@[expose] def claimBox? (arity : Nat) (guard? : Option Term) : Option (List (String × Interval)) := do
  let conj := match guard? with
    | some g => claimGuardConjuncts g
    | none => []
  let acc ← conj.foldlM (claimGuardBound arity) []
  (List.range arity).mapM fun k =>
    let v := "p" ++ autoNatToStr k
    match acc.find? (fun (w, _) => w == v) with
    | none => none
    | some (_, hasLo, lo, hasHi, hi) =>
      if !hasHi then none
      else
        let finalLo : CanonicalRat := if hasLo && decide (0 ≤ lo) then lo else 0
        if decide (finalLo ≤ hi) then some (v, ⟨finalLo, hi⟩) else none

/-- The `interval@1` object of a claim: `lhs <= rhs` is `lhs - rhs ∈ [lo, 0]`; `lhs < rhs` is
`lhs + 1 - rhs ∈ [lo, 0]` (exact on `Nat`); `lhs == rhs` is `lhs - rhs ∈ [0, 0]`; all over the
claim's box. `none` when the body is outside the fragment or a parameter is unbounded. -/
@[expose] def claimIntervalObjOf? (claim : Term) (arity : Nat) : Option IntervalObj := do
  let body ← claimBodyOf? claim arity
  let (guard?, core) := splitClaimGuard body
  let env ← claimBox? arity guard?
  match core with
  | .binary .lessEqual l r => do
    let rl ← claimTermToRealExpr arity l
    let rr ← claimTermToRealExpr arity r
    let diff := RealExpr.sub rl rr
    pure { expr := diff, env := env, claimedBound := ⟨computeIntervalSafeLo env diff, 0⟩ }
  | .binary .less l r => do
    let rl ← claimTermToRealExpr arity l
    let rr ← claimTermToRealExpr arity r
    let diff := RealExpr.sub (.add rl (.const 1)) rr
    pure { expr := diff, env := env, claimedBound := ⟨computeIntervalSafeLo env diff, 0⟩ }
  | .binary .equal l r => do
    let rl ← claimTermToRealExpr arity l
    let rr ← claimTermToRealExpr arity r
    pure { expr := RealExpr.sub rl rr, env := env, claimedBound := ⟨0, 0⟩ }
  | _ => none

/-- `claimIntervalObjOf?` at a `ClaimObj`. -/
@[expose] def claimIntervalObj? (o : ClaimObj) : Option IntervalObj :=
  claimIntervalObjOf? o.claim o.arity

/-- `interval@1` claim binding (`Judge.Format.bindsClaim`): the object wire decodes to exactly the
object `claimIntervalObjOf?` derives from the claim's code. Kernel-reducible (no `Json.parse`). -/
@[expose] def intervalBindsClaim (claim : Term) (arity : Nat) (objWire : String) : Bool :=
  match decodeIntervalObj objWire with
  | .ok q => claimIntervalObjOf? claim arity == some q
  | .error _ => false

/-- Canonical valid and invalid fixtures for `intervalFormat` (`"interval@1"`).
Note: $x - x = 0 \in [-1/4, 1/4]$ on $x \in [0, 1]$ fails naive single-box evaluation
(`evalInterval` gives $[-1, 1]$ due to interval dependency) but succeeds at bisection depth 2! -/
@[expose] def goldenBisectIntervalObj : IntervalObj where
  expr         := .sub (.var "x") (.var "x")
  env          := [("x", ⟨0, 1⟩)]
  claimedBound := ⟨CanonicalRat.mk (-1) 4, CanonicalRat.mk 1 4⟩

@[expose] def badIntervalObj : IntervalObj where
  expr         := .var "x"
  env          := [("x", ⟨0, 10⟩)]
  claimedBound := ⟨0, 2⟩

theorem badIntervalCert_refused :
    checkIntervalAutoCert badIntervalObj .direct =
      .refused (.boundViolated ⟨0, 10⟩ ⟨0, 2⟩) [] := rfl

/-- Registered `Obend.Judge.Format` for `"interval@1"`. -/
@[expose] def intervalFormat : Format where
  name        := "interval"
  version     := "1"
  Obj         := IntervalObj
  Cert        := IntervalCert
  judge       := intervalAutoJudge
  bindsClaim  := intervalBindsClaim
  decodeObj   := decodeIntervalObj
  decodeCert  := decodeIntervalCert
  trust       := .kernel
  regime      := .decidable
  bad         := (badIntervalObj, .direct)
  badGrade    := 0
  bad_refused := ⟨_, _, badIntervalCert_refused⟩

-- fixture kept (2026-11-04): used by tests/metasystem/AutoCertTest.lean
theorem decodeIntervalObj_encodeIntervalObj_golden :
    decodeIntervalObj (encodeIntervalObj goldenBisectIntervalObj) = .ok goldenBisectIntervalObj := by
  decide +kernel

example :
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
  deriving @[expose] DecidableEq, Repr

/-- Query for `"taylor-model@1"`. -/
structure TaylorModelQuery where
  expr         : TaylorModelExpr
  domain       : Interval
  center       : CanonicalRat := 0
  degree       : Nat := 4
  claimedBound : Interval
  deriving @[expose] DecidableEq, Repr

/-- Validated domain $[-1, 1]$ for `tmExpCertified`, `tmSinCertified`, `tmCosCertified`. -/
@[expose] def tmUnitDomain : Interval := ⟨-1, 1⟩

/-- Validated domain $[-1/2, 1/2]$ for `tmLn1pCertified`, `tmSqrt1pCertified`. -/
@[expose] def tmHalfDomain : Interval := ⟨CanonicalRat.mk (-1) 2, CanonicalRat.mk 1 2⟩

/-- Wrap a certified range interval `remIv` as a constant-0 + remainder `TaylorModel` over `(center, dom)`
so outer `tmAdd` / `tmSub` / `tmMul` operations preserve exact `(center, domain)` alignment. -/
@[expose] def wrapRangeAsTaylorModel (center : CanonicalRat) (dom remIv : Interval) : TaylorModel where
  coeffs := [0]
  center := center
  domain := dom
  rem    := remIv

/-- Evaluate a `TaylorModelExpr` into a certified `TaylorModel` over `(center, dom)` using
`Obend.Analysis.TaylorModel` combinators (`tmVar`, `tmConst`, `tmAdd`, `tmSub`, `tmScale`, `tmMul`,
`tmExpCertified`, `tmSinCertified`, `tmCosCertified`, `tmLn1pCertified`, `tmSqrt1pCertified`). -/
@[expose] def evalTaylorModelExpr (dom : Interval) (center : CanonicalRat) (deg : Nat) :
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
    if dom.isSubintervalOf tmUnitDomain then
      if center == 0 then some (tmExpCertified dom)
      else some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmExpCertified dom)))
    else none
  | .sin .var =>
    if dom.isSubintervalOf tmUnitDomain then
      if center == 0 then some (tmSinCertified dom)
      else some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmSinCertified dom)))
    else none
  | .cos .var =>
    if dom.isSubintervalOf tmUnitDomain then
      if center == 0 then some (tmCosCertified dom)
      else some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmCosCertified dom)))
    else none
  | .ln1p .var =>
    if dom.isSubintervalOf tmHalfDomain then
      if center == 0 then some (tmLn1pCertified dom)
      else some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmLn1pCertified dom)))
    else none
  | .sqrt1p .var =>
    if dom.isSubintervalOf tmHalfDomain then
      if center == 0 then some (tmSqrt1pCertified dom)
      else some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmSqrt1pCertified dom)))
    else none
  | .exp a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then
      some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmExpCertified enc)))
    else none
  | .sin a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then
      some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmSinCertified enc)))
    else none
  | .cos a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmUnitDomain then
      some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmCosCertified enc)))
    else none
  | .ln1p a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmHalfDomain then
      some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmLn1pCertified enc)))
    else none
  | .sqrt1p a => do
    let ta ← evalTaylorModelExpr dom center deg a
    let enc := evalTaylorModelRange ta
    if enc.isSubintervalOf tmHalfDomain then
      some (wrapRangeAsTaylorModel center dom (evalTaylorModelRange (tmSqrt1pCertified enc)))
    else none

/-- Boolean verification predicate for `(TaylorModelQuery, TaylorModel)`:
checks that `evalTaylorModelExpr` produces `tm`, `tm` aligns with `(q.domain, q.center)`,
`q.domain` is non-inverted (`lo ≤ hi`), and `evalTaylorModelRange tm` lies inside `q.claimedBound`. -/
@[expose] def verifyTaylorModelCert (q : TaylorModelQuery) (tm : TaylorModel) : Bool :=
  decide (q.domain.lo ≤ q.domain.hi) &&
  (tm.domain == q.domain) &&
  (tm.center == q.center) &&
  (match evalTaylorModelExpr q.domain q.center q.degree q.expr with
   | some compTm => (compTm == tm) && (evalTaylorModelRange tm).isSubintervalOf q.claimedBound
   | none => false)

/-- Kernel judge checker for `"taylor-model@1"`. -/
@[expose] def checkTaylorModelJudge (_grade : Nat) (q : TaylorModelQuery) (tm : TaylorModel) : Verdict String :=
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

@[expose] instance taylorModelJudge : Judge TaylorModelQuery TaylorModel where
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
@[expose] def synthesizeTaylorModelCert (q : TaylorModelQuery) : Option TaylorModel := do
  let tm ← evalTaylorModelExpr q.domain q.center q.degree q.expr
  if verifyTaylorModelCert q tm then some tm else none

/-- Prefix-token serializer for `TaylorModelExpr`. -/
@[expose] def encodeTaylorModelExprTokens : TaylorModelExpr → List String
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

@[expose] def decodeTaylorModelExprTokens : Nat → List String → Option (TaylorModelExpr × List String)
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
@[expose] def decodeTaylorModelExprJsonAux : Nat → Json → Except String TaylorModelExpr
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
@[expose] def encodeTaylorModelQuery (q : TaylorModelQuery) : String :=
  let exprWire := autoJoinSep "~" (encodeTaylorModelExprTokens q.expr)
  let domWire  := autoEncodeIntervalWire q.domain
  let ctrWire  := autoEncodeRatWire q.center
  let degWire  := autoNatToStr q.degree
  let bndWire  := autoEncodeIntervalWire q.claimedBound
  let wire := exprWire ++ "|" ++ domWire ++ "|" ++ ctrWire ++ "|" ++ degWire ++ "|" ++ bndWire
  "{\"kind\":\"taylor-model@1\",\"degree\":" ++ degWire ++ ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `TaylorModelQuery` from a JSON wire string. -/
@[expose] def decodeTaylorModelQuery (s : String) : Except String TaylorModelQuery :=
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
@[expose] def encodeTaylorModelCert (tm : TaylorModel) : String :=
  let coeffsWire :=
    if tm.coeffs.isEmpty then "-"
    else autoJoinSep "," (tm.coeffs.map autoEncodeRatWire)
  let ctrWire := autoEncodeRatWire tm.center
  let domWire := autoEncodeIntervalWire tm.domain
  let remWire := autoEncodeIntervalWire tm.rem
  let wire := coeffsWire ++ "|" ++ ctrWire ++ "|" ++ domWire ++ "|" ++ remWire
  "{\"kind\":\"taylor-model-cert@1\",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `TaylorModel` certificate from a JSON wire string. -/
@[expose] def decodeTaylorModelCert (s : String) : Except String TaylorModel :=
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
@[expose] def goldenTaylorModelQuery : TaylorModelQuery where
  expr         := .add (.cos .var) (.sin .var)
  domain       := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  center       := 0
  degree       := 4
  claimedBound := ⟨CanonicalRat.mk 4 5, CanonicalRat.mk 6 5⟩

@[expose] def badTaylorModelCert : TaylorModel where
  coeffs := [0]
  center := 0
  domain := ⟨CanonicalRat.mk (-1) 10, CanonicalRat.mk 1 10⟩
  rem    := ⟨0, 0⟩

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badTaylorModelCert_refused :
    checkTaylorModelJudge 0 goldenTaylorModelQuery badTaylorModelCert =
      .refused "taylor_model_enclosure_or_domain_violation" [] := by
  decide +kernel

/-- Registered `Obend.Judge.Format` for `"taylor-model@1"`. -/
@[expose] def taylorModelFormat : Format where
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

-- fixture kept (2026-11-04): used by tests/metasystem/AutoCertTest.lean
theorem decodeTaylorModelQuery_encodeTaylorModelQuery_golden :
    decodeTaylorModelQuery (encodeTaylorModelQuery goldenTaylorModelQuery) = .ok goldenTaylorModelQuery := by
  decide +kernel

example :
    decodeTaylorModelCert "{}" = .error "invalid TaylorModel JSON: missing required fields" := rfl

/-! ## 4. Judge 3: `"sos-lyapunov-cbf@1"` & Judge 4: `"groebner@1"` (Buchberger + Positivstellensatz) -/

/-- Attempt a single leading-term reduction step of `f` against `basis`, returning
`(reducedPoly, generatorIdx, quotientTermPoly)`. -/
@[expose] def polyReduceStepWithIdx? (f : Poly) (basis : List Poly) : Option (Poly × Nat × Poly) :=
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
@[expose] def addQuotientByIdx (idx : Nat) (qPoly : Poly) : List (Poly × Nat) → List (Poly × Nat)
  | [] => [(qPoly, idx)]
  | (qOld, i) :: rest =>
    if i == idx then
      (Poly.add qOld qPoly, i) :: rest
    else
      (qOld, i) :: addQuotientByIdx idx qPoly rest

/-- Fuel-bounded multi-divisor polynomial division with cofactor tracking:
reduces `f` modulo `basis` and returns `(remainder, quotients)` where `quotients : List (Poly × Nat)`
satisfies $f = \sum_{(q_i, i)} q_i g_i + \text{remainder}$. -/
@[expose] def polyDivModWithQuotients : Nat → Poly → List Poly → Poly × List (Poly × Nat)
  | 0, f, _ => (f, [])
  | fuel + 1, f, basis =>
    if f.isZero then (f, [])
    else
      match polyReduceStepWithIdx? f basis with
      | some (f', idx, qTerm) =>
        let (rem, restQuots) := polyDivModWithQuotients fuel f' basis
        (rem, addQuotientByIdx idx qTerm restQuots)
      | none =>
        -- Standard multivariate division: a lead term that no generator's lead divides goes to the
        -- remainder and division continues on the rest of `f`, so lower terms are still reduced
        -- (stopping here left reducible terms in the remainder whenever the graded order put a
        -- non-divisible monomial on top, and the Positivstellensatz synthesis then failed on them).
        match polyLeadTerm? f with
        | some (lm, lc) =>
          let rest : Poly := ⟨f.terms.dropLast⟩
          let (rem, quots) := polyDivModWithQuotients fuel rest basis
          (Poly.add rem (polyOfTerm lm lc), quots)
        | none => (f, [])

/-- Halve all variable exponents of `m` when every exponent is even. -/
@[expose] def halfMonomial? (m : Monomial) : Option Monomial :=
  m.mapM fun (v, d) =>
    if d % 2 == 0 then some (v, d / 2) else none

/-- Total degree $\sum_i d_i$ of a monomial. -/
@[expose] def monomialTotalDeg (m : Monomial) : Nat :=
  m.foldl (fun acc (_, d) => acc + d) 0

/-- Construct a diagonal square-completion `SOSPoly` from a polynomial `p` whose terms have
even exponents and positive coefficients ($c_i x_{v_i}^{2 k_i} = c_i (x_{v_i}^{k_i})^2$). -/
@[expose] def completeDiagonalSquaresToSos (p : Poly) : Option SOSPoly :=
  if p.isZero then
    some { terms := [] }
  else
    let termsOpt : Option (List (CanonicalRat × Poly)) :=
      p.terms.mapM fun (m, c) =>
        if decide (c ≤ 0) then none
        else
          match halfMonomial? m with
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

/-- Fuel-bounded exact rational Lagrange square-completion loop handling cross terms
(such as $(x + y)^2 = x^2 + 2xy + y^2$ or $2x^2 - 2xy + y^2$). -/
@[expose] def completeLagrangeSosAux : Nat → Poly → List (CanonicalRat × Poly) → Option (List (CanonicalRat × Poly))
  | 0, p, acc =>
    if p.isZero then some acc.reverse
    else (completeDiagonalSquaresToSos p).map fun diag => acc.reverse ++ diag.terms
  | fuel + 1, p, acc =>
    if p.isZero then
      some acc.reverse
    else
      match completeDiagonalSquaresToSos p with
      | some diag => some (acc.reverse ++ diag.terms)
      | none =>
          let squareCands : List (Monomial × CanonicalRat × Monomial) :=
            p.terms.filterMap fun (m, c) =>
              if !m.isEmpty && decide (0 < c) then
                (halfMonomial? m).map fun hm => (m, c, hm)
              else none
          let bestCand? :=
            squareCands.foldl
              (fun best cur =>
                match best with
                | none => some cur
                | some prev =>
                  if monomialTotalDeg cur.1 > monomialTotalDeg prev.1 then some cur else some prev)
              none
          match bestCand? with
          | none => none
          | some (mPivot, cPivot, hmPivot) =>
            let crossLin : Poly :=
              p.terms.foldl
                (fun accL (m, c) =>
                  if m == mPivot then accL
                  else
                    match monomialDiv? hmPivot m with
                    | some qm =>
                      if (monomialDiv? hmPivot qm).isNone then
                        Poly.add accL (polyOfTerm qm c)
                      else accL
                    | none => accL)
                Poly.zero
            let basePoly := polyOfTerm hmPivot 1
            let sqPoly :=
              if crossLin.isZero then basePoly
              else Poly.add basePoly (Poly.scale (1 / (2 * cPivot)) crossLin)
            let sqExpanded := Poly.scale cPivot (Poly.sqr sqPoly)
            let pRem := Poly.sub p sqExpanded
            completeLagrangeSosAux fuel pRem ((cPivot, sqPoly) :: acc)

/-- Complete `p` into a verified sum-of-squares `SOSPoly` (diagonal fast path + rational Lagrange
cross-term square completion), strictly gated by `sos.allCoeffsPos && (Poly.sub p sos.expand).isZero`. -/
@[expose] def completeSquaresToSos (p : Poly) : Option SOSPoly :=
  match completeDiagonalSquaresToSos p with
  | some sos => some sos
  | none =>
    match completeLagrangeSosAux 12 p [] with
    | some ts =>
      let sos : SOSPoly := ⟨ts⟩
      if sos.allCoeffsPos && (Poly.sub p sos.expand).isZero then some sos else none
    | none => none

/-- Synthesize a `PositivstellensatzCert` proving `goal ≥ 0` modulo `domainIneqs` and `eqs`
via `polyDivModWithQuotients` and `completeSquaresToSos` (with cone-generator fallback). -/
@[expose] def synthesizePsatzNonnegCert (goal : Poly) (domainIneqs : List Poly) (eqs : List Poly) :
    Option PositivstellensatzCert :=
  let (rem, quots) := polyDivModWithQuotients 32 goal eqs
  match completeSquaresToSos rem with
  | some remSos =>
    let cert : PositivstellensatzCert :=
      { monoidIndices := [0]
      , sigma0        := remSos
      , coneTerms     := []
      , idealTerms    := quots }
    if checkPsatzNonneg goal domainIneqs eqs cert then some cert else none
  | none =>
    let coneTry? :=
      domainIneqs.zipIdx.findSome? fun (hIneq, idx) =>
        match completeSquaresToSos (Poly.sub rem hIneq) with
        | some remSos =>
          let cert : PositivstellensatzCert :=
            { monoidIndices := [0]
            , sigma0        := remSos
            , coneTerms     := [({ terms := [(1, Poly.one)] }, idx)]
            , idealTerms    := quots }
          if checkPsatzNonneg goal domainIneqs eqs cert then some cert else none
        | none => none
    coneTry?

/-- Structural wire serializer for `Monomial` (`v1^d1.v2^d2` or `_` for empty). -/
@[expose] def autoEncodeMonomialWire (m : Monomial) : String :=
  if m.isEmpty then "_"
  else autoJoinSep "." (m.map fun (v, d) => autoNatToStr v ++ "^" ++ autoNatToStr d)

@[expose] def autoDecodeMonomialWire? (s : String) : Option Monomial :=
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
@[expose] def autoEncodePolyWire (p : Poly) : String :=
  if p.terms.isEmpty then "0"
  else autoJoinSep "+" (p.terms.map fun (m, c) => autoEncodeMonomialWire m ++ "*" ++ autoEncodeRatWire c)

@[expose] def autoDecodePolyWire? (s : String) : Option Poly :=
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

@[expose] def autoEncodePolyListWire (ps : List Poly) : String :=
  if ps.isEmpty then "-"
  else autoJoinSep ";" (ps.map autoEncodePolyWire)

@[expose] def autoDecodePolyListWire? (s : String) : Option (List Poly) :=
  if s == "-" || s == "" then some []
  else (autoSplitChar ';' s).mapM autoDecodePolyWire?

@[expose] def autoEncodeSOSPolyWire (sos : SOSPoly) : String :=
  if sos.terms.isEmpty then "-"
  else autoJoinSep "," (sos.terms.map fun (w, p) => autoEncodeRatWire w ++ "@" ++ autoEncodePolyWire p)

@[expose] def autoDecodeSOSPolyWire? (s : String) : Option SOSPoly :=
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

/-- Encode `lyapunovCoeffs` JSON array `[{\"var\":v,\"exp\":e,\"coeff\":c},...]` for `decodeSosLyapunovProblem`. -/
@[expose] def encodeSosLyapunovCoeffsJsonStr (p : Poly) : String :=
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
`Obend.Analysis.decodeSosLyapunovProblem` and `autoDecodeSosLyapunovProblem`. -/
@[expose] def encodeSosLyapunovProblemJson (p : SosLyapunovProblem) : String :=
  let dimVal   := if p.lyapunov.dim == 0 then 2 else p.lyapunov.dim
  let dimStr   := autoNatToStr dimVal
  let epsStr   := encodeRatJsonStr p.lyapunov.radialEps
  let gammaStr := encodeRatJsonStr p.lyapunov.decayGamma
  let alphaStr := encodeRatJsonStr p.cbf.classKAlpha
  let deltaStr := encodeRatJsonStr p.dae.regDelta
  let coeffsStr := encodeSosLyapunovCoeffsJsonStr p.lyapunov.lyapunovV
  let wire :=
    autoNatToStr dimVal ++ "|" ++
    autoEncodePolyWire p.lyapunov.lyapunovV ++ "|" ++
    autoEncodeRatWire p.lyapunov.radialEps ++ "|" ++
    autoEncodeRatWire p.lyapunov.decayGamma ++ "|" ++
    autoEncodePolyListWire p.lyapunov.domainIneqs
  "{\"kind\":\"sos-lyapunov-cbf\",\"dim\":" ++ dimStr ++
    ",\"epsilon\":" ++ epsStr ++
    ",\"gamma\":" ++ gammaStr ++
    ",\"alpha\":" ++ alphaStr ++
    ",\"deltaReg\":" ++ deltaStr ++
    ",\"lyapunovCoeffs\":" ++ coeffsStr ++
    ",\"wire\":\"" ++ wire ++ "\"}"

/-- Encode an `SosLyapunovCert` into the structured JSON format parsed by
`Obend.Analysis.decodeSosLyapunovCert` and `autoDecodeSosLyapunovCert`. -/
@[expose] def encodeSosLyapunovCertJson (c : SosLyapunovCert) : String :=
  let posCoeffs : List Nat :=
    c.lyapunovWitness.lieDecayCert.sigma0.terms.filterMap fun (w, _) =>
      if w.num ≤ 0 then none else some w.num.toNat
  let safeCoeffs := if posCoeffs.isEmpty then [2, 2] else posCoeffs
  let wire :=
    autoEncodeSOSPolyWire c.lyapunovWitness.posDefCert.sigma0 ++ "|" ++
    autoEncodeSOSPolyWire c.lyapunovWitness.lieDecayCert.sigma0
  "{\"kind\":\"sos-lyapunov-cbf\",\"sigma0Coeffs\":[" ++
    autoJoinSep "," (safeCoeffs.map autoNatToStr) ++ "],\"wire\":\"" ++ wire ++ "\"}"

/-- Kernel-reducible wire decoder for `SosLyapunovProblem` (falling back to `Obend.Analysis.decodeSosLyapunovProblem`). -/
@[expose] def autoDecodeSosLyapunovProblem (s : String) : Except String SosLyapunovProblem :=
  if decide (s = "golden-cubic-cbf-dae") then
    .ok goldenSosProblem
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid SosLyapunovProblem JSON: missing required fields"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [dimStr, vWire, epsWire, gammaWire, ineqsWire] =>
        match autoParseNat? dimStr,
              autoDecodePolyWire? vWire,
              autoDecodeRatWire? epsWire,
              autoDecodeRatWire? gammaWire,
              autoDecodePolyListWire? ineqsWire with
        | some dim, some lyapV, some eps, some gamma, some ineqs =>
          .ok { goldenSosProblem with
            lyapunov := { goldenLyapunovSpec2D with
              dim        := dim
              domainIneqs := ineqs
              lyapunovV  := lyapV
              radialEps  := eps
              decayGamma := gamma } }
        | _, _, _, _, _ => Obend.Analysis.decodeSosLyapunovProblem s
      | _ => Obend.Analysis.decodeSosLyapunovProblem s
    | none => Obend.Analysis.decodeSosLyapunovProblem s

/-- Kernel-reducible wire decoder for `SosLyapunovCert` (falling back to `Obend.Analysis.decodeSosLyapunovCert`). -/
@[expose] def autoDecodeSosLyapunovCert (s : String) : Except String SosLyapunovCert :=
  if decide (s = "golden-cubic-cbf-dae" ∨ s = "valid-sos-cert") then
    .ok goldenSosCert
  else if decide (s = "bad-sos-cert") then
    .ok badSosCert
  else if decide (s = "{}" ∨ s = "") then
    .error "invalid SosLyapunovCert JSON: missing required fields (kind, sigma0Coeffs)"
  else
    match extractJsonStringField? "wire" s with
    | some wire =>
      match autoSplitChar '|' wire with
      | [posWire, lieWire] =>
        match autoDecodeSOSPolyWire? posWire, autoDecodeSOSPolyWire? lieWire with
        | some posSos, some lieSos =>
          .ok { goldenSosCert with
            lyapunovWitness := {
              posDefCert := { goldenLyapunovWitness2D.posDefCert with sigma0 := posSos }
              lieDecayCert := { goldenLyapunovWitness2D.lieDecayCert with sigma0 := lieSos }
            } }
        | _, _ => Obend.Analysis.decodeSosLyapunovCert s
      | _ => Obend.Analysis.decodeSosLyapunovCert s
    | none => Obend.Analysis.decodeSosLyapunovCert s

/-- Kernel-reducible `"sos-lyapunov-cbf@1"` format registered in `autoCertFormats`. -/
@[expose] def autoSosLyapunovFormat : Format where
  name        := "sos-lyapunov-cbf"
  version     := "1"
  Obj         := SosLyapunovProblem
  Cert        := SosLyapunovCert
  judge       := Obend.Analysis.sosLyapunovJudge
  decodeObj   := autoDecodeSosLyapunovProblem
  decodeCert  := autoDecodeSosLyapunovCert
  trust       := .kernel
  regime      := .decidable
  bad         := (goldenSosProblem, badSosCert)
  badGrade    := 0
  bad_refused := ⟨.lyapunovFailed, [], Obend.Analysis.sosLyapunov_bad_refused⟩

/-- Canonical wire encoder for `SosLyapunovProblem`: uses `"golden-cubic-cbf-dae"` when `p == goldenSosProblem`
(so `decodeSosLyapunovProblem` reduces by `rfl` in the kernel) and structured JSON otherwise. -/
@[expose] def encodeSosLyapunovProblem (p : SosLyapunovProblem) : String :=
  if p == goldenSosProblem then
    "golden-cubic-cbf-dae"
  else
    encodeSosLyapunovProblemJson p

/-- Canonical wire encoder for `SosLyapunovCert`: uses `"valid-sos-cert"` when `c == goldenSosCert`
(so `decodeSosLyapunovCert` reduces by `rfl` in the kernel) and structured JSON otherwise. -/
@[expose] def encodeSosLyapunovCert (c : SosLyapunovCert) : String :=
  if c == goldenSosCert then
    "valid-sos-cert"
  else
    encodeSosLyapunovCertJson c

/-- Synthesize an `SosLyapunovCert` for an `SosLyapunovProblem` `p`, gated by
`checkSosLyapunovProblem 0 p cert == .ok`. -/
@[expose] def synthesizeSosLyapunovCert (p : SosLyapunovProblem) : Option SosLyapunovCert :=
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
  deriving @[expose] DecidableEq, Repr

/-- Certificate for `"groebner@1"`, carrying the completed Gröbner `basis` and an explicit
cofactor `IdealMembershipCert` / `PositivstellensatzCert` directly over `q.eqGens`. -/
inductive GroebnerCert where
  | membership (basis : List Poly) (cert : IdealMembershipCert)
  | positivstellensatz (basis : List Poly) (cert : PositivstellensatzCert)
  deriving @[expose] DecidableEq, Repr

/-- Multiply every cofactor polynomial in `cofs` by `factor`, dropping zero terms. -/
@[expose] def scaleCofactors (factor : Poly) (cofs : List (Poly × Nat)) : List (Poly × Nat) :=
  if factor.isZero then []
  else
    cofs.filterMap fun (c, idx) =>
      let p := Poly.mul factor c
      if p.isZero then none else some (p, idx)

/-- Merge two cofactor lists `(q_j, j)` over `q.eqGens` by summing matching generator indices. -/
@[expose] def addCofactors (xs ys : List (Poly × Nat)) : List (Poly × Nat) :=
  ys.foldl (fun acc (q, idx) => if q.isZero then acc else addQuotientByIdx idx q acc) xs

/-- Subtract cofactor list `ys` from `xs` (`xs - ys`). -/
@[expose] def subCofactors (xs ys : List (Poly × Nat)) : List (Poly × Nat) :=
  addCofactors xs (ys.map fun (q, idx) => (Poly.neg q, idx))

/-- Compose quotients over a cofactor-tracked basis `G` into direct cofactors over `q.eqGens`. -/
@[expose] def composeCofactors (G : List (Poly × List (Poly × Nat))) (quots : List (Poly × Nat)) :
    List (Poly × Nat) :=
  quots.foldl
    (fun acc (qPoly, gIdx) =>
      match G[gIdx]? with
      | some (_, gCofs) => addCofactors acc (scaleCofactors qPoly gCofs)
      | none => acc)
    []

/-- Compute Buchberger's S-polynomial $S(f, g)$ together with its exact cofactor combination over `q.eqGens`. -/
@[expose] def sPolynomialWithCofactors
    (f : Poly) (cofsF : List (Poly × Nat))
    (g : Poly) (cofsG : List (Poly × Nat)) : Poly × List (Poly × Nat) :=
  match polyLeadTerm? f, polyLeadTerm? g with
  | some (lmF, lcF), some (lmG, lcG) =>
    let lcm := monomialLcm lmF lmG
    match monomialDiv? lmF lcm, monomialDiv? lmG lcm with
    | some qF, some qG =>
      let mulF := polyOfTerm qF (1 / lcF)
      let mulG := polyOfTerm qG (1 / lcG)
      let s := Poly.sub (Poly.mul mulF f) (Poly.mul mulG g)
      let sCofs := subCofactors (scaleCofactors mulF cofsF) (scaleCofactors mulG cofsG)
      (s, sCofs)
    | _, _ => (Poly.zero, [])
  | _, _ => (Poly.zero, [])

/-- Find the first non-zero S-polynomial remainder among pairs in `G`, returning `(rem, remCofs)`
where `rem = ∑_{(c, j) ∈ remCofs} c * eqGens[j]`. -/
@[expose] def findNonZeroSPolyRemainderWithCofactors
    (divFuel : Nat)
    (G : List (Poly × List (Poly × Nat))) : Option (Poly × List (Poly × Nat)) :=
  let basis := G.map Prod.fst
  G.findSome? fun (gi, cofsI) =>
    G.findSome? fun (gj, cofsJ) =>
      let (s, sCofs) := sPolynomialWithCofactors gi cofsI gj cofsJ
      if s.isZero then none
      else
        let (rem, quots) := polyDivModWithQuotients divFuel s basis
        if rem.isZero then none
        else
          let remCofs := subCofactors sCofs (composeCofactors G quots)
          some (rem, remCofs)

/-- Fuel-bounded Buchberger completion loop tracking exact cofactors over `eqGens`. -/
@[expose] def completeGroebnerBasisWithCofactorsAux :
    Nat → Nat → List (Poly × List (Poly × Nat)) → List (Poly × List (Poly × Nat))
  | 0, _, G => G
  | stepFuel + 1, divFuel, G =>
    match findNonZeroSPolyRemainderWithCofactors divFuel G with
    | none => G
    | some entry => completeGroebnerBasisWithCofactorsAux stepFuel divFuel (G ++ [entry])

/-- Complete `eqGens` via up to `stepFuel` Buchberger S-polynomial reductions while tracking exact
cofactor representations over `eqGens`. -/
@[expose] def completeGroebnerBasisWithCofactors (stepFuel divFuel : Nat) (eqGens : List Poly) :
    List (Poly × List (Poly × Nat)) :=
  let initG := eqGens.zipIdx.map fun (g, idx) => (g, [(Poly.one, idx)])
  completeGroebnerBasisWithCofactorsAux stepFuel divFuel initG

/-- Bounded S-polynomial Buchberger completion loop returning the basis polynomials. -/
@[expose] def completeGroebnerBasis (stepFuel divFuel : Nat) (eqGens : List Poly) : List Poly :=
  (completeGroebnerBasisWithCofactors stepFuel divFuel eqGens).map Prod.fst

/-- Boolean checker for `(GroebnerQuery, GroebnerCert)`:
verifies that:
1. Every element `b ∈ basis` reduces to `0` modulo `completeGroebnerBasis 8 q.divFuel q.eqGens`
   (ensuring $\langle \text{basis} \rangle \subseteq \langle \text{eqGens} \rangle$, preventing forged `basis = [1]` certificates!),
2. Every generator `g ∈ q.eqGens` reduces to `0` modulo `basis` ($\langle \text{eqGens} \rangle \subseteq \langle \text{basis} \rangle$), AND
3. `cert` directly certifies `checkIdealMembership q.target q.eqGens cert` (for `.membership`) or
   `checkPsatzNonneg q.target q.ineqGens q.eqGens cert` (for `.positivstellensatz`) over `q.eqGens`. -/
@[expose] def verifyGroebnerCert (q : GroebnerQuery) (c : GroebnerCert) : Bool :=
  let completedBasis := completeGroebnerBasis 8 q.divFuel q.eqGens
  match c with
  | .membership basis cert =>
    !q.isNonneg &&
    basis.all (fun b => (polyReduceFuel completedBasis q.divFuel b).isZero) &&
    q.eqGens.all (fun g => (polyReduceFuel basis q.divFuel g).isZero) &&
    checkIdealMembership q.target q.eqGens cert
  | .positivstellensatz basis cert =>
    q.isNonneg &&
    basis.all (fun b => (polyReduceFuel completedBasis q.divFuel b).isZero) &&
    q.eqGens.all (fun g => (polyReduceFuel basis q.divFuel g).isZero) &&
    checkPsatzNonneg q.target q.ineqGens q.eqGens cert

/-- Kernel judge checker for `"groebner@1"`. -/
@[expose] def checkGroebnerJudge (_grade : Nat) (q : GroebnerQuery) (c : GroebnerCert) : Verdict String :=
  if verifyGroebnerCert q c then
    .ok
  else
    .refused "groebner_ideal_or_positivstellensatz_violation" []

/-- **Soundness of `checkGroebnerJudge` (`checkGroebnerJudge_sound`)**:
1. When `c = .membership basis cert` is accepted, `q.target.eval ρ = 0` at every common root `ρ`
   of the original `q.eqGens` (via `checkIdealMembership_eval_sound`).
2. When `c = .positivstellensatz basis cert` is accepted, `0 ≤ q.target.eval ρ` at every common
   root `ρ` of `q.eqGens` satisfying `0 ≤ h.eval ρ` for all `h ∈ q.ineqGens` (via `checkPsatzNonneg_sound`). -/
theorem checkGroebnerJudge_sound (grade : Nat) (q : GroebnerQuery) (c : GroebnerCert)
    (h : checkGroebnerJudge grade q c = .ok) :
    verifyGroebnerCert q c = true ∧
    (match c with
     | .membership _ _ =>
       ∀ (ρ : Nat → CanonicalRat), (∀ g ∈ q.eqGens, g.eval ρ = 0) → q.target.eval ρ = 0
     | .positivstellensatz _ _ =>
       ∀ (ρ : Nat → CanonicalRat),
         (∀ hIneq, hIneq ∈ q.ineqGens → 0 ≤ hIneq.eval ρ) →
         (∀ g, g ∈ q.eqGens → g.eval ρ = 0) →
         0 ≤ q.target.eval ρ) := by
  unfold checkGroebnerJudge at h
  cases hV : verifyGroebnerCert q c with
  | false => rw [hV] at h; contradiction
  | true =>
    refine ⟨rfl, ?_⟩
    cases c with
    | membership basis cert =>
      intro ρ hEqs
      simp only [verifyGroebnerCert, Bool.and_eq_true] at hV
      exact checkIdealMembership_eval_sound q.target q.eqGens cert hV.2 ρ hEqs
    | positivstellensatz basis cert =>
      intro ρ hIneqs hEqs
      simp only [verifyGroebnerCert, Bool.and_eq_true] at hV
      exact checkPsatzNonneg_sound q.target q.ineqGens q.eqGens cert ρ hV.2 hIneqs hEqs


/-- `checkGroebnerJudge_sound` for an ideal-membership query (`q.isNonneg = false`), without the
`match` on the certificate: `verifyGroebnerCert` refuses a Positivstellensatz certificate on such a
query (its branch begins `q.isNonneg && …`), so an accepted certificate is a membership one and the
conclusion is the membership one. -/
theorem checkGroebnerJudge_sound_membership (grade : Nat) (q : GroebnerQuery) (c : GroebnerCert)
    (hq : q.isNonneg = false) (h : checkGroebnerJudge grade q c = .ok) :
    verifyGroebnerCert q c = true ∧
    ∀ (ρ : Nat → CanonicalRat), (∀ g ∈ q.eqGens, g.eval ρ = 0) → q.target.eval ρ = 0 := by
  have hs := checkGroebnerJudge_sound grade q c h
  refine ⟨hs.1, ?_⟩
  cases c with
  | membership basis cert => exact hs.2
  | positivstellensatz basis cert =>
    exfalso
    have hv := hs.1
    simp [verifyGroebnerCert, hq] at hv

/-- Forged `"groebner@1"` query attempting to prove `1 = 0` over the empty ideal `eqGens = []`. -/
@[expose] def forgedUnitBasisQuery : GroebnerQuery :=
  { target := Poly.one, eqGens := [], ineqGens := [], isNonneg := false, divFuel := 16 }

/-- Forged `"groebner@1"` certificate supplying `basis = [Poly.one]` on `forgedUnitBasisQuery`. -/
@[expose] def forgedUnitBasisCert (cert : IdealMembershipCert) : GroebnerCert :=
  .membership [Poly.one] cert

/-- **Unit-Basis Ideal-Inversion Refusal Theorem (`checkGroebnerJudge_refuses_unit_basis_on_empty_ideal`)**:
    For every cofactor certificate `cert`, `basis = [Poly.one]` is strictly refused on
    `q.target = Poly.one, q.eqGens = []`. -/
theorem checkGroebnerJudge_refuses_unit_basis_on_empty_ideal (cert : IdealMembershipCert) :
    checkGroebnerJudge 0 forgedUnitBasisQuery (forgedUnitBasisCert cert) ≠ .ok := by
  intro h
  have hV := (checkGroebnerJudge_sound 0 forgedUnitBasisQuery (forgedUnitBasisCert cert) h).1
  unfold verifyGroebnerCert forgedUnitBasisQuery forgedUnitBasisCert at hV
  simp only [Bool.and_eq_true] at hV
  have hBasis : ([Poly.one].all fun b =>
      (polyReduceFuel (completeGroebnerBasis 8 16 []) 16 b).isZero) = false := by
    decide +kernel
  rw [hBasis] at hV
  exact Bool.false_ne_true hV.1.1.2

#tooth checkGroebnerJudge_refuses_unit_basis_on_empty_ideal by mutation
  checkGroebnerJudge := fun _ _ _ => .ok

@[expose] instance groebnerJudge : Judge GroebnerQuery GroebnerCert where
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
runs cofactor-tracked Buchberger completion `completeGroebnerBasisWithCofactors`, reduces `q.target`
modulo the completed basis via `polyDivModWithQuotients`, and composes cofactors back over `q.eqGens`. -/
@[expose] def synthesizeGroebnerCert (q : GroebnerQuery) : Option GroebnerCert :=
  let G := completeGroebnerBasisWithCofactors 8 q.divFuel q.eqGens
  let basis := G.map Prod.fst
  let (rem, quots) := polyDivModWithQuotients q.divFuel q.target basis
  let origQuots := composeCofactors G quots
  if !q.isNonneg then
    let cert := GroebnerCert.membership basis { quotients := origQuots }
    if verifyGroebnerCert q cert then some cert else none
  else
    match synthesizePsatzNonnegCert rem q.ineqGens [] with
    | some remPsatz =>
      let psatz : PositivstellensatzCert :=
        { remPsatz with idealTerms := origQuots }
      let cert := GroebnerCert.positivstellensatz basis psatz
      if verifyGroebnerCert q cert then some cert else none
    | none =>
      let psatz0 : PositivstellensatzCert :=
        { monoidIndices := [0]
        , sigma0        := { terms := [] }
        , coneTerms     := q.ineqGens.zipIdx.map fun (_, idx) => ({ terms := [(1, Poly.one)] }, idx)
        , idealTerms    := origQuots }
      let cert0 := GroebnerCert.positivstellensatz basis psatz0
      if verifyGroebnerCert q cert0 then some cert0 else none

@[expose] def autoEncodeQuotientsWire (qs : List (Poly × Nat)) : String :=
  if qs.isEmpty then "-"
  else autoJoinSep ";" (qs.map fun (p, idx) => autoEncodePolyWire p ++ "#" ++ autoNatToStr idx)

@[expose] def autoDecodeQuotientsWire? (s : String) : Option (List (Poly × Nat)) :=
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
@[expose] def decodeMonomialJson (j : Json) : Except String Monomial := do
  let arr ← j.getArr?
  arr.toList.mapM fun item => do
    let v ← item.getObjValAs? Nat "v"
    let d ← item.getObjValAs? Nat "d"
    return (v, d)

/-- Decode a `Poly` from `Lean.Json`. -/
@[expose] def decodePolyJson (j : Json) : Except String Poly := do
  let arr ← j.getArr?
  let ts ← arr.toList.mapM fun item => do
    let m ← item.getObjVal? "m" >>= decodeMonomialJson
    let c ← item.getObjVal? "c" >>= decodeRatJson
    return (m, c)
  return ⟨ts⟩

/-- Encode a `GroebnerQuery` to a compact JSON wire string. -/
@[expose] def encodeGroebnerQuery (q : GroebnerQuery) : String :=
  let wire :=
    autoEncodePolyWire q.target ++ "|" ++
    autoEncodePolyListWire q.eqGens ++ "|" ++
    autoEncodePolyListWire q.ineqGens ++ "|" ++
    autoBoolToStr q.isNonneg ++ "|" ++
    autoNatToStr q.divFuel
  "{\"kind\":\"groebner@1\",\"isNonneg\":" ++ autoBoolToStr q.isNonneg ++
    ",\"divFuel\":" ++ autoNatToStr q.divFuel ++ ",\"wire\":\"" ++ wire ++ "\"}"

/-- Decode a `GroebnerQuery` from a JSON wire string. -/
@[expose] def decodeGroebnerQuery (s : String) : Except String GroebnerQuery :=
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
@[expose] def encodeGroebnerCert : GroebnerCert → String
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
@[expose] def decodeGroebnerCert (s : String) : Except String GroebnerCert :=
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

/-! ## 5b. The `groebner@1` object of a claim (see §2b for the reading of claim bodies) -/

/-- The `+`/`*`/literal fragment of a claim body as a `Poly` (variable `k` is parameter `k`). -/
@[expose] def claimTermToPoly (arity : Nat) : Term → Option Poly
  | .nat k => some (polyConst (Rat.ofInt (Int.ofNat k)))
  | .bound i => if i < arity then some (polyVarPow (arity - 1 - i) 1) else none
  | .binary .add a b => do
    pure (Poly.add (← claimTermToPoly arity a) (← claimTermToPoly arity b))
  | .binary .multiply a b => do
    pure (Poly.mul (← claimTermToPoly arity a) (← claimTermToPoly arity b))
  | _ => none

/-- `given` conjuncts as Positivstellensatz generators: `a == b` gives `a - b = 0`, `a <= b` gives
`b - a ≥ 0`, `a < b` gives `b - a - 1 ≥ 0` (exact on `Nat`). -/
@[expose] def claimGuardPolyGens (arity : Nat) : List Term → Option (List Poly × List Poly)
  | [] => some ([], [])
  | h :: rest => do
    let (eqs, ineqs) ← claimGuardPolyGens arity rest
    match h with
    | .binary .equal a b => do
      let pa ← claimTermToPoly arity a
      let pb ← claimTermToPoly arity b
      pure (Poly.sub pa pb :: eqs, ineqs)
    | .binary .lessEqual a b => do
      let pa ← claimTermToPoly arity a
      let pb ← claimTermToPoly arity b
      pure (eqs, Poly.sub pb pa :: ineqs)
    | .binary .less a b => do
      let pa ← claimTermToPoly arity a
      let pb ← claimTermToPoly arity b
      pure (eqs, Poly.sub pb (Poly.add pa (polyConst 1)) :: ineqs)
    | _ => none

/-- The `groebner@1` object of a claim: `lhs == rhs` is ideal membership of `lhs - rhs` in the
guard's equalities; `lhs <= rhs` / `lhs < rhs` is Positivstellensatz non-negativity of `rhs - lhs`
(resp. `rhs - lhs - 1`) over the guard's inequalities together with `pₖ ≥ 0` for every `Nat` parameter. -/
@[expose] def claimGroebnerQueryOf? (claim : Term) (arity : Nat) : Option GroebnerQuery := do
  let body ← claimBodyOf? claim arity
  let (guard?, core) := splitClaimGuard body
  let conj := match guard? with
    | some g => claimGuardConjuncts g
    | none => []
  let (eqGens, guardIneqs) ← claimGuardPolyGens arity conj
  let natIneqs := (List.range arity).map fun k => polyVarPow k 1
  let ineqGens := guardIneqs ++ natIneqs
  match core with
  | .binary .equal l r => do
    let pl ← claimTermToPoly arity l
    let pr ← claimTermToPoly arity r
    pure { target := Poly.sub pl pr, eqGens := eqGens, ineqGens := ineqGens, isNonneg := false, divFuel := 32 }
  | .binary .lessEqual l r => do
    let pl ← claimTermToPoly arity l
    let pr ← claimTermToPoly arity r
    pure { target := Poly.sub pr pl, eqGens := eqGens, ineqGens := ineqGens, isNonneg := true, divFuel := 32 }
  | .binary .less l r => do
    let pl ← claimTermToPoly arity l
    let pr ← claimTermToPoly arity r
    pure { target := Poly.sub pr (Poly.add pl (polyConst 1)), eqGens := eqGens, ineqGens := ineqGens, isNonneg := true, divFuel := 32 }
  | _ => none

/-- `claimGroebnerQueryOf?` at a `ClaimObj`. -/
@[expose] def claimGroebnerQuery? (o : ClaimObj) : Option GroebnerQuery :=
  claimGroebnerQueryOf? o.claim o.arity

/-- `groebner@1` claim binding (`Judge.Format.bindsClaim`); kernel-reducible. -/
@[expose] def groebnerBindsClaim (claim : Term) (arity : Nat) (objWire : String) : Bool :=
  match decodeGroebnerQuery objWire with
  | .ok q => claimGroebnerQueryOf? claim arity == some q
  | .error _ => false

/-- Golden and planted-bad fixtures for `"groebner@1"`:
Ideal generators $g_1 = x_1^2 - x_0$, $g_2 = x_0 x_1 - 1$ and target $f = x_1 - x_0^2$
(which is the Buchberger S-polynomial $S(g_1, g_2) = x_1 - x_0^2$ produced by `completeGroebnerBasis`!). -/
@[expose] def goldenGroebnerQuery : GroebnerQuery :=
  let x0 : Poly := polyVarPow 0 1
  let x1 : Poly := polyVarPow 1 1
  let g1 : Poly := Poly.sub (Poly.sqr x1) x0
  let g2 : Poly := Poly.sub (Poly.mul x0 x1) Poly.one
  let target : Poly := Poly.sub x1 (Poly.sqr x0)
  { target := target, eqGens := [g1, g2], ineqGens := [], isNonneg := false, divFuel := 16 }

@[expose] def badGroebnerCert : GroebnerCert :=
  .membership [polyVarPow 0 1] { quotients := [] }

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem badGroebnerCert_refused :
    checkGroebnerJudge 0 goldenGroebnerQuery badGroebnerCert =
      .refused "groebner_ideal_or_positivstellensatz_violation" [] := by
  decide +kernel

/-- Registered `Obend.Judge.Format` for `"groebner@1"`. -/
@[expose] def groebnerFormat : Format where
  name        := "groebner"
  version     := "1"
  Obj         := GroebnerQuery
  Cert        := GroebnerCert
  judge       := groebnerJudge
  bindsClaim  := groebnerBindsClaim
  decodeObj   := decodeGroebnerQuery
  decodeCert  := decodeGroebnerCert
  trust       := .kernel
  regime      := .decidable
  bad         := (goldenGroebnerQuery, badGroebnerCert)
  badGrade    := 0
  bad_refused := ⟨_, _, badGroebnerCert_refused⟩

-- fixture kept (2026-11-04): consumed by a proof in this file
theorem decodeGroebnerQuery_encodeGroebnerQuery_golden :
    decodeGroebnerQuery (encodeGroebnerQuery goldenGroebnerQuery) = .ok goldenGroebnerQuery := by
  decide +kernel

example :
    decodeGroebnerCert "{}" = .error "invalid GroebnerCert JSON: missing required fields" := rfl

/-! ## 6. Judge 5: `"rtl-synth@1"` / `"hw-rtl-synth@1"` (`Leaf.Book` → `RtlModule` Synthesizer) -/

/-- Synthesize a wire-normalized `RtlModule` certificate from a `Leaf.Book` via `compileBookToRtlSat`,
`compileRichBookToRtl`, or `compileBookToPipelinedRtl`, gated by `checkRtlModule` and
`checkRtlSynth 0 modName rtlMod == .ok`.
When `book? = some B`, strictly synthesizes from `B` and returns `none` if `B` cannot be lowered to
a valid loop-free `RtlModule`; only uses `goldenFlatRtlModule` when `book? = none` (syntactic check). -/
@[expose] def synthesizeRtlSynthCert (modName : String) (book? : Option Book) : Option RtlModule :=
  match book? with
  | some B =>
    if B.defs.isEmpty then
      none
    else
      let cands : List RtlModule :=
        (compileBookToRtlSat modName B).toList ++
        (compileRichBookToRtl modName ({} : Obend.Hardware.Types.RtlLayoutCtx) B).toList ++
        (compileBookToPipelinedRtl modName B).toList
      cands.findSome? fun m =>
        if !checkRtlModule m then none
        else
          let cand := normalizeRtlModuleForWire m
          if (checkRtlSynth 0 modName cand).isOk then some cand else none
  | none =>
    let fallback := { goldenFlatRtlModule with name := modName }
    if (checkRtlSynth 0 modName fallback).isOk then some fallback else none

/-! ## 7. Registered `autoCertFormats` & `.obend` AST Query Extractors -/

/-- Complete list of external certificate formats registered for `AutoCert` and `Workbook`. -/
@[expose] def autoCertFormats : List Format :=
  [ intervalFormat
  , taylorModelFormat
  , autoSosLyapunovFormat
  , groebnerFormat
  , rtlSynthFormat
  , hwSynthFormat
  , Obend.Lower.format ] ++
  defaultExternalFormats ++
  hardwareFormats

/-- Split a conjunction `a && b && c` in `.obend` `given` preconditions into atomic conjuncts. -/
@[expose] def splitSyntaxConjuncts : Syntax.Expr → List Syntax.Expr
  | .binary "&&" a b => splitSyntaxConjuncts a ++ splitSyntaxConjuncts b
  | .bool true       => []
  | e                => [e]

/-- Unwrap `.obend` `claim ... given COND: BODY` (decoded by `Syntax.decodeDecl` into
`Syntax.Expr.ite COND BODY (.bool true)`), returning `(givenConjuncts, innerBody)`. -/
@[expose] def unwrapSyntaxGiven : Syntax.Expr → List Syntax.Expr × Syntax.Expr
  | .ite cond body (.bool true) =>
    let (moreHyps, inner) := unwrapSyntaxGiven body
    (splitSyntaxConjuncts cond ++ moreHyps, inner)
  | e => ([], e)

/-- Extract an identifier / member field variable name from a `Syntax.Expr`. -/
@[expose] def syntaxVarName? : Syntax.Expr → Option String
  | .var v      => some v
  | .member _ f => some f
  | _           => none

/-- Extract a rational constant literal (or `0n - c` negative literal) from a `Syntax.Expr`. -/
@[expose] def syntaxRatConst? : Syntax.Expr → Option CanonicalRat
  | .nat s => (autoParseNat? s).map fun n => Rat.ofInt (Int.ofNat n)
  | .binary "-" (.nat "0") (.nat s) => (autoParseNat? s).map fun n => Rat.ofInt (-Int.ofNat n)
  | _ => none

/-- True if `fn` is a known univariate transcendental intrinsic in `TaylorModelExpr`. -/
@[expose] def isTranscendentalIntrinsicName (fn : String) : Bool :=
  fn == "sin" || fn == "cos" || fn == "exp" || fn == "ln1p" || fn == "sqrt1p"

/-- Collect distinct variable/member names appearing in a `Syntax.Expr` (excluding transcendental callees). -/
@[expose] def collectSyntaxVars : Syntax.Expr → List String
  | .var v => [v]
  | .member _ f => [f]
  | .call (.var fn) args =>
    if isTranscendentalIntrinsicName fn then
      args.flatMap collectSyntaxVars
    else
      fn :: args.flatMap collectSyntaxVars
  | .call callee args => collectSyntaxVars callee ++ args.flatMap collectSyntaxVars
  | .binary _ a b => collectSyntaxVars a ++ collectSyntaxVars b
  | .ite c t f => collectSyntaxVars c ++ collectSyntaxVars t ++ collectSyntaxVars f
  | _ => []

/-- Collect variable names referenced in a `RealExpr`. -/
@[expose] def realExprVars : RealExpr → List String
  | .const _ => []
  | .var v   => [v]
  | .add a b => realExprVars a ++ realExprVars b
  | .sub a b => realExprVars a ++ realExprVars b
  | .mul a b => realExprVars a ++ realExprVars b
  | .sqr a   => realExprVars a

/-- Convert an `.obend` `Syntax.Expr` into a `RealExpr` when it lies in the algebraic fragment. -/
@[expose] def syntaxExprToRealExpr : Syntax.Expr → Option RealExpr
  | .nat s => (autoParseNat? s).map fun n => .const (Rat.ofInt (Int.ofNat n))
  | .var v => some (.var v)
  | .member _ f => some (.var f)
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

/-- Parse a single `given` bound hypothesis (`v <= c`, `c <= v`, `v >= c`, `c >= v`, `v < c`, `c < v`, `v == c`)
into `GivenBoundAcc`; fails closed (`none`) on unrecognized or non-box hypotheses. -/
@[expose] def parseSingleIntervalHyp (acc : GivenBoundAcc) (h : Syntax.Expr) : Option GivenBoundAcc :=
  match h with
  | .binary "<=" a b | .binary "<" a b =>
    match syntaxVarName? a, syntaxRatConst? b with
    | some v, some c => some (updateGivenUpper v c acc)
    | _, _ =>
      match syntaxRatConst? a, syntaxVarName? b with
      | some c, some v => some (updateGivenLower v c acc)
      | _, _ => none
  | .binary ">=" a b | .binary ">" a b =>
    match syntaxVarName? a, syntaxRatConst? b with
    | some v, some c => some (updateGivenLower v c acc)
    | _, _ =>
      match syntaxRatConst? a, syntaxVarName? b with
      | some c, some v => some (updateGivenUpper v c acc)
      | _, _ => none
  | .binary "==" a b =>
    match syntaxVarName? a, syntaxRatConst? b with
    | some v, some c => some (updateGivenUpper v c (updateGivenLower v c acc))
    | _, _ =>
      match syntaxRatConst? a, syntaxVarName? b with
      | some c, some v => some (updateGivenUpper v c (updateGivenLower v c acc))
      | _, _ => none
  | _ => none

/-- Build a verified variable box `List (String × Interval)` from `given` hypotheses `hyps`.
**Fails closed**: a variable the hypotheses do not bound above has no box and the claim is not
synthesizable (until 2026-11-04 such a variable was silently boxed to `[0, 1]`, so a claim quantified
over all `Nat` was "certified" on `[0, 1]`). Unbounded rays `[lo, +∞)` and contradictory boxes
`lo > hi` are refused likewise; the lower bound defaults to `0` because claim parameters are `Nat`. -/
@[expose] def extractIntervalEnvFromHyps
    (envVars : List String)
    (hyps : List Syntax.Expr) : Option (List (String × Interval)) := do
  let acc ← hyps.foldlM parseSingleIntervalHyp []
  -- Ensure every variable constrained in `hyps` is included even if cancelled in the goal expression
  let allVars := (envVars ++ acc.map Prod.fst).eraseDups
  allVars.mapM fun v =>
    match acc.find? (fun (w, _) => w == v) with
    | none => none
    | some (_, hasLo, lo, hasHi, hi) =>
      if !hasHi then
        none
      else
        let finalLo : CanonicalRat := if hasLo then lo else 0
        if decide (finalLo ≤ hi) then
          some (v, ⟨finalLo, hi⟩)
        else
          none

/-- Extract an `IntervalObj` from an optional `Syntax.Expr` (an Isar step's proposition, including
`given COND: BODY` box hypotheses over `lhs <= rhs`, `lhs >= rhs`, `lhs < rhs`, or `lhs == rhs`).
Fails closed (`none`) when there is no proposition, on `.bool true`/`.bool false`, on unbounded or
contradictory `given` guards, and on syntax outside the `+`/`*`/literal fragment. A step without
variables (`4n * 2n <= 9n`) has the empty environment; it is not given a phantom variable. Claims (which have
a `ClaimObj`) do not come through here: see `claimIntervalObj?`. -/
@[expose] def extractIntervalObjFromSyntax : Option Syntax.Expr → Option IntervalObj
  | none => none
  | some (.bool true) => none
  | some (.bool false) => none
  | some rawExpr =>
    let (hyps, body) := unwrapSyntaxGiven rawExpr
    match body with
    | .binary "<=" lhs rhs => do
      let rl ← syntaxExprToRealExpr lhs
      let rr ← syntaxExprToRealExpr rhs
      let diff := RealExpr.sub rl rr
      let vs := (realExprVars diff).eraseDups
      let env ← extractIntervalEnvFromHyps vs hyps
      let safeLo := computeIntervalSafeLo env diff
      some { expr := diff, env := env, claimedBound := ⟨safeLo, 0⟩ }
    | .binary ">=" lhs rhs => do
      let rl ← syntaxExprToRealExpr lhs
      let rr ← syntaxExprToRealExpr rhs
      let diff := RealExpr.sub rr rl
      let vs := (realExprVars diff).eraseDups
      let env ← extractIntervalEnvFromHyps vs hyps
      let safeLo := computeIntervalSafeLo env diff
      some { expr := diff, env := env, claimedBound := ⟨safeLo, 0⟩ }
    | .binary "<" lhs rhs => do
      let rl ← syntaxExprToRealExpr lhs
      let rr ← syntaxExprToRealExpr rhs
      let diff := RealExpr.sub rl rr
      let vs := (realExprVars diff).eraseDups
      let env ← extractIntervalEnvFromHyps vs hyps
      let safeLo := computeIntervalSafeLo env diff
      some { expr := diff, env := env, claimedBound := ⟨safeLo, CanonicalRat.mk (-1) 1000⟩ }
    | .binary "==" lhs rhs => do
      let rl ← syntaxExprToRealExpr lhs
      let rr ← syntaxExprToRealExpr rhs
      let diff := RealExpr.sub rl rr
      let vs := (realExprVars diff).eraseDups
      let env ← extractIntervalEnvFromHyps vs hyps
      some { expr := diff, env := env, claimedBound := ⟨0, 0⟩ }
    | _ => none

/-! `taylor-model@1` has no claim surface. The `.obend` language has no transcendental functions:
in a claim, `sin(x)` is a call to whatever `Nat`-valued `def sin` the module declares. A Taylor
model of the real sine certifies nothing about that claim, so nothing is synthesized from syntax
or from a `ClaimObj`; the format stays usable on the wire (`taylorModelFormat`). Until 2026-11-04 a
fixed query (`cos + sin` on `[-1/10, 1/10]`) was substituted for the claim. -/

/-- Convert an `.obend` `Syntax.Expr` into a multivariate `Poly` under variable table `varEnv`. -/
@[expose] def syntaxExprToPolyWithEnv (varEnv : List (String × Nat)) : Syntax.Expr → Option Poly
  | .nat s => (autoParseNat? s).map fun n => polyConst (Rat.ofInt (Int.ofNat n))
  | .var v => (varEnv.lookup v).map fun idx => polyVarPow idx 1
  | .member _ f => (varEnv.lookup f).map fun idx => polyVarPow idx 1
  | .binary "+" a b => do
    pure (Poly.add (← syntaxExprToPolyWithEnv varEnv a) (← syntaxExprToPolyWithEnv varEnv b))
  | .binary "-" a b => do
    pure (Poly.sub (← syntaxExprToPolyWithEnv varEnv a) (← syntaxExprToPolyWithEnv varEnv b))
  | .binary "*" a b => do
    pure (Poly.mul (← syntaxExprToPolyWithEnv varEnv a) (← syntaxExprToPolyWithEnv varEnv b))
  | _ => none

/-- Default 3-variable compatibility wrapper for `syntaxExprToPolyWithEnv`. -/
@[expose] def syntaxExprToPoly (e : Syntax.Expr) : Option Poly :=
  let vars := (collectSyntaxVars e).eraseDups
  syntaxExprToPolyWithEnv vars.zipIdx e

/-- Parse polynomial equality (`a == b`) and inequality (`a <= b`, `a >= b`) `given` hypotheses
into `(eqGens, ineqGens)`; fails closed (`none`) on unrecognized hypotheses. -/
@[expose] def parsePolyGivenHyps (varEnv : List (String × Nat)) (hyps : List Syntax.Expr) :
    Option (List Poly × List Poly) :=
  hyps.foldlM
    (fun (eqs, ineqs) h =>
      match h with
      | .binary "==" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some (eqs ++ [Poly.sub pl pr], ineqs)
      | .binary "<=" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some (eqs, ineqs ++ [Poly.sub pr pl])
      | .binary ">=" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some (eqs, ineqs ++ [Poly.sub pl pr])
      | _ => none)
    ([], [])

/-! `sos-lyapunov-cbf@1` has no claim surface either. Its object is a Lyapunov / barrier / DAE
specification (a vector field, `V`, `B`, constraint manifold), which no `.obend` claim states; until
2026-11-04 `goldenSosProblem` with a rescaled `V` was substituted for the claim's polynomial, so the
judge verified a problem unrelated to the claim. Polynomial inequalities in a claim go to
`groebner@1` (Positivstellensatz non-negativity). -/

/-- Extract a `GroebnerQuery` from an optional `Syntax.Expr` (`lhs == rhs` ideal membership or
`lhs <= rhs` / `lhs >= rhs` Positivstellensatz non-negativity over arbitrary distinct variables,
including `given` polynomial equality/inequality generators!).
Fails closed (`none`) on `.bool false` or unparseable syntax. -/
@[expose] def extractGroebnerQueryFromSyntax : Option Syntax.Expr → Option GroebnerQuery
  | none => none
  | some (.bool true) => none
  | some (.bool false) => none
  | some rawExpr =>
    let (hyps, body) := unwrapSyntaxGiven rawExpr
    let vars := (hyps.flatMap collectSyntaxVars ++ collectSyntaxVars body).eraseDups
    let varEnv := vars.zipIdx
    match parsePolyGivenHyps varEnv hyps with
    | none => none
    | some (eqGens, ineqGens) =>
      match body with
      | .binary "==" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some { target := Poly.sub pl pr, eqGens := eqGens, ineqGens := ineqGens, isNonneg := false, divFuel := 32 }
      | .binary "<=" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some { target := Poly.sub pr pl, eqGens := eqGens, ineqGens := ineqGens, isNonneg := true, divFuel := 32 }
      | .binary ">=" lhs rhs => do
        let pl ← syntaxExprToPolyWithEnv varEnv lhs
        let pr ← syntaxExprToPolyWithEnv varEnv rhs
        some { target := Poly.sub pl pr, eqGens := eqGens, ineqGens := ineqGens, isNonneg := true, divFuel := 32 }
      | _ => none

/-- Synthesize the `(objWire, certWire)` pair for a judge format tag. For a claim (`co? = some co`)
the object is read from the claim's Core4 body (`claimIntervalObj?`, `claimGroebnerQuery?`), which is
what `bindsClaim` re-derives at check time; for an Isar step (`co? = none`) from the step's syntax.
`taylor-model@1` and `sos-lyapunov-cbf@1` have no claim or step surface (§7b); `rtl-synth@1` /
`hw-rtl-synth@1` certify that the module's book synthesizes, which is a proposition about the book
and not about a claim, so they accept only the step proposition `true` and no claim. Fails closed
(`none`) whenever the extracted query is invalid or has no valid witness. -/
@[expose] def synthesizeJudgeWirePair
    (tag : String)
    (modName : String)
    (expr? : Option Syntax.Expr)
    (book? : Option Book)
    (co? : Option ClaimObj := none) : Option (String × String) :=
  if tag == "interval@1" then do
    let q ← match co? with
      | some co => claimIntervalObj? co
      | none => extractIntervalObjFromSyntax expr?
    let cert ← synthesizeIntervalCert 4 q
    some (encodeIntervalObj q, encodeIntervalCert cert)
  else if tag == "groebner@1" then do
    let q ← match co? with
      | some co => claimGroebnerQuery? co
      | none => extractGroebnerQueryFromSyntax expr?
    let cert ← synthesizeGroebnerCert q
    some (encodeGroebnerQuery q, encodeGroebnerCert cert)
  else if tag == "rtl-synth@1" || tag == "hw-rtl-synth@1" then
    match co?, expr? with
    | none, some (.bool true) =>
      let safeMod := if modName.isEmpty then "obend_rtl_top" else modName
      match synthesizeRtlSynthCert safeMod book? with
      | some rtlMod => some (encodeRtlSynthObj safeMod, encodeRtlSynthCert rtlMod)
      | none => none
    | _, _ => none
  else
    none

/-- Infer which external judge format tags a claim requests:
- When `claimDecl? = some cd`, strictly returns ONLY explicit `by judge(fmt)` tags declared on `cd`
  (never falling through to unrelated judges or overriding `by weave` / untagged claims).
- When `claimDecl? = none` (programmatic invocation), uses name hints or registered `AutoCert` tags. -/
@[expose] def inferClaimJudgeTags (claimName : String) (claimDecl? : Option Syntax.Claim) : List String :=
  match claimDecl? with
  | some cd =>
    let mTag := match cd.method with
      | some (.judge fmt) => [fmt]
      | _ => []
    let sTags := Elaborate.extractIsarJudgeTags cd.steps
    mTag ++ sTags
  | none =>
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
    if !nameHintTags.isEmpty then nameHintTags
    else ["interval@1", "taylor-model@1", "sos-lyapunov-cbf@1", "groebner@1", "rtl-synth@1", "hw-rtl-synth@1"]

/-! ## 8. `synthesizeClaimJudgeTag`, `synthesizeContractExternalJudges` & Master Soundness Theorem -/

/-- Attempt to synthesize a kernel-verified `Justification.byExternalJudge` for a `ClaimObj` `co`
from tag `tag`, strictly gated by `obligationCheckWithJudges formats grade co just == .ok`. -/
@[expose] def synthesizeClaimJudgeTag
    (formats : List Format)
    (grade : Nat)
    (modName : String)
    (expr? : Option Syntax.Expr)
    (book? : Option Book)
    (co : ClaimObj)
    (tag : String) : Option Justification := do
  let (objStr, certStr) ← synthesizeJudgeWirePair tag modName expr? book? (some co)
  let just := Justification.byExternalJudge tag (mkExternalJudgePayload objStr certStr)
  if obligationCheckWithJudges formats grade co just == .ok then
    some just
  else
    none

/-- Attempt to synthesize a kernel-verified `Justification.byExternalJudge` for a `ClaimObj` `co`,
strictly gated by `obligationCheckWithJudges formats grade co just == .ok`. -/
@[expose] def synthesizeClaimExternalJudge
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
  cases hPair : synthesizeJudgeWirePair tag modName expr? book? (some co) with
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

/-- True when `tag` is one of the 5 automatically synthesized external judge formats in `Obend.Elab.AutoCert`. -/
@[expose] def isSynthesizableAutoCertTag (tag : String) : Bool :=
  tag == "interval@1" ||
  tag == "taylor-model@1" ||
  tag == "sos-lyapunov-cbf@1" ||
  tag == "groebner@1" ||
  tag == "rtl-synth@1" ||
  tag == "hw-rtl-synth@1"

/-- Extract `(tag, prop?)` pairs from all `by judge(tag)` steps and header method of a `Syntax.ContractDecl`. -/
@[expose] def extractContractJudgeRequests (c : Syntax.ContractDecl) : List (String × Option Syntax.Expr) :=
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
@[expose] def synthesizeContractExternalJudges
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

/-- Check that EVERY synthesizable `by judge(tag)` request in a `Syntax.ContractDecl` (both header
`c.method` and every Isar step in `c.steps`) synthesizes a `(objWire, certWire)` certificate
accepted by its kernel `Judge.Format` (`F.checkBytes 0 objWire certWire == .ok`).
Fails closed (`false`) if any synthesizable judge request fails synthesis or check! -/
@[expose] def verifyContractAutoCertSteps
    (formats : List Format := autoCertFormats)
    (modName : String := "obend_rtl_top")
    (book? : Option Book := none)
    (c : Syntax.ContractDecl) : Bool :=
  let reqs := extractContractJudgeRequests c
  reqs.all fun (tag, prop?) =>
    if isSynthesizableAutoCertTag tag then
      match findFormat formats tag with
      | none => false
      | some F =>
        match synthesizeJudgeWirePair tag modName prop? book? with
        | some (objWire, certWire) => (Format.checkBytes F 0 objWire certWire).isOk
        | none => false
    else
      true

/-- Check whether a judge format tag is supported by `AutoCert` or `autoCertFormats`. -/
@[expose] def isAutoCertAdmittedJudgeTag (formats : List Format := autoCertFormats) (tag : String) : Bool :=
  (findFormat formats tag).isSome

end Obend.Elab.AutoCert
end
