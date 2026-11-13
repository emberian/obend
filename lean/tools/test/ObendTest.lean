/-
# `obend-test` — Compiled Native Runtime Test Runner (Tier 2A)

Executes runtime verification suites across Obend's subsystems as compiled native C/machine code
(`lake exe obend-test`), exercising `@[csimp]` fast paths (`Core.Machine.runBounded`,
`Core.Data.forceWith`, `Digest.Cshake256.cshake256Bytes`, `Crypto.BinaryTower256.towerMul`,
`Doc.Graph.beforeB`, `Vault.Store.{quiet,pendingAt,writesFor,overwrite}`, `Run.Core4.turn`)
at native speed in milliseconds without elaborator `#eval` heap overhead.

Every suite receives an opaque runtime zero (`runtimeZero : IO Nat`) derived from the monotonic clock
so the compiler cannot constant-fold or hoist closed test expressions into module initialization;
all reported per-suite timings measure genuine runtime execution inside `runSuite`.
-/
import Obend.Core.MachineFast
import Obend.Core.Data
import Obend.Core.Digest
import Obend.Core.FiniteBisimulation
import Obend.Core.Proofs.BidirectionalCompleteness
import Obend.Digest.Cshake256.Seam
import Obend.Digest.Cshake256.Fast
import Obend.Leaf.BytecodeRegisterJit
import Obend.Leaf.SelfApplicableMix
import Obend.Crypto.FastRing
import Obend.Crypto.BinaryTower256
import Obend.Elab.Coerce
import Obend.Elab.Prepare
import Obend.Spec.C4
import Obend.Spec.Law
import Obend.Doc.Graph
import Obend.Doc.Patch
import Obend.Doc.Merge
import Obend.Doc.Section
import Obend.Doc.Backlinks
import Obend.Vault.Hyperedge
import Obend.Vault.Branch
import Obend.Vault.Store
import Obend.Run.Core4
import Obend.Run.Negotiation
import Obend.Run.HyperLaw
import Obend.Hardware.OpenHypergraph
import Obend.Hardware.ReductionMachine
import Obend.Hardware.Kinematics
import Obend.SymbolicZk.CamUnifyArith
import Obend.SymbolicZk.RankedFixpointArith
import Obend.SymbolicZk.SemiringDatalog
import Obend.Trailblaze.StageBInstances

set_option autoImplicit false

namespace ObendTest

/-- Opaque runtime zero (`0`) derived from `IO.monoNanosNow` to prevent compiler `_closed_*`
hoisting of suite expressions into module initialization. -/
@[noinline] def runtimeZero : IO Nat := do
  let ns ← IO.monoNanosNow
  return (if ns == 0 && ns == 1 then 1 else 0)

def formatMicros (ns : Nat) : String :=
  let us := ns / 1000
  let msWhole := us / 1000
  let msFrac := (us % 1000) / 10
  let fracStr := if msFrac < 10 then s!"0{msFrac}" else s!"{msFrac}"
  s!"{msWhole}.{fracStr} ms"

def runSuite (suiteName : String) (checks : Nat → List (String × Bool)) : IO (Nat × Nat × Nat) := do
  let z ← runtimeZero
  let t0 ← IO.monoNanosNow
  let results := checks z
  let mut passed := 0
  let mut failed := 0
  for (label, ok) in results do
    if ok then
      passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"  [FAIL] {suiteName} :: {label}"
  let t1 ← IO.monoNanosNow
  let dt := t1 - t0
  let status := if failed == 0 then "PASS" else "FAIL"
  IO.println s!"[{status}] {suiteName} ({passed}/{passed + failed} assertions, {formatMicros dt})"
  return (passed, failed, dt)

/-! ## Suite 1: `Core.MachineFast` & `Core.Data` (`@[csimp]` `runBounded` / `forceWith`) -/

section CoreMachineSuite
open Obend.Core.Term Obend.Core.Machine Obend.Core.Data

def coreLimits : Limits := ⟨4096, 256⟩
def coreBudget : Budget := ⟨1024, 256, 65536⟩

-- `(λ f. λ x. f (f x)) (λ y. y + 7) (10 + z)` -> `24 + z`
def churchTwoAdd7 (z : Nat) : Term :=
  .app
    (.app
      (.lam (.lam (.app (.bound 1) (.app (.bound 1) (.bound 0)))))
      (.lam (.binary .add (.bound 0) (.nat 7))))
    (.nat (10 + z))

-- Shared record projection `{ a = 6 * 7, b = 99 }.a + (8 + z)` -> `50 + z`
def recordProjTerm (z : Nat) : Term :=
  .binary .add
    (.get (.record [("a", .binary .multiply (.nat 6) (.nat 7)), ("b", .nat 99)]) "a")
    (.nat (8 + z))

def coreMachineChecks (z : Nat) : List (String × Bool) :=
  let s1 := initial (churchTwoAdd7 z)
  let out1 := runBounded coreLimits (64 + z) s1
  let (forced2, remTicks) := forceWith (fun _ => true) coreLimits (64 + z) (initial (recordProjTerm z))
  let mat1 :=
    match forced2 with
    | .finished v st =>
      match materializeWith (fun _ => true) coreLimits 32 coreBudget v st with
      | .ok ⟨.natural n, _, _⟩ => n == 50 + z
      | _ => false
    | _ => false
  [ ("runBounded (@[csimp] runBoundedFast) evaluates churchTwoAdd7 to 24",
      match out1 with | .finished (.natural n) _ => n == 24 + z | _ => false)
  , ("forceWith (@[csimp] forceWithFast) evaluates shared record projection to 50",
      mat1 && remTicks < 64 + z)
  , ("tick budget 0 suspends immediately without stepping",
      match runBounded coreLimits z s1 with | .suspended .ticks st => st.heap.size == 0 | _ => false)
  , ("tick budget 1 suspends cleanly mid-reduction",
      match runBounded coreLimits (1 + z) s1 with | .suspended .ticks _ => true | _ => false)
  , ("tight heap/stack capacity (1, 1) suspends with .capacity",
      match runBounded ⟨1, 1⟩ (64 + z) (initial (recordProjTerm z)) with
      | .suspended .capacity _ => true | _ => false)
  ]
end CoreMachineSuite

/-! ## Suite 2: `Core.FiniteBisimulation` (Evicted Worklist Probes) -/

section FiniteBisimSuite
open Obend.Core.FiniteBisimulation Obend.Core.FiniteBisimulation.Probes

@[noinline] def opaqueId {α : Type} (z : Nat) (x : α) : α :=
  if z == 999999999 then x else x

def finiteBisimChecks (z : Nat) : List (String × Bool) :=
  [ ("visitedSame accepts differentPeriods", visitedSame (opaqueId z differentPeriods) 0 1)
  , ("visitedSame rejects reachableMismatch", !(visitedSame (opaqueId z reachableMismatch) 0 1))
  , ("visitedSame rejects arityMismatch", !(visitedSame (opaqueId z arityMismatch) 0 1))
  ]
end FiniteBisimSuite

/-! ## Suite 3: `Digest.Cshake256.Fast` & `Core.Digest` (`@[csimp]` Keccak-f[1600]) -/

section DigestSuite
open Obend.Digest.Cshake256 Obend.Digest.Cshake256.Fast Obend.Core.Digest

def digestChecks (z : Nat) : List (String × Bool) :=
  let msgEmpty : List UInt8 := List.replicate z 0
  let msgShort : List UInt8 := [0x61, 0x62, UInt8.ofNat (0x63 + z)]
  let mkBytes (n : Nat) : List UInt8 := (List.range (n + z)).map (fun i => UInt8.ofNat (i % 251))
  let cust : List UInt8 := "OBEND.TEST/v1".toUTF8.data.toList
  let dEmptyMsg := cshake256Bytes [] msgEmpty
  let dShort := cshake256Bytes [] msgShort
  let d135 := cshake256Bytes cust (mkBytes 135)
  let d136 := cshake256Bytes cust (mkBytes 136)
  let d137 := cshake256Bytes cust (mkBytes 137)
  let d300 := cshake256Bytes cust (mkBytes 300)
  [ ("cshake256Bytes (@[csimp] cshake256Native) agrees with cshake256Fast on empty & 3-byte inputs",
      dEmptyMsg == cshake256Fast [] msgEmpty &&
      dShort == cshake256Fast [] msgShort &&
      dEmptyMsg != dShort && dShort.length == 32)
  , ("cshake256Bytes agrees with cshake256Fast across exact Keccak rate boundary (135, 136, 137 bytes)",
      d135 == cshake256Fast cust (mkBytes 135) &&
      d136 == cshake256Fast cust (mkBytes 136) &&
      d137 == cshake256Fast cust (mkBytes 137) &&
      d135 != d136 && d136 != d137)
  , ("cshake256Bytes agrees with cshake256Fast on 300-byte multi-block input",
      d300 == cshake256Fast cust (mkBytes 300) && d300 != d137)
  , ("deployed digest (1, 1) matches KAT",
      digest (1 + z) 1 == 33544760771157370539093351361262075193213937251298462105196476525256921960532)
  , ("ballot seal (voter 1, YES, salt 111) matches KAT",
      digest (digest (1 + z) 1) 111 == 83370838008729781310004166183474027631933533742037976749282545846343963921357)
  , ("sealed low bit does not leak vote bit and distinct votes are non-adjacent",
      digest (digest (1 + z) 1) 101 % 2 == 0 &&
      digest (digest (1 + z) 0) 100 % 2 == 1 &&
      digest (digest (1 + z) 1) 111 != digest (digest (1 + z) 0) 111 &&
      digest (digest (1 + z) 1) 111 != digest (digest (1 + z) 0) 111 + 1)
  ]
end DigestSuite

/-! ## Suite 4: `Leaf.BytecodeRegisterJit` & `Leaf.SelfApplicableMix` (Native Loops & Futamura 1–3) -/

section LeafJitMixSuite
open Obend.Leaf.BytecodeRegisterJit Obend.Leaf.SelfApplicableMix

def leafJitMixChecks (z : Nat) : List (String × Bool) :=
  let n := 30000 + z
  let jitDirect := execBytecode sumToLoopCode #[0, UInt64.ofNat n, 0, 0, 0, 0] (180002 + z) == some 450015000
  let jitCompiled := runSumToBytecode n == some 450015000
  let fut1Ok :=
    match runMixSpecialize (400 + z) objInterp (quoteObjSrc quadPolyObjSrc) with
    | some target =>
      checkSpecializesProg 40 objInterp (quoteObjSrc quadPolyObjSrc) target &&
      !hasStaticConstruct target &&
      evalMix 40 target .nil (.num (7 + z)) == some (.num 75)
    | none => false
  let fut2Ok :=
    match runMixSpecialize (3000 + z) mixProg (quoteProg objInterp) with
    | some comp =>
      checkSpecializesProg 300 mixProg (quoteProg objInterp) comp &&
      !hasStaticConstruct comp &&
      comp.procs.length == 6
    | none => false
  let fut3Ok :=
    match runMixSpecialize (4000 + z) mixProg (quoteProg mixProg) with
    | some cogen =>
      checkSpecializesProg 280 mixProg (quoteProg mixProg) cogen &&
      !hasStaticConstruct cogen &&
      cogen.procs.length == 13
    | none => false
  [ ("execBytecode sumToLoopCode (30,000 iterations) == 450015000", jitDirect)
  , ("runSumToBytecode 30000 specializes & executes to 450015000", jitCompiled)
  , ("Futamura 1 specializes quadPolyObjSrc and evaluates x=7 -> 75", fut1Ok)
  , ("Futamura 2 self-applies mix to objInterp -> 6-proc standalone compiler", fut2Ok)
  , ("Futamura 3 self-applies mix to mixProg -> 13-proc standalone cogen", fut3Ok)
  ]
end LeafJitMixSuite

/-! ## Suite 5: `Crypto.FastRing` & `Crypto.BinaryTower256` (`@[csimp]` Karatsuba & Negacyclic Convolution) -/

section CryptoSuite
open Obend.Crypto.Fast Obend.Crypto.BinaryTower256

def cryptoChecks (z : Nat) : List (String × Bool) :=
  let pA : FastIntPoly 4 := Sized.ofFn fun i => Int.ofNat (i.val + 2 + z) - 4
  let pB : FastIntPoly 4 := Sized.ofFn fun i => Int.ofNat (5 + z) - Int.ofNat (2 * i.val)
  let prodFast := negacyclicMulFast pA pB
  let prodSpecMatches :=
    (List.finRange 4).all fun k =>
      prodFast.spec k == negacyclicSpec pA.spec pB.spec k
  let p1A : FastIntPoly 1 := Sized.ofFn fun _ => -7 + Int.ofNat z
  let p1B : FastIntPoly 1 := Sized.ofFn fun _ => 9
  let prod1Ok := (negacyclicMulFast p1A p1B).spec ⟨0, by omega⟩ == -63
  let k4 := 4 + z
  let k8 := 8 + z
  let tOne4 := towerOne k4
  let tX4 := towerX k4
  let tOne8 := towerOne k8
  let tX8 := towerX k8
  let tSum8 := towerAdd k8 tOne8 tX8
  [ ("FastRing negacyclicMulFast (d=4, signed coeffs) matches negacyclicSpec", prodSpecMatches)
  , ("FastRing negacyclicMulFast (d=1) and intSub/intAdd roundtrip",
      prod1Ok && (List.finRange 4).all fun k => (intSub (intAdd pA pB) pB).spec k == pA.spec k)
  , ("BinaryTower256 (@[csimp] towerKaratsuba) distributes at k=0, k=4 (16-bit), and k=8 (256-bit)",
      towerMul 0 (towerOne 0) (towerOne 0) == towerOne 0 &&
      towerMul k4 tX4 (towerAdd k4 tOne4 tX4) ==
        towerAdd k4 (towerMul k4 tX4 tOne4) (towerMul k4 tX4 tX4) &&
      towerMul k8 tX8 tSum8 ==
        towerAdd k8 (towerMul k8 tX8 tOne8) (towerMul k8 tX8 tX8))
  , ("BinaryTower256 multiplicative identity and GF(2) characteristic at k=8",
      towerMul k8 tSum8 tOne8 == tSum8 && towerAdd k8 tSum8 tSum8 == towerZero k8)
  ]
end CryptoSuite

/-! ## Suite 6: `Elab.Coerce` & `Elab.Prepare` (All 34 Relocated Elaborator Probes) -/

section ElabProbesSuite
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Elab.Coerce Obend.Elab.Prepare
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Term (Term)

def quantities : List Quantity := [.erased, .affine, .linear, .unrestricted]

def wrapperMeasured (q q' : Quantity) : Bool :=
  (checkAgainst ⟨.lam (.app (.bound 1) (.bound 0)),
      fun path => if path = [] then some ⟨.natural, .natural, q', .reusable⟩ else none, {}⟩
    [⟨.arrow .reusable q .natural .natural, .unrestricted⟩]
    (.arrow .reusable q' .natural .natural)).toBool

def custodyRow : Ty :=
  .field "handle" (.custody 0) (.field "tag" .natural
    (.field "extra" (.arrow .once .affine .natural .natural) .emptyRow))

def projection (q : Quantity) (kept : List String) : Bool :=
  let target := kept.foldr (fun name row => Ty.field name
    (if name == "handle" then .custody 0 else .natural) row) .emptyRow
  (checkAgainst ⟨.lam (.record (kept.map fun name => (name, .get (.bound 0) name))),
      fun path => if path = [] then some ⟨custodyRow, target, q, .once⟩ else none, {}⟩
    [] (.arrow .once q custodyRow target)).toBool

def seedRow : Ty := .field "x" .natural (.field "extra" .boolean .emptyRow)

def elabChecks (z : Nat) : List (String × Bool) :=
  let n3 := 3 + z
  let letProbe : AnnotatedTerm := ⟨.app (.lam (.bound 0)) (.nat n3), noHints, {}⟩
  let twiceProbe : AnnotatedTerm := ⟨.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat n3), noHints, {}⟩
  let storedProbe : AnnotatedTerm := ⟨.app (.get (.record [("f", .lam (.bound 0))]) "f") (.nat n3), noHints, {}⟩
  let recordParameterProbe : AnnotatedTerm :=
    ⟨.app (.get (.record [("f", .lam (.get (.bound 0) "x"))]) "f") (.record [("x", .nat (1 + z))]), noHints, {}⟩
  let treeDropRefused :=
    match checkAgainst ⟨.lam (.lam (.app (.lam (.record [("x", .get (.bound 0) "x")])) (.app (.bound 1) (.bound 0)))),
        treeAnnotations (.node (some ⟨.arrow .reusable .linear .natural seedRow,
            .arrow .reusable .linear .natural (.field "x" .natural .emptyRow), .unrestricted, .reusable⟩)
          [.node (some ⟨.natural, .field "x" .natural .emptyRow, .linear, .reusable⟩)
            [.node (some (hint (.arrow .reusable .affine seedRow (.field "x" .natural .emptyRow)) (.field "x" .natural .emptyRow)))
              [.node (some ⟨seedRow, .field "x" .natural .emptyRow, .affine, .reusable⟩)
                [.node (some (hint .emptyRow (.field "x" .natural .emptyRow))) [.node none [.node none []]]],
               .node (some (hint (.arrow .reusable .linear .natural seedRow) seedRow)) [.node none [], .node none []]]]]), {}⟩
      [] (.arrow .reusable .unrestricted (.arrow .reusable .linear .natural seedRow)
        (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow))) with
    | .error (.linearArgumentDropped _ 0 .affine) => true | _ => false
  [ ("Coerce 4x4 wrapperMeasured matrix, linear filter, launders characterization & wrapperAllowed",
      (quantities.map fun q => quantities.map fun q' => wrapperMeasured q q') ==
        [[false, true, false, true], [false, true, false, true], [false, true, true, true], [false, false, false, true]] &&
      (quantities.filter fun q => wrapperMeasured q .linear) == [.linear] &&
      quantities.all (fun q => quantities.all fun q' =>
        launders q q' == (q' == .linear && q != .linear && q != .unrestricted)) &&
      quantities.all (fun q => quantities.all fun q' => wrapperMeasured q q' == wrapperAllowed q q'))
  , ("Coerce linearArgumentDropped named refusal on erased/affine",
      [Quantity.erased, .affine].all fun q =>
        match checkAgainst ⟨.lam (.app (.bound 1) (.bound 0)),
            fun path => if path = [] then some ⟨.natural, .natural, .linear, .reusable⟩ else none, {}⟩
          [⟨.arrow .reusable q .natural .natural, .unrestricted⟩] (.arrow .reusable .linear .natural .natural) with
        | .error (.linearArgumentDropped [0, 1] 0 q') => q' == q
        | _ => false)
  , ("Coerce custodyRow single-field affine ok, two-field needsSharing refused",
      projection .affine ["handle"] && projection .affine ["tag"] &&
      quantities.all (fun q => !projection q ["handle", "tag"]) &&
      (coerce {} custodyRow (.field "handle" (.custody 0) .emptyRow)).toBool &&
      (match coerce {} custodyRow (.field "handle" (.custody 0) (.field "tag" .natural .emptyRow)) with
       | .error (.needsSharing _) => true | _ => false))
  , ("Coerce record width/depth, variant widening, and missingLabel refusal",
      (coerce {} seedRow (.field "x" .natural .emptyRow)).toBool &&
      (coerce {} seedRow (.field "extra" .boolean (.field "x" .natural .emptyRow))).toBool &&
      (coerce {} (.field "p" seedRow .emptyRow) (.field "p" (.field "x" .natural .emptyRow) .emptyRow)).toBool &&
      (coerce {} (.variant (.field "a" .natural .emptyRow))
        (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))).toBool &&
      (match coerce {} (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))
          (.variant (.field "a" .natural .emptyRow)) with
       | .error (.missingLabel "b" _) => true | _ => false))
  , ("Coerce function laundering (affine/erased -> linear), converse affine, and sum linear -> linear",
      (match coerce {} (.arrow .reusable .affine .natural seedRow)
          (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow)) with
       | .error (.launders .affine .linear) => true | _ => false) &&
      (match coerce {} (.arrow .reusable .erased .natural .natural)
          (.arrow .reusable .linear .natural .natural) with
       | .error (.launders .erased .linear) => true | _ => false) &&
      (coerce {} (.arrow .reusable .linear .natural seedRow)
        (.arrow .reusable .affine .natural (.field "x" .natural .emptyRow))).toBool &&
      (coerce {} (.arrow .reusable .affine .natural seedRow)
        (.arrow .reusable .affine .natural (.field "x" .natural .emptyRow))).toBool &&
      (coerce {} (.arrow .reusable .linear .natural (.variant (.field "a" .natural .emptyRow)))
        (.arrow .reusable .linear .natural (.variant (.field "a" .natural (.field "b" .boolean .emptyRow))))).toBool)
  , ("Coerce codomain/domain linearProjected, linearBinderUnused, treeAnnotations drop, quantityNotWrappable, reuseChanged & recursive",
      (match coerce {} (.arrow .reusable .linear .natural seedRow)
          (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow)) with
       | .error (.checker (.linearProjected _ 0)) => true | _ => false) &&
      treeDropRefused &&
      (match coerce {} (.arrow .reusable .linear (.field "x" .natural .emptyRow) .natural)
          (.arrow .reusable .linear seedRow .natural) with
       | .error (.checker (.linearProjected _ 0)) => true | _ => false) &&
      (match coerce {} (.arrow .reusable .linear .emptyRow .natural)
          (.arrow .reusable .linear seedRow .natural) with
       | .error (.checker (.linearBinderUnused _)) => true | _ => false) &&
      (match coerce {} (.arrow .reusable .unrestricted .natural .natural)
          (.arrow .reusable .affine .natural .natural) with
       | .error (.quantityNotWrappable .unrestricted .affine) => true | _ => false) &&
      (match coerce {} (.arrow .reusable .affine .natural .natural)
          (.arrow .reusable .erased .natural .natural) with
       | .error (.quantityNotWrappable .affine .erased) => true | _ => false) &&
      (match coerce {} (.arrow .once .affine .natural .natural)
          (.arrow .reusable .affine .natural .natural) with
       | .error (.reuseChanged .once .reusable) => true | _ => false) &&
      (match coerce ⟨[(0, .variant (.field "a" .boolean .emptyRow))], [], [], []⟩
          (.variant (.field "a" .natural .emptyRow)) (.variable 0) with
       | .error (.recursive _ _) => true | _ => false))
  , ("Prepare all 6 probes: missingLambdaAnnotation, letProbe, twiceProbe, silent lambda, search=1, and 72-candidate exhaustion",
      (match checkAgainst letProbe [] .natural with | .error (.missingLambdaAnnotation [0]) => true | _ => false) &&
      (prepareChecked letProbe [] .natural).toBool &&
      (prepareChecked twiceProbe [] .natural).toBool &&
      (match prepareChecked storedProbe [] .natural with | .error (.silent [0, 0, 0] "lambda") => true | _ => false) &&
      (prepareSearch (1 + z) storedProbe [] .natural).toBool &&
      (match prepareSearch (1 + z) recordParameterProbe [] .natural with
       | .error (.searchExhausted [0, 0, 0] 72) => true | _ => false))
  ]
end ElabProbesSuite

/-! ## Suite 7: `Spec.C4` & `Spec.Law` (Pommette Linearization, Refusals & Law Parser) -/

section SpecSuite
open Obend.Spec.C4

def c4Ancestry (supers : String → List String) (isSuffix : String → Bool) :
    Nat → String → Except String (List (String × List String))
  | 0, _ => .error "ancestry depth"
  | fuel + 1, x => do
    let mut known : List (String × List String) := []
    for p in supers x do
      for entry in ← c4Ancestry supers isSuffix fuel p do
        if !(known.any (·.1 == entry.1)) then known := known ++ [entry]
    let graph : Graph := ⟨fun y => (known.lookup y).getD [], isSuffix⟩
    let (list, _) ← (linearize graph [x] [supers x]).mapError Refusal.message
    return known ++ [(x, list)]

def c4PrecedenceOf (fuel : Nat) (supers : String → List String) (isSuffix : String → Bool) (x : String) :
    Option (List String) :=
  match c4Ancestry supers isSuffix fuel x with
  | .ok known => known.lookup x
  | .error _ => none

def c4Table : List (String × List String) :=
  ("O|A O|B O|C O|D O|E O|K1 A B C|K2 D B E|K3 D A|Z K1 K2 K3|J1 C A B|J2 B D E|J3 A D|Y J1 J3 J2|DB B|WB B|" ++
   "EL DB|SM DB|PWB EL WB|SC SM|P PWB SC|GL O|HG GL|VG GL|HVG HG VG|VHG VG HG|HH|GG HH|II GG|FF HH|EE HH|" ++
   "DD FF|CC EE FF GG|BB|AA BB CC DD|o O|a o|b a|c b o|d D c|M A B b a|N C c|L M N|k D L|j E k A|I N M|x1|x2 x1|" ++
   "x3 x2|x4 x3|x5 x4 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBB").splitOn "|" |>.map fun row =>
    match row.splitOn " " with
    | x :: ps => (x, ps)
    | [] => ("", [])

def c4Expected : List String :=
  ("O|A O|B O|C O|D O|E O|K1 A B C O|K2 D B E O|K3 D A O|Z K1 K2 K3 D A B C E O|J1 C A B O|J2 B D E O|J3 A D O|" ++
   "Y J1 C J3 A J2 B D E O|DB B O|WB B O|EL DB B O|SM DB B O|PWB EL DB WB B O|SC SM DB B O|P PWB EL SC SM DB WB B O|" ++
   "GL O|HG GL O|VG GL O|HVG HG VG GL O|VHG VG HG GL O|HH|GG HH|II GG HH|FF HH|EE HH|DD FF HH|CC EE FF GG HH|BB|" ++
   "AA BB CC EE DD FF GG HH|o O|a o O|b a o O|c b a o O|d D c b a o O|M A B b a o O|N C c b a o O|" ++
   "L M A B N C c b a o O|k D L M A B N C c b a o O|j E k D L M A B N C c b a o O|I N C M A B c b a o O|x1|x2 x1|" ++
   "x3 x2 x1|x4 x3 x2 x1|x5 x4 x3 x2 x1|SBA|SBB|SBS SBA|sBs SBA|SBC SBS SBA SBB").splitOn "|"

def specChecks (z : Nat) : List (String × Bool) :=
  let fuel := 64 + z
  let supers (x : String) := (c4Table.lookup x).getD []
  let isStruct (x : String) := match x.toList.head? with | some c => 'a' ≤ c && c ≤ 'z' | none => false
  let pommetteOk := c4Expected.all fun line =>
    let names := line.splitOn " "
    c4PrecedenceOf fuel supers isStruct names.head! == some names
  let refusalsOk :=
    c4PrecedenceOf fuel (fun x => if x == "CG" then ["HVG", "VHG"] else supers x) isStruct "CG" == none &&
    c4PrecedenceOf fuel (fun x => if x == "SBc" then ["sBs", "SBB"] else supers x) isStruct "SBc" == none
  let lawTallyOk :=
    (Obend.Spec.Law.parse "new.total <= 1000 and monotone(total)").toOption ==
      some (.and (.leC (.field "total") 1000) (.monotone "total"))
  let lawPrecOk :=
    (Obend.Spec.Law.parse "not new.a == 1 or new.b in [1, -2] implies request.caller == new.c and new.d <= new.e + 3").toOption ==
      some (.implies (.or (.not (.eqC (.field "a") 1)) (.inC (.field "b") [1, -2]))
        (.and (.eqR .caller (.field "c")) (.leROff (.field "d") (.field "e") 3)))
  let lawRefuseOk :=
    [ "new.a.b == 1", "old.a == 1", "new.a < 1", "new.a + 1 <= new.b",
      "witnessed(x)", "monotone(request.caller)" ].all fun s =>
      !(Obend.Spec.Law.parse s).toBool
  [ ("C4 pommette 53 published precedence vectors match", pommetteOk)
  , ("C4 inconsistent local order (CG) and incompatible suffix (SBc) refuse", refusalsOk)
  , ("Spec.Law parser parses tally & operator precedence accurately", lawTallyOk && lawPrecOk)
  , ("Spec.Law parser refuses all 6 out-of-fragment constructs", lawRefuseOk)
  ]
end SpecSuite

/-! ## Suite 8: `Doc` (`Graph.beforeB` `@[csimp]`, Tombstones/Cycles, `Merge`, `Section`, `Backlinks`) -/

section DocSuite
open Obend.Doc

def docChecks (z : Nat) : List (String × Bool) :=
  let a1 := 1 + z
  let a2 := 2 + z
  let a3 := 3 + z
  let a4 := 4 + z
  let gBase : Graph :=
    { atoms := [(a1, .text "Hello "), (a2, .text "world ^blk1\nLine two")]
    , dead := []
    , edges := [(0, a1), (a1, a2)] }
  let gLeft : Graph :=
    { atoms := gBase.atoms ++ [(a3, .text "!")]
    , dead := []
    , edges := gBase.edges ++ [(a2, a3)] }
  let gRight : Graph :=
    { atoms := gBase.atoms ++ [(a4, .field "status" "verified")]
    , dead := []
    , edges := gBase.edges }
  let gMerged := Graph.merge gLeft gRight
  let gDeadBridge : Graph :=
    { atoms := gLeft.atoms, dead := [a2], edges := gLeft.edges }
  let gCycle : Graph :=
    { atoms := [(a1, .text "x"), (a2, .text "y")]
    , dead := []
    , edges := [(0, a1), (a1, a2), (a2, a1)] }
  let deps := [("pageB", "pageA"), ("pageC", "pageB"), ("pageD", "pageC")]
  let closure := impactedClosureFuel (8 + z) deps ["pageA"]
  [ ("Doc.Graph.beforeB (@[csimp] beforeBFast) orders chain, conducts through tombstones, and terminates on cycles",
      gMerged.beforeB a1 a3 && !gMerged.beforeB a3 a1 &&
      gDeadBridge.beforeB a1 a3 && gDeadBridge.isDead a2 &&
      gCycle.beforeB a1 a2 && !gCycle.beforeB a1 99)
  , ("Doc.Graph.merge pushout preserves both text atom 3 and field atom 4",
      gMerged.present a3 && gMerged.present a4 && Graph.compatB gLeft gRight)
  , ("Doc.Section block quote extracts ^blk1 line bytes",
      (quoteOf gBase (.block "blk1")).isSome && (quoteOf gBase (.block "missing")).isNone)
  , ("Doc.Backlinks transitive impact closure reaches pageD from pageA",
      closure.contains "pageB" && closure.contains "pageC" && closure.contains "pageD")
  ]
end DocSuite

/-! ## Suite 9: `Vault` (`Store` `@[csimp]` Indexed Fast Paths, `Hyperedge`, `Branch.MergeKind`) -/

section VaultSuite
open Obend.Vault

def vaultChecks (z : Nat) : List (String × Bool) :=
  let s0 := updateStore (updateStore emptyStore "acct/alice" (some (.natural (100 + z)))) "acct/bob" (some (.natural 50))
  let fpValid : Footprint :=
    [⟨"acct/alice", some (.natural (100 + z))⟩, ⟨"acct/bob", some (.natural 50)⟩, ⟨"acct/carol", none⟩]
  let fpStale : Footprint := [⟨"acct/alice", some (.natural 99)⟩]
  let fpUnexpectedPresent : Footprint := [⟨"acct/alice", none⟩]
  let dupErr := checkNodupCells ["acct/alice", "acct/bob", "acct/alice"]
  let mergeKindsOk :=
    ["add", "max", "union"].all (fun name =>
      match Branch.MergeKind.ofString? name with
      | some k => k.name == name
      | none => false) &&
    (Branch.MergeKind.ofString? "counter").isNone
  let storePages : Store :=
    { pages :=
        [ { name := "notes/_kind", id := 1 + z, history := [], seen := some "kind-v1", authors := [], note := none }
        , { name := "notes/alpha", id := 2 + z, history := [], seen := some "alpha-v1", authors := [], note := none }
        , { name := "notes/beta",  id := 3 + z, history := [], seen := some "beta-v1",  authors := [], note := none } ] }
  let filesClean := [("notes/_kind", "kind-v1"), ("notes/alpha", "alpha-v1"), ("notes/beta", "beta-v1")]
  let filesDirty := [("notes/alpha", "alpha-v2"), ("notes/_kind", "kind-v2"), ("notes/beta", "beta-v1")]
  let pend := pendingAt storePages filesDirty
  let wf := writesFor storePages filesDirty
  let ow := overwrite filesClean [("notes/alpha", "alpha-v2")]
  [ ("Vault.admitFootprint admits matching + absent pins and rejects stale or present-as-none pins",
      (admitFootprint s0 fpValid).isOk &&
      !(admitFootprint s0 fpStale).isOk &&
      !(admitFootprint s0 fpUnexpectedPresent).isOk &&
      !dupErr.isOk)
  , ("Vault.Branch MergeKind roundtrips all 3 valid kinds (add, max, union) and rejects unknown",
      mergeKindsOk)
  , ("Vault.Store (@[csimp] quietIndexed & pendingAtIndexed) detects clean vs dirty files and orders _kind first",
      quiet storePages filesClean &&
      !quiet storePages filesDirty &&
      pend == [("notes/_kind", "kind-v2"), ("notes/alpha", "alpha-v2")])
  , ("Vault.Store (@[csimp] writesForIndexed & overwriteIndexed) computes store writes and restores clean files",
      wf == [("notes/_kind", "kind-v1"), ("notes/alpha", "alpha-v1")] &&
      overwrite filesDirty wf == [("notes/alpha", "alpha-v1"), ("notes/_kind", "kind-v1"), ("notes/beta", "beta-v1")] &&
      ow == [("notes/_kind", "kind-v1"), ("notes/alpha", "alpha-v2"), ("notes/beta", "beta-v1")])
  ]
end VaultSuite

/-! ## Suite 10: `Run` (`Core4.turn` `@[csimp]`, `Negotiation`, `HyperLaw`) -/

section RunSuite
open Obend.Run.HyperLaw Obend.Run.Negotiation

def runChecks (z : Nat) : List (String × Bool) :=
  let L : Obend.Core.Machine.Limits := ⟨1024, 128⟩
  let B : Obend.Core.Data.Budget := ⟨256, 64, 4096⟩
  let st := Obend.Core.Machine.initial (.binary .add (.nat (19 + z)) (.nat 23))
  let tRes := Obend.Run.Core4.turn L (32 + z) B st
  let niSafe := checkHyperLaw2NonInterference secLowView safeTracePair
  let niLeak := checkHyperLaw2NonInterference secLowView leakingTracePair
  [ ("Run.Core4.turn (@[csimp] turnFast) evaluates terminal addition to 42",
      match tRes with
      | .stop (.ended (.finished (.natural n) _)) => n == 42 + z
      | _ => false)
  , ("Run.Negotiation stepW enforces monotone clock and deadline irreversibility",
      stepW everything { everything with clock := 1 + z } &&
      !stepW { everything with beforeDeadline := false, clock := 1 + z }
             { everything with beforeDeadline := true, clock := 2 + z })
  , ("Run.HyperLaw non-interference accepts safeTracePair and rejects leakingTracePair",
      niSafe && !niLeak)
  ]
end RunSuite

/-! ## Suite 11: `Hardware` & `Trailblaze.LeanFpga` (CSR Hypergraph, ReductionMachine, Kinematics, FPGA) -/

section HardwareSuite
open Obend.Hardware.Kinematics Obend.Hardware.ReductionMachine Obend.Trailblaze.LeanFpga

def hardwareChecks (z : Nat) : List (String × Bool) :=
  let u : Vec3 := ⟨1 + Int.ofNat z, 0, 0⟩
  let v : Vec3 := ⟨0, 1, 0⟩
  let w := cross3 u v
  let slotA := mkConNode z 1 ⟨10, 0⟩ ⟨11, 0⟩
  let slotB := mkConNode (1 + z) 1 ⟨20, 0⟩ ⟨21, 0⟩
  let pe0 := initBramInteractionNetPe
    [ { slotId := z, kind := .con 1, aux0 := 10, aux1 := 11, active := true }
    , { slotId := 1 + z, kind := .con 1, aux0 := 20, aux1 := 21, active := true } ]
  let pe1 := stepActivePair pe0 { left := slotA, right := slotB }
  [ ("Kinematics 3D cross product (e_x × e_y == e_z) and orthogonality",
      w == ⟨0, 0, 1⟩ && dot3 u w == 0 && dot3 v w == 0)
  , ("ReductionMachine CON-CON annihilation allocates 0 BRAM nodes and shrinks active count by 2",
      pe1.allocCount == 0 && activeNodeCount pe1 + 2 == activeNodeCount pe0)
  , ("Trailblaze.LeanFpga silverLeanFpgaSmoke & HVM net emitter pass natively",
      silverLeanFpgaSmoke && !(emitHvmNetText sampleLinearDeltaNet).isEmpty)
  ]
end HardwareSuite

/-! ## Suite 12: `SymbolicZk` (`SemiringDatalog`, `RankedFixpointArith`, `CamUnifyArith`) -/

section SymbolicZkSuite
open Obend.SymbolicZk.Datalog Obend.SymbolicZk.Ranked Obend.SymbolicZk.Cam Obend.Lower.ExprCAM

def zkChecks (z : Nat) : List (String × Bool) :=
  let c1 : TropicalMinCost := ⟨some (5 + z)⟩
  let c2 : TropicalMinCost := ⟨some 9⟩
  let tAdd := tropicalAdd c1 c2
  let tMul := tropicalMul c1 c2
  let prog : ArithProgram :=
    { numAtoms := 2
    , rules := #[{ head := z, pos := #[], neg := #[1] }] }
  let rGammaOk := checkRankedGamma prog #[false, false] #[true, false] #[0, 0] #[0, 0]
  let wLeaf := packCamWord64 ⟨0#4, false, false, 0#26, 0#16, 0#16⟩
  let wApp := packCamWord64 ⟨4#4, false, false, 0#26, 0#16, 0#16⟩
  let wMVar := packCamWord64 ⟨10#4, false, false, 0#26, 0#16, 0#16⟩
  let dagPool : CamDagPool :=
    { words := #[wLeaf, wApp, wMVar]
    , sigma := #[none, none, some (1 + z)] }
  [ ("SemiringDatalog tropicalAdd=min(5,9)=5 and tropicalMul=5+9=14",
      tAdd == ⟨some (5 + z)⟩ && tMul == ⟨some (14 + z)⟩)
  , ("RankedFixpointArith checkRankedGamma validates stratified rule firing",
      WFProgram prog && rGammaOk)
  , ("CamUnifyArith checkTopologicalUnifyExec accepts acyclic DAG and rejects cyclic heights",
      checkTopologicalUnifyExec dagPool #[0, 1, 1] &&
      !checkTopologicalUnifyExec dagPool #[1, 1, 1])
  ]
end SymbolicZkSuite

end ObendTest

def main : IO UInt32 := do
  let suites : List (String × (Nat → List (String × Bool))) :=
    [ ("Core.MachineFast & Data (@[csimp])", ObendTest.coreMachineChecks)
    , ("Core.FiniteBisimulation", ObendTest.finiteBisimChecks)
    , ("Digest.Cshake256.Fast & Core.Digest (@[csimp])", ObendTest.digestChecks)
    , ("Leaf.BytecodeRegisterJit & SelfApplicableMix", ObendTest.leafJitMixChecks)
    , ("Crypto.FastRing & BinaryTower256 (@[csimp])", ObendTest.cryptoChecks)
    , ("Elab.Coerce & Elab.Prepare (34 probes)", ObendTest.elabChecks)
    , ("Spec.C4 & Spec.Law", ObendTest.specChecks)
    , ("Doc.Graph, Merge, Section & Backlinks (@[csimp])", ObendTest.docChecks)
    , ("Vault.Store, Hyperedge & Branch (@[csimp])", ObendTest.vaultChecks)
    , ("Run.Core4, Negotiation & HyperLaw (@[csimp])", ObendTest.runChecks)
    , ("Hardware & Trailblaze.LeanFpga", ObendTest.hardwareChecks)
    , ("SymbolicZk (Datalog, RankedWFS & CamUnify)", ObendTest.zkChecks)
    ]
  IO.println "=== obend-test: Native Compiled Runtime Suite ==="
  let tStart ← IO.monoNanosNow
  let mut totalPassed := 0
  let mut totalFailed := 0
  for (name, fn) in suites do
    let (p, f, _) ← ObendTest.runSuite name fn
    totalPassed := totalPassed + p
    totalFailed := totalFailed + f
  let tEnd ← IO.monoNanosNow
  let totalElapsed := ObendTest.formatMicros (tEnd - tStart)
  IO.println s!"=== Summary: {totalPassed} passed, {totalFailed} failed across {suites.length} suites in {totalElapsed} ==="
  return (if totalFailed == 0 then 0 else 1)
