/-
# `obend-emit-hvm` — Leaf books lowered to HVM2 nets (`Obend.Hardware.Hvm`)

    obend-emit-hvm list
    obend-emit-hvm <book> [--plant P] [--out FILE]
        the book's nets and an `@main` for its first vector, in HVM2's syntax (the committed
        `hardware/hvm/<book>.hvm`); a refused book prints the refusal and exits 3
    obend-emit-hvm <book> --vectors DIR [--plant P]
        one `.hvm` per vector (`DIR/<member>_<x>.hvm`) and `DIR/expected.tsv`, one line per vector:
        file, member, x, sort, `evalBookAt` when it is a literal (`-` otherwise), `evalBookAt` run on
        Core4's demand machine, and the Lean model's own run (`Obend.Hardware.Hvm.run`), each decoded
        to the number HVM2 prints (a Boolean as `0`/`1`)

`--plant swapSwitch` prints every switch with its two cases exchanged and `--plant addAsSub` prints
`[+]` as `[-]`: rules planted in the emitter's text only, for the verify script's tooth. The vectors are
the pairs on which the lowered expression's exact evaluation stays below `2^24` (the hypothesis of
`lowerBookToHvm_sound`); the ones it drops are counted.
-/
import Obend.Hardware.Hvm
import Obend.Core.Machine

open Obend.Core.Term
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Hardware.Hvm

/-! ## The books

Vtables in the shape `Obend.Leaf.emitVtable` takes: each entry under the `self` binder, a method as
`λx. body` (so `self` is index 1 inside it), anything else a cell. -/

/-- First-order methods over naturals and Booleans: every construct of the fragment, a read of
another slot through `self` (`quad`, resolved by `evalBook`'s pins), and a cell (`answer`). -/
def arithVtable : List (String × Term) :=
  [ ("double", .lam (.binary .add (.bound 0) (.bound 0)))
  , ("poly", .lam (.binary .add (.binary .add (.binary .multiply (.bound 0) (.bound 0))
      (.binary .multiply (.nat 3) (.bound 0))) (.nat 7)))
  , ("small", .lam (.ifBool (.binary .less (.bound 0) (.nat 3)) (.nat 1) (.binary .subtract (.bound 0) (.nat 3))))
  , ("isEven", .lam (.binary .equal (.binary .modulo (.bound 0) (.nat 2)) (.nat 0)))
  , ("inRange", .lam (.binary .conjunction (.binary .lessEqual (.nat 3) (.bound 0))
      (.binary .less (.bound 0) (.nat 10))))
  , ("predTwice", .lam (.ifZero (.bound 0) (.nat 100) (.binary .multiply (.bound 0) (.nat 2))))
  , ("tri", .lam (.ifZero (.bound 0) (.nat 0)
      (.binary .add (.binary .multiply (.bound 0) (.bound 0)) (.bound 0))))
  , ("mixed", .lam (.ifZero (.bound 0) (.nat 7) (.binary .add (.bound 0) (.binary .multiply (.bound 1) (.nat 2)))))
  , ("letChain", .lam (.app (.lam (.app (.lam (.binary .subtract (.bound 0) (.bound 2)))
      (.binary .multiply (.bound 0) (.bound 0)))) (.binary .add (.bound 0) (.nat 1))))
  , ("divmod", .lam (.binary .add (.binary .divide (.bound 0) (.nat 3))
      (.binary .multiply (.binary .modulo (.bound 0) (.nat 3)) (.nat 10))))
  , ("clampSub", .lam (.binary .subtract (.nat 50) (.bound 0)))
  , ("quad", .lam (.app (.get (.bound 1) "double") (.app (.get (.bound 1) "double") (.bound 0))))
  , ("answer", .nat 42) ]

/-- A book the lowering refuses: recursion through `fix`. -/
def refusedVtable : List (String × Term) :=
  [ ("double", .lam (.binary .add (.bound 0) (.bound 0)))
  , ("loop", .lam (.app (.fix (.lam (.lam (.bound 0))) (.record [])) (.bound 0))) ]

def books : List (String × List (String × Term)) :=
  [("arith", arithVtable), ("refused", refusedVtable)]

def defaultArgs : List Nat := [0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 64, 100, 1000, 4095, 65535]

/-! ## Expected values -/

def encodeLit : Term → Option Nat
  | .nat n => some n
  | .boolean b => some (if b then 1 else 0)
  | _ => none

/-- `evalBookAt`'s term run on Core4's demand machine, decoded. -/
def machineValue (t : Term) : String :=
  match Obend.Core.Machine.runBounded ⟨1000000, 1000000⟩ 10000000 (Obend.Core.Machine.initial t) with
  | .finished (.natural n) _ => toString n
  | .finished (.boolean b) _ => if b then "1" else "0"
  | .finished _ _ => "nonground"
  | _ => "unfinished"

/-- The model's own run, decoded. -/
def modelValue (H : HvmBook) (d : HvmMember) (x : Nat) : String :=
  match run H.defs 1000000 (mainCfg d x) with
  | ⟨.num (.u24 v), []⟩ => toString v
  | _ => "stuck"

def sortText : HSort → String
  | .nat => "nat"
  | .bool => "bool"

structure HvmVector where
  member : HvmMember
  x : Nat

def vectorsOf (H : HvmBook) : List HvmVector × Nat :=
  let all := H.members.flatMap fun d => defaultArgs.map fun x => (⟨d, x⟩ : HvmVector)
  let ok := all.filter fun v => (evalE (cons (some v.x) (fun _ => none)) v.member.fexp).isSome
  (ok, all.length - ok.length)

def vectorFile (v : HvmVector) : String := s!"{v.member.member}_{v.x}.hvm"

def expectedLine (B : Book) (H : HvmBook) (v : HvmVector) : String :=
  let r := evalBookAt B v.member.member (.nat v.x)
  let lit := match r.bind encodeLit with | some n => toString n | none => "-"
  let mach := match r with | some t => machineValue t | none => "none"
  s!"{vectorFile v}\t{v.member.member}\t{v.x}\t{sortText v.member.sort}\t{lit}\t{mach}\t{modelValue H v.member v.x}"

/-! ## The command -/

def usage : String :=
  "usage: obend-emit-hvm list | <book> [--plant P] [--out FILE] | <book> --vectors DIR [--plant P]"

partial def parseFlags : List String → Except String (Option String × Option String × Plant)
  | [] => .ok (none, none, .none)
  | "--out" :: f :: rest => do let (_, v, p) ← parseFlags rest; pure (some f, v, p)
  | "--vectors" :: d :: rest => do let (o, _, p) ← parseFlags rest; pure (o, some d, p)
  | "--plant" :: p :: rest => do
    let (o, v, _) ← parseFlags rest
    match Plant.ofString? p with
    | some q => pure (o, v, q)
    | none => throw s!"unknown plant {p} (none, swapSwitch, addAsSub)"
  | a :: _ => throw s!"unknown argument {a}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for (n, _) in books do IO.println n
    return 0
  | name :: rest =>
    let some vt := books.lookup name | do IO.eprintln s!"unknown book {name}"; return 2
    let (out, vdir, plant) ← match parseFlags rest with
      | .ok r => pure r
      | .error e => do IO.eprintln e; IO.eprintln usage; return 2
    let B := emitVtable vt
    match lowerBookToHvmE B with
    | .error e =>
      IO.println s!"refused: {e}"
      return 3
    | .ok H =>
      let (vs, dropped) := vectorsOf H
      match vdir with
      | some dir =>
        IO.FS.createDirAll dir
        let mut lines : Array String := #[]
        for v in vs do
          IO.FS.writeFile s!"{dir}/{vectorFile v}" (emitMain H v.member v.x plant)
          lines := lines.push (expectedLine B H v)
        IO.FS.writeFile s!"{dir}/expected.tsv" (String.intercalate "\n" lines.toList ++ "\n")
        IO.println s!"{name}: {vs.length} vectors written to {dir} ({dropped} dropped: exact value not below 2^24)"
        return 0
      | none =>
        let some v := vs.head? | do IO.eprintln "no vector"; return 2
        let header := s!"// Generated by obend-emit-hvm {name} from Obend.Hardware.Hvm.lowerBookToHvm (lean/tools/emithvm).\n" ++
          s!"// Do not edit: the verify script compares bytes. @main runs {v.member.member} at {v.x}.\n\n"
        let text := header ++ emitMain H v.member v.x plant
        match out with
        | some f => IO.FS.writeFile f text
        | none => IO.print text
        return 0
  | _ =>
    IO.eprintln usage
    return 2
