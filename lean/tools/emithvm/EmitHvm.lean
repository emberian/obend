/-
# `obend-emit-hvm` — Leaf books lowered to HVM2 nets (`Obend.Hardware.Hvm`)

    obend-emit-hvm list
    obend-emit-hvm <book> [--plant P] [--out FILE]
        the book's nets and an `@main` for its first vector, in HVM2's syntax (the committed
        `hardware/hvm/<book>.hvm`); a refused book prints the refusal and exits 3
    obend-emit-hvm <book> --vectors DIR [--plant P]
        one `.hvm` per vector (`DIR/<member>_<args>.hvm`) and `DIR/expected.tsv`, one line per vector:
        file, member, arguments, the slots `evalBookAt` shows (each probe of `HSort.observe` run on
        Core4's demand machine, decoded to the number HVM2 prints, as the tuple HVM2 prints), and the
        Lean model's own run (`Obend.Hardware.Hvm.run`) printed the same way

`--plant swapSwitch` prints every switch with its two cases exchanged, `--plant addAsSub` prints
`[+]` as `[-]`: rules planted in the emitter's text only, for the verify script's tooth. The vectors
are those on which every result slot's exact evaluation answers (the hypothesis of
`lowerBookToHvm_sound`); the ones dropped are counted.
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

/-- First-order methods over naturals and Booleans (the first rung's book). -/
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

/-- `Nat.rec z s` as `Obend.Lower.lowerT` lowers it (`natRecSpec`). -/
def natRecT (z s m : Term) : Term := .app (.fix (Obend.Lower.natRecSpec z s) (.record [])) m

/- Recursion: a factorial, `Nat.rec` as Lean's lowering emits it, a loop that reads another slot
through `self` (resolved by `evalBook`'s pins), and Fibonacci over a record state. -/

/-- `fix (λrec. λsup. λx. body) {}` applied to `arg`. -/
def fixApp (body arg : Term) : Term := .app (.fix (.lam (.lam (.lam body))) (.record [])) arg

def recVtable : List (String × Term) :=
  [ ("fact", .lam (fixApp (.ifZero (.bound 0) (.nat 1)
      (.binary .multiply (.binary .add (.bound 0) (.nat 1)) (.app (.bound 3) (.bound 0)))) (.bound 0)))
  , ("sumTo", .lam (natRecT (.nat 0)
      (.lam (.lam (.binary .add (.binary .add (.bound 0) (.bound 1)) (.nat 1)))) (.bound 0)))
  , ("step", .lam (.binary .add (.binary .multiply (.bound 0) (.nat 2)) (.nat 1)))
  , ("loop", .lam (fixApp (.ifZero (.bound 0) (.nat 0)
      (.app (.get (.bound 5) "step") (.app (.bound 3) (.bound 0)))) (.bound 0)))
  , ("fib", .lam (fixApp (.ifZero (.get (.bound 0) "n") (.get (.bound 0) "a")
      (.app (.bound 3) (.record [("n", .bound 0), ("a", .get (.bound 1) "b"),
        ("b", .binary .add (.get (.bound 1) "a") (.get (.bound 1) "b"))])))
      (.record [("n", .bound 0), ("a", .nat 0), ("b", .nat 1)]))) ]

/-- Records, sums, `case`, and closures returned by methods. -/
def dataVtable : List (String × Term) :=
  [ ("pair", .lam (.record [("a", .binary .add (.bound 0) (.nat 1)), ("b", .binary .less (.bound 0) (.nat 5))]))
  , ("qr", .lam (.record [("q", .binary .divide (.bound 0) (.nat 7)), ("r", .binary .modulo (.bound 0) (.nat 7))]))
  , ("pick", .lam (.binary .add
      (.get (.ifBool (.binary .less (.bound 0) (.nat 5)) (.record [("a", .nat 1), ("b", .nat 2)])
        (.record [("a", .bound 0), ("b", .binary .add (.bound 0) (.nat 1))])) "a")
      (.get (.record [("a", .nat 10), ("b", .bound 0)]) "b")))
  , ("opt", .lam (.ifZero (.bound 0) (.inject "none" (.record [])) (.inject "some" (.binary .multiply (.bound 0) (.nat 3)))))
  , ("useOpt", .lam (.case (.ifZero (.bound 0) (.inject "none" (.record [])) (.inject "some" (.binary .multiply (.bound 0) (.nat 3))))
      [("some", .binary .add (.bound 0) (.nat 1)), ("none", .nat 0)]))
  , ("area", .lam (.case (.ifBool (.binary .less (.bound 0) (.nat 10)) (.inject "circle" (.bound 0))
        (.inject "rect" (.record [("w", .bound 0), ("h", .binary .add (.bound 0) (.nat 1))])))
      [("circle", .binary .multiply (.nat 3) (.binary .multiply (.bound 0) (.bound 0))),
       ("rect", .binary .multiply (.get (.bound 0) "w") (.get (.bound 0) "h"))]))
  , ("shape", .lam (.ifBool (.binary .less (.bound 0) (.nat 10)) (.inject "circle" (.bound 0))
        (.inject "rect" (.record [("w", .bound 0), ("h", .binary .add (.bound 0) (.nat 1))]))))
  , ("add", .lam (.lam (.binary .add (.bound 1) (.bound 0))))
  , ("affine", .lam (.lam (.lam (.binary .add (.binary .multiply (.bound 2) (.bound 1)) (.bound 0))))) ]

/-- A book the lowering refuses: a label. -/
def refusedVtable : List (String × Term) :=
  [ ("double", .lam (.binary .add (.bound 0) (.bound 0)))
  , ("named", .lam (.label "x")) ]

def books : List (String × List (String × Term)) :=
  [("arith", arithVtable), ("rec", recVtable), ("data", dataVtable), ("refused", refusedVtable)]

def args1 : List Nat := [0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 20, 64, 100, 1000, 4095]
def args2 : List (List Nat) := [[0, 0], [1, 2], [3, 4], [10, 20], [100, 7], [4095, 4095]]
def args3 : List (List Nat) := [[0, 0, 0], [1, 2, 3], [5, 6, 7], [100, 3, 9]]

def argsFor : Nat → List (List Nat)
  | 1 => args1.map fun x => [x]
  | 2 => args2
  | 3 => args3
  | _ => []

def fuel : Nat := 100000

/-! ## Expected values -/

def machineValue (t : Term) : Option Nat :=
  match Obend.Core.Machine.runBounded ⟨1000000, 1000000⟩ 10000000 (Obend.Core.Machine.initial t) with
  | .finished (.natural n) _ => some n
  | .finished (.boolean b) _ => some (if b then 1 else 0)
  | _ => none

def machineLabel (t : Term) : Option String :=
  match Obend.Core.Machine.runBounded ⟨1000000, 1000000⟩ 10000000 (Obend.Core.Machine.initial t) with
  | .finished (.label l) _ => some l
  | _ => none

/-- The slots `evalBookAt`'s term shows, each probe run on the demand machine. -/
def expectedSlots (σ : HSort) (pre : List PStep) (r : Term) : Option (List Nat) :=
  match σ with
  | .val (.sc _) => (machineValue (applyPath pre r)).map fun v => [v]
  | .val (.rcd fs) => fs.mapM fun f => machineValue (applyPath (pre ++ [.get f.1]) r)
  | .sum arms => do
    let l ← machineLabel (applyPath (pre ++ [.tag (arms.map (·.1))]) r)
    let (j, v) ← armIdx arms l
    let pay ← match v with
      | .sc _ => (machineValue (applyPath (pre ++ [.pay l]) r)).map fun w => [w]
      | .rcd fs => fs.mapM fun f => machineValue (applyPath (pre ++ [.payGet l f.1]) r)
    pure (j :: pay ++ List.replicate (maxW arms - pay.length) 0)

def tupText : List Nat → String
  | [] => "*"
  | [v] => toString v
  | v :: vs => s!"({v} {tupText vs})"

def modelText (H : HvmBook) (d : HvmMember) (xs : List Nat) : String :=
  match run H.defs 1000000 (mainCfgOf d.member (xs.map some)) with
  | ⟨root, []⟩ => treeText .none root
  | _ => "stuck"

structure HvmVector where
  member : HvmMember
  xs : List Nat

def vectorsOf (H : HvmBook) : List HvmVector × Nat :=
  let all := H.members.flatMap fun d => (argsFor d.arity).map fun xs => (⟨d, xs⟩ : HvmVector)
  let ok := all.filter fun v => v.member.slots.all fun e =>
    (evalE H.fdefs fuel (bindEnv (revRange v.member.arity) (v.xs.map some)) e).isSome
  (ok, all.length - ok.length)

def vectorFile (v : HvmVector) : String :=
  s!"{v.member.member}_{String.intercalate "_" (v.xs.map toString)}.hvm"

def expectedLine (B : Book) (H : HvmBook) (v : HvmVector) : String :=
  let exp := match v.xs with
    | x :: rest => match evalBookAt B v.member.member (.nat x) with
      | some r => match expectedSlots v.member.sort (rest.map .arg) r with
        | some ws => tupText ws
        | none => "unfinished"
      | none => "none"
    | [] => "none"
  s!"{vectorFile v}\t{v.member.member}\t{String.intercalate "," (v.xs.map toString)}\t{exp}\t{modelText H v.member v.xs}"

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
          IO.FS.writeFile s!"{dir}/{vectorFile v}" (emitMain H v.member v.xs plant)
          lines := lines.push (expectedLine B H v)
        IO.FS.writeFile s!"{dir}/expected.tsv" (String.intercalate "\n" lines.toList ++ "\n")
        IO.println s!"{name}: {vs.length} vectors written to {dir} ({dropped} dropped: a slot's exact value does not answer)"
        return 0
      | none =>
        let some v := vs.head? | do IO.eprintln "no vector"; return 2
        let header := s!"// Generated by obend-emit-hvm {name} from Obend.Hardware.Hvm.lowerBookToHvm (lean/tools/emithvm).\n" ++
          s!"// Do not edit: the verify script compares bytes. @main runs {v.member.member} at {v.xs}.\n\n"
        let text := header ++ emitMain H v.member v.xs plant
        match out with
        | some f => IO.FS.writeFile f text
        | none => IO.print text
        return 0
  | _ =>
    IO.eprintln usage
    return 2
