/-
# obend-rdna2 — the RDNA2 decoder and model on RADV's dumps (rung G2)

    obend-rdna2 decode ISA.txt         every instruction of hardware/gpu/isa/<graph>.txt, decoded from its
                                       machine code and written in LLVM's syntax, one per line, in order
                                       (`hardware/gpu/isa_check.sh` diffs this against `llvm-mc --disassemble`)
    obend-rdna2 flip ISA.txt           for every instruction, every bit of its machine code flipped once: the
                                       decoding must change or fail unless the bit lies in no field of the
                                       encoding (a bit the specification does not name); exits 1 otherwise
    obend-rdna2 waitcnt ISA.txt [--nop STAGE:INSTR]
                                       every stage's waits are sufficient (Obend.Hardware.Gpu.Rdna2.Waitcnt);
                                       with --nop, that instruction (an s_waitcnt) is replaced by s_nop 0
                                       first and the check must refuse (isa_check.sh stage 6)
    obend-rdna2 gem5 VECTORS.tsv       every row of hardware/gpu/rdna2/gem5_vectors.tsv replayed through the
                                       model's step and compared register by register (isa_check.sh stage 5)
    obend-rdna2 run GRAPH_DIR [--isa ISA.txt] [--flip STAGE:INSTR:BIT]
                                       the model: every stage's program from ISA.txt (default GRAPH_DIR/../../isa/<graph>.txt)
                                       run on every vector of expected.tsv (Obend.Hardware.Gpu.Rdna2.Check);
                                       with --flip, one bit of one instruction is flipped first and the
                                       comparison must fail (the gate's tooth)
-/
import Obend.Hardware.Gpu.Rdna2.Decode
import Obend.Hardware.Gpu.Rdna2.Check
import Obend.Hardware.Gpu.Rdna2.Waitcnt
import Obend.Hardware.Gpu.Rdna2.Cert
import Obend.Hardware.SquareGraphs
import Obend.Hardware.Gpu.Rdna2.Lift
import Obend.Hardware.Gpu.Rdna2.Certified
import Obend.Hardware.Gpu.Ntt

open Obend.Hardware.Gpu.Rdna2

def usage : String :=
  "obend-rdna2 decode ISA.txt | flip ISA.txt | waitcnt ISA.txt [--nop STAGE:INSTR] | gem5 VECTORS.tsv | run GRAPH_DIR [--isa ISA.txt] [--flip STAGE:INSTR:BIT]"

/-- `(text, words)` for every instruction line (`\t<text>\t; <hex>...`) of a dump, in order. -/
def instructionLines (s : String) : List (String × List UInt32) :=
  s.splitOn "\n" |>.filterMap fun ln =>
    if ln.startsWith "\t" then
      match ln.splitOn "\t; " with
      | [text, hexes] =>
        some ((text.drop 1).toString, (hexes.splitOn " ").filterMap fun h =>
          if h.isEmpty then none else some (UInt32.ofNat (hexToNat h)))
      | _ => none
    else none
where
  hexToNat (h : String) : Nat := h.foldl (fun acc c => acc * 16 + (c.toNat - (if c.isDigit then '0'.toNat else 'a'.toNat - 10))) 0

def renderWords (ws : List UInt32) : String :=
  match decodeInst ws with
  | none => "<undecoded>"
  | some (i, k) =>
    if k != ws.length then s!"<width {k} of {ws.length} dwords: {i.name}>"
    else (i.render).getD s!"<unrendered {i.name} in {i.enc.name}>"

def cmdDecode (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  for (_, ws) in instructionLines s do
    IO.println (renderWords ws)
  return 0

/-- Is bit `b` (of the whole instruction, first dword lowest) inside some field of `e`? -/
def inSomeField (e : Encoding) (b : Nat) : Bool :=
  e.fields.any fun f => f.ranges.any fun r => r.offset ≤ b && b < r.offset + r.count

def cmdFlip (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  let mut changed := 0
  let mut failed := 0
  let mut unnamed := 0
  let mut bad : List String := []
  for (text, ws) in instructionLines s do
    let some (orig, _) := decodeInst ws | bad := bad ++ [s!"undecoded: {text}"]; continue
    let origR := orig.render
    for w in [0:ws.length] do
      for b in [0:32] do
        let ws' := ws.set w (ws[w]! ^^^ (1 <<< b.toUInt32))
        let bit := 32 * w + b
        match decodeInst ws' with
        | none => failed := failed + 1
        | some (i', k') =>
          if k' != ws.length || i'.fields != orig.fields || i'.inst.name != orig.inst.name || i'.enc.name != orig.enc.name || i'.render != origR then
            changed := changed + 1
          else if !inSomeField orig.enc bit then
            unnamed := unnamed + 1
          else
            bad := bad ++ [s!"bit {bit} of `{text}` ({orig.enc.name}) flipped and nothing changed"]
  IO.println s!"flip: {changed} bit flips changed the decoding, {failed} made it fail, {unnamed} lay in no field of their encoding"
  for b in bad.take 20 do IO.eprintln s!"[FAIL] {b}"
  return if bad.isEmpty then 0 else 1

def cmdRun (dir : String) (isaArg : Option String) (flip : Option String) : IO UInt32 := do
  let graph := (System.FilePath.mk dir).fileName.getD dir
  let isaPath := match isaArg with
    | some p => System.FilePath.mk p
    | none => (System.FilePath.mk dir) / ".." / ".." / "isa" / (graph ++ ".txt")
  let isa ← IO.FS.readFile isaPath
  let plan ← IO.FS.readFile ((System.FilePath.mk dir) / "plan.json")
  let expected ← IO.FS.readFile ((System.FilePath.mk dir) / "expected.tsv")
  let flipSpec : Option (Nat × Nat × Nat) := flip.bind fun f =>
    match f.splitOn ":" |>.map String.toNat? with
    | [some a, some b, some c] => some (a, b, c)
    | _ => none
  match checkGraphReport isa plan expected flipSpec with
  | .ok report =>
    IO.println s!"{graph}: {report}"
    return if flipSpec.isSome then 1 else 0
  | .error e =>
    if flipSpec.isSome then
      IO.println s!"{graph}: planted flip {flip.getD ""} caught: {e}"
      return 0
    IO.eprintln s!"[FAIL] {graph}: {e}"
    return 1

def cmdGem5 (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  match checkGem5Report s with
  | .ok r => IO.println r; return 0
  | .error e => IO.eprintln s!"[FAIL] {e}"; return 1

def cmdWaitcnt (path : String) (nop : Option String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  let spec : Option (Nat × Nat) := nop.bind fun f =>
    match f.splitOn ":" |>.map String.toNat? with
    | [some a, some b] => some (a, b)
    | _ => none
  let graph := (System.FilePath.mk path).fileStem.getD path
  match checkWaitcntDumpReport s spec with
  | .ok r =>
    IO.println s!"{graph}: {r}"
    return if spec.isSome then 1 else 0
  | .error e =>
    if spec.isSome then
      IO.println s!"{graph}: wait replaced by s_nop at {nop.getD ""} refused: {e}"
      return 0
    IO.eprintln s!"[FAIL] {graph}: {e}"
    return 1

/-- Where the certificate check refuses, said in words (a diagnostic run of the same steps). -/
def explainCert {σ : Type} (words : Nat) (lay : Memory) (specs : List (Spec σ)) (progs : List Program) : String := Id.run do
  let mut known : Known := {}
  for (spec, k) in specs.zipIdx do
    let some prog := progs[k]? | return s!"stage {k}: no program"
    let some T := spec.table (readWord words lay known)
      | return s!"stage {k}: the specification's table is refused (a value the lowering does not know)"
    let mut acc : Acc := ⟨{}, [], {}⟩
    for g in List.range (groupsOf spec.threads) do
      let st := symWave words lay prog spec.lds known acc.stored g
      if let some e := st.err then return s!"stage {k}, workgroup {g}: the symbolic run refused: {e}"
      unless st.halted do return s!"stage {k}, workgroup {g}: the symbolic run did not halt"
      for (a, t) in st.mem.stores.toList do
        if inLds a then continue
        if acc.stored.contains a then return s!"stage {k}: dword 0x{String.ofList (Nat.toDigits 16 a.toNat)} stored twice"
        match storeOk words T a t with
        | none =>
          let off := (a - wDw).toNat
          return s!"stage {k}, workgroup {g}: the store to word {off / 2} (dword {off % 2}) is refused: " ++
            (if !inW words a then "outside the wire buffer" else
             match T[off / 2]? with
             | none => "the stage does not write that word"
             | some _ => "the residual exceeds the abstraction budget")
        | some r? =>
          acc := { stored := acc.stored.insert a, updates := (a, t.litVal?) :: acc.updates,
                   needed := match r? with | some r => acc.needed.insert r | none => acc.needed }
    for (i, _) in T.toList do
      unless acc.stored.contains (dwLo i) && acc.stored.contains (dwLo i + 1) do
        return s!"stage {k}: word {i} of the table never stored"
    known := applyUpdates known acc.updates
  return "accepted"

/-! ### Residuals that are 64-bit ring identities (`Rdna2.Lift`) -/

def isVar (t : Tm) : Option UInt64 := match t.op with | .var a => some a | _ => none

/-- The 64-bit expressions whose limb lowering could have the high dword `hi` and low dword `lo`
(candidates; the generator keeps one only if its lowering is the residual's side, term for term). -/
partial def pairParse (lo hi : Tm) (fuel : Nat) : List W :=
  if fuel = 0 then [] else
  match isVar lo, isVar hi with
  | some a, some b => [.leaf a b]
  | _, _ => hiParse hi (fuel - 1)
where
  hiParse (hi : Tm) (fuel : Nat) : List W :=
    match hi.op, hi.args with
    | .addc, [x, y, c] =>
      match c.op, c.args with
      | .carry, [p, q] =>
        [(p, x, q, y), (p, y, q, x)].flatMap fun (pl, ph, ql, qh) =>
          (pairParse pl ph fuel).flatMap fun a => (pairParse ql qh fuel).map fun b => W.add a b
      | _, _ => []
    | .subc, [x, y, c] =>
      match c.op, c.args with
      | .borrow, [p, q] =>
        (pairParse p x fuel).flatMap fun a => (pairParse q y fuel).map fun b => W.sub a b
      | _, _ => []
    | .sum, args =>
      match args.find? (·.op == .mulHi) with
      | some m =>
        match m.args with
        | [u, v] =>
          let muls := args.filter (fun t => t.op == .mul)
          let other (t f : Tm) : Option Tm :=
            match t.args with
            | [x, y] => if x == f then some y else if y == f then some x else none
            | _ => none
          if args.length != 3 || muls.length != 2 then [] else
          [(u, v), (v, u)].flatMap fun (a0, b0) =>
            [(muls[0]!, muls[1]!), (muls[1]!, muls[0]!)].flatMap fun (t1, t2) =>
              match other t1 b0, other t2 a0 with
              | some a1, some b1 =>
                (pairParse a0 a1 fuel).flatMap fun a => (pairParse b0 b1 fuel).map fun b => W.mul a b
              | _, _ => []
        | _ => []
      | none => []
    | _, _ => []

partial def wLean : W → String
  | .leaf a b => s!"(.leaf {a} {b})"
  | .add a b => s!"(.add {wLean a} {wLean b})"
  | .sub a b => s!"(.sub {wLean a} {wLean b})"
  | .mul a b => s!"(.mul {wLean a} {wLean b})"

/-- The two sides as the high dwords of 64-bit expressions, if they are. -/
def liftHi (r : Tm.Residual) : Option (W × W) :=
  let c1 := (pairParse.hiParse r.lhs 8).filter fun w => w.lower.2 == r.lhs
  let c2 := (pairParse.hiParse r.rhs 8).filter fun w => w.lower.2 == r.rhs
  match c1, c2 with
  | w1 :: _, w2 :: _ => some (w1, w2)
  | _, _ => none

/-- An operation in Lean syntax. -/
def opLean : TOp → String
  | .lit v => s!"(.lit {v})" | .var a => s!"(.var {a})" | .bit k => s!"(.bit {k})"
  | .sum => ".sum" | .sub => ".sub" | .mul => ".mul" | .mulHi => ".mulHi" | .band => ".band"
  | .bor => ".bor" | .shl => ".shl" | .lshr => ".lshr" | .ite => ".ite" | .carry => ".carry"
  | .borrow => ".borrow" | .addc => ".addc" | .carryc => ".carryc" | .subc => ".subc"
  | .borrowc => ".borrowc" | .ule => ".ule" | .ugt => ".ugt" | .ult64 => ".ult64" | .ne64 => ".ne64"
  | .pack => ".pack" | .shl64lo => ".shl64lo" | .shl64hi => ".shl64hi" | .lshr64lo => ".lshr64lo"
  | .lshr64hi => ".lshr64hi" | .nez64 => ".nez64"

/-- `let` lines naming every distinct subterm of `t` once, children first; the name of `t`. -/
partial def letLines (t : Tm) (st : Std.HashMap Tm String × Array String) : String × (Std.HashMap Tm String × Array String) :=
  match st.1.get? t with
  | some n => (n, st)
  | none =>
    let (names, st) := t.args.foldl (fun (acc : Array String × _) c =>
      let (n, st) := letLines c acc.2; (acc.1.push n, st)) (#[], st)
    let n := s!"n{st.2.size}"
    let line := s!"  let {n} := node {opLean t.op} [{", ".intercalate names.toList}]"
    (n, (st.1.insert t n, st.2.push line))

/-- The Lean module proving `rs` with `bv_decide`: a `Residual` per entry, built by `node` exactly as the
check builds it, and its `Holds` theorem. -/
def residualModule (modName : String) (tag : String) (graphsNote : String) (rs : List Tm.Residual) : String := Id.run do
  let mut out := s!"/-\n# {modName} — the residuals the certificates need, each proved\n\nGenerated by `obend-rdna2 reslib` over every dumped graph ({graphsNote}); do not edit:\n`hardware/gpu/isa_check.sh` regenerates it and compares bytes. Each residual is the pair of terms the\ncheck leaves for a stored dword after cutting (`Equiv`), over leaf variables, built here by `node` exactly\nas the check builds it, so that `certify`'s membership test finds it. Each is proved for every memory:\nby `bv_decide`, by `grind` where it multiplies, or, where it is a 64-bit ring identity written in limbs,\nby `W.holds_hi` and `grind` on the 64-bit words (`Lift`).\n-/\nmodule\npublic import Obend.Hardware.Gpu.Rdna2.Lift\nmeta import Std.Tactic.BVDecide\n@[expose] public section\n\nnamespace {modName}\nopen Obend.Hardware.Gpu.Rdna2 Obend.Hardware.Gpu.Rdna2.Tm\n\n"
  let mut names : Array String := #[]
  for (r, k) in rs.zipIdx do
    if let some (w1, w2) := liftHi r then
      let nm := s!"{tag}_{k}"
      names := names.push nm
      out := out ++ s!"/-- A 64-bit ring identity in limbs (`Lift`). -/\ndef {nm} : Tm.Residual := ⟨(W.lower {wLean w1}).2, (W.lower {wLean w2}).2⟩\n\ntheorem {nm}_holds : {nm}.Holds :=\n  W.holds_hi _ _ fun env => by simp only [W.eval]; grind\n\n"
      continue
    let (l, st) := letLines r.lhs ({}, #[])
    let (rr, st) := letLines r.rhs st
    let nm := s!"{tag}_{k}"
    -- products are ring identities, which SAT decides badly: `grind`'s ring solver first for those
    let tac := if st.2.any (fun l => (l.splitOn "node .mul").length > 1) then "first | grind | bv_decide (config := { timeout := 120 })" else "bv_decide (config := { timeout := 120 })"
    names := names.push nm
    out := out ++ s!"def {nm} : Tm.Residual :=\n{"\n".intercalate st.2.toList}\n  ⟨{l}, {rr}⟩\n\n"
    out := out ++ s!"set_option linter.unusedSimpArgs false in\ntheorem {nm}_holds : {nm}.Holds := by\n  intro env\n  simp only [{nm}, eval_node, TOp.sem, List.map, List.getD_cons_zero, List.getD_cons_succ, List.foldr, b2w, join64, carryBV, carrycBV, borrowBV, borrowcBV, mulHiBV, lshlrev64, lshrrev64, packWord, bne]\n  {tac}\n\n"
  out := out ++ s!"/-- Every residual above. -/\ndef all : List Tm.Residual := [{", ".intercalate names.toList}]\n\ntheorem all_hold : ∀ r ∈ all, r.Holds := by\n  simp only [all, List.mem_cons, List.not_mem_nil, or_false]\n  rintro r ({" | ".intercalate (names.toList.map fun _ => "rfl")}){String.join (names.toList.map fun n => s!"\n  · exact {n}_holds")}\n\nend {modName}\n"
  return out

/-! ### Block programs (the NTT) -/

def blockOf (graph : String) : Option Obend.Hardware.ArrayKernel.Program :=
  (Obend.Hardware.SquareGraphs.blockGraphs.find? (·.1 == graph)).map fun x => Obend.Hardware.Gpu.Ntt.nttBlockProgram x.2

def blockNeeded (p : Obend.Hardware.ArrayKernel.Program) (isa : String) (progs : List Program) : Option (List Tm.Residual) :=
  (checkProgram (Block.blockWords p) (layoutMem (Block.blockWords p) (Obend.Hardware.Gpu.BlockEmit.constWords p) [])
    (Block.blockSpecs p (ldssOf isa)) progs {} {}).map (·.toList)

/-- A term's head, `depth` levels deep (a residual is a DAG; its tree can be exponentially larger). -/
def brief : Nat → Tm → String
  | 0, _ => "…"
  | d + 1, .mk _ o as => s!"({Tm.opLean o}{String.join (as.take 4 |>.map fun a => " " ++ brief d a)}{if as.length > 4 then " …" else ""})"

def missingWhy (rs : List Tm.Residual) : String :=
  let missing := rs.filter (!Residuals.all.contains ·)
  if missing.isEmpty then "the program bounds (words, array ranges)"
  else s!"needs {missing.length} residual(s) the library does not prove, e.g. {brief 4 missing.head!.lhs} = {brief 4 missing.head!.rhs}"

/-- One residual library over several graphs: `GRAPH=ISA` pairs, residuals deduplicated. -/
def cmdResLib (modName tag : String) (pairs : List String) : IO UInt32 := do
  let mut all : Array Tm.Residual := #[]
  let mut seen : Std.HashSet Tm.Residual := {}
  for pr in pairs do
    let [graph, isaPath] := pr.splitOn "=" | IO.eprintln s!"[FAIL] {pr}: want GRAPH=ISA"; return 1
    let isa ← IO.FS.readFile isaPath
    let progs := (parseDump isa).toList.filterMap fun ws => (decodeProgram (ws.flatMap id)).toOption
    let needed ← match blockOf graph with
      | some bp => pure (blockNeeded bp isa progs)
      | none =>
        let some c := Obend.Hardware.SquareGraphs.graphs.find? (·.name == graph)
          | IO.eprintln s!"[FAIL] no graph {graph}"; return 1
        let .ok tg := c.build ()
          | IO.eprintln s!"[FAIL] {graph}: its source does not type"; return 1
        let p := Obend.Hardware.Gpu.lowerArrayToGpu tg.graph
        let .ok sched := Obend.Hardware.Gpu.ArrayEmit.compile p
          | IO.eprintln s!"[FAIL] {graph}: the schedule does not compile"; return 1
        pure (Schedule.neededSchedule p sched (ldssOf isa) progs)
    match needed with
    | some rs =>
      let fresh := rs.filter (!seen.contains ·)
      IO.eprintln s!"{graph}: {rs.length} residuals, {fresh.length} new"
      for r in fresh do seen := seen.insert r; all := all.push r
    | none => IO.eprintln s!"[FAIL] {graph}: not certified"; return 1
  let names := pairs.filterMap fun pr => (pr.splitOn "=").head?
  IO.print (residualModule modName tag (", ".intercalate names) all.toList)
  return 0

/-- Why the certificate refuses decoded programs (diagnostic; the check itself is `certifySchedule`). -/
def whyRefused (p : Obend.Hardware.Gpu.GpuProgram) (sched : Obend.Hardware.Gpu.ArrayEmit.Schedule) (isa : String)
    (progs : List Program) : String :=
  let acts := sched.actions.toList
  match Schedule.neededSchedule p sched (ldssOf isa) progs with
  | none => explainCert sched.words (layoutMem sched.words p.consts (Obend.Hardware.Gpu.ArrayEmit.scheduleTables p acts))
      (Schedule.scheduleSpecs p sched.words acts (ldssOf isa)) progs
  | some rs => missingWhy rs

/-- The gate's certificate stage: `certifyNamed`, the function every pin runs, on one dump; with `--flip`,
one bit of one instruction flipped first, which the certificate must refuse. -/
def blockWhy (p : Obend.Hardware.ArrayKernel.Program) (isa : String) (progs : List Program) : String :=
  match blockNeeded p isa progs with
  | none => explainCert (Block.blockWords p) (layoutMem (Block.blockWords p) (Obend.Hardware.Gpu.BlockEmit.constWords p) [])
      (Block.blockSpecs p (ldssOf isa)) progs
  | some rs => missingWhy rs

def cmdCertBlock (graph : String) (p : Obend.Hardware.ArrayKernel.Program) (isa : String) (flip : Option String) : IO UInt32 := do
  match flip with
  | none =>
    let t0 ← IO.monoMsNow
    let ok := certifyBlockNamed graph isa
    let t1 ← IO.monoMsNow
    if ok then
      IO.println s!"{graph}: certified, {p.dispatches.length} dispatches, check {t1 - t0} ms"
      return 0
    let why := match p.check with
      | .error e => s!"the block source is not admitted: {e}"
      | .ok () => if !checkWaitcntDump isa then "a load is not waited for (obend-rdna2 waitcnt)"
        else match progsOf isa with
          | none => "a stage does not decode"
          | some progs => blockWhy p isa progs
    IO.eprintln s!"[FAIL] {graph}: refused: {why}"
    return 1
  | some f =>
    let spec := match f.splitOn ":" with
      | [a, b, c] => (a.toNat?.bind fun a => b.toNat?.bind fun b => c.toNat?.map fun c => (a, b, c))
      | _ => none
    let some (st, ins, bit) := spec | IO.eprintln s!"[FAIL] --flip {f}: want STAGE:INSTR:BIT"; return 1
    match flipBit (parseDump isa) st ins bit with
    | .error e => IO.eprintln s!"[FAIL] {graph}: {e}"; return 1
    | .ok dumps =>
      match dumps.toList.mapM (fun ws => (decodeProgram (ws.flatMap id)).toOption) with
      | none => IO.println s!"{graph}: planted flip {f} refused: a stage no longer decodes"; return 0
      | some progs =>
        if Block.certifyBlock p (ldssOf isa) progs Residuals.all then
          IO.eprintln s!"[FAIL] {graph}: planted flip {f} certified"; return 1
        IO.println s!"{graph}: planted flip {f} refused: {blockWhy p isa progs}"
        return 0

def cmdCert (graph : String) (isaPath : String) (flip : Option String) : IO UInt32 := do
  if let some bp := blockOf graph then
    return ← cmdCertBlock graph bp (← IO.FS.readFile isaPath) flip
  let some c := Obend.Hardware.SquareGraphs.graphs.find? (·.name == graph)
    | IO.eprintln s!"[FAIL] no graph {graph}"; return 1
  let .ok tg := c.build ()
    | IO.eprintln s!"[FAIL] {graph}: its source does not type"; return 1
  let g := tg.graph
  let p := Obend.Hardware.Gpu.lowerArrayToGpu g
  let isa ← IO.FS.readFile isaPath
  let .ok sched := Obend.Hardware.Gpu.ArrayEmit.compile p
    | IO.eprintln s!"[FAIL] {graph}: the schedule does not compile"; return 1
  match flip with
  | none =>
    let t0 ← IO.monoMsNow
    let ok := certifyNamed graph isa
    let t1 ← IO.monoMsNow
    if ok then
      IO.println s!"{graph}: certified, {sched.actions.size} actions, {(ldssOf isa).length} dispatches, check {t1 - t0} ms"
      return 0
    let why := if !g.wf then "the graph is not well formed"
      else if !checkWaitcntDump isa then "a load is not waited for (obend-rdna2 waitcnt)"
      else match progsOf isa with
        | none => "a stage does not decode"
        | some progs => whyRefused p sched isa progs
    IO.eprintln s!"[FAIL] {graph}: refused: {why}"
    return 1
  | some f =>
    let spec := match f.splitOn ":" with
      | [a, b, c] => (a.toNat?.bind fun a => b.toNat?.bind fun b => c.toNat?.map fun c => (a, b, c))
      | _ => none
    let some (st, ins, bit) := spec | IO.eprintln s!"[FAIL] --flip {f}: want STAGE:INSTR:BIT"; return 1
    match flipBit (parseDump isa) st ins bit with
    | .error e => IO.eprintln s!"[FAIL] {graph}: {e}"; return 1
    | .ok dumps =>
      match dumps.toList.mapM (fun ws => (decodeProgram (ws.flatMap id)).toOption) with
      | none => IO.println s!"{graph}: planted flip {f} refused: a stage no longer decodes"; return 0
      | some progs =>
        if Schedule.certifySchedule p sched (ldssOf isa) progs Residuals.all then
          IO.eprintln s!"[FAIL] {graph}: planted flip {f} certified"; return 1
        IO.println s!"{graph}: planted flip {f} refused: {whyRefused p sched isa progs}"
        return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cert", g, isa] => cmdCert g isa none
  | ["cert", g, isa, "--flip", f] => cmdCert g isa (some f)
  | "reslib" :: m :: tag :: pairs => cmdResLib m tag pairs
  | ["waitcnt", p] => cmdWaitcnt p none
  | ["waitcnt", p, "--nop", f] => cmdWaitcnt p (some f)
  | ["gem5", p] => cmdGem5 p
  | ["decode", p] => cmdDecode p
  | ["flip", p] => cmdFlip p
  | ["run", d] => cmdRun d none none
  | ["run", d, "--flip", f] => cmdRun d none (some f)
  | ["run", d, "--isa", p] => cmdRun d (some p) none
  | ["run", d, "--isa", p, "--flip", f] => cmdRun d (some p) (some f)
  | _ => IO.eprintln usage; return 2
