/-
# `obend-litmus-check` — the litmus shapes of `hardware/gpu/litmus/` under `Obend.Hardware.Gpu.Memory`

    obend-litmus-check table [--plant P]
        one line per shape and outcome: test, outcome id, GPUHarbor class, verdict (allowed | forbidden),
        racy flag, the reads per thread, the final values of the atomic locations
    obend-litmus-check dartagnan --out DIR
        every shape and outcome as a Dartagnan Vulkan litmus test DIR/<test>__<id>.litmus with an `exists`
        assertion naming that outcome, and DIR/index.tsv (file, test, id, the model's verdict); the gate
        runs Dartagnan under cat/vulkan.cat and compares
    obend-litmus-check restrict
        for every shape and every consistent device witness, the witness restricted to each workgroup and
        each thread is a consistent witness of the restricted shape (the section functor restricts along
        `Obj.le`): a check of the open proof named in Memory.lean's header, on the suite's shapes
    obend-litmus-check list

`--plant dropCoherence` removes `asmo` from the cycle set and from `fr`; `--plant dropBarrierSync`
replaces `locord` by same-thread program order (barriers synchronize nothing); `--plant sequential` adds
program order between memory events to the cycle set (sequential consistency). Each is a tooth for
`hardware/gpu/verify_litmus.sh`.

The shapes are the kernels' per-thread programs projected to one instance's locations with every barrier
of the program kept in place: a kernel thread plays role 0 of its own instance and role 1 of another, so a
barrier between the roles is in both threads' program order (see the suite README). Classes are the
result kernels' `TestResults` fields, by the same conditions.
-/
import Obend.Hardware.Gpu.Memory
open Obend.Hardware.Gpu.Memory

/-! ## The shapes -/

def xs : Loc := ⟨.storage, 0⟩
def ys : Loc := ⟨.storage, 1⟩
def xw : Loc := ⟨.workgroup, 0⟩
def yw : Loc := ⟨.workgroup, 1⟩

def aw (l : Loc) (v : Nat) : Ev := .write l v true
def ar (l : Loc) : Ev := .read l true
def nw (l : Loc) (v : Nat) : Ev := .write l v false
def nr (l : Loc) : Ev := .read l false
def sbar (i : Nat) : Ev := .barrier i [.storage]
def wbar (i : Nat) : Ev := .barrier i [.workgroup]
def xchg (l : Loc) (v : Nat) : Ev := .rmw l (.exchange v)
def add (l : Loc) (v : Nat) : Ev := .rmw l (.add v)

/-- Two threads in different workgroups (device scope). -/
def dev (a b : List Ev) : Shape := { threads := [⟨0, 0, a⟩, ⟨1, 1, b⟩] }
/-- Two threads in one workgroup (workgroup scope). -/
def wg (a b : List Ev) : Shape := { threads := [⟨0, 0, a⟩, ⟨1, 0, b⟩] }
def single (a : List Ev) : Shape := { threads := [⟨0, 0, a⟩] }

/-- The value of thread `t`'s `i`-th read in an outcome. -/
def rd (o : Outcome) (t i : Nat) : Nat :=
  let h := o.histories.getD t []
  let reads := h.filterMap fun (_, v) => v
  reads.getD i 0

def fin (o : Outcome) (i : Nat) : Nat := o.finals.getD i 0

/-- The four-way classification of the two-output result kernels, by `(r0, r1)`. -/
def class2 (seq0 seq1 inter weak : Nat × Nat) (r : Nat × Nat) : String :=
  if r == seq0 then "seq0" else if r == seq1 then "seq1" else if r == inter then "interleaved"
  else if r == weak then "weak" else "other"

def class1 (seq weak : Nat) (r : Nat) : String :=
  if r == seq then "seq" else if r == weak then "weak" else "other"

structure Test where
  name : String
  shape : Shape
  classify : Outcome → String

def mpClass (o : Outcome) : String := class2 (0, 0) (1, 1) (0, 1) (1, 0) (rd o 1 0, rd o 1 1)
def sbClass (o : Outcome) : String := class2 (1, 0) (0, 1) (1, 1) (0, 0) (rd o 0 0, rd o 1 0)
/-- The rmw variants: thread 1's first read is the exchange's return value, which the kernel discards;
`r1` is its load. -/
def sbRmwClass (o : Outcome) : String := class2 (1, 0) (0, 1) (1, 1) (0, 0) (rd o 0 0, rd o 1 1)
def lbClass (o : Outcome) : String := class2 (1, 0) (0, 1) (0, 0) (1, 1) (rd o 0 0, rd o 1 0)
def corrClass (o : Outcome) : String := class2 (0, 0) (1, 1) (0, 1) (1, 0) (rd o 1 0, rd o 1 1)

def tests : List Test := [
  -- device scope: role 0 in workgroup 0, role 1 in workgroup 1; storage atomics
  { name := "mp", shape := dev [aw xs 1, aw ys 1] [ar ys, ar xs], classify := mpClass },
  { name := "mp-barrier",
    shape := dev [aw xs 1, sbar 0, aw ys 1, sbar 1] [sbar 0, ar ys, sbar 1, ar xs], classify := mpClass },
  { name := "sb", shape := dev [aw xs 1, ar ys] [aw ys 1, ar xs], classify := sbClass },
  { name := "sb-rmw-barrier",
    shape := dev [aw xs 1, sbar 0, add ys 0, sbar 1] [sbar 0, xchg ys 1, sbar 1, ar xs], classify := sbRmwClass },
  { name := "lb", shape := dev [ar ys, aw xs 1] [ar xs, aw ys 1], classify := lbClass },
  { name := "lb-barrier",
    shape := dev [ar ys, sbar 0, aw xs 1, sbar 1] [sbar 0, ar xs, sbar 1, aw ys 1], classify := lbClass },
  { name := "iriw",
    shape := { threads := [⟨0, 0, [aw xs 1]⟩, ⟨1, 1, [aw ys 1]⟩, ⟨2, 2, [ar xs, ar ys]⟩, ⟨3, 3, [ar ys, ar xs]⟩] },
    classify := fun o =>
      let (r0, r1, r2, r3) := (rd o 2 0, rd o 2 1, rd o 3 0, rd o 3 1)
      if r0 == r1 && r2 == r3 then "seq"
      else if r0 == 1 && r1 == 0 && r2 == 1 && r3 == 0 then "weak" else "interleaved" },
  { name := "2+2w", shape := dev [aw xs 2, aw ys 1, wbar 0] [aw ys 2, aw xs 1, wbar 0],
    classify := fun o => class2 (1, 2) (2, 1) (1, 1) (2, 2) (fin o 0, fin o 1) },
  { name := "corr", shape := dev [aw xs 1] [ar xs, ar xs], classify := corrClass },
  { name := "coww", shape := single [aw xs 1, aw xs 2, wbar 0], classify := fun o => class1 2 1 (fin o 0) },
  { name := "cowr", shape := dev [aw xs 1, ar xs, wbar 0] [aw xs 2, wbar 0],
    classify := fun o => class2 (1, 2) (1, 1) (2, 2) (2, 1) (rd o 0 0, fin o 0) },
  { name := "corw1", shape := single [ar xs, aw xs 1, wbar 0], classify := fun o => class1 0 1 (rd o 0 0) },
  { name := "corw2", shape := dev [ar xs, aw xs 1, wbar 0] [aw xs 2, wbar 0],
    classify := fun o => class2 (0, 2) (2, 1) (0, 1) (2, 2) (rd o 0 0, fin o 0) },
  { name := "atomicity", shape := dev [xchg xs 1, wbar 0] [aw xs 2, wbar 0],
    classify := fun o =>
      let r := (rd o 0 0, fin o 0)
      if r == (0, 2) then "seq0" else if r == (2, 1) then "seq1" else if r == (0, 1) then "weak" else "other" },
  -- workgroup scope: both roles in workgroup 0
  { name := "mp-workgroup", shape := wg [aw xw 1, aw yw 1] [ar yw, ar xw], classify := mpClass },
  { name := "mp-workgroup-barrier",
    shape := wg [aw xw 1, wbar 0, aw yw 1, wbar 1, wbar 2] [wbar 0, ar yw, wbar 1, ar xw, wbar 2], classify := mpClass },
  { name := "mp-storage-workgroup", shape := wg [aw xs 1, aw ys 1, wbar 0] [ar ys, ar xs, wbar 0], classify := mpClass },
  { name := "mp-storage-workgroup-barrier",
    shape := wg [aw xs 1, sbar 0, aw ys 1, sbar 1, wbar 2] [sbar 0, ar ys, sbar 1, ar xs, wbar 2], classify := mpClass },
  { name := "sb-workgroup", shape := wg [aw xw 1, ar yw, wbar 0] [aw yw 1, ar xw, wbar 0], classify := sbClass },
  { name := "sb-workgroup-rmw-barrier",
    shape := wg [aw xw 1, wbar 0, add yw 0, wbar 1, wbar 2] [wbar 0, xchg yw 1, wbar 1, ar xw, wbar 2], classify := sbRmwClass },
  { name := "lb-workgroup", shape := wg [ar yw, aw xw 1, wbar 0] [ar xw, aw yw 1, wbar 0], classify := lbClass },
  { name := "lb-workgroup-barrier",
    shape := wg [ar yw, wbar 0, aw xw 1, wbar 1, wbar 2] [wbar 0, ar xw, wbar 1, aw yw 1, wbar 2], classify := lbClass },
  { name := "corr-workgroup", shape := wg [aw xw 1] [ar xw, ar xw], classify := corrClass },
  { name := "coww-workgroup", shape := single [aw xw 1, aw xw 2, wbar 0, ar xw],
    classify := fun o => class1 2 1 (rd o 0 0) },
  { name := "barrier-store-load", shape := wg [nw xw 1, wbar 0, wbar 1] [wbar 0, nr xw, wbar 1],
    classify := fun o => class1 1 0 (rd o 1 0) },
  { name := "barrier-load-store", shape := wg [nr xw, wbar 0, wbar 1] [wbar 0, nw xw 1, wbar 1],
    classify := fun o => class1 0 1 (rd o 0 0) },
  { name := "barrier-store-store", shape := wg [nw xw 1, wbar 0, wbar 1] [wbar 0, nw xw 2, wbar 1, nr xw],
    classify := fun o => class1 2 1 (rd o 1 0) }
]

/-! ## Rendering -/

def locName (l : Loc) : String :=
  match l.idx with
  | 0 => "x"
  | 1 => "y"
  | n => s!"l{n}"

def showReads (P : Shape) (o : Outcome) : String :=
  ",".intercalate <| (P.threads.zipIdx).flatMap fun (_, t) =>
    let h := o.histories.getD t []
    let reads := h.filterMap fun (_, v) => v
    (reads.zipIdx).map fun (v, j) => s!"P{t}:r{j}={v}"

def showFinals (P : Shape) (o : Outcome) : String :=
  ",".intercalate <| (P.atomicLocs.zip o.finals).map fun (l, v) => s!"{locName l}={v}"

def plantOf : String → Option Axioms
  | "dropCoherence" => some { coherence := false }
  | "dropBarrierSync" => some { barrierSync := false }
  | "sequential" => some { sequential := true }
  | _ => none

def verdict (ax : Axioms) (P : Shape) (o : Outcome) : String :=
  if P.allowedWith ax o then "allowed" else "forbidden"

def table (ax : Axioms) : IO Unit := do
  IO.println "test\toutcome\tclass\tverdict\tracy\treads\tfinals"
  for t in tests do
    let P := t.shape
    let racy := if P.static.racy then "racy" else "race-free"
    for (o, k) in P.outcomes.zipIdx do
      IO.println s!"{t.name}\to{k}\t{t.classify o}\t{verdict ax P o}\t{racy}\t{showReads P o}\t{showFinals P o}"

/-! ## Dartagnan's Vulkan litmus syntax -/

def spaceSc : Space → String
  | .storage => "sc0"
  | .workgroup => "sc1"

/-- WGSL's scopes: storage atomics are QueueFamily, workgroup atomics are Workgroup. -/
def spaceScope : Space → String
  | .storage => "qf"
  | .workgroup => "wg"

def semSc (sems : List Space) : String := String.join <| sems.map fun s => "." ++ "sem" ++ spaceSc s

/-- One instruction; `r` is the next register number of the thread. -/
def instr (e : Ev) (r : Nat) : String × Nat :=
  match e with
  | .write l v true => (s!"st.atom.{spaceScope l.space}.{spaceSc l.space} {locName l}, {v}", r)
  | .write l v false => (s!"st.av.wg.{spaceSc l.space} {locName l}, {v}", r)
  | .read l true => (s!"ld.atom.{spaceScope l.space}.{spaceSc l.space} r{r}, {locName l}", r + 1)
  | .read l false => (s!"ld.vis.wg.{spaceSc l.space} r{r}, {locName l}", r + 1)
  | .rmw l (.exchange v) => (s!"rmw.atom.{spaceScope l.space}.{spaceSc l.space} r{r}, {locName l}, {v}", r + 1)
  | .rmw l (.add v) => (s!"rmw.atom.{spaceScope l.space}.{spaceSc l.space}.add r{r}, {locName l}, {v}", r + 1)
  | .barrier i sems => (s!"cbar.acq_rel.wg{semSc sems} {i}", r)

def threadLines (th : Thread) : List String :=
  let rec go (es : List Ev) (r : Nat) : List String :=
    match es with
    | [] => []
    | e :: es' => let (s, r') := instr e r; s :: go es' r'
  go th.prog 0

def padTo (n : Nat) (s : String) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

def litmus (name : String) (P : Shape) (o : Outcome) : String :=
  let locs := P.locs
  let readCounts := P.threads.map fun th => (th.prog.filter Ev.isRead).length
  let inits := (locs.map fun l => s!"{locName l}=0;") ++
    (P.threads.zipIdx).flatMap fun (_, t) => (List.range (readCounts.getD t 0)).map fun j => s!"P{t}:r{j}=0;"
  let heads := (P.threads.zipIdx).map fun (th, t) => s!"P{t}@sg {t}, wg {th.wg}, qf 0"
  let cols := P.threads.map threadLines
  let rows := cols.foldl (fun n c => max n c.length) 0
  let width := (heads ++ cols.flatten).foldl (fun n s => max n s.length) 0 + 1
  let line := fun (cells : List String) => " " ++ " | ".intercalate (cells.map (padTo width)) ++ " ;"
  let body := (List.range rows).map fun i => line (cols.map fun c => c.getD i "")
  let conds := ((P.threads.zipIdx).flatMap fun (_, t) =>
      let reads := (o.histories.getD t []).filterMap fun (_, v) => v
      (reads.zipIdx).map fun (v, j) => s!"P{t}:r{j} == {v}") ++
    (P.atomicLocs.zip o.finals).map fun (l, v) => s!"{locName l} == {v}"
  "VULKAN " ++ name ++ "\n" ++
  "\"obend-litmus-check: " ++ name ++ ", the shape of hardware/gpu/litmus/wgsl/" ++ name ++ ".wgsl\"\n" ++
  "{\n" ++ "\n".intercalate inits ++ "\n}\n" ++
  line heads ++ "\n" ++ "\n".intercalate body ++ "\n\n" ++
  "exists (" ++ " /\\ ".intercalate conds ++ ")\n"

def dartagnan (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let mut index := #["file\ttest\toutcome\tverdict"]
  for t in tests do
    let P := t.shape
    for (o, k) in P.outcomes.zipIdx do
      let file := s!"{t.name}__o{k}.litmus"
      IO.FS.writeFile (dir ++ "/" ++ file) (litmus t.name P o)
      index := index.push s!"{file}\t{t.name}\to{k}\t{verdict {} P o}"
  IO.FS.writeFile (dir ++ "/index.tsv") ("\n".intercalate index.toList ++ "\n")
  IO.println s!"{index.size - 1} litmus tests under {dir}"

/-! ## Restriction -/

def wfCheck : List Nat → List (List Nat) → Bool
  | [], [] => true
  | x :: w, c :: cs => c.contains x && wfCheck w cs
  | _, _ => false

/-- The position of the node with identity `id` in `s`. -/
def idxOf (s : Static) (id : EvId) : Nat := posOf (List.range s.nodes.length) ((s.nodes.findIdx? (·.id == id)).getD s.nodes.length)

/-- Renumber the values of `f` on `xs` by their order: the `k`-th smallest gets `k`. -/
def compress (xs : List Nat) (f : Nat → Nat) : Nat → Nat := fun a =>
  (xs.filter fun b => f b < f a).length

/-- The device witness `w` of `P` restricted to `U`, as a witness of `P.restrict U`. -/
def restrictWitness (P : Shape) (w : List Nat) (U : Obj) : Except String (List Nat) := do
  let s := P.static
  let P' := P.restrict U
  let s' := P'.static
  let back := fun a' => idxOf s (s'.nodes.getD a' default).id
  let mut out : Array Nat := #[]
  for r' in s'.reads do
    let r := back r'
    match s.rf w r with
    | .init => out := out.push 0
    | .internal a =>
      let id := (s.nodes.getD a default).id
      match s'.nodes.findIdx? (·.id == id) with
      | some a' => out := out.push (a' + 1)
      | none =>
        let v := s.valueOfWrite w s.nodes.length a
        let l := (s.nodes.getD a default).ev.loc?
        match (s'.externalAt r').find? fun j => s'.external.getD j default == (l.getD default, v) with
        | some j => out := out.push (s'.nodes.length + 1 + j)
        | none => throw s!"external value {v} missing at the restriction to {repr U}"
    | .external v =>
      match (s'.externalAt r').find? fun j => (s'.external.getD j default).2 == v with
      | some j => out := out.push (s'.nodes.length + 1 + j)
      | none => throw "external read in the device shape"
  for a' in s'.writes do
    let same := (s'.writesAt a').map back
    out := out.push (compress same (s.rank w) (back a'))
  for a' in s'.mems do
    out := out.push (compress (s'.mems.map back) (s.ord w) (back a'))
  pure out.toList

def restrictCheck : IO UInt32 := do
  let mut bad := 0
  for t in tests do
    let P := t.shape
    let s := P.static
    let objs : List Obj := (P.threads.map fun th => Obj.workgroup th.wg) ++ P.threads.map fun th => Obj.thread th.id
    let mut n := 0
    let mut fails : List String := []
    for w in sequence s.spec do
      if s.consistent w then
        n := n + 1
        for U in objs do
          match restrictWitness P w U with
          | .error e => fails := fails ++ [e]
          | .ok w' =>
            let P' := P.restrict U
            if !(wfCheck w' P'.spec) then fails := fails ++ [s!"restriction to {repr U} is not well-formed"]
            else if !(P'.consistent w') then fails := fails ++ [s!"restriction to {repr U} is inconsistent"]
    if fails.isEmpty then IO.println s!"  {t.name}: {n} device witnesses restrict consistently"
    else
      bad := bad + 1
      IO.println s!"  {t.name}: FAIL {fails.head!} ({fails.length} failures over {n} witnesses)"
  pure (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for t in tests do IO.println t.name
    pure 0
  | ["table"] => table {}; pure 0
  | ["table", "--plant", p] =>
    match plantOf p with
    | some ax => table ax; pure 0
    | none => IO.eprintln s!"unknown plant {p}"; pure 2
  | ["dartagnan", "--out", dir] => dartagnan dir; pure 0
  | ["restrict"] => restrictCheck
  | _ =>
    IO.eprintln "usage: obend-litmus-check list | table [--plant P] | dartagnan --out DIR | restrict"
    pure 2
