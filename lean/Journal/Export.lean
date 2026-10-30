module
/-
# Journal.Export — one row per declaration of the `Obend` tree, from the built environment

The exporter imports the tree's `.olean`s at `OLeanLevel.private` (every body, as if no `module`
annotations existed), walks `Environment.constants`, keeps the constants whose module name starts
with `Obend`, and writes a `Journal.Row` for each. A second import of the `module` files alone at
`OLeanLevel.exported` is the honest instrument for visibility: a name the exported view finds is
`public`; a definition whose value the exported view carries is `exposed`.

Content hashes are `hashExpr`: a 64-bit structural hash of the kernel term (constructor tag,
constant names, universe levels with the declaration's level parameters renamed to their position,
literals, de Bruijn indices, projection structure and index; binder names, binder info and `mdata`
omitted, as `Expr.eqv` omits them), mixed with `mixHash` and cached by pointer so it is linear in
the DAG. It is not `Expr.hash`, whose cached field is 32 bits, and not a pretty-printed string,
whose rendering depends on `pp` options and open namespaces. The same traversal collects the
constants a term cites, including the structure named by an `Expr.proj`, which `getUsedConstants`
omits (the memo's note on `Verify/ObjectiveManifest.lean`).

Axiom sets are collected as `Lean.collectAxioms` collects them (type and value of definitions,
theorems and opaques; types of constructors and recursors; an inductive's type and constructors),
with one memo shared across every row instead of one per call.
-/
public import Lean
public import Journal.Journal
@[expose] public section

namespace Journal.Export

open Lean

/-! ## A 64-bit structural hash and the citations, in one cached traversal -/

/-- Hash of a universe level with the declaration's parameters renamed to their position. -/
def hashLevel (lps : List Name) : Level → UInt64
  | .zero => 1
  | .succ l => mixHash 2 (hashLevel lps l)
  | .max a b => mixHash 3 (mixHash (hashLevel lps a) (hashLevel lps b))
  | .imax a b => mixHash 4 (mixHash (hashLevel lps a) (hashLevel lps b))
  | .param n => mixHash 5 (lps.idxOf n).toUInt64
  | .mvar _ => 6

namespace Impl

unsafe structure State where
  cache : PtrMap Expr UInt64 := mkPtrMap
  cites : NameSet := {}

unsafe def visit (lps : List Name) (e : Expr) : StateM State UInt64 := do
  if let some h := (← get).cache.find? e then return h
  let h ← match e with
    | .bvar i => pure (mixHash 11 i.toUInt64)
    | .fvar id => pure (mixHash 12 (hash id.name))
    | .mvar id => pure (mixHash 13 (hash id.name))
    | .sort l => pure (mixHash 14 (hashLevel lps l))
    | .const n ls => do
      modify fun s => { s with cites := s.cites.insert n }
      pure (mixHash 15 (ls.foldl (fun acc l => mixHash acc (hashLevel lps l)) (hash n)))
    | .app f a => do
      let hf ← visit lps f
      let ha ← visit lps a
      pure (mixHash 16 (mixHash hf ha))
    | .lam _ t b _ => do
      let ht ← visit lps t
      let hb ← visit lps b
      pure (mixHash 17 (mixHash ht hb))
    | .forallE _ t b _ => do
      let ht ← visit lps t
      let hb ← visit lps b
      pure (mixHash 18 (mixHash ht hb))
    | .letE _ t v b _ => do
      let ht ← visit lps t
      let hv ← visit lps v
      let hb ← visit lps b
      pure (mixHash 19 (mixHash ht (mixHash hv hb)))
    | .lit l => pure (mixHash 20 (hash l))
    | .mdata _ b => visit lps b
    | .proj s i b => do
      modify fun st => { st with cites := st.cites.insert s }
      let hb ← visit lps b
      pure (mixHash 21 (mixHash (hash s) (mixHash i.toUInt64 hb)))
  modify fun s => { s with cache := s.cache.insert e h }
  return h

unsafe def analyzeUnsafe (lps : List Name) (e : Expr) : UInt64 × Array Name :=
  let (h, s) := (visit lps e).run {}
  (h, s.cites.toArray.qsort Name.lt)

end Impl

/-- The structural hash of `e` and, sorted, the constants it cites (`const` names and `proj`
structures). -/
@[implemented_by Impl.analyzeUnsafe]
opaque analyze (lps : List Name) (e : Expr) : UInt64 × Array Name

/-- The structural hash alone. -/
def hashExpr (lps : List Name) (e : Expr) : UInt64 := (analyze lps e).1

/-! ## Axioms, memoised across the whole export -/

/-- The expressions `collectAxioms` walks for a constant, and the constants it recurses into besides
the ones those cite (an inductive's constructors). -/
def axiomRoots : ConstantInfo → List Expr × List Name
  | .axiomInfo v => ([v.type], [])
  | .defnInfo v => ([v.type, v.value], [])
  | .thmInfo v => ([v.type, v.value], [])
  | .opaqueInfo v => ([v.type, v.value], [])
  | .quotInfo _ => ([], [])
  | .ctorInfo v => ([v.type], [])
  | .recInfo v => ([v.type], [])
  | .inductInfo v => ([v.type], v.ctors)

/-- Axioms reachable from `c`, as `Lean.collectAxioms` finds them, with the memo in the state. The
sentinel `#[]` inserted before recursing is `collectAxioms`'s own guard against the inductive ↔
constructor cycle, kept so the two agree. -/
partial def axiomsOf (env : Environment) (c : Name) : StateM (NameMap (Array Name)) (Array Name) := do
  if let some r := (← get).find? c then return r
  modify (·.insert c #[])
  let mut acc : NameSet := {}
  match env.find? c with
  | none => pure ()
  | some ci =>
    if ci matches .axiomInfo _ then acc := acc.insert c
    let (exprs, extra) := axiomRoots ci
    let mut names : Array Name := extra.toArray
    for e in exprs do
      names := names ++ e.getUsedConstants
    for n in names do
      for a in (← axiomsOf env n) do
        acc := acc.insert a
  let r := acc.toArray.qsort Name.lt
  modify (·.insert c r)
  return r

/-! ## Rows -/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Is `n` declared in a module whose name starts with `root`? -/
def inTree (env : Environment) (root : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => root.isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

def hashNames (names : List Name) : UInt64 :=
  names.foldl (fun acc n => mixHash acc (hash n)) 23

/-- The value hash and value citations of a constant: the body for definitions, theorems and
opaques; the shape for inductives (parameters, indices, recursivity, the block, the constructors
with their types), constructors (inductive, index, arities) and recursors (arities, the rules'
right-hand sides). Axioms and quotients have none. -/
def valueOf (env : Environment) (ci : ConstantInfo) : UInt64 × Array Name :=
  let lps := ci.levelParams
  match ci with
  | .defnInfo v => analyze lps v.value
  | .thmInfo v => analyze lps v.value
  | .opaqueInfo v => analyze lps v.value
  | .axiomInfo _ | .quotInfo _ => (0, #[])
  | .inductInfo v =>
    let ctorHashes := v.ctors.foldl (init := hashNames v.ctors) fun acc c =>
      match env.find? c with
      | some cci => mixHash acc (hashExpr cci.levelParams cci.type)
      | none => acc
    let shape := mixHash v.numParams.toUInt64 <| mixHash v.numIndices.toUInt64 <|
      mixHash (if v.isRec then 1 else 0) <| mixHash (if v.isReflexive then 1 else 0) <|
      mixHash (hashNames v.all) ctorHashes
    (shape, (v.ctors ++ v.all).toArray.qsort Name.lt)
  | .ctorInfo v =>
    (mixHash (hash v.induct) <| mixHash v.cidx.toUInt64 <|
      mixHash v.numParams.toUInt64 v.numFields.toUInt64, #[v.induct])
  | .recInfo v =>
    let (h, cites) := v.rules.foldl (init := (hashNames v.all, ({} : NameSet))) fun (acc, cs) rule =>
      let (hr, cr) := analyze lps rule.rhs
      (mixHash acc (mixHash (hash rule.ctor) (mixHash rule.nfields.toUInt64 hr)),
        cr.foldl (·.insert ·) (cs.insert rule.ctor))
    let shape := mixHash v.numParams.toUInt64 <| mixHash v.numIndices.toUInt64 <|
      mixHash v.numMotives.toUInt64 <| mixHash v.numMinors.toUInt64 <|
      mixHash (if v.k then 1 else 0) h
    (shape, (v.all.foldl (·.insert ·) cites).toArray.qsort Name.lt)

/-- The visibility instrument: the exported view, when the tree's `module` files were imported at
`OLeanLevel.exported`. `none` when no such view was built. -/
structure Views where
  /-- everything, private level -/
  all : Environment
  /-- the `module` files, exported level -/
  exported : Option Environment

/-- The row of one constant. -/
def rowOf (views : Views) (root : Name) (n : Name) (ci : ConstantInfo) :
    StateM (NameMap (Array Name)) Row := do
  let env := views.all
  let moduleName := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let (typeHash, typeCites) := analyze ci.levelParams ci.type
  let (valueHash, valueCites) := valueOf env ci
  let axioms ← axiomsOf env n
  let keep (cs : Array Name) : List String :=
    (cs.filter (inTree env root ·)).toList.map (·.toString (escape := false))
  let (visibility, exposed) := match views.exported with
    | some ex =>
      let ex := ex.setExporting true
      match ex.find? n with
      | some eci => ("public", eci.hasValue)
      | none =>
        -- a legacy file is not in the exported view: its names are all visible, private ones mangled
        if (ex.header.moduleNames.contains moduleName) then ("private", false)
        else (if isPrivateName n then "private" else "public", true)
    | none => (if isPrivateName n then "private" else "public", true)
  return {
    name := n.toString (escape := false)
    module := moduleName.toString (escape := false)
    kind := kindOf ci
    visibility, exposed
    typeCites := keep typeCites
    valueCites := keep valueCites
    typeHash, valueHash
    axioms := axioms.toList.map (·.toString (escape := false)) }

/-- Every row of the tree under `root`, sorted by name. -/
def rows (views : Views) (root : Name) : Array Row :=
  let names := views.all.constants.fold (init := #[]) fun acc n ci =>
    if inTree views.all root n then acc.push (n, ci) else acc
  let names := names.qsort fun a b => Name.lt a.1 b.1
  let (rs, _) := (names.mapM fun (n, ci) => rowOf views root n ci).run {}
  rs

/-! ## JSON -/

def _root_.Journal.Row.toJson (r : Row) : Json :=
  Json.mkObj [
    ("name", r.name), ("module", r.module), ("kind", r.kind), ("visibility", r.visibility),
    ("exposed", r.exposed),
    ("typeCites", Json.arr (r.typeCites.toArray.map Json.str)),
    ("valueCites", Json.arr (r.valueCites.toArray.map Json.str)),
    ("typeHash", toString r.typeHash), ("valueHash", toString r.valueHash),
    ("axioms", Json.arr (r.axioms.toArray.map Json.str))]

def _root_.Journal.Row.fromJson? (j : Json) : Except String Row := do
  let strs (k : String) : Except String (List String) := do
    let arr ← (← j.getObjVal? k).getArr?
    arr.toList.mapM (·.getStr?)
  let u64 (k : String) : Except String UInt64 := do
    let s ← (← j.getObjVal? k).getStr?
    match s.toNat? with
    | some n => pure n.toUInt64
    | none => throw s!"{k}: not a decimal: {s}"
  return {
    name := ← (← j.getObjVal? "name").getStr?
    module := ← (← j.getObjVal? "module").getStr?
    kind := ← (← j.getObjVal? "kind").getStr?
    visibility := ← (← j.getObjVal? "visibility").getStr?
    exposed := ← (← j.getObjVal? "exposed").getBool?
    typeCites := ← strs "typeCites"
    valueCites := ← strs "valueCites"
    typeHash := ← u64 "typeHash"
    valueHash := ← u64 "valueHash"
    axioms := ← strs "axioms" }

/-- The first line of an export file: what was exported, from where. -/
structure Header where
  commit : String
  dirty : Bool
  toolchain : String
  root : String
  /-- the module prefix an `--only` export was restricted to; empty for the whole tree -/
  only : String := ""
  modules : Nat
  rows : Nat
  deriving Repr

def Header.toJson (h : Header) : Json :=
  Json.mkObj [("header", true), ("commit", h.commit), ("dirty", h.dirty),
    ("toolchain", h.toolchain), ("root", h.root), ("only", h.only), ("modules", h.modules),
    ("rows", h.rows)]

/-- The whole file: header line, then one row per line. -/
def render (h : Header) (rs : Array Row) : String :=
  let lines := #[h.toJson.compress] ++ rs.map (·.toJson.compress)
  String.intercalate "\n" lines.toList ++ "\n"

/-- Read an export file back: rows by name (the header line is skipped). -/
def parse (text : String) : Except String Export := do
  let mut rows : List Row := []
  for line in text.splitOn "\n" do
    if line.all Char.isWhitespace then continue
    let j ← Json.parse line
    if (j.getObjVal? "header").toOption.isSome then continue
    rows := (← Row.fromJson? j) :: rows
  return Export.ofRows rows

end Journal.Export

end
