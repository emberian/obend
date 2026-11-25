module
public import Std.Data.HashMap
import Std.Data.HashSet
public import Obend.SymbolicZk.SkolemChaseCore
import all Obend.SymbolicZk.SkolemChaseCore
public section
namespace Obend.SemanticKG
open Obend.SymbolicZk.SkolemChaseCore
set_option autoImplicit false

namespace Colt
abbrev Column := Array Nat
abbrev Rows := Array Nat
private abbrev Buckets := Std.HashMap Nat Rows

/-- A ragged column has no key at a missing row. Such rows cannot satisfy an equality probe. -/
private def insertRow (col : Column) (m : Buckets) (row : Nat) : Buckets :=
  match col[row]? with
  | none => m
  | some key => m.alter key (fun bucket => some ((bucket.getD #[]).push row))

private theorem partition_lookup (col : Column) (rows : Rows) (k : Nat) :
    ((rows.foldl (insertRow col) ({} : Buckets))[k]?).getD #[] =
    rows.filter (fun r => col[r]? == some k) := by
  have go (rs : List Nat) (m : Buckets) :
      ((rs.foldl (insertRow col) m)[k]?).getD #[] =
        (m[k]?).getD #[] ++ (rs.filter (fun r => col[r]? == some k)).toArray := by
    induction rs generalizing m with
    | nil => simp
    | cons r rs ih =>
      rw [List.foldl_cons, ih]
      unfold insertRow
      cases h : col[r]? with
      | none => simp [h]
      | some key =>
        by_cases he : key = k
        · subst key; simp [h]
        · simp [h, he, Std.HashMap.getElem?_alter]
  apply Array.toList_inj.mp
  simpa using congrArg Array.toList (go rows.toList {})

/-- Reference equality selection for a sequence of bound attributes. -/
def select : List Column → Rows → List Nat → Rows
  | _, rows, [] => rows
  | [], _, _ :: _ => #[]
  | col :: cols, rows, k :: ks =>
    select cols (rows.filter (fun r => col[r]? == some k)) ks

private theorem select_empty (cols : List Column) (keys : List Nat) : select cols #[] keys = #[] := by
  induction cols generalizing keys with
  | nil => cases keys <;> rfl
  | cons c cs ih => cases keys <;> simp [select, ih]

/-- Keeping both fields in a cursor prevents the compiler from eta-expanding the partition
constructor into the inner loop of a batch probe. -/
structure Cursor where
  rows : Rows
  next : Thunk (Std.HashMap Nat (List Nat → Rows))

def Cursor.probe (c : Cursor) : List Nat → Rows
  | [] => c.rows
  | k :: rest => match c.next.get[k]? with
    | some search => search rest
    | none => #[]

/-- Opening a level allocates its thunk. The first nonempty probe partitions this level's rows.
Each child closes over its own cursor so subsequent probes reuse the same partition. -/
@[noinline] def openTrie : List Column → Rows → Cursor
  | [], rows => ⟨rows, ⟨fun _ => {}⟩⟩
  | col :: cols, rows => ⟨rows, ⟨fun _ =>
      (rows.foldl (insertRow col) ({} : Buckets)).map fun _ rs => (openTrie cols rs).probe⟩⟩

theorem probe_eq_select (cols : List Column) (rows : Rows) (keys : List Nat) :
    (openTrie cols rows).probe keys = select cols rows keys := by
  induction cols generalizing keys rows with
  | nil => cases keys <;> simp [openTrie, Cursor.probe, Thunk.get, select]
  | cons col cols ih =>
    cases keys with
    | nil => rfl
    | cons k ks =>
      simp only [Cursor.probe, openTrie, Thunk.get, Std.HashMap.getElem?_map, select]
      have h := partition_lookup col rows k
      cases hb : (rows.foldl (insertRow col) ({} : Buckets))[k]? with
      | none => simp only [hb, Option.getD_none] at h; simp [← h, select_empty]
      | some rs => simp only [hb, Option.getD_some] at h; simp [← h, ih]

/-- Output groups retain left row order, right row order, and duplicate multiplicity. -/
def relationalJoin (left : Array (List Nat)) (cols : List Column) (rightCount : Nat) : Array Rows :=
  left.map (select cols (Array.range rightCount))

def coltJoin (left : Array (List Nat)) (cols : List Column) (rightCount : Nat) : Array Rows :=
  let probe := openTrie cols (Array.range rightCount)
  left.map probe.probe

theorem coltJoin_eq_relationalJoin (left : Array (List Nat)) (cols : List Column) (rightCount : Nat) :
    coltJoin left cols rightCount = relationalJoin left cols rightCount := by
  unfold coltJoin relationalJoin
  exact congrArg (fun f => left.map f) (funext (probe_eq_select _ _))

/-- A Free Join subatom checks a relation prefix using the named positions of the current tuple.
Order each relation's physical columns by the order its attributes are first bound. -/
structure Subatom where
  relation : Nat
  bound : List Nat

structure JoinStep where
  driver : Subatom
  column : Nat
  checks : Array Subatom

structure Relation where
  columns : List Column
  count : Nat

private abbrev Lookup := Nat → List Nat → Rows

private def matchingRows (lookup : Lookup) (tuple : Array Nat) (sub : Subatom) : Rows :=
  match sub.bound.mapM (fun v => tuple[v]?) with
  | some keys => lookup sub.relation keys
  | none => #[]

private def extendTuple (db : Array Relation) (lookup : Lookup) (s : JoinStep)
    (tuple : Array Nat) : Array (Array Nat) := Id.run do
  let some col := db[s.driver.relation]?.bind (fun r => r.columns[s.column]?) | return #[]
  let mut seen : Std.HashSet Nat := {}
  let mut result := #[]
  for row in matchingRows lookup tuple s.driver do
    let some value := col[row]? | continue
    if seen.contains value then continue
    seen := seen.insert value
    let extended := tuple.push value
    if s.checks.all (fun sub => !(matchingRows lookup extended sub).isEmpty) then
      result := result.push extended
  return result

private def executePlan (db : Array Relation) (lookup : Lookup) (steps : Array JoinStep) :=
  steps.foldl (fun tuples s => tuples.flatMap (extendTuple db lookup s)) #[#[]]

/-- Nested relational semijoins. At each planned variable, project the driver's matching rows,
deduplicate its values, and retain extensions witnessed by every subatom at that node. -/
def relationalPlan (db : Array Relation) (steps : Array JoinStep) : Array (Array Nat) :=
  executePlan db (fun idx keys => match db[idx]? with
    | some r => select r.columns (Array.range r.count) keys
    | none => #[]) steps

/-- One shared lazy trie per relation. Different subatoms of the same relation need not appear
in the same join node. This permits interleaved plans for cyclic joins. -/
def freeJoin (db : Array Relation) (steps : Array JoinStep) : Array (Array Nat) :=
  let cursors := db.map (fun r => openTrie r.columns (Array.range r.count))
  executePlan db (fun idx keys => match cursors[idx]? with
    | some cursor => cursor.probe keys
    | none => #[]) steps

theorem freeJoin_eq_relationalPlan (db : Array Relation) (steps : Array JoinStep) :
    freeJoin db steps = relationalPlan db steps := by
  unfold freeJoin relationalPlan
  dsimp only
  apply congrArg (fun lookup => executePlan db lookup steps)
  funext i keys
  cases hr : db[i]? <;> simp [Array.getElem?_map, hr, probe_eq_select]

end Colt

private def argumentKey (a : Atom Term) : Nat := (a.args.head?.map extractConstId).getD 0

private def boundKey (p : PatAtom) (σ : Subst Term) : Option Nat :=
  (p.args.head?.bind (evalPatTerm Term.const σ)).map extractConstId

/-- Free-join body evaluation on the WFS atom dictionary. A relation probe followed by an optional
first-argument probe narrows the rows before the ordinary matcher binds the remaining variables. -/
def openAtomTrie (atoms : Array (Atom Term)) : Colt.Cursor :=
  Colt.openTrie [atoms.map (·.rel), atoms.map argumentKey]
    (Array.range atoms.size)

def matchBodyColt (atoms : Array (Atom Term)) (probe : List Nat → Colt.Rows) :
    List PatAtom → Subst Term → Array (Subst Term)
  | [], σ => #[σ]
  | p :: tail, σ =>
    let keys := p.rel :: (boundKey p σ).toList
    (probe keys).flatMap fun i =>
      match atoms[i]?.bind (matchPatAtom Term.const σ p) with
      | none => #[]
      | some next => matchBodyColt atoms probe tail next

private theorem match_keys {σ τ : Subst Term} {p : PatAtom} {a : Atom Term}
    (hm : matchPatAtom Term.const σ p a = some τ) :
    a.rel = p.rel ∧ ∀ k, boundKey p σ = some k → argumentKey a = k := by
  obtain ⟨ext, ev⟩ := matchPatAtom_sound _ _ _ _ _ hm
  unfold evalPatAtom at ev
  cases args : evalPatArgs Term.const τ p.args with
  | none => simp [args] at ev
  | some ts =>
    simp only [args, Option.some.injEq] at ev
    subst a
    refine ⟨rfl, ?_⟩
    intro k hk
    unfold boundKey at hk
    cases hp : p.args with
    | nil => simp [hp] at hk
    | cons pt pts =>
      simp only [hp, List.head?_cons, Option.bind_some] at hk
      cases he : evalPatTerm Term.const σ pt with
      | none => simp [he] at hk
      | some t =>
        have he' := evalPatTerm_ext Term.const ext pt t he
        simp only [he, Option.map_some, Option.some.injEq] at hk
        simp only [hp, evalPatArgs, he'] at args
        cases ht : evalPatArgs Term.const τ pts with
        | none => simp [ht] at args
        | some rest =>
          simp only [ht, Option.some.injEq] at args
          subst ts
          simpa [argumentKey] using hk

private theorem skip_filtered {α β : Type} (p : α → Bool) (emit : α → List β)
    (skip : ∀ x, p x = false → emit x = []) (xs : List α) :
    (xs.filter p).flatMap emit = xs.flatMap emit := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h, ih, skip]

private theorem emit_all {α β : Type} (xs : Array α) (emit : α → List β) :
    (List.range xs.size).flatMap (fun i => (xs[i]?).toList.flatMap emit) = xs.toList.flatMap emit := by
  have loop (n : Nat) (hn : n ≤ xs.size) :
      (List.range n).flatMap (fun i => (xs[i]?).toList.flatMap emit) =
        (xs.toList.take n).flatMap emit := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hi : n < xs.size := hn
      rw [List.range_succ, List.take_succ_eq_append_getElem (by simpa using hi)]
      simp [List.flatMap_append, ih (Nat.le_of_lt hi), hi]
  simpa [List.take_of_length_le (show xs.toList.length ≤ xs.size from Nat.le_refl _)] using loop xs.size (Nat.le_refl _)

/-- Reference body matcher over a list of ground atoms (`matchPatAtoms`). -/
abbrev matchBody (atoms : List (Atom Term)) (ps : List PatAtom) (σ : Subst Term) :
    List (Subst Term) :=
  matchPatAtoms Term.const σ ps atoms

/-- Every multi-atom body produces exactly the reference substitutions, with their original
order and multiplicity. This includes partially bound and repeated variables and Skolem terms. -/
theorem matchBodyColt_eq_spec (atoms : Array (Atom Term)) (ps : List PatAtom) (σ : Subst Term) :
    (matchBodyColt atoms (openAtomTrie atoms).probe ps σ).toList =
      matchPatAtoms Term.const σ ps atoms.toList := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
    let emit := fun a => match matchPatAtom Term.const σ p a with
      | some next => matchPatAtoms Term.const next ps atoms.toList
      | none => []
    let out := fun (i : Nat) => atoms[i]?.toList.flatMap emit
    have project (i : Nat) :
        (match atoms[i]?.bind (matchPatAtom Term.const σ p) with
        | none => #[]
        | some next => matchBodyColt atoms (openAtomTrie atoms).probe ps next).toList = out i := by
      cases h : atoms[i]? with
      | none => simp [out, h]
      | some a =>
        cases h' : matchPatAtom Term.const σ p a <;> simp [out, emit, h, h', ih]
    have drop {f : Atom Term → Nat} {k : Nat}
        (pres : ∀ a t, matchPatAtom Term.const σ p a = some t → f a = k) :
        ∀ i, ((atoms.map f)[i]? == some k) = false → out i = [] := by
      intro i hi
      cases h : atoms[i]? with
      | none => simp [out, h]
      | some a =>
        cases hm : matchPatAtom Term.const σ p a with
        | none => simp [out, emit, h, hm]
        | some t => simp [Array.getElem?_map, h, pres a t hm] at hi
    have rel := @drop (·.rel) p.rel (fun _ _ hm => (match_keys hm).1)
    simp only [matchBodyColt, Array.toList_flatMap, project, matchPatAtoms]
    refine Eq.trans (b := atoms.toList.flatMap emit) ?left ?right
    case right =>
      apply congrArg (fun f => atoms.toList.flatMap f)
      funext a
      cases h : matchPatAtom Term.const σ p a <;> simp [emit, h]
    rw [openAtomTrie, Colt.probe_eq_select]
    cases hk : boundKey p σ with
    | none =>
      simp only [Option.toList_none, Colt.select, Array.toList_filter, Array.toList_range]
      rw [skip_filtered _ _ rel]; exact emit_all atoms emit
    | some k =>
      have arg := @drop argumentKey k (fun _ _ hm => (match_keys hm).2 k hk)
      simp only [Option.toList_some, Colt.select, Array.toList_filter, Array.toList_range]
      rw [skip_filtered _ _ arg, skip_filtered _ _ rel]; exact emit_all atoms emit

/-- Exact equality between COLT trie-indexed body evaluation and reference `matchBody`. -/
theorem matchBodyColt_eq_matchBody (atoms : Array (Atom Term)) (ps : List PatAtom) (σ : Subst Term) :
    (matchBodyColt atoms (openAtomTrie atoms).probe ps σ).toList = matchBody atoms.toList ps σ :=
  matchBodyColt_eq_spec atoms ps σ

/-- Soundness of COLT body matching: every emitted substitution extends `σ` and instantiates
`ps` into atoms present in `atoms`. -/
theorem matchBodyColt_sound (atoms : Array (Atom Term)) (ps : List PatAtom) (σ σ' : Subst Term)
    (hm : σ' ∈ matchBodyColt atoms (openAtomTrie atoms).probe ps σ) :
    ExtendsSubst σ σ' ∧
      ∃ groundAtoms, evalPatAtoms Term.const σ' ps = some groundAtoms ∧
        ∀ a ∈ groundAtoms, a ∈ atoms.toList := by
  have hmem : σ' ∈ matchPatAtoms Term.const σ ps atoms.toList := by
    rw [← matchBodyColt_eq_spec]; exact Array.mem_toList_iff.mpr hm
  exact matchPatAtoms_sound Term.const σ σ' ps atoms.toList hmem

/-- Completeness of COLT body matching: any substitution `τ` extending `σ` whose instantiation
of `ps` lies in `atoms` is covered by an emitted substitution `σ'` extending `σ` and extended by `τ`. -/
theorem matchBodyColt_complete (atoms : Array (Atom Term)) (ps : List PatAtom) (σ τ : Subst Term)
    (hext : ExtendsSubst σ τ) (groundAtoms : List (Atom Term))
    (hev : evalPatAtoms Term.const τ ps = some groundAtoms)
    (hSub : ∀ a ∈ groundAtoms, a ∈ atoms.toList) :
    ∃ σ' ∈ matchBodyColt atoms (openAtomTrie atoms).probe ps σ, ExtendsSubst σ' τ := by
  obtain ⟨σ', hmem, hext'⟩ :=
    matchPatAtoms_complete Term.const σ τ hext ps groundAtoms atoms.toList hev hSub
  rw [← matchBodyColt_eq_spec] at hmem
  exact ⟨σ', Array.mem_toList_iff.mp hmem, hext'⟩

private theorem match_eq_exec (atoms : Array (Atom Term)) (body : List PatAtom) (σ : Subst Term) :
    matchBodyColt atoms (openAtomTrie atoms).probe body σ = matchPatAtomsExec Term.const σ body atoms :=
  Array.toList_inj.mp ((matchBodyColt_eq_spec atoms body σ).trans
    (matchPatAtomsExec_eq_spec Term.const σ body atoms).symm)

/-- All rule bodies and heads in a satisfaction check share one index on the immutable facts. -/
def satisfiedColt (rules : Array TgdRule) (atoms : Array (Atom Term)) : Bool :=
  let cursor := openAtomTrie atoms
  rules.all fun r => (matchBodyColt atoms cursor.probe r.body []).all fun σ =>
    !(matchBodyColt atoms cursor.probe r.head (frontierSubst r.frontierVars σ)).isEmpty

@[csimp] theorem allRulesSatisfiedExec_eq_colt : @allRulesSatisfiedExec = @satisfiedColt := by
  funext rules atoms; simp [satisfiedColt, allRulesSatisfiedExec, isSatisfiedExec, match_eq_exec]

private def fireRuleColt (atoms : Array (Atom Term)) (r : TgdRule) : Array (Atom Term) :=
  let cursor := openAtomTrie atoms
  (matchBodyColt atoms cursor.probe r.body []).foldl (fireMatchExec r) atoms

private theorem fireRuleColt_eq : fireRuleColt = fireRuleExec := by
  funext atoms r; simp [fireRuleColt, fireRuleExec, match_eq_exec]

def runColtChase (rules : Array TgdRule) : Nat → Array (Atom Term) → Array (Atom Term)
  | 0, atoms => atoms
  | n + 1, atoms => if satisfiedColt rules atoms then atoms
    else runColtChase rules n (rules.foldl fireRuleColt atoms)

@[csimp] theorem runBoundedChaseExec_eq_colt : @runBoundedChaseExec = @runColtChase := by
  funext rs n atoms
  induction n generalizing atoms with
  | zero => rfl
  | succ n ih => simp [runColtChase, runBoundedChaseExec, ← allRulesSatisfiedExec_eq_colt,
      stepChaseExec, fireRuleColt_eq, ih]

end Obend.SemanticKG
