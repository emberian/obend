module
/-
# Check units, constructed once

A form's witnesses can produce the same check many times. Comparing a new check against every
earlier key reconstructed those earlier checks, including their compiled laws and holed states.
The capture now constructs each candidate unit once, remembers complete units in a hash set, and
checks only the first key of each unit. Hashes select buckets; full structural equality decides
membership. A proposal likewise constructs the captured units once before classifying its calls.

The compiler replacements below preserve the exact list and order of accepted keys and the exact
classification. This cache lives for the operation; records loaded from disk still go through the
checker. It is not a persisted cache of judgment verdicts.
-/
public import Obend.Vault.FormCheck
public import Std.Data.HashSet.Lemmas
@[expose] public section

namespace Obend.Vault.Form

set_option autoImplicit false

/- Hash every part of a check, including its types and terms. Equality, never the hash alone,
decides reuse. These structural instances do not change the equality of any source type. -/
deriving instance Hashable for Obend.Core.Ty.Quantity
deriving instance Hashable for Obend.Core.Ty.Reuse
deriving instance Hashable for Obend.Core.Ty.Ty
deriving instance Hashable for Obend.Core.Ty.Binding
deriving instance Hashable for Obend.Core.Check.HoleDecl
deriving instance Hashable for Obend.Core.Term.Primitive
deriving instance Hashable for Obend.Core.Term.Term
deriving instance Hashable for CheckUnit

/-- A key together with the unit already constructed from it. The proof is erased at runtime. -/
structure KeyUnit where
  key : CheckKey
  unit : CheckUnit
  correct : unit = key.unit

/-- Accept the already constructed unit, retaining the key the log records. -/
def KeyUnit.checked (form : String) (ku : KeyUnit) : Option Checked :=
  if h : ku.unit.accepted = true then
    some ⟨form, ku.key, ku.correct ▸ h⟩
  else none

theorem KeyUnit.checked_eq (form : String) (ku : KeyUnit) :
    ku.checked form = Checked.of form ku.key := by
  obtain ⟨key, unit, h⟩ := ku
  subst unit
  rfl

/-- Keep the first key of each complete unit, carrying its constructed unit to the checker. -/
def uniqueUnits : List CheckKey → Std.HashSet CheckUnit → List KeyUnit
  | [], _ => []
  | k :: ks, seen =>
    let u := k.unit
    if seen.contains u then uniqueUnits ks seen
    else ⟨k, u, rfl⟩ :: uniqueUnits ks (seen.insert u)

/-- The set and the ordered keys describe the same prior units. -/
def UnitsSeen (seen : Std.HashSet CheckUnit) (acc : List CheckKey) : Prop :=
  ∀ u, seen.contains u = acc.any (fun k => k.unit == u)

theorem uniqueUnits_keys (ks : List CheckKey) (seen : Std.HashSet CheckUnit)
    (acc : List CheckKey) (hseen : UnitsSeen seen acc) :
    acc ++ (uniqueUnits ks seen).map KeyUnit.key =
      ks.foldl (fun prior k => if prior.any (·.unit == k.unit) then prior else prior ++ [k]) acc := by
  induction ks generalizing seen acc with
  | nil => simp [uniqueUnits]
  | cons k ks ih =>
    simp only [uniqueUnits, List.foldl_cons]
    rw [hseen k.unit]
    by_cases hk : acc.any (fun q => q.unit == k.unit) = true
    · simp only [hk, ↓reduceIte]
      exact ih seen acc hseen
    · simp only [hk, Bool.false_eq_true, ite_false, List.map_cons]
      have hs : UnitsSeen (seen.insert k.unit) (acc ++ [k]) := by
        intro u
        simp only [Std.HashSet.contains_insert, hseen u, List.any_append, List.any_cons,
          List.any_nil, Bool.or_false]
        exact Bool.or_comm _ _
      simpa only [List.append_assoc, List.singleton_append] using ih (seen.insert k.unit) (acc ++ [k]) hs

/-- Tail worker: append distinct constructed units to an unshared array. -/
def uniqueUnitsGo : List CheckKey → Std.HashSet CheckUnit → Array KeyUnit → List KeyUnit
  | [], _, out => out.toList
  | k :: ks, seen, out =>
    let u := k.unit
    if seen.contains u then uniqueUnitsGo ks seen out
    else uniqueUnitsGo ks (seen.insert u) (out.push ⟨k, u, rfl⟩)

theorem uniqueUnitsGo_eq (ks : List CheckKey) (seen : Std.HashSet CheckUnit) (out : Array KeyUnit) :
    uniqueUnitsGo ks seen out = out.toList ++ uniqueUnits ks seen := by
  induction ks generalizing seen out with
  | nil => simp [uniqueUnitsGo, uniqueUnits]
  | cons k ks ih =>
    simp only [uniqueUnitsGo, uniqueUnits]
    split
    · exact ih seen out
    · rw [ih]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append]

def uniqueUnitsArray (ks : List CheckKey) (seen : Std.HashSet CheckUnit) : List KeyUnit :=
  uniqueUnitsGo ks seen #[]

/-- Captures need no stack frame per distinct check; the array worker is the ordered deduplicator. -/
@[csimp] theorem uniqueUnits_eq_array : @uniqueUnits = @uniqueUnitsArray := by
  funext ks seen
  simp only [uniqueUnitsArray, uniqueUnitsGo_eq, Array.toList_empty, List.nil_append]

/-- Capture's checks with unit construction shared by deduplication and checking. -/
def Form.checksAtCached (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) : List Checked :=
  let keys := f.witnesses.flatMap fun a =>
    match preparedOf H s f [] a with
    | .ok (_, prs) => (callsOf s.entries prs).map fun x => keyOf x.1 f.assets x.2
    | .error _ => []
  (uniqueUnits keys ∅).filterMap (KeyUnit.checked f.name)

/-- Every capture keeps exactly its original checks, in their original order. -/
@[csimp] theorem Form.checksAt_eq_cached : @Form.checksAt = @Form.checksAtCached := by
  funext H s f
  unfold Form.checksAt Form.checksAtCached
  dsimp only
  have hkeys : (fun a => match preparedOf H s f [] a with
      | .ok (_, prs) => (callsOf s.entries prs).map fun x => keyOf x.1 f.assets x.2
      | .error _ => []) =
      (fun a => Form.checksAt.match_1 (fun _ => List CheckKey) (preparedOf H s f [] a)
        (fun _ prs => (callsOf s.entries prs).map fun x => keyOf x.1 f.assets x.2) (fun _ => [])) := by
    funext a
    cases preparedOf H s f [] a with
    | error e => rfl
    | ok pair => cases pair; rfl
  rw [← hkeys]
  have hk := uniqueUnits_keys
    (f.witnesses.flatMap fun a => match preparedOf H s f [] a with
      | .ok (_, prs) => (callsOf s.entries prs).map fun x => keyOf x.1 f.assets x.2
      | .error _ => []) ∅ [] (by intro u; simp)
  simp only [List.nil_append] at hk
  rw [← hk, List.filterMap_map]
  congr 1
  funext ku
  exact (KeyUnit.checked_eq f.name ku).symm

/-- Captured units, constructed once, indexed by form and complete unit. -/
def capturedUnits (checked : List Checked) : Std.HashSet (String × CheckUnit) :=
  .ofList (checked.map fun c => (c.form, c.unit))

theorem capturedUnits_contains (checked : List Checked) (form : String) (u : CheckUnit) :
    (capturedUnits checked).contains (form, u) =
      checked.any (fun c => c.form == form && c.unit == u) := by
  apply Bool.eq_iff_iff.mpr
  simp [capturedUnits, List.mem_map, List.any_eq_true, Prod.ext_iff]

/-- Classify using the shared set of captured units. -/
def classifyCached (checked : List Checked) (form : String) (moved : List String)
    (calls : List (String × JudgeCall)) : List Judged :=
  let units := capturedUnits checked
  calls.map fun x =>
    let u := unitOf x.1 moved x.2
    ⟨x.1, x.2, u, units.contains (form, u)⟩

/-- The cached classifier makes precisely the same kept/checked-now decision for every call. -/
@[csimp] theorem classify_eq_cached : @classify = @classifyCached := by
  funext checked form moved calls
  simp only [classify, classifyCached, capturedUnits_contains]

/-- The overlap count for the classifier's own result. -/
def recheckedClassified (checked : List Checked) (form : String) (moved : List String)
    (calls : List (String × JudgeCall)) : Nat :=
  rechecked checked form (classify checked form moved calls)

/-- A classifier never checks a kept unit again (`rechecked_zero`). -/
def recheckedClassifiedZero (_ : List Checked) (_ : String) (_ : List String)
    (_ : List (String × JudgeCall)) : Nat := 0

/-- Computing this diagnostic needs neither a second membership scan nor another checker call. -/
@[csimp] theorem recheckedClassified_eq_zero : @recheckedClassified = @recheckedClassifiedZero := by
  funext checked form moved calls
  exact rechecked_zero checked form moved calls

end Obend.Vault.Form
