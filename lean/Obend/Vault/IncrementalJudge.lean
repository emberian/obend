module
public import Obend.Vault.Store
import all Obend.Vault.Store
public import Obend.Doc.Patch
public import Obend.Spec.Law
public section
namespace Obend.Vault.IncrementalJudge
open Obend.Core.Data (Data)
open Obend.Doc

abbrev Tip := List (String × Data)
abbrev Slots := List (String × Option Data)
abbrev RemoteLaw := String × Laws × Option Data

/-- The external operands of the four link-law loops, in first-refusal order.
The page, row, actor and request operands belong to the indexed Prepared itself. -/
structure Reads where
  mine : Slots
  incoming : List (Option RemoteLaw)
  mineBy : Slots
  outgoing : List (Option RemoteLaw)

instance : DecidableEq Reads := fun a b =>
  letI : DecidableEq Slots := inferInstance
  letI : DecidableEq RemoteLaw := inferInstance
  letI : DecidableEq (List (Option RemoteLaw)) := inferInstance
  decidable_of_iff
  (a.mine = b.mine ∧ a.incoming = b.incoming ∧ a.mineBy = b.mineBy ∧ a.outgoing = b.outgoing)
  ⟨fun ⟨a₁,a₂,a₃,a₄⟩ => by cases a; cases b; congr, fun h => h ▸ ⟨rfl,rfl,rfl,rfl⟩⟩

private def slots (world : VaultStore) (names : List String) : Slots :=
  names.map fun c => (c, world c)

private def incomingLaw (es : List Entry) (world : VaultStore) (pr : Prepared) (e : Entry) :
    Option RemoteLaw :=
  if e.name != pr.p.name && (citesPage e.graph pr.p.id && (linkTargets e.graph).contains pr.p.id) then
    match lawsFor es e.name e.graph with
    | .ok laws => if (linkLaws laws).isEmpty then none else some (e.name, laws, world pr.p.name)
    | .error _ => none
  else none

private def outgoingLaw (es res : List Entry) (world : VaultStore) (pr : Prepared) (over : Tip)
    (x : String) : Option RemoteLaw :=
  if x != pr.p.name then
    match es.find? (·.name == x) with
    | some e =>
      match lawsFor es e.name e.graph with
      | .ok laws =>
        if (byLaws laws).isEmpty then none else
        let gx := if over.isEmpty then e.graph else ((res.find? (·.name == x)).map (·.graph)).getD e.graph
        let listed := if (linkTargets gx).contains pr.p.id then [pr.p.name] else []
        some (e.name, laws, listedStore world listed pr.p.name)
      | .error _ => none
    | none => none
  else none

def observe (es res : List Entry) (pr : Prepared) (over : Tip) (bucket : List Entry) : Reads :=
  let world := (pr.queryContext es res over).store
  let cited := citedNames res pr.G'
  let mine := if (linkLaws pr.laws).isEmpty then [] else slots world cited
  let mineBy := if (byLaws pr.laws).isEmpty then [] else
    let listed := (linkTargets pr.G').filterMap fun q => (es.find? (·.id == q)).map (·.name)
    slots (listedStore world listed) (pr.linkers bucket)
  ⟨mine, bucket.map (incomingLaw es world pr), mineBy, cited.map (outgoingLaw es res world pr over)⟩

private def checkSlots (pkg : String) (laws : List (String × Obend.Spec.Law.LawExpr)) (rq : Data) :
    Slots → Option LinkRefusal
  | [] => none
  | (c, d) :: rest =>
    match judgeLinksIn (fun _ => d) pkg laws rq [c] with
    | some r => some r
    | none => checkSlots pkg laws rq rest

private theorem checkSlots_eq (world : VaultStore) (pkg : String) (laws) (rq : Data) (cells) :
    checkSlots pkg laws rq (slots world cells) = judgeLinksIn world pkg laws rq cells := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [slots, List.map_cons, checkSlots, judgeLinksIn] at *
    cases world c with
    | none => rfl
    | some d => simp only; cases (linkCall pkg laws d rq).verdict <;> first | exact ih | rfl

private def checkIncoming (pr : Prepared) : Option RemoteLaw → Except String Unit
  | none => .ok ()
  | some (name, laws, d) => do
    if let some r := judgeLinksIn (fun _ => d) name (linkLaws laws) pr.rq [pr.p.name] then
      throw (backlinkRefusalText name pr.p.name laws r pr.facts pr.n ((scalarFields (settled pr.G')).map (·.1)))

private def checkOutgoing (pr : Prepared) : Option RemoteLaw → Except String Unit
  | none => .ok ()
  | some (name, laws, d) => do
    if let some r := judgeLinksIn (fun _ => d) name (byLaws laws) pr.rq [pr.p.name] then
      throw (byRefusalText pr.p.name name laws r pr.facts)

private theorem checkIncoming_eq (es : List Entry) (world : VaultStore) (pr : Prepared) (bucket : List Entry) :
    (do for slot in bucket.map (incomingLaw es world pr) do checkIncoming pr slot) =
      judgeOtherLinks es world pr bucket := by
  simp only [List.forIn_map, judgeOtherLinks]
  congr 2
  funext e acc
  unfold incomingLaw
  split
  · cases lawsFor es e.name e.graph with
    | error _ => rfl
    | ok laws =>
      simp only
      split
      · rfl
      · simp only [checkIncoming, judgeLinksIn]
        split <;> (try simp_all only) <;> rfl
  · rfl

private theorem checkOutgoing_eq (es res : List Entry) (world : VaultStore) (pr : Prepared) (over : Tip)
    (cited : List String) :
    (do for slot in cited.map (outgoingLaw es res world pr over) do checkOutgoing pr slot) =
      judgeOutgoingLinks es res world pr over cited := by
  simp only [List.forIn_map, judgeOutgoingLinks]
  congr 2
  funext x acc
  unfold outgoingLaw
  split
  · cases es.find? (·.name == x) with
    | none => rfl
    | some e =>
      simp only
      cases lawsFor es e.name e.graph with
      | error _ => rfl
      | ok laws =>
        simp only
        split
        · rfl
        · simp only [checkOutgoing, judgeLinksIn]
          split <;> (try simp_all only) <;> rfl
  · rfl

private theorem ownSlots (world : VaultStore) (pkg : String) (laws : List (String × Obend.Spec.Law.LawExpr))
    (rq : Data) (cells : List String) :
    (if laws.isEmpty then none else judgeLinksIn world pkg laws rq cells) =
      checkSlots pkg laws rq (if laws.isEmpty then [] else slots world cells) := by
  split
  · rfl
  · exact (checkSlots_eq ..).symm


/-- Reuse depends on the ordered observations. A change to some other cell in
the overlay, or in either store, cannot change even the refusal text. -/
theorem judgePreparedFrom_frame {es res es' res' : List Entry} {pr : Prepared}
    {over over' : Tip} {bucket bucket' : List Entry}
    (same : observe es res pr over bucket = observe es' res' pr over' bucket') :
    judgePreparedFrom es res pr over bucket = judgePreparedFrom es' res' pr over' bucket' := by
  have hm := congrArg Reads.mine same
  have hi := congrArg Reads.incoming same
  have hb := congrArg Reads.mineBy same
  have ho := congrArg Reads.outgoing same
  simp only [observe] at hm hi hb ho
  unfold judgePreparedFrom
  have outEq := congrArg (fun xs : List (Option RemoteLaw) => (do
    for slot in xs do checkOutgoing pr slot : Except String Unit)) ho
  simp only [checkOutgoing_eq] at outEq
  simp only [← checkIncoming_eq, ownSlots, hm, hi, hb, outEq]

/-- The frame condition against the original scan, for independently resolved old and new tips. -/
theorem judgePrepared_frame {es res es' res' : List Entry} {pr : Prepared} {over over' : Tip}
    (same : observe es res pr over (Index.bucket (entryLinkIndex es) pr.p.id) =
      observe es' res' pr over' (Index.bucket (entryLinkIndex es') pr.p.id)) :
    judgePrepared es res pr over = judgePrepared es' res' pr over' := by
  simpa only [entryLinkIndex_eq_scan, judgePreparedFrom_filter] using judgePreparedFrom_frame same

/-- Only a successful execution supplies this evidence. It is erased by the compiler.
Indexing by the exact Prepared also pins its laws, graphs, actor, request and environment. -/
structure CachedJudgment (pr : Prepared) where
  reads : Reads
  accepted : ∀ es res over bucket, observe es res pr over bucket = reads →
    judgePreparedFrom es res pr over bucket = .ok ()

structure Slot where
  prepared : Prepared
  previous : Option (CachedJudgment prepared) := none

private def checkFresh (es res : List Entry) (over : Tip) (pr : Prepared) (bucket : List Entry) :
    Except String (CachedJudgment pr) :=
  match h : judgePreparedFrom es res pr over bucket with
  | .error msg => .error msg
  | .ok () => .ok ⟨observe es res pr over bucket, fun _ _ _ _ eqReads =>
      (judgePreparedFrom_frame eqReads).trans h⟩

private def validate (es res : List Entry) (over : Tip) (slot : Slot) (bucket : List Entry) :
    Nat × Except String (CachedJudgment slot.prepared) :=
  match slot.previous with
  | some cache =>
    if observe es res slot.prepared over bucket = cache.reads then (0, .ok cache)
    else (1, checkFresh es res over slot.prepared bucket)
  | none => (1, checkFresh es res over slot.prepared bucket)

private theorem validate_eq (es res : List Entry) (over : Tip) (slot : Slot) (bucket : List Entry) :
    ((validate es res over slot bucket).2.map fun _ => ()) =
      judgePreparedFrom es res slot.prepared over bucket := by
  unfold validate
  cases slot.previous with
  | none => simp only [checkFresh]; split <;> rename_i h <;> exact h.symm
  | some cache =>
    dsimp only
    split
    · rename_i eqReads
      exact (cache.accepted _ _ _ _ eqReads).symm
    · simp only [checkFresh]; split <;> rename_i h <;> exact h.symm

/-- Validate one prepared slot against a pre-built reverse-link index, reusing its prior
`CachedJudgment` whenever its observed link reads match and returning the refreshed evidence
when admitted. -/
def validateSlot (es res : List Entry) (over : Tip) (index : Index.Buckets PageId Entry)
    (slot : Slot) : Option (CachedJudgment slot.prepared) :=
  match (validate es res over slot (Index.bucket index slot.prepared.p.id)).2 with
  | .ok cache => some cache
  | .error _ => none

theorem validateSlot_isSome_eq_judgePrepared (es res : List Entry) (over : Tip) (slot : Slot) :
    (validateSlot es res over (entryLinkIndex es) slot).isSome =
      (judgePrepared es res slot.prepared over).toBool := by
  unfold validateSlot
  generalize hv : validate es res over slot (Index.bucket (entryLinkIndex es) slot.prepared.p.id) = v
  obtain ⟨calls, result⟩ := v
  have agree := validate_eq es res over slot (Index.bucket (entryLinkIndex es) slot.prepared.p.id)
  rw [hv, entryLinkIndex_eq_scan, judgePreparedFrom_filter] at agree
  rw [← agree]
  cases result <;> rfl

/-- The call count includes a failing judgment and excludes the unvisited suffix. Successful
batches return their refreshed slots for the next tip. -/
private def walk (es res : List Entry) (over : Tip) (index : Index.Buckets PageId Entry) :
    List Slot → Nat × Except String (List Slot)
  | [] => (0, .ok [])
  | slot :: rest =>
    let (calls, result) := validate es res over slot (Index.bucket index slot.prepared.p.id)
    match result with
    | .error why => (calls, .error ("at " ++ slot.prepared.p.name ++ ": " ++ why))
    | .ok cache =>
      let (later, tailResult) := walk es res over index rest
      (calls + later, tailResult.map (⟨slot.prepared, some cache⟩ :: ·))

def refresh (es res : List Entry) (over : Tip) (slots : List Slot) :=
  walk es res over (entryLinkIndex es) slots

def judgeIncremental (es res : List Entry) (over : Tip) (slots : List Slot) : Except String Unit :=
  (refresh es res over slots).2.map fun _ => ()

theorem judgeIncremental_eq_judgeAll (es res : List Entry) (over : Tip) (slots : List Slot) :
    judgeIncremental es res over slots = judgeAll es res over (slots.map Slot.prepared) := by
  unfold judgeIncremental refresh
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    simp only [List.map_cons, judgeAll, walk]
    generalize hv : validate es res over slot (Index.bucket (entryLinkIndex es) slot.prepared.p.id) = v
    obtain ⟨calls, result⟩ := v
    have agree := validate_eq es res over slot (Index.bucket (entryLinkIndex es) slot.prepared.p.id)
    rw [hv, entryLinkIndex_eq_scan, judgePreparedFrom_filter] at agree
    rw [← agree]
    cases result with
    | error => rfl
    | ok cache =>
      dsimp only
      generalize ht : walk es res over (entryLinkIndex es) rest = t at ih ⊢
      obtain ⟨later, tail⟩ := t
      cases tail <;> exact ih

end Obend.Vault.IncrementalJudge
