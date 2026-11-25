module
public import Obend.Vault.WorldTree.ShardedWorld
import all Obend.Vault.WorldTree.ShardedWorld
import all Obend.Vault.Store
import all Obend.Vault.Page
import all Obend.Doc.Render
import all Obend.Doc.Section
public section

namespace Obend.Vault.ChunkedWorld
open Obend.Codec.Hex (bytesToHex)
set_option autoImplicit false

/-- The manifest's directory of checkpoint shards. An open handle owns no decoded pages. -/
structure DemandWorld where
  metadata : NonStoreMeta
  pages : Nat
  tombs : Nat
  digests : Array (Option String)

def openDemandWorld (manifest : ByteArray) : Option DemandWorld := do
  let (metadata, pages, tombs, ds) ← unframeManifestArray manifest
  guard (ds.length == numBuckets)
  return ⟨metadata, pages, tombs, ds.toArray⟩

def DemandWorld.manifest (w : DemandWorld) : ByteArray :=
  frameManifestArray (w.metadata, w.pages, w.tombs, w.digests.toList)

def DemandWorld.load {m : Type → Type} [Monad m] (w : DemandWorld) (read : String → m (Option ByteArray))
    (b : Nat) : m (Option ShardPayload) := do
  match w.digests[b]? with
  | none => return none
  | some none => return some ([], [])
  | some (some d) =>
    let some bytes ← read (shardKey b d) | return none
    if bytesToHex (logHashArray bytes) != d then return none
    return decodeShardPayloadArray bytes

/-- Outer none denotes failed authentication, inner none an absent title. -/
def DemandWorld.getPage {m : Type → Type} [Monad m] (w : DemandWorld) (read : String → m (Option ByteArray))
    (name : String) : m (Option (Option Page)) := do
  let pay ← w.load read (bucketOf name)
  return pay.map fun (ps, _) => (ps.find? (fun (_, p) => p.name == name)).map Prod.snd

def fullDirectory (w : World) : DemandWorld :=
  ⟨metaOf w, w.store.pages.length, w.store.tombs.length,
    (Array.range numBuckets).map fun b => (shardForBucket w b).map Prod.fst⟩

def fullPayload (w : World) (b : Nat) : ShardPayload :=
  (bucketItems b (enumList w.store.pages), bucketItems b (enumList w.store.tombs))

private theorem load_full (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (b : Nat) (hb : b < numBuckets) :
    (fullDirectory w).load (m := Id) read b = some (fullPayload w b) := by
  have hg : (fullDirectory w).digests[b]? = some ((shardForBucket w b).map Prod.fst) := by
    simp [fullDirectory, hb]
  unfold DemandWorld.load
  rw [hg]
  let pay := fullPayload w b
  by_cases he : isEmptyShard pay = true
  · have hf : shardForBucket w b = none := by change shardSpecOf pay = none; simp [shardSpecOf, he]
    rw [hf]
    exact congrArg some ((isEmptyShard_iff pay).mp he).symm
  · let bytes := encodeShardPayload pay
    have hf : shardForBucket w b = some (bytesToHex (logHash bytes), bytes) := by
      change shardSpecOf pay = _
      simp [shardSpecOf, he, bytes]
    rw [hf]
    simp [hs _ _ _ hb hf, logHashArray_eq, decodeShardPayloadArray_eq, bytes,
      decodeShardPayload_encodeShardPayload, pay, Bind.bind]
    rfl

private theorem directory_manifest (w : World) :
    (fullDirectory w).manifest.data.toList = manifestBytes w := by
  simp [DemandWorld.manifest, fullDirectory, frameManifestArray_eq, manifestBytes, List.map_map,
    Function.comp_def, Array.toList_range]

private theorem unframe_array_frame (c : ManifestCore) :
    unframeManifestArray (frameManifestArray c) = some c := by
  let bs := frameManifestArray c
  let p := manifestPrefixArray
  have hdata : bs.data.toList = p.data.toList ++ cManifestCore.enc c := frameManifestArray_eq _
  have hsize : p.size ≤ bs.size := by
    have h := congrArg List.length hdata
    simp only [List.length_append, Array.length_toList, ByteArray.size_data] at h
    omega
  have hs : sliceEq bs 0 p = true := by
    unfold sliceEq
    have bound : 0 + p.size ≤ bs.size := by simpa using hsize
    rw [sliceEqGo_eq bs 0 p bound 0, decide_eq_true bound]
    simp only [Nat.add_zero, List.drop_zero, Nat.sub_zero, Bool.true_and]
    change (bs.data.toList.take p.data.toList.length == p.data.toList) = true
    rw [hdata, take_append_exact, beq_self_eq_true]
  have hd : (bs.extract p.size bs.size).data.toList = cManifestCore.enc c := by
    rw [ByteArray.data_extract]
    change (bs.data.extract p.data.toList.length bs.data.toList.length).toList = _
    rw [Array.toList_extract, hdata]
    simp [List.extract]
  change (if decide (p.size ≤ bs.size) && sliceEq bs 0 p then _ else _) = _
  simp only [hs, decide_eq_true hsize, Bool.and_self, ↓reduceIte]
  change cManifestCore.decodeExactArray (bs.extract p.size bs.size) = _
  rw [FastCodec.decodeExactArray_eq, hd, FastCodec.decodeExact_enc]

private theorem open_fullDirectory (w : World) :
    openDemandWorld (fullDirectory w).manifest = some (fullDirectory w) := by
  simp [openDemandWorld, DemandWorld.manifest, unframe_array_frame, fullDirectory, guard]
  apply Array.toList_inj.mp; simp

theorem openDemandWorld_getPage_eq_openFullWorld (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (name : String) :
    ((openDemandWorld (encodeWorldIncremental w none).1).bind
      (fun d => d.getPage (m := Id) read name)) = some (w.store.page? name) := by
  have he : (encodeWorldIncremental w none).1 = (fullDirectory w).manifest := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [encodeWorldIncremental_manifest_eq, directory_manifest]
  rw [he, open_fullDirectory]
  simp only [Option.bind_some, DemandWorld.getPage, load_full w read hs _ (bucketOf_lt name)]
  exact congrArg some (find_bucketItems_enumGo name 0 w.store.pages)

/-- One admitted Store.setPage replacement, using its pre-edit bucket payload. The caller persists
the returned content-addressed shard before publishing the returned manifest. -/
def applyEditDemand (d : DemandWorld) (p : Page) (old : ShardPayload) : DemandWorld × CachedBucket :=
  let pages := old.1.map fun (i, q) => (i, if q.name == p.name then p else q)
  let cb := buildCachedBucket (pages, old.2) none
  let dir := { d with
    metadata := { d.metadata with turn := d.metadata.turn + 1 }
    digests := d.digests.setIfInBounds (bucketOf p.name) (cb.entry?.map Prod.fst) }
  (dir, cb)

/-- Authenticated point replacement. Corrupt or absent shard data cannot enter the update. -/
def DemandWorld.edit {m : Type → Type} [Monad m] (d : DemandWorld) (read : String → m (Option ByteArray))
    (p : Page) : m (Option (DemandWorld × CachedBucket)) := do
  let old ← d.load read (bucketOf p.name)
  return old.map (applyEditDemand d p)

private theorem edit_partition (p : Page) (b k : Nat) (ps : List Page) :
    bucketItems b (enumGo k (ps.map (fun q => if q.name == p.name then p else q))) =
    if b = bucketOf p.name then
      (bucketItems b (enumGo k ps)).map (fun (i,q) => (i, if q.name == p.name then p else q))
    else bucketItems b (enumGo k ps) := by
  induction ps generalizing k with
  | nil => simp [enumGo, bucketItems]
  | cons q qs ih =>
    simp only [List.map_cons, enumGo, bucketItems, List.filter_cons] at ih ⊢
    specialize ih (k + 1)
    by_cases hn : q.name = p.name <;> by_cases hb : b = bucketOf p.name <;>
      by_cases hq : bucketOf q.name = b <;> simp_all

theorem applyEditDemand_root_eq_full (w : World) (p : Page) :
    let d := fullDirectory w
    ((applyEditDemand d p (fullPayload w (bucketOf p.name))).1.manifest).data.toList =
      manifestBytes { w with store := w.store.setPage p } := by
  intro d
  rw [← directory_manifest]
  apply congrArg (fun dir : DemandWorld => dir.manifest.data.toList)
  let after := { w with store := w.store.setPage p }
  let old := fullPayload w (bucketOf p.name)
  let pay : ShardPayload := (old.1.map (fun (i,q) => (i, if q.name == p.name then p else q)), old.2)
  have hdigest : (buildCachedBucket pay none).entry?.map Prod.fst = (shardSpecOf pay).map Prod.fst := by
    have h := congrArg (Option.map Prod.fst) (buildCachedBucket pay none).entry_eq
    simpa [Option.map_map, Function.comp_def, buildCachedBucket_payload] using h
  have hdirs : (applyEditDemand d p old).1.digests = (fullDirectory after).digests := by
    apply Array.ext (by simp [applyEditDemand, d, fullDirectory, after])
    intro b hb1 hb2
    have hb : b < numBuckets := by simpa [fullDirectory] using hb2
    have hsize : b < d.digests.size := by simpa [d, fullDirectory] using hb
    change (d.digests.setIfInBounds (bucketOf p.name) _)[b] = _
    refine (Array.getElem_setIfInBounds (xs := d.digests) (i := bucketOf p.name)
      (a := (buildCachedBucket pay none).entry?.map Prod.fst) hsize).trans ?_
    simp only [d, fullDirectory, Array.getElem_map, Array.getElem_range, after, Store.setPage,
      shardForBucket, enumList, edit_partition]
    by_cases h : b = bucketOf p.name
    · subst b; simpa [pay, old, fullPayload, enumList] using hdigest
    · simp [h, Ne.symm h]
  have extDir {a b : DemandWorld} (hm : a.metadata = b.metadata) (hp : a.pages = b.pages)
      (ht : a.tombs = b.tombs) (hd : a.digests = b.digests) : a = b := by
    cases a; cases b; simp_all
  apply extDir (a := (applyEditDemand d p old).1) (b := fullDirectory after)
  · rfl
  · simp [applyEditDemand, d, fullDirectory, after, Store.setPage]
  · rfl
  · exact hdirs

/-- The authenticated read-modify-write endpoint realizes the full store's next manifest. -/
theorem edit_manifest_eq_full (w : World) (read : String → Option ByteArray)
    (hs : ∀ b d bytes, b < numBuckets → shardForBucket w b = some (d, bytes) →
      read (shardKey b d) = some ⟨bytes.toArray⟩) (p : Page) :
    ((fullDirectory w).edit (m := Id) read p).map (fun r => r.1.manifest.data.toList) =
      some (manifestBytes { w with store := w.store.setPage p }) := by
  simp only [DemandWorld.edit, load_full w read hs _ (bucketOf_lt p.name)]
  exact congrArg some (applyEditDemand_root_eq_full w p)

/-! ### Batch Cone Updates & Demand-Open Soundness -/

/-- Replace each page whose name appears in `updates` with its updated record, preserving order. -/
def applyPageUpdates (ps : List Page) (updates : List Page) : List Page :=
  ps.map fun q => match updates.find? (·.name == q.name) with
    | some u => u
    | none => q

/-- Full-world specification for applying a batch of page updates and advancing `turn`. -/
def applyWorldUpdates (w : World) (updates : List Page) (turnDelta : Nat) : World :=
  { w with store := { w.store with
      pages := applyPageUpdates w.store.pages updates
      turn := w.store.turn + turnDelta } }

/-- Update one shard bucket payload with all matching page replacements from `updates`. -/
def applyBucketUpdates (updates : List Page) (old : ShardPayload) : CachedBucket :=
  let pages := old.1.map fun (i, q) =>
    (i, match updates.find? (·.name == q.name) with | some u => u | none => q)
  buildCachedBucket (pages, old.2) none

def applyEditsDemandGo (updates : List Page) (oldBucket : Nat → Option ShardPayload) :
    List Nat → Array (Option String) → Option (Array (Option String) × List (Nat × CachedBucket))
  | [], digests => some (digests, [])
  | b :: bs, digests => do
    let old ← oldBucket b
    let cb := applyBucketUpdates updates old
    let (digests', rest) ← applyEditsDemandGo updates oldBucket bs
      (digests.setIfInBounds b (cb.entry?.map Prod.fst))
    return (digests', (b, cb) :: rest)

/-- Apply a batch of page updates over ONLY the touched buckets, returning the next `DemandWorld`
and updated `CachedBucket`s for the touched buckets. -/
def applyEditsDemand (d : DemandWorld) (updates : List Page) (turnDelta : Nat)
    (oldBucket : Nat → Option ShardPayload) : Option (DemandWorld × List (Nat × CachedBucket)) := do
  let touched := (updates.map fun p => bucketOf p.name).eraseDups
  let (digests', built) ← applyEditsDemandGo updates oldBucket touched d.digests
  return ({ d with
    metadata := { d.metadata with turn := d.metadata.turn + turnDelta }
    digests := digests' }, built)

private theorem find?_name_eq {updates : List Page} {q u : Page}
    (h : updates.find? (fun x : Page => x.name == q.name) = some u) : u.name = q.name := by
  simpa using List.find?_some h

private theorem bucket_of_update (updates : List Page) (q : Page) :
    bucketOf (match updates.find? (fun x : Page => x.name == q.name) with | some u => u | none => q).name =
      bucketOf q.name := by
  cases h : updates.find? (fun x : Page => x.name == q.name) with
  | none => rfl
  | some u => simp [find?_name_eq h]

private theorem updates_partition (updates : List Page) (b k : Nat) (ps : List Page) :
    bucketItems b (enumGo k (applyPageUpdates ps updates)) =
    (bucketItems b (enumGo k ps)).map fun (i, q) =>
      (i, match updates.find? (·.name == q.name) with | some u => u | none => q) := by
  induction ps generalizing k with
  | nil => simp [applyPageUpdates, enumGo, bucketItems]
  | cons q qs ih =>
    simp only [applyPageUpdates, List.map_cons, enumGo, bucketItems, List.filter_cons] at ih ⊢
    rw [bucket_of_update]
    by_cases hq : bucketOf q.name = b <;> simp [hq, ih (k + 1)]

private theorem updates_untouched (updates : List Page) (b : Nat)
    (hNot : b ∉ (updates.map fun p => bucketOf p.name).eraseDups) (xs : List (Nat × Page))
    (hB : ∀ x ∈ xs, bucketOf x.2.name = b) :
    xs.map (fun (i, q) => (i, match updates.find? (·.name == q.name) with | some u => u | none => q)) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hxb : bucketOf x.2.name = b := hB x List.mem_cons_self
    have hNone : updates.find? (·.name == x.2.name) = none := by
      rw [List.find?_eq_none]
      intro u hu heq
      have hun : u.name = x.2.name := beq_iff_eq.mp heq
      apply hNot
      rw [List.mem_eraseDups, List.mem_map]
      exact ⟨u, hu, by rw [hun, hxb]⟩
    simp only [List.map_cons, hNone, ih (fun y hy => hB y (List.mem_cons_of_mem _ hy))]

private theorem applyEditsDemandGo_spec (w : World) (updates : List Page)
    (oldBucket : Nat → Option ShardPayload) :
    ∀ (bs : List Nat) (digests : Array (Option String)),
      bs.Nodup →
      (∀ b ∈ bs, b < numBuckets ∧ oldBucket b = some (fullPayload w b)) →
      (hsz : digests.size = numBuckets) →
      ∃ (digests' : Array (Option String)) (built : List (Nat × CachedBucket)) (hsz' : digests'.size = numBuckets),
        applyEditsDemandGo updates oldBucket bs digests = some (digests', built) ∧
        ∀ (i : Nat) (hi : i < numBuckets),
          digests'[i]'(by omega) =
            if i ∈ bs then (applyBucketUpdates updates (fullPayload w i)).entry?.map Prod.fst
            else digests[i]'(by omega)
  | [], digests, _, _, hsz =>
    ⟨digests, [], hsz, rfl, fun i hi => by simp⟩
  | b :: bs, digests, hnd, hOld, hsz => by
    obtain ⟨hbNotIn, hndRest⟩ := List.nodup_cons.mp hnd
    obtain ⟨hbLt, hbOld⟩ := hOld b List.mem_cons_self
    let cb := applyBucketUpdates updates (fullPayload w b)
    let d1 := digests.setIfInBounds b (cb.entry?.map Prod.fst)
    have hsz1 : d1.size = numBuckets := by simp [d1, hsz]
    obtain ⟨digests', rest, hsz', hgo, hget⟩ := applyEditsDemandGo_spec w updates oldBucket bs d1 hndRest
      (fun x hx => hOld x (List.mem_cons_of_mem _ hx)) hsz1
    refine ⟨digests', (b, cb) :: rest, hsz', ?_, fun i hi => ?_⟩
    · simp only [applyEditsDemandGo, hbOld, bind, Option.bind, pure]
      change (applyEditsDemandGo updates oldBucket bs d1).bind _ = _
      rw [hgo]; rfl
    · rw [hget i hi]
      by_cases hibs : i ∈ bs
      · have hne : i ≠ b := fun he => hbNotIn (he ▸ hibs)
        simp [hibs, hne]
      · by_cases hib : i = b
        · subst hib
          have hltD : i < digests.size := by omega
          simp only [hibs, ↓reduceIte, List.mem_cons, true_or, d1]
          rw [Array.getElem_setIfInBounds hltD]
          simp [cb]
        · have hltD : i < digests.size := by omega
          simp only [hibs, hib, List.mem_cons, or_self, ↓reduceIte, d1]
          rw [Array.getElem_setIfInBounds hltD]
          simp [Ne.symm hib]

/-- Demand-updating ONLY the buckets touched by `updates` produces the exact same `DemandWorld`
and canonical manifest bytes as applying `updates` to the full world. -/
theorem applyEditsDemand_manifest_eq_full (w : World) (updates : List Page) (turnDelta : Nat)
    (oldBucket : Nat → Option ShardPayload)
    (hOld : ∀ b ∈ (updates.map fun p => bucketOf p.name).eraseDups, oldBucket b = some (fullPayload w b)) :
    ∃ built,
      applyEditsDemand (fullDirectory w) updates turnDelta oldBucket =
        some (fullDirectory (applyWorldUpdates w updates turnDelta), built) ∧
      ((applyEditsDemand (fullDirectory w) updates turnDelta oldBucket).map
        (fun r => r.1.manifest.data.toList)) =
        some (manifestBytes (applyWorldUpdates w updates turnDelta)) := by
  let touched := (updates.map fun p => bucketOf p.name).eraseDups
  have hnd : touched.Nodup := Index.eraseDups_nodup _
  have hBnd : ∀ b ∈ touched, b < numBuckets ∧ oldBucket b = some (fullPayload w b) := by
    intro b hb
    refine ⟨?_, hOld b hb⟩
    have hm := List.mem_eraseDups.mp hb
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hm
    exact bucketOf_lt p.name
  have hsz : (fullDirectory w).digests.size = numBuckets := by simp [fullDirectory]
  obtain ⟨digests', built, hsz', hgo, hget⟩ := applyEditsDemandGo_spec w updates oldBucket touched
    (fullDirectory w).digests hnd hBnd hsz
  let after := applyWorldUpdates w updates turnDelta
  have hdigs : digests' = (fullDirectory after).digests := by
    apply Array.ext (by simp [fullDirectory, hsz'])
    intro i hi1 hi2
    have hi : i < numBuckets := by simpa [fullDirectory] using hi2
    rw [hget i hi]
    simp only [fullDirectory, Array.getElem_map, Array.getElem_range]
    by_cases hit : i ∈ touched
    · simp only [hit, ↓reduceIte, applyBucketUpdates]
      have hpart : fullPayload after i =
          ((fullPayload w i).1.map fun (idx, q) =>
            (idx, match updates.find? (·.name == q.name) with | some u => u | none => q),
           (fullPayload w i).2) := by
        simp only [fullPayload, after, applyWorldUpdates, enumList, updates_partition]
      have hcb := congrArg (Option.map Prod.fst) (buildCachedBucket (fullPayload after i) none).entry_eq
      rw [hpart] at hcb
      simpa [Option.map_map, Function.comp_def, buildCachedBucket_payload, shardForBucket,
        fullPayload, enumList, after, applyWorldUpdates, updates_partition] using hcb
    · simp only [hit, ↓reduceIte, shardForBucket, enumList, after, applyWorldUpdates, updates_partition]
      have hB : ∀ x ∈ bucketItems i (enumGo 0 w.store.pages), bucketOf x.2.name = i := by
        intro x hx
        exact beq_iff_eq.mp (List.mem_filter.mp hx).2
      rw [updates_untouched updates i hit _ hB]
  have hdir : ({ fullDirectory w with
      metadata := { (fullDirectory w).metadata with turn := (fullDirectory w).metadata.turn + turnDelta }
      digests := digests' } : DemandWorld) = fullDirectory after := by
    have extDir {a b : DemandWorld} (hm : a.metadata = b.metadata) (hp : a.pages = b.pages)
        (ht : a.tombs = b.tombs) (hd : a.digests = b.digests) : a = b := by
      cases a; cases b; simp_all
    apply extDir
    · rfl
    · simp [fullDirectory, after, applyWorldUpdates, applyPageUpdates]
    · rfl
    · exact hdigs
  have hRes : applyEditsDemand (fullDirectory w) updates turnDelta oldBucket =
      some (fullDirectory after, built) := by
    unfold applyEditsDemand
    dsimp only
    change (applyEditsDemandGo updates oldBucket touched (fullDirectory w).digests).bind _ = _
    rw [hgo]
    simp [hdir]
  refine ⟨built, hRes, ?_⟩
  rw [hRes]
  exact congrArg some (directory_manifest after)

/-- Local cleanliness check for a single atom: only identity cites, no raw wikilink text,
and no dangling-link candidates. -/
def atomLocallyClean : Obend.Doc.Content → Bool
  | .cite _ c => c.span == .identity
  | .text t => !((t.startsWith "[[" || t.startsWith "![[") && t.endsWith "]]") && !danglingCandidate (.text t)
  | _ => true

/-- A page is locally clean when it has no refusal note, has a current version whose `seen`
already matches its plain source rendering, has no open sections, and every atom is locally clean. -/
def pageLocallyClean (p : Page) : Bool :=
  match p.note, p.current with
  | none, some G =>
    p.seen == some (render G p.name p.who) &&
    (sections G).isEmpty &&
    G.atoms.all fun (_, c) => atomLocallyClean c
  | _, _ => false

theorem holds_cite_of_world_eq (H : Obend.Digest.HashBytes.Hash) {W₁ W₂ : Obend.Doc.World}
    {c : Obend.Doc.Cite} (hW : W₁ c.page = W₂ c.page) :
    ∀ f ∈ Obend.Doc.citeFacts c, Obend.Doc.holds H W₁ f = Obend.Doc.holds H W₂ f := by
  intro f hf
  unfold Obend.Doc.citeFacts at hf
  cases hs : c.span <;> cases hm : c.mode <;> simp only [hs, hm, List.mem_cons, List.not_mem_nil, or_false] at hf
  all_goals
    rcases hf with rfl | rfl <;>
      simp [Obend.Doc.holds, Obend.Doc.quoted, Obend.Doc.latestQuote, Obend.Doc.World.current, hW]

theorem viewAtom_congr_of_cites (H : Obend.Digest.HashBytes.Hash) {W₁ W₂ : Obend.Doc.World}
    {G : Obend.Doc.Graph} (hW : ∀ id, citesPage G id = true → W₁ id = W₂ id) :
    Obend.Doc.viewAtom H W₁ G = Obend.Doc.viewAtom H W₂ G := by
  funext a
  unfold Obend.Doc.viewAtom
  cases hl : G.label a with
  | none => rfl
  | some content =>
    cases content with
    | text _ | field _ _ | cell _ _ _ _ _ => rfl
    | cite n c =>
      have hmem : (a, Obend.Doc.Content.cite n c) ∈ G.atoms := lookup_atoms_mem hl
      have hc : citesPage G c.page = true := List.any_eq_true.mpr ⟨(a, .cite n c), hmem, by simp⟩
      have hFilt : ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H W₁ f) =
          ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H W₂ f) := by
        apply List.filter_congr
        intro f hf
        rw [holds_cite_of_world_eq H (hW c.page hc) f hf]
      simp only [hFilt]

/-- Frame invariance for `remarkInWorld`: a page whose cited target histories agree in `W₁` and
`W₂` produces the exact same remarked page. -/
theorem remarkInWorld_frame_of_not_cites (H : Obend.Digest.HashBytes.Hash)
    {W₁ W₂ : Obend.Doc.World} (p : Page)
    (hW : ∀ G, p.current = some G → ∀ id, citesPage G id = true → W₁ id = W₂ id) :
    remarkInWorld H W₁ p = remarkInWorld H W₂ p := by
  unfold remarkInWorld
  by_cases hn : p.note.isSome = true
  · simp [hn]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    cases hc : p.current with
    | none => rfl
    | some G =>
      simp only [Option.map_some, viewAtom_congr_of_cites H (hW G hc)]

/-- Frame invariance for `remarkPage` across two stores agreeing on all targets cited by `p`. -/
theorem remarkPage_frame_of_not_cites (H : Obend.Digest.HashBytes.Hash) {s₁ s₂ : Store} (p : Page)
    (hW : ∀ G, p.current = some G → ∀ id, citesPage G id = true → s₁.world id = s₂.world id) :
    remarkPage H s₁ p = remarkPage H s₂ p := by
  rw [← remarkInWorld_store H s₁ p, ← remarkInWorld_store H s₂ p]
  exact remarkInWorld_frame_of_not_cites H p hW

/-- Frame invariance for `citeReport` across two stores agreeing on all targets cited by `p`. -/
theorem citeReport_frame_of_not_cites (H : Obend.Digest.HashBytes.Hash) {s₁ s₂ : Store} (p : Page)
    (hW : ∀ G, p.current = some G → ∀ id, citesPage G id = true →
      s₁.world id = s₂.world id ∧
      (s₁.pages.find? (·.id == id)).map Page.name = (s₂.pages.find? (·.id == id)).map Page.name) :
    citeReport H s₁ p = citeReport H s₂ p := by
  unfold citeReport
  cases hc : p.current with
  | none => rfl
  | some G =>
    dsimp only
    apply Obend.Doc.filterMap_congr'
    intro pc _
    cases pc with
    | mark _ _ => rfl
    | atom a txt =>
      dsimp only
      cases hl : G.label a with
      | none => rfl
      | some content =>
        cases content with
        | text _ | field _ _ | cell _ _ _ _ _ => rfl
        | cite n c =>
          dsimp only
          have hmem : (a, Obend.Doc.Content.cite n c) ∈ G.atoms := lookup_atoms_mem hl
          have hcp : citesPage G c.page = true := List.any_eq_true.mpr ⟨(a, .cite n c), hmem, by simp⟩
          obtain ⟨hWorld, hName⟩ := hW G hc c.page hcp
          have hName' : (Option.map (fun x => x.name) (s₁.pages.find? (·.id == c.page))) =
              (Option.map (fun x => x.name) (s₂.pages.find? (·.id == c.page))) := hName
          have hFilt : ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H s₁.world f) =
              ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H s₂.world f) := by
            apply List.filter_congr
            intro f hf
            rw [holds_cite_of_world_eq H hWorld f hf]
          have hWords : ∀ f ∈ ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H s₂.world f),
              factWords s₁ (((s₂.pages.find? (·.id == c.page)).map (·.name)).getD n) f =
              factWords s₂ (((s₂.pages.find? (·.id == c.page)).map (·.name)).getD n) f := by
            intro f hf
            have hmf := (List.mem_filter.mp hf).1
            unfold Obend.Doc.citeFacts at hmf
            cases hs : c.span <;> cases hm : c.mode <;>
              simp only [hs, hm, List.mem_cons, List.not_mem_nil, or_false] at hmf
            all_goals
              rcases hmf with rfl | rfl <;> simp [factWords, hWorld]
          rw [hName', hFilt]
          congr 1; congr 1; congr 1
          by_cases he : ((Obend.Doc.citeFacts c).filter fun f => !Obend.Doc.holds H s₂.world f).isEmpty = true
          · simp [he]
          · simp only [he, Bool.false_eq_true, ↓reduceIte]
            congr 1; exact List.map_congr_left hWords

/-- A locally clean page whose cited page IDs are all present in `s.world` is already fixed by
`fixDangling` and `remarkPage`, has zero failing cites in `citeReport`, and has zero open sections. -/
theorem pageLocallyClean_settled_and_clean (H : Obend.Digest.HashBytes.Hash) (s : Store) (p : Page)
    (hClean : pageLocallyClean p = true)
    (hPres : ∀ G, p.current = some G → ∀ id, citesPage G id = true → (s.world id).isEmpty = false) :
    fixDangling H s p = p ∧
    remarkPage H s p = p ∧
    ((citeReport H s p).filterMap fun (c, ok, why) =>
      if ok then none else some (p.name ++ ": " ++ c ++ " is " ++ why)) = [] ∧
    sectionReport p = [] := by
  unfold pageLocallyClean at hClean
  cases hnote : p.note with
  | some _ => simp [hnote] at hClean
  | none =>
    cases hcur : p.current with
    | none => simp [hnote, hcur] at hClean
    | some G =>
      simp only [hnote, hcur, Bool.and_eq_true, beq_iff_eq] at hClean
      obtain ⟨⟨hseen, hsec⟩, hatoms⟩ := hClean
      have hAtom : ∀ x ∈ G.atoms, atomLocallyClean x.2 = true := List.all_eq_true.mp hatoms
      have hFix : fixDangling H s p = p := by
        unfold fixDangling
        simp only [hnote, hcur, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        have hinert : ∀ a, (G.label a).bind (danglingOf H s.entries) = none := by
          intro a
          cases hl : G.label a with
          | none => rfl
          | some c =>
            simp only [Option.bind_some]
            apply danglingOf_none_of_not_candidate
            have ha := hAtom (a, c) (lookup_atoms_mem hl)
            cases c with
            | text t => simp only [atomLocallyClean, Bool.and_eq_true, Bool.not_eq_true'] at ha; exact ha.2
            | cite _ _ | field _ _ | cell _ _ _ _ _ => rfl
        rw [replaceAll_inert H G _ _ _ hinert]
        rfl
      have hView : Obend.Doc.viewAtom H s.world G = G.atomText := by
        funext a
        unfold Obend.Doc.viewAtom
        cases hl : G.label a with
        | none => rfl
        | some c =>
          cases c with
          | text _ | field _ _ | cell _ _ _ _ _ => rfl
          | cite n ct =>
            have hmem : (a, Obend.Doc.Content.cite n ct) ∈ G.atoms := lookup_atoms_mem hl
            have ha := hAtom (a, .cite n ct) hmem
            have hsp : ct.span = .identity := beq_iff_eq.mp ha
            have hcp : citesPage G ct.page = true := List.any_eq_true.mpr ⟨(a, .cite n ct), hmem, by simp⟩
            have hpr := hPres G hcur ct.page hcp
            have hnil : ((Obend.Doc.citeFacts ct).filter fun f => !Obend.Doc.holds H s.world f) = [] := by
              simp [Obend.Doc.citeFacts, hsp, Obend.Doc.holds, hpr]
            simp only [hnil]
      have hRemark : remarkPage H s p = p := by
        unfold remarkPage Page.view
        simp only [hnote, hcur, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          Option.map_some, hView]
        have hrend : renderWith G.atomText G p.name p.who = render G p.name p.who := rfl
        rw [hrend, ← hseen]
        cases p with
        | mk nm pid hist sn auth nt kd =>
          simp only at hnote; subst hnote; rfl
      have hQuick : allCitesOkQuick H (indexedWorld (Index.ofList Page.id s.pages)) G = true := by
        rw [indexedWorld_pages]
        unfold allCitesOkQuick
        rw [List.all_eq_true]
        intro ⟨a, c⟩ hmem
        have ha := hAtom (a, c) hmem
        cases c with
        | text t =>
          simp only [atomLocallyClean, Bool.and_eq_true] at ha
          exact ha.1
        | cite n ct =>
          have hsp : ct.span = .identity := beq_iff_eq.mp ha
          have hcp : citesPage G ct.page = true := List.any_eq_true.mpr ⟨(a, .cite n ct), hmem, by simp⟩
          have hpr := hPres G hcur ct.page hcp
          simp [Obend.Doc.citeFacts, hsp, Obend.Doc.holds, hpr]
        | field _ _ | cell _ _ _ _ _ => rfl
      have hCite : ((citeReport H s p).filterMap fun (c, ok, why) =>
          if ok then none else some (p.name ++ ": " ++ c ++ " is " ++ why)) = [] := by
        rw [← citeReportIndexed_eq H s p]
        exact citeReportIndexed_no_failures_of_quick H (Index.ofList Page.id s.pages) p G hcur hQuick
      have hSec : sectionReport p = [] := by
        unfold sectionReport
        rw [hcur]
        have hnil : sections G = [] := List.isEmpty_iff.mp hsec
        simp [hnil]
      exact ⟨hFix, hRemark, hCite, hSec⟩

/-- When every page's file on disk matches its recorded `seen` text and every file belongs to a
recorded page, both `forgetMissing` and `openVault` are exact no-ops. -/
theorem reopen_unchanged_eq_full (H : Obend.Digest.HashBytes.Hash) (s : Store)
    (V : List (String × String))
    (hAll : ∀ p ∈ s.pages, ∃ md, V.lookup p.name = some md ∧ p.seen = some md)
    (hCov : ∀ e ∈ V, s.pages.any (·.name == e.1) = true) :
    forgetMissing s V = { store := s } ∧ openVault H s V = ⟨s, []⟩ := by
  have hFg : forgetMissing s V = { store := s } := by
    apply forgetMissing_unchanged s V
    · intro p hp
      obtain ⟨md, hmd, _⟩ := hAll p hp
      simp [hmd]
    · exact hCov
  have hQuiet : quiet s V = true := by
    simp only [quiet, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun p hp => ?_, hCov⟩
    obtain ⟨md, hmd, hsn⟩ := hAll p hp
    simp [hmd, hsn]
  exact ⟨hFg, by simp [openVault, hQuiet]⟩

end Obend.Vault.ChunkedWorld
