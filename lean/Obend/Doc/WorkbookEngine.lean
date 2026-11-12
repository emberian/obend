module
/-
# Obend.Doc.WorkbookEngine — Live Multi-Projection Bidirectional Houyhnhnm Workbook
Unifies literate markdown sections & transclusions (`Doc.Graph`, `Section`, `Render`, `Backlinks`),
typed `.obnb` cells (`Doc.Structured`), topological reactive evaluation & 256-bit receipts
(`Doc.Reactive`), Putnam/Foster bidirectional scrubbable lenses, conflict-preserving pushout branch
merge, and capability-scoped cSHAKE256 Merkle redaction (`Receipt.Merkle`).
-/
public import Obend.Doc.Backlinks
public import Obend.Doc.Structured
public import Obend.Doc.ReactiveNotebook
public import Obend.Receipt.Merkle
public import Obend.Spec.Sha256
import all Obend.Doc.ReactiveNotebook
public section
namespace Obend.Doc.WorkbookEngine
open Obend.Core.Data (Data)
open Obend.Doc
open Obend.Doc.Reactive (CellId SymbolName Environment Opcode Instruction CellBody
  ReactiveCell CellResult CachedCell CellKernel scientificKernel evalCell evalCell_frame
  publish publish_frame publish_same AgreeOutside checkNotebookDag DependencyPath)
open Obend.Core.Digest (digestWith deployed digest_lt)
open Obend.Digest.HashBytes (Hash CollisionAmong)
open Obend.Receipt.Merkle (Bounded deployed_bounded Opening openingPreimages mapRoot mapOpening opens
  opens_complete opens_binds_scoped)
set_option autoImplicit false

/-! ## 1. Literate Prose Sections & Transitive Wikilink / Transclusion Graph -/
structure WorkbookSection where
  sectionKey : String
  markdown : String
  blocks : List (String × Int) := []
  deriving DecidableEq, Repr
@[expose] def ownerSectionKey (citeKey : String) : String :=
  String.ofList (citeKey.toList.takeWhile (· != '#'))
private theorem takeWhile_idem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).takeWhile p = xs.takeWhile p
  | [] => rfl
  | x :: xs => by
    simp only [List.takeWhile]; cases hp : p x
    · simp [List.takeWhile]
    · simp [List.takeWhile, hp, takeWhile_idem p xs]
theorem ownerSectionKey_idem (s : String) :
    ownerSectionKey (ownerSectionKey s) = ownerSectionKey s := by
  unfold ownerSectionKey; simp [String.toList_ofList, takeWhile_idem]
def tokCiteTarget? : Tok → Option String
  | .text _ => none
  | .link raw =>
    let (page, sp) := target false raw
    let pStr := String.ofList page
    if pStr.isEmpty then none else match sp with | .block b => some (pStr ++ "#^" ++ b) | _ => some pStr
  | .embed raw =>
    let (page, sp) := target true raw
    let pStr := String.ofList page
    if pStr.isEmpty then none else match sp with | .block b => some (pStr ++ "#^" ++ b) | _ => some pStr
def extractMarkdownCiteTargets (md : String) : List String :=
  dedupCellKeys ((tokens md).filterMap tokCiteTarget?)
def sha256String256 (s : String) : BitVec 256 :=
  (Obend.Spec.Sha256.digest s.toUTF8).foldl
    (fun acc (w : UInt32) => (acc <<< 32) ||| BitVec.ofNat 256 w.toNat) 0
def sha256Bytes32 (bs : ByteArray) : ByteArray :=
  ByteArray.mk <| (Obend.Spec.Sha256.digest bs).foldl (fun (acc : Array UInt8) (w : UInt32) =>
    acc.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8
       |>.push (w >>> 8).toUInt8 |>.push w.toUInt8) #[]
def markdownFingerprintInt (md : String) : Int :=
  Int.ofNat (((Obend.Spec.Sha256.digest md.toUTF8)[0]?.getD 0).toNat)
def findSection? (secs : List WorkbookSection) (secKey : String) : Option WorkbookSection :=
  secs.find? (fun s => s.sectionKey == secKey)
def citeBlockSuffix? (citeKey : String) : Option String :=
  match citeKey.toList.dropWhile (· != '#') with
  | '#' :: '^' :: rest => some (String.ofList rest)
  | '#' :: rest => some (String.ofList rest)
  | _ => none
def directSectionValue (secs : List WorkbookSection) (citeKey : String) : Int :=
  match findSection? secs (ownerSectionKey citeKey) with
  | none => 0
  | some sec =>
    match citeBlockSuffix? citeKey with
    | some blk => (sec.blocks.lookup blk).getD (markdownFingerprintInt sec.markdown)
    | none => markdownFingerprintInt sec.markdown + sec.blocks.foldl (fun acc kv => acc + kv.2) 0
def directCitedOwners (secs : List WorkbookSection) (secKey : String) : List String :=
  match findSection? secs secKey with
  | none => []
  | some sec => dedupCellKeys ((extractMarkdownCiteTargets sec.markdown).map ownerSectionKey)
def sectionOwnerDeps (secs : List WorkbookSection) : List (String × String) :=
  secs.flatMap fun sec => (directCitedOwners secs sec.sectionKey).map fun cited => (sec.sectionKey, cited)
theorem mem_sectionOwnerDeps {secs : List WorkbookSection} {src dst : String}
    (hFind : ∃ sec ∈ secs, sec.sectionKey = src) (hCited : dst ∈ directCitedOwners secs src) :
    (src, dst) ∈ sectionOwnerDeps secs := by
  obtain ⟨sec, hMem, hKey⟩ := hFind
  unfold sectionOwnerDeps; rw [List.mem_flatMap]
  exact ⟨sec, hMem, by rw [hKey, List.mem_map]; exact ⟨dst, hCited, rfl⟩⟩
def evalCiteKeyFuel : Nat → List WorkbookSection → String → Int
  | 0, secs, citeKey => directSectionValue secs citeKey
  | fuel + 1, secs, citeKey =>
    directSectionValue secs citeKey +
      (directCitedOwners secs (ownerSectionKey citeKey)).foldl
        (fun acc targetOwner => acc + evalCiteKeyFuel fuel secs targetOwner) 0
def updateSectionInList (secs : List WorkbookSection) (targetSecKey newMd : String)
    (newBlocks : List (String × Int)) : List WorkbookSection :=
  secs.map fun s => if s.sectionKey == targetSecKey then { s with markdown := newMd, blocks := newBlocks } else s
theorem findSection_update_other (secs : List WorkbookSection) (targetSecKey newMd k : String)
    (newBlocks : List (String × Int)) (hNe : k ≠ targetSecKey) :
    findSection? (updateSectionInList secs targetSecKey newMd newBlocks) k = findSection? secs k := by
  unfold findSection? updateSectionInList
  induction secs with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons]
    cases hT : s.sectionKey == targetSecKey
    · simp only [Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      cases hk : s.sectionKey == k
      · exact ih
      · rfl
    · have hNeSK : (s.sectionKey == k) = false :=
        beq_eq_false_iff_ne.mpr (fun hk => hNe (hk.symm.trans (beq_iff_eq.mp hT)))
      simp only [↓reduceIte, List.find?_cons, hNeSK]; exact ih
theorem findSection_some_mem {secs : List WorkbookSection} {k : String} {sec : WorkbookSection}
    (h : findSection? secs k = some sec) : sec ∈ secs ∧ sec.sectionKey = k := by
  unfold findSection? at h
  induction secs with
  | nil => cases h
  | cons s rest ih =>
    simp only [List.find?_cons] at h
    cases hk : s.sectionKey == k
    · simp only [hk] at h; exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    · simp only [hk, Option.some.injEq] at h; subst h
      exact ⟨List.mem_cons_self .., beq_iff_eq.mp hk⟩
theorem directSectionValue_update_other (secs : List WorkbookSection) (targetSecKey newMd citeKey : String)
    (newBlocks : List (String × Int)) (hNe : ownerSectionKey citeKey ≠ targetSecKey) :
    directSectionValue (updateSectionInList secs targetSecKey newMd newBlocks) citeKey =
      directSectionValue secs citeKey := by
  simp [directSectionValue, findSection_update_other secs targetSecKey newMd (ownerSectionKey citeKey) newBlocks hNe]
theorem directCitedOwners_update_other (secs : List WorkbookSection) (targetSecKey newMd secKey : String)
    (newBlocks : List (String × Int)) (hNe : secKey ≠ targetSecKey) :
    directCitedOwners (updateSectionInList secs targetSecKey newMd newBlocks) secKey =
      directCitedOwners secs secKey := by
  simp [directCitedOwners, findSection_update_other secs targetSecKey newMd secKey newBlocks hNe]
private theorem foldl_add_congr {α : Type} (f g : α → Int) :
    ∀ (xs : List α) (init : Int), (∀ x ∈ xs, f x = g x) →
      xs.foldl (fun acc x => acc + f x) init = xs.foldl (fun acc x => acc + g x) init
  | [], _, _ => rfl
  | x :: xs, init, h => by
    simp only [List.foldl_cons, h x (List.mem_cons_self ..)]
    exact foldl_add_congr f g xs _ (fun y hy => h y (List.mem_cons_of_mem x hy))
/-- **Multi-Hop Transclusion Frame Lemma**: citations outside `impactedBacklinksFuel` preserve value. -/
theorem evalCiteKeyFuel_frame_outside_impacted :
    ∀ (fuel : Nat) (secs : List WorkbookSection) (targetSecKey newMd citeKey : String)
      (newBlocks : List (String × Int)),
      ownerSectionKey citeKey ∉ impactedBacklinksFuel fuel (sectionOwnerDeps secs) targetSecKey →
      evalCiteKeyFuel fuel (updateSectionInList secs targetSecKey newMd newBlocks) citeKey =
        evalCiteKeyFuel fuel secs citeKey
  | 0, secs, targetSecKey, newMd, citeKey, newBlocks, hOut => by
    simp only [impactedBacklinksFuel, impactedClosureFuel, List.mem_singleton] at hOut
    exact directSectionValue_update_other secs targetSecKey newMd citeKey newBlocks hOut
  | fuel + 1, secs, targetSecKey, newMd, citeKey, newBlocks, hOut => by
    have hNe : ownerSectionKey citeKey ≠ targetSecKey := by
      intro hEq; apply hOut
      exact impactedBacklinksFuel_mono (Nat.zero_le (fuel + 1)) (sectionOwnerDeps secs) targetSecKey _
        (by simp [impactedBacklinksFuel, impactedClosureFuel, hEq])
    simp only [evalCiteKeyFuel,
      directSectionValue_update_other secs targetSecKey newMd citeKey newBlocks hNe,
      directCitedOwners_update_other secs targetSecKey newMd (ownerSectionKey citeKey) newBlocks hNe]
    congr 1
    cases hFind : findSection? secs (ownerSectionKey citeKey) with
    | none => simp [directCitedOwners, hFind]
    | some sec =>
      have ⟨hSecMem, hSecKey⟩ := findSection_some_mem hFind
      have hAllClean : ∀ targetOwner ∈ directCitedOwners secs (ownerSectionKey citeKey),
          evalCiteKeyFuel fuel (updateSectionInList secs targetSecKey newMd newBlocks) targetOwner =
            evalCiteKeyFuel fuel secs targetOwner := by
        intro targetOwner hMemCited
        have hEdge := mem_sectionOwnerDeps ⟨sec, hSecMem, hSecKey⟩ hMemCited
        have hTargetOut : targetOwner ∉ impactedBacklinksFuel fuel (sectionOwnerDeps secs) targetSecKey := by
          intro hTargetIn; apply hOut
          rw [show impactedBacklinksFuel (fuel + 1) (sectionOwnerDeps secs) targetSecKey =
              impactStep (sectionOwnerDeps secs) (impactedBacklinksFuel fuel (sectionOwnerDeps secs) targetSecKey)
              from impactedClosureFuel_succ_right fuel (sectionOwnerDeps secs) [targetSecKey]]
          exact step_contains_directCiteDependent hEdge hTargetIn
        have hIdemOwner : ownerSectionKey targetOwner = targetOwner := by
          simp only [directCitedOwners, hFind, mem_dedupCellKeys, List.mem_map] at hMemCited
          obtain ⟨rawCite, _, rfl⟩ := hMemCited; exact ownerSectionKey_idem rawCite
        apply evalCiteKeyFuel_frame_outside_impacted fuel secs targetSecKey newMd targetOwner newBlocks
        rwa [hIdemOwner]
      simp only [directCitedOwners, hFind] at hAllClean ⊢
      exact foldl_add_congr _ _ _ 0 hAllClean

/-! ## 2. Unified `.obnb` + Reactive Workbook Cells & DAG Admission -/
inductive CellVisibility where | publicCell | sealedPrivate (clearanceTag : String) (salt : BitVec 256) deriving DecidableEq, Repr
structure WorkbookCell where
  cellKey : String
  structured : StructuredCell
  reactive : ReactiveCell
  citedKeys : List String := []
  visibility : CellVisibility := .publicCell
  deriving DecidableEq, Repr
structure CachedWorkbookCell where (entry : WorkbookCell) (result : CellResult) deriving DecidableEq, Repr
structure Workbook where (title : String) (sections : List WorkbookSection) (cells : List CachedWorkbookCell) deriving DecidableEq, Repr
@[expose] def allCitedKeys (w : WorkbookCell) : List String :=
  dedupCellKeys (w.citedKeys ++ extractMarkdownCiteTargets w.reactive.note)
@[expose] def citeSymbol (citeKey : String) : SymbolName := "cite::" ++ citeKey
def stripCiteSymbolChars : List Char → Option String
  | 'c' :: 'i' :: 't' :: 'e' :: ':' :: ':' :: rest => some (String.ofList rest)
  | _ => none
theorem stripCiteSymbolChars_citeSymbol (ck : String) :
    stripCiteSymbolChars (citeSymbol ck).toList = some ck := by
  simp [citeSymbol, stripCiteSymbolChars, String.ofList_toList]
theorem eq_citeSymbol_of_stripCiteSymbolChars {s ck : String}
    (h : stripCiteSymbolChars s.toList = some ck) : s = citeSymbol ck := by
  unfold stripCiteSymbolChars at h
  split at h
  · rename_i rest hcs
    simp only [Option.some.injEq] at h; subst h
    have hEqList : s.toList = (citeSymbol (String.ofList rest)).toList := by
      simp [citeSymbol, String.toList_append, String.toList_ofList, hcs]
    simpa [String.ofList_toList] using congrArg String.ofList hEqList
  · cases h
def effectiveReactiveCell (w : WorkbookCell) : ReactiveCell :=
  { w.reactive with
    reads := w.reactive.reads ++ (allCitedKeys w).map citeSymbol
    defs := w.reactive.defs ++ [citeSymbol w.cellKey] }
@[expose] def checkWorkbookDag (cs : List WorkbookCell) : Bool :=
  decide ((cs.map WorkbookCell.cellKey).Nodup) &&
  checkNotebookDag (cs.map effectiveReactiveCell)
theorem checkWorkbookDag_acyclic_sound (cs : List WorkbookCell) (h : checkWorkbookDag cs = true) :
    (cs.map WorkbookCell.cellKey).Nodup ∧
    ((cs.map effectiveReactiveCell).map ReactiveCell.id).Nodup ∧
    ∃ rank : CellId → Nat, ∀ p ∈ cs, ∀ u ∈ cs,
      Obend.Doc.Reactive.dependency (effectiveReactiveCell p) (effectiveReactiveCell u) →
      rank p.reactive.id < rank u.reactive.id := by
  simp only [checkWorkbookDag, Bool.and_eq_true, decide_eq_true_eq] at h
  have ⟨hIds, _, rank, hRank⟩ := Obend.Doc.Reactive.checkNotebookDag_acyclic_sound _ h.2
  refine ⟨h.1, hIds, rank, fun p hp u hu hDep => ?_⟩
  exact hRank (effectiveReactiveCell p) (List.mem_map_of_mem (f := effectiveReactiveCell) hp)
    (effectiveReactiveCell u) (List.mem_map_of_mem (f := effectiveReactiveCell) hu) hDep
theorem checkWorkbookDag_rejects_cycle (cs : List WorkbookCell) {c : ReactiveCell}
    (hCycle : DependencyPath (cs.map effectiveReactiveCell) c c) :
    checkWorkbookDag cs = false := by
  simp [checkWorkbookDag, Obend.Doc.Reactive.cyclic_refused _ hCycle]
theorem checkWorkbookDag_rejects_self_cite (cs : List WorkbookCell) {w : WorkbookCell}
    (hw : w ∈ cs) (hSelf : w.cellKey ∈ allCitedKeys w) :
    checkWorkbookDag cs = false := by
  have hDep : Obend.Doc.Reactive.dependency (effectiveReactiveCell w) (effectiveReactiveCell w) := by
    unfold Obend.Doc.Reactive.dependency
    refine ⟨citeSymbol w.cellKey, by simp [effectiveReactiveCell], ?_⟩
    simp only [effectiveReactiveCell, List.mem_append, List.mem_map]
    exact .inr ⟨w.cellKey, hSelf, rfl⟩
  exact checkWorkbookDag_rejects_cycle cs
    (.edge (List.mem_map_of_mem (f := effectiveReactiveCell) hw)
           (List.mem_map_of_mem (f := effectiveReactiveCell) hw) hDep)

/-! ## 3. Unified Dirty-Cone Incremental Recomputation (`Backlinks ∪ CellDeps`) -/
def sectionEnvironment (secs : List WorkbookSection) (fuel : Nat) : Environment :=
  fun sym => match stripCiteSymbolChars sym.toList with
    | some ck => evalCiteKeyFuel fuel secs ck
    | none => 0
def evalWorkbookCell (k : CellKernel) (w : WorkbookCell) (env : Environment) : CellResult :=
  evalCell k (effectiveReactiveCell w) env
def publishWorkbookCell (w : WorkbookCell) (r : CellResult) (env : Environment) : Environment :=
  publish (effectiveReactiveCell w) r env
def evalWorkbookSchedule (k : CellKernel) : List WorkbookCell → Environment → List CachedWorkbookCell
  | [], _ => []
  | w :: ws, env =>
    let r := evalWorkbookCell k w env
    ⟨w, r⟩ :: evalWorkbookSchedule k ws (publishWorkbookCell w r env)
theorem evalWorkbookSchedule_length (k : CellKernel) (cs : List WorkbookCell) (env : Environment) :
    (evalWorkbookSchedule k cs env).length = cs.length := by
  induction cs generalizing env with
  | nil => rfl
  | cons _ _ ih => simp [evalWorkbookSchedule, ih]
theorem evalWorkbookSchedule_entries (k : CellKernel) (cs : List WorkbookCell) (env : Environment) :
    (evalWorkbookSchedule k cs env).map CachedWorkbookCell.entry = cs := by
  induction cs generalizing env with
  | nil => rfl
  | cons _ _ ih => simp [evalWorkbookSchedule, ih]
@[expose] def evalWorkbookFull (k : CellKernel) (title : String)
    (secs : List WorkbookSection) (cs : List WorkbookCell) : Workbook :=
  { title := title, sections := secs
    cells := evalWorkbookSchedule k cs (sectionEnvironment secs (secs.length + 1)) }
inductive WorkbookEdit where
  | editCellBody (targetId : CellId) (newAst : Data) (newBody : CellBody)
  | editSection (sectionKey : String) (newMarkdown : String) (newBlocks : List (String × Int))
  deriving DecidableEq, Repr
def applyEditToSections (secs : List WorkbookSection) : WorkbookEdit → List WorkbookSection
  | .editCellBody _ _ _ => secs
  | .editSection secKey newMd newBlocks => updateSectionInList secs secKey newMd newBlocks
theorem applyEditToSections_length (secs : List WorkbookSection) (edit : WorkbookEdit) :
    (applyEditToSections secs edit).length = secs.length := by
  cases edit <;> simp [applyEditToSections, updateSectionInList]
def applyEditToCell (edit : WorkbookEdit) (w : WorkbookCell) : WorkbookCell :=
  match edit with
  | .editCellBody tid newAst newBody =>
    if w.reactive.id = tid then
      { w with structured := { w.structured with ast := newAst }
               reactive := { w.reactive with body := newBody } }
    else w
  | .editSection _ _ _ => w
@[simp] theorem applyEditToCell_cellKey (edit : WorkbookEdit) (w : WorkbookCell) :
    (applyEditToCell edit w).cellKey = w.cellKey := by
  cases edit with | editSection _ _ _ => rfl | editCellBody _ _ _ => dsimp only [applyEditToCell]; split <;> rfl
@[simp] theorem applyEditToCell_id (edit : WorkbookEdit) (w : WorkbookCell) :
    (applyEditToCell edit w).reactive.id = w.reactive.id := by
  cases edit with | editSection _ _ _ => rfl | editCellBody _ _ _ => dsimp only [applyEditToCell]; split <;> rfl
@[simp] theorem applyEditToCell_reads (edit : WorkbookEdit) (w : WorkbookCell) :
    (applyEditToCell edit w).reactive.reads = w.reactive.reads := by
  cases edit with | editSection _ _ _ => rfl | editCellBody _ _ _ => dsimp only [applyEditToCell]; split <;> rfl
@[simp] theorem applyEditToCell_defs (edit : WorkbookEdit) (w : WorkbookCell) :
    (applyEditToCell edit w).reactive.defs = w.reactive.defs := by
  cases edit with | editSection _ _ _ => rfl | editCellBody _ _ _ => dsimp only [applyEditToCell]; split <;> rfl
@[simp] theorem applyEditToCell_allCitedKeys (edit : WorkbookEdit) (w : WorkbookCell) :
    allCitedKeys (applyEditToCell edit w) = allCitedKeys w := by
  cases edit with | editSection _ _ _ => rfl | editCellBody _ _ _ => dsimp only [applyEditToCell]; split <;> rfl
@[simp] theorem applyEditToCell_effective_reads (edit : WorkbookEdit) (w : WorkbookCell) :
    (effectiveReactiveCell (applyEditToCell edit w)).reads = (effectiveReactiveCell w).reads := by simp [effectiveReactiveCell]
@[simp] theorem applyEditToCell_effective_defs (edit : WorkbookEdit) (w : WorkbookCell) :
    (effectiveReactiveCell (applyEditToCell edit w)).defs = (effectiveReactiveCell w).defs := by simp [effectiveReactiveCell]
def isWorkbookCellDirty (edit : WorkbookEdit) (impactedOwners : List String)
    (changedSyms : List SymbolName) (w : WorkbookCell) : Bool :=
  let directTarget : Bool := match edit with
    | .editCellBody tid _ _ => decide (w.reactive.id = tid)
    | .editSection _ _ _ => false
  let citeHit : Bool := (allCitedKeys w).any fun ck => decide (ownerSectionKey ck ∈ impactedOwners)
  let symHit : Bool := (effectiveReactiveCell w).reads.any fun s => decide (s ∈ changedSyms)
  directTarget || citeHit || symHit
@[simp] theorem isWorkbookCellDirty_applyEdit (edit : WorkbookEdit) (impactedOwners : List String)
    (changedSyms : List SymbolName) (w : WorkbookCell) :
    isWorkbookCellDirty edit impactedOwners changedSyms (applyEditToCell edit w) =
      isWorkbookCellDirty edit impactedOwners changedSyms w := by
  simp [isWorkbookCellDirty]
def nextWorkbookChanged (edit : WorkbookEdit) (impactedOwners : List String)
    (changedSyms : List SymbolName) (w : WorkbookCell) : List SymbolName :=
  if isWorkbookCellDirty edit impactedOwners changedSyms w then
    (effectiveReactiveCell w).defs ++ changedSyms
  else changedSyms
@[simp] theorem nextWorkbookChanged_applyEdit (edit : WorkbookEdit) (impactedOwners : List String)
    (changedSyms : List SymbolName) (w : WorkbookCell) :
    nextWorkbookChanged edit impactedOwners changedSyms (applyEditToCell edit w) =
      nextWorkbookChanged edit impactedOwners changedSyms w := by
  simp [nextWorkbookChanged]
def editImpactedOwners (secs : List WorkbookSection) : WorkbookEdit → List String
  | .editCellBody _ _ _ => []
  | .editSection secKey _ _ => impactedBacklinksFuel (secs.length + 1) (sectionOwnerDeps secs) secKey
def scanWorkbookDirtyCone (edit : WorkbookEdit) (impactedOwners : List String) :
    List WorkbookCell → List SymbolName → List CellId
  | [], _ => []
  | w :: ws, changedSyms =>
    let rest := scanWorkbookDirtyCone edit impactedOwners ws
      (nextWorkbookChanged edit impactedOwners changedSyms w)
    if isWorkbookCellDirty edit impactedOwners changedSyms w then w.reactive.id :: rest else rest
@[expose] def workbookDirtyCone (wb : Workbook) (edit : WorkbookEdit) : List CellId :=
  scanWorkbookDirtyCone edit (editImpactedOwners wb.sections edit)
    (wb.cells.map CachedWorkbookCell.entry) []
def recomputeWorkbookSchedule (k : CellKernel) (edit : WorkbookEdit) (impactedOwners : List String) :
    List CachedWorkbookCell → Environment → List SymbolName → List CachedWorkbookCell
  | [], _, _ => []
  | old :: cs, env, changedSyms =>
    let w' := applyEditToCell edit old.entry
    let r := if isWorkbookCellDirty edit impactedOwners changedSyms w' then
      evalWorkbookCell k w' env else old.result
    ⟨w', r⟩ :: recomputeWorkbookSchedule k edit impactedOwners cs
      (publishWorkbookCell w' r env) (nextWorkbookChanged edit impactedOwners changedSyms w')
@[expose] def evalWorkbookIncremental (k : CellKernel) (wb : Workbook) (edit : WorkbookEdit) : Workbook :=
  let newSecs := applyEditToSections wb.sections edit
  let seedEnv := sectionEnvironment newSecs (newSecs.length + 1)
  { title := wb.title, sections := newSecs
    cells := recomputeWorkbookSchedule k edit (editImpactedOwners wb.sections edit) wb.cells seedEnv [] }
def WorkbookEnvAgreeOutside (impactedOwners : List String) (changedSyms : List SymbolName)
    (e1 e2 : Environment) : Prop :=
  ∀ s, s ∉ changedSyms → (∀ ck, s = citeSymbol ck → ownerSectionKey ck ∉ impactedOwners) → e1 s = e2 s
theorem sectionEnvironment_agree_after_edit (secs : List WorkbookSection) (edit : WorkbookEdit) :
    let newSecs := applyEditToSections secs edit
    WorkbookEnvAgreeOutside (editImpactedOwners secs edit) []
      (sectionEnvironment secs (secs.length + 1))
      (sectionEnvironment newSecs (newSecs.length + 1)) := by
  intro newSecs s _ hNoImpact
  cases edit with
  | editCellBody _ _ _ => rfl
  | editSection secKey newMd newBlocks =>
    rw [applyEditToSections_length secs (.editSection secKey newMd newBlocks)]
    unfold sectionEnvironment
    cases hStrip : stripCiteSymbolChars s.toList with
    | none => rfl
    | some ck =>
      exact (evalCiteKeyFuel_frame_outside_impacted (secs.length + 1) secs secKey newMd ck newBlocks
        (hNoImpact ck (eq_citeSymbol_of_stripCiteSymbolChars hStrip))).symm
theorem publishWorkbookCell_frame (w1 w2 : WorkbookCell) (r1 r2 : CellResult)
    (e1 e2 : Environment) (impactedOwners : List String) (changedSyms : List SymbolName)
    (hDefs : (effectiveReactiveCell w1).defs = (effectiveReactiveCell w2).defs)
    (hAgree : WorkbookEnvAgreeOutside impactedOwners changedSyms e1 e2) :
    WorkbookEnvAgreeOutside impactedOwners ((effectiveReactiveCell w1).defs ++ changedSyms)
      (publishWorkbookCell w1 r1 e1) (publishWorkbookCell w2 r2 e2) := by
  intro s hsNotMem hNoImpact
  simp only [List.mem_append, not_or] at hsNotMem
  unfold publishWorkbookCell publish
  simp [← hDefs, hsNotMem.1, hAgree s hsNotMem.2 hNoImpact]
theorem publishWorkbookCell_same (w : WorkbookCell) (r : CellResult)
    (e1 e2 : Environment) (impactedOwners : List String) (changedSyms : List SymbolName)
    (hAgree : WorkbookEnvAgreeOutside impactedOwners changedSyms e1 e2) :
    WorkbookEnvAgreeOutside impactedOwners changedSyms
      (publishWorkbookCell w r e1) (publishWorkbookCell w r e2) := by
  intro s hsNotMem hNoImpact; unfold publishWorkbookCell publish
  split
  · rfl
  · exact hAgree s hsNotMem hNoImpact
theorem clean_workbook_cell_support (edit : WorkbookEdit) (impactedOwners : List String)
    (changedSyms : List SymbolName) (w : WorkbookCell)
    (hClean : isWorkbookCellDirty edit impactedOwners changedSyms w = false) :
    applyEditToCell edit w = w ∧
    (∀ ck ∈ allCitedKeys w, ownerSectionKey ck ∉ impactedOwners) ∧
    (∀ s ∈ (effectiveReactiveCell w).reads, s ∉ changedSyms) := by
  simp only [isWorkbookCellDirty, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq] at hClean
  obtain ⟨⟨hDirect, hCite⟩, hSym⟩ := hClean
  refine ⟨?_, hCite, hSym⟩
  cases edit with
  | editSection _ _ _ => rfl
  | editCellBody tid _ _ => simp only [decide_eq_false_iff_not] at hDirect; simp [applyEditToCell, hDirect]
private theorem citeSymbol_inj {a b : String} (h : citeSymbol a = citeSymbol b) : a = b := by
  have h1 := congrArg (fun s => stripCiteSymbolChars s.toList) h
  simpa [stripCiteSymbolChars_citeSymbol] using h1
def WellFormedCellReads (w : WorkbookCell) : Prop :=
  ∀ ck, citeSymbol ck ∈ w.reactive.reads → ck ∈ allCitedKeys w
theorem evalWorkbookCell_clean_agree (k : CellKernel) (w : WorkbookCell) (hWf : WellFormedCellReads w)
    (impactedOwners : List String) (changedSyms : List SymbolName) (oldEnv newEnv : Environment)
    (hAgree : WorkbookEnvAgreeOutside impactedOwners changedSyms oldEnv newEnv)
    (hCiteClean : ∀ ck ∈ allCitedKeys w, ownerSectionKey ck ∉ impactedOwners)
    (hSymClean : ∀ s ∈ (effectiveReactiveCell w).reads, s ∉ changedSyms) :
    evalWorkbookCell k w oldEnv = evalWorkbookCell k w newEnv := by
  apply evalCell_frame
  intro s hsRead
  apply hAgree s (hSymClean s hsRead)
  intro ck hsEq; subst hsEq
  simp only [effectiveReactiveCell, List.mem_append, List.mem_map] at hsRead
  rcases hsRead with hInRaw | ⟨ck', hMemCk', hEqSym⟩
  · exact hCiteClean ck (hWf ck hInRaw)
  · rw [← citeSymbol_inj hEqSym]; exact hCiteClean ck' hMemCk'
theorem recomputeWorkbookSchedule_eq_full (k : CellKernel) (edit : WorkbookEdit)
    (impactedOwners : List String) (cs : List WorkbookCell) (hWf : ∀ w ∈ cs, WellFormedCellReads w)
    (oldEnv newEnv : Environment) (changedSyms : List SymbolName)
    (hAgree : WorkbookEnvAgreeOutside impactedOwners changedSyms oldEnv newEnv) :
    recomputeWorkbookSchedule k edit impactedOwners
      (evalWorkbookSchedule k cs oldEnv) newEnv changedSyms =
    evalWorkbookSchedule k (cs.map (applyEditToCell edit)) newEnv := by
  induction cs generalizing oldEnv newEnv changedSyms with
  | nil => rfl
  | cons w ws ih =>
    have hwWf := hWf w (List.mem_cons_self ..)
    have hwsWf := fun u hu => hWf u (List.mem_cons_of_mem w hu)
    by_cases hDirty : isWorkbookCellDirty edit impactedOwners changedSyms w = true
    · simp only [evalWorkbookSchedule, recomputeWorkbookSchedule, List.map_cons,
        isWorkbookCellDirty_applyEdit, hDirty, ↓reduceIte, nextWorkbookChanged,
        applyEditToCell_effective_defs]
      congr 1; apply ih hwsWf
      exact publishWorkbookCell_frame w (applyEditToCell edit w) _ _ oldEnv newEnv
        impactedOwners changedSyms (applyEditToCell_effective_defs edit w).symm hAgree
    · have hClean := Bool.eq_false_iff.mpr hDirty
      obtain ⟨hwEq, hCiteClean, hSymClean⟩ := clean_workbook_cell_support edit impactedOwners changedSyms w hClean
      have hEvalEq := evalWorkbookCell_clean_agree k w hwWf impactedOwners changedSyms oldEnv newEnv
        hAgree hCiteClean hSymClean
      simp only [evalWorkbookSchedule, recomputeWorkbookSchedule, List.map_cons,
        hwEq, hClean, Bool.false_eq_true, ↓reduceIte, nextWorkbookChanged, hEvalEq]
      congr 1; apply ih hwsWf
      exact publishWorkbookCell_same w (evalWorkbookCell k w newEnv) oldEnv newEnv
        impactedOwners changedSyms hAgree
/-- **Exact Incremental vs. Full Workbook Equivalence (`evalWorkbookIncremental_eq_full`)**. -/
theorem evalWorkbookIncremental_eq_full (k : CellKernel) (title : String)
    (secs : List WorkbookSection) (cs : List WorkbookCell)
    (hWf : ∀ w ∈ cs, WellFormedCellReads w) (edit : WorkbookEdit) :
    evalWorkbookIncremental k (evalWorkbookFull k title secs cs) edit =
      evalWorkbookFull k title (applyEditToSections secs edit) (cs.map (applyEditToCell edit)) := by
  unfold evalWorkbookIncremental evalWorkbookFull
  simp only [Workbook.mk.injEq, true_and]
  exact recomputeWorkbookSchedule_eq_full k edit (editImpactedOwners secs edit) cs hWf _ _ []
    (sectionEnvironment_agree_after_edit secs edit)
inductive WorkbookStepTrace (k : CellKernel) (edit : WorkbookEdit) (impactedOwners : List String) :
    List CachedWorkbookCell → Environment → List SymbolName → List CachedWorkbookCell → List CellId → Prop where
  | done (env changedSyms) :
      WorkbookStepTrace k edit impactedOwners [] env changedSyms [] []
  | clean (old : CachedWorkbookCell) (cs env changedSyms out recomputed)
      (hClean : isWorkbookCellDirty edit impactedOwners changedSyms old.entry = false)
      (hRest : WorkbookStepTrace k edit impactedOwners cs
        (publishWorkbookCell old.entry old.result env) changedSyms out recomputed) :
      WorkbookStepTrace k edit impactedOwners (old :: cs) env changedSyms (old :: out) recomputed
  | dirty (old : CachedWorkbookCell) (cs env changedSyms out recomputed)
      (hDirty : isWorkbookCellDirty edit impactedOwners changedSyms old.entry = true)
      (hRest : WorkbookStepTrace k edit impactedOwners cs
        (publishWorkbookCell (applyEditToCell edit old.entry)
          (evalWorkbookCell k (applyEditToCell edit old.entry) env) env)
        ((effectiveReactiveCell old.entry).defs ++ changedSyms) out recomputed) :
      WorkbookStepTrace k edit impactedOwners (old :: cs) env changedSyms
        (⟨applyEditToCell edit old.entry,
          evalWorkbookCell k (applyEditToCell edit old.entry) env⟩ :: out)
        (old.entry.reactive.id :: recomputed)
theorem recomputeWorkbookSchedule_trace (k : CellKernel) (edit : WorkbookEdit)
    (impactedOwners : List String) (cs : List CachedWorkbookCell)
    (env : Environment) (changedSyms : List SymbolName) :
    WorkbookStepTrace k edit impactedOwners cs env changedSyms
      (recomputeWorkbookSchedule k edit impactedOwners cs env changedSyms)
      (scanWorkbookDirtyCone edit impactedOwners (cs.map CachedWorkbookCell.entry) changedSyms) := by
  induction cs generalizing env changedSyms with
  | nil => exact .done env changedSyms
  | cons old rest ih =>
    by_cases hDirty : isWorkbookCellDirty edit impactedOwners changedSyms old.entry = true
    · simp only [recomputeWorkbookSchedule, List.map_cons, scanWorkbookDirtyCone,
        isWorkbookCellDirty_applyEdit, hDirty, ↓reduceIte, nextWorkbookChanged,
        applyEditToCell_effective_defs]
      exact .dirty old rest env changedSyms _ _ hDirty (ih _ _)
    · have hClean := Bool.eq_false_iff.mpr hDirty
      have hwEq := (clean_workbook_cell_support edit impactedOwners changedSyms old.entry hClean).1
      simp only [recomputeWorkbookSchedule, List.map_cons, scanWorkbookDirtyCone,
        hwEq, hClean, Bool.false_eq_true, ↓reduceIte, nextWorkbookChanged]
      have hOld : (⟨old.entry, old.result⟩ : CachedWorkbookCell) = old := by cases old; rfl
      rw [hOld]; exact .clean old rest env changedSyms _ _ hClean (ih _ _)
theorem recomputeWorkbookSchedule_preserves_clean (k : CellKernel) (edit : WorkbookEdit)
    (impactedOwners : List String) (cs : List CachedWorkbookCell)
    (env : Environment) (changedSyms : List SymbolName) (u : CachedWorkbookCell)
    (hu : u ∈ cs)
    (hNotDirty : u.entry.reactive.id ∉
      scanWorkbookDirtyCone edit impactedOwners (cs.map CachedWorkbookCell.entry) changedSyms) :
    u ∈ recomputeWorkbookSchedule k edit impactedOwners cs env changedSyms := by
  induction cs generalizing env changedSyms with
  | nil => cases hu
  | cons old rest ih =>
    simp only [List.mem_cons] at hu
    by_cases hDirty : isWorkbookCellDirty edit impactedOwners changedSyms old.entry = true
    · simp only [List.map_cons, scanWorkbookDirtyCone, hDirty, ↓reduceIte,
        List.mem_cons, not_or] at hNotDirty
      have huRest : u ∈ rest := hu.resolve_left fun hEq =>
        hNotDirty.1 (congrArg (fun x => x.entry.reactive.id) hEq)
      simp only [recomputeWorkbookSchedule, isWorkbookCellDirty_applyEdit, hDirty,
        ↓reduceIte, nextWorkbookChanged_applyEdit, List.mem_cons]
      exact .inr (ih _ _ huRest hNotDirty.2)
    · have hClean := Bool.eq_false_iff.mpr hDirty
      have hwEq := (clean_workbook_cell_support edit impactedOwners changedSyms old.entry hClean).1
      simp only [List.map_cons, scanWorkbookDirtyCone, hClean, Bool.false_eq_true, ↓reduceIte] at hNotDirty
      simp only [recomputeWorkbookSchedule, hwEq, hClean, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rcases hu with rfl | huRest
      · exact .inl (by cases u; rfl)
      · exact .inr (ih _ _ huRest hNotDirty)
/-- **Dirty-Cone Exactness & Receipt Reuse (`workbook_edit_recomputes_only_dirty_cone`)**. -/
theorem workbook_edit_recomputes_only_dirty_cone (k : CellKernel) (wb : Workbook) (edit : WorkbookEdit) :
    let newSecs := applyEditToSections wb.sections edit
    WorkbookStepTrace k edit (editImpactedOwners wb.sections edit)
      wb.cells (sectionEnvironment newSecs (newSecs.length + 1)) []
      (evalWorkbookIncremental k wb edit).cells (workbookDirtyCone wb edit) ∧
    (∀ u ∈ wb.cells, u.entry.reactive.id ∉ workbookDirtyCone wb edit →
      u ∈ (evalWorkbookIncremental k wb edit).cells) :=
  ⟨recomputeWorkbookSchedule_trace k edit _ wb.cells _ [],
   fun u hu hNotDirty => recomputeWorkbookSchedule_preserves_clean k edit _ wb.cells _ [] u hu hNotDirty⟩

/-! ## 4. Bidirectional Scrubbable Projection Lenses ("No Dead Pixels", Houyhnhnm Ch. 7) -/
inductive DataTag where | natTag | boolTag | labelTag | recordTag | variantTag deriving DecidableEq, Repr
def dataMatchesTag : Data → DataTag → Bool
  | .natural _, .natTag | .boolean _, .boolTag | .label _, .labelTag
  | .record _, .recordTag | .variant _ _, .variantTag => true
  | _, _ => false
inductive LensFieldAccess where | scrubbable | readOnlyBadge deriving DecidableEq, Repr
structure ProjectedField where (name : String) (value : Data) (access : LensFieldAccess) deriving DecidableEq, Repr
structure ProjectedView where
  (cellId : String) (kind : ProjectionKind) (fields : List ProjectedField) (verifiedBadge : Option ByteArray)
  deriving DecidableEq, Repr
def ProjectedView.lookupField (v : ProjectedView) (fieldName : String) : Option ProjectedField :=
  v.fields.find? (fun f => f.name == fieldName)
def ProjectedView.lookupValue (v : ProjectedView) (fieldName : String) : Option Data :=
  (v.lookupField fieldName).map ProjectedField.value
structure ViewEdit where (fieldName : String) (newValue : Data) deriving DecidableEq, Repr
inductive LensRefusal where
  | readOnlyField (fieldName : String)
  | unknownField (fieldName : String)
  | typeMismatch (fieldName : String) (expected : DataTag)
  | kindMismatch (expected actual : ProjectionKind)
  | malformedCellRecord (cellId : String)
  deriving DecidableEq, Repr
structure ProjectionLens where
  kind : ProjectionKind
  editableSchema : List (String × DataTag)
  badgeFields : List String
  view : StructuredCell → ProjectedView
  scrub : StructuredCell → ViewEdit → Except LensRefusal (StructuredCell × Patch)
def computeFieldPin32 (fieldName : String) (val : Data) : ByteArray :=
  sha256Bytes32 ((fieldName ++ "=" ++ reprStr val).toUTF8)
def lensSchemaForKind : ProjectionKind → List (String × DataTag) × List String
  | .prose                 => ([("summary", .labelTag)], ["wordCountBadge"])
  | .obendCode             => ([("fuelBudget", .natTag), ("inputParam", .natTag)], ["typeBadge", "proofBadge"])
  | .casSymbolic           => ([("degreeCap", .natTag), ("modulus", .natTag)], ["groebnerCert", "proofBadge"])
  | .leanBridge            => ([("timeoutMs", .natTag)], ["kernelVerified", "proofBadge"])
  | .lawContract           => ([("bound", .natTag), ("budgetCap", .natTag), ("strictMode", .boolTag)], ["confluenceDial", "proofBadge"])
  | .deosAffordance        => ([("quorum", .natTag), ("epochCap", .natTag)], ["simplexTier", "proofBadge"])
  | .hardwareSchematic     => ([("clockMhz", .natTag), ("pipelineStages", .natTag)], ["cdcClean", "rtlSynthCert"])
  | .hardwareTiming        => ([("periodPs", .natTag), ("uncertaintyPs", .natTag)], ["wnsPs", "staSignoffCert"])
  | .hardwareLayout        => ([("utilizationPct", .natTag), ("aspectRatio", .natTag)], ["drcClean", "pnrCert"])
  | .ledgerSeat            => ([("transferAmount", .natTag), ("reserveFloor", .natTag)], ["conservationCert", "proofBadge"])
  | .pdeConservation       => ([("cflMilli", .natTag), ("gridCells", .natTag)], ["entropyResidual", "hyperbolicCert"])
  | .feecSimplicialFem     => ([("polynomialOrder", .natTag), ("meshRefinement", .natTag)], ["pragerSyngeGap", "cohomologyBetti"])
  | .pcbMultiphysicsDfm    => ([("traceWidthUm", .natTag), ("clearanceUm", .natTag), ("copperWeightOz", .natTag)], ["drcVerified", "impedanceOhm", "tempestMarginDb"])
  | .vehicle6DofTrajectory => ([("thrustN", .natTag), ("massKg", .natTag), ("horizonSteps", .natTag)], ["se3SymplecticCert", "energyDriftPpm"])
  | .zkCustodyReceipt      => ([("epochLimit", .natTag), ("thresholdK", .natTag)], ["merkleRoot", "custodyProof"])
  | .frustumRedactedView   => ([("viewerClearance", .labelTag), ("maxDepth", .natTag)], ["commitmentRoot", "redactionProof"])
def updateAssocInPlace {β : Type} (xs : List (String × β)) (key : String) (val : β) : List (String × β) :=
  xs.map fun kv => if kv.1 == key then (key, val) else kv
theorem updateAssocInPlace_lookup_same {β : Type} {xs : List (String × β)} {key : String} {val : β}
    (hPresent : ∃ old, xs.lookup key = some old) :
    (updateAssocInPlace xs key val).lookup key = some val := by
  unfold updateAssocInPlace
  induction xs with
  | nil => obtain ⟨_, h⟩ := hPresent; cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩; simp only [List.map_cons]
    cases hk : k == key
    · have hkSym : (key == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hk))
      simp only [Bool.false_eq_true, ↓reduceIte, List.lookup, hkSym] at hPresent ⊢
      exact ih hPresent
    · simp [List.lookup]
theorem updateAssocInPlace_lookup_other {β : Type} (xs : List (String × β)) (key other : String) (val : β)
    (hNe : other ≠ key) :
    (updateAssocInPlace xs key val).lookup other = xs.lookup other := by
  unfold updateAssocInPlace
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩; simp only [List.map_cons]
    cases hk : k == key
    · simp only [Bool.false_eq_true, ↓reduceIte, List.lookup]
      cases other == k
      · exact ih
      · rfl
    · have hkEq := beq_iff_eq.mp hk; subst hkEq
      have hOtherK : (other == k) = false := beq_eq_false_iff_ne.mpr hNe
      simp only [↓reduceIte, List.lookup, hOtherK]; exact ih
theorem updateAssocInPlace_self {β : Type} {xs : List (String × β)} {key : String} {val : β}
    (hNoDup : (xs.map Prod.fst).Nodup) (hLookup : xs.lookup key = some val) :
    updateAssocInPlace xs key val = xs := by
  unfold updateAssocInPlace
  induction xs with
  | nil => cases hLookup
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.map_cons, List.nodup_cons] at hNoDup ⊢
    cases hk : key == k
    · have hkSym : (k == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hk))
      simp only [List.lookup, hk] at hLookup
      simp only [hkSym, Bool.false_eq_true, ↓reduceIte]
      exact congrArg ((k, v) :: ·) (ih hNoDup.2 hLookup)
    · have hkEq := beq_iff_eq.mp hk; subst hkEq
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hLookup; subst hLookup
      simp only [beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      have hRestId : ∀ x ∈ rest, (if x.1 == key then (key, v) else x) = x := fun x hx => by
        have hNeX : x.1 ≠ key := fun hEq => hNoDup.1 (by rw [← hEq]; exact List.mem_map_of_mem hx)
        simp only [beq_eq_false_iff_ne.mpr hNeX, Bool.false_eq_true, ↓reduceIte]
      clear hNoDup ih
      induction rest with
      | nil => rfl
      | cons r rs ihr =>
        simp only [List.map_cons, hRestId r (List.mem_cons_self ..)]
        exact congrArg (r :: ·) (ihr (fun z hz => hRestId z (List.mem_cons_of_mem r hz)))
theorem updateAssocInPlace_idem {β : Type} (xs : List (String × β)) (key : String) (v1 v2 : β) :
    updateAssocInPlace (updateAssocInPlace xs key v1) key v2 = updateAssocInPlace xs key v2 := by
  unfold updateAssocInPlace
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩; simp only [List.map_cons]
    cases hk : k == key
    · simp only [Bool.false_eq_true, ↓reduceIte, hk]; exact congrArg ((k, v) :: ·) ih
    · simp only [↓reduceIte, beq_self_eq_true]; exact congrArg ((key, v2) :: ·) ih
def renderLensView (kind : ProjectionKind) (c : StructuredCell) : ProjectedView :=
  let (editSchema, badges) := lensSchemaForKind kind
  let recFields : List (String × Data) := match c.ast with | .record fs => fs | _ => []
  let projected := recFields.map fun (fname, fval) =>
    let access := if badges.contains fname then .readOnlyBadge
      else if (editSchema.lookup fname).isSome then .scrubbable else .readOnlyBadge
    ({ name := fname, value := fval, access := access } : ProjectedField)
  { cellId := c.id, kind := c.kind, fields := projected, verifiedBadge := c.receipt }
def scrubLensCell (kind : ProjectionKind) (c : StructuredCell) (edit : ViewEdit) :
    Except LensRefusal (StructuredCell × Patch) :=
  let (editSchema, badges) := lensSchemaForKind kind
  if c.kind != kind then .error (.kindMismatch kind c.kind)
  else if badges.contains edit.fieldName || edit.fieldName == "receiptBadge" then
    .error (.readOnlyField edit.fieldName)
  else match editSchema.lookup edit.fieldName with
    | none => .error (.unknownField edit.fieldName)
    | some expectedTag =>
      if !dataMatchesTag edit.newValue expectedTag then
        .error (.typeMismatch edit.fieldName expectedTag)
      else match c.ast with
        | .record fs =>
          match fs.lookup edit.fieldName with
          | none => .error (.unknownField edit.fieldName)
          | some _ =>
            let fs' := updateAssocInPlace fs edit.fieldName edit.newValue
            let pins' := updateAssocInPlace c.pins edit.fieldName
              (computeFieldPin32 edit.fieldName edit.newValue)
            let c' : StructuredCell := { c with ast := .record fs', pins := pins' }
            .ok (c', [.add 1 c'.toContent root])
        | _ => .error (.malformedCellRecord c.id)
@[expose] def lensForKind (kind : ProjectionKind) : ProjectionLens :=
  let (editSchema, badges) := lensSchemaForKind kind
  { kind := kind, editableSchema := editSchema, badgeFields := badges
    view := renderLensView kind, scrub := scrubLensCell kind }
structure WellFormedLensCell (kind : ProjectionKind) (c : StructuredCell) : Prop where
  kind_eq : c.kind = kind
  record_ast : ∃ fs, c.ast = .record fs ∧ (fs.map Prod.fst).Nodup ∧
    (∀ f tag, (lensSchemaForKind kind).1.lookup f = some tag →
      f ∉ (lensSchemaForKind kind).2 ∧ f ≠ "receiptBadge" ∧
      (∀ v, fs.lookup f = some v → dataMatchesTag v tag = true) ∧
      (∀ v, fs.lookup f = some v → c.pins.lookup f = some (computeFieldPin32 f v))) ∧
    (c.pins.map Prod.fst).Nodup
private theorem find_projectedField_of_nodup (badges : List String)
    (editSchema : List (String × DataTag)) (fs : List (String × Data)) (fname : String) :
    ((fs.map fun (n, v) =>
      ({ name := n, value := v
         access := if badges.contains n then .readOnlyBadge
                   else if (editSchema.lookup n).isSome then .scrubbable
                   else .readOnlyBadge } : ProjectedField)).find? (fun pf => pf.name == fname)).map
      ProjectedField.value = fs.lookup fname := by
  induction fs with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.map_cons, List.find?_cons]
    by_cases hk : (k == fname) = true
    · have hkEq := beq_iff_eq.mp hk; subst hkEq; simp [List.lookup]
    · have hkFalse : (k == fname) = false := Bool.eq_false_iff.mpr hk
      have hkSym : (fname == k) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hkFalse))
      simp only [hkFalse, Option.map, List.lookup, hkSym] at ih ⊢; exact ih
private theorem list_contains_false_of_not_mem {xs : List String} {x : String} (h : x ∉ xs) :
    xs.contains x = false :=
  Bool.eq_false_iff.mpr (fun hc => h (List.contains_iff_mem.mp hc))
/-- **Read-Only Badge Immutability (`scrub_readOnly_refused`)**. -/
theorem scrub_readOnly_refused (kind : ProjectionKind) (c : StructuredCell)
    (hKind : c.kind = kind) (edit : ViewEdit)
    (hBadge : edit.fieldName ∈ (lensForKind kind).badgeFields ∨ edit.fieldName = "receiptBadge") :
    (lensForKind kind).scrub c edit = .error (.readOnlyField edit.fieldName) := by
  dsimp only [lensForKind]; unfold scrubLensCell; dsimp only
  have hBne : (c.kind != kind) = false := by simp [hKind]
  have hCond : ((lensSchemaForKind kind).2.contains edit.fieldName || edit.fieldName == "receiptBadge") = true := by
    rcases hBadge with hMem | hEq
    · dsimp only [lensForKind] at hMem; rw [List.contains_iff_mem.mpr hMem]; rfl
    · simp [hEq]
  simp only [hBne, Bool.false_eq_true, ↓reduceIte, hCond]
/-- **Putnam/Foster Lens Law 1 — `GetPut` (`lens_get_put`)**. -/
theorem lens_get_put (kind : ProjectionKind) (c : StructuredCell)
    (hWf : WellFormedLensCell kind c) (f : String) (tag : DataTag) (val : Data)
    (hSchema : (lensSchemaForKind kind).1.lookup f = some tag)
    (hGet : ((lensForKind kind).view c).lookupValue f = some val) :
    ((lensForKind kind).scrub c ⟨f, val⟩).map Prod.fst = .ok c := by
  obtain ⟨fs, hAst, hFsNodup, hFields, hPinsNodup⟩ := hWf.record_ast
  have ⟨hNotBadge, hNotReceipt, hTagOk, hPinSync⟩ := hFields f tag hSchema
  have hFsLookup : fs.lookup f = some val := by
    dsimp only [ProjectedView.lookupValue, ProjectedView.lookupField, lensForKind, renderLensView] at hGet
    rw [hAst, find_projectedField_of_nodup] at hGet; exact hGet
  have hMatch := hTagOk val hFsLookup
  have hPinLookup := hPinSync val hFsLookup
  dsimp only [lensForKind]; unfold scrubLensCell; dsimp only
  have hKindBne : (c.kind != kind) = false := by simp [hWf.kind_eq]
  have hBadgeFalse : ((lensSchemaForKind kind).2.contains f || f == "receiptBadge") = false := by
    rw [list_contains_false_of_not_mem hNotBadge, beq_eq_false_iff_ne.mpr hNotReceipt]; rfl
  simp only [hKindBne, Bool.false_eq_true, ↓reduceIte, hBadgeFalse, hSchema, hMatch,
    Bool.not_true, hAst, hFsLookup, Except.map]
  congr 1
  rw [updateAssocInPlace_self hFsNodup hFsLookup, updateAssocInPlace_self hPinsNodup hPinLookup, ← hAst]
/-- **Putnam/Foster Lens Law 2 — `PutGet` (`lens_put_get`)**. -/
theorem lens_put_get (kind : ProjectionKind) (c c' : StructuredCell) (patch : Patch) (edit : ViewEdit)
    (hScrub : (lensForKind kind).scrub c edit = .ok (c', patch)) :
    ((lensForKind kind).view c').lookupValue edit.fieldName = some edit.newValue ∧
    ((∃ oldPin, c.pins.lookup edit.fieldName = some oldPin) →
      c'.pins.lookup edit.fieldName = some (computeFieldPin32 edit.fieldName edit.newValue)) := by
  dsimp only [lensForKind] at hScrub; unfold scrubLensCell at hScrub; dsimp only at hScrub
  split at hScrub <;> try cases hScrub
  split at hScrub <;> try cases hScrub
  cases hSchema : (lensSchemaForKind kind).1.lookup edit.fieldName with
  | none => simp [hSchema] at hScrub
  | some tag =>
    simp only [hSchema] at hScrub; split at hScrub <;> try cases hScrub
    cases hAst : c.ast with
    | natural _ | boolean _ | label _ | variant _ _ => simp [hAst] at hScrub
    | record fs =>
      simp only [hAst] at hScrub
      cases hOld : fs.lookup edit.fieldName with
      | none => simp [hOld] at hScrub
      | some oldVal =>
        simp only [hOld, Except.ok.injEq, Prod.mk.injEq] at hScrub
        rcases hScrub with ⟨rfl, _⟩
        refine ⟨?_, fun hPin => updateAssocInPlace_lookup_same hPin⟩
        dsimp only [ProjectedView.lookupValue, ProjectedView.lookupField, lensForKind, renderLensView]
        rw [find_projectedField_of_nodup]
        exact updateAssocInPlace_lookup_same ⟨oldVal, hOld⟩
/-- **Putnam/Foster Lens Law 3 — `PutPut` (`lens_put_put`)**. -/
theorem lens_put_put (kind : ProjectionKind) (c c1 c2 : StructuredCell)
    (p1 p2 : Patch) (f : String) (v1 v2 : Data)
    (h1 : (lensForKind kind).scrub c ⟨f, v1⟩ = .ok (c1, p1))
    (h2 : (lensForKind kind).scrub c1 ⟨f, v2⟩ = .ok (c2, p2)) :
    (lensForKind kind).scrub c ⟨f, v2⟩ = .ok (c2, p2) := by
  dsimp only [lensForKind] at h1 h2 ⊢; unfold scrubLensCell at h1 h2 ⊢; dsimp only at h1 h2 ⊢
  split at h1 <;> try cases h1
  rename_i hKindOk
  split at h1 <;> try cases h1
  rename_i hNotBadge
  cases hSchema : (lensSchemaForKind kind).1.lookup f with
  | none => simp [hSchema] at h1
  | some tag =>
    simp only [hSchema] at h1 ⊢; split at h1 <;> try cases h1
    cases hAst : c.ast with
    | natural _ | boolean _ | label _ | variant _ _ => simp [hAst] at h1
    | record fs =>
      simp only [hAst] at h1 ⊢
      cases hOld : fs.lookup f with
      | none => simp [hOld] at h1
      | some oldVal =>
        simp only [hOld, Except.ok.injEq, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, _⟩
        have hKindF : (c.kind != kind) = false := Bool.eq_false_iff.mpr hKindOk
        have hBadgeF : ((lensSchemaForKind kind).2.contains f || f == "receiptBadge") = false :=
          Bool.eq_false_iff.mpr hNotBadge
        simp only [hKindF, Bool.false_eq_true, ↓reduceIte, hBadgeF, hSchema] at h2 ⊢
        split at h2 <;> try cases h2
        rename_i hTag2
        have hTag2F : (!dataMatchesTag v2 tag) = false := Bool.eq_false_iff.mpr hTag2
        have hLookup1 := updateAssocInPlace_lookup_same (xs := fs) (key := f) (val := v1) ⟨oldVal, hOld⟩
        simp only [hTag2F, Bool.false_eq_true, ↓reduceIte, hLookup1, Except.ok.injEq, Prod.mk.injEq] at h2 ⊢
        rcases h2 with ⟨rfl, rfl⟩; simp [updateAssocInPlace_idem]
/-- **Sibling-Pin & Proof-Badge Frame Preservation (`lens_scrub_preserves_sibling_pins`)**. -/
theorem lens_scrub_preserves_sibling_pins (kind : ProjectionKind) (c c' : StructuredCell)
    (patch : Patch) (edit : ViewEdit)
    (hScrub : (lensForKind kind).scrub c edit = .ok (c', patch)) :
    c'.receipt = c.receipt ∧
    (∀ g, g ≠ edit.fieldName →
      ((lensForKind kind).view c').lookupValue g = ((lensForKind kind).view c).lookupValue g ∧
      c'.pins.lookup g = c.pins.lookup g) := by
  dsimp only [lensForKind] at hScrub; unfold scrubLensCell at hScrub; dsimp only at hScrub
  split at hScrub <;> try cases hScrub
  split at hScrub <;> try cases hScrub
  cases hSchema : (lensSchemaForKind kind).1.lookup edit.fieldName with
  | none => simp [hSchema] at hScrub
  | some tag =>
    simp only [hSchema] at hScrub
    split at hScrub <;> try cases hScrub
    cases hAst : c.ast with
    | natural _ | boolean _ | label _ | variant _ _ => simp [hAst] at hScrub
    | record fs =>
      simp only [hAst] at hScrub
      cases hOld : fs.lookup edit.fieldName with
      | none => simp [hOld] at hScrub
      | some _ =>
        simp only [hOld, Except.ok.injEq, Prod.mk.injEq] at hScrub
        rcases hScrub with ⟨rfl, _⟩
        refine ⟨rfl, fun g hNe => ⟨?_, updateAssocInPlace_lookup_other c.pins edit.fieldName g _ hNe⟩⟩
        dsimp only [ProjectedView.lookupValue, ProjectedView.lookupField, lensForKind, renderLensView]
        rw [hAst, find_projectedField_of_nodup, find_projectedField_of_nodup]
        exact updateAssocInPlace_lookup_other fs edit.fieldName g edit.newValue hNe
def dataToLiteralInt? : Data → Option Int
  | .natural n => some (Int.ofNat n)
  | .boolean b => some (if b then 1 else 0)
  | _ => none
@[expose] def scrubWorkbookCell (k : CellKernel) (wb : Workbook) (targetCellKey : String)
    (edit : ViewEdit) : Except LensRefusal (Workbook × Patch) :=
  match wb.cells.find? (fun c => c.entry.cellKey == targetCellKey) with
  | none => .error (.unknownField targetCellKey)
  | some targetCached =>
    let sc := targetCached.entry.structured
    match (lensForKind sc.kind).scrub sc edit with
    | .error err => .error err
    | .ok (sc', patch) =>
      let newBody : CellBody := match dataToLiteralInt? edit.newValue with
        | some lit => [[{ op := .literal, arg := lit }]]
        | none => targetCached.entry.reactive.body
      let wbSeeded : Workbook :=
        { wb with cells := wb.cells.map fun c =>
            if c.entry.cellKey == targetCellKey then
              { c with entry := { c.entry with structured := sc' } }
            else c }
      .ok (evalWorkbookIncremental k wbSeeded
        (.editCellBody targetCached.entry.reactive.id sc'.ast newBody), patch)

/-! ## 5. Conflict-Preserving Pushout Branch Merge (`mergeWorkbookBranches`) -/
structure WorkbookMergeConflict where
  (cellKey : String) (baseCell leftCell rightCell : Option WorkbookCell) deriving DecidableEq, Repr
structure WorkbookBranchMergeResult where
  (mergedPageGraph : Graph) (mergedCells : List (String × CachedWorkbookCell)) (conflicts : List WorkbookMergeConflict)
  deriving DecidableEq, Repr
def lookupCachedByKey (cs : List CachedWorkbookCell) (key : String) : Option CachedWorkbookCell :=
  (cs.map fun c => (c.entry.cellKey, c)).lookup key
def lookupSpecByKey (cs : List CachedWorkbookCell) (key : String) : Option WorkbookCell :=
  (lookupCachedByKey cs key).map CachedWorkbookCell.entry
def collectWorkbookMergeKeys (base left right : Workbook) : List String :=
  dedupCellKeys ((base.cells.map (·.entry.cellKey)) ++
    (left.cells.map (·.entry.cellKey)) ++ (right.cells.map (·.entry.cellKey)))
def mergeWorkbookCellAt (base left right : Workbook) (key : String) :
    MergeCellResult (Option CachedWorkbookCell) :=
  match mergeCell3 (lookupSpecByKey base.cells key)
                   (lookupSpecByKey left.cells key)
                   (lookupSpecByKey right.cells key) with
  | .merged none => .merged none
  | .merged (some chosenSpec) =>
    let cachedChoice :=
      match lookupCachedByKey left.cells key, lookupCachedByKey right.cells key with
      | some lc, _ =>
        if lc.entry = chosenSpec then some lc
        else (lookupCachedByKey right.cells key).filter (fun rc => decide (rc.entry = chosenSpec))
      | none, some rc => if rc.entry = chosenSpec then some rc else none
      | none, none => none
    .merged cachedChoice
  | .conflict _ _ _ =>
    .conflict (lookupCachedByKey base.cells key)
              (lookupCachedByKey left.cells key)
              (lookupCachedByKey right.cells key)
@[expose] def mergeWorkbookBranches (baseGraph leftGraph rightGraph : Graph)
    (base left right : Workbook) : WorkbookBranchMergeResult :=
  let _ := baseGraph
  let keys := collectWorkbookMergeKeys base left right
  { mergedPageGraph := Graph.merge leftGraph rightGraph
    mergedCells := keys.filterMap fun k =>
      (match mergeWorkbookCellAt base left right k with
       | .merged (some cc) => some cc | _ => none).map fun v => (k, v)
    conflicts := keys.filterMap fun k =>
      match mergeCell3 (lookupSpecByKey base.cells k)
                       (lookupSpecByKey left.cells k)
                       (lookupSpecByKey right.cells k) with
      | .merged _ => none | .conflict b l r => some ⟨k, b, l, r⟩ }
private theorem lookup_filterMap_unique_keys {α : Type} (keys : List String) (hNodup : keys.Nodup)
    (f : String → Option α) (k : String) :
    (keys.filterMap fun x => (f x).map fun v => (x, v)).lookup k =
      if k ∈ keys then f k else none := by
  induction keys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.nodup_cons] at hNodup
    by_cases hkx : k = x
    · subst hkx
      cases hfx : f k with
      | none => simp [hfx, ih hNodup.2, hNodup.1]
      | some v => simp [hfx]
    · have hNeBeq : (k == x) = false := beq_eq_false_iff_ne.mpr hkx
      cases hfx : f x <;> simp [hfx, List.lookup, hNeBeq, ih hNodup.2, hkx]
theorem mem_collectWorkbookMergeKeys_iff (base left right : Workbook) (k : String) :
    k ∈ collectWorkbookMergeKeys base left right ↔
      k ∈ base.cells.map (·.entry.cellKey) ∨
      k ∈ left.cells.map (·.entry.cellKey) ∨
      k ∈ right.cells.map (·.entry.cellKey) := by
  simp only [collectWorkbookMergeKeys, mem_dedupCellKeys, List.mem_append]
  exact ⟨fun h => h.elim (fun h12 => h12.elim .inl (fun h2 => .inr (.inl h2))) (fun h3 => .inr (.inr h3)),
         fun h => h.elim (fun h1 => .inl (.inl h1)) (fun h23 => h23.elim (fun h2 => .inl (.inr h2)) .inr)⟩
private theorem conflict_swap_mem (baseGraph g1 g2 : Graph) (base w1 w2 : Workbook)
    (k : String) (b l r : Option WorkbookCell)
    (hMem : (⟨k, b, l, r⟩ : WorkbookMergeConflict) ∈
      (mergeWorkbookBranches baseGraph g1 g2 base w1 w2).conflicts) :
    (⟨k, b, r, l⟩ : WorkbookMergeConflict) ∈
      (mergeWorkbookBranches baseGraph g2 g1 base w2 w1).conflicts := by
  simp only [mergeWorkbookBranches, List.mem_filterMap] at hMem ⊢
  obtain ⟨k', hk'Mem, hk'Eq⟩ := hMem
  cases hM : mergeCell3 (lookupSpecByKey base.cells k')
                        (lookupSpecByKey w1.cells k')
                        (lookupSpecByKey w2.cells k') with
  | merged _ => simp [hM] at hk'Eq
  | conflict b' l' r' =>
    simp only [hM, Option.some.injEq, WorkbookMergeConflict.mk.injEq] at hk'Eq
    rcases hk'Eq with ⟨hkEq, hbEq, hlEq, hrEq⟩
    subst hkEq; subst hbEq; subst hlEq; subst hrEq
    have hM_def : b' = lookupSpecByKey base.cells k' ∧
                  l' = lookupSpecByKey w1.cells k' ∧
                  r' = lookupSpecByKey w2.cells k' := by
      have hM' := hM; unfold mergeCell3 at hM'
      split at hM' <;> try cases hM'
      split at hM' <;> try cases hM'
      split at hM' <;> try cases hM'
      exact ⟨rfl, rfl, rfl⟩
    rcases hM_def with ⟨rfl, rfl, rfl⟩
    have hComm := (mergeCell3_commutative
      (lookupSpecByKey base.cells k') (lookupSpecByKey w1.cells k') (lookupSpecByKey w2.cells k')).2.mp hM
    have hkSwap : k' ∈ collectWorkbookMergeKeys base w2 w1 := by
      rw [mem_collectWorkbookMergeKeys_iff] at hk'Mem ⊢
      rcases hk'Mem with h1 | h2 | h3
      · exact .inl h1
      · exact .inr (.inr h2)
      · exact .inr (.inl h3)
    exact ⟨k', hkSwap, by simp [hComm]⟩
/-- **Pushout & Cell Merge Commutativity (`mergeWorkbookBranches_comm`)**. -/
theorem mergeWorkbookBranches_comm (baseGraph leftGraph rightGraph : Graph)
    (hCompat : Graph.Compatible leftGraph rightGraph)
    (base left right : Workbook) :
    Graph.Same
      (mergeWorkbookBranches baseGraph leftGraph rightGraph base left right).mergedPageGraph
      (mergeWorkbookBranches baseGraph rightGraph leftGraph base right left).mergedPageGraph ∧
    (∀ k b l r,
      (⟨k, b, l, r⟩ : WorkbookMergeConflict) ∈
        (mergeWorkbookBranches baseGraph leftGraph rightGraph base left right).conflicts ↔
      (⟨k, b, r, l⟩ : WorkbookMergeConflict) ∈
        (mergeWorkbookBranches baseGraph rightGraph leftGraph base right left).conflicts) :=
  ⟨Graph.merge_comm hCompat, fun k b l r =>
    ⟨conflict_swap_mem baseGraph leftGraph rightGraph base left right k b l r,
     conflict_swap_mem baseGraph rightGraph leftGraph base right left k b r l⟩⟩
private theorem mem_keys_of_lookup_some {α : Type} {xs : List (String × α)} {k : String} {v : α}
    (h : xs.lookup k = some v) : (k, v) ∈ xs := by
  induction xs with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    by_cases hk : k = k'
    · subst hk; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h; subst h
      exact List.mem_cons_self ..
    · simp only [List.lookup, beq_eq_false_iff_ne.mpr hk] at h
      exact List.mem_cons_of_mem _ (ih h)
/-- **Unconflicted Cached-Receipt Preservation (`mergeWorkbookBranches_preserves_unconflicted_receipts`)**. -/
theorem mergeWorkbookBranches_preserves_unconflicted_receipts
    (baseGraph leftGraph rightGraph : Graph)
    (base left right : Workbook) (k : String) (lc : CachedWorkbookCell)
    (hLeft : lookupCachedByKey left.cells k = some lc)
    (hRightUnchanged : lookupSpecByKey right.cells k = lookupSpecByKey base.cells k) :
    (mergeWorkbookBranches baseGraph leftGraph rightGraph base left right).mergedCells.lookup k =
      some lc := by
  have hkMem : k ∈ collectWorkbookMergeKeys base left right := by
    rw [mem_collectWorkbookMergeKeys_iff]; right; left
    have hPairMem := mem_keys_of_lookup_some hLeft
    rw [List.mem_map] at hPairMem
    obtain ⟨c, hcMem, hcEq⟩ := hPairMem
    injection hcEq with hkEq _; rw [← hkEq]; exact List.mem_map_of_mem hcMem
  have hLSpec : lookupSpecByKey left.cells k = some lc.entry := by simp [lookupSpecByKey, hLeft]
  have hMerge3 : mergeCell3 (lookupSpecByKey base.cells k)
                            (lookupSpecByKey left.cells k)
                            (lookupSpecByKey right.cells k) = .merged (some lc.entry) := by
    rw [hRightUnchanged, hLSpec, mergeCell3_right_unchanged]
  have hCellAt : mergeWorkbookCellAt base left right k = .merged (some lc) := by
    unfold mergeWorkbookCellAt; rw [hMerge3, hLeft]; simp
  unfold mergeWorkbookBranches; dsimp only
  rw [lookup_filterMap_unique_keys (collectWorkbookMergeKeys base left right) (nodup_dedupCellKeys _)]
  simp [hkMem, hCellAt]

/-! ## 6. Capability-Scoped Redacted Export (`projectWorkbookForViewer`) & Multi-Turn Trace -/
def isCellVisibleToViewer (viewerClearances : List String) : CellVisibility → Bool
  | .publicCell => true
  | .sealedPrivate tag _ => viewerClearances.contains tag
def cellSaltedCommitment (H : Hash) (c : CachedWorkbookCell) : Nat :=
  let saltNat : Nat := match c.entry.visibility with
    | .publicCell => 0 | .sealedPrivate _ salt => salt.toNat
  let metaDigest := (sha256String256 (c.entry.cellKey ++ ":" ++ c.entry.structured.kind.toLabel)).toNat
  let valDigest := (sha256String256 (reprStr c.result.values)).toNat
  let step1 := digestWith H c.entry.reactive.id metaDigest
  let step2 := digestWith H step1 valDigest
  let step3 := digestWith H step2 c.result.receipt.toNat
  digestWith H step3 saltNat
theorem cellSaltedCommitment_lt {H : Hash} (hb : Bounded H) (c : CachedWorkbookCell) :
    cellSaltedCommitment H c < 2 ^ 256 := hb _ _
inductive ExportedWorkbookCell where
  | visible (cached : CachedWorkbookCell) (commitment : BitVec 256) (opening : Opening)
  | redacted (cellId : CellId) (cellKey : String) (kind : ProjectionKind)
      (exportedDefs : List (SymbolName × Int)) (commitment : BitVec 256) (opening : Opening)
  deriving DecidableEq, Repr
def ExportedWorkbookCell.openingOf : ExportedWorkbookCell → Opening
  | .visible _ _ o | .redacted _ _ _ _ _ o => o
def ExportedWorkbookCell.commitmentOf : ExportedWorkbookCell → BitVec 256
  | .visible _ cm _ | .redacted _ _ _ _ cm _ => cm
structure RedactedWorkbook where
  (title : String) (sections : List WorkbookSection) (merkleRoot : Nat) (entries : List ExportedWorkbookCell)
  deriving DecidableEq, Repr
def exportedBindingsOfCell (c : CachedWorkbookCell) : List (SymbolName × Int) :=
  let effDefs := (effectiveReactiveCell c.entry).defs
  effDefs.map fun sym => (sym, c.result.values[effDefs.idxOf sym]?.getD 0)
@[expose] def projectWorkbookForViewer (H : Hash) (viewerClearances : List String)
    (wb : Workbook) : RedactedWorkbook :=
  let leafValues := wb.cells.map (cellSaltedCommitment H)
  { title := wb.title, sections := wb.sections, merkleRoot := mapRoot H leafValues
    entries := wb.cells.zipIdx.map fun (c, idx) =>
      let cmBv := BitVec.ofNat 256 (cellSaltedCommitment H c)
      let op := mapOpening H leafValues idx
      if isCellVisibleToViewer viewerClearances c.entry.visibility then
        ExportedWorkbookCell.visible c cmBv op
      else
        ExportedWorkbookCell.redacted c.entry.reactive.id c.entry.cellKey
          c.entry.structured.kind (exportedBindingsOfCell c) cmBv op }
def publishExportedCell : ExportedWorkbookCell → Environment → Environment
  | .visible c _ _, env => publishWorkbookCell c.entry c.result env
  | .redacted _ _ _ bindings _ _, env =>
    fun s => match bindings.lookup s with | some v => v | none => env s
private theorem lookup_map_pair_self (xs : List SymbolName) (f : SymbolName → Int) (s : SymbolName) :
    (xs.map fun x => (x, f x)).lookup s = if s ∈ xs then some (f s) else none := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    by_cases hs : s = x
    · subst hs; simp
    · simp [List.lookup, beq_eq_false_iff_ne.mpr hs, hs, ih]
theorem publishExportedCell_eq_publishWorkbookCell (viewerClearances : List String)
    (c : CachedWorkbookCell) (cm : BitVec 256) (op : Opening) (env : Environment) :
    publishExportedCell
      (if isCellVisibleToViewer viewerClearances c.entry.visibility then
        ExportedWorkbookCell.visible c cm op
      else
        ExportedWorkbookCell.redacted c.entry.reactive.id c.entry.cellKey
          c.entry.structured.kind (exportedBindingsOfCell c) cm op) env =
    publishWorkbookCell c.entry c.result env := by
  split
  · rfl
  · funext s
    dsimp only [publishExportedCell, exportedBindingsOfCell, publishWorkbookCell, publish]
    rw [lookup_map_pair_self]
    by_cases hs : s ∈ (effectiveReactiveCell c.entry).defs <;> simp [hs]
def verifyExportedSchedule (k : CellKernel) (H : Hash) (merkleRoot : Nat) :
    List ExportedWorkbookCell → Environment → Bool
  | [], _ => true
  | e :: es, env =>
    let merkleOk := opens H e.openingOf merkleRoot && decide (e.openingOf.value = e.commitmentOf.toNat)
    let cellOk := match e with
      | .visible c cm _ =>
        decide (evalWorkbookCell k c.entry env = c.result) && decide (cellSaltedCommitment H c = cm.toNat)
      | .redacted _ _ _ _ _ _ => true
    merkleOk && cellOk && verifyExportedSchedule k H merkleRoot es (publishExportedCell e env)
@[expose] def verifyRedactedWorkbook (k : CellKernel) (H : Hash) (rwb : RedactedWorkbook) : Bool :=
  verifyExportedSchedule k H rwb.merkleRoot rwb.entries
    (sectionEnvironment rwb.sections (rwb.sections.length + 1))
/-- **Confidentiality / Sealed-Payload Erasure (`projectWorkbookForViewer_hides_sealed`)**. -/
theorem projectWorkbookForViewer_hides_sealed (H : Hash) (viewerClearances : List String)
    (wb : Workbook) (idx : Nat) (c : CachedWorkbookCell) (tag : String) (salt : BitVec 256)
    (hIdx : wb.cells[idx]? = some c)
    (hVis : c.entry.visibility = .sealedPrivate tag salt)
    (hNotCleared : tag ∉ viewerClearances) :
    ∃ bindings cm op,
      (projectWorkbookForViewer H viewerClearances wb).entries[idx]? =
        some (.redacted c.entry.reactive.id c.entry.cellKey c.entry.structured.kind bindings cm op) := by
  have hVisFalse : isCellVisibleToViewer viewerClearances c.entry.visibility = false := by
    rw [hVis]; exact list_contains_false_of_not_mem hNotCleared
  refine ⟨exportedBindingsOfCell c, BitVec.ofNat 256 (cellSaltedCommitment H c),
    mapOpening H (wb.cells.map (cellSaltedCommitment H)) idx, ?_⟩
  unfold projectWorkbookForViewer
  simp [List.getElem?_map, List.getElem?_zipIdx, hIdx, hVisFalse]
private theorem verifyExportedSchedule_complete_aux (k : CellKernel) {H : Hash} (hb : Bounded H)
    (viewerClearances : List String) (allLeaves : List Nat) :
    ∀ (cs : List WorkbookCell) (idx : Nat) (env : Environment),
      idx + cs.length ≤ allLeaves.length →
      allLeaves.length < 2 ^ 256 →
      (∀ j (hj : j < cs.length),
        allLeaves.getD (idx + j) 0 =
          cellSaltedCommitment H ((evalWorkbookSchedule k cs env)[j]'(by
            rw [evalWorkbookSchedule_length]; exact hj))) →
      let evaluated := evalWorkbookSchedule k cs env
      let exported := (evaluated.zipIdx idx).map fun (c, j) =>
        let cmBv := BitVec.ofNat 256 (cellSaltedCommitment H c)
        let op := mapOpening H allLeaves j
        if isCellVisibleToViewer viewerClearances c.entry.visibility then
          ExportedWorkbookCell.visible c cmBv op
        else
          ExportedWorkbookCell.redacted c.entry.reactive.id c.entry.cellKey
            c.entry.structured.kind (exportedBindingsOfCell c) cmBv op
      verifyExportedSchedule k H (mapRoot H allLeaves) exported env = true
  | [], _, _, _, _, _ => rfl
  | w :: ws, idx, env, hBound, hSmallLen, hLeavesAt => by
    intro evaluated exported
    have hIdxLt : idx < allLeaves.length := by simp at hBound; omega
    have hIdxSmall : idx < 2 ^ 256 := Nat.lt_trans hIdxLt hSmallLen
    let r := evalWorkbookCell k w env
    let c0 : CachedWorkbookCell := ⟨w, r⟩
    have hLeaf0 : allLeaves[idx]?.getD 0 = cellSaltedCommitment H c0 := by
      have h0 : allLeaves.getD idx 0 = cellSaltedCommitment H c0 := by
        simpa [Nat.add_zero, evalWorkbookSchedule, c0, r] using hLeavesAt 0 (by simp)
      rwa [List.getD_eq_getElem?_getD] at h0
    have hBvToNat : (BitVec.ofNat 256 (cellSaltedCommitment H c0)).toNat = cellSaltedCommitment H c0 :=
      Nat.mod_eq_of_lt (cellSaltedCommitment_lt hb c0)
    have hOpens0 := opens_complete hb allLeaves idx hIdxLt hIdxSmall
    have hPubEq := publishExportedCell_eq_publishWorkbookCell viewerClearances c0
      (BitVec.ofNat 256 (cellSaltedCommitment H c0)) (mapOpening H allLeaves idx) env
    have hTail := verifyExportedSchedule_complete_aux k hb viewerClearances allLeaves ws (idx + 1)
      (publishWorkbookCell w r env) (by simp at hBound ⊢; omega) hSmallLen (fun j hj => by
        have hStep := hLeavesAt (j + 1) (by simp; omega)
        rw [show idx + (j + 1) = (idx + 1) + j by omega] at hStep
        simpa [evalWorkbookSchedule, c0, r] using hStep)
    change verifyExportedSchedule k H (mapRoot H allLeaves)
      ((if isCellVisibleToViewer viewerClearances c0.entry.visibility then
          ExportedWorkbookCell.visible c0 (BitVec.ofNat 256 (cellSaltedCommitment H c0)) (mapOpening H allLeaves idx)
        else
          ExportedWorkbookCell.redacted c0.entry.reactive.id c0.entry.cellKey
            c0.entry.structured.kind (exportedBindingsOfCell c0)
            (BitVec.ofNat 256 (cellSaltedCommitment H c0)) (mapOpening H allLeaves idx)) ::
        List.map _ ((evalWorkbookSchedule k ws (publishWorkbookCell w r env)).zipIdx (idx + 1))) env = true
    unfold verifyExportedSchedule
    rw [hPubEq]
    dsimp only [c0, r] at hLeaf0 hBvToNat ⊢
    by_cases hVis : isCellVisibleToViewer viewerClearances w.visibility = true
    · simp only [hVis, ↓reduceIte, ExportedWorkbookCell.openingOf,
        ExportedWorkbookCell.commitmentOf, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hOpens0, by rw [show (mapOpening H allLeaves idx).value = allLeaves[idx]?.getD 0 from rfl, hLeaf0, hBvToNat]⟩,
        ⟨trivial, hBvToNat.symm⟩⟩, hTail⟩
    · simp only [Bool.not_eq_true] at hVis
      simp only [hVis, Bool.false_eq_true, ↓reduceIte, ExportedWorkbookCell.openingOf,
        ExportedWorkbookCell.commitmentOf, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hOpens0, by rw [show (mapOpening H allLeaves idx).value = allLeaves[idx]?.getD 0 from rfl, hLeaf0, hBvToNat]⟩,
        trivial⟩, hTail⟩
/-- **Collaborator Downstream Verification Completeness (`verifyRedactedWorkbook_complete`)**. -/
theorem verifyRedactedWorkbook_complete (k : CellKernel) (title : String)
    (secs : List WorkbookSection) (cs : List WorkbookCell)
    (hLen : cs.length < 2 ^ 256) (viewerClearances : List String) :
    verifyRedactedWorkbook k deployed
      (projectWorkbookForViewer deployed viewerClearances (evalWorkbookFull k title secs cs)) = true := by
  unfold verifyRedactedWorkbook projectWorkbookForViewer evalWorkbookFull
  dsimp only
  have hSchedLen := evalWorkbookSchedule_length k cs (sectionEnvironment secs (secs.length + 1))
  refine verifyExportedSchedule_complete_aux k deployed_bounded viewerClearances
    ((evalWorkbookSchedule k cs (sectionEnvironment secs (secs.length + 1))).map (cellSaltedCommitment deployed))
    cs 0 (sectionEnvironment secs (secs.length + 1)) ?_ ?_ ?_
  · simp [hSchedLen]
  · simpa [hSchedLen] using hLen
  · intro j hj
    have hjEval : j < (evalWorkbookSchedule k cs (sectionEnvironment secs (secs.length + 1))).length := by
      rwa [hSchedLen]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjEval]
/-- **256-Bit Merkle Commitment Binding (`verifyRedactedWorkbook_binds_or_collides`)**. -/
theorem verifyRedactedWorkbook_binds_or_collides (rwb : RedactedWorkbook) {o o' : Opening}
    (h1 : opens deployed o rwb.merkleRoot = true)
    (h2 : opens deployed o' rwb.merkleRoot = true)
    (hSize : o.size = o'.size) (hIdx : o.index = o'.index) :
    opens deployed o rwb.merkleRoot = true ∧
      (o.value = o'.value ∨
        CollisionAmong deployed (fun m => m ∈ openingPreimages deployed o ++ openingPreimages deployed o')) :=
  ⟨h1, opens_binds_scoped deployed_bounded h1 h2 hSize hIdx⟩
inductive WorkbookTurn where
  | stepEdit (edit : WorkbookEdit)
  | scrubCell (cellKey : String) (viewEdit : ViewEdit)
  deriving DecidableEq, Repr
def stepWorkbookTurn (k : CellKernel) (wb : Workbook) : WorkbookTurn → Workbook
  | .stepEdit edit => evalWorkbookIncremental k wb edit
  | .scrubCell cellKey viewEdit =>
    match scrubWorkbookCell k wb cellKey viewEdit with
    | .ok (wb', _) => wb'
    | .error _ => wb
def runWorkbookTurns (k : CellKernel) : Workbook → List WorkbookTurn → Workbook
  | wb, [] => wb
  | wb, t :: ts => runWorkbookTurns k (stepWorkbookTurn k wb t) ts
def ValidWorkbookState (k : CellKernel) (wb : Workbook) : Prop :=
  let rawCells := wb.cells.map CachedWorkbookCell.entry
  checkWorkbookDag rawCells = true ∧
  (∀ w ∈ rawCells, WellFormedCellReads w) ∧
  wb = evalWorkbookFull k wb.title wb.sections rawCells
theorem checkWorkbookDag_applyEdit (edit : WorkbookEdit) (cs : List WorkbookCell) :
    checkWorkbookDag (cs.map (applyEditToCell edit)) = checkWorkbookDag cs := by
  have hKeys : (cs.map (applyEditToCell edit)).map WorkbookCell.cellKey = cs.map WorkbookCell.cellKey := by
    rw [List.map_map]; congr 1; funext w; exact applyEditToCell_cellKey edit w
  have hDagEq : checkNotebookDag ((cs.map (applyEditToCell edit)).map effectiveReactiveCell) =
      checkNotebookDag (cs.map effectiveReactiveCell) := by
    cases edit with
    | editSection sk md blks =>
      have hId : cs.map (applyEditToCell (.editSection sk md blks)) = cs := by
        clear hKeys; induction cs with | nil => rfl | cons x xs ih => exact congrArg (x :: ·) ih
      rw [hId]
    | editCellBody tid newAst newBody =>
      have hMapEq : (cs.map (applyEditToCell (.editCellBody tid newAst newBody))).map effectiveReactiveCell =
          Obend.Doc.Reactive.applyEdit ⟨tid, newBody⟩ (cs.map effectiveReactiveCell) := by
        simp only [Obend.Doc.Reactive.applyEdit, List.map_map]; congr 1; funext w
        dsimp only [Function.comp_def, applyEditToCell, Obend.Doc.Reactive.editCell, effectiveReactiveCell]
        split <;> simp [allCitedKeys]
      rw [hMapEq]; exact Obend.Doc.Reactive.checkNotebookDag_edit ⟨tid, newBody⟩ (cs.map effectiveReactiveCell)
  unfold checkWorkbookDag; rw [hKeys, hDagEq]
theorem wellFormedCellReads_applyEdit (edit : WorkbookEdit) {w : WorkbookCell}
    (hWf : WellFormedCellReads w) : WellFormedCellReads (applyEditToCell edit w) := by
  intro ck hMem
  rw [applyEditToCell_allCitedKeys]
  rw [applyEditToCell_reads] at hMem
  exact hWf ck hMem
private theorem evalWorkbookSchedule_map_struct (k : CellKernel) (cellKey : String) (sc' : StructuredCell)
    (rawCs : List WorkbookCell) (env0 : Environment) :
    (evalWorkbookSchedule k rawCs env0).map (fun c =>
      if c.entry.cellKey == cellKey then { c with entry := { c.entry with structured := sc' } } else c) =
    evalWorkbookSchedule k (rawCs.map fun w =>
      if w.cellKey == cellKey then { w with structured := sc' } else w) env0 := by
  induction rawCs generalizing env0 with
  | nil => rfl
  | cons w ws ih =>
    have hEffEq : effectiveReactiveCell (if w.cellKey == cellKey then { w with structured := sc' } else w) =
        effectiveReactiveCell w := by split <;> rfl
    have hEvalW : evalWorkbookCell k (if w.cellKey == cellKey then { w with structured := sc' } else w) env0 =
        evalWorkbookCell k w env0 := by unfold evalWorkbookCell; rw [hEffEq]
    have hPubW : publishWorkbookCell (if w.cellKey == cellKey then { w with structured := sc' } else w)
        (evalWorkbookCell k w env0) env0 = publishWorkbookCell w (evalWorkbookCell k w env0) env0 := by
      unfold publishWorkbookCell; rw [hEffEq]
    simp only [evalWorkbookSchedule, List.map_cons, hEvalW, hPubW, ih]
    congr 1; split <;> rfl
/-- **Multi-Turn Workbook Trace Soundness (`stepWorkbookTurn_preserves_valid`)**. -/
theorem stepWorkbookTurn_preserves_valid (k : CellKernel) (wb : Workbook) (t : WorkbookTurn)
    (hValid : ValidWorkbookState k wb) :
    ValidWorkbookState k (stepWorkbookTurn k wb t) := by
  obtain ⟨hDag, hWf, hFull⟩ := hValid
  cases t with
  | stepEdit edit =>
    dsimp only [stepWorkbookTurn]
    rw [hFull, evalWorkbookIncremental_eq_full k wb.title wb.sections _ hWf edit]
    dsimp only [ValidWorkbookState, evalWorkbookFull]
    rw [evalWorkbookSchedule_entries]
    refine ⟨by rw [checkWorkbookDag_applyEdit]; exact hDag, ?_, rfl⟩
    intro w' hw'; rw [List.mem_map] at hw'; obtain ⟨w, hwMem, rfl⟩ := hw'
    exact wellFormedCellReads_applyEdit edit (hWf w hwMem)
  | scrubCell cellKey viewEdit =>
    dsimp only [stepWorkbookTurn]; unfold scrubWorkbookCell
    cases hFind : wb.cells.find? (fun c => c.entry.cellKey == cellKey) with
    | none => exact ⟨hDag, hWf, hFull⟩
    | some targetCached =>
      dsimp only
      cases hScrub : (lensForKind targetCached.entry.structured.kind).scrub targetCached.entry.structured viewEdit with
      | error _ => exact ⟨hDag, hWf, hFull⟩
      | ok res =>
        rcases res with ⟨sc', patch⟩
        dsimp only
        let rawCs := wb.cells.map CachedWorkbookCell.entry
        let updateStruct : WorkbookCell → WorkbookCell := fun w =>
          if w.cellKey == cellKey then { w with structured := sc' } else w
        let seededCells := rawCs.map updateStruct
        have hWbSeededEq :
            ({ wb with cells := wb.cells.map fun c =>
                if c.entry.cellKey == cellKey then { c with entry := { c.entry with structured := sc' } }
                else c } : Workbook) =
            evalWorkbookFull k wb.title wb.sections seededCells := by
          have hCellsEq : wb.cells = evalWorkbookSchedule k rawCs
              (sectionEnvironment wb.sections (wb.sections.length + 1)) := by
            have := congrArg Workbook.cells hFull; simpa [evalWorkbookFull, rawCs] using this
          cases wb with
          | mk t secs cs =>
            dsimp only [evalWorkbookFull, seededCells, updateStruct] at hCellsEq ⊢
            congr 1
            rw [hCellsEq]
            exact evalWorkbookSchedule_map_struct k cellKey sc' _ _
        have hWfSeeded : ∀ w ∈ seededCells, WellFormedCellReads w := by
          intro w' hw'; simp only [seededCells, List.mem_map] at hw'
          obtain ⟨w, hwMem, rfl⟩ := hw'
          intro ck hCk
          have hReads : (updateStruct w).reactive.reads = w.reactive.reads := by
            dsimp only [updateStruct]; split <;> rfl
          have hCites : allCitedKeys (updateStruct w) = allCitedKeys w := by
            dsimp only [updateStruct]; split <;> rfl
          rw [hCites]; exact hWf w hwMem ck (hReads ▸ hCk)
        have hDagSeeded : checkWorkbookDag seededCells = true := by
          have hKeys : seededCells.map WorkbookCell.cellKey = rawCs.map WorkbookCell.cellKey := by
            simp only [seededCells, List.map_map]; congr 1; funext w
            dsimp only [Function.comp_def, updateStruct]; split <;> rfl
          have hEffs : seededCells.map effectiveReactiveCell = rawCs.map effectiveReactiveCell := by
            simp only [seededCells, List.map_map]; congr 1; funext w
            dsimp only [Function.comp_def, updateStruct]; split <;> rfl
          unfold checkWorkbookDag; rw [hKeys, hEffs]; exact hDag
        let newBody : CellBody := match dataToLiteralInt? viewEdit.newValue with
          | some lit => [[{ op := .literal, arg := lit }]]
          | none => targetCached.entry.reactive.body
        let editAct := WorkbookEdit.editCellBody targetCached.entry.reactive.id sc'.ast newBody
        rw [hWbSeededEq, evalWorkbookIncremental_eq_full k wb.title wb.sections seededCells hWfSeeded editAct]
        dsimp only [ValidWorkbookState, evalWorkbookFull]
        rw [evalWorkbookSchedule_entries]
        refine ⟨by rw [checkWorkbookDag_applyEdit]; exact hDagSeeded, ?_, rfl⟩
        intro w' hw'; rw [List.mem_map] at hw'; obtain ⟨w, hwMem, rfl⟩ := hw'
        exact wellFormedCellReads_applyEdit editAct (hWfSeeded w hwMem)
theorem runWorkbookTurns_preserves_valid (k : CellKernel) (wb : Workbook) (turns : List WorkbookTurn)
    (hValid : ValidWorkbookState k wb) :
    ValidWorkbookState k (runWorkbookTurns k wb turns) := by
  induction turns generalizing wb with
  | nil => exact hValid
  | cons t ts ih => exact ih _ (stepWorkbookTurn_preserves_valid k wb t hValid)
end Obend.Doc.WorkbookEngine
end
