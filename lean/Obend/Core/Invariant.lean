module
/- Lexical invariants for the partial Objective Bend edition. These proofs do
not assert totality, ownership of native effects, or source/heap adequacy. -/
public import Obend.Tactic.Cases
public import Obend.Core.TermTraverse
public import Obend.Core.Machine
@[expose] public section
namespace Obend.Core.Invariant
open Obend.Core.Term
open Obend.Core.Machine
set_option autoImplicit false

/-- All free indices have lexical bindings. A successor branch binds the
predecessor; a lambda binds its argument. Recursive self is bound by the heap
machine, rather than counted as a free index of the source Fix constructor. -/
inductive Scoped : Nat → Term → Prop where
  | hole {n k : Nat} {σ : List Term} : (∀ t ∈ σ, Scoped n t) → Scoped n (.hole k σ)
  | bound {n i : Nat} : i < n → Scoped n (.bound i)
  | lam {n : Nat} {body : Term} : Scoped (n+1) body → Scoped n (.lam body)
  | app {n : Nat} {f a : Term} : Scoped n f → Scoped n a → Scoped n (.app f a)
  | mix {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.mix a b)
  | fix {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.fix a b)
  | specification {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.specification a b)
  | prototype {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.prototype a b)
  | reflect {n : Nat} {t : Term} : Scoped n t → Scoped n (.reflect t)
  | metadata {n : Nat} {t : Term} : Scoped n t → Scoped n (.metadata t)
  | project {n : Nat} {t : Term} : Scoped n t → Scoped n (.project t)
  | natural {n : Nat} (v : Nat) : Scoped n (.nat v)
  | boolean {n : Nat} (v : Bool) : Scoped n (.boolean v)
  | label {n : Nat} (v : String) : Scoped n (.label v)
  | binary {n : Nat} {p : Primitive} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.binary p a b)
  | extend {n : Nat} {t : Term} {fs : List (String × Term)} :
      Scoped n t → (∀ f ∈ fs, Scoped n f.2) → Scoped n (.extend t fs)
  | record {n : Nat} {fs : List (String × Term)} :
      (∀ f ∈ fs, Scoped n f.2) → Scoped n (.record fs)
  | get {n : Nat} {t : Term} {name : String} : Scoped n t → Scoped n (.get t name)
  | condition {n : Nat} {t z s : Term} : Scoped n t → Scoped n z → Scoped (n+1) s → Scoped n (.ifZero t z s)
  | inject {n : Nat} {tag : String} {p : Term} : Scoped n p → Scoped n (.inject tag p)
  | case {n : Nat} {t : Term} {arms : List (String × Term)} :
      Scoped n t → (∀ arm ∈ arms, Scoped (n+1) arm.2) → Scoped n (.case t arms)
  | ifBool {n : Nat} {c t f : Term} : Scoped n c → Scoped n t → Scoped n f → Scoped n (.ifBool c t f)
  | perform {n : Nat} {plan : Term} : Scoped n plan → Scoped n (.perform plan)
  | done {n : Nat} {value : Term} : Scoped n value → Scoped n (.done value)

@[simp] theorem scoped_hole_iff (n k : Nat) (σ : List Term) :
    Scoped n (.hole k σ) ↔ ∀ t ∈ σ, Scoped n t := by
  constructor
  · intro h; obend_cases h with []
  · exact Scoped.hole

@[simp] theorem scoped_bound_iff (n : Nat) (i : Nat) :
    Scoped n (.bound i) ↔ i < n := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .bound h

@[simp] theorem scoped_lam_iff (n : Nat) (body : Term) :
    Scoped n (.lam body) ↔ Scoped (n+1) body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .lam h

@[simp] theorem scoped_app_iff (n : Nat) (a b : Term) :
    Scoped n (.app a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .app h.1 h.2

@[simp] theorem scoped_mix_iff (n : Nat) (a b : Term) :
    Scoped n (.mix a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .mix h.1 h.2

@[simp] theorem scoped_fix_iff (n : Nat) (a b : Term) :
    Scoped n (.fix a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .fix h.1 h.2

@[simp] theorem scoped_specification_iff (n : Nat) (a b : Term) :
    Scoped n (.specification a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .specification h.1 h.2

@[simp] theorem scoped_prototype_iff (n : Nat) (a b : Term) :
    Scoped n (.prototype a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .prototype h.1 h.2

@[simp] theorem scoped_reflect_iff (n : Nat) (body : Term) :
    Scoped n (.reflect body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .reflect h

@[simp] theorem scoped_metadata_iff (n : Nat) (body : Term) :
    Scoped n (.metadata body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .metadata h

@[simp] theorem scoped_project_iff (n : Nat) (body : Term) :
    Scoped n (.project body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .project h

@[simp] theorem scoped_binary_iff (n : Nat) (p : Primitive) (a b : Term) :
    Scoped n (.binary p a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .binary h.1 h.2

@[simp] theorem scoped_extend_iff (n : Nat) (body : Term) (fields : List (String × Term)) :
    Scoped n (.extend body fields) ↔ Scoped n body ∧ ∀ field ∈ fields, Scoped n field.2 := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .extend h.1 h.2

@[simp] theorem scoped_record_iff (n : Nat) (fields : List (String × Term)) :
    Scoped n (.record fields) ↔ ∀ field ∈ fields, Scoped n field.2 := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .record h

@[simp] theorem scoped_get_iff (n : Nat) (body : Term) (name : String) :
    Scoped n (.get body name) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .get h

@[simp] theorem scoped_condition_iff (n : Nat) (v z b : Term) :
    Scoped n (.ifZero v z b) ↔ Scoped n v ∧ Scoped n z ∧ Scoped (n+1) b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption,by assumption⟩
  · intro h; exact .condition h.1 h.2.1 h.2.2

@[simp] theorem scoped_inject_iff (n : Nat) (tag : String) (p : Term) :
    Scoped n (.inject tag p) ↔ Scoped n p := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .inject h

@[simp] theorem scoped_case_iff (n : Nat) (t : Term) (arms : List (String × Term)) :
    Scoped n (.case t arms) ↔ Scoped n t ∧ ∀ arm ∈ arms, Scoped (n+1) arm.2 := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .case h.1 h.2

@[simp] theorem scoped_ifBool_iff (n : Nat) (c t f : Term) :
    Scoped n (.ifBool c t f) ↔ Scoped n c ∧ Scoped n t ∧ Scoped n f := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption,by assumption⟩
  · intro h; exact .ifBool h.1 h.2.1 h.2.2

@[simp] theorem scoped_perform_iff (n : Nat) (plan : Term) :
    Scoped n (.perform plan) ↔ Scoped n plan := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .perform h

@[simp] theorem scoped_done_iff (n : Nat) (value : Term) :
    Scoped n (.done value) ↔ Scoped n value := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .done h

/-- The syntax encoding's binder has exactly the source lexical policy. -/
theorem shape_scoped_bind {Tag : Type} (n : Nat) (body : Traverse.Tree Tag) :
    Traverse.Tree.Scoped n (.bind body) ↔ Traverse.Tree.Scoped (n+1) body := by
  simp only [Traverse.Tree.Scoped, Traverse.Tree.All]
  apply Traverse.Tree.all_congr
  intro i; cases i <;> simp +arith

theorem shape_forall_true {α : Type} : (∀ _ : α, True) ↔ True := ⟨fun _ => trivial, fun _ _ => trivial⟩

theorem shape_scoped_node {Tag : Type} (n : Nat) (tag : Tag) (children : List (Traverse.Tree Tag)) :
    Traverse.Tree.Scoped n (.node tag children) ↔ ∀ c ∈ children, Traverse.Tree.Scoped n c := by
  simp only [Traverse.Tree.Scoped, Traverse.Tree.All]

/-- The machine's lexical invariant agrees with the generic syntax traversal. -/
theorem scoped_encode_iff (n : Nat) (t : Term) : Scoped n t ↔ TermTraverse.Scoped n t := by
  obend_cases t with []
  all_goals simp only [
    TermTraverse.Scoped, TermTraverse.encode, shape_scoped_bind, shape_scoped_node,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, shape_forall_true, and_true]
  all_goals try simp only [Prod.forall]
  all_goals first
    | (constructor <;> intro h <;> first | trivial | constructor; done)
    | (simp only [Traverse.Tree.Scoped, Traverse.Tree.All]; done)
    | (repeat first
        | apply and_congr
        | exact scoped_encode_iff _ _
        | (apply forall_congr'; intro a; apply forall_congr'; intro b
           apply forall_congr'; intro hf
           exact scoped_encode_iff _ b)
        | (apply forall_congr'; intro a; apply forall_congr'; intro ha
           exact scoped_encode_iff _ a))
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have hlist := List.sizeOf_lt_of_mem hf
       simp at hlist
       omega)

/-- A renaming that fixes every index below `n` fixes a term scoped under `n`. (Moved from
`Core.Proofs.Adequacy` on 2026-10-30, where it was private; `Core.Proofs.Substitution` needs it too.) -/
theorem scoped_rename_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Nat) (hf : ∀ i, i < n → f i = i) : term.rename f = term := by
  exact TermTraverse.scoped_rename_identity term n ((scoped_encode_iff n term).mp h) f hf

 theorem scoped_rename {n : Nat} {t : Term} (h : Scoped n t)
    (f : Nat → Nat) (m : Nat) (hf : ∀ i, i < n → f i < m) :
    Scoped m (t.rename f) := by
  exact (scoped_encode_iff m _).mpr
    (TermTraverse.scoped_rename t n m ((scoped_encode_iff n t).mp h) f hf)

 theorem scoped_weaken {n : Nat} {t : Term} (h : Scoped n t) :
    Scoped (n+1) (t.rename Nat.succ) :=
  scoped_rename h Nat.succ (n+1) (fun _ hi => Nat.succ_lt_succ hi)

 theorem scoped_substitute {n : Nat} {t : Term} (h : Scoped n t)
    (substitution : Nat → Term) (m : Nat)
    (hs : ∀ i, i < n → Scoped m (substitution i)) : Scoped m (t.substitute substitution) := by
  exact (scoped_encode_iff m _).mpr
    (TermTraverse.scoped_substitute t n m ((scoped_encode_iff n t).mp h) substitution
      (fun i hi => (scoped_encode_iff m _).mp (hs i hi)))

 theorem scoped_mixBody {n : Nat} {lower upper : Term}
    (hl : Scoped n lower) (hu : Scoped n upper) : Scoped n (mixBody lower upper) := by
  apply Scoped.lam
  apply Scoped.lam
  apply Scoped.app
  · exact .app (scoped_rename hu (fun i => i+2) (n+1+1)
      (fun i hi => Nat.add_lt_add_right hi 2)) (.bound (by omega))
  · exact .app (.app (scoped_rename hl (fun i => i+2) (n+1+1)
      (fun i hi => Nat.add_lt_add_right hi 2)) (.bound (by omega))) (.bound (by omega))

/-- Unlike a tree-unfolding predicate, this permits a thunk to capture itself
and permits mutually reachable cells. It only requires allocated addresses. -/
def EnvironmentValid (bound : Nat) (environment : Environment) : Prop :=
  ∀ address ∈ environment, address < bound

def RuntimeValueValid (bound : Nat) : RuntimeValue → Prop
  | .closure body environment => Scoped (environment.length+1) body ∧ EnvironmentValid bound environment
  | .natural _ | .boolean _ | .label _ => True
  | .record fields => ∀ field ∈ fields, field.2 < bound
  | .specification metadata extension => metadata < bound ∧ extension < bound
  | .prototype specification target => specification < bound ∧ target < bound
  | .variant _ payload => payload < bound

 theorem environmentValid_mono {a b : Nat} {environment : Environment}
    (h : EnvironmentValid a environment) (hab : a ≤ b) : EnvironmentValid b environment :=
  fun address member => Nat.lt_of_lt_of_le (h address member) hab

 theorem environmentValid_tied {bound : Nat} {environment : Environment}
    (h : EnvironmentValid bound environment) : EnvironmentValid (bound+1) (bound::environment) := by
  intro address member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (h address member)

def ClosureValid (bound : Nat) (closure : Closure) : Prop :=
  Scoped closure.environment.length closure.term ∧ EnvironmentValid bound closure.environment

def CellValid (bound : Nat) : Cell → Prop
  | .suspended origin | .evaluating origin => ClosureValid bound origin
  | .cached origin value => ClosureValid bound origin ∧ RuntimeValueValid bound value

def FrameValid (bound : Nat) : Frame → Prop
  | .argument term environment | .binaryLeft _ term environment => ClosureValid bound ⟨term,environment⟩
  | .update address => address < bound
  | .field _ | .reflect | .metadata | .project => True
  | .extend fields environment => EnvironmentValid bound environment ∧ ∀ field ∈ fields, Scoped environment.length field.2
  | .condition zero successorBody environment => EnvironmentValid bound environment ∧
      Scoped environment.length zero ∧ Scoped (environment.length+1) successorBody
  | .binaryRight _ value => RuntimeValueValid bound value
  | .case arms environment => EnvironmentValid bound environment ∧
      ∀ arm ∈ arms, Scoped (environment.length+1) arm.2
  | .ifBool whenTrue whenFalse environment => EnvironmentValid bound environment ∧
      Scoped environment.length whenTrue ∧ Scoped environment.length whenFalse

def ControlValid (bound : Nat) : Control → Prop
  | .evaluate term environment => ClosureValid bound ⟨term,environment⟩
  | .enter address | .blackhole address => address < bound
  | .returned value | .complete value => RuntimeValueValid bound value
  | .refused _ => True
  | .yielded plan => plan < bound

def LexicalInvariant (state : State) : Prop :=
  (∀ (address : Nat) (cell : Cell), state.heap[address]? = some cell → CellValid state.heap.size cell) ∧
    ControlValid state.heap.size state.control ∧ ∀ frame ∈ state.stack, FrameValid state.heap.size frame

 theorem initial_lexicalInvariant {term : Term} (closed : Scoped 0 term) :
    LexicalInvariant (initial term) := by
  refine ⟨?_,⟨closed,?_⟩,?_⟩
  · intro address cell found; simp [initial] at found
  · intro address member; simp at member
  · intro frame member; simp [initial] at member

 theorem runtimeValueValid_mono {a b : Nat} {value : RuntimeValue}
    (h : RuntimeValueValid a value) (hab : a ≤ b) : RuntimeValueValid b value := by
  cases value with
  | closure body environment => exact ⟨h.1,environmentValid_mono h.2 hab⟩
  | natural _ | boolean _ | label _ => trivial
  | record fields => exact fun field member => Nat.lt_of_lt_of_le (h field member) hab
  | specification _ _ | prototype _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab,Nat.lt_of_lt_of_le h.2 hab⟩
  | variant _ _ => exact Nat.lt_of_lt_of_le h hab

 theorem closureValid_mono {a b : Nat} {closure : Closure}
    (h : ClosureValid a closure) (hab : a ≤ b) : ClosureValid b closure :=
  ⟨h.1,environmentValid_mono h.2 hab⟩

 theorem cellValid_mono {a b : Nat} {cell : Cell}
    (h : CellValid a cell) (hab : a ≤ b) : CellValid b cell := by
  cases cell with
  | suspended _ | evaluating _ => exact closureValid_mono h hab
  | cached _ _ => exact ⟨closureValid_mono h.1 hab,runtimeValueValid_mono h.2 hab⟩

 theorem frameValid_mono {a b : Nat} {frame : Frame}
    (h : FrameValid a frame) (hab : a ≤ b) : FrameValid b frame := by
  cases frame with
  | argument _ _ | binaryLeft _ _ _ => exact closureValid_mono h hab
  | update _ => exact Nat.lt_of_lt_of_le h hab
  | field _ | reflect | metadata | project => trivial
  | extend _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | condition _ _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | binaryRight _ _ => exact runtimeValueValid_mono h hab
  | case _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | ifBool _ _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩

 theorem controlValid_mono {a b : Nat} {control : Control}
    (h : ControlValid a control) (hab : a ≤ b) : ControlValid b control := by
  cases control with
  | evaluate _ _ => exact closureValid_mono h hab
  | enter _ | blackhole _ => exact Nat.lt_of_lt_of_le h hab
  | returned _ | complete _ => exact runtimeValueValid_mono h hab
  | refused _ => trivial
  | yielded _ => exact Nat.lt_of_lt_of_le h hab

abbrev HeapValid (heap : Array Cell) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellValid heap.size cell

 theorem heapValid_push {heap : Array Cell} {cell : Cell} (h : HeapValid heap)
    (hc : CellValid (heap.size+1) cell) : HeapValid (heap.push cell) := by
  intro address value found
  rw [Array.getElem?_push] at found
  split at found
  · cases found; simpa using hc
  · exact cellValid_mono (h address value found) (by simp)

 theorem heapValid_set {heap : Array Cell} {address : Nat} {cell : Cell}
    (h : HeapValid heap) (hc : CellValid heap.size cell) : HeapValid (heap.set! address cell) := by
  intro index value found
  by_cases he : address < heap.size
  · by_cases same : index = address
    · subst index
      simp [Array.set!,Array.setIfInBounds,he] at found
      subst value; simpa [Array.set!] using hc
    · have old : heap[index]? = some value := by simpa [Array.set!,Array.setIfInBounds,he,same,Ne.symm same] using found
      simpa [Array.set!] using h index value old
  · simpa [Array.set!,Array.setIfInBounds,he] using h index value (by simpa [Array.set!,Array.setIfInBounds,he] using found)

 theorem allocateFields_valid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2) :
    HeapValid (allocateFields heap environment fields).1 ∧
      ∀ field ∈ (allocateFields heap environment fields).2,
        field.2 < (allocateFields heap environment fields).1.size := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      HeapValid pair.1 → EnvironmentValid pair.1.size environment →
      (∀ field ∈ pair.2, field.2 < pair.1.size) →
      (∀ field ∈ fields, Scoped environment.length field.2) →
      let result := fields.foldl (fun prior field =>
        (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) pair
      HeapValid result.1 ∧ ∀ field ∈ result.2, field.2 < result.1.size := by
    intro fs
    induction fs with
    | nil => intro pair hp he hr hs; exact ⟨hp,hr⟩
    | cons field fs ih =>
      intro pair hp he hr hs
      apply ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)
      · apply heapValid_push hp
        exact ⟨hs field (by simp),environmentValid_mono he (by simp)⟩
      · exact environmentValid_mono he (by simp)
      · intro f member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp
        · exact Nat.lt_of_lt_of_le (hr f member) (by simp)
      · intro f member; exact hs f (by simp [member])
  obtain ⟨hp,hr⟩ := loop fields (heap,[]) hh he (by simp) hf
  refine ⟨hp,?_⟩
  intro f member
  exact hr f (List.mem_reverse.mp member)

 theorem allocateFields_cellValid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2)
    (address : Nat) (cell : Cell) (found : (allocateFields heap environment fields).1[address]? = some cell) :
    CellValid (allocateFields heap environment fields).1.size cell :=
  (allocateFields_valid hh he hf).1 address cell found

 theorem allocateFields_addressValid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2)
    (field : String × Address) (member : field ∈ (allocateFields heap environment fields).2) :
    field.2 < (allocateFields heap environment fields).1.size :=
  (allocateFields_valid hh he hf).2 field member

 theorem scalarValue_valid {term : Term} {value : RuntimeValue} (bound : Nat)
    (h : scalarValue term = some value) : RuntimeValueValid bound value := by
  cases term <;> simp [scalarValue] at h
  all_goals cases h; trivial

/-- Origin is lexical source plus capture vector, retained even while a cell is
being evaluated or after its result has been memoized. -/
def cellOrigin : Cell → Closure
  | .suspended origin | .evaluating origin | .cached origin _ => origin

/-- No transition can retarget an allocated thunk. This permits new allocations
and memoization; it forbids changing either its source or its lexical captures. -/
def PreservesOrigins (before after : Array Cell) : Prop :=
  before.size ≤ after.size ∧ ∀ (address : Nat) (cell : Cell), before[address]? = some cell →
    ∃ (next : Cell), after[address]? = some next ∧ cellOrigin next = cellOrigin cell

 theorem preservesOrigins_refl (heap : Array Cell) : PreservesOrigins heap heap :=
  ⟨Nat.le_refl _,fun _ cell found => ⟨cell,found,rfl⟩⟩

 theorem preservesOrigins_trans {a b c : Array Cell}
    (hab : PreservesOrigins a b) (hbc : PreservesOrigins b c) : PreservesOrigins a c := by
  constructor
  · exact Nat.le_trans hab.1 hbc.1
  · intro address cell found
    obtain ⟨middle, hm, ho⟩ := hab.2 address cell found
    obtain ⟨next, hn, hon⟩ := hbc.2 address middle hm
    exact ⟨next,hn,hon.trans ho⟩

 theorem preservesOrigins_push (heap : Array Cell) (cell : Cell) :
    PreservesOrigins heap (heap.push cell) := by
  constructor
  · simp
  · intro address original found
    have hbound : address < heap.size := by
      exact (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨original,by simpa [Array.getElem?_push, Nat.ne_of_lt hbound] using found,rfl⟩

 theorem preservesOrigins_set {heap : Array Cell} {address : Nat} {old next : Cell}
    (found : heap[address]? = some old) (origin : cellOrigin next = cellOrigin old) :
    PreservesOrigins heap (heap.set! address next) := by
  have hbound : address < heap.size := (Array.getElem?_eq_some_iff.mp found).1
  constructor
  · simp [Array.set!]
  · intro index original hi
    by_cases same : index = address
    · subst index
      have eq : original = old := Option.some.inj (hi.symm.trans found)
      subst original
      exact ⟨next,by simp [Array.set!,hbound],origin⟩
    · exact ⟨original,by simpa [Array.set!,same,Ne.symm same] using hi,rfl⟩

 theorem allocateFields_preservesOrigins (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) :
    PreservesOrigins heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PreservesOrigins pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact preservesOrigins_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using preservesOrigins_trans (preservesOrigins_push pair.1 (.suspended ⟨field.2,environment⟩)) (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

 theorem allocateFields_size_mono (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) : heap.size ≤ (allocateFields heap environment fields).1.size :=
  (allocateFields_preservesOrigins heap environment fields).1

/-- Every raw transition, including all terminal, refusal and blackhole cases,
preserves origin at every previously allocated address. No reachability or
adequacy oracle is a premise. -/
 theorem stepRaw_preservesOrigins (state : State) :
    PreservesOrigins state.heap (stepRaw state).heap := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact preservesOrigins_refl _
    | exact preservesOrigins_push _ _
    | exact preservesOrigins_trans (preservesOrigins_push _ _) (preservesOrigins_push _ _)
    | exact allocateFields_preservesOrigins _ _ _
    | apply preservesOrigins_set; assumption; rfl

 theorem environmentValid_lookup {bound index address : Nat} {environment : Environment}
    (h : EnvironmentValid bound environment) (found : environment[index]? = some address) :
    address < bound := h address (List.mem_of_getElem? found)

/-! ### `stepRaw` keeps the lexical invariant, one lemma per transition

Each lemma fixes the control (and, for a return, the top frame) and runs the same discharge,
`lexical_unfold` and `lexical_discharge`; `stepRaw_lexicalInvariant` dispatches on the state. -/

set_option hygiene false in
/-- Open `invariant` and unfold `stepRaw`; the caller then fixes the transition by `simp only` at
its control (and for a return its top frame) and closes it with `lexical_discharge`. -/
macro "lexical_unfold" : tactic => `(tactic| (
  rcases invariant with ⟨hh,hc,hs⟩
  have stackHead : ∀ frame rest, state.stack = frame::rest → FrameValid state.heap.size frame := by
    intro frame rest eq
    exact hs frame (eq ▸ List.mem_cons_self)
  have hp := stepRaw_preservesOrigins state
  have hg : state.heap.size ≤ (stepRaw state).heap.size := hp.1
  unfold stepRaw))

set_option hygiene false in
/-- Split what is left of the transition and discharge `LexicalInvariant` of each result. -/
macro "lexical_discharge" : tactic => `(tactic| (
  repeat' first | split
  all_goals try dsimp only at *
  all_goals try (have headValid := stackHead _ _ (by assumption))
  all_goals simp_all only [LexicalInvariant, ControlValid, ClosureValid,
    CellValid.eq_1, CellValid.eq_2, CellValid.eq_3,
    RuntimeValueValid.eq_1, RuntimeValueValid.eq_2, RuntimeValueValid.eq_3, RuntimeValueValid.eq_4, RuntimeValueValid.eq_5, RuntimeValueValid.eq_6, RuntimeValueValid.eq_7,
    FrameValid.eq_1, FrameValid.eq_2, FrameValid.eq_3, FrameValid.eq_4, FrameValid.eq_5, FrameValid.eq_6, FrameValid.eq_7, FrameValid.eq_8, FrameValid.eq_9, FrameValid.eq_10, FrameValid.eq_11, FrameValid.eq_12,
    scoped_bound_iff, scoped_lam_iff, scoped_app_iff,
    scoped_mix_iff, scoped_fix_iff, scoped_specification_iff, scoped_prototype_iff,
    scoped_reflect_iff, scoped_metadata_iff, scoped_project_iff, scoped_binary_iff,
    scoped_extend_iff, scoped_record_iff, scoped_get_iff, scoped_condition_iff,
    scoped_inject_iff, scoped_case_iff, scoped_ifBool_iff, scoped_perform_iff, scoped_done_iff,
    List.mem_cons, List.not_mem_nil, false_or, or_false, Array.size_push]
  all_goals try (have lookupValid := environmentValid_lookup hc.2 (by assumption))
  all_goals try (have allocationValid := allocateFields_valid hh hc.2 hc.1)
  all_goals try (have allocationValid := allocateFields_valid hh headValid.1 headValid.2)
  all_goals grind [heapValid_push,heapValid_set, allocateFields_cellValid, allocateFields_addressValid, allocateFields_size_mono, scalarValue_valid,
    ClosureValid, CellValid, FrameValid, RuntimeValueValid, EnvironmentValid, environmentValid_lookup, Scoped.app, Scoped.bound, Scoped.natural, Scoped.boolean, Scoped.label, List.length_cons, List.mem_of_getElem?, List.mem_of_find?_eq_some,
    environmentValid_mono,environmentValid_tied,cellValid_mono,frameValid_mono,
    runtimeValueValid_mono,scoped_weaken,scoped_mixBody]
  ))

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_hole {state : State} {environment : Environment} {n : Nat} {σ : List Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.hole n σ) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_bound {state : State} {environment : Environment} {index : Nat}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.bound index) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_lam {state : State} {environment : Environment} {body : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.lam body) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_app {state : State} {environment : Environment} {function : Term} {argument : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.app function argument) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_mix {state : State} {environment : Environment} {lower : Term} {upper : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.mix lower upper) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_fix {state : State} {environment : Environment} {spec : Term} {inherited : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.fix spec inherited) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_specification {state : State} {environment : Environment} {descriptor : Term} {extension : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.specification descriptor extension) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_prototype {state : State} {environment : Environment} {spec : Term} {target : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.prototype spec target) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_reflect {state : State} {environment : Environment} {term : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.reflect term) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_metadata {state : State} {environment : Environment} {term : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.metadata term) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_project {state : State} {environment : Environment} {term : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.project term) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_nat {state : State} {environment : Environment} {n : Nat}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.nat n) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_boolean {state : State} {environment : Environment} {value : Bool}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.boolean value) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_label {state : State} {environment : Environment} {name : String}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.label name) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_binary {state : State} {environment : Environment} {primitive : Primitive} {left : Term} {right : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.binary primitive left right) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_extend {state : State} {environment : Environment} {inherited : Term} {fields : List (String × Term)}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.extend inherited fields) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_record {state : State} {environment : Environment} {fields : List (String × Term)}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.record fields) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_get {state : State} {environment : Environment} {target : Term} {name : String}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.get target name) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_ifZero {state : State} {environment : Environment} {value : Term} {zero : Term} {successorBody : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.ifZero value zero successorBody) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_inject {state : State} {environment : Environment} {tag : String} {payload : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.inject tag payload) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_case {state : State} {environment : Environment} {scrutinee : Term} {arms : List (String × Term)}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.case scrutinee arms) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_ifBool {state : State} {environment : Environment} {condition : Term} {whenTrue : Term} {whenFalse : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.ifBool condition whenTrue whenFalse) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_perform {state : State} {environment : Environment} {plan : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.perform plan) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_evaluate_done {state : State} {environment : Environment} {value : Term}
    (invariant : LexicalInvariant state) (current : state.control = .evaluate (.done value) environment) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_argument {state : State} {value : RuntimeValue} {rest : List Frame} {argument : Term} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .argument argument environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_update {state : State} {value : RuntimeValue} {rest : List Frame} {address : Address}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .update address :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_field {state : State} {value : RuntimeValue} {rest : List Frame} {name : String}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .field name :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_reflect {state : State} {value : RuntimeValue} {rest : List Frame} 
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .reflect :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_metadata {state : State} {value : RuntimeValue} {rest : List Frame} 
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .metadata :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_project {state : State} {value : RuntimeValue} {rest : List Frame} 
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .project :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_extend {state : State} {value : RuntimeValue} {rest : List Frame} {fields : List (String × Term)} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .extend fields environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_condition {state : State} {value : RuntimeValue} {rest : List Frame} {zero : Term} {successorBody : Term} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .condition zero successorBody environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_binaryLeft {state : State} {value : RuntimeValue} {rest : List Frame} {primitive : Primitive} {right : Term} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .binaryLeft primitive right environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_binaryRight {state : State} {value : RuntimeValue} {rest : List Frame} {primitive : Primitive} {left : RuntimeValue}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .binaryRight primitive left :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_case {state : State} {value : RuntimeValue} {rest : List Frame} {arms : List (String × Term)} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .case arms environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_ifBool {state : State} {value : RuntimeValue} {rest : List Frame} {whenTrue : Term} {whenFalse : Term} {environment : Environment}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = .ifBool whenTrue whenFalse environment :: rest) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_enter {state : State} {address : Address}
    (invariant : LexicalInvariant state) (current : state.control = .enter address) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current]
  lexical_discharge

set_option linter.unusedSimpArgs false in
theorem lexical_return_complete {state : State} {value : RuntimeValue}
    (invariant : LexicalInvariant state) (current : state.control = .returned value)
    (top : state.stack = []) :
    LexicalInvariant (stepRaw state) := by
  lexical_unfold
  simp only [current, top]
  lexical_discharge

theorem lexical_terminal {state : State} (invariant : LexicalInvariant state)
    (terminal : stepRaw state = state) : LexicalInvariant (stepRaw state) :=
  by rw [terminal]; exact invariant

theorem stepRaw_lexicalInvariant {state : State} (invariant : LexicalInvariant state) :
    LexicalInvariant (stepRaw state) := by
  match current : state.control with
  | .complete _ | .refused _ | .blackhole _ | .yielded _ =>
    exact lexical_terminal invariant (by unfold stepRaw; rw [current])
  | .enter _ => exact lexical_enter invariant current
  | .evaluate term _ =>
    cases term with
    | hole => exact lexical_evaluate_hole invariant current
    | bound => exact lexical_evaluate_bound invariant current
    | lam => exact lexical_evaluate_lam invariant current
    | app => exact lexical_evaluate_app invariant current
    | mix => exact lexical_evaluate_mix invariant current
    | fix => exact lexical_evaluate_fix invariant current
    | specification => exact lexical_evaluate_specification invariant current
    | prototype => exact lexical_evaluate_prototype invariant current
    | reflect => exact lexical_evaluate_reflect invariant current
    | metadata => exact lexical_evaluate_metadata invariant current
    | project => exact lexical_evaluate_project invariant current
    | nat => exact lexical_evaluate_nat invariant current
    | boolean => exact lexical_evaluate_boolean invariant current
    | label => exact lexical_evaluate_label invariant current
    | binary => exact lexical_evaluate_binary invariant current
    | extend => exact lexical_evaluate_extend invariant current
    | record => exact lexical_evaluate_record invariant current
    | get => exact lexical_evaluate_get invariant current
    | ifZero => exact lexical_evaluate_ifZero invariant current
    | inject => exact lexical_evaluate_inject invariant current
    | case => exact lexical_evaluate_case invariant current
    | ifBool => exact lexical_evaluate_ifBool invariant current
    | perform => exact lexical_evaluate_perform invariant current
    | done => exact lexical_evaluate_done invariant current
  | .returned _ =>
    match top : state.stack with
    | [] => exact lexical_return_complete invariant current top
    | frame :: _ =>
      cases frame with
      | argument => exact lexical_return_argument invariant current top
      | update => exact lexical_return_update invariant current top
      | field => exact lexical_return_field invariant current top
      | reflect => exact lexical_return_reflect invariant current top
      | metadata => exact lexical_return_metadata invariant current top
      | project => exact lexical_return_project invariant current top
      | extend => exact lexical_return_extend invariant current top
      | condition => exact lexical_return_condition invariant current top
      | binaryLeft => exact lexical_return_binaryLeft invariant current top
      | binaryRight => exact lexical_return_binaryRight invariant current top
      | case => exact lexical_return_case invariant current top
      | ifBool => exact lexical_return_ifBool invariant current top

/-- Memoization is permanent: later raw steps cannot overwrite or re-enter an
already cached cell. This is the operational sharing fact; it makes no native
effect claim (this edition has no native-effect value constructor). -/
def PreservesCached (before after : Array Cell) : Prop :=
  ∀ (address : Nat) (origin : Closure) (value : RuntimeValue),
    before[address]? = some (.cached origin value) → after[address]? = some (.cached origin value)

 theorem preservesCached_refl (heap : Array Cell) : PreservesCached heap heap :=
  fun _ _ _ found => found

 theorem preservesCached_trans {a b c : Array Cell}
    (hab : PreservesCached a b) (hbc : PreservesCached b c) : PreservesCached a c :=
  fun address origin value found => hbc address origin value (hab address origin value found)

 theorem preservesCached_push (heap : Array Cell) (cell : Cell) :
    PreservesCached heap (heap.push cell) := by
  intro address origin value found
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  simpa [Array.getElem?_push,Nat.ne_of_lt bound] using found

 theorem preservesCached_set {heap : Array Cell} {address : Nat} {old next : Cell}
    (found : heap[address]? = some old)
    (uncached : ∀ origin value, old ≠ .cached origin value) :
    PreservesCached heap (heap.set! address next) := by
  intro index origin value cached
  by_cases same : index = address
  · subst index
    exact False.elim (uncached origin value (Option.some.inj (found.symm.trans cached)))
  · simpa [Array.set!,same,Ne.symm same] using cached

 theorem allocateFields_preservesCached (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) :
    PreservesCached heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PreservesCached pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact preservesCached_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using preservesCached_trans
        (preservesCached_push pair.1 (.suspended ⟨field.2,environment⟩))
        (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

 theorem stepRaw_preservesCached (state : State) :
    PreservesCached state.heap (stepRaw state).heap := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact preservesCached_refl _
    | exact preservesCached_push _ _
    | exact preservesCached_trans (preservesCached_push _ _) (preservesCached_push _ _)
    | exact allocateFields_preservesCached _ _ _
    | apply preservesCached_set; assumption; intro origin value equality; cases equality

/-- Raw reachability is resource independent. Capacity may postpone a raw
transition, but cannot turn it into a different heap computation. -/
inductive Reachable (initial : State) : State → Prop where
  | start : Reachable initial initial
  | next {state : State} : Reachable initial state → Reachable initial (stepRaw state)

 theorem reachable_preservesOrigins {initial state : State}
    (reachable : Reachable initial state) : PreservesOrigins initial.heap state.heap := by
  induction reachable with
  | start => exact preservesOrigins_refl _
  | next reachable ih => exact preservesOrigins_trans ih (stepRaw_preservesOrigins _)

 theorem reachable_lexicalInvariant {source : Term} {state : State}
    (closed : Scoped 0 source) (reachable : Reachable (initial source) state) :
    LexicalInvariant state := by
  induction reachable with
  | start => exact initial_lexicalInvariant closed
  | next _ ih => exact stepRaw_lexicalInvariant ih

 theorem reachable_preservesCached {initial state : State}
    (reachable : Reachable initial state) : PreservesCached initial.heap state.heap := by
  induction reachable with
  | start => exact preservesCached_refl _
  | next _ ih => exact preservesCached_trans ih (stepRaw_preservesCached _)

/-- The active update stack owns evaluation marks. The relation permits cyclic
origins, but never duplicate active demand of one address. Re-entry observes a
blackhole before pushing another update frame. -/
def stackUpdates : List Frame → List Address
  | [] => []
  | .update address::rest => address::stackUpdates rest
  | _::rest => stackUpdates rest

def Busy (heap : Array Cell) (stack : List Frame) : Prop :=
  (stackUpdates stack).Nodup ∧ ∀ address,
    address ∈ stackUpdates stack ↔ ∃ origin, heap[address]? = some (.evaluating origin)

def BusyInvariant (state : State) : Prop := Busy state.heap state.stack

 theorem initial_busyInvariant (source : Term) : BusyInvariant (initial source) := by
  simp [BusyInvariant,Busy,initial,stackUpdates]

 theorem busy_stack_eq {heap : Array Cell} {before after : List Frame}
    (busy : Busy heap before) (same : stackUpdates after = stackUpdates before) : Busy heap after := by
  simpa only [Busy,same] using busy

 theorem busy_push {heap : Array Cell} {stack : List Frame} {cell : Cell}
    (busy : Busy heap stack) (notEvaluating : ∀ origin, cell ≠ .evaluating origin) :
    Busy (heap.push cell) stack := by
  refine ⟨busy.1,?_⟩
  intro address
  constructor
  · intro member
    obtain ⟨origin,found⟩ := (busy.2 address).mp member
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨origin,by simpa [Array.getElem?_push,Nat.ne_of_lt bound] using found⟩
  · intro ⟨origin,found⟩
    rw [Array.getElem?_push] at found
    split at found
    · exact False.elim (notEvaluating origin (Option.some.inj found))
    · exact (busy.2 address).mpr ⟨origin,found⟩

 theorem busy_enter {heap : Array Cell} {stack : List Frame} {address : Nat} {origin : Closure}
    (busy : Busy heap stack) (found : heap[address]? = some (.suspended origin)) :
    Busy (heap.set! address (.evaluating origin)) (.update address::stack) := by
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  have absent : address ∉ stackUpdates stack := by
    intro member
    obtain ⟨other,marked⟩ := (busy.2 address).mp member
    have contradiction := Option.some.inj (found.symm.trans marked)
    cases contradiction
  refine ⟨List.nodup_cons.mpr ⟨absent,busy.1⟩,?_⟩
  intro index
  by_cases same : index = address
  · subst index
    simp [stackUpdates,Array.set!,bound]
  · simpa [stackUpdates,Array.set!,same,Ne.symm same] using busy.2 index

 theorem busy_update_exists {heap : Array Cell} {stack rest : List Frame} {address : Nat}
    (busy : Busy heap stack) (head : stack = .update address::rest) :
    ∃ origin, heap[address]? = some (.evaluating origin) :=
  (busy.2 address).mp (by simp [head,stackUpdates])

 theorem busy_cache {heap : Array Cell} {stack rest : List Frame} {address : Nat} {origin : Closure}
    (busy : Busy heap stack) (head : stack = .update address::rest)
    (found : heap[address]? = some (.evaluating origin)) (value : RuntimeValue) :
    Busy (heap.set! address (.cached origin value)) rest := by
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  have noDup : (address::stackUpdates rest).Nodup := by simpa [head,stackUpdates] using busy.1
  have absent := (List.nodup_cons.mp noDup).1
  refine ⟨(List.nodup_cons.mp noDup).2,?_⟩
  intro index
  by_cases same : index = address
  · subst index
    simp [Array.set!,bound,absent]
  · simpa [head,stackUpdates,Array.set!,same,Ne.symm same] using busy.2 index

 theorem allocateFields_busy {heap : Array Cell} {stack : List Frame}
    (busy : Busy heap stack) (environment : Environment) (fields : List (String × Term)) :
    Busy (allocateFields heap environment fields).1 stack := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      Busy pair.1 stack → Busy
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 stack := by
    intro fields
    induction fields with
    | nil => intro pair busy; exact busy
    | cons field fields ih =>
      intro pair busy
      apply ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)
      exact busy_push busy (by intro origin equality; cases equality)
  exact loop fields (heap,[]) busy

 theorem stepRaw_busyInvariant {state : State} (busy : BusyInvariant state) :
    BusyInvariant (stepRaw state) := by
  change Busy state.heap state.stack at busy
  unfold BusyInvariant stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact busy
    | apply busy_stack_eq busy; simp [stackUpdates, *]
    | apply busy_enter busy; assumption
    | apply busy_cache busy; assumption; assumption
    | apply busy_push busy; intro origin equality; cases equality
    | apply busy_push (busy_push busy (by intro origin equality; cases equality));
      intro origin equality; cases equality
    | exact allocateFields_busy busy _ _
    | apply busy_stack_eq (busy_push busy (by intro origin equality; cases equality));
      simp [stackUpdates, *]
    | apply busy_stack_eq (allocateFields_busy busy _ _); simp [stackUpdates, *]
    | exfalso
      have marked := busy_update_exists busy (by assumption)
      obtain ⟨origin,found⟩ := marked
      grind

 theorem reachable_busyInvariant {source : Term} {state : State}
    (reachable : Reachable (initial source) state) : BusyInvariant state := by
  induction reachable with
  | start => exact initial_busyInvariant _
  | next _ ih => exact stepRaw_busyInvariant ih

 theorem stepRaw_no_invalidUpdate {state : State} (busy : BusyInvariant state)
    (prior : state.control ≠ .refused .invalidUpdate) :
    (stepRaw state).control ≠ .refused .invalidUpdate := by
  change Busy state.heap state.stack at busy
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | have marked := busy_update_exists busy (by assumption)
      obtain ⟨origin,found⟩ := marked
      grind

 theorem stepRaw_no_unbound {state : State} (lexical : LexicalInvariant state)
    (prior : state.control ≠ .refused .unbound) :
    (stepRaw state).control ≠ .refused .unbound := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | simp_all [LexicalInvariant,ControlValid,ClosureValid,scoped_bound_iff]

 theorem stepRaw_no_missingCell {state : State} (lexical : LexicalInvariant state)
    (prior : state.control ≠ .refused .missingCell) :
    (stepRaw state).control ≠ .refused .missingCell := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | simp_all [LexicalInvariant,ControlValid]

 theorem reachable_no_internalRefusal {source : Term} {state : State}
    (closed : Scoped 0 source) (reachable : Reachable (initial source) state) :
    state.control ≠ .refused .unbound ∧ state.control ≠ .refused .missingCell ∧
      state.control ≠ .refused .invalidUpdate := by
  induction reachable with
  | start => simp [initial]
  | next reachable ih =>
      have lexical := reachable_lexicalInvariant closed reachable
      have busy := reachable_busyInvariant reachable
      exact ⟨stepRaw_no_unbound lexical ih.1,stepRaw_no_missingCell lexical ih.2.1,
        stepRaw_no_invalidUpdate busy ih.2.2⟩

/-- Completion is exposed only after the continuation has been discharged. -/
def FinalStackInvariant (state : State) : Prop :=
  ∀ value, state.control = .complete value → state.stack = []

 theorem initial_finalStackInvariant (source : Term) : FinalStackInvariant (initial source) := by
  intro value complete; cases complete

 theorem stepRaw_finalStackInvariant {state : State} (final : FinalStackInvariant state) :
    FinalStackInvariant (stepRaw state) := by
  unfold FinalStackInvariant stepRaw at *
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve | exact final | simp_all

 theorem reachable_finalStackInvariant {source : Term} {state : State}
    (reachable : Reachable (initial source) state) : FinalStackInvariant state := by
  induction reachable with
  | start => exact initial_finalStackInvariant _
  | next _ ih => exact stepRaw_finalStackInvariant ih

end Obend.Core.Invariant

end