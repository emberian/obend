module
/-
# Obend.Judge.Genealogy — the judge as a value, and its succession judged by itself

svenvs's one gate (`~/dev/svenvs/ARCHITECTURE.md`, `CLAIMS.md` §0, §2, §9) brought into obend's
judge: an action, or a change of the judge, is admitted exactly when it discharges an explicit
obligation checked by a judge the actor cannot forge. The root is not frozen: it is the current term
of a genealogy of judges, sound at genesis and certified forward (svenvs
`genealogy/genealogyScript.sml : genealogy_sound`).

- A **habitat** (`Habitat`) is the system the judges govern: states, actions with the format each is
  proposed in, floors (decidable properties of a state, given as syntax with a fixed meaning, so two
  floors are compared as data and a successor cannot keep a floor's name and change what it says),
  the theorems it has about which formats preserve which floors (`proved`, with `proved_sound`), and
  the operator's `revert`, which every floor survives.
- A **judge** (`Gate`) is a value: its formats (the obligations it checks), its floors (what every
  action it admits preserves), its checker (`methods`: per format and floor, a `Method`: a theorem of
  the habitat, or an evaluation of the floor on the state the action leads to, run under a
  `TrustBase`), and its basis (the trust bases its verdicts rest on). A pair the checker has no
  method for is not checked; that is what `wellFormed` refuses.
- An execution model (`Exec`) says what a run under each trust base returns; `Exec.Holds t` is the
  principle that a run under `t` that says yes is right. The kernel's runs are the decision itself;
  a compiled or external run is not, and no judge that does not already hold that principle can
  certify a successor that rests on it (Gödel/Löb: a sound judge cannot certify a logically stronger
  successor for free). Such a step is admitted only when it is labelled with the principle, and every
  theorem that uses it carries the labels as the hypothesis `LobCost`.
- A **succession** is an action judged by the current judge (`succeed`): the successor keeps every
  floor (non-regression), is well formed (every floor discharged on every format, `revert` among its
  formats and discharged by theorem, a corrigibility floor among its floors), its floors hold now, and
  its basis exceeds the current judge's by exactly the labels.

Theorems: `succession_sound` (along an admitted chain from a well-formed genesis, every judge
keeps every genesis floor and every action it admits preserves it, given `LobCost`); `run_floors`
(the same over a run of the system driven by any actor, successions and actions interleaved);
`cage_not_inhabitant` and `run_noninterference` (admission depends on the move, never on who
proposes it or what it says of itself); `revert_admitted` (every well-formed judge admits `revert` in
every state); `lob_labelled` (in an admitted chain each step's labels are exactly the principles its
successor holds and its predecessor did not); `succession_sound_meaning` (the checker's acceptance is
the `Succeeds` relation). The concrete habitat (`Rec`: a store with its judged past and the
operator's home), its decidable corrigibility floor (`home_decidable`, `operator_brings_home`), the
necessity of the Löb hypothesis (`lob_cost_necessary`) and the registered format
`judge-succession@1` follow.
-/
public import Obend.Judge.Class
public import Lean.Data.Json
@[expose] public section

namespace Obend.Judge.Genealogy

set_option autoImplicit false

/-! ## Habitats, judges, execution -/

/-- Equality of trust bases, by cases: the instance `Obend.Judge.Class` derives is not exposed, so
neither the kernel nor the interpreter can run it from here. -/
instance (priority := high) trustBaseDecEq : DecidableEq TrustBase
  | .kernel, .kernel => isTrue rfl
  | .compiled, .compiled => isTrue rfl
  | .external a, .external b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .kernel, .compiled | .kernel, .external _ | .compiled, .kernel | .compiled, .external _
  | .external _, .kernel | .external _, .compiled => isFalse nofun

/-- How a judge discharges one floor on one format. -/
inductive Method where
  /-- decide the floor on the state the action leads to, the decision run under a trust base -/
  | eval (t : TrustBase)
  /-- a theorem of the habitat: every action of the format preserves the floor -/
  | lemma
  deriving DecidableEq, Repr

/-- **A habitat**: the system a genealogy of judges governs. -/
structure Habitat where
  State : Type
  Act : Type
  Floor : Type
  [floorEq : DecidableEq Floor]
  /-- what a floor says of a state -/
  holds : Floor → State → Prop
  [decHolds : ∀ φ s, Decidable (holds φ s)]
  step : Act → State → State
  /-- the format an action is proposed in -/
  format : Act → String
  /-- the habitat's theorems: format `f` preserves floor `φ` -/
  proved : String → Floor → Bool
  proved_sound : ∀ {f : String} {φ : Floor}, proved f φ = true →
    ∀ a s, format a = f → holds φ s → holds φ (step a s)
  /-- the operator's move back to the last judged state -/
  revert : Act
  revert_proved : ∀ φ, proved (format revert) φ = true
  /-- the corrigibility floors: the bedrock no succession may drop -/
  bedrock : Floor → Bool

attribute [instance] Habitat.floorEq Habitat.decHolds

variable {H : Habitat}

/-- **A judge, as a value.** -/
structure Gate (H : Habitat) where
  name : String
  /-- the obligations it checks: the formats it admits actions in -/
  formats : List String
  /-- what every action it admits preserves -/
  floors : List H.Floor
  /-- its checker: per format and floor, how the floor is discharged (the first entry wins) -/
  methods : List (String × H.Floor × Method)
  /-- the trust bases its verdicts rest on -/
  basis : List TrustBase

/-- The checker's method for floor `φ` on format `f`, if it has one. -/
def Gate.method (G : Gate H) (f : String) (φ : H.Floor) : Option Method :=
  (G.methods.find? fun m => m.1 == f && decide (m.2.1 = φ)).map (·.2.2)

/-- What a run under each trust base returns, given the decision it was asked to run. -/
structure Exec where
  runs : TrustBase → Bool → Bool

/-- The principle that a run under `t` that says yes is right. -/
def Exec.Holds (X : Exec) (t : TrustBase) : Prop := ∀ b, X.runs t b = true → b = true

/-- The execution in which every run is the decision. The command line's judge runs as compiled code
and reports under this model; its theorems are stated for every `Exec`. -/
def Exec.faithful : Exec := ⟨fun _ b => b⟩

theorem Exec.faithful_holds (t : TrustBase) : Exec.faithful.Holds t := fun _ h => h

/-- Whether the checker discharges floor `φ` for action `a` in state `s`. A pair it has no method
for is not checked. -/
def discharge (X : Exec) (G : Gate H) (s : H.State) (a : H.Act) (φ : H.Floor) : Bool :=
  match G.method (H.format a) φ with
  | some (.eval t) => X.runs t (decide (H.holds φ (H.step a s)))
  | some .lemma => H.proved (H.format a) φ
  | none => true

/-- **The gate**: an action is admitted when its format is one of the judge's and every floor the
judge exports is discharged. Its inputs are the judge, the state and the action. -/
def admits (X : Exec) (G : Gate H) (s : H.State) (a : H.Act) : Bool :=
  G.formats.contains (H.format a) && G.floors.all (discharge X G s a)

/-- A judge is sound under `X` when every action it admits preserves every floor it exports. -/
def GateSound (X : Exec) (G : Gate H) : Prop :=
  ∀ s a, admits X G s a = true → ∀ φ ∈ G.floors, H.holds φ s → H.holds φ (H.step a s)

/-! ## Refusals and the checks -/

/-- Why a judge, or a proposed successor, is refused. -/
inductive Refusal (H : Habitat) where
  /-- the successor does not export a floor the current judge exports -/
  | dropsFloor (φ : H.Floor)
  /-- a floor of the successor does not hold in the state the succession is proposed in -/
  | floorFails (φ : H.Floor)
  /-- no corrigibility floor -/
  | noBedrock
  /-- `revert`'s format is not among the judge's formats -/
  | refusesRevert
  /-- `revert` is discharged by evaluation, not by the habitat's theorem, on this floor -/
  | revertUnproved (φ : H.Floor)
  /-- the checker has no method for this floor on this format -/
  | unchecked (f : String) (φ : H.Floor)
  /-- the checker cites a theorem the habitat does not have -/
  | unproved (f : String) (φ : H.Floor)
  /-- the checker evaluates under a trust base its basis does not declare -/
  | undeclared (f : String) (φ : H.Floor) (t : TrustBase)
  /-- the successor rests on a trust base the current judge does not hold, and the step is not
      labelled with it -/
  | stronger (t : TrustBase)
  /-- a label the step does not need: the successor does not rest on it, or the current judge holds it -/
  | labelNotNeeded (t : TrustBase)

/-- Refuse with `r` unless `b`. -/
def need (b : Bool) (r : Refusal H) : Except (Refusal H) Unit := if b then .ok () else .error r

/-- The first refusal of `k` along `l`. -/
def allE {α : Type} : List α → (α → Except (Refusal H) Unit) → Except (Refusal H) Unit
  | [], _ => .ok ()
  | x :: xs, k => match k x with
    | .ok () => allE xs k
    | .error e => .error e

/-- `a`, then `b`. -/
def both (a b : Except (Refusal H) Unit) : Except (Refusal H) Unit :=
  match a with
  | .ok () => b
  | .error e => .error e

theorem need_ok {b : Bool} {r : Refusal H} : need b r = .ok () ↔ b = true := by
  cases b <;> simp [need]

theorem allE_ok {α : Type} {l : List α} {k : α → Except (Refusal H) Unit} :
    allE l k = .ok () ↔ ∀ x ∈ l, k x = .ok () := by
  induction l with
  | nil => simp [allE]
  | cons x xs ih =>
    simp only [allE, List.mem_cons, forall_eq_or_imp]
    cases hk : k x with
    | ok u => cases u; simp [ih]
    | error e => simp

theorem both_ok {a b : Except (Refusal H) Unit} : both a b = .ok () ↔ a = .ok () ∧ b = .ok () := by
  cases a with
  | ok u => cases u; simp [both]
  | error e => simp [both]

/-- One floor on one format: the checker's method is a theorem the habitat has, or an evaluation
under a declared trust base on a format other than `revert`'s. -/
def methodCheck (G : Gate H) (f : String) (φ : H.Floor) : Except (Refusal H) Unit :=
  match G.method f φ with
  | none => .error (.unchecked f φ)
  | some .lemma => need (H.proved f φ) (.unproved f φ)
  | some (.eval t) =>
    if f = H.format H.revert then .error (.revertUnproved φ)
    else need (G.basis.contains t) (.undeclared f φ t)

/-- **A well-formed judge**: a corrigibility floor among its floors, `revert` among its formats, and
every floor discharged on every format. -/
def wellFormed (G : Gate H) : Except (Refusal H) Unit :=
  both (need (G.floors.any H.bedrock) .noBedrock) <|
  both (need (G.formats.contains (H.format H.revert)) .refusesRevert) <|
  allE G.formats fun f => allE G.floors fun φ => methodCheck G f φ

/-- **Non-regression**: the successor exports every floor the current judge exports. -/
def nonRegression (G G' : Gate H) : Except (Refusal H) Unit :=
  allE G.floors fun φ => need (G'.floors.contains φ) (.dropsFloor φ)

/-- **A succession, judged by the current judge** `G` in state `s`: the successor `G'` with the
labels `L` (the principles it rests on that `G` does not hold). -/
def succeed (G : Gate H) (s : H.State) (G' : Gate H) (L : List TrustBase) : Except (Refusal H) Unit :=
  both (nonRegression G G') <|
  both (wellFormed G') <|
  both (allE G'.floors fun φ => need (decide (H.holds φ s)) (.floorFails φ)) <|
  both (allE G'.basis fun t => need (G.basis.contains t || L.contains t) (.stronger t)) <|
  allE L fun t => need (G'.basis.contains t && !G.basis.contains t) (.labelNotNeeded t)

/-! ## A well-formed judge is sound, and admits `revert` -/

theorem methodCheck_ok {G : Gate H} {f : String} {φ : H.Floor} (h : methodCheck G f φ = .ok ()) :
    (G.method f φ = some .lemma ∧ H.proved f φ = true) ∨
      (∃ t, G.method f φ = some (.eval t) ∧ t ∈ G.basis ∧ f ≠ H.format H.revert) := by
  unfold methodCheck at h
  split at h
  · cases h
  · next hm => exact .inl ⟨hm, need_ok.1 h⟩
  · next t hm =>
    split at h
    · cases h
    · next hne => exact .inr ⟨t, hm, List.contains_iff_mem.1 (need_ok.1 h), hne⟩

theorem wellFormed_parts {G : Gate H} (h : wellFormed G = .ok ()) :
    G.floors.any H.bedrock = true ∧ H.format H.revert ∈ G.formats ∧
      ∀ f ∈ G.formats, ∀ φ ∈ G.floors, methodCheck G f φ = .ok () := by
  unfold wellFormed at h
  obtain ⟨h1, h⟩ := both_ok.1 h
  obtain ⟨h2, h3⟩ := both_ok.1 h
  exact ⟨need_ok.1 h1, List.contains_iff_mem.1 (need_ok.1 h2),
    fun f hf φ hφ => allE_ok.1 (allE_ok.1 h3 f hf) φ hφ⟩

/-- A well-formed judge whose basis holds is sound. -/
theorem wellFormed_sound (X : Exec) (G : Gate H) (hw : wellFormed G = .ok ())
    (hb : ∀ t ∈ G.basis, X.Holds t) : GateSound X G := by
  intro s a ha φ hφ hs
  obtain ⟨-, -, hm⟩ := wellFormed_parts hw
  simp only [admits, Bool.and_eq_true, List.all_eq_true] at ha
  obtain ⟨hf, hd⟩ := ha
  have hd := hd φ hφ
  rcases methodCheck_ok (hm _ (List.contains_iff_mem.1 hf) φ hφ) with ⟨_, hp⟩ | ⟨t, he, ht, _⟩
  · exact H.proved_sound hp a s rfl hs
  · simp only [discharge, he] at hd
    exact of_decide_eq_true (hb t ht _ hd)

/-- **Every well-formed judge admits `revert`, in every state and under every execution.** -/
theorem revert_admitted (X : Exec) (G : Gate H) (hw : wellFormed G = .ok ()) (s : H.State) :
    admits X G s H.revert = true := by
  obtain ⟨-, hr, hm⟩ := wellFormed_parts hw
  simp only [admits, Bool.and_eq_true, List.all_eq_true]
  refine ⟨List.contains_iff_mem.2 hr, fun φ hφ => ?_⟩
  rcases methodCheck_ok (hm _ hr φ hφ) with ⟨he, hp⟩ | ⟨t, -, -, hne⟩
  · simp [discharge, he, hp]
  · exact absurd rfl hne

/-! ## The succession checker's meaning -/

/-- **What an admitted succession establishes.** -/
structure Succeeds (G : Gate H) (s : H.State) (G' : Gate H) (L : List TrustBase) : Prop where
  keeps : ∀ φ ∈ G.floors, φ ∈ G'.floors
  holdsNow : ∀ φ ∈ G'.floors, H.holds φ s
  labelled : ∀ t ∈ G'.basis, t ∈ G.basis ∨ t ∈ L
  exact : ∀ t ∈ L, t ∈ G'.basis ∧ t ∉ G.basis
  sound : ∀ X : Exec, (∀ t ∈ G.basis, X.Holds t) → (∀ t ∈ L, X.Holds t) → GateSound X G'
  revert : ∀ (X : Exec) (s' : H.State), admits X G' s' H.revert = true

theorem succeed_parts {G G' : Gate H} {s : H.State} {L : List TrustBase}
    (h : succeed G s G' L = .ok ()) :
    nonRegression G G' = .ok () ∧ wellFormed G' = .ok () ∧ (∀ φ ∈ G'.floors, H.holds φ s) ∧
      (∀ t ∈ G'.basis, t ∈ G.basis ∨ t ∈ L) ∧ (∀ t ∈ L, t ∈ G'.basis ∧ t ∉ G.basis) := by
  unfold succeed at h
  obtain ⟨h1, h⟩ := both_ok.1 h
  obtain ⟨h2, h⟩ := both_ok.1 h
  obtain ⟨h3, h⟩ := both_ok.1 h
  obtain ⟨h4, h5⟩ := both_ok.1 h
  refine ⟨h1, h2, fun φ hφ => of_decide_eq_true (need_ok.1 (allE_ok.1 h3 φ hφ)), fun t ht => ?_,
    fun t ht => ?_⟩
  · have := need_ok.1 (allE_ok.1 h4 t ht)
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    exact this
  · have := need_ok.1 (allE_ok.1 h5 t ht)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
    exact ⟨this.1, fun hm => Bool.false_ne_true (this.2.symm.trans (List.contains_iff_mem.2 hm))⟩

theorem nonRegression_keeps {G G' : Gate H} (h : nonRegression G G' = .ok ()) :
    ∀ φ ∈ G.floors, φ ∈ G'.floors :=
  fun φ hφ => List.contains_iff_mem.1 (need_ok.1 (allE_ok.1 h φ hφ))

/-- **The succession checker is sound**: its acceptance is `Succeeds`. -/
theorem succession_sound_meaning {G G' : Gate H} {s : H.State} {L : List TrustBase}
    (h : succeed G s G' L = .ok ()) : Succeeds G s G' L := by
  obtain ⟨hn, hw, hs, hl, he⟩ := succeed_parts h
  refine ⟨nonRegression_keeps hn, hs, hl, he, fun X hG hL => wellFormed_sound X G' hw ?_,
    fun X s' => revert_admitted X G' hw s'⟩
  intro t ht
  rcases hl t ht with h | h
  · exact hG t h
  · exact hL t h

/-- A dropped floor is refused. -/
theorem succeed_refuses_drop {G G' : Gate H} {s : H.State} {L : List TrustBase} {φ : H.Floor}
    (hφ : φ ∈ G.floors) (hd : φ ∉ G'.floors) : succeed G s G' L ≠ .ok () :=
  fun h => hd (nonRegression_keeps (succeed_parts h).1 φ hφ)

/-- The identity succession: a well-formed judge whose floors hold succeeds itself, with no label
(svenvs `identity_vouch_unconditional`). -/
theorem succeed_self {G : Gate H} {s : H.State} (hw : wellFormed G = .ok ())
    (hs : ∀ φ ∈ G.floors, H.holds φ s) : succeed G s G [] = .ok () := by
  unfold succeed nonRegression
  refine both_ok.2 ⟨allE_ok.2 fun φ hφ => need_ok.2 (List.contains_iff_mem.2 hφ), both_ok.2 ⟨hw,
    both_ok.2 ⟨allE_ok.2 fun φ hφ => need_ok.2 (decide_eq_true (hs φ hφ)),
    both_ok.2 ⟨allE_ok.2 fun t ht => need_ok.2 (by simp [ht]),
    allE_ok.2 fun t ht => by simp at ht⟩⟩⟩⟩

/-! ## Chains of successions -/

/-- One proposed succession: the state it is proposed in, the successor, the labels. -/
structure Succession (H : Habitat) where
  state : H.State
  next : Gate H
  labels : List TrustBase

/-- Each succession admitted by the judge before it. -/
def Admitted : Gate H → List (Succession H) → Prop
  | _, [] => True
  | G, σ :: rest => succeed G σ.state σ.next σ.labels = .ok () ∧ Admitted σ.next rest

/-- The judges of a chain, genesis first. -/
def judges : Gate H → List (Succession H) → List (Gate H)
  | G, [] => [G]
  | G, σ :: rest => G :: judges σ.next rest

/-- The last judge of a chain. -/
def lastJudge : Gate H → List (Succession H) → Gate H
  | G, [] => G
  | _, σ :: rest => lastJudge σ.next rest

/-- Every label a chain carries. -/
def labels (steps : List (Succession H)) : List TrustBase := steps.flatMap (·.labels)

/-- **The Löb cost**: the principles the stronger steps were labelled with hold. Every theorem that
uses a labelled step carries this hypothesis by name, and the census lists those theorems. -/
def LobCost (X : Exec) (labels : List TrustBase) : Prop := ∀ t ∈ labels, X.Holds t

theorem chain_invariant (X : Exec) :
    ∀ (steps : List (Succession H)) (G : Gate H), wellFormed G = .ok () → (∀ t ∈ G.basis, X.Holds t) →
      Admitted G steps → LobCost X (labels steps) →
      ∀ G' ∈ judges G steps, wellFormed G' = .ok () ∧ (∀ φ ∈ G.floors, φ ∈ G'.floors) ∧
        ∀ t ∈ G'.basis, X.Holds t
  | [], G, hw, hb, _, _, G', hG' => by
    simp only [judges, List.mem_singleton] at hG'
    subst hG'
    exact ⟨hw, fun _ h => h, hb⟩
  | σ :: rest, G, hw, hb, ⟨hs, hrest⟩, hlob, G', hG' => by
    simp only [judges, List.mem_cons] at hG'
    obtain ⟨hn, hw', -, hl, -⟩ := succeed_parts hs
    have hb' : ∀ t ∈ σ.next.basis, X.Holds t := fun t ht => by
      rcases hl t ht with h | h
      · exact hb t h
      · exact hlob t (by simp [labels]; exact Or.inl h)
    have hlob' : LobCost X (labels rest) := fun t ht => hlob t (by
      simp only [labels, List.flatMap_cons, List.mem_append]; exact Or.inr ht)
    rcases hG' with rfl | hG'
    · exact ⟨hw, fun _ h => h, hb⟩
    · obtain ⟨h1, h2, h3⟩ := chain_invariant X rest σ.next hw' hb' hrest hlob' G' hG'
      exact ⟨h1, fun φ hφ => h2 φ (nonRegression_keeps hn φ hφ), h3⟩

/-- **Succession is sound.** Along a chain of successions each admitted by the judge before it,
from a well-formed genesis whose basis holds, and given the Löb cost of the chain, every judge
exports every genesis floor and every action it admits preserves it. -/
theorem succession_sound (X : Exec) (G₀ : Gate H) (steps : List (Succession H))
    (genesis : wellFormed G₀ = .ok ()) (trusted : ∀ t ∈ G₀.basis, X.Holds t)
    (chain : Admitted G₀ steps) (lob : LobCost X (labels steps)) :
    ∀ G ∈ judges G₀ steps, ∀ φ ∈ G₀.floors, φ ∈ G.floors ∧
      ∀ s a, admits X G s a = true → H.holds φ s → H.holds φ (H.step a s) := by
  intro G hG φ hφ
  obtain ⟨hw, hk, hb⟩ := chain_invariant X steps G₀ genesis trusted chain lob G hG
  exact ⟨hk φ hφ, fun s a ha => wellFormed_sound X G hw hb s a ha φ (hk φ hφ)⟩

/-- Each step's labels are exactly the principles its successor holds and its predecessor did not. -/
def Labelled : Gate H → List (Succession H) → Prop
  | _, [] => True
  | G, σ :: rest => (∀ t, t ∈ σ.labels ↔ t ∈ σ.next.basis ∧ t ∉ G.basis) ∧ Labelled σ.next rest

theorem lastJudge_mem : ∀ (G : Gate H) (steps : List (Succession H)), lastJudge G steps ∈ judges G steps
  | G, [] => by simp [lastJudge, judges]
  | G, σ :: rest => by simp only [lastJudge, judges, List.mem_cons]; exact .inr (lastJudge_mem _ _)

/-- **The Löb cost is labelled.** In an admitted chain every stronger step is labelled with exactly
the principles it adds, and the last judge rests on nothing beyond genesis and the labels. -/
theorem lob_labelled :
    ∀ (G₀ : Gate H) (steps : List (Succession H)), Admitted G₀ steps →
      Labelled G₀ steps ∧ ∀ t ∈ (lastJudge G₀ steps).basis, t ∈ G₀.basis ∨ t ∈ labels steps
  | G, [], _ => ⟨trivial, fun t ht => .inl ht⟩
  | G, σ :: rest, ⟨hs, hrest⟩ => by
    obtain ⟨-, -, -, hl, he⟩ := succeed_parts hs
    obtain ⟨hL, hlast⟩ := lob_labelled σ.next rest hrest
    refine ⟨⟨fun t => ⟨he t, fun ⟨h1, h2⟩ => (hl t h1).resolve_left h2⟩, hL⟩, fun t ht => ?_⟩
    simp only [labels, List.flatMap_cons, List.mem_append, lastJudge] at ht ⊢
    rcases hlast t ht with h | h
    · rcases hl t h with h' | h'
      · exact .inl h'
      · exact .inr (.inl h')
    · exact .inr (.inr h)

/-- A step is stronger than its predecessor exactly when it carries a label. -/
theorem stronger_iff_labelled {G G' : Gate H} {s : H.State} {L : List TrustBase}
    (h : succeed G s G' L = .ok ()) : (∃ t ∈ G'.basis, t ∉ G.basis) ↔ L ≠ [] := by
  obtain ⟨-, -, -, hl, he⟩ := succeed_parts h
  constructor
  · rintro ⟨t, ht, hn⟩ rfl
    simpa [hn] using hl t ht
  · intro hne
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil L hne
    exact ⟨t, (he t ht).1, (he t ht).2⟩

/-! ## The system over time, driven by any actor -/

/-- What an actor may propose: an action, or a successor judge with its labels. -/
inductive Move (H : Habitat) where
  | act (a : H.Act)
  | succeed (next : Gate H) (labels : List TrustBase)

/-- A proposal: who proposes, what, and what the proposer says of itself. -/
structure Proposal (H : Habitat) (Actor : Type) where
  actor : Actor
  move : Move H
  testimony : String

/-- The system: the current judge, the state, the labels spent so far. -/
structure Sys (H : Habitat) where
  judge : Gate H
  state : H.State
  spent : List TrustBase

/-- One step: an admitted move takes effect; a refused one changes nothing. -/
def Sys.step {Actor : Type} (X : Exec) (sys : Sys H) (p : Proposal H Actor) : Sys H :=
  match p.move with
  | .act a => if admits X sys.judge sys.state a then { sys with state := H.step a sys.state } else sys
  | .succeed G' L => match succeed sys.judge sys.state G' L with
    | .ok () => { judge := G', state := sys.state, spent := sys.spent ++ L }
    | .error _ => sys

/-- The run of the system under an actor: any function of the time and the system. -/
def run {Actor : Type} (X : Exec) (actor : Nat → Sys H → Proposal H Actor) (sys₀ : Sys H) : Nat → Sys H
  | 0 => sys₀
  | n + 1 => (run X actor sys₀ n).step X (actor n (run X actor sys₀ n))

/-- **The cage, not the inhabitant**: two proposals with the same move, whoever proposes them and
whatever they say of themselves, take the system to the same place. -/
theorem cage_not_inhabitant {Actor Actor' : Type} (X : Exec) (sys : Sys H) (p : Proposal H Actor)
    (q : Proposal H Actor') (h : p.move = q.move) : sys.step X p = sys.step X q := by
  unfold Sys.step; rw [h]

/-- Noninterference over the actor: two actors whose moves agree run the system identically. -/
theorem run_noninterference {Actor Actor' : Type} (X : Exec) (actor : Nat → Sys H → Proposal H Actor)
    (actor' : Nat → Sys H → Proposal H Actor') (h : ∀ n sys, (actor n sys).move = (actor' n sys).move)
    (sys₀ : Sys H) : ∀ n, run X actor sys₀ n = run X actor' sys₀ n
  | 0 => rfl
  | n + 1 => by
    simp only [run]
    rw [run_noninterference X actor actor' h sys₀ n]
    exact cage_not_inhabitant X _ _ _ (h _ _)

theorem run_spent_mono {Actor : Type} (X : Exec) (actor : Nat → Sys H → Proposal H Actor) (sys₀ : Sys H) :
    ∀ n, ∀ t ∈ (run X actor sys₀ n).spent, t ∈ (run X actor sys₀ (n + 1)).spent := by
  intro n t ht
  simp only [run, Sys.step]
  split
  · split <;> exact ht
  · split
    · exact List.mem_append_left _ ht
    · exact ht

/-- The invariant a run keeps. -/
structure RunInv (G₀ : Gate H) (sys : Sys H) : Prop where
  wf : wellFormed sys.judge = .ok ()
  keeps : ∀ φ ∈ G₀.floors, φ ∈ sys.judge.floors
  holds : ∀ φ ∈ sys.judge.floors, H.holds φ sys.state
  basis : ∀ t ∈ sys.judge.basis, t ∈ G₀.basis ∨ t ∈ sys.spent

theorem run_invariant {Actor : Type} (X : Exec) (actor : Nat → Sys H → Proposal H Actor)
    (G₀ : Gate H) (s₀ : H.State) (genesis : wellFormed G₀ = .ok ()) (trusted : ∀ t ∈ G₀.basis, X.Holds t)
    (init : ∀ φ ∈ G₀.floors, H.holds φ s₀) :
    ∀ n, (∀ t ∈ (run X actor ⟨G₀, s₀, []⟩ n).spent, X.Holds t) → RunInv G₀ (run X actor ⟨G₀, s₀, []⟩ n)
  | 0, _ => ⟨genesis, fun _ h => h, init, fun t ht => .inl ht⟩
  | n + 1, hlob => by
    have I := run_invariant X actor G₀ s₀ genesis trusted init n
      (fun t ht => hlob t (run_spent_mono X actor _ n t ht))
    have hb : ∀ t ∈ (run X actor ⟨G₀, s₀, []⟩ n).judge.basis, X.Holds t := fun t ht => by
      rcases I.basis t ht with h | h
      · exact trusted t h
      · exact hlob t (run_spent_mono X actor _ n t h)
    revert hlob
    simp only [run, Sys.step]
    split
    · next a _ =>
      split
      · next ha =>
        intro _
        exact ⟨I.wf, I.keeps, fun φ hφ => wellFormed_sound X _ I.wf hb _ a ha φ hφ (I.holds φ hφ), I.basis⟩
      · intro _; exact I
    · next G' L _ =>
      split
      · next hs =>
        intro _
        obtain ⟨hn, hw', hnow, hl, -⟩ := succeed_parts hs
        refine ⟨hw', fun φ hφ => nonRegression_keeps hn φ (I.keeps φ hφ), hnow, fun t ht => ?_⟩
        rcases hl t ht with h | h
        · rcases I.basis t h with h' | h'
          · exact .inl h'
          · exact .inr (List.mem_append_left _ h')
        · exact .inr (List.mem_append_right _ h)
      · intro _; exact I

/-- **The genesis floors hold along every run, whatever the actor.** Successions and actions
interleaved, each judged by the judge of its moment; the labels the run spent are its Löb cost. -/
theorem run_floors {Actor : Type} (X : Exec) (actor : Nat → Sys H → Proposal H Actor)
    (G₀ : Gate H) (s₀ : H.State) (genesis : wellFormed G₀ = .ok ()) (trusted : ∀ t ∈ G₀.basis, X.Holds t)
    (init : ∀ φ ∈ G₀.floors, H.holds φ s₀) (n : Nat)
    (lob : LobCost X (run X actor ⟨G₀, s₀, []⟩ n).spent) :
    ∀ φ ∈ G₀.floors, H.holds φ (run X actor ⟨G₀, s₀, []⟩ n).state := by
  have I := run_invariant X actor G₀ s₀ genesis trusted init n lob
  exact fun φ hφ => I.holds φ (I.keeps φ hφ)

/-! ## The succession checker as an obend judge -/

/-- **The succession judge**: the object is the current judge and the state, the certificate the
successor and its labels; acceptance means `Succeeds`. It never refutes (a refused successor says
nothing of the others), and it is complete where the current judge is well formed and its floors
hold: the judge succeeds itself. -/
instance successionJudge (H : Habitat) : Judge (Gate H × H.State) (Gate H × List TrustBase) where
  Clause := Refusal H
  Meaning o c := Succeeds o.1 o.2 c.1 c.2
  check _ o c := match succeed o.1 o.2 c.1 c.2 with
    | .ok () => .ok
    | .error r => .refused r []
  sound {_ o c} h := by
    revert h
    split
    · next hs => intro _; exact succession_sound_meaning hs
    · intro h; cases h
  refutes _ := false
  refuted _ h := by cases h
  Fragment o := wellFormed o.1 = .ok () ∧ ∀ φ ∈ o.1.floors, H.holds φ o.2
  complete {o} hf _ := ⟨(o.1, []), 0, by simp [succeed_self hf.1 hf.2]⟩
  mono _ _ := rfl

/-! ## The record: a store, its judged past, and the operator's home -/

/-- A store: cells and their values, sorted by cell. -/
abbrev Store := List (String × Nat)

/-- A cell's value (0 when absent). -/
def Store.get (st : Store) (c : String) : Nat := (st.lookup c).getD 0

/-- Set a cell, keeping the store sorted. -/
def Store.set : Store → String → Nat → Store
  | [], c, v => [(c, v)]
  | (d, w) :: rest, c, v =>
    if c = d then (c, v) :: rest
    else if c < d then (c, v) :: (d, w) :: rest
    else (d, w) :: Store.set rest c v

/-- **The record**: the store, the judged stores before it (the latest first), and the operator's
home (the store at genesis). -/
structure Rec where
  store : Store
  past : List Store
  home : Store
  deriving DecidableEq, Repr

/-- The actions on the record. -/
inductive RecAct where
  /-- set a cell, keeping the store it replaces as the last judged state -/
  | write (c : String) (v : Nat)
  /-- the operator's move: back to the last judged state -/
  | revert
  /-- drop the judged past: a one-way door -/
  | forget
  deriving DecidableEq, Repr

def RecAct.format : RecAct → String
  | .write .. => "write@1"
  | .revert => "revert@1"
  | .forget => "forget@1"

def recStep : RecAct → Rec → Rec
  | .write c v, r => { r with store := r.store.set c v, past := r.store :: r.past }
  | .revert, r => match r.past with
    | [] => r
    | p :: ps => { r with store := p, past := ps }
  | .forget, r => { r with past := [] }

/-- The oldest judged store: where reverting all the way leads. -/
def Rec.bottom (r : Rec) : Store := (r.store :: r.past).getLast (List.cons_ne_nil _ _)

/-- The floors of the record. -/
inductive RecFloor where
  /-- **the corrigibility floor**: the operator can bring the system home within `h` reverts -/
  | home (h : Nat)
  /-- every judged store keeps cell `c` at most `max` -/
  | cap (c : String) (max : Nat)
  deriving DecidableEq, Repr

def RecFloor.holds : RecFloor → Rec → Prop
  | .home h, r => r.bottom = r.home ∧ r.past.length ≤ h
  | .cap c m, r => ∀ st ∈ r.store :: r.past, st.get c ≤ m

/-- **The corrigibility floor is decidable**, and so is every floor of the record. -/
instance floor_decidable : ∀ (φ : RecFloor) (r : Rec), Decidable (φ.holds r)
  | .home _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .cap _ _, _ => inferInstanceAs (Decidable (∀ st ∈ _, _))

/-- The record's theorems: `revert` preserves every floor; `forget` preserves every cap. -/
def recProved : String → RecFloor → Bool
  | "revert@1", _ => true
  | "forget@1", .cap _ _ => true
  | _, _ => false

theorem revert_keeps (φ : RecFloor) (r : Rec) (h : φ.holds r) : φ.holds (recStep .revert r) := by
  rcases r with ⟨st, past, home⟩
  cases past with
  | nil => exact h
  | cons p ps =>
    cases φ with
    | home k =>
      obtain ⟨hb, hl⟩ := h
      refine ⟨?_, by simp [recStep] at hl ⊢; omega⟩
      simpa [recStep, Rec.bottom, List.getLast_cons] using hb
    | cap c m =>
      intro x hx
      exact h x (List.mem_cons_of_mem _ hx)

theorem forget_keeps_cap (c : String) (m : Nat) (r : Rec) (h : (RecFloor.cap c m).holds r) :
    (RecFloor.cap c m).holds (recStep .forget r) := by
  intro x hx
  simp only [recStep, List.mem_singleton] at hx
  subst hx
  exact h _ List.mem_cons_self

theorem recProved_sound {f : String} {φ : RecFloor} (hp : recProved f φ = true) :
    ∀ a r, RecAct.format a = f → φ.holds r → φ.holds (recStep a r) := by
  intro a r hf hr
  subst hf
  cases a with
  | write c v => simp [recProved, RecAct.format] at hp
  | revert => exact revert_keeps φ r hr
  | forget =>
    cases φ with
    | home _ => simp [recProved, RecAct.format] at hp
    | cap c m => exact forget_keeps_cap c m r hr

/-- **The record as a habitat.** -/
@[reducible] def record : Habitat where
  State := Rec
  Act := RecAct
  Floor := RecFloor
  holds := RecFloor.holds
  step := recStep
  format := RecAct.format
  proved := recProved
  proved_sound := recProved_sound
  revert := .revert
  revert_proved φ := by cases φ <;> rfl
  bedrock
    | .home _ => true
    | .cap _ _ => false

theorem ok_of_toBool {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  cases e with
  | ok u => cases u; rfl
  | error _ => cases h

/-- `k` reverts. -/
def reverts : Nat → Rec → Rec
  | 0, r => r
  | k + 1, r => reverts k (recStep .revert r)

theorem reverts_home : ∀ (r : Rec), (reverts r.past.length r).store = r.bottom ∧ (reverts r.past.length r).home = r.home
  | ⟨st, [], home⟩ => by simp [reverts, Rec.bottom]
  | ⟨st, p :: ps, home⟩ => by
    have ih := reverts_home ⟨p, ps, home⟩
    refine ⟨?_, ih.2⟩
    show (reverts ps.length ⟨p, ps, home⟩).store = _
    rw [ih.1]
    simp [Rec.bottom, List.getLast_cons]

/-- **The operator brings the system home**: where the corrigibility floor holds, at most `h`
reverts reach the home store. -/
theorem operator_brings_home (h : Nat) (r : Rec) (hr : (RecFloor.home h).holds r) :
    ∃ k ≤ h, (reverts k r).store = r.home :=
  ⟨r.past.length, hr.2, (reverts_home r).1.trans hr.1⟩

/-- **`revert` is an obligation every judge admits**: a well-formed judge of the record admits it,
whatever the state and the execution. -/
theorem revert_obligation (X : Exec) (G : Gate record) (hw : wellFormed G = .ok ()) (r : Rec) :
    admits X G r RecAct.revert = true :=
  revert_admitted X G hw r

/-! ### The Löb hypothesis cannot be dropped -/

/-- A kernel-only judge of the record. -/
def lobGenesis : Gate record :=
  { name := "g0", formats := ["write@1", "revert@1"], floors := [.home 3, .cap "a" 100],
    methods := [("write@1", .home 3, .eval .kernel), ("write@1", .cap "a" 100, .eval .kernel),
      ("revert@1", .home 3, .lemma), ("revert@1", .cap "a" 100, .lemma)],
    basis := [.kernel] }

/-- Its successor, evaluating writes by compiled code. -/
def lobSuccessor : Gate record :=
  { name := "g1", formats := ["write@1", "revert@1"], floors := [.home 3, .cap "a" 100],
    methods := [("write@1", .home 3, .eval .compiled), ("write@1", .cap "a" 100, .eval .compiled),
      ("revert@1", .home 3, .lemma), ("revert@1", .cap "a" 100, .lemma)],
    basis := [.kernel, .compiled] }

/-- Three writes behind the home store. -/
def lobState : Rec := ⟨[("a", 0)], [[("a", 0)], [("a", 0)], [("a", 0)]], [("a", 0)]⟩

/-- **The Löb cost is load-bearing.** Under any execution whose kernel runs are right but whose
compiled runs can say yes to a false decision, a kernel-only genesis admits, labelled `compiled`, a
successor that then admits a write breaking a genesis floor. `succession_sound` without `LobCost`
would be false. -/
theorem lob_cost_necessary (X : Exec) (hk : X.Holds .kernel) (lies : X.runs .compiled false = true) :
    ∃ (G₀ G₁ : Gate record) (s : Rec) (a : RecAct),
      wellFormed G₀ = .ok () ∧ (∀ t ∈ G₀.basis, X.Holds t) ∧ succeed G₀ s G₁ [.compiled] = .ok () ∧
      admits X G₁ s a = true ∧ ∃ φ ∈ G₀.floors, record.holds φ s ∧ ¬ record.holds φ (record.step a s) := by
  refine ⟨lobGenesis, lobSuccessor, lobState, .write "a" 200, ok_of_toBool (by decide +kernel), ?_,
    ok_of_toBool (by decide +kernel), ?_, .cap "a" 100, List.mem_cons_of_mem _ List.mem_cons_self,
    by decide +kernel, by decide +kernel⟩
  · intro t ht
    simp only [lobGenesis, List.mem_singleton] at ht
    subst ht; exact hk
  · have e1 : decide (record.holds (.home 3) (record.step (.write "a" 200) lobState)) = false := by
      decide +kernel
    have e2 : decide (record.holds (.cap "a" 100) (record.step (.write "a" 200) lobState)) = false := by
      decide +kernel
    have d1 : discharge X lobSuccessor lobState (.write "a" 200) (.home 3) = X.runs .compiled
        (decide (record.holds (.home 3) (record.step (.write "a" 200) lobState))) := rfl
    have d2 : discharge X lobSuccessor lobState (.write "a" 200) (.cap "a" 100) = X.runs .compiled
        (decide (record.holds (.cap "a" 100) (record.step (.write "a" 200) lobState))) := rfl
    have hf : lobSuccessor.formats.contains (record.format (.write "a" 200)) = true := by decide +kernel
    show (lobSuccessor.formats.contains _ &&
      [RecFloor.home 3, .cap "a" 100].all (discharge X lobSuccessor lobState (.write "a" 200))) = true
    rw [hf]
    simp only [List.all_cons, List.all_nil, d1, d2, e1, e2, lies, Bool.and_self]

/-! ## Wire forms, refusal texts, and the registered format `judge-succession@1` -/

section Wire
open Lean (Json)

def trustText (t : TrustBase) : String := t.label

def trustOf (s : String) : Except String TrustBase :=
  if s = "kernel" then .ok .kernel
  else if s = "compiled" then .ok .compiled
  else if s.startsWith "external:" then .ok (.external (s.drop 9).toString)
  else .error s!"unknown trust base `{s}` (kernel, compiled, external:WHO)"

def RecFloor.text : RecFloor → String
  | .home h => s!"home {h}"
  | .cap c m => s!"{c} <= {m}"

instance : ToString RecFloor := ⟨RecFloor.text⟩

def floorOf (s : String) : Except String RecFloor :=
  match s.splitOn " <= " with
  | [c, m] => match m.toNat? with
    | some m => if c.isEmpty then .error s!"floor `{s}`: no cell" else .ok (.cap c m)
    | none => .error s!"floor `{s}`: `{m}` is not a number"
  | _ => match s.splitOn " " with
    | ["home", h] => match h.toNat? with
      | some h => .ok (.home h)
      | none => .error s!"floor `{s}`: `{h}` is not a number"
    | _ => .error s!"floor `{s}`: neither `home N` nor `CELL <= N`"

def Method.text : Method → String
  | .lemma => "lemma"
  | .eval t => trustText t

def methodOf (s : String) : Except String Method :=
  if s = "lemma" then .ok .lemma else Method.eval <$> trustOf s

/-- The fields of a JSON object, in key order. -/
def fieldsOf (j : Json) : Except String (List (String × Json)) := do
  let kvs ← j.getObj?
  return (kvs.foldl (fun acc k v => (k, v) :: acc) []).reverse

def strsOf (j : Json) (key : String) : Except String (List String) := do
  (← (← j.getObjVal? key).getArr?).toList.mapM (·.getStr?)

/-- A judge from JSON. `methods` maps a format to its method for every floor, or `"FORMAT FLOOR"` to
the method for one floor (which wins). -/
def gateOf (j : Json) : Except String (Gate record) := do
  let name ← (← j.getObjVal? "name").getStr?
  let formats ← strsOf j "formats"
  let floors ← (← strsOf j "floors").mapM floorOf
  let basis ← (← strsOf j "basis").mapM trustOf
  let ms ← fieldsOf (← j.getObjVal? "methods")
  let mut one : List (String × RecFloor × Method) := []
  let mut every : List (String × RecFloor × Method) := []
  for (k, v) in ms do
    let m ← methodOf (← v.getStr?)
    match k.splitOn " " with
    | [f] => every := every ++ floors.map fun φ => (f, φ, m)
    | f :: rest => one := one ++ [(f, ← floorOf (" ".intercalate rest), m)]
    | [] => throw "empty method key"
  return { name, formats, floors, methods := one ++ every, basis }

def storeOf (j : Json) : Except String Store := do
  (← fieldsOf j).foldlM (fun st (k, v) => do return st.set k (← v.getNat?)) []

def storeJson (st : Store) : Json := Json.mkObj (st.map fun (k, v) => (k, Json.num v))

/-- A judge as JSON: its checker written out as the method it uses for each floor on each of its
formats (what `admits` and `wellFormed` read of it). -/
def gateJson (G : Gate record) : Json :=
  Json.mkObj [("name", Json.str G.name), ("formats", Json.arr (G.formats.map Json.str).toArray),
    ("floors", Json.arr (G.floors.map (Json.str ·.text)).toArray),
    ("methods", Json.mkObj (G.formats.flatMap fun f => G.floors.filterMap fun φ =>
      (G.method f φ).map fun m => (s!"{f} {φ.text}", Json.str m.text))),
    ("basis", Json.arr (G.basis.map (Json.str ∘ trustText)).toArray)]

def recOf (j : Json) : Except String Rec := do
  return ⟨← storeOf (← j.getObjVal? "store"),
    ← (← (← j.getObjVal? "past").getArr?).toList.mapM storeOf, ← storeOf (← j.getObjVal? "home")⟩

def recJson (r : Rec) : Json :=
  Json.mkObj [("store", storeJson r.store), ("past", Json.arr (r.past.map storeJson).toArray),
    ("home", storeJson r.home)]

/-- The object: the current judge and the state. -/
def objOf (s : String) : Except String (Gate record × Rec) := do
  let j ← Json.parse s
  return (← gateOf (← j.getObjVal? "judge"), ← recOf (← j.getObjVal? "state"))

/-- The certificate: the successor and its labels. -/
def certOf (s : String) : Except String (Gate record × List TrustBase) := do
  let j ← Json.parse s
  return (← gateOf (← j.getObjVal? "successor"), ← (← strsOf j "lob").mapM trustOf)

def objJson (G : Gate record) (r : Rec) : Json := Json.mkObj [("judge", gateJson G), ("state", recJson r)]

def certJson (G' : Gate record) (L : List TrustBase) : Json :=
  Json.mkObj [("successor", gateJson G'), ("lob", Json.arr (L.map (Json.str ∘ trustText)).toArray)]

end Wire

/-- A refusal, said with the judges' names. -/
def Refusal.text (G G' : Gate record) : Refusal record → String
  | .dropsFloor φ => s!"{G'.name} drops the floor `{φ}`, which {G.name} exports"
  | .floorFails φ => s!"the floor `{φ}` of {G'.name} does not hold now"
  | .noBedrock => s!"{G'.name} exports no corrigibility floor (`home N`)"
  | .refusesRevert => s!"{G'.name} does not admit revert@1, which every judge admits"
  | .revertUnproved φ =>
    s!"{G'.name} discharges `{φ}` on revert@1 by evaluation; revert is admitted in every state, by the theorem"
  | .unchecked f φ => s!"{G'.name}'s checker does not discharge `{φ}` on {f}"
  | .unproved f φ => s!"{G'.name} cites a theorem that {f} preserves `{φ}`; there is none"
  | .undeclared f φ t =>
    s!"{G'.name} evaluates `{φ}` on {f} under {trustText t}, which its basis does not declare"
  | .stronger t =>
    s!"{G'.name} rests on {trustText t}, which {G.name} does not hold: a stronger successor, admitted only labelled with its Löb cost (--lob {trustText t})"
  | .labelNotNeeded t =>
    s!"the label {trustText t} is not needed: {G'.name} does not rest on it, or {G.name} already holds it"

/-- The planted certificate: at three writes from home, a successor of `lobGenesis` that drops the
cap on `a`. -/
def plantedSuccessor : Gate record :=
  { name := "g1", formats := ["write@1", "revert@1"], floors := [.home 3],
    methods := [("write@1", .home 3, .eval .kernel), ("revert@1", .home 3, .lemma)], basis := [.kernel] }

-- fixture kept (2026-11-05): consumed by `successionFormat.bad_refused`
theorem planted_refused :
    (successionJudge record).check 0 (lobGenesis, lobState) (plantedSuccessor, []) =
      .refused (.dropsFloor (.cap "a" 100)) [] := rfl

/-- **The registered format `judge-succession@1`.** The object is the current judge and the state,
the certificate the successor and its labels; the command line runs the checker compiled. -/
def successionFormat : Judge.Format where
  name := "judge-succession"
  version := "1"
  Obj := Gate record × Rec
  Cert := Gate record × List TrustBase
  judge := successionJudge record
  decodeObj := objOf
  decodeCert := certOf
  trust := .compiled
  regime := .decidable
  bad := ((lobGenesis, lobState), (plantedSuccessor, []))
  badGrade := 0
  bad_refused := ⟨_, _, planted_refused⟩
  explain _ obj cert := match objOf obj, certOf cert with
    | .ok (G, r), .ok (G', L) => match succeed G r G' L with
      | .error e => e.text G G'
      | .ok () => ""
    | .error e, _ => s!"object: {e}"
    | _, .error e => s!"certificate: {e}"

end Obend.Judge.Genealogy

end
