module
/-
# Obend.Category.GradedLogic — 5-axis resource/effect grade monoid & graded Hoare logic

Compositional resource-graded stateful computation and Hoare triples over any `[GradeMonoid G]`,
specialized to the 5-axis `CompositeGrade`:

- `CompositeGrade`: tracks linear/affine `uses : Nat`, truncation/rounding `errorNum : Nat`,
  cryptographic/FHE `noise : Nat`, execution `cycles : Nat`, and signed `exergy : Int`, equipped
  with a lawful `GradeMonoid CompositeGrade` instance.
- `GradedM G σ α`: state-and-cost monad `σ → α × σ × G` accumulating grades via `GradeMonoid`
  addition, with lawful `Monad` equations (`pure_bind`, `bind_pure`, `bind_assoc`).
- `GradedTriple P cmd g Q`: total-correctness graded Hoare triple asserting that from any state
  satisfying `P`, `cmd` establishes `Q` within grade budget `cost ≤ g`.
- Structural & compositional rules:
  - `pure_triple` (zero cost `0`),
  - `bind_triple` (sequential composition adds grades `g₁ + g₂`),
  - `conseq_triple` (precondition strengthening, postcondition weakening, grade relaxation `g ≤ g'`),
  - `frame_triple` (separating state-lens projection `StateLens Ω σ Frame` preserving disjoint frame `F`),
  - `loop_triple` (`N`-iteration `repeatN` accumulating `GradeMonoid.nsmul N g`).
-/
public import Obend.Category.Refines
public section
namespace Obend.Category
set_option autoImplicit false

universe u v w w'

/-! ## 1. The 5-Axis Resource/Effect Grade (`CompositeGrade`) -/

/-- Polymorphic 5-axis cyber-physical & cryptographic resource grade:
    - `uses`: linear/resource consumption count
    - `errorNum`: numerical/fixed-point error numerator bound
    - `noise`: lattice/FHE ciphertext noise growth
    - `cycles`: clock cycle / step budget
    - `exergy`: signed net free-energy / dissipation delta -/
structure CompositeGrade where
  uses : Nat := 0
  errorNum : Nat := 0
  noise : Nat := 0
  cycles : Nat := 0
  exergy : Int := 0
  deriving @[expose] DecidableEq, Repr

namespace CompositeGrade

instance : Zero CompositeGrade where
  zero := ⟨0, 0, 0, 0, 0⟩

instance : Add CompositeGrade where
  add g₁ g₂ :=
    { uses := g₁.uses + g₂.uses
      errorNum := g₁.errorNum + g₂.errorNum
      noise := g₁.noise + g₂.noise
      cycles := g₁.cycles + g₂.cycles
      exergy := g₁.exergy + g₂.exergy }

instance : LE CompositeGrade where
  le g₁ g₂ :=
    g₁.uses ≤ g₂.uses ∧
    g₁.errorNum ≤ g₂.errorNum ∧
    g₁.noise ≤ g₂.noise ∧
    g₁.cycles ≤ g₂.cycles ∧
    g₁.exergy ≤ g₂.exergy

instance (g₁ g₂ : CompositeGrade) : Decidable (g₁ ≤ g₂) :=
  inferInstanceAs (Decidable
    (g₁.uses ≤ g₂.uses ∧ g₁.errorNum ≤ g₂.errorNum ∧ g₁.noise ≤ g₂.noise ∧
     g₁.cycles ≤ g₂.cycles ∧ g₁.exergy ≤ g₂.exergy))

@[simp] theorem add_uses (g₁ g₂ : CompositeGrade) : (g₁ + g₂).uses = g₁.uses + g₂.uses := rfl
@[simp] theorem add_errorNum (g₁ g₂ : CompositeGrade) : (g₁ + g₂).errorNum = g₁.errorNum + g₂.errorNum := rfl
@[simp] theorem add_noise (g₁ g₂ : CompositeGrade) : (g₁ + g₂).noise = g₁.noise + g₂.noise := rfl
@[simp] theorem add_cycles (g₁ g₂ : CompositeGrade) : (g₁ + g₂).cycles = g₁.cycles + g₂.cycles := rfl
@[simp] theorem add_exergy (g₁ g₂ : CompositeGrade) : (g₁ + g₂).exergy = g₁.exergy + g₂.exergy := rfl

theorem le_iff (g₁ g₂ : CompositeGrade) :
    g₁ ≤ g₂ ↔
      g₁.uses ≤ g₂.uses ∧
      g₁.errorNum ≤ g₂.errorNum ∧
      g₁.noise ≤ g₂.noise ∧
      g₁.cycles ≤ g₂.cycles ∧
      g₁.exergy ≤ g₂.exergy := by
  constructor <;> exact fun h => h

instance instGradeMonoid : GradeMonoid CompositeGrade where
  add_zero g := by
    rcases g with ⟨u, e, n, c, x⟩
    change CompositeGrade.mk (u + 0) (e + 0) (n + 0) (c + 0) (x + 0) = CompositeGrade.mk u e n c x
    simp
  zero_add g := by
    rcases g with ⟨u, e, n, c, x⟩
    change CompositeGrade.mk (0 + u) (0 + e) (0 + n) (0 + c) (0 + x) = CompositeGrade.mk u e n c x
    simp
  add_assoc a b c := by
    rcases a with ⟨u₁, e₁, n₁, c₁, x₁⟩
    rcases b with ⟨u₂, e₂, n₂, c₂, x₂⟩
    rcases c with ⟨u₃, e₃, n₃, c₃, x₃⟩
    change CompositeGrade.mk (u₁ + u₂ + u₃) (e₁ + e₂ + e₃) (n₁ + n₂ + n₃) (c₁ + c₂ + c₃) (x₁ + x₂ + x₃) =
      CompositeGrade.mk (u₁ + (u₂ + u₃)) (e₁ + (e₂ + e₃)) (n₁ + (n₂ + n₃)) (c₁ + (c₂ + c₃)) (x₁ + (x₂ + x₃))
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Int.add_assoc]
  add_comm a b := by
    rcases a with ⟨u₁, e₁, n₁, c₁, x₁⟩
    rcases b with ⟨u₂, e₂, n₂, c₂, x₂⟩
    change CompositeGrade.mk (u₁ + u₂) (e₁ + e₂) (n₁ + n₂) (c₁ + c₂) (x₁ + x₂) =
      CompositeGrade.mk (u₂ + u₁) (e₂ + e₁) (n₂ + n₁) (c₂ + c₁) (x₂ + x₁)
    rw [Nat.add_comm u₁, Nat.add_comm e₁, Nat.add_comm n₁, Nat.add_comm c₁, Int.add_comm x₁]
  le_refl g :=
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Int.le_refl _⟩
  le_trans h₁ h₂ :=
    ⟨Nat.le_trans h₁.1 h₂.1,
     Nat.le_trans h₁.2.1 h₂.2.1,
     Nat.le_trans h₁.2.2.1 h₂.2.2.1,
     Nat.le_trans h₁.2.2.2.1 h₂.2.2.2.1,
     Int.le_trans h₁.2.2.2.2 h₂.2.2.2.2⟩
  add_mono h₁ h₂ :=
    ⟨Nat.add_le_add h₁.1 h₂.1,
     Nat.add_le_add h₁.2.1 h₂.2.1,
     Nat.add_le_add h₁.2.2.1 h₂.2.2.1,
     Nat.add_le_add h₁.2.2.2.1 h₂.2.2.2.1,
     Int.add_le_add h₁.2.2.2.2 h₂.2.2.2.2⟩

@[simp] theorem nsmul_uses (n : Nat) (g : CompositeGrade) :
    (GradeMonoid.nsmul n g).uses = n * g.uses := by
  induction n with
  | zero => simp [GradeMonoid.nsmul]; rfl
  | succ k ih =>
    simp [GradeMonoid.nsmul, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nsmul_errorNum (n : Nat) (g : CompositeGrade) :
    (GradeMonoid.nsmul n g).errorNum = n * g.errorNum := by
  induction n with
  | zero => simp [GradeMonoid.nsmul]; rfl
  | succ k ih =>
    simp [GradeMonoid.nsmul, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nsmul_noise (n : Nat) (g : CompositeGrade) :
    (GradeMonoid.nsmul n g).noise = n * g.noise := by
  induction n with
  | zero => simp [GradeMonoid.nsmul]; rfl
  | succ k ih =>
    simp [GradeMonoid.nsmul, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nsmul_cycles (n : Nat) (g : CompositeGrade) :
    (GradeMonoid.nsmul n g).cycles = n * g.cycles := by
  induction n with
  | zero => simp [GradeMonoid.nsmul]; rfl
  | succ k ih =>
    simp [GradeMonoid.nsmul, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nsmul_exergy (n : Nat) (g : CompositeGrade) :
    (GradeMonoid.nsmul n g).exergy = (n : Int) * g.exergy := by
  induction n with
  | zero =>
    change (0 : Int) = ((0 : Nat) : Int) * g.exergy
    simp
  | succ k ih =>
    simp only [GradeMonoid.nsmul, add_exergy, ih]
    rw [Int.natCast_add, Int.add_mul]
    simp [Int.add_comm]

end CompositeGrade

/-! ## 2. Separating State Lenses (`StateLens`) -/

/-- A lawful separating decomposition `Ω ≃ σ × Frame` splitting global state `Ω` into a local
    footprint `σ` and an untouched disjoint frame `Frame`. -/
structure StateLens (Ω : Type v) (σ : Type w) (Frame : Type w') where
  view : Ω → σ × Frame
  build : σ → Frame → Ω
  view_build : ∀ (s : σ) (f : Frame), view (build s f) = (s, f)
  build_view : ∀ ω : Ω, build (view ω).1 (view ω).2 = ω

namespace StateLens

/-- Canonical lens focusing on the left component of `σ₁ × σ₂` with frame `σ₂`. -/
@[expose] def fst (σ₁ : Type w) (σ₂ : Type w') : StateLens (σ₁ × σ₂) σ₁ σ₂ where
  view p := p
  build s f := (s, f)
  view_build _ _ := rfl
  build_view _ := rfl

/-- Canonical lens focusing on the right component of `σ₁ × σ₂` with frame `σ₁`. -/
@[expose] def snd (σ₁ : Type w') (σ₂ : Type w) : StateLens (σ₁ × σ₂) σ₂ σ₁ where
  view p := (p.2, p.1)
  build s f := (f, s)
  view_build _ _ := rfl
  build_view _ := rfl

end StateLens

/-! ## 3. Graded State Monad (`GradedM`) -/

/-- Resource-graded stateful computation over grade monoid `G` and state `σ`. -/
structure GradedM (G : Type u) (σ : Type v) (α : Type w) where
  run : σ → α × σ × G

namespace GradedM

@[expose] def pure {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} (a : α) : GradedM G σ α where
  run s := (a, s, 0)

@[expose] def bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    (m : GradedM G σ α) (k : α → GradedM G σ β) : GradedM G σ β where
  run s :=
    let (a, s₁, c₁) := m.run s
    let (b, s₂, c₂) := (k a).run s₁
    (b, s₂, c₁ + c₂)

instance {G : Type u} [GradeMonoid G] {σ : Type v} : Monad (GradedM G σ) where
  pure := GradedM.pure
  bind := GradedM.bind

@[simp] theorem pure_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    (a : α) (k : α → GradedM G σ β) :
    (GradedM.pure a).bind k = k a := by
  cases hk : k a with
  | mk runK =>
    apply congrArg GradedM.mk
    funext s
    simp [GradedM.pure, hk, GradeMonoid.zero_add]

@[simp] theorem bind_pure {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    (m : GradedM G σ α) :
    m.bind GradedM.pure = m := by
  cases m with
  | mk runM =>
    apply congrArg GradedM.mk
    funext s
    simp [GradedM.pure, GradeMonoid.add_zero]

theorem bind_assoc {G : Type u} [GradeMonoid G] {σ : Type v} {α β γ : Type w}
    (m : GradedM G σ α) (f : α → GradedM G σ β) (g : β → GradedM G σ γ) :
    (m.bind f).bind g = m.bind (fun a => (f a).bind g) := by
  apply congrArg GradedM.mk
  funext s
  simp [GradedM.bind, GradeMonoid.add_assoc]

/-- Charge grade `cost : G` without altering state. -/
@[expose] def tick {G : Type u} {σ : Type v} (cost : G) : GradedM G σ Unit where
  run s := ((), s, cost)

/-- Read current state at zero grade cost. -/
@[expose] def get {G : Type u} [GradeMonoid G] {σ : Type v} : GradedM G σ σ where
  run s := (s, s, 0)

/-- Transform state via `f : σ → σ` while charging `cost : G`. -/
@[expose] def modifyCost {G : Type u} {σ : Type v} (f : σ → σ) (cost : G) : GradedM G σ Unit where
  run s := ((), f s, cost)

/-- Transform state and emit a return value via `step : σ → α × σ` at cost `cost : G`. -/
@[expose] def actionCost {G : Type u} {σ : Type v} {α : Type w}
    (step : σ → α × σ) (cost : G) : GradedM G σ α where
  run s :=
    let (a, s') := step s
    (a, s', cost)

/-- Lift a local command `GradedM G σ α` onto global state `Ω` along a `StateLens Ω σ Frame`. -/
@[expose] def zoom {G : Type u} {Ω : Type v} {σ : Type w} {Frame : Type w'} {α : Type u}
    (L : StateLens Ω σ Frame) (cmd : GradedM G σ α) : GradedM G Ω α where
  run ω :=
    let (s, frame) := L.view ω
    let (a, s', c) := cmd.run s
    (a, L.build s' frame, c)

/-- Iterate `body : α → GradedM G σ α` exactly `N` times starting from `a₀`. -/
@[expose] def repeatN {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} :
    Nat → (α → GradedM G σ α) → α → GradedM G σ α
  | 0, _, a => GradedM.pure a
  | n + 1, body, a => (body a).bind (fun a' => repeatN n body a')

end GradedM

/-! ## 4. Graded Hoare Triples & Structural Rules -/

/-- Graded Hoare triple `{P} cmd @[g] {Q}`: from any state `s` satisfying `P s`, executing `cmd`
    produces `(a, s', cost)` with `Q a s'` and `cost ≤ g`. -/
@[expose] def GradedTriple {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    (P : σ → Prop) (cmd : GradedM G σ α) (g : G) (Q : α → σ → Prop) : Prop :=
  ∀ s : σ, P s →
    let (a, s', cost) := cmd.run s
    Q a s' ∧ cost ≤ g

/-- **Pure Rule (`pure_triple`).** Returning `a` establishes `r = a ∧ P s` at grade `0`. -/
theorem pure_triple {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    (P : σ → Prop) (a : α) :
    GradedTriple (G := G) P (GradedM.pure a) 0 (fun r s => r = a ∧ P s) := by
  intro s hp
  exact ⟨⟨rfl, hp⟩, GradeMonoid.le_refl 0⟩

/-- **Sequential Bind Rule (`bind_triple`).** Grades compose additively (`g₁ + g₂`). -/
theorem bind_triple {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    {P : σ → Prop} {m : GradedM G σ α} {g₁ : G} {R : α → σ → Prop}
    {k : α → GradedM G σ β} {g₂ : G} {Q : β → σ → Prop}
    (hm : GradedTriple P m g₁ R)
    (hk : ∀ a : α, GradedTriple (R a) (k a) g₂ Q) :
    GradedTriple P (m.bind k) (g₁ + g₂) Q := by
  intro s hp
  have ⟨hr, hc₁⟩ := hm s hp
  have ⟨hq, hc₂⟩ := hk (m.run s).1 (m.run s).2.1 hr
  exact ⟨hq, GradeMonoid.add_mono hc₁ hc₂⟩

/-- **Rule of Consequence (`conseq_triple`).** Strengthens precondition, weakens postcondition,
    and relaxes grade budget `g ≤ g'`. -/
theorem conseq_triple {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {P P' : σ → Prop} {cmd : GradedM G σ α} {g g' : G} {Q Q' : α → σ → Prop}
    (hPre : ∀ s : σ, P' s → P s)
    (hPost : ∀ (a : α) (s : σ), Q a s → Q' a s)
    (hGrade : g ≤ g')
    (hCmd : GradedTriple P cmd g Q) :
    GradedTriple P' cmd g' Q' := by
  intro s hp'
  have ⟨hq, hc⟩ := hCmd s (hPre s hp')
  exact ⟨hPost _ _ hq, GradeMonoid.le_trans hc hGrade⟩

/-- **Separating State-Projection Frame Rule (`frame_triple`).**
    Any invariant `F : Frame → Prop` over the disjoint complement of `L : StateLens Ω σ Frame`
    survives `cmd.zoom L` untouched with identical grade `g`. -/
theorem frame_triple {G : Type u} [GradeMonoid G]
    {Ω : Type v} {σ : Type w} {Frame : Type w'} {α : Type u}
    (L : StateLens Ω σ Frame)
    {P : σ → Prop} {cmd : GradedM G σ α} {g : G} {Q : α → σ → Prop}
    (F : Frame → Prop)
    (hLocal : GradedTriple P cmd g Q) :
    GradedTriple
      (fun ω => P (L.view ω).1 ∧ F (L.view ω).2)
      (cmd.zoom L)
      g
      (fun a ω' => Q a (L.view ω').1 ∧ F (L.view ω').2) := by
  intro ω ⟨hp, hf⟩
  have ⟨hq, hc⟩ := hLocal (L.view ω).1 hp
  dsimp only [GradedM.zoom]
  rw [L.view_build]
  exact ⟨⟨hq, hf⟩, hc⟩

/-- **Bounded `N`-Iteration Loop Rule (`loop_triple`).**
    Iterating `body` `N` times with step grade `g` preserves loop invariant `Inv` within
    total grade `GradeMonoid.nsmul N g` (`N • g`). -/
theorem loop_triple {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    (N : Nat) {body : α → GradedM G σ α} {g : G}
    (Inv : α → σ → Prop)
    (hStep : ∀ a : α, GradedTriple (Inv a) (body a) g Inv)
    (a₀ : α) :
    GradedTriple (Inv a₀) (GradedM.repeatN N body a₀) (GradeMonoid.nsmul N g) Inv := by
  induction N generalizing a₀ with
  | zero =>
    exact conseq_triple
      (fun _ h => h)
      (fun _ _ ⟨heq, hinv⟩ => heq ▸ hinv)
      (GradeMonoid.le_refl 0)
      (pure_triple (Inv a₀) a₀)
  | succ n ih =>
    exact bind_triple (hStep a₀) (fun a' => ih a')

/-! ## 5. Weakest-Precondition VCG Lemmas (Used by `by graded_vcg`) -/

theorem vcg_pure {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {P : σ → Prop} (a : α) {g : G} {Q : α → σ → Prop}
    (hGrade : (0 : G) ≤ g) (hImp : ∀ s : σ, P s → Q a s) :
    GradedTriple P (GradedM.pure a) g Q :=
  conseq_triple (fun _ h => h) (fun _ s ⟨rfl, hp⟩ => hImp s hp) hGrade (pure_triple P a)

theorem vcg_tick {G : Type u} [GradeMonoid G] {σ : Type v}
    {P : σ → Prop} (cost : G) {g : G} {Q : Unit → σ → Prop}
    (hGrade : cost ≤ g) (hImp : ∀ s : σ, P s → Q () s) :
    GradedTriple P (GradedM.tick cost) g Q :=
  fun s hp => ⟨hImp s hp, hGrade⟩

theorem vcg_get {G : Type u} [GradeMonoid G] {σ : Type v}
    {P : σ → Prop} {g : G} {Q : σ → σ → Prop}
    (hGrade : (0 : G) ≤ g) (hImp : ∀ s : σ, P s → Q s s) :
    GradedTriple P GradedM.get g Q :=
  fun s hp => ⟨hImp s hp, hGrade⟩

theorem vcg_modifyCost {G : Type u} [GradeMonoid G] {σ : Type v}
    {P : σ → Prop} (f : σ → σ) (cost : G) {g : G} {Q : Unit → σ → Prop}
    (hGrade : cost ≤ g) (hImp : ∀ s : σ, P s → Q () (f s)) :
    GradedTriple P (GradedM.modifyCost f cost) g Q :=
  fun s hp => ⟨hImp s hp, hGrade⟩

theorem vcg_actionCost {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {P : σ → Prop} (step : σ → α × σ) (cost : G) {g : G} {Q : α → σ → Prop}
    (hGrade : cost ≤ g) (hImp : ∀ s : σ, P s → Q (step s).1 (step s).2) :
    GradedTriple P (GradedM.actionCost step cost) g Q :=
  fun s hp => ⟨hImp s hp, hGrade⟩

theorem vcg_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    {P : σ → Prop} {m : GradedM G σ α} {k : α → GradedM G σ β}
    {g₁ g₂ g : G} {R : α → σ → Prop} {Q : β → σ → Prop}
    (hm : GradedTriple P m g₁ R)
    (hk : ∀ a : α, GradedTriple (R a) (k a) g₂ Q)
    (hGrade : g₁ + g₂ ≤ g) :
    GradedTriple P (m.bind k) g Q :=
  conseq_triple (fun _ h => h) (fun _ _ h => h) hGrade (bind_triple hm hk)

end Obend.Category
end
