module
/-
# Obend.Core.Fill — substituting in variables and continuing the computation, at the object level

ember's principle: a captured situation stays live if its data can be replaced by variables, the
variables filled later, and the computation continued from where it stood, in the object language
itself rather than by re-running it. Here that is a theorem of the kernel's own term language.

A hole `.hole n σ` is a contextual metavariable: `σ` is the explicit substitution for the `Δ n`
variables of its context (`HoleArity Δ`). `Term.fill θ` replaces each hole that `θ` has a filler for
by the filler under `σ` (filled first); a filler mentions only its hole's `Δ n` variables
(`FillersScoped Δ θ`). Because the hole carries its context, filling crosses binders without
shifting, and it commutes with renaming and substitution (`fill_rename`, `fill_substitute`,
`fill_liftSubstitution`, `fill_instantiate`, `fill_mixBody`), proved once on the generic shape
(`fillS_rename`, `fillS_substitute` over `Tree.substitute_comp`/`substitute_rename`).

A hole is stuck (no rule of `Step` has one in a redex position) and is copied unevaluated, so every
step of a term with holes is a step of each of its fillings (`fill_step`, all twenty-nine rules), the
arity is kept by the step (`holeArity_step`), and so for runs (`fill_steps`). With
`Obend.Law.step_deterministic` this is the principle (`fill_continues`):

    Steps t r → (Evaluates (t.fill θ) v ↔ Evaluates (r.fill θ) v)

run the term with holes as far as it goes, fill, and continue: the same value as filling first.
`fill_evaluates`: a term that evaluates with its holes in it evaluates, filled, to its value filled.

The arity is what makes the substitution under a hole meaningful: an index past the end of `σ` is
left as a free variable, which is not shifted under binders, and commutation with substitution fails
there; with `σ` as long as the filler's scope it never arises.
-/
public import Obend.Core.TermTraverse
public import Obend.Law.Proofs.Run
@[expose] public section
set_option autoImplicit false

namespace Obend.Core.TermTraverse
open Obend.Core.Term Obend.Core.Traverse

/-- The shape a hole's substitution gives index `i`: its `i`-th entry. -/
def listSubstS (cs : List Shape) (i : Nat) : Shape := cs.getD i (.var i)

/-- A node with its children already filled: a hole with a filler is the filler under the hole's
substitution; anything else is itself. -/
def fillNode (θ : Nat → Option Shape) (tag : Tag) (cs : List Shape) : Shape :=
  match tag with
  | .hole n => match θ n with
    | some u => Tree.substitute (listSubstS cs) u
    | none => .node (.hole n) cs
  | _ => .node tag cs

def fillS (θ : Nat → Option Shape) : Shape → Shape
  | .var i => .var i
  | .bind b => .bind (fillS θ b)
  | .node tag cs => fillNode θ tag (cs.map (fillS θ))

def tagArity (Δ : Nat → Nat) (tag : Tag) (k : Nat) : Prop :=
  match tag with
  | .hole n => k = Δ n
  | _ => True

/-- Every hole `n` carries a substitution of length `Δ n`. -/
def ArityS (Δ : Nat → Nat) : Shape → Prop
  | .var _ => True
  | .bind b => ArityS Δ b
  | .node tag cs => tagArity Δ tag cs.length ∧ ∀ c ∈ cs, ArityS Δ c

/-- Every filler of hole `n` mentions only the `Δ n` variables its hole's substitution gives. -/
def FillersS (Δ : Nat → Nat) (θ : Nat → Option Shape) : Prop :=
  ∀ n u, θ n = some u → Tree.Scoped (Δ n) u

theorem rename_var' (f : Nat → Nat) (i : Nat) : Tree.rename f (.var i : Shape) = .var (f i) := by
  simp only [Tree.rename, Tree.traverse]
theorem rename_bind' (f : Nat → Nat) (b : Shape) :
    Tree.rename f (.bind b) = .bind (Tree.rename (liftRename f) b) := by
  simp only [Tree.rename, Tree.traverse]
theorem rename_node' (f : Nat → Nat) (tag : Tag) (cs : List Shape) :
    Tree.rename f (.node tag cs) = .node tag (cs.map (Tree.rename f)) := by
  simp only [Tree.rename, Tree.traverse]
theorem substitute_var' (σ : Nat → Shape) (i : Nat) : Tree.substitute σ (.var i) = σ i := by
  simp only [Tree.substitute, Tree.traverse]
theorem substitute_bind' (σ : Nat → Shape) (b : Shape) :
    Tree.substitute σ (.bind b) = .bind (Tree.substitute (Tree.liftSubst σ) b) := by
  simp only [Tree.substitute, Tree.traverse]
theorem substitute_node' (σ : Nat → Shape) (tag : Tag) (cs : List Shape) :
    Tree.substitute σ (.node tag cs) = .node tag (cs.map (Tree.substitute σ)) := by
  simp only [Tree.substitute, Tree.traverse]

theorem listSubstS_map (g : Shape → Shape) (cs : List Shape) (i : Nat) (h : i < cs.length) :
    listSubstS (cs.map g) i = g (listSubstS cs i) := by
  simp [listSubstS, List.getD_eq_getElem?_getD, h]

theorem fillNode_substitute (Δ : Nat → Nat) (θ : Nat → Option Shape) (hθ : FillersS Δ θ)
    (τ : Nat → Shape) (tag : Tag) (cs : List Shape) (h : tagArity Δ tag cs.length) :
    fillNode θ tag (cs.map (Tree.substitute τ)) = Tree.substitute τ (fillNode θ tag cs) := by
  cases tag
  case hole n =>
    simp only [fillNode]
    cases hn : θ n with
    | none => simp only [substitute_node']
    | some u =>
      simp only [tagArity] at h
      rw [Tree.substitute_comp]
      apply Tree.substitute_congr_on u _ (hθ n u hn)
      intro i hi
      exact listSubstS_map _ cs i (by omega)
  all_goals simp only [fillNode, substitute_node']

theorem fillNode_rename (Δ : Nat → Nat) (θ : Nat → Option Shape) (hθ : FillersS Δ θ)
    (f : Nat → Nat) (tag : Tag) (cs : List Shape) (h : tagArity Δ tag cs.length) :
    fillNode θ tag (cs.map (Tree.rename f)) = Tree.rename f (fillNode θ tag cs) := by
  cases tag
  case hole n =>
    simp only [fillNode]
    cases hn : θ n with
    | none => simp only [rename_node']
    | some u =>
      simp only [tagArity] at h
      rw [Tree.substitute_rename]
      apply Tree.substitute_congr_on u _ (hθ n u hn)
      intro i hi
      exact listSubstS_map _ cs i (by omega)
  all_goals simp only [fillNode, rename_node']

theorem tagArity_map (Δ : Nat → Nat) (tag : Tag) {α : Type} (g : α → Shape) (cs : List α) :
    tagArity Δ tag (cs.map g).length ↔ tagArity Δ tag cs.length := by
  rw [List.length_map]

theorem arityS_var (Δ : Nat → Nat) (i : Nat) : ArityS Δ (.var i) := by simp only [ArityS]
theorem arityS_bind (Δ : Nat → Nat) (b : Shape) : ArityS Δ (.bind b) ↔ ArityS Δ b := by
  simp only [ArityS]
theorem arityS_node (Δ : Nat → Nat) (tag : Tag) (cs : List Shape) :
    ArityS Δ (.node tag cs) ↔ tagArity Δ tag cs.length ∧ ∀ c ∈ cs, ArityS Δ c := by
  simp only [ArityS]
theorem fillS_var (θ : Nat → Option Shape) (i : Nat) : fillS θ (.var i) = .var i := by simp only [fillS]
theorem fillS_bind (θ : Nat → Option Shape) (b : Shape) : fillS θ (.bind b) = .bind (fillS θ b) := by
  simp only [fillS]
theorem fillS_node (θ : Nat → Option Shape) (tag : Tag) (cs : List Shape) :
    fillS θ (.node tag cs) = fillNode θ tag (cs.map (fillS θ)) := by
  simp only [fillS]

theorem arityS_rename (Δ : Nat → Nat) (t : Shape) (h : ArityS Δ t) (f : Nat → Nat) :
    ArityS Δ (Tree.rename f t) := by
  induction t using Tree.inductionOn generalizing f with
  | var i => rw [rename_var']; exact arityS_var Δ _
  | bind b ih => rw [rename_bind', arityS_bind]; exact ih ((arityS_bind Δ b).1 h) _
  | node tag cs ih =>
    rw [arityS_node] at h
    rw [rename_node', arityS_node]
    refine ⟨(tagArity_map Δ tag _ cs).2 h.1, ?_⟩
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact ih c' hc' (h.2 c' hc') f

theorem arityS_substitute (Δ : Nat → Nat) (t : Shape) (h : ArityS Δ t) (σ : Nat → Shape)
    (hσ : ∀ i, ArityS Δ (σ i)) : ArityS Δ (Tree.substitute σ t) := by
  induction t using Tree.inductionOn generalizing σ with
  | var i => rw [substitute_var']; exact hσ i
  | bind b ih =>
    rw [substitute_bind', arityS_bind]
    refine ih ((arityS_bind Δ b).1 h) _ ?_
    intro i; cases i with
    | zero => simp only [Tree.liftSubst]; exact arityS_var Δ _
    | succ i => simp only [Tree.liftSubst]; exact arityS_rename Δ _ (hσ i) _
  | node tag cs ih =>
    rw [arityS_node] at h
    rw [substitute_node', arityS_node]
    refine ⟨(tagArity_map Δ tag _ cs).2 h.1, ?_⟩
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact ih c' hc' (h.2 c' hc') σ hσ

theorem fillS_rename (Δ : Nat → Nat) (θ : Nat → Option Shape) (hθ : FillersS Δ θ) (t : Shape)
    (h : ArityS Δ t) (f : Nat → Nat) : fillS θ (Tree.rename f t) = Tree.rename f (fillS θ t) := by
  induction t using Tree.inductionOn generalizing f with
  | var i => rw [rename_var', fillS_var, fillS_var, rename_var']
  | bind b ih =>
    rw [rename_bind', fillS_bind, fillS_bind, ih ((arityS_bind Δ b).1 h), rename_bind']
  | node tag cs ih =>
    rw [arityS_node] at h
    rw [rename_node', fillS_node, fillS_node, List.map_map]
    have : cs.map (fillS θ ∘ Tree.rename f) = (cs.map (fillS θ)).map (Tree.rename f) := by
      rw [List.map_map]; exact List.map_congr_left (fun c hc => ih c hc (h.2 c hc) f)
    rw [this, fillNode_rename Δ θ hθ f tag _ ((tagArity_map Δ tag _ cs).2 h.1)]

theorem fillS_substitute (Δ : Nat → Nat) (θ : Nat → Option Shape) (hθ : FillersS Δ θ) (t : Shape)
    (h : ArityS Δ t) (σ : Nat → Shape) (hσ : ∀ i, ArityS Δ (σ i)) :
    fillS θ (Tree.substitute σ t) = Tree.substitute (fun i => fillS θ (σ i)) (fillS θ t) := by
  induction t using Tree.inductionOn generalizing σ with
  | var i => rw [substitute_var', fillS_var, substitute_var']
  | bind b ih =>
    rw [substitute_bind', fillS_bind, fillS_bind, ih ((arityS_bind Δ b).1 h) _ ?_, substitute_bind']
    · congr 2; funext i; cases i with
      | zero => simp only [Tree.liftSubst]; exact fillS_var θ 0
      | succ i => simp only [Tree.liftSubst]; exact fillS_rename Δ θ hθ (σ i) (hσ i) Nat.succ
    · intro i; cases i with
      | zero => simp only [Tree.liftSubst]; exact arityS_var Δ _
      | succ i => simp only [Tree.liftSubst]; exact arityS_rename Δ _ (hσ i) _
  | node tag cs ih =>
    rw [arityS_node] at h
    rw [substitute_node', fillS_node, fillS_node, List.map_map]
    have : cs.map (fillS θ ∘ Tree.substitute σ) =
        (cs.map (fillS θ)).map (Tree.substitute fun i => fillS θ (σ i)) := by
      rw [List.map_map]; exact List.map_congr_left (fun c hc => ih c hc (h.2 c hc) σ hσ)
    rw [this, fillNode_substitute Δ θ hθ _ tag _ ((tagArity_map Δ tag _ cs).2 h.1)]

/-- Filling keeps the arity when every filler has it. -/
theorem arityS_fillS (Δ : Nat → Nat) (θ : Nat → Option Shape) (hθa : ∀ n u, θ n = some u → ArityS Δ u)
    (t : Shape) (h : ArityS Δ t) : ArityS Δ (fillS θ t) := by
  induction t using Tree.inductionOn with
  | var i => rw [fillS_var]; exact arityS_var Δ _
  | bind b ih => rw [fillS_bind, arityS_bind]; exact ih ((arityS_bind Δ b).1 h)
  | node tag cs ih =>
    rw [arityS_node] at h
    have hcs : ∀ c ∈ cs.map (fillS θ), ArityS Δ c := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ih c' hc' (h.2 c' hc')
    rw [fillS_node]
    cases tag
    case hole n =>
      simp only [fillNode]
      cases hn : θ n with
      | none => exact (arityS_node Δ _ _).2 ⟨(tagArity_map Δ _ _ cs).2 h.1, hcs⟩
      | some u =>
        apply arityS_substitute Δ u (hθa n u hn)
        intro i
        simp only [listSubstS, List.getD_eq_getElem?_getD]
        cases hi : (cs.map (fillS θ))[i]? with
        | none => exact arityS_var Δ _
        | some c => exact hcs c (List.mem_of_getElem? hi)
    all_goals exact (arityS_node Δ _ _).2 ⟨trivial, hcs⟩

end Obend.Core.TermTraverse

namespace Obend.Core.Term
open Obend.Core.Traverse Obend.Core.TermTraverse

/-- The term a hole's substitution gives index `i`: its `i`-th entry. -/
def listSubst (σ : List Term) (i : Nat) : Term := σ.getD i (.bound i)

/-- Fill the holes `θ` has fillers for: `.hole n σ` becomes `θ n` with its variables replaced by
`σ`'s entries, filled first. A hole carries its context as `σ`, so filling crosses binders without
shifting. Fillers are not filled again. -/
def Term.fill (θ : Nat → Option Term) : Term → Term
  | .hole n σ => match θ n with
    | some u => u.substitute (listSubst (σ.map fun t => t.fill θ))
    | none => .hole n (σ.map fun t => t.fill θ)
  | .bound index => .bound index
  | .lam body => .lam (body.fill θ)
  | .app function argument => .app (function.fill θ) (argument.fill θ)
  | .mix first second => .mix (first.fill θ) (second.fill θ)
  | .fix spec inherited => .fix (spec.fill θ) (inherited.fill θ)
  | .specification descriptor extension => .specification (descriptor.fill θ) (extension.fill θ)
  | .prototype spec target => .prototype (spec.fill θ) (target.fill θ)
  | .reflect target => .reflect (target.fill θ)
  | .metadata spec => .metadata (spec.fill θ)
  | .project target => .project (target.fill θ)
  | .nat value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .binary primitive left right => .binary primitive (left.fill θ) (right.fill θ)
  | .extend inherited fields => .extend (inherited.fill θ)
      (fields.map fun field => (field.1, field.2.fill θ))
  | .record fields => .record (fields.map fun field => (field.1, field.2.fill θ))
  | .get target name => .get (target.fill θ) name
  | .ifZero value zero successorBody =>
      .ifZero (value.fill θ) (zero.fill θ) (successorBody.fill θ)
  | .inject tag payload => .inject tag (payload.fill θ)
  | .case scrutinee arms => .case (scrutinee.fill θ) (arms.map fun field => (field.1, field.2.fill θ))
  | .ifBool condition whenTrue whenFalse =>
      .ifBool (condition.fill θ) (whenTrue.fill θ) (whenFalse.fill θ)
  | .perform plan => .perform (plan.fill θ)
  | .done value => .done (value.fill θ)
  | .split target names function => .split (target.fill θ) names (function.fill θ)
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf field.snd < sizeOf field := by
         cases field
         simp +arith
       omega)

/-- Every hole `n` in `t` carries a substitution of length `Δ n`: its context has `Δ n` variables. -/
def HoleArity (Δ : Nat → Nat) (t : Term) : Prop := ArityS Δ (encode t)

/-- Every filler of hole `n` mentions only the `Δ n` variables of the hole's context. -/
def FillersScoped (Δ : Nat → Nat) (θ : Nat → Option Term) : Prop :=
  ∀ n u, θ n = some u → TermTraverse.Scoped (Δ n) u

theorem encode_listSubst (σ : List Term) (i : Nat) :
    encode (listSubst σ i) = listSubstS (σ.map encode) i := by
  simp only [listSubst, listSubstS, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases σ[i]? <;> simp [encode]

theorem encode_fill (θ : Nat → Option Term) (t : Term) :
    encode (t.fill θ) = fillS (fun n => (θ n).map encode) (encode t) := by
  cases t
  case hole n σ =>
    have hσ : (σ.map fun t => t.fill θ).map encode = (σ.map encode).map (fillS fun n => (θ n).map encode) := by
      simp only [List.map_map]
      apply List.map_congr_left; intro a ha
      exact encode_fill θ a
    rw [encode, fillS_node]
    simp only [Term.fill, fillNode]
    cases hn : θ n with
    | none => simp only [Option.map_none, encode, hσ]
    | some u =>
      simp only [Option.map_some, encode_substitute]
      congr 1; funext i
      rw [encode_listSubst, hσ]
  all_goals simp only [Term.fill, encode, fillS_node, fillS_bind, fillS_var, fillNode, List.map_cons,
    List.map_nil, List.map_map, Tree.node.injEq, Tree.bind.injEq, List.cons.injEq, and_true, true_and]
  all_goals
    repeat first
      | rfl
      | exact encode_fill _ _
      | (apply List.map_congr_left; intro a ha
         simp only [Function.comp_apply, fillS_node, fillS_bind, fillNode, List.map_cons, List.map_nil]
         rw [encode_fill θ a.2])
      | constructor
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have hlist := List.sizeOf_lt_of_mem ha
       have hpair : sizeOf a.snd < sizeOf a := by cases a; simp +arith
       omega)

theorem fillersS_of (Δ : Nat → Nat) (θ : Nat → Option Term) (hθ : FillersScoped Δ θ) :
    FillersS Δ (fun n => (θ n).map encode) := by
  intro n u hu
  cases hn : θ n with
  | none => simp [hn] at hu
  | some v =>
    simp only [hn, Option.map_some, Option.some.injEq] at hu
    subst hu; exact hθ n v hn

/-! ## Filling commutes with renaming and substitution -/

theorem holeArity_rename (Δ : Nat → Nat) (t : Term) (h : HoleArity Δ t) (f : Nat → Nat) :
    HoleArity Δ (t.rename f) := by
  unfold HoleArity; rw [encode_rename]; exact arityS_rename Δ _ h f

theorem holeArity_substitute (Δ : Nat → Nat) (t : Term) (h : HoleArity Δ t) (σ : Nat → Term)
    (hσ : ∀ i, HoleArity Δ (σ i)) : HoleArity Δ (t.substitute σ) := by
  unfold HoleArity; rw [encode_substitute]; exact arityS_substitute Δ _ h _ hσ

theorem holeArity_bound (Δ : Nat → Nat) (i : Nat) : HoleArity Δ (.bound i) := by
  unfold HoleArity; rw [encode]; exact arityS_var Δ i

theorem holeArity_instantiate (Δ : Nat → Nat) (body argument : Term) (hb : HoleArity Δ body)
    (ha : HoleArity Δ argument) : HoleArity Δ (instantiate body argument) := by
  apply holeArity_substitute Δ body hb
  intro i; cases i with
  | zero => exact ha
  | succ i => exact holeArity_bound Δ i

/-- A filled term keeps the arity when its fillers have it. -/
theorem holeArity_fill (Δ : Nat → Nat) (θ : Nat → Option Term) (hθa : ∀ n u, θ n = some u → HoleArity Δ u)
    (t : Term) (h : HoleArity Δ t) : HoleArity Δ (t.fill θ) := by
  unfold HoleArity; rw [encode_fill]
  apply arityS_fillS Δ _ _ _ h
  intro n u hu
  cases hn : θ n with
  | none => simp [hn] at hu
  | some v =>
    simp only [hn, Option.map_some, Option.some.injEq] at hu
    subst hu; exact hθa n v hn

theorem fill_rename {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) (t : Term)
    (h : HoleArity Δ t) (f : Nat → Nat) : (t.rename f).fill θ = (t.fill θ).rename f := by
  apply encode_injective
  rw [encode_fill, encode_rename, encode_rename, encode_fill]
  exact fillS_rename Δ _ (fillersS_of Δ θ hθ) _ h f

theorem fill_substitute {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) (t : Term)
    (h : HoleArity Δ t) (σ : Nat → Term) (hσ : ∀ i, HoleArity Δ (σ i)) :
    (t.substitute σ).fill θ = (t.fill θ).substitute (fun i => (σ i).fill θ) := by
  apply encode_injective
  rw [encode_fill, encode_substitute, encode_substitute, encode_fill]
  simp only [encode_fill]
  exact fillS_substitute Δ _ (fillersS_of Δ θ hθ) _ h _ hσ

theorem fill_liftSubstitution {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    (σ : Nat → Term) (hσ : ∀ i, HoleArity Δ (σ i)) (i : Nat) :
    (liftSubstitution σ i).fill θ = liftSubstitution (fun j => (σ j).fill θ) i := by
  cases i with
  | zero => simp only [liftSubstitution, Term.fill]
  | succ i => simp only [liftSubstitution]; exact fill_rename hθ (σ i) (hσ i) Nat.succ

theorem fill_instantiate {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    (body argument : Term) (hb : HoleArity Δ body) (ha : HoleArity Δ argument) :
    (instantiate body argument).fill θ = instantiate (body.fill θ) (argument.fill θ) := by
  unfold instantiate
  rw [fill_substitute hθ body hb]
  · congr 1; funext i; cases i <;> simp only [Term.fill]
  · intro i; cases i with
    | zero => exact ha
    | succ i => exact holeArity_bound Δ i

theorem fill_mixBody {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    (lower upper : Term) (hl : HoleArity Δ lower) (hu : HoleArity Δ upper) :
    (mixBody lower upper).fill θ = mixBody (lower.fill θ) (upper.fill θ) := by
  simp only [mixBody, Term.fill, fill_rename hθ lower hl, fill_rename hθ upper hu]

/-! ## Arity, constructor by constructor -/

section
variable {Δ : Nat → Nat}

@[simp] theorem holeArity_app (a b : Term) : HoleArity Δ (.app a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_mix (a b : Term) : HoleArity Δ (.mix a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_fix (a b : Term) : HoleArity Δ (.fix a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_specification (a b : Term) : HoleArity Δ (.specification a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_prototype (a b : Term) : HoleArity Δ (.prototype a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_binary (p : Primitive) (a b : Term) :
    HoleArity Δ (.binary p a b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_reflect (a : Term) : HoleArity Δ (.reflect a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_metadata (a : Term) : HoleArity Δ (.metadata a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_project (a : Term) : HoleArity Δ (.project a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_perform (a : Term) : HoleArity Δ (.perform a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_done (a : Term) : HoleArity Δ (.done a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_inject (l : String) (a : Term) : HoleArity Δ (.inject l a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_get (a : Term) (l : String) : HoleArity Δ (.get a l) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_lam (a : Term) : HoleArity Δ (.lam a) ↔ HoleArity Δ a := by
  simp [HoleArity, encode, arityS_bind]

@[simp] theorem holeArity_ifZero (a b c : Term) :
    HoleArity Δ (.ifZero a b c) ↔ HoleArity Δ a ∧ HoleArity Δ b ∧ HoleArity Δ c := by
  simp [HoleArity, encode, arityS_node, arityS_bind, tagArity]

@[simp] theorem holeArity_ifBool (a b c : Term) :
    HoleArity Δ (.ifBool a b c) ↔ HoleArity Δ a ∧ HoleArity Δ b ∧ HoleArity Δ c := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_split (a : Term) (ns : List String) (b : Term) :
    HoleArity Δ (.split a ns b) ↔ HoleArity Δ a ∧ HoleArity Δ b := by
  simp [HoleArity, encode, arityS_node, tagArity]

@[simp] theorem holeArity_record (fs : List (String × Term)) :
    HoleArity Δ (.record fs) ↔ ∀ f ∈ fs, HoleArity Δ f.2 := by
  simp only [HoleArity, encode, arityS_node, tagArity, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, imp_true_iff, and_true, true_and]

@[simp] theorem holeArity_extend (a : Term) (fs : List (String × Term)) :
    HoleArity Δ (.extend a fs) ↔ HoleArity Δ a ∧ ∀ f ∈ fs, HoleArity Δ f.2 := by
  simp only [HoleArity, encode, arityS_node, tagArity, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, imp_true_iff, and_true, true_and]

@[simp] theorem holeArity_case (a : Term) (arms : List (String × Term)) :
    HoleArity Δ (.case a arms) ↔ HoleArity Δ a ∧ ∀ f ∈ arms, HoleArity Δ f.2 := by
  simp only [HoleArity, encode, arityS_node, arityS_bind, tagArity, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, imp_true_iff, and_true, true_and]

@[simp] theorem holeArity_hole (n : Nat) (σ : List Term) :
    HoleArity Δ (.hole n σ) ↔ σ.length = Δ n ∧ ∀ t ∈ σ, HoleArity Δ t := by
  simp [HoleArity, encode, arityS_node, tagArity]

end

/-! ## What a step reads, filled -/

theorem value_fill (θ : Nat → Option Term) {t : Term} (h : Value t) : Value (t.fill θ) := by
  cases h <;> simp only [Term.fill] <;> constructor

/-- A scalar literal: what a primitive reads and writes. -/
def IsLiteral : Term → Prop
  | .nat _ => True
  | .boolean _ => True
  | .label _ => True
  | _ => False

theorem primitiveResult_literal {p : Primitive} {l r res : Term} (h : primitiveResult p l r = some res) :
    IsLiteral l ∧ IsLiteral r ∧ IsLiteral res := by
  unfold primitiveResult at h
  split at h <;> cases h <;> simp [IsLiteral]

theorem fill_literal (θ : Nat → Option Term) {t : Term} (h : IsLiteral t) : t.fill θ = t := by
  cases t <;> simp_all [IsLiteral, Term.fill]

theorem holeArity_literal (Δ : Nat → Nat) {t : Term} (h : IsLiteral t) : HoleArity Δ t := by
  cases t <;> simp_all [IsLiteral, HoleArity, encode, arityS_node, tagArity]

theorem extendFields_map (g : Term → Term) (inherited fields : List (String × Term)) :
    extendFields (inherited.map fun f => (f.1, g f.2)) (fields.map fun f => (f.1, g f.2)) =
      (extendFields inherited fields).map fun f => (f.1, g f.2) := by
  simp [extendFields, List.filter_map, Function.comp_def, List.any_map]

theorem applyAll_fill (θ : Nat → Option Term) (values : List Term) :
    ∀ function : Term,
      (applyAll function values).fill θ = applyAll (function.fill θ) (values.map fun v => v.fill θ) := by
  induction values with
  | nil => intro f; rfl
  | cons v vs ih => intro f; simp only [applyAll, List.map_cons, ih, Term.fill]

theorem splitValues_mem {α : Type} (fields : List (String × α)) :
    ∀ (names : List String) (values : List α), splitValues fields names = some values →
      ∀ v ∈ values, ∃ f ∈ fields, f.2 = v
  | [], values, h, v, hv => by simp [splitValues] at h; subst h; simp at hv
  | name :: names, values, h, v, hv => by
    simp only [splitValues] at h
    cases hf : fields.find? (fun field => field.1 == name) with
    | none => simp [hf] at h
    | some f =>
      cases hr : splitValues fields names with
      | none => simp [hf, hr] at h
      | some rest =>
        simp only [hf, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨f, List.mem_of_find?_eq_some hf, rfl⟩
        · exact splitValues_mem fields names rest hr v hv

theorem holeArity_applyAll (Δ : Nat → Nat) (values : List Term) (hv : ∀ v ∈ values, HoleArity Δ v) :
    ∀ function : Term, HoleArity Δ function → HoleArity Δ (applyAll function values) := by
  induction values with
  | nil => intro f hf; exact hf
  | cons v vs ih =>
    intro f hf
    simp only [applyAll]
    apply ih (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    simp only [HoleArity, encode, arityS_node, tagArity, List.mem_cons, List.not_mem_nil] at hf ⊢
    refine ⟨trivial, ?_⟩
    rintro c (rfl | rfl | h)
    · exact hf
    · exact hv v (List.mem_cons_self ..)
    · exact h.elim

/-! ## A step keeps the holes' arity -/

theorem holeArity_step (Δ : Nat → Nat) {t t' : Term} (s : Step t t') (h : HoleArity Δ t) : HoleArity Δ t' := by
  induction s with
  | beta body argument =>
    simp only [holeArity_app, holeArity_lam] at h
    exact holeArity_instantiate Δ body argument h.1 h.2
  | mix lower upper =>
    simp only [holeArity_mix] at h
    simp only [mixBody, holeArity_lam, holeArity_app]
    exact ⟨⟨holeArity_rename Δ _ h.2 _, holeArity_bound Δ 1⟩,
      ⟨holeArity_rename Δ _ h.1 _, holeArity_bound Δ 1⟩, holeArity_bound Δ 0⟩
  | fix spec inherited =>
    simp only [holeArity_fix] at h
    simp only [holeArity_app, holeArity_fix]
    exact ⟨⟨h.1, h⟩, h.2⟩
  | applySpecification metadata extension argument =>
    simp only [holeArity_app, holeArity_specification] at h ⊢; exact ⟨h.1.2, h.2⟩
  | reflectPrototype spec target => simp only [holeArity_reflect, holeArity_prototype] at h; exact h.1
  | metadataSpecification metadata extension =>
    simp only [holeArity_metadata, holeArity_specification] at h; exact h.1
  | projectPrototype spec target => simp only [holeArity_project, holeArity_prototype] at h; exact h.2
  | reflectStep _ ih => simp only [holeArity_reflect] at h ⊢; exact ih h
  | metadataStep _ ih => simp only [holeArity_metadata] at h ⊢; exact ih h
  | projectStep _ ih => simp only [holeArity_project] at h ⊢; exact ih h
  | application argument _ ih => simp only [holeArity_app] at h ⊢; exact ⟨ih h.1, h.2⟩
  | target name _ ih => simp only [holeArity_get] at h ⊢; exact ih h
  | field fields name body hf =>
    simp only [holeArity_get, holeArity_record] at h
    exact h _ (List.mem_of_find?_eq_some hf)
  | extendTarget fields _ ih => simp only [holeArity_extend] at h ⊢; exact ⟨ih h.1, h.2⟩
  | extendRecord inherited fields =>
    simp only [holeArity_extend, holeArity_record] at h ⊢
    intro f hf
    simp only [extendFields, List.mem_append, List.mem_filter] at hf
    rcases hf with hf | ⟨hf, _⟩
    · exact h.2 f hf
    · exact h.1 f hf
  | binaryLeft primitive right _ ih => simp only [holeArity_binary] at h ⊢; exact ⟨ih h.1, h.2⟩
  | binaryRight primitive left _ _ ih => simp only [holeArity_binary] at h ⊢; exact ⟨h.1, ih h.2⟩
  | primitive primitive left right result _ _ hr =>
    exact holeArity_literal Δ (primitiveResult_literal hr).2.2
  | condition zero successorBody _ ih => simp only [holeArity_ifZero] at h ⊢; exact ⟨ih h.1, h.2⟩
  | zero zero successorBody => simp only [holeArity_ifZero] at h; exact h.2.1
  | successor n zero successorBody =>
    simp only [holeArity_ifZero] at h
    exact holeArity_instantiate Δ _ _ h.2.2 (holeArity_literal Δ (by simp [IsLiteral]))
  | caseTarget arms _ ih => simp only [holeArity_case] at h ⊢; exact ⟨ih h.1, h.2⟩
  | caseInject label payload arms body hf =>
    simp only [holeArity_case, holeArity_inject] at h
    exact holeArity_instantiate Δ _ _ (h.2 _ (List.mem_of_find?_eq_some hf)) h.1
  | ifCondition whenTrue whenFalse _ ih => simp only [holeArity_ifBool] at h ⊢; exact ⟨ih h.1, h.2⟩
  | ifTrue whenTrue whenFalse => simp only [holeArity_ifBool] at h; exact h.2.1
  | ifFalse whenTrue whenFalse => simp only [holeArity_ifBool] at h; exact h.2.2
  | done value => simp only [holeArity_done] at h; exact h
  | splitTarget names function _ ih => simp only [holeArity_split] at h ⊢; exact ⟨ih h.1, h.2⟩
  | splitRecord fields names function values hv =>
    simp only [holeArity_split, holeArity_record] at h
    apply holeArity_applyAll Δ values _ function h.2
    intro v hv'
    obtain ⟨f, hf, rfl⟩ := splitValues_mem fields names values hv v hv'
    exact h.1 f hf

/-! ## Filling commutes with the step -/

/-- **A step of the term with holes is a step of every filling of it.** Holes are stuck (no rule
has one in its redex position) and are copied unevaluated, so filling them before or after the
step gives the same term. -/
theorem fill_step {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) {t t' : Term}
    (s : Step t t') (h : HoleArity Δ t) : Step (t.fill θ) (t'.fill θ) := by
  induction s with
  | beta body argument =>
    simp only [holeArity_app, holeArity_lam] at h
    simp only [Term.fill]
    rw [fill_instantiate hθ body argument h.1 h.2]
    exact .beta _ _
  | mix lower upper =>
    simp only [holeArity_mix] at h
    simp only [Term.fill]
    rw [fill_mixBody hθ lower upper h.1 h.2]
    exact .mix _ _
  | fix spec inherited => simp only [Term.fill]; exact .fix _ _
  | applySpecification metadata extension argument =>
    simp only [Term.fill]; exact .applySpecification _ _ _
  | reflectPrototype spec target => simp only [Term.fill]; exact .reflectPrototype _ _
  | metadataSpecification metadata extension => simp only [Term.fill]; exact .metadataSpecification _ _
  | projectPrototype spec target => simp only [Term.fill]; exact .projectPrototype _ _
  | reflectStep _ ih => simp only [holeArity_reflect] at h; simp only [Term.fill]; exact .reflectStep (ih h)
  | metadataStep _ ih =>
    simp only [holeArity_metadata] at h; simp only [Term.fill]; exact .metadataStep (ih h)
  | projectStep _ ih => simp only [holeArity_project] at h; simp only [Term.fill]; exact .projectStep (ih h)
  | application argument _ ih =>
    simp only [holeArity_app] at h; simp only [Term.fill]; exact .application _ (ih h.1)
  | target name _ ih => simp only [holeArity_get] at h; simp only [Term.fill]; exact .target name (ih h)
  | field fields name body hf =>
    simp only [Term.fill]
    have hm := find?_map_snd (fun t : Term => t.fill θ) name fields
    simp only [hf, Option.map_some] at hm
    exact .field _ name _ hm
  | extendTarget fields _ ih =>
    simp only [holeArity_extend] at h; simp only [Term.fill]; exact .extendTarget _ (ih h.1)
  | extendRecord inherited fields =>
    simp only [Term.fill]
    rw [← extendFields_map (fun t : Term => t.fill θ) inherited fields]
    exact .extendRecord _ _
  | binaryLeft primitive right _ ih =>
    simp only [holeArity_binary] at h; simp only [Term.fill]; exact .binaryLeft primitive _ (ih h.1)
  | binaryRight primitive left hv _ ih =>
    simp only [holeArity_binary] at h; simp only [Term.fill]
    exact .binaryRight primitive _ (value_fill θ hv) (ih h.2)
  | primitive primitive left right result hl hr hres =>
    obtain ⟨ll, lr, lres⟩ := primitiveResult_literal hres
    simp only [Term.fill]
    rw [fill_literal θ ll, fill_literal θ lr, fill_literal θ lres]
    exact .primitive primitive left right result hl hr hres
  | condition zero successorBody _ ih =>
    simp only [holeArity_ifZero] at h; simp only [Term.fill]; exact .condition _ _ (ih h.1)
  | zero zero successorBody => simp only [Term.fill]; exact .zero _ _
  | successor n zero successorBody =>
    simp only [holeArity_ifZero] at h
    simp only [Term.fill]
    rw [fill_instantiate hθ successorBody (.nat n) h.2.2 (holeArity_literal Δ (by simp [IsLiteral]))]
    simp only [Term.fill]
    exact .successor n _ _
  | caseTarget arms _ ih =>
    simp only [holeArity_case] at h; simp only [Term.fill]; exact .caseTarget _ (ih h.1)
  | caseInject label payload arms body hf =>
    simp only [holeArity_case, holeArity_inject] at h
    simp only [Term.fill]
    rw [fill_instantiate hθ body payload (h.2 _ (List.mem_of_find?_eq_some hf)) h.1]
    have hm := find?_map_snd (fun t : Term => t.fill θ) label arms
    simp only [hf, Option.map_some] at hm
    exact .caseInject label _ _ _ hm
  | ifCondition whenTrue whenFalse _ ih =>
    simp only [holeArity_ifBool] at h; simp only [Term.fill]; exact .ifCondition _ _ (ih h.1)
  | ifTrue whenTrue whenFalse => simp only [Term.fill]; exact .ifTrue _ _
  | ifFalse whenTrue whenFalse => simp only [Term.fill]; exact .ifFalse _ _
  | done value => simp only [Term.fill]; exact .done _
  | splitTarget names function _ ih =>
    simp only [holeArity_split] at h; simp only [Term.fill]; exact .splitTarget names _ (ih h.1)
  | splitRecord fields names function values hv =>
    simp only [Term.fill]
    rw [applyAll_fill]
    have hm := splitValues_map (fun t : Term => t.fill θ) fields names
    simp only [hv, Option.map_some] at hm
    exact .splitRecord _ names _ _ hm

theorem holeArity_steps (Δ : Nat → Nat) {t r : Term} (s : Steps t r) (h : HoleArity Δ t) : HoleArity Δ r := by
  induction s with
  | refl => exact h
  | next first _ ih => exact ih (holeArity_step Δ first h)

theorem fill_steps {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) {t r : Term}
    (s : Steps t r) (h : HoleArity Δ t) : Steps (t.fill θ) (r.fill θ) := by
  induction s with
  | refl => exact .refl _
  | next first _ ih => exact .next (fill_step hθ first h) (ih (holeArity_step Δ first h))

/-! ## Substituting in variables and continuing the computation -/

/-- **The object-level substitution principle.** Run a term with holes as far as it goes, to `r`;
fill the holes; continue. That is evaluating the filled original: the work done before the fill is
never redone and never wrong. -/
theorem fill_continues {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) {t r : Term}
    (s : Steps t r) (h : HoleArity Δ t) (v : Term) :
    Evaluates (t.fill θ) v ↔ Evaluates (r.fill θ) v :=
  ⟨Obend.Law.evaluates_of_steps (fill_steps hθ s h), Obend.Law.evaluates_steps (fill_steps hθ s h)⟩

/-- A term that evaluates with its holes in it evaluates, filled, to its value filled. -/
theorem fill_evaluates {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) {t w : Term}
    (e : Evaluates t w) (h : HoleArity Δ t) : Evaluates (t.fill θ) (w.fill θ) :=
  ⟨fill_steps hθ e.1 h, value_fill θ e.2⟩

end Obend.Core.Term
