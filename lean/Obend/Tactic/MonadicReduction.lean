module
/- Source-first congruence for executable proof reduction. Register locally
where simplifying a symbolic continuation would expand speculative branches. -/
public import Lean
@[expose] public section
namespace Obend.Tactic.MonadicReduction
set_option autoImplicit false
universe u v w

/-- Simplify the source first and leave its continuation fixed. Once the source
is `some`, the ordinary bind equation substitutes the actual value before the
continuation is simplified. No global congruence behavior is changed. -/
theorem option_bind_source_congr {α : Type u} {β : Type v}
    (source replacement : Option α) (same : source = replacement)
    (next : α → Option β) : source.bind next = replacement.bind next :=
  congrArg (fun value => value.bind next) same

/-- The same source-first normalization boundary for error-producing code. -/
theorem except_bind_source_congr {ε : Type u} {α : Type v} {β : Type w}
    (source replacement : Except ε α) (same : source = replacement)
    (next : α → Except ε β) : source.bind next = replacement.bind next :=
  congrArg (fun value => value.bind next) same

theorem except_monad_bind {ε α β : Type}
    (source : Except ε α) (next : α → Except ε β) :
    (source >>= next) = source.bind next := rfl

theorem except_bind_ok {ε α β : Type}
    (value : α) (next : α → Except ε β) :
    (Except.ok value : Except ε α).bind next = next value := rfl

theorem except_bind_error {ε α β : Type}
    (error : ε) (next : α → Except ε β) :
    (Except.error error : Except ε α).bind next = .error error := rfl

theorem except_map_source_congr {ε α β : Type}
    (next : α → β) (source replacement : Except ε α) (same : source = replacement) :
    Except.map next source = Except.map next replacement :=
  congrArg (Except.map next) same

theorem except_functor_map {ε α β : Type}
    (next : α → β) (source : Except ε α) :
    next <$> source = Except.map next source := rfl

theorem except_map_ok {ε α β : Type} (next : α → β) (value : α) :
    Except.map next (.ok value : Except ε α) = .ok (next value) := rfl

theorem except_map_error {ε α β : Type} (next : α → β) (error : ε) :
    Except.map next (.error error : Except ε α) = .error error := rfl

theorem option_monad_bind {α β : Type}
    (source : Option α) (next : α → Option β) :
    (source >>= next) = source.bind next := rfl

theorem option_bind_some {α β : Type}
    (value : α) (next : α → Option β) :
    (some value).bind next = next value := rfl

theorem option_bind_none {α β : Type}
    (next : α → Option β) :
    (none : Option α).bind next = none := rfl

theorem option_map_source_congr {α β : Type}
    (next : α → β) (source replacement : Option α) (same : source = replacement) :
    Option.map next source = Option.map next replacement :=
  congrArg (Option.map next) same

theorem option_functor_map {α β : Type}
    (next : α → β) (source : Option α) :
    next <$> source = Option.map next source := rfl

theorem option_map_some {α β : Type} (next : α → β) (value : α) :
    Option.map next (some value) = some (next value) := rfl

theorem option_map_none {α β : Type} (next : α → β) :
    Option.map next (none : Option α) = none := rfl

theorem option_bind_assoc {α β γ : Type}
    (m : Option α) (f : α → Option β) (g : β → Option γ) :
    (m.bind f).bind g = m.bind (fun x => (f x).bind g) := by
  cases m <;> rfl

theorem except_bind_assoc {ε α β γ : Type}
    (m : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (m.bind f).bind g = m.bind (fun x => (f x).bind g) := by
  cases m <;> rfl

theorem stateT_run_pure {σ α : Type} {m : Type → Type} [Monad m] (a : α) (s : σ) :
    (pure a : StateT σ m α).run s = pure (a, s) := rfl

theorem stateT_run_bind {σ α β : Type} {m : Type → Type} [Monad m]
    (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f).run s = (x.run s >>= fun (a, s') => (f a).run s') := rfl

theorem stateT_run_get {σ : Type} {m : Type → Type} [Monad m] (s : σ) :
    (get : StateT σ m σ).run s = pure (s, s) := rfl

theorem stateT_run_set {σ : Type} {m : Type → Type} [Monad m] (s' s : σ) :
    (set s' : StateT σ m PUnit).run s = pure (⟨⟩, s') := rfl

theorem estateM_run_pure {ε σ α : Type} (a : α) (s : σ) :
    (pure a : EStateM ε σ α).run s = .ok a s := rfl

theorem estateM_run_get {ε σ : Type} (s : σ) :
    (get : EStateM ε σ σ).run s = .ok s s := rfl

theorem estateM_run_set {ε σ : Type} (s' s : σ) :
    (set s' : EStateM ε σ PUnit).run s = .ok ⟨⟩ s' := rfl

/-- Normalize chained `Option`, `Except`, `StateT`, and `EStateM` monadic/functorial expressions step-by-step. -/
macro "monadic_reduce" : tactic =>
  `(tactic| (
      simp only [
        except_monad_bind, except_bind_ok, except_bind_error,
        except_functor_map, except_map_ok, except_map_error,
        option_monad_bind, option_bind_some, option_bind_none,
        option_functor_map, option_map_some, option_map_none,
        option_bind_assoc, except_bind_assoc,
        stateT_run_pure, stateT_run_bind, stateT_run_get, stateT_run_set,
        estateM_run_pure, estateM_run_get, estateM_run_set,
        Pure.pure, Except.pure
      ]
  ))

end Obend.Tactic.MonadicReduction

