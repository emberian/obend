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

end Obend.Tactic.MonadicReduction
