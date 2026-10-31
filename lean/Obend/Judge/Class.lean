module
/-
# Obend.Judge.Class — a judge is a certificate checker over a declared domain

`review/GENERALIZATION-20261031.md` G2, `review/VISION-CLAUDE-20261031.md` §6.1–6.2,
`astra/ASTRA-VISION-20261031.md` §4.1. The typing checker's interface generalized to every judge: a
deterministic `check : Nat → Obj → Cert → Verdict`, where the verdict is `ok`, a refusal
naming the clause and the path where it applies, or `uncovered` (the grade ran out, which is not
`false`). The laws are fields:

- `sound`: `ok` means the declared meaning of the object under that certificate;
- `refuted`: a refusal by a clause the judge marks REFUTING (`refutes`) means no certificate could
  have meant it: the claim is false, not merely unproved. A judge that never refutes (`refutes` is
  constantly `false`) is admitted and says so by that field;
- `complete` on a stated `Fragment`: when the meaning is inhabited there, some certificate is
  accepted at some grade;
- `mono`: raising the grade does not change a verdict that was not `uncovered`.

`Deepen` turns any procedure that is sound at every grade into a monotone one by running it at
every grade up to the one granted and keeping the first answer (iterative deepening); the law
machine's probe is judged this way (`Obend.Judge.Instances`), so no fuel monotonicity of the
machine is needed.

A `Format` is a judge registered for use on bytes: its name and version, its decoders, the checker,
its trust base (`kernel`, `compiled`, `external`), the regime of the claims it establishes
(`decidable`, `semidecidable`, `attestable`: the vision study §6.1), and a planted bad certificate
with the theorem that it is refused at every grade (a format whose checker accepts everything has
no such certificate, so it cannot be registered). `Format.checkBytes_sound` is the theorem that the
statement a byte-level acceptance establishes is the one the bytes decode to. A `Translation` from
a domain into a format's objects carries `encode_sound`; `Translation.sound` composes it with the
checker.
-/
public section
namespace Obend
set_option autoImplicit false

/-- A judge's verdict: accepted, refused by a clause at a path, or not decided within the grade. -/
inductive Judge.Verdict (Clause : Type) where
  | ok
  | refused (clause : Clause) (path : List Nat)
  | uncovered
  deriving @[expose] DecidableEq, Repr

namespace Judge.Verdict
variable {Clause : Type}

/-- Rename the clauses. -/
def map {Clause' : Type} (f : Clause → Clause') : Verdict Clause → Verdict Clause'
  | .ok => .ok
  | .refused k p => .refused (f k) p
  | .uncovered => .uncovered

@[simp] theorem map_ok {Clause' : Type} (f : Clause → Clause') : (Verdict.ok : Verdict Clause).map f = .ok := by rfl

theorem map_eq_ok {Clause' : Type} {f : Clause → Clause'} {v : Verdict Clause} (h : v.map f = .ok) : v = .ok := by
  cases v <;> simp_all [map]

theorem map_ne_uncovered {Clause' : Type} {f : Clause → Clause'} {v : Verdict Clause}
    (h : v.map f ≠ .uncovered) : v ≠ .uncovered := by
  cases v <;> simp_all [map]

end Judge.Verdict

/-- **A judge**: a deterministic certificate checker over objects `Obj` and certificates `Cert`,
graded by a natural number (the work or fuel granted), with its laws as fields. -/
class Judge (Obj Cert : Type) where
  /-- the refusal vocabulary -/
  Clause : Type
  /-- what an accepted certificate establishes of the object -/
  Meaning : Obj → Cert → Prop
  /-- the checker -/
  check : Nat → Obj → Cert → Judge.Verdict Clause
  sound : ∀ {r : Nat} {o : Obj} {c : Cert}, check r o c = .ok → Meaning o c
  /-- the clauses whose refusal is a refutation, not a failure to prove -/
  refutes : Clause → Bool
  refuted : ∀ {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat},
    check r o c = .refused k p → refutes k = true → ∀ c', ¬ Meaning o c'
  /-- where completeness is claimed -/
  Fragment : Obj → Prop
  complete : ∀ {o : Obj}, Fragment o → (∃ c, Meaning o c) → ∃ c r, check r o c = .ok
  mono : ∀ {r r' : Nat} {o : Obj} {c : Cert}, r ≤ r' → check r o c ≠ .uncovered → check r' o c = check r o c

namespace Judge
variable {Obj Cert : Type} [J : Judge Obj Cert]

/-- An accepted verdict stays accepted at every larger grade. -/
theorem ok_mono {r r' : Nat} {o : Obj} {c : Cert} (h : J.check r o c = .ok) (le : r ≤ r') :
    J.check r' o c = .ok := by
  rw [J.mono le (by rw [h]; exact fun e => by cases e)]; exact h

/-- A judge's acceptance used under a joint budget keeps its meaning. -/
theorem sound_lift {r s : Nat} {o : Obj} {c : Cert} (h : J.check r o c = .ok) (le : r ≤ s) : J.Meaning o c :=
  J.sound (ok_mono h le)

/-- A decided verdict is the verdict at every larger grade. -/
theorem decided_agree {r r' : Nat} {o : Obj} {c : Cert} (le : r ≤ r') (h : J.check r o c ≠ .uncovered) :
    J.check r o c = J.check r' o c :=
  (J.mono le h).symm

end Judge

/-! ## Iterative deepening: a monotone judge from a procedure sound at every grade -/

namespace Judge

/-- The first answer `f` gives at a grade `0, 1, …, k`. -/
def deepen {α : Type} (f : Nat → Option α) : Nat → Option α
  | 0 => f 0
  | k + 1 => match deepen f k with
    | some a => some a
    | none => f (k + 1)

theorem deepen_mono {α : Type} (f : Nat → Option α) {k : Nat} {a : α} (h : deepen f k = some a) :
    ∀ {k'}, k ≤ k' → deepen f k' = some a := by
  intro k' le
  induction k' with
  | zero => cases Nat.le_zero.1 le; exact h
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le le with lt | eq
    · simp [deepen, ih (Nat.lt_succ_iff.1 lt)]
    · subst eq; exact h

theorem deepen_some {α : Type} (f : Nat → Option α) : ∀ {k : Nat} {a : α}, deepen f k = some a → ∃ i, i ≤ k ∧ f i = some a
  | 0, a, h => ⟨0, Nat.le_refl _, h⟩
  | k + 1, a, h => by
    simp only [deepen] at h
    cases hk : deepen f k with
    | some b =>
      rw [hk] at h; cases h
      obtain ⟨i, le, hi⟩ := deepen_some f hk
      exact ⟨i, Nat.le_succ_of_le le, hi⟩
    | none => rw [hk] at h; exact ⟨k + 1, Nat.le_refl _, h⟩

theorem deepen_isSome {α : Type} (f : Nat → Option α) {i : Nat} {a : α} (h : f i = some a) :
    ∃ b, deepen f i = some b := by
  cases i with
  | zero => exact ⟨a, h⟩
  | succ k =>
    simp only [deepen]
    cases deepen f k with
    | some b => exact ⟨b, rfl⟩
    | none => exact ⟨a, h⟩

end Judge

/-! ## Regimes, trust bases, formats -/

/-- The regime a claim is established in (the vision study §6.1). -/
inductive Judge.Regime where
  /-- the kernel decides it, within a grade -/
  | decidable
  /-- a certificate may exist; its search may not halt; checking one is decidable -/
  | semidecidable
  /-- only a named party's attestation, or a bound, can stand for it -/
  | attestable
  deriving DecidableEq, Repr

/-- What is trusted when a format's checker accepts. -/
inductive Judge.TrustBase where
  /-- the checker's run is a kernel reduction: the Lean kernel only -/
  | kernel
  /-- the checker is the kernel-proved function, run as compiled code (`Lean.trustCompiler`) -/
  | compiled
  /-- an external checker or party, named -/
  | external (who : String)
  deriving DecidableEq, Repr

def Judge.TrustBase.label : Judge.TrustBase → String
  | .kernel => "kernel"
  | .compiled => "compiled"
  | .external who => s!"external:{who}"

/-- A format's refusals: the bytes did not decode, or the judge refused. -/
inductive Judge.FormatClause (Clause : Type) where
  | malformed (what : String)
  | judge (clause : Clause)
  deriving DecidableEq, Repr

/-- **A registered certificate format.** -/
structure Judge.Format where
  name : String
  version : String
  Obj : Type
  Cert : Type
  [judge : Judge Obj Cert]
  /-- the object's canonical decoder -/
  decodeObj : String → Except String Obj
  /-- the certificate's decoder -/
  decodeCert : String → Except String Cert
  trust : Judge.TrustBase
  regime : Judge.Regime
  /-- a planted bad certificate -/
  bad : Obj × Cert
  /-- the grade it is refused at -/
  badGrade : Nat
  /-- it is refused there, by a clause (and so at every larger grade, `refused_above`) -/
  bad_refused : ∃ k p, judge.check badGrade bad.1 bad.2 = .refused k p

namespace Judge.Format

attribute [instance] Format.judge

/-- Check bytes: decode the object and the certificate, then judge. -/
def checkBytes (F : Format) (r : Nat) (obj cert : String) : Verdict (FormatClause F.judge.Clause) :=
  match F.decodeObj obj, F.decodeCert cert with
  | .ok o, .ok c => (F.judge.check r o c).map .judge
  | .error e, _ => .refused (.malformed s!"object: {e}") []
  | _, .error e => .refused (.malformed s!"certificate: {e}") []

/-- **Decoded bytes denote the checked statement**: an acceptance of bytes is an acceptance of the
statement they decode to, and its meaning holds of exactly that statement. -/
theorem checkBytes_sound (F : Format) {r : Nat} {obj cert : String} (h : F.checkBytes r obj cert = .ok) :
    ∃ o c, F.decodeObj obj = .ok o ∧ F.decodeCert cert = .ok c ∧ F.judge.Meaning o c := by
  unfold checkBytes at h
  cases ho : F.decodeObj obj with
  | error e => rw [ho] at h; cases h
  | ok o =>
    cases hc : F.decodeCert cert with
    | error e => rw [ho, hc] at h; cases h
    | ok c =>
      rw [ho, hc] at h
      exact ⟨o, c, rfl, rfl, F.judge.sound (Verdict.map_eq_ok h)⟩

/-- The planted certificate is refused at every grade past the planted one. -/
theorem refused_above (F : Format) {r : Nat} (le : F.badGrade ≤ r) :
    ∃ k p, F.judge.check r F.bad.1 F.bad.2 = .refused k p := by
  obtain ⟨k, p, h⟩ := F.bad_refused
  refine ⟨k, p, ?_⟩
  rw [F.judge.mono le (by rw [h]; exact fun e => by cases e), h]

/-- A format cannot accept everything: its planted certificate is not accepted past its grade. -/
theorem not_trivial (F : Format) {r : Nat} (le : F.badGrade ≤ r) : F.judge.check r F.bad.1 F.bad.2 ≠ .ok := by
  obtain ⟨k, p, h⟩ := F.refused_above le
  rw [h]; exact fun e => by cases e

end Judge.Format

/-- A judge whose checker accepts everything cannot be registered: no planted certificate of it is
refused. -/
theorem Judge.trivial_unregistrable {Obj Cert : Type} (J : Judge Obj Cert)
    (htriv : ∀ r o c, J.check r o c = .ok) (bad : Obj × Cert) (r : Nat) :
    ¬ ∃ k p, J.check r bad.1 bad.2 = .refused k p := by
  rintro ⟨k, p, h⟩; rw [htriv] at h; cases h

/-- **A translation** from a domain's claims into a format's objects: the encoding is part of the
trust boundary, so it carries its theorem. -/
structure Judge.Translation (F : Judge.Format) (Domain : Type) (Claim : Domain → Prop) where
  encode : Domain → F.Obj
  encode_sound : ∀ d c, F.judge.Meaning (encode d) c → Claim d

/-- The composition rule: a checked certificate for the encoding establishes the domain's claim. -/
theorem Judge.Translation.sound {F : Judge.Format} {Domain : Type} {Claim : Domain → Prop}
    (T : Judge.Translation F Domain Claim) {r : Nat} {d : Domain} {c : F.Cert}
    (h : F.judge.check r (T.encode d) c = .ok) : Claim d :=
  T.encode_sound d c (F.judge.sound h)

end Obend
end
