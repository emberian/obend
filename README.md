# Objective Bend

Objects anyone can extend without forking, laws judged on every write, documents that remember why
they say what they say, and a kernel that checks every answer's evidence. Built to become the
symbolic core of what comes after Mathematica. [`AMBITION.md`](AMBITION.md) says where this goes.

## The idea in a paragraph

A specification is a layer that sees the whole it will become (`self`) and the thing it extends
(`super`); anyone may add a layer later without reading or copying yours; `fix` closes the stack
lazily, so a partial object is still a value you can inspect, extend and judge. Laws are lines
people can read, judged at the moment someone tries to change something, inheritable from the
kind of thing you made and from the packages you extend, and a refusal tells you which clause said
no and what would pass. Decisions that are not ready stay open as slots with their justifications,
which can be withdrawn and repaired. Every admission is a re-executed check of a certificate the
kernel did not search for, and every receipt says in which regime its answer was established.

```
record Review:
  review(value: Nat) -> Nat
  twice(value: Nat) -> Nat

spec Base for Review:
  def review(value: Nat) -> Nat:
    value + 1n

spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))

spec Augmented for Review:
  def review(value: Nat) -> Nat:
    super.review(value) + 1n

def twiceOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).twice(3n)
```

```
$ obend run Review.obend twiceOfThree
result: 7
```

## What is here

Everything lives in [`lean/`](lean/), a Lean 4.35 library with no Mathlib and no native code: about
240 modules, 2,500 theorems, a whole-library axiom census in the build, and mutation teeth that fail
a theorem under a planted fault. Each library has a report under [`lean/docs/`](lean/docs/) saying
what is proved and what is not.

| library | what it is |
|---|---|
| `Core` | the calculus (lazy open recursion, reflection, activities) with a call-by-name reference semantics and a call-by-need machine proved equal to it; a bidirectional checker complete on a stated fragment, equi-recursive type agreement by finite bisimulation, executable annotation preparation |
| `Spec` | the `.obend` front end, ported from minidregg and conformant on its cohorts; `package … extends …` across packages with intentions as slots; orthogonal protocols |
| `Law` | laws by occasion as closed terms, judged by re-executing a machine probe, inheriting along the ancestry with the ancestor named, compiled from the surface fragment |
| `Slot` | deferred decisions: candidates, withdrawable supports, repair under a compatibility condition, stored selection with an incumbent-first default and chooser override, a `World` with pin, retirement and version laws |
| `Run` | a guarded runner (`refines`: every dispatched operation admitted at its view, no token spent twice, nothing in flight replanned), selection control, a Core4 adapter, and the shared-World ledger with `joint_reachable_ticket_exclusive` |
| `Fold` | the audited fold every admission is an instance of, with `receipt_sufficient` |
| `Doc`, `Vault` | pages as graphs, patches, merge as a pushout with conflicts as objects, sections as slots, identity and byte cites, backlinks; `obend open DIR` on a folder of markdown with laws in frontmatter |
| `Equiv` | `≈b` and `mix_assoc` over the reference semantics |
| `Journal` | the exact set of theorems a change affects, by name |

Not yet, in the order they are planned: the judgment class and receipt type (in progress), `quote`
and the observer ladder, nominal kinds and one intention module, the leaf emitter against BendTT,
the specialization slot, the platform kinds. [`PLAN.md`](PLAN.md) is the project plan.

## Reading

[`AMBITION.md`](AMBITION.md) is the destination. [`THESIS.md`](THESIS.md) states the claim so it can
be wrong. [`DESIGN.md`](DESIGN.md) is the design as built and as planned. [`METATHEORY.md`](METATHEORY.md)
is what is mechanized and what each remaining theorem wants. [`GROUNDING.md`](GROUNDING.md) maps the
source trees this was extracted from. [`review/`](review/) holds the outside reads and studies,
[`review/DECISIONS-20261031.md`](review/DECISIONS-20261031.md) every decision and who took it, and
[`astra/`](astra/) GPT-6 Astra's evaluations.

## Who

Ember ([ember.software](https://ember.software)), with Claude, Astra and Kimi doing a great deal of
the reading, arguing and typing. Faré's work is the foundation; Victor Taelin's Bend is the leaf we
stand on. Neither has reviewed this. AGPL-3.0.
