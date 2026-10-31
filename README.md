# Objective Bend

Objects anyone can extend without forking, laws judged on every write, and documents that
remember why they say what they say. A language with a Lean-checked core, built to run Bend
underneath.

## Why

[Bend](https://github.com/bendlang/bend) lets you write laws your code can never break, proved
once and checked by a small kernel. That is the right promise for a function. It is not the right
promise for the things people actually want to keep: a shared document, a game's rules, a group's
ledger, an agent's standing permissions. Those are *objects*, built by many hands over time, and
the law that matters is the one judged at the moment someone tries to change them, by a judge
that says which clause refused and what would pass.

Objective Bend takes its objects from François-René Rideau's
[*Lambda, the Ultimate Object*](https://fare.tunes.org/files/cs/poof/ltuo.html). A specification
is a layer that sees the whole it will become (`self`) and the thing it extends (`super`); anyone
may add a layer later without reading or copying yours; `fix` closes the stack lazily, so a
partial object is still a value you can inspect, extend and reason about.

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
status: finished
type: Nat
result: 7
```

## What is here

Everything lives in [`lean/`](lean/), a Lean 4.35 library with no Mathlib and no native code,
about two hundred modules and twenty-five hundred theorems, with a whole-library axiom census in
the build and mutation teeth that fail a theorem under a planted fault. Each piece has a report
under [`lean/docs/`](lean/docs/) saying what is proved and what is not.

- **The calculus and its machine** (`Obend.Core`): lazy open recursion with reflection, a
  call-by-name reference semantics and a call-by-need machine proved equal to it, checkpoints.
- **The checker**: a bidirectional checker complete for a stated fragment of the declarative
  typing, equi-recursive type agreement decided by finite bisimulation, and executable annotation
  preparation, so a term with a derivation can be made to check without a proof-search oracle.
- **The front end** (`Obend.Spec`): the `.obend` surface, ported from minidregg and conformant on
  its cohorts. `obend check` and `obend run` read source.
- **Laws** (`Obend.Law`): laws by occasion (birth, write, adopt, relaw, invoke) as closed terms,
  with meaning theorems, inheritance along the linearized ancestry with the ancestor named in a
  refusal, and the `.obend` law fragment compiled to them.
- **The slot** (`Obend.Slot`): a deferred decision with candidates, supports that can be withdrawn,
  repair under a stated compatibility condition, and stored selection with an incumbent-first
  default and a chooser's override.
- **The runner** (`Obend.Run`): a guarded runner with the theorem that every dispatched operation
  was admitted at its own view, no token is spent twice, and nothing in flight can be replanned,
  re-sent or quietly replaced; a Core4 activity adapted to it; an end-to-end example with a grant
  revoked mid-plan and a lost reply.
- **Documents** (`Obend.Doc`): pages as graphs, patches with merge as a pushout and conflicts as
  objects, sections as slots, identity and byte cites, backlinks, and a markdown vault round trip.
- **The journal** (`Journal`): for any change, the exact set of theorems whose justification it
  affects, by name.

Not yet: the Bend leaf emitter and its refinement against BendTT, cross-package extension at the
surface, a vault a stranger opens with one command, and carry between package versions.

## Reading

[`THESIS.md`](THESIS.md) states the claim so it can be wrong. [`DESIGN.md`](DESIGN.md) is the seam
between the lazy object layer and affine Bend leaves, cross-package extension, and documents as the
primary thing. [`METATHEORY.md`](METATHEORY.md) is what is mechanized and what each remaining
theorem wants. [`SHIP.md`](SHIP.md) is how this becomes one library the sibling repositories depend
on. [`GROUNDING.md`](GROUNDING.md) maps the source trees. [`review/`](review/) holds the outside
reads (a hostile review, prior art by aspect, the checker-completeness problem and Gemini Argon's
answer, algebraic subtyping, a refuted synthesis) and [`astra/`](astra/) GPT-6 Astra's evaluations.

## Where it comes from

Three months of research across [minidregg](https://github.com/emberian/minidregg) (the calculus
and its metatheory), [nanodregg](https://github.com/emberian/nanodregg) (the contextual theory of
deferred decisions) and [delvetalk](https://github.com/emberian/delvetalk) (objects in front of
agents in a shared town), extracted into one library.

## Who

Ember ([ember.software](https://ember.software)), with Claude, Astra and Kimi doing a great deal of
the reading, arguing and typing. Faré's work is the foundation; Victor Taelin's Bend is the leaf we
stand on. Neither has reviewed this. AGPL-3.0.
