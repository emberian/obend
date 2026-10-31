# Objective Bend

Objects you can extend without forking, laws judged on every write, and documents that
remember why they say what they say. Built on Lean, running Bend underneath.

## The idea in a paragraph

[Bend](https://github.com/bendlang/bend) lets you write laws your code can never break, proved
once and checked by a small kernel. That is the right promise for a function. It is not quite the
right promise for the things people actually want to keep: a shared document, a game's rules, a
group's ledger, an agent's standing permissions. Those are *objects*, built by many hands over
time, and the law that matters is the one judged at the moment someone tries to change them.
Objective Bend is a language of partial specifications in the sense of François-René Rideau's
[*Lambda, the Ultimate Object*](https://fare.tunes.org/files/cs/poof/ltuo.html): you write a
layer, it sees the whole it will eventually be part of (`self`) and the thing it is extending
(`super`), and anyone may add a layer later without reading or copying yours. Laws are lines
people can read, judged on every write, inheritable from the kind of thing you made, and a
refusal tells you which clause said no. Underneath, the actual computation is ordinary Bend:
strict, affine, fast, with its proofs.

## Where it comes from

This is the extraction of three months of research across several repositories:
[minidregg](https://github.com/emberian/minidregg) built the calculus and its Lean metatheory
(Core4: lazy open recursion, specification/target conflation, reflection, modular typing,
activities), [nanodregg](https://github.com/emberian/nanodregg) built the contextual theory
(deferred decisions with justifications that can be withdrawn and repaired), and
[delvetalk](https://github.com/emberian/delvetalk) put objects written in it in front of agents
in a shared town and watched what they did. The theses, the design, and the honest state of each
piece are written up here:

- [`THESIS.md`](THESIS.md): why objects and judged laws, not affinity, are the ground for "AI
  with laws", stated so it can be wrong
- [`DESIGN.md`](DESIGN.md): the seam between the lazy object layer and affine Bend leaves,
  cross-package extension, and documents as the primary thing
- [`SHIP.md`](SHIP.md): how it becomes one library the other repositories depend on
- [`GROUNDING.md`](GROUNDING.md): the map of the source trees, with dates and file paths
- [`astra/`](astra/): an independent read of all of the above by GPT-6 Astra, with its corrections

## State

The Lean library in [`lean/`](lean/) builds at Lean 4.35 with no Mathlib and no native code: about
two hundred modules, twenty-five hundred theorems, every proof module pinned to Lean's three
standard axioms, seventy-odd mutation teeth that fail their theorem under a planted fault. It holds
the calculus and its demand machine with their proofs; a bidirectional checker complete for a stated
fragment of the declarative typing, with equi-recursive type agreement decided by finite
bisimulation and executable annotation preparation; laws by occasion with inheritance along the
linearized ancestry, and the `.obend` law fragment compiled to them; the slot (deferred decisions
with justifications, repair under a stated compatibility condition, stored selection with an
incumbent-first default and chooser override); a guarded runner proving that every dispatched
operation was admitted at its own view, no token is spent twice, and nothing in flight can be
replanned or re-sent, with a Core4 activity adapted to it; and documents as page graphs with
patches, pushout merge, conflicts as objects, sections as slots, identity and byte cites, and
backlinks. The `.obend` front end from minidregg is ported and conformant on its cohorts; `obend
check` and `obend run` read source. A declaration-level journal computes the exact set of theorems
a change affects.

Not yet: the Bend leaf emitter and its refinement against BendTT; a markdown vault a stranger
opens; carry between package versions. The reports under `lean/docs/` say, per module, what is
proved and what is not.

## Who

Ember ([ember.software](https://ember.software)), with Claude, Astra and Kimi doing a great deal
of the reading, arguing and typing. Faré's work is the foundation; Victor Taelin's Bend is the
leaf we stand on. Neither has reviewed this. AGPL-3.0, like its sibling repositories.
