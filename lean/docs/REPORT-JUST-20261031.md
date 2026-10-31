# REPORT 2026-10-31 — Lane Just: the justification lattice, the polynomial slot, and the gate

Lane Just (Claude Opus), on `lean/docs/LANE-JUST-BRIEF-20261031.md`: build the corrected
justification algebra of `review/SYNTHESIS-20261031.md` §3 under Astra's corrections
(`astra/ASTRA-EVAL-20261031.md` lines 11–27, 87, 109), run experiment E1, state `Integrity.repair` as
the corollary it is and replace B4′ with an operational transition property. Tags: **MEASURED** (a
command run here, output read), **READ** (a file opened), **INFERRED** (my reasoning). Worktree
`scratchpad/just` on branch `lane-just` from `origin/dev` `d37888a`; Lean v4.35.0.

## 1. What landed

| file | what |
|---|---|
| `Obend/Just.lean` (new, 492 lines) | `Just K`: bounded distributive lattice (absorption **and** `mul_idem`); `astra3_absorptive` + `astra3_not_idem` (Astra's three-element countermodel, in Lean); `Raw X` written polynomials, `Raw.eval` with `eval_append`, `eval_mul`, `eval_congr`, `eval_zero_tok`, Boolean `eval_bool`; normal form `Raw.norm` (decidable token equality) with `norm_antichain`, `norm_nodup`, `eval_norm` (value preserved in every `Just K`); `canonical` (two antichains with the same Boolean function have the same monomials up to token order) and `raw_not_canonical` (`a + a·b` vs `a`); `Poly X` (normalized, carries its antichain proof) with `eval_add/mul/one/var`; dual evaluation `Raw.missing` with `eval_subst`, `missing_bool` (Boolean image) and `missing_mono` (one monomial ↦ the monomial of its failed tokens). |
| `Obend/Slot/PolySlot.lean` (new, 481 lines) | E1: `usable` = Boolean evaluation of the candidate's monomial (judge token + support tokens); `read`, `select`, `resolve`, `advance` take eligibility from it; every theorem of `Slot.lean`, `World.lean`, `Integrity.lean` that mentions a redefined name re-proved against it, with the originals' teeth (10 `#tooth`, all rejected); bridges `usable_eq`, `alternatives_eq`, `read_eq`, `select_eq`, `advance_eq` (the redefinition is observationally the original); `missing_eq` (the written dual monomial is the judge token if rejected, then `Slot.dead` in order); `dup_normal` (the normal form has one token where `Slot.dead` has `[f, f]`). |
| `Obend/Slot/Repair.lean` (new, 179 lines) | Repair soundness under **compatibility** (`Repair.Compatible`: the repair preserves every requirement of the candidate that holds): `repair_sound`; the sufficient local form `compatible_of_local`; the pin world with Astra's pin-0/pin-1 candidate: `clash_unsat`, `clash_naive` (the synthesis's T2 hypotheses hold and the conclusion fails), `clash_refused` (compatibility refuses it), `apart_repaired` (two cells: compatible, repaired). Tooth: mutating `Compatible` to `True` breaks `plan_keeps`. |
| `Obend/Slot/Integrity.lean` (268 → 458 lines) | `repair_of_contextual` (REPAIR for every filler from B4); B4′ is now `Integrity.transition` over `Advance` (a stored-selection transition); `Integrity F A := contextual F ∧ transition A`; `slotAdvance` (incumbent-first) and `slotFiller_integrity` for the pair; `transition_retired`; `select_prefix` / `select_reuse` (exact reuse of a first-usable choice needs the rejected prefix) and `reuse_needs_prefix` (Astra's early/chosen countermodel); floors `churn` and `sticky` refuted; `toy_advance`. Floors of B4 now refute `contextual` alone (a stronger statement than the old `¬ Integrity`). |
| `tools/proofsize.py`, `tools/just-control.lean` | the instrument and the control of §3. |
| `Obend.lean` | re-exports `Obend.Just`, `Obend.Slot.Repair`. |

MEASURED: `LEAN_NUM_THREADS=2 lake build` 180 jobs green (177 + three new modules); 38 `#tooth`
rejections in the log; every new theorem in an `#assert_axioms` line; no `sorry`, no axiom.

## 2. The corrections, as Lean

- **Absorption is not idempotence.** `astra3_absorptive` checks all nine synthesis laws on
  `{0,1,2}` by `decide`; `astra3_not_idem` shows `1·1 ≠ 1`. `Just` therefore carries `mul_idem`.
- **`Poly` is a normal form, not a list.** `canonical` is the useful half of the free-object
  property (Boolean evaluation separates normal forms); with `eval_norm` and the homomorphism
  lemmas it is what "the free bounded distributive lattice" can mean without Mathlib. Not proved:
  uniqueness of the homomorphism out of `Poly` as a typeclass statement (Poly's operations are
  lawful only up to `canonical`'s set equality, so `Poly` is not itself a `Just` instance on the nose).
- **The dual names what is missing, not a refutation.** Docstring of `Obend.Just`; `missing_mono` is
  exactly the slot's case. A refusal (failure) and a restoration (missing set) stay different things.
- **Ordered observations stay lists.** `Slot.dead`, `Slot.evidence` and the refusal order are not
  read back from a monomial anywhere. INFERRED: the *written* dual monomial (`missing_eq`) still has
  order and multiplicity; it is normalization that forgets them (`dup_normal`).
- **Repair needs compatibility.** `repair_sound` assumes it; the pin countermodel is refused by it.
- **Replay needs the prefix.** `select_prefix`/`select_reuse` state the certificate of a first-usable
  choice: its eligibility *and* the earlier candidates' ineligibility.

## 3. The gate: does the proof text get shorter? (MEASURED once)

Instrument: `tools/proofsize.py` counts non-blank lines and characters after each theorem's
statement `:=`. Set: the 31 theorems whose statements mention a redefined name (`Slot.lean` 6,
`World.lean` 4, `Integrity.lean` 21, the last against this commit's Integrity, so statements match).

| | proof lines | proof chars |
|---|---:|---:|
| originals (`Slot`, `World`, `Integrity`) | 222 | 6992 |
| polynomial (`PolySlot`, + `usable_dead`) | 147 | 5461 |
| **control**: `PolySlot` with `usable := judge && dead.isEmpty`, no `Just` import (`tools/just-control.lean`) | 142 | 5210 |
| charged to the polynomial: `Just.lean` proofs | 203 | 5652 |
| charged: bridges + dual (`usable_eq` … `dup_normal`) | 19 | 660 |

**Result: the polynomial does not shorten the slot.** The 34% drop from the originals is real and is
entirely due to two definitional restructurings (`read` branches on `usable` first; `resolve :=
(select …).map body`) and tighter tactics. The control has them and no lattice, and is 5 lines
shorter than the polynomial. Only three proofs touch the lattice at all: `usable_iff` (same length),
`usable_dead` (+1 line), and `usable_congr`, which is longer through `eval_congr` (6 lines) than
through `dead_congr` (2). This is what Astra predicted at line 15: the slot already stores its
monomial in normal form. Per the brief, the adoption stops here. `PolySlot` stays as the record
(it builds, and its bridges are the refinement Astra asked for at line 87).

INFERRED: the restructuring is worth taking into `Slot.lean` on its own (−35% proof text, same
observations by `read_eq`/`select_eq`); I did not, because it changes `Slot.read`'s definition under
the runner lane and that is not this lane's call.

**Retired 2026-11-01** (lane Parsimony, `REPORT-PARSIMONY-20261101.md`): `Obend/Just.lean`,
`Obend/Slot/PolySlot.lean` and `tools/just-control.lean` had no consumer but the census, so they are
deleted; this table is the record. To rerun the measurement, check out `5892944`, where all three
files and `tools/proofsize.py` still stand.

**`Slot/Repair.lean` retired too** (same lane, on the coordinator's word): nothing imported it but the
root and the census. It stands at `4753f62`. Its record, stated over any `World`:

- `Repair` = an audited step `act : V → V` with `step : ∀ v, Step v (act v)` and
  `establishes : ∀ v, holdsAt (act v) fact = true`; `Compatible r S c` = every requirement of `c` that
  holds at `v` still holds at `act v`; `applyPlan` applies a plan in order.
- `repair_sound`: if `S.judge c = true`, every repair of the plan is `Compatible S c`, and every dead
  support of `c` at `v` is some repair's `fact`, then `Later v (applyPlan plan v)` and `c` is usable
  there. Tooth: `Compatible := True` breaks it.
- `compatible_of_local`: a repair that moves only its own fact's cell is compatible with a candidate
  none of whose other requirements is about that cell.
- The clash (Astra, `ASTRA-EVAL` line 27), on `pinWorld` (cells `Bool`, a pin `Nat × Nat`, fact
  `(cell, n)` = "the pin is `n`"): `clash` needs `(false, 0)` and `(false, 1)`. `clash_unsat`: no view
  makes it usable; `clash_naive`: the plan `[pin false := 0, pin false := 1]` covers both dead supports
  and the candidate stays unusable; `clash_refused`: `pin false := 0` is not `Compatible` (it retires
  `(false, 1)` where it held). `apart` (`(false, 0)`, `(true, 1)`): `apart_repaired`, the two local
  repairs make it usable, via `repair_sound` and `compatible_of_local`.

`repair_of_contextual` (`Integrity`) does not want the condition: its REPAIR is withdrawal plus
fillability, not a plan of steps, so the record lives here rather than beside it.

## 4. B4′ for the runner

`Advance.advance : Slot → V → order → Option Cand → Except Refusal Cand`, `Integrity.transition`:
(1) a stored selection usable at the view is kept; (2) an advanced selection is usable and is either
the kept one or the head of `alternatives`; (3) a refusal only when the stored selection and every
candidate are unusable, naming dead supports per candidate. `transition_retired` gives the old B4′(1)
for any lawful advance. Floors: `churn` (re-select every view) violates (1); `sticky` violates (2).
READ `origin/dev`: no `Obend/Run/` commit yet at rebase time; nothing to reconcile.

## 5. Not done

- Universal property of `Poly` as a homomorphism-uniqueness theorem (see §2).
- T1 (trace justification of a nested fill), E2, E3: not in this brief.
- Exponential blow-up of eager normalization (Astra line 29): not measured; `Raw` is kept so a
  caller can evaluate without normalizing.

## 6. The one decision for Ember

**Incumbent-first or first-usable for a stored selection.** `slotAdvance` keeps a stored selection
while it is usable (no churn on replan; what "replan changes only undispatched choices" suggests).
The alternative, re-running `select` at every view, is the canonical replay and is what `Slot.select`
alone means; it is refuted as a B4′ instance here (`not_transition_churn`), and under it Bob's
still-valid choice flips back to Alice whenever her grant returns (`reuse_needs_prefix`). The runner
lane will build on whichever B4′ says. I chose incumbent-first.
