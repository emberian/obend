# Objective Bend (`obend`)

> **Draft, 2026-11-04.** This README was rewritten by an agent lane in the project's research
> frame (`AMBITION.md`); ember has said the previous one was not in their voice, and this one is
> not either. It is a draft for ember to voice. It names only what the built `obend` binary does
> today, with the commands that were run to check it.

Objective Bend is a research project into what follows from a few design decisions taken
together: programs as open objects other hands extend without forking (`self`/`super`/`fix`),
laws as readable lines judged at the moment of a write and inherited along kinds, deferred
decisions as slots with withdrawable supports, answers labelled by the regime that established
them, and a kernel that re-executes rather than trusts. The calculus and its metatheory are in
Lean 4 under `lean/Obend/`; the CLI is `lean/.lake/build/bin/obend`. What the project is and is
not is in `AMBITION.md`; what is proved and what is open is in `THESIS.md`.

## What runs today

### A vault of markdown

A folder of `.md` files, Obsidian-shaped: one page per file, `[[wikilinks]]`, `![[embeds]]`,
`[[Page#^block]]` quotes, frontmatter. `obend open` reads it as a world kept beside it in
`.obend/world.json` and never changes the shape of your notes.

```sh
cd my-notes
obend open                      # every page a version; dangling links named
obend status [PAGE]             # each page, each cite and whether it holds
```

A page's frontmatter may carry laws, `law NAME: EXPR`, over its measures (`words`, `lines`,
`bytes`, `links`, `embeds`, `quotes`, `dangling`, `sections`, `version`), over the write itself
(`deletions`, `insertions`: `new.deletions == 0` is append-only, line by line) and its numeric fields; a folder's
`_kind.md` carries laws for every page in it. An edit that breaks a law is refused by name, with
the value that would pass, and the file keeps what you typed:

```
Beta: refused by its law short: `new.words <= 20` does not hold; words = 20 would pass (this write has words = 27)
```

Members post without overwriting (`obend member add scout --grant post:Alpha`, `obend post`,
`obend select`); a copy edited offline merges back by pushout (`obend merge ../laptop`); a quote
whose source moved is marked `{behind}` in your file and re-grounded with `obend recite`; a file
you delete is a page deleted, a file you rename is the page renamed. The whole of it, run and
checked line by line: `lean/tests/vault/WALKTHROUGH.md`.

### A ledger in a vault

A register folder whose `_kind.md` carries the laws every posting must keep (`balanced`,
`solvent`, `sealed`) makes the vault a double-entry ledger: documents are pages, posting is a
write judged by those laws, a wrong posting is reversed and never edited, a period closes once,
and every posting has a receipt anyone re-judges without the books.

```sh
obend ledger post invoices/INV-1       # posted as P-0001, receipt .obend/receipts/P-0001.json
obend verify .obend/receipts/P-0001.json
obend ledger status | obend ledger reverse P-0001 | obend ledger close 11
obend report trial-balance 11
```

Walkthrough: `lean/tests/ledger/WALKTHROUGH.md`.

### Programs and packages

The language (`.obend`): records, sums, functions, lazy fields, and specs that layer over a
record through `self` and `super`, closed by `fix`. The tutorial's programs are under
`lean/tests/obend-source/tutorial/`.

```sh
obend run lean/tests/obend-source/tutorial/ch4-late-binding.obend raisedTotal   # result: 16
obend check FILE.obend                 # every declaration's type, one JSON line each
obend check DIR | obend run DIR ENTRY  # a directory of .obend files as one package
obend run --package WORKSPACE.json     # packages extending packages they did not write
```

A refusal names what would pass: `refused (competing-protocol): … is implemented by kit/pdf and
by kit/html, neither package extending the other; a package extending both decides by
implementing it`. Packages declare laws over their objects' state; a write is judged by every
package's laws in precedence order (`obend judge`), and a recorded turn re-derives at the records
it was made at or is stale by name (`obend admit`).

### Claims, receipts and the leaf

```sh
obend check --obligations PKG --object ENTRY        # a program's claims, at the object they are about
obend prove PKG SPEC.CLAIM --object ENTRY --out r.json
obend verify r.json                                 # re-judged with no producer state
obend ground PKG ENTRY 7                            # ok, or refuted: runs to false
obend emit PKG --object ENTRY --out book.json --call twice 3
obend specialize PKG --object ENTRY --book book.json --call twice 3
```

`prove` certifies what re-execution and late binding reach (a method equals its unfolding under
the layers that are there), refutes a claim by a ground instance that runs to false, and says
`unchecked` for everything else; it does not do arithmetic or induction. `obend analyze impact
CELL@PIN --world DIR` says which dependents of a page or cell a change reaches.

### Hardware and analysis

`lean/Obend/Hardware/` and `lean/Obend/Analysis/` are studies of what the same primitives carry
(RTL emission and a tapeout pipeline, interval and Taylor-model judges, consensus). They are
reached from Lean (`#import_obend`, the `Obend/Apps/*.lean` fixtures) and are described in
`PHYSICAL.md`, `SILICON-ELABORATOR.md` and `NEXT-MATHEMATICA.md`, which say what is proved and
what is a worked example. The application directories under `apps/` are fixtures for those
studies; each is a directory of `.obend` modules you can `obend check apps/NAME` and whose claims
you can list and prove with the commands above.

## Building

```sh
cd lean && lake build obend          # the CLI
python3 tests/vault/walkthrough.py   # then the conformance runners, each under a minute:
python3 tests/ledger/walkthrough.py
python3 tests/run-obend-source.py tests/run-workspace.py tests/run-logic.py tests/run-leaf.py tests/run-receipts.py
```

The Rust crates (`crates/`) are an FFI session over the Lean library, a sandbox, a node
simulator of the consensus theorems, and `obend-gui`, an HTTP workbench whose notebook format
is a prototype; they are not part of the workflows above.

## Layout

| Directory | Contents |
| :--- | :--- |
| `lean/Obend/` | the calculus (`Core`), specs and laws (`Spec`, `Law`), slots and kinds, documents and vaults (`Doc`, `Vault`, `Ledger`), claims (`Logic`), the leaf (`Leaf`), judges and receipts, the studies (`Analysis`, `Hardware`, `Consensus`, `Lower`), the CLI (`Main.lean`) |
| `lean/tests/` | the walkthroughs and conformance runners; `obend-source/` holds the tutorial, the probes and the stranger and three-package workspaces |
| `stdlib/`, `apps/` | `.obend` programs: a small standard library and the eight study fixtures |
| `crates/` | Rust: FFI, sandbox, node simulator, workbench |
| `review/` | decisions and the expert reports that drive the current work |

## License

AGPL-3.0 — Ember Arlynx ([ember.software](https://ember.software)).
