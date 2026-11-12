# Structured Symbolic Documents and Certified Computational Notebooks

Obend combines local-first patch-graph documents (`lean/Obend/Doc`) with graded algebraic/analytic certificate checkers (`lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Judge`) and a stateful FFI session client (`lean/Obend/FFI/Bridge.lean`, `crates/obend-ffi`, `crates/obend-gui`), turning computational notebooks (`.obnb`) into commutative, dependency-pinned, kernel-verified artifacts.

---

## 1. Patch-Graph Documents and Quotation Cells (`lean/Obend/Doc`)

Unlike JSON-array notebooks where concurrent edits trigger brittle line-diff conflicts and cell re-execution silently invalidates downstream results, `Obend.Doc` represents a page as a directed atom graph (`lean/Obend/Doc/Graph.lean`):

```lean
inductive ProjectionKind where
  | prose
  | obendCode
  | casSymbolic
  | leanBridge
  | lawContract
  | deosAffordance
  | hardwareSchematic
  | hardwareTiming
  | hardwareLayout
  | ledgerSeat

inductive Content where
  | text (s : String)
  | cite (name : String) (c : Cite)
  | field (name value : String)
  | cell (id : String) (kind : ProjectionKind) (ast : Obend.Core.Data.Data)
         (pins : List (String × ByteArray)) (receipt : Option ByteArray)
```

### 1.1 Pushout Merging and Keyed Cell Commutativity (`lean/Obend/Doc/Merge.lean`)

- Graph merges construct categorical pushouts (`IsPushout`).
- Structured cells keyed by `id` merge via 3-way ancestor reconciliation (`mergeKeyedCells3`):
  - `mergeKeyedCells3_idempotent` and `mergeKeyedCells3_commutative` prove order-independent convergence across peers.
  - `mergeKeyedCellAt_disjoint_edits_succeed` and `mergeKeyedCells3_disjoint_edits_no_conflicts` guarantee conflict-free composition whenever collaborators edit distinct cells.

### 1.2 Lossless Cell Projection and Staleness Detection (`lean/Obend/Doc/Structured.lean`)

`StructuredCell` (`lean/Obend/Doc/Structured.lean`) provides a typed view over `Content.cell` inside an `ObnbDocument`:
- Binary footprint digests (`pins : List (String × ByteArray)`) and optional Merkle receipts (`receipt : Option ByteArray`) serialize into `Core.Data.Data` via `pinsToData` and `receiptToData`.
- `hexToByteArray_byteArrayToHex` proves exact `ByteArray` round-tripping across hexadecimal encoding, closing unconditional `projection_preservation` and `Content.toCell_toContent` alongside `cell_preserved_under_add`.
- `stale_pin_invalidates` proves that if any upstream symbol or page digest in `env : String → Option ByteArray` diverges from a cell's recorded `pins`, pin validation immediately reports `PinStatus.stale` naming the invalidated key.
- Cross-page transclusions (`Cite` in `lean/Obend/Doc/Section.lean`) similarly detect upstream atom or byte-span edits via `SourceMoves`.

---

## 2. Certified Symbolic and Numerical Computation (`lean/Obend/Elab/AutoCert.lean`)

Symbolic manipulations in traditional computer algebra systems trust large unverified simplifiers. In Obend, external CAS routines propose algebraic or analytic witnesses that are checked inside Lean 4 by total judges registered in `Obend.Judge.registry`:

| Registered Format | Lean Implementation | Verified Mathematical Meaning |
| :--- | :--- | :--- |
| `groebner-ideal@1` / `groebner@1` | `lean/Obend/Elab/AutoCert.lean` (`GroebnerQuery`, `GroebnerCert`) | Multivariate Buchberger S-polynomial ideal membership (`checkGroebnerJudge_sound_membership`) and Positivstellensatz SOS non-negativity modulo ideal generators (`checkGroebnerJudge_sound`, `badGroebnerCert_refused`). |
| `taylor-model@1` | `lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean` (`TaylorModelQuery`, `TaylorModelExpr`) | Polynomial-plus-interval remainder bounds over `CanonicalRat` domains (`evalTaylorModelExpr_models`, `taylorModelJudge_semantic`). |
| `interval-bound@1` / `interval@1` | `lean/Obend/Judge/RealAnalysis.lean`, `lean/Obend/Elab/AutoCert.lean` (`IntervalQuery`, `IntervalObj`) | Subdivision enclosures of rational/transcendental expressions (`intervalCheck_sound`, `checkIntervalAutoCert_sound`). |
| `sos-lyapunov-cbf@1` | `lean/Obend/Analysis/SosLyapunov.lean` (`SosLyapunovProblem`, `SosLyapunovCert`) | Symbolic Jacobian / reverse-mode AD agreement (`polyPartialDeriv_agrees_with_symbolicDeriv_and_reverseAD`), SOS Lyapunov stability, CBF invariance, and DAE manifold certificates (`checkSosLyapunovProblem_sound`). |
| `lrat@1` | `lean/Obend/Judge/Lrat.lean`, `lean/Obend/Judge/Identity.lean` | Clausal unsatisfiability and bitvector Boolean identities (`check_sound`, `checkText_sound`, `planted_refused`). |

Within `.obend` source modules, `synthesizeClaimJudgeTag_ok` and `synthesizeClaimExternalJudge_sound` (`lean/Obend/Elab/AutoCert.lean`) synthesize and verify external-judge obligations during package elaboration (`lean/Obend/Elab/Workbook.lean`).

---

## 3. Live Session Execution and Host Workbench Libraries

Interactive sessions connect `.obend` / `.obnb` cells directly to the Lean kernel checker and durable vault without unverified middle-tier shadow stores:

1. **`Obend.FFI.Bridge` (`lean/Obend/FFI/Bridge.lean`)**:
   - Maintains a live `Obend.Vault.Replay.Session` per session handle.
   - Evaluates `.obend` cells through `Obend.Spec` elaboration and refuses unrecognized cell payloads (`evalCellCore_non_obend_refused`).
   - Admits proposed turns into `Replay.World` (`turnCommitCore_preserves_reachable`), checks footprint staleness (`admitFootprint_stale_pin_refused`), verifies `TurnWitness` certificates against `Obend.Judge.registry` (`projectHardwareCore_sound`), and validates 56-byte Merkle receipts against committed roots (`verifyReceiptCore_sound`).
2. **Rust Host Libraries (`crates/obend-ffi`, `crates/obend-gui`, `crates/obend-sandbox`)**:
   - `crates/obend-ffi`: Safe RAII `Session` bindings over `libobend_Obend.so`.
   - `crates/obend-gui`: Asynchronous PIDE document session client (`ObendSession` in `crates/obend-gui/src/evaluator.rs`) paired with streaming `.vcd`, `.stl`, and `.ngc` engineering artifact parsers (`crates/obend-gui/src/apps.rs`).
   - `crates/obend-sandbox`: Isolated execution (`GrainExecutor`, `LaunchGate`, `CpuMeter`) for external CAS, SAT, and EDA worker processes.
