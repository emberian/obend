# Expert read: distributed systems and security (2026-11-03)

Slug `distributed-security`. The reader: someone who has shipped a BFT protocol, reviewed ocap
systems, and has had receipts forged against them. Tags: **READ** (file opened, `path:line`),
**INFERRED** (deduced from READ facts), **PROPOSED**. Working tree as of today, not HEAD. No Lean
or Rust was built; the one thing run was `python3 -I tests/run-receipts.py` from `lean/`
(32/32 hold, under a minute).

## 0. Verdict in one paragraph

The Lean spine that the receipts stand on is the real thing: `Obend.Receipt.Merkle` is a
positional Merkle map with binding proved up to a named collision, `Obend.Receipt.dated_sound`
has the correct shape, and the `obend verify` CLI re-derives every claim from the receipt and a
root the verifier chose. Everything *distributed* or *adversarial* that sits on top of that spine
is, today, either a model that no code path instantiates (`VaultTurn.witnesses`, `ValidAt`, the
`Simplex.State` machine), or a Rust mirror that the Lean theorems do not describe (the node's
protocol, its "Ed25519", its judges, its receipt check). The single most serious item is that the
consensus protocol in `crates/obend-node/src/net.rs` is not Simplex and is not safe: honest nodes
cast their *finalize* vote on receipt of a bare leader proposal, in any view up to `current+64`,
with the parent/height check applied only when the view equals the current one. One Byzantine
leader (within the `f` the protocol claims to tolerate) splits the honest set permanently at one
height. The Lean theorem cited for safety (`qc_same_view_unique`) is a same-view quorum lemma over
abstract predicates and says nothing about this. The second most serious item is that the "Merkle
receipt verification through the Lean kernel" the node performs is `propose(root); commit;
verify(root)` against a session whose only check is "have I been told this root before"
(`Bridge.lean:775-795`, `lib.rs:1192-1200`). The 11-01 backdoors were not removed; they were
re-plumbed so the caller supplies the admission.

## 1. Method

Read in this order: `review/FABLE-COUNCIL-20261101.md` §1-2, `git show 26f3ce8:AMBITION.md` vs
`AMBITION.md`, `DEOS-CONTRACTS-CONSENSUS.md`, then every file the brief names: the four
`Consensus/*.lean`, nine `Vault/*.lean`, `Receipt.lean` and `Receipt/*`, four `Run/*.lean`, four
`Judge/*.lean`, `FFI/Bridge.lean`, `Digest/{Cshake256,HashBytes}.lean`, `Spec/Sha256.lean`,
`Core/Digest.lean`, `crates/obend-node/src/{net,lib,judge_witness}.rs`, `crates/obend-sandbox/src/*`,
`crates/obend-ffi/{build.rs,src/sys.rs,src/session.rs}`, `lean/tests/run-receipts.py`. For every
theorem the documents lean on I read the statement and the definitions it quantifies over.
Line counts: `wc -l` gives 47,046 lines across the named files; `net.rs` is 4,990, `lib.rs` 5,270.

## 2. Suspicions, evidence, verdicts

Ranked by how it would land in front of a protocol or security reviewer, not by fix cost.

### S1. "Simplex BFT" is not Simplex and is not safe under one Byzantine leader

**What made me suspicious.** `DEOS-CONTRACTS-CONSENSUS.md` §5.2 (READ) describes Chan-Pass Simplex
correctly: `PropCert(h,b)` is 2f+1 notarize votes, `FinCert(h,b)` is 2f+1 finalize votes from
validators who saw the PropCert and did not skip. `lib.rs:862-890` (READ) defines `PropCert` as a
*single leader-signed* proposal. A one-round "vote to finalize on proposal" protocol needs a lock
to be safe across views; I looked for one.

**Evidence.** READ `net.rs:2507-2585`, the `Propose` handler:

- `net.rs:2527-2531`: a proposal is accepted if `prop_cert.view >= st.current_view` and
  `<= st.current_view + 64`.
- `net.rs:2533-2535`: the parent-hash and `height == committed_height + 1` checks are inside
  `(prop_cert.view == st.current_view && ...)`. For any *future* view they are skipped. The only
  height check that remains is `payload.height <= st.committed_height` refuses.
- `net.rs:2560-2583`: the node then casts `SimplexVoteKind::Finalize` for the proposal, gated only
  by "not already Finalize/Skip-voted *in that view*" and `wal.check_can_vote`.
- `net.rs:1688-1720` `check_can_vote_inner` (READ): refuses a second vote of the same kind in the
  same view with a different hash, and Skip after Finalize in the same view. Nothing across views.
- `net.rs:2651-2683` `FinalizationCertificate` handler and `net.rs:2920-3002`
  `apply_finalized_block` (READ): no check that `payload.height == committed_height + 1` or that the
  parent is the committed tip. Dedup is `finalized_blocks.any(|b| b.height == payload.height)`
  (`:2928-2933`), then `committed_height = payload.height; committed_tip_hash = fin_cert.block_hash`
  (`:2998-2999`), including when `payload.height` is *below* a previously committed height that
  was reached by a skip.

**INFERRED attack** (N=4, f=1, quorum 3; everyone honest except the leader of view 2, node 1):
view 1 leader proposes `B` at height 1, parent genesis; nodes 0,2,3 Finalize-vote; `FinCert(1,B)`
forms. Before (or while) that propagates, node 1 broadcasts a view-2 proposal `B'` at height 1,
parent genesis. Every honest node has `current_view = 1`, `2 <= 1+64`, the parent check is skipped
because `2 != current_view`, and `height 1 > committed_height 0` on any node that has not yet
applied `FinCert(1,B)`. They all Finalize-vote `(2, B')`; node 1 does too. `FinCert(2,B')` forms.
Each node applies whichever FinCert arrives first and drops the other by the height dedup. Two
honest nodes now hold different blocks at height 1, forever. No equivocation receipt is produced:
`record_vote_and_check_equivocation` (`net.rs:2785-2832`) only matches same `(voter, view, kind)`.
Node 1 signed one proposal per view; by this code's own definition it did nothing slashable.

Even if the parent check were applied to future views it would pass, because the honest nodes'
committed tip is still genesis. The missing rule is Simplex's: vote only in your current
iteration, enter iteration `v+1` only on a notarization or a skip of `v`, and finalize only a
notarized block. There is no notarize phase here at all.

**What the Lean says.** READ `Consensus/Simplex.lean:243-291`: `honest_quorum_intersection` and
`qc_same_view_unique` quantify over arbitrary `p q : α → Bool` and a `vote : Nat → Option α`; they
are correct quorum-intersection lemmas with no protocol, no views other than "the same one", no
chain, no locking. READ `:128-200`: `State`, `ViewRecord`, `register`, `broadcast`, `castVote` and
one theorem `castVote_already_voted` (`:198`). There is no proposal handler, vote handler,
view-change, or commit rule anywhere in the file (`grep -n '^def ' Simplex.lean`, 40 defs, none
after `castVote` touches `State`). `simplex_safety`, `simplex_no_skip_and_fin`,
`simplex_bounded_liveness_after_gst` cited in DEOS §5.2 do not exist (grep, §4 below). The node
also has **no view timer**: skip votes are only created by the test driver `run_view_skip`
(`net.rs:3803-3828`, READ; `grep -n 'SimplexVoteKind::Skip,'` finds only driver and test sites).
Liveness is a harness property.

**Verdict: confirmed.** The deployed protocol is unsafe for `f >= 1` and has no liveness mechanism
of its own. The safety proof that exists is about a different, simpler object.

### S2. The "kernel-verified Merkle receipt" is a self-admission loop

**What made me suspicious.** The 11-01 review found `verifyReceiptCore` accepting a 1-leaf tree
and `turnCommitCore` accepting unproposed digests; a later lane says it fixed them in place.

**Evidence.** READ `FFI/Bridge.lean`:

- `:57-66` `SessionState.admittedRoots : Array ByteArray`.
- `:716-731` `turnProposeCore`: hashes the turn bytes into a 32-byte id, then
  `roots1 := pushAdmittedRoot s.admittedRoots tidBytes; roots2 := pushAdmittedRoot roots1 turnBytes`
  (`:727`). If the caller's turn payload is itself 32 bytes, **the payload becomes an admitted root**.
- `:768-797` `verifyReceiptCore`: `admittedInSession := s.admittedRoots.contains claimedRoot ||
  s.admittedRoots.contains rcptBytes` (`:775`); refuse if false; otherwise accept when
  `trailing.isEmpty || opensFromPayload || opensFromDigest` (`:793`). Both openings are still
  `Opening := ⟨1, 0, h, []⟩` (`:787`, `:791`): size-1 tree, index 0, no siblings. A bare 32-byte
  admitted value with nothing after it verifies with no opening at all.
- `:737-752` `turnCommitCore` now requires a pending proposal (this part is fixed).
- The theorems added as evidence (`:1410-1547`) all say "refused on the empty session" or "refused
  when unadmitted". None says anything about what admission requires, because admission requires
  nothing beyond calling `turnProposeCore`.

READ `crates/obend-node/src/lib.rs:1192-1200` `BlindedVaultMultiProof::verify_via_ffi`:
`session.propose_turn(&self.unredacted_root)?; session.commit_turn(&tid)?;
session.verify_receipt(&self.unredacted_root)`. The root is 32 bytes, so `propose_turn` admits it
(Bridge `:727`), and `verify_receipt` finds it. Same pattern at `net.rs:1080-1083` and
`:1286-1289` for `CollapsedEpochReceipt`. **INFERRED:** `verify_via_ffi` returns `Ok(true)` for
any 32-byte value whatsoever, on any fresh session. The node's "kernel verification" of its state
root is a round trip through a set it just inserted into.

Also READ `crates/obend-ffi/build.rs:47-54`: if the Lean dylib is not found the build silently
switches to a **stub FFI** (`cargo:rustc-cfg=feature="stub"`), and `sys.rs:300-325` implements the
stub `obend_verify_receipt` with the same admitted-roots semantics plus a magic-prefix check. On
this Mac the dylib exists (`lean/.lake/build/lib/libobend_Obend.dylib`); on any machine without a
Lean build the node's tests pass against the stub unless `OBEND_REQUIRE_NATIVE_FFI=1`.

And READ `Bridge.lean:1352-1377` `isValidCertObligation`: a "proof certificate" is accepted by
scanning its text for the substrings `sorry`, `axiom`, `: True :=`, then `theorem ` and `:= by`,
then parsing `<` / `>` / `=` between integers in the conclusion. This is a prose gate on a string
the caller wrote, and on success it admits a root (`:1393-1400`).

**Verdict: confirmed, not fixed.** The 1-leaf opening is still the only opening; the gate moved
from "any digest" to "any digest the caller admitted", and the caller admits everything.

### S3. The Lean `SlashingReceipt` is not a slashing receipt; the Rust one is, and they are unrelated

READ `Simplex.lean:670-675`: `SlashingReceipt := { view blockA blockB : Nat, equivocatingVoters :
List Nat }`. READ `:731-738` `extractSlashingReceipt ... (votedA votedB : Nat → Bool)` filters a
committee by two predicates. There are no votes, no signatures, no blocks, nothing a third party
can check: anyone can "extract" a receipt naming anyone by choosing the predicates.
`simplex_accountable_safety` (`:769-790`) proves that if two quorums of predicates overlap enough
then the filter is long enough: true, and not accountability.

READ `lib.rs:997-1010` `EquivocationSlashReceipt { offender_id, view, vote_a, vote_b }` with
`verify` checking both signatures against the committee and `block_hash` differing: this *is* the
right shape. No theorem relates it to the Lean type (different fields, different file, no bridge).
**Verdict: confirmed.** The proven object is unverifiable; the verifiable object is unproven.

### S4. The certSigners-count contract was not replaced; a second gate was added beside it

READ `Simplex.lean:329-334` `Cert.signerCount : Nat`; `:361-368` `SimplexState.certSigners : Nat`;
`:405-412` `simplexQuorumLaw` compares `quorumThreshold <= certSigners`; `:600-604`
`simplexInvariant` is `2f+1 <= certSigners <= 3f+1`; `:639-663` `simplexCellContractOf` carries it.
All unchanged: the cell contract still trusts a number. READ `Finality.lean:296-343`: a new
`QuorumBoundFinalityGate` with `signers : List Nat`, `Nodup`, membership in `committee := [0,1,2,3]`
by default. READ `SovereignFinality.lean:137-166` `tier2_simplex_quorum_and_accountable_safety`
is the conjunction of the gate lemma, the predicate lemma, and the filter lemma, about three
unrelated objects, joined by `∧`. **Verdict: confirmed.** Two of everything; the signers are still
`Nat`s with no signature, and the thing a Vault cell actually evaluates is the count.

### S5. `VaultTurn.witnesses` is sound and unpopulated; the node verifies witnesses in a Rust mirror

READ `Vault/Hyperedge.lean:203-211` `witnesses : List TurnWitness := []`; `:263-272` `ValidAt`
requires every witness to pass its registered `Judge.Format`; `:275-287` `witness_sound` is
correct. `grep -rn 'witnesses :=\|turnId :=\|: VaultTurn :=' lean/Obend` finds **no construction
of a `VaultTurn`** anywhere except `Finality.lean:266` (a `FinalityGate`, different type). The
`SovereignEngine` consumes `turn.witnesses` (`SovereignEngine.lean:336,429,540,627`, READ) but no
code builds the turn it consumes. `ValidAt` (a `Prop`) is used only as a hypothesis in
`SovereignFinality.lean:112-116`; the executable check is `checkOracleTurnValidAt`
(`SovereignEngine.lean:298`) with no theorem to `ValidAt`.

READ `crates/obend-node/src/judge_witness.rs:1-14, 1403-1440`: `verify_all_turn_witnesses`
dispatches on `"drex-clearing@1" | "clearing@1"`, `"world-carry@1"`, `"interval@1"`,
`"rtl-synth@1"` to **Rust reimplementations** of those judges. The node never calls Lean's
`checkBytes`. `Judge.Format.checkBytes_sound` (`Judge/Class.lean:212`) is a theorem about code the
node does not run. **Verdict: confirmed on both counts.**

### S6. Cryptography: a bespoke signature scheme with variable-time scalar multiplication, derived from public seeds

READ `crates/obend-node/Cargo.toml`: dependencies are `serde`, `serde_json`, `thiserror`, and
sibling crates. No `ed25519-dalek`, no `aws-lc-rs`, no `blake3` (all three are named in DEOS §5.2).
READ `lib.rs:46` hand-rolled SHA-256 (a second copy at `obend-sandbox/src/grain.rs:23`);
`lib.rs:150-223` hand-rolled Keccak-f[1600]/cSHAKE256; `lib.rs:440-520` hand-rolled field and
Edwards arithmetic; `lib.rs:500-511` `scalar_mul` is a plain double-and-add with a data-dependent
branch on each secret bit (`if ((byte >> bit) & 1) == 1 { res = res.add(temp) }`), used for
signing (`:721`) and for deriving the public key from the secret (`:703`).

READ `lib.rs:694-779`: key derivation `cshake256_domain(b"obend.ed25519.sk", node_id, seed)`,
nonce `cshake256_domain(b"obend.ed25519.r", secret_key, msg)`, challenge
`cshake256_domain(b"obend.ed25519.k", R, A||msg)`. This is a Schnorr signature on edwards25519
with cSHAKE256 in place of SHA-512 and non-RFC-8032 key clamping. It is **not Ed25519**: no
test vector from any other implementation can apply to it, and nothing outside this repository
can verify its signatures. The verify side does check canonical `S`, small-order `A` and `R`, and
a cofactor equation (`:743-779`), which is more care than the sign side got.

READ `net.rs:3425-3431`: every validator's secret is `from_seed(id, "obend-ws32-validator-seed-{id}")`,
a string in the source. READ `net.rs:2290-2294`: every node binds `127.0.0.1:0`. **INFERRED:** there
is no deployable node. There is one process that forks N threads sharing a public seed. There is no
key loading, no config, no peer discovery, no TLS, no replay window on the wire
(`WireEnvelope`, `net.rs:1378-1442`, signs `sender_id || JSON(payload)`; nothing in the envelope
names a chain, genesis, or epoch, so with the shared-seed keys a signed vote from one cluster is
valid in any other).

Also READ, no Lean-vs-Rust cross-check of cSHAKE256 exists (`grep -rn 'lean-vectors\|KAT\|known.answer'
crates/obend-node/src/lib.rs` is empty). The node compares roots it computed with its own Keccak
against roots the Lean session merely stores, so a divergence would be invisible.

**Verdict: confirmed.** Replace with a vetted library before anyone calls this signed.

### S7. Canonical encoding of the signed turn is ambiguous

READ `net.rs:296-320` `VaultTurn::digest`: `meta = turn_id || agent.as_bytes() || cost(8) ||
epoch(8) || method(8) || read_slots...` with **no length prefix on `agent`** and a variable-length
tail. INFERRED concrete collision: `{agent:"x", cost:0, epoch:0, method:0, read_slots:[5]}` and
`{agent:"x\0\0\0\0\0\0\0\0", cost:0, epoch:0, method:5, read_slots:[]}` produce identical `meta`
and identical digests with identical write slots. `SignedFastPathAck` signs that digest
(`net.rs:393-402`), so acks collected for the first turn validate a `FastPathCert` carrying the
second (`FastPathCert::verify` checks only `turn.digest() == turn_digest`, `:443-461`). The write
effect is the same, so this is metadata forgery (agent name, method, read footprint), which is
exactly what `Mandate.check_turn` (`:579-640`) keys on. Separately the same object has a second
encoding, `serde_json::to_vec` (`:941`), used for `PropCert.turn_payload`. **Verdict: confirmed
(low-moderate severity, textbook).**

### S8. "Durable WAL" is a `Vec<u8>` in process memory

READ `net.rs:1515-1545` `DurableNodeWal { journal: Vec<WalEntry>, byte_log: Vec<u8>, ... }`;
`:1582-1590` frames are JSON with an **unkeyed** cSHAKE digest; `grep -n 'std::fs\|OpenOptions\|
sync_all' net.rs` finds only the sandbox gate directory (`:816-818`). `simulate_crash()` clears the
in-memory volatile fields and `recover_from_wal()` replays the in-memory journal. The Lean model
`DurableSimplexHost` (`SovereignFinality.lean:269-330`, READ) is a faithful model of exactly that:
a list that survives because nothing deletes it. **Verdict: confirmed.** The equivocation
protection that `durable_recovery_prevents_equivocation` promises does not survive a real crash.

### S9. Confinement: fail-closed is right, the Seatbelt profile and the "metering" are not

Good first: READ `bwrap.rs:340-355, 392-404` the runner refuses to run unconfined unless
`allow_unsandboxed_fallback` is set, and `net.rs:759-790` `verify_strict_policy` insists on
`--unshare-net`, `--cap-drop ALL`, `--disable-userns` etc. for untrusted grains. That is the correct
default and the receipt binds `is_fallback` (`bwrap.rs:123`).

Then: READ `bwrap.rs:249-262` the macOS profile is `(deny default) (allow process*) (allow
sysctl-read) (allow mach-lookup) ... file-read* on "/", /usr, /bin, /sbin, /System, /Library,
/AppleInternal, /private, /dev, /tmp, /var, /etc ... file-write* on /private/tmp, /tmp, /dev/null,
workspace`. `(allow mach-lookup)` with no service list is every Mach service on the machine
(launchd, pasteboard, security agents, user notification); `(allow process*)` is fork/exec of
anything; writes to the shared `/tmp` let two grains talk. `memory_max_mb` and `cpu_quota_usec`
exist in config and are enforced nowhere on macOS (no `setrlimit`, no cgroup; `grep -n
'rlimit\|cgroup' bwrap.rs` is empty). READ `bwrap.rs:513-517`: `fuel_consumed =
wall_clock_usec/10_000 + observed_bytes/64` and `peak_rss_bytes = 4096 + observed_bytes`. The
"deterministic fuel" is wall-clock time; the RSS is a formula on output size. Both go into
`receipt_digest`. **Verdict: confirmed.** The Linux path is a reasonable bwrap wrapper; the macOS
path is cosmetic; the metering in the receipt is fiction.

### S10. Capabilities are strings; delegation does not conserve budget

READ `net.rs:384-392` `Mandate { grantor, holder, target: String, ... }`; `:579-583` identity is
`turn.agent != self.holder` on strings; `Powerbox.mandates: BTreeMap<String, Mandate>` (`:646`).
Whoever can submit a turn with `agent: "alice"` holds alice's mandate. That is an ACL keyed on a
self-asserted name, the thing ocap exists to avoid. READ `:653-700` `delegate`: clamps the child's
quota to the parent's *remaining* budget but **does not debit the parent**; a parent with 100 can
mint children of 100, 100, 100. `attenuates` is checked with `debug_assert!` (`:697`), absent in
release. READ `Vault/Mandate.lean:120-129`: `subDelegate` sets `budget := min parent.budget quota`,
same non-conservation; `:219-224` `children_no_oversubscribe` is `hp.1`, i.e. it restates the
`BudgetPartitioned` hypothesis rather than establishing it. **Verdict: confirmed.** The
Sandstorm/ocap vocabulary is present; the semantics (unforgeable reference, conserved authority)
are not.

### S11. Theorems whose hypotheses are false at the deployed hash

READ `Digest/HashBytes.lean:90-94`: "Over all byte strings and a fixed-width `H` this
[`Collision H`] is true by pigeonhole". READ `Vault/SovereignEngine.lean:648-663`
`sovereignEngine_blinded_view_non_forgeable` takes `(h_no_coll : ¬ Collision H)`; the grep count
is 8 uses across `SovereignEngine.lean` and `Projection.lean`. READ `Receipt.lean:555-558`
`Binds d := ∀ r r', d r = d r' → r = r'` and `chain_binds` under it; READ `Vault/Rehydration.lean:
211-212` `chain_tamper_evident (HInj : Function.Injective H)`. For a 32-byte hash over an infinite
type these hypotheses are unsatisfiable; the theorems are true and say nothing. The spine's own
idiom (`∨ Collision H` in `dated_sound`, `opens_binds`) is right; these later files abandoned it.
`Theory.CollisionFloor`, cited at `HashBytes.lean:93`, does not exist in the tree. READ
`Core/Digest.lean:247-251`: `Hiding` is explicitly **ASSUMED, NOT PROVED**, so "secret cell contents
are provably unobservable" (`Projection.lean:24-25`) is an assumption, labelled as such in one file
and sold as a theorem in another. **Verdict: confirmed.**

### S12. Blinding salt in the node is derived from public data

READ `net.rs:326-340` `apply_to_cells`: a new cell's `salt = cshake256_domain("obend.vault.cell.salt",
slot_id, turn_id)` and `required: vec![IpcAuth::Read]`. Both inputs are in the finalized block.
**INFERRED:** anyone holding the chain can recompute every salt and dictionary-attack any cell
whose content has low entropy; and every cell created by a turn is world-readable by default.
`Projection.lean`'s hiding story needs a uniformly random salt (`Core/Digest.lean:249`). **Verdict:
confirmed.**

### S13. Merkle: sound tree, misnamed multiproof, odd-leaf duplication in the node

READ `Receipt/Merkle.lean:45-66, 188-210, 234-254`: `root`/`climb`/`opens` with `opens_binds`
requiring `o.size = o'.size` and `opens_view` requiring `o.size = vs.length`. Correct: binding is
proved for a verifier that knows the tree size. Leaf vs node confusion is excluded because a leaf
is `digestWith H index value` with a small index. READ `:305-355` `MerkleBatchProof` is a list of
independent single openings plus an index-distinctness check; a multiproof shares siblings, this
does not. READ `lib.rs:1146-1162` the node's own tree duplicates the last odd leaf
(`H(p0,p0)`), the Bitcoin CVE-2012-2459 shape: `[a,b,c]` and `[a,b,c,c]` share a root, and
`BlindedVaultMultiProof::verify_stranger` (`:1186-1189`) does not bind the leaf count. Two Merkle
trees, one proved, one deployed. **Verdict: confirmed (Lean fine; node not covered by it).**

### S14. The 11-01 unkeyed `sha256("{declName}:{format}:ok")` receipt

`grep -rn 'format}:ok\|declName}:' lean/Obend crates lean/tests` is empty. The SHA-256 call sites
that remain (`Spec/Capture.lean:40`, `Spec/Identity.lean:50-56`, `Elab/Workbook.lean:358,1395`,
app modules) are source-fingerprints, which is what `Spec/Sha256.lean:3-8` says they are for.
**Verdict: cleared** in the form reported. The *pattern* (an unkeyed digest standing in for an
authenticated verdict) survives in Bridge's `cert_{n}` admission (`Bridge.lean:1400`) and the WAL
frame digest (`net.rs:1586`).

### S15. JSON on every wire

READ `net.rs:1395` (`WireEnvelope`), `:941` (`BlockPayload::to_bytes`), `:1583` (WAL frames),
`judge_witness.rs:24-28` (witness payloads are JSON strings), `Receipt/Export.lean` (receipts).
`AMBITION.md:23` (READ, current) says "no ad-hoc JSON schemas outside the kernel". The signed
object is the serde re-serialization of a parsed document (`net.rs:1426-1434`), which is
canonical-by-accident: it depends on serde_json's field order and float formatting staying fixed
across versions. **Verdict: confirmed; the ask for a binary format was not done.**

### S16. Epistemic "Sybil bound" and Escrow "no theft"

READ `Consensus/Epistemic.lean:500-508`: `epistemic_sybil_bounded_by_seed_cut` takes
`h_conservation : influence <= sybilTotalInfluence` as a hypothesis and concludes `influence <=
sybilSeedCutBound`; the lemma it uses is "sum of flows <= sum of capacities". It is `a <= b -> b <= c
-> a <= c`. The content of SybilGuard/SybilLimit (that influence *is* bounded by cut flow, over
paths) is the hypothesis. READ `Vault/Escrow.lean:112-130`: `EscrowOp` has `deposit`, `settle`,
`reclaim` with no principal; any party may `reclaim` any side. The conservation theorems hold; the
object is an accounting identity, not a contract with authority. **Verdict: confirmed as
theorem-shaped tests (the 11-01 pattern), low exposure because nothing deploys them.**

### S17. What is genuinely good (so it is not thrown out with the rest)

- `Receipt.lean:459-479 dated_sound`, `Receipt/Merkle.lean` binding, `Receipt/Cli.lean` and
  `Receipt/Export.lean`: a receipt is re-derived, the only trusted input is `--root` from an
  authority the verifier picked, 32/32 teeth hold including the consistent-lie case
  (`run-receipts.py` "an opening re-valued with its proof does not open"). This is the design a
  stranger-checkable receipt should have. It has no signer, which is correct for its role.
- `Digest/Cshake256/*` with `@[csimp] cshake256Bytes_eq_native` (`Seam.lean:67`) is a clean seam;
  in obend the compiled path is the Lean fast path, no foreign kernel (`Seam.lean:48`).
- `Judge/Lrat.lean` `check_sound` (`:239`) and the CLI `obend lrat`.
- `Vault/Hyperedge.lean` `no_toctou`, `vaultTurn_disjoint_commutes`; `Run/Fork.lean`
  `stitch_atomic`, `stitch_double_spend`; `Run/Reflect.lean` `forged_descriptor_refused`.
- `Judge/TranscriptPolicy.lean` redaction confinement is a real (small) non-interference result.
- `obend-sandbox` fail-closed default and the bwrap flag set.

## 3. What a deployment would be exposed to today, ranked

1. **Chain split under one Byzantine leader** (S1): permanent disagreement at one height among
   honest nodes; no slashing evidence produced. Also: no liveness without the test driver.
2. **Forged "kernel-verified" state roots** (S2): any 32-byte value passes `verify_via_ffi`; the
   receipts the node emits (`CollapsedEpochReceipt`, `BlindedVaultMultiProof`) carry a verification
   bit that means nothing. With the FFI stub, the same holds with no Lean present at all.
3. **Key compromise by reading the source** (S6): all validator secrets derive from a literal
   seed; signatures are a bespoke scheme nobody else can verify; secret-dependent timing.
4. **Authority forgery by name** (S10): a mandate is claimed by writing its holder's string into a
   turn; budgets multiply under delegation.
5. **Unverifiable accountability** (S3): the Lean receipt cannot convict anyone; the Rust one is
   never produced for the attack in (1).
6. **Loss of vote state on crash** (S8): a restarted node forgets what it voted and will
   equivocate; "durable" is in-memory.
7. **Witness bypass by construction** (S5): the only witness checker the node runs is a Rust
   rewrite with no proof; the proved checker has no caller.
8. **Signed-object malleability** (S7, S15): ambiguous turn digest; JSON canonicalisation by
   convention.
9. **Content disclosure of "blinded" cells** (S12, S11): public salts, hiding assumed.
10. **Sandbox escape on macOS, resource exhaustion anywhere** (S9): `mach-lookup` and `process*`
    open; no memory or CPU cap; metering values are invented.
11. **Merkle leaf-count malleability in the node** (S13).

## 4. Names the documents cite that do not exist (re-run today)

`for n in ...; grep -rqE "(theorem|def|lemma|abbrev) +$n( |$|:)" lean/Obend --include='*.lean'`:
MISSING `simplex_safety`, `simplex_no_skip_and_fin`, `simplex_bounded_liveness_after_gst`,
`blinded_projection_non_forgeable`, `blinded_projection_sound`, `grain_confinement_sound`,
`powerbox_attenuation_monotonic`, `mandate_bounds_turn`, `collapse_preserves_accepts`,
`disjoint_turns_commute`, `vaultTurn_wide_pullback_sound`, `vaultTurn_conserves_linear_slots`,
`zoe_offer_safety`, `relaw_preserves_forever_crown`, `one_checker_to_rule_them_all`. All fifteen
are load-bearing in `DEOS-CONTRACTS-CONSENSUS.md`. Nothing changed here since 11-01.

## 5. The three changes I would make first

1. **Make the node run Simplex, and make the Lean state machine the one it runs** (S1, S3).
   Delete the Rust protocol logic in `net.rs:2507-3030` and drive the node from an executable Lean
   `Simplex.step : State -> Message -> State x List Message` with notarize and finalize votes, "vote
   only in `current`", enter `v+1` only on `Notar(v)` or `Skip(v)`, finalize only a notarized block,
   and a timer-driven skip. Prove same-height safety *for that step function* (it is the standard
   two-lemma proof once the state machine exists; `honest_quorum_intersection` is the right tool).
   Make `SlashingReceipt` carry the two signed votes and prove `verify = true -> equivocation`.
   Cost: roughly two weeks for one person who has done it before; the Lean lemmas are a few
   hundred lines; the Rust shrinks.
2. **Delete `admittedRoots`; make `verifyReceiptCore` a real `Merkle.opens` against a root the
   caller must justify** (S2). The signature becomes `verify(root, Opening, expectedSize) -> Bool`
   with `opens_view` as its theorem, and `verify_via_ffi` goes away: the node checks openings
   against the FinCert's `post_state_root`, which is the only root it has any reason to trust.
   Delete the stub FFI fallback or make it loud (`OBEND_REQUIRE_NATIVE_FFI` default on). Delete
   `isValidCertObligation`. Cost: a day in Lean, a day in Rust, plus rewriting the tests that
   currently pass because the loop closes.
3. **Replace the home-made crypto and the string capabilities** (S6, S10). `ed25519-dalek` (or
   `aws-lc-rs`) for signatures with keys loaded from per-node files and never from a literal;
   `sha2`/`sha3` for the hashes with a Lean-vs-Rust KAT for cSHAKE256 at `deployed`; a
   length-prefixed canonical encoding (or a fixed binary schema) for every signed object;
   mandates bound to a public key with the turn signed by it; delegation debits the parent.
   Cost: three to four days; it removes about 700 lines from `lib.rs`.

Not in the top three but cheap: write `VaultTurn` constructors and route the node's turns through
`ValidAt`'s executable twin with a bridge theorem; put `∨ Collision H` back into the eight
`¬ Collision` theorems; fix the Seatbelt profile (`mach-lookup` to a named list, drop `process*`),
and either enforce or delete `memory_max_mb`/`fuel_consumed`/`peak_rss_bytes`.

## 6. The one question for Ember

Is the node meant to be a *deployable validator* (keys, peers, disk, an adversary on the wire),
or a *simulator* that exercises the Lean theorems in-process? The code is unambiguously the
second (one process, `127.0.0.1:0`, seeds in the source, in-memory WAL, harness-driven view
change), while every document and the `#tooth`/test names describe the first. The honest fix for
a simulator is to say so in its module header and strip the words "Ed25519", "durable", and
"stranger-checkable" from what it emits; the honest fix for a validator is §5. They are different
projects and I cannot tell which one you want.

## 7. What landed (2026-11-04)

Built and tested on bb2 in `~/lane-security`: HEAD `a180c75` plus this lane's files. The Lean
library was built as `lake build Obend:shared` with, locally on bb2 only, the `Obend` umbrella
module dropped from the lib globs (HEAD's lakefile had already moved `Obend.Apps.*` to tier 2)
and `Hardware/UserspacePhysical.lean` taken from the working tree, because HEAD's copy and HEAD's
`Obend.lean` import `Obend.Leaf.BendTT`, which HEAD deleted in `fb35622`; HEAD is red there and
that is the compiler lane's. 876 jobs, no errors, `libobend_Obend.so` 45.8 MB. Rust against that
library with `OBEND_REQUIRE_NATIVE_FFI=1`: `cargo test -p obend-ffi` 27/27 (unit 2, C-ABI edges
8, pool stress 7, integration 5, receipt-session binding 5); `cargo test -p obend-node --lib`
filtered to the protocol, WAL, mandate, witness and clearing tests 23/23; the cluster integration
test 2/2; `cargo test -p obend-sandbox` 22/22; `python3 -I tests/run-receipts.py` 32/32 on the Mac.
Five named-file commits, Bridge first; the sixth is this section.

**Closed in place.**
- S2 (the self-admission loop). `admittedRoots` is gone; `committedRoots` is written only by
  `turnCommitCore` (`turnProposeCore_committedRoots_unchanged`); `verifyReceiptCore` takes the
  frame `root || size || index || pathLen || path || payload`, refuses anything under 56 bytes
  (so the bare 32-byte root of 11-01), and opens the payload with `Merkle.opens` against a
  committed root (`verifyReceiptCore_sound`). The prose gate `checkObligationPropHolds` and
  `isValidCertObligation` are deleted. A certificate enters a session only as a
  `TurnWitness {format, version, grade, obj, cert}` checked by `Obend.Judge.registry`
  (`Bridge.lean:1228-1260`). The Rust session's `commit_payload` returns the frame
  `verify_receipt` accepts, and the stub refuses every weave because it has no judge registry;
  `kernel_is_native()` exists so a test that needs the kernel says so rather than pass.
  Receipts are bound to the committing session (`receipt_session_binding.rs`, 5 tests).
- `VaultTurn.witnesses` is populated. `VaultTurn.ofWitnessLegs` (`Vault/Hyperedge.lean`) is the
  constructor; every Bridge commit goes through it; in the node, the clearing step encodes the
  batch and certificate as the Lean `drex-clearing@1` witness (`lean_clearing_witness_json`,
  `Nat` ids as `decodeClearingObj` reads them), weaves it, and commits the woven turn. The two
  node tests that step a verified session with a clearing batch now pass only when the Lean judge
  accepts that witness, and do (natively, 2/2).
- S14 (the unkeyed `ok` receipt): no such receipt is produced by any path that survived; the
  registry is the one seam (`sessionJudgeFormats := registry`) and six entries whose decoders
  read nothing, or named formats that exist nowhere, are out of it (`Judge.lean:54-79`).
- S11 (false `¬ Collision H` hypotheses): the eight theorems conclude `P ∨ Collision H` with the
  pair exhibited (`Receipt.lean`, `Vault/Projection.lean`, `Vault/Rehydration.lean`,
  `Vault/SovereignEngine.lean`). SovereignEngine's token bound needed `Lower/PolicyToGrain` to
  refuse a stream longer than `maxTokens` instead of scanning its prefix; that change is in the
  same commit.
- Panel-diff items. `Law/Contract.lean`: reverted to HEAD (the working-tree "soundness theorem"
  was a check over eight sampled states and never built), then the `.byLrat` tier refused
  outright (`checkContractCert_byLrat_refused`; its default clause set `[[1],[-1]]` was
  unsatisfiable alone, so any refutation passed). `Judge/Clearing.lean`: a batch with two orders
  from one account is refused (`duplicateAccount`, `judge_ok_accounts_nodup`), the condition
  under which a per-account net-flow fill is an order's fill. `Ledger/Seat.lean`: duplicate asset
  keys summed. `sovereign-drex`: `obend check` accepts, `verilator --lint-only` clean.
- S10, in part: delegating a mandate debits the parent's budget (`net.rs:704-727`).
- The obend-gui segfault: the C bridge initialises the runtime once under `pthread_once` and
  `pool.rs` attaches threads through `obend_ensure_lean_thread` instead of calling
  `lean_initialize_thread` first. `silicon_bridge` builds against the HAL without the F2 backend.

**Renamed, not fixed.** `obend-node` is now described everywhere (crate, module headers, PLAN
WS 21/26/32, DEOS §5.2) as the in-process simulator it is. The curve arithmetic is
`SimulatorKeypair` under a quarantine header; no doc line calls it Ed25519. The `Propose` handler
casts its finalize vote only in its current view and only for a proposal extending its committed
tip (`net.rs:2540-2580`), which removes the future-view split of S1, but the protocol is still one
phase without a lock and `Consensus/Simplex.lean`'s header now says that no state machine, timer
or cross-view safety theorem exists. `DrexClearingCertificate::verify_with_kernel` is documented
as the Rust mirror judge it always was (it never used its session).

**Still exposed** (the ranking of §3 stands for these): S1 as a protocol (no notarize phase, no
lock, no Lean step function; the fix is §5.1); S6 (the simulator crypto is in the signing path
of every certificate the simulator emits); S10 (mandates keyed by a self-asserted holder string);
S12 (blinding salt from public data); S15 (JSON on every wire); S9 (the WAL is a `Vec<u8>`);
the stub FFI is still a silent fallback unless `OBEND_REQUIRE_NATIVE_FFI=1` is set.

Not this lane's, found on the way: HEAD is red at the Leaf seam (`Obend.lean` and
`Hardware/UserspacePhysical.lean` import the deleted `Obend.Leaf.BendTT`; the working-tree
`Leaf/Futamura.lean` rewrite leaves HEAD's `Stdlib.lean` without the names it opens).
`Lower/Proofs/SiliconKernel.lean` in the working tree imports the untracked `Leaf/Static.lean`.
