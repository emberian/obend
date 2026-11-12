module
/-
# Obend.Vault.Lsafe — redaction confinement, open-world completeness tokens, forget while forked

Cards `K9` and `K10`. Three parts.

**§1 Redaction confinement (`K9a`).** The machine is `Obend.Judge.VpaJson.stepJson`, the RFC 8259
grammar in one pass: `runLsafeVpa` is `runFullJsonGrammar` (values, separators, strings with their
escapes, numbers, literals, unique keys in every object), and `checkLsafeRedaction doc l r
replacement` is `checkJsonRedaction` on a document that passes the grammar, with a replacement of
`isSafeRedactionByte` bytes (string-safe, and neither `<` nor `>`). The span may contain whole
escape sequences; it may not cut one, so redacting the backslash of `\"` is refused.
`lsafe_redaction_confinement`: after an accepted redaction the spliced document passes the
grammar, its machine state is the original state at `l` all through the replacement and the
original state at `r + j` at every `j` after it, its final state and object key sets are the
original ones, and the replacement carries none of the six bytes.
`lsafe_object_keys_nodup`: every object the machine closed has pairwise distinct keys.
`jsonCborCommit` commits to a JSON value tree through `Obend.Codec.DetCbor`
(`jsonCborCommit_binding`).

`spanRootCollision` computes, from two different span lists whose `VpaJson` span roots share a
`top`, an explicit collision at the tag; no choice is used, so extractors built on it run.

**§2 Open-world completeness (`K9b`).** `edgesDigest` is the `top` of the span tree over the
edges' deterministic encodings under the graph tag; it binds the edge count. One edge opens to
it by a logarithmic path (`KgEdgeOpening`, `verifyKgEdgeOpening`): `verifyKgEdgeOpening_complete`
and `verifyKgEdgeOpening_binding`, and `evalOpenedKgQuery` answers `entailed` for an opened edge
and never refutes (`openedKgQuery_entailed_sound`, `openedKgQuery_complete`).
`evalOpenWorldKgQuery` answers `entailed` only for an edge found in an authenticated witness,
`refuted` only under a `CompletenessToken` that verifies for exactly this graph, predicate and
subject and commits to the witness, and `undetermined` otherwise
(`openWorld_without_token_never_refutes`, `openWorld_invalid_token_never_refutes`,
`completenessToken_refute_sound`, `openWorld_entailed_sound`,
`completenessToken_refute_binding`). `edgesCollision` is the explicit collision of two different
within-width edge arrays with one digest.

**§3 Forget while forked (`K10`).** A vault of 16 buckets under a depth-4 Merkle tree.
`forgetHistoricalBase` keeps only the base root and is total: an open fork does not block it.
A fork merges into the compacted vault by presenting a `BaseProof` (its base bucket and a
Merkle path). `forget_commutes_with_fork_merge`: the honest proof verifies and merging after
forgetting is forgetting after merging, as an equation. `baseProofCollision` computes, from two
verifying proofs of different base buckets at one index under one root, an explicit collision
of the bucket hash or of the node hash; `baseProof_binding_collision` states it.
`merge3Bucket_lookup` is the three-way merge's law per key.

The hash is a parameter (`Hasher`: a tagged hash with 32-byte output); `cshakeHasher` is
cSHAKE256 with the tag as customization. Both, the key sort and the splice live in
`Obend.Judge.Commit` (below the JSON machine) and are re-exported here.

What is not here: `keysDistinctB` is proved sound, not complete; a refutation still presents the
tokened slice whole (absence has no logarithmic proof here: the leaves are not required sorted in
the tree); the token's tag is a keyed hash under a shared secret, not a signature; buckets are
fixed at 16.
-/

public import Obend.Codec.DetCbor
public import Obend.Digest.Cshake256
public import Obend.Judge.VpaComplementAndJson
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson

public section

namespace Obend.Vault.Lsafe

export Obend.Judge.Commit (Hasher cshakeHasher HashCollision mergeFuel mergeFuel_perm mergePass
  mergePass_perm mergeLoop mergeLoop_perm sortBy flatten_singletons sortBy_perm keysDistinctB
  keysDistinctB_sound spliceByteArray extract_toList spliceByteArray_toList)

open Obend.Codec.DetCbor
open Obend.Judge.VpaJson
open Obend.Judge.Commit (countSpan countSpan_injective)

set_option autoImplicit false

/-! ## 1. Redaction confinement over the JSON grammar

The machine is `Obend.Judge.VpaJson.stepJson`: values, structural characters in their places,
strings with the short escapes and `\uXXXX`, numbers, literals, unique keys per object. -/

/-- The machine state after the first `i` bytes of a document. -/
def stateAt (doc : ByteArray) (i : Nat) : JState := jsonStateAt doc i

/-- The machine state after the whole document. -/
def lsafeRun (doc : ByteArray) : JState := jsonRun doc

/-- **The document check**: one RFC 8259 value with unique keys in every object. -/
def runLsafeVpa (doc : ByteArray) : Bool := runFullJsonGrammar doc

/-- The key sets of the objects of a document, innermost-closed first. -/
def objectKeysOf (doc : ByteArray) : List (List ByteArray) := jsonObjectKeys doc

/-- **A byte a redaction may write**: a mask byte (printable ASCII without `"` and `\`) that is
neither `<` nor `>` (tag breakout). Carriage return and line feed are below `0x20`. -/
def isSafeRedactionByte (b : UInt8) : Bool := isSafeMaskByte b && b != 0x3c && b != 0x3e

theorem isSafeRedactionByte_spec {b : UInt8} (h : isSafeRedactionByte b = true) :
    isSafeMaskByte b = true ∧
      b ≠ 0x22 ∧ b ≠ 0x5c ∧ b ≠ 0x0d ∧ b ≠ 0x0a ∧ b ≠ 0x3c ∧ b ≠ 0x3e := by
  simp only [isSafeRedactionByte, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hm, h3c⟩, h3e⟩ := h
  have hm' := hm
  simp only [isSafeMaskByte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hm'
  obtain ⟨⟨⟨h20, _⟩, h22⟩, h5c⟩ := hm'
  refine ⟨hm, h22, h5c, ?_, ?_, h3c, h3e⟩
  · intro h0d; rw [h0d] at h20; exact absurd h20 (by decide)
  · intro h0a; rw [h0a] at h20; exact absurd h20 (by decide)

/-- **The redaction check.** The document passes the grammar, the span `[l, r)` starts in a value
string outside any escape, stays inside that string at every byte and ends in the starting
machine state (so it cuts no escape sequence), and every byte written is safe. -/
def checkLsafeRedaction (doc : ByteArray) (l r : Nat) (replacement : ByteArray) : Bool :=
  runFullJsonGrammar doc && checkJsonRedaction doc l r replacement &&
    replacement.data.toList.all isSafeRedactionByte

theorem checkLsafeRedaction_parts {doc replacement : ByteArray} {l r : Nat}
    (h : checkLsafeRedaction doc l r replacement = true) :
    runFullJsonGrammar doc = true ∧ checkJsonRedaction doc l r replacement = true ∧
      ∀ x ∈ replacement.data.toList, isSafeRedactionByte x = true := by
  simp only [checkLsafeRedaction, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Redaction confinement.** After an accepted redaction:
1. the spliced document passes the grammar;
2. at every offset `j` after the replacement the machine is in the state the original was in
   at `r + j`, so the suffix makes exactly the original transitions;
3. all through the replacement the machine is in the original state at `l`;
4. the replacement carries no `"`, `\`, carriage return, line feed, `<` or `>`;
5. the object key sets are the original ones, and so is the whole final state. -/
theorem lsafe_redaction_confinement {doc replacement : ByteArray} {l r : Nat}
    (h : checkLsafeRedaction doc l r replacement = true) :
    runLsafeVpa (spliceByteArray doc l r replacement) = true ∧
    (∀ j, stateAt (spliceByteArray doc l r replacement) (l + replacement.size + j) =
      stateAt doc (r + j)) ∧
    (∀ j, j ≤ replacement.size →
      stateAt (spliceByteArray doc l r replacement) (l + j) = stateAt doc l) ∧
    (∀ x ∈ replacement.data.toList,
      x ≠ 0x22 ∧ x ≠ 0x5c ∧ x ≠ 0x0d ∧ x ≠ 0x0a ∧ x ≠ 0x3c ∧ x ≠ 0x3e) ∧
    objectKeysOf (spliceByteArray doc l r replacement) = objectKeysOf doc ∧
    lsafeRun (spliceByteArray doc l r replacement) = lsafeRun doc := by
  obtain ⟨hgram, hred, hsafe⟩ := checkLsafeRedaction_parts h
  obtain ⟨hv, hk, hcut⟩ := jsonRedaction_preserves_valid_parse_and_keys hred
  obtain ⟨hlr, hr, hmode⟩ : l ≤ r ∧ r ≤ doc.size ∧ (jsonStateAt doc l).mode = .str false .normal := by
    have h' := hred
    simp only [checkJsonRedaction, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact ⟨h'.1.1.1.1, h'.1.1.1.2, h'.1.1.2⟩
  have hL := toList_length doc
  have hR := toList_length replacement
  have hS := spliceByteArray_toList doc l r replacement
  have hlenl : (doc.data.toList.take l).length = l := by rw [List.length_take, hL]; omega
  have hmask : replacement.data.toList.all isSafeMaskByte = true :=
    List.all_eq_true.2 fun x hx => (isSafeRedactionByte_spec (hsafe x hx)).1
  refine ⟨?_, ?_, ?_, fun x hx => (isSafeRedactionByte_spec (hsafe x hx)).2, hk, jsonRedaction_run hred⟩
  · unfold runLsafeVpa
    rw [hv]
    exact hgram
  · intro j
    have hlen2 : (doc.data.toList.take l ++ replacement.data.toList).length =
        l + replacement.size := by rw [List.length_append, hlenl, hR]
    have hsplit : (spliceByteArray doc l r replacement).data.toList.take
        (l + replacement.size + j) =
        doc.data.toList.take l ++ replacement.data.toList ++ (doc.data.toList.drop r).take j := by
      rw [hS, List.take_add, List.take_left' hlen2, List.drop_left' hlen2]
    unfold stateAt
    rw [jsonStateAt_eq, hsplit, hcut j]
  · intro j hj
    have hsplit : (spliceByteArray doc l r replacement).data.toList.take (l + j) =
        doc.data.toList.take l ++ replacement.data.toList.take j := by
      rw [hS, List.append_assoc, List.take_add, List.take_left' hlenl, List.drop_left' hlenl,
        List.take_append_of_le_length (by rw [hR]; exact hj)]
    have hpre : (replacement.data.toList.take j).all isSafeMaskByte = true := by
      rw [List.all_eq_true] at hmask ⊢
      exact fun x hx => hmask x (List.mem_of_mem_take hx)
    unfold stateAt
    rw [jsonStateAt_eq, hsplit, specRunJson_append, ← jsonStateAt_eq,
      specRunJson_safe hmode _ hpre]

/-- **No duplicate key.** Every object the machine closed has pairwise distinct keys. -/
theorem lsafe_object_keys_nodup (doc : ByteArray) : ∀ ks ∈ objectKeysOf doc, ks.Nodup :=
  json_object_keys_nodup doc

/-! ### The value tree and its canonical commitment -/

/-- A JSON value: numbers keep their literal bytes, strings and keys their content bytes. -/
inductive JVal where
  | null
  | bool (b : Bool)
  | num (lit : ByteArray)
  | str (s : ByteArray)
  | arr (xs : List JVal)
  | obj (kvs : List (ByteArray × JVal))

mutual
/-- The image in deterministic CBOR: `null ↦ 0`, a number ↦ its literal as a byte string, a
string ↦ text, an object ↦ a map with text keys in the order given. -/
def jsonToCbor : JVal → CborVal
  | .null => .uint 0
  | .bool b => .simpleBool b
  | .num lit => .bytes lit
  | .str s => .text s
  | .arr xs => .array (jsonListToCbor xs)
  | .obj kvs => .map (jsonMembersToCbor kvs)
termination_by structural v => v
def jsonListToCbor : List JVal → List CborVal
  | [] => []
  | x :: xs => jsonToCbor x :: jsonListToCbor xs
termination_by structural xs => xs
def jsonMembersToCbor : List (ByteArray × JVal) → List (CborVal × CborVal)
  | [] => []
  | kv :: rest => (.text kv.1, jsonToCbor kv.2) :: jsonMembersToCbor rest
termination_by structural kvs => kvs
end

mutual
/-- The inverse reading, where there is one. -/
def cborToJson : CborVal → Option JVal
  | .uint n => if n = 0 then some .null else none
  | .nint _ => none
  | .simpleBool b => some (.bool b)
  | .bytes lit => some (.num lit)
  | .text s => some (.str s)
  | .array xs => (cborListToJson xs).map .arr
  | .map kvs => (cborMembersToJson kvs).map .obj
termination_by structural v => v
def cborListToJson : List CborVal → Option (List JVal)
  | [] => some []
  | x :: xs =>
    match cborToJson x, cborListToJson xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none
termination_by structural xs => xs
def cborMembersToJson : List (CborVal × CborVal) → Option (List (ByteArray × JVal))
  | [] => some []
  | (k, v) :: rest =>
    match k, cborToJson v, cborMembersToJson rest with
    | .text s, some jv, some r => some ((s, jv) :: r)
    | _, _, _ => none
termination_by structural kvs => kvs
end

mutual
theorem cborToJson_jsonToCbor : ∀ v : JVal, cborToJson (jsonToCbor v) = some v
  | .null => by simp [jsonToCbor, cborToJson]
  | .bool _ => by simp [jsonToCbor, cborToJson]
  | .num _ => by simp [jsonToCbor, cborToJson]
  | .str _ => by simp [jsonToCbor, cborToJson]
  | .arr xs => by simp [jsonToCbor, cborToJson, cborListToJson_jsonListToCbor xs]
  | .obj kvs => by simp [jsonToCbor, cborToJson, cborMembersToJson_jsonMembersToCbor kvs]
termination_by structural v => v
theorem cborListToJson_jsonListToCbor : ∀ xs : List JVal,
    cborListToJson (jsonListToCbor xs) = some xs
  | [] => by simp [jsonListToCbor, cborListToJson]
  | x :: xs => by
    simp [jsonListToCbor, cborListToJson, cborToJson_jsonToCbor x, cborListToJson_jsonListToCbor xs]
termination_by structural xs => xs
theorem cborMembersToJson_jsonMembersToCbor : ∀ kvs : List (ByteArray × JVal),
    cborMembersToJson (jsonMembersToCbor kvs) = some kvs
  | [] => by simp [jsonMembersToCbor, cborMembersToJson]
  | kv :: rest => by
    simp [jsonMembersToCbor, cborMembersToJson, cborToJson_jsonToCbor kv.2,
      cborMembersToJson_jsonMembersToCbor rest]
termination_by structural kvs => kvs
end

theorem jsonToCbor_injective {a b : JVal} (h : jsonToCbor a = jsonToCbor b) : a = b :=
  Option.some.inj (by rw [← cborToJson_jsonToCbor a, ← cborToJson_jsonToCbor b, h])

/-- The customization string of value commitments. -/
def jsonTag : String := "obend.judge.json.cbor.v1"

/-- **The commitment of a value**: the digest of its canonical CBOR, when the image is canonical
(strings valid UTF-8, object keys strictly ascending by encoding). -/
def jsonCborCommit (H : Hasher) (v : JVal) : Option ByteArray :=
  if CanonicalCbor (jsonToCbor v) then some (H.hash jsonTag (encodeDetCbor (jsonToCbor v))) else none

theorem jsonCborCommit_canonical {H : Hasher} {v : JVal} {d : ByteArray}
    (h : jsonCborCommit H v = some d) :
    CanonicalCbor (jsonToCbor v) = true ∧ d = H.hash jsonTag (encodeDetCbor (jsonToCbor v)) := by
  unfold jsonCborCommit at h
  split at h
  · rename_i hc; exact ⟨hc, (Option.some.inj h).symm⟩
  · cases h

/-- **Value commitments bind**: two values with one commitment are equal, or their canonical
encodings are two different messages with one digest. -/
theorem jsonCborCommit_binding (H : Hasher) {v₁ v₂ : JVal} {d : ByteArray}
    (h₁ : jsonCborCommit H v₁ = some d) (h₂ : jsonCborCommit H v₂ = some d) :
    v₁ = v₂ ∨ ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash jsonTag m₁ = H.hash jsonTag m₂ := by
  obtain ⟨c1, e1⟩ := jsonCborCommit_canonical h₁
  obtain ⟨c2, e2⟩ := jsonCborCommit_canonical h₂
  by_cases he : encodeDetCbor (jsonToCbor v₁) = encodeDetCbor (jsonToCbor v₂)
  · exact Or.inl (jsonToCbor_injective (encodeDetCbor_injective_canonical _ _ c1 c2 he))
  · exact Or.inr ⟨_, _, he, e1.symm.trans e2⟩

theorem jsonMembersToCbor_keys : ∀ kvs : List (ByteArray × JVal),
    (jsonMembersToCbor kvs).map (·.1) = kvs.map fun kv => CborVal.text kv.1
  | [] => by simp [jsonMembersToCbor]
  | kv :: rest => by simp [jsonMembersToCbor, jsonMembersToCbor_keys rest]

/-- **A committed object has unique keys.** -/
theorem jsonCborCommit_keys_nodup {H : Hasher} {kvs : List (ByteArray × JVal)} {d : ByteArray}
    (h : jsonCborCommit H (.obj kvs) = some d) : (kvs.map (·.1)).Nodup := by
  have hc := (jsonCborCommit_canonical h).1
  simp only [jsonToCbor] at hc
  have hn := canonicalMap_keys_nodup hc
  rw [jsonMembersToCbor_keys, List.Nodup, List.pairwise_map] at hn
  rw [List.Nodup, List.pairwise_map]
  exact hn.imp fun hne heq => hne (by rw [heq])

/-! ### Span roots bind the whole list, computably

`Obend.Judge.VpaJson` proves that one span opens to a root or a collision exists. Here the
collision is computed: from two different span lists whose roots share a `top`, an explicit pair
of messages. No choice is used, so the extractor runs. -/

/-- Two span lists with one list of leaf digests: the first difference is a leaf collision. -/
def leafListCollision (H : Hasher) (tag : String) : (s₁ s₂ : List ByteArray) → s₁ ≠ s₂ →
    s₁.map (leafHash H tag) = s₂.map (leafHash H tag) → HashCollision H tag
  | [], [], hne, _ => absurd rfl hne
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: r, b :: s, hne, h =>
    have h' : leafHash H tag a :: r.map (leafHash H tag) =
        leafHash H tag b :: s.map (leafHash H tag) := h
    if hm : leafMsg a = leafMsg b then
      leafListCollision H tag r s (fun hrs => hne (by rw [leafMsg_injective hm, hrs]))
        (List.cons.inj h').2
    else ⟨leafMsg a, leafMsg b, hm, (List.cons.inj h').1⟩

/-- Two different levels of one length with one image under `pairUp`: a node collision. -/
def pairUpCollision (H : Hasher) (tag : String) : (l₁ l₂ : List ByteArray) →
    l₁.length = l₂.length → (∀ y ∈ l₁, y.size = 32) → (∀ y ∈ l₂, y.size = 32) → l₁ ≠ l₂ →
    pairUp H tag l₁ = pairUp H tag l₂ → HashCollision H tag
  | [], [], _, _, _, hne, _ => absurd rfl hne
  | [a], [b], _, _, _, hne, h => absurd (show [a] = [b] from h) hne
  | a :: b :: r, c :: d :: s, hlen, h₁, h₂, hne, h =>
    have h' : nodeHash H tag a b :: pairUp H tag r = nodeHash H tag c d :: pairUp H tag s := h
    if hm : nodeMsg a b = nodeMsg c d then
      pairUpCollision H tag r s (Nat.succ.inj (Nat.succ.inj hlen))
        (fun y hy => h₁ y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))
        (fun y hy => h₂ y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))
        (fun hrs => hne (by
          obtain ⟨hac, hbd⟩ := nodeMsg_injective hm
            ((h₁ a List.mem_cons_self).trans (h₂ c List.mem_cons_self).symm)
          rw [hac, hbd, hrs]))
        (List.cons.inj h').2
    else ⟨nodeMsg a b, nodeMsg c d, hm, (List.cons.inj h').1⟩
  | [], _ :: _, hlen, _, _, _, _ => absurd hlen (Nat.succ_ne_zero _).symm
  | _ :: _, [], hlen, _, _, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | [_], _ :: _ :: _, hlen, _, _, _, _ => absurd (Nat.succ.inj hlen) (Nat.succ_ne_zero _).symm
  | _ :: _ :: _, [_], hlen, _, _, _, _ => absurd (Nat.succ.inj hlen) (Nat.succ_ne_zero _)

theorem small_levels_eq : ∀ {l₁ l₂ : List ByteArray}, l₁.length = l₂.length → l₁.length ≤ 1 →
    l₁.headD ByteArray.empty = l₂.headD ByteArray.empty → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [a], [b], _, _, h => congrArg (fun x => [x]) (show a = b from h)
  | [], _ :: _, hlen, _, _ => absurd hlen (Nat.succ_ne_zero _).symm
  | [_], [], hlen, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | [_], _ :: _ :: _, hlen, _, _ => absurd (Nat.succ.inj hlen) (Nat.succ_ne_zero _).symm
  | _ :: _ :: _, _, _, hs, _ => absurd (Nat.le_of_succ_le_succ hs) (Nat.not_succ_le_zero _)

/-- Two different levels of one length, within the fuel, with one tree top: a node collision. -/
def treeTopCollision (H : Hasher) (tag : String) : (f : Nat) → (l₁ l₂ : List ByteArray) →
    l₁.length = l₂.length → l₁.length ≤ f → (∀ y ∈ l₁, y.size = 32) → (∀ y ∈ l₂, y.size = 32) →
    l₁ ≠ l₂ → treeTop H tag f l₁ = treeTop H tag f l₂ → HashCollision H tag
  | 0, l₁, l₂, hlen, hf, _, _, hne, _ =>
    absurd (by
      have e1 : l₁ = [] := List.length_eq_zero_iff.1 (by omega)
      have e2 : l₂ = [] := List.length_eq_zero_iff.1 (by omega)
      rw [e1, e2]) hne
  | f + 1, l₁, l₂, hlen, hf, h₁, h₂, hne, h =>
    if hs : l₁.length ≤ 1 then
      absurd (small_levels_eq hlen hs (by
        have hs2 : l₂.length ≤ 1 := by rw [← hlen]; exact hs
        simpa only [treeTop, hs, hs2, ↓reduceIte] using h)) hne
    else if hp : pairUp H tag l₁ = pairUp H tag l₂ then
      pairUpCollision H tag l₁ l₂ hlen h₁ h₂ hne hp
    else
      treeTopCollision H tag f (pairUp H tag l₁) (pairUp H tag l₂)
        (by rw [pairUp_length, pairUp_length, hlen]) (by rw [pairUp_length]; omega)
        (pairUp_sizes H tag l₁ h₁) (pairUp_sizes H tag l₂ h₂) hp
        (by
          have hs2 : ¬ l₂.length ≤ 1 := by rw [← hlen]; exact hs
          simpa only [treeTop, hs, hs2, ↓reduceIte] using h)

theorem leafHashes_size (H : Hasher) (tag : String) (s : List ByteArray) :
    ∀ y ∈ s.map (leafHash H tag), y.size = 32 := fun y hy => by
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
  exact H.size_eq _ _

/-- **Span roots bind the whole list.** Two different span lists whose roots have one `top`
give an explicit collision at the tag: of two root messages, of two count leaves, of two span
leaves, or of two nodes. -/
def spanRootCollision (H : Hasher) (tag : String) {s₁ s₂ : List ByteArray} (hne : s₁ ≠ s₂)
    (h : (spanMerkleRoot H tag s₁).top = (spanMerkleRoot H tag s₂).top) : HashCollision H tag :=
  if hm : rootMsg (leafHash H tag (countSpan s₁.length))
        (treeTop H tag s₁.length (s₁.map (leafHash H tag))) =
      rootMsg (leafHash H tag (countSpan s₂.length))
        (treeTop H tag s₂.length (s₂.map (leafHash H tag))) then
    if hl : leafMsg (countSpan s₁.length) = leafMsg (countSpan s₂.length) then
      have hn : s₁.length = s₂.length := countSpan_injective (leafMsg_injective hl)
      if hleaves : s₁.map (leafHash H tag) = s₂.map (leafHash H tag) then
        leafListCollision H tag s₁ s₂ hne hleaves
      else
        treeTopCollision H tag s₁.length (s₁.map (leafHash H tag)) (s₂.map (leafHash H tag))
          (by simp [hn]) (by simp) (leafHashes_size H tag s₁) (leafHashes_size H tag s₂) hleaves
          (by
            have ht := (pairMsg_injective hm ((H.size_eq _ _).trans (H.size_eq _ _).symm)).2
            rw [← hn] at ht
            exact ht)
    else
      ⟨leafMsg (countSpan s₁.length), leafMsg (countSpan s₂.length), hl,
        (pairMsg_injective hm ((H.size_eq _ _).trans (H.size_eq _ _).symm)).1⟩
  else ⟨_, _, hm, h⟩

/-! ## 2. Open-world queries, completeness tokens, and single-edge openings -/


def graphTag : String := "obend.vault.lsafe.graph.v1"
def completeTag : String := "obend.vault.lsafe.complete.v1"

/-- A knowledge-graph edge. -/
structure KgEdge where
  predId : UInt64
  subj : ByteArray
  obj : ByteArray
  deriving DecidableEq

def KgEdge.toCbor (e : KgEdge) : CborVal := .array [.uint e.predId, .bytes e.subj, .bytes e.obj]

/-- The sort key of an edge: its deterministic encoding. -/
def KgEdge.key (e : KgEdge) : ByteArray := encodeDetCbor e.toCbor

def edgesCbor (es : Array KgEdge) : CborVal := .array (es.toList.map KgEdge.toCbor)

/-- The leaves of an edge array: each edge's deterministic encoding. -/
def edgeLeaves (es : Array KgEdge) : List ByteArray := es.toList.map KgEdge.key

/-- **The commitment to an edge array**: the `top` of the span tree over the edges' encodings
under the graph tag (leaf, node and root messages are domain-separated by their first byte). It
binds the edge count, and one edge opens to it by a logarithmic path. -/
def edgesDigest (H : Hasher) (es : Array KgEdge) : ByteArray :=
  (spanMerkleRoot H graphTag (edgeLeaves es)).top

inductive QueryVerdict where
  | entailed
  | refuted
  | undetermined
  deriving DecidableEq, Repr

/-- `complete_p(S)`: the issuer's statement that, in the graph with this digest, the edges with
this predicate and subject are exactly the slice with this digest. -/
structure CompletenessToken where
  graphDigest32 : ByteArray
  predId : UInt64
  subjScope : ByteArray
  scopedEdgesDigest32 : ByteArray
  issuerTag32 : ByteArray
  deriving DecidableEq

/-- The issuer's tag over the token's four fields, keyed by the shared authenticator. -/
def tokenMac (H : Hasher) (auth32 : ByteArray) (tok : CompletenessToken) : ByteArray :=
  H.hash completeTag (encodeDetCbor (.array [.bytes auth32, .bytes tok.graphDigest32,
    .uint tok.predId, .bytes tok.subjScope, .bytes tok.scopedEdgesDigest32]))

def inScope (predId : UInt64) (subj : ByteArray) (es : Array KgEdge) : Bool :=
  es.toList.all fun e => e.predId == predId && decide (e.subj = subj)

/-- A token verifies for a query when it names this graph, predicate and subject, carries the
issuer's tag, and commits to the presented witness, which is in scope and strictly sorted. -/
def verifyCompletenessToken (H : Hasher) (graphDigest32 expectedAuth32 : ByteArray)
    (predId : UInt64) (subj : ByteArray) (witnessEdges : Array KgEdge)
    (tok : CompletenessToken) : Bool :=
  decide (tok.graphDigest32 = graphDigest32) && tok.predId == predId &&
    decide (tok.subjScope = subj) && decide (tok.issuerTag32 = tokenMac H expectedAuth32 tok) &&
    inScope predId subj witnessEdges && sortedByKeyB KgEdge.key witnessEdges.toList &&
    decide (edgesDigest H witnessEdges = tok.scopedEdgesDigest32)

/-- Membership in a sorted edge array by binary search on the key, confirmed on the edge. -/
def containsEdge (es : Array KgEdge) (q : KgEdge) : Bool :=
  match sortedSearch KgEdge.key es q.key with
  | some e => decide (e = q)
  | none => false

def tokenOk (H : Hasher) (graphDigest32 expectedAuth32 : ByteArray) (predId : UInt64)
    (subj : ByteArray) (witnessEdges : Array KgEdge) : Option CompletenessToken → Bool
  | some tok => verifyCompletenessToken H graphDigest32 expectedAuth32 predId subj witnessEdges tok
  | none => false

/-- The witness is the whole committed graph. -/
def graphOk (H : Hasher) (graphDigest32 : ByteArray) (witnessEdges : Array KgEdge) : Bool :=
  sortedByKeyB KgEdge.key witnessEdges.toList && decide (edgesDigest H witnessEdges = graphDigest32)

/-- **The open-world query.** Entailed: the edge is in an authenticated witness. Refuted: a
verifying completeness token commits to the witness and the edge is not in it. Otherwise the
answer is undetermined; absence from a graph is not falsity. -/
def evalOpenWorldKgQuery (H : Hasher) (graphDigest32 expectedAuth32 : ByteArray)
    (predId : UInt64) (subj targetObj : ByteArray) (witnessEdges : Array KgEdge)
    (tok? : Option CompletenessToken) : QueryVerdict :=
  if (tokenOk H graphDigest32 expectedAuth32 predId subj witnessEdges tok? ||
      graphOk H graphDigest32 witnessEdges) &&
      containsEdge witnessEdges ⟨predId, subj, targetObj⟩ then .entailed
  else if tokenOk H graphDigest32 expectedAuth32 predId subj witnessEdges tok? then .refuted
  else .undetermined

/-- **No token, no refutation.** An empty witness cannot forge a non-entailment. -/
theorem openWorld_without_token_never_refutes (H : Hasher) (g a : ByteArray) (p : UInt64)
    (s o : ByteArray) (edges : Array KgEdge) :
    evalOpenWorldKgQuery H g a p s o edges none ≠ .refuted := by
  unfold evalOpenWorldKgQuery
  split
  · intro h; cases h
  · simp [tokenOk]

/-- A token that does not verify refutes nothing either. -/
theorem openWorld_invalid_token_never_refutes (H : Hasher) (g a : ByteArray) (p : UInt64)
    (s o : ByteArray) (edges : Array KgEdge) (tok : CompletenessToken)
    (hbad : verifyCompletenessToken H g a p s edges tok = false) :
    evalOpenWorldKgQuery H g a p s o edges (some tok) ≠ .refuted := by
  unfold evalOpenWorldKgQuery
  split
  · intro h; cases h
  · simp [tokenOk, hbad]

theorem containsEdge_of_mem {es : Array KgEdge} {q : KgEdge}
    (hs : es.toList.Pairwise (fun x y => lexLtBytes x.key y.key = true)) (hq : q ∈ es.toList) :
    containsEdge es q = true := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hq
  have hx : es.toList[i]? = some q := by rw [List.getElem?_eq_getElem hi, hget]
  unfold containsEdge
  rw [sortedSearch_eq_find KgEdge.key es q.key hs, find?_of_sorted hs hx]
  simp

theorem mem_of_containsEdge {es : Array KgEdge} {q : KgEdge}
    (hs : es.toList.Pairwise (fun x y => lexLtBytes x.key y.key = true))
    (h : containsEdge es q = true) : q ∈ es.toList := by
  unfold containsEdge at h
  rw [sortedSearch_eq_find KgEdge.key es q.key hs] at h
  cases hf : es.toList.find? (fun e => decide (e.key = q.key)) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, decide_eq_true_eq] at h
    subst h
    exact List.mem_of_find?_eq_some hf

theorem verifyCompletenessToken_parts {H : Hasher} {g a : ByteArray} {p : UInt64}
    {s : ByteArray} {edges : Array KgEdge} {tok : CompletenessToken}
    (h : verifyCompletenessToken H g a p s edges tok = true) :
    tok.graphDigest32 = g ∧ tok.predId = p ∧ tok.subjScope = s ∧
      tok.issuerTag32 = tokenMac H a tok ∧
      (∀ e ∈ edges.toList, e.predId = p ∧ e.subj = s) ∧
      edges.toList.Pairwise (fun x y => lexLtBytes x.key y.key = true) ∧
      edgesDigest H edges = tok.scopedEdgesDigest32 := by
  simp only [verifyCompletenessToken, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, sortedByKeyB_sound _ _ h6, h7⟩
  intro e he
  have := List.all_eq_true.1 h5 e he
  simpa using this

/-- **Refutation is sound.** A `refuted` verdict comes with a token that verifies for this
graph, predicate and subject and commits to the witness; the witness lies in scope, and the
queried edge is not in it. -/
theorem completenessToken_refute_sound {H : Hasher} {g a : ByteArray} {p : UInt64}
    {s o : ByteArray} {edges : Array KgEdge} {tok? : Option CompletenessToken}
    (h : evalOpenWorldKgQuery H g a p s o edges tok? = .refuted) :
    ∃ tok, tok? = some tok ∧ verifyCompletenessToken H g a p s edges tok = true ∧
      edgesDigest H edges = tok.scopedEdgesDigest32 ∧
      (∀ e ∈ edges.toList, e.predId = p ∧ e.subj = s) ∧ (⟨p, s, o⟩ : KgEdge) ∉ edges.toList := by
  unfold evalOpenWorldKgQuery at h
  split at h
  · cases h
  · rename_i hne
    split at h
    · rename_i htok
      cases tok? with
      | none => simp [tokenOk] at htok
      | some tok =>
        simp only [tokenOk] at htok
        obtain ⟨_, _, _, _, hscope, hsorted, hdig⟩ := verifyCompletenessToken_parts htok
        refine ⟨tok, rfl, htok, hdig, hscope, ?_⟩
        intro hmem
        apply hne
        simp only [tokenOk, htok, Bool.true_or, Bool.true_and]
        exact containsEdge_of_mem hsorted hmem
    · cases h

/-- **Entailment is sound.** An `entailed` verdict means the edge is in the witness, and the
witness is the committed graph or the slice a verifying token commits to. -/
theorem openWorld_entailed_sound {H : Hasher} {g a : ByteArray} {p : UInt64}
    {s o : ByteArray} {edges : Array KgEdge} {tok? : Option CompletenessToken}
    (h : evalOpenWorldKgQuery H g a p s o edges tok? = .entailed) :
    (⟨p, s, o⟩ : KgEdge) ∈ edges.toList ∧
      (edgesDigest H edges = g ∨
        ∃ tok, tok? = some tok ∧ verifyCompletenessToken H g a p s edges tok = true) := by
  unfold evalOpenWorldKgQuery at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
    obtain ⟨hauth, hcont⟩ := hc
    rcases hauth with htok | hg
    · cases tok? with
      | none => simp [tokenOk] at htok
      | some tok =>
        simp only [tokenOk] at htok
        obtain ⟨_, _, _, _, _, hsorted, _⟩ := verifyCompletenessToken_parts htok
        exact ⟨mem_of_containsEdge hsorted hcont, Or.inr ⟨tok, rfl, htok⟩⟩
    · simp only [graphOk, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨mem_of_containsEdge (sortedByKeyB_sound _ _ hg.1) hcont, Or.inl hg.2⟩
  · split at h <;> cases h

/-- **Binding to the issuer's slice.** If the query is refuted under a token and `authentic` is
the slice the issuer committed to, the edge is absent from `authentic`, or the presented witness
and `authentic` are two different edge arrays with one commitment. -/
theorem completenessToken_refute_binding {H : Hasher} {g a : ByteArray} {p : UInt64}
    {s o : ByteArray} {edges : Array KgEdge} {tok : CompletenessToken}
    (h : evalOpenWorldKgQuery H g a p s o edges (some tok) = .refuted)
    (authentic : Array KgEdge) (hauth : edgesDigest H authentic = tok.scopedEdgesDigest32) :
    (⟨p, s, o⟩ : KgEdge) ∉ authentic.toList ∨
      (edges ≠ authentic ∧ edgesDigest H edges = edgesDigest H authentic) := by
  obtain ⟨tok', htok, _, hdig, _, habs⟩ := completenessToken_refute_sound h
  cases htok
  by_cases he : edges = authentic
  · subst he
    exact Or.inl habs
  · exact Or.inr ⟨he, hdig.trans hauth.symm⟩

theorem toCbor_injective : ∀ {a b : List KgEdge},
    a.map KgEdge.toCbor = b.map KgEdge.toCbor → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hxy, hrest⟩ := h
    have hx : x = y := by
      obtain ⟨p1, s1, o1⟩ := x
      obtain ⟨p2, s2, o2⟩ := y
      simp only [KgEdge.toCbor, CborVal.array.injEq, List.cons.injEq, CborVal.uint.injEq,
        CborVal.bytes.injEq, and_true] at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      rfl
    rw [hx, toCbor_injective hrest]

theorem KgEdge.key_injective {x y : KgEdge} (hx : WithinWidth x.toCbor = true)
    (hy : WithinWidth y.toCbor = true) (h : x.key = y.key) : x = y := by
  have hc := encodeDetCbor_injective _ _ hx hy h
  have hl := toCbor_injective (a := [x]) (b := [y]) (by simp [hc])
  simpa using hl

theorem edge_width_of_mem {es : Array KgEdge} (h : WithinWidth (edgesCbor es) = true) {e : KgEdge}
    (he : e ∈ es.toList) : WithinWidth e.toCbor = true := by
  simp only [WithinWidth, edgesCbor, wfVal, Bool.and_eq_true] at h
  exact wfList_mem h.2 (List.mem_map.2 ⟨e, he, rfl⟩)

theorem keys_injective : ∀ {a b : List KgEdge}, (∀ x ∈ a, WithinWidth x.toCbor = true) →
    (∀ y ∈ b, WithinWidth y.toCbor = true) → a.map KgEdge.key = b.map KgEdge.key → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [KgEdge.key_injective (ha x List.mem_cons_self) (hb y List.mem_cons_self) h.1,
      keys_injective (fun z hz => ha z (List.mem_cons_of_mem _ hz))
        (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h.2]

/-- Two different edge arrays with one commitment, both within width, are an explicit
collision of the hash at the graph tag, computed by `spanRootCollision`. -/
def edgesCollision (H : Hasher) {e₁ e₂ : Array KgEdge} (hne : e₁ ≠ e₂)
    (h₁ : WithinWidth (edgesCbor e₁) = true) (h₂ : WithinWidth (edgesCbor e₂) = true)
    (heq : edgesDigest H e₁ = edgesDigest H e₂) : HashCollision H graphTag :=
  spanRootCollision H graphTag
    (fun hl => hne (Array.toList_inj.1 (keys_injective (fun _ hx => edge_width_of_mem h₁ hx)
      (fun _ hy => edge_width_of_mem h₂ hy) hl))) heq

/-! ### Single-edge openings -/

/-- The opening of one edge: the edge count the digest binds and the inclusion path. -/
structure KgEdgeOpening where
  count : Nat
  proof : SpanProof

/-- **Verify one edge against a graph digest**, in `⌈log₂ count⌉` hashes. -/
def verifyKgEdgeOpening (H : Hasher) (graphDigest32 : ByteArray) (e : KgEdge)
    (o : KgEdgeOpening) : Bool :=
  verifySpanMerkleInclusion H graphTag ⟨o.count, graphDigest32⟩ e.key o.proof

/-- The honest opening of the edge at an index. -/
def openKgEdge (H : Hasher) (es : Array KgEdge) (i : Nat) : KgEdgeOpening :=
  ⟨es.size, spanMerkleProof H graphTag (edgeLeaves es) i⟩

/-- **Completeness**: the honest opening of every committed edge verifies. -/
theorem verifyKgEdgeOpening_complete (H : Hasher) (es : Array KgEdge) (i : Nat) (hi : i < es.size) :
    verifyKgEdgeOpening H (edgesDigest H es) es[i] (openKgEdge H es i) = true := by
  have hl : i < (edgeLeaves es).length := by simp [edgeLeaves]; exact hi
  have h := verifySpanMerkleInclusion_complete H graphTag (edgeLeaves es) i hl
  have hroot : (⟨es.size, edgesDigest H es⟩ : SpanRoot) =
      spanMerkleRoot H graphTag (edgeLeaves es) := by
    simp [spanMerkleRoot, edgesDigest, edgeLeaves]
  have hleaf : (edgeLeaves es)[i]'hl = es[i].key := by simp [edgeLeaves]
  unfold verifyKgEdgeOpening openKgEdge
  rw [hroot, ← hleaf]
  exact h

/-- **Openings bind.** An edge that opens to the digest of an edge array is, as an encoding, the
leaf at the opened index, whatever count the opening claims; or the hash collides at the graph
tag. -/
theorem verifyKgEdgeOpening_binding (H : Hasher) {es : Array KgEdge} {e : KgEdge}
    {o : KgEdgeOpening} : verifyKgEdgeOpening H (edgesDigest H es) e o = true →
    (edgeLeaves es)[o.proof.index]? = some e.key ∨
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash graphTag m₁ = H.hash graphTag m₂ :=
  verifySpanMerkleInclusion_top_binding H graphTag (root := ⟨o.count, edgesDigest H es⟩) rfl

/-- Within width the opened edge is an edge of the array. -/
theorem verifyKgEdgeOpening_mem (H : Hasher) {es : Array KgEdge} {e : KgEdge} {o : KgEdgeOpening}
    (hes : WithinWidth (edgesCbor es) = true) (he : WithinWidth e.toCbor = true) :
    verifyKgEdgeOpening H (edgesDigest H es) e o = true →
    e ∈ es.toList ∨ ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash graphTag m₁ = H.hash graphTag m₂ := by
  intro h
  rcases verifyKgEdgeOpening_binding H h with hk | hc
  · obtain ⟨x, hx, hxe⟩ := List.mem_map.1 (List.mem_of_getElem? hk)
    rw [← KgEdge.key_injective (edge_width_of_mem hes hx) he hxe]
    exact Or.inl hx
  · exact Or.inr hc

/-- **The opened query.** Entailed: the queried edge opens to the graph digest by a single-edge
inclusion path, with no other edge presented. Otherwise undetermined: a missing or failing
opening is not falsity, and this evaluator never refutes. -/
def evalOpenedKgQuery (H : Hasher) (graphDigest32 : ByteArray) (predId : UInt64)
    (subj targetObj : ByteArray) (opening? : Option KgEdgeOpening) : QueryVerdict :=
  match opening? with
  | some o =>
    if verifyKgEdgeOpening H graphDigest32 ⟨predId, subj, targetObj⟩ o then .entailed
    else .undetermined
  | none => .undetermined

theorem openedKgQuery_never_refutes (H : Hasher) (g : ByteArray) (p : UInt64) (s o : ByteArray)
    (opening? : Option KgEdgeOpening) : evalOpenedKgQuery H g p s o opening? ≠ .refuted := by
  unfold evalOpenedKgQuery
  split
  · split <;> exact fun h => by cases h
  · exact fun h => by cases h

/-- **An opened entailment is sound.** The edge is an edge of every within-width array with that
digest, or the hash collides at the graph tag. -/
theorem openedKgQuery_entailed_sound (H : Hasher) {es : Array KgEdge} {p : UInt64}
    {s o : ByteArray} {opening? : Option KgEdgeOpening}
    (hes : WithinWidth (edgesCbor es) = true)
    (he : WithinWidth (KgEdge.toCbor ⟨p, s, o⟩) = true) :
    evalOpenedKgQuery H (edgesDigest H es) p s o opening? = .entailed →
    (⟨p, s, o⟩ : KgEdge) ∈ es.toList ∨
      ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧ H.hash graphTag m₁ = H.hash graphTag m₂ := by
  intro h
  unfold evalOpenedKgQuery at h
  split at h
  · split at h
    · rename_i hv
      exact verifyKgEdgeOpening_mem H hes he hv
    · cases h
  · cases h

example : WithinWidth (edgesCbor #[⟨7, ⟨#[1]⟩, ⟨#[2]⟩⟩, ⟨7, ⟨#[1]⟩, ⟨#[3]⟩⟩]) = true := by decide +kernel

/-- **Every committed edge is entailed by its honest opening.** -/
theorem openedKgQuery_complete (H : Hasher) (es : Array KgEdge) (i : Nat) (hi : i < es.size) :
    evalOpenedKgQuery H (edgesDigest H es) es[i].predId es[i].subj es[i].obj
      (some (openKgEdge H es i)) = .entailed := by
  have h := verifyKgEdgeOpening_complete H es i hi
  simp only [evalOpenedKgQuery, h, ↓reduceIte]

/-! ## 3. Forgetting the historical base while a fork is open -/

def bucketTag : String := "obend.vault.bucket.v1"
def merkleTag : String := "obend.vault.merkle.v1"

/-- A bucket: key/value entries. -/
abbrev BucketEntries := List (ByteArray × ByteArray)

def bucketCbor (b : BucketEntries) : CborVal :=
  .array (b.map fun kv => .array [.bytes kv.1, .bytes kv.2])

/-- The bytes a bucket is hashed from. -/
def bucketMsg (b : BucketEntries) : ByteArray := encodeDetCbor (bucketCbor b)

/-- Every length in the bucket fits a 64-bit argument. -/
def bucketFits (b : BucketEntries) : Bool := WithinWidth (bucketCbor b)

def bucketHash (H : Hasher) (b : BucketEntries) : ByteArray := H.hash bucketTag (bucketMsg b)

theorem bucketCborItems_injective : ∀ {a b : BucketEntries},
    (a.map fun kv => CborVal.array [.bytes kv.1, .bytes kv.2]) =
      (b.map fun kv => CborVal.array [.bytes kv.1, .bytes kv.2]) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hxy, hrest⟩ := h
    have hx : x = y := by
      obtain ⟨k1, v1⟩ := x
      obtain ⟨k2, v2⟩ := y
      simp only [CborVal.array.injEq, List.cons.injEq, CborVal.bytes.injEq, and_true] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rfl
    rw [hx, bucketCborItems_injective hrest]

theorem bucketMsg_injective {b₁ b₂ : BucketEntries} (h₁ : bucketFits b₁ = true)
    (h₂ : bucketFits b₂ = true) (h : bucketMsg b₁ = bucketMsg b₂) : b₁ = b₂ := by
  have hc := encodeDetCbor_injective _ _ h₁ h₂ h
  simp only [bucketCbor, CborVal.array.injEq] at hc
  exact bucketCborItems_injective hc

def nodeHash (H : Hasher) (l r : ByteArray) : ByteArray := H.hash merkleTag (l ++ r)

/-- Hash adjacent pairs: one level up the tree. -/
def pairUp (H : Hasher) : List ByteArray → List ByteArray
  | a :: b :: rest => nodeHash H a b :: pairUp H rest
  | _ => []

theorem pairUp_length (H : Hasher) : ∀ (l : List ByteArray), (pairUp H l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [pairUp]
  | a :: b :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length H rest]
    omega

theorem pairUp_getD (H : Hasher) (d : ByteArray) : ∀ (l : List ByteArray) (i : Nat),
    2 * i + 1 < l.length →
    (pairUp H l).getD i d = nodeHash H (l.getD (2 * i) d) (l.getD (2 * i + 1) d)
  | [], i, h => by simp at h
  | [_], i, h => by simp at h
  | a :: b :: rest, 0, _ => rfl
  | a :: b :: rest, i + 1, h => by
    have ih := pairUp_getD H d rest i (by simp only [List.length_cons] at h; omega)
    have e1 : 2 * (i + 1) = (2 * i) + 1 + 1 := by omega
    rw [e1]
    simp only [pairUp, List.getD_cons_succ]
    exact ih

theorem pairUp_size (H : Hasher) : ∀ (l : List ByteArray), ∀ x ∈ pairUp H l, x.size = 32
  | [], x, hx => by cases hx
  | [_], x, hx => by cases hx
  | a :: b :: rest, x, hx => by
    simp only [pairUp, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact H.size_eq _ _
    · exact pairUp_size H rest x hx

theorem getD_of_lt {l : List ByteArray} {i : Nat} (h : i < l.length) (d : ByteArray) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The sibling of position `i`. -/
def sibIdx (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i - 1

/-- The Merkle root of `2^d` leaves. -/
def rootOf (H : Hasher) : Nat → List ByteArray → ByteArray
  | 0, l => l.getD 0 ByteArray.empty
  | d + 1, l => rootOf H d (pairUp H l)

/-- The sibling path of leaf `i`, leaf level first. -/
def pathOf (H : Hasher) : Nat → List ByteArray → Nat → List ByteArray
  | 0, _, _ => []
  | d + 1, l, i => l.getD (sibIdx i) ByteArray.empty :: pathOf H d (pairUp H l) (i / 2)

/-- Fold a leaf digest up a sibling path. -/
def climb (H : Hasher) (i : Nat) (cur : ByteArray) : List ByteArray → ByteArray
  | [] => cur
  | s :: rest =>
    climb H (i / 2) (if i % 2 = 0 then nodeHash H cur s else nodeHash H s cur) rest

theorem sibIdx_lt {i n : Nat} (hi : i < n * 2) : sibIdx i < n * 2 := by
  unfold sibIdx
  split <;> omega

/-- One level of the climb is one entry of the level above. -/
theorem climb_step (H : Hasher) (l : List ByteArray) (i : Nat) (hi : 2 * (i / 2) + 1 < l.length) :
    (if i % 2 = 0 then
        nodeHash H (l.getD i ByteArray.empty) (l.getD (sibIdx i) ByteArray.empty)
      else nodeHash H (l.getD (sibIdx i) ByteArray.empty) (l.getD i ByteArray.empty)) =
      (pairUp H l).getD (i / 2) ByteArray.empty := by
  rw [pairUp_getD H _ l (i / 2) hi]
  by_cases he : i % 2 = 0
  · have e1 : 2 * (i / 2) = i := by omega
    rw [ite_eq_left he, sibIdx, ite_eq_left he, e1]
  · have e1 : 2 * (i / 2) + 1 = i := by omega
    have e2 : 2 * (i / 2) = i - 1 := by omega
    rw [ite_eq_right he, sibIdx, ite_eq_right he, e1, e2]

theorem pathOf_length (H : Hasher) : ∀ (d : Nat) (l : List ByteArray) (i : Nat),
    (pathOf H d l i).length = d
  | 0, _, _ => rfl
  | d + 1, l, i => by simp [pathOf, pathOf_length H d]

/-- **The path opens to the root.** -/
theorem climb_pathOf (H : Hasher) : ∀ (d : Nat) (l : List ByteArray) (i : Nat),
    l.length = 2 ^ d → i < 2 ^ d →
    climb H i (l.getD i ByteArray.empty) (pathOf H d l i) = rootOf H d l
  | 0, l, i, _, hi => by
    have h0 : i = 0 := by simpa using hi
    subst h0
    rfl
  | d + 1, l, i, hl, hi => by
    rw [Nat.pow_succ] at hl hi
    have hlen : (pairUp H l).length = 2 ^ d := by rw [pairUp_length, hl]; omega
    have hstep := climb_step H l i (by omega)
    simp only [pathOf, climb, rootOf]
    rw [hstep]
    exact climb_pathOf H d _ (i / 2) hlen (by omega)

theorem pathOf_size (H : Hasher) : ∀ (d : Nat) (l : List ByteArray) (i : Nat),
    l.length = 2 ^ d → i < 2 ^ d → (∀ x ∈ l, x.size = 32) →
    ∀ s ∈ pathOf H d l i, s.size = 32
  | 0, _, _, _, _, _, s, hs => by cases hs
  | d + 1, l, i, hl, hi, hall, s, hs => by
    rw [Nat.pow_succ] at hl hi
    simp only [pathOf, List.mem_cons] at hs
    rcases hs with rfl | hs
    · have hsib : sibIdx i < l.length := by
        rw [hl]
        exact sibIdx_lt hi
      rw [getD_of_lt hsib]
      exact hall _ (List.getElem_mem hsib)
    · exact pathOf_size H d _ (i / 2) (by rw [pairUp_length, hl]; omega) (by omega)
        (pairUp_size H l) s hs

/-- A fork's evidence of its base: the base bucket it started from and that bucket's Merkle
path to the base root. -/
structure BaseProof where
  baseBucketBefore : BucketEntries
  siblings : List ByteArray
  deriving DecidableEq

/-- An open fork: the base root it forked from, the one bucket it touched, and that bucket now. -/
structure OpenFork where
  baseRoot32 : ByteArray
  touchedBucketIdx : Fin 16
  forkBucketAfter : BucketEntries
  deriving DecidableEq

/-- A base proof verifies against a root at an index: a depth-4 path of 32-byte siblings from
the hash of a bucket within width. -/
def verifyBaseProof (H : Hasher) (root : ByteArray) (idx : Fin 16) (p : BaseProof) : Bool :=
  p.siblings.length == 4 && p.siblings.all (fun s => s.size == 32) &&
    bucketFits p.baseBucketBefore &&
    decide (climb H idx.val (bucketHash H p.baseBucketBefore) p.siblings = root)

def leafDigests (H : Hasher) (base : Array BucketEntries) : List ByteArray :=
  base.toList.map (bucketHash H)

/-- The Merkle root of 16 buckets. -/
def merkleRoot16 (H : Hasher) (base : Array BucketEntries) : ByteArray :=
  rootOf H 4 (leafDigests H base)

/-- The honest proof, extracted when the fork is created. -/
def extractBaseProof (H : Hasher) (base : Array BucketEntries) (idx : Fin 16) : BaseProof :=
  ⟨base.getD idx.val [], pathOf H 4 (leafDigests H base) idx.val⟩

/-- **The honest base proof verifies.** -/
theorem verifyBaseProof_extractBaseProof (H : Hasher) (base : Array BucketEntries) (idx : Fin 16)
    (hsize : base.size = 16) (hfits : bucketFits (base.getD idx.val []) = true) :
    verifyBaseProof H (merkleRoot16 H base) idx (extractBaseProof H base idx) = true := by
  have hlen : (leafDigests H base).length = 2 ^ 4 := by simp [leafDigests, hsize]
  have hidx : idx.val < 2 ^ 4 := idx.isLt
  have hleaf : (leafDigests H base).getD idx.val ByteArray.empty =
      bucketHash H (base.getD idx.val []) := by
    have hi : idx.val < base.size := by omega
    have hi' : idx.val < (leafDigests H base).length := by rw [hlen]; exact hidx
    rw [getD_of_lt hi']
    simp [leafDigests, Array.getD, hi]
  have hall : ∀ x ∈ leafDigests H base, x.size = 32 := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
    exact H.size_eq _ _
  have hclimb := climb_pathOf H 4 (leafDigests H base) idx.val hlen hidx
  rw [hleaf] at hclimb
  have hsz := pathOf_size H 4 (leafDigests H base) idx.val hlen hidx hall
  simp only [verifyBaseProof, extractBaseProof, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  exact ⟨⟨⟨pathOf_length H 4 _ _, hsz⟩, hfits⟩, decide_eq_true hclimb⟩

def lookupKey (b : BucketEntries) (k : ByteArray) : Option ByteArray :=
  (b.find? (fun kv => decide (kv.1 = k))).map (·.2)

/-- The fork changed key `k` relative to the base (wrote, overwrote or deleted it). -/
def forkChanged (base fork : BucketEntries) (k : ByteArray) : Bool :=
  decide (lookupKey fork k ≠ lookupKey base k)

/-- **Three-way bucket merge**: a key the fork changed takes the fork's entry (or its absence);
every other key keeps the live entry. -/
def merge3Bucket (base live fork : BucketEntries) : BucketEntries :=
  fork.filter (fun kv => forkChanged base fork kv.1) ++
    live.filter (fun kv => !forkChanged base fork kv.1)

theorem find?_filter_key (c : ByteArray → Bool) (k : ByteArray) : ∀ (l : BucketEntries),
    (l.filter (fun kv => c kv.1)).find? (fun kv => decide (kv.1 = k)) =
      if c k = true then l.find? (fun kv => decide (kv.1 = k)) else none
  | [] => by simp
  | a :: l => by
    have ih := find?_filter_key c k l
    by_cases ha : a.1 = k
    · subst ha
      by_cases hc : c a.1 = true
      · simp [hc]
      · simp [hc, ih]
    · by_cases hca : c a.1 = true
      · simp [hca, ha, ih]
      · simp [hca, ha, ih]

/-- The merge's law per key. -/
theorem merge3Bucket_lookup (base live fork : BucketEntries) (k : ByteArray) :
    lookupKey (merge3Bucket base live fork) k =
      if forkChanged base fork k then lookupKey fork k else lookupKey live k := by
  unfold merge3Bucket lookupKey
  rw [List.find?_append, find?_filter_key (fun k => forkChanged base fork k) k fork,
    find?_filter_key (fun k => !forkChanged base fork k) k live]
  by_cases hc : forkChanged base fork k = true
  · simp [hc]
  · simp [hc]

/-- The vault with its history: live buckets, the base buckets open forks started from, and the
base roots of the forks still open. -/
structure ShardedVault where
  liveBuckets : Array BucketEntries
  baseBuckets : Array BucketEntries
  openForks : List ByteArray
  deriving DecidableEq

/-- The vault after forgetting: the base is only its root. -/
structure CompactedVault where
  liveBuckets : Array BucketEntries
  horizonBaseRoot32 : ByteArray
  openForks : List ByteArray
  deriving DecidableEq

/-- **Forget the historical base.** Total: open forks do not block it. -/
def forgetHistoricalBase (H : Hasher) (v : ShardedVault) : CompactedVault :=
  ⟨v.liveBuckets, merkleRoot16 H v.baseBuckets, v.openForks⟩

/-- Merge a fork with the base at hand. -/
def mergeWithFullBase (live : ShardedVault) (fullBase : Array BucketEntries) (fork : OpenFork) :
    ShardedVault :=
  { live with
    liveBuckets := live.liveBuckets.setIfInBounds fork.touchedBucketIdx.val
      (merge3Bucket (fullBase.getD fork.touchedBucketIdx.val [])
        (live.liveBuckets.getD fork.touchedBucketIdx.val []) fork.forkBucketAfter)
    openForks := live.openForks.erase fork.baseRoot32 }

/-- Merge a fork into a compacted vault: the fork must name the horizon root and open its base
bucket to it. -/
def mergeAfterForgetWithBaseProof (H : Hasher) (c : CompactedVault) (fork : OpenFork)
    (proof : BaseProof) : Option CompactedVault :=
  if decide (fork.baseRoot32 = c.horizonBaseRoot32) &&
      verifyBaseProof H c.horizonBaseRoot32 fork.touchedBucketIdx proof then
    some { c with
      liveBuckets := c.liveBuckets.setIfInBounds fork.touchedBucketIdx.val
        (merge3Bucket proof.baseBucketBefore
          (c.liveBuckets.getD fork.touchedBucketIdx.val []) fork.forkBucketAfter)
      openForks := c.openForks.erase fork.baseRoot32 }
  else none

/-- **Forget commutes with fork merge.** For a fork of the vault's base: its honest base proof
verifies, and merging it after forgetting the base is forgetting the base after merging it. -/
theorem forget_commutes_with_fork_merge (H : Hasher) (v : ShardedVault) (fork : OpenFork)
    (hsize : v.baseBuckets.size = 16)
    (hfits : bucketFits (v.baseBuckets.getD fork.touchedBucketIdx.val []) = true)
    (hroot : fork.baseRoot32 = merkleRoot16 H v.baseBuckets) :
    verifyBaseProof H (merkleRoot16 H v.baseBuckets) fork.touchedBucketIdx
        (extractBaseProof H v.baseBuckets fork.touchedBucketIdx) = true ∧
      mergeAfterForgetWithBaseProof H (forgetHistoricalBase H v) fork
          (extractBaseProof H v.baseBuckets fork.touchedBucketIdx) =
        some (forgetHistoricalBase H (mergeWithFullBase v v.baseBuckets fork)) := by
  have hv := verifyBaseProof_extractBaseProof H v.baseBuckets fork.touchedBucketIdx hsize hfits
  refine ⟨hv, ?_⟩
  unfold mergeAfterForgetWithBaseProof
  have hcond : (decide (fork.baseRoot32 = (forgetHistoricalBase H v).horizonBaseRoot32) &&
      verifyBaseProof H (forgetHistoricalBase H v).horizonBaseRoot32 fork.touchedBucketIdx
        (extractBaseProof H v.baseBuckets fork.touchedBucketIdx)) = true := by
    simp only [forgetHistoricalBase, Bool.and_eq_true]
    exact ⟨decide_eq_true hroot, hv⟩
  rw [ite_eq_left hcond]
  rfl

theorem byteArray_append_inj {a b c d : ByteArray} (h : a ++ b = c ++ d)
    (hs : a.size = c.size) : a = c ∧ b = d := by
  have hl : a.data.toList ++ b.data.toList = c.data.toList ++ d.data.toList := by
    have := congrArg (fun x => x.data.toList) h
    simpa [ByteArray.data_append] using this
  have hlen : a.data.toList.length = c.data.toList.length := by
    rw [toList_length, toList_length, hs]
  obtain ⟨h1, h2⟩ := List.append_inj hl hlen
  exact ⟨byteArray_eq_of_toList h1, byteArray_eq_of_toList h2⟩

/-- Two different 32-byte digests that climb to one value along sibling paths of one length
yield an explicit collision of the node hash. Computed, not chosen. -/
def climbCollision (H : Hasher) : (i : Nat) → (c₁ c₂ : ByteArray) → (s₁ s₂ : List ByteArray) →
    c₁.size = 32 → c₂.size = 32 → (∀ s ∈ s₁, s.size = 32) → (∀ s ∈ s₂, s.size = 32) →
    s₁.length = s₂.length → c₁ ≠ c₂ → climb H i c₁ s₁ = climb H i c₂ s₂ →
    HashCollision H merkleTag
  | _, _, _, [], [], _, _, _, _, _, hne, heq => absurd heq hne
  | _, _, _, [], _ :: _, _, _, _, _, hlen, _, _ => absurd hlen.symm (Nat.succ_ne_zero _)
  | _, _, _, _ :: _, [], _, _, _, _, hlen, _, _ => absurd hlen (Nat.succ_ne_zero _)
  | i, c₁, c₂, a :: r₁, b :: r₂, h₁, h₂, ha, hb, hlen, hne, heq =>
    if hpar : i % 2 = 0 then
      if hn : nodeHash H c₁ a = nodeHash H c₂ b then
        ⟨c₁ ++ a, c₂ ++ b,
          fun hm => hne (byteArray_append_inj hm (h₁.trans h₂.symm)).1, hn⟩
      else
        climbCollision H (i / 2) (nodeHash H c₁ a) (nodeHash H c₂ b) r₁ r₂
          (H.size_eq _ _) (H.size_eq _ _)
          (fun s hs => ha s (List.mem_cons_of_mem _ hs))
          (fun s hs => hb s (List.mem_cons_of_mem _ hs))
          (Nat.succ.inj hlen) hn
          (by simpa only [climb, ite_eq_left hpar] using heq)
    else
      if hn : nodeHash H a c₁ = nodeHash H b c₂ then
        ⟨a ++ c₁, b ++ c₂,
          fun hm => hne (byteArray_append_inj hm
            ((ha a List.mem_cons_self).trans (hb b List.mem_cons_self).symm)).2, hn⟩
      else
        climbCollision H (i / 2) (nodeHash H a c₁) (nodeHash H b c₂) r₁ r₂
          (H.size_eq _ _) (H.size_eq _ _)
          (fun s hs => ha s (List.mem_cons_of_mem _ hs))
          (fun s hs => hb s (List.mem_cons_of_mem _ hs))
          (Nat.succ.inj hlen) hn
          (by simpa only [climb, ite_eq_right hpar] using heq)

/-- A collision of the bucket hash or of the node hash. -/
inductive MerkleCollision (H : Hasher) where
  | leaf (c : HashCollision H bucketTag)
  | node (c : HashCollision H merkleTag)

theorem verifyBaseProof_parts {H : Hasher} {root : ByteArray} {idx : Fin 16} {p : BaseProof}
    (h : verifyBaseProof H root idx p = true) :
    p.siblings.length = 4 ∧ (∀ s ∈ p.siblings, s.size = 32) ∧
      bucketFits p.baseBucketBefore = true ∧
      climb H idx.val (bucketHash H p.baseBucketBefore) p.siblings = root := by
  simp only [verifyBaseProof, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **Collision extraction.** From two base proofs of different buckets that both verify at
one index under one root, compute an explicit collision. -/
def baseProofCollision (H : Hasher) {root : ByteArray} {idx : Fin 16} {p₁ p₂ : BaseProof}
    (h₁ : verifyBaseProof H root idx p₁ = true) (h₂ : verifyBaseProof H root idx p₂ = true)
    (hne : p₁.baseBucketBefore ≠ p₂.baseBucketBefore) : MerkleCollision H :=
  if hl : bucketHash H p₁.baseBucketBefore = bucketHash H p₂.baseBucketBefore then
    .leaf ⟨bucketMsg p₁.baseBucketBefore, bucketMsg p₂.baseBucketBefore,
      fun hm => hne (bucketMsg_injective (verifyBaseProof_parts h₁).2.2.1
        (verifyBaseProof_parts h₂).2.2.1 hm), hl⟩
  else
    .node (climbCollision H idx.val (bucketHash H p₁.baseBucketBefore)
      (bucketHash H p₂.baseBucketBefore) p₁.siblings p₂.siblings
      (H.size_eq _ _) (H.size_eq _ _) (verifyBaseProof_parts h₁).2.1
      (verifyBaseProof_parts h₂).2.1
      ((verifyBaseProof_parts h₁).1.trans (verifyBaseProof_parts h₂).1.symm) hl
      ((verifyBaseProof_parts h₁).2.2.2.trans (verifyBaseProof_parts h₂).2.2.2.symm))

/-- **Base proofs bind.** A fork cannot open a different base bucket at its index under the
same root without exhibiting two different messages with one digest, at the bucket tag or at
the node tag. -/
theorem baseProof_binding_collision (H : Hasher) {root : ByteArray} {idx : Fin 16}
    {fake honest : BaseProof} (hf : verifyBaseProof H root idx fake = true)
    (ht : verifyBaseProof H root idx honest = true)
    (hne : fake.baseBucketBefore ≠ honest.baseBucketBefore) :
    ∃ (tag : String) (m₁ m₂ : ByteArray), (tag = bucketTag ∨ tag = merkleTag) ∧ m₁ ≠ m₂ ∧
      H.hash tag m₁ = H.hash tag m₂ :=
  match baseProofCollision H hf ht hne with
  | .leaf c => ⟨bucketTag, c.m₁, c.m₂, Or.inl rfl, c.ne, c.eq⟩
  | .node c => ⟨merkleTag, c.m₁, c.m₂, Or.inr rfl, c.ne, c.eq⟩

/-- The binding theorem at cSHAKE256. -/
theorem cshake_baseProof_binding {root : ByteArray} {idx : Fin 16} {fake honest : BaseProof}
    (hf : verifyBaseProof cshakeHasher root idx fake = true)
    (ht : verifyBaseProof cshakeHasher root idx honest = true)
    (hne : fake.baseBucketBefore ≠ honest.baseBucketBefore) :
    ∃ (tag : String) (m₁ m₂ : ByteArray), (tag = bucketTag ∨ tag = merkleTag) ∧ m₁ ≠ m₂ ∧
      cshakeHasher.hash tag m₁ = cshakeHasher.hash tag m₂ :=
  baseProof_binding_collision cshakeHasher hf ht hne

end Obend.Vault.Lsafe

end
