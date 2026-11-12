module
/-
# Obend.Vault.Lsafe — redaction confinement, open-world completeness tokens, forget while forked

Cards `K9` and `K10`. Three parts.

**§1 Redaction confinement (`K9a`).** `stepLex2Bit` is the two-bit string/escape lexer.
`stepLsafe` composes it with a bracket-stack skeleton machine that tracks, per open object, key
versus value position and the keys seen, refuses a backslash inside a key (so two keys equal as
bytes are equal as JSON strings), and checks at every `}` that the object's keys are pairwise
distinct by a merge sort and one adjacent pass. `runLsafeVpa` accepts a document whose run ends
outside any string with an empty stack and no refusal. `checkLsafeRedaction doc l r replacement`
accepts a span that starts strictly inside a value string and whose old and new bytes are all
`isSafeRedactionByte` (printable ASCII without `"`, `\`, `<`, `>`).

`safeSpan_preserves_lexAndVpa`: a safe byte inside a value string leaves the whole machine state
unchanged. `lsafe_redaction_confinement`: after an accepted redaction the spliced document is
accepted, its machine state is the original state at `l` all through the replacement and the
original state at `r + j` at every `j` after it, its final state is the original final state
(so the object key sets are the same), and the replacement carries none of the six bytes.
`lsafe_object_keys_nodup`: every object the machine closed has pairwise distinct keys.

**§2 Open-world completeness (`K9b`).** `evalOpenWorldKgQuery` answers `entailed` only for an
edge found in an authenticated witness, `refuted` only under a `CompletenessToken` that verifies
for exactly this graph, predicate and subject and commits to the witness, and `undetermined`
otherwise. `openWorld_without_token_never_refutes`, `openWorld_invalid_token_never_refutes`,
`completenessToken_refute_sound`, `openWorld_entailed_sound`, and
`completenessToken_refute_binding` (against the issuer's own slice: absent there, or the two
slices are a collision of the scoped-edges commitment).

**§3 Forget while forked (`K10`).** A vault of 16 buckets under a depth-4 Merkle tree.
`forgetHistoricalBase` keeps only the base root and is total: an open fork does not block it.
A fork merges into the compacted vault by presenting a `BaseProof` (its base bucket and a
Merkle path). `forget_commutes_with_fork_merge`: the honest proof verifies and merging after
forgetting is forgetting after merging, as an equation. `baseProofCollision` computes, from two
verifying proofs of different base buckets at one index under one root, an explicit collision
of the bucket hash or of the node hash; `baseProof_binding_collision` states it.
`merge3Bucket_lookup` is the three-way merge's law per key.

The hash is a parameter (`Hasher`: a tagged hash with 32-byte output); `cshakeHasher` is
cSHAKE256 with the tag as customization, and `cshake_baseProof_binding` is the binding theorem
at it. Canonical bytes for hashing are `Obend.Codec.DetCbor`.

What is not here: the skeleton machine is not a JSON validator (it does not check scalars,
separators between values, or that a key is followed by a colon before the object closes);
`keysDistinctB` is proved sound, not complete; a positive query presents the whole edge set or a
tokened slice, with no Merkle inclusion path for a single edge; the token's tag is a keyed hash
under a shared secret, not a signature; buckets are fixed at 16.
-/

public import Obend.Codec.DetCbor
public import Obend.Digest.Cshake256

public section

namespace Obend.Vault.Lsafe

open Obend.Codec.DetCbor

set_option autoImplicit false

/-! ## 1. The two-bit lexer, the skeleton machine, and redaction confinement -/

/-- The lexer state: inside a string literal, and whether the previous byte was an unconsumed
backslash. -/
structure LexState2Bit where
  inString : Bool
  escaped : Bool
  deriving DecidableEq, Repr

/-- One byte of the string/escape lexer. An escaped byte is consumed: it neither closes the
string nor starts an escape. -/
def stepLex2Bit (st : LexState2Bit) (b : UInt8) : LexState2Bit :=
  if st.inString then
    if st.escaped then ⟨true, false⟩
    else if b == 0x5c then ⟨true, true⟩
    else if b == 0x22 then ⟨false, false⟩
    else ⟨true, false⟩
  else if b == 0x22 then ⟨true, false⟩
  else ⟨false, false⟩

/-- A stable merge at a fuel; out of fuel it concatenates, which is still a permutation. -/
def mergeFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeFuel le f xs (y :: ys) else y :: mergeFuel le f (x :: xs) ys

theorem mergeFuel_perm {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (xs ys : List α), (mergeFuel le f xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: xs, [] => by simp [mergeFuel]
  | f + 1, x :: xs, y :: ys => by
    simp only [mergeFuel]
    split
    · exact (mergeFuel_perm le f xs (y :: ys)).cons x
    · exact ((mergeFuel_perm le f (x :: xs) ys).cons y).trans List.perm_middle.symm

/-- Merge adjacent runs. -/
def mergePass {α : Type} (le : α → α → Bool) : List (List α) → List (List α)
  | a :: b :: rest => mergeFuel le (a.length + b.length) a b :: mergePass le rest
  | l => l

theorem mergePass_perm {α : Type} (le : α → α → Bool) :
    ∀ (runs : List (List α)), (mergePass le runs).flatten.Perm runs.flatten
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: rest => by
    simp only [mergePass, List.flatten_cons]
    rw [← List.append_assoc]
    exact (mergeFuel_perm le _ a b).append (mergePass_perm le rest)

/-- Halve the runs until one is left. -/
def mergeLoop {α : Type} (le : α → α → Bool) : Nat → List (List α) → List α
  | 0, runs => runs.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | f + 1, a :: b :: rest => mergeLoop le f (mergePass le (a :: b :: rest))

theorem mergeLoop_perm {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (runs : List (List α)), (mergeLoop le f runs).Perm runs.flatten
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [a] => by simp [mergeLoop]
  | f + 1, a :: b :: rest => by
    simp only [mergeLoop]
    exact (mergeLoop_perm le f _).trans (mergePass_perm le _)

/-- **Bottom-up merge sort**, `O(n log n)` comparisons, structural (it reduces in the kernel). -/
def sortBy {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  mergeLoop le (l.length + 1) (l.map fun x => [x])

theorem flatten_singletons {α : Type} : ∀ (l : List α), (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: xs => by simp [flatten_singletons xs]

theorem sortBy_perm {α : Type} (le : α → α → Bool) (l : List α) : (sortBy le l).Perm l := by
  have h := mergeLoop_perm le (l.length + 1) (l.map fun x => [x])
  rw [flatten_singletons] at h
  exact h

/-- **Pairwise-distinct keys**: sort, then one pass checking each adjacent pair strictly
ascending. No quadratic scan. -/
def keysDistinctB (ks : List ByteArray) : Bool :=
  sortedByKeyB id (sortBy (fun a b => !lexLtBytes b a) ks)

theorem keysDistinctB_sound {ks : List ByteArray} (h : keysDistinctB ks = true) : ks.Nodup := by
  have hs := sortedByKeyB_sound id _ h
  have hn : (sortBy (fun a b => !lexLtBytes b a) ks).Nodup := by
    refine hs.imp ?_
    intro a b hab heq
    rw [heq] at hab
    simp only [id] at hab
    rw [lexLtBytes_irrefl] at hab
    cases hab
  exact (sortBy_perm _ ks).nodup_iff.1 hn

/-- An open bracket: an object or an array; for an object, whether the cursor is in value
position (after its `:`), and the keys read so far. -/
structure Frame where
  isObj : Bool
  inValue : Bool
  keys : List ByteArray
  deriving DecidableEq

/-- The machine state: lexer, bracket stack, the key being read, the key sets of the objects
already closed, and whether nothing has been refused. -/
structure LsafeState where
  lex : LexState2Bit
  stack : List Frame
  curKey : ByteArray
  closed : List (List ByteArray)
  ok : Bool
  deriving DecidableEq

def LsafeState.init : LsafeState := ⟨⟨false, false⟩, [], ByteArray.empty, [], true⟩

/-- The innermost open bracket is an object in key position. -/
def atKey (stack : List Frame) : Bool :=
  match stack with
  | f :: _ => f.isObj && !f.inValue
  | [] => false

def pushKey (k : ByteArray) : List Frame → List Frame
  | f :: rest => { f with keys := k :: f.keys } :: rest
  | [] => []

/-- Close an object: its keys must be pairwise distinct. -/
def closeObj : List Frame → Option (List Frame × List ByteArray)
  | f :: rest => if f.isObj && keysDistinctB f.keys then some (rest, f.keys) else none
  | [] => none

/-- Every structural byte except `}`; other bytes leave the stack alone. -/
def structuralOther (b : UInt8) (stack : List Frame) : Option (List Frame) :=
  if b == 0x7b then some (⟨true, false, []⟩ :: stack)
  else if b == 0x5b then some (⟨false, true, []⟩ :: stack)
  else if b == 0x5d then
    match stack with
    | f :: rest => if f.isObj then none else some rest
    | [] => none
  else if b == 0x3a then
    match stack with
    | f :: rest => if f.isObj && !f.inValue then some ({ f with inValue := true } :: rest) else none
    | [] => none
  else if b == 0x2c then
    match stack with
    | f :: rest =>
      if f.isObj then (if f.inValue then some ({ f with inValue := false } :: rest) else none)
      else some (f :: rest)
    | [] => none
  else some stack

/-- **One byte of the composed machine.** Structural bytes act only outside strings. Inside a
key string the byte is collected (a backslash is refused); inside a value string nothing but the
lexer moves. -/
def stepLsafe (st : LsafeState) (b : UInt8) : LsafeState :=
  if st.lex.inString then
    if atKey st.stack then
      if (stepLex2Bit st.lex b).inString then
        { st with lex := stepLex2Bit st.lex b, curKey := st.curKey.push b,
                  ok := st.ok && b != 0x5c }
      else
        { st with lex := stepLex2Bit st.lex b, stack := pushKey st.curKey st.stack,
                  curKey := ByteArray.empty }
    else { st with lex := stepLex2Bit st.lex b }
  else if b == 0x7d then
    match closeObj st.stack with
    | some (stack', ks) =>
      { st with lex := stepLex2Bit st.lex b, stack := stack', closed := ks :: st.closed }
    | none => { st with lex := stepLex2Bit st.lex b, ok := false }
  else
    match structuralOther b st.stack with
    | some stack' => { st with lex := stepLex2Bit st.lex b, stack := stack' }
    | none => { st with lex := stepLex2Bit st.lex b, ok := false }

/-- The reasoning-tier run: fold the machine over a byte list. -/
def specRun (bs : List UInt8) (st : LsafeState) : LsafeState := bs.foldl stepLsafe st

/-- The execution-tier run over the span `[i, e)` of a buffer, by cursor. -/
def runSpan (doc : ByteArray) : Nat → Nat → Nat → LsafeState → LsafeState
  | 0, _, _, st => st
  | fuel + 1, i, e, st =>
    if i < e then runSpan doc fuel (i + 1) e (stepLsafe st (byteAt doc i)) else st

theorem runSpan_eq (doc : ByteArray) : ∀ (fuel i e : Nat) (st : LsafeState),
    e ≤ doc.size → e - i ≤ fuel →
    runSpan doc fuel i e st = specRun ((doc.data.toList.drop i).take (e - i)) st
  | 0, i, e, st, _, hf => by
    have hi : ¬ i < e := by omega
    rw [slice_nil doc i e hi]
    rfl
  | fuel + 1, i, e, st, he, hf => by
    unfold runSpan
    by_cases hi : i < e
    · rw [ite_eq_left hi, slice_cons doc i e hi he]
      exact runSpan_eq doc fuel (i + 1) e _ he (by omega)
    · rw [ite_eq_right hi, slice_nil doc i e hi]
      rfl

/-- The machine state after the first `i` bytes of a document. -/
def stateAt (doc : ByteArray) (i : Nat) : LsafeState :=
  runSpan doc (min i doc.size) 0 (min i doc.size) LsafeState.init

theorem stateAt_eq (doc : ByteArray) (i : Nat) :
    stateAt doc i = specRun (doc.data.toList.take i) LsafeState.init := by
  unfold stateAt
  rw [runSpan_eq doc _ 0 _ _ (Nat.min_le_right _ _) (by omega)]
  simp only [List.drop_zero, Nat.sub_zero]
  by_cases h : i ≤ doc.size
  · rw [Nat.min_eq_left h]
  · have h1 : doc.data.toList.length ≤ i := by rw [toList_length]; omega
    rw [Nat.min_eq_right (by omega), List.take_of_length_le h1,
      List.take_of_length_le (Nat.le_of_eq (toList_length doc))]

/-- The machine state after the whole document. -/
def lsafeRun (doc : ByteArray) : LsafeState := stateAt doc doc.size

theorem lsafeRun_eq (doc : ByteArray) : lsafeRun doc = specRun doc.data.toList LsafeState.init := by
  rw [lsafeRun, stateAt_eq, List.take_of_length_le (Nat.le_of_eq (toList_length doc))]

/-- A final state is accepting: nothing refused, every bracket closed, outside any string. -/
def accepting (st : LsafeState) : Bool :=
  st.ok && st.stack.isEmpty && !st.lex.inString && !st.lex.escaped

/-- **The document skeleton check**: balanced brackets, strings closed, no duplicate key in any
object, no backslash in a key. -/
def runLsafeVpa (doc : ByteArray) : Bool := accepting (lsafeRun doc)

/-- The key sets of the objects of a document, innermost-closed first. -/
def objectKeysOf (doc : ByteArray) : List (List ByteArray) := (lsafeRun doc).closed

/-- **A byte a redaction may remove or write**: printable ASCII, and none of `"` (closes the
string), `\` (byte 92: eats the closing quote), `<` and `>` (tag breakout). Carriage return
and line feed are below `0x20` and are refused by the range. -/
def isSafeRedactionByte (b : UInt8) : Bool :=
  decide (0x20 ≤ b.toNat) && decide (b.toNat ≤ 0x7e) && b != 0x22 && b != 0x5c && b != 0x0d &&
    b != 0x0a && b != 0x3e && b != 0x3c

theorem isSafeRedactionByte_spec {b : UInt8} (h : isSafeRedactionByte b = true) :
    b ≠ 0x22 ∧ b ≠ 0x5c ∧ b ≠ 0x0d ∧ b ≠ 0x0a ∧ b ≠ 0x3c ∧ b ≠ 0x3e := by
  simp only [isSafeRedactionByte, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.2, h.1.2⟩

/-- Every byte of the span `[i, e)` is safe. -/
def allSafeSpan (doc : ByteArray) : Nat → Nat → Nat → Bool
  | 0, i, e => decide (e ≤ i)
  | fuel + 1, i, e =>
    if i < e then isSafeRedactionByte (byteAt doc i) && allSafeSpan doc fuel (i + 1) e else true

theorem allSafeSpan_eq (doc : ByteArray) : ∀ (fuel i e : Nat), e ≤ doc.size → e - i ≤ fuel →
    allSafeSpan doc fuel i e =
      ((doc.data.toList.drop i).take (e - i)).all isSafeRedactionByte
  | 0, i, e, _, hf => by
    have hi : ¬ i < e := by omega
    rw [slice_nil doc i e hi]
    simp [allSafeSpan]
    omega
  | fuel + 1, i, e, he, hf => by
    unfold allSafeSpan
    by_cases hi : i < e
    · rw [ite_eq_left hi, slice_cons doc i e hi he, List.all_cons,
        allSafeSpan_eq doc fuel (i + 1) e he (by omega)]
    · rw [ite_eq_right hi, slice_nil doc i e hi]
      rfl

/-- Strictly inside a value string: in a string, not after a backslash, not in key position. -/
def InValueString (st : LsafeState) : Prop :=
  st.lex = ⟨true, false⟩ ∧ atKey st.stack = false

def inValueStringB (st : LsafeState) : Bool :=
  st.lex.inString && !st.lex.escaped && !atKey st.stack

theorem inValueString_of_B {st : LsafeState} (h : inValueStringB st = true) : InValueString st := by
  obtain ⟨⟨s, e⟩, stack, curKey, closed, ok⟩ := st
  simp only [inValueStringB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hs, he⟩, hk⟩ := h
  subst hs
  subst he
  exact ⟨rfl, hk⟩

/-- **The redaction check.** The span `[l, r)` lies in the document, the document passes the
skeleton check, the span starts strictly inside a value string, and every byte removed and every
byte written is safe. Linear in the document and the replacement. -/
def checkLsafeRedaction (doc : ByteArray) (l r : Nat) (replacement : ByteArray) : Bool :=
  decide (l ≤ r) && decide (r ≤ doc.size) && runLsafeVpa doc && inValueStringB (stateAt doc l) &&
    allSafeSpan doc (r - l) l r && allSafeSpan replacement replacement.size 0 replacement.size

/-- Replace the span `[l, r)` of a document. -/
def spliceByteArray (doc : ByteArray) (l r : Nat) (replacement : ByteArray) : ByteArray :=
  doc.extract 0 l ++ replacement ++ doc.extract r doc.size

theorem extract_toList (doc : ByteArray) (s e : Nat) :
    (doc.extract s e).data.toList = (doc.data.toList.drop s).take (e - s) := by
  rw [ByteArray.data_extract, Array.toList_extract]

theorem spliceByteArray_toList (doc : ByteArray) (l r : Nat) (replacement : ByteArray) :
    (spliceByteArray doc l r replacement).data.toList =
      doc.data.toList.take l ++ replacement.data.toList ++ doc.data.toList.drop r := by
  unfold spliceByteArray
  rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append,
    extract_toList, extract_toList]
  simp only [List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (l := doc.data.toList.drop r)
    (Nat.le_of_eq (by rw [List.length_drop, toList_length]))]

theorem stepLex2Bit_safe {b : UInt8} (h : isSafeRedactionByte b = true) :
    stepLex2Bit ⟨true, false⟩ b = ⟨true, false⟩ := by
  obtain ⟨h22, h5c, _⟩ := isSafeRedactionByte_spec h
  have e1 : (b == 0x5c) = false := by simpa using h5c
  have e2 : (b == 0x22) = false := by simpa using h22
  simp [stepLex2Bit, e1, e2]

/-- **The key invariant.** A safe byte read strictly inside a value string changes nothing:
not the lexer, not the stack, not the collected keys. -/
theorem safeSpan_preserves_lexAndVpa_step {st : LsafeState} {b : UInt8} (hv : InValueString st)
    (h : isSafeRedactionByte b = true) : stepLsafe st b = st := by
  obtain ⟨lex, stack, curKey, closed, ok⟩ := st
  obtain ⟨hlex, hk⟩ := hv
  simp only at hlex hk
  subst hlex
  simp [stepLsafe, hk, stepLex2Bit_safe h]

/-- The same over any run of safe bytes: the state is identically the starting state. -/
theorem safeSpan_preserves_lexAndVpa {st : LsafeState} (hv : InValueString st) :
    ∀ (bs : List UInt8), bs.all isSafeRedactionByte = true → specRun bs st = st
  | [], _ => rfl
  | b :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [specRun, List.foldl_cons]
    rw [safeSpan_preserves_lexAndVpa_step hv h.1]
    exact safeSpan_preserves_lexAndVpa hv bs h.2

theorem specRun_append (xs ys : List UInt8) (st : LsafeState) :
    specRun (xs ++ ys) st = specRun ys (specRun xs st) := by
  simp [specRun, List.foldl_append]

theorem checkLsafeRedaction_parts {doc replacement : ByteArray} {l r : Nat}
    (h : checkLsafeRedaction doc l r replacement = true) :
    l ≤ r ∧ r ≤ doc.size ∧ runLsafeVpa doc = true ∧ InValueString (stateAt doc l) ∧
      ((doc.data.toList.drop l).take (r - l)).all isSafeRedactionByte = true ∧
      replacement.data.toList.all isSafeRedactionByte = true := by
  simp only [checkLsafeRedaction, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlr, hr⟩, hrun⟩, hin⟩, hold⟩, hnew⟩ := h
  refine ⟨hlr, hr, hrun, inValueString_of_B hin, ?_, ?_⟩
  · rw [← allSafeSpan_eq doc (r - l) l r hr (Nat.le_refl _)]
    exact hold
  · rw [allSafeSpan_eq replacement _ 0 _ (Nat.le_refl _) (by omega)] at hnew
    simp only [List.drop_zero, Nat.sub_zero] at hnew
    rw [List.take_of_length_le (Nat.le_of_eq (toList_length replacement))] at hnew
    exact hnew

/-- **Redaction confinement.** After an accepted redaction:
1. the spliced document passes the skeleton check;
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
  obtain ⟨hlr, hr, hrun, hin, hold, hnew⟩ := checkLsafeRedaction_parts h
  have hL := toList_length doc
  have hR := toList_length replacement
  have hS := spliceByteArray_toList doc l r replacement
  have hlenl : (doc.data.toList.take l).length = l := by rw [List.length_take, hL]; omega
  have hSl : stateAt doc l = specRun (doc.data.toList.take l) LsafeState.init := stateAt_eq doc l
  rw [hSl] at hin
  -- the original state at `r + j`
  have hdoc : ∀ j, stateAt doc (r + j) =
      specRun ((doc.data.toList.drop r).take j)
        (specRun (doc.data.toList.take l) LsafeState.init) := by
    intro j
    have hsplit : doc.data.toList.take (r + j) =
        doc.data.toList.take l ++ ((doc.data.toList.drop l).take (r - l) ++
          (doc.data.toList.drop r).take j) := by
      have e1 : r + j = l + ((r - l) + j) := by omega
      rw [e1, List.take_add, List.take_add, List.drop_drop]
      have e2 : l + (r - l) = r := by omega
      rw [e2]
    rw [stateAt_eq, hsplit, specRun_append, specRun_append,
      safeSpan_preserves_lexAndVpa hin _ hold]
  -- the spliced state inside the replacement
  have hmid : ∀ j, j ≤ replacement.size →
      stateAt (spliceByteArray doc l r replacement) (l + j) =
        specRun (doc.data.toList.take l) LsafeState.init := by
    intro j hj
    have hsplit : (spliceByteArray doc l r replacement).data.toList.take (l + j) =
        doc.data.toList.take l ++ replacement.data.toList.take j := by
      rw [hS, List.append_assoc, List.take_add, List.take_left' hlenl, List.drop_left' hlenl,
        List.take_append_of_le_length (by rw [hR]; exact hj)]
    have hsafe : (replacement.data.toList.take j).all isSafeRedactionByte = true := by
      rw [List.all_eq_true] at hnew ⊢
      exact fun x hx => hnew x (List.mem_of_mem_take hx)
    rw [stateAt_eq, hsplit, specRun_append, safeSpan_preserves_lexAndVpa hin _ hsafe]
  -- the spliced state after the replacement
  have hsuf : ∀ j, stateAt (spliceByteArray doc l r replacement) (l + replacement.size + j) =
      stateAt doc (r + j) := by
    intro j
    have hlen2 : (doc.data.toList.take l ++ replacement.data.toList).length =
        l + replacement.size := by rw [List.length_append, hlenl, hR]
    have hsplit : (spliceByteArray doc l r replacement).data.toList.take
        (l + replacement.size + j) =
        doc.data.toList.take l ++ (replacement.data.toList ++
          (doc.data.toList.drop r).take j) := by
      rw [hS, List.take_add, List.take_left' hlen2, List.drop_left' hlen2, List.append_assoc]
    rw [stateAt_eq, hsplit, specRun_append, specRun_append,
      safeSpan_preserves_lexAndVpa hin _ hnew, hdoc j]
  have hfinal : lsafeRun (spliceByteArray doc l r replacement) = lsafeRun doc := by
    have hsz : (spliceByteArray doc l r replacement).size =
        l + replacement.size + (doc.size - r) := by
      rw [← toList_length, hS, List.length_append, List.length_append, hlenl, hR,
        List.length_drop, hL]
    have hd : doc.size = r + (doc.size - r) := by omega
    unfold lsafeRun
    rw [hsz, hsuf (doc.size - r), ← hd]
  refine ⟨?_, hsuf, ?_, ?_, ?_, hfinal⟩
  · unfold runLsafeVpa
    rw [hfinal]
    exact hrun
  · intro j hj
    rw [hmid j hj, hSl]
  · intro x hx
    exact isSafeRedactionByte_spec (List.all_eq_true.1 hnew x hx)
  · unfold objectKeysOf
    rw [hfinal]

theorem closeObj_distinct {stack stack' : List Frame} {ks : List ByteArray}
    (h : closeObj stack = some (stack', ks)) : keysDistinctB ks = true := by
  cases stack with
  | nil => cases h
  | cons f rest =>
    simp only [closeObj] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      simp only [Bool.and_eq_true] at hc
      exact hc.2
    · cases h

theorem stepLsafe_closed_nodup (st : LsafeState) (b : UInt8)
    (hinv : ∀ ks ∈ st.closed, ks.Nodup) : ∀ ks ∈ (stepLsafe st b).closed, ks.Nodup := by
  unfold stepLsafe
  split
  · split
    · split <;> exact hinv
    · exact hinv
  · split
    · split
      · rename_i stack' ks hc
        intro ks' hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact keysDistinctB_sound (closeObj_distinct hc)
        · exact hinv _ hk
      · exact hinv
    · split <;> exact hinv

theorem specRun_closed_nodup : ∀ (bs : List UInt8) (st : LsafeState),
    (∀ ks ∈ st.closed, ks.Nodup) → ∀ ks ∈ (specRun bs st).closed, ks.Nodup
  | [], _, h => h
  | b :: bs, st, h => specRun_closed_nodup bs _ (stepLsafe_closed_nodup st b h)

/-- **No duplicate key.** Every object the machine closed has pairwise distinct keys. -/
theorem lsafe_object_keys_nodup (doc : ByteArray) : ∀ ks ∈ objectKeysOf doc, ks.Nodup := by
  unfold objectKeysOf
  rw [lsafeRun_eq]
  exact specRun_closed_nodup _ _ (fun _ hk => by cases hk)

/-! ## 2. Open-world queries and completeness tokens -/

/-- A tagged hash with 32-byte output. -/
structure Hasher where
  hash : String → ByteArray → ByteArray
  size_eq : ∀ (tag : String) (m : ByteArray), (hash tag m).size = 32

/-- cSHAKE256 with the tag as customization string. -/
def cshakeHasher : Hasher where
  hash tag m :=
    ⟨(Obend.Digest.Cshake256.cshake256Bytes tag.toUTF8.data.toList m.data.toList).toArray⟩
  size_eq tag m := by simp [ByteArray.size]

/-- An explicit collision of a hasher at a tag: two different messages, one digest. -/
structure HashCollision (H : Hasher) (tag : String) where
  m₁ : ByteArray
  m₂ : ByteArray
  ne : m₁ ≠ m₂
  eq : H.hash tag m₁ = H.hash tag m₂

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

/-- The commitment to an edge array: the tagged hash of its deterministic encoding. -/
def edgesDigest (H : Hasher) (es : Array KgEdge) : ByteArray :=
  H.hash graphTag (encodeDetCbor (edgesCbor es))

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

/-- Two different edge arrays with one commitment, both within width, are an explicit
collision of the hash itself. -/
def edgesCollision (H : Hasher) {e₁ e₂ : Array KgEdge} (hne : e₁ ≠ e₂)
    (h₁ : WithinWidth (edgesCbor e₁) = true) (h₂ : WithinWidth (edgesCbor e₂) = true)
    (heq : edgesDigest H e₁ = edgesDigest H e₂) : HashCollision H graphTag where
  m₁ := encodeDetCbor (edgesCbor e₁)
  m₂ := encodeDetCbor (edgesCbor e₂)
  ne := by
    intro hm
    have hc := encodeDetCbor_injective _ _ h₁ h₂ hm
    simp only [edgesCbor, CborVal.array.injEq] at hc
    exact hne (Array.toList_inj.1 (toCbor_injective hc))
  eq := heq

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
