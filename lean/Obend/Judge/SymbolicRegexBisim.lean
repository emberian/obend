module
/-
# Obend.Judge.SymbolicRegexBisim — committed derivative-bisimulation certificates for regular policies

A policy over a byte stream is a Boolean-closed regular expression `PredRE`: byte-interval atoms
`range lo hi`, concatenation, union, intersection, complement and iteration. `absenceOf bad` is the
policy "no factor of the stream matches `bad`", the shape of a delimiter ban.

**Semantics.** `Matches w r` is the denotational word semantics, by recursion on the expression
(complement is `¬`, so it is not an inductive predicate). `null` and `der` are Brzozowski's
nullability and derivative; `null_iff_matches_nil` and `der_iff_matches_cons` are their two laws, and
`matchB` is the matcher they give (`matchB_iff`), which makes `Matches` decidable.

**Normal forms.** `nrm` rebuilds an expression through smart constructors: unions are flattened,
deduplicated and absorbed by the full language; `ff` and `eps` are units and zeros of
concatenation; double complement cancels. `nrm_matches` says it keeps the language; `simDecide`
compares normal forms and `simDecide_sound` is its soundness. Nothing else about `nrm` is used, so
no syntactic similarity relation is carried through the proofs.

**Minterms.** A derivative reads a byte only through the interval atoms of the expression.
`classesOf ps` lists one representative per cell of the partition those intervals cut `UInt8`
into: byte `0`, every interval's lower end, and every upper end's successor. `classesOf_covers`:
every byte agrees with some representative on every atom. `der_factors_over_minterm`: two bytes that
agree on the atoms of `r` have the same derivative of `r`, as an equation of expressions.

**Certificates.** A certificate for `L(r) ⊆ L(s)` is a list of pairs. `bisimCheck` asks that the
normal form of `(r, s)` is in the list, that `null p → null q` at every pair, and that the
normalized derivative pair of every pair by every class representative is in the list again.
`bisimCheck_sound` and `bisimEqCheck_sound` (mutual inclusion) are by induction on the word.
`absenceOf_sound`: a certificate into `absenceOf bad` shows no word of `L(r)` has a factor in
`L(bad)`.

**Commitments.** `encRE` is a prefix code of the syntax tree with the left inverse `decRE`
(`decRE_encRE`, `encRE_injective`). `commitRE` is cSHAKE256 of it. `verifyCommittedBisim` checks both
openings and the certificate; `committedBisimExtract` computes, for the policies `P`, `Q` intended at
the two roots, either the inclusion `L(P) ⊆ L(Q)` or two different messages with one digest
(`verifyCommittedBisim_sound_or_collision` at cSHAKE256).

**Search and the judge.** `emitBisimPairs` is a fuel-bounded worklist over normalized derivative
pairs; it is not trusted. `symbolicRegexInclusionJudge` means language inclusion. It accepts a
certificate `bisimCheck` accepts; otherwise it searches by iterative deepening for a word of
`L(lhs)` outside `L(rhs)` and refuses with that word as the path (`cexAt_sound`), which refutes the
inclusion for every certificate. Its fragment is the queries whose exploration closes within some
fuel; there the emitted list is accepted whenever the inclusion holds (`emit_accepted_of_incl`).

Not here: a bound on the fuel at which exploration closes (the finiteness of derivatives up to the
similarity `nrm` decides is not proved, so the fragment is stated by the exploration itself); the
pair table is a list scanned linearly, not a hashed table.
-/
public import Obend.Judge.Class
public import Obend.Codec.DetCbor
public import Obend.Digest.Cshake256
import all Obend.Codec.DetCbor

public section

/-! ## 0. Shared carriers: the tagged hasher, key distinctness, splicing

The regular, the visibly pushdown and the vault layers commit with one hasher and check object
keys with one sort; they live below all three (`Obend.Vault.Lsafe` re-exports them). -/

namespace Obend.Judge.Commit

open Obend.Codec.DetCbor

set_option autoImplicit false

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

example : keysDistinctB ["b".toByteArray, "a".toByteArray] = true := by decide +kernel
example : keysDistinctB ["b".toByteArray, "a".toByteArray, "b".toByteArray] = false := by
  decide +kernel

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

/-- The base-256 digits of a count, least significant first, at a fuel. -/
def countDigits : Nat → Nat → List UInt8
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else UInt8.ofNat (n % 256) :: countDigits f (n / 256)

def ofDigits : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * ofDigits bs

theorem ofDigits_countDigits : ∀ (f n : Nat), n ≤ f → ofDigits (countDigits f n) = n
  | 0, n, h => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | f + 1, n, h => by
    unfold countDigits
    by_cases hn : n = 0
    · subst hn
      rfl
    · rw [ite_eq_right hn]
      simp only [ofDigits]
      rw [ofDigits_countDigits f (n / 256) (by omega), UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := by decide
      rw [h8]
      omega

/-- The leaf count as a span: the framing of a leaf message binds it. -/
def countSpan (n : Nat) : ByteArray := ⟨(countDigits n n).toArray⟩

theorem countSpan_injective {a b : Nat} (h : countSpan a = countSpan b) : a = b := by
  have hl : countDigits a a = countDigits b b := by
    have := congrArg (fun x : ByteArray => x.data.toList) h
    simpa [countSpan] using this
  calc a = ofDigits (countDigits a a) := (ofDigits_countDigits a a (Nat.le_refl _)).symm
    _ = ofDigits (countDigits b b) := by rw [hl]
    _ = b := ofDigits_countDigits b b (Nat.le_refl _)

/-- Lowercase hex of a byte string: the wire form of the byte formats. -/
def hexOf (b : ByteArray) : String :=
  b.data.toList.foldl (fun s x =>
    (s.push (Char.ofNat (if x.toNat / 16 < 10 then 48 + x.toNat / 16 else 87 + x.toNat / 16))).push
      (Char.ofNat (if x.toNat % 16 < 10 then 48 + x.toNat % 16 else 87 + x.toNat % 16))) ""

def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87) else none

def unhexChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
    match hexVal a, hexVal b, unhexChars rest with
    | some x, some y, some r => some (UInt8.ofNat (16 * x + y) :: r)
    | _, _, _ => none

/-- The byte string a lowercase hex string spells; odd lengths and other characters are refused. -/
def unhex (s : String) : Except String ByteArray :=
  match unhexChars s.toList with
  | some l => .ok ⟨l.toArray⟩
  | none => .error "not lowercase hex"

/-- A decimal field. -/
def natField (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error "not a decimal number"

end Obend.Judge.Commit

namespace Obend.Judge.SymbolicRegex

open Obend.Judge.Commit (Hasher cshakeHasher HashCollision hexOf unhex)

set_option autoImplicit false

/-! ## 1. Expressions, semantics, derivatives -/

/-- A Boolean-closed regular expression over bytes. -/
inductive PredRE where
  | ff
  | eps
  | range (lo hi : UInt8)
  | cat (l r : PredRE)
  | alt (l r : PredRE)
  | inter (l r : PredRE)
  | neg (r : PredRE)
  | star (r : PredRE)
  deriving DecidableEq

/-- Complement, by its usual name. -/
abbrev PredRE.compl (r : PredRE) : PredRE := .neg r

/-- The byte lies in the closed interval. -/
@[expose] def inRange (lo hi b : UInt8) : Bool := decide (lo.toNat ≤ b.toNat) && decide (b.toNat ≤ hi.toNat)

/-- **The word semantics.** -/
def Matches : List UInt8 → PredRE → Prop
  | _, .ff => False
  | w, .eps => w = []
  | w, .range lo hi => ∃ b, w = [b] ∧ inRange lo hi b = true
  | w, .cat l r => ∃ u v, w = u ++ v ∧ Matches u l ∧ Matches v r
  | w, .alt l r => Matches w l ∨ Matches w r
  | w, .inter l r => Matches w l ∧ Matches w r
  | w, .neg r => ¬ Matches w r
  | w, .star r => ∃ ws : List (List UInt8), w = ws.flatten ∧ ∀ u ∈ ws, u ≠ [] ∧ Matches u r

/-- Every word. -/
def tt : PredRE := .neg .ff
/-- Any one byte. -/
def anyByte : PredRE := .range 0 255
/-- One given byte. -/
def byte (b : UInt8) : PredRE := .range b b
/-- The bytes of a literal, in sequence. -/
def lit : List UInt8 → PredRE
  | [] => .eps
  | [b] => byte b
  | b :: bs => .cat (byte b) (lit bs)
/-- No factor of the word matches `bad`. -/
def absenceOf (bad : PredRE) : PredRE := .neg (.cat tt (.cat bad tt))

theorem matches_tt (w : List UInt8) : Matches w tt := by simp [tt, Matches]

/-- Nullability: the empty word is in the language. -/
@[expose] def null : PredRE → Bool
  | .ff => false
  | .eps => true
  | .range _ _ => false
  | .cat l r => null l && null r
  | .alt l r => null l || null r
  | .inter l r => null l && null r
  | .neg r => !null r
  | .star _ => true

/-- The derivative by one byte. -/
@[expose] def der (c : UInt8) : PredRE → PredRE
  | .ff => .ff
  | .eps => .ff
  | .range lo hi => if inRange lo hi c then .eps else .ff
  | .cat l r => if null l then .alt (.cat (der c l) r) (der c r) else .cat (der c l) r
  | .alt l r => .alt (der c l) (der c r)
  | .inter l r => .inter (der c l) (der c r)
  | .neg r => .neg (der c r)
  | .star r => .cat (der c r) (.star r)

theorem null_iff_matches_nil : ∀ r : PredRE, null r = true ↔ Matches [] r
  | .ff => by simp [null, Matches]
  | .eps => by simp [null, Matches]
  | .range _ _ => by simp [null, Matches]
  | .cat l r => by
    simp only [null, Matches, Bool.and_eq_true, null_iff_matches_nil l, null_iff_matches_nil r]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨[], [], rfl, h1, h2⟩
    · rintro ⟨u, v, h, h1, h2⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      exact ⟨h1, h2⟩
  | .alt l r => by
    simp only [null, Matches, Bool.or_eq_true, null_iff_matches_nil l, null_iff_matches_nil r]
  | .inter l r => by
    simp only [null, Matches, Bool.and_eq_true, null_iff_matches_nil l, null_iff_matches_nil r]
  | .neg r => by
    simp only [null, Matches, ← null_iff_matches_nil r]
    cases null r <;> simp
  | .star r => by
    simp only [null, Matches, true_iff]
    exact ⟨[], rfl, fun u hu => by cases hu⟩

theorem der_iff_matches_cons : ∀ (r : PredRE) (c : UInt8) (w : List UInt8),
    Matches (c :: w) r ↔ Matches w (der c r)
  | .ff, _, _ => by simp [der, Matches]
  | .eps, _, _ => by simp [der, Matches]
  | .range lo hi, c, w => by
    simp only [der]
    constructor
    · rintro ⟨b, hb, hr⟩
      cases hb
      simp [hr, Matches]
    · intro h
      cases hc : inRange lo hi c with
      | false => rw [hc] at h; simp [Matches] at h
      | true =>
        rw [hc] at h
        simp only [↓reduceIte, Matches] at h
        exact ⟨c, by rw [h], hc⟩
  | .cat l r, c, w => by
    have ihl := fun w => der_iff_matches_cons l c w
    have ihr := der_iff_matches_cons r c w
    have hn := null_iff_matches_nil l
    simp only [der]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      cases u with
      | nil =>
        simp only [List.nil_append] at huv
        subst huv
        have hnl : null l = true := hn.2 hu
        simp only [hnl, ↓reduceIte, Matches]
        exact Or.inr (ihr.1 hv)
      | cons c' u' =>
        simp only [List.cons_append, List.cons.injEq] at huv
        obtain ⟨rfl, rfl⟩ := huv
        have hcat : Matches (u' ++ v) (.cat (der c l) r) := ⟨u', v, rfl, (ihl u').1 hu, hv⟩
        split
        · simp only [Matches]; exact Or.inl hcat
        · exact hcat
    · intro h
      split at h
      · rename_i hnl
        simp only [Matches] at h
        rcases h with ⟨u', v, rfl, hu, hv⟩ | h
        · exact ⟨c :: u', v, rfl, (ihl u').2 hu, hv⟩
        · exact ⟨[], c :: w, rfl, hn.1 hnl, ihr.2 h⟩
      · simp only [Matches] at h
        obtain ⟨u', v, rfl, hu, hv⟩ := h
        exact ⟨c :: u', v, rfl, (ihl u').2 hu, hv⟩
  | .alt l r, c, w => by
    simp only [der, Matches, der_iff_matches_cons l c w, der_iff_matches_cons r c w]
  | .inter l r, c, w => by
    simp only [der, Matches, der_iff_matches_cons l c w, der_iff_matches_cons r c w]
  | .neg r, c, w => by
    simp only [der, Matches, der_iff_matches_cons r c w]
  | .star r, c, w => by
    have ih := fun w => der_iff_matches_cons r c w
    simp only [der, Matches]
    constructor
    · rintro ⟨ws, hw, hall⟩
      cases ws with
      | nil => simp at hw
      | cons x ws' =>
        have hx := hall x List.mem_cons_self
        cases x with
        | nil => exact absurd rfl hx.1
        | cons c' x' =>
          simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact ⟨x', ws'.flatten, rfl, (ih x').1 hx.2, ws', rfl,
            fun u hu => hall u (List.mem_cons_of_mem _ hu)⟩
    · rintro ⟨u, v, rfl, hu, ws, rfl, hall⟩
      refine ⟨(c :: u) :: ws, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨List.cons_ne_nil _ _, (ih u).2 hu⟩
      · exact hall x hx

/-- **The matcher**: derive by each byte, then read nullability. -/
@[expose] def matchB : List UInt8 → PredRE → Bool
  | [], r => null r
  | c :: w, r => matchB w (der c r)

theorem matchB_iff : ∀ (w : List UInt8) (r : PredRE), matchB w r = true ↔ Matches w r
  | [], r => by simp only [matchB]; exact null_iff_matches_nil r
  | c :: w, r => by
    simp only [matchB]
    exact (matchB_iff w (der c r)).trans (der_iff_matches_cons r c w).symm

instance (w : List UInt8) (r : PredRE) : Decidable (Matches w r) :=
  decidable_of_iff _ (matchB_iff w r)

/-- The two expressions have one language. -/
def LangEq (r s : PredRE) : Prop := ∀ w, Matches w r ↔ Matches w s
/-- Language inclusion. -/
def Incl (r s : PredRE) : Prop := ∀ w, Matches w r → Matches w s

theorem langEq_der {p p' : PredRE} (h : LangEq p p') (a : UInt8) : LangEq (der a p) (der a p') :=
  fun w => by rw [← der_iff_matches_cons, ← der_iff_matches_cons]; exact h (a :: w)

theorem langEq_null {p p' : PredRE} (h : LangEq p p') : null p = null p' :=
  Bool.eq_iff_iff.2 (by rw [null_iff_matches_nil, null_iff_matches_nil]; exact h [])

theorem matches_absenceOf (bad : PredRE) (w : List UInt8) :
    Matches w (absenceOf bad) ↔ ∀ u x v, w = u ++ x ++ v → ¬ Matches x bad := by
  simp only [absenceOf, Matches]
  constructor
  · intro h u x v hw hx
    exact h ⟨u, x ++ v, by rw [hw, List.append_assoc], matches_tt u, x, v, rfl, hx, matches_tt v⟩
  · rintro h ⟨u, y, hw, _, x, v, hy, hx, _⟩
    exact h u x v (by rw [hw, hy, List.append_assoc]) hx

/-! ## 2. Normal forms -/

/-- Append an element that is not there yet. -/
def addNew {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]

/-- Remove repetitions, keeping first occurrences in order. -/
def dedup {α : Type} [DecidableEq α] (l : List α) : List α := l.foldl addNew []

theorem mem_addNew {α : Type} [DecidableEq α] {acc : List α} {x y : α} :
    y ∈ addNew acc x ↔ y ∈ acc ∨ y = x := by
  unfold addNew
  split
  · rename_i h
    constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp [List.mem_append]

theorem mem_foldl_addNew {α : Type} [DecidableEq α] : ∀ (l acc : List α) (y : α),
    y ∈ l.foldl addNew acc ↔ y ∈ acc ∨ y ∈ l
  | [], acc, y => by simp
  | x :: xs, acc, y => by
    rw [List.foldl_cons, mem_foldl_addNew xs, mem_addNew, List.mem_cons, or_assoc]

theorem mem_dedup {α : Type} [DecidableEq α] {l : List α} {y : α} : y ∈ dedup l ↔ y ∈ l := by
  unfold dedup
  rw [mem_foldl_addNew]
  simp

/-- The members of a union, flattened; `ff` contributes none. -/
def alts : PredRE → List PredRE
  | .alt l r => alts l ++ alts r
  | .ff => []
  | .eps => [.eps]
  | .range lo hi => [.range lo hi]
  | .cat l r => [.cat l r]
  | .inter l r => [.inter l r]
  | .neg r => [.neg r]
  | .star r => [.star r]

theorem matches_alts : ∀ (r : PredRE) (w : List UInt8), Matches w r ↔ ∃ x ∈ alts r, Matches w x
  | .alt l r, w => by
    simp only [Matches, alts, List.mem_append, matches_alts l w, matches_alts r w]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, Or.inl hx, h⟩
      · exact ⟨x, Or.inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact Or.inl ⟨x, hx, h⟩
      · exact Or.inr ⟨x, hx, h⟩
  | .ff, _ => by simp [Matches, alts]
  | .eps, _ => by simp [alts]
  | .range _ _, _ => by simp [alts]
  | .cat _ _, _ => by simp [alts]
  | .inter _ _, _ => by simp [alts]
  | .neg _, _ => by simp [alts]
  | .star _, _ => by simp [alts]

/-- A right-nested union of a list. -/
def mkAlts : List PredRE → PredRE
  | [] => .ff
  | [r] => r
  | r :: r' :: rs => .alt r (mkAlts (r' :: rs))

theorem matches_mkAlts : ∀ (l : List PredRE) (w : List UInt8),
    Matches w (mkAlts l) ↔ ∃ x ∈ l, Matches w x
  | [], _ => by simp [mkAlts, Matches]
  | [_], _ => by simp [mkAlts]
  | r :: r' :: rs, w => by
    have ih := matches_mkAlts (r' :: rs) w
    simp only [mkAlts, Matches, ih]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨r, List.mem_cons_self, h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, h⟩

/-- The union of a member list: the full language absorbs it. -/
def altOfList (xs : List PredRE) : PredRE := if tt ∈ xs then tt else mkAlts xs

/-- Union, flattened and deduplicated. -/
def mkAlt (l r : PredRE) : PredRE := altOfList (dedup (alts l ++ alts r))

theorem matches_mkAlt (l r : PredRE) (w : List UInt8) :
    Matches w (mkAlt l r) ↔ Matches w l ∨ Matches w r := by
  have key : (∃ x ∈ dedup (alts l ++ alts r), Matches w x) ↔ Matches w l ∨ Matches w r := by
    rw [matches_alts l w, matches_alts r w]
    constructor
    · rintro ⟨x, hx, h⟩
      rcases List.mem_append.1 (mem_dedup.1 hx) with hx | hx
      · exact Or.inl ⟨x, hx, h⟩
      · exact Or.inr ⟨x, hx, h⟩
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, mem_dedup.2 (List.mem_append.2 (Or.inl hx)), h⟩
      · exact ⟨x, mem_dedup.2 (List.mem_append.2 (Or.inr hx)), h⟩
  unfold mkAlt altOfList
  split
  · rename_i ht
    exact ⟨fun _ => key.1 ⟨tt, ht, matches_tt w⟩, fun _ => matches_tt w⟩
  · rw [matches_mkAlts]; exact key

/-- Concatenation with `ff` as zero and `eps` as unit. -/
def mkCat (l r : PredRE) : PredRE :=
  if l = .ff ∨ r = .ff then .ff else if l = .eps then r else if r = .eps then l else .cat l r

theorem matches_mkCat (l r : PredRE) (w : List UInt8) :
    Matches w (mkCat l r) ↔ Matches w (.cat l r) := by
  unfold mkCat
  split
  · rename_i h
    simp only [Matches]
    constructor
    · exact False.elim
    · rintro ⟨u, v, _, hu, hv⟩
      rcases h with rfl | rfl
      · simp only [Matches] at hu
      · simp only [Matches] at hv
  · split
    · rename_i h
      subst h
      simp only [Matches]
      exact ⟨fun h => ⟨[], w, rfl, rfl, h⟩,
        fun ⟨u, v, hw, hu, hv⟩ => by subst hu; rw [hw]; exact hv⟩
    · split
      · rename_i h
        subst h
        simp only [Matches]
        exact ⟨fun h => ⟨w, [], (List.append_nil w).symm, h, rfl⟩,
          fun ⟨u, v, hw, hu, hv⟩ => by subst hv; rw [hw, List.append_nil]; exact hu⟩
      · exact Iff.rfl

/-- Intersection with `ff` as zero, the full language as unit, and idempotence. -/
def mkInter (l r : PredRE) : PredRE :=
  if l = .ff ∨ r = .ff then .ff else if l = tt then r else if r = tt then l
  else if l = r then l else .inter l r

theorem matches_mkInter (l r : PredRE) (w : List UInt8) :
    Matches w (mkInter l r) ↔ Matches w l ∧ Matches w r := by
  unfold mkInter
  split
  · rename_i h
    rcases h with rfl | rfl <;> simp [Matches]
  · split
    · rename_i h; subst h
      exact ⟨fun h => ⟨matches_tt w, h⟩, fun h => h.2⟩
    · split
      · rename_i h; subst h
        exact ⟨fun h => ⟨h, matches_tt w⟩, fun h => h.1⟩
      · split
        · rename_i h; subst h
          exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
        · simp only [Matches]

/-- Complement; a double complement cancels. -/
def mkNeg (r : PredRE) : PredRE :=
  match r with
  | .neg x => x
  | _ => .neg r

theorem matches_mkNeg (r : PredRE) (w : List UInt8) : Matches w (mkNeg r) ↔ ¬ Matches w r := by
  cases r <;> simp only [mkNeg, Matches]
  exact Decidable.not_not.symm

/-- Iteration; the iteration of `ff` or of `eps` is `eps`. -/
def mkStar (r : PredRE) : PredRE := if r = .ff ∨ r = .eps then .eps else .star r

theorem matches_mkStar (r : PredRE) (w : List UInt8) :
    Matches w (mkStar r) ↔ Matches w (.star r) := by
  unfold mkStar
  split
  · rename_i h
    simp only [Matches]
    constructor
    · rintro rfl; exact ⟨[], rfl, fun u hu => by cases hu⟩
    · rintro ⟨ws, rfl, hall⟩
      cases ws with
      | nil => rfl
      | cons x ws' =>
        have hx := hall x List.mem_cons_self
        rcases h with rfl | rfl
        · simp only [Matches] at hx; exact hx.2.elim
        · simp only [Matches] at hx; exact absurd hx.2 hx.1
  · exact Iff.rfl

/-- **The normal form.** -/
def nrm : PredRE → PredRE
  | .ff => .ff
  | .eps => .eps
  | .range lo hi => if lo.toNat ≤ hi.toNat then .range lo hi else .ff
  | .cat l r => mkCat (nrm l) (nrm r)
  | .alt l r => mkAlt (nrm l) (nrm r)
  | .inter l r => mkInter (nrm l) (nrm r)
  | .neg r => mkNeg (nrm r)
  | .star r => mkStar (nrm r)

/-- **Normalization keeps the language.** -/
theorem nrm_matches : ∀ (r : PredRE) (w : List UInt8), Matches w (nrm r) ↔ Matches w r
  | .ff, _ => by simp only [nrm]
  | .eps, _ => by simp only [nrm]
  | .range lo hi, w => by
    simp only [nrm]
    split
    · exact Iff.rfl
    · rename_i h
      simp only [Matches, inRange, Bool.and_eq_true, decide_eq_true_eq, false_iff]
      rintro ⟨b, _, h1, h2⟩
      exact h (Nat.le_trans h1 h2)
  | .cat l r, w => by
    simp only [nrm, matches_mkCat, Matches, nrm_matches l, nrm_matches r]
  | .alt l r, w => by
    simp only [nrm, matches_mkAlt, Matches, nrm_matches l, nrm_matches r]
  | .inter l r, w => by
    simp only [nrm, matches_mkInter, Matches, nrm_matches l, nrm_matches r]
  | .neg r, w => by
    simp only [nrm, matches_mkNeg, Matches, nrm_matches r]
  | .star r, w => by
    simp only [nrm, matches_mkStar, Matches, nrm_matches r]

/-- Similarity, decided: equal normal forms. -/
def simDecide (r s : PredRE) : Bool := decide (nrm r = nrm s)

theorem simDecide_sound {r s : PredRE} (h : simDecide r s = true) : LangEq r s := fun w => by
  rw [← nrm_matches r w, ← nrm_matches s w, of_decide_eq_true h]

/-! ## 3. Minterms: one representative byte per class -/

/-- The interval atoms of an expression. -/
def atoms : PredRE → List (UInt8 × UInt8)
  | .ff => []
  | .eps => []
  | .range lo hi => [(lo, hi)]
  | .cat l r => atoms l ++ atoms r
  | .alt l r => atoms l ++ atoms r
  | .inter l r => atoms l ++ atoms r
  | .neg r => atoms r
  | .star r => atoms r

/-- A candidate bisimulation: a list of pairs. -/
abbrev Pairs := List (PredRE × PredRE)

/-- Every interval atom of a pair list. -/
def pairAtoms (ps : Pairs) : List (UInt8 × UInt8) := ps.flatMap fun pq => atoms pq.1 ++ atoms pq.2

/-- Two bytes agree on every atom. -/
def SameClass (as : List (UInt8 × UInt8)) (b c : UInt8) : Prop :=
  ∀ a ∈ as, inRange a.1 a.2 b = inRange a.1 a.2 c

/-- **Derivatives factor over minterms**: bytes that agree on the atoms of `r` give the same
derivative of `r`. -/
theorem der_factors_over_minterm : ∀ (r : PredRE) {b c : UInt8}, SameClass (atoms r) b c →
    der b r = der c r
  | .ff, _, _, _ => by simp only [der]
  | .eps, _, _, _ => by simp only [der]
  | .range lo hi, _, _, h => by
    simp only [der, h (lo, hi) (by simp [atoms])]
  | .cat l r, _, _, h => by
    simp only [der,
      der_factors_over_minterm l (fun a ha => h a (by simp [atoms, ha])),
      der_factors_over_minterm r (fun a ha => h a (by simp [atoms, ha]))]
  | .alt l r, _, _, h => by
    simp only [der,
      der_factors_over_minterm l (fun a ha => h a (by simp [atoms, ha])),
      der_factors_over_minterm r (fun a ha => h a (by simp [atoms, ha]))]
  | .inter l r, _, _, h => by
    simp only [der,
      der_factors_over_minterm l (fun a ha => h a (by simp [atoms, ha])),
      der_factors_over_minterm r (fun a ha => h a (by simp [atoms, ha]))]
  | .neg r, _, _, h => by
    simp only [der, der_factors_over_minterm r (fun a ha => h a (by simp [atoms, ha]))]
  | .star r, _, _, h => by
    simp only [der, der_factors_over_minterm r (fun a ha => h a (by simp [atoms, ha]))]

/-- Where a class can start: an interval's lower end, and the byte after its upper end. -/
def breakpoints (as : List (UInt8 × UInt8)) : List UInt8 :=
  as.flatMap fun a => if a.2.toNat < 255 then [a.1, a.2 + 1] else [a.1]

/-- One step of the search for the largest breakpoint at or below `b`. -/
def floorStep (b best x : UInt8) : UInt8 :=
  if best.toNat ≤ x.toNat ∧ x.toNat ≤ b.toNat then x else best

theorem floorFold_spec (b : UInt8) : ∀ (bps : List UInt8) (acc : UInt8), acc.toNat ≤ b.toNat →
    (bps.foldl (floorStep b) acc = acc ∨ bps.foldl (floorStep b) acc ∈ bps) ∧
      (bps.foldl (floorStep b) acc).toNat ≤ b.toNat ∧
      acc.toNat ≤ (bps.foldl (floorStep b) acc).toNat ∧
      ∀ x ∈ bps, x.toNat ≤ b.toNat → x.toNat ≤ (bps.foldl (floorStep b) acc).toNat
  | [], acc, h => ⟨Or.inl rfl, h, Nat.le_refl _, fun _ hx => by cases hx⟩
  | x :: xs, acc, h => by
    rw [List.foldl_cons]
    by_cases hs : acc.toNat ≤ x.toNat ∧ x.toNat ≤ b.toNat
    · have hstep : floorStep b acc x = x := by simp only [floorStep, hs, and_self, ↓reduceIte]
      rw [hstep]
      obtain ⟨h1, h2, h3, h4⟩ := floorFold_spec b xs x hs.2
      refine ⟨Or.inr ?_, h2, Nat.le_trans hs.1 h3, ?_⟩
      · rcases h1 with h1 | h1
        · rw [h1]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h1
      · intro y hy hyb
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h3
        · exact h4 y hy hyb
    · have hstep : floorStep b acc x = acc := by simp only [floorStep, hs, ↓reduceIte]
      rw [hstep]
      obtain ⟨h1, h2, h3, h4⟩ := floorFold_spec b xs acc h
      refine ⟨?_, h2, h3, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro y hy hyb
        rcases List.mem_cons.1 hy with rfl | hy
        · have : y.toNat < acc.toNat := by
            rcases Nat.lt_or_ge y.toNat acc.toNat with hlt | hge
            · exact hlt
            · exact absurd ⟨hge, hyb⟩ hs
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le this h3)
        · exact h4 y hy hyb

/-- **The class representatives** of a pair list. -/
def classesOf (ps : Pairs) : List UInt8 := dedup (0 :: breakpoints (pairAtoms ps))

theorem succ_toNat {x : UInt8} (h : x.toNat < 255) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt8.toNat_add]
  have h1 : (1 : UInt8).toNat = 1 := rfl
  rw [h1]
  omega

/-- **The representatives cover the alphabet**: every byte agrees with one of them on every atom
of the pair list. -/
theorem classesOf_covers (ps : Pairs) (b : UInt8) :
    ∃ c ∈ classesOf ps, SameClass (pairAtoms ps) b c := by
  have hz : (0 : UInt8).toNat ≤ b.toNat := Nat.zero_le _
  obtain ⟨h1, h2, _, h4⟩ := floorFold_spec b (breakpoints (pairAtoms ps)) 0 hz
  refine ⟨(breakpoints (pairAtoms ps)).foldl (floorStep b) 0, ?_, ?_⟩
  · unfold classesOf
    rw [mem_dedup]
    rcases h1 with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h1
  · intro a ha
    have hlo : a.1 ∈ breakpoints (pairAtoms ps) := by
      unfold breakpoints
      refine List.mem_flatMap.2 ⟨a, ha, ?_⟩
      split <;> simp
    apply Bool.eq_iff_iff.2
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hl, hh⟩
      exact ⟨h4 a.1 hlo hl, Nat.le_trans h2 hh⟩
    · rintro ⟨hl, hh⟩
      refine ⟨Nat.le_trans hl h2, ?_⟩
      rcases Nat.lt_or_ge a.2.toNat b.toNat with hlt | hge
      · have hb : b.toNat < 256 := UInt8.toNat_lt b
        have h255 : a.2.toNat < 255 := by omega
        have hhi : a.2 + 1 ∈ breakpoints (pairAtoms ps) := by
          unfold breakpoints
          refine List.mem_flatMap.2 ⟨a, ha, ?_⟩
          simp [h255]
        have := h4 (a.2 + 1) hhi (by rw [succ_toNat h255]; omega)
        rw [succ_toNat h255] at this
        omega
      · exact hge

theorem atoms_subset_pairAtoms {ps : Pairs} {pq : PredRE × PredRE} (h : pq ∈ ps) :
    (∀ a ∈ atoms pq.1, a ∈ pairAtoms ps) ∧ (∀ a ∈ atoms pq.2, a ∈ pairAtoms ps) := by
  constructor <;> intro a ha <;>
    exact List.mem_flatMap.2 ⟨pq, h, List.mem_append.2 (by simp [ha])⟩

/-! ## 4. The bisimulation checker -/

/-- The nullability obligation of an inclusion pair. -/
def nullImp (p q : PredRE) : Bool := !null p || null q
/-- The nullability obligation of an equivalence pair. -/
def nullEq (p q : PredRE) : Bool := null p == null q

/-- The normal form of `(p, q)` is in the list. -/
def memSim (ps : Pairs) (p q : PredRE) : Bool := decide ((nrm p, nrm q) ∈ ps)

/-- One pair is closed under the derivative by every class representative. -/
def closedAt (cls : List UInt8) (ps : Pairs) (pq : PredRE × PredRE) : Bool :=
  cls.all fun c => memSim ps (der c pq.1) (der c pq.2)

/-- The root is in the list, and every pair meets its nullability obligation and is closed. -/
def bisimOk (nullRel : PredRE → PredRE → Bool) (cls : List UInt8) (ps : Pairs) (r s : PredRE) :
    Bool :=
  memSim ps r s && ps.all fun pq => nullRel pq.1 pq.2 && closedAt cls ps pq

/-- **The inclusion checker**: the classes are computed from the pair list. -/
def bisimCheck (ps : Pairs) (r s : PredRE) : Bool := bisimOk nullImp (classesOf ps) ps r s

/-- **The equivalence checker.** -/
def bisimEqCheck (ps : Pairs) (r s : PredRE) : Bool := bisimOk nullEq (classesOf ps) ps r s

theorem memSim_spec {ps : Pairs} {p q : PredRE} (h : memSim ps p q = true) :
    ∃ pq ∈ ps, LangEq p pq.1 ∧ LangEq q pq.2 :=
  ⟨(nrm p, nrm q), of_decide_eq_true h, fun w => (nrm_matches p w).symm,
    fun w => (nrm_matches q w).symm⟩

theorem nullImp_spec {p q : PredRE} (h : nullImp p q = true) : null p = true → null q = true := by
  intro hp
  simp only [nullImp, hp, Bool.not_true, Bool.false_or] at h
  exact h

theorem nullEq_spec {p q : PredRE} (h : nullEq p q = true) : null p = null q := by
  simpa [nullEq] using h

/-- Closure under the representatives is closure under every byte: a byte and the representative
of its class have the same derivative. -/
theorem closedAt_spec {ps : Pairs} {pq : PredRE × PredRE} (hpq : pq ∈ ps)
    (hcl : closedAt (classesOf ps) ps pq = true) (a : UInt8) :
    ∃ pq' ∈ ps, LangEq (der a pq.1) pq'.1 ∧ LangEq (der a pq.2) pq'.2 := by
  obtain ⟨c, hc, hsame⟩ := classesOf_covers ps a
  have hsub := atoms_subset_pairAtoms hpq
  have h1 : der a pq.1 = der c pq.1 :=
    der_factors_over_minterm pq.1 (fun x hx => hsame x (hsub.1 x hx))
  have h2 : der a pq.2 = der c pq.2 :=
    der_factors_over_minterm pq.2 (fun x hx => hsame x (hsub.2 x hx))
  rw [h1, h2]
  unfold closedAt at hcl
  exact memSim_spec (List.all_eq_true.1 hcl c hc)

/-- The bisimulation argument, for any relation the pairs' nullabilities satisfy: by induction on
the word, a byte moves both sides to a pair of the list with the same languages. -/
theorem bisim_core (Rel : Bool → Bool → Prop) {ps : Pairs}
    (hnull : ∀ pq ∈ ps, Rel (null pq.1) (null pq.2))
    (hcl : ∀ pq ∈ ps, ∀ a : UInt8,
      ∃ pq' ∈ ps, LangEq (der a pq.1) pq'.1 ∧ LangEq (der a pq.2) pq'.2) :
    ∀ (w : List UInt8) (p q : PredRE), (∃ pq ∈ ps, LangEq p pq.1 ∧ LangEq q pq.2) →
      Rel (matchB w p) (matchB w q)
  | [], p, q, ⟨pq, hm, hp, hq⟩ => by
    simp only [matchB]
    rw [langEq_null hp, langEq_null hq]
    exact hnull pq hm
  | a :: w, p, q, ⟨pq, hm, hp, hq⟩ => by
    simp only [matchB]
    obtain ⟨pq', hm', h1, h2⟩ := hcl pq hm a
    exact bisim_core Rel hnull hcl w _ _
      ⟨pq', hm', fun u => (langEq_der hp a u).trans (h1 u), fun u => (langEq_der hq a u).trans (h2 u)⟩

theorem bisimOk_parts {nullRel : PredRE → PredRE → Bool} {cls : List UInt8} {ps : Pairs}
    {r s : PredRE} (h : bisimOk nullRel cls ps r s = true) :
    memSim ps r s = true ∧ ∀ pq ∈ ps, nullRel pq.1 pq.2 = true ∧ closedAt cls ps pq = true := by
  simp only [bisimOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h

/-- **An accepted inclusion certificate proves the inclusion.** -/
theorem bisimCheck_sound {ps : Pairs} {r s : PredRE} (h : bisimCheck ps r s = true) :
    ∀ w, Matches w r → Matches w s := by
  obtain ⟨hroot, hall⟩ := bisimOk_parts h
  intro w hw
  rw [← matchB_iff] at hw ⊢
  exact bisim_core (fun x y => x = true → y = true) (fun pq hm => nullImp_spec (hall pq hm).1)
    (fun pq hm => closedAt_spec hm (hall pq hm).2) w r s (memSim_spec hroot) hw

/-- **An accepted equivalence certificate proves the two languages equal.** -/
theorem bisimEqCheck_sound {ps : Pairs} {r s : PredRE} (h : bisimEqCheck ps r s = true) :
    ∀ w, Matches w r ↔ Matches w s := by
  obtain ⟨hroot, hall⟩ := bisimOk_parts h
  intro w
  rw [← matchB_iff, ← matchB_iff]
  rw [bisim_core (fun x y => x = y) (fun pq hm => nullEq_spec (hall pq hm).1)
    (fun pq hm => closedAt_spec hm (hall pq hm).2) w r s (memSim_spec hroot)]

/-- **A certificate into `absenceOf bad`**: no word of `L(r)` has a factor in `L(bad)`. -/
theorem absenceOf_sound {ps : Pairs} {r bad : PredRE}
    (h : bisimCheck ps r (absenceOf bad) = true) :
    ∀ w, Matches w r → ∀ u x v, w = u ++ x ++ v → ¬ Matches x bad :=
  fun w hw => (matches_absenceOf bad w).1 (bisimCheck_sound h w hw)

/-! ## 5. The committed form -/

/-- A prefix code of the syntax tree: one tag byte per node, the interval ends after tag `2`. -/
def encList : PredRE → List UInt8
  | .ff => [0]
  | .eps => [1]
  | .range lo hi => [2, lo, hi]
  | .cat l r => 3 :: (encList l ++ encList r)
  | .alt l r => 4 :: (encList l ++ encList r)
  | .inter l r => 5 :: (encList l ++ encList r)
  | .neg r => 6 :: encList r
  | .star r => 7 :: encList r

/-- Read one expression off the front of a byte list, at a fuel. -/
def decList : Nat → List UInt8 → Option (PredRE × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, t :: rest =>
    if t = 0 then some (.ff, rest)
    else if t = 1 then some (.eps, rest)
    else if t = 2 then
      match rest with
      | lo :: hi :: r => some (.range lo hi, r)
      | _ => none
    else if t = 3 then
      match decList n rest with
      | some (l, r₁) => (decList n r₁).map fun x => (.cat l x.1, x.2)
      | none => none
    else if t = 4 then
      match decList n rest with
      | some (l, r₁) => (decList n r₁).map fun x => (.alt l x.1, x.2)
      | none => none
    else if t = 5 then
      match decList n rest with
      | some (l, r₁) => (decList n r₁).map fun x => (.inter l x.1, x.2)
      | none => none
    else if t = 6 then (decList n rest).map fun x => (.neg x.1, x.2)
    else if t = 7 then (decList n rest).map fun x => (.star x.1, x.2)
    else none

theorem decList_encList : ∀ (a : PredRE) (n : Nat) (rest : List UInt8), (encList a).length ≤ n →
    decList n (encList a ++ rest) = some (a, rest)
  | .ff, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp [decList, encList]
  | .eps, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp [decList, encList]
  | .range lo hi, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp [decList, encList]
  | .cat l r, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp only [encList, List.length_cons, List.length_append] at hn
    simp only [encList, List.cons_append, List.append_assoc, decList]
    rw [decList_encList l m _ (by omega)]
    simp [decList_encList r m rest (by omega)]
  | .alt l r, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp only [encList, List.length_cons, List.length_append] at hn
    simp only [encList, List.cons_append, List.append_assoc, decList]
    rw [decList_encList l m _ (by omega)]
    simp [decList_encList r m rest (by omega)]
  | .inter l r, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp only [encList, List.length_cons, List.length_append] at hn
    simp only [encList, List.cons_append, List.append_assoc, decList]
    rw [decList_encList l m _ (by omega)]
    simp [decList_encList r m rest (by omega)]
  | .neg r, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp only [encList, List.length_cons] at hn
    simp [decList, encList, decList_encList r m rest (by omega)]
  | .star r, n, rest, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encList] at hn; omega⟩
    simp only [encList, List.length_cons] at hn
    simp [decList, encList, decList_encList r m rest (by omega)]

/-- **The committed bytes of an expression.** -/
def encRE (r : PredRE) : ByteArray := ⟨(encList r).toArray⟩

/-- The decoder: the whole buffer is one expression. -/
def decRE (b : ByteArray) : Option PredRE :=
  match decList b.size b.data.toList with
  | some (r, []) => some r
  | _ => none

theorem decRE_encRE (r : PredRE) : decRE (encRE r) = some r := by
  have h := decList_encList r (encList r).length [] (Nat.le_refl _)
  rw [List.append_nil] at h
  simp [decRE, encRE, ByteArray.size, h]

theorem encRE_injective {a b : PredRE} (h : encRE a = encRE b) : a = b :=
  Option.some.inj (by rw [← decRE_encRE a, ← decRE_encRE b, h])

/-- The customization string of policy commitments. -/
def regexTag : String := "obend.judge.regex.commit.v1"

/-- The commitment of a policy under a hasher. -/
def commitREWith (H : Hasher) (r : PredRE) : ByteArray := H.hash regexTag (encRE r)

/-- **The commitment of a policy**: cSHAKE256 of its encoding, 32 bytes. -/
def commitRE (r : PredRE) : ByteArray := commitREWith cshakeHasher r

theorem commitREWith_size (H : Hasher) (r : PredRE) : (commitREWith H r).size = 32 :=
  H.size_eq _ _

/-- A certificate for a committed inclusion: both policies in the clear, and the pair list. -/
structure CommittedBisimCert where
  lhs : PredRE
  rhs : PredRE
  pairs : Pairs

/-- The expression opens the root. -/
def rootBinds (H : Hasher) (root : ByteArray) (r : PredRE) : Bool :=
  decide (commitREWith H r = root)

/-- The committed verifier at a hasher: both openings, then the certificate. -/
def verifyCommittedBisimWith (H : Hasher) (rootP rootQ : ByteArray) (cert : CommittedBisimCert) :
    Bool :=
  rootBinds H rootP cert.lhs && rootBinds H rootQ cert.rhs &&
    bisimCheck cert.pairs cert.lhs cert.rhs

/-- **The committed verifier** at cSHAKE256. -/
def verifyCommittedBisim (rootP rootQ : ByteArray) (cert : CommittedBisimCert) : Bool :=
  verifyCommittedBisimWith cshakeHasher rootP rootQ cert

theorem verifyCommittedBisimWith_parts {H : Hasher} {rootP rootQ : ByteArray}
    {cert : CommittedBisimCert} (h : verifyCommittedBisimWith H rootP rootQ cert = true) :
    commitREWith H cert.lhs = rootP ∧ commitREWith H cert.rhs = rootQ ∧
      bisimCheck cert.pairs cert.lhs cert.rhs = true := by
  simp only [verifyCommittedBisimWith, rootBinds, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Two different policies with one commitment are two different messages with one digest. -/
def commitCollision (H : Hasher) {a b : PredRE} (hne : a ≠ b)
    (heq : commitREWith H a = commitREWith H b) : HashCollision H regexTag :=
  ⟨encRE a, encRE b, fun h => hne (encRE_injective h), heq⟩

/-- **The binding extractor.** For the policies `P`, `Q` intended at the two roots, an accepted
certificate gives the inclusion `L(P) ⊆ L(Q)`, or a collision between a certificate policy and an
intended one. The branch is decided by comparing the syntax trees. -/
def committedBisimExtract (H : Hasher) {rootP rootQ : ByteArray} {cert : CommittedBisimCert}
    (h : verifyCommittedBisimWith H rootP rootQ cert = true) (P Q : PredRE)
    (hP : commitREWith H P = rootP) (hQ : commitREWith H Q = rootQ) :
    PSum (∀ w, Matches w P → Matches w Q) (HashCollision H regexTag) :=
  if hl : cert.lhs = P then
    if hr : cert.rhs = Q then
      .inl (hl ▸ hr ▸ bisimCheck_sound (verifyCommittedBisimWith_parts h).2.2)
    else .inr (commitCollision H hr ((verifyCommittedBisimWith_parts h).2.1.trans hQ.symm))
  else .inr (commitCollision H hl ((verifyCommittedBisimWith_parts h).1.trans hP.symm))

/-- **Committed inclusion, or a cSHAKE256 collision.** -/
theorem verifyCommittedBisim_sound_or_collision (rootP rootQ : ByteArray)
    (cert : CommittedBisimCert) (P Q : PredRE) :
    verifyCommittedBisim rootP rootQ cert = true → commitRE P = rootP → commitRE Q = rootQ →
      (∀ w, Matches w P → Matches w Q) ∨
        ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
          cshakeHasher.hash regexTag m₁ = cshakeHasher.hash regexTag m₂ := fun h hP hQ =>
  match committedBisimExtract cshakeHasher h P Q hP hQ with
  | .inl incl => Or.inl incl
  | .inr c => Or.inr ⟨c.m₁, c.m₂, c.ne, c.eq⟩

/-! ## 6. The explorer (untrusted) -/

/-- A worklist over normalized derivative pairs. -/
def explore (cls : List UInt8) : Nat → Pairs → Pairs → Pairs
  | 0, _, done => done
  | _ + 1, [], done => done
  | n + 1, (p, q) :: todo, done =>
    if (p, q) ∈ done then explore cls n todo done
    else explore cls n (todo ++ cls.map fun c => (nrm (der c p), nrm (der c q))) (done ++ [(p, q)])

/-- **The certificate search**: explore from the normalized root at a fuel. -/
def emitBisimPairs (fuel : Nat) (r s : PredRE) : Pairs :=
  explore (classesOf [(r, s)]) fuel [(nrm r, nrm s)] []

theorem incl_step {p q : PredRE} (h : Incl p q) (c : UInt8) :
    Incl (nrm (der c p)) (nrm (der c q)) := fun w hw =>
  (nrm_matches _ w).2 ((der_iff_matches_cons q c w).1
    (h _ ((der_iff_matches_cons p c w).2 ((nrm_matches _ w).1 hw))))

/-- Exploration from included pairs reaches only included pairs. -/
theorem explore_incl (cls : List UInt8) : ∀ (n : Nat) (todo done : Pairs),
    (∀ pq ∈ todo, Incl pq.1 pq.2) → (∀ pq ∈ done, Incl pq.1 pq.2) →
    ∀ pq ∈ explore cls n todo done, Incl pq.1 pq.2
  | 0, _, _, _, hd => by simpa only [explore] using hd
  | _ + 1, [], _, _, hd => by simpa only [explore] using hd
  | n + 1, (p, q) :: todo, done, ht, hd => by
    have hpq : Incl p q := ht (p, q) List.mem_cons_self
    have ht' : ∀ pq ∈ todo, Incl pq.1 pq.2 := fun pq h => ht pq (List.mem_cons_of_mem _ h)
    simp only [explore]
    split
    · exact explore_incl cls n todo done ht' hd
    · refine explore_incl cls n _ _ ?_ ?_
      · intro pq h
        rcases List.mem_append.1 h with h | h
        · exact ht' pq h
        · obtain ⟨c, _, rfl⟩ := List.mem_map.1 h
          exact incl_step hpq c
      · intro pq h
        rcases List.mem_append.1 h with h | h
        · exact hd pq h
        · rw [List.mem_singleton.1 h]; exact hpq

theorem emit_incl {r s : PredRE} (h : Incl r s) (fuel : Nat) :
    ∀ pq ∈ emitBisimPairs fuel r s, Incl pq.1 pq.2 :=
  explore_incl _ fuel _ _
    (fun pq hm => by
      rw [List.mem_singleton.1 hm]
      exact fun w hw => (nrm_matches s w).2 (h w ((nrm_matches r w).1 hw)))
    (fun _ hm => by cases hm)

/-! ## 7. The judge -/

/-- A query: is `L(lhs) ⊆ L(rhs)`? -/
structure InclusionQuery where
  lhs : PredRE
  rhs : PredRE

/-- The exploration at this fuel is closed: the root is in it and every derivative pair of every
pair is in it. Nullability is not consulted. -/
def exploreCloses (fuel : Nat) (q : InclusionQuery) : Bool :=
  bisimOk (fun _ _ => true) (classesOf (emitBisimPairs fuel q.lhs q.rhs))
    (emitBisimPairs fuel q.lhs q.rhs) q.lhs q.rhs

/-- **Completeness on closed explorations.** When the exploration closes and the inclusion holds,
the emitted list is an accepted certificate: every explored pair is an included pair, so its
nullability obligation holds. -/
theorem emit_accepted_of_incl {fuel : Nat} {q : InclusionQuery} (hc : exploreCloses fuel q = true)
    (hi : Incl q.lhs q.rhs) :
    bisimCheck (emitBisimPairs fuel q.lhs q.rhs) q.lhs q.rhs = true := by
  obtain ⟨hroot, hall⟩ := bisimOk_parts hc
  simp only [bisimCheck, bisimOk, Bool.and_eq_true, List.all_eq_true]
  refine ⟨hroot, fun pq hm => ⟨?_, (hall pq hm).2⟩⟩
  have hincl := emit_incl hi fuel pq hm
  simp only [nullImp]
  cases hp : null pq.1 with
  | false => rfl
  | true =>
    exact (null_iff_matches_nil pq.2).2 (hincl [] ((null_iff_matches_nil pq.1).1 hp))

/-- The first answer over a list of bytes. -/
def firstSome (f : UInt8 → Option (List UInt8)) : List UInt8 → Option (List UInt8)
  | [] => none
  | c :: cs => match f c with
    | some w => some w
    | none => firstSome f cs

theorem firstSome_spec {f : UInt8 → Option (List UInt8)} : ∀ {cs : List UInt8} {w : List UInt8},
    firstSome f cs = some w → ∃ c, f c = some w
  | [], _, h => by cases h
  | c :: cs, w, h => by
    simp only [firstSome] at h
    cases hf : f c with
    | some w' => rw [hf] at h; exact ⟨c, by rw [hf]; exact h⟩
    | none => rw [hf] at h; exact firstSome_spec h

/-- A word of `L(p)` outside `L(q)` of length at most the depth, read along class
representatives: a pair with `p` nullable and `q` not is the end of one. -/
def cexAt (cls : List UInt8) : Nat → PredRE → PredRE → Option (List UInt8)
  | 0, p, q => if null p && !null q then some [] else none
  | n + 1, p, q =>
    if null p && !null q then some []
    else firstSome (fun c => (cexAt cls n (nrm (der c p)) (nrm (der c q))).map (c :: ·)) cls

/-- **A found word is a counterexample.** -/
theorem cexAt_sound (cls : List UInt8) : ∀ (n : Nat) (p q : PredRE) (w : List UInt8),
    cexAt cls n p q = some w → Matches w p ∧ ¬ Matches w q := by
  have base : ∀ (p q : PredRE), (null p && !null q) = true → Matches [] p ∧ ¬ Matches [] q := by
    intro p q h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨(null_iff_matches_nil p).1 h.1, fun hq => ?_⟩
    rw [(null_iff_matches_nil q).2 hq] at h
    exact absurd h.2 (by decide)
  intro n
  induction n with
  | zero =>
    intro p q w h
    simp only [cexAt] at h
    split at h
    · rename_i hn; cases h; exact base p q hn
    · cases h
  | succ n ih =>
    intro p q w h
    simp only [cexAt] at h
    split at h
    · rename_i hn; cases h; exact base p q hn
    · obtain ⟨c, hc⟩ := firstSome_spec h
      cases hr : cexAt cls n (nrm (der c p)) (nrm (der c q)) with
      | none => rw [hr] at hc; cases hc
      | some w' =>
        rw [hr] at hc
        cases hc
        obtain ⟨h1, h2⟩ := ih _ _ _ hr
        exact ⟨(der_iff_matches_cons p c w').2 ((nrm_matches _ w').1 h1),
          fun hq => h2 ((nrm_matches _ w').2 ((der_iff_matches_cons q c w').1 hq))⟩

/-- The refutation search of a query at a depth. -/
def searchCex (q : InclusionQuery) (depth : Nat) : Option (List UInt8) :=
  cexAt (classesOf [(q.lhs, q.rhs)]) depth (nrm q.lhs) (nrm q.rhs)

theorem searchCex_sound {q : InclusionQuery} {depth : Nat} {w : List UInt8}
    (h : searchCex q depth = some w) : ¬ Incl q.lhs q.rhs := by
  obtain ⟨h1, h2⟩ := cexAt_sound _ _ _ _ _ h
  exact fun hi => h2 ((nrm_matches _ w).2 (hi w ((nrm_matches _ w).1 h1)))

/-- Why an inclusion is refused. Both clauses come with the word, as the refusal's path. -/
inductive InclusionRefusal where
  /-- the empty word: `lhs` is nullable and `rhs` is not -/
  | nullableMismatch
  /-- a non-empty word of `L(lhs)` outside `L(rhs)` -/
  | counterexample
  deriving DecidableEq, Repr

/-- The verdict: an accepted certificate, else a counterexample found within the grade (first
answer over depths `0 … grade`), else undecided. -/
def inclusionCheck (grade : Nat) (q : InclusionQuery) (cert : Pairs) :
    Judge.Verdict InclusionRefusal :=
  if bisimCheck cert q.lhs q.rhs then .ok
  else match Judge.deepen (searchCex q) grade with
    | some w =>
      .refused (if w.isEmpty then .nullableMismatch else .counterexample) (w.map UInt8.toNat)
    | none => .uncovered

/-- **The inclusion judge.** Its meaning is language inclusion; every refusal is a refutation. -/
instance symbolicRegexInclusionJudge : Judge InclusionQuery Pairs where
  Clause := InclusionRefusal
  Meaning q _ := Incl q.lhs q.rhs
  check := inclusionCheck
  sound := by
    intro r q c h
    unfold inclusionCheck at h
    split at h
    · rename_i hb; exact bisimCheck_sound hb
    · split at h <;> cases h
  refutes _ := true
  refuted := by
    intro r q c k p h _ c' hm
    unfold inclusionCheck at h
    split at h
    · cases h
    · split at h
      · rename_i w hw
        obtain ⟨i, _, hi⟩ := Judge.deepen_some _ hw
        exact searchCex_sound hi hm
      · cases h
  Fragment q := ∃ fuel,
    (nrm q.lhs, nrm q.rhs) ∈ emitBisimPairs fuel q.lhs q.rhs ∧
    ∀ pq ∈ emitBisimPairs fuel q.lhs q.rhs, ∀ b : UInt8,
      (nrm (der b pq.1), nrm (der b pq.2)) ∈ emitBisimPairs fuel q.lhs q.rhs
  complete := by
    rintro q ⟨fuel, hroot, hclosed⟩ ⟨_, hi⟩
    have hc : exploreCloses fuel q = true := by
      simp only [exploreCloses, bisimOk, memSim, closedAt, Bool.and_eq_true,
        Bool.true_and, List.all_eq_true, decide_eq_true_eq]
      exact ⟨hroot, fun pq hp b _ => hclosed pq hp b⟩
    refine ⟨emitBisimPairs fuel q.lhs q.rhs, 0, ?_⟩
    simp only [inclusionCheck, emit_accepted_of_incl hc hi, ↓reduceIte]
  mono := by
    intro r r' q c le h
    simp only [inclusionCheck] at h ⊢
    cases hb : bisimCheck c q.lhs q.rhs with
    | true => rfl
    | false =>
      rw [hb] at h
      cases hd : Judge.deepen (searchCex q) r with
      | some w => rw [Judge.deepen_mono _ hd le]
      | none => rw [hd] at h; simp at h

/-- Finite exploration supplies the semantic fragment through minterm coverage. -/
theorem exploreCloses_fragment {fuel : Nat} {q : InclusionQuery}
    (h : exploreCloses fuel q = true) : symbolicRegexInclusionJudge.Fragment q := by
  obtain ⟨hr, hc⟩ := bisimOk_parts h
  refine ⟨fuel, of_decide_eq_true hr, fun pq hp b => ?_⟩
  obtain ⟨c, hcm, hsame⟩ := classesOf_covers (emitBisimPairs fuel q.lhs q.rhs) b
  have sub := atoms_subset_pairAtoms hp
  rw [der_factors_over_minterm pq.1 (fun a ha => hsame a (sub.1 a ha)),
    der_factors_over_minterm pq.2 (fun a ha => hsame a (sub.2 a ha))]
  exact of_decide_eq_true (List.all_eq_true.1 (hc pq hp).2 c hcm)

/-! ## 8. Witnesses: the checkers accept something and refuse something -/

example : bisimCheck (emitBisimPairs 8 (byte 97) anyByte) (byte 97) anyByte = true := by
  decide +kernel
example : bisimCheck (emitBisimPairs 8 anyByte (byte 97)) anyByte (byte 97) = false := by
  decide +kernel
example : bisimEqCheck (emitBisimPairs 8 (.alt (byte 97) (byte 98)) (.range 97 98))
    (.alt (byte 97) (byte 98)) (.range 97 98) = true := by decide +kernel
example : bisimCheck (emitBisimPairs 16 (lit [97, 98]) (absenceOf (lit [98, 97])))
    (lit [97, 98]) (absenceOf (lit [98, 97])) = true := by decide +kernel
example : simDecide (.alt (byte 97) (.alt .ff (byte 97))) (byte 97) = true := by decide +kernel
example : ∃ q : InclusionQuery, exploreCloses 8 q = true := ⟨⟨byte 97, anyByte⟩, by decide +kernel⟩
example : cexAt [0] 1 anyByte .eps = some [0] := by decide +kernel
example : searchCex ⟨anyByte, .eps⟩ 1 = some [0] := by decide +kernel
example : searchCex ⟨.eps, anyByte⟩ 0 = some [] := by decide +kernel
example : decRE (encRE (absenceOf (lit [123, 123]))) = some (absenceOf (lit [123, 123])) := by
  decide +kernel

/-! ## 9. The byte format `sym-regex-bisim@1`

An object is the two expressions' prefix codes in hex, joined by `:`; a certificate is the pairs'
codes, flat, joined by `:` (empty for no pairs). -/

def encodeInclusionQuery (q : InclusionQuery) : String :=
  hexOf (encRE q.lhs) ++ ":" ++ hexOf (encRE q.rhs)

def decodeREHex (s : String) : Except String PredRE :=
  match unhex s with
  | .error e => .error e
  | .ok b =>
    match decRE b with
    | some r => .ok r
    | none => .error "not an expression code"

def decodeInclusionQuery (s : String) : Except String InclusionQuery :=
  match s.splitOn ":" with
  | [l, r] =>
    match decodeREHex l, decodeREHex r with
    | .ok l, .ok r => .ok ⟨l, r⟩
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error "an inclusion query is two fields"

def encodePairs (ps : Pairs) : String :=
  ":".intercalate (ps.flatMap fun pq => [hexOf (encRE pq.1), hexOf (encRE pq.2)])

def pairOff : List PredRE → Option Pairs
  | [] => some []
  | [_] => none
  | p :: q :: rest => (pairOff rest).map ((p, q) :: ·)

def decodePairs (s : String) : Except String Pairs :=
  if s.isEmpty then .ok []
  else
    match (s.splitOn ":").mapM decodeREHex with
    | .error e => .error e
    | .ok rs =>
      match pairOff rs with
      | some ps => .ok ps
      | none => .error "an odd number of expressions"

/-- The planted refusal: `ε ⊆ any byte` under the empty certificate is refuted by the empty word. -/
theorem plantedInclusion_refused :
    ∃ k p, symbolicRegexInclusionJudge.check 0 (⟨.eps, anyByte⟩ : InclusionQuery) ([] : Pairs) =
      .refused k p := by
  have hb : bisimCheck [] PredRE.eps anyByte = false := by decide +kernel
  obtain ⟨w, hw⟩ := Judge.deepen_isSome (searchCex ⟨.eps, anyByte⟩) (i := 0) (a := [])
    (by decide +kernel)
  refine ⟨if w.isEmpty then .nullableMismatch else .counterexample, w.map UInt8.toNat, ?_⟩
  show inclusionCheck 0 ⟨.eps, anyByte⟩ [] = _
  simp [inclusionCheck, hb, hw]

/-- **The registered format** `sym-regex-bisim@1`. -/
@[expose] def symRegexBisimFormat : Judge.Format where
  name := "sym-regex-bisim"
  version := "1"
  Obj := InclusionQuery
  Cert := Pairs
  decodeObj := decodeInclusionQuery
  decodeCert := decodePairs
  trust := .kernel
  regime := .decidable
  bad := (⟨.eps, anyByte⟩, [])
  badGrade := 0
  bad_refused := plantedInclusion_refused

end Obend.Judge.SymbolicRegex

end
