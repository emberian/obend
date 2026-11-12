module
/-
# Exact-input decoder reuse

A command reads a checkpoint, then checks the bytes it writes as its next checkpoint. On an
unchanged open these are the same bytes. Retain one decoder result with its proof, and compare the
next input as a ByteArray (the runtime's byte comparison), before parsing and rebuilding a world.
There is no claim that a decoded world has a canonical encoding: equality is of the inputs.
-/
public import Obend.Vault.LogBytes
@[expose] public section

namespace Obend.Vault.DecodeCache

open Obend.Vault.Log

set_option autoImplicit false

/-- One result of the actual decoder, together with the bytes it decoded. The proof is erased. -/
structure Entry {W : Type} (decode : Bytes → Option W) where
  bytes : ByteArray
  result : Option W
  correct : result = decode bytes.data.toList

/-- Decode a new input, retaining a packed byte key without rebuilding the decoder's list. -/
def fresh {W : Type} (decode : Bytes → Option W) (bytes : Bytes) : Entry decode :=
  ⟨⟨bytes.toArray⟩, decode bytes, by simp⟩

/-- Reuse exactly matching bytes; a different input is decoded normally. Retain only this entry. -/
def read {W : Type} (decode : Bytes → Option W) (cached : Option (Entry decode))
    (bytes : Bytes) : Entry decode :=
  -- Doc.Graph also exports equality via boxed arrays; select the native byte comparison here.
  letI : DecidableEq ByteArray := ByteArray.decEq
  match cached with
  | none => fresh decode bytes
  | some e => if e.bytes = (⟨bytes.toArray⟩ : ByteArray) then e else fresh decode bytes

/-- The cached decoder returns the decoder's result on every input, including malformed bytes and
failed decodes, for every previously cached input. -/
theorem read_eq {W : Type} (decode : Bytes → Option W) (cached : Option (Entry decode))
    (bytes : Bytes) : (read decode cached bytes).result = decode bytes := by
  cases cached with
  | none => rfl
  | some e =>
    simp only [read]
    split
    · rename_i h
      have hc := e.correct
      rw [h] at hc
      simpa using hc
    · rfl

/-- Check the log anchor and world commitment first, then decode once. This factors the deployed
checkpoint check without treating an unauthenticated flag or cache file as a proof. -/
theorem holdsAt_bind {W : Type} (Hb : Bytes → Bytes) (decode : Bytes → Option W)
    (ck : Checkpoint) (bytes : ByteArray) :
    Obend.Vault.LogBytes.holdsAt Hb decode ck bytes =
      (Obend.Vault.LogBytes.holdsAt Hb some ck bytes).bind decode := by
  unfold Obend.Vault.LogBytes.holdsAt
  split
  · rfl
  · dsimp only
    split
    · split
      · split <;> rfl
      · rfl
    · rfl

end Obend.Vault.DecodeCache
