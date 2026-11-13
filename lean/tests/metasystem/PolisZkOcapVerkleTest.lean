module
meta import all Obend.Crypto.Transcript
import all Obend.Crypto.Transcript
meta import all Obend.Polis.ZkBiscuit
import all Obend.Polis.ZkBiscuit
meta import all Obend.Polis.EvidencedOcap
import all Obend.Polis.EvidencedOcap
meta import all Obend.Polis.BlumRam
import all Obend.Polis.BlumRam
import Obend.Polis.EvidencedOcap
import Obend.Polis.ZkBiscuit
import Obend.Polis.BlumRam
import Obend.AssertAxioms
import Obend.Tactic.Tooth

public section
set_option Elab.async false

/-!
# `tests/metasystem/PolisZkOcapVerkleTest.lean`

Runs `Obend.Polis.{EvidencedOcap, ZkBiscuit, VerkleUmem}` on concrete data and aims a `#tooth` at
each headline theorem.

* `#guard` lines evaluate the executable definitions (the fuel evaluator of `capPCA`, the authority
  fold, the chain fold and revoked set, the memory checker, the hash tree).
* `example`s instantiate the universal theorems.
* Each `#tooth` replaces one check by a weaker one and requires the kernel to reject the stored
  proof of a universal theorem that depended on it.
* `#assert_axioms_tree` is the axiom census over every package constant this file can see.
-/

namespace Obend.Tests.PolisZkOcapVerkleTest

open Obend.Polis
open Obend.Crypto
open Obend.Digest.Cshake256

#assert_axioms_tree

/-! Kernel mutation checks and axiom audits for the imported contracts. -/

#tooth Obend.Polis.KleenePred3.accepts_not3 by mutation
  Obend.Polis.KleenePred3.not3 := fun p =>
    match p with
    | .true3 => .false3
    | .false3 => .true3
    | .unbound3 => .true3

#tooth Obend.Polis.Caveat.accepts_stable by mutation
  Obend.Polis.KleenePred3.not3 := fun p =>
    match p with
    | .true3 => .false3
    | .false3 => .true3
    | .unbound3 => .true3

#tooth Obend.Polis.amplify_superadditive by mutation
  Obend.Polis.authorityStep := fun _ acc c =>
    match c with
    | .direct r => acc ||| r
    | .sealBox _ p => acc ||| p
    | .unsealer _ => acc

#tooth Obend.Polis.CombTerm.abst_eval by mutation
  Obend.Polis.CombTerm.lamCode := @lamCodeNoIdentity

#tooth Obend.Polis.attenuate_monotone_rights by mutation
  Obend.Polis.attenuationOk := fun _ _ => true

#tooth Obend.Polis.revoke_ancestor_kills_cone by mutation
  Obend.Polis.lineageLive := fun _ _ => true

#tooth Obend.Polis.revoke_channel_kills by mutation
  Obend.Polis.channelLive := fun _ _ => true

#tooth Obend.Polis.RevokedSet.contains_iff by mutation
  Obend.Polis.RevokedSet.contains := fun s x => searchAux s.keys x s.keys.size 0 (s.keys.size / 2)

#tooth Obend.Polis.pinned_injective by mutation
  Obend.Polis.FullPinnedPublicInputs.ioBytes := fun pi =>
    encodeFrame pi.turnHash pi.capRoot ByteArray.empty

#tooth Obend.Polis.pinned_injective by mutation
  Obend.Polis.FullPinnedPublicInputs.relBytes := fun _ => ByteArray.empty

#tooth Obend.Polis.bindTurn_binds_or_collides by mutation
  Obend.Polis.FullPinnedPublicInputs.ioBytes := fun pi =>
    encodeFrame pi.turnHash pi.capRoot ByteArray.empty

#tooth Obend.Polis.verifyFastBlumArray_sound by mutation
  Obend.Polis.offReadOk := fun _ _ => true

#tooth Obend.Polis.verifyFastBlumArray_sound by mutation
  Obend.Polis.offOrder := fun _ _ => true

#tooth Obend.Polis.verifyFastBlumArray_sound by mutation
  Obend.Polis.permStep := fun _ _ i _ => some (i + 1)

#tooth Obend.Polis.verifyFastBlumArray_reads_last_write by mutation
  Obend.Polis.offReadOk := fun _ _ => true

#tooth Obend.Polis.verifyOpening_binds by mutation
  Obend.Polis.insertAt := fun _ _ sibs => sibs

#tooth Obend.Polis.verifyOpening_inhabited by mutation
  Obend.Polis.verifyOpening := fun _ _ _ _ => false

-- ============================================================================
-- 1. `EvidencedOcap`: S-K terms, the capability PCA, evidenced frames, sealers, Kleene caveats
-- ============================================================================

abbrev T := CombTerm capPCA

def env0 : Nat → CapCode := fun _ => .k

/-- `λ*x. x`. -/
def identityCode : CapCode := CombTerm.lamCode (P := capPCA) 0 env0 (.var 0)

/-- `λ*x. λ*y. y x`. -/
def swapCode : CapCode :=
  CombTerm.lamCode (P := capPCA) 0 env0 (CombTerm.abst 1 (.ap (.var 1) (.var 0)))

/-- `λ*c. guard need c x y`: select `x` when the token `c` carries `need`, else `y`. -/
def guardedSelect (need : UInt64) (x y : CapCode) : CapCode :=
  CombTerm.lamCode (P := capPCA) 0 env0
    (.ap (.ap (.ap (.const (.guard need)) (.var 0)) (.const x)) (.const y))

-- `I = S K K`, and it is the identity.
#guard identityCode == CapCode.s2 .k .k
#guard capApply 8 identityCode (.cap 5) == some (.cap 5)

-- `swap a f = f a`: the attenuator ends up applied to the token.
#guard (capApply 64 swapCode (.cap 7)).bind (fun g => capApply 64 g (.attenuate 3)) == some (.cap 3)

-- The guard selects by authority, and has no result on a non-token.
#guard capApply 64 (guardedSelect 1 (.cap 100) (.cap 200)) (.cap 3) == some (.cap 100)
#guard capApply 64 (guardedSelect 4 (.cap 100) (.cap 200)) (.cap 3) == some (.cap 200)
#guard capApply 64 (guardedSelect 1 (.cap 100) (.cap 200)) .k == none
#guard capApply 8 (.guard 1) .s == none

-- Fuel is a bound, not a semantics: too little yields no answer, never a wrong one.
#guard capApply 1 (guardedSelect 1 (.cap 100) (.cap 200)) (.cap 3) == none

-- Combinatory completeness, instantiated: the abstraction of any term has a code that β-reduces.
example (t : T) (ρ : Nat → CapCode) :
    ∃ f, (t.abst 0).Eval ρ f ∧ ∀ a r, CapApp f a r ↔ t.Eval (PCA.update ρ 0 a) r :=
  CombTerm.abst_eval 0 ρ t

-- What the evaluator returned above is a derivation of the big-step relation.
example : CapApp identityCode (.cap 5) (.cap 5) := capApply_sound 8 _ _ _ (by decide)

-- Evidence composes in the realizability frame, and the composite is a code one can run.
example (rights : UInt64) :
    (realizabilityFrame capPCA).Leads (holdsCap rights)
      ((realizabilityFrame capPCA).seq (CapCode.attenuate 6) (CapCode.attenuate 3))
      (holdsCap (rights &&& 6 &&& 3)) :=
  attenuate_seq_leads rights 6 3

#guard capApply 16 (capPCA.seqCode (.attenuate 6) (.attenuate 3)) (.cap 7) == some (.cap 2)

-- Pairing and projection codes.
#guard capApply 32 capPCA.fstCode (capPCA.pairCode (.cap 1) (.cap 2)) == some (.cap 1)
#guard capApply 32 capPCA.sndCode (capPCA.pairCode (.cap 1) (.cap 2)) == some (.cap 2)
#guard capApply 64 (capPCA.pairEv (.attenuate 1) (.attenuate 2)) (.cap 3) ==
  some (capPCA.pairCode (.cap 1) (.cap 2))

-- Curry then apply, in any evidenced frame.
example (F : EvidencedFrame) (φ₁ φ₂ ψ : F.Ω) (e : F.E) (h : F.Leads (F.conj φ₁ φ₂) e ψ) :
    F.Leads (F.conj φ₁ φ₂) (F.seq (F.pair (F.seq F.efst (F.lam e)) F.esnd) F.eeval) ψ :=
  F.leads_beta h

-- Morris sealer/unsealer: neither half alone, both together, wrong brand.
#guard authority [.sealBox 9 0xF0] == 0
#guard authority [.unsealer 9] == 0
#guard authority [.sealBox 9 0xF0, .unsealer 9] == 0xF0
#guard authority [.sealBox 9 0xF0, .unsealer 8] == 0
#guard authority [.direct 0x0F, .sealBox 9 0xF0, .unsealer 9] == 0xFF

example (brand payload : UInt64) (i : Nat) (hp : hasRight payload i) :
    hasRight (authority ([.sealBox brand payload] ++ [.unsealer brand])) i ∧
      ¬ hasRight (authority [.sealBox brand payload] ||| authority [.unsealer brand]) i :=
  amplify_superadditive brand payload i hp

-- Kleene caveats: an unbound fact refuses, under negation too.
def partialEnv : Nat → KleenePred3
  | 0 => .true3
  | 1 => .false3
  | _ => .unbound3

#guard (KleenePred3.not3 .unbound3).accepts == false
#guard (Caveat.eval partialEnv (.not (.atom 2))).accepts == false
#guard (Caveat.eval partialEnv (.atom 2)).accepts == false
#guard (Caveat.eval partialEnv (.not (.atom 1))).accepts == true
#guard (Caveat.eval partialEnv (.and (.atom 0) (.not (.atom 1)))).accepts == true
#guard (Caveat.eval partialEnv (.and (.atom 0) (.atom 2))).accepts == false
-- Strong Kleene: a decided disjunct decides the disjunction, a decided false conjunct the conjunction.
#guard Caveat.eval partialEnv (.or (.atom 0) (.atom 2)) == .true3
#guard Caveat.eval partialEnv (.and (.atom 1) (.atom 2)) == .false3

-- Tooth 1: let negation turn "unbound" into "true".




-- A sealed box that opens without its unsealer.


/-- Bracket abstraction that forgets the bound variable. -/
def lamCodeNoIdentity {P : PCA} (x : Nat) (ρ : Nat → P.Code) : CombTerm P → P.Code
  | .var n => P.k1 (ρ n)
  | .const c => P.k1 c
  | .ap t u => P.s2 (lamCodeNoIdentity x ρ t) (lamCodeNoIdentity x ρ u)



-- ============================================================================
-- 2. `ZkBiscuit`: revoked set, chain fold, cone revocation, pinned inputs
-- ============================================================================

def bytes (l : List UInt8) : ByteArray := Native.bytesOfList l

-- The revoked set: inserts in any order, sorted keys, binary search.
def revokedSample : RevokedSet := (((RevokedSet.empty.insert 5).insert 1).insert 9).insert 3

#guard revokedSample.keys == #[1, 3, 5, 9]
#guard revokedSample.contains 3 && revokedSample.contains 9 && revokedSample.contains 1
#guard !revokedSample.contains 4 && !revokedSample.contains 0 && !revokedSample.contains 10
#guard (revokedSample.insert 5).keys.size == 4

example (s : RevokedSet) (x : Nat) : s.contains x = true ↔ x ∈ s.keys.toList :=
  s.contains_iff x

-- A root grant and three hops, each narrowing: 0xFF ⊇ 0x0F ⊇ 0x03 ⊇ 0x01.
def rootGrant : Block := ⟨0xFF, .atom 0, bytes [1], bytes [10]⟩
def hop1 : Block := ⟨0x0F, .const true, bytes [2], bytes [11]⟩
def hop2 : Block := ⟨0x03, .not (.atom 1), bytes [3], bytes [12]⟩
def hop3 : Block := ⟨0x01, .const true, bytes [4], bytes [13]⟩
/-- A sibling of `hop1`: same parent, another holder. -/
def hop1' : Block := ⟨0x0F, .const true, bytes [20], bytes [14]⟩
/-- A hop that asks for a right its parent lacks. -/
def widening : Block := ⟨0x10, .const true, bytes [5], bytes [15]⟩
/-- A hop whose caveat needs a fact nobody has supplied. -/
def needsUnbound : Block := ⟨0x01, .not (.atom 2), bytes [6], bytes [16]⟩

def chain : Array Block := #[hop1, hop2, hop3]

#guard (foldChain .empty partialEnv rootGrant chain).map (·.rights) == some 0x01
#guard (foldChain .empty partialEnv rootGrant chain).map (authorize · 0x01) == some true
#guard (foldChain .empty partialEnv rootGrant chain).map (authorize · 0x02) == some false
#guard (foldChain .empty partialEnv rootGrant chain).map (·.lineage.size) == some 32
-- The accumulator carries the chain's provenance digest.
#guard (foldChain .empty partialEnv rootGrant chain).map (·.lineage) ==
  some (lineageOf rootGrant chain.toList)
-- Widening is refused at the hop that tries it.
#guard (foldChain .empty partialEnv rootGrant #[hop1, widening]).isNone
-- An unbound caveat folds, and authorizes nothing, negated or not.
#guard (foldChain .empty partialEnv rootGrant #[hop1, needsUnbound]).map (·.verdict) ==
  some .unbound3
#guard (foldChain .empty partialEnv rootGrant #[hop1, needsUnbound]).map (authorize · 0x01) ==
  some false

-- Revoke `hop1` with one write: its whole cone dies, its sibling lives.
def afterRevoke : RevokedSet := RevokedSet.empty.insert (credNul (lineageOf rootGrant [hop1]))

#guard afterRevoke.keys.size == 1
#guard (foldChain afterRevoke partialEnv rootGrant #[hop1]).isNone
#guard (foldChain afterRevoke partialEnv rootGrant #[hop1, hop2]).isNone
#guard (foldChain afterRevoke partialEnv rootGrant chain).isNone
#guard (foldChain afterRevoke partialEnv rootGrant #[hop1', hop2]).isSome
#guard (foldChain afterRevoke partialEnv rootGrant #[]).isSome
-- Revoking the root grant kills everything under it.
#guard (foldChain (RevokedSet.empty.insert (credNul (lineageOf rootGrant []))) partialEnv rootGrant
  #[hop1', hop2]).isNone
-- Revoking a channel kills the chains with a hop on it, and no others.
#guard (foldChain (RevokedSet.empty.insert (chanNul hop2.channel)) partialEnv rootGrant chain).isNone
#guard (foldChain (RevokedSet.empty.insert (chanNul hop2.channel)) partialEnv rootGrant #[hop1]).isSome

example (rs : RevokedSet) (env : Nat → KleenePred3) (ext : Array Block) :
    foldChain (rs.insert (credNul (lineageOf rootGrant [hop1]))) env rootGrant (#[hop1] ++ ext) =
      none :=
  revoke_ancestor_kills_cone rs env rootGrant #[hop1] ext

-- Pinned public inputs: every field moves the absorbed bytes and the transcript state.
def seedTr : Transcript .unseeded := Transcript.newUnseeded (bytes [0xA1, 0xA2])

def inputsA : FullPinnedPublicInputs :=
  ⟨bytes [1, 1], bytes [2, 2], RevokedSet.empty.root, bytes [4, 4]⟩
def inputsRevoked : FullPinnedPublicInputs := { inputsA with revokedRoot := afterRevoke.root }
def inputsVk : FullPinnedPublicInputs := { inputsA with vkDigest := bytes [4, 5] }
def inputsTurn : FullPinnedPublicInputs := { inputsA with turnHash := bytes [1, 2] }
def inputsCap : FullPinnedPublicInputs := { inputsA with capRoot := bytes [2, 3] }

#guard RevokedSet.empty.root.bytes.size == 32
#guard RevokedSet.empty.root != afterRevoke.root
#guard inputsA.ioBytes != inputsRevoked.ioBytes
#guard inputsA.ioBytes != inputsTurn.ioBytes
#guard inputsA.ioBytes != inputsCap.ioBytes
#guard inputsA.relBytes != inputsVk.relBytes
#guard (bindTurn inputsA seedTr).transcript.state.size == 32
#guard (bindTurn inputsA seedTr).transcript.state != (bindTurn inputsRevoked seedTr).transcript.state
#guard (bindTurn inputsA seedTr).transcript.state != (bindTurn inputsVk seedTr).transcript.state
#guard (bindTurn inputsA seedTr).transcript.state != (bindTurn inputsTurn seedTr).transcript.state
#guard (bindTurn inputsA seedTr).transcript.state != (bindTurn inputsCap seedTr).transcript.state

-- Tooth 2: accept a hop without checking that it narrows; skip the lineage revocation check.






-- A search that only looks at the left half.


-- Tooth 3: leave the revoked root, or the verifier key, out of what is bound.






-- ============================================================================
-- 3. `VerkleUmem`: RAM replay, the offline memory checker, the hash tree
-- ============================================================================

/-- Writes to three addresses, reads back, overwrites, reads again; one read of a cell never
written. -/
def online : Array MemOp :=
  #[ ⟨200, 1, true, 77⟩
   , ⟨100, 2, true, 42⟩
   , ⟨200, 3, false, 77⟩
   , ⟨300, 4, false, 0⟩
   , ⟨100, 5, false, 42⟩
   , ⟨100, 6, true, 43⟩
   , ⟨0xFFFF_FFFF_FFFF_FFFF, 7, true, 9⟩
   , ⟨100, 8, false, 43⟩
   , ⟨0xFFFF_FFFF_FFFF_FFFF, 9, false, 9⟩ ]

/-- The same rows sorted by `(addr, clk)`, written by hand. -/
def offline : Array MemOp :=
  #[ ⟨100, 2, true, 42⟩
   , ⟨100, 5, false, 42⟩
   , ⟨100, 6, true, 43⟩
   , ⟨100, 8, false, 43⟩
   , ⟨200, 1, true, 77⟩
   , ⟨200, 3, false, 77⟩
   , ⟨300, 4, false, 0⟩
   , ⟨0xFFFF_FFFF_FFFF_FFFF, 7, true, 9⟩
   , ⟨0xFFFF_FFFF_FFFF_FFFF, 9, false, 9⟩ ]

def perm : Array Nat := #[1, 4, 5, 7, 0, 2, 3, 6, 8]

#guard (execRamSpec online.toList).map (fun ram => (ram 100, ram 200, ram 300)) == some (43, 77, 0)
#guard verifyFastBlumArray online offline perm
-- The prover's merge sort finds the same witness.
#guard (blumWitness online).1 == offline
#guard (blumWitness online).2 == perm
#guard verifyFastBlumArray online (blumWitness online).1 (blumWitness online).2

/-- The read at clock 8 returns the overwritten value. -/
def forgedOnline : Array MemOp := online.set! 7 ⟨100, 8, false, 42⟩

#guard (execRamSpec forgedOnline.toList).isNone
#guard !verifyFastBlumArray forgedOnline (blumWitness forgedOnline).1 (blumWitness forgedOnline).2
-- A read of an unwritten cell that does not return zero.
#guard !verifyFastBlumArray (online.set! 3 ⟨300, 4, false, 1⟩)
  (blumWitness (online.set! 3 ⟨300, 4, false, 1⟩)).1 (blumWitness (online.set! 3 ⟨300, 4, false, 1⟩)).2
-- An offline transcript out of order, a wrong permutation, a dropped row, a repeated clock.
#guard !verifyFastBlumArray online (offline.swapIfInBounds 0 1) (perm.swapIfInBounds 0 1)
#guard !verifyFastBlumArray online offline (perm.swapIfInBounds 0 1)
#guard !verifyFastBlumArray online offline.pop perm.pop
#guard !verifyFastBlumArray (online.set! 1 ⟨100, 1, true, 42⟩)
  (blumWitness (online.set! 1 ⟨100, 1, true, 42⟩)).1 (blumWitness (online.set! 1 ⟨100, 1, true, 42⟩)).2

-- Soundness and completeness, as theorems about every trace.
example (on off : Array MemOp) (p : Array Nat) (h : verifyFastBlumArray on off p = true) :
    ∃ ram : ExtRam, OnlineMatchesExtRam on ram :=
  verifyFastBlumArray_sound on off p h

example (on : Array MemOp) (ram : ExtRam) (hclk : on.toList.Pairwise clkLt)
    (hrun : OnlineMatchesExtRam on ram) :
    verifyFastBlumArray on (blumWitness on).1 (blumWitness on).2 = true :=
  verifyFastBlumArray_complete on ram hclk hrun

-- The hash tree: a sparse memory, its root, openings, an update.
def mem : Array (UInt64 × UInt64) := #[(100, 43), (200, 77), (0xFFFF_FFFF_FFFF_FFFF, 9)]
def mem' : Array (UInt64 × UInt64) := #[(100, 44), (200, 77), (0xFFFF_FFFF_FFFF_FFFF, 9)]
def root : ByteArray := sparseRoot mem

#guard root.size == 32
#guard (sparseOpen mem 100).size == 16 && (sparseOpen mem 100).all (·.size == 15)
#guard verifyOpening root 100 43 (sparseOpen mem 100)
#guard verifyOpening root 200 77 (sparseOpen mem 200)
#guard verifyOpening root 0xFFFF_FFFF_FFFF_FFFF 9 (sparseOpen mem 0xFFFF_FFFF_FFFF_FFFF)
-- A cell never written opens to zero.
#guard verifyOpening root 300 0 (sparseOpen mem 300)
-- Wrong value, wrong address for the path, a tampered sibling, a short path.
#guard !verifyOpening root 100 42 (sparseOpen mem 100)
#guard !verifyOpening root 101 43 (sparseOpen mem 100)
#guard !verifyOpening root 100 43 ((sparseOpen mem 100).modify 3 (·.set! 0 root))
#guard !verifyOpening root 100 43 (sparseOpen mem 100).pop
-- A write moves the root, and the old siblings verify the move.
#guard sparseRoot mem' != root
#guard verifyUpdate root (sparseRoot mem') 100 43 44 (sparseOpen mem 100)
#guard !verifyUpdate root root 100 43 44 (sparseOpen mem 100)
-- The 256-bit tag of a node is the tag the tree hashes.
#guard (Arity16Node.mk (Array.replicate 16 (leafTag 0)) (by simp)).verkleTag256 ==
  nodeTag (List.replicate 16 (leafTag 0))

example (r : ByteArray) (addr v₁ v₂ : UInt64) (p₁ p₂ : Array (Array ByteArray))
    (h₁ : verifyOpening r addr v₁ p₁ = true) (h₂ : verifyOpening r addr v₂ p₂ = true) :
    (v₁ = v₂ ∧ p₁ = p₂) ∨
      Obend.Digest.HashBytes.CollisionAmong treeHash
        (fun x => OpeningHashed addr v₁ p₁ x ∨ OpeningHashed addr v₂ p₂ x) :=
  verifyOpening_binds h₁ h₂

-- Tooth 4: skip read consistency; skip the `(addr, clk)` order; skip the lookup in `online`.








-- A node hash that drops the running tag.




end Obend.Tests.PolisZkOcapVerkleTest
