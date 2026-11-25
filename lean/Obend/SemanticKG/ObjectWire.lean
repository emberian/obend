module
public import Obend.SemanticKG.HypergraphChase
import Obend.Codec.HexString
import all Obend.Vault.WorldTree.ShardedWorld
import all Obend.Judge.SymbolicRegexBisim
import all Obend.SemanticKG.SpanParse

public section
namespace Obend.SemanticKG
open Obend Obend.Core.Digest Obend.Judge Obend.SymbolicZk.SkolemChaseCore
open Obend.Vault.ChunkedWorld
open Obend.Polis (Caveat KleenePred3)
set_option autoImplicit false

structure SemanticKgObj where
  db             : SemanticDatabank
  expectedDbRoot : DatabankRoot256
  grammar        : GrammarSpec
  tgdRules       : Array TgdRule
  targetAtom     : Atom Term
  queryPolicy    : KgQueryPolicy
  rights         : UInt64
  mask           : UInt64
  bindings       : Array (Nat × KleenePred3)

def SemanticKgObj.env (o : SemanticKgObj) (v : Nat) : KleenePred3 :=
  ((o.bindings.find? (fun e => e.1 == v)).map Prod.snd).getD .unbound3

private def cRoot : FastCodec DatabankRoot256 :=
  cMap BitVec.toNat (fun n => if n < 2^256 then some (BitVec.ofNat 256 n) else none)
    (fun d => by simp [d.isLt]) cNat

private def cU32 : FastCodec UInt32 :=
  cMap UInt32.toNat (fun n => if n < 2^32 then some n.toUInt32 else none)
    (fun n => by simp [n.toNat_lt]) cNat

private def cU64 : FastCodec UInt64 :=
  cMap UInt64.toNat (fun n => if n < 2^64 then some n.toUInt64 else none)
    (fun n => by simp [n.toNat_lt]) cNat

private def cRegex : FastCodec SymbolicRegex.PredRE :=
  cMap SymbolicRegex.encRE SymbolicRegex.decRE SymbolicRegex.decRE_encRE cByteArray

private def cChunk : FastCodec DocChunkEntry :=
  cMap (fun c => (c.docId, c.byteOffset, c.rawBytes, c.chunkDigest256))
    (fun (id, off, raw, digest) => some ⟨id, off, raw, digest⟩) (fun _ => rfl)
    (cPair cNat (cPair cNat (cPair cByteArray cRoot)))

private def cDb : FastCodec SemanticDatabank :=
  cMap (fun db => (db.worldLogRoot256, db.chunks)) (fun (d, cs) => some ⟨d, cs⟩)
    (fun _ => rfl) (cPair cRoot (cArray cChunk))

private def cSpanRule : FastCodec SpanRuleSpec :=
  cMap (fun r => (r.predTag, r.predSym, r.arity, r.slicePattern, r.banDelimiter))
    (fun (tag, sym, n, pat, ban) => some ⟨tag, sym, n, pat, ban⟩) (fun _ => rfl)
    (cPair cByteArray (cPair cU32 (cPair cNat (cPair cRegex cRegex))))

private def grammarVpa (accept : Bool) : VpaJson.DetVpa JsonBracketSort JsonStructTok Unit Unit :=
  { wellMatchedJsonVpa with acc := fun _ => accept }

private theorem grammarVpa_eta (v : VpaJson.DetVpa JsonBracketSort JsonStructTok Unit Unit) :
    grammarVpa (v.acc ()) = v := by
  cases v with
  | mk init acc si sc sr =>
    cases init
    have ha : (fun _ : Unit => acc ()) = acc := by funext u; cases u; rfl
    unfold grammarVpa wellMatchedJsonVpa
    congr

private def cGrammar : FastCodec GrammarSpec :=
  cMap (fun g => (g.structuralVpa.acc (), g.entityDict.entries, g.rules))
    (fun (accept, es, rs) => some ⟨grammarVpa accept, ⟨es⟩, rs⟩)
    (fun g => by cases g; simp [grammarVpa_eta])
    (cPair cBool (cPair (cArray (cPair cByteArray cU32)) (cArray cSpanRule)))

private def cPatTerm : FastCodec PatTerm :=
  cMap (fun | .var v => Sum.inl v | .const c => .inr c)
    (fun | .inl v => some (.var v) | .inr c => some (.const c))
    (fun x => by cases x <;> rfl) (cSum cNat cNat)

private def cPat : FastCodec PatAtom :=
  cMap (fun p => (p.rel, p.args)) (fun (rel, args) => some ⟨rel, args⟩)
    (fun _ => rfl) (cPair cNat (cList cPatTerm))

private def cRuleKg : FastCodec TgdRule :=
  cMap (fun r => (r.id, r.frontierVars, r.existVars, r.body, r.head))
    (fun (i, f, e, b, h) => some ⟨i, f, e, b, h⟩) (fun _ => rfl)
    (cPair cNat (cPair (cList cNat) (cPair (cList cNat) (cPair (cList cPat) (cList cPat)))))

mutual
private def termDepth : Term → Nat
  | .const _ => 1
  | .skolem _ _ ts => termsDepth ts + 1
private def termsDepth : List Term → Nat
  | [] => 0
  | t :: ts => max (termDepth t) (termsDepth ts)
end

private theorem termDepth_le {ts : List Term} {t : Term} (h : t ∈ ts) :
    termDepth t ≤ termsDepth ts := by
  induction ts with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hm) (Nat.le_max_right ..)

private def termStep (r : RawCodec Term) : RawCodec Term :=
  rawMap (fun | .const c => Sum.inl c | .skolem i v ts => .inr (i, v, ts))
    (fun | .inl c => some (.const c) | .inr (i, v, ts) => some (.skolem i v ts))
    (rawSum cNat.toRawCodec (rawPair cNat.toRawCodec (rawPair cNat.toRawCodec (rawList r))))

private theorem termRoundtrip : ∀ (k : Nat) (t : Term), termDepth t ≤ k → ∀ rest,
    (iterRaw termStep k).dec ((iterRaw termStep k).enc t ++ rest) = some (t, rest)
  | 0, .const _, hk, _ | 0, .skolem _ _ _, hk, _ => by simp [termDepth] at hk
  | k+1, .const _, _, _ => by simp [iterRaw, termStep, rawMap, rawSum, cNat.roundtrip]
  | k+1, .skolem i v ts, hk, rest => by
    have hts : termsDepth ts ≤ k := by simpa [termDepth] using hk
    have hm := fun t (ht : t ∈ ts) => termRoundtrip k t (Nat.le_trans (termDepth_le ht) hts)
    simp [iterRaw, termStep, rawMap, rawSum, rawPair, rawList, List.append_assoc,
      cNat.roundtrip, decNat_encNat, decListN_enc_mem _ ts hm]

private def cTerm : FastCodec Term := cRec termDepth termStep (fun t k => termRoundtrip k t)

private def cAtom : FastCodec (Atom Term) :=
  cMap (fun a => (a.rel, a.args)) (fun (r, args) => some ⟨r, args⟩)
    (fun _ => rfl) (cPair cNat (cList cTerm))

private def caveatDepth : Caveat → Nat
  | .atom _ | .const _ => 1
  | .not a => caveatDepth a + 1
  | .and a b | .or a b => max (caveatDepth a) (caveatDepth b) + 1

private def caveatStep (r : RawCodec Caveat) : RawCodec Caveat :=
  rawMap (fun | .atom v => .inl (.inl v) | .const b => .inl (.inr b)
              | .not a => .inr (.inl a) | .and a b => .inr (.inr (true, a, b))
              | .or a b => .inr (.inr (false, a, b)))
    (fun | .inl (.inl v) => some (.atom v) | .inl (.inr b) => some (.const b)
         | .inr (.inl a) => some (.not a) | .inr (.inr (true, a, b)) => some (.and a b)
         | .inr (.inr (false, a, b)) => some (.or a b))
    (rawSum (rawSum cNat.toRawCodec cBool.toRawCodec)
      (rawSum r (rawPair cBool.toRawCodec (rawPair r r))))

private theorem caveatRoundtrip (k : Nat) (v : Caveat) (hk : caveatDepth v ≤ k) :
    ∀ rest, (iterRaw caveatStep k).dec ((iterRaw caveatStep k).enc v ++ rest) = some (v, rest) := by
  induction k generalizing v with
  | zero => cases v <;> simp [caveatDepth] at hk
  | succ k ih =>
    cases v with
    | atom v => simp [iterRaw, caveatStep, rawMap, rawSum, cNat.roundtrip]
    | const v => simp [iterRaw, caveatStep, rawMap, rawSum, cBool.roundtrip]
    | not a =>
      have ha : caveatDepth a ≤ k := Nat.le_of_succ_le_succ hk
      simp [iterRaw, caveatStep, rawMap, rawSum, ih a ha]
    | and a b | or a b =>
      have hab : max (caveatDepth a) (caveatDepth b) ≤ k := Nat.le_of_succ_le_succ hk
      obtain ⟨ha, hb⟩ := Nat.max_le.mp hab
      simp [iterRaw, caveatStep, rawMap, rawSum, rawPair, List.append_assoc, cBool.roundtrip,
        ih a ha, ih b hb]

private def cCaveat := cRec caveatDepth caveatStep (fun v k => caveatRoundtrip k v)

private def cPolicy : FastCodec KgQueryPolicy :=
  cMap (fun p => (p.query.atoms, p.needRights, p.caveat))
    (fun (qs, rights, caveat) => some ⟨⟨qs⟩, rights, caveat⟩) (fun _ => rfl)
    (cPair (cList cPat) (cPair cU64 cCaveat))

private def cTruth : FastCodec KleenePred3 :=
  cMap (fun | .true3 => some true | .false3 => some false | .unbound3 => none)
    (fun | some true => some .true3 | some false => some .false3 | none => some .unbound3)
    (fun v => by cases v <;> rfl) (cOption cBool)

private def cObject : FastCodec SemanticKgObj :=
  cMap (fun o => (o.db, o.expectedDbRoot, o.grammar, o.tgdRules, o.targetAtom, o.queryPolicy,
      o.rights, o.mask, o.bindings))
    (fun (db, root, g, rs, tgt, pol, rights, mask, env) =>
      some ⟨db, root, g, rs, tgt, pol, rights, mask, env⟩) (fun _ => rfl)
    (cPair cDb (cPair cRoot (cPair cGrammar (cPair (cArray cRuleKg) (cPair cAtom
      (cPair cPolicy (cPair cU64 (cPair cU64 (cArray (cPair cNat cTruth))))))))))

private def payload (o : SemanticKgObj) : String :=
  Obend.Codec.Hex.hexString (cObject.encodeArray o)

def encodeSemanticKgObj (o : SemanticKgObj) : String := "!" ++ payload o

def decodeKgWith (legacy : String → Except String SemanticKgObj) (s : String) :
    Except String SemanticKgObj := do
  if s.front? != some '!' then return ← legacy s
  let some bytes := Obend.Codec.Hex.hexByteArrayStrict? (s.drop 1).copy.toUTF8
    | throw "invalid semantic KG hex envelope"
  let some o := cObject.decodeExactArray bytes | throw "invalid semantic KG binary object"
  return o

theorem decodeKgWith_encode (legacy : String → Except String SemanticKgObj) (o : SemanticKgObj) :
    decodeKgWith legacy (encodeSemanticKgObj o) = .ok o := by
  have hbang : "!".toList = ['!'] := rfl
  have hdrop : ((encodeSemanticKgObj o).drop 1).copy = payload o := by
    apply String.toList_inj.mp
    simp [String.toList_copy_drop, encodeSemanticKgObj, hbang]
  have hfront : (encodeSemanticKgObj o).front? = some '!' := by
    simp [String.front?_eq, encodeSemanticKgObj, hbang]
  have hx := Obend.Codec.Hex.hexByteArrayStrict?_hexString (cObject.encodeArray o)
  rw [String.toUTF8_eq_toByteArray] at hx
  simp [decodeKgWith, hfront, hdrop, payload, hx,
    FastCodec.decodeExactArray_eq, FastCodec.encodeArray_eq, FastCodec.decodeExact_enc]

end Obend.SemanticKG
