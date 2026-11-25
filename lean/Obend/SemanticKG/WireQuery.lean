module
public import Obend.SemanticKG.SemanticCert
import Std.Data.String.ToNat
import all Obend.SemanticKG.SemanticCert
import all Obend.SemanticKG.SpanParse
import all Obend.SemanticKG.ObjectWire
import all Obend.SemanticKG.Databank
import all Obend.SemanticKG.HypergraphChase
import all Obend.Polis.EvidencedOcap
public section

namespace Obend.SemanticKG
open Obend Obend.Judge Obend.SymbolicZk.SkolemChaseCore

/-- A real document supplies the queried relational fact through the registered object and
certificate decoders. The statement is uniform in the predicate symbol and world anchor. -/
theorem semanticKg_wire_query (sym : UInt32) (anchor : DatabankRoot256) :
    let raw := "{\"p\":\"rel\",\"a\":\"x\"}".toByteArray
    let db : SemanticDatabank := ⟨anchor, #[mkDocChunk 1 0 raw]⟩
    let g : GrammarSpec := ⟨wellMatchedJsonVpa, ⟨#[("x".toByteArray, 7)]⟩,
      #[⟨"rel".toByteArray, sym, 1, SymbolicRegex.tt, .ff⟩]⟩
    let o : SemanticKgObj := ⟨db, databankCommit256 db, g, #[], ⟨sym.toNat, [.const 7]⟩,
      ⟨⟨[]⟩, 1, .atom 3⟩, 1, 1, #[(3, .true3)]⟩
    semanticKgFormat.decodeObj (encodeSemanticKgObj o) = .ok o ∧
    semanticKgFormat.decodeCert (Nat.repr 0) = .ok (.chaseProof 0) ∧
    semanticKgJudge.check 0 o (.chaseProof 0) = .ok := by
  intro raw db g o
  refine ⟨decode_encode_semanticKgObj o, ?_, ?_⟩
  · change decodeSemanticKgCert (Nat.repr 0) = _
    simp only [decodeSemanticKgCert, Nat.toNat?_repr]; rfl
  let a : SpanBoundAtom := ⟨sym, #[7], 1, 0, 19, computeSpanSliceDigest 1 0 19 (raw.extract 0 19)⟩
  have he : extractSpanBoundAtoms g (mkDocChunk 1 0 raw) = .ok #[a] :=
    (extractSpanBoundAtoms_singleton sym).2.2
  have hWf : WfDatabank db = true := by
    have hc : WfDocChunk (mkDocChunk 1 0 raw) = true :=
      wfDocChunk_mkDocChunk (by decide) (by decide) (by decide)
    simp [WfDatabank, db, hc]
  have hBase : isBaseAtom o.targetAtom = true := rfl
  have hGuard : checkKgQueryGuard o.queryPolicy o.rights o.mask o.env = true := by
    change checkKgQueryGuard ⟨⟨[]⟩, 1, .atom 3⟩ 1 1 (fun v => ((#[(3, Obend.Polis.KleenePred3.true3)].find? (fun e => e.1 == v)).map Prod.snd).getD .unbound3) = true
    decide +kernel
  exact check_single_extraction o _ a rfl rfl rfl hWf hBase hGuard he rfl

end Obend.SemanticKG
