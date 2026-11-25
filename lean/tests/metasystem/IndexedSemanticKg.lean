import Obend.Tactic.Tooth
import Obend.AssertAxioms
import Obend.SemanticKG.WireQuery
import Obend.SemanticKG.SlottedEGraph
import Obend.Vault.WorldTree.Demand

open Obend.SemanticKG Obend.Core.Term

open Obend.SymbolicZk.SkolemChaseCore in
private def worldWire : Bool := Id.run do
  let raw := "{\"p\":\"rel\",\"a\":\"x\"}"
  let graph : Obend.Doc.Graph := { atoms := [(1, .text raw)], edges := [(0, 1)] }
  let page : Obend.Vault.Page := ⟨"facts", 1, [graph], some raw, [], none, none⟩
  let world : Obend.Vault.ChunkedWorld.World := { store := {pages := [page]} }
  let some db := databankFromWorld world #[⟨1, 0, 0, raw.utf8ByteSize⟩] | return false
  if (databankFromWorld world #[⟨1, 1, 0, 1⟩]).isSome ||
      (databankFromWorld world #[⟨1, 0, 0, raw.utf8ByteSize+1⟩]).isSome then return false
  let o : SemanticKgObj := ⟨db, databankCommit256 db,
    ⟨wellMatchedJsonVpa, ⟨#[("x".toUTF8, 7)]⟩, #[⟨"rel".toUTF8, 11, 1, Obend.Judge.SymbolicRegex.tt, .ff⟩]⟩,
    #[], ⟨11, [.const 7]⟩, ⟨⟨[]⟩, 1, .atom 3⟩, 1, 1, #[(3, .true3)]⟩
  let check := fun (obj : SemanticKgObj) =>
    explainSemanticKg 0 (encodeSemanticKgObj obj) "{\"kind\":\"chaseProof\",\"fuel\":0}"
  let derived : Atom Obend.SymbolicZk.SkolemChaseCore.Term := ⟨12, [.const 7]⟩
  let absent : Atom Obend.SymbolicZk.SkolemChaseCore.Term := ⟨13, [.const 7]⟩
  let rule : TgdRule := ⟨1, [0], [], [⟨11, [.var 0]⟩], [⟨12, [.var 0]⟩]⟩
  let cert : Obend.SymbolicZk.Ranked.ArrayCert :=
    ⟨#[0,0,0], #[0,1,0], #[0,1,0], #[0,1,0], #[0,1,0], #[(false,0),(false,0)]⟩
  let bits := #[true,true,false]
  let verify := fun atoms target => verifyWhyNotReceipt o.expectedDbRoot o.grammar #[rule] target
    ⟨db, .wfsNegationBlocker atoms bits bits cert true⟩
  let atoms := #[o.targetAtom, derived, absent]
  unless verify atoms absent && !verify atoms o.targetAtom && !verify atoms derived &&
      !verify #[absent, derived, o.targetAtom] absent do return false
  return check o == "accepted" && check {o with targetAtom := ⟨12, [.const 7]⟩} == "uncovered within grade" &&
    check {o with bindings := #[]} == SemanticKgClause.queryGuardDenied.describe &&
    check {o with expectedDbRoot := o.expectedDbRoot + 1} == SemanticKgClause.databankRootMismatch.describe

#guard worldWire

private def binderFixture : StateM Slotted.Graph Bool := do
  let x ← Slotted.insertCore (.lam (.app (.bound 0) (.bound 1))) (fun _ => 8)
  let y ← Slotted.insertCore (.lam (.app (.bound 0) (.bound 1))) (fun _ => 13)
  let captured ← Slotted.insertCore (.lam (.app (.bound 0) (.bound 0)))
  let p ← Slotted.insertCore (.prototype (.bound 0) (.bound 1))
  let swapped ← Slotted.insertCore (.prototype (.bound 1) (.bound 0))
  let a ← Slotted.insertCore (.fix (.nat 1) (.lam (.bound 0)))
  let b ← Slotted.insertCore (.fix (.nat 2) (.lam (.bound 0)))
  let lhs ← Slotted.insertCore (.nat 1)
  let rhs ← Slotted.insertCore (.nat 2)
  let g ← get
  let reps := g.close #[(lhs.id, rhs.id)]
  return x.id == y.id && x.slots == #[16] && y.slots == #[26] &&
    captured.id != x.id && captured.slots.isEmpty &&
    p.id == swapped.id && p.slots == #[0, 2] && swapped.slots == #[2, 0] &&
    a.id != b.id && reps[a.id]? == reps[b.id]? && reps[captured.id]? != reps[x.id]?

#guard binderFixture.run' {}

#guard Colt.coltJoin #[[], [2], [2, 9], [1, 9], [3]] [#[2, 1, 2, 2], #[9, 8, 9]] 4 ==
  #[#[0, 1, 2, 3], #[0, 2, 3], #[0, 2], #[], #[]]

#guard (coreCongruenceRelation #[.nat 1, .nat 2, .lam (.nat 1), .lam (.nat 2)] #[(0,1)]).map
  (fun rel => Colt.coltJoin #[[2,1], [3,1]] rel.columns rel.count) == some #[#[2], #[3]]
#guard (coreCongruenceRelation #[.bound 0, .bound 1] #[(0,1)]).isNone

-- R(x,y), S(y,z), T(x,z). T participates twice, before and after z is introduced.
private def triangle := Colt.freeJoin
  #[⟨[#[1, 1, 2, 1], #[2, 3, 3, 2]], 4⟩, ⟨[#[2, 3, 3], #[4, 5, 4]], 3⟩,
    ⟨[#[1, 2], #[4, 5]], 2⟩]
  #[⟨⟨0, []⟩, 0, #[⟨2, [0]⟩]⟩, ⟨⟨0, [0]⟩, 1, #[⟨1, [1]⟩]⟩,
    ⟨⟨1, [1]⟩, 1, #[⟨2, [0, 2]⟩]⟩]

#guard triangle == #[#[1, 2, 4], #[1, 3, 4], #[2, 3, 5]]

#guard_msgs (drop info) in
#tooth Obend.SemanticKG.Colt.freeJoin_eq_relationalPlan by mutation
  Obend.SemanticKG.Colt.freeJoin := fun _ _ => #[]

#guard_msgs (drop info) in
#tooth Obend.SemanticKG.Colt.coltJoin_eq_relationalJoin by mutation
  Obend.SemanticKG.Colt.coltJoin := fun _ _ _ => #[]

#guard_msgs (drop info) in
#tooth Obend.SemanticKG.decode_encode_semanticKgObj by mutation
  Obend.SemanticKG.decodeSemanticKgObj := fun _ => .error "unsupported"

#guard_msgs (drop info) in
#tooth Obend.SemanticKG.Slotted.slottedRebuild_sound by mutation
  Obend.SemanticKG.Slotted.slottedRebuild := fun _ _ => #[(0, 1)]

#guard_msgs (drop info) in
#tooth Obend.Vault.ChunkedWorld.applyEditDemand_root_eq_full by mutation
  Obend.Vault.ChunkedWorld.applyEditDemand := fun d _ old =>
    (d, Obend.Vault.ChunkedWorld.buildCachedBucket old none)

#guard_msgs (drop info) in
#tooth Obend.Vault.ChunkedWorld.openDemandWorld_getPage_eq_openFullWorld by mutation
  Obend.Vault.ChunkedWorld.openDemandWorld := fun _ => none

#guard_msgs (drop info) in
#assert_axioms_tree
