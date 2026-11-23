module
import all Obend.Lower.Pancake.BeltLatch
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms
import all Obend.Lower.Pancake.EmitPnk

public section
open Obend.Lower.Pancake BeltLatch
namespace PancakeBeltLatchTest

private def wordAt (name : String) (i : Nat) : PExp :=
  .load .One (.binop .Add [.lvar name, .const (BitVec.ofNat 64 (8*i))])

#tooth pancakeBeltLatch_correct by mutation digestGuard := fun i j yes no =>
  let check k pass := PStmt.ite (.cmp .Equal (wordAt "current" (i+k)) (wordAt "candidate" (j+k))) pass no
  check 0 (check 1 (check 2 yes))

#tooth pancakeBeltLatch_correct by mutation epochTest :=
  .cmp .NotLower (wordAt "candidate" 5) (wordAt "current" 5)

#tooth pancakeBeltLatch_refusal_preserves_state by mutation commitIfAcknowledged :=
  .seq storeHead (.ite (.cmp .Equal (wordAt "candidate" 18) (.const 1))
    (.ret (.const 0)) (.ret (.const 6)))

private def initial : State :=
  ⟨1, ⟨0xa2d3739942c82117, 2, 3, 4⟩, 0x7fffffffffffffff,
    ⟨5, 6, 7, 0xb71133f0c627d9ae⟩, ⟨9, 10, 11, 12⟩⟩

private def advance : Request :=
  ⟨initial.genesis, initial.epoch, 0x8000000000000000, initial.digest,
    ⟨13, 14, 15, 0xfedcba9876543210⟩, initial.policy, 1⟩

private def flip (d : Digest) : List Digest :=
  [{d with w0 := d.w0 ^^^ 1}, {d with w1 := d.w1 ^^^ 1},
   {d with w2 := d.w2 ^^^ 1}, {d with w3 := d.w3 ^^^ 1}]

private def vectors : List (State × Request × Status) :=
  let after := (stepBeltLatch initial advance).2
  let last := {advance with parentEpoch := after.epoch, parent := after.digest, nextEpoch := -1}
  [(initial, advance, .accepted), (after, advance, .staleParent), (after, last, .accepted),
   ((stepBeltLatch after last).2, {last with parentEpoch := -1, nextEpoch := 0}, .nonIncreasing),
   (initial, {advance with nextEpoch := initial.epoch}, .nonIncreasing),
   (initial, {advance with persistAck := 0}, .missingAck), (initial, {advance with persistAck := 2}, .missingAck),
   ({initial with initialized := 0}, advance, .genesisMismatch), ({initial with initialized := 2}, advance, .genesisMismatch)] ++
  (flip advance.genesis).map (fun d => (initial, {advance with genesis := d}, .genesisMismatch)) ++
  (flip advance.parent).map (fun d => (initial, {advance with parent := d}, .parentFork)) ++
  (flip advance.policy).map (fun d => (initial, {advance with policy := d}, .policyDrift))

#guard vectors.all fun (s, r, v) => decide ((stepBeltLatch s r).1 = v)

private def limbs (d : Digest) := [d.w0, d.w1, d.w2, d.w3]
private def stateWords (s : State) :=
  [s.initialized] ++ limbs s.genesis ++ [s.epoch] ++ limbs s.digest ++ limbs s.policy
private def requestWords (r : Request) :=
  limbs r.genesis ++ [r.parentEpoch, r.nextEpoch] ++ limbs r.parent ++ limbs r.nextDigest ++
    limbs r.policy ++ [r.persistAck]

private def bytes (ws : List Word) : ByteArray := ⟨(ws.flatMap fun w =>
  (List.range 8).map fun i => UInt8.ofNat (w.toNat >>> (8*i))).toArray⟩

private def fixture : PanState Unit where
  locals := FUPDATE (FUPDATE FEMPTY ("current", .word 0)) ("candidate", .word 112)
  globals := FEMPTY
  code := FEMPTY
  memory := fun a => (stateWords initial ++ requestWords advance).getD (a.toNat / 8) 0
  memaddrs := fun a => decide (a.toNat < 264 ∧ a.toNat % 8 = 0)
  clock := 0
  be := false
  ffi := ⟨fun _ _ _ _ => .Oracle_final .FFI_failed, (), []⟩
  base_addr := 0
  top_addr := 264

example : Mapped fixture "current" 0 14 ∧ Mapped fixture "candidate" 112 19 := by
  constructor
  · exact ⟨rfl, fun i hi => (by decide : ∀ k : Fin 14, fixture.memaddrs (WordBuffer.address 0 k) = true) ⟨i, hi⟩⟩
  · exact ⟨rfl, fun i hi => (by decide : ∀ k : Fin 19, fixture.memaddrs (WordBuffer.address 112 k) = true) ⟨i, hi⟩⟩

example : readState fixture.memory 0 = initial ∧ readRequest fixture.memory 112 = advance := by decide

def verifyNative (exe file : System.FilePath) : IO Unit := do
  for (s, r, v) in vectors do
    let (actual, next) := stepBeltLatch s r
    unless actual = v do throw (IO.userError s!"invalid vector for {repr v}")
    IO.FS.writeBinFile file (bytes (stateWords s ++ requestWords r))
    let child ← IO.Process.spawn {cmd := exe.toString, args := #[file.toString], stdout := .piped}
    let output ← child.stdout.readBinToEnd
    unless (← child.wait) = 0 && output == bytes ([v.code] ++ stateWords next ++ requestWords r) do
      throw (IO.userError s!"native mismatch for {repr v}")
  IO.println s!"{vectors.length} native status, state and request buffers match Lean"

#print axioms pancakeBeltLatch_correct
#print axioms pancakeBeltLatch_refusal_preserves_state
#assert_axioms_tree
end PancakeBeltLatchTest

def main (args : List String) : IO Unit := do
  let some src := emitPnkFun BeltLatch.kernel | throw (IO.userError "BeltLatch emission failed")
  match args with
  | ["--emit", path] => IO.FS.writeFile path src
  | [exe, file] =>
    unless (← IO.FS.readFile "Obend/Lower/Pancake/beltLatch.pnk") == src do
      throw (IO.userError "beltLatch.pnk differs from the Lean emitter")
    PancakeBeltLatchTest.verifyNative exe file
  | _ => throw (IO.userError "expected --emit PATH or EXECUTABLE SCRATCH_FILE")
