module
import all Obend.Lower.Pancake.MacaroonVerifier
import all Obend.Lower.Pancake.PancakeKeccak
import all Obend.Lower.Pancake.ByteMemory
import all Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

public section
open Obend.Lower.Pancake Macaroon
namespace PancakeMacaroonTest

private def wordAt (name : String) (i : Nat) : PExp :=
  .load .One (.binop .Add [.lvar name, .const (BitVec.ofNat 64 (8*i))])

private def limb (i : Nat) : PExp := .binop .Xor [wordAt "state" i, wordAt "msg" i]

-- The top byte of each message's last word goes unauthenticated, so one tampered caveat byte passes.
#tooth pancakeMacaroonVerify_correct by mutation absorbField := fun i =>
  let c := Keccak.lanes prefixState i
  if i.val < 4 then .binop .Xor [.const c, wordAt "state" i.val]
  else if i.val < 7 then .binop .Xor [.const c, wordAt "msg" (i.val - 4)]
  else if i.val < 8 then .binop .Xor [.const c, .binop .And [wordAt "msg" 3, .const 0x00ffffffffffffff]]
  else .const (c ^^^ padWords.getD (i.val - 8) 0)

-- A spend above the limit is admitted.
#tooth pancakeMacaroonVerify_correct by mutation caveatCheck :=
  .ite (.cmp .Equal (.binop .And [wordAt "cav" 0, .lvar "op"]) (.lvar "op"))
    (.ite (.cmp .Equal (wordAt "cav" 1) (.lvar "seat"))
      (.ite (.cmp .NotLower (.lvar "epoch") (wordAt "cav" 3)) nextCaveat (.ret (.const 6)))
      (.ret (.const 4)))
    (.ret (.const 3))

-- A spend equal to the limit is refused.
#tooth pancakeMacaroonVerify_correct by mutation caveatCheck :=
  .ite (.cmp .Equal (.binop .And [wordAt "cav" 0, .lvar "op"]) (.lvar "op"))
    (.ite (.cmp .Equal (wordAt "cav" 1) (.lvar "seat"))
      (.ite (.cmp .Lower (.lvar "spend") (wordAt "cav" 2))
        (.ite (.cmp .NotLower (.lvar "epoch") (wordAt "cav" 3)) nextCaveat (.ret (.const 6)))
        (.ret (.const 5)))
      (.ret (.const 4)))
    (.ret (.const 3))

-- The comparison drops the last of the four tag limbs.
#tooth pancakeMacaroonVerify_correct by mutation tagDiff :=
  .binop .Or [.binop .Or [limb 0, limb 1], limb 2]

-- A mismatch writes the limb difference into caller-visible memory.
#tooth pancakeMacaroonVerify_correct by mutation refuseForged :=
  .seq (.store (.lvar "state") (.lvar "diff")) (.ret (.const 2))

-- The workspace keeps the final permutation state, from which the previous link's key inverts.
#tooth pancakeMacaroonVerify_scrubs by mutation scrub := .skip

-- SHAKE256's suffix in place of cSHAKE256's.
#tooth pancakeMacaroonVerify_correct by mutation padWords :=
  [0x1f, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000]

-- The message pointer walks 24-byte records.
#tooth pancakeMacaroonVerify_correct by mutation advance :=
  .seq (.lassign "msg" (.binop .Add [.lvar "msg", .const 24]))
    (.lassign "left" (.binop .Sub [.lvar "left", .const 1]))

-- The epoch floor is not consulted.
#tooth pancakeMacaroonVerify_correct by mutation caveatCheck :=
  .ite (.cmp .Equal (.binop .And [wordAt "cav" 0, .lvar "op"]) (.lvar "op"))
    (.ite (.cmp .Equal (wordAt "cav" 1) (.lvar "seat"))
      (.ite (.cmp .NotLower (wordAt "cav" 2) (.lvar "spend")) nextCaveat (.ret (.const 5)))
      (.ret (.const 4)))
    (.ret (.const 3))

/-! ## Vectors -/

private def rootKey : Digest := ⟨0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x8796a5b4c3d2e1f0⟩
private def nonce : Digest := ⟨1, 2, 3, 0xdeadbeefcafebabe⟩
private def request : Request := ⟨0b0110, 42, 500, 1000⟩

/-- Every one of these admits `request`; `c2` sits on both bounds. -/
private def c1 : Caveat := ⟨0b1111, 42, 1000, 900⟩
private def c2 : Caveat := ⟨0b0110, 42, 500, 1000⟩
private def admitting : List Caveat :=
  [c1, c2, ⟨0xffffffffffffffff, 42, 0xffffffffffffffff, 0⟩, ⟨0b0111, 42, 700, 10⟩,
   ⟨0b1110, 42, 600, 999⟩, ⟨0xff, 42, 501, 1000⟩, ⟨0b0110, 42, 0x8000000000000000, 1⟩,
   ⟨0b1110, 42, 0x7fffffffffffffff, 1000⟩]

/-- A token whose claimed tag is the real chain under `rootKey`. -/
private def mint (cs : List Caveat) : Token :=
  let t : Token := ⟨rootKey, nonce, cs, ⟨0, 0, 0, 0⟩⟩
  {t with claimed := t.tag}

private def flipClaimed (t : Token) (i : Nat) : Token :=
  let d := t.claimed
  {t with claimed := match i with
    | 0 => {d with w0 := d.w0 ^^^ 1} | 1 => {d with w1 := d.w1 ^^^ 0x100}
    | 2 => {d with w2 := d.w2 ^^^ 0x8000000000000000} | _ => {d with w3 := d.w3 ^^^ 0x10000}}

private def mapFirst (f : Caveat → Caveat) : List Caveat → List Caveat
  | [] => []
  | c :: cs => f c :: cs

private def mapLast (f : Caveat → Caveat) (cs : List Caveat) : List Caveat :=
  (mapFirst f cs.reverse).reverse

private structure Case where
  name : String
  count : Word
  token : Token
  request : Request
  expected : Status

private def vec (name : String) (t : Token) (r : Request) (v : Status) : Case :=
  ⟨name, BitVec.ofNat 64 t.caveats.length, t, r, v⟩

private def vectors : List Case :=
  let two := mint [c1, c2]
  let refusing (c : Caveat) := mint [c]
  [vec "no caveats" (mint []) request .accepted,
   vec "one caveat" (mint [c1]) request .accepted,
   vec "spend and epoch on their bounds" (mint [c2]) request .accepted,
   vec "three caveats" (mint (admitting.take 3)) request .accepted,
   vec "eight caveats" (mint admitting) request .accepted,
   ⟨"nine caveats", 9, mint admitting, request, .malformed⟩,
   ⟨"count 2^64-1", 0xffffffffffffffff, mint admitting, request, .malformed⟩,
   vec "flipped bit in a caveat mask" {two with caveats := mapFirst (fun c => {c with opMask := c.opMask ^^^ 1}) two.caveats} request .forged,
   vec "flipped top byte of the last epoch floor" {two with caveats := mapLast (fun c => {c with minEpoch := c.minEpoch ^^^ 0xff00000000000000}) two.caveats} request .forged,
   vec "flipped nonce" {two with nonce := {nonce with w3 := nonce.w3 ^^^ 1}} request .forged,
   vec "other root key" {two with rootKey := {rootKey with w0 := 0}} request .forged,
   vec "claimed limb 0" (flipClaimed two 0) request .forged,
   vec "claimed limb 1" (flipClaimed two 1) request .forged,
   vec "claimed limb 2" (flipClaimed two 2) request .forged,
   vec "claimed limb 3" (flipClaimed two 3) request .forged,
   vec "last caveat removed" {two with caveats := [c1]} request .forged,
   vec "operation outside the mask" (refusing ⟨0b0100, 42, 1000, 0⟩) request .opDenied,
   vec "other seat" (refusing ⟨0b1111, 41, 1000, 0⟩) request .wrongSeat,
   vec "spend one over" (refusing ⟨0b1111, 42, 499, 0⟩) request .overSpend,
   vec "epoch one under" (refusing ⟨0b1111, 42, 1000, 1001⟩) request .tooEarly,
   vec "first refusal decides" (mint [⟨0b1111, 41, 1000, 0⟩, ⟨0, 42, 0, 9999⟩]) request .wrongSeat,
   vec "later caveat refuses" (mint [c1, ⟨0b1111, 42, 100, 0⟩]) request .overSpend,
   vec "forgery outranks refusal" (flipClaimed (refusing ⟨0b1111, 41, 1000, 0⟩) 3) request .forged,
   vec "unsigned spend" (refusing ⟨0b1111, 42, 1, 0⟩) {request with spend := 0x8000000000000000} .overSpend,
   vec "unsigned epoch" (refusing ⟨0b1111, 42, 1000, 0x8000000000000000⟩) {request with epoch := 1} .tooEarly,
   vec "attenuated by the holder" ((mint [c1]).attenuate c2) request .accepted,
   vec "attenuation narrows" ((mint [c1]).attenuate ⟨0b1111, 42, 100, 0⟩) request .overSpend]

#guard vectors.all fun v =>
  v.count.toNat > maxCaveats ||
    (v.count.toNat == v.token.caveats.length && verifyMacaroon v.token v.request == v.expected)
#guard vectors.length ≥ 20
#guard domain == "OBEND.PANCAKE.MACAROON/v1".toUTF8.toList

/-! ## Memory image -/

private def tokenSlots : Nat := tokenWords maxCaveats

/-- Token and request words, padded to the eight-caveat size with a marker. -/
private def image (t : Token) (r : Request) : List Word :=
  let ws := t.rootKey.words ++ t.nonce.words ++ t.caveats.flatMap (·.body.words) ++
    t.claimed.words ++ [r.op, r.seat, r.spend, r.epoch]
  ws ++ List.replicate (tokenSlots - ws.length) 0x5a5a5a5a5a5a5a5a

/-- Arbitrary initial workspace: the verifier must not depend on it, and must clear it. -/
private def scratch : List Word := (List.range 25).map fun i => BitVec.ofNat 64 (0x9e3779b97f4a7c15 * (i+1))

private def record (v : Case) : List Word := [v.count] ++ scratch ++ image v.token v.request

private def outcome (v : Case) : List Word :=
  [v.expected.code] ++ image v.token v.request ++
    (if v.count.toNat ≤ maxCaveats then List.replicate 25 0 else scratch)

private def bytes (ws : List Word) : ByteArray := ⟨(leBytes ws).toArray⟩

/-- Token at 0, workspace at 512, all else unmapped. -/
private def fixture (v : Case) : PanState Unit where
  locals := FUPDATE (FUPDATE (FUPDATE FEMPTY ("token", .word 0)) ("count", .word v.count)) ("state", .word 512)
  globals := FEMPTY
  code := FEMPTY
  memory := fun a =>
    if a.toNat < 512 then (image v.token v.request).getD (a.toNat / 8) 0
    else scratch.getD ((a.toNat - 512) / 8) 0
  memaddrs := fun a => decide (a.toNat % 8 = 0 ∧ (a.toNat < 8 * tokenSlots ∨ 512 ≤ a.toNat ∧ a.toNat < 712))
  clock := 2 * maxCaveats + 1
  be := false
  ffi := ⟨fun _ _ _ _ => .Oracle_final .FFI_failed, (), []⟩
  base_addr := 0
  top_addr := 712

private def single : Case := vec "one caveat" (mint [c1]) request .accepted

example : Frame (fixture single) 0 1 512 := by
  refine ⟨rfl, rfl, rfl, fun j => ?_, fun _ i hi => ?_, fun _ i hi j => ?_, by decide⟩
  · exact (by decide : ∀ k : Fin 25, (fixture single).memaddrs (WordBuffer.address 512 k) = true) j
  · exact (by decide : ∀ k : Fin 20, (fixture single).memaddrs (WordBuffer.address 0 k) = true) ⟨i, hi⟩
  · exact (by decide : ∀ k : Fin 20, ∀ l : Fin 25, WordBuffer.address 0 k ≠ WordBuffer.address 512 l) ⟨i, hi⟩ j

#guard readToken (fixture single).memory 0 1 == single.token &&
  readRequest (fixture single).memory 0 1 == single.request

-- The emitted AST under PanSem, on the fixture: status, token words and cleared workspace.
#guard
  let (r, t) := evaluate kernel.body (fixture single)
  r == .ret (.word Status.accepted.code) &&
    ((List.range tokenSlots).all fun i => t.memory (BitVec.ofNat 64 (8*i)) == (fixture single).memory (BitVec.ofNat 64 (8*i))) &&
    ((List.range 25).all fun i => t.memory (BitVec.ofNat 64 (512 + 8*i)) == 0)

/-- Records of minted tokens with 0, 1, 4 and 8 caveats, for timing the native verifier. -/
def writeBenchRecords (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for n in [0, 1, 4, 8] do
    let v := vec s!"{n} caveats" (mint (admitting.take n)) request .accepted
    unless verifyMacaroon v.token v.request == .accepted do throw (IO.userError "bench token refused")
    IO.FS.writeBinFile (dir / s!"caveats{n}.rec") (bytes (record v))

def verifyNative (exe file : System.FilePath) : IO Unit := do
  for v in vectors do
    let (result, state) := evaluate kernel.body (fixture v)
    let .ret (.word status) := result | throw (IO.userError s!"PanSem failed: {v.name}")
    let wordsAt (base count : Nat) := (List.range count).map fun i =>
      state.memory (BitVec.ofNat 64 (base + 8*i))
    let expected := bytes ([status] ++ wordsAt 0 tokenSlots ++ wordsAt 512 25)
    unless expected == bytes (outcome v) do throw (IO.userError s!"PanSem mismatch: {v.name}")
    IO.FS.writeBinFile file (bytes (record v))
    let child ← IO.Process.spawn {cmd := exe.toString, args := #[file.toString], stdout := .piped}
    let output ← child.stdout.readBinToEnd
    unless (← child.wait) = 0 && output == expected do
      throw (IO.userError s!"native mismatch: {v.name}")
  IO.println s!"{vectors.length} native verdicts, token buffers and workspaces match Lean"

#print axioms pancakeMacaroonVerify_correct
#print axioms pancakeMacaroonVerify_scrubs
#assert_axioms_tree
end PancakeMacaroonTest

def main (args : List String) : IO Unit := do
  let some src := emitPnkFun Macaroon.kernel | throw (IO.userError "macaroon emission failed")
  match args with
  | ["--emit", path] => IO.FS.writeFile path src
  | ["--records", dir] => PancakeMacaroonTest.writeBenchRecords dir
  | [exe, file] =>
    unless (← IO.FS.readBinFile "Obend/Lower/Pancake/macaroonVerify.pnk") == src.toUTF8 do
      throw (IO.userError "macaroonVerify.pnk differs from the Lean emitter")
    PancakeMacaroonTest.verifyNative exe file
  | _ => throw (IO.userError "expected --emit PATH, --records DIR or EXECUTABLE SCRATCH_FILE")
