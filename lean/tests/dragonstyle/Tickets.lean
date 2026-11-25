import Obend.OS.DragonStyleAppliance
import Obend.Consensus.SimplexLiveness

open Obend.Consensus.SimplexProtocol Obend.Consensus.SimplexLiveness
open Obend.Polis Obend.Polis.GrainPowerbox Obend.Vault.IrreversibleOutbox
open Obend.OS.DragonStyleAppliance Obend.OS.Sel4MicrokitKernel Obend.OS.SmmuDmaConfinement
open Obend.Trailblaze.Polis (sampleValidPartition)

private def members : List Nat := [0,1,2,3]
private def protocol : Protocol := ⟨[0,1,2,3],1,fun _ => false,by decide,by decide,by decide⟩

private def deliver (msgs : List Msg) : List NetEvent :=
  msgs.flatMap fun m => members.map fun n => .deliver n m

private def finalizeView (net : NetState) (v : Nat) (parent chain : Chain) : Option NetState :=
  let proposal : Msg := ⟨protocol.leader v,v,.propose,.block chain⟩
  let votes : List Msg := members.map fun n => ⟨n,v,.vote,.block chain⟩
  let finalVotes : List Msg := members.map fun n => ⟨n,v,.finalize,.block chain⟩
  runNet protocol ⟨0,1,5⟩ net (
    members.map (fun n => .enter n v parent) ++ [.send proposal] ++ deliver [proposal] ++
    votes.map NetEvent.send ++ deliver votes ++ finalVotes.map NetEvent.send ++ deliver finalVotes ++ [.tick])

private def bodyFor (i : Nat) : ByteArray := Id.run do
  let (principal,nonce,cost,n) := if i = 1 then (1,17,8,10) else if i = 2 then (1,31,12,99)
    else (2,i,1,30)
  let mut out := ByteArray.mk #[principal.toUInt8,nonce.toUInt8,i.toUInt8,cost.toUInt8]
  for j in [4:n] do out := out.push (UInt8.ofNat (i*13+j*41))
  return out

private def initHost : Option PowerboxHost :=
  let root : Block := ⟨1,.const true,"turn".toUTF8,"private verifier".toUTF8⟩
  runPowerbox (genesis [0] fun _ => .unbound3) #[.spawn,.spawn,.spawn,
    .grant 0 1 "turn" root none, .grant 0 2 "turn" root none]

private def cfg : IngressCfg := ⟨3,4096,8192,100⟩
private def ports : Ports := ⟨1,2,[80,81]⟩
private def part : Obend.Trailblaze.Polis.SeL4MicrokitPartition :=
  {sampleValidPartition with domains := sampleValidPartition.domains ++ [⟨2,"storage driver",[],[]⟩]}

private def cap (pd : PdId) (obj : CapObj) (w : Bool := true) : Option CapNode :=
  some ⟨pd,⟨obj,⟨true,w,false⟩,0⟩,none,true⟩

private def initKernel : KState :=
  let cs := #[cap 3 (.pageTableCap 3), cap 3 (.frameCap 0x60846) false, cap 3 (.frameCap 0x60300),
    cap 0 (.smmuStreamCap 16),cap 0 (.frameCap 0x60846),cap 1 (.pageTableCap 1),
    cap 1 (.frameCap 80),cap 2 (.pageTableCap 2),cap 2 (.frameCap 81)]
  runK ⟨cs,[],fun _ => 0,#[],0⟩ [
    .syscall 3 (.map (.cpu 3) 0 1 1 0x60846 false),
    .syscall 3 (.map (.cpu 3) 0 2 2 0x60300 true),
    .syscall 0 (.map (.dev 16) 3 4 0x80000 0x60846 true),
    .syscall 1 (.map (.cpu 1) 5 6 3 80 true),
    .syscall 2 (.map (.cpu 2) 7 8 3 81 true)]

/-- Populate the hosted verifier's private approval table before device boot.
Entries come from successive powerbox invocations and finalized outbox steps. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a ticket image path")
  let some h := initHost | throw (IO.userError "powerbox boot failed")
  let mut state : LoopState := ⟨initKernel,[],⟨3,0,500,0,[],0,[]⟩,h⟩
  unless state.kernel.maps.length == 5 do throw (IO.userError "incomplete boot mappings")
  let mut net : NetState := ⟨0,[],fun _ _ => false,fun _ _ => none⟩
  let mut chain : Chain := []
  let mut tickets := ByteArray.empty
  for i in [1:9] do
    let body := bodyFor i
    let some r := ofBody body | throw (IO.userError "malformed record")
    let bytes := envelope body
    let next := chain ++ [.block i (effectCommitNat r.nullifier .irreversibleActuation bytes)]
    let some network := finalizeView net i chain next
      | throw (IO.userError s!"network refused view {i}")
    let cert : FinCert := ⟨i,next,members⟩
    let req : OutboxEffectReq := ⟨r.nullifier,.irreversibleActuation,i,next,some cert,none,⟨0,bytes⟩⟩
    let t : SmmuVerifierTurn := ⟨[],[.write 16 0x80000000 bytes],[],
      [.write 16 0x80000000 (ByteArray.mk #[0xff]), .write 32 0x60300000 (ByteArray.mk #[0xff])],
      bytes,⟨network.sent,req,none⟩,r.principal,0,1⟩
    let some final := authorizeBody protocol part cfg canonicalSmmuConfig ports state t r
      | throw (IO.userError s!"verifier refused view {i}")
    let st := final.outbox
    let some act := st.dispatchedActuations.head? | throw (IO.userError "missing actuation")
    unless act.dispatchedPayload == bytes && st.highWaterNullifier == r.nullifier do
      throw (IO.userError "ticket differs from finalized dispatch")
    tickets := tickets ++ act.dispatchedPayload
    state := final
    net := network
    chain := next
  -- Cross-check the physical header encoder for every supported generation.
  for i in [0:9] do
    let crc := (Obend.OS.NvmeDurablePersist.mkHeader i.toUInt64).crc32c
    for j in [0:4] do tickets := tickets.push (crc >>> (8*j).toUInt32).toUInt8
  IO.FS.writeBinFile path tickets
