module
/- The front end's gate: a decoded typed packet is admitted when preparation
(`Obend.Elab.Prepare`, with the packet's annotations as hints) succeeds in synthesis,
`Bidirectional.checkAgainst` accepts the prepared term at the predicted type, and the prepared
term's `checkWork` is within the packet's grant (the request's `limits.checkWork`, the same
measure and the same word as the slot judge's grant, `Slot.Core4.checkWork`). This replaces the historical fuelled
`Check.check` everywhere the front end admits a program: `FrontEnd.accept`, the open
template check, `Preview.preview`, `obend run` on a packet and `obend check-core`.

A refusal is classified as before, by re-running the same gate on variations of the
packet, and named with the same three sentences: work beyond the grant is the checker
budget; acceptance once every quantity is relaxed is ownership; anything else is
typing. The gate's own refusal (`GateRefusal`) carries the checker's structured refusal
and its path. -/
public import Obend.Elab.Prepare
public import Obend.Elab.Work
public import Obend.Core.Packet

@[expose] public section
namespace Obend.Elab.Gate
open Lean (Json toJson)
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Packet
open Obend.Elab.Prepare Obend.Elab.Work
set_option autoImplicit false

inductive GateRefusal where
  /-- The prepared term's checker work exceeds the packet's grant. -/
  | budget (work grant : Nat)
  | prepare (refusal : PrepareRefusal)
  deriving Repr

/-- What the gate admits: the prepared annotations and the checker's certificate for the
packet's own term and assumptions under them. -/
structure Admitted (source : AnnotatedTerm) (context : Context) (fuel : Nat) where
  annotations : Annotations
  checked : Checked { source with annotations := annotations } context
  within : checkWork { source with annotations := annotations } ≤ fuel

/-- The gate on a source, a context and a work grant. -/
def admitSource (source : AnnotatedTerm) (context : Context) (fuel : Nat) :
    Except GateRefusal (Admitted source context fuel) :=
  match prepareInferred source context with
  | .ok ⟨annotations, checked⟩ =>
    if within : checkWork { source with annotations := annotations } ≤ fuel then
      .ok ⟨annotations, checked, within⟩
    else .error (.budget (checkWork { source with annotations := annotations }) fuel)
  | .error refusal => .error (.prepare refusal)

/-- The gate on a decoded packet. -/
def admit (packet : DecodedPacket) : Except GateRefusal (Admitted packet.source packet.context packet.fuel) :=
  admitSource packet.source packet.context packet.fuel

/-- The admitted program is the packet's erased term, typed. -/
theorem Admitted.erase {source : AnnotatedTerm} {context : Context} {fuel : Nat}
    (admitted : Admitted source context fuel) :
    PartialTyping source.assumptions context source.term admitted.checked.type admitted.checked.uses :=
  admitted.checked.derivation

/-- The admitted certificate with the packet's own annotations replaced: the same erased term
and assumptions, so it is a `Checked` for every source that agrees on those. -/
def Admitted.certificate {source : AnnotatedTerm} {context : Context} {fuel : Nat}
    (admitted : Admitted source context fuel) : Checked { source with annotations := admitted.annotations } context :=
  admitted.checked

/-- Which kind of rule a refused packet broke, by the gate's answer on two variations. -/
def refusalKind (packet : DecodedPacket) : RefusalKind :=
  match admit packet with
  | .error (.budget _ _) => .budget
  | _ =>
    let relaxed := relaxQuantities packet
    if (admit relaxed).toBool then .ownership else .typing

def refusalReason (packet : DecodedPacket) : String :=
  match refusalKind packet with
  | .budget =>
    let work := match admit packet with
      | .error (.budget work _) => toString work
      | _ => "more"
    s!"checker budget refused: checkWork {packet.fuel} is too small for this program (its checker work is {work}); raise limits.checkWork"
  | .ownership =>
    match admit packet with
    | .error (.prepare (.checker (.linearBinderUnused _)))
    | .error (.prepare (.checker (.linearArgumentDropped _ _ _))) =>
      "ownership refused: a linear parameter is used exactly once, and only by a linear parameter; one is not used, or is passed where it may be dropped or shared (the program checks with every quantity unrestricted)"
    | _ => "ownership refused: an affine or linear parameter is used more than once (both mean at most once), or one is captured by a closure that may run again (the program checks with every quantity unrestricted)"
  | .typing => "typing refused: types disagree, a custody value is shared or captured, or an activity rule (an Activity is refused as an argument, record/extend field, specification or prototype component, or sum payload; a Plan must be a sum of first-order data; a response must be first-order data)"

def packetReceipt (value : Json) : Except String Json := do
  let packet ← decodePacket value
  match admit packet with
  | .error _ => throw (refusalReason packet)
  | .ok admitted =>
    return Json.mkObj [
      ("schema", toJson "dregg.objective-bend.typing-receipt.v1"),
      ("status", toJson "accepted"),
      ("type", typeJson admitted.checked.type), ("uses", toJson admitted.checked.uses),
      ("typingScope", toJson "compiled proof-producing bidirectional checker after executable annotation preparation; preservation and demand adequacy separate"),
      ("laws", toJson "undischarged unless independent total law providers are supplied"),
      ("authority", toJson "no current native authority granted")]

/-- Native entry point for a core packet (`obend check-core`). -/
def checkPacketFile (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let result := do
    let parsed ← Json.parse input
    packetReceipt parsed
  match result with
  | .ok receipt => IO.println receipt.compress; return 0
  | .error message =>
      IO.eprintln (Json.mkObj [("schema",toJson "dregg.objective-bend.typing-receipt.v1"),
        ("status",toJson "refused"),("stage",toJson "objective-source-type-check"),("message",toJson message)]).compress
      return 2

end Obend.Elab.Gate
end
