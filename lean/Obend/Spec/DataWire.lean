module
/-
# Obend.Spec.DataWire — typed Objective Bend data on the JSON wire

typed-values-v1 plus `variant`: the ONE decoder of the responses a yielded activity is resumed with,
and the ONE printer of extracted Plans and deep results (`Obend.Spec.Preview`). Ported from
minidregg `Compiler/ObjectiveBendDataWire.lean` (commit 092027a2); `dataJson` was `partial def`
there and is structural here (SHIP §5: no `partial def` on a deployed path).
-/
public import Lean
public import Obend.Core.Data
@[expose] public section
namespace Obend.Spec.DataWire
open Lean (Json toJson)
open Obend.Core.Data (Data)
set_option autoImplicit false

mutual
/-- Typed data on the wire: typed-values-v1 plus `variant`. -/
def dataJson : Data → Json
  | .natural n => Json.mkObj [("tag",toJson "natural"),("value",toJson (toString n))]
  | .boolean b => Json.mkObj [("tag",toJson "boolean"),("value",toJson b)]
  | .label s => Json.mkObj [("tag",toJson "label"),("value",toJson s)]
  | .record fields => Json.mkObj [("tag",toJson "record"),("fields",Json.arr (fieldsJson fields).toArray)]
  | .variant label payload => Json.mkObj [("tag",toJson "variant"),("label",toJson label),("payload",dataJson payload)]
def fieldsJson : List (String × Data) → List Json
  | [] => []
  | (name, value) :: rest => Json.mkObj [("name",toJson name),("value",dataJson value)] :: fieldsJson rest
end

def decodeNatural (json : Json) : Except String Data := do
  let text ← json.getObjValAs? String "value"
  let some n := text.toNat? | throw "response natural must be canonical decimal"
  if toString n != text then throw "response natural must be canonical decimal"
  pure (.natural n)

def decodeData : Nat → Json → Except String Data
  | 0, _ => throw "response nesting capacity"
  | fuel + 1, json => do
    let tag ← json.getObjValAs? String "tag"
    if tag == "natural" then decodeNatural json
    else if tag == "boolean" then return .boolean (← json.getObjValAs? Bool "value")
    else if tag == "label" then return .label (← json.getObjValAs? String "value")
    else if tag == "record" then
      let fields ← (← json.getObjVal? "fields").getArr?
      return .record (← fields.toList.mapM fun field => do
        return (← field.getObjValAs? String "name", ← decodeData fuel (← field.getObjVal? "value")))
    else if tag == "variant" then
      return .variant (← json.getObjValAs? String "label") (← decodeData fuel (← json.getObjVal? "payload"))
    else throw "unknown response data tag"

end Obend.Spec.DataWire

end
