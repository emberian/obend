/-
# `obend-emit-cam` — write the fidget program and its `cam-gouge@1` certificate

    obend-emit-cam [--root DIR]     (default `..`, the repository root seen from `lean/`)

Writes `apps/fidget-cam/cam/impeller_5axis.ngc` (the posted program), `impeller_5axis.obj` (the
judge's object wire) and `impeller_5axis.cert`: per move, the k-d tree `searchKdZ` finds (larger
groups of moves cost more leaves than they save, measured 2026-11-04). The search runs here, once;
`Obend.Apps.FidgetCamCert` only replays the committed certificate.
-/
import Obend.Apps.FidgetCam

open Obend.Hardware.GeometryCAM Obend.Apps.FidgetCam

partial def groupPass (part tool0 : FRepExpr) (box : Box3D) :
    List (Pt3 × Pt3) → Except String CamPassCert
  | [] => .ok []
  | ms =>
    let rec tryK : List Nat → Except String (Nat × KdCert)
      | [] => .error "a single move has no certificate (it may gouge)"
      | k :: ks =>
        match searchKdZ part tool0 120 box (movesBoxZ (ms.take k)) with
        | some t => .ok (k, t)
        | none => tryK ks
    match tryK [1] with
    | .ok (k, t) => (groupPass part tool0 box (ms.drop k)).map ((k, t) :: ·)
    | .error e => .error e

def checkOnly (root : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let text ← IO.FS.readFile s!"{root}/apps/fidget-cam/cam/impeller_5axis.cert"
  let t1 ← IO.monoMsNow
  match decodeCamCert text with
  | .error e => IO.eprintln e; return 1
  | .ok c =>
    let t2 ← IO.monoMsNow
    let ok := match checkCamGouge fidgetCamObj c with | .ok => true | _ => false
    let t3 ← IO.monoMsNow
    IO.println s!"read {t1-t0} ms, decode {t2-t1} ms, check {t3-t2} ms, accepted {ok}"
    return (if ok then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args == ["--check"] then return (← checkOnly "..")
  let root := match args with
    | ["--root", r] => r
    | _ => ".."
  let o := fidgetCamObj
  let mut certs : Array CamPassCert := #[]
  for ch in o.chunks do
    match groupPass o.part (frepBallEndMill 0 0 0 ch.axis o.toolR o.shankLen) o.box ch.moves with
    | .ok gs => certs := certs.push gs
    | .error e => IO.eprintln e; return 1
  let dir := s!"{root}/apps/fidget-cam/cam"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/impeller_5axis.ngc" impeller5AxisNgc
  IO.FS.writeFile s!"{dir}/impeller_5axis.obj" (encodeCamObj o)
  IO.FS.writeFile s!"{dir}/impeller_5axis.cert" (encodeCamCert certs.toList)
  match checkCamGouge o certs.toList with
  | .ok =>
    let groups := certs.foldl (fun a gs => a + gs.length) 0
    IO.println s!"wrote {dir}: {o.chunks.length} passes, {groups} groups certified"; return 0
  | _ => IO.eprintln "the emitted certificate does not check"; return 1
