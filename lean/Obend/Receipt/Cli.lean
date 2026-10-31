module
/-
# Obend.Receipt.Cli — `obend verify`, `obend receipt`, `obend lrat`

    obend verify RECEIPT.json [--prev PREV.json]
        re-check a receipt with no producer state (`Obend.Receipt.Export.verify`); with its
        predecessor, the chain link too. Exit 0 when it verifies, 3 otherwise.
    obend receipt identity N CERT.lrat OUT.json [--prev PREV.json]
        the receipt of `noCarry N` (x &&& y = 0 → x + y = x ||| y at N bits) with a solver's certificate.
    obend receipt negotiation OUT.json [--full] [--prev PREV.json]
        the receipt of the negotiation's admitted dispatch of the commitment to `p2`.
    obend receipt cnf N OUT.cnf
        the DIMACS encoding of `noCarry N`, for a solver.
    obend lrat CNF PROOF
        check a DIMACS formula and an LRAT proof (or a `v`-line model): the registered `lrat@1` format.
-/
public import Obend.Receipt.Export

open Lean (Json)

namespace Obend.Receipt.Cli

def readJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

def prevDigest (prev : Option String) : IO Digest := do
  match prev with
  | none => pure Export.genesis
  | some p => pure (Export.receiptDigest (← readJson p))

def verifyCommand (path : String) (prev : Option String) : IO UInt32 := do
  let j ← readJson path
  let pj ← match prev with
    | none => pure none
    | some p => pure (some (← readJson p))
  match Export.verify j pj with
  | .ok lines => for l in lines do IO.println l
                 IO.println "verified"; return 0
  | .error e => IO.eprintln s!"refused: {e}"; return 3

def identityCommand (n : Nat) (cert out : String) (prev : Option String) : IO UInt32 := do
  let p ← prevDigest prev
  match Export.identityReceipt (Judge.Identity.noCarry n) (← IO.FS.readFile cert) p with
  | .ok j => IO.FS.writeFile out (j.pretty ++ "\n"); IO.println s!"wrote {out}"; return 0
  | .error e => IO.eprintln e; return 2

def negotiationCommand (out : String) (full : Bool) (prev : Option String) : IO UInt32 := do
  let p ← prevDigest prev
  IO.FS.writeFile out ((Export.negotiationReceipt full p).pretty ++ "\n")
  IO.println s!"wrote {out}"; return 0

def lratCommand (cnf proof : String) : IO UInt32 := do
  let c ← IO.FS.readFile cnf
  let p ← IO.FS.readFile proof
  match Judge.Lrat.checkText 1000000000 c p with
  | .ok => IO.println "ok: unsatisfiable (lrat@1, checked by the compiled kernel-proved checker)"; return 0
  | .refused k path => IO.println s!"refused: {repr k} at {path}"; return 3
  | .uncovered => IO.println "uncovered"; return 3

public def main? : List String → Option (IO UInt32)
  | ["verify", path] => some (verifyCommand path none)
  | ["verify", path, "--prev", prev] => some (verifyCommand path (some prev))
  | ["receipt", "identity", n, cert, out] => n.toNat?.map fun n => identityCommand n cert out none
  | ["receipt", "identity", n, cert, out, "--prev", prev] => n.toNat?.map fun n => identityCommand n cert out (some prev)
  | ["receipt", "negotiation", out] => some (negotiationCommand out false none)
  | ["receipt", "negotiation", out, "--full"] => some (negotiationCommand out true none)
  | ["receipt", "negotiation", out, "--prev", prev] => some (negotiationCommand out false (some prev))
  | ["receipt", "negotiation", out, "--full", "--prev", prev] => some (negotiationCommand out true (some prev))
  | ["receipt", "cnf", n, out] => n.toNat?.map fun n => do
      IO.FS.writeFile out (Judge.Identity.encode (Judge.Identity.noCarry n)).toDimacs; return 0
  | ["lrat", cnf, proof] => some (lratCommand cnf proof)
  | _ => none

end Obend.Receipt.Cli
