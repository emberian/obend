import Obend.Vault.IncrementalJudge
import Obend.Tactic.Tooth

open Obend.Vault Obend.Vault.IncrementalJudge Obend.Doc Obend.Core.Data

private def plain (md : String) : Graph := {atoms := [(1, .text md)], edges := [(0, 1)]}
private def link (md name : String) (id : PageId) : Graph :=
  {atoms := [(1, .text md), (2, .cite name ⟨id, .identity, 0, [], .pinned⟩)], edges := [(0, 1), (1, 2)]}

private def makeEntry (n i : Nat) : Entry :=
  let header := "---\namount: 4\nlaw own: new.amount <= 100\n"
  let g := if i + 1 == n then link (header ++ "law cap: linked.balance <= 100\n---\n") "target" (n + 1)
    else plain (header ++ "---\n")
  ⟨"p" ++ toString i, i + 1, g, 0⟩

private def makeSlot (es : List Entry) (e : Entry) : Except String Slot := do
  let p : Page := ⟨e.name, e.id, [], none, [], none, none⟩
  let pr ← prepareWrite es p e.graph [] .owner 1
  return ⟨pr, none⟩

private def tip (balance : Nat) : Tip := [("target", .record [("balance", .natural balance)])]

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 500
  let entries := (List.range n).map (makeEntry n)
  let es := ⟨"target", n+1, plain "---\nbalance: 2\n---\n", 0⟩ :: entries
  let slots ← IO.ofExcept (entries.mapM (makeSlot es))
  let (cold, cached) := refresh es es (tip 2) slots
  let warmed ← IO.ofExcept cached
  unless cold == n do throw (IO.userError "cold call count")
  let batch := slots.map Slot.prepared
  for balance in [3, 101] do
    let over := tip balance
    let start ← IO.monoMsNow
    let baseline := judgeAllIndexed es es over batch
    let mid ← IO.monoMsNow
    let (calls, result) := refresh es es over warmed
    let stop ← IO.monoMsNow
    unless calls == 1 && result.toBool == (balance ≤ 100) do
      throw (IO.userError s!"unexpected calls or verdict: {calls}, {result.toBool}")
    match baseline, result with
    | .ok (), .ok _ => pure ()
    | .error a, .error b => unless a == b do throw (IO.userError "first-refusal mismatch")
    | _, _ => throw (IO.userError "verdict mismatch")
    IO.println s!"BENCH n={n} balance={balance} cold_calls={cold} indexed_calls={n} refreshed_calls={calls} indexed_ms={mid-start} refreshed_ms={stop-mid}"
  -- Neither an unrelated overlay nor a shadowed second binding changes an effective read.
  let shadowed := [("unrelated", Data.natural 42)] ++ tip 2 ++ tip 101
  let (cleanCalls, clean) := refresh es es shadowed warmed
  unless cleanCalls == 0 && clean.toBool do
    throw (IO.userError "unchanged reads caused a judgment or a refusal")
  IO.println s!"BENCH n={n} unchanged_effective_reads_calls={cleanCalls}"

  -- The changed world adds a law which reads the first writer. Its own prepared inputs and tip are identical.
  let added := link "---\nlaw zero: linked.amount <= 0\n---\n" "p0" 1
  let es' := ⟨"new-limiter", n+2, added, 0⟩ :: es
  let (calls, refused) := refresh es' es' (tip 2) warmed
  unless calls == 1 && !refused.toBool do throw (IO.userError "new incoming bucket failed to invalidate")

  -- Identity resolution still succeeds in res even after the corresponding state disappears from es.
  let (missCalls, miss) := refresh entries es [] warmed
  unless missCalls == 1 && !miss.toBool do throw (IO.userError "present-to-absent pin failed to invalidate")

#print axioms judgePrepared_frame
#tooth judgePrepared_frame by
  mutation observe := fun _ _ _ _ _ => ⟨[], [], [], []⟩

#print axioms validateSlot_isSome_eq_judgePrepared

#print axioms judgeIncremental_eq_judgeAll
#tooth judgeIncremental_eq_judgeAll by
  mutation judgeIncremental := fun _ _ _ _ => .ok ()
