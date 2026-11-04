/-
# `Obend/Teeth/Law/Fixtures.lean` — the closed fixtures that left tier 1 (2026-11-04)

Each `example` here was a `theorem` in a tier-1 module of `Obend/Law/`: a closed statement, proved by
`decide +kernel` on literal data, that nothing cites. The triage of 2026-11-04 (`Obend/Census.lean`,
`review/DECISIONS-20261031.md`) keeps them as what they are, end-to-end runs worth doing before a
push and not on every library build. Each carries the module it came from and why it is kept. This
file is tier 2: `lake build Teeth`; a plain file, so it sees every definition with its body.
-/

import Obend.Law.Proofs.Claim
import Obend.Law.Proofs.Inherit
import Obend.Law.Proofs.Std

set_option autoImplicit false

-- from Obend/Law/Proofs/Claim.lean:248: refusal witness inside a 18-line fixture; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag encode)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
example :
    checkClaim [("small", smallTotal), ("law", keeps unitTy smallTotal)] (.keeps "small" "law") = true ∧
      checkClaim [("small", smallTotal), ("law", bounded unitTy "total" 5)] (.keeps "small" "law") = false ∧
      checkClaim [("small", smallTotal), ("law", lawOf unitTy (fun _ => okT) (fun _ => okT) (fun _ => okT)
        (fun _ => okT) (fun _ => okT))] (.keeps "small" "law") = false ∧
      checkClaim [("small", .lam (leNat (.get (.bound 1) "total") (natT 5))),
        ("law", keeps unitTy (.lam (leNat (.get (.bound 1) "total") (natT 5))))] (.keeps "small" "law") = false ∧
      Keeps smallTotal (totalIs 5) ∧ ¬ Keeps smallTotal (totalIs 6) ∧ closedB smallTotal = true ∧
      Admits (keeps unitTy smallTotal) (totalIs 0) (totalIs 4) (rqBy "ann" "ann" writeO) ∧
      Refuses (keeps unitTy smallTotal) (totalIs 0) (totalIs 6) (rqBy "ann" "ann" (adoptO "L")) "invariant" :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    boolOf_eval 100 (by decide +kernel),
    fun h => by
      have h' : Evaluates (.app smallTotal (totalIs 6).term) (.boolean false) := boolOf_eval 100 (by decide +kernel)
      have := evaluates_unique h h'
      simp at this,
    by decide +kernel,
    admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Inherit.lean:427: a 9-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
example :
    Admits (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO) ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO) "room" (.label "total over the bound") ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) "board" (.label "not on the allowlist") ∧
      RefusedBy (effective boardLaws) (totalIs 0) (totalIs 9) (rqBy "bob" "ann" writeO) "board2" (.label "not signed by the owner") ∧
      Admits (bounded unitTy "total" 5) (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO) :=
  ⟨admits_of_run 500 (by decide +kernel), refusedBy_of_run 500 (by decide +kernel),
    refusedBy_of_run 500 (by decide +kernel), refusedBy_of_run 500 (by decide +kernel),
    admits_of_run 500 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Inherit.lean:452: a 7-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)
example :
    (Obend.Spec.C4.linearize (boardTree.graph 4) ["board2"] (boardTree.parents "board2")).toOption =
      some (["board2", "board", "room"], none) ∧
    (precedence (boardTree.graph 4) "board2" (boardTree.parents "board2")).toOption = some ["board2", "board", "room"] ∧
    ((effectiveVia (boardTree.graph 4) boardLaws "board2" (boardTree.parents "board2")).toOption.map
        fun t => okB (run 500 (applyLaw t (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO)))) = some true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
end Obend.Law

-- from Obend/Law/Proofs/Std.lean:1034: a 7-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data rowMember)
example :
    Admits (bounded unitTy "total" 5) (totalIs 1) (totalIs 5) (rqBy "ann" "ann" (invokeO 0)) ∧
      Refuses (bounded unitTy "total" 5) (totalIs 1) (totalIs 6) (rqBy "ann" "ann" (adoptO "L"))
        "total over the bound" ∧
      Admits (bounded unitTy "total" 5) (totalIs 9) (totalIs 9) (rqBy "ann" "ann" retireO) :=
  ⟨admits_of_run 200 (by decide +kernel), refuses_of_run 200 (by decide +kernel),
    admits_of_run 200 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Std.lean:1048: a 9-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data rowMember)
example :
    Admits doorLaw (door "shut") (door "shut") (rqBy "ann" "ann" birthO) ∧
      Refuses doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (adoptO "L")) "door does not start at shut" ∧
      Admits doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (invokeO 0)) ∧
      Refuses doorLaw (door "shut") (door "open") (rqBy "ann" "ann" (invokeO 1)) "no edge" ∧
      Refuses doorLaw (door "shut") (door "shut") (rqBy "ann" "ann" writeO) "a machine changes only by its methods" :=
  ⟨admits_of_run 400 (by decide +kernel), refuses_of_run 400 (by decide +kernel),
    admits_of_run 400 (by decide +kernel), refuses_of_run 400 (by decide +kernel),
    refuses_of_run 400 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Std.lean:1064: a 24-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data rowMember)
example :
    Admits councilLaw (council 0 0 (.variant "set" (.natural 0))) (council 0 0 (.variant "set" (.natural 0)))
      (rqBy "ann" "ann" birthO) ∧
      Refuses councilLaw (council 0 3 (.variant "set" (.natural 0))) (council 0 3 (.variant "set" (.natural 0)))
        (rqBy "ann" "ann" (adoptO "L")) "approvals at birth" ∧
      Admits councilLaw (council 0 3 (.variant "laws" (.label "L"))) (council 0 3 (.variant "laws" (.label "L")))
        (rqBy "bob" "ann" (relawO "L")) ∧
      Refuses councilLaw (council 0 1 (.variant "laws" (.label "L"))) (council 0 1 (.variant "laws" (.label "L")))
        (rqBy "bob" "ann" (relawO "L")) "no quorum" ∧
      Refuses councilLaw (council 0 3 (.variant "laws" (.label "L"))) (council 0 3 (.variant "laws" (.label "M")))
        (rqBy "bob" "ann" (relawO "M")) "not the proposal" ∧
      Admits councilLaw (council 0 1 (.variant "set" (.natural 7))) (council 0 3 (.variant "set" (.natural 7)))
        (rqBy "bob" "ann" writeO) ∧
      Admits councilLaw (council 0 3 (.variant "set" (.natural 7))) (council 7 0 (.variant "set" (.natural 7)))
        (rqBy "cy" "ann" writeO) ∧
      Refuses councilLaw (council 0 1 (.variant "set" (.natural 7))) (council 7 0 (.variant "set" (.natural 7)))
        (rqBy "cy" "ann" writeO) "no quorum" ∧
      Refuses councilLaw (council 0 0 (.variant "set" (.natural 0))) (council 0 0 (.variant "set" (.natural 0)))
        (rqBy "ann" "ann" retireO) "quorum" :=
  ⟨admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    refuses_of_run 2000 (by decide +kernel), admits_of_run 2000 (by decide +kernel),
    admits_of_run 2000 (by decide +kernel), refuses_of_run 2000 (by decide +kernel),
    refuses_of_run 2000 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Std.lean:1095: a 9-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data rowMember)
example :
    Admits rateLaw (rated 0 0 0) (rated 0 0 0) (rqBy "ann" "ann" birthO) ∧
      Admits rateLaw (rated 0 0 0) (rated 1 1 0) (rqBy "ann" "ann" writeO) ∧
      Refuses rateLaw (rated 1 1 0) (rated 2 2 0) (rqBy "ann" "ann" writeO) "over the rate limit" ∧
      Refuses rateLaw (rated 0 0 0) (rated 0 0 0) (request "ann" "ann" 5 15 birthO) "window spans epochs" ∧
      Refuses rateLaw (rated 0 1 0) (rated 0 1 0) (rqBy "ann" "ann" (adoptO "L")) "count at birth" :=
  ⟨admits_of_run 1000 (by decide +kernel), admits_of_run 1000 (by decide +kernel),
    refuses_of_run 1000 (by decide +kernel), refuses_of_run 1000 (by decide +kernel),
    refuses_of_run 1000 (by decide +kernel)⟩
end Obend.Law

-- from Obend/Law/Proofs/Std.lean:1119: a 11-line closed evaluation; worth a pre-push run
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data rowMember)
/-- A quorum guarding a RECORD field: a commit of the proposed pair with two approvals is admitted;
the same commit with one approval, or of another pair, is refused; rewriting the pair to an equal
pair is no change and needs no quorum. -/
example :
    Admits pairCouncilLaw (pairCouncil (pairD 0 0) 3 (.variant "set" (pairD 1 2)))
      (pairCouncil (pairD 1 2) 0 (.variant "set" (pairD 1 2))) (rqBy "cy" "ann" writeO) ∧
    Refuses pairCouncilLaw (pairCouncil (pairD 0 0) 1 (.variant "set" (pairD 1 2)))
      (pairCouncil (pairD 1 2) 0 (.variant "set" (pairD 1 2))) (rqBy "cy" "ann" writeO) "no quorum" ∧
    Refuses pairCouncilLaw (pairCouncil (pairD 0 0) 3 (.variant "set" (pairD 1 2)))
      (pairCouncil (pairD 1 3) 0 (.variant "set" (pairD 1 2))) (rqBy "cy" "ann" writeO) "not the proposal" ∧
    Admits pairCouncilLaw (pairCouncil (pairD 1 2) 1 (.variant "set" (pairD 1 2)))
      (pairCouncil (pairD 1 2) 1 (.variant "set" (pairD 1 2))) (rqBy "cy" "ann" writeO) :=
  ⟨admits_of_run 4000 (by decide +kernel), refuses_of_run 4000 (by decide +kernel),
    refuses_of_run 4000 (by decide +kernel), admits_of_run 4000 (by decide +kernel)⟩
end Obend.Law
