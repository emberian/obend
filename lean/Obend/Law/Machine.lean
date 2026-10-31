module
/-
# Obend.Law.Machine — a kernel judges a law by running the machine

A verdict is a sum (`ok {}` or `refused label`), and the machine's output path reads ground Data
through `execute` (`Obend.Core.Data`). A kernel therefore runs a PROBE: the law applied to the old
state, the new state and the request, read by a `case` into a ground observation:

    case (law old new req) [ok ↦ true, refused r ↦ asLabel r]

`asLabel r` is `r` when `r` is a label and is stuck otherwise, so the two observations cannot be
confused: `true` is `ok`, a label `why` is a refusal with reason `why`. `judge` executes the probe
and reads the observation back as a `Verdict`. An effective law (`Obend.Law.Inherit`) refuses with
a record `{by, reason}`; `judgeEffective` runs one probe per field.

What the machine's verdict means is `Obend.Law.Proofs.Machine`: under any policy and resources a
`judge` verdict is the relation's (`Judged`, over `Evaluates`), and with enough resources the
unrestricted `judge` returns it.
-/
public import Obend.Law.Inherit
public import Obend.Core.Data
@[expose] public section
namespace Obend.Law
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Data (Data Budget executeWith)
open Obend.Core.Machine (State Limits)
set_option autoImplicit false

/-! ## The probe -/

/-- `t`, when `t` is a label (`labelEqual t t` faults on anything else). -/
def asLabel (t : Term) : Term := .ifBool (.binary .labelEqual t t) t t

/-- Read a verdict `v` as a ground observation: `true` for `ok`; for `refused r`, `read` (a term
over the payload, `bound 0`) as a label. -/
def readVerdict (read : Term) (v : Term) : Term :=
  .case v [("ok", .boolean true), ("refused", asLabel read)]

/-- The probe of a law with `verdictTy`: the reason itself. -/
def verdictProbe (law : Term) (o n rq : Data) : Term := readVerdict (.bound 0) (applyLaw law o n rq)

/-- The probe of an effective law (`inheritedVerdictTy`): field `field` of the refusal record. -/
def blameProbe (field : String) (law : Term) (o n rq : Data) : Term :=
  readVerdict (.get (.bound 0) field) (applyLaw law o n rq)

/-! ## Verdicts -/

/-- A verdict as the kernel reads it. -/
inductive Verdict where
  | ok
  | refused (why : String)
  deriving DecidableEq, Repr

/-- The probe's observation as a verdict: `true` is `ok`, a label is a refusal. -/
def Verdict.ofData : Data → Option Verdict
  | .boolean true => some .ok
  | .label why => some (.refused why)
  | _ => none

/-- The probe's observation for a verdict. -/
def Verdict.data : Verdict → Data
  | .ok => .boolean true
  | .refused why => .label why

/-- An effective law's verdict as the kernel reads it: `ok`, or refused BY an ancestor. -/
inductive Blame where
  | ok
  | refusedBy (name why : String)
  deriving DecidableEq, Repr

/-! ## The judge: execute the probe -/

/-- Execute `t` and return the extracted Data. -/
def runProbe (policy : State → Bool) (limits : Limits) (budget : Budget) (t : Term) : Option Data :=
  match executeWith policy limits budget t with
  | .ok e => some e.extraction.result.value
  | .error _ => none

/-- The machine's verdict on a law: execute its probe and read the observation. `none` when the run
does not finish within the resources, faults, or observes something else. -/
def judge (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term) (o n rq : Data) :
    Option Verdict :=
  (runProbe policy limits budget (verdictProbe law o n rq)).bind Verdict.ofData

/-- The machine's verdict on an effective law: the `by` probe, and on a refusal the `reason` probe. -/
def judgeEffective (policy : State → Bool) (limits : Limits) (budget : Budget) (law : Term)
    (o n rq : Data) : Option Blame :=
  match (runProbe policy limits budget (blameProbe "by" law o n rq)).bind Verdict.ofData with
  | some .ok => some .ok
  | some (.refused name) =>
    match (runProbe policy limits budget (blameProbe "reason" law o n rq)).bind Verdict.ofData with
    | some (.refused why) => some (.refusedBy name why)
    | _ => none
  | none => none

/-! ## What the relation says -/

/-- The law refuses `old → new` under `req` with a reason that evaluates to the label `why` (a lazy
reason; `Refuses` is the case of a literal one). -/
def RefusesAs (law : Term) (o n rq : Data) (why : String) : Prop :=
  ∃ p, Evaluates (applyLaw law o n rq) (.inject "refused" p) ∧ Evaluates p (.label why)

/-- The verdict the reference semantics gives. -/
def Judged (law : Term) (o n rq : Data) : Verdict → Prop
  | .ok => Admits law o n rq
  | .refused why => RefusesAs law o n rq why

/-- The effective law refuses, its record's `by` the label `name` and its `reason` the label `why`. -/
def BlamedAs (law : Term) (o n rq : Data) (name why : String) : Prop :=
  ∃ p, Evaluates (applyLaw law o n rq) (.inject "refused" p) ∧
    Evaluates (.get p "by") (.label name) ∧ Evaluates (.get p "reason") (.label why)

/-- The effective verdict the reference semantics gives. -/
def BlameJudged (law : Term) (o n rq : Data) : Blame → Prop
  | .ok => Admits law o n rq
  | .refusedBy name why => BlamedAs law o n rq name why

end Obend.Law
