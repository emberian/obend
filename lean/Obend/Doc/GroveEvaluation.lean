module
public import Obend.Doc.Grove
import Obend.Core.TermTraverse
import all Obend.Doc.Grove

public section
namespace Obend.Doc.Grove
open Obend.Core.Term Obend.Core.Ty Obend.Core.Machine Obend.Core.Check Obend.Core.MachineTyping
set_option autoImplicit false

open Obend.Core.TermTraverse in
private def sourceHoleBound : Shape → Nat
  | .var _ => 0
  | .bind b => sourceHoleBound b
  | .node tag children =>
    let start := match tag with | .hole n => n + 1 | _ => 0
    (children.map sourceHoleBound).foldl max start

private def Marked.firstFresh : Marked → Nat
  | .code t => sourceHoleBound (Obend.Core.TermTraverse.encode t)
  | .app f a => max f.firstFresh a.firstFresh
  | .hole _ => 0

structure HoleTable where
  first : Nat
  entries : Array ConflictHole

def HoleTable.lookup (table : HoleTable) (id : Nat) : Option ConflictHole :=
  if id < table.first then none else table.entries[id - table.first]?

/-- Lower to real machine syntax. A generated hole carries an index into this
projection's table. The machine's call-by-need stack determines which holes matter. -/
def Marked.lower (first : Nat) : Marked → Array ConflictHole → Term × Array ConflictHole
  | .code term, holes => (term, holes)
  | .hole h, holes => (.hole (first + holes.size) [], holes.push h)
  | .app fn arg, holes =>
    let (f, fs) := fn.lower first holes
    let (a, both) := arg.lower first fs
    (.app f a, both)

inductive Observation where
  | machine (result : Outcome)
  | conflict (hole : ConflictHole) (checkpoint : State) (table : HoleTable)

/-- Intercept a demanded generated hole before Core4's ordinary unresolved-hole
refusal. Other machine outcomes, including capacity and tick suspension, survive. -/
def observe (table : HoleTable) (limits : Limits) : Nat → State → Observation
  | ticks, s =>
    let demanded := match s.control with
      | .evaluate (.hole id _) _ => table.lookup id
      | _ => none
    match demanded with
    | some h => .conflict h s table
    | none =>
      match ticks with
      | 0 => .machine (runBounded limits 0 s)
      | n + 1 =>
        match step limits s with
        | .suspended .ticks next => observe table limits n next
        | other => .machine other

def evaluate (tree : Marked) (limits : Limits) (ticks : Nat) : Observation :=
  let first := tree.firstFresh
  let (term, holes) := tree.lower first #[]
  observe ⟨first, holes⟩ limits ticks (initial term)

theorem demanded_hole (table : HoleTable) (limits : Limits) (ticks : Nat)
    {s : State} {id : Nat} {subst : List Term} {env : Environment} {h : ConflictHole}
    (demand : s.control = .evaluate (.hole id subst) env) (named : table.lookup id = some h) :
    observe table limits ticks s = .conflict h s table := by
  cases ticks <;> simp [observe, demand, named]

theorem evaluate_hole (h : ConflictHole) (limits : Limits) (ticks : Nat) :
    evaluate (.hole h) limits ticks = .conflict h (initial (.hole 0 [])) ⟨0, #[h]⟩ :=
  demanded_hole ⟨0, #[h]⟩ limits ticks rfl (by simp [HoleTable.lookup, Marked.firstFresh])

/-- Each cover is a selectable root hole. The program and other covers stay
independently executable. The default root demand surfaces the first pending cut. -/
def LiveRoot.demand (r : LiveRoot) : Marked :=
  match r.detached with
  | [] => r.program
  | first :: _ => .hole first

theorem covered_demand (r : LiveRoot) {h : ConflictHole} {rest : List ConflictHole}
    (visible : r.detached = h :: rest) (limits : Limits) (ticks : Nat) :
    evaluate r.demand limits ticks = .conflict h (initial (.hole 0 [])) ⟨0, #[h]⟩ := by
  simpa [LiveRoot.demand, visible] using evaluate_hole h limits ticks

/-- The entire observation, including the resulting ground value and heap, is
unchanged by edits outside a closed region. -/
theorem evaluate_disjoint (nodes : Catalog) (a b : StructurePatch)
    (region : Nat → Prop)
    (incident : ∀ e : Edge, region e.port.1 ∨ region e.target →
      (e ∈ liveEdges a ↔ e ∈ liveEdges b))
    (closed : ∀ e ∈ liveEdges a, region e.port.1 → region e.target)
    (p : Port) (ty : Ty) (hp : region p.1) (limits : Limits) (ticks : Nat) :
    evaluate (project nodes (indexEdges (liveEdges a)) nodes.size [] p ty) limits ticks =
    evaluate (project nodes (indexEdges (liveEdges b)) nodes.size [] p ty) limits ticks := by
  rw [project_frame nodes a b region incident closed _ _ _ _ hp]

/-- Discharging a conflict requires a resolved program on every branch, including
arguments that the current evaluation could leave unforced. -/
def Marked.resolve : Marked → Except ConflictHole Term
  | .code t => .ok t
  | .hole h => .error h
  | .app f a => do return .app (← f.resolve) (← a.resolve)

theorem resolved_typed {m : Marked} {ty : Ty} (typed : HasType m ty) {t : Term}
    (ok : m.resolve = .ok t) : PartialTyping {} [] t ty [] := by
  induction typed generalizing t with
  | code h => cases ok; exact h
  | hole => cases ok
  | @app f a r q dom ran _ _ allowed ihf iha =>
    cases hf : f.resolve with
    | error h => simp [Marked.resolve, hf, bind, Except.bind] at ok
    | ok ft =>
      cases ha : a.resolve with
      | error h => simp [Marked.resolve, hf, ha, bind, Except.bind] at ok
      | ok atTerm =>
        simp [Marked.resolve, hf, ha, bind, Except.bind, pure, Except.pure] at ok
        subst t
        exact .application (ihf hf) (iha ha) rfl rfl allowed

/-- Turn a resolved Grove root into the same certified checkpoint accepted by
Vault Replay. A detached edit takes priority even if the main program is closed. -/
def freezeRoot (nodes : Catalog) (valid : nodes.Valid) (entry : Port → Ty) (p : Port)
    (g : StructurePatch) : Except ConflictHole (LiveObject.Checkpoint {} [] (portType nodes entry p)) :=
  let root := liveRoot nodes entry p g
  match root.detached with
  | h :: _ => .error h
  | [] =>
    match eq : root.program.resolve with
    | .error h => .error h
    | .ok t =>
      let source : AnnotatedTerm := ⟨t, fun _ => none, {}⟩
      let checked : Checked source [] :=
        ⟨_, [], resolved_typed (project_typed nodes valid _ _ [] p _) eq, rfl, rfl, rfl⟩
      .ok ⟨initial t, ⟨checked_initial_state source checked⟩⟩

end Obend.Doc.Grove
