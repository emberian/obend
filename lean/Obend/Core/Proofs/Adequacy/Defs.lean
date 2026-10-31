module
/- The definitions of the source/graph correspondence: meanings, realizations, the graph relation, `rawRun`, budgets. -/
public import Obend.Tactic.Cases
public import Obend.Core.Invariant
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.StepCases
namespace Obend.Core.Proofs.Adequacy
open Obend.Core.Term
open Obend.Core.Machine
open Obend.Core.Invariant
set_option autoImplicit false

/-- A finite independent CBN evaluation derivation. Cost counts demand
constructors, including values; it is a proof measure for partial programs,
not a total evaluator or a promise that Fix terminates. -/
public inductive SourceDerivation : Term → Term → Nat → Prop where
  | value {term : Term} : Value term → SourceDerivation term term 1
  | applicationLambda {function body argument result : Term} {functionCost bodyCost : Nat} :
      SourceDerivation function (.lam body) functionCost →
      SourceDerivation (instantiate body argument) result bodyCost →
      SourceDerivation (.app function argument) result (functionCost+bodyCost+1)
  | applicationSpecification {function descriptor extension argument result : Term} {functionCost bodyCost : Nat} :
      SourceDerivation function (.specification descriptor extension) functionCost →
      SourceDerivation (.app extension argument) result bodyCost →
      SourceDerivation (.app function argument) result (functionCost+bodyCost+1)
  | mix {lower upper result : Term} {cost : Nat} :
      SourceDerivation (mixBody lower upper) result cost → SourceDerivation (.mix lower upper) result (cost+1)
  | fix {spec inherited result : Term} {cost : Nat} :
      SourceDerivation (.app (.app spec (.fix spec inherited)) inherited) result cost →
      SourceDerivation (.fix spec inherited) result (cost+1)
  | reflect {target spec inherited result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.prototype spec inherited) targetCost →
      SourceDerivation spec result resultCost → SourceDerivation (.reflect target) result (targetCost+resultCost+1)
  | metadata {target descriptor extension result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.specification descriptor extension) targetCost →
      SourceDerivation descriptor result resultCost → SourceDerivation (.metadata target) result (targetCost+resultCost+1)
  | project {target spec inherited result : Term} {targetCost resultCost : Nat} :
      SourceDerivation target (.prototype spec inherited) targetCost →
      SourceDerivation inherited result resultCost → SourceDerivation (.project target) result (targetCost+resultCost+1)
  | field {target body result : Term} {fields : List (String × Term)} {name : String} {targetCost resultCost : Nat} :
      SourceDerivation target (.record fields) targetCost →
      fields.find? (fun field => field.1 == name) = some (name,body) →
      SourceDerivation body result resultCost → SourceDerivation (.get target name) result (targetCost+resultCost+1)
  | extend {target : Term} {inherited fields : List (String × Term)} {targetCost : Nat} :
      SourceDerivation target (.record inherited) targetCost →
      SourceDerivation (.extend target fields) (.record (extendFields inherited fields)) (targetCost+1)
  | binary {primitive : Primitive} {left right leftValue rightValue result : Term} {leftCost rightCost : Nat} :
      SourceDerivation left leftValue leftCost → SourceDerivation right rightValue rightCost →
      primitiveResult primitive leftValue rightValue = some result →
      SourceDerivation (.binary primitive left right) result (leftCost+rightCost+1)
  | zero {condition zero body result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.nat 0) conditionCost → SourceDerivation zero result resultCost →
      SourceDerivation (.ifZero condition zero body) result (conditionCost+resultCost+1)
  | successor {condition zero body result : Term} {number conditionCost resultCost : Nat} :
      SourceDerivation condition (.nat (number+1)) conditionCost →
      SourceDerivation (instantiate body (.nat number)) result resultCost →
      SourceDerivation (.ifZero condition zero body) result (conditionCost+resultCost+1)
  | case {scrutinee payload body result : Term} {arms : List (String × Term)} {tag : String}
      {scrutineeCost resultCost : Nat} :
      SourceDerivation scrutinee (.inject tag payload) scrutineeCost →
      arms.find? (fun arm => arm.1 == tag) = some (tag,body) →
      SourceDerivation (instantiate body payload) result resultCost →
      SourceDerivation (.case scrutinee arms) result (scrutineeCost+resultCost+1)
  | ifTrue {condition whenTrue whenFalse result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.boolean true) conditionCost → SourceDerivation whenTrue result resultCost →
      SourceDerivation (.ifBool condition whenTrue whenFalse) result (conditionCost+resultCost+1)
  | ifFalse {condition whenTrue whenFalse result : Term} {conditionCost resultCost : Nat} :
      SourceDerivation condition (.boolean false) conditionCost → SourceDerivation whenFalse result resultCost →
      SourceDerivation (.ifBool condition whenTrue whenFalse) result (conditionCost+resultCost+1)
  | done {value result : Term} {cost : Nat} :
      SourceDerivation value result cost → SourceDerivation (.done value) result (cost+1)

/-- The assignment gives each address a finite source computation; it does NOT
recursively unfold its pointers. In particular a recursive address can denote a
source Fix while its origin denotes the one-step expansion of that same Fix. -/
@[expose] public abbrev AddressMeaning := Address → Term

@[expose] public def environmentSubstitution (meaning : AddressMeaning) (environment : Environment) (index : Nat) : Term :=
  match environment[index]? with
  | some address => meaning address
  | none => .bound index

@[expose] public def closeTerm (meaning : AddressMeaning) (environment : Environment) (term : Term) : Term :=
  match environment with
  | [] => term
  | _::_ => term.substitute (environmentSubstitution meaning environment)

@[expose] public def closeOrigin (meaning : AddressMeaning) (origin : Closure) : Term :=
  closeTerm meaning origin.environment origin.term

@[expose] public def valueMeaning (meaning : AddressMeaning) : RuntimeValue → Term
  | .closure body environment => closeTerm meaning environment (.lam body)
  | .natural value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .record fields => .record (fields.map fun field => (field.1,meaning field.2))
  | .specification metadata extension => .specification (meaning metadata) (meaning extension)
  | .prototype specification target => .prototype (meaning specification) (meaning target)
  | .variant tag payload => .inject tag (meaning payload)

/- The evaluating phase retains its source meaning. A cache additionally has
an actual independent reference evaluation, rather than an arbitrary cached
scalar. Stable origins let the same relation survive the phase change. -/
/-- Each allocated graph name denotes a closed source computation. The
assignment remains finite syntax even when these computations contain Fix. -/
@[expose] public def MeaningsScoped (bound : Nat) (meaning : AddressMeaning) : Prop :=
  ∀ address, address < bound → Scoped 0 (meaning address)

@[expose] public def CellRealizes (meaning : AddressMeaning) (address : Address) (cell : Cell) : Prop :=
  Steps (meaning address) (closeOrigin meaning (cellOrigin cell)) ∧
    match cell with
    | .cached _ value => Evaluates (meaning address) (valueMeaning meaning value)
    | _ => True

@[expose] public def HeapRealizes (meaning : AddressMeaning) (heap : Array Cell) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellRealizes meaning address cell

@[expose] public def frameMeaning (meaning : AddressMeaning) (frame : Frame) (hole : Term) : Term :=
  match frame with
  | .argument term environment => .app hole (closeTerm meaning environment term)
  | .update _ => hole
  | .field name => .get hole name
  | .reflect => .reflect hole
  | .metadata => .metadata hole
  | .project => .project hole
  | .extend fields environment => .extend hole
      (fields.map fun field => (field.1,closeTerm meaning environment field.2))
  | .condition zero successorBody environment => .ifZero hole
      (closeTerm meaning environment zero)
      (successorBody.substitute (liftSubstitution (environmentSubstitution meaning environment)))
  | .binaryLeft primitive right environment => .binary primitive hole (closeTerm meaning environment right)
  | .binaryRight primitive left => .binary primitive (valueMeaning meaning left) hole
  | .case arms environment => .case hole
      (arms.map fun arm => (arm.1,arm.2.substitute (liftSubstitution (environmentSubstitution meaning environment))))
  | .ifBool whenTrue whenFalse environment => .ifBool hole
      (closeTerm meaning environment whenTrue) (closeTerm meaning environment whenFalse)

@[expose] public def stackMeaning (meaning : AddressMeaning) (stack : List Frame) (hole : Term) : Term :=
  stack.foldl (fun prior frame => frameMeaning meaning frame prior) hole

@[expose] public def controlMeaning (meaning : AddressMeaning) : Control → Option Term
  | .evaluate term environment => some (closeTerm meaning environment term)
  | .enter address => some (meaning address)
  | .returned value | .complete value => some (valueMeaning meaning value)
  | .blackhole _ | .refused _ => none
  -- A yielded program means its stuck source redex `perform plan`.
  | .yielded plan => some (.perform (meaning plan))

/-- A dynamic demand focus reads the actual cell phase. The fixed source
address meaning remains in HeapRealizes and local update provenance; this
focus exposes already justified unfolding/cache reductions at pointer entry. -/
@[expose] public def enteredFocus (meaning : AddressMeaning) (heap : Array Cell) : Control → Option Term
  | .enter address => match heap[address]? with
      | some (.suspended origin) => some (closeOrigin meaning origin)
      | some (.cached _ value) => some (valueMeaning meaning value)
      | some (.evaluating _) | none => none
  | control => controlMeaning meaning control

/-- Every active update carries its own demand-segment source evaluation.
Erasing update frames would lose the LOCAL proof required when writing a cache:
a whole-program reduction alone cannot justify that heap-cell result. -/
@[expose] public def StackRealizes (meaning : AddressMeaning) (root focus : Term) : List Frame → Prop
  | [] => Steps root focus
  | .update address::rest =>
      Steps (meaning address) focus ∧ StackRealizes meaning root (meaning address) rest
  | frame::rest => StackRealizes meaning root (frameMeaning meaning frame focus) rest

/-- The concrete heap/continuation relation retains source meanings at shared
addresses and local provenance for every active update. Initialization,
running/finished transition preservation and ground soundness are proved
below; no source-evaluator oracle is a field of this relation. -/
@[expose] public def GraphRepresents (state : State) (source : Term) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ FinalStackInvariant state ∧ ∃ meaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
    ∃ residual, controlMeaning meaning state.control = some residual ∧
      StackRealizes meaning source residual state.stack

/-- The source contexts that start a lexical demand without allocating heap
cells. This enumerates actual syntax and actual machine frames. -/
public inductive DemandContext where
  | argument (term : Term)
  | field (name : String)
  | reflect | metadata | project
  | extend (fields : List (String × Term))
  | condition (zero successorBody : Term)
  | binary (primitive : Primitive) (right : Term)
  | case (arms : List (String × Term))
  | ifBool (whenTrue whenFalse : Term)

@[expose] public def DemandContext.term : DemandContext → Term → Term
  | .argument arg, hole => .app hole arg
  | .field name, hole => .get hole name
  | .reflect, hole => .reflect hole
  | .metadata, hole => .metadata hole
  | .project, hole => .project hole
  | .extend fields, hole => .extend hole fields
  | .condition zero successorBody, hole => .ifZero hole zero successorBody
  | .binary primitive right, hole => .binary primitive hole right
  | .case arms, hole => .case hole arms
  | .ifBool whenTrue whenFalse, hole => .ifBool hole whenTrue whenFalse

@[expose] public def DemandContext.frame : DemandContext → Environment → Frame
  | .argument arg, environment => .argument arg environment
  | .field name, _ => .field name
  | .reflect, _ => .reflect
  | .metadata, _ => .metadata
  | .project, _ => .project
  | .extend fields, environment => .extend fields environment
  | .condition zero successorBody, environment => .condition zero successorBody environment
  | .binary primitive right, environment => .binaryLeft primitive right environment
  | .case arms, environment => .case arms environment
  | .ifBool whenTrue whenFalse, environment => .ifBool whenTrue whenFalse environment

public inductive ImmediateValue where
  | closure (body : Term)
  | natural (number : Nat)
  | boolean (value : Bool)
  | label (name : String)

@[expose] public def ImmediateValue.term : ImmediateValue → Term
  | .closure body => .lam body
  | .natural number => .nat number
  | .boolean value => .boolean value
  | .label name => .label name

@[expose] public def ImmediateValue.runtime : ImmediateValue → Environment → RuntimeValue
  | .closure body, environment => .closure body environment
  | .natural number, _ => .natural number
  | .boolean value, _ => .boolean value
  | .label name, _ => .label name



public inductive ObjectAccess where
  | reflect | metadata | project

@[expose] public def ObjectAccess.frame : ObjectAccess → Frame
  | .reflect => .reflect | .metadata => .metadata | .project => .project

@[expose] public def ObjectAccess.value : ObjectAccess → Address → Address → RuntimeValue
  | .reflect, first, second => .prototype first second
  | .metadata, first, second => .specification first second
  | .project, first, second => .prototype first second

@[expose] public def ObjectAccess.address : ObjectAccess → Address → Address → Address
  | .reflect, first, _ => first | .metadata, first, _ => first | .project, _, second => second





@[expose] public def extendMeaning (meaning : AddressMeaning) (address : Address) (term : Term) : AddressMeaning :=
  fun index => if index = address then term else meaning index

public inductive PairObject where
  | specification | prototype

@[expose] public def PairObject.term : PairObject → Term → Term → Term
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second

@[expose] public def PairObject.value : PairObject → Address → Address → RuntimeValue
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second



@[expose] public def allocationLoop (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) : Array Cell × List (String × Address) :=
  fields.foldl (fun pair field =>
    (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)) (heap,prior)

/-- Running and finished controls have a source focus. Faults and blackholes
are retained operational outcomes and are deliberately not source values. -/
@[expose] public def ResultControl : Control → Prop
  | .evaluate _ _ | .enter _ | .returned _ | .complete _ => True
  -- A yield is not a pure result: it is a whole-program step taken only by a
  -- resume, so (like a fault) it never appears on a terminating pure trace.
  | .refused _ | .blackhole _ | .yielded _ => False

/-- Actual thunk birth provenance: ordinary captures precede their address;
the sole same-address capture is the exact body installed by tied Fix. Cached
RESULT edges may point forward; the permanent SOURCE origin obeys this law. -/
@[expose] public def OriginBorn (address : Address) (origin : Closure) : Prop :=
  EnvironmentValid address origin.environment ∨
    ∃ (spec inherited : Term) (captured : Environment),
      origin.environment = address::captured ∧ EnvironmentValid address captured ∧
      origin.term = .app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)

@[expose] public def HeapOriginsBorn (heap : Array Cell) : Prop :=
  ∀ address cell, heap[address]? = some cell → OriginBorn address (cellOrigin cell)

/-- A graph representation at a specified permanent source assignment. This
interface retains address-name identity for reachability and update budgets. -/
@[expose] public def GraphRepresentsBy (meaning : AddressMeaning) (state : State) (source : Term) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ FinalStackInvariant state ∧
    MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
    ∃ residual, controlMeaning meaning state.control = some residual ∧
      StackRealizes meaning source residual state.stack

@[expose] public def SourceNamesAgree (before : State) (meaning next : AddressMeaning) : Prop :=
  ∀ address, address < before.heap.size → meaning address = next address

/-- The actual semantic transition consumes a continuation prefix and one
independent source reduction; remaining heap names retain their prefix. -/
@[expose] public def SourceDispatch (meaning next : AddressMeaning) (state : State) : Prop :=
  ∃ consumed before after,
    controlMeaning meaning state.control = some before ∧
    controlMeaning next (stepRaw state).control = some after ∧
    state.stack = consumed ++ (stepRaw state).stack ∧
    Step (stackMeaning meaning consumed before) after

/-- Finite raw execution is independent of capacity. Resource completeness
below computes a sufficient bound from this real transition trace; it does not
assert that a source computation terminates. -/
@[expose] public def rawRun : Nat → State → State
  | 0,state => state
  | ticks+1,state => rawRun ticks (stepRaw state)

/-- Pointer entry and bare variable lookup are administrative demand work.
The endpoint can be a genuine source constructor, returned/cache value, or an
explicit fault/blackhole; terminating this segment does not label a blackhole
as source divergence. -/
@[expose] public def DemandAdministrative (state : State) : Prop :=
  match state.control with
  | .enter _ | .evaluate (.bound _) _ => True
  | _ => False

@[expose] public def DemandAdministrationHalts (state : State) : Prop :=
  ∃ ticks, ¬ DemandAdministrative (rawRun ticks state)

@[expose] public def AdministrativeBudget (cost cap : Nat) : Prop :=
  ∀ (meaning : AddressMeaning) (state : State), HeapRealizes meaning state.heap → HeapOriginsBorn state.heap →
    (∀ (address : Address) (result : Term), state.control = .enter address → address+1 ≤ cap →
      SourceDerivation (meaning address) result cost → DemandAdministrationHalts state) ∧
    (∀ (term : Term) (environment : Environment) (result : Term), state.control = .evaluate term environment →
      EnvironmentValid cap environment → SourceDerivation (closeTerm meaning environment term) result cost →
      DemandAdministrationHalts state)

@[expose] public def retainedState : Outcome → State
  | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state
  | .yielded _ state => state

@[expose] public def TraceFits (limits : Limits) : Nat → State → Prop
  | 0,_ => True
  | ticks+1,state =>
      (stepRaw state).heap.size ≤ limits.heap ∧
      (stepRaw state).stack.length ≤ limits.stack ∧ TraceFits limits ticks (stepRaw state)

/-- Explicit maximum heap/stack bounds along the requested finite trace. Tick
bound is its length. A resource suspension requires larger bounds and keeps the
exact resumable state; this maximum is a semantic bound, not a native allocator. -/
@[expose] public def traceLimits : Nat → State → Limits
  | 0,_ => ⟨0,0⟩
  | ticks+1,state =>
      let next := stepRaw state
      let later := traceLimits ticks next
      ⟨max next.heap.size later.heap,max next.stack.length later.stack⟩

@[expose] public def observationTerm : Observation → Term
  | .natural number => .nat number
  | .boolean value => .boolean value
  | .label name => .label name

@[expose] public def observationRuntime : Observation → RuntimeValue
  | .natural number => .natural number
  | .boolean value => .boolean value
  | .label name => .label name

/-- An actual uninterrupted evaluating interval starts by entering this exact
suspended origin. Every later member is an actual transition still carrying
that same evaluating cell, rather than an assumed phase marker. -/
public inductive EvaluatingSegment (address : Address) (origin : Closure) (entered : State) : State → Prop where
  | start : entered.control = .enter address → entered.heap[address]? = some (.suspended origin) →
      EvaluatingSegment address origin entered (stepRaw entered)
  | next {state : State} : EvaluatingSegment address origin entered state →
      (stepRaw state).heap[address]? = some (.evaluating origin) →
      EvaluatingSegment address origin entered (stepRaw state)

/-- A cap for the exact addresses retained by the current lexical closure. -/
@[expose] public def captureCap : Environment → Nat
  | [] => 0
  | address::rest => max (address+1) (captureCap rest)

/-- Demand focus also exposes evaluating entry as its permanent name, so a
finite-budget active-update invariant can rule it out instead of silently
omitting the blackhole-producing state. -/
@[expose] public def budgetFocus (meaning : AddressMeaning) (state : State) : Option Term :=
  match state.control with
  | .enter address => match state.heap[address]? with
      | some (.suspended origin) => some (closeOrigin meaning origin)
      | some (.cached _ value) => some (valueMeaning meaning value)
      | some (.evaluating _) | none => some (meaning address)
  | control => controlMeaning meaning control

@[expose] public def budgetCap (state : State) : Nat :=
  match state.control with
  | .evaluate _ environment => captureCap environment
  | .enter address => match state.heap[address]? with
      | some (.suspended origin) => captureCap origin.environment
      | some (.cached _ _) => 0
      | some (.evaluating _) | none => address+1
  | _ => 0

/-- Universal partial-budget invariant: undemanded divergent names need no
finite evaluation. Every FINITE pending-name/current-demand pair satisfies
strict semantic decrease or equal-cost lexical cap confinement. -/
@[expose] public def DemandSafety (meaning : AddressMeaning) (state : State) : Prop :=
  ∀ (address : Address) (origin : Closure), state.heap[address]? = some (.evaluating origin) →
    ∀ (nameValue : Term) (nameCost : Nat), SourceDerivation (meaning address) nameValue nameCost →
      ∀ focus, budgetFocus meaning state = some focus →
        ∀ (focusValue : Term) (focusCost : Nat), SourceDerivation focus focusValue focusCost →
          focusCost < nameCost ∨ (focusCost = nameCost ∧ budgetCap state ≤ address)

/-- The closed lazy Fix program of `lazy_fixed_function`. -/
@[expose] public def lazyFixedSource : Term := .fix (.lam (.lam (.lam (.bound 0)))) (.nat 7)

end Obend.Core.Proofs.Adequacy
