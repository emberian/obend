module
/-
# Obend.Core.MachineReify — DAG-Sharing `Machine.State → Core.Term` Decompilation & Adequacy
Sharing-preserving readback (`reifyMachineDag`) from `Obend.Core.Machine.State` into `Core.Term`
up to `Equiv.IEquiv`: topological `letChain` DAG spine across `.suspended`/`.evaluating`/`.cached`
cells, `.update` frame-zipper splitting (`plugStackSplittingUpdates`), bidirectional `unshift0?`
`.fix` knot recovery (`recoverFixKnot?`), and `Evaluates`/`Yields`/`resume` adequacy.
-/
public import Obend.Core.Machine
public import Obend.Core.TermTraverse
public import Obend.Equiv.Yields
public section
namespace Obend.Core.MachineReify
open Obend.Core.Term Obend.Core.Machine Obend.Equiv
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Scoped encode encode_injective encode_rename rename_comp
  scoped_rename_identity scoped_substitute_identity)
set_option autoImplicit false
deriving instance DecidableEq for Refusal
/-! ## 1. Structured Reification Refusals & Renaming-Invariant AST Node Metric -/

inductive ReifyError where
  | machineRefused (reason : Refusal)
  | machineBlackhole (address : Address)
  | danglingAddress (address : Address)
  | unboundVariable (index : Nat)
  | unrecoverableCycle (address : Address)
  | fuelExhausted
  | yieldUnderSharedUpdate
  deriving Repr, DecidableEq
def treeNodeCount {Tag : Type} : Tree Tag → Nat
  | .var _ => 1
  | .bind b => 1 + treeNodeCount b
  | .node _ cs => 1 + cs.foldl (fun acc c => acc + treeNodeCount c) 0
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
@[expose] def termNodeCount (t : Term) : Nat := treeNodeCount (encode t)
theorem treeNodeCount_pos {Tag : Type} (t : Tree Tag) : 1 ≤ treeNodeCount t := by
  cases t <;> simp [treeNodeCount] <;> omega
theorem termNodeCount_pos (t : Term) : 1 ≤ termNodeCount t := treeNodeCount_pos (encode t)
theorem treeNodeCount_rename {Tag : Type} (f : Nat → Nat) (t : Tree Tag) :
    treeNodeCount (Tree.rename f t) = treeNodeCount t := by
  induction t using Tree.inductionOn generalizing f with
  | var _ => simp [Tree.rename, Tree.traverse, treeNodeCount]
  | bind body ih => simp only [Tree.rename, Tree.traverse, treeNodeCount, ih (liftRename f)]
  | node _ cs ih =>
    simp only [Tree.rename, Tree.traverse, treeNodeCount]
    suffices h : ∀ (xs : List (Tree Tag)) (init : Nat),
        (∀ c ∈ xs, treeNodeCount (Tree.rename f c) = treeNodeCount c) →
        (xs.map (Tree.traverse (fun g i => .var (g i)) liftRename f)).foldl
          (fun acc c => acc + treeNodeCount c) init =
          xs.foldl (fun acc c => acc + treeNodeCount c) init by
      rw [h cs 0 (fun c hc => ih c hc f)]
    intro xs; induction xs with
    | nil => intro _ _; rfl
    | cons x rest ihx =>
      intro init hx; simp only [List.map_cons, List.foldl_cons]
      rw [show Tree.traverse (fun g i => .var (g i)) liftRename f x = Tree.rename f x from rfl,
        hx x List.mem_cons_self]
      exact ihx (init + treeNodeCount x) (fun y hy => hx y (List.mem_cons_of_mem x hy))
theorem termNodeCount_rename (f : Nat → Nat) (t : Term) :
    termNodeCount (t.rename f) = termNodeCount t := by
  simp [termNodeCount, encode_rename, treeNodeCount_rename]
/-! ## 2. Bidirectional De Bruijn `unshift0?` & Cycle-Safe `.fix` Knot Recovery -/

@[expose] def unshift0? (u : Term) : Option Term :=
  if Tree.all (fun j => j != 0) (encode u) then some (u.rename Nat.pred) else none
private theorem all_true_univ {Tag : Type} (t : Tree Tag) : Tree.All (fun _ => True) t := by
  induction t using Tree.inductionOn with
  | var _ => simp [Tree.All]
  | bind body ih =>
    simp only [Tree.All]
    exact (Tree.all_congr body (fun _ => True) _ (fun i => by cases i <;> simp)).mp ih
  | node _ _ ih =>
    simp only [Tree.All]
    exact ih
theorem unshift0?_rename_succ (t : Term) : unshift0? (t.rename Nat.succ) = some t := by
  unfold unshift0?
  have hall : Tree.all (fun j => j != 0) (encode (t.rename Nat.succ)) = true := by
    rw [encode_rename, Tree.all_eq_true]
    exact Tree.all_rename (encode t) (fun _ => True) (fun j => (j != 0) = true)
      (all_true_univ (encode t)) Nat.succ (fun _ _ => rfl)
  simp only [hall, ite_true, rename_comp]; congr 1; apply encode_injective
  rw [encode_rename, show (fun i : Nat => i.succ.pred) = id from rfl]
  exact Tree.rename_id (encode t)
theorem unshift0?_sound {u t : Term} (h : unshift0? u = some t) : t.rename Nat.succ = u := by
  unfold unshift0? at h
  split at h
  · rename_i hall; cases h; rw [rename_comp]; apply encode_injective; rw [encode_rename]
    have hAllProp := (Tree.all_eq_true (encode u) (fun j => j != 0)).1 hall
    refine (Tree.rename_congr_on (encode u) (fun j => (j != 0) = true) hAllProp
      (fun i => Nat.succ (Nat.pred i)) id ?_).trans (Tree.rename_id (encode u))
    intro i hi; cases i with | zero => simp at hi | succ _ => rfl
  · cases h
@[expose] def recoverFixKnot? (addr : Address) (origin : Closure) :
    Option (Term × Term × Environment) :=
  match origin.environment, origin.term with
  | selfAddr :: outerEnv, .app (.app specShifted (.bound 0)) inhShifted =>
      if selfAddr == addr then
        match unshift0? specShifted, unshift0? inhShifted with
        | some spec, some inh => some (spec, inh, outerEnv)
        | _, _ => none
      else none
  | _, _ => none
theorem recoverFixKnot_complete (addr : Address) (spec inherited : Term) (outerEnv : Environment) :
    recoverFixKnot? addr
      ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ), addr :: outerEnv⟩ =
      some (spec, inherited, outerEnv) := by
  simp [recoverFixKnot?, unshift0?_rename_succ]
theorem recoverFixKnot?_inhabited (addr : Address) (s i : Term) (e : Environment) :
    ∃ org, recoverFixKnot? addr org = some (s, i, e) := ⟨_, recoverFixKnot_complete addr s i e⟩
theorem recoverFixKnot_sound {addr : Address} {origin : Closure}
    {spec inherited : Term} {outerEnv : Environment}
    (h : recoverFixKnot? addr origin = some (spec, inherited, outerEnv)) :
    origin = ⟨.app (.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ),
      addr :: outerEnv⟩ := by
  unfold recoverFixKnot? at h; rcases origin with ⟨tm, env⟩
  cases env with
  | nil => simp at h
  | cons selfAddr rest =>
    cases tm <;> try simp at h
    rename_i fn arg; cases fn <;> try simp at h
    rename_i fn2 mid; cases mid <;> try simp at h
    rename_i idx; cases idx with
    | zero =>
      simp at h; rcases h with ⟨rfl, hmatch⟩
      cases hs : unshift0? fn2 <;> cases hi : unshift0? arg <;> rw [hs, hi] at hmatch <;> simp at hmatch
      rcases hmatch with ⟨rfl, rfl, rfl⟩; rw [unshift0?_sound hs, unshift0?_sound hi]
    | succ _ => simp at h
/-! ## 3. Topological `let`-DAG Chain (`letChain`) & Root `Step.beta` Adequacy -/

@[expose] def letChain : List Term → Term → Term
  | [], body => body
  | rhs :: rest, body => .app (.lam (letChain rest body)) rhs
theorem termNodeCount_letChain (rhss : List Term) (body : Term) :
    termNodeCount (letChain rhss body) =
      termNodeCount body + rhss.foldl (fun acc r => acc + 2 + termNodeCount r) 0 := by
  induction rhss generalizing body with
  | nil => simp [letChain]
  | cons rhs rest ih =>
    have happ : termNodeCount (.app (.lam (letChain rest body)) rhs) =
        2 + termNodeCount (letChain rest body) + termNodeCount rhs := by
      simp [termNodeCount, encode, treeNodeCount]; omega
    simp only [letChain, happ, ih, List.foldl_cons]
    have hshift : ∀ (xs : List Term) (init : Nat),
        xs.foldl (fun acc r => acc + 2 + termNodeCount r) init =
          init + xs.foldl (fun acc r => acc + 2 + termNodeCount r) 0 := by
      intro xs; induction xs with
      | nil => intro init; simp
      | cons y ys ihy =>
        intro init; simp only [List.foldl_cons]
        rw [ihy (init + 2 + termNodeCount y), ihy (0 + 2 + termNodeCount y)]; omega
    rw [hshift rest (0 + 2 + termNodeCount rhs)]; omega
def liftSubstN : Nat → (Nat → Term) → (Nat → Term)
  | 0, σ => σ
  | k + 1, σ => liftSubstitution (liftSubstN k σ)
def substLetChain : Nat → (Nat → Term) → List Term → List Term
  | _, _, [] => []
  | depth, σ, rhs :: rest =>
      rhs.substitute (liftSubstN depth σ) :: substLetChain (depth + 1) σ rest
@[simp] theorem substLetChain_length (depth : Nat) (σ : Nat → Term) (rhss : List Term) :
    (substLetChain depth σ rhss).length = rhss.length := by
  induction rhss generalizing depth with
  | nil => rfl
  | cons _ rest ih => simp [substLetChain, ih]
theorem letChain_substitute (rhss : List Term) (body : Term) (depth : Nat) (σ : Nat → Term) :
    (letChain rhss body).substitute (liftSubstN depth σ) =
      letChain (substLetChain depth σ rhss) (body.substitute (liftSubstN (depth + rhss.length) σ)) := by
  induction rhss generalizing depth with
  | nil => simp [letChain, substLetChain]
  | cons rhs rest ih =>
    simp only [letChain, Term.substitute, substLetChain, List.length_cons]
    have hlift : liftSubstitution (liftSubstN depth σ) = liftSubstN (depth + 1) σ := rfl
    rw [hlift, ih (depth + 1), show depth + 1 + rest.length = depth + (rest.length + 1) by omega]
def singleSubst (arg : Term) : Nat → Term
  | 0 => arg
  | n + 1 => .bound n
def evalLetChainAux : Nat → List Term → Term → Term
  | 0, _, body | _ + 1, [], body => body
  | fuel + 1, rhs :: rest, body =>
      let σ₀ := singleSubst rhs
      evalLetChainAux fuel (substLetChain 0 σ₀ rest) (body.substitute (liftSubstN rest.length σ₀))
@[expose] def evalLetChain (rhss : List Term) (body : Term) : Term :=
  evalLetChainAux rhss.length rhss body
theorem letChain_steps_evalLetChain (rhss : List Term) (body : Term) :
    Steps (letChain rhss body) (evalLetChain rhss body) := by
  unfold evalLetChain
  suffices h : ∀ (n : Nat) (rs : List Term) (b : Term), rs.length = n →
      Steps (letChain rs b) (evalLetChainAux n rs b) from h rhss.length rhss body rfl
  intro n; induction n with
  | zero => intro rs b hlen; cases rs <;> first | exact .refl b | simp at hlen
  | succ k ih =>
    intro rs b hlen; cases rs with
    | nil => simp at hlen
    | cons rhs rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [letChain, evalLetChainAux]
      have hbeta : Step (.app (.lam (letChain rest b)) rhs)
          (instantiate (letChain rest b) rhs) := Step.beta _ _
      have hinst : instantiate (letChain rest b) rhs =
          letChain (substLetChain 0 (singleSubst rhs) rest)
            (b.substitute (liftSubstN rest.length (singleSubst rhs))) := by
        change (letChain rest b).substitute (liftSubstN 0 (singleSubst rhs)) = _
        simpa using letChain_substitute rest b 0 (singleSubst rhs)
      rw [hinst] at hbeta
      exact .next hbeta (ih _ _ (by simp [hlen]))
theorem letChain_iequiv_evalLetChain (rhss : List Term) (body : Term) :
    IEquiv (letChain rhss body) (evalLetChain rhss body) :=
  iequiv_of_ahead (Ahead.ofStepsRefl (letChain_steps_evalLetChain rhss body))
/-! ## 4. Commutation of `evalLetChain` with Values, Closed Terms, and `SourceFrame` Contexts -/

def substSourceFrame (σ : Nat → Term) : SourceFrame → SourceFrame
  | .application arg => .application (arg.substitute σ)
  | .field name => .field name
  | .extend fs => .extend (fs.map fun f => (f.1, f.2.substitute σ))
  | .binaryLeft op r => .binaryLeft op (r.substitute σ)
  | .binaryRight op l => .binaryRight op (l.substitute σ)
  | .condition z s => .condition (z.substitute σ) (s.substitute (liftSubstitution σ))
  | .case arms => .case (arms.map fun f => (f.1, f.2.substitute (liftSubstitution σ)))
  | .ifBool wt wf => .ifBool (wt.substitute σ) (wf.substitute σ)
  | .reflect => .reflect | .metadata => .metadata | .project => .project
  | .split names fn => .split names (fn.substitute σ)
theorem substSourceFrame_plug (σ : Nat → Term) (f : SourceFrame) (hole : Term) :
    (f.plug hole).substitute σ = (substSourceFrame σ f).plug (hole.substitute σ) := by
  cases f <;> simp [SourceFrame.plug, substSourceFrame, Term.substitute]
theorem plug_substitute (σ : Nat → Term) (ctx : List SourceFrame) (hole : Term) :
    (plug ctx hole).substitute σ = plug (ctx.map (substSourceFrame σ)) (hole.substitute σ) := by
  induction ctx generalizing hole with
  | nil => rfl
  | cons f rest ih =>
    change (plug rest (f.plug hole)).substitute σ =
      plug (rest.map (substSourceFrame σ)) ((substSourceFrame σ f).plug (hole.substitute σ))
    rw [ih (f.plug hole), substSourceFrame_plug]
theorem value_substitute (σ : Nat → Term) {v : Term} (hv : Value v) : Value (v.substitute σ) := by
  cases hv <;> simp only [Term.substitute]
  · exact .function _
  · exact .natural _
  · exact .boolean _
  · exact .label _
  · exact .record _
  · exact .specification _ _
  · exact .prototype _ _
  · exact .inject _ _
def ValidYieldCtx (ctx : List SourceFrame) : Prop :=
  ∀ f ∈ ctx, ∀ op l, f = .binaryRight op l → Value l
theorem validYieldCtx_map_subst (σ : Nat → Term) {ctx : List SourceFrame}
    (h : ValidYieldCtx ctx) : ValidYieldCtx (ctx.map (substSourceFrame σ)) := by
  intro f' hf' op l' heq; obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hf'
  cases f <;> simp [substSourceFrame] at heq
  rcases heq with ⟨rfl, rfl⟩; exact value_substitute σ (h _ hf _ _ rfl)
def evalLetChainCtxAux : Nat → List Term → List SourceFrame → List SourceFrame
  | 0, _, ctx | _ + 1, [], ctx => ctx
  | fuel + 1, rhs :: rest, ctx =>
      let σ₀ := singleSubst rhs
      evalLetChainCtxAux fuel (substLetChain 0 σ₀ rest)
        (ctx.map (substSourceFrame (liftSubstN rest.length σ₀)))
def evalLetChainCtx (rhss : List Term) (ctx : List SourceFrame) : List SourceFrame :=
  evalLetChainCtxAux rhss.length rhss ctx
private theorem evalLetChain_ind {P : Term → Prop} (rhss : List Term) (t : Term)
    (h0 : P t) (hstep : ∀ σ u, P u → P (u.substitute σ)) : P (evalLetChain rhss t) := by
  unfold evalLetChain
  suffices gen : ∀ (n : Nat) (rs : List Term) (u : Term), rs.length = n → P u →
      P (evalLetChainAux n rs u) from gen rhss.length rhss t rfl h0
  intro n; induction n with
  | zero => intro _ _ _ hu; exact hu
  | succ _ ih =>
    intro rs u hlen hu; cases rs with
    | nil => simp at hlen
    | cons _ rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact ih _ _ (by rw [substLetChain_length, hlen]) (hstep _ u hu)
theorem evalLetChain_plug (rhss : List Term) (ctx : List SourceFrame) (hole : Term) :
    evalLetChain rhss (plug ctx hole) =
      plug (evalLetChainCtx rhss ctx) (evalLetChain rhss hole) := by
  unfold evalLetChain evalLetChainCtx
  suffices h : ∀ (n : Nat) (rs : List Term) (c : List SourceFrame) (u : Term), rs.length = n →
      evalLetChainAux n rs (plug c u) =
        plug (evalLetChainCtxAux n rs c) (evalLetChainAux n rs u) from
    h rhss.length rhss ctx hole rfl
  intro n; induction n with
  | zero => intro _ _ _ _; rfl
  | succ _ ih =>
    intro rs c u hlen; cases rs with
    | nil => simp at hlen
    | cons _ rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [evalLetChainAux, evalLetChainCtxAux]
      rw [plug_substitute, ih _ _ _ (by rw [substLetChain_length, hlen])]
theorem evalLetChain_perform (rhss : List Term) (plan : Term) :
    evalLetChain rhss (.perform plan) = .perform (evalLetChain rhss plan) := by
  unfold evalLetChain
  suffices h : ∀ (n : Nat) (rs : List Term) (p : Term), rs.length = n →
      evalLetChainAux n rs (.perform p) = .perform (evalLetChainAux n rs p) from
    h rhss.length rhss plan rfl
  intro n; induction n with
  | zero => intro _ _ _; rfl
  | succ _ ih =>
    intro rs p hlen; cases rs with
    | nil => simp at hlen
    | cons _ rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [evalLetChainAux, Term.substitute]
      exact ih _ _ (by rw [substLetChain_length, hlen])
theorem evalLetChain_value (rhss : List Term) {v : Term} (hv : Value v) :
    Value (evalLetChain rhss v) :=
  evalLetChain_ind rhss v hv (fun σ _ hu => value_substitute σ hu)
theorem evalLetChain_nat (rhss : List Term) (m : Nat) : evalLetChain rhss (.nat m) = .nat m :=
  evalLetChain_ind (P := fun x => x = .nat m) rhss (.nat m) rfl
    (fun _ _ hu => by rw [hu]; simp [Term.substitute])
theorem evalLetChain_boolean (rhss : List Term) (b : Bool) :
    evalLetChain rhss (.boolean b) = .boolean b :=
  evalLetChain_ind (P := fun x => x = .boolean b) rhss (.boolean b) rfl
    (fun _ _ hu => by rw [hu]; simp [Term.substitute])
theorem evalLetChain_label (rhss : List Term) (s : String) :
    evalLetChain rhss (.label s) = .label s :=
  evalLetChain_ind (P := fun x => x = .label s) rhss (.label s) rfl
    (fun _ _ hu => by rw [hu]; simp [Term.substitute])
theorem evalLetChain_closed (rhss : List Term) {t : Term} (hClosed : Scoped 0 t) :
    evalLetChain rhss t = t :=
  evalLetChain_ind (P := fun x => x = t) rhss t rfl (fun σ _ hu => by
    rw [hu]
    exact scoped_substitute_identity t 0 hClosed σ (fun _ hi => absurd hi (Nat.not_lt_zero _)))
theorem evalLetChainCtx_validYield (rhss : List Term) {ctx : List SourceFrame}
    (h : ValidYieldCtx ctx) : ValidYieldCtx (evalLetChainCtx rhss ctx) := by
  unfold evalLetChainCtx
  suffices gen : ∀ (n : Nat) (rs : List Term) (c : List SourceFrame), rs.length = n →
      ValidYieldCtx c → ValidYieldCtx (evalLetChainCtxAux n rs c) from
    gen rhss.length rhss ctx rfl h
  intro n; induction n with
  | zero => intro _ _ _ hc; exact hc
  | succ _ ih =>
    intro rs c hlen hc; cases rs with
    | nil => simp at hlen
    | cons _ rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact ih _ _ (by rw [substLetChain_length, hlen]) (validYieldCtx_map_subst _ hc)
theorem plug_yields_perform {ctx : List SourceFrame} (hValid : ValidYieldCtx ctx) (plan : Term) :
    Yields (plug ctx (.perform plan)) plan ctx := by
  suffices gen : ∀ (c : List SourceFrame) (acc : List SourceFrame) (u : Term),
      ValidYieldCtx c → Yields u plan acc → Yields (plug c u) plan (acc ++ c) by
    simpa using gen ctx [] (.perform plan) hValid (.perform plan)
  intro c; induction c with
  | nil => intro acc u _ hy; simpa [plug] using hy
  | cons f rest ih =>
    intro acc u hvc hy
    have hf : ∀ op l, f = .binaryRight op l → Value l := fun op l heq =>
      hvc f List.mem_cons_self op l heq
    have hrest : ValidYieldCtx rest := fun g hg => hvc g (List.mem_cons_of_mem f hg)
    have hstep : Yields (f.plug u) plan (acc ++ [f]) := by
      cases f with
      | application a => exact .application a hy
      | field name => exact .field name hy
      | extend fs => exact .extend fs hy
      | binaryLeft op r => exact .binaryLeft op r hy
      | binaryRight op l => exact .binaryRight op (hf op l rfl) hy
      | condition z s => exact .condition z s hy
      | case arms => exact .case arms hy
      | ifBool wt wf => exact .ifBool wt wf hy
      | reflect => exact .reflect hy
      | metadata => exact .metadata hy
      | project => exact .project hy
      | split names fn => exact .split names fn hy
    simpa [plug, List.append_assoc] using ih (acc ++ [f]) (f.plug u) hrest hstep
/-! ## 5. Reachability Collector, `.update` Zipper Splitting & `reifyMachineDag` -/

def runtimeValueDeps : RuntimeValue → List Address
  | .closure _ env => env
  | .natural _ | .boolean _ | .label _ => []
  | .record fs => fs.map Prod.snd
  | .specification m e => [m, e]
  | .prototype s t => [s, t]
  | .variant _ p => [p]
def cellDeps (addr : Address) : Cell → List Address
  | .suspended origin | .evaluating origin =>
      match recoverFixKnot? addr origin with
      | some (_, _, outerEnv) => outerEnv
      | none => origin.environment
  | .cached origin val =>
      match recoverFixKnot? addr origin with
      | some (_, _, outerEnv) => outerEnv
      | none => runtimeValueDeps val
def frameDeps : Frame → List Address
  | .argument _ env | .extend _ env | .condition _ _ env | .binaryLeft _ _ env
  | .case _ env | .ifBool _ _ env | .split _ _ env => env
  | .binaryRight _ leftVal => runtimeValueDeps leftVal
  | .update _ | .field _ | .reflect | .metadata | .project => []
def controlDeps : Control → List Address
  | .evaluate _ env => env
  | .enter addr | .yielded addr => [addr]
  | .returned val | .complete val => runtimeValueDeps val
  | .blackhole _ | .refused _ => []
def dedupAddrs : List Address → List Address
  | [] => []
  | a :: rest =>
      let r := dedupAddrs rest
      if r.contains a then r else a :: r
inductive VisitTask where
  | enterAddr (addr : Address)
  | finishAddr (addr : Address)
def collectTopoAux (heap : Array Cell) :
    Nat → List VisitTask → List Address → List Address → Except ReifyError (List Address)
  | 0, [], _, postRev | _ + 1, [], _, postRev => .ok postRev.reverse
  | 0, _ :: _, _, _ => .error .fuelExhausted
  | fuel + 1, .finishAddr addr :: rest, visiting, postRev =>
      let visiting' := visiting.filter (fun a => a != addr)
      let postRev' := if postRev.contains addr then postRev else addr :: postRev
      collectTopoAux heap fuel rest visiting' postRev'
  | fuel + 1, .enterAddr addr :: rest, visiting, postRev =>
      if postRev.contains addr then collectTopoAux heap fuel rest visiting postRev
      else if visiting.contains addr then .error (.unrecoverableCycle addr)
      else match heap[addr]? with
        | none => .error (.danglingAddress addr)
        | some cell =>
            collectTopoAux heap fuel ((dedupAddrs (cellDeps addr cell)).map VisitTask.enterAddr ++
              (.finishAddr addr :: rest)) (addr :: visiting) postRev
def collectReachableTopo (heap : Array Cell) (roots : List Address) :
    Except ReifyError (List Address) :=
  let uniqueRoots := dedupAddrs roots
  let fuel := (heap.size + 1) * (heap.size + uniqueRoots.length + 4) + 16
  collectTopoAux heap fuel (uniqueRoots.map VisitTask.enterAddr) [] []
def indexOfAddr? (addr : Address) : List Address → Option Nat
  | [] => none
  | a :: rest => if a == addr then some 0 else (indexOfAddr? addr rest).map Nat.succ
def resolveHeapAddr (scope : List Address) (localBinders : Nat) (addr : Address) :
    Except ReifyError Term :=
  match indexOfAddr? addr scope with
  | some idx => .ok (.bound (localBinders + idx))
  | none => .error (.danglingAddress addr)
def checkEnvVar (k : Nat) (scope : List Address) (env : Environment) (i : Nat) : Bool :=
  if i < k then true else match env[i - k]? with
    | some addr => (indexOfAddr? addr scope).isSome
    | none => false
def mapEnvVar (k : Nat) (scope : List Address) (env : Environment) (i : Nat) : Nat :=
  if i < k then i else match env[i - k]? with
    | some addr => k + (indexOfAddr? addr scope).getD 0
    | none => i
def reifyTermUnder (k : Nat) (scope : List Address) (env : Environment) (t : Term) :
    Except ReifyError Term :=
  if Tree.all (checkEnvVar k scope env) (encode t) then .ok (t.rename (mapEnvVar k scope env))
  else if !Tree.all (fun i => decide (i < k + env.length)) (encode t) then .error (.unboundVariable 0)
  else .error (.danglingAddress 0)
abbrev reifyTermInScope (scope : List Address) (env : Environment) (t : Term) :
    Except ReifyError Term := reifyTermUnder 0 scope env t
theorem reifyTermUnder_closed (k : Nat) (scope : List Address) (env : Environment)
    (t : Term) (hScoped : Scoped k t) : reifyTermUnder k scope env t = .ok t := by
  unfold reifyTermUnder
  have hall : Tree.all (checkEnvVar k scope env) (encode t) = true := by
    rw [Tree.all_eq_true]
    simpa only [Tree.rename_id] using Tree.all_rename (encode t) (fun i => i < k)
      (fun i => checkEnvVar k scope env i = true) hScoped id (fun i hi => by simp [checkEnvVar, hi])
  simp only [hall, ite_true]; congr 1
  exact scoped_rename_identity t k hScoped (mapEnvVar k scope env) (fun i hi => by simp [mapEnvVar, hi])
def mapExcept {α β : Type} (f : α → Except ReifyError β) : List α → Except ReifyError (List β)
  | [] => .ok []
  | x :: xs => do pure ((← f x) :: (← mapExcept f xs))
def reifyValueInScope (scope : List Address) : RuntimeValue → Except ReifyError Term
  | .closure body env => (.lam ·) <$> reifyTermUnder 1 scope env body
  | .natural n => .ok (.nat n)
  | .boolean b => .ok (.boolean b)
  | .label s => .ok (.label s)
  | .record fs => (.record ·) <$> mapExcept (fun p => (p.1, ·) <$> resolveHeapAddr scope 0 p.2) fs
  | .specification m e => do pure (.specification (← resolveHeapAddr scope 0 m) (← resolveHeapAddr scope 0 e))
  | .prototype s t => do pure (.prototype (← resolveHeapAddr scope 0 s) (← resolveHeapAddr scope 0 t))
  | .variant tag p => (.inject tag ·) <$> resolveHeapAddr scope 0 p
theorem reifyValueInScope_is_value (scope : List Address) (rv : RuntimeValue) (t : Term)
    (h : reifyValueInScope scope rv = .ok t) : Value t := by
  cases rv <;> dsimp only [reifyValueInScope, bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map] at h
  · split at h <;> cases h; exact .function _
  · cases h; exact .natural _
  · cases h; exact .boolean _
  · cases h; exact .label _
  · split at h <;> cases h; exact .record _
  · split at h
    · cases h
    · split at h <;> cases h; exact .specification _ _
  · split at h
    · cases h
    · split at h <;> cases h; exact .prototype _ _
  · split at h <;> cases h; exact .inject _ _
def reifyCellRhs (scope : List Address) (addr : Address) : Cell → Except ReifyError Term
  | .suspended origin | .evaluating origin =>
      match recoverFixKnot? addr origin with
      | some (spec, inh, outerEnv) => do
          pure (.fix (← reifyTermInScope scope outerEnv spec) (← reifyTermInScope scope outerEnv inh))
      | none => reifyTermInScope scope origin.environment origin.term
  | .cached origin val =>
      match recoverFixKnot? addr origin with
      | some (spec, inh, outerEnv) => do
          pure (.fix (← reifyTermInScope scope outerEnv spec) (← reifyTermInScope scope outerEnv inh))
      | none => reifyValueInScope scope val
def buildDagBindings (heap : Array Cell) :
    List Address → List Address → Except ReifyError (List Term × List Address)
  | [], scope => .ok ([], scope)
  | addr :: rest, scope =>
      match heap[addr]? with
      | none => .error (.danglingAddress addr)
      | some cell => do
          let rhs ← reifyCellRhs scope addr cell
          let (restRhss, finalScope) ← buildDagBindings heap rest (addr :: scope)
          pure (rhs :: restRhss, finalScope)
def reifyNonUpdateFrame (scope : List Address) : Frame → Except ReifyError (Option SourceFrame)
  | .update _ => .ok none
  | .argument arg env => (some ∘ .application) <$> reifyTermInScope scope env arg
  | .field name => .ok (some (.field name))
  | .reflect => .ok (some .reflect)
  | .metadata => .ok (some .metadata)
  | .project => .ok (some .project)
  | .extend fs env => (some ∘ .extend) <$> mapExcept (fun p => (p.1, ·) <$> reifyTermInScope scope env p.2) fs
  | .condition z s env => do pure (some (.condition (← reifyTermInScope scope env z) (← reifyTermUnder 1 scope env s)))
  | .binaryLeft op r env => (some ∘ .binaryLeft op) <$> reifyTermInScope scope env r
  | .binaryRight op leftVal => (some ∘ .binaryRight op) <$> reifyValueInScope scope leftVal
  | .case arms env => (some ∘ .case) <$> mapExcept (fun p => (p.1, ·) <$> reifyTermUnder 1 scope env p.2) arms
  | .ifBool wt wf env => do pure (some (.ifBool (← reifyTermInScope scope env wt) (← reifyTermInScope scope env wf)))
  | .split names fn env => (some ∘ .split names) <$> reifyTermInScope scope env fn
theorem reifyNonUpdateFrame_valid (scope : List Address) (f : Frame) (sf : SourceFrame)
    (h : reifyNonUpdateFrame scope f = .ok (some sf)) :
    ∀ op l, sf = .binaryRight op l → Value l := by
  cases f <;> dsimp only [reifyNonUpdateFrame, bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map, Function.comp] at h
  · split at h <;> cases h; intro _ _ hk; cases hk
  · cases h
  · cases h; intro _ _ hk; cases hk
  · cases h; intro _ _ hk; cases hk
  · cases h; intro _ _ hk; cases hk
  · cases h; intro _ _ hk; cases hk
  · split at h <;> cases h; intro _ _ hk; cases hk
  · split at h
    · cases h
    · split at h <;> cases h; intro _ _ hk; cases hk
  · split at h <;> cases h; intro _ _ hk; cases hk
  · split at h
    · cases h
    · rename_i lv hl; cases h; intro _ _ hk; cases hk
      exact reifyValueInScope_is_value scope _ _ hl
  · split at h <;> cases h; intro _ _ hk; cases hk
  · split at h
    · cases h
    · split at h <;> cases h; intro _ _ hk; cases hk
  · split at h <;> cases h; intro _ _ hk; cases hk
def reifyStackFrames (scope : List Address) : List Frame → Except ReifyError (List SourceFrame)
  | [] => .ok []
  | f :: rest => do
      let sf? ← reifyNonUpdateFrame scope f
      let restCtx ← reifyStackFrames scope rest
      match sf? with | some sf => pure (sf :: restCtx) | none => pure restCtx
theorem reifyStackFrames_validYield (scope : List Address) (frames : List Frame)
    (ctx : List SourceFrame) (h : reifyStackFrames scope frames = .ok ctx) :
    ValidYieldCtx ctx := by
  induction frames generalizing ctx with
  | nil => cases h; intro _ hf; cases hf
  | cons f rest ih =>
    dsimp only [reifyStackFrames, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i sf? hsf
      split at h
      · cases h
      · rename_i restCtx hr
        cases sf? with
        | none => simp only [Except.ok.injEq] at h; subst h; exact ih _ hr
        | some sf =>
          simp only [Except.ok.injEq] at h; subst h; intro g hg op l heq
          rcases List.mem_cons.1 hg with rfl | hm
          · exact reifyNonUpdateFrame_valid scope f g hsf op l heq
          · exact ih _ hr g hm op l heq
/-- **`.update` Frame-Zipper Splitter (`plugStackSplittingUpdates`)**. -/
@[expose] def plugStackSplittingUpdates (scope : List Address) :
    List Frame → Term → Except ReifyError Term
  | [], focus => .ok focus
  | .update addr :: outer, focus => do
      pure (.app (.lam (← plugStackSplittingUpdates (addr :: scope) outer (.bound 0))) focus)
  | f :: rest, focus => do
      match ← reifyNonUpdateFrame scope f with
      | some sf => plugStackSplittingUpdates scope rest (sf.plug focus)
      | none => plugStackSplittingUpdates scope rest focus
def finishStackInScope (rhss : List Term) (scope : List Address) (stack : List Frame)
    (focus : Term) : Except ReifyError Term :=
  if forcingShared stack then (letChain rhss ·) <$> plugStackSplittingUpdates scope stack focus
  else (fun ctx => letChain rhss (plug ctx focus)) <$> reifyStackFrames scope stack
def reifyMachineWithOrder (st : State) (order : List Address) : Except ReifyError Term := do
  let (rhss, scope) ← buildDagBindings st.heap order []
  match st.control with
  | .refused reason => .error (.machineRefused reason)
  | .blackhole addr => .error (.machineBlackhole addr)
  | .complete val => (letChain rhss ·) <$> reifyValueInScope scope val
  | .yielded planAddr =>
      if forcingShared st.stack then .error .yieldUnderSharedUpdate
      else do
        let planRef ← resolveHeapAddr scope 0 planAddr
        let ctx ← reifyStackFrames scope st.stack
        pure (letChain rhss (plug ctx (.perform planRef)))
  | .evaluate term env => finishStackInScope rhss scope st.stack (← reifyTermInScope scope env term)
  | .enter addr => finishStackInScope rhss scope st.stack (← resolveHeapAddr scope 0 addr)
  | .returned val => finishStackInScope rhss scope st.stack (← reifyValueInScope scope val)
@[expose] def reifyMachineDag (st : State) : Except ReifyError Term := do
  let roots := controlDeps st.control ++ st.stack.foldr (fun f acc => frameDeps f ++ acc) []
  reifyMachineWithOrder st (← collectReachableTopo st.heap roots)
/-! ## 6. Linear DAG Size Theorem & Diamond $O(d)$ vs Tree $O(2^d)$ Separation -/

theorem foldl_bound_le {xs : List Term} {B : Nat} (hB : ∀ r ∈ xs, termNodeCount r ≤ B) :
    xs.foldl (fun acc r => acc + 2 + termNodeCount r) 0 ≤ xs.length * (B + 2) := by
  suffices gen : ∀ (ys : List Term) (init : Nat), (∀ r ∈ ys, termNodeCount r ≤ B) →
      ys.foldl (fun acc r => acc + 2 + termNodeCount r) init ≤ init + ys.length * (B + 2) from
    by simpa using gen xs 0 hB
  intro ys; induction ys with
  | nil => intro _ _; simp
  | cons y rest ih =>
    intro init hy; simp only [List.foldl_cons, List.length_cons]
    have hy0 := hy y List.mem_cons_self
    have hrest := ih (init + 2 + termNodeCount y) (fun z hz => hy z (List.mem_cons_of_mem y hz))
    have hmul : (rest.length + 1) * (B + 2) = rest.length * (B + 2) + (B + 2) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
theorem reifyMachineDag_linear_in_reachable_heap
    (rhss : List Term) (focusPlugged : Term) (F B : Nat)
    (hFocus : termNodeCount focusPlugged ≤ F)
    (hCells : ∀ r ∈ rhss, termNodeCount r ≤ B) :
    termNodeCount (letChain rhss focusPlugged) ≤ F + rhss.length * (B + 2) := by
  rw [termNodeCount_letChain]; have hb := foldl_bound_le hCells; omega
def mkDiamondHeap : Nat → Array Cell
  | 0 => #[.suspended ⟨.nat 1, []⟩]
  | d + 1 => (mkDiamondHeap d).push (.suspended ⟨.binary .add (.bound 0) (.bound 0), [d]⟩)
@[expose] def mkDiamondState (d : Nat) : State :=
  { heap := mkDiamondHeap d, control := .enter d, stack := [] }
def reifyAddrTree (heap : Array Cell) : Nat → Address → Except ReifyError Term
  | 0, _ => .error .fuelExhausted
  | fuel + 1, addr =>
      match heap[addr]? with
      | none => .error (.danglingAddress addr)
      | some (.cached _ (.natural n)) => .ok (.nat n)
      | some (.suspended ⟨.nat n, []⟩) => .ok (.nat n)
      | some (.suspended ⟨.binary op (.bound 0) (.bound 0), [dep]⟩) => do
          let sub ← reifyAddrTree heap fuel dep; pure (.binary op sub sub)
      | _ => .error .fuelExhausted
private theorem mkDiamondHeap_size (m : Nat) : (mkDiamondHeap m).size = m + 1 := by
  induction m with | zero => rfl | succ _ ihq => simp [mkDiamondHeap, Array.size_push, ihq]
private theorem mkDiamondHeap_get0 (n : Nat) :
    (mkDiamondHeap n)[0]? = some (.suspended ⟨.nat 1, []⟩) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [mkDiamondHeap, Array.getElem?_push, mkDiamondHeap_size m]
    simp [ih]
private theorem mkDiamondHeap_getSucc (n j : Nat) (hj : j + 1 ≤ n) :
    (mkDiamondHeap n)[j + 1]? = some (.suspended ⟨.binary .add (.bound 0) (.bound 0), [j]⟩) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [mkDiamondHeap, Array.getElem?_push, mkDiamondHeap_size m]
    by_cases heq : j = m
    · subst heq; simp
    · simp [heq, ih (by omega)]
theorem diamond_tree_exponential (d : Nat) :
    ∃ tTree, reifyAddrTree (mkDiamondHeap d) (d + 1) d = .ok tTree ∧
      2 ^ d ≤ termNodeCount tTree := by
  suffices gen : ∀ (k : Nat), k ≤ d →
      ∃ t, reifyAddrTree (mkDiamondHeap d) (k + 1) k = .ok t ∧ 2 ^ k ≤ termNodeCount t from
    gen d (Nat.le_refl d)
  intro k hk; induction k with
  | zero =>
    refine ⟨.nat 1, by simp [reifyAddrTree, mkDiamondHeap_get0 d],
      by simp [termNodeCount, encode, treeNodeCount]⟩
  | succ j ih =>
    obtain ⟨sub, hsub, hcnt⟩ := ih (by omega)
    refine ⟨.binary .add sub sub, ?_, ?_⟩
    · rw [reifyAddrTree.eq_2, mkDiamondHeap_getSucc d j hk]
      simp [bind, Except.bind, pure, Except.pure, hsub]
    · have hbin : termNodeCount (.binary .add sub sub) = 1 + termNodeCount sub + termNodeCount sub := by
        simp [termNodeCount, encode, treeNodeCount]; omega
      have hp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
      omega
private theorem filter_ne_self_of_not_mem {a : Address} {xs : List Address} (h : a ∉ xs) :
    (a :: xs).filter (fun x => x != a) = xs := by
  have hTail : xs.filter (fun x => x != a) = xs :=
    List.filter_eq_self.2 (fun x hx => bne_iff_ne.2 (fun heq => h (heq ▸ hx)))
  simp [hTail]
private theorem dedupAddrs_nil : dedupAddrs [] = [] := rfl
private theorem dedupAddrs_singleton (a : Address) : dedupAddrs [a] = [a] := rfl
private theorem dedupAddrs_pair_self (a : Address) : dedupAddrs [a, a] = [a] := by
  simp [dedupAddrs]
private theorem collectTopoAux_mkDiamondHeap (d : Nat) :
    ∀ (k : Nat), k ≤ d → ∀ (f : Nat) (rest : List VisitTask) (vis post : List Address),
      (∀ m ≤ k, m ∉ vis ∧ m ∉ post) →
      collectTopoAux (mkDiamondHeap d) (f + 2 * (k + 1)) (.enterAddr k :: rest) vis post =
        collectTopoAux (mkDiamondHeap d) f rest vis ((List.range (k + 1)).reverse ++ post) := by
  intro k; induction k with
  | zero =>
    intro _ f rest vis post hFresh
    obtain ⟨h0V, h0P⟩ := hFresh 0 (Nat.le_refl 0)
    have hEqF : f + 2 * 1 = (f + 1) + 1 := by omega
    rw [hEqF]
    have hNotV : vis.contains 0 = false := Bool.eq_false_iff.2 (fun hc => h0V (List.contains_iff_mem.1 hc))
    have hNotP : post.contains 0 = false := Bool.eq_false_iff.2 (fun hc => h0P (List.contains_iff_mem.1 hc))
    simp only [collectTopoAux, hNotP, hNotV, Bool.false_eq_true, ite_false,
      mkDiamondHeap_get0 d, cellDeps, recoverFixKnot?, dedupAddrs_nil, List.map, List.nil_append,
      filter_ne_self_of_not_mem h0V]
    rfl
  | succ j ih =>
    intro hk f rest vis post hFresh
    obtain ⟨hj1V, hj1P⟩ := hFresh (j + 1) (Nat.le_refl _)
    have hNotV : vis.contains (j + 1) = false := Bool.eq_false_iff.2 (fun hc => hj1V (List.contains_iff_mem.1 hc))
    have hNotP : post.contains (j + 1) = false := Bool.eq_false_iff.2 (fun hc => hj1P (List.contains_iff_mem.1 hc))
    have hEqF : f + 2 * (j + 2) = ((f + 1) + 2 * (j + 1)) + 1 := by omega
    rw [hEqF]
    simp only [collectTopoAux, hNotP, hNotV, Bool.false_eq_true, ite_false,
      mkDiamondHeap_getSucc d j hk, cellDeps, recoverFixKnot?,
      dedupAddrs_singleton, List.map, List.cons_append, List.nil_append]
    have hFreshSub : ∀ m ≤ j, m ∉ ((j + 1) :: vis) ∧ m ∉ post := by
      intro m hm; refine ⟨fun hMem => ?_, (hFresh m (by omega)).2⟩
      rcases List.mem_cons.1 hMem with rfl | hv
      · omega
      · exact (hFresh m (by omega)).1 hv
    rw [ih (by omega) (f + 1) (.finishAddr (j + 1) :: rest) ((j + 1) :: vis) post hFreshSub]
    have hNotInPost' : ((List.range (j + 1)).reverse ++ post).contains (j + 1) = false := by
      apply Bool.eq_false_iff.2; intro hc
      rcases List.mem_append.1 (List.contains_iff_mem.1 hc) with hR | hP
      · have hLt : j + 1 < j + 1 := List.mem_range.1 (List.mem_reverse.1 hR); omega
      · exact hj1P hP
    simp only [collectTopoAux, filter_ne_self_of_not_mem hj1V, hNotInPost',
      Bool.false_eq_true, ite_false, List.range_succ (n := j + 1), List.reverse_append]
    rfl
theorem collectReachableTopo_mkDiamondHeap (d : Nat) :
    collectReachableTopo (mkDiamondHeap d) [d] = .ok (List.range (d + 1)) := by
  unfold collectReachableTopo
  simp only [dedupAddrs_singleton, List.length, List.map, mkDiamondHeap_size]
  have hSplit : d + 1 + 1 + 4 = (d + 4) + 2 := by omega
  have hFuel : (d + 1 + 1) * (d + 1 + 1 + 4) + 16 = ((d + 1 + 1) * (d + 4) + 18) + 2 * (d + 1) := by
    rw [hSplit, Nat.mul_add]; omega
  rw [hFuel, collectTopoAux_mkDiamondHeap d d (Nat.le_refl d) ((d + 1 + 1) * (d + 4) + 18) [] [] []
    (fun _ _ => ⟨List.not_mem_nil, List.not_mem_nil⟩)]
  have hSucc : (d + 1 + 1) * (d + 4) + 18 = ((d + 1 + 1) * (d + 4) + 17) + 1 := by omega
  rw [hSucc]; simp [collectTopoAux]
theorem diamond_dag_linear_bound (d : Nat) :
    ∃ tDag, reifyMachineDag (mkDiamondState d) = .ok tDag ∧
      termNodeCount tDag ≤ 5 * d + 6 := by
  have happ : ∀ (xs ys : List Address) (sc : List Address) (rs1 : List Term) (sc1 : List Address),
      buildDagBindings (mkDiamondHeap d) xs sc = .ok (rs1, sc1) →
      ∀ (rs2 : List Term) (sc2 : List Address),
      buildDagBindings (mkDiamondHeap d) ys sc1 = .ok (rs2, sc2) →
      buildDagBindings (mkDiamondHeap d) (xs ++ ys) sc = .ok (rs1 ++ rs2, sc2) := by
    intro xs; induction xs with
    | nil => intro _ _ _ _ h1 _ _ h2; cases h1; simpa using h2
    | cons a rest ihx =>
      intro ys sc rs1 sc1 h1 rs2 sc2 h2
      simp only [List.cons_append, buildDagBindings, bind, Except.bind, pure, Except.pure] at h1 ⊢
      split at h1
      · cases h1
      · split at h1
        · cases h1
        · rename_i rhs hr
          split at h1
          · cases h1
          · rename_i pair hb
            rcases pair with ⟨restRhss, finalSc⟩
            cases h1
            rw [ihx ys (a :: sc) restRhss finalSc hb rs2 sc2 h2]; rfl
  have hbuild : ∀ (k : Nat), k ≤ d →
      ∃ rhss scope,
        buildDagBindings (mkDiamondHeap d) (List.range (k + 1)) [] = .ok (rhss, scope) ∧
        scope = (List.range (k + 1)).reverse ∧ rhss.length = k + 1 ∧
        (∀ r ∈ rhss, termNodeCount r ≤ 3) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨[.nat 1], [0], ?_, rfl, rfl, ?_⟩
      · simp [List.range_succ, buildDagBindings, mkDiamondHeap_get0 d, reifyCellRhs, recoverFixKnot?,
          reifyTermInScope, reifyTermUnder, encode, Tree.all, Term.rename, bind, Except.bind, pure, Except.pure]
      · intro r hr; rcases List.mem_singleton.1 hr with rfl
        simp [termNodeCount, encode, treeNodeCount]
    | succ j ih =>
      obtain ⟨rhssJ, scopeJ, hbJ, hscJ, hlenJ, hcntJ⟩ := ih (by omega)
      have hhead : scopeJ = j :: (List.range j).reverse := by
        rw [hscJ, List.range_succ, List.reverse_append]; rfl
      have hlast : buildDagBindings (mkDiamondHeap d) [j + 1] scopeJ =
          .ok ([.binary .add (.bound 0) (.bound 0)], (j + 1) :: scopeJ) := by
        simp [buildDagBindings, mkDiamondHeap_getSucc d j hk, reifyCellRhs, recoverFixKnot?,
          reifyTermInScope, reifyTermUnder, encode, Tree.all, checkEnvVar, mapEnvVar,
          hhead, indexOfAddr?, Term.rename, bind, Except.bind, pure, Except.pure]
      have hcomb := happ (List.range (j + 1)) [j + 1] [] rhssJ scopeJ hbJ _ _ hlast
      rw [← List.range_succ] at hcomb
      refine ⟨rhssJ ++ [.binary .add (.bound 0) (.bound 0)], (j + 1) :: scopeJ, hcomb, ?_, ?_, ?_⟩
      · rw [hscJ, List.range_succ (n := j + 1), List.reverse_append]; simp
      · simp [hlenJ]
      · intro r hr; rcases List.mem_append.1 hr with h1 | h2
        · exact hcntJ r h1
        · rcases List.mem_singleton.1 h2 with rfl; simp [termNodeCount, encode, treeNodeCount]
  obtain ⟨rhss, scope, hb, hsc, hlen, hcnt⟩ := hbuild d (Nat.le_refl d)
  have htopInScope : resolveHeapAddr scope 0 d = .ok (.bound 0) := by
    rw [hsc, List.range_succ, List.reverse_append]; simp [resolveHeapAddr, indexOfAddr?]
  refine ⟨letChain rhss (.bound 0), ?_, ?_⟩
  · simp [reifyMachineDag, mkDiamondState, controlDeps, collectReachableTopo_mkDiamondHeap d,
      reifyMachineWithOrder, finishStackInScope, hb, htopInScope, forcingShared,
      reifyStackFrames, plug, bind, Except.bind, Functor.map, Except.map]
  · have hlin := reifyMachineDag_linear_in_reachable_heap rhss (.bound 0) 1 3
      (by simp [termNodeCount, encode, treeNodeCount]) hcnt
    rw [hlen] at hlin; omega
theorem reifyMachineDag_complete_nat (n : Nat) :
    reifyMachineDag ⟨#[], .complete (.natural n), []⟩ = .ok (.nat n) := by rfl
theorem reifyMachineDag_initial (t : Term) (hClosed : Scoped 0 t) :
    reifyMachineDag (Machine.initial t) = .ok t := by
  have hclosedIn : reifyTermInScope [] [] t = .ok t := reifyTermUnder_closed 0 [] [] t hClosed
  simp [reifyMachineDag, Machine.initial, controlDeps, collectReachableTopo, dedupAddrs, collectTopoAux,
    reifyMachineWithOrder, finishStackInScope, buildDagBindings, hclosedIn, forcingShared,
    reifyStackFrames, letChain, plug, bind, Except.bind, Functor.map, Except.map]
theorem reifyMachineDag_fix_step_iequiv (spec inherited : Term)
    (hSpec : Scoped 0 spec) (hInh : Scoped 0 inherited) :
    ∃ t, reifyMachineDag (Machine.stepRaw (Machine.initial (.fix spec inherited))) = .ok t ∧
      IEquiv t (.fix spec inherited) := by
  have hs : reifyTermInScope [] [] spec = .ok spec := reifyTermUnder_closed 0 [] [] spec hSpec
  have hi : reifyTermInScope [] [] inherited = .ok inherited := reifyTermUnder_closed 0 [] [] inherited hInh
  refine ⟨letChain [.fix spec inherited] (.bound 0), ?_, ?_⟩
  · simp [Machine.initial, Machine.stepRaw, reifyMachineDag, controlDeps, collectReachableTopo,
      dedupAddrs, collectTopoAux, cellDeps, recoverFixKnot_complete, reifyMachineWithOrder, finishStackInScope,
      buildDagBindings, reifyCellRhs, hs, hi, resolveHeapAddr, indexOfAddr?, forcingShared,
      reifyStackFrames, plug, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · simpa [evalLetChain, evalLetChainAux, singleSubst, liftSubstN, Term.substitute] using
      letChain_iequiv_evalLetChain [.fix spec inherited] (.bound 0)
theorem plugStackSplittingUpdates_update_iequiv (scope : List Address) (addr : Address)
    (outer : List Frame) (liveFocus outerBody : Term)
    (hOuter : plugStackSplittingUpdates (addr :: scope) outer (.bound 0) = .ok outerBody) :
    ∃ splitTm,
      plugStackSplittingUpdates scope (.update addr :: outer) liveFocus = .ok splitTm ∧
      Steps splitTm (instantiate outerBody liveFocus) ∧
      IEquiv splitTm (instantiate outerBody liveFocus) := by
  refine ⟨.app (.lam outerBody) liveFocus, ?_, ?_⟩
  · simp [plugStackSplittingUpdates, hOuter, bind, Except.bind, pure, Except.pure]
  · let hs : Steps (.app (.lam outerBody) liveFocus) (instantiate outerBody liveFocus) :=
      .next (Step.beta outerBody liveFocus) (.refl _)
    exact ⟨hs, iequiv_of_ahead (Ahead.ofStepsRefl hs)⟩
theorem reifyMachineDag_sound (st : State) :
    (∀ val t, st.control = .complete val → reifyMachineDag st = .ok t →
      ∃ v, Evaluates t v ∧ IEquiv t v ∧ (∀ n, val = .natural n → v = .nat n) ∧
        (∀ b, val = .boolean b → v = .boolean b) ∧ (∀ s, val = .label s → v = .label s)) ∧
    (∀ planAddr t, st.control = .yielded planAddr → reifyMachineDag st = .ok t →
      ∃ order rhss scope planRef rawCtx,
        collectReachableTopo st.heap
          (controlDeps st.control ++ st.stack.foldr (fun f acc => frameDeps f ++ acc) []) = .ok order ∧
        buildDagBindings st.heap order [] = .ok (rhss, scope) ∧
        resolveHeapAddr scope 0 planAddr = .ok planRef ∧
        reifyStackFrames scope st.stack = .ok rawCtx ∧
        let ctx' := evalLetChainCtx rhss rawCtx; let plan' := evalLetChain rhss planRef
        Steps t (plug ctx' (.perform plan')) ∧ Yields (plug ctx' (.perform plan')) plan' ctx' ∧
        IEquiv t (plug ctx' (.perform plan')) ∧
        (∀ response st', Machine.resume response st = some st' → Scoped 0 response →
          ∃ tResumed, reifyMachineWithOrder st' order = .ok tResumed ∧
            Steps tResumed (plug ctx' response) ∧ IEquiv tResumed (plug ctx' response))) := by
  constructor
  · intro val t hctrl hreify; dsimp only [reifyMachineDag, bind, Except.bind] at hreify
    split at hreify; · cases hreify
    rename_i order hord
    dsimp only [reifyMachineWithOrder, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at hreify
    rw [hctrl] at hreify; split at hreify; · cases hreify
    rename_i pair hb; rcases pair with ⟨rhss, scope⟩; dsimp only at hreify
    split at hreify; · cases hreify
    rename_i vTerm hv; cases hreify
    have hvVal : Value vTerm := reifyValueInScope_is_value scope val vTerm hv
    refine ⟨evalLetChain rhss vTerm,
      ⟨letChain_steps_evalLetChain rhss vTerm, evalLetChain_value rhss hvVal⟩,
      letChain_iequiv_evalLetChain rhss vTerm, ?_, ?_, ?_⟩
    · intro n hvn; subst hvn; cases hv; exact evalLetChain_nat rhss n
    · intro b hvb; subst hvb; cases hv; exact evalLetChain_boolean rhss b
    · intro s hvs; subst hvs; cases hv; exact evalLetChain_label rhss s
  · intro planAddr t hctrl hreify; dsimp only [reifyMachineDag, bind, Except.bind] at hreify
    split at hreify; · cases hreify
    rename_i order hord
    dsimp only [reifyMachineWithOrder, bind, Except.bind, pure, Except.pure] at hreify
    rw [hctrl] at hreify; split at hreify; · cases hreify
    rename_i pair hb; rcases pair with ⟨rhss, scope⟩; dsimp only at hreify
    cases hforce : forcingShared st.stack
    · simp only [hforce, Bool.false_eq_true, ite_false] at hreify
      split at hreify; · cases hreify
      rename_i planRef hp; split at hreify; · cases hreify
      rename_i rawCtx hctx; cases hreify
      have hvy : ValidYieldCtx (evalLetChainCtx rhss rawCtx) :=
        evalLetChainCtx_validYield rhss (reifyStackFrames_validYield scope st.stack rawCtx hctx)
      have hsteps : Steps (letChain rhss (plug rawCtx (.perform planRef)))
          (plug (evalLetChainCtx rhss rawCtx) (.perform (evalLetChain rhss planRef))) := by
        have s0 := letChain_steps_evalLetChain rhss (plug rawCtx (.perform planRef))
        rw [evalLetChain_plug, evalLetChain_perform] at s0; exact s0
      refine ⟨order, rhss, scope, planRef, rawCtx, hord, hb, hp, hctx, hsteps,
        plug_yields_perform hvy (evalLetChain rhss planRef),
        iequiv_of_ahead (Ahead.ofStepsRefl hsteps), ?_⟩
      intro response st' hres hClosed
      obtain ⟨hheap, hstack, hctrl'⟩ := Machine.resume_keeps_heap_and_stack response st st' hres
      have hrespIn : reifyTermInScope scope [] response = .ok response :=
        reifyTermUnder_closed 0 scope [] response hClosed
      refine ⟨letChain rhss (plug rawCtx response), ?_, ?_, ?_⟩
      · simp [reifyMachineWithOrder, finishStackInScope, hheap, hstack, hctrl', hb, hrespIn,
          hforce, hctx, bind, Except.bind, Functor.map, Except.map]
      · have s1 := letChain_steps_evalLetChain rhss (plug rawCtx response)
        rw [evalLetChain_plug, evalLetChain_closed rhss hClosed] at s1; exact s1
      · have s1 := letChain_steps_evalLetChain rhss (plug rawCtx response)
        rw [evalLetChain_plug, evalLetChain_closed rhss hClosed] at s1
        exact iequiv_of_ahead (Ahead.ofStepsRefl s1)
    · simp only [hforce, ite_true] at hreify; cases hreify
end Obend.Core.MachineReify
end
