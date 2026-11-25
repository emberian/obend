module
public import Obend.Doc.Grove
import Obend.Core.TermTraverse
import all Obend.Doc.Grove
import all Obend.Core.Proofs.Preservation.Base.Insert

public section
namespace Obend.Doc.Grove
open Obend.Core.Term Obend.Core.Ty Obend.Core.Machine Obend.Core.Check Obend.Core.MachineTyping
set_option autoImplicit false
attribute [local instance] lexOrd

open Obend.Core.TermTraverse in
private def sourceHoleBound : Shape → Nat
  | .var _ => 0
  | .bind b => sourceHoleBound b
  | .node tag children =>
    let start := match tag with | .hole n => n + 1 | _ => 0
    (children.map sourceHoleBound).foldl max start

mutual
private def Marked.firstFresh : Marked → Nat
  | .code t _ => sourceHoleBound (Obend.Core.TermTraverse.encode t)
  | .var _ => 0
  | .lam _ _ _ b => b.firstFresh
  | .app f a => max f.firstFresh a.firstFresh
  | .letBind _ _ v b => max v.firstFresh b.firstFresh
  | .fix s i => max s.firstFresh i.firstFresh
  | .mix lo hi => max lo.firstFresh hi.firstFresh
  | .prototype s t => max s.firstFresh t.firstFresh
  | .projectProto t => t.firstFresh
  | .reflectProto t => t.firstFresh
  | .record fields => fieldsFirstFresh fields
  | .get t _ => t.firstFresh
  | .binary _ l r => max l.firstFresh r.firstFresh
  | .ifBool c wt wf => max c.firstFresh (max wt.firstFresh wf.firstFresh)
  | .hole _ => 0

private def fieldsFirstFresh : List (String × Marked) → Nat
  | [] => 0
  | (_, m) :: rest => max m.firstFresh (fieldsFirstFresh rest)
end

structure HoleTable where
  first : Nat
  entries : Array ConflictHole

def HoleTable.lookup (table : HoleTable) (id : Nat) : Option ConflictHole :=
  if id < table.first then none else table.entries[id - table.first]?

mutual
/-- Lower a full Core4 `Marked` tree to real machine syntax. Generated conflict holes carry
distinct indices above all source holes; the call-by-need machine decides which holes are forced. -/
def Marked.lower (first : Nat) : Marked → Array ConflictHole → Term × Array ConflictHole
  | .code term _, holes => (term, holes)
  | .var i, holes => (.bound i, holes)
  | .hole h, holes => (.hole (first + holes.size) [], holes.push h)
  | .lam _ _ _ body, holes =>
    let (b, bs) := body.lower first holes
    (.lam b, bs)
  | .app fn arg, holes =>
    let (f, fs) := fn.lower first holes
    let (a, both) := arg.lower first fs
    (.app f a, both)
  | .letBind _ _ val body, holes =>
    let (b, bs) := body.lower first holes
    let (v, both) := val.lower first bs
    (.app (.lam b) v, both)
  | .fix spec inh, holes =>
    let (s, ss) := spec.lower first holes
    let (i, both) := inh.lower first ss
    (.fix s i, both)
  | .mix lo hi, holes =>
    let (l, ls) := lo.lower first holes
    let (h, both) := hi.lower first ls
    (.mix l h, both)
  | .prototype sp tg, holes =>
    let (s, ss) := sp.lower first holes
    let (t, both) := tg.lower first ss
    (.prototype s t, both)
  | .projectProto tg, holes =>
    let (t, ts) := tg.lower first holes
    (.project t, ts)
  | .reflectProto tg, holes =>
    let (t, ts) := tg.lower first holes
    (.reflect t, ts)
  | .record fields, holes =>
    let (fs, hs) := lowerFields first fields holes
    (.record fs, hs)
  | .get tg name, holes =>
    let (t, ts) := tg.lower first holes
    (.get t name, ts)
  | .binary prim l r, holes =>
    let (lt, ls) := l.lower first holes
    let (rt, both) := r.lower first ls
    (.binary prim lt rt, both)
  | .ifBool c wt wf, holes =>
    let (ct, cs) := c.lower first holes
    let (tt, ts) := wt.lower first cs
    let (ft, fs) := wf.lower first ts
    (.ifBool ct tt ft, fs)

def lowerFields (first : Nat) : List (String × Marked) → Array ConflictHole →
    List (String × Term) × Array ConflictHole
  | [], holes => ([], holes)
  | (name, m) :: rest, holes =>
    let (mt, hs1) := m.lower first holes
    let (rt, hs2) := lowerFields first rest hs1
    ((name, mt) :: rt, hs2)
end

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

/-- Localized demand: evaluate the document program directly, with every reachable detached
delete-modify cut localized as a first-class conflict hole at its exact port.
Never throws away `r.program` when `r.detached` is non-empty! -/
def LiveRoot.demand (r : LiveRoot) : Marked := r.program

/-- When a detached delete-modify cut is anchored at `rootPort`, localized demand immediately
surfaces that cut as a conflict hole at the root. -/
theorem covered_demand_at_root (nodes : Catalog) (expected : Port → Ty)
    (rootPort : Port) (g : StructurePatch) (cut : Cut) (edit : Edge)
    (deleted : cut ∈ g.removed.val.toList)
    (changed : (edit ∈ liveEdges g ∧ edit ∉ cut.2) ∨ (edit ∈ cut.2 ∧ edit ≠ cut.1 ∧ edit ∉ liveEdges g))
    (inside : EdgePath (liveEdges g) cut.1.target edit.port.1)
    (detached : ¬ RootPath (liveEdges g) rootPort cut.1.target)
    (atRoot : cut.1.port = rootPort)
    (limits : Limits) (ticks : Nat) :
    ∃ h, h ∈ (liveRoot nodes expected rootPort g).detached ∧
      h.port = rootPort ∧
      evaluate (liveRoot nodes expected rootPort g).demand limits ticks =
        .conflict { h with expected := portType nodes expected rootPort }
          (initial (.hole 0 [])) ⟨0, #[{ h with expected := portType nodes expected rootPort }]⟩ := by
  obtain ⟨h, hmem, hport, hproj⟩ :=
    DeleteModifyLocalized nodes expected rootPort g cut edit deleted changed inside detached
      nodes.size [] [] (portType nodes expected rootPort)
  refine ⟨h, hmem, hport.trans atRoot, ?_⟩
  have hprog : (liveRoot nodes expected rootPort g).demand = .hole { h with expected := portType nodes expected rootPort } := by
    unfold LiveRoot.demand liveRoot
    unfold liveRoot at hproj
    simpa [atRoot] using hproj
  rw [hprog]
  exact evaluate_hole _ limits ticks

/-- Localized non-wipeout theorem: when an `ifBool` root selects its clean `then` branch (`.nat n`),
an arbitrary localized detached conflict hole on the unforced `else` branch NEVER wipes out
evaluation — even when `r.detached` is non-empty! -/
theorem unaffected_ifBool_evaluates (n : Nat) (detachedHole : ConflictHole)
    (detachedList : List ConflictHole) (limits : Limits) (ticks : Nat)
    (hStack : 1 ≤ limits.stack) (hTicks : 5 ≤ ticks) :
    let r : LiveRoot := ⟨.ifBool (.code (.boolean true)) (.code (.nat n)) (.hole detachedHole), detachedList⟩
    evaluate r.demand limits ticks = .machine (.finished (.natural n) ⟨#[], .complete (.natural n), []⟩) := by
  obtain ⟨k, rfl⟩ : ∃ k, ticks = k + 5 := ⟨ticks - 5, by omega⟩
  have h0 : (Marked.ifBool (.code (.boolean true)) (.code (.nat n)) (.hole detachedHole)).firstFresh = 0 := by
    simp [Marked.firstFresh, sourceHoleBound, Obend.Core.TermTraverse.encode]
  have hlow : (Marked.ifBool (.code (.boolean true)) (.code (.nat n)) (.hole detachedHole)).lower 0 #[] =
      (.ifBool (.boolean true) (.nat n) (.hole 0 []), #[detachedHole]) := rfl
  simp only [LiveRoot.demand, evaluate, h0, hlow, initial]
  cases k with
  | zero =>
    simp [observe, step, stepRaw, runBounded, hStack]
  | succ k' =>
    simp [observe, step, stepRaw, hStack]

/-- The entire observation, including the resulting ground value and heap, is
unchanged by edits outside a closed region. -/
theorem evaluate_disjoint (nodes : Catalog) (a b : StructurePatch)
    (cutsA cutsB : Std.TreeMap.Raw Port (List ConflictHole) compare)
    (region : Nat → Prop)
    (incident : ∀ e : Edge, region e.port.1 ∨ region e.target →
      (e ∈ liveEdges a ↔ e ∈ liveEdges b))
    (closed : ∀ e ∈ liveEdges a, region e.port.1 → region e.target)
    (cutsSame : ∀ p : Port, region p.1 → cutsA.getD p [] = cutsB.getD p [])
    (p : Port) (ty : Ty) (hp : region p.1) (limits : Limits) (ticks : Nat) :
    evaluate (project nodes (indexEdges (liveEdges a)) cutsA nodes.size [] [] p ty) limits ticks =
    evaluate (project nodes (indexEdges (liveEdges b)) cutsB nodes.size [] [] p ty) limits ticks := by
  rw [project_frame nodes a b cutsA cutsB region incident closed cutsSame _ _ _ _ _ hp]

/-! ## Resolution, Typing Soundness & Certified Freezing -/

mutual
/-- Discharging a conflict requires a resolved program on every branch, including
arguments or branches that the current evaluation could leave unforced. -/
def Marked.resolve : Marked → Except ConflictHole Term
  | .code t _ => .ok t
  | .var i => .ok (.bound i)
  | .hole h => .error h
  | .lam _ _ _ body => do return .lam (← body.resolve)
  | .app f a => do return .app (← f.resolve) (← a.resolve)
  | .letBind _ _ val body => do return .app (.lam (← body.resolve)) (← val.resolve)
  | .fix s i => do return .fix (← s.resolve) (← i.resolve)
  | .mix lo hi => do return .mix (← lo.resolve) (← hi.resolve)
  | .prototype s t => do return .prototype (← s.resolve) (← t.resolve)
  | .projectProto t => do return .project (← t.resolve)
  | .reflectProto t => do return .reflect (← t.resolve)
  | .record fields => do return .record (← resolveFields fields)
  | .get t name => do return .get (← t.resolve) name
  | .binary p l r => do return .binary p (← l.resolve) (← r.resolve)
  | .ifBool c wt wf => do return .ifBool (← c.resolve) (← wt.resolve) (← wf.resolve)

def resolveFields : List (String × Marked) → Except ConflictHole (List (String × Term))
  | [] => .ok []
  | (name, m) :: rest => do
    let t ← m.resolve
    let rs ← resolveFields rest
    return (name, t) :: rs
end

mutual
/-- Collect the exact `Bidirectional` path-indexed `AnnTable` alongside resolved `Term`. -/
def Marked.collectAnns (path : List Nat) : Marked → LiveObject.AnnTable
  | .code _ anns => anns.map fun (p, a) => (path ++ p, a)
  | .var _ | .hole _ => []
  | .lam r dom cod body =>
    (path, ⟨dom, cod, .unrestricted, r⟩) :: body.collectAnns (path ++ [0])
  | .app f a => f.collectAnns (path ++ [0]) ++ a.collectAnns (path ++ [1])
  | .letBind bTy bodyTy val body =>
    (path ++ [0], ⟨bTy, bodyTy, .unrestricted, .reusable⟩) ::
      body.collectAnns (path ++ [0, 0]) ++ val.collectAnns (path ++ [1])
  | .fix s i => s.collectAnns (path ++ [0]) ++ i.collectAnns (path ++ [1])
  | .mix lo hi => lo.collectAnns (path ++ [0]) ++ hi.collectAnns (path ++ [1])
  | .prototype s t => s.collectAnns (path ++ [0]) ++ t.collectAnns (path ++ [1])
  | .projectProto t | .reflectProto t | .get t _ => t.collectAnns (path ++ [0])
  | .record fields => collectFieldsAnns path 0 fields
  | .binary _ l r => l.collectAnns (path ++ [0]) ++ r.collectAnns (path ++ [1])
  | .ifBool c wt wf =>
    c.collectAnns (path ++ [0]) ++ wt.collectAnns (path ++ [1]) ++ wf.collectAnns (path ++ [2])

def collectFieldsAnns (path : List Nat) (idx : Nat) : List (String × Marked) → LiveObject.AnnTable
  | [] => []
  | (_, m) :: rest => m.collectAnns (path ++ [idx]) ++ collectFieldsAnns path (idx + 1) rest
end

/-- Ambient lexical context invariant maintained by Grove projection:
every binder introduced by `lam` or `letBind` is `unrestricted` and `shareable`. -/
def AllUnrestrictedShareable (ctx : Context) : Prop :=
  ∀ b ∈ ctx, b.quantity = .unrestricted ∧ b.type.shareable = true

private theorem allUS_cons {ctx : Context} (h : AllUnrestrictedShareable ctx)
    {ty : Ty} (hs : ty.shareable = true) :
    AllUnrestrictedShareable (⟨ty, .unrestricted⟩ :: ctx) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ⟨rfl, hs⟩
  · exact h b hb

private theorem allUS_validContext {ctx : Context} (h : AllUnrestrictedShareable ctx) :
    validContext [] ctx = true := by
  unfold validContext
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨hq, hs⟩ := h b hb
  simp [hq, hs]

private theorem allUS_safeUses {ctx : Context} (h : AllUnrestrictedShareable ctx)
    {u : Uses} (hlen : u.length = ctx.length) : safeUses ctx u = true := by
  unfold safeUses
  rw [Bool.and_eq_true]
  refine ⟨beq_iff_eq.mpr hlen, List.all_eq_true.mpr ?_⟩
  intro pair hpair
  have hb := List.of_mem_zip hpair
  obtain ⟨hq, _⟩ := h pair.1 hb.1
  simp [safeQuantity, hq]

private theorem allUS_linearFree {ctx : Context} (h : AllUnrestrictedShareable ctx) (u : Uses) :
    linearFree ctx u = true := by
  unfold linearFree
  rw [List.all_eq_true]
  intro pair hpair
  have hb := List.of_mem_zip hpair
  obtain ⟨hq, _⟩ := h pair.1 hb.1
  simp [hq]

private theorem allUS_reusableCaptures {ctx : Context} (h : AllUnrestrictedShareable ctx)
    {u : Uses} (hlen : u.length = ctx.length) : reusableCaptures [] ctx u = true := by
  unfold reusableCaptures
  rw [Bool.and_eq_true]
  refine ⟨beq_iff_eq.mpr hlen, List.all_eq_true.mpr ?_⟩
  intro pair hpair
  have hb := List.of_mem_zip hpair
  obtain ⟨hq, hs⟩ := h pair.1 hb.1
  simp [hq, hs]

private theorem allUS_branchesAgree {ctx : Context} (h : AllUnrestrictedShareable ctx) :
    ∀ (u₁ u₂ : Uses), branchesAgree ctx u₁ u₂ = true := by
  induction ctx with
  | nil => intro u₁ u₂; simp [branchesAgree]
  | cons b rest ih =>
    intro u₁ u₂
    obtain ⟨hq, _⟩ := h b (List.mem_cons_self ..)
    cases u₁ with
    | nil => simp [branchesAgree]
    | cons x xs =>
      cases u₂ with
      | nil => simp [branchesAgree]
      | cons y ys =>
        simp [branchesAgree, Quantity.agrees, hq, ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

private theorem allUS_argumentAllowed {ctx : Context} (h : AllUnrestrictedShareable ctx)
    {q : Quantity} {dom : Ty} {u : Uses} (hlen : u.length = ctx.length)
    (h0 : argumentAllowed {} q [] dom [] = true) :
    argumentAllowed {} q ctx dom u = true := by
  unfold argumentAllowed at h0 ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h0 ⊢
  refine ⟨⟨h0.1.1, Or.inr (allUS_linearFree h u)⟩, ?_⟩
  rcases h0.2 with hne | ⟨hs, _⟩
  · exact Or.inl hne
  · exact Or.inr ⟨hs, allUS_reusableCaptures h hlen⟩

private theorem weaken_closed {t : Term} {ty : Ty} (h : PartialTyping {} [] t ty []) :
    ∀ (ctx : Context), AllUnrestrictedShareable ctx → PartialTyping {} ctx t ty (zeroUses ctx)
  | [], _ => h
  | b :: rest, hctx => by
    have ih := weaken_closed h rest (fun b' hb' => hctx b' (List.mem_cons_of_mem _ hb'))
    have hbValid : validContext [] [b] = true := by
      obtain ⟨hq, hs⟩ := hctx b (List.mem_cons_self ..)
      simp [validContext, hq, hs]
    have hw := Obend.Core.Proofs.Preservation.source_weaken (binding := b) ih hbValid
    have hsc : Obend.Core.Invariant.Scoped 0 t := source_scoped h
    have hren : t.rename Nat.succ = t :=
      Obend.Core.Invariant.scoped_rename_identity hsc Nat.succ (fun i hi => by omega)
    simpa [hren, zeroUses, List.replicate_succ] using hw

private theorem labelsDistinct_of_nodup : ∀ {fs : List (String × Term)},
    (fs.map Prod.fst).Nodup → labelsDistinct fs = true
  | [], _ => rfl
  | (n, t) :: rest, hnd => by
    obtain ⟨hnotmem, hrest⟩ := List.nodup_cons.mp hnd
    simp only [labelsDistinct, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    refine ⟨fun x hx heq => hnotmem (heq ▸ List.mem_map.mpr ⟨x, hx, rfl⟩), labelsDistinct_of_nodup hrest⟩

private theorem resolveFields_map_fst : ∀ {fs : List (String × Marked)} {ts : List (String × Term)},
    resolveFields fs = .ok ts → ts.map Prod.fst = fs.map Prod.fst
  | [], ts, ok => by simp [resolveFields] at ok; subst ok; rfl
  | (n, m) :: rest, ts, ok => by
    simp only [resolveFields, bind, Except.bind, pure, Except.pure] at ok
    cases hm : m.resolve with
    | error _ => simp [hm] at ok
    | ok mt =>
      cases hr : resolveFields rest with
      | error _ => simp [hm, hr] at ok
      | ok rt =>
        simp only [hm, hr, Except.ok.injEq] at ok
        subst ok
        simp [resolveFields_map_fst hr]

theorem resolved_typed_ctx {ctx : Context} (hctx : AllUnrestrictedShareable ctx)
    {m : Marked} {ty : Ty} (typed : HasType ctx m ty) {t : Term}
    (ok : m.resolve = .ok t) : ∃ uses, PartialTyping {} ctx t ty uses := by
  refine HasType.rec
    (motive_1 := fun ctx m ty _ => AllUnrestrictedShareable ctx →
      ∀ {t}, m.resolve = .ok t → ∃ uses, PartialTyping {} ctx t ty uses)
    (motive_2 := fun ctx fs row _ => AllUnrestrictedShareable ctx →
      ∀ {ts}, resolveFields fs = .ok ts → ∃ uses, FieldsTyping {} ctx ts row uses)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed hctx ok
  · -- code
    intro ctx t anns ty hpt hctx t' ok
    simp only [Marked.resolve, Except.ok.injEq] at ok; subst ok
    exact ⟨zeroUses ctx, weaken_closed hpt ctx hctx⟩
  · -- var
    intro ctx i b ty hget hty _ t' ok
    simp only [Marked.resolve, Except.ok.injEq] at ok; subst ok; subst hty
    exact ⟨variableUses ctx i, .bound hget⟩
  · -- hole
    intro ctx h _ t' ok; simp [Marked.resolve] at ok
  · -- lam
    intro ctx r dom cod body hdom _ ih hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hb : body.resolve with
    | error _ => simp [hb] at ok
    | ok bt =>
      simp only [hb, Except.ok.injEq] at ok; subst ok
      have hctx' := allUS_cons hctx hdom
      obtain ⟨bu, hbu⟩ := ih hctx' hb
      have hlen := source_uses_length hbu
      have htail : bu.tail.length = ctx.length := by
        cases bu with
        | nil => simp at hlen
        | cons _ _ => simp at hlen ⊢; exact hlen
      exact ⟨bu.tail, .lambda (annotation := ⟨dom, cod, .unrestricted, r⟩) hbu
        (allUS_safeUses hctx' hlen) (allUS_validContext hctx')
        (by unfold reusableAllowed; cases r <;> simp [allUS_reusableCaptures hctx htail])
        rfl⟩
  · -- app
    intro ctx f a r q dom ran _ _ hallow ihf iha hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hf : f.resolve with
    | error _ => simp [hf] at ok
    | ok ft =>
      cases ha : a.resolve with
      | error _ => simp [hf, ha] at ok
      | ok atTerm =>
        simp only [hf, ha, Except.ok.injEq] at ok; subst ok
        obtain ⟨fu, hfu⟩ := ihf hctx hf
        obtain ⟨au, hau⟩ := iha hctx ha
        exact ⟨addUses fu au, .application hfu hau rfl rfl
          (allUS_argumentAllowed hctx (source_uses_length hau) hallow)⟩
  · -- letBind
    intro ctx bTy bodyTy val body hbTy _ _ ihv ihb hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hb : body.resolve with
    | error _ => simp [hb] at ok
    | ok bt =>
      cases hv : val.resolve with
      | error _ => simp [hb, hv] at ok
      | ok vt =>
        simp only [hb, hv, Except.ok.injEq] at ok; subst ok
        have hctx' := allUS_cons hctx hbTy
        obtain ⟨bu, hbu⟩ := ihb hctx' hb
        obtain ⟨vu, hvu⟩ := ihv hctx hv
        have hlen := source_uses_length hbu
        have htail : bu.tail.length = ctx.length := by
          cases bu with
          | nil => simp at hlen
          | cons _ _ => simp at hlen ⊢; exact hlen
        have hlam : PartialTyping {} ctx (.lam bt) (.arrow .reusable .unrestricted bTy bodyTy) bu.tail :=
          .lambda (annotation := ⟨bTy, bodyTy, .unrestricted, .reusable⟩) hbu
            (allUS_safeUses hctx' hlen) (allUS_validContext hctx')
            (by simp [reusableAllowed, allUS_reusableCaptures hctx htail]) rfl
        have harg : argumentAllowed {} .unrestricted ctx bTy vu = true := by
          unfold argumentAllowed
          simp [Ty.shareable_not_computation bTy hbTy, allUS_linearFree hctx vu,
            hbTy, allUS_reusableCaptures hctx (source_uses_length hvu)]
        exact ⟨addUses bu.tail vu, .application hlam hvu rfl rfl harg⟩
  · -- fix
    intro ctx inh target spec inhTerm htar hinh _ _ ihs ihi hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hs : spec.resolve with
    | error _ => simp [hs] at ok
    | ok st =>
      cases hi : inhTerm.resolve with
      | error _ => simp [hs, hi] at ok
      | ok it =>
        simp only [hs, hi, Except.ok.injEq] at ok; subst ok
        obtain ⟨su, hsu⟩ := ihs hctx hs
        obtain ⟨iu, hiu⟩ := ihi hctx hi
        have harg : argumentAllowed {} .unrestricted ctx inh iu = true := by
          unfold argumentAllowed
          simp [Ty.shareable_not_computation inh hinh, allUS_linearFree hctx iu,
            hinh, allUS_reusableCaptures hctx (source_uses_length hiu)]
        exact ⟨addUses su iu, .fix hsu rfl hiu (by simpa using htar) harg
          (allUS_reusableCaptures hctx (source_uses_length hsu))⟩
  · -- mix
    intro ctx self inh mid prov lo hi hself hinh hmid _ _ ihl ihh hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hl : lo.resolve with
    | error _ => simp [hl] at ok
    | ok lt =>
      cases hh : hi.resolve with
      | error _ => simp [hl, hh] at ok
      | ok ht =>
        simp only [hl, hh, Except.ok.injEq] at ok; subst ok
        obtain ⟨lu, hlu⟩ := ihl hctx hl
        obtain ⟨hu, hhu⟩ := ihh hctx hh
        have haddLen : (addUses lu hu).length = ctx.length := by
          simp [addUses, List.length_zipWith, source_uses_length hlu, source_uses_length hhu]
        exact ⟨addUses lu hu, .mix hlu hhu rfl rfl (allUS_reusableCaptures hctx haddLen)
          (by simpa using hself) (by simpa using hinh) (by simpa using hmid)⟩
  · -- prototype
    intro ctx s t sp tg hs ht _ _ ihs iht hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : sp.resolve with
    | error _ => simp [h1] at ok
    | ok s' =>
      cases h2 : tg.resolve with
      | error _ => simp [h1, h2] at ok
      | ok t'' =>
        simp only [h1, h2, Except.ok.injEq] at ok; subst ok
        obtain ⟨su, hsu⟩ := ihs hctx h1
        obtain ⟨tu, htu⟩ := iht hctx h2
        exact ⟨addUses su tu, .prototype hsu htu hs ht⟩
  · -- projectProto
    intro ctx s t tg _ ih hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : tg.resolve with
    | error _ => simp [h1] at ok
    | ok tg' =>
      simp only [h1, Except.ok.injEq] at ok; subst ok
      obtain ⟨u, hu⟩ := ih hctx h1
      exact ⟨u, .project hu (allUS_linearFree hctx u)⟩
  · -- reflectProto
    intro ctx s t tg _ ih hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : tg.resolve with
    | error _ => simp [h1] at ok
    | ok tg' =>
      simp only [h1, Except.ok.injEq] at ok; subst ok
      obtain ⟨u, hu⟩ := ih hctx h1
      exact ⟨u, .reflect hu (allUS_linearFree hctx u)⟩
  · -- record
    intro ctx fields row hnd _ ih hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases hf : resolveFields fields with
    | error _ => simp [hf] at ok
    | ok ts =>
      simp only [hf, Except.ok.injEq] at ok; subst ok
      obtain ⟨u, hu⟩ := ih hctx hf
      have hnd' : (ts.map Prod.fst).Nodup := by rw [resolveFields_map_fst hf]; exact hnd
      exact ⟨u, .record hu (labelsDistinct_of_nodup hnd')⟩
  · -- get
    intro ctx row name member tg hlook _ ih hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : tg.resolve with
    | error _ => simp [h1] at ok
    | ok tg' =>
      simp only [h1, Except.ok.injEq] at ok; subst ok
      obtain ⟨u, hu⟩ := ih hctx h1
      obtain ⟨fuel, hfl⟩ := hlook
      exact ⟨u, .get hu hfl (allUS_linearFree hctx u)⟩
  · -- binary
    intro ctx prim l r _ _ ihl ihr hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : l.resolve with
    | error _ => simp [h1] at ok
    | ok lt =>
      cases h2 : r.resolve with
      | error _ => simp [h1, h2] at ok
      | ok rt =>
        simp only [h1, h2, Except.ok.injEq] at ok; subst ok
        obtain ⟨lu, hlu⟩ := ihl hctx h1
        obtain ⟨ru, hru⟩ := ihr hctx h2
        exact ⟨addUses lu ru, .binary rfl hlu hru⟩
  · -- ifBool
    intro ctx ty c wt wf _ _ _ ihc iht ihf hctx t' ok
    simp only [Marked.resolve, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : c.resolve with
    | error _ => simp [h1] at ok
    | ok ct =>
      cases h2 : wt.resolve with
      | error _ => simp [h1, h2] at ok
      | ok tt =>
        cases h3 : wf.resolve with
        | error _ => simp [h1, h2, h3] at ok
        | ok ft =>
          simp only [h1, h2, h3, Except.ok.injEq] at ok; subst ok
          obtain ⟨cu, hcu⟩ := ihc hctx h1
          obtain ⟨tu, htu⟩ := iht hctx h2
          obtain ⟨fu, hfu⟩ := ihf hctx h3
          exact ⟨addUses cu (joinUses tu fu), .ifBool hcu htu hfu (allUS_branchesAgree hctx tu fu)⟩
  · -- HasFieldTypes.nil
    intro ctx _ ts ok
    simp only [resolveFields, Except.ok.injEq] at ok; subst ok
    exact ⟨zeroUses ctx, .nil ctx⟩
  · -- HasFieldTypes.cons
    intro ctx name m rest ty row hpure _ _ ihm ihr hctx ts ok
    simp only [resolveFields, bind, Except.bind, pure, Except.pure] at ok
    cases h1 : m.resolve with
    | error _ => simp [h1] at ok
    | ok mt =>
      cases h2 : resolveFields rest with
      | error _ => simp [h1, h2] at ok
      | ok rt =>
        simp only [h1, h2, Except.ok.injEq] at ok; subst ok
        obtain ⟨mu, hmu⟩ := ihm hctx h1
        obtain ⟨ru, hru⟩ := ihr hctx h2
        exact ⟨addUses mu ru, .cons hmu hru hpure⟩

theorem resolved_typed {m : Marked} {ty : Ty} (typed : HasType [] m ty) {t : Term}
    (ok : m.resolve = .ok t) : PartialTyping {} [] t ty [] := by
  obtain ⟨u, hu⟩ := resolved_typed_ctx (fun _ hb => by cases hb) typed ok
  have hnil : u = [] := List.length_eq_zero_iff.mp (source_uses_length hu)
  exact hnil ▸ hu

/-- Reason a Grove root could not be frozen into a certified Vault Replay checkpoint. -/
inductive FreezeError where
  | conflict (hole : ConflictHole)
  | uncertified (detail : String)
  deriving Repr

/-- Turn a resolved Grove root into a `StateCert`-verified checkpoint accepted by Vault Replay.
Every detached edit and unresolved branch conflict blocks freezing; when clean, the emitted
`StateCert` is verified directly by `checkStateCert` with zero erased-ghost bypass. -/
def freezeRoot (nodes : Catalog) (entry : Port → Ty) (p : Port)
    (g : StructurePatch) : Except FreezeError (LiveObject.Checkpoint {} [] (portType nodes entry p)) :=
  let root := liveRoot nodes entry p g
  match root.detached with
  | h :: _ => .error (.conflict h)
  | [] =>
    match root.program.resolve with
    | .error h => .error (.conflict h)
    | .ok t =>
      let ty := portType nodes entry p
      let cert := LiveObject.StateCert.ofInitial {} ty (root.program.collectAnns [])
      let st := initial t
      if hok : LiveObject.checkStateCert cert st = true then
        .ok ⟨st, cert, LiveObject.StateCert.ofInitial_assumptions _ _ _,
          LiveObject.StateCert.ofInitial_addressTypes _ _ _,
          LiveObject.StateCert.ofInitial_result _ _ _, hok⟩
      else
        .error (.uncertified "resolved Grove root failed executable StateCert check")

end Obend.Doc.Grove
