module
public import Obend.Vault.Store
public import Obend.Vault.Rehydration
public import Obend.Spec.DataWire
public import Obend.Core.Term
public import Obend.Digest.Cshake256
public import Obend.Digest.HashBytes
public import Obend.Equiv.Reduction
public import Lean.Data.Json
public section
namespace Obend.Vault.Form
set_option autoImplicit false
open Obend.Core.Data (Data)
open Obend.Vault.Affordance (Auth fireGate fireGate_iff_subset fireGate_trans)
open Obend.Vault.Rehydration (MembraneViewer Membrane.reshare reshare_some_attenuates Sturdyref)
open Obend.Doc (Graph AtomId)
inductive PRef where
  | page (name : String) | hole (name : String)
deriving DecidableEq, Repr
inductive NExpr where
  | lit (n : Nat) | hole (name : String) | field (p : PRef) (f : String) | add (a b : NExpr) | sub (a b : NExpr)
deriving DecidableEq, Repr
abbrev Known := String → Option Data
abbrev Agrees (k' k : Known) : Prop := ∀ n d, k' n = some d → k n = some d
theorem Agrees.refl (k : Known) : Agrees k k := fun _ _ h => h
structure Assignment where
  nats : List (String × Nat) := []
  pages : List (String × String) := []
  labels : List (String × String) := []
deriving DecidableEq, Repr
abbrev PRef.subst (a : Assignment) : PRef → PRef
  | .page n => .page n
  | .hole h => match a.pages.lookup h with
    | some n => .page n | none => .hole h
@[expose] def NExpr.subst (a : Assignment) : NExpr → NExpr
  | .lit n => .lit n
  | .hole h => match a.nats.lookup h with
    | some n => .lit n | none => .hole h
  | .field p f => .field (p.subst a) f | .add x y => .add (x.subst a) (y.subst a) | .sub x y => .sub (x.subst a) (y.subst a)
@[expose] def NExpr.eval (k : Known) : NExpr → Option Nat
  | .lit n => some n | .hole _ => none | .field (.page n) f => (k n).map (natAt · f) | .field (.hole _) _ => none
  | .add x y => do let u ← x.eval k; let v ← y.eval k; pure (u + v)
  | .sub x y => do
    let u ← x.eval k; let v ← y.eval k
    if v ≤ u then pure (u - v) else none
@[expose] def addN : NExpr → NExpr → NExpr
  | .lit u, .lit v => .lit (u + v) | x, y => .add x y
@[expose] def subN : NExpr → NExpr → NExpr
  | .lit u, .lit v => if v ≤ u then .lit (u - v) else .sub (.lit u) (.lit v) | x, y => .sub x y
@[expose] def NExpr.peval (k : Known) : NExpr → NExpr
  | .lit n => .lit n | .hole h => .hole h
  | .field (.page n) f => match k n with
    | some d => .lit (natAt d f) | none => .field (.page n) f
  | .field (.hole h) f => .field (.hole h) f | .add x y => addN (x.peval k) (y.peval k) | .sub x y => subN (x.peval k) (y.peval k)
theorem eval_subst_addN (k : Known) (a : Assignment) (x y : NExpr) : ((addN x y).subst a).eval k = ((NExpr.add x y).subst a).eval k := by cases x <;> cases y <;> simp [addN, NExpr.subst, NExpr.eval]
theorem eval_subst_subN (k : Known) (a : Assignment) (x y : NExpr) : ((subN x y).subst a).eval k = ((NExpr.sub x y).subst a).eval k := by
  cases x <;> cases y <;> simp only [subN, NExpr.subst, NExpr.eval] <;> try rfl
  rename_i u v
  by_cases h : v ≤ u <;> simp [h, NExpr.subst, NExpr.eval]
theorem eval_subst_peval {k' k : Known} (hk : Agrees k' k) (a : Assignment) : ∀ e : NExpr, ((e.peval k').subst a).eval k = (e.subst a).eval k
  | .lit _ => rfl | .hole _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases h : k' n with
    | none => rfl | some d => simp [NExpr.subst, PRef.subst, NExpr.eval, hk n d h]
  | .field (.hole _) _ => rfl
  | .add x y => by simp only [NExpr.peval]; rw [eval_subst_addN]; simp only [NExpr.subst, NExpr.eval]; rw [eval_subst_peval hk a x, eval_subst_peval hk a y]
  | .sub x y => by simp only [NExpr.peval]; rw [eval_subst_subN]; simp only [NExpr.subst, NExpr.eval]; rw [eval_subst_peval hk a x, eval_subst_peval hk a y]
def NExpr.knownFree (k : Known) : NExpr → Bool
  | .lit _ | .hole _ | .field (.hole _) _ => true | .field (.page n) _ => (k n).isNone | .add x y | .sub x y => x.knownFree k && y.knownFree k
theorem knownFree_addN (k : Known) (x y : NExpr) (hx : x.knownFree k = true) (hy : y.knownFree k = true) : (addN x y).knownFree k = true := by cases x <;> cases y <;> simp_all [addN, NExpr.knownFree]
theorem knownFree_subN (k : Known) (x y : NExpr) (hx : x.knownFree k = true) (hy : y.knownFree k = true) : (subN x y).knownFree k = true := by cases x <;> cases y <;> simp_all [subN, NExpr.knownFree] <;> split <;> simp [NExpr.knownFree]
theorem residual_reads_nothing_known (k : Known) : ∀ e : NExpr, (e.peval k).knownFree k = true
  | .lit _ | .hole _ | .field (.hole _) _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases h : k n with
    | none => simp [NExpr.knownFree, h] | some d => rfl
  | .add x y => knownFree_addN k _ _ (residual_reads_nothing_known k x) (residual_reads_nothing_known k y) | .sub x y => knownFree_subN k _ _ (residual_reads_nothing_known k x) (residual_reads_nothing_known k y)
def NExpr.abstractNat (v : Nat) (h : String) : NExpr → NExpr
  | .lit n => if n == v then .hole h else .lit n | .hole x => .hole x | .field p f => .field p f | .add x y => .add (x.abstractNat v h) (y.abstractNat v h) | .sub x y => .sub (x.abstractNat v h) (y.abstractNat v h)
def PRef.abstractPage (n h : String) : PRef → PRef
  | .page m => if m == n then .hole h else .page m | .hole x => .hole x
def NExpr.abstractPage (n h : String) : NExpr → NExpr
  | .lit m => .lit m | .hole x => .hole x | .field p f => .field (p.abstractPage n h) f | .add x y => .add (x.abstractPage n h) (y.abstractPage n h) | .sub x y => .sub (x.abstractPage n h) (y.abstractPage n h)
def PRef.holes : PRef → List String
  | .page _ => [] | .hole h => [h]
def NExpr.holes : NExpr → List String
  | .lit _ => [] | .hole h => [h] | .field p _ => p.holes | .add x y | .sub x y => x.holes ++ y.holes
theorem PRef.subst_abstractPage_cons (n h : String) (a : Assignment) : ∀ p : PRef, h ∉ p.holes → (p.abstractPage n h).subst ⟨a.nats, (h, n) :: a.pages, a.labels⟩ = p.subst a
  | .page m, _ => by by_cases hm : m = n; (next => subst hm; simp [PRef.abstractPage, PRef.subst]); (next => simp [PRef.abstractPage, PRef.subst, hm])
  | .hole x, hx => by
    have hne : (x == h) = false := by simpa using fun e => hx (by simp [PRef.holes, e])
    simp [PRef.abstractPage, PRef.subst, List.lookup, hne]
theorem NExpr.subst_abstractNat_cons (v : Nat) (h : String) (a : Assignment) : ∀ e : NExpr, h ∉ e.holes → (e.abstractNat v h).subst ⟨(h, v) :: a.nats, a.pages, a.labels⟩ = e.subst a
  | .lit n, _ => by by_cases hn : n = v; (next => subst hn; simp [NExpr.abstractNat, NExpr.subst]); (next => simp [NExpr.abstractNat, NExpr.subst, hn])
  | .hole x, hx => by
    have hne : (x == h) = false := by simpa using fun e => hx (by simp [NExpr.holes, e])
    simp [NExpr.abstractNat, NExpr.subst, List.lookup, hne]
  | .field p f, _ => by simp [NExpr.abstractNat, NExpr.subst, PRef.subst]
  | .add x y, hxy => by simp only [NExpr.holes, List.mem_append, not_or] at hxy; simp [NExpr.abstractNat, NExpr.subst, subst_abstractNat_cons v h a x hxy.1, subst_abstractNat_cons v h a y hxy.2]
  | .sub x y, hxy => by simp only [NExpr.holes, List.mem_append, not_or] at hxy; simp [NExpr.abstractNat, NExpr.subst, subst_abstractNat_cons v h a x hxy.1, subst_abstractNat_cons v h a y hxy.2]
theorem NExpr.subst_abstractPage_cons (n h : String) (a : Assignment) : ∀ e : NExpr, h ∉ e.holes → (e.abstractPage n h).subst ⟨a.nats, (h, n) :: a.pages, a.labels⟩ = e.subst a
  | .lit _, _ => rfl
  | .hole x, hx => by simp [NExpr.abstractPage, NExpr.subst]
  | .field p f, hp => by simp only [NExpr.holes] at hp; simp [NExpr.abstractPage, NExpr.subst, PRef.subst_abstractPage_cons n h a p hp]
  | .add x y, hxy => by simp only [NExpr.holes, List.mem_append, not_or] at hxy; simp [NExpr.abstractPage, NExpr.subst, subst_abstractPage_cons n h a x hxy.1, subst_abstractPage_cons n h a y hxy.2]
  | .sub x y, hxy => by simp only [NExpr.holes, List.mem_append, not_or] at hxy; simp [NExpr.abstractPage, NExpr.subst, subst_abstractPage_cons n h a x hxy.1, subst_abstractPage_cons n h a y hxy.2]
def allAuths : List Auth := [.read, .write, .grant, .call, .reply, .reset, .control, .notify]
structure Grant where
  holder : String
  held : List Auth
  patterns : List String
deriving @[expose] DecidableEq, Repr
abbrev Grant.permits (g : Grant) (n : String) : Bool := g.patterns.any (patternMatches · n)
abbrev Grant.viewer (g : Grant) (scope : List String) : MembraneViewer := { held := g.held, permits := g.permits, activeNames := scope }
def ownerGrant : Grant := { holder := "owner", held := allAuths, patterns := ["*"] }
inductive Refusal where
  | amplifies (holder delegate : String) (held asked : List Auth) | notInForm (page holder : String) | notWritable (page holder : String) (held : List Auth) | unfilled (hole : String) | unknownPage (page : String) | resources (page asset : String) (holds moves : Nat) | unevaluated (what : String) | twice (page : String) | numeric (page field : String) | illFormed (page field : String)
deriving DecidableEq, Repr
def resolveChain (scope : List String) : MembraneViewer → String → List Grant → Except Refusal (MembraneViewer × String)
  | cur, who, [] => .ok (cur, who)
  | cur, who, g :: rest =>
    match Membrane.reshare cur (g.viewer scope) with
    | some m => resolveChain scope m g.holder rest | none => .error (.amplifies who g.holder cur.held g.held)
theorem resolveChain_attenuates (scope : List String) (gs : List Grant) (cur : MembraneViewer) (who : String) {v : MembraneViewer} {w : String} (h : resolveChain scope cur who gs = .ok (v, w)) : v.held ⊆ cur.held ∧ ∀ n, v.permits n = true → cur.permits n = true := by
  induction gs generalizing cur who with
  | nil => simp only [resolveChain, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨fun _ hx => hx, fun _ hn => hn⟩ | cons g rest ih => simp only [resolveChain] at h; split at h; (next => rename_i m hm; have ⟨hheld, _, _, hperm, _⟩ := reshare_some_attenuates (φ := Unit) hm; have ⟨ih1, ih2⟩ := ih m g.holder h; exact ⟨List.Subset.trans ih1 hheld, fun n hn => hperm n (ih2 n hn)⟩); (next => cases h)
structure Cell where
  name : String
  required : List Auth := [.read]
  state : Data
deriving Repr
def shows (v : MembraneViewer) (c : Cell) : Bool := fireGate c.required v.held && v.permits c.name
def capture (v : MembraneViewer) (cs : List Cell) : List Cell := cs.filter (shows v)
theorem capture_hidden_absent (v : MembraneViewer) (cs : List Cell) (c : Cell) (hhide : shows v c = false) : c ∉ capture v cs := by intro hc; have := (List.mem_filter.mp hc).2; rw [hhide] at this; cases this
theorem capture_hidden_change (v : MembraneViewer) (pre post : List Cell) (c c' : Cell) (hc : shows v c = false) (hc' : shows v c' = false) : capture v (pre ++ c :: post) = capture v (pre ++ c' :: post) := by simp [capture, List.filter_append, hc, hc']
inductive HoleTy where
  | nat | page | label | text
deriving DecidableEq, Repr
inductive SExpr where
  | lit (s : String) | hole (name : String) | field (p : PRef) (f : String)
deriving DecidableEq, Repr
def labelAt (d : Data) (f : String) : String :=
  match d with
  | .record fs => match fs.lookup f with
    | some (.label s) => s | _ => ""
  | _ => ""
def SExpr.subst (a : Assignment) : SExpr → SExpr
  | .lit s => .lit s
  | .hole h => match a.labels.lookup h with
    | some v => .lit v | none => .hole h
  | .field p f => .field (p.subst a) f
def SExpr.eval (k : Known) : SExpr → Option String
  | .lit s => some s | .hole _ => none | .field (.page n) f => (k n).map (labelAt · f) | .field (.hole _) _ => none
def SExpr.peval (k : Known) : SExpr → SExpr
  | .lit s => .lit s | .hole h => .hole h
  | .field (.page n) f => match k n with
    | some d => .lit (labelAt d f) | none => .field (.page n) f
  | .field (.hole h) f => .field (.hole h) f
def SExpr.holes : SExpr → List String
  | .lit _ => [] | .hole h => [h] | .field p _ => p.holes
theorem SExpr.eval_subst_peval {k' k : Known} (hk : Agrees k' k) (a : Assignment) : ∀ e : SExpr, ((e.peval k').subst a).eval k = (e.subst a).eval k
  | .lit _ => rfl | .hole _ => rfl
  | .field (.page n) f => by
    simp only [SExpr.peval]
    cases hn : k' n with
    | none => rfl | some d => simp [SExpr.subst, SExpr.eval, PRef.subst, hk n d hn]
  | .field (.hole _) _ => rfl
theorem SExpr.holes_subst_peval (k : Known) (a : Assignment) : ∀ e : SExpr, ((e.peval k).subst a).holes = (e.subst a).holes
  | .lit _ | .hole _ | .field (.hole _) _ => rfl
  | .field (.page n) f => by
    simp only [SExpr.peval]
    cases k n <;> rfl
structure SetMove where
  page : PRef
  fields : List (String × SExpr)
deriving DecidableEq, Repr
def SetMove.subst (a : Assignment) (m : SetMove) : SetMove := { page := m.page.subst a, fields := m.fields.map fun x => (x.1, x.2.subst a) }
def SetMove.peval (k : Known) (m : SetMove) : SetMove :=
  { m with fields := m.fields.map fun x => (x.1, x.2.peval k) }
structure Move where
  asset : String
  src : PRef
  dst : PRef
  amount : NExpr
deriving DecidableEq, Repr
structure Form where
  name : String
  grants : List Grant
  cells : List Cell
  refs : List String := []
  holes : List (String × HoleTy) := []
  moves : List Move
  sets : List SetMove := []
deriving Repr
abbrev Form.scope (f : Form) : List String := f.cells.map (·.name) ++ f.refs
abbrev Form.known (f : Form) : Known := fun n => (f.cells.find? (·.name == n)).map (·.state)
abbrev Form.knownLive (f : Form) (live : VaultStore) : Known := fun n =>
  match f.known n with
  | some d => some d | none => live n
theorem Form.known_agrees (f : Form) (live : VaultStore) : Agrees f.known (f.knownLive live) := by intro n d h; simp [Form.knownLive, h]
abbrev Form.sturdyref (_f : Form) (vault : String) (lineage : MembraneViewer) (page : String) : Sturdyref Data := { uri := "obend://" ++ vault ++ "/" ++ page, surface := [], log := [], lineage := lineage, reachable := true, cellId := page }
theorem Form.sturdyref_live (f : Form) (vault : String) (lineage : MembraneViewer) (page : String) : (f.sturdyref vault lineage page).liveness = .Live := rfl
structure RMove where
  asset : String
  src : PRef
  dst : PRef
  amount : NExpr
  debit : NExpr
  credit : NExpr
deriving DecidableEq, Repr
abbrev Move.unfold (m : Move) : RMove := { asset := m.asset, src := m.src, dst := m.dst, amount := m.amount, debit := .sub (.field m.src m.asset) m.amount, credit := .add (.field m.dst m.asset) m.amount }
abbrev RMove.peval (k : Known) (r : RMove) : RMove :=
  { r with amount := r.amount.peval k, debit := r.debit.peval k, credit := r.credit.peval k }
abbrev RMove.subst (a : Assignment) (r : RMove) : RMove := { asset := r.asset, src := r.src.subst a, dst := r.dst.subst a, amount := r.amount.subst a, debit := r.debit.subst a, credit := r.credit.subst a }
abbrev Form.residual (k : Known) (f : Form) : List RMove := f.moves.map fun m => m.unfold.peval k
def Form.setResidual (k : Known) (f : Form) : List SetMove := f.sets.map (·.peval k)
structure SetLeg where
  page : String
  pre : Data
  vals : List (String × String)
deriving Repr
def lineSafe (v : String) : Bool := !v.contains '\n' && !v.contains '"'
def evalFields (kv : Known) (page : String) (pre : Data) : List (String × SExpr) → Except Refusal (List (String × String))
  | [] => .ok []
  | (f, e) :: rest =>
    match e.eval kv with
    | none => .error (if e.holes.isEmpty then .unevaluated (page ++ "." ++ f) else .unfilled (e.holes.headD "?"))
    | some v =>
      if natAt pre f != 0 then .error (.numeric page f) else if !lineSafe v then .error (.illFormed page f)
      else match evalFields kv page pre rest with
        | .error r => .error r | .ok vs => .ok ((f, v) :: vs)
def SetMove.leg (kv kp : Known) (m : SetMove) : Except Refusal SetLeg :=
  match m.page with
  | .hole h => .error (.unfilled h)
  | .page n =>
    match kp n with
    | none => .error (.unknownPage n)
    | some d =>
      match evalFields kv n d m.fields with
      | .error r => .error r | .ok vs => .ok ⟨n, d, vs⟩
def setsOf (kv kp : Known) : List SetMove → Except Refusal (List SetLeg)
  | [] => .ok []
  | m :: ms => do let l ← m.leg kv kp; let ls ← setsOf kv kp ms; pure (l :: ls)
theorem evalFields_peval_subst {k' kv : Known} (hk : Agrees k' kv) (a : Assignment) (page : String) (pre : Data) (fs : List (String × SExpr)) : evalFields kv page pre ((fs.map fun x => (x.1, x.2.peval k')).map fun x => (x.1, x.2.subst a)) = evalFields kv page pre (fs.map fun x => (x.1, x.2.subst a)) := by
  induction fs with
  | nil => rfl | cons x rest ih => simp only [List.map_cons, evalFields, SExpr.eval_subst_peval hk, SExpr.holes_subst_peval, ih]
theorem SetMove.leg_peval_subst {k' kv : Known} (hk : Agrees k' kv) (kp : Known) (a : Assignment) (m : SetMove) : ((m.peval k').subst a).leg kv kp = (m.subst a).leg kv kp := by simp only [SetMove.peval, SetMove.subst, SetMove.leg, evalFields_peval_subst hk]
structure LegPair where
  asset : String
  src : String
  dst : String
  srcPre : Data
  dstPre : Data
  amount : Nat
  srcAfter : Nat
  dstAfter : Nat
deriving Repr
def NExpr.firstHole (e : NExpr) : String := (e.holes.head?).getD "?"
abbrev RMove.pair (k : Known) (r : RMove) : Except Refusal LegPair :=
  match r.src, r.dst with
  | .hole h, _ => .error (.unfilled h) | .page _, .hole h => .error (.unfilled h)
  | .page s, .page d =>
    match k s, k d with
    | none, _ => .error (.unknownPage s) | some _, none => .error (.unknownPage d)
    | some ps, some pd =>
      match r.amount.eval k with
      | none => .error (if r.amount.holes.isEmpty then .unevaluated "the amount" else .unfilled r.amount.firstHole)
      | some x =>
        match r.debit.eval k, r.credit.eval k with
        | some sa, some da => .ok ⟨r.asset, s, d, ps, pd, x, sa, da⟩ | none, _ => .error (.resources s r.asset (natAt ps r.asset) x) | some _, none => .error (.unevaluated (d ++ "." ++ r.asset))
@[expose] def pairsOf (k : Known) : List RMove → Except Refusal (List LegPair)
  | [] => .ok []
  | r :: rs => do let p ← r.pair k; let ps ← pairsOf k rs; pure (p :: ps)
theorem holes_subst_addN (a : Assignment) (x y : NExpr) : ((addN x y).subst a).holes = ((NExpr.add x y).subst a).holes := by cases x <;> cases y <;> simp [addN, NExpr.subst, NExpr.holes]
theorem holes_subst_subN (a : Assignment) (x y : NExpr) : ((subN x y).subst a).holes = ((NExpr.sub x y).subst a).holes := by
  cases x <;> cases y <;> simp only [subN, NExpr.subst, NExpr.holes] <;> try rfl
  rename_i u v
  by_cases h : v ≤ u <;> simp [h, NExpr.subst, NExpr.holes]
theorem holes_subst_peval (k : Known) (a : Assignment) : ∀ e : NExpr, ((e.peval k).subst a).holes = (e.subst a).holes
  | .lit _ | .hole _ | .field (.hole _) _ => rfl
  | .field (.page n) f => by
    simp only [NExpr.peval]
    cases k n <;> rfl
  | .add x y => by simp only [NExpr.peval]; rw [holes_subst_addN]; simp only [NExpr.subst, NExpr.holes, holes_subst_peval k a x, holes_subst_peval k a y]
  | .sub x y => by simp only [NExpr.peval]; rw [holes_subst_subN]; simp only [NExpr.subst, NExpr.holes, holes_subst_peval k a x, holes_subst_peval k a y]
theorem RMove.pair_peval_subst {k' k : Known} (hk : Agrees k' k) (a : Assignment) (r : RMove) : ((r.peval k').subst a).pair k = (r.subst a).pair k := by simp only [RMove.peval, RMove.subst, RMove.pair, eval_subst_peval hk, NExpr.firstHole, holes_subst_peval]
theorem eval_fill_eq_subst_residual {k' k : Known} (hk : Agrees k' k) (f : Form) (a : Assignment) : pairsOf k ((f.residual k').map (·.subst a)) = pairsOf k (f.moves.map fun m => m.unfold.subst a) := by
  unfold Form.residual
  induction f.moves with
  | nil => rfl | cons m ms ih => simp only [List.map_cons, pairsOf]; rw [RMove.pair_peval_subst hk]; simp only [List.map_map] at ih ⊢; rw [ih]
def setEntry (f : String) (v : Nat) (e : String × Data) : String × Data := if e.1 == f then (e.1, .natural v) else e
def putNat (d : Data) (f : String) (v : Nat) : Data :=
  match d with
  | .record fs => if fs.any (·.1 == f) then .record (fs.map (setEntry f v)) else .record (fs ++ [(f, .natural v)]) | _ => .record [(f, .natural v)]
theorem lookup_map_set (f : String) (v : Nat) : ∀ fs : List (String × Data), fs.any (·.1 == f) = true → (fs.map (setEntry f v)).lookup f = some (.natural v)
  | [], h => by simp at h
  | (k, x) :: rest, h => by
    by_cases hk : k = f
    · subst hk; simp [setEntry]
    · have hne : (f == k) = false := by simpa using Ne.symm hk
      have hne' : (k == f) = false := by simpa using hk
      simp only [List.any_cons, hne', Bool.false_or] at h; have ih := lookup_map_set f v rest h; simp only [List.map_cons, setEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup, hne]; exact ih
theorem lookup_map_set_ne (f g : String) (v : Nat) (hg : g ≠ f) : ∀ fs : List (String × Data), (fs.map (setEntry f v)).lookup g = fs.lookup g
  | [] => rfl
  | (k, x) :: rest => by
    have ih := lookup_map_set_ne f g v hg rest
    by_cases hk : k = f
    · subst hk; have hne : (g == k) = false := by simpa using hg
      simp only [List.map_cons, setEntry, beq_self_eq_true, ↓reduceIte, List.lookup, hne]; exact ih
    · have hne' : (k == f) = false := by simpa using hk
      simp only [List.map_cons, setEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup]; split; (next => rfl); (next => exact ih)
theorem lookup_append_absent (f : String) (d : Data) : ∀ fs : List (String × Data), fs.any (·.1 == f) = false → (fs ++ [(f, d)]).lookup f = some d
  | [], _ => by simp
  | (k, x) :: rest, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hne : (f == k) = false := by
      have : k ≠ f := by simpa using h.1
      simpa using Ne.symm this
    simp [List.lookup, hne, lookup_append_absent f d rest h.2]
theorem lookup_append_ne (f g : String) (d : Data) (hg : g ≠ f) : ∀ fs : List (String × Data), (fs ++ [(f, d)]).lookup g = fs.lookup g
  | [] => by
    have hne : (g == f) = false := by simpa using hg
    simp [List.lookup, hne]
  | (k, x) :: rest => by
    simp only [List.cons_append, List.lookup]
    split <;> simp_all [lookup_append_ne f g d hg rest]
theorem natAt_putNat (d : Data) (f : String) (v : Nat) : natAt (putNat d f v) f = v := by
  unfold putNat
  split
  · rename_i fs; split
    · rename_i h; simp [natAt, lookup_map_set f v fs h]
    · rename_i h; have h' : fs.any (·.1 == f) = false := by revert h; cases fs.any (·.1 == f) <;> simp
      simp [natAt, lookup_append_absent f _ fs h']
  · simp [natAt, List.lookup]
theorem natAt_putNat_ne (d : Data) (f g : String) (v : Nat) (hg : g ≠ f) : natAt (putNat d f v) g = natAt d g := by
  unfold putNat
  split
  · rename_i fs; split; (next => simp [natAt, lookup_map_set_ne f g v hg fs]); (next => simp [natAt, lookup_append_ne f g _ hg fs])
  · rename_i hnot; have hne : (g == f) = false := by simpa using hg
    cases d with
    | record fs => exact absurd rfl (hnot fs) | _ => simp [natAt, List.lookup, hne]
def putLabel (d : Data) (f v : String) : Data :=
  match d with
  | .record fs => if fs.any (·.1 == f) then .record (fs.map fun e => if e.1 == f then (f, .label v) else e)
    else .record (fs ++ [(f, .label v)])
  | _ => .record [(f, .label v)]
def setLabelEntry (f v : String) (e : String × Data) : String × Data := if e.1 == f then (f, .label v) else e
theorem lookup_map_label_ne (f v g : String) (hg : g ≠ f) : ∀ fs : List (String × Data), (fs.map (setLabelEntry f v)).lookup g = fs.lookup g
  | [] => rfl
  | (k, x) :: rest => by
    have ih := lookup_map_label_ne f v g hg rest
    by_cases hk : k = f
    · subst hk; have hne : (g == k) = false := by simpa using hg
      simp only [List.map_cons, setLabelEntry, beq_self_eq_true, ↓reduceIte, List.lookup, hne]; exact ih
    · have hne' : (k == f) = false := by simpa using hk
      simp only [List.map_cons, setLabelEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup]; split; (next => rfl); (next => exact ih)
theorem lookup_map_label_eq (f v : String) : ∀ fs : List (String × Data), fs.any (·.1 == f) = true → (fs.map (setLabelEntry f v)).lookup f = some (.label v)
  | [], h => by cases h
  | (k, x) :: rest, h => by
    by_cases hk : k = f
    · subst hk; simp [setLabelEntry, List.lookup]
    · have hne' : (k == f) = false := by simpa using hk
      have hne : (f == k) = false := by simpa using Ne.symm hk
      simp only [List.any_cons, hne', Bool.false_or] at h; simp only [List.map_cons, setLabelEntry, hne', Bool.false_eq_true, ↓reduceIte, List.lookup, hne]; exact lookup_map_label_eq f v rest h
theorem natAt_putLabel (d : Data) (f v A : String) : natAt (putLabel d f v) A = if A = f then 0 else natAt d A := by
  cases d with
  | record fs =>
    simp only [putLabel]
    split
    · rename_i hany; have hm : (fs.map fun e => if e.1 == f then (f, Data.label v) else e) = fs.map (setLabelEntry f v) := rfl
      rw [hm]; by_cases hA : A = f; (next => subst hA; simp [natAt, lookup_map_label_eq A v fs hany]); (next => simp [natAt, lookup_map_label_ne f v A hA fs, hA])
    · rename_i hno; have hno' : fs.any (·.1 == f) = false := Bool.eq_false_iff.mpr hno; by_cases hA : A = f; (next => subst hA; simp [natAt, lookup_append_absent A (.label v) fs hno']); (next => simp [natAt, lookup_append_ne f A (.label v) hA fs, hA])
  | _ =>
    by_cases hA : A = f
    · simp [putLabel, natAt, List.lookup, hA]
    · have hne : (A == f) = false := by simpa using hA
      simp [putLabel, natAt, List.lookup, hne, hA]
def putLabels (d : Data) (vals : List (String × String)) : Data := vals.foldl (fun d fv => putLabel d fv.1 fv.2) d
theorem natAt_putLabels (A : String) : ∀ (vals : List (String × String)) (d : Data), (∀ fv ∈ vals, natAt d fv.1 = 0) → natAt (putLabels d vals) A = natAt d A
  | [], _, _ => rfl
  | (f, v) :: rest, d, h => by
    simp only [putLabels, List.foldl_cons] at h ⊢; have h' : ∀ fv ∈ rest, natAt (putLabel d f v) fv.1 = 0 := by intro fv hfv; rw [natAt_putLabel]; split; (next => rfl); (next => exact h fv (List.mem_cons_of_mem _ hfv))
    rw [show List.foldl (fun d fv => putLabel d fv.1 fv.2) (putLabel d f v) rest = putLabels (putLabel d f v) rest from rfl, natAt_putLabels A rest _ h', natAt_putLabel]
    split; (next => rename_i hA; subst hA; exact (h (A, v) (List.mem_cons_self ..)).symm); (next => rfl)
def SetLeg.delta (tid : ByteArray) (l : SetLeg) : CellDelta := { cell := l.page, preState := l.pre, postState := putLabels l.pre l.vals, touchedFields := l.vals.map (·.1), halfEdges := [], cert := some (.byLoweredDecider "form-set" [] tid) }
def setDeltas (tid : ByteArray) (ls : List SetLeg) : List CellDelta := ls.map (SetLeg.delta tid)
abbrev LegPair.srcDelta (tid : ByteArray) (p : LegPair) : CellDelta := { cell := p.src, preState := p.srcPre, postState := putNat p.srcPre p.asset p.srcAfter, touchedFields := [p.asset], halfEdges := [(p.asset, -(p.amount : Int))], cert := some (.byLoweredDecider "form-leg" [] tid) }
abbrev LegPair.dstDelta (tid : ByteArray) (p : LegPair) : CellDelta := { cell := p.dst, preState := p.dstPre, postState := putNat p.dstPre p.asset p.dstAfter, touchedFields := [p.asset], halfEdges := [(p.asset, (p.amount : Int))], cert := some (.byLoweredDecider "form-leg" [] tid) }
@[expose] def pairDeltas (tid : ByteArray) : List LegPair → List CellDelta
  | [] => [] | p :: ps => p.srcDelta tid :: p.dstDelta tid :: pairDeltas tid ps
theorem foldl_add_int (l : List Int) (acc : Int) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp | cons x xs ih => simp [List.foldl, ih, Int.add_assoc]
theorem deltaAsset_src (tid : ByteArray) (p : LegPair) (a : String) : deltaAsset (p.srcDelta tid) a = if p.asset == a then -(p.amount : Int) else 0 := by
  unfold deltaAsset LegPair.srcDelta
  by_cases h : p.asset = a <;> simp [h]
theorem deltaAsset_dst (tid : ByteArray) (p : LegPair) (a : String) : deltaAsset (p.dstDelta tid) a = if p.asset == a then (p.amount : Int) else 0 := by
  unfold deltaAsset LegPair.dstDelta
  by_cases h : p.asset = a <;> simp [h]
theorem pairs_balanced (tid : ByteArray) (ps : List LegPair) (a : String) : sumAssetDelta (pairDeltas tid ps) a = 0 := by
  unfold sumAssetDelta; rw [foldl_add_int, Int.zero_add]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairDeltas, List.map_cons, List.sum_cons, deltaAsset_src, deltaAsset_dst]; rw [ih]
    split <;> omega
theorem legTurnId_pairDeltas (tid : ByteArray) (ps : List LegPair) : ∀ d ∈ pairDeltas tid ps, legTurnId d = tid := by
  induction ps with
  | nil => intro d hd; cases hd
  | cons p ps ih =>
    intro d hd; simp only [pairDeltas, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    (next => rfl); (next => rfl); (next => exact ih d hd)
abbrev pairsTurn (tid : ByteArray) (pins : Footprint) (occ : Data) (ps : List LegPair) (h : ((pairDeltas tid ps).map CellDelta.cell).Nodup) : VaultTurn where
  turnId := tid
  readPins := pins
  writeCells := pairDeltas tid ps
  occasion := occ
  agree := legTurnId_pairDeltas tid ps
  balanced := pairs_balanced tid ps
  nodup_cells := h
abbrev mayWrite (v : MembraneViewer) (n : String) : Bool := v.permits n && fireGate [.read, .write] v.held
abbrev maySee (v : MembraneViewer) (n : String) : Bool := v.permits n && fireGate [.read] v.held
theorem maySee_of_mayWrite {v : MembraneViewer} {n : String} (h : mayWrite v n = true) : maySee v n = true := by simp only [mayWrite, maySee, Bool.and_eq_true, fireGate_iff_subset] at h ⊢; exact ⟨h.1, fun x hx => h.2 (by simp at hx; simp [hx])⟩
theorem mayWrite_mono {v w : MembraneViewer} (hheld : v.held ⊆ w.held) (hperm : ∀ n, v.permits n = true → w.permits n = true) {n : String} (h : mayWrite v n = true) : mayWrite w n = true := by simp only [mayWrite, Bool.and_eq_true] at h ⊢; exact ⟨hperm n h.1, fireGate_trans hheld h.2⟩
theorem maySee_mono {v w : MembraneViewer} (hheld : v.held ⊆ w.held) (hperm : ∀ n, v.permits n = true → w.permits n = true) {n : String} (h : maySee v n = true) : maySee w n = true := by simp only [maySee, Bool.and_eq_true] at h ⊢; exact ⟨hperm n h.1, fireGate_trans hheld h.2⟩
abbrev checkPage (f : Form) (v : MembraneViewer) (holder : String) : PRef → Except Refusal Unit
  | .hole h => .error (.unfilled h) | .page n => if !f.scope.contains n then .error (.notInForm n holder) else if !mayWrite v n then .error (.notWritable n holder v.held) else .ok ()
@[expose] def checkMoves (f : Form) (v : MembraneViewer) (holder : String) : List RMove → Except Refusal Unit
  | [] => .ok ()
  | r :: rs => do
    checkPage f v holder r.src; checkPage f v holder r.dst
    checkMoves f v holder rs
abbrev gate (root : MembraneViewer) (f : Form) (hops : List Grant) (rs : List RMove) : Except Refusal (MembraneViewer × String) :=
  match resolveChain f.scope root "owner" (f.grants ++ hops) with
  | .error r => .error r
  | .ok (v, holder) =>
    match checkMoves f v holder rs with
    | .error r => .error r | .ok () => .ok (v, holder)
abbrev Form.pinsOf (f : Form) (ps : List LegPair) : Footprint := (ps.flatMap fun p => [p.src, p.dst]).filterMap fun c => (f.known c).map fun d => ⟨c, some d⟩
abbrev Form.fill (f : Form) (a : Assignment) : List RMove := (f.residual f.known).map (·.subst a)
structure Admitted where
  viewer : MembraneViewer
  holder : String
  pairs : List LegPair
  turn : VaultTurn
abbrev admit (root : MembraneViewer) (f : Form) (hops : List Grant) (k : Known) (a : Assignment) (tid : ByteArray) (occ : Data) : Except Refusal Admitted :=
  match gate root f hops (f.fill a) with
  | .error r => .error r
  | .ok (v, holder) =>
    match pairsOf k (f.fill a) with
    | .error r => .error r | .ok ps => if h : ((pairDeltas tid ps).map CellDelta.cell).Nodup then .ok ⟨v, holder, ps, pairsTurn tid (f.pinsOf ps) occ ps h⟩ else .error (.twice ((firstDuplicateCell? ((pairDeltas tid ps).map CellDelta.cell)).getD "?"))
theorem checkPage_ok {f : Form} {v : MembraneViewer} {holder : String} {p : PRef} (h : checkPage f v holder p = .ok ()) : ∃ n, p = .page n ∧ n ∈ f.scope ∧ mayWrite v n = true := by
  cases p with
  | hole x => cases h
  | page n =>
    simp only [checkPage] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2; refine ⟨n, rfl, ?_, ?_⟩
        · exact List.contains_iff_mem.1 (by revert h1; cases f.scope.contains n <;> simp)
        · simpa using h2
theorem checkMoves_ok {f : Form} {v : MembraneViewer} {holder : String} : ∀ {rs : List RMove}, checkMoves f v holder rs = .ok () → ∀ r ∈ rs, checkPage f v holder r.src = .ok () ∧ checkPage f v holder r.dst = .ok ()
  | [], _, r, hr => by cases hr
  | q :: qs, h, r, hr => by
    simp only [checkMoves, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hs; split at h
      · cases h
      · rename_i hd; rcases List.mem_cons.1 hr with rfl | hr
        (next => exact ⟨hs, hd⟩); (next => exact checkMoves_ok h r hr)
theorem gate_ok {root : MembraneViewer} {f : Form} {hops : List Grant} {rs : List RMove} {v : MembraneViewer} {holder : String} (h : gate root f hops rs = .ok (v, holder)) : resolveChain f.scope root "owner" (f.grants ++ hops) = .ok (v, holder) ∧ checkMoves f v holder rs = .ok () := by unfold gate at h; split at h; (next => cases h); (next => rename_i v' holder' hres; split at h; (next => cases h); (next => rename_i hc; simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hres, hc⟩))
theorem RMove.pair_ok {k : Known} {r : RMove} {p : LegPair} (h : r.pair k = .ok p) : r.src = .page p.src ∧ r.dst = .page p.dst ∧ k p.src = some p.srcPre ∧ k p.dst = some p.dstPre ∧ r.amount.eval k = some p.amount ∧ r.debit.eval k = some p.srcAfter ∧ r.credit.eval k = some p.dstAfter ∧ r.asset = p.asset := by
  unfold RMove.pair at h; split at h
  (next => cases h); (next => cases h)
  · rename_i s d hs hd; split at h; (next => cases h); (next => cases h)
    · rename_i ps pd hps hpd; split at h
      · cases h
      · rename_i x hx; split at h
        · rename_i sa da hsa hda; simp only [Except.ok.injEq] at h; subst h; exact ⟨hs, hd, hps, hpd, hx, hsa, hda, rfl⟩
        (next => cases h); (next => cases h)
theorem pairsOf_ok {k : Known} : ∀ {rs : List RMove} {ps : List LegPair}, pairsOf k rs = .ok ps → ∀ p ∈ ps, ∃ r ∈ rs, r.pair k = .ok p
  | [], ps, h, p, hp => by simp only [pairsOf, Except.ok.injEq] at h; subst h; cases hp
  | r :: rs, ps, h, p, hp => by
    simp only [pairsOf, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq; split at h
      · cases h
      · rename_i qs hqs; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rcases List.mem_cons.1 hp with rfl | hp
        (next => exact ⟨r, List.mem_cons_self .., hq⟩); (next => obtain ⟨r', hr', h'⟩ := pairsOf_ok hqs p hp; exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩)
theorem mem_pairDeltas {tid : ByteArray} {d : CellDelta} : ∀ {ps : List LegPair}, d ∈ pairDeltas tid ps → ∃ p ∈ ps, d = p.srcDelta tid ∨ d = p.dstDelta tid
  | [], h => by cases h
  | p :: ps, h => by
    simp only [pairDeltas, List.mem_cons] at h
    rcases h with rfl | rfl | h
    (next => exact ⟨p, List.mem_cons_self .., Or.inl rfl⟩); (next => exact ⟨p, List.mem_cons_self .., Or.inr rfl⟩)
    · obtain ⟨q, hq, hd⟩ := mem_pairDeltas h; exact ⟨q, List.mem_cons_of_mem _ hq, hd⟩
theorem admit_ok {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) : gate root f hops (f.fill a) = .ok (ad.viewer, ad.holder) ∧ pairsOf k (f.fill a) = .ok ad.pairs ∧ ad.turn.writeCells = pairDeltas tid ad.pairs ∧ ad.turn.readPins = f.pinsOf ad.pairs := by unfold admit at h; split at h; (next => cases h); (next => rename_i v holder hg; split at h; (next => cases h); (next => rename_i ps hps; split at h; (next => simp only [Except.ok.injEq] at h; subst h; exact ⟨hg, hps, rfl, rfl⟩); (next => cases h)))
theorem admit_writes {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) : ∀ d ∈ ad.turn.writeCells, mayWrite ad.viewer d.cell = true ∧ d.cell ∈ f.scope := by
  obtain ⟨hg, hps, hw, _⟩ := admit_ok h; obtain ⟨_, hc⟩ := gate_ok hg; intro d hd; rw [hw] at hd; obtain ⟨p, hp, hdp⟩ := mem_pairDeltas hd; obtain ⟨r, hr, hpair⟩ := pairsOf_ok hps p hp; obtain ⟨hsrc, hdst, _⟩ := RMove.pair_ok hpair; obtain ⟨hcs, hcd⟩ := checkMoves_ok hc r hr
  rcases hdp with rfl | rfl
  (next => rw [hsrc] at hcs; obtain ⟨n, hn, hscope, hmay⟩ := checkPage_ok hcs; cases hn; exact ⟨hmay, hscope⟩); (next => rw [hdst] at hcd; obtain ⟨n, hn, hscope, hmay⟩ := checkPage_ok hcd; cases hn; exact ⟨hmay, hscope⟩)
theorem mem_pinsOf {f : Form} {ps : List LegPair} {q : FootprintPin} (hq : q ∈ f.pinsOf ps) : ∃ p ∈ ps, q.cell = p.src ∨ q.cell = p.dst := by
  simp only [Form.pinsOf, List.mem_filterMap, List.mem_flatMap] at hq; obtain ⟨c, ⟨p, hp, hc⟩, hq⟩ := hq
  cases hk : f.known c with
  | none => rw [hk] at hq; cases hq | some d => rw [hk] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; exact ⟨p, hp, hc⟩
theorem srcDelta_mem {tid : ByteArray} {p : LegPair} : ∀ {ps : List LegPair}, p ∈ ps → p.srcDelta tid ∈ pairDeltas tid ps ∧ p.dstDelta tid ∈ pairDeltas tid ps
  | [], h => by cases h
  | q :: qs, h => by
    rcases List.mem_cons.1 h with rfl | h
    (next => simp [pairDeltas]); (next => have := srcDelta_mem (tid := tid) h; simp [pairDeltas, this.1, this.2])
abbrev DirectlyAdmits (v : MembraneViewer) (t : VaultTurn) : Prop := (∀ d ∈ t.writeCells, mayWrite v d.cell = true) ∧ (∀ q ∈ t.readPins, maySee v q.cell = true)
theorem admit_no_amplification {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) : DirectlyAdmits ad.viewer ad.turn ∧ DirectlyAdmits root ad.turn ∧ ad.viewer.held ⊆ root.held ∧ (∀ n, ad.viewer.permits n = true → root.permits n = true) := by
  obtain ⟨hg, hps, hw, hpins⟩ := admit_ok h; obtain ⟨hres, _⟩ := gate_ok hg; obtain ⟨hheld, hperm⟩ := resolveChain_attenuates f.scope _ root "owner" hres; have hwrites := admit_writes h
  have hreads : ∀ q ∈ ad.turn.readPins, maySee ad.viewer q.cell = true := by
    intro q hq; rw [hpins] at hq; obtain ⟨p, hp, hc⟩ := mem_pinsOf hq; have hsd : p.srcDelta tid ∈ ad.turn.writeCells ∧ p.dstDelta tid ∈ ad.turn.writeCells := by rw [hw]; exact srcDelta_mem hp
    rcases hc with hc | hc
    (next => rw [hc]; exact maySee_of_mayWrite (hwrites _ hsd.1).1); (next => rw [hc]; exact maySee_of_mayWrite (hwrites _ hsd.2).1)
  refine ⟨⟨fun d hd => (hwrites d hd).1, hreads⟩, ⟨fun d hd => ?_, fun q hq => ?_⟩, hheld, hperm⟩
  (next => exact mayWrite_mono hheld hperm (hwrites d hd).1); (next => exact maySee_mono hheld hperm (hreads q hq))
theorem admit_hidden_untouched {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) {n : String} (hn : root.permits n = false) : n ∉ ad.turn.writeFootprint ∧ n ∉ ad.turn.readFootprint := by obtain ⟨⟨_, _⟩, ⟨hw, hr⟩, _, _⟩ := admit_no_amplification h; constructor; (next => intro hmem; simp only [VaultTurn.writeFootprint, List.mem_map] at hmem; obtain ⟨d, hd, rfl⟩ := hmem; have := hw d hd; simp [mayWrite, hn] at this); (next => intro hmem; simp only [VaultTurn.readFootprint, List.mem_map] at hmem; obtain ⟨q, hq, rfl⟩ := hmem; have := hr q hq; simp [maySee, hn] at this)
def captureForm (name : String) (grants : List Grant) (v : MembraneViewer) (cs : List Cell) (refs : List String) (holes : List (String × HoleTy)) (moves : List Move) : Form := { name := name, grants := grants, cells := capture v cs, refs := refs, holes := holes, moves := moves }
theorem hidden_change_invisible_through_form (name : String) (grants : List Grant) (v : MembraneViewer) (pre post : List Cell) (c c' : Cell) (hc : shows v c = false) (hc' : shows v c' = false) (refs : List String) (holes : List (String × HoleTy)) (moves : List Move) (root : MembraneViewer) (hops : List Grant) (k : Known) (a : Assignment) (tid : ByteArray) (occ : Data) : captureForm name grants v (pre ++ c :: post) refs holes moves = captureForm name grants v (pre ++ c' :: post) refs holes moves ∧ admit root (captureForm name grants v (pre ++ c :: post) refs holes moves) hops k a tid occ = admit root (captureForm name grants v (pre ++ c' :: post) refs holes moves) hops k a tid occ := by
  have heq : captureForm name grants v (pre ++ c :: post) refs holes moves =
      captureForm name grants v (pre ++ c' :: post) refs holes moves := by
    simp only [captureForm, capture_hidden_change v pre post c c' hc hc']
  exact ⟨heq, by rw [heq]⟩
theorem admit_pairs_honest {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) : ∀ p ∈ ad.pairs, p.srcAfter + p.amount = natAt p.srcPre p.asset ∧ p.dstAfter = natAt p.dstPre p.asset + p.amount := by obtain ⟨_, hps, _, _⟩ := admit_ok h; intro p hp; obtain ⟨r, hr, hpair⟩ := pairsOf_ok hps p hp; simp only [Form.fill, Form.residual, List.map_map, List.mem_map, Function.comp] at hr; obtain ⟨m, _, rfl⟩ := hr; rw [RMove.pair_peval_subst hk] at hpair; obtain ⟨hsrc, hdst, hks, hkd, hx, hdeb, hcred, hasset⟩ := RMove.pair_ok hpair; simp only [Move.unfold, RMove.subst] at hsrc hdst hx hdeb hcred hasset; rw [← hasset]; simp only [NExpr.subst, NExpr.eval, hsrc, hdst, hks, hkd, hx, Option.map_some, Option.bind_eq_bind, Option.bind_some] at hdeb hcred; constructor; (next => split at hdeb; (next => rename_i hle; simp only [pure, Option.some.injEq] at hdeb; omega); (next => cases hdeb)); (next => simp only [pure, Option.some.injEq] at hcred; omega)
theorem admit_halfEdges_honest {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) : ∀ d ∈ ad.turn.writeCells, ∀ A : String, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A := by
  obtain ⟨_, _, hw, _⟩ := admit_ok h; have hhon := admit_pairs_honest hk h; intro d hd A; rw [hw] at hd; obtain ⟨p, hp, hdp⟩ := mem_pairDeltas hd; obtain ⟨h1, h2⟩ := hhon p hp
  rcases hdp with rfl | rfl
  · rw [deltaAsset_src]; simp only [LegPair.srcDelta]; by_cases hA : p.asset = A
    · subst hA; simp only [natAt_putNat, beq_self_eq_true, ↓reduceIte]; omega
    · have hne : (p.asset == A) = false := by simpa using hA
      rw [natAt_putNat_ne _ _ _ _ (Ne.symm hA)]; simp [hne]
  · rw [deltaAsset_dst]; simp only [LegPair.dstDelta]; by_cases hA : p.asset = A
    · subst hA; simp only [natAt_putNat, beq_self_eq_true, ↓reduceIte]; omega
    · have hne : (p.asset == A) = false := by simpa using hA
      rw [natAt_putNat_ne _ _ _ _ (Ne.symm hA)]; simp [hne]
theorem sum_map_add {l : List CellDelta} {post pre δ : CellDelta → Int} (h : ∀ d ∈ l, post d = pre d + δ d) : (l.map post).sum = (l.map pre).sum + (l.map δ).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]; rw [h d (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    omega
theorem admit_conserves_written {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) (A : String) : (ad.turn.writeCells.map fun d => (natAt d.postState A : Int)).sum = (ad.turn.writeCells.map fun d => (natAt d.preState A : Int)).sum := by
  rw [sum_map_add (δ := fun d => deltaAsset d A) (admit_halfEdges_honest hk h · · A)]
  have hb := ad.turn.balanced A; unfold sumAssetDelta at hb; rw [foldl_add_int, Int.zero_add] at hb; rw [hb, Int.add_zero]
def total (s : VaultStore) (A : String) (cs : List String) : Int := (cs.map fun c => (((s c).map (natAt · A)).getD 0 : Int)).sum
theorem sum_filter_or {α : Type} (l : List α) (p q : α → Bool) (g : α → Int) (hdis : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) : ((l.filter fun x => p x || q x).map g).sum = ((l.filter p).map g).sum + ((l.filter q).map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih fun y hy => hdis y (List.mem_cons_of_mem _ hy)
    have hx := hdis x (List.mem_cons_self ..)
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega
theorem filter_cell_single {d : CellDelta} : ∀ {W : List CellDelta}, (W.map CellDelta.cell).Nodup → d ∈ W → (W.filter fun x => x.cell == d.cell) = [d]
  | [], _, hd => by cases hd
  | x :: xs, hnd, hd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hd with rfl | hd'
    · have : (xs.filter fun y => y.cell == d.cell) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy hyc; exact hnd.1 (by simp at hyc; rw [← hyc]; exact List.mem_map_of_mem hy)
      simp [this]
    · have hne : (x.cell == d.cell) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; exact hnd.1 (he ▸ List.mem_map_of_mem hd')
      simp [hne, filter_cell_single hnd.2 hd']
theorem change_at (s : VaultStore) (t : VaultTurn) (A c : String) (hpre : ∀ d ∈ t.writeCells, s d.cell = some d.preState) : ((((applyTurn s t c).map (natAt · A)).getD 0 : Nat) : Int) - (((s c).map (natAt · A)).getD 0 : Nat) = ((t.writeCells.filter fun d => d.cell == c).map fun d => (natAt d.postState A : Int) - natAt d.preState A).sum := by
  by_cases hc : c ∈ t.writeFootprint
  · simp only [VaultTurn.writeFootprint, List.mem_map] at hc; obtain ⟨d, hd, rfl⟩ := hc; rw [applyTurn_write s t d hd, hpre d hd]; rw [filter_cell_single t.nodup_cells hd]; simp
  · rw [applyTurn_frame_of_not_mem s t c hc]; have : (t.writeCells.filter fun d => d.cell == c) = [] := by rw [List.filter_eq_nil_iff]; intro d hd hdc; simp at hdc; exact hc (hdc ▸ List.mem_map_of_mem hd)
    simp [this]
theorem sum_over_cells (W : List CellDelta) (h : CellDelta → Int) : ∀ cs : List String, cs.Nodup → (cs.map fun c => ((W.filter fun d => d.cell == c).map h).sum).sum = ((W.filter fun d => cs.contains d.cell).map h).sum
  | [], _ => by
    have : (W.filter fun d => ([] : List String).contains d.cell) = [] := by rw [List.filter_eq_nil_iff]; intro d _; simp
    rw [this]; rfl
  | c :: rest, hnd => by
    rw [List.nodup_cons] at hnd; rw [List.map_cons, List.sum_cons, sum_over_cells W h rest hnd.2]
    have hsplit := sum_filter_or W (fun d => d.cell == c) (fun d => rest.contains d.cell) h (by
      intro d _ ⟨h1, h2⟩; simp at h1 h2
      exact hnd.1 (h1 ▸ h2))
    have hfun : (fun d : CellDelta => (c :: rest).contains d.cell) =
        (fun d => (d.cell == c) || rest.contains d.cell) := by
      funext d; simp only [List.contains_cons]
    rw [hfun, hsplit]
theorem applyTurn_conserves_total (s : VaultStore) (t : VaultTurn) (A : String) (cs : List String) (hcs : cs.Nodup) (hw : ∀ c ∈ t.writeFootprint, c ∈ cs) (hpre : ∀ d ∈ t.writeCells, s d.cell = some d.preState) (hhon : ∀ d ∈ t.writeCells, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A) : total (applyTurn s t) A cs = total s A cs := by
  unfold total
  have hdiff : ∀ c ∈ cs, ((((applyTurn s t c).map (natAt · A)).getD 0 : Nat) : Int) =
      (((s c).map (natAt · A)).getD 0 : Nat) +
        ((t.writeCells.filter fun d => d.cell == c).map fun d =>
          (natAt d.postState A : Int) - natAt d.preState A).sum := by
    intro c _; have := change_at s t A c hpre; omega
  rw [List.map_congr_left hdiff]
  rw [show ∀ (l : List String) (f g : String → Int), (l.map fun c => f c + g c).sum = (l.map f).sum + (l.map g).sum
    from fun l f g => by induction l <;> simp_all [Int.add_assoc, Int.add_left_comm]]
  rw [sum_over_cells _ _ cs hcs]; have hall : (t.writeCells.filter fun d => cs.contains d.cell) = t.writeCells := by rw [List.filter_eq_self]; intro d hd; simpa using hw d.cell (List.mem_map_of_mem hd)
  rw [hall]
  have hz : (t.writeCells.map fun d => (natAt d.postState A : Int) - natAt d.preState A).sum = 0 := by
    have hb := t.balanced A; unfold sumAssetDelta at hb; rw [foldl_add_int, Int.zero_add] at hb; rw [← hb]
    congr 1
    exact List.map_congr_left fun d hd => by have := hhon d hd; omega
  rw [hz, Int.add_zero]
theorem admit_conserves_total {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {ad : Admitted} (h : admit root f hops k a tid occ = .ok ad) (s : VaultStore) (hpre : ∀ d ∈ ad.turn.writeCells, s d.cell = some d.preState) (A : String) (cs : List String) (hcs : cs.Nodup) (hw : ∀ c ∈ ad.turn.writeFootprint, c ∈ cs) : total (applyTurn s ad.turn) A cs = total s A cs := applyTurn_conserves_total s ad.turn A cs hcs hw hpre fun d hd => admit_halfEdges_honest hk h d hd A
def Form.fillSets (f : Form) (a : Assignment) : List SetMove := (f.setResidual f.known).map (·.subst a)
theorem eval_fill_eq_subst_residual_sets {k' kv : Known} (hk : Agrees k' kv) (kp : Known) (f : Form) (a : Assignment) : setsOf kv kp ((f.setResidual k').map (·.subst a)) = setsOf kv kp (f.sets.map (·.subst a)) := by
  unfold Form.setResidual
  induction f.sets with
  | nil => rfl | cons m ms ih => simp only [List.map_cons, setsOf]; rw [SetMove.leg_peval_subst hk]; simp only [List.map_map] at ih ⊢; rw [ih]
def checkSets (f : Form) (v : MembraneViewer) (holder : String) : List SetMove → Except Refusal Unit
  | [] => .ok ()
  | m :: ms => do checkPage f v holder m.page; checkSets f v holder ms
theorem checkSets_ok {f : Form} {v : MembraneViewer} {holder : String} : ∀ {ms : List SetMove}, checkSets f v holder ms = .ok () → ∀ m ∈ ms, checkPage f v holder m.page = .ok ()
  | [], _, m, hm => by cases hm
  | q :: qs, h, m, hm => by
    simp only [checkSets, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hq; rcases List.mem_cons.1 hm with rfl | hm
      (next => exact hq); (next => exact checkSets_ok h m hm)
theorem evalFields_ok {kv : Known} {page : String} {pre : Data} : ∀ {fs : List (String × SExpr)} {vs : List (String × String)}, evalFields kv page pre fs = .ok vs → ∀ fv ∈ vs, natAt pre fv.1 = 0
  | [], vs, h, fv, hfv => by simp only [evalFields, Except.ok.injEq] at h; subst h; cases hfv
  | (f, e) :: rest, vs, h, fv, hfv => by
    simp only [evalFields] at h
    split at h
    · cases h
    · rename_i v hv; split at h
      · cases h
      · rename_i hnat; split at h
        · cases h
        · split at h
          · cases h
          · rename_i vs' hrest; simp only [Except.ok.injEq] at h; subst h; rcases List.mem_cons.1 hfv with rfl | hfv
            (next => simpa using hnat); (next => exact evalFields_ok hrest fv hfv)
theorem SetMove.leg_ok {kv kp : Known} {m : SetMove} {l : SetLeg} (h : m.leg kv kp = .ok l) : m.page = .page l.page ∧ kp l.page = some l.pre ∧ ∀ fv ∈ l.vals, natAt l.pre fv.1 = 0 := by unfold SetMove.leg at h; split at h; (next => cases h); (next => rename_i n hn; split at h; (next => cases h); (next => rename_i d hd; split at h; (next => cases h); (next => rename_i vs hvs; simp only [Except.ok.injEq] at h; subst h; exact ⟨hn, hd, evalFields_ok hvs⟩)))
theorem setsOf_ok {kv kp : Known} : ∀ {ms : List SetMove} {ls : List SetLeg}, setsOf kv kp ms = .ok ls → ∀ l ∈ ls, ∃ m ∈ ms, m.leg kv kp = .ok l
  | [], ls, h, l, hl => by simp only [setsOf, Except.ok.injEq] at h; subst h; cases hl
  | m :: ms, ls, h, l, hl => by
    simp only [setsOf, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq; split at h
      · cases h
      · rename_i qs hqs; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rcases List.mem_cons.1 hl with rfl | hl
        (next => exact ⟨m, List.mem_cons_self .., hq⟩); (next => obtain ⟨m', hm', h'⟩ := setsOf_ok hqs l hl; exact ⟨m', List.mem_cons_of_mem _ hm', h'⟩)
theorem sum_deltaAsset_setDeltas (tid : ByteArray) (ls : List SetLeg) (a : String) : ((setDeltas tid ls).map fun d => deltaAsset d a).sum = 0 := by
  induction ls with
  | nil => rfl | cons l ls ih => simp only [setDeltas, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; simp [deltaAsset, SetLeg.delta]
def fillTurn (t : VaultTurn) (ls : List SetLeg) (h : ((t.writeCells ++ setDeltas t.turnId ls).map CellDelta.cell).Nodup) : VaultTurn where
  turnId := t.turnId
  readPins := t.readPins
  writeCells := t.writeCells ++ setDeltas t.turnId ls
  occasion := t.occasion
  agree := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    (next => exact t.agree d hd); (next => simp only [setDeltas, List.mem_map] at hd; obtain ⟨l, _, rfl⟩ := hd; rfl)
  balanced := fun a => by have hb := t.balanced a; unfold sumAssetDelta at hb ⊢; rw [foldl_add_int, Int.zero_add] at hb ⊢; rw [List.map_append, List.sum_append, hb, sum_deltaAsset_setDeltas, Int.add_zero]
  nodup_cells := h
structure Filled where
  ad : Admitted
  sets : List SetLeg
  turn : VaultTurn
def admitFill (root : MembraneViewer) (f : Form) (hops : List Grant) (k : Known) (a : Assignment) (tid : ByteArray) (occ : Data) : Except Refusal Filled :=
  match gate root f hops (f.fill a) with
  | .error r => .error r
  | .ok (v, holder) =>
    match checkSets f v holder (f.fillSets a) with
    | .error r => .error r
    | .ok () =>
      match admit root f hops k a tid occ with
      | .error r => .error r
      | .ok ad =>
        match setsOf f.known k (f.fillSets a) with
        | .error r => .error r | .ok ls => if h : ((ad.turn.writeCells ++ setDeltas ad.turn.turnId ls).map CellDelta.cell).Nodup then .ok ⟨ad, ls, fillTurn ad.turn ls h⟩ else .error (.twice ((firstDuplicateCell? ((ad.turn.writeCells ++ setDeltas ad.turn.turnId ls).map CellDelta.cell)).getD "?"))
theorem admitFill_ok {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {fl : Filled} (h : admitFill root f hops k a tid occ = .ok fl) : admit root f hops k a tid occ = .ok fl.ad ∧ checkSets f fl.ad.viewer fl.ad.holder (f.fillSets a) = .ok () ∧ setsOf f.known k (f.fillSets a) = .ok fl.sets ∧ fl.turn.writeCells = fl.ad.turn.writeCells ++ setDeltas fl.ad.turn.turnId fl.sets ∧ fl.turn.readPins = fl.ad.turn.readPins := by
  unfold admitFill at h
  split at h
  · cases h
  · rename_i v holder hg; split at h; (next => cases h); (next => rename_i hc; split at h; (next => cases h); (next => rename_i ad had; have hg' := (admit_ok had).1; rw [hg] at hg'; simp only [Except.ok.injEq, Prod.mk.injEq] at hg'; obtain ⟨rfl, rfl⟩ := hg'; split at h; (next => cases h); (next => rename_i ls hls; split at h; (next => simp only [Except.ok.injEq] at h; subst h; exact ⟨had, hc, hls, rfl, rfl⟩); (next => cases h))))
theorem admitFill_writes {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {fl : Filled} (h : admitFill root f hops k a tid occ = .ok fl) : ∀ d ∈ fl.turn.writeCells, mayWrite fl.ad.viewer d.cell = true ∧ d.cell ∈ f.scope := by
  obtain ⟨had, hc, hls, hw, _⟩ := admitFill_ok h; intro d hd; rw [hw] at hd
  rcases List.mem_append.1 hd with hd | hd
  (next => exact admit_writes had d hd); (next => simp only [setDeltas, List.mem_map] at hd; obtain ⟨l, hl, rfl⟩ := hd; obtain ⟨m, hm, hleg⟩ := setsOf_ok hls l hl; obtain ⟨hpage, _, _⟩ := SetMove.leg_ok hleg; have hcp := checkSets_ok hc m hm; rw [hpage] at hcp; obtain ⟨n, hn, hscope, hmay⟩ := checkPage_ok hcp; cases hn; exact ⟨hmay, hscope⟩)
theorem admitFill_no_amplification {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} {a : Assignment} {tid : ByteArray} {occ : Data} {fl : Filled} (h : admitFill root f hops k a tid occ = .ok fl) : DirectlyAdmits fl.ad.viewer fl.turn ∧ DirectlyAdmits root fl.turn ∧ fl.ad.viewer.held ⊆ root.held ∧ (∀ n, fl.ad.viewer.permits n = true → root.permits n = true) := by obtain ⟨had, _, _, _, hpins⟩ := admitFill_ok h; obtain ⟨⟨_, hvr⟩, ⟨_, hrr⟩, hheld, hperm⟩ := admit_no_amplification had; have hwrites := admitFill_writes h; refine ⟨⟨fun d hd => (hwrites d hd).1, fun q hq => hvr q (hpins ▸ hq)⟩, ⟨fun d hd => mayWrite_mono hheld hperm (hwrites d hd).1, fun q hq => hrr q (hpins ▸ hq)⟩, hheld, hperm⟩
theorem admitFill_halfEdges_honest {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {fl : Filled} (h : admitFill root f hops k a tid occ = .ok fl) : ∀ d ∈ fl.turn.writeCells, ∀ A : String, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A := by
  obtain ⟨had, _, hls, hw, _⟩ := admitFill_ok h; intro d hd A; rw [hw] at hd
  rcases List.mem_append.1 hd with hd | hd
  · exact admit_halfEdges_honest hk had d hd A
  · simp only [setDeltas, List.mem_map] at hd; obtain ⟨l, hl, rfl⟩ := hd; obtain ⟨m, _, hleg⟩ := setsOf_ok hls l hl; obtain ⟨_, _, hzero⟩ := SetMove.leg_ok hleg; simp only [SetLeg.delta, deltaAsset, List.find?_nil, Int.add_zero]
    rw [natAt_putLabels A l.vals l.pre hzero]
theorem admitFill_conserves_total {root : MembraneViewer} {f : Form} {hops : List Grant} {k : Known} (hk : Agrees f.known k) {a : Assignment} {tid : ByteArray} {occ : Data} {fl : Filled} (h : admitFill root f hops k a tid occ = .ok fl) (s : VaultStore) (hpre : ∀ d ∈ fl.turn.writeCells, s d.cell = some d.preState) (A : String) (cs : List String) (hcs : cs.Nodup) (hw : ∀ c ∈ fl.turn.writeFootprint, c ∈ cs) : total (applyTurn s fl.turn) A cs = total s A cs := applyTurn_conserves_total s fl.turn A cs hcs hw hpre fun d hd => admitFill_halfEdges_honest hk h d hd A
theorem admitFill_gate_first {root : MembraneViewer} {f : Form} {hops : List Grant} {a : Assignment} {v : MembraneViewer} {holder : String} {r : Refusal} (hg : gate root f hops (f.fill a) = .ok (v, holder)) (hc : checkSets f v holder (f.fillSets a) = .error r) (k : Known) (tid : ByteArray) (occ : Data) : admitFill root f hops k a tid occ = .error r := by simp only [admitFill, hg, hc]
theorem admitFill_no_sets {root : MembraneViewer} {f : Form} (hs : f.sets = []) (hops : List Grant) (k : Known) (a : Assignment) (tid : ByteArray) (occ : Data) : (admitFill root f hops k a tid occ).map (·.ad) = admit root f hops k a tid occ := by
  have hfs : f.fillSets a = [] := by simp [Form.fillSets, Form.setResidual, hs]
  unfold admitFill; rw [hfs]
  cases hg : gate root f hops (f.fill a) with
  | error r => simp only [Except.map]; simp only [admit, hg]
  | ok vh =>
    obtain ⟨v, holder⟩ := vh; simp only [checkSets]
    cases had : admit root f hops k a tid occ with
    | error r => rfl
    | ok ad =>
      simp only [setsOf, setDeltas, List.map_nil, List.append_nil]; rw [dite_eq_left (by simpa using ad.turn.nodup_cells)]
      rfl
def Move.abstractNat (v : Nat) (h : String) (m : Move) : Move := { m with amount := m.amount.abstractNat v h }
def Move.abstractPage (n h : String) (m : Move) : Move :=
  { m with src := m.src.abstractPage n h, dst := m.dst.abstractPage n h, amount := m.amount.abstractPage n h }
def Move.holes (m : Move) : List String := m.src.holes ++ m.dst.holes ++ m.amount.holes
theorem PRef.subst_nats (p : PRef) (a : Assignment) (x : String × Nat) : p.subst ⟨x :: a.nats, a.pages, a.labels⟩ = p.subst a := by cases p <;> rfl
theorem Move.unfold_subst_abstractNat (v : Nat) (h : String) (a : Assignment) (m : Move) (hf : h ∉ m.holes) : (m.abstractNat v h).unfold.subst ⟨(h, v) :: a.nats, a.pages, a.labels⟩ = m.unfold.subst a := by simp only [Move.holes, List.mem_append, not_or] at hf; simp only [Move.abstractNat, Move.unfold, RMove.subst, NExpr.subst, PRef.subst_nats, NExpr.subst_abstractNat_cons v h a m.amount hf.2]
theorem Move.unfold_subst_abstractPage (n h : String) (a : Assignment) (m : Move) (hf : h ∉ m.holes) : (m.abstractPage n h).unfold.subst ⟨a.nats, (h, n) :: a.pages, a.labels⟩ = m.unfold.subst a := by simp only [Move.holes, List.mem_append, not_or] at hf; simp only [Move.abstractPage, Move.unfold, RMove.subst, NExpr.subst, PRef.subst_abstractPage_cons n h a m.src hf.1.1, PRef.subst_abstractPage_cons n h a m.dst hf.1.2, NExpr.subst_abstractPage_cons n h a m.amount hf.2]
def Form.abstractNat (f : Form) (v : Nat) (h : String) : Form :=
  { f with moves := f.moves.map (·.abstractNat v h), holes := f.holes ++ [(h, .nat)] }
def Form.abstractPage (f : Form) (n h : String) : Form :=
  { f with moves := f.moves.map (·.abstractPage n h), holes := f.holes ++ [(h, .page)] }
theorem abstract_then_fill {k : Known} (f : Form) (hk : Agrees f.known k) (a : Assignment) (h : String) (hf : ∀ m ∈ f.moves, h ∉ m.holes) : (∀ v : Nat, pairsOf k ((f.abstractNat v h).fill ⟨(h, v) :: a.nats, a.pages, a.labels⟩) = pairsOf k (f.fill a)) ∧ (∀ n : String, pairsOf k ((f.abstractPage n h).fill ⟨a.nats, (h, n) :: a.pages, a.labels⟩) = pairsOf k (f.fill a)) := by constructor; (next => intro v; have hk' : Agrees (f.abstractNat v h).known k := hk; simp only [Form.fill]; rw [eval_fill_eq_subst_residual hk', eval_fill_eq_subst_residual hk]; congr 1; simp only [Form.abstractNat, List.map_map]; exact List.map_congr_left fun m hm => Move.unfold_subst_abstractNat v h a m (hf m hm)); (next => intro n; have hk' : Agrees (f.abstractPage n h).known k := hk; simp only [Form.fill]; rw [eval_fill_eq_subst_residual hk', eval_fill_eq_subst_residual hk]; congr 1; simp only [Form.abstractPage, List.map_map]; exact List.map_congr_left fun m hm => Move.unfold_subst_abstractPage n h a m (hf m hm))
def Form.abstract (f : Form) (value hole : String) : Except String Form := if f.holes.any (·.1 == hole) || (f.moves.flatMap Move.holes).contains hole then .error ("the form " ++ f.name ++ " has a hole named " ++ hole)
  else match value.toNat? with
    | some v =>
      let g := f.abstractNat v hole
      if g.moves == f.moves then .error ("no " ++ value ++ " in the moves of " ++ f.name) else .ok g
    | none =>
      let g := f.abstractPage value hole
      if g.moves == f.moves then .error ("no page " ++ value ++ " in the moves of " ++ f.name) else .ok g
def setFront (md field : String) (v : Nat) : Option String :=
  match md.splitOn "\n" with
  | first :: rest =>
    if trim first != "---" then none else
    let fm := rest.takeWhile fun l => trim l != "---"
    let after := rest.drop fm.length; let isField (l : String) : Bool := (splitColon l).map (·.1) == some field
    if after.isEmpty || !(fm.any isField) then none else some ("\n".intercalate (first :: fm.map (fun l => if isField l then field ++ ": " ++ toString v else l) ++ after))
  | [] => none
def setFrontLine (md field value : String) (insert : Bool) : Option String :=
  match md.splitOn "\n" with
  | first :: rest =>
    if trim first != "---" then none else
    let fm := rest.takeWhile fun l => trim l != "---"
    let after := rest.drop fm.length; let isField (l : String) : Bool := (splitColon l).map (·.1) == some field
    if after.isEmpty then none else if fm.any isField then some ("\n".intercalate (first :: fm.map (fun l => if isField l then field ++ ": " ++ value else l) ++ after)) else if insert then some ("\n".intercalate (first :: fm ++ [field ++ ": " ++ value] ++ after)) else none
  | [] => none
def frontValue (d : Data) (f : String) : String × Bool :=
  match d with
  | .record fs => match fs.lookup f with
    | some (.label v) => ("\"" ++ v ++ "\"", true) | _ => (toString (natAt d f), false)
  | _ => (toString (natAt d f), false)
def setFronts (md : String) (d : Data) : List String → Option String
  | [] => some md | f :: fs => (setFrontLine md f (frontValue d f).1 (frontValue d f).2).bind fun md' => setFronts md' d fs
@[expose] def legWritesOf (H : Obend.Digest.HashBytes.Hash) (s : Store) (poster : String) : List CellDelta → Except String (List (Page × Graph × List (AtomId × String)))
  | [] => .ok []
  | d :: ds =>
    match s.page? d.cell with
    | none => .error (d.cell ++ " is not a page here")
    | some p =>
      match p.current, p.render?, d.touchedFields.head? with
      | some G, some md, some field =>
        match setFront md field (natAt d.postState field) with
        | none => .error (d.cell ++ " has no frontmatter line `" ++ field ++ ":`")
        | some md' =>
          let b := editPatch H G (align (pieces G p.name p.who) (Obend.Doc.contents (resolveIn H s.entries) (stripToks (Obend.Doc.tokens md')))) "owner"
          if b.ops.isEmpty then .error ("at " ++ d.cell ++ ": the fill changes nothing")
          else match legWritesOf H s poster ds with
            | .error e => .error e | .ok ws => .ok ((p, G.apply b.ops, b.added.map (·, poster)) :: ws)
      | _, _, _ => .error (d.cell ++ " has no version to write")
theorem legWritesOf_ok {H : Obend.Digest.HashBytes.Hash} {s : Store} {poster : String} : ∀ {ds : List CellDelta} {ws : List (Page × Graph × List (AtomId × String))}, legWritesOf H s poster ds = .ok ws → ws.map (·.1.name) = ds.map (·.cell) ∧ ∀ w ∈ ws, s.page? w.1.name = some w.1
  | [], ws, h => by simp only [legWritesOf, Except.ok.injEq] at h; subst h; simp
  | d :: ds, ws, h => by
    simp only [legWritesOf] at h
    split at h
    · cases h
    · rename_i p hp
      have hpn : p.name = d.cell := by
        unfold Store.page? at hp
        simpa using List.find?_some hp
      split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i ws' hws; simp only [Except.ok.injEq] at h; subst h; obtain ⟨ih1, ih2⟩ := legWritesOf_ok hws; refine ⟨by simp [hpn, ih1], fun w hw => ?_⟩
              rcases List.mem_cons.1 hw with rfl | hw
              (next => simpa [hpn] using hp); (next => exact ih2 w hw)
      · cases h
def setWritesOf (H : Obend.Digest.HashBytes.Hash) (s : Store) (poster : String) : List CellDelta → Except String (List (Page × Graph × List (AtomId × String)))
  | [] => .ok []
  | d :: ds =>
    match s.page? d.cell with
    | none => .error (d.cell ++ " is not a page here")
    | some p =>
      match p.current, p.render? with
      | some G, some md =>
        match setFronts md d.postState d.touchedFields with
        | none => .error (d.cell ++ " has no frontmatter to set " ++ ", ".intercalate d.touchedFields ++ " in")
        | some md' =>
          let b := editPatch H G (align (pieces G p.name p.who) (Obend.Doc.contents (resolveIn H s.entries) (stripToks (Obend.Doc.tokens md')))) "owner"
          if b.ops.isEmpty then .error ("at " ++ d.cell ++ ": the fill changes nothing")
          else match setWritesOf H s poster ds with
            | .error e => .error e | .ok ws => .ok ((p, G.apply b.ops, b.added.map (·, poster)) :: ws)
      | _, _ => .error (d.cell ++ " has no version to write")
theorem setWritesOf_ok {H : Obend.Digest.HashBytes.Hash} {s : Store} {poster : String} : ∀ {ds : List CellDelta} {ws : List (Page × Graph × List (AtomId × String))}, setWritesOf H s poster ds = .ok ws → ws.map (·.1.name) = ds.map (·.cell)
  | [], ws, h => by simp only [setWritesOf, Except.ok.injEq] at h; subst h; simp
  | d :: ds, ws, h => by
    simp only [setWritesOf] at h
    split at h
    · cases h
    · rename_i p hp
      have hpn : p.name = d.cell := by
        unfold Store.page? at hp
        simpa using List.find?_some hp
      split at h; (next => split at h; (next => cases h); (next => split at h; (next => cases h); (next => split at h; (next => cases h); (next => rename_i ws' hws; simp only [Except.ok.injEq] at h; subst h; simp [hpn, setWritesOf_ok hws])))); (next => cases h)
abbrev landedDelta (assets : List String) (pr : Prepared) : CellDelta := { cell := pr.p.name, preState := pr.o, postState := pr.n, touchedFields := assets, halfEdges := assets.map fun A => (A, (natAt pr.n A : Int) - natAt pr.o A), cert := some (.byLoweredDecider "form-leg" [] ByteArray.empty) }
theorem deltaAsset_landed (assets : List String) (pr : Prepared) (A : String) : deltaAsset (landedDelta assets pr) A = if A ∈ assets then (natAt pr.n A : Int) - natAt pr.o A else 0 := by
  unfold deltaAsset landedDelta; simp only
  induction assets with
  | nil => simp
  | cons B bs ih =>
    by_cases hB : B = A
    · subst hB; simp
    · have hne : (B == A) = false := by simpa using hB
      simp only [List.map_cons, List.find?_cons, hne] at ih ⊢
      rw [ih]; simp [Ne.symm hB]
abbrev Form.assets (f : Form) : List String := (f.moves.map (·.asset)).eraseDups
abbrev landedTurn (f : Form) (pins : Footprint) (occ : Data) (prs : List Prepared) : Except String VaultTurn :=
  if hn : ((prs.map (landedDelta f.assets)).map CellDelta.cell).Nodup then
    if hb : f.assets.all (fun A => sumAssetDelta (prs.map (landedDelta f.assets)) A == 0) = true then
      .ok { turnId := ByteArray.empty, readPins := pins, writeCells := prs.map (landedDelta f.assets), occasion := occ,
            agree := by
              intro d hd; simp only [List.mem_map] at hd; obtain ⟨pr, _, rfl⟩ := hd
              rfl,
            balanced := fun A => by
              by_cases hA : A ∈ f.assets
              · simpa using List.all_eq_true.1 hb A hA
              · have h0 : ∀ pr, deltaAsset (landedDelta f.assets pr) A = 0 := fun pr => by
                  rw [deltaAsset_landed]; simp [hA]
                have hl : ∀ l : List Prepared, (l.map fun pr => deltaAsset (landedDelta f.assets pr) A).sum = 0 := by intro l; induction l <;> simp_all
                unfold sumAssetDelta; rw [foldl_add_int, Int.zero_add, List.map_map]
                exact hl prs,
            nodup_cells := hn }
    else .error ("refused: the turn as written does not conserve " ++ ", ".intercalate (f.assets.map fun A => A ++ " (net " ++ toString (sumAssetDelta (prs.map (landedDelta f.assets)) A) ++ ")"))
  else .error "refused: the turn writes a page twice"
theorem landedTurn_ok {f : Form} {pins : Footprint} {occ : Data} {prs : List Prepared} {t : VaultTurn} (h : landedTurn f pins occ prs = .ok t) : t.writeCells = prs.map (landedDelta f.assets) ∧ t.readPins = pins := by unfold landedTurn at h; split at h; (next => split at h; (next => simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩); (next => cases h)); (next => cases h)
def authName : Auth → String
  | .read => "read" | .write => "write" | .grant => "grant" | .call => "call" | .reply => "reply" | .reset => "reset" | .control => "control" | .notify => "notify"
def authOf : String → Option Auth
  | "read" => some .read | "write" => some .write | "grant" => some .grant | "call" => some .call | "reply" => some .reply | "reset" => some .reset | "control" => some .control | "notify" => some .notify | _ => none
def showAuths (l : List Auth) : String := if l.isEmpty then "nothing" else ", ".intercalate (l.map authName)
def refusalText (f : Form) : Refusal → String
  | .amplifies who delegate held asked => "refused by the membrane: " ++ who ++ " holds " ++ showAuths held ++ "; resharing " ++ showAuths asked ++ " to " ++ delegate ++ " would amplify it"
  | .notInForm page holder => "refused by the membrane: " ++ page ++ " is not a page of this form (" ++ holder ++ " may name " ++ ", ".intercalate f.scope ++ ")"
  | .notWritable page holder held => "refused by the membrane: " ++ holder ++ "'s grant does not let it write " ++ page ++ " (it holds " ++ showAuths held ++ ")"
  | .unfilled h => "refused: the hole " ++ h ++ " is not filled" | .unknownPage page => "refused: " ++ page ++ " has no state to read"
  | .resources page asset holds moves => "refused by the form's resources: " ++ page ++ " holds " ++ asset ++ " " ++ toString holds ++ "; the fill moves " ++ toString moves
  | .unevaluated what => "refused: " ++ what ++ " does not evaluate" | .twice page => "refused: the fill writes " ++ page ++ " twice" | .numeric page field => "refused: " ++ page ++ " holds " ++ field ++ " as a number; a set writes labels only" | .illFormed page field => "refused: the value for " ++ page ++ "." ++ field ++ " cannot be a frontmatter line (it holds a newline or a double quote)"
abbrev ownerViewer (f : Form) : MembraneViewer := ownerGrant.viewer f.scope
abbrev judgeProposal (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) (hops : List Grant) (a : Assignment) : Except String (Store × Admitted × VaultTurn) :=
  match admit (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty
      (.label f.name) with
  | .error r => .error (refusalText f r)
  | .ok ad =>
    match admitFootprint (stateStore s.entries) ad.turn.readPins with
    | .error (.footprintStale cell exp cur) => .error ("refused: stale: the form read " ++ cell ++ " as it was when captured (" ++ stateDiffText exp cur ++ "); capture it again")
    | .error _ => .error "refused: its pins do not hold here"
    | .ok _ =>
      match legWritesOf H s ad.holder ad.turn.writeCells with
      | .error e => .error e
      | .ok ws =>
        match commitTurn s.entries s.entries ws .owner s.turn ad.holder s.environment with
        | .error e => .error e
        | .ok prs =>
          match landedTurn f ad.turn.readPins ad.turn.occasion prs with
          | .error e => .error e | .ok t => .ok (s.landAll prs, ad, t)
theorem judgeProposal_gate_first (H : Obend.Digest.HashBytes.Hash) (f : Form) (hops : List Grant) (a : Assignment) {r : Refusal} (hg : gate (ownerViewer f) f hops (f.fill a) = .error r) (s : Store) : judgeProposal H s f hops a = .error (refusalText f r) := by simp only [judgeProposal, admit, hg]
theorem judgeProposal_ok {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant} {a : Assignment} {ad : Admitted} {t : VaultTurn} (h : judgeProposal H s f hops a = .ok (s', ad, t)) : admit (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty (.label f.name) = .ok ad ∧ admitFootprint (stateStore s.entries) ad.turn.readPins = .ok () ∧ ∃ ws prs, legWritesOf H s ad.holder ad.turn.writeCells = .ok ws ∧ commitTurn s.entries s.entries ws .owner s.turn ad.holder s.environment = .ok prs ∧ landedTurn f ad.turn.readPins ad.turn.occasion prs = .ok t ∧ s' = s.landAll prs := by
  unfold judgeProposal at h
  split at h
  · cases h
  · rename_i ad' had; split at h; (next => cases h); (next => cases h)
    · rename_i u hfp; split at h; (next => cases h); (next => rename_i ws hws; split at h; (next => cases h); (next => rename_i prs hprs; split at h; (next => cases h); (next => rename_i t' ht; simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨had, hfp, ws, prs, hws, hprs, ht, rfl⟩)))
theorem judgeProposal_atomic {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant} {a : Assignment} {ad : Admitted} {t : VaultTurn} (h : judgeProposal H s f hops a = .ok (s', ad, t)) : t.writeFootprint = ad.turn.writeFootprint ∧ (∀ n, n ∉ t.writeFootprint → s'.page? n = s.page? n) ∧ (∀ d ∈ t.writeCells, ∃ (q : Page) (pr : Prepared), s.page? d.cell = some q ∧ s'.page? d.cell = some (q.withChange pr.change) ∧ pr.p = q ∧ pr.change.history = q.history ++ [pr.G'] ∧ d.preState = pr.o ∧ d.postState = pr.n ∧ judgePrepared s.entries s.entries pr (t.writeCells.map fun d => (d.cell, d.postState)) = .ok ()) ∧ s'.turn = s.turn + 1 := by
  obtain ⟨_, _, ws, prs, hws, hprs, ht, rfl⟩ := judgeProposal_ok h; obtain ⟨hwn, hwp⟩ := legWritesOf_ok hws; obtain ⟨hpw, hjudge⟩ := commitTurn_ok hprs; obtain ⟨htw, _⟩ := landedTurn_ok ht; have hnames : prs.map (·.p.name) = ws.map (·.1.name) := by rw [show (prs.map fun pr => pr.p.name) = (prs.map (·.p)).map (·.name) by simp, hpw]; simp
  have hfoot : t.writeFootprint = prs.map (·.p.name) := by simp [VaultTurn.writeFootprint, htw, landedDelta]
  have hnd : (prs.map (·.p.name)).Nodup := hfoot ▸ t.nodup_cells; have htip : tipOf prs = t.writeCells.map fun d => (d.cell, d.postState) := by simp [tipOf, htw, landedDelta]
  refine ⟨?_, ?_, ?_, rfl⟩
  (next => rw [hfoot, hnames, hwn]; rfl); (next => intro n hn; apply landAll_frame; intro pr hpr he; exact hn (hfoot ▸ he ▸ List.mem_map_of_mem hpr))
  · intro d hd; rw [htw] at hd; obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 hd; have hpin : pr.p ∈ ws.map (·.1) := hpw ▸ List.mem_map_of_mem hpr; obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hpin; have hq : s.page? pr.p.name = some pr.p := by rw [← hwe]; exact hwp w hw
    refine ⟨pr.p, pr, hq, landAll_lands s prs hnd hpr hq, rfl, rfl, rfl, rfl, ?_⟩
    rw [← htip]; exact hjudge pr hpr
theorem judgeProposal_sound {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant} {a : Assignment} {ad : Admitted} {t : VaultTurn} (h : judgeProposal H s f hops a = .ok (s', ad, t)) : DirectlyAdmits (ownerViewer f) t ∧ DirectlyAdmits ad.viewer t ∧ (∀ c ∈ t.writeFootprint, c ∈ f.scope) ∧ ∀ A ∈ f.assets, (t.writeCells.map fun d => (natAt d.postState A : Int)).sum = (t.writeCells.map fun d => (natAt d.preState A : Int)).sum := by
  obtain ⟨had, _, ws, prs, hws, hprs, ht, _⟩ := judgeProposal_ok h; obtain ⟨hfoot, _⟩ := judgeProposal_atomic h; obtain ⟨⟨hvw, hvr⟩, ⟨hrw, hrr⟩, _, _⟩ := admit_no_amplification had; obtain ⟨htw, htp⟩ := landedTurn_ok ht; obtain ⟨_, _, _, hpins⟩ := admit_ok had; have hcell : ∀ d ∈ t.writeCells, ∃ e ∈ ad.turn.writeCells, e.cell = d.cell := by intro d hd; have : d.cell ∈ ad.turn.writeFootprint := hfoot ▸ List.mem_map_of_mem hd; simpa [VaultTurn.writeFootprint] using this
  have hwrites := admit_writes had
  refine ⟨⟨fun d hd => ?_, fun q hq => hrr q (htp ▸ hq)⟩, ⟨fun d hd => ?_, fun q hq => hvr q (htp ▸ hq)⟩, fun c hc => ?_, fun A hA => ?_⟩
  (next => obtain ⟨e, he, hec⟩ := hcell d hd; rw [← hec]; exact hrw e he); (next => obtain ⟨e, he, hec⟩ := hcell d hd; rw [← hec]; exact hvw e he)
  · rw [hfoot] at hc; simp only [VaultTurn.writeFootprint, List.mem_map] at hc; obtain ⟨e, he, rfl⟩ := hc; exact (hwrites e he).2
  · have hhon : ∀ d ∈ t.writeCells, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A := by
      intro d hd; rw [htw] at hd; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hd; rw [deltaAsset_landed]; simp only [hA, ite_true, landedDelta]; omega
    rw [sum_map_add (post := fun d => (natAt d.postState A : Int)) (pre := fun d => (natAt d.preState A : Int)) (δ := fun d => deltaAsset d A) hhon]
    have hb := t.balanced A; unfold sumAssetDelta at hb; rw [foldl_add_int, Int.zero_add] at hb; rw [hb, Int.add_zero]
def judgeFill (H : Obend.Digest.HashBytes.Hash) (s : Store) (f : Form) (hops : List Grant) (a : Assignment) : Except String (Store × Admitted × VaultTurn) := if f.sets.isEmpty then judgeProposal H s f hops a else
  match admitFill (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty
      (.label f.name) with
  | .error r => .error (refusalText f r)
  | .ok fl =>
    match admitFootprint (stateStore s.entries) fl.turn.readPins with
    | .error (.footprintStale cell exp cur) => .error ("refused: stale: the form read " ++ cell ++ " as it was when captured (" ++ stateDiffText exp cur ++ "); capture it again")
    | .error _ => .error "refused: its pins do not hold here"
    | .ok _ =>
      match legWritesOf H s fl.ad.holder fl.ad.turn.writeCells,
          setWritesOf H s fl.ad.holder (setDeltas fl.ad.turn.turnId fl.sets) with
      | .error e, _ => .error e | _, .error e => .error e
      | .ok ws1, .ok ws2 =>
        let ws := ws1 ++ ws2
        match commitTurn s.entries s.entries ws .owner s.turn fl.ad.holder s.environment with
        | .error e => .error e
        | .ok prs =>
          match landedTurn f fl.turn.readPins fl.turn.occasion prs with
          | .error e => .error e | .ok t => .ok (s.landAll prs, fl.ad, t)
theorem judgeFill_no_sets (H : Obend.Digest.HashBytes.Hash) (s : Store) {f : Form} (hs : f.sets = []) (hops : List Grant) (a : Assignment) : judgeFill H s f hops a = judgeProposal H s f hops a := by simp [judgeFill, hs]
theorem judgeFill_ok {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant} {a : Assignment} {ad : Admitted} {t : VaultTurn} (hs : f.sets ≠ []) (h : judgeFill H s f hops a = .ok (s', ad, t)) : ∃ fl, admitFill (ownerViewer f) f hops (f.knownLive (stateStore s.entries)) a ByteArray.empty (.label f.name) = .ok fl ∧ fl.ad = ad ∧ ∃ ws1 ws2 prs, legWritesOf H s ad.holder ad.turn.writeCells = .ok ws1 ∧ setWritesOf H s ad.holder (setDeltas ad.turn.turnId fl.sets) = .ok ws2 ∧ commitTurn s.entries s.entries (ws1 ++ ws2) .owner s.turn ad.holder s.environment = .ok prs ∧ landedTurn f fl.turn.readPins fl.turn.occasion prs = .ok t ∧ s' = s.landAll prs := by
  have he : f.sets.isEmpty = false := by cases hx : f.sets with
    | nil => exact absurd hx hs | cons _ _ => rfl
  unfold judgeFill at h; rw [he] at h; simp only [Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  · rename_i fl hfl; split at h; (next => cases h); (next => cases h)
    · split at h; (next => cases h); (next => cases h)
      · rename_i ws1 ws2 hws1 hws2; split at h; (next => cases h); (next => rename_i prs hprs; split at h; (next => cases h); (next => rename_i t' ht; simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨fl, hfl, rfl, ws1, ws2, prs, hws1, hws2, hprs, ht, rfl⟩))
theorem judgeFill_sound {H : Obend.Digest.HashBytes.Hash} {s s' : Store} {f : Form} {hops : List Grant} {a : Assignment} {ad : Admitted} {t : VaultTurn} (h : judgeFill H s f hops a = .ok (s', ad, t)) : DirectlyAdmits (ownerViewer f) t ∧ DirectlyAdmits ad.viewer t ∧ (∀ c ∈ t.writeFootprint, c ∈ f.scope) ∧ ∀ A ∈ f.assets, (t.writeCells.map fun d => (natAt d.postState A : Int)).sum = (t.writeCells.map fun d => (natAt d.preState A : Int)).sum := by
  by_cases hs : f.sets = []
  · rw [judgeFill_no_sets H s hs] at h; exact judgeProposal_sound h
  obtain ⟨fl, hfl, rfl, ws1, ws2, prs, hws1, hws2, hprs, ht, _⟩ := judgeFill_ok hs h; obtain ⟨⟨hvw, hvr⟩, ⟨hrw, hrr⟩, _, _⟩ := admitFill_no_amplification hfl; obtain ⟨_, _, _, hflw, _⟩ := admitFill_ok hfl; have hwn : (ws1 ++ ws2).map (·.1.name) = fl.turn.writeCells.map (·.cell) := by rw [hflw, List.map_append, List.map_append, (legWritesOf_ok hws1).1, setWritesOf_ok hws2]
  obtain ⟨hpw, _⟩ := commitTurn_ok hprs; obtain ⟨htw, htp⟩ := landedTurn_ok ht; have hnames : prs.map (·.p.name) = (ws1 ++ ws2).map (·.1.name) := by rw [show (prs.map fun pr => pr.p.name) = (prs.map (·.p)).map (·.name) by simp, hpw]; simp [Function.comp_def]
  have hfoot : t.writeFootprint = fl.turn.writeFootprint := by
    simp only [VaultTurn.writeFootprint, htw, List.map_map]; have : (prs.map (CellDelta.cell ∘ landedDelta f.assets)) = prs.map (·.p.name) := by simp [Function.comp, landedDelta]
    rw [this, hnames, hwn]
  have hcell : ∀ d ∈ t.writeCells, ∃ e ∈ fl.turn.writeCells, e.cell = d.cell := by intro d hd; have : d.cell ∈ fl.turn.writeFootprint := hfoot ▸ List.mem_map_of_mem hd; simpa [VaultTurn.writeFootprint] using this
  have hwrites := admitFill_writes hfl
  refine ⟨⟨fun d hd => ?_, fun q hq => hrr q (htp ▸ hq)⟩, ⟨fun d hd => ?_, fun q hq => hvr q (htp ▸ hq)⟩, fun c hc => ?_, fun A hA => ?_⟩
  (next => obtain ⟨e, he, hec⟩ := hcell d hd; rw [← hec]; exact hrw e he); (next => obtain ⟨e, he, hec⟩ := hcell d hd; rw [← hec]; exact hvw e he)
  · rw [hfoot] at hc; simp only [VaultTurn.writeFootprint, List.mem_map] at hc; obtain ⟨e, he, rfl⟩ := hc; exact (hwrites e he).2
  · have hhon : ∀ d ∈ t.writeCells, (natAt d.postState A : Int) = natAt d.preState A + deltaAsset d A := by
      intro d hd; rw [htw] at hd; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hd; rw [deltaAsset_landed]; simp only [hA, ite_true, landedDelta]; omega
    rw [sum_map_add (post := fun d => (natAt d.postState A : Int)) (pre := fun d => (natAt d.preState A : Int)) (δ := fun d => deltaAsset d A) hhon]
    have hb := t.balanced A; unfold sumAssetDelta at hb; rw [foldl_add_int, Int.zero_add] at hb; rw [hb, Int.add_zero]
open Lean (Json toJson)
open Obend.Spec.DataWire (dataJson decodeData)
open Obend.Vault.Rehydration (WitnessReceipt mkReceipt)
def grantJson (g : Grant) : Json := Json.mkObj [("holder", g.holder), ("held", Json.arr (g.held.map fun x => toJson (authName x)).toArray), ("patterns", Json.arr (g.patterns.map toJson).toArray)]
def grantOf (j : Json) : Except String Grant := do
  let holder ← j.getObjValAs? String "holder"; let held ← j.getObjValAs? (Array String) "held"; let patterns ← j.getObjValAs? (Array String) "patterns"
  let auths ← held.toList.mapM fun x => match authOf x with
    | some a => .ok a | none => .error ("no cap named " ++ x)
  return ⟨holder, auths, patterns.toList⟩
def prefJson : PRef → Json
  | .page n => Json.mkObj [("page", n)] | .hole h => Json.mkObj [("hole", h)]
def prefOf (j : Json) : Except String PRef :=
  match j.getObjValAs? String "page" with
  | .ok n => .ok (.page n)
  | .error _ => do return .hole (← j.getObjValAs? String "hole")
def nexprJson : NExpr → Json
  | .lit n => Json.mkObj [("lit", toJson n)] | .hole h => Json.mkObj [("hole", h)] | .field p f => Json.mkObj [("field", f), ("of", prefJson p)] | .add x y => Json.mkObj [("add", Json.arr #[nexprJson x, nexprJson y])] | .sub x y => Json.mkObj [("sub", Json.arr #[nexprJson x, nexprJson y])]
def nexprOf : Nat → Json → Except String NExpr
  | 0, _ => .error "an expression nested too deep"
  | fuel + 1, j =>
    match j.getObjValAs? Nat "lit", j.getObjValAs? String "hole", j.getObjValAs? String "field" with
    | .ok n, _, _ => .ok (.lit n) | _, .ok h, _ => .ok (.hole h)
    | _, _, .ok f => do return .field (← prefOf (← j.getObjVal? "of")) f
    | _, _, _ =>
      let two (key : String) : Except String (NExpr × NExpr) := do
        let xs ← j.getObjValAs? (Array Json) key
        match xs.toList with
        | [x, y] => return (← nexprOf fuel x, ← nexprOf fuel y) | _ => .error "a sum or difference has two sides"
      match two "add", two "sub" with
      | .ok (x, y), _ => .ok (.add x y) | _, .ok (x, y) => .ok (.sub x y) | _, _ => .error "not an expression"
def moveJson (m : Move) : Json := Json.mkObj [("asset", m.asset), ("from", prefJson m.src), ("to", prefJson m.dst), ("amount", nexprJson m.amount)]
def moveOf (j : Json) : Except String Move := do return ⟨← j.getObjValAs? String "asset", ← prefOf (← j.getObjVal? "from"), ← prefOf (← j.getObjVal? "to"), ← nexprOf 64 (← j.getObjVal? "amount")⟩
def cellJson (c : Cell) : Json := Json.mkObj [("page", c.name), ("required", Json.arr (c.required.map fun x => toJson (authName x)).toArray), ("state", dataJson c.state)]
def cellOf (j : Json) : Except String Cell := do
  let req ← j.getObjValAs? (Array String) "required"
  let auths ← req.toList.mapM fun x => match authOf x with
    | some a => .ok a | none => .error ("no cap named " ++ x)
  return ⟨← j.getObjValAs? String "page", auths, ← decodeData 16 (← j.getObjVal? "state")⟩
def holeTyName : HoleTy → String
  | .nat => "natural" | .page => "page" | .label => "label" | .text => "text"
def holeTyOf : String → HoleTy
  | "page" => .page | "label" => .label | "text" => .text | _ => .nat
def sexprJson : SExpr → Json
  | .lit v => Json.mkObj [("lit", Json.str v)] | .hole h => Json.mkObj [("hole", h)] | .field p f => Json.mkObj [("field", f), ("of", prefJson p)]
def sexprOf (j : Json) : Except String SExpr :=
  match j.getObjValAs? String "lit", j.getObjValAs? String "hole", j.getObjValAs? String "field" with
  | .ok v, _, _ => .ok (.lit v) | _, .ok h, _ => .ok (.hole h)
  | _, _, .ok f => do return .field (← prefOf (← j.getObjVal? "of")) f
  | _, _, _ => .error "not a string position"
def setJson (m : SetMove) : Json := Json.mkObj [("page", prefJson m.page), ("fields", Json.arr (m.fields.map fun x => Json.mkObj [("field", x.1), ("value", sexprJson x.2)]).toArray)]
def setOf (j : Json) : Except String SetMove := do
  let fs ← (← j.getObjValAs? (Array Json) "fields").toList.mapM fun x => do return ((← x.getObjValAs? String "field"), ← sexprOf (← x.getObjVal? "value"))
  return ⟨← prefOf (← j.getObjVal? "page"), fs⟩
def formJson (f : Form) : Json :=
  Json.mkObj [("name", f.name), ("grants", Json.arr (f.grants.map grantJson).toArray), ("cells", Json.arr (f.cells.map cellJson).toArray), ("refs", Json.arr (f.refs.map toJson).toArray), ("holes", Json.arr (f.holes.map fun (h, t) => Json.mkObj [("hole", h), ("type", holeTyName t)]).toArray), ("moves", Json.arr (f.moves.map moveJson).toArray)] |>.mergeObj
    (if f.sets.isEmpty then Json.mkObj [] else Json.mkObj [("sets", Json.arr (f.sets.map setJson).toArray)])
def formOf (j : Json) : Except String Form := do
  let grants ← (← j.getObjValAs? (Array Json) "grants").toList.mapM grantOf; let cells ← (← j.getObjValAs? (Array Json) "cells").toList.mapM cellOf; let refs ← j.getObjValAs? (Array String) "refs"; let holes ← (← j.getObjValAs? (Array Json) "holes").toList.mapM fun h => do let t ← h.getObjValAs? String "type"; return (← h.getObjValAs? String "hole", holeTyOf t)
  let moves ← (← j.getObjValAs? (Array Json) "moves").toList.mapM moveOf
  let sets ← match j.getObjValAs? (Array Json) "sets" with
    | .ok xs => xs.toList.mapM setOf | .error _ => pure []
  return { name := ← j.getObjValAs? String "name", grants := grants, cells := cells, refs := refs.toList, holes := holes, moves := moves, sets := sets }
def assignmentJson (a : Assignment) : Json :=
  Json.mkObj [("nats", Json.arr (a.nats.map fun (h, n) => Json.mkObj [("hole", h), ("value", toJson n)]).toArray), ("pages", Json.arr (a.pages.map fun (h, n) => Json.mkObj [("hole", h), ("page", n)]).toArray)] |>.mergeObj
    (if a.labels.isEmpty then Json.mkObj [] else Json.mkObj [("labels", Json.arr (a.labels.map fun (h, v) => Json.mkObj [("hole", h), ("value", Json.str v)]).toArray)])
def assignmentOf (j : Json) : Except String Assignment := do
  let nats ← (← j.getObjValAs? (Array Json) "nats").toList.mapM fun x => do return (← x.getObjValAs? String "hole", ← x.getObjValAs? Nat "value")
  let pages ← (← j.getObjValAs? (Array Json) "pages").toList.mapM fun x => do return (← x.getObjValAs? String "hole", ← x.getObjValAs? String "page")
  let labels ← match j.getObjValAs? (Array Json) "labels" with
    | .ok xs => xs.toList.mapM fun x => do return (← x.getObjValAs? String "hole", ← x.getObjValAs? String "value")
    | .error _ => pure []
  return ⟨nats, pages, labels⟩
def digestNat (H : Obend.Digest.HashBytes.Hash) (s : String) : Nat := ((H s.toUTF8.toList).take 8).foldl (fun acc b => acc * 256 + b.toNat) 0
def hex16 (n : Nat) : String :=
  let ds := (List.range 16).reverse.map fun i => (n / 16 ^ i) % 16
  String.ofList (ds.map fun d => if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d))
def formDigest (H : Obend.Digest.HashBytes.Hash) (f : Form) : String := hex16 (digestNat H (formJson f).compress)
def receiptJson (r : WitnessReceipt) : Json := Json.mkObj [("prev", toJson r.prevHash), ("old", toJson r.oldCommit), ("new", toJson r.newCommit), ("effects", toJson r.effectsHash)]
def receiptOf (j : Json) : Except String WitnessReceipt := do
  return mkReceipt (← j.getObjValAs? Nat "prev") (← j.getObjValAs? Nat "old") (← j.getObjValAs? Nat "new")
    (← j.getObjValAs? Nat "effects")
def receiptDigest (H : Obend.Digest.HashBytes.Hash) (r : WitnessReceipt) : Nat := digestNat H (receiptJson r).compress
def receiptFor (H : Obend.Digest.HashBytes.Hash) (prev : Option WitnessReceipt) (f : Form) (a : Assignment) (ad : Admitted) (t : VaultTurn) : WitnessReceipt :=
  let states (post : Bool) : String := (Json.arr (t.writeCells.map fun d => Json.mkObj [("page", d.cell), ("state", dataJson (if post then d.postState else d.preState))]).toArray).compress
  mkReceipt ((prev.map (receiptDigest H)).getD Obend.Vault.Rehydration.genesisSentinel)
    (digestNat H (states false)) (digestNat H (states true))
    (digestNat H (Json.mkObj [("form", formDigest H f), ("fill", assignmentJson a), ("by", ad.holder)]).compress)
def PRef.show : PRef → String
  | .page n => n | .hole h => h
def NExpr.show : NExpr → String
  | .lit n => toString n | .hole h => h | .field p f => p.show ++ "." ++ f | .add x y => x.show ++ " + " ++ y.show | .sub x (.add a b) => x.show ++ " - (" ++ a.show ++ " + " ++ b.show ++ ")" | .sub x (.sub a b) => x.show ++ " - (" ++ (NExpr.sub a b).show ++ ")" | .sub x y => x.show ++ " - " ++ y.show
def SExpr.show : SExpr → String
  | .lit v => "\"" ++ v ++ "\"" | .hole h => h | .field p f => p.show ++ "." ++ f
def SetMove.lines (m : SetMove) : List String := m.fields.map fun x => m.page.show ++ "." ++ x.1 ++ " := " ++ x.2.show
def RMove.lines (r : RMove) : List String := [r.src.show ++ "." ++ r.asset ++ " := " ++ r.debit.show, r.dst.show ++ "." ++ r.asset ++ " := " ++ r.credit.show]
def Form.describe (f : Form) : List String :=
  let holder := ((f.grants.getLast?).map (·.holder)).getD "owner"; let g := f.grants.getLast?
  [f.name ++ ": a form for " ++ holder ++ (match g with
      | some g => " (" ++ showAuths g.held ++ " on " ++ ", ".intercalate g.patterns ++ ")" | none => "")] ++
  (f.cells.map fun c => "  " ++ c.name ++ ": " ++ (if f.moves.isEmpty then "shown" else ", ".intercalate (((f.moves.map (·.asset)).eraseDups).map fun a => a ++ " " ++ toString (natAt c.state a)))) ++
  (f.refs.map fun r => "  " ++ r ++ ": a reference (read where the form is judged)") ++
  (f.holes.map fun (h, t) => "  hole " ++ h ++ ": a " ++ holeTyName t) ++
  ((f.residual f.known).flatMap fun r => r.lines.map ("  " ++ ·)) ++
  ((f.setResidual f.known).flatMap fun m => m.lines.map ("  " ++ ·))
def captureFrom (s : Store) (situation name : String) (g : Grant) (src dst : String) (amount : Nat) (field : String) (refs : List String) : Except String (Form × Nat) := do
  let some p := s.page? situation | throw ("no page named " ++ situation)
  let some G := p.current | throw (situation ++ " has no version yet")
  let names := ([situation] ++ citedNames s.entries G ++ [src, dst]).eraseDups; let live := stateStore s.entries; let cands : List Cell := names.filterMap fun n => (live n).map fun d => { name := n, state := d }
  let scope := cands.map (·.name) ++ refs; let root := ownerGrant.viewer scope
  if (Membrane.reshare root (g.viewer scope)).isNone then throw (refusalText { name := name, grants := [], cells := [], moves := [] } (.amplifies "owner" g.holder root.held g.held))
  let v := g.viewer scope; let cells := capture v cands
  for n in [src, dst] do
    unless cells.any (·.name == n) do
      throw (n ++ " is not shown to " ++ g.holder ++ "'s grant (" ++ showAuths g.held ++ " on " ++ ", ".intercalate g.patterns ++ ")")
  for r in refs do
    unless g.permits r do throw (r ++ " is not permitted to " ++ g.holder ++ "'s grant")
  let mv : Move := { asset := field, src := .page src, dst := .page dst, amount := .lit amount }; let f : Form := { name := name, grants := [g], cells := cells, refs := refs, moves := [mv] }; return (f, cands.length - cells.length)
def Form.preview (f : Form) (a : Assignment) : List String := (f.fill a).flatMap (fun r => (r.peval f.known).lines) ++ (f.fillSets a).flatMap (·.lines)
def briefFrom (s : Store) (page name : String) (g : Grant) (lits : List (String × String)) (holes : List (String × HoleTy)) : Except String (Form × Nat) := do
  let some p := s.page? page | throw ("no page named " ++ page)
  let some G := p.current | throw (page ++ " has no version yet")
  let names := ([page] ++ citedNames s.entries G).eraseDups; let live := stateStore s.entries; let cands : List Cell := names.filterMap fun n => (live n).map fun d => { name := n, state := d }
  let scope := cands.map (·.name); let root := ownerGrant.viewer scope
  if (Membrane.reshare root (g.viewer scope)).isNone then throw (refusalText { name := name, grants := [], cells := [], moves := [] } (.amplifies "owner" g.holder root.held g.held))
  let cells := capture (g.viewer scope) cands
  unless cells.any (·.name == page) do
    throw (page ++ " is not shown to " ++ g.holder ++ "'s grant (" ++ showAuths g.held ++ " on " ++ ", ".intercalate g.patterns ++ ")")
  for (f, v) in lits do
    unless lineSafe v do throw ("the value for " ++ f ++ " cannot be a frontmatter line")
  let fields := lits.map (fun (f, v) => (f, SExpr.lit v)) ++ holes.map fun (h, _) => (h, SExpr.hole h)
  let f : Form := { name := name, grants := [g], cells := cells, holes := holes, moves := [], sets := [{ page := .page page, fields := fields }] }; return (f, cands.length - cells.length)
private def encodeBytes : List UInt8 → List UInt8
  | [] => [0] | b :: bs => 1 :: b :: encodeBytes bs
private theorem encodeBytes_prefix_inj {xs ys r₁ r₂ : List UInt8} (h : encodeBytes xs ++ r₁ = encodeBytes ys ++ r₂) : xs = ys ∧ r₁ = r₂ := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => simpa [encodeBytes] using h | cons _ _ => simp [encodeBytes] at h
  | cons b₁ bs₁ ih =>
    cases ys with
    | nil => simp [encodeBytes] at h
    | cons b₂ bs₂ =>
      simp only [encodeBytes, List.cons_append, List.cons.injEq] at h
      obtain ⟨_, rfl, hrest⟩ := h; obtain ⟨hbs, hr⟩ := ih hrest; exact ⟨hbs ▸ rfl, hr⟩
private theorem string_eq_of_utf8_list {a b : String} (h : a.toByteArray.data.toList = b.toByteArray.data.toList) : a = b := by
  cases a; cases b; cases ByteArray.ext (Array.ext' h); rfl
def fieldCommitDomain : List UInt8 := "Obend.Vault.Form.FieldCommit.v1".toByteArray.data.toList
def fieldCommitHash : Obend.Digest.HashBytes.Hash := Obend.Digest.Cshake256.cshake256Bytes fieldCommitDomain
def encodeFieldCommitPreimage (page field : String) (val : UInt64) (salt : BitVec 256) : List UInt8 :=
  encodeBytes page.toByteArray.data.toList ++ (encodeBytes field.toByteArray.data.toList ++ (Obend.Digest.HashBytes.be 8 val.toNat ++ Obend.Digest.HashBytes.be 32 salt.toNat))
theorem encodeFieldCommitPreimage_injective {p₁ p₂ f₁ f₂ : String} {v₁ v₂ : UInt64} {s₁ s₂ : BitVec 256} (h : encodeFieldCommitPreimage p₁ f₁ v₁ s₁ = encodeFieldCommitPreimage p₂ f₂ v₂ s₂) : p₁ = p₂ ∧ f₁ = f₂ ∧ v₁ = v₂ ∧ s₁ = s₂ := by
  unfold encodeFieldCommitPreimage at h; obtain ⟨hp, h1⟩ := encodeBytes_prefix_inj h; obtain ⟨hf, h2⟩ := encodeBytes_prefix_inj h1
  obtain ⟨hv, hs⟩ := List.append_inj h2 (by simp [Obend.Digest.HashBytes.length_be]); have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have h32 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  exact ⟨string_eq_of_utf8_list hp, string_eq_of_utf8_list hf, UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Obend.Digest.HashBytes.be_injective (h8 ▸ v₁.toBitVec.isLt) (h8 ▸ v₂.toBitVec.isLt) hv)), BitVec.eq_of_toNat_eq (Obend.Digest.HashBytes.be_injective (h32 ▸ s₁.isLt) (h32 ▸ s₂.isLt) hs)⟩
def commitField256 (page field : String) (val : UInt64) (salt : BitVec 256) : BitVec 256 :=
  BitVec.ofNat 256 (Obend.Digest.HashBytes.ofBE (fieldCommitHash (encodeFieldCommitPreimage page field val salt)))
private theorem commitField256_toNat (p f : String) (v : UInt64) (s : BitVec 256) : (commitField256 p f v s).toNat = Obend.Digest.HashBytes.ofBE (fieldCommitHash (encodeFieldCommitPreimage p f v s)) := by
  unfold commitField256; rw [BitVec.toNat_ofNat]; have hlen : (fieldCommitHash (encodeFieldCommitPreimage p f v s)).length = 32 := by simp [fieldCommitHash]
  have hlt : Obend.Digest.HashBytes.ofBE (fieldCommitHash (encodeFieldCommitPreimage p f v s)) < 256 ^ 32 := by simpa [hlen] using Obend.Digest.HashBytes.ofBE_lt (fieldCommitHash (encodeFieldCommitPreimage p f v s))
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  exact Nat.mod_eq_of_lt (hpow ▸ hlt)
structure FieldCommitCollisionWitness (p₁ f₁ : String) (v₁ : UInt64) (s₁ : BitVec 256) (p₂ f₂ : String) (v₂ : UInt64) (s₂ : BitVec 256) where
  pre₁ : List UInt8
  pre₂ : List UInt8
  hPre₁ : pre₁ = encodeFieldCommitPreimage p₁ f₁ v₁ s₁
  hPre₂ : pre₂ = encodeFieldCommitPreimage p₂ f₂ v₂ s₂
  hNe : pre₁ ≠ pre₂
  hColl : Obend.Digest.HashBytes.ofBE (fieldCommitHash pre₁) = Obend.Digest.HashBytes.ofBE (fieldCommitHash pre₂)
def extractCommitField256Collision (p₁ f₁ : String) (v₁ : UInt64) (s₁ : BitVec 256) (p₂ f₂ : String) (v₂ : UInt64) (s₂ : BitVec 256) (hEq : commitField256 p₁ f₁ v₁ s₁ = commitField256 p₂ f₂ v₂ s₂) : PSum (p₁ = p₂ ∧ f₁ = f₂ ∧ v₁ = v₂ ∧ s₁ = s₂) (FieldCommitCollisionWitness p₁ f₁ v₁ s₁ p₂ f₂ v₂ s₂) :=
  if hSame : p₁ = p₂ ∧ f₁ = f₂ ∧ v₁ = v₂ ∧ s₁ = s₂ then .inl hSame
  else .inr { pre₁ := encodeFieldCommitPreimage p₁ f₁ v₁ s₁, pre₂ := encodeFieldCommitPreimage p₂ f₂ v₂ s₂, hPre₁ := rfl, hPre₂ := rfl, hNe := fun hp => hSame (encodeFieldCommitPreimage_injective hp), hColl := by have hn := congrArg BitVec.toNat hEq; rwa [commitField256_toNat, commitField256_toNat] at hn }
theorem commitField256_collisionAmong {p₁ f₁ : String} {v₁ : UInt64} {s₁ : BitVec 256} {p₂ f₂ : String} {v₂ : UInt64} {s₂ : BitVec 256} (w : FieldCommitCollisionWitness p₁ f₁ v₁ s₁ p₂ f₂ v₂ s₂) : Obend.Digest.HashBytes.CollisionAmong fieldCommitHash (fun x => x = encodeFieldCommitPreimage p₁ f₁ v₁ s₁ ∨ x = encodeFieldCommitPreimage p₂ f₂ v₂ s₂) := ⟨w.pre₁, w.pre₂, .inl w.hPre₁, .inr w.hPre₂, w.hNe, w.hColl⟩
inductive RedactedNExpr where
  | publicLit (n : Nat) | hole (name : String) | remoteField (p : PRef) (f : String) | committedSecret (page field : String) (digest : BitVec 256) | add (a b : RedactedNExpr) | sub (a b : RedactedNExpr)
deriving DecidableEq, Repr
inductive RedactRefusal where
  | constantUnderflow (lhs rhs : Nat) | missingSecretCommitment (page field : String)
deriving DecidableEq, Repr
@[expose] def pevalRedacted (pubKnown : Known) (isSecret : String → Bool) (secretCommits : String → String → Option (BitVec 256)) : NExpr → Except RedactRefusal RedactedNExpr
  | .lit n => .ok (.publicLit n) | .hole h => .ok (.hole h) | .field (.hole h) f => .ok (.remoteField (.hole h) f)
  | .field (.page n) f =>
    if isSecret n then match secretCommits n f with | some dg => .ok (.committedSecret n f dg) | none => .error (.missingSecretCommitment n f)
    else match pubKnown n with | some d => .ok (.publicLit (natAt d f)) | none => .ok (.remoteField (.page n) f)
  | .add x y => do let rx ← pevalRedacted pubKnown isSecret secretCommits x; let ry ← pevalRedacted pubKnown isSecret secretCommits y; match rx, ry with | .publicLit u, .publicLit v => .ok (.publicLit (u + v)) | _, _ => .ok (.add rx ry)
  | .sub x y => do let rx ← pevalRedacted pubKnown isSecret secretCommits x; let ry ← pevalRedacted pubKnown isSecret secretCommits y; match rx, ry with | .publicLit u, .publicLit v => if v ≤ u then .ok (.publicLit (u - v)) else .error (.constantUnderflow u v) | _, _ => .ok (.sub rx ry)
@[expose] def RedactedNExpr.eval (a : Assignment) (fullKnown : Known) (isSecret : String → Bool) (openings : String → String → Option (UInt64 × BitVec 256)) : RedactedNExpr → Option Nat
  | .publicLit n => some n | .hole h => a.nats.lookup h
  | .committedSecret page field dg => match openings page field with | some (v, s) => if commitField256 page field v s == dg then some v.toNat else none | none => none
  | .remoteField p f => match p.subst a with | .page n => if isSecret n then none else (fullKnown n).map (natAt · f) | .hole _ => none
  | .add x y => do let u ← x.eval a fullKnown isSecret openings; let v ← y.eval a fullKnown isSecret openings; pure (u + v)
  | .sub x y => do let u ← x.eval a fullKnown isSecret openings; let v ← y.eval a fullKnown isSecret openings; if v ≤ u then pure (u - v) else none
theorem pevalRedacted_zero_secret_leak (pub₁ pub₂ : Known) (isSecret : String → Bool) (sc : String → String → Option (BitVec 256)) (hPubAgree : ∀ p, isSecret p = false → pub₁ p = pub₂ p) : (∀ e : NExpr, pevalRedacted pub₁ isSecret sc e = pevalRedacted pub₂ isSecret sc e) ∧ (∀ u v : Nat, ¬ v ≤ u → pevalRedacted pub₁ isSecret sc (.sub (.lit u) (.lit v)) = .error (.constantUnderflow u v)) := by
  refine ⟨?_, fun u v huv => by simp [pevalRedacted, bind, Except.bind, huv]⟩
  intro e; induction e with
  | lit _ | hole _ => rfl
  | field p f => cases p with | hole _ => rfl | page n => simp only [pevalRedacted]; cases hs : isSecret n; (next => simp [hPubAgree n hs]); (next => rfl)
  | add x y ihx ihy => simp only [pevalRedacted, ihx, ihy] | sub x y ihx ihy => simp only [pevalRedacted, ihx, ihy]
theorem pevalRedacted_eval_sound {pubKnown fullKnown : Known} {isSecret : String → Bool} {sc : String → String → Option (BitVec 256)} {openings : String → String → Option (UInt64 × BitVec 256)} (a : Assignment) (hPub : ∀ p d, isSecret p = false → pubKnown p = some d → fullKnown p = some d) (hHolePub : ∀ h n, a.pages.lookup h = some n → isSecret n = false) (hSec : ∀ p f dg, isSecret p = true → sc p f = some dg → ∃ v s, openings p f = some (v, s) ∧ commitField256 p f v s = dg ∧ (fullKnown p).map (natAt · f) = some v.toNat) : ∀ {e : NExpr} {re : RedactedNExpr}, pevalRedacted pubKnown isSecret sc e = .ok re → re.eval a fullKnown isSecret openings = (e.subst a).eval fullKnown
  | .lit _, _, h => by simp only [pevalRedacted, Except.ok.injEq] at h; subst h; rfl
  | .hole h, _, hr => by simp only [pevalRedacted, Except.ok.injEq] at hr; subst hr; simp only [RedactedNExpr.eval, NExpr.subst]; cases a.nats.lookup h <;> rfl
  | .field (.hole h) f, _, hr => by
    simp only [pevalRedacted, Except.ok.injEq] at hr; subst hr; simp only [RedactedNExpr.eval, NExpr.subst, PRef.subst]
    cases hl : a.pages.lookup h with | none => rfl | some n => simp [hHolePub h n hl, NExpr.eval]
  | .field (.page n) f, _, hr => by
    simp only [pevalRedacted] at hr; cases hs : isSecret n <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hr
    · cases hp : pubKnown n <;> simp only [hp, Except.ok.injEq] at hr <;> subst hr
      (next => simp [RedactedNExpr.eval, PRef.subst, NExpr.subst, NExpr.eval, hs]); (next d => simp [RedactedNExpr.eval, PRef.subst, NExpr.subst, NExpr.eval, hPub n d hs hp])
    · cases hc : sc n f <;> simp only [hc] at hr
      (next => cases hr); (next dg => simp only [Except.ok.injEq] at hr; subst hr; obtain ⟨v, s, ho, hcd, hfk⟩ := hSec n f dg hs hc; simp [RedactedNExpr.eval, NExpr.subst, PRef.subst, NExpr.eval, ho, hcd, hfk])
  | .add x y, re, hr => by
    simp only [pevalRedacted, bind, Except.bind] at hr
    cases hx : pevalRedacted pubKnown isSecret sc x <;> simp only [hx] at hr; · cases hr
    rename_i rx; cases hy : pevalRedacted pubKnown isSecret sc y <;> simp only [hy] at hr; · cases hr
    rename_i ry; have ihx := pevalRedacted_eval_sound a hPub hHolePub hSec hx; have ihy := pevalRedacted_eval_sound a hPub hHolePub hSec hy
    cases rx <;> cases ry <;> simp only [Except.ok.injEq] at hr <;> subst hr <;> simp [RedactedNExpr.eval, NExpr.subst, NExpr.eval, ← ihx, ← ihy]
  | .sub x y, re, hr => by
    simp only [pevalRedacted, bind, Except.bind] at hr
    cases hx : pevalRedacted pubKnown isSecret sc x <;> simp only [hx] at hr; · cases hr
    rename_i rx; cases hy : pevalRedacted pubKnown isSecret sc y <;> simp only [hy] at hr; · cases hr
    rename_i ry; have ihx := pevalRedacted_eval_sound a hPub hHolePub hSec hx; have ihy := pevalRedacted_eval_sound a hPub hHolePub hSec hy
    cases rx <;> cases ry <;> try (simp only [Except.ok.injEq] at hr; subst hr; simp [RedactedNExpr.eval, NExpr.subst, NExpr.eval, ← ihx, ← ihy]; done)
    rename_i u v; by_cases huv : v ≤ u <;> simp only [huv, ite_true, ite_false] at hr
    (next => simp only [Except.ok.injEq] at hr; subst hr; simp [RedactedNExpr.eval, NExpr.subst, NExpr.eval, ← ihx, ← ihy, huv]); (next => cases hr)
theorem pevalRedacted_complete (pub : Known) (isSec : String → Bool) (sc : String → String → Option (BitVec 256)) (n : Nat) : pevalRedacted pub isSec sc (.lit n) = .ok (.publicLit n) := by rfl
def embedNExprChecked (natHoleSlot : String → Nat) (pageFieldHoleSlot : String → String → Nat) : NExpr → Obend.Core.Term.Term
  | .lit n => .nat n | .hole h => .hole (natHoleSlot h) [] | .field (.hole h) f => .hole (pageFieldHoleSlot h f) []
  | .field (.page p) f => .label (toString p.length ++ ":" ++ p ++ ":" ++ f)
  | .add x y => .binary .add (embedNExprChecked natHoleSlot pageFieldHoleSlot x) (embedNExprChecked natHoleSlot pageFieldHoleSlot y)
  | .sub x y => let tx := embedNExprChecked natHoleSlot pageFieldHoleSlot x; let ty := embedNExprChecked natHoleSlot pageFieldHoleSlot y; .ifBool (.binary .lessEqual ty tx) (.binary .subtract tx ty) (.boolean false)
theorem embedNExprChecked_hole_is_core_hole (nh : String → Nat) (pfh : String → String → Nat) (h f : String) : embedNExprChecked nh pfh (.hole h) = .hole (nh h) [] ∧ embedNExprChecked nh pfh (.field (.hole h) f) = .hole (pfh h f) [] := by exact ⟨rfl, rfl⟩
theorem embedNExprChecked_lit_sub_exact (nh : String → Nat) (pfh : String → String → Nat) (u v : Nat) : (v ≤ u → Obend.Core.Term.Evaluates (embedNExprChecked nh pfh (.sub (.lit u) (.lit v))) (.nat (u - v))) ∧ (¬ v ≤ u → Obend.Core.Term.Evaluates (embedNExprChecked nh pfh (.sub (.lit u) (.lit v))) (.boolean false) ∧ ∀ w, ¬ Obend.Core.Term.Evaluates (embedNExprChecked nh pfh (.sub (.lit u) (.lit v))) (.nat w)) := by
  refine ⟨fun hle => ?_, fun hgt => ⟨?_, fun w hw => ?_⟩⟩
  · refine ⟨.next (.ifCondition _ _ (.primitive .lessEqual _ _ _ (.natural v) (.natural u) (by simp [embedNExprChecked, Obend.Core.Term.primitiveResult, hle]))) (.next (.ifTrue _ _) (.next (.primitive .subtract _ _ _ (.natural u) (.natural v) rfl) (.refl _))), .natural _⟩
  · exact ⟨.next (.ifCondition _ _ (.primitive .lessEqual _ _ _ (.natural v) (.natural u) (by simp [embedNExprChecked, Obend.Core.Term.primitiveResult, hgt]))) (.next (.ifFalse _ _) (.refl _)), .boolean false⟩
  · have hs1 : Obend.Core.Term.Step (embedNExprChecked nh pfh (.sub (.lit u) (.lit v))) (.ifBool (.boolean false) (.binary .subtract (.nat u) (.nat v)) (.boolean false)) :=
      .ifCondition _ _ (.primitive .lessEqual _ _ _ (.natural v) (.natural u) (by simp [embedNExprChecked, Obend.Core.Term.primitiveResult, hgt]))
    rcases hw.1 with _ | ⟨st1, rest1⟩; have hm1 := Obend.Equiv.step_deterministic hs1 st1; subst hm1
    rcases rest1 with _ | ⟨st2, rest2⟩; have hm2 := Obend.Equiv.step_deterministic (.ifFalse _ _) st2; subst hm2
    cases Obend.Equiv.value_steps_eq (.boolean false) rest2
end Obend.Vault.Form
end
