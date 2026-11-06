module
/-
# Obend.Hardware.Hvm.Net — expressions, their nets, and the net theorem

`FExp` is the expression language the lowering targets: U24 literals, variables, HVM2's operators,
a strict `let`, a switch whose branches are inline (`ifz`, both branches built, the untaken one
erased) and a switch whose branches are λ-lifted definitions (`ifzL`, the untaken branch a reference
that is voided before it is ever expanded, the shape recursion needs under eager evaluation), and a
call of a named definition (`call`). `comp` compiles an expression to redexes; `defNet` compiles a
definition (parameters, outputs) to an HVM2 net.

**The net theorem** `comp_reduces`: under `Good` (every lifted branch and every called definition
is in the book as `defNet` compiles it), an expression whose value at fuel `f` is `v`
(`evalF D f ρ e = some v`; `v = none` is an erased value) reduces, under the model's `Step`, to the
single redex `nul v ~ K`. `callDef` is the same fact for a reference meeting its arguments: the
definition's outputs, as one tuple, meet the caller's continuation.
-/
public import Obend.Hardware.Hvm.Model
@[expose] public section
namespace Obend.Hardware.Hvm
set_option autoImplicit false

/-! ## 1. Expressions -/

inductive FExp where
  | lit (v : Nat)
  | var (i : Nat)
  | op (o : HOp) (a b : FExp)
  | let_ (a b : FExp)
  | ifz (v z s : FExp)
  /-- A switch whose branches are the definitions `nz` (`z`, the environment's first `d` indices
  as parameters) and `ns` (`s`, the predecessor and the same `d`). -/
  | ifzL (d : Nat) (nz ns : String) (v z s : FExp)
  /-- A call of the definition `g`, its parameters bound to the variables `idxs`. -/
  | call (g : String) (idxs : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A definition: its name, the index each parameter binds (in the order the argument tree carries
them), and its body. -/
structure FDef where
  name : String
  params : List Nat
  body : FExp
  deriving DecidableEq, Repr

def cons {α : Type} (x : α) (ρ : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero {α : Type} (x : α) (ρ : Nat → α) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ {α : Type} (x : α) (ρ : Nat → α) (i : Nat) : cons x ρ (i + 1) = ρ i := rfl

/-- `[d-1, …, 0]`. -/
def revRange : Nat → List Nat
  | 0 => []
  | d + 1 => d :: revRange d

/-- The environment's first `d` indices. -/
def restrict (d : Nat) (ρ : Nat → Option Nat) : Nat → Option Nat := fun i => if i < d then ρ i else none

/-- The environment a definition's body sees: parameter `ps[j]` bound to `vs[j]`. -/
def bindEnv : List Nat → List (Option Nat) → Nat → Option Nat
  | p :: ps, v :: vs, i => if i = p then v else bindEnv ps vs i
  | _, _, _ => none

def predOf : Option Nat → Option Nat
  | some (k + 1) => some k
  | _ => none

def selectZ : Option Nat → Option Nat → Option Nat → Option Nat
  | some 0, vz, _ => vz
  | some (_ + 1), _, vs => vs
  | none, _, _ => none

def opW (o : HOp) : Option Nat → Option Nat → Option Nat
  | none, _ => none
  | some _, none => none
  | some x, some y => some (o.u24 x y)

/-- **The net's value** at fuel `f` (each call spends one): `some v` with `v` HVM2's wrapping U24
value, or `none` for an erased one (the eraser reaching the continuation); `none` outside: the fuel
ran out, or a call does not match its definition. An inline switch builds both branches (the
untaken one is erased, its predecessor erased); a lifted switch expands only the taken one. -/
def evalF (D : List FDef) : Nat → (Nat → Option Nat) → FExp → Option (Option Nat)
  | _, _, .lit v => some (some v)
  | _, ρ, .var i => some (ρ i)
  | f, ρ, .op o a b => match evalF D f ρ a, evalF D f ρ b with
    | some x, some y => some (opW o x y)
    | _, _ => none
  | f, ρ, .let_ a b => match evalF D f ρ a with
    | some x => evalF D f (cons x ρ) b
    | none => none
  | f, ρ, .ifz v z s => match evalF D f ρ v with
    | some x => match evalF D f ρ z, evalF D f (cons (predOf x) ρ) s with
      | some vz, some vs => some (selectZ x vz vs)
      | _, _ => none
    | none => none
  | f, ρ, .ifzL d _ _ v z s =>
    if d = 0 then none else
    match evalF D f ρ v with
    | some (some 0) => evalF D f (restrict d ρ) z
    | some (some (k + 1)) => evalF D f (cons (some k) (restrict d ρ)) s
    | some none => some none
    | none => none
  | 0, _, .call _ _ => none
  | f + 1, ρ, .call g idxs => match D.find? (·.name == g) with
    | some d => if idxs.length = d.params.length ∧ idxs ≠ [] then
        evalF D f (bindEnv d.params (idxs.map ρ)) d.body else none
    | none => none
termination_by f _ e => (f, sizeOf e)

/-! ## 2. Nets -/

def nul : Option Nat → HTree
  | some v => .num (.u24 v)
  | none => .era

def dupTree : List Nat → HTree
  | [] => .era
  | [o] => .var o
  | o :: o' :: os => .dup (.var o) (dupTree (o' :: os))

structure Out where
  bag : List Redex
  occ : List (Nat × Nat)
  next : Nat

def occ0 (occ : List (Nat × Nat)) : List Nat := (occ.filter (fun p => p.1 == 0)).map (·.2)

def shiftOcc (occ : List (Nat × Nat)) : List (Nat × Nat) :=
  occ.filterMap fun p => if p.1 = 0 then none else some (p.1 - 1, p.2)

/-- The argument tree `(v_n (v_{n+1} … K))`, one fresh variable per argument. -/
def argChain : List Nat → Nat → HTree → HTree
  | [], _, K => K
  | _ :: is, n, K => .con (.var n) (argChain is (n + 1) K)

/-- The occurrences an argument tree makes: index `is[j]` at variable `n + j`. -/
def argOcc : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | i :: is, n => (i, n) :: argOcc is (n + 1)

/-- The argument tree of given trees. -/
def argTree : List HTree → HTree → HTree
  | [], K => K
  | t :: ts, K => .con t (argTree ts K)

/-- **The compilation of an expression**, its value delivered to the main port of `K`, on fresh
variables from `n`. -/
def comp : FExp → HTree → Nat → Out
  | .lit v, K, n => ⟨[(.num (.u24 v), K)], [], n⟩
  | .var i, K, n => ⟨[(.var n, K)], [(i, n)], n + 1⟩
  | .op o a b, K, n =>
    let rb := comp b (.var n) (n + 1)
    let ra := comp a (.opr (.num (.sym o)) (.opr (.var n) K)) rb.next
    ⟨rb.bag ++ ra.bag, rb.occ ++ ra.occ, ra.next⟩
  | .let_ a b, K, n =>
    let rb := comp b K n
    let ra := comp a (dupTree (occ0 rb.occ)) rb.next
    ⟨ra.bag ++ rb.bag, ra.occ ++ shiftOcc rb.occ, ra.next⟩
  | .ifz v z s, K, n =>
    let rz := comp z (.var n) (n + 2)
    let rs := comp s (.var (n + 1)) rz.next
    let rv := comp v (.swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K) rs.next
    ⟨rv.bag ++ rz.bag ++ rs.bag, rv.occ ++ rz.occ ++ shiftOcc rs.occ, rv.next⟩
  | .ifzL d nz ns v _ _, K, n =>
    let rv := comp v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    ⟨rv.bag, rv.occ ++ argOcc (revRange d) n, rv.next⟩
  | .call g idxs, K, n => ⟨[(.ref g, argChain idxs n K)], argOcc idxs n, n + idxs.length⟩

/-- The occurrences of index `i`. -/
def occAt (i : Nat) (occ : List (Nat × Nat)) : List Nat := (occ.filter (fun p => p.1 == i)).map (·.2)

/-- The parameter tree: one duplicator tree per parameter, then the outputs. -/
def paramTree (occ : List (Nat × Nat)) : List Nat → HTree → HTree
  | [], R => R
  | p :: ps, R => .con (dupTree (occAt p occ)) (paramTree occ ps R)

/-- A tuple: one tree as itself, more as a right-nested `CON` chain. -/
def tup : List HTree → HTree
  | [] => .era
  | [t] => t
  | t :: t' :: ts => .con t (tup (t' :: ts))

def outVars : Nat → Nat → List HTree
  | 0, _ => []
  | k + 1, j => .var j :: outVars k (j + 1)

/-- Several expressions, output `i` delivered to variable `j + i`, on fresh variables from `n`. -/
def compAll : List FExp → Nat → Nat → Out
  | [], _, n => ⟨[], [], n⟩
  | f :: fs, j, n =>
    let r := comp f (.var j) n
    let rs := compAll fs (j + 1) r.next
    ⟨r.bag ++ rs.bag, r.occ ++ rs.occ, rs.next⟩

/-- **A definition's net**: `@name = (P₁ (… (Pₖ (r₀ (… r_{m-1}))))) & …`, parameter `ps[j]` handed
to its occurrences by `Pⱼ`, output `i` delivered to `rᵢ` (variables `0 … m-1`). -/
def defNet (name : String) (ps : List Nat) (fs : List FExp) : HDef :=
  let r := compAll fs 0 fs.length
  ⟨name, paramTree r.occ ps (tup (outVars fs.length 0)), r.bag⟩

/-! ## 3. Substitution facts -/

/-- Every tree a substitution puts in has no variables. -/
def ClosedImg (S : Nat → Option HTree) : Prop := ∀ m T, S m = some T → T.vars = []

/-- The substitution handing `N` to every variable of `os`. -/
def many (os : List Nat) (N : HTree) : Nat → Option HTree := fun m => if m ∈ os then some N else none

/-- Two substitutions, the first one first. -/
def merge (S T : Nat → Option HTree) : Nat → Option HTree := fun m => (S m).or (T m)

@[simp] theorem bagVars_nil : bagVars [] = [] := rfl
@[simp] theorem bagVars_cons (r : Redex) (l : List Redex) :
    bagVars (r :: l) = r.1.vars ++ r.2.vars ++ bagVars l := by
  simp [bagVars, redexVars]
@[simp] theorem bagVars_append (l₁ l₂ : List Redex) : bagVars (l₁ ++ l₂) = bagVars l₁ ++ bagVars l₂ := by
  simp [bagVars]

@[simp] theorem nul_vars (x : Option Nat) : (nul x).vars = [] := by cases x <;> rfl

@[simp] theorem dupTree_vars : ∀ os : List Nat, (dupTree os).vars = os
  | [] => rfl
  | [_] => rfl
  | o :: o' :: os => by simp [dupTree, HTree.vars, dupTree_vars (o' :: os)]

theorem HTree.subst_id_of {S : Nat → Option HTree} :
    ∀ (t : HTree), (∀ v ∈ t.vars, S v = none) → t.subst S = t
  | .var n, h => by simp [HTree.subst, h n (by simp [HTree.vars])]
  | .era, _ => rfl
  | .ref _, _ => rfl
  | .num _, _ => rfl
  | .con a b, h | .dup a b, h | .opr a b, h | .swi a b, h => by
    simp only [HTree.vars, List.mem_append] at h
    simp only [HTree.subst, HTree.subst_id_of a (fun v hv => h v (.inl hv)),
      HTree.subst_id_of b (fun v hv => h v (.inr hv))]

theorem HTree.subst_closed {S : Nat → Option HTree} (t : HTree) (h : t.vars = []) : t.subst S = t :=
  t.subst_id_of (by simp [h])

@[simp] theorem nul_subst (S : Nat → Option HTree) (x : Option Nat) : (nul x).subst S = nul x :=
  HTree.subst_closed _ (nul_vars x)

theorem HTree.vars_subst {S : Nat → Option HTree} (hS : ClosedImg S) :
    ∀ (t : HTree) (v : Nat), v ∈ (t.subst S).vars → v ∈ t.vars
  | .var n, v, h => by
    simp only [HTree.subst] at h
    cases hn : S n with
    | none => simpa [hn, HTree.vars] using h
    | some T => simp [hn, hS n T hn] at h
  | .era, _, h | .ref _, _, h | .num _, _, h => by simp [HTree.subst, HTree.vars] at h
  | .con a b, v, h | .dup a b, v, h | .opr a b, v, h | .swi a b, v, h => by
    simp only [HTree.subst, HTree.vars, List.mem_append] at h ⊢
    exact h.imp (HTree.vars_subst hS a v) (HTree.vars_subst hS b v)

theorem bagVars_map_subst {S : Nat → Option HTree} (hS : ClosedImg S) (l : List Redex) (v : Nat)
    (h : v ∈ bagVars (l.map (Redex.subst S))) : v ∈ bagVars l := by
  induction l with
  | nil => simp at h
  | cons r l ih =>
    simp only [List.map_cons, bagVars_cons, Redex.subst, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (HTree.vars_subst hS _ v h))
    · exact .inl (.inr (HTree.vars_subst hS _ v h))
    · exact .inr (ih h)

theorem bag_subst_id {S : Nat → Option HTree} (l : List Redex) (h : ∀ v ∈ bagVars l, S v = none) :
    l.map (Redex.subst S) = l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [bagVars_cons, List.mem_append] at h
    simp only [List.map_cons, Redex.subst, List.cons.injEq]
    refine ⟨?_, ih (fun v hv => h v (.inr hv))⟩
    rw [HTree.subst_id_of r.1 (fun v hv => h v (.inl (.inl hv))),
      HTree.subst_id_of r.2 (fun v hv => h v (.inl (.inr hv)))]

theorem HTree.subst_merge {S : Nat → Option HTree} (T : Nat → Option HTree) (hS : ClosedImg S) :
    ∀ (t : HTree), (t.subst S).subst T = t.subst (merge S T)
  | .var n => by
    simp only [HTree.subst, merge]
    cases hn : S n with
    | none => simp [HTree.subst]
    | some A => simp [HTree.subst_closed A (hS n A hn)]
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b | .dup a b | .opr a b | .swi a b => by
    simp only [HTree.subst, HTree.subst_merge T hS a, HTree.subst_merge T hS b]

theorem bag_subst_merge {S : Nat → Option HTree} (T : Nat → Option HTree) (hS : ClosedImg S)
    (l : List Redex) : (l.map (Redex.subst S)).map (Redex.subst T) = l.map (Redex.subst (merge S T)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simp [Redex.subst, HTree.subst_merge T hS]

theorem HTree.subst_comm_one {S : Nat → Option HTree} {x : Nat} {A : HTree} (hS : ClosedImg S)
    (hx : S x = none) (hA : A.subst S = A) :
    ∀ (t : HTree), (t.subst S).subst (one x A) = (t.subst (one x A)).subst S
  | .var n => by
    by_cases h : n = x
    · subst h; simp [HTree.subst, hx, one, hA]
    · cases hn : S n with
      | none => simp [HTree.subst, hn, one, h]
      | some B => simp [HTree.subst, hn, one, h, HTree.subst_closed B (hS n B hn)]
  | .era => rfl
  | .ref _ => rfl
  | .num _ => rfl
  | .con a b | .dup a b | .opr a b | .swi a b => by
    simp only [HTree.subst, HTree.subst_comm_one hS hx hA a, HTree.subst_comm_one hS hx hA b]

theorem bag_subst_comm_one {S : Nat → Option HTree} {x : Nat} {A : HTree} (hS : ClosedImg S)
    (hx : S x = none) (hA : A.subst S = A) (l : List Redex) :
    (l.map (Redex.subst S)).map (Redex.subst (one x A)) =
      (l.map (Redex.subst (one x A))).map (Redex.subst S) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _
  simp [Redex.subst, HTree.subst_comm_one hS hx hA]

theorem closedImg_merge {S T : Nat → Option HTree} (hS : ClosedImg S) (hT : ClosedImg T) :
    ClosedImg (merge S T) := by
  intro m U h
  simp only [merge] at h
  cases hm : S m with
  | none => rw [hm] at h; exact hT m U h
  | some B => rw [hm] at h; cases h; exact hS m _ hm

theorem closedImg_many {os : List Nat} {N : HTree} (hN : N.vars = []) : ClosedImg (many os N) := by
  intro m U h
  simp only [many] at h
  split at h
  · cases h; exact hN
  · cases h

theorem closedImg_one {x : Nat} {N : HTree} (hN : N.vars = []) : ClosedImg (one x N) := by
  intro m U h
  simp only [one] at h
  split at h
  · cases h; exact hN
  · cases h


/-! ## 4. Steps in context -/
theorem steps_eq {book : List HDef} {c c' : Cfg} (h : c = c') : Steps book c c' := h ▸ .refl c

theorem sRule {book : List HDef} {root : HTree} {l l' : List Redex} (pre post : List Redex) {a b : HTree}
    {ns : List Redex} (h : localRule a b = some ns) (hl : l = pre ++ (a, b) :: post)
    (hl' : l' = pre ++ (ns ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'; rw [← List.append_assoc]; exact .single (.rule h)

theorem sSwap {book : List HDef} {root : HTree} {l l' : List Redex} (pre post : List Redex) {a b : HTree}
    (hl : l = pre ++ (a, b) :: post) (hl' : l' = pre ++ (b, a) :: post) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'; exact .single .swap

theorem one_none {x v : Nat} {t : HTree} (h : v ≠ x) : one x t v = none := by simp [one, h]

theorem sLink {book : List HDef} {root : HTree} {l l' : List Redex} (pre mid post : List Redex) (x : Nat)
    (t : HTree) (hr : x ∉ root.vars) (hp : x ∉ bagVars pre) (hq : x ∉ bagVars post)
    (hl : l = pre ++ (.var x, t) :: (mid ++ post))
    (hl' : l' = pre ++ (mid.map (Redex.subst (one x t)) ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ := by
  subst hl hl'
  have h1 := Step.link (book := book) (root := root) (pre := pre) (post := mid ++ post) (x := x) (t := t)
  have er : root.subst (one x t) = root :=
    HTree.subst_id_of _ (fun v hv => one_none (fun h => hr (h ▸ hv)))
  have ep : pre.map (Redex.subst (one x t)) = pre :=
    bag_subst_id _ (fun v hv => one_none (fun h => hp (h ▸ hv)))
  have eq : post.map (Redex.subst (one x t)) = post :=
    bag_subst_id _ (fun v hv => one_none (fun h => hq (h ▸ hv)))
  rw [er, List.map_append, List.map_append, ep, eq] at h1
  exact .single h1

theorem sLinkR {book : List HDef} {root : HTree} {l l' : List Redex} (pre mid post : List Redex) (x : Nat)
    (t : HTree) (hr : x ∉ root.vars) (hp : x ∉ bagVars pre) (hq : x ∉ bagVars post)
    (hl : l = pre ++ (t, .var x) :: (mid ++ post))
    (hl' : l' = pre ++ (mid.map (Redex.subst (one x t)) ++ post)) : Steps book ⟨root, l⟩ ⟨root, l'⟩ :=
  (sSwap pre (mid ++ post) hl rfl).trans (sLink pre mid post x t hr hp hq rfl hl')

/-- A nullary value meets the duplicator tree: every occurrence receives it. -/
def Nullary (N : HTree) : Prop := N = .era ∨ ∃ v, N = .num (.u24 v)

theorem nullary_nul (x : Option Nat) : Nullary (nul x) := by
  cases x
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

theorem Nullary.vars {N : HTree} (h : Nullary N) : N.vars = [] := by
  rcases h with rfl | ⟨v, rfl⟩ <;> rfl

theorem localRule_void {N M : HTree} (hN : Nullary N) (hM : Nullary M) : localRule N M = some [] := by
  rcases hN with rfl | ⟨_, rfl⟩ <;> rcases hM with rfl | ⟨_, rfl⟩ <;> rfl

theorem sSpread {book : List HDef} (N : HTree) (hN : Nullary N) : ∀ (os : List Nat) {root : HTree}
    {l l' : List Redex} (pre mid post : List Redex), os.Nodup →
    (∀ o ∈ os, o ∉ root.vars ∧ o ∉ bagVars pre ∧ o ∉ bagVars post) →
    l = pre ++ (N, dupTree os) :: (mid ++ post) →
    l' = pre ++ (mid.map (Redex.subst (many os N)) ++ post) →
    Steps book ⟨root, l⟩ ⟨root, l'⟩
  | [], root, l, l', pre, mid, post, _, _, hl, hl' => by
    refine sRule pre (mid ++ post) (localRule_void hN (.inl rfl)) hl ?_
    rw [hl', bag_subst_id mid (fun v _ => by simp [many])]
    simp
  | [o], root, l, l', pre, mid, post, _, ho, hl, hl' => by
    obtain ⟨h1, h2, h3⟩ := ho o (by simp)
    refine sLinkR pre mid post o N h1 h2 h3 hl ?_
    rw [hl']
    have : many [o] N = one o N := by funext m; simp [many, one]
    rw [this]
  | o :: o' :: os, root, l, l', pre, mid, post, hnd, ho, hl, hl' => by
    obtain ⟨h1, h2, h3⟩ := ho o (by simp)
    have hr : localRule N (.dup (.var o) (dupTree (o' :: os))) =
        some [(N, .var o), (N, dupTree (o' :: os))] := by
      rcases hN with rfl | ⟨_, rfl⟩ <;> rfl
    have hno : o ∉ o' :: os := (List.nodup_cons.1 hnd).1
    have hnd' : (o' :: os).Nodup := (List.nodup_cons.1 hnd).2
    refine (sRule pre (mid ++ post) hr hl rfl).trans ?_
    refine (sLinkR pre ((N, dupTree (o' :: os)) :: mid) post o N h1 h2 h3 (by simp) rfl).trans ?_
    have e1 : ((N, dupTree (o' :: os)) :: mid).map (Redex.subst (one o N)) =
        (N, dupTree (o' :: os)) :: mid.map (Redex.subst (one o N)) := by
      simp only [List.map_cons, Redex.subst, List.cons.injEq, Prod.mk.injEq, and_true]
      refine ⟨HTree.subst_closed _ hN.vars, HTree.subst_id_of _ ?_⟩
      intro v hv; rw [dupTree_vars] at hv
      exact one_none (fun h => hno (h ▸ hv))
    rw [e1]
    refine sSpread N hN (o' :: os) pre (mid.map (Redex.subst (one o N))) post hnd'
      (fun o'' h => ho o'' (List.mem_cons_of_mem _ h)) (by simp) ?_
    rw [hl', bag_subst_merge _ (closedImg_one hN.vars)]
    have : merge (one o N) (many (o' :: os) N) = many (o :: o' :: os) N := by
      funext m; by_cases hm : m = o
      · subst hm; simp [merge, one, many]
      · simp [merge, one, many, hm]
    rw [this]

theorem fresh4 {root K : HTree} {pre post : List Redex} {P : Nat → Prop}
    (h : ∀ v ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, P v) :
    (∀ v ∈ root.vars, P v) ∧ (∀ v ∈ bagVars pre, P v) ∧ (∀ v ∈ bagVars post, P v) ∧ (∀ v ∈ K.vars, P v) :=
  ⟨fun v hv => h v (by simp [hv]), fun v hv => h v (by simp [hv]), fun v hv => h v (by simp [hv]),
    fun v hv => h v (by simp [hv])⟩

theorem fresh4_mk {root K : HTree} {pre post : List Redex} {P : Nat → Prop}
    (hr : ∀ v ∈ root.vars, P v) (hp : ∀ v ∈ bagVars pre, P v) (hq : ∀ v ∈ bagVars post, P v)
    (hk : ∀ v ∈ K.vars, P v) : ∀ v ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, P v := by
  intro v hv
  simp only [List.mem_append] at hv
  rcases hv with ((h | h) | h) | h
  · exact hr v h
  · exact hp v h
  · exact hq v h
  · exact hk v h

theorem nodup_name {l : List (Nat × Nat)} (h : (l.map Prod.snd).Nodup) {x y : Nat × Nat} (hx : x ∈ l)
    (hy : y ∈ l) (he : x.2 = y.2) : x = y := by
  induction l with
  | nil => cases hx
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 hx with ex | lx <;> rcases List.mem_cons.1 hy with ey | ly
    · rw [ex, ey]
    · subst ex; exact absurd ⟨y, ly, he.symm⟩ h.1
    · subst ey; exact absurd ⟨x, lx, he⟩ h.1
    · exact ih h.2 lx ly


/-! ## 5. Facts about `comp` -/

theorem mem_occ0 {occ : List (Nat × Nat)} {o : Nat} : o ∈ occ0 occ ↔ (0, o) ∈ occ := by
  simp only [occ0, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨i, o'⟩, ⟨h, hi⟩, rfl⟩; simp only at hi; subst hi; exact h
  · intro h; exact ⟨(0, o), ⟨h, rfl⟩, rfl⟩

theorem mem_shiftOcc {occ : List (Nat × Nat)} {p : Nat × Nat} : p ∈ shiftOcc occ ↔ (p.1 + 1, p.2) ∈ occ := by
  simp only [shiftOcc, List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, o⟩, h, he⟩
    split at he
    · cases he
    · cases he; rename_i hi
      have : i - 1 + 1 = i := by omega
      simpa [this] using h
  · intro h
    exact ⟨(p.1 + 1, p.2), h, by simp⟩

theorem shiftOcc_names_sublist (occ : List (Nat × Nat)) :
    ((shiftOcc occ).map Prod.snd).Sublist (occ.map Prod.snd) := by
  induction occ with
  | nil => simp [shiftOcc]
  | cons p occ ih =>
    simp only [shiftOcc] at ih ⊢
    by_cases h : p.1 = 0
    · simp only [List.filterMap_cons, h, ite_true]; exact ih.cons _
    · simp only [List.filterMap_cons, h, ite_false, List.map_cons]; exact ih.cons_cons _

theorem occ0_sublist (occ : List (Nat × Nat)) : (occ0 occ).Sublist (occ.map Prod.snd) :=
  (List.filter_sublist).map _


@[simp] theorem revRange_length : ∀ d, (revRange d).length = d
  | 0 => rfl
  | d + 1 => by simp [revRange, revRange_length d]

theorem argOcc_mem : ∀ {is : List Nat} {n : Nat} {p : Nat × Nat}, p ∈ argOcc is n →
    n ≤ p.2 ∧ p.2 < n + is.length
  | [], _, _, h => by simp [argOcc] at h
  | i :: is, n, p, h => by
    simp only [argOcc, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := argOcc_mem h; simp only [List.length_cons]; omega

theorem argOcc_nodup : ∀ (is : List Nat) (n : Nat), ((argOcc is n).map Prod.snd).Nodup
  | [], _ => by simp [argOcc]
  | i :: is, n => by
    simp only [argOcc, List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, argOcc_nodup is (n + 1)⟩
    rintro ⟨p, hp, he⟩
    have := argOcc_mem hp; omega

theorem argChain_vars : ∀ {is : List Nat} {n : Nat} {K : HTree} {v : Nat}, v ∈ (argChain is n K).vars →
    (n ≤ v ∧ v < n + is.length) ∨ v ∈ K.vars
  | [], _, _, _, h => .inr h
  | _ :: is, n, K, v, h => by
    simp only [argChain, HTree.vars, List.mem_append, List.mem_singleton] at h
    rcases h with rfl | h
    · exact .inl ⟨Nat.le_refl _, by simp⟩
    · rcases argChain_vars h with h | h
      · exact .inl (by simp only [List.length_cons]; omega)
      · exact .inr h

theorem argChain_subst : ∀ (is : List Nat) (n : Nat) (K : HTree) (S : Nat → Option HTree),
    (∀ v, n ≤ v → v < n + is.length → S v = none) → (argChain is n K).subst S = argChain is n (K.subst S)
  | [], _, _, _, _ => rfl
  | _ :: is, n, K, S, h => by
    simp only [argChain, HTree.subst, h n (Nat.le_refl _) (by simp), Option.getD_none]
    rw [argChain_subst is (n + 1) K S (fun v h1 h2 => h v (by omega) (by simp only [List.length_cons]; omega))]

theorem comp_indep : ∀ (e : FExp) (K K' : HTree) (n : Nat),
    (comp e K n).occ = (comp e K' n).occ ∧ (comp e K n).next = (comp e K' n).next
  | .lit _, _, _, _ => ⟨rfl, rfl⟩
  | .var _, _, _, _ => ⟨rfl, rfl⟩
  | .op o a b, K, K', n => by
    simp only [comp]
    obtain ⟨h1, h2⟩ := comp_indep a (.opr (.num (.sym o)) (.opr (.var n) K))
      (.opr (.num (.sym o)) (.opr (.var n) K')) (comp b (.var n) (n + 1)).next
    exact ⟨by rw [h1], h2⟩
  | .let_ a b, K, K', n => by
    simp only [comp]
    obtain ⟨hb1, hb2⟩ := comp_indep b K K' n
    rw [hb1, hb2]
    exact ⟨rfl, rfl⟩
  | .ifz v z s, K, K', n => by
    simp only [comp]
    obtain ⟨h1, h2⟩ := comp_indep v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K)
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K')
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    exact ⟨by rw [h1], h2⟩
  | .ifzL d nz ns v _ _, K, K', n => by
    simp only [comp]
    obtain ⟨h1, h2⟩ := comp_indep v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K))
      (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K')) (n + d)
    exact ⟨by rw [h1], h2⟩
  | .call _ _, _, _, _ => ⟨rfl, rfl⟩

/-- `comp`'s variables: fresh ones in `[n, next)`, and those of the continuation. -/
theorem comp_facts : ∀ (e : FExp) (K : HTree) (n : Nat),
    n ≤ (comp e K n).next ∧
    (∀ p ∈ (comp e K n).occ, n ≤ p.2 ∧ p.2 < (comp e K n).next) ∧
    ((comp e K n).occ.map Prod.snd).Nodup ∧
    (∀ v ∈ bagVars (comp e K n).bag, (n ≤ v ∧ v < (comp e K n).next) ∨ v ∈ K.vars)
  | .lit _, K, n => by
    refine ⟨Nat.le_refl _, by simp [comp], by simp [comp], ?_⟩
    intro v hv; simp [comp, HTree.vars] at hv; exact .inr hv
  | .var _, K, n => by
    refine ⟨Nat.le_succ _, by simp [comp], by simp [comp], ?_⟩
    intro v hv
    simp only [comp, bagVars_cons, HTree.vars, bagVars_nil, List.append_nil, List.mem_append,
      List.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact .inl ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact .inr hv
  | .op o a b, K, n => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · have := a2 p hp; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨b3, a3, ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := b2 p hp; have := a2 q hq; omega
    · intro v hv
      rcases List.mem_append.1 (by simpa using hv) with hv | hv
      · rcases b4 v hv with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)
      · rcases a4 v hv with h | h
        · exact .inl (by omega)
        · simp only [HTree.vars, List.nil_append, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact .inl (by omega)
          · exact .inr h
  | .let_ a b, K, n => by
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b K n
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := a2 p hp; omega
      · have := b2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨a3, b3.sublist (shiftOcc_names_sublist _), ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := a2 p hp; have := b2 _ (mem_shiftOcc.1 hq); simp only at this; omega
    · intro v hv
      rcases List.mem_append.1 (by simpa using hv) with hv | hv
      · rcases a4 v hv with h | h
        · exact .inl (by omega)
        · rw [dupTree_vars] at h
          have := b2 _ (mem_occ0.1 h); simp only at this; exact .inl (by omega)
      · rcases b4 v hv with h | h
        · exact .inl (by omega)
        · exact .inr h
  | .ifz v z s, K, n => by
    obtain ⟨z1, z2, z3, z4⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, s3, s4⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K) (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · have := v2 p hp; omega
      · have := z2 p hp; omega
      · have := s2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
      refine ⟨⟨v3, z3, ?_⟩, s3.sublist (shiftOcc_names_sublist _), ?_⟩
      · intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have := v2 p hp; have := z2 q hq; omega
      · intro x hx y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have hq' := s2 _ (mem_shiftOcc.1 hq); simp only at hq'
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := v2 p hp; omega
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; have := z2 p hp; omega
    · intro w hw
      simp only [bagVars_append, List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · rcases v4 w hw with h | h
        · exact .inl (by omega)
        · simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton, or_assoc] at h
          rcases h with h | h | h | h
          · exact .inl (by omega)
          · have := s2 _ (mem_occ0.1 h); simp only at this; exact .inl (by omega)
          · exact .inl (by omega)
          · exact .inr h
      · rcases z4 w hw with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)
      · rcases s4 w hw with h | h
        · exact .inl (by omega)
        · simp [HTree.vars] at h; exact .inl (by omega)
  | .ifzL d nz ns v _ _, K, n => by
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    simp only [comp]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := v2 p hp; omega
      · have := argOcc_mem hp; simp only [revRange_length] at this; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨v3, argOcc_nodup _ _, ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := v2 p hp; have := argOcc_mem hq; simp only [revRange_length] at this; omega
    · intro w hw
      rcases v4 w hw with h | h
      · exact .inl (by omega)
      · simp only [HTree.vars, List.nil_append] at h
        rcases argChain_vars h with h | h
        · simp only [revRange_length] at h; exact .inl (by omega)
        · exact .inr h
  | .call _ idxs, K, n => by
    simp only [comp]
    refine ⟨by omega, fun p hp => argOcc_mem hp, argOcc_nodup _ _, ?_⟩
    intro w hw
    simp only [bagVars_cons, HTree.vars, List.nil_append, bagVars_nil, List.append_nil] at hw
    rcases argChain_vars hw with h | h
    · exact .inl h
    · exact .inr h

/-- Substituting for variables outside `comp`'s fresh range is substituting into the continuation. -/
theorem comp_subst_K : ∀ (e : FExp) (K : HTree) (n : Nat) (S : Nat → Option HTree),
    (∀ v, n ≤ v → v < (comp e K n).next → S v = none) →
    (comp e K n).bag.map (Redex.subst S) = (comp e (K.subst S) n).bag
  | .lit _, K, n, S, _ => by simp [comp, Redex.subst, HTree.subst]
  | .var _, K, n, S, h => by
    have := h n (Nat.le_refl _) (by simp [comp])
    simp [comp, Redex.subst, HTree.subst, this]
  | .op o a b, K, n, S, h => by
    obtain ⟨b1, -, -, -⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, -, -, -⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    simp only [comp] at h ⊢
    have hn : S n = none := h n (Nat.le_refl _) (by omega)
    rw [List.map_append, comp_subst_K b _ (n + 1) S (fun v h1 h2 => h v (by omega) (by omega)),
      comp_subst_K a _ _ S (fun v h1 h2 => h v (by omega) (by omega))]
    simp [HTree.subst, hn]
  | .let_ a b, K, n, S, h => by
    obtain ⟨b1, b2, -, -⟩ := comp_facts b K n
    obtain ⟨a1, -, -, -⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    simp only [comp] at h ⊢
    have hd : (dupTree (occ0 (comp b K n).occ)).subst S = dupTree (occ0 (comp b K n).occ) := by
      apply HTree.subst_id_of
      intro v hv
      rw [dupTree_vars] at hv
      have := b2 _ (mem_occ0.1 hv); simp only at this
      exact h v (by omega) (by omega)
    obtain ⟨hi1, hi2⟩ := comp_indep b K (K.subst S) n
    rw [List.map_append, comp_subst_K a _ _ S (fun v h1 h2 => h v (by omega) (by omega)),
      comp_subst_K b _ n S (fun v h1 h2 => h v (by omega) (by omega)), hd, hi1, hi2]
  | .ifz v z s, K, n, S, h => by
    obtain ⟨z1, -, -, -⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, -, -⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, -, -, -⟩ := comp_facts v
      (.swi (.con (.var n) (.con (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ))
        (.var (n + 1)))) K) (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    simp only [comp] at h ⊢
    have hn : S n = none := h n (Nat.le_refl _) (by omega)
    have hn1 : S (n + 1) = none := h (n + 1) (by omega) (by omega)
    have hd : (dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)).subst S =
        dupTree (occ0 (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ) := by
      apply HTree.subst_id_of
      intro w hw
      rw [dupTree_vars] at hw
      have := s2 _ (mem_occ0.1 hw); simp only at this
      exact h w (by omega) (by omega)
    rw [List.map_append, List.map_append, comp_subst_K v _ _ S (fun w h1 h2 => h w (by omega) (by omega)),
      comp_subst_K z _ (n + 2) S (fun w h1 h2 => h w (by omega) (by omega)),
      comp_subst_K s _ _ S (fun w h1 h2 => h w (by omega) (by omega))]
    simp [HTree.subst, hn, hn1, hd]
  | .ifzL d nz ns v _ _, K, n, S, h => by
    obtain ⟨v1, -, -, -⟩ := comp_facts v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    simp only [comp] at h ⊢
    rw [comp_subst_K v _ _ S (fun w h1 h2 => h w (by omega) (by omega))]
    simp only [HTree.subst]
    rw [argChain_subst _ _ _ _ (fun w h1 h2 => h w h1 (by simp only [revRange_length] at h2; omega))]
  | .call _ idxs, K, n, S, h => by
    simp only [comp] at h ⊢
    simp only [List.map_cons, List.map_nil, Redex.subst, HTree.subst]
    rw [argChain_subst _ _ _ _ (fun w h1 h2 => h w h1 h2)]

/-! ### Renaming: a definition's net under CALL's fresh names -/

theorem dupTree_rename (f : Nat → Nat) : ∀ os : List Nat, (dupTree os).rename f = dupTree (os.map f)
  | [] => rfl
  | [_] => rfl
  | o :: o' :: os => by simp [dupTree, HTree.rename, dupTree_rename f (o' :: os)]

def shiftP (b : Nat) (p : Nat × Nat) : Nat × Nat := (p.1, p.2 + b)

theorem occ0_shift (b : Nat) (occ : List (Nat × Nat)) : occ0 (occ.map (shiftP b)) = (occ0 occ).map (· + b) := by
  induction occ with
  | nil => rfl
  | cons p occ ih =>
    simp only [occ0, List.map_cons, List.filter_cons, shiftP] at ih ⊢
    split <;> simp_all

theorem occAt_shift (i b : Nat) (occ : List (Nat × Nat)) :
    occAt i (occ.map (shiftP b)) = (occAt i occ).map (· + b) := by
  induction occ with
  | nil => rfl
  | cons p occ ih =>
    simp only [occAt, List.map_cons, List.filter_cons, shiftP] at ih ⊢
    split <;> simp_all

theorem shiftOcc_shift (b : Nat) (occ : List (Nat × Nat)) :
    shiftOcc (occ.map (shiftP b)) = (shiftOcc occ).map (shiftP b) := by
  induction occ with
  | nil => rfl
  | cons p occ ih =>
    simp only [shiftOcc, List.map_cons, List.filterMap_cons, shiftP] at ih ⊢
    by_cases h : p.1 = 0 <;> simp [h, ih, shiftP]

theorem argChain_rename (b : Nat) : ∀ (is : List Nat) (n : Nat) (K : HTree),
    (argChain is n K).rename (· + b) = argChain is (n + b) (K.rename (· + b))
  | [], _, _ => rfl
  | _ :: is, n, K => by
    simp only [argChain, HTree.rename, argChain_rename b is (n + 1) K]
    congr 2; omega

theorem argOcc_shift (b : Nat) : ∀ (is : List Nat) (n : Nat),
    (argOcc is n).map (shiftP b) = argOcc is (n + b)
  | [], _ => rfl
  | i :: is, n => by
    simp only [argOcc, List.map_cons, shiftP, argOcc_shift b is (n + 1)]
    congr 2; omega

theorem comp_rename (b : Nat) : ∀ (e : FExp) (K : HTree) (n : Nat),
    (comp e K n).bag.map (Redex.rename (· + b)) = (comp e (K.rename (· + b)) (n + b)).bag ∧
    (comp e K n).occ.map (shiftP b) = (comp e (K.rename (· + b)) (n + b)).occ ∧
    (comp e K n).next + b = (comp e (K.rename (· + b)) (n + b)).next
  | .lit _, K, n => by simp [comp, Redex.rename, HTree.rename]
  | .var _, K, n => by simp [comp, Redex.rename, HTree.rename, shiftP]; omega
  | .op o a b', K, n => by
    obtain ⟨b1, b2, b3⟩ := comp_rename b b' (.var n) (n + 1)
    obtain ⟨a1, a2, a3⟩ := comp_rename b a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b' (.var n) (n + 1)).next
    simp only [HTree.rename] at b1 b2 b3 a1 a2 a3
    simp only [comp, List.map_append]
    rw [show n + 1 + b = n + b + 1 by omega] at b1 b2 b3
    rw [b3] at a1 a2 a3
    exact ⟨by rw [b1, a1], by rw [b2, a2], a3⟩
  | .let_ a b', K, n => by
    obtain ⟨b1, b2, b3⟩ := comp_rename b b' K n
    obtain ⟨a1, a2, a3⟩ := comp_rename b a (dupTree (occ0 (comp b' K n).occ)) (comp b' K n).next
    simp only [comp, List.map_append]
    rw [dupTree_rename, ← occ0_shift, b2, b3] at a1 a2 a3
    refine ⟨by rw [a1, b1], ?_, a3⟩
    rw [a2, ← shiftOcc_shift, b2]
  | .ifz v z s, K, n => by
    obtain ⟨z1, z2, z3⟩ := comp_rename b z (.var n) (n + 2)
    obtain ⟨s1, s2, s3⟩ := comp_rename b s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, v2, v3⟩ := comp_rename b v (.swi (.con (.var n) (.con (dupTree (occ0
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)) (.var (n + 1)))) K)
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    simp only [HTree.rename] at z1 z2 z3 s1 s2 s3 v1 v2 v3
    rw [show n + 2 + b = n + b + 2 by omega] at z1 z2 z3
    rw [z3, show n + 1 + b = n + b + 1 by omega] at s1 s2 s3
    rw [dupTree_rename, ← occ0_shift, s2, s3, show n + 1 + b = n + b + 1 by omega] at v1 v2 v3
    simp only [comp, List.map_append]
    refine ⟨by rw [v1, z1, s1], ?_, v3⟩
    rw [v2, z2, ← shiftOcc_shift, s2]
  | .ifzL d nz ns v _ _, K, n => by
    obtain ⟨v1, v2, v3⟩ := comp_rename b v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    simp only [HTree.rename, argChain_rename] at v1 v2 v3
    rw [show n + d + b = n + b + d by omega] at v1 v2 v3
    simp only [comp, List.map_append]
    exact ⟨v1, by rw [v2, argOcc_shift], v3⟩
  | .call _ idxs, K, n => by
    simp only [comp, List.map_cons, List.map_nil, Redex.rename, HTree.rename, argChain_rename, argOcc_shift]
    refine ⟨trivial, trivial, by omega⟩

/-! ### Facts about `compAll` and `defNet` -/

theorem compAll_facts : ∀ (fs : List FExp) (j n : Nat),
    n ≤ (compAll fs j n).next ∧
    (∀ p ∈ (compAll fs j n).occ, n ≤ p.2 ∧ p.2 < (compAll fs j n).next) ∧
    ((compAll fs j n).occ.map Prod.snd).Nodup ∧
    (∀ v ∈ bagVars (compAll fs j n).bag, (n ≤ v ∧ v < (compAll fs j n).next) ∨ (j ≤ v ∧ v < j + fs.length))
  | [], j, n => by simp [compAll]
  | f :: fs, j, n => by
    obtain ⟨c1, c2, c3, c4⟩ := comp_facts f (.var j) n
    obtain ⟨r1, r2, r3, r4⟩ := compAll_facts fs (j + 1) (comp f (.var j) n).next
    simp only [compAll]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := c2 p hp; omega
      · have := r2 p hp; omega
    · rw [List.map_append, List.nodup_append]
      refine ⟨c3, r3, ?_⟩
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := c2 p hp; have := r2 q hq; omega
    · intro v hv
      simp only [bagVars_append, List.mem_append] at hv
      rcases hv with hv | hv
      · rcases c4 v hv with h | h
        · exact .inl (by omega)
        · simp only [HTree.vars, List.mem_singleton] at h; exact .inr (by simp only [List.length_cons]; omega)
      · rcases r4 v hv with h | h
        · exact .inl (by omega)
        · exact .inr (by simp only [List.length_cons]; omega)

theorem compAll_rename (b : Nat) : ∀ (fs : List FExp) (j n : Nat),
    (compAll fs j n).bag.map (Redex.rename (· + b)) = (compAll fs (j + b) (n + b)).bag ∧
    (compAll fs j n).occ.map (shiftP b) = (compAll fs (j + b) (n + b)).occ ∧
    (compAll fs j n).next + b = (compAll fs (j + b) (n + b)).next
  | [], j, n => by simp [compAll]
  | f :: fs, j, n => by
    obtain ⟨c1, c2, c3⟩ := comp_rename b f (.var j) n
    obtain ⟨r1, r2, r3⟩ := compAll_rename b fs (j + 1) (comp f (.var j) n).next
    simp only [HTree.rename] at c1 c2 c3
    rw [c3, show j + 1 + b = j + b + 1 by omega] at r1 r2 r3
    simp only [compAll, List.map_append]
    exact ⟨by rw [c1, r1], by rw [c2, r2], r3⟩

theorem paramTree_rename (b : Nat) (occ : List (Nat × Nat)) : ∀ (ps : List Nat) (R : HTree),
    (paramTree occ ps R).rename (· + b) = paramTree (occ.map (shiftP b)) ps (R.rename (· + b))
  | [], _ => rfl
  | p :: ps, R => by simp only [paramTree, HTree.rename, dupTree_rename, occAt_shift, paramTree_rename b occ ps R]

theorem outVars_rename (b : Nat) : ∀ (m j : Nat), (tup (outVars m j)).rename (· + b) = tup (outVars m (j + b))
  | 0, _ => rfl
  | 1, j => rfl
  | m + 2, j => by
    have := outVars_rename b (m + 1) (j + 1)
    rw [show j + 1 + b = j + b + 1 by omega] at this
    simp only [outVars] at this ⊢
    simp only [tup, HTree.rename, this]

theorem defNet_rename (b : Nat) (L : String) (ps : List Nat) (fs : List FExp) :
    (defNet L ps fs).root.rename (· + b) =
      paramTree (compAll fs b (fs.length + b)).occ ps (tup (outVars fs.length b)) ∧
    (defNet L ps fs).bag.map (Redex.rename (· + b)) = (compAll fs b (fs.length + b)).bag := by
  obtain ⟨r1, r2, -⟩ := compAll_rename b fs 0 fs.length
  simp only [Nat.zero_add] at r1 r2
  refine ⟨?_, r1⟩
  simp only [defNet, paramTree_rename, r2, outVars_rename, Nat.zero_add]

/-- A bound above every element. -/
def bound : List Nat → Nat
  | [] => 0
  | a :: l => max a (bound l)

theorem le_bound : ∀ {l : List Nat} {v : Nat}, v ∈ l → v ≤ bound l
  | a :: l, v, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · have := le_bound h; simp only [bound]; omega

/-! ### Parameters meet arguments -/

theorem occ0_sublist' (occ : List (Nat × Nat)) (i : Nat) : (occAt i occ).Sublist (occ.map Prod.snd) :=
  (List.filter_sublist).map _

/-- The substitution the parameter tree's duplicators perform: occurrence of `ps[j]` gets `Ns[j]`. -/
def pSub (occ : List (Nat × Nat)) : List Nat → List HTree → Nat → Option HTree
  | p :: ps, N :: Ns => merge (many (occAt p occ) N) (pSub occ ps Ns)
  | _, _ => fun _ => none

theorem mem_occAt {i o : Nat} {occ : List (Nat × Nat)} : o ∈ occAt i occ ↔ (i, o) ∈ occ := by
  simp only [occAt, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨i', o'⟩, ⟨h, hi⟩, rfl⟩; simp only at hi; subst hi; exact h
  · intro h; exact ⟨(i, o), ⟨h, rfl⟩, rfl⟩

theorem pSub_closed (occ : List (Nat × Nat)) : ∀ (ps : List Nat) (Ns : List HTree), (∀ N ∈ Ns, N.vars = []) →
    ClosedImg (pSub occ ps Ns)
  | p :: ps, N :: Ns, h => closedImg_merge (closedImg_many (h N (by simp)))
      (pSub_closed occ ps Ns (fun M hM => h M (List.mem_cons_of_mem _ hM)))
  | [], _, _ => fun _ _ h => by simp [pSub] at h
  | _ :: _, [], _ => fun _ _ h => by simp [pSub] at h

theorem pSub_none (occ : List (Nat × Nat)) (o : Nat) : ∀ (ps : List Nat) (Ns : List HTree),
    (∀ i ∈ ps, (i, o) ∉ occ) → pSub occ ps Ns o = none
  | p :: ps, N :: Ns, h => by
    have h1 : o ∉ occAt p occ := fun hm => h p (by simp) (mem_occAt.1 hm)
    simp [pSub, merge, many, h1, pSub_none occ o ps Ns (fun i hi => h i (List.mem_cons_of_mem _ hi))]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem pSub_occ (occ : List (Nat × Nat)) (hnd : (occ.map Prod.snd).Nodup) (q : Nat × Nat) (hq : q ∈ occ) :
    ∀ (ps : List Nat) (ws : List (Option Nat)), ps.length = ws.length → q.1 ∈ ps →
      pSub occ ps (ws.map nul) q.2 = some (nul (bindEnv ps ws q.1))
  | p :: ps, w :: ws, hl, hm => by
    by_cases hp : q.1 = p
    · have : q.2 ∈ occAt p occ := mem_occAt.2 (by rw [← hp]; exact hq)
      simp [pSub, merge, many, this, bindEnv, hp]
    · have h1 : q.2 ∉ occAt p occ := by
        intro hm'
        have := nodup_name hnd hq (mem_occAt.1 hm') rfl
        exact hp (by rw [this])
      have hm' : q.1 ∈ ps := by simpa [hp] using hm
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp [pSub, merge, many, h1, bindEnv, hp, pSub_occ occ hnd q hq ps ws hl hm']
  | [], _, _, hm => by simp at hm

theorem paramTree_vars {occ : List (Nat × Nat)} : ∀ {ps : List Nat} {R : HTree} {v : Nat},
    v ∈ (paramTree occ ps R).vars → (∃ i ∈ ps, (i, v) ∈ occ) ∨ v ∈ R.vars
  | [], _, _, h => .inr h
  | p :: ps, R, v, h => by
    simp only [paramTree, HTree.vars, dupTree_vars, List.mem_append] at h
    rcases h with h | h
    · exact .inl ⟨p, by simp, mem_occAt.1 h⟩
    · rcases paramTree_vars h with ⟨i, hi, h⟩ | h
      · exact .inl ⟨i, List.mem_cons_of_mem _ hi, h⟩
      · exact .inr h

theorem argTree_vars : ∀ {Ns : List HTree} {K : HTree} {v : Nat}, (∀ N ∈ Ns, N.vars = []) →
    v ∈ (argTree Ns K).vars → v ∈ K.vars
  | [], _, _, _, h => h
  | N :: Ns, K, v, hN, h => by
    simp only [argTree, HTree.vars, hN N (by simp), List.nil_append] at h
    exact argTree_vars (fun M hM => hN M (List.mem_cons_of_mem _ hM)) h

/-- **The parameter tree meets the argument tree**: one annihilation per parameter, each argument
spread to its parameter's occurrences, and the outputs left facing the continuation. -/
theorem sParams (book : List HDef) (occ : List (Nat × Nat)) (hnd : (occ.map Prod.snd).Nodup) :
    ∀ (ps : List Nat) (Ns : List HTree) (R K root : HTree) (pre mid post : List Redex),
    ps.length = Ns.length → (∀ N ∈ Ns, Nullary N) → ps.Nodup →
    (∀ p ∈ occ, p.2 ∉ root.vars ∧ p.2 ∉ bagVars pre ∧ p.2 ∉ bagVars post ∧ p.2 ∉ R.vars ∧ p.2 ∉ K.vars) →
    Steps book ⟨root, pre ++ (paramTree occ ps R, argTree Ns K) :: (mid ++ post)⟩
      ⟨root, pre ++ (R, K) :: (mid.map (Redex.subst (pSub occ ps Ns)) ++ post)⟩
  | [], [], R, K, root, pre, mid, post, _, _, _, _ => by
    refine steps_eq ?_
    simp only [paramTree, argTree, pSub]
    rw [bag_subst_id mid (fun _ _ => rfl)]
  | p :: ps, N :: Ns, R, K, root, pre, mid, post, hl, hN, hpn, hF => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hN0 := hN N (by simp)
    have hNs : ∀ M ∈ Ns, Nullary M := fun M hM => hN M (List.mem_cons_of_mem _ hM)
    have hpn' := (List.nodup_cons.1 hpn)
    simp only [paramTree, argTree]
    -- annihilate, spread `N` to the occurrences of `p`, then the rest
    refine (sRule pre (mid ++ post) (a := .con (dupTree (occAt p occ)) (paramTree occ ps R))
      (b := .con N (argTree Ns K)) (ns := [(dupTree (occAt p occ), N), (paramTree occ ps R, argTree Ns K)])
      rfl rfl rfl).trans ?_
    refine (sSwap pre ((paramTree occ ps R, argTree Ns K) :: (mid ++ post)) (a := dupTree (occAt p occ)) (b := N)
      (by simp) rfl).trans ?_
    have hos : ∀ o ∈ occAt p occ, (p, o) ∈ occ := fun o h => mem_occAt.1 h
    refine (sSpread N hN0 (occAt p occ) pre ((paramTree occ ps R, argTree Ns K) :: mid) post
      ((hnd.sublist (occ0_sublist' occ p)))
      (fun o ho => let h := hF (p, o) (hos o ho); ⟨h.1, h.2.1, h.2.2.1⟩) (by simp) rfl).trans ?_
    have hkeep : Redex.subst (many (occAt p occ) N) (paramTree occ ps R, argTree Ns K) =
        (paramTree occ ps R, argTree Ns K) := by
      simp only [Redex.subst, Prod.mk.injEq]
      constructor
      · refine HTree.subst_id_of _ (fun v hv => ?_)
        have hnot : v ∉ occAt p occ := by
          intro hm
          have hpv := mem_occAt.1 hm
          rcases paramTree_vars hv with ⟨i, hi, hiv⟩ | hR
          · have := nodup_name hnd hpv hiv rfl
            simp only [Prod.mk.injEq] at this
            exact hpn'.1 (this.1 ▸ hi)
          · exact (hF _ hpv).2.2.2.1 hR
        simp [many, hnot]
      · refine HTree.subst_id_of _ (fun v hv => ?_)
        have hK := argTree_vars (fun M hM => (hNs M hM).vars) hv
        have hnot : v ∉ occAt p occ := fun hm => (hF _ (mem_occAt.1 hm)).2.2.2.2 hK
        simp [many, hnot]
    simp only [List.map_cons, hkeep]
    refine (sParams book occ hnd ps Ns R K root pre (mid.map (Redex.subst (many (occAt p occ) N))) post
      hl hNs hpn'.2 hF).trans ?_
    refine steps_eq ?_
    simp only [pSub]
    rw [bag_subst_merge _ (closedImg_many hN0.vars)]

/-! ### The outputs, then a whole call -/

/-- **What an expression reducing means**: `comp e K n`'s redexes, every occurrence of index `i`
holding `nul (ρ i)`, reduce to the one redex `nul v ~ K`, beside any `pre` and `post` in which the
fresh variables `[n, next)` do not occur. -/
def Reduces (book : List HDef) (e : FExp) (ρ : Nat → Option Nat) (v : Option Nat) : Prop :=
  ∀ (K : HTree) (n : Nat) (S : Nat → Option HTree) (root : HTree) (pre post : List Redex),
    (∀ p ∈ (comp e K n).occ, S p.2 = some (nul (ρ p.1))) →
    (∀ o, n ≤ o → o < (comp e K n).next → (∀ p ∈ (comp e K n).occ, p.2 ≠ o) → S o = none) →
    ClosedImg S → K.subst S = K →
    (∀ w ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, w < n ∨ (comp e K n).next ≤ w) →
    Steps book ⟨root, pre ++ ((comp e K n).bag.map (Redex.subst S) ++ post)⟩
      ⟨root, pre ++ (nul v, K) :: post⟩

/-- Output `j + i` gets `nul vs[i]`. -/
def outSub (j : Nat) : List (Option Nat) → Nat → Option HTree
  | [] => fun _ => none
  | v :: vs => fun m => if m = j then some (nul v) else outSub (j + 1) vs m

theorem outSub_none (j : Nat) : ∀ (vs : List (Option Nat)) (m : Nat), (m < j ∨ j + vs.length ≤ m) →
    outSub j vs m = none
  | [], _, _ => rfl
  | v :: vs, m, h => by
    simp only [List.length_cons] at h
    simp only [outSub]
    rw [if_neg (by omega), outSub_none (j + 1) vs m (by omega)]

theorem closedImg_outSub (j : Nat) : ∀ vs : List (Option Nat), ClosedImg (outSub j vs)
  | [] => fun _ _ h => by simp [outSub] at h
  | v :: vs => fun m T h => by
    simp only [outSub] at h
    split at h
    · cases h; exact nul_vars v
    · exact closedImg_outSub (j + 1) vs m T h

theorem HTree.subst_congr {S T : Nat → Option HTree} :
    ∀ (t : HTree), (∀ v ∈ t.vars, S v = T v) → t.subst S = t.subst T
  | .var n, h => by simp [HTree.subst, h n (by simp [HTree.vars])]
  | .era, _ => rfl
  | .ref _, _ => rfl
  | .num _, _ => rfl
  | .con a b, h | .dup a b, h | .opr a b, h | .swi a b, h => by
    simp only [HTree.vars, List.mem_append] at h
    simp only [HTree.subst, HTree.subst_congr a (fun v hv => h v (.inl hv)),
      HTree.subst_congr b (fun v hv => h v (.inr hv))]

theorem outVars_vars : ∀ {k j v : Nat}, v ∈ (tup (outVars k j)).vars → j ≤ v ∧ v < j + k
  | 0, _, _, h => by simp [outVars, tup, HTree.vars] at h
  | 1, j, v, h => by simp [outVars, tup, HTree.vars] at h; omega
  | k + 2, j, v, h => by
    simp only [outVars, tup, HTree.vars, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · omega
    · have := outVars_vars (k := k + 1) (j := j + 1) (by simpa only [outVars] using h); omega

theorem tup_outSub : ∀ (vs : List (Option Nat)) (j : Nat),
    (tup (outVars vs.length j)).subst (outSub j vs) = tup (vs.map nul)
  | [], _ => rfl
  | [v], j => by simp [outVars, tup, HTree.subst, outSub]
  | v :: v' :: vs, j => by
    have ih := tup_outSub (v' :: vs) (j + 1)
    simp only [List.length_cons] at ih ⊢
    simp only [outVars, tup, HTree.subst, List.map_cons] at ih ⊢
    simp only [outSub, if_pos rfl, Option.getD_some]
    congr 1
    rw [← ih]
    refine HTree.subst_congr _ (fun w hw => ?_)
    have := outVars_vars (k := vs.length + 1) (j := j + 1) (by simpa only [outVars] using hw)
    simp only [outSub]
    rw [if_neg (by omega)]

theorem sLinkSplit {book : List HDef} {root : HTree} (A B : List Redex) (x : Nat) (t : HTree)
    (hr : x ∉ root.vars) :
    Steps book ⟨root, A ++ (.var x, t) :: B⟩ ⟨root, A.map (Redex.subst (one x t)) ++ B.map (Redex.subst (one x t))⟩ := by
  have h := Step.link (book := book) (root := root) (pre := A) (post := B) (x := x) (t := t)
  rw [HTree.subst_id_of _ (fun v hv => one_none (fun h => by subst h; exact hr hv)), List.map_append] at h
  exact .single h

theorem HTree.vars_subst_dom {S : Nat → Option HTree} (hS : ClosedImg S) :
    ∀ (t : HTree) (v : Nat), v ∈ (t.subst S).vars → S v = none
  | .var n, v, h => by
    simp only [HTree.subst] at h
    cases hn : S n with
    | none => simp [hn, HTree.vars] at h; subst h; exact hn
    | some T => simp [hn, hS n T hn] at h
  | .era, _, h | .ref _, _, h | .num _, _, h => by simp [HTree.subst, HTree.vars] at h
  | .con a b, v, h | .dup a b, v, h | .opr a b, v, h | .swi a b, v, h => by
    simp only [HTree.subst, HTree.vars, List.mem_append] at h
    rcases h with h | h
    · exact HTree.vars_subst_dom hS a v h
    · exact HTree.vars_subst_dom hS b v h

/-- **The outputs reduce**, one after the other, each value linked into the tuple `T` that waits for
it facing the continuation. -/
theorem sOutputs (book : List HDef) (ρ : Nat → Option Nat) (S : Nat → Option HTree) (hS : ClosedImg S) :
    ∀ (fs : List FExp) (vs : List (Option Nat)) (j n : Nat) (T K root : HTree) (pre post : List Redex),
    fs.length = vs.length → j + fs.length ≤ n →
    (∀ (i : Nat) f v, fs[i]? = some f → vs[i]? = some v → Reduces book f ρ v) →
    (∀ p ∈ (compAll fs j n).occ, S p.2 = some (nul (ρ p.1))) →
    (∀ o, n ≤ o → o < (compAll fs j n).next → (∀ p ∈ (compAll fs j n).occ, p.2 ≠ o) → S o = none) →
    (∀ o, j ≤ o → o < j + fs.length → S o = none) →
    (∀ w ∈ root.vars ++ bagVars pre ++ bagVars post ++ K.vars, w < j) →
    (∀ w ∈ T.vars, w < j + fs.length) →
    Steps book ⟨root, pre ++ (T, K) :: ((compAll fs j n).bag.map (Redex.subst S) ++ post)⟩
      ⟨root, pre ++ (T.subst (outSub j vs), K) :: post⟩
  | [], [], j, n, T, K, root, pre, post, _, _, _, _, _, _, _, _ => by
    refine steps_eq ?_
    simp [compAll, HTree.subst_id_of T (fun _ _ => rfl), outSub]
  | f :: fs, v :: vs, j, n, T, K, root, pre, post, hl, hjn, hR, h1, h2, h3, hF, hT => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hjn hT h3
    obtain ⟨c1, c2, c3, c4⟩ := comp_facts f (.var j) n
    obtain ⟨r1, r2, r3, r4⟩ := compAll_facts fs (j + 1) (comp f (.var j) n).next
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    simp only [compAll] at h1 h2 ⊢
    have hSj : S j = none := h3 j (Nat.le_refl _) (by omega)
    -- the first output
    have hred := hR 0 f v rfl rfl (.var j) n S root (pre ++ [(T, K)])
      ((compAll fs (j + 1) (comp f (.var j) n).next).bag.map (Redex.subst S) ++ post)
      (fun p hp => h1 p (List.mem_append_left _ hp))
      (fun o ho1 ho2 hno => h2 o ho1 (by omega) (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hno p hp
        · have := r2 p hp; omega))
      hS (by simp [HTree.subst, hSj]) (by
        refine fresh4_mk (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_)
        · have := Fr w hw; omega
        · simp only [bagVars_append, bagVars_cons, bagVars_nil, List.append_nil, List.mem_append] at hw
          rcases hw with hw | hw | hw
          · have := Fp w hw; omega
          · have := hT w hw; omega
          · have := Fk w hw; omega
        · simp only [bagVars_append, List.mem_append] at hw
          rcases hw with hw | hw
          · rcases r4 w (bagVars_map_subst hS _ w hw) with h | h
            · omega
            · omega
          · have := Fq w hw; omega
        · simp only [HTree.vars, List.mem_singleton] at hw; omega)
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans (hred.trans ?_)
    -- its value, linked into `T`
    refine (sSwap (pre ++ [(T, K)]) ((compAll fs (j + 1) (comp f (.var j) n).next).bag.map (Redex.subst S) ++ post)
      (a := nul v) (b := .var j) rfl rfl).trans ?_
    refine (sLinkSplit (pre ++ [(T, K)]) _ j (nul v) (fun h => by have := Fr j h; omega)).trans ?_
    have epre : pre.map (Redex.subst (one j (nul v))) = pre :=
      bag_subst_id _ (fun w hw => one_none (by have := Fp w hw; omega))
    have eK : K.subst (one j (nul v)) = K := HTree.subst_id_of _ (fun w hw => one_none (by have := Fk w hw; omega))
    have epost : post.map (Redex.subst (one j (nul v))) = post :=
      bag_subst_id _ (fun w hw => one_none (by have := Fq w hw; omega))
    have erest : ((compAll fs (j + 1) (comp f (.var j) n).next).bag.map (Redex.subst S)).map
        (Redex.subst (one j (nul v))) = (compAll fs (j + 1) (comp f (.var j) n).next).bag.map (Redex.subst S) :=
      bag_subst_id _ (fun w hw => one_none (by
        rcases r4 w (bagVars_map_subst hS _ w hw) with h | h <;> omega))
    simp only [List.map_append, List.map_cons, List.map_nil, epre, epost, erest, Redex.subst, eK,
      List.append_assoc, List.cons_append, List.nil_append]
    -- the rest
    have IH := sOutputs book ρ S hS fs vs (j + 1) (comp f (.var j) n).next (T.subst (one j (nul v))) K root pre post
      hl (by omega) (fun i g w hg hw => hR (i + 1) g w hg hw)
      (fun p hp => h1 p (List.mem_append_right _ hp))
      (fun o ho1 ho2 hno => h2 o (by omega) ho2 (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · have := c2 p hp; omega
        · exact hno p hp))
      (fun o ho1 ho2 => h3 o (by omega) (by omega))
      (by
        refine fresh4_mk (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_)
        · have := Fr w hw; omega
        · have := Fp w hw; omega
        · have := Fq w hw; omega
        · have := Fk w hw; omega)
      (fun w hw => by
        have h := HTree.vars_subst (closedImg_one (nul_vars v)) T w hw
        have := hT w h
        have hne := HTree.vars_subst_dom (closedImg_one (nul_vars v)) T w hw
        have : w ≠ j := fun e => by subst e; simp [one] at hne
        omega)
    refine IH.trans (steps_eq ?_)
    rw [HTree.subst_merge _ (closedImg_one (nul_vars v))]
    have : merge (one j (nul v)) (outSub (j + 1) vs) = outSub j (v :: vs) := by
      funext m; by_cases hm : m = j
      · subst hm; simp [merge, one, outSub]
      · simp [merge, one, outSub, hm]
    rw [this]

theorem argTree_vars_K : ∀ {Ns : List HTree} {K : HTree} {v : Nat}, v ∈ K.vars → v ∈ (argTree Ns K).vars
  | [], _, _, h => h
  | N :: Ns, K, v, h => by
    simp only [argTree, HTree.vars, List.mem_append]
    exact .inr (argTree_vars_K h)

/-- A definition the book can call: at least one parameter, no index bound twice, every occurrence
in its body one of its parameters. -/
def DefOk (ps : List Nat) (fs : List FExp) : Prop :=
  ps ≠ [] ∧ ps.Nodup ∧ ∀ p ∈ (compAll fs 0 fs.length).occ, p.1 ∈ ps

theorem nullary_map_nul (ws : List (Option Nat)) : ∀ N ∈ ws.map nul, Nullary N := by
  intro N h; obtain ⟨w, -, rfl⟩ := List.mem_map.1 h; exact nullary_nul w

/-- **A call**: a reference meeting its arguments expands (CALL, on variables above every variable of
the configuration), its parameters meet the arguments, its outputs reduce, and the tuple of their
values meets the caller's continuation. -/
theorem callDef (book : List HDef) (L : String) (ps : List Nat) (fs : List FExp) (ws vs : List (Option Nat))
    (K root : HTree) (pre post : List Redex)
    (hb : book.find? (·.name == L) = some (defNet L ps fs)) (hok : DefOk ps fs)
    (hl : ps.length = ws.length) (hv : fs.length = vs.length)
    (hR : ∀ (i : Nat) f v, fs[i]? = some f → vs[i]? = some v → Reduces book f (bindEnv ps ws) v) :
    Steps book ⟨root, pre ++ (.ref L, argTree (ws.map nul) K) :: post⟩
      ⟨root, pre ++ (tup (vs.map nul), K) :: post⟩ := by
  obtain ⟨hne, hnd, hocc⟩ := hok
  let c : Cfg := ⟨root, pre ++ (.ref L, argTree (ws.map nul) K) :: post⟩
  let b := bound c.vars + 1
  have hc : ∀ v ∈ c.vars, v < b := fun v hv => Nat.lt_succ_of_le (le_bound hv)
  have hroot : ∀ v ∈ root.vars, v < b := fun v hv => hc v (by simp [c, Cfg.vars, hv])
  have hpre : ∀ v ∈ bagVars pre, v < b := fun v hv => hc v (by simp [c, Cfg.vars, hv])
  have hpost : ∀ v ∈ bagVars post, v < b := fun v hv => hc v (by simp [c, Cfg.vars, hv])
  have hK : ∀ v ∈ K.vars, v < b := fun v hv => hc v (by
    simp only [c, Cfg.vars, bagVars_append, bagVars_cons, List.mem_append, argTree_vars_K hv, true_or, or_true])
  obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
    cases ws with
    | nil => cases ps with
      | nil => exact absurd rfl hne
      | cons _ _ => simp at hl
    | cons w ws' => exact ⟨w, ws', rfl⟩
  -- CALL
  refine Steps.next (Step.call (root := root) (pre := pre) (post := post) (f := L)
    (t := argTree ((w :: ws').map nul) K) (d := defNet L ps fs) (fun u => u + b) hb
    ⟨.con, nul w, argTree (ws'.map nul) K, rfl, by decide⟩ (fun u _ v _ h => by omega)
    (fun u _ h => by have := hc _ h; omega)) ?_
  obtain ⟨e1, e2⟩ := defNet_rename b L ps fs
  rw [e1, e2]
  obtain ⟨f1, f2, f3, f4⟩ := compAll_facts fs b (fs.length + b)
  obtain ⟨-, r2, -⟩ := compAll_rename b fs 0 fs.length
  simp only [Nat.zero_add] at r2
  have hocc' : ∀ p ∈ (compAll fs b (fs.length + b)).occ, p.1 ∈ ps := by
    intro p hp
    rw [← r2] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hocc q hq
  -- the parameters meet the arguments
  refine (steps_eq (by simp)).trans ((sParams book _ f3 ps ((w :: ws').map nul) (tup (outVars fs.length b)) K root
    pre (compAll fs b (fs.length + b)).bag post (by simp [hl]) (nullary_map_nul _) hnd (fun p hp => by
      have := f2 p hp
      refine ⟨fun h => by have := hroot _ h; omega, fun h => by have := hpre _ h; omega,
        fun h => by have := hpost _ h; omega, fun h => by have := outVars_vars h; omega,
        fun h => by have := hK _ h; omega⟩)).trans ?_)
  -- the outputs reduce
  have hS := pSub_closed (compAll fs b (fs.length + b)).occ ps ((w :: ws').map nul)
    (fun N hN => (nullary_map_nul _ N hN).vars)
  refine (sOutputs book (bindEnv ps (w :: ws')) _ hS fs vs b (fs.length + b) (tup (outVars fs.length b)) K root pre post
    hv (by omega) hR
    (fun p hp => pSub_occ _ f3 p hp ps (w :: ws') hl (hocc' p hp))
    (fun o _ _ hno => pSub_none _ o ps _ (fun i _ hm => hno _ hm rfl))
    (fun o h1 h2 => pSub_none _ o ps _ (fun i _ hm => by have := f2 _ hm; simp only at this; omega))
    (fresh4_mk hroot hpre hpost hK)
    (fun v hv => by have := outVars_vars hv; omega)).trans ?_
  rw [hv, tup_outSub]
  exact .refl _

/-- Every lifted branch of an expression is in the book as `defNet` compiles it. -/
def Good (book : List HDef) : FExp → Prop
  | .op _ a b => Good book a ∧ Good book b
  | .let_ a b => Good book a ∧ Good book b
  | .ifz v z s => Good book v ∧ Good book z ∧ Good book s
  | .ifzL d nz ns v z s => Good book v ∧ Good book z ∧ Good book s ∧
      book.find? (·.name == nz) = some (defNet nz (revRange d) [z]) ∧ DefOk (revRange d) [z] ∧
      book.find? (·.name == ns) = some (defNet ns (0 :: (revRange d).map (· + 1)) [s]) ∧
      DefOk (0 :: (revRange d).map (· + 1)) [s]
  | _ => True

/-- Every definition of `D` is in the book as `defNet` compiles it. -/
def BookOk (book : List HDef) (D : List FDef) : Prop :=
  ∀ g d, D.find? (·.name == g) = some d →
    book.find? (·.name == g) = some (defNet g d.params [d.body]) ∧ DefOk d.params [d.body] ∧ Good book d.body

theorem argChain_S (S : Nat → Option HTree) (ρ : Nat → Option Nat) (K : HTree) : ∀ (is : List Nat) (n : Nat),
    (∀ p ∈ argOcc is n, S p.2 = some (nul (ρ p.1))) →
    (argChain is n K).subst S = argTree ((is.map ρ).map nul) (K.subst S)
  | [], _, _ => rfl
  | i :: is, n, h => by
    simp only [argChain, HTree.subst, h (i, n) (by simp [argOcc]), Option.getD_some, List.map_cons, argTree]
    rw [argChain_S S ρ K is (n + 1) (fun p hp => h p (by simp [argOcc, hp]))]

theorem bindEnv_revRange (ρ : Nat → Option Nat) : ∀ d, bindEnv (revRange d) ((revRange d).map ρ) = restrict d ρ
  | 0 => by funext i; simp [bindEnv, revRange, restrict]
  | d + 1 => by
    funext i
    simp only [revRange, List.map_cons, bindEnv, bindEnv_revRange ρ d, restrict]
    by_cases h : i = d
    · subst h; simp
    · by_cases h' : i < d
      · simp [h, h', show i < d + 1 by omega]
      · simp [h, h', show ¬ i < d + 1 by omega]

theorem bindEnv_succ (ρ : Nat → Option Nat) (x : Option Nat) : ∀ (ps : List Nat) (vs : List (Option Nat)),
    bindEnv (0 :: ps.map (· + 1)) (x :: vs) = cons x (bindEnv ps vs)
  | ps, vs => by
    funext i
    cases i with
    | zero =>
      simp [bindEnv]
    | succ i =>
      simp only [bindEnv, cons_succ, Nat.add_one_ne_zero, ite_false]
      induction ps generalizing vs with
      | nil => cases vs <;> simp [bindEnv]
      | cons p ps ih =>
        cases vs with
        | nil => simp [bindEnv]
        | cons v vs => simp [bindEnv, ih]

theorem sEraseArgs {book : List HDef} {root K : HTree} (pre post : List Redex) :
    ∀ (Ns : List HTree), (∀ N ∈ Ns, Nullary N) →
    Steps book ⟨root, pre ++ (.era, argTree Ns K) :: post⟩ ⟨root, pre ++ (.era, K) :: post⟩
  | [], _ => .refl _
  | N :: Ns, h => by
    refine (sRule pre post (a := .era) (b := .con N (argTree Ns K)) (ns := [(.era, N), (.era, argTree Ns K)])
      rfl rfl rfl).trans ?_
    refine (sRule pre ((.era, argTree Ns K) :: post) (localRule_void (.inl rfl) (h N (by simp))) (by simp) rfl).trans ?_
    exact (steps_eq (by simp)).trans (sEraseArgs pre post Ns (fun M hM => h M (List.mem_cons_of_mem _ hM)))

theorem comp_reduces_aux (book : List HDef) (D : List FDef) (fuel : Nat)
    (hcall : ∀ g idxs ρ v, evalF D fuel ρ (.call g idxs) = some v → Reduces book (.call g idxs) ρ v) :
    ∀ (e : FExp) (ρ : Nat → Option Nat) (v : Option Nat), Good book e → evalF D fuel ρ e = some v →
      Reduces book e ρ v
  | .lit w, ρ, v, _, he => by
    simp only [evalF, Option.some.injEq] at he; subst he
    intro K n S root pre post _ _ _ hK _
    simp only [comp, List.map_cons, List.map_nil, Redex.subst, HTree.subst, hK, nul,
      List.cons_append, List.nil_append]
    exact .refl _
  | .var i, ρ, v, _, he => by
    simp only [evalF, Option.some.injEq] at he; subst he
    intro K n S root pre post h1 _ _ hK _
    have := h1 (i, n) (by simp [comp])
    simp only [comp, List.map_cons, List.map_nil, Redex.subst, HTree.subst, hK, this,
      Option.getD_some, List.cons_append, List.nil_append]
    exact .refl _
  | .op o a b, ρ, v, hg, he => by
    obtain ⟨va, ha⟩ : ∃ va, evalF D fuel ρ a = some va := by
      cases h : evalF D fuel ρ a with
      | none => simp [evalF, h] at he
      | some x => exact ⟨x, rfl⟩
    obtain ⟨vb, hb⟩ : ∃ vb, evalF D fuel ρ b = some vb := by
      cases h : evalF D fuel ρ b with
      | none => simp [evalF, ha, h] at he
      | some x => exact ⟨x, rfl⟩
    simp only [evalF, ha, hb, Option.some.injEq] at he
    subst he
    have IHa' := comp_reduces_aux book D fuel hcall a ρ va hg.1 ha
    have IHb' := comp_reduces_aux book D fuel hcall b ρ vb hg.2 hb
    intro K n S root pre post h1 h2 hS hK hF
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b (.var n) (n + 1)
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    obtain ⟨i1, i2⟩ := comp_indep a (.opr (.num (.sym o)) (.opr (nul vb) K))
      (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
    have hsub := comp_subst_K a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next
      (one n (nul vb)) (fun v hv _ => one_none (by omega))
    have IHb := IHb' (.var n) (n + 1) S root pre
      ((comp a (.opr (.num (.sym o)) (.opr (.var n) K)) (comp b (.var n) (n + 1)).next).bag.map
        (Redex.subst S) ++ post)
    have IHa := IHa' (.opr (.num (.sym o)) (.opr (nul vb) K))
      (comp b (.var n) (n + 1)).next S root pre post
    simp only [comp] at h1 h2 hF ⊢
    rw [i1, i2] at IHa
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    have hKn : K.subst (one n (nul vb)) = K :=
      HTree.subst_id_of _ (fun v hv => one_none (by have := Fk v hv; omega))
    rw [show (HTree.opr (.num (.sym o)) (.opr (.var n) K)).subst (one n (nul vb)) =
      .opr (.num (.sym o)) (.opr (nul vb) K) by simp [HTree.subst, one, hKn]] at hsub
    generalize comp b (.var n) (n + 1) = rb at *
    generalize comp a (.opr (.num (.sym o)) (.opr (.var n) K)) rb.next = ra at *
    have hSn : S n = none := h2 n (Nat.le_refl _) (by omega) (by
      intro p hp; rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · have := a2 p hp; omega)
    -- b, then its value linked into a's continuation, then a
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHb (fun p hp => h1 p (List.mem_append_left _ hp)) ?_ hS (by simp [HTree.subst, hSn]) ?_).trans ?_)
    · intro o' ho1 ho2 hno
      refine h2 o' (by omega) (by omega) (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · exact hno p hp
      · have := a2 p hp; omega
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · simp only [bagVars_append, List.mem_append] at hv
        rcases hv with hv | hv
        · rcases a4 v (bagVars_map_subst hS _ v hv) with h | h
          · omega
          · simp only [HTree.vars, List.nil_append, List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · omega
            · have := Fk v h; omega
        · have := Fq v hv; omega
      · simp only [HTree.vars, List.mem_singleton] at hv; omega
    refine (sLinkR pre (ra.bag.map (Redex.subst S)) post n (nul vb)
      (fun h => by have := Fr n h; omega) (fun h => by have := Fp n h; omega)
      (fun h => by have := Fq n h; omega) rfl rfl).trans ?_
    rw [bag_subst_comm_one hS hSn (nul_subst S _), hsub]
    refine (IHa (fun p hp => h1 p (List.mem_append_right _ hp)) ?_ hS
      (by simp [HTree.subst, hK]) ?_).trans ?_
    · intro o' ho1 ho2 hno
      refine h2 o' (by omega) ho2 (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · have := b2 p hp; omega
      · exact hno p hp
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · have := Fq v hv; omega
      · simp only [HTree.vars, nul_vars, List.nil_append] at hv
        have := Fk v hv; omega
    -- the operator node meets the two values
    cases va with
    | none =>
      simp only [opW]
      refine (sRule pre post (a := .era) (b := .opr (.num (.sym o)) (.opr (nul vb) K))
        (ns := [(.era, .num (.sym o)), (.era, .opr (nul vb) K)]) rfl (by simp [nul]) rfl).trans ?_
      refine (sRule pre ((.era, .opr (nul vb) K) :: post) (a := .era) (b := .num (.sym o))
        (ns := []) rfl (by simp) rfl).trans ?_
      refine (sRule pre post (a := .era) (b := .opr (nul vb) K)
        (ns := [(.era, nul vb), (.era, K)]) rfl (by simp) rfl).trans ?_
      exact sRule pre ((.era, K) :: post) (localRule_void (.inl rfl) (nullary_nul vb)) (by simp)
        (by simp [nul])
    | some x =>
      cases vb with
      | none =>
        simp only [opW]
        refine (sRule pre post (a := .num (.u24 x)) (b := .opr (.num (.sym o)) (.opr .era K))
          (ns := [(.num (.part o x), .opr .era K)]) rfl (by simp [nul]) rfl).trans ?_
        refine (sRule pre post (a := .num (.part o x)) (b := .opr .era K)
          (ns := [(.era, .opr (.num (.part o x)) K)]) rfl (by simp) rfl).trans ?_
        refine (sRule pre post (a := .era) (b := .opr (.num (.part o x)) K)
          (ns := [(.era, .num (.part o x)), (.era, K)]) rfl (by simp) rfl).trans ?_
        exact sRule pre ((.era, K) :: post) (a := .era) (b := .num (.part o x)) (ns := []) rfl (by simp)
          (by simp [nul])
      | some y =>
        simp only [opW]
        refine (sRule pre post (a := .num (.u24 x)) (b := .opr (.num (.sym o)) (.opr (.num (.u24 y)) K))
          (ns := [(.num (.part o x), .opr (.num (.u24 y)) K)]) rfl (by simp [nul]) rfl).trans ?_
        exact sRule pre post (a := .num (.part o x)) (b := .opr (.num (.u24 y)) K)
          (ns := [(.num (.u24 (o.u24 x y)), K)]) rfl (by simp) (by simp [nul])
  | .let_ a b, ρ, v, hg, he => by
    obtain ⟨va, ha⟩ : ∃ va, evalF D fuel ρ a = some va := by
      cases h : evalF D fuel ρ a with
      | none => simp [evalF, h] at he
      | some x => exact ⟨x, rfl⟩
    simp only [evalF, ha] at he
    have IHa' := comp_reduces_aux book D fuel hcall a ρ va hg.1 ha
    have IHb' := comp_reduces_aux book D fuel hcall b (cons va ρ) v hg.2 he
    intro K n S root pre post h1 h2 hS hK hF
    obtain ⟨b1, b2, b3, b4⟩ := comp_facts b K n
    obtain ⟨a1, a2, a3, a4⟩ := comp_facts a (dupTree (occ0 (comp b K n).occ)) (comp b K n).next
    have IHa := IHa' (dupTree (occ0 (comp b K n).occ)) (comp b K n).next S root pre
      ((comp b K n).bag.map (Redex.subst S) ++ post)
    have IHb := IHb' K n
      (merge S (many (occ0 (comp b K n).occ) (nul va))) root pre post
    simp only [comp] at h1 h2 hF ⊢
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    generalize comp b K n = rb at *
    generalize comp a (dupTree (occ0 rb.occ)) rb.next = ra at *
    have hos : ∀ o ∈ occ0 rb.occ, n ≤ o ∧ o < rb.next := fun o ho => b2 _ (mem_occ0.1 ho)
    have hshift : ∀ p ∈ shiftOcc rb.occ, ∀ o ∈ occ0 rb.occ, p.2 ≠ o := by
      intro p hp o ho heq
      have := nodup_name b3 (mem_shiftOcc.1 hp) (mem_occ0.1 ho) heq
      simp at this
    have hSos : ∀ o ∈ occ0 rb.occ, S o = none := by
      intro o ho
      have hr := hos o ho
      refine h2 o hr.1 (by omega) (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · have := a2 p hp; omega
      · exact hshift p hp o ho
    have hnd : (occ0 rb.occ).Nodup := b3.sublist (occ0_sublist _)
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHa (fun p hp => h1 p (List.mem_append_left _ hp)) ?_ hS
        (HTree.subst_id_of _ (fun v hv => hSos v (by rwa [dupTree_vars] at hv))) ?_).trans ?_)
    · intro o ho1 ho2 hno
      refine h2 o (by omega) ho2 (fun p hp => ?_)
      rcases List.mem_append.1 hp with hp | hp
      · exact hno p hp
      · have := b2 _ (mem_shiftOcc.1 hp); simp only at this; omega
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · simp only [bagVars_append, List.mem_append] at hv
        rcases hv with hv | hv
        · rcases b4 v (bagVars_map_subst hS _ v hv) with h | h
          · omega
          · have := Fk v h; omega
        · have := Fq v hv; omega
      · rw [dupTree_vars] at hv; have := hos v hv; omega
    refine (sSpread (nul va) (nullary_nul _) (occ0 rb.occ) pre (rb.bag.map (Redex.subst S)) post
      hnd (fun o ho => ?_) rfl rfl).trans ?_
    · have := hos o ho
      exact ⟨fun h => by have := Fr o h; omega, fun h => by have := Fp o h; omega,
        fun h => by have := Fq o h; omega⟩
    rw [bag_subst_merge _ hS]
    refine IHb ?_ ?_ (closedImg_merge hS (closedImg_many (nul_vars _))) ?_ ?_
    · rintro ⟨i, o⟩ hp
      cases i with
      | zero =>
        have ho : o ∈ occ0 rb.occ := mem_occ0.2 hp
        simp [merge, hSos o ho, many, ho]
      | succ k =>
        have := h1 (k, o) (List.mem_append_right _ (mem_shiftOcc.2 hp))
        simp [merge, this]
    · intro o ho1 ho2 hno
      have hSo : S o = none := by
        refine h2 o ho1 (by omega) (fun p hp => ?_)
        rcases List.mem_append.1 hp with hp | hp
        · have := a2 p hp; omega
        · exact hno (p.1 + 1, p.2) (mem_shiftOcc.1 hp)
      have hmo : o ∉ occ0 rb.occ := fun h => hno _ (mem_occ0.1 h) rfl
      simp [merge, hSo, many, hmo]
    · rw [← HTree.subst_merge _ hS, hK]
      refine HTree.subst_id_of _ (fun v hv => ?_)
      have hv' : v ∉ occ0 rb.occ := fun h => by have := hos v h; have := Fk v hv; omega
      simp [many, hv']
    · refine fresh4_mk (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · have := Fr v hv; omega
      · have := Fp v hv; omega
      · have := Fq v hv; omega
      · have := Fk v hv; omega
  | .ifz v z s, ρ, val, hg, he => by
    obtain ⟨x, hxE⟩ : ∃ x, evalF D fuel ρ v = some x := by
      cases h : evalF D fuel ρ v with
      | none => simp [evalF, h] at he
      | some x => exact ⟨x, rfl⟩
    obtain ⟨vz, hzE⟩ : ∃ vz, evalF D fuel ρ z = some vz := by
      cases h : evalF D fuel ρ z with
      | none => simp [evalF, hxE, h] at he
      | some x => exact ⟨x, rfl⟩
    obtain ⟨vs, hsE⟩ : ∃ vs, evalF D fuel (cons (predOf x) ρ) s = some vs := by
      cases h : evalF D fuel (cons (predOf x) ρ) s with
      | none => simp [evalF, hxE, hzE, h] at he
      | some x => exact ⟨x, rfl⟩
    simp only [evalF, hxE, hzE, hsE, Option.some.injEq] at he
    subst he
    have IHv' := comp_reduces_aux book D fuel hcall v ρ x hg.1 hxE
    have IHz' := comp_reduces_aux book D fuel hcall z ρ vz hg.2.1 hzE
    have IHs' := comp_reduces_aux book D fuel hcall s _ vs hg.2.2 hsE
    intro K n S root pre post h1 h2 hS hK hF
    obtain ⟨z1, z2, z3, z4⟩ := comp_facts z (.var n) (n + 2)
    obtain ⟨s1, s2, s3, s4⟩ := comp_facts s (.var (n + 1)) (comp z (.var n) (n + 2)).next
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v (.swi (.con (.var n) (.con (dupTree (occ0
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)) (.var (n + 1)))) K)
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next
    have IHv := IHv' (.swi (.con (.var n) (.con (dupTree (occ0
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ)) (.var (n + 1)))) K)
      (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next S root pre
      ((comp z (.var n) (n + 2)).bag.map (Redex.subst S) ++
        ((comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).bag.map (Redex.subst S) ++ post))
    have hz : ∀ T, (comp z (.var n) (n + 2)).bag.map (Redex.subst (one n T)) = (comp z T (n + 2)).bag := by
      intro T
      rw [comp_subst_K z _ _ _ (fun w h _ => one_none (by omega))]
      simp [HTree.subst, one]
    have hs : ∀ T, (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).bag.map
        (Redex.subst (one (n + 1) T)) = (comp s T (comp z (.var n) (n + 2)).next).bag := by
      intro T
      rw [comp_subst_K s _ _ _ (fun w h _ => one_none (by omega))]
      simp [HTree.subst, one]
    have iz : ∀ T, (comp z T (n + 2)).occ = (comp z (.var n) (n + 2)).occ ∧
        (comp z T (n + 2)).next = (comp z (.var n) (n + 2)).next := fun T => comp_indep z T _ _
    have is' : ∀ T, (comp s T (comp z (.var n) (n + 2)).next).occ =
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ ∧
        (comp s T (comp z (.var n) (n + 2)).next).next =
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next := fun T => comp_indep s T _ _
    have fz : ∀ T, ∀ w ∈ bagVars (comp z T (n + 2)).bag, (n + 2 ≤ w ∧ w < (comp z (.var n) (n + 2)).next) ∨
        w ∈ T.vars := by
      intro T w hw
      obtain ⟨-, -, -, h4⟩ := comp_facts z T (n + 2)
      rw [(iz T).2] at h4; exact h4 w hw
    have fs : ∀ T, ∀ w ∈ bagVars (comp s T (comp z (.var n) (n + 2)).next).bag,
        ((comp z (.var n) (n + 2)).next ≤ w ∧ w < (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next) ∨
        w ∈ T.vars := by
      intro T w hw
      obtain ⟨-, -, -, h4⟩ := comp_facts s T (comp z (.var n) (n + 2)).next
      rw [(is' T).2] at h4; exact h4 w hw
    have IHz : ∀ (T : HTree) (S' : Nat → Option HTree) (root' : HTree)
        (pre' post' : List Redex),
        (∀ p ∈ (comp z (.var n) (n + 2)).occ, S' p.2 = some (nul (ρ p.1))) →
        (∀ o, n + 2 ≤ o → o < (comp z (.var n) (n + 2)).next → (∀ p ∈ (comp z (.var n) (n + 2)).occ, p.2 ≠ o) →
          S' o = none) →
        ClosedImg S' → T.subst S' = T →
        (∀ w ∈ root'.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < n + 2 ∨ (comp z (.var n) (n + 2)).next ≤ w) →
        Steps book ⟨root', pre' ++ ((comp z T (n + 2)).bag.map (Redex.subst S') ++ post')⟩
          ⟨root', pre' ++ (nul vz, T) :: post'⟩ := by
      intro T S' root' pre' post'
      rw [← (iz T).1, ← (iz T).2]
      exact IHz' T (n + 2) S' root' pre' post'
    have IHs : ∀ (T : HTree) (S' : Nat → Option HTree) (root' : HTree)
        (pre' post' : List Redex),
        (∀ p ∈ (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ,
          S' p.2 = some (nul (cons (predOf x) ρ p.1))) →
        (∀ o, (comp z (.var n) (n + 2)).next ≤ o → o < (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next →
          (∀ p ∈ (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).occ, p.2 ≠ o) → S' o = none) →
        ClosedImg S' → T.subst S' = T →
        (∀ w ∈ root'.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < (comp z (.var n) (n + 2)).next ∨
          (comp s (.var (n + 1)) (comp z (.var n) (n + 2)).next).next ≤ w) →
        Steps book ⟨root', pre' ++ ((comp s T (comp z (.var n) (n + 2)).next).bag.map (Redex.subst S') ++ post')⟩
          ⟨root', pre' ++ (nul vs, T) :: post'⟩ := by
      intro T S' root' pre' post'
      rw [← (is' T).1, ← (is' T).2]
      exact IHs' T _ S' root' pre' post'
    simp only [comp] at h1 h2 hF ⊢
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    generalize comp z (.var n) (n + 2) = rz at *
    generalize comp s (.var (n + 1)) rz.next = rs at *
    generalize comp v (.swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K) rs.next = rv at *
    -- facts
    have hos : ∀ o ∈ occ0 rs.occ, rz.next ≤ o ∧ o < rs.next := fun o ho => s2 _ (mem_occ0.1 ho)
    have hnd : (occ0 rs.occ).Nodup := s3.sublist (occ0_sublist _)
    have notOcc : ∀ o, n ≤ o → o < rv.next → (∀ p ∈ rv.occ, p.2 ≠ o) → (∀ p ∈ rz.occ, p.2 ≠ o) →
        (∀ p ∈ rs.occ, p.2 ≠ o) → S o = none := by
      intro o h1o h2o hv hz' hs'
      refine h2 o h1o h2o (fun p hp => ?_)
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hv p hp
      · exact hz' p hp
      · exact hs' (p.1 + 1, p.2) (mem_shiftOcc.1 hp)
    have hSn : S n = none := notOcc n (Nat.le_refl _) (by omega)
      (fun p hp => by have := v2 p hp; omega) (fun p hp => by have := z2 p hp; omega)
      (fun p hp => by have := s2 p hp; omega)
    have hSn1 : S (n + 1) = none := notOcc (n + 1) (by omega) (by omega)
      (fun p hp => by have := v2 p hp; omega) (fun p hp => by have := z2 p hp; omega)
      (fun p hp => by have := s2 p hp; omega)
    have hSos : ∀ o ∈ occ0 rs.occ, S o = none := by
      intro o ho
      have := hos o ho
      refine h2 o (by omega) (by omega) (fun p hp => ?_)
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · have := v2 p hp; omega
      · have := z2 p hp; omega
      · intro heq
        have := nodup_name s3 (mem_shiftOcc.1 hp) (mem_occ0.1 ho) heq
        simp at this
    have sH1 : ∀ x : Option Nat, ∀ p ∈ rs.occ,
        merge S (many (occ0 rs.occ) (nul x)) p.2 = some (nul (cons x ρ p.1)) := by
      rintro x ⟨i, o⟩ hp
      cases i with
      | zero =>
        have ho : o ∈ occ0 rs.occ := mem_occ0.2 hp
        simp [merge, hSos o ho, many, ho]
      | succ k =>
        have := h1 (k, o) (List.mem_append_right _ (mem_shiftOcc.2 hp))
        simp [merge, this]
    have sH2 : ∀ N, ∀ o, rz.next ≤ o → o < rs.next → (∀ p ∈ rs.occ, p.2 ≠ o) →
        merge S (many (occ0 rs.occ) N) o = none := by
      intro N o ho1 ho2 hno
      have hSo : S o = none := notOcc o (by omega) (by omega) (fun p hp => by have := v2 p hp; omega)
        (fun p hp => by have := z2 p hp; omega) hno
      have hmo : o ∉ occ0 rs.occ := fun h => hno _ (mem_occ0.1 h) rfl
      simp [merge, hSo, many, hmo]
    have zH2 : ∀ o, n + 2 ≤ o → o < rz.next → (∀ p ∈ rz.occ, p.2 ≠ o) → S o = none := by
      intro o ho1 ho2 hno
      exact notOcc o (by omega) (by omega) (fun p hp => by have := v2 p hp; omega) hno
        (fun p hp => by have := s2 p hp; omega)
    have hKos : ∀ N, K.subst (many (occ0 rs.occ) N) = K := fun N => HTree.subst_id_of _ (fun w hw => by
      have hw' : w ∉ occ0 rs.occ := fun h => by have := hos w h; have := Fk w hw; omega
      simp [many, hw'])
    have hKS1 : ∀ N, K.subst (merge S (many (occ0 rs.occ) N)) = K := fun N => by
      rw [← HTree.subst_merge _ hS, hK, hKos]
    have hS1 : ∀ x : Option Nat, ClosedImg (merge S (many (occ0 rs.occ) (nul x))) :=
      fun x => closedImg_merge hS (closedImg_many (nul_vars _))
    have hS1n1 : ∀ N, merge S (many (occ0 rs.occ) N) (n + 1) = none := fun N => by
      have : n + 1 ∉ occ0 rs.occ := fun h => by have := hos _ h; omega
      simp [merge, hSn1, many, this]
    -- unchanged pieces
    have keepZ : ∀ T (U : Nat → Option HTree), (∀ w, (n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ T.vars → U w = none) →
        ((comp z T (n + 2)).bag.map (Redex.subst S)).map (Redex.subst U) =
          (comp z T (n + 2)).bag.map (Redex.subst S) := fun T U hU =>
      bag_subst_id _ (fun w hw => hU w (fz T w (bagVars_map_subst hS _ w hw)))
    have keepS : ∀ U : Nat → Option HTree, (∀ w, (rz.next ≤ w ∧ w < rs.next) ∨ w = n + 1 → U w = none) →
        (rs.bag.map (Redex.subst S)).map (Redex.subst U) = rs.bag.map (Redex.subst S) := by
      intro U hU
      refine bag_subst_id _ (fun w hw => hU w ?_)
      rcases s4 w (bagVars_map_subst hS _ w hw) with h | h
      · exact .inl h
      · simp only [HTree.vars, List.mem_singleton] at h; exact .inr h
    have many_none : ∀ N w, w ∉ occ0 rs.occ → many (occ0 rs.occ) N w = none := fun N w h => by
      simp [many, h]
    have nFr : ∀ w, n ≤ w → w < rv.next → w ∉ root.vars := fun w h1 h2 h => by have := Fr w h; omega
    have nFp : ∀ w, n ≤ w → w < rv.next → w ∉ bagVars pre := fun w h1 h2 h => by have := Fp w h; omega
    have nFq : ∀ w, n ≤ w → w < rv.next → w ∉ bagVars post := fun w h1 h2 h => by have := Fq w h; omega
    have nFk : ∀ w, n ≤ w → w < rv.next → w ∉ K.vars := fun w h1 h2 h => by have := Fk w h; omega
    have spreadFresh : ∀ o ∈ occ0 rs.occ, o ∉ root.vars ∧ o ∉ bagVars pre ∧ o ∉ bagVars post := fun o ho => by
      have := hos o ho
      exact ⟨nFr o (by omega) (by omega), nFp o (by omega) (by omega), nFq o (by omega) (by omega)⟩
    have Pfix : (HTree.con (dupTree (occ0 rs.occ)) (.var (n + 1))).subst (one n K) =
        .con (dupTree (occ0 rs.occ)) (.var (n + 1)) := by
      refine HTree.subst_id_of _ (fun w hw => one_none ?_)
      simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have := hos w hw; omega
      · omega
    have Pfix' : ∀ T, (HTree.con (dupTree (occ0 rs.occ)) (.var (n + 1))).subst (one n T) =
        .con (dupTree (occ0 rs.occ)) (.var (n + 1)) := by
      intro T
      refine HTree.subst_id_of _ (fun w hw => one_none ?_)
      simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have := hos w hw; omega
      · omega
    have Rfix : ∀ T, Redex.subst (one n T) (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) =
        (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) := fun T => by
      simp only [Redex.subst, Pfix' T]; rfl
    have KfixN : ∀ T, K.subst (one n T) = K := fun T =>
      HTree.subst_id_of _ (fun w hw => one_none (fun h => nFk w (by omega) (by omega) (h ▸ hw)))
    have Kfix1 : ∀ T, K.subst (one (n + 1) T) = K := fun T =>
      HTree.subst_id_of _ (fun w hw => one_none (fun h => nFk w (by omega) (by omega) (h ▸ hw)))
    have zfresh : ∀ T, T.vars = [] ∨ T = K → ∀ (pre' post' : List Redex),
        (∀ w ∈ bagVars pre', w < n + 2 ∨ rz.next ≤ w) → (∀ w ∈ bagVars post', w < n + 2 ∨ rz.next ≤ w) →
        ∀ w ∈ root.vars ++ bagVars pre' ++ bagVars post' ++ T.vars, w < n + 2 ∨ rz.next ≤ w := by
      intro T hT pre' post' hp hq
      refine fresh4_mk (fun w hw => ?_) hp hq (fun w hw => ?_)
      · have := Fr w hw; omega
      · rcases hT with hT | rfl
        · simp [hT] at hw
        · have := Fk w hw; omega
    -- the condition first
    refine (steps_eq (by simp [List.map_append, List.append_assoc])).trans
      ((IHv (fun p hp => h1 p (List.mem_append_left _ (List.mem_append_left _ hp))) ?_ hS ?_ ?_).trans ?_)
    · intro o ho1 ho2 hno
      exact notOcc o (by omega) ho2 hno (fun p hp => by have := z2 p hp; omega)
        (fun p hp => by have := s2 p hp; omega)
    · have hd : (dupTree (occ0 rs.occ)).subst S = dupTree (occ0 rs.occ) :=
        HTree.subst_id_of _ (fun w hw => hSos w (by rwa [dupTree_vars] at hw))
      simp [HTree.subst, hSn, hSn1, hd, hK]
    · refine fresh4_mk (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_)
      · have := Fr w hw; omega
      · have := Fp w hw; omega
      · simp only [bagVars_append, List.mem_append] at hw
        rcases hw with hw | hw | hw
        · rcases z4 w (bagVars_map_subst hS _ w hw) with h | h
          · omega
          · simp [HTree.vars] at h; omega
        · rcases s4 w (bagVars_map_subst hS _ w hw) with h | h
          · omega
          · simp [HTree.vars] at h; omega
        · have := Fq w hw; omega
      · simp only [HTree.vars, dupTree_vars, List.mem_append, List.mem_singleton, or_assoc] at hw
        rcases hw with hw | hw | hw | hw
        · omega
        · have := hos w hw; omega
        · omega
        · have := Fk w hw; omega
    have zH1 : ∀ p ∈ rz.occ, S p.2 = some (nul (ρ p.1)) :=
      fun p hp => h1 p (List.mem_append_left _ (List.mem_append_right _ hp))
    have sFresh : ∀ (T : HTree) (pre' : List Redex), (∀ w ∈ T.vars, w < rz.next ∨ rs.next ≤ w) →
        (∀ w ∈ bagVars pre', w < rz.next ∨ rs.next ≤ w) →
        ∀ w ∈ root.vars ++ bagVars pre' ++ bagVars post ++ T.vars, w < rz.next ∨ rs.next ≤ w := by
      intro T pre' hT hp
      refine fresh4_mk (fun w hw => ?_) hp (fun w hw => ?_) hT
      · have := Fr w hw; omega
      · have := Fq w hw; omega
    have preK : ∀ (N : HTree), N.vars = [] → ∀ w ∈ bagVars (pre ++ [(N, K)]), w < rz.next ∨ rs.next ≤ w := by
      intro N hN w hw
      simp only [bagVars_append, bagVars_cons, hN, bagVars_nil, List.append_nil, List.nil_append,
        List.mem_append] at hw
      rcases hw with hw | hw
      · have := Fp w hw; omega
      · have := Fk w hw; omega
    have seFresh : ∀ (T : HTree) (S' : Nat → Option HTree), ClosedImg S' → T.vars = [] →
        ∀ w ∈ bagVars ((comp s T rz.next).bag.map (Redex.subst S') ++ post), w < n + 2 ∨ rz.next ≤ w := by
      intro T S' hS' hT w hw
      simp only [bagVars_append, List.mem_append] at hw
      rcases hw with hw | hw
      · rcases fs T w (bagVars_map_subst hS' _ w hw) with h | h
        · omega
        · simp [hT] at h
      · have := Fq w hw; omega
    have pFresh : ∀ w ∈ bagVars pre, w < n + 2 ∨ rz.next ≤ w := fun w hw => by have := Fp w hw; omega
    have osNot : ∀ w, ((n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ K.vars) → w ∉ occ0 rs.occ := by
      intro w hw ho
      have := hos w ho
      rcases hw with hw | hw
      · omega
      · exact nFk w (by omega) (by omega) hw
    have osNot' : ∀ w, ((n + 2 ≤ w ∧ w < rz.next) ∨ w ∈ (nul none).vars) → w ∉ occ0 rs.occ := by
      intro w hw ho
      have := hos w ho
      rcases hw with hw | hw
      · omega
      · simp [nul, HTree.vars] at hw
    have n1os : n + 1 ∉ occ0 rs.occ := fun h => by have := hos _ h; omega
    cases x with
    | some k =>
      cases k with
      | zero =>
        simp only [selectZ]
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .num (.u24 0)) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
          (ns := [(.con K .era, .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))])
          rfl (by simp [nul]) rfl).trans ?_
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con K .era) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
          (ns := [(K, .var n), (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))]) rfl (by simp) rfl).trans ?_
        refine (sLinkR pre ((.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) ::
          (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n K
          (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
          (by simp) rfl).trans ?_
        rw [List.map_cons, List.map_append, bag_subst_comm_one hS hSn hK, hz,
          keepS _ (fun w hw => one_none (by omega)), Rfix]
        refine (sRule pre ((comp z K (n + 2)).bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .era) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
          (ns := [(.era, dupTree (occ0 rs.occ)), (.era, .var (n + 1))]) rfl (by simp) rfl).trans ?_
        refine (sSpread (nul none) (nullary_nul none) (occ0 rs.occ) pre ((.era, .var (n + 1)) ::
          ((comp z K (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
          (by simp [nul]) rfl).trans ?_
        rw [List.map_cons, List.map_append, keepZ K _ (fun w hw => many_none _ _ (osNot w hw)),
          bag_subst_merge _ hS]
        simp only [Redex.subst, HTree.subst, many_none _ _ n1os, Option.getD_none]
        refine (sLinkR pre ((comp z K (n + 2)).bag.map (Redex.subst S) ++
          rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul none))))) post (n + 1) (nul none)
          (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
          (by simp [nul]) rfl).trans ?_
        rw [List.map_append, keepZ K _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · exact fun h => nFk w (by omega) (by omega) (h ▸ hw))),
          bag_subst_comm_one (hS1 none) (hS1n1 _) (nul_subst _ _), hs]
        rw [List.append_assoc]
        refine (IHz K S root pre _ zH1 zH2 hS hK
          (zfresh K (.inr rfl) pre _ pFresh (seFresh _ _ (hS1 none) (nul_vars none)))).trans ?_
        refine (steps_eq (by simp)).trans ((IHs (nul none) _ root (pre ++ [(nul vz, K)]) post
          (sH1 none) (sH2 _) (hS1 none) (nul_subst _ _)
          (sFresh _ _ (by simp) (preK _ (nul_vars _)))).trans ?_)
        exact sRule (pre ++ [(nul vz, K)]) post
          (localRule_void (nullary_nul (vs)) (nullary_nul none)) rfl (by simp)
      | succ k =>
        simp only [selectZ]
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .num (.u24 (k + 1))) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
          (ns := [(.con .era (.con (.num (.u24 k)) K), .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))])
          (by simp [localRule, Numb.payload]) (by simp [nul]) rfl).trans ?_
        refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con .era (.con (.num (.u24 k)) K)) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
          (ns := [(.era, .var n), (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))])
          rfl (by simp) rfl).trans ?_
        refine (sLinkR pre ((.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) ::
          (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n (nul none)
          (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
          (by simp [nul]) rfl).trans ?_
        have R2 : Redex.subst (one n (nul none)) (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) =
            (.con (.num (.u24 k)) K, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) := by
          simp only [Redex.subst, Pfix' (nul none)]
          simp only [HTree.subst, KfixN]
        rw [List.map_cons, List.map_append, bag_subst_comm_one hS hSn (nul_subst _ _), hz,
          keepS _ (fun w hw => one_none (by omega)), R2]
        refine (sRule pre ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
          (a := .con (.num (.u24 k)) K) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
          (ns := [(.num (.u24 k), dupTree (occ0 rs.occ)), (K, .var (n + 1))]) rfl (by simp) rfl).trans ?_
        refine (sSpread (nul (some k)) (nullary_nul _) (occ0 rs.occ) pre ((K, .var (n + 1)) ::
          ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
          (by simp [nul]) rfl).trans ?_
        have R3 : Redex.subst (many (occ0 rs.occ) (nul (some k))) (K, .var (n + 1)) = (K, .var (n + 1)) := by
          simp only [Redex.subst, hKos]
          simp [HTree.subst, many_none _ _ n1os]
        rw [List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => many_none _ _ (osNot' w hw)),
          bag_subst_merge _ hS, R3]
        refine (sLinkR pre ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
          rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul (some k)))))) post (n + 1) K
          (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
          (by simp) rfl).trans ?_
        rw [List.map_append, keepZ (nul none) _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · simp [nul, HTree.vars] at hw)),
          bag_subst_comm_one (hS1 (some k)) (hS1n1 _) (hKS1 _), hs]
        rw [List.append_assoc]
        refine (IHz (nul none) S root pre _ zH1 zH2 hS (nul_subst _ _)
          (zfresh (nul none) (.inl (nul_vars _)) pre _ pFresh ?_)).trans ?_
        · intro w hw
          simp only [bagVars_append, List.mem_append] at hw
          rcases hw with hw | hw
          · rcases fs K w (bagVars_map_subst (hS1 (some k)) _ w hw) with h | h
            · omega
            · have := Fk w h; omega
          · have := Fq w hw; omega
        refine (sRule pre ((comp s K rz.next).bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul (some k))))) ++ post)
          (localRule_void (nullary_nul vz) (nullary_nul none)) rfl rfl).trans ?_
        refine (steps_eq (by simp)).trans (IHs K _ root pre post
          (sH1 (some k)) (sH2 _) (hS1 (some k)) (hKS1 _) (sFresh _ _ (fun w hw => by have := Fk w hw; omega)
            (fun w hw => by have := Fp w hw; omega)))
    | none =>
      simp only [selectZ]
      refine (sRule pre (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post))
        (a := .era) (b := .swi (.con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))) K)
        (ns := [(.era, .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1)))), (.era, K)])
        rfl (by simp [nul]) rfl).trans ?_
      refine (sRule pre ((.era, K) :: (rz.bag.map (Redex.subst S) ++ (rs.bag.map (Redex.subst S) ++ post)))
        (a := .era) (b := .con (.var n) (.con (dupTree (occ0 rs.occ)) (.var (n + 1))))
        (ns := [(.era, .var n), (.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1)))]) rfl (by simp) rfl).trans ?_
      refine (sLinkR pre ((.era, .con (dupTree (occ0 rs.occ)) (.var (n + 1))) :: (.era, K) ::
        (rz.bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post n (nul none)
        (nFr n (Nat.le_refl _) (by omega)) (nFp n (Nat.le_refl _) (by omega)) (nFq n (Nat.le_refl _) (by omega))
        (by simp [nul]) rfl).trans ?_
      have R4 : Redex.subst (one n (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, KfixN]; rfl
      rw [List.map_cons, List.map_cons, List.map_append, bag_subst_comm_one hS hSn (nul_subst _ _), hz,
        keepS _ (fun w hw => one_none (by omega)), Rfix, R4]
      refine (sRule pre ((.era, K) :: ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
          (rs.bag.map (Redex.subst S) ++ post)))
        (a := .era) (b := .con (dupTree (occ0 rs.occ)) (.var (n + 1)))
        (ns := [(.era, dupTree (occ0 rs.occ)), (.era, .var (n + 1))]) rfl (by simp) rfl).trans ?_
      refine (sSpread (nul none) (nullary_nul none) (occ0 rs.occ) pre ((.era, .var (n + 1)) :: (.era, K) ::
        ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++ rs.bag.map (Redex.subst S))) post hnd spreadFresh
        (by simp [nul]) rfl).trans ?_
      have R5 : Redex.subst (many (occ0 rs.occ) (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, hKos]; rfl
      have R6 : Redex.subst (many (occ0 rs.occ) (nul none)) (.era, .var (n + 1)) = (.era, .var (n + 1)) := by
        simp [Redex.subst, HTree.subst, many_none _ _ n1os]
      rw [List.map_cons, List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => many_none _ _ (osNot' w hw)),
        bag_subst_merge _ hS, R5, R6]
      refine (sLinkR pre ((.era, K) :: ((comp z (nul none) (n + 2)).bag.map (Redex.subst S) ++
        rs.bag.map (Redex.subst (merge S (many (occ0 rs.occ) (nul none)))))) post (n + 1) (nul none)
        (nFr _ (by omega) (by omega)) (nFp _ (by omega) (by omega)) (nFq _ (by omega) (by omega))
        (by simp [nul]) rfl).trans ?_
      have R7 : Redex.subst (one (n + 1) (nul none)) (.era, K) = (.era, K) := by
        simp only [Redex.subst, Kfix1]; rfl
      rw [List.map_cons, List.map_append, keepZ (nul none) _ (fun w hw => one_none (by
            rcases hw with hw | hw
            · omega
            · simp [nul, HTree.vars] at hw)),
        bag_subst_comm_one (hS1 none) (hS1n1 _) (nul_subst _ _), hs, R7]
      refine (steps_eq (by simp)).trans ((IHz (nul none) S root (pre ++ [(.era, K)]) _ zH1 zH2 hS (nul_subst _ _)
          (zfresh (nul none) (.inl (nul_vars _)) _ _ ?_ (seFresh _ _ (hS1 none) (nul_vars none)))).trans ?_)
      · intro w hw
        simp only [bagVars_append, bagVars_cons, HTree.vars, bagVars_nil, List.append_nil, List.nil_append,
          List.mem_append] at hw
        rcases hw with hw | hw
        · have := Fp w hw; omega
        · have := Fk w hw; omega
      refine (sRule (pre ++ [(.era, K)]) ((comp s (nul none) rz.next).bag.map
          (Redex.subst (merge S (many (occ0 rs.occ) (nul none)))) ++ post)
        (localRule_void (nullary_nul vz) (nullary_nul none)) rfl rfl).trans ?_
      refine (steps_eq (by simp)).trans ((IHs (nul none) _ root (pre ++ [(.era, K)]) post
        (sH1 none) (sH2 _) (hS1 none) (nul_subst _ _) (sFresh _ _ (by simp) (preK .era rfl))).trans ?_)
      exact sRule (pre ++ [(.era, K)]) post
        (localRule_void (nullary_nul (vs)) (nullary_nul none)) rfl (by simp [nul])
  | .ifzL d nz ns v z s, ρ, val, hg, he => by
    obtain ⟨hgv, hgz, hgs, hbz, hokz, hbs, hoks⟩ := hg
    have hd : d ≠ 0 := by intro h; simp [evalF, h] at he
    obtain ⟨x, hxE⟩ : ∃ x, evalF D fuel ρ v = some x := by
      cases h : evalF D fuel ρ v with
      | none => simp [evalF, hd, h] at he
      | some x => exact ⟨x, rfl⟩
    have IHv' := comp_reduces_aux book D fuel hcall v ρ x hgv hxE
    intro K n S root pre post h1 h2 hS hK hF
    obtain ⟨v1, v2, v3, v4⟩ := comp_facts v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    simp only [comp] at h1 h2 hF ⊢
    obtain ⟨Fr, Fp, Fq, Fk⟩ := fresh4 hF
    -- the argument occurrences first, then the condition
    let Sa : Nat → Option HTree := fun o => if n ≤ o ∧ o < n + d then S o else none
    have hSa : ClosedImg Sa := fun m T h => by
      simp only [Sa] at h; split at h
      · exact hS m T h
      · cases h
    have hmerge : merge Sa S = S := by
      funext o; simp only [merge, Sa]; split
      · cases S o <;> rfl
      · rfl
    have hargs : ∀ p ∈ argOcc (revRange d) n, S p.2 = some (nul (ρ p.1)) :=
      fun p hp => h1 p (List.mem_append_right _ hp)
    have hKa : K.subst Sa = K := HTree.subst_id_of _ (fun w hw => by
      simp only [Sa]; rw [if_neg (by have := Fk w hw; omega)])
    have hsplit := comp_subst_K v (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d) Sa
      (fun w hw1 _ => by simp only [Sa]; rw [if_neg (by omega)])
    have eKv : (HTree.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)).subst Sa =
        .swi (.con (.ref nz) (.ref ns)) (argTree (((revRange d).map ρ).map nul) K) := by
      simp only [HTree.subst]
      rw [argChain_S Sa ρ K (revRange d) n (fun p hp => by
        have := argOcc_mem hp; simp only [revRange_length] at this
        simp only [Sa]; rw [if_pos this]; exact hargs p hp), hKa]
    rw [eKv] at hsplit
    rw [← hmerge, ← bag_subst_merge _ hSa, hsplit]
    obtain ⟨i1, i2⟩ := comp_indep v (.swi (.con (.ref nz) (.ref ns)) (argTree (((revRange d).map ρ).map nul) K))
      (.swi (.con (.ref nz) (.ref ns)) (argChain (revRange d) n K)) (n + d)
    have hNs : ∀ N ∈ ((revRange d).map ρ).map nul, Nullary N := nullary_map_nul _
    have hAT : (argTree (((revRange d).map ρ).map nul) K).subst S = argTree (((revRange d).map ρ).map nul) K := by
      refine HTree.subst_id_of _ (fun w hw => ?_)
      have := argTree_vars (fun N hN => (hNs N hN).vars) hw
      exact HTree.vars_subst_dom hS K w (by rw [hK]; exact this)
    refine (IHv' _ (n + d) S root pre post (by rw [i1]; exact fun p hp => h1 p (List.mem_append_left _ hp))
      (by rw [i1, i2]; intro o ho1 ho2 hno; exact h2 o (by omega) ho2 (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hno p hp
        · have := argOcc_mem hp; simp only [revRange_length] at this; omega))
      hS (by simp only [HTree.subst, hAT]) (by
        rw [i2]
        refine fresh4_mk (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_) (fun w hw => ?_)
        · have := Fr w hw; omega
        · have := Fp w hw; omega
        · have := Fq w hw; omega
        · simp only [HTree.vars, List.nil_append] at hw
          have := Fk w (argTree_vars (fun N hN => (hNs N hN).vars) hw); omega)).trans ?_
    have hlen : (revRange d).length = ((revRange d).map ρ).length := by simp
    cases x with
    | none =>
      simp only [evalF, hd, hxE, ite_false, Option.some.injEq] at he
      subst he
      refine (sRule pre post (a := nul none) (b := .swi (.con (.ref nz) (.ref ns)) (argTree (((revRange d).map ρ).map nul) K))
        (ns := [(.era, .con (.ref nz) (.ref ns)), (.era, argTree (((revRange d).map ρ).map nul) K)]) rfl rfl rfl).trans ?_
      refine (sRule pre ((.era, argTree (((revRange d).map ρ).map nul) K) :: post) (a := .era)
        (b := .con (.ref nz) (.ref ns)) (ns := [(.era, .ref nz), (.era, .ref ns)]) rfl (by simp) rfl).trans ?_
      refine (sRule pre ((.era, .ref ns) :: (.era, argTree (((revRange d).map ρ).map nul) K) :: post) (a := .era)
        (b := .ref nz) (ns := []) rfl (by simp) rfl).trans ?_
      refine (sRule pre ((.era, argTree (((revRange d).map ρ).map nul) K) :: post) (a := .era)
        (b := .ref ns) (ns := []) rfl (by simp) rfl).trans ?_
      exact (steps_eq (by simp)).trans (sEraseArgs pre post _ hNs)
    | some k =>
      cases k with
      | zero =>
        simp only [evalF, hd, hxE, ite_false] at he
        have IHz' := comp_reduces_aux book D fuel hcall z (restrict d ρ) val hgz he
        refine (sRule pre post (a := nul (some 0)) (b := .swi (.con (.ref nz) (.ref ns)) (argTree (((revRange d).map ρ).map nul) K))
          (ns := [(.con (argTree (((revRange d).map ρ).map nul) K) .era, .con (.ref nz) (.ref ns))]) rfl rfl rfl).trans ?_
        refine (sRule pre post (a := .con (argTree (((revRange d).map ρ).map nul) K) .era) (b := .con (.ref nz) (.ref ns))
          (ns := [(argTree (((revRange d).map ρ).map nul) K, .ref nz), (.era, .ref ns)]) rfl (by simp) rfl).trans ?_
        refine (sRule (pre ++ [(argTree (((revRange d).map ρ).map nul) K, .ref nz)]) post (a := .era) (b := .ref ns)
          (ns := []) rfl (by simp) rfl).trans ?_
        refine (sSwap pre post (a := argTree (((revRange d).map ρ).map nul) K) (b := .ref nz) (by simp) rfl).trans ?_
        have := callDef book nz (revRange d) [z] ((revRange d).map ρ) [val] K root pre post hbz hokz hlen rfl
          (fun i f w hf hw => by
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hf hw
              subst hf hw; rw [bindEnv_revRange]; exact IHz'
            | succ i => simp at hf)
        simpa [tup] using this
      | succ k =>
        simp only [evalF, hd, hxE, ite_false] at he
        have IHs' := comp_reduces_aux book D fuel hcall s (cons (some k) (restrict d ρ)) val hgs he
        refine (sRule pre post (a := nul (some (k + 1)))
          (b := .swi (.con (.ref nz) (.ref ns)) (argTree (((revRange d).map ρ).map nul) K))
          (ns := [(.con .era (.con (.num (.u24 k)) (argTree (((revRange d).map ρ).map nul) K)), .con (.ref nz) (.ref ns))])
          (by simp [localRule, nul, Numb.payload]) rfl rfl).trans ?_
        refine (sRule pre post (a := .con .era (.con (.num (.u24 k)) (argTree (((revRange d).map ρ).map nul) K)))
          (b := .con (.ref nz) (.ref ns))
          (ns := [(.era, .ref nz), (.con (.num (.u24 k)) (argTree (((revRange d).map ρ).map nul) K), .ref ns)])
          rfl (by simp) rfl).trans ?_
        refine (sRule pre ((.con (.num (.u24 k)) (argTree (((revRange d).map ρ).map nul) K), .ref ns) :: post)
          (a := .era) (b := .ref nz) (ns := []) rfl (by simp) rfl).trans ?_
        refine (sSwap pre post (a := .con (.num (.u24 k)) (argTree (((revRange d).map ρ).map nul) K)) (b := .ref ns)
          (by simp) rfl).trans ?_
        have := callDef book ns (0 :: (revRange d).map (· + 1)) [s] (some k :: (revRange d).map ρ) [val] K root pre post
          hbs hoks (by simp) rfl
          (fun i f w hf hw => by
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hf hw
              subst hf hw; rw [bindEnv_succ ρ, bindEnv_revRange]; exact IHs'
            | succ i => simp at hf)
        simpa [tup, argTree, nul] using this
  | .call g idxs, ρ, v, _, he => hcall g idxs ρ v he

/-- **The net theorem.** In a book holding every definition of `D` and every lifted branch, an
expression whose value at some fuel is `v` reduces, under `Step`, to `nul v ~ K`. -/
theorem comp_reduces (book : List HDef) (D : List FDef) (hD : BookOk book D) : ∀ (fuel : Nat) (e : FExp)
    (ρ : Nat → Option Nat) (v : Option Nat), Good book e → evalF D fuel ρ e = some v → Reduces book e ρ v
  | 0 => comp_reduces_aux book D 0 (fun g idxs ρ v h => by simp [evalF] at h)
  | f + 1 => comp_reduces_aux book D (f + 1) (fun g idxs ρ v h => by
      simp only [evalF] at h
      cases hd : D.find? (·.name == g) with
      | none => simp [hd] at h
      | some d =>
        simp only [hd] at h
        split at h
        · rename_i hc
          obtain ⟨hbook, hok, hgood⟩ := hD g d hd
          have IH := comp_reduces book D hD f d.body _ v hgood h
          intro K n S root pre post h1 _ _ hK _
          simp only [comp] at h1 ⊢
          simp only [List.map_cons, List.map_nil, Redex.subst, HTree.subst, argChain_S S ρ K idxs n h1, hK,
            List.cons_append, List.nil_append]
          have := callDef book g d.params [d.body] (idxs.map ρ) [v] K root pre post hbook hok
            (by simp [hc.1]) rfl (fun i f w hf hw => by
              cases i with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hf hw
                subst hf hw; exact IH
              | succ i => simp at hf)
          simpa [tup] using this
        · cases h)

/-- `@main = r & @m ~ (#x₁ (… r))`, as a configuration. -/
def mainCfgOf (m : String) (ws : List (Option Nat)) : Cfg := ⟨.var 0, [(.ref m, argTree (ws.map nul) (.var 0))]⟩

/-- **A run from `@main`**: the root becomes the tuple of the definition's output values, and no redex
is left. -/
theorem main_reduces (book : List HDef) (m : String) (ps : List Nat) (fs : List FExp) (ws vs : List (Option Nat))
    (hb : book.find? (·.name == m) = some (defNet m ps fs)) (hok : DefOk ps fs)
    (hl : ps.length = ws.length) (hv : fs.length = vs.length)
    (hR : ∀ (i : Nat) f v, fs[i]? = some f → vs[i]? = some v → Reduces book f (bindEnv ps ws) v) :
    Steps book (mainCfgOf m ws) ⟨tup (vs.map nul), []⟩ := by
  have h := callDef book m ps fs ws vs (.var 0) (.var 0) [] [] hb hok hl hv hR
  refine (steps_eq (by simp [mainCfgOf])).trans (h.trans ?_)
  refine (sSwap [] [] (a := tup (vs.map nul)) (b := .var 0) rfl rfl).trans ?_
  have := Step.link (book := book) (root := .var 0) (pre := []) (post := []) (x := 0) (t := tup (vs.map nul))
  simp only [List.nil_append, List.map_nil, HTree.subst, one, if_pos rfl, Option.getD_some] at this
  exact Steps.single this
