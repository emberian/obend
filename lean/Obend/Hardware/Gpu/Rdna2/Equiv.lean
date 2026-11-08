/-
# Obend.Hardware.Gpu.Rdna2.Equiv — is the stored term the specified one?

Translation validation at the granularity of a stored dword (Necula, "Translation Validation for an
Optimizing Compiler", PLDI 2000; Alive2, Lopes et al., PLDI 2021, for the shape of the obligation):
the term the symbolic run stores and the term `Lower` specifies are compared after their common subterms
are made one object (`ShareCommon.shareCommon'`). Where they are the same term, they are equal. Where the
compiler rewrote (a `select` folded into an add, a negation moved across a compare), the two sides are
cut at their maximal common subterms and at memory words (cutpoints, as in combinational equivalence
checking: Kuehlmann and Krohm, DAC 1997), which leaves a small `Residual` over cut variables; each
distinct residual is a separate lemma, discharged by `bv_decide` in a generated module, and the check
accepts a store only if its residual is one of them. `residual_sound`: a pair whose residual is trivial
or holds evaluates equally for every memory. What is cut is chosen by an unverified search; the abstraction that uses the choice is
verified, so a bad choice can only refuse, never accept.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Term
public import Std.Data.HashSet
import all Init.ShareCommon
@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2
namespace Tm

/-! ## 1. Structural equality, fast on shared objects (`decEqT`, in `Term`) -/


instance : Hashable Tm := ⟨hsh⟩

/-! ## 2. Cutting at leaves -/

/-- Every node of a term, once (the subterms of the specification side). -/
partial def collect (t : Tm) (seen : Std.HashSet Tm) : Std.HashSet Tm :=
  if seen.contains t then seen else t.args.foldl (fun s a => collect a s) (seen.insert t)

/-- The leaves both sides are cut at, in first-occurrence order: memory words, and the maximal subterms
of one side that occur in the other, never a literal or a 0/1 term. An unverified search: soundness never depends on it. -/
partial def findLeaves (other : Std.HashSet Tm) (t : Tm) (acc : Array Tm × Std.HashSet Tm) : Array Tm × Std.HashSet Tm :=
  if acc.2.contains t then acc
  else
    let acc := (acc.1, acc.2.insert t)
    -- a literal is never cut: its value is what the residual needs
    if (match t.op with | .lit _ => true | _ => false) then acc
    -- nor a 0/1 term (a carry, a compare): as a free 32-bit leaf it would take values it never has, so
    -- the cut descends to its operands
    else if (other.contains t && !isBool t) || (match t.op with | .var _ => true | _ => false) then
      if acc.1.contains t then acc else (acc.1.push t, acc.2)
    else t.args.foldl (fun a c => findLeaves other c a) acc

/-- The environment of leaf variables: leaf `k` is what `leaves[k]` evaluates to. -/
def leafEnv (env : UInt64 → UInt32) (leaves : Array Tm) : UInt64 → UInt32 :=
  fun k => eval env (leaves.getD k.toNat (lit 0))

/-- A memo table of results that evaluate as their keys do (under `ρ` and `env`). -/
def MemoOk (ρ env : UInt64 → UInt32) (memo : Std.HashMap Tm Tm) : Prop :=
  ∀ t r, memo[t]? = some r → eval ρ r = eval env t

theorem MemoOk.empty (ρ env : UInt64 → UInt32) : MemoOk ρ env {} := by
  intro t r h; simp at h

theorem MemoOk.insert {ρ env : UInt64 → UInt32} {memo : Std.HashMap Tm Tm} (hm : MemoOk ρ env memo) (t r : Tm)
    (h : eval ρ r = eval env t) : MemoOk ρ env (memo.insert t r) := by
  intro t' r' h'
  rw [Std.HashMap.getElem?_insert] at h'
  split at h'
  · rename_i heq; have := eq_of_beq heq; subst this; simp at h'; subst h'; exact h
  · exact hm t' r' h'

/-- The term over leaf variables (`var k` for `leaves[k]`), memoized over shared subterms, within a depth
budget; `none` when a memory word is not a leaf or the budget runs out. -/
def absM (leaves : Array Tm) : Nat → Tm → Std.HashMap Tm Tm → Option (Tm × Std.HashMap Tm Tm)
  | 0, _, _ => none
  | fuel + 1, t, memo =>
    match memo[t]? with
    | some r => some (r, memo)
    | none =>
      match leaves.findIdx? (· == t) with
      | some k => if k < 2 ^ 32 then some (var k.toUInt64, memo.insert t (var k.toUInt64)) else none
      | none =>
        if t.op.pure then
          (t.args.foldlM (fun (acc : List Tm × Std.HashMap Tm Tm) a =>
              (absM leaves fuel a acc.2).map fun (r, m) => (acc.1 ++ [r], m)) ([], memo)).map
            fun (rs, m) => let r := node t.op rs; (r, m.insert t r)
        else none

theorem leaf_sound (env : UInt64 → UInt32) (leaves : Array Tm) (t : Tm) (k : Nat)
    (hk : leaves.findIdx? (· == t) = some k) (h32 : k < 2 ^ 32) :
    eval (leafEnv env leaves) (var k.toUInt64) = eval env t := by
  rw [Array.findIdx?_eq_some_iff_getElem] at hk
  obtain ⟨hlt, heq, _⟩ := hk
  have : leaves[k] = t := eq_of_beq heq
  simp only [eval_var, leafEnv]
  have hk64 : (k.toUInt64).toNat = k := by rw [Nat.toUInt64_eq]; simp [UInt64.toNat_ofNat']; omega
  rw [hk64, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  simp [this]

theorem absM_sound (env : UInt64 → UInt32) (leaves : Array Tm) :
    ∀ (fuel : Nat) (t : Tm) (memo : Std.HashMap Tm Tm) (r : Tm) (memo' : Std.HashMap Tm Tm),
      MemoOk (leafEnv env leaves) env memo → absM leaves fuel t memo = some (r, memo') →
      eval (leafEnv env leaves) r = eval env t ∧ MemoOk (leafEnv env leaves) env memo'
  | 0, _, _, _, _, _, h => by simp [absM] at h
  | fuel + 1, mk h0 o as, memo, r, memo', hm, h => by
    unfold absM at h
    split at h
    · rename_i r0 hr0
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm _ _ hr0, hm⟩
    · split at h
      · rename_i k hk
        split at h
        · rename_i h32
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          have e := leaf_sound env leaves _ k hk h32
          exact ⟨e, hm.insert _ _ e⟩
        · simp at h
      · split at h
        · rename_i hp
          simp only [op] at hp
          simp only [args, Option.map_eq_some_iff] at h
          obtain ⟨⟨rs, m⟩, hfold, hres⟩ := h
          simp only [Prod.mk.injEq] at hres; obtain ⟨rfl, rfl⟩ := hres
          -- the fold: every argument abstracted soundly, the memo kept sound
          have key : ∀ (xs : List Tm) (acc : List Tm × Std.HashMap Tm Tm) (out : List Tm × Std.HashMap Tm Tm),
              MemoOk (leafEnv env leaves) env acc.2 →
              xs.foldlM (fun (acc : List Tm × Std.HashMap Tm Tm) a =>
                (absM leaves fuel a acc.2).map fun (r, m) => (acc.1 ++ [r], m)) acc = some out →
              out.1.map (eval (leafEnv env leaves)) = acc.1.map (eval (leafEnv env leaves)) ++ xs.map (eval env) ∧
                MemoOk (leafEnv env leaves) env out.2 := by
            intro xs
            induction xs with
            | nil => intro acc out hacc hf; simp at hf; subst hf; simpa using hacc
            | cons x xs ih =>
              intro acc out hacc hf
              rw [List.foldlM_cons] at hf
              cases h1 : absM leaves fuel x acc.2 with
              | none => simp [h1] at hf
              | some p =>
              obtain ⟨r1, m1⟩ := p
              simp only [h1, Option.map_some] at hf
              obtain ⟨e1, hm1⟩ := absM_sound env leaves fuel x acc.2 r1 m1 hacc h1
              obtain ⟨e2, hm2⟩ := ih _ out hm1 hf
              refine ⟨?_, hm2⟩
              rw [e2]; simp [e1]
          obtain ⟨e, hmr⟩ := key as ([], memo) (rs, m) hm hfold
          simp only [List.map_nil, List.nil_append] at e
          have ev : eval (leafEnv env leaves) (node o rs) = eval env (mk h0 o as) := by
            rw [eval_node, eval_mk, sem_pure (leafEnv env leaves) env o hp, e]
          exact ⟨ev, hmr.insert _ _ ev⟩
        · simp at h

/-! ## 3. Rebuilding through the smart constructors -/

def argT (as : List Tm) (i : Nat) : Tm := as.getD i (lit 0)

/-- An operation applied by its smart constructor (folding, ordering commutative operands by hash). -/
def smartNode (o : TOp) (as : List Tm) : Tm :=
  match o with
  | .lit v => lit v
  | .var a => var a
  | .sum => mkSum as
  | .tsum => mkSum as
  | .sub => mkSub (argT as 0) (argT as 1)
  | .mul => mkMul (argT as 0) (argT as 1)
  | .mulHi => mkMulHi (argT as 0) (argT as 1)
  | .band => mkAnd (argT as 0) (argT as 1)
  | .bor => mkOr (argT as 0) (argT as 1)
  | .shl => mkShl (argT as 0) (argT as 1)
  | .lshr => mkLshr (argT as 0) (argT as 1)
  | .ite => mkIte (argT as 0) (argT as 1) (argT as 2)
  | .carry => mkCarry (argT as 0) (argT as 1)
  | .borrow => mkBorrow (argT as 0) (argT as 1)
  | .addc => mkAddc (argT as 0) (argT as 1) (argT as 2)
  | .carryc => mkCarryc (argT as 0) (argT as 1) (argT as 2)
  | .subc => mkSubc (argT as 0) (argT as 1) (argT as 2)
  | .borrowc => mkBorrowc (argT as 0) (argT as 1) (argT as 2)
  | .ule => mkUle (argT as 0) (argT as 1)
  | .ugt => mkUgt (argT as 0) (argT as 1)
  | .ult64 => mkUlt64 (argT as 0) (argT as 1) (argT as 2) (argT as 3)
  | .ne64 => mkNe64 (argT as 0) (argT as 1) (argT as 2) (argT as 3)
  | .bit k => mkBitF 8 (argT as 0) k
  | .pack => mkPack as
  | .shl64lo => (mkShl64 (argT as 0) (argT as 1) (argT as 2)).1
  | .shl64hi => (mkShl64 (argT as 0) (argT as 1) (argT as 2)).2
  | .lshr64lo => (mkLshr64 (argT as 0) (argT as 1) (argT as 2)).1
  | .lshr64hi => (mkLshr64 (argT as 0) (argT as 1) (argT as 2)).2
  | .nez64 => mkNez64 (argT as 0) (argT as 1)

theorem eval_argT (env : UInt64 → UInt32) (as : List Tm) (i : Nat) :
    eval env (argT as i) = (as.map (eval env)).getD i 0 := by
  unfold argT
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases as[i]? <;> simp

theorem eval_smartNode (env : UInt64 → UInt32) (o : TOp) (as : List Tm) :
    eval env (smartNode o as) = o.sem env (as.map (eval env)) := by
  have hs := eval_shl64 env (argT as 0) (argT as 1) (argT as 2)
  have hr := eval_lshr64 env (argT as 0) (argT as 1) (argT as 2)
  cases o <;> simp only [smartNode, TOp.sem, eval_lit, eval_var]
  case sum => rw [eval_mkSum]
  case tsum => rw [eval_mkSum]
  case sub => exact eval_sub env _ _ |>.trans (by simp [Dom.sub, eval_argT])
  case mul => exact (eval_mul env _ _).trans (by simp [Dom.mul, mulLo, eval_argT])
  case mulHi => exact (eval_mulHi env _ _).trans (by simp [Dom.mulHi, mulHi_eq, eval_argT])
  case band => exact (eval_and env _ _).trans (by simp [Dom.band, eval_argT])
  case bor => exact (eval_or env _ _).trans (by simp [Dom.bor, eval_argT])
  case shl => exact (eval_shl env _ _).trans (by simp [Dom.shl, eval_argT])
  case lshr => exact (eval_lshr env _ _).trans (by simp [eval_argT])
  case ite => exact (eval_ite env _ _ _).trans (by simp [Dom.ite, w2b, eval_argT])
  case carry => exact (eval_carry env _ _).trans (by simp [Dom.carry, carry_eq, eval_argT])
  case borrow => exact (eval_borrow env _ _).trans (by simp [Dom.borrow, borrow_eq, eval_argT])
  case addc => exact (eval_addc env _ _ _).trans (by simp [Dom.addc, addCi, w2b, eval_argT])
  case carryc => exact (eval_carryc env _ _ _).trans (by simp [Dom.carryc, carryc_eq, eval_argT])
  case subc => exact (eval_subc env _ _ _).trans (by simp [Dom.subc, subCi, w2b, eval_argT])
  case borrowc => exact (eval_borrowc env _ _ _).trans (by simp [Dom.borrowc, borrowc_eq, eval_argT])
  case ule => exact (eval_ule env _ _).trans (by simp [Dom.ule, eval_argT])
  case ugt => exact (eval_ugt env _ _).trans (by simp [Dom.ugt, eval_argT])
  case ult64 => exact (eval_ult64 env _ _ _ _).trans (by simp [Dom.ult64, eval_argT])
  case ne64 => exact (eval_ne64 env _ _ _ _).trans (by simp [Dom.ne64, eval_argT])
  case bit => exact (eval_bit env _ _).trans (by simp [Dom.bit, eval_argT])
  case pack => exact (eval_pack env _).trans (by simp [Dom.pack])
  case shl64lo => rw [show (mkShl64 (argT as 0) (argT as 1) (argT as 2)) = Dom.shl64 _ _ _ from rfl];
                  exact (congrArg Prod.fst hs).trans (by simp [Dom.shl64, eval_argT])
  case shl64hi => rw [show (mkShl64 (argT as 0) (argT as 1) (argT as 2)) = Dom.shl64 _ _ _ from rfl];
                  exact (congrArg Prod.snd hs).trans (by simp [Dom.shl64, eval_argT])
  case lshr64lo => rw [show (mkLshr64 (argT as 0) (argT as 1) (argT as 2)) = Dom.lshr64 _ _ _ from rfl];
                   exact (congrArg Prod.fst hr).trans (by simp [Dom.lshr64, eval_argT])
  case lshr64hi => rw [show (mkLshr64 (argT as 0) (argT as 1) (argT as 2)) = Dom.lshr64 _ _ _ from rfl];
                   exact (congrArg Prod.snd hr).trans (by simp [Dom.lshr64, eval_argT])
  case nez64 => exact (eval_nez64 env _ _).trans (by simp [Dom.nez64, eval_argT])

/-- The term rebuilt bottom-up through the smart constructors, memoized over shared subterms. -/
def rebuildM : Nat → Tm → Std.HashMap Tm Tm → Option (Tm × Std.HashMap Tm Tm)
  | 0, _, _ => none
  | fuel + 1, t, memo =>
    match memo[t]? with
    | some r => some (r, memo)
    | none =>
      (t.args.foldlM (fun (acc : List Tm × Std.HashMap Tm Tm) a =>
          (rebuildM fuel a acc.2).map fun (r, m) => (acc.1 ++ [r], m)) ([], memo)).map
        fun (rs, m) => let r := smartNode t.op rs; (r, m.insert t r)

theorem rebuildM_sound (env : UInt64 → UInt32) :
    ∀ (fuel : Nat) (t : Tm) (memo : Std.HashMap Tm Tm) (r : Tm) (memo' : Std.HashMap Tm Tm),
      MemoOk env env memo → rebuildM fuel t memo = some (r, memo') →
      eval env r = eval env t ∧ MemoOk env env memo'
  | 0, _, _, _, _, _, h => by simp [rebuildM] at h
  | fuel + 1, mk h0 o as, memo, r, memo', hm, h => by
    unfold rebuildM at h
    split at h
    · rename_i r0 hr0
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm _ _ hr0, hm⟩
    · simp only [args, Option.map_eq_some_iff] at h
      obtain ⟨⟨rs, m⟩, hfold, hres⟩ := h
      simp only [Prod.mk.injEq] at hres; obtain ⟨rfl, rfl⟩ := hres
      have key : ∀ (xs : List Tm) (acc : List Tm × Std.HashMap Tm Tm) (out : List Tm × Std.HashMap Tm Tm),
          MemoOk env env acc.2 →
          xs.foldlM (fun (acc : List Tm × Std.HashMap Tm Tm) a =>
            (rebuildM fuel a acc.2).map fun (r, m) => (acc.1 ++ [r], m)) acc = some out →
          out.1.map (eval env) = acc.1.map (eval env) ++ xs.map (eval env) ∧ MemoOk env env out.2 := by
        intro xs
        induction xs with
        | nil => intro acc out hacc hf; simp at hf; subst hf; simpa using hacc
        | cons x xs ih =>
          intro acc out hacc hf
          rw [List.foldlM_cons] at hf
          cases h1 : rebuildM fuel x acc.2 with
          | none => simp [h1] at hf
          | some p =>
          obtain ⟨r1, m1⟩ := p
          simp only [h1, Option.map_some] at hf
          obtain ⟨e1, hm1⟩ := rebuildM_sound env fuel x acc.2 r1 m1 hacc h1
          obtain ⟨e2, hm2⟩ := ih _ out hm1 hf
          refine ⟨?_, hm2⟩
          rw [e2]; simp [e1]
      obtain ⟨e, hmr⟩ := key as ([], memo) (rs, m) hm hfold
      simp only [List.map_nil, List.nil_append] at e
      have ev : eval env (smartNode o rs) = eval env (mk h0 o as) := by
        rw [eval_smartNode, eval_mk, e]
      exact ⟨ev, hmr.insert _ _ ev⟩

/-- Leaf indices in order of first occurrence, each shared node visited once (unverified; only chooses a
numbering). -/
partial def occurrences (t : Tm) (acc : Array UInt64 × Std.HashSet Tm) : Array UInt64 × Std.HashSet Tm :=
  if acc.2.contains t then acc else
  let acc := (acc.1, acc.2.insert t)
  match t.op with
  | .var k => if acc.1.contains k then acc else (acc.1.push k, acc.2)
  | _ => t.args.foldl (fun a c => occurrences c a) acc

/-- The two sides abstracted over `leaves` and rebuilt. -/
def abstractPair (leaves : Array Tm) (impl spec : Tm) : Option (Tm × Tm) :=
  (absM leaves 4096 impl {}).bind fun (l, m) => (absM leaves 4096 spec m).bind fun (r, _) =>
    (rebuildM 4096 l {}).bind fun (l', m2) => (rebuildM 4096 r m2).map fun (r', _) => (l', r')

/-- Renumber the leaves by first occurrence in the rebuilt residual, a round at a time (unverified). -/
def canonLeaves (impl spec : Tm) (leaves : Array Tm) : Nat → Array Tm
  | 0 => leaves
  | n + 1 =>
    match abstractPair leaves impl spec with
    | some (l, r) =>
      let order := (occurrences r (occurrences l (#[], {}))).1
      let rest := (List.range leaves.size).filter (fun k => !order.contains k.toUInt64)
      let leaves' := order.map (fun k => leaves.getD k.toNat (lit 0)) ++ rest.toArray.map (fun k => leaves.getD k (lit 0))
      canonLeaves impl spec leaves' n
    | none => leaves

/-! ## 4. Residuals and the check -/

def opLean : TOp → String
  | .lit v => s!"(.lit {v})" | .var a => s!"(.var {a})" | .sum => ".sum" | .tsum => ".tsum" | .sub => ".sub" | .mul => ".mul"
  | .mulHi => ".mulHi" | .band => ".band" | .bor => ".bor" | .shl => ".shl" | .lshr => ".lshr" | .ite => ".ite"
  | .carry => ".carry" | .borrow => ".borrow" | .addc => ".addc" | .carryc => ".carryc" | .subc => ".subc"
  | .borrowc => ".borrowc" | .ule => ".ule" | .ugt => ".ugt" | .ult64 => ".ult64" | .ne64 => ".ne64"
  | .bit k => s!"(.bit {k})" | .pack => ".pack" | .shl64lo => ".shl64lo" | .shl64hi => ".shl64hi"
  | .lshr64lo => ".lshr64lo" | .lshr64hi => ".lshr64hi" | .nez64 => ".nez64"

/-- The term as Lean source, `Tm.mk` with its cached hash, so that the term read back is this term. -/
def toLean : Tm → String
  | mk h o as => s!"(.mk {h} {opLean o} [{", ".intercalate (as.map toLean)}])"
termination_by t => sizeOf t
decreasing_by all_goals (simp_wf; have := List.sizeOf_lt_of_mem ‹_›; omega)


/-- An obligation left after cutting: the two sides over leaf variables. -/
structure Residual where
  lhs : Tm
  rhs : Tm
  deriving DecidableEq, Inhabited

def Residual.Holds (r : Residual) : Prop := ∀ env : UInt64 → UInt32, r.lhs.eval env = r.rhs.eval env

/-- The leaves of a pair, by the unverified search. -/
def leavesOf (impl spec : Tm) : Array Tm :=
  let specNodes := collect spec {}
  let implNodes := collect impl {}
  (findLeaves implNodes spec ((findLeaves specNodes impl (#[], {})).1, {})).1

/-- The memory words of a pair: its leaves when nothing else is cut. -/
def wordLeaves (impl spec : Tm) : Array Tm :=
  (findLeaves {} spec ((findLeaves {} impl (#[], {})).1, {})).1

/-- Environments a residual is tried on before it is kept. -/
def sampleEnvs : List (UInt64 → UInt32) :=
  [1, 2, 3, 4, 5, 6, 7, 8].map fun s => fun a => (mixHash (hash a) s).toUInt32

/-- A term's value with each shared node evaluated once (a residual is a DAG; `eval` unfolds its tree). -/
partial def evalMemo (env : UInt64 → UInt32) (t : Tm) (m : Std.HashMap Tm UInt32) : UInt32 × Std.HashMap Tm UInt32 :=
  match m[t]? with
  | some v => (v, m)
  | none =>
    let (vs, m) := t.args.foldl (fun (acc : Array UInt32 × Std.HashMap Tm UInt32) a =>
      let (v, m) := evalMemo env a acc.2; (acc.1.push v, m)) (#[], m)
    let v := t.op.sem env vs.toList
    (v, m.insert t v)

/-- Some sample environment tells the two sides apart: the residual is false. -/
def refuted (l r : Tm) : Bool :=
  sampleEnvs.any fun env => let (a, m) := evalMemo env l {}; a != (evalMemo env r m).1

/-- The residual of an implementation term against a specification term: cut at the maximal common
subterms; when a sample refutes that, a cut hid a relation the two sides need (a compiler's `2y`
computed apart from `y`, cut at `y`), and the pair is cut at its memory words alone (counterexample-guided
refinement of the cutpoints, as in combinational equivalence checking). -/
def residual (impl spec : Tm) : Option Residual :=
  let p := ShareCommon.shareCommon' (impl, spec)
  let leaves := canonLeaves p.1 p.2 (leavesOf p.1 p.2) 1
  match abstractPair leaves p.1 p.2 with
  | some (l, r) =>
    if refuted l r then
      (abstractPair (canonLeaves p.1 p.2 (wordLeaves p.1 p.2) 1) p.1 p.2).map fun (l, r) => ⟨l, r⟩
    else some ⟨l, r⟩
  | none => none

private theorem shareCommon_eq' {α : Type} (a : α) : ShareCommon.shareCommon' a = a := by
  unfold ShareCommon.shareCommon'; rfl

/-- `shareCommon'` only changes which equal objects are shared (its definition is the identity; the
runtime implementation is Lean's `lean_sharecommon_quick`). -/
theorem shareCommon_eq {α : Type} (a : α) : ShareCommon.shareCommon' a = a := shareCommon_eq' a

theorem abstractPair_sound (env : UInt64 → UInt32) (leaves : Array Tm) (impl spec l r : Tm)
    (h : abstractPair leaves impl spec = some (l, r)) :
    eval (leafEnv env leaves) l = eval env impl ∧ eval (leafEnv env leaves) r = eval env spec := by
  simp only [abstractPair, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨l0, m⟩, h1, ⟨r0, m1⟩, h2, ⟨l1, m2⟩, h3, ⟨r1, m3⟩, h4, he⟩ := h
  simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨e1, hm⟩ := absM_sound env leaves 4096 impl {} l0 m (MemoOk.empty _ _) h1
  obtain ⟨e2, _⟩ := absM_sound env leaves 4096 spec m r0 m1 hm h2
  obtain ⟨e3, hm2⟩ := rebuildM_sound (leafEnv env leaves) 4096 l0 {} l1 m2 (MemoOk.empty _ _) h3
  obtain ⟨e4, _⟩ := rebuildM_sound (leafEnv env leaves) 4096 r0 m2 r1 m3 hm2 h4
  exact ⟨e3.trans e1, e4.trans e2⟩

/-- A residual that is trivial or holds makes the two terms evaluate equally, in every memory. -/
theorem residual_sound (env : UInt64 → UInt32) (impl spec : Tm) (r : Residual)
    (h : residual impl spec = some r) (hr : r.lhs = r.rhs ∨ r.Holds) : impl.eval env = spec.eval env := by
  have hab : ∀ (leaves : Array Tm) (l r' : Tm), abstractPair leaves impl spec = some (l, r') →
      (l = r' ∨ ∀ env, l.eval env = r'.eval env) → impl.eval env = spec.eval env := by
    intro leaves l r' hp hr
    obtain ⟨e1, e2⟩ := abstractPair_sound env _ impl spec l r' hp
    rw [← e1, ← e2]
    rcases hr with h | h
    · rw [h]
    · exact h _
  simp only [residual, shareCommon_eq] at h
  split at h
  · rename_i l r' hp
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨l2, r2⟩, hp2, rfl⟩ := h
      exact hab _ l2 r2 hp2 hr
    · simp only [Option.some.injEq] at h; subst h
      exact hab _ l r' hp hr
  · simp at h

end Tm
end Obend.Hardware.Gpu.Rdna2
