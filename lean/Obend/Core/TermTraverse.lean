module
public import Obend.Core.Term
public import Obend.Tactic.Cases
public import Obend.Core.Traverse
@[expose] public section
namespace Obend.Core.TermTraverse
open Obend.Core.Term
open Obend.Core.Traverse
set_option autoImplicit false

/-- Payloads and field labels are retained without imposing a fixed child arity
on the generic traversal. Field wrappers also retain duplicate labels and order. -/
inductive Tag where
  | hole (n : Nat)
  | app
  | mix
  | fix
  | specification
  | prototype
  | reflect
  | metadata
  | project
  | ifBool
  | perform
  | done
  | nat (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | binary (primitive : Primitive)
  | extend | record | ifZero | case
  | get (name : String)
  | inject (name : String)
  | field (name : String)

abbrev Shape := Tree Tag

def encode : Term → Shape
  | .hole n σ => .node (.hole n) (σ.map encode)
  | .bound i => .var i
  | .lam b => .bind (encode b)
  | .app a b => .node .app [encode a, encode b]
  | .mix a b => .node .mix [encode a, encode b]
  | .fix a b => .node .fix [encode a, encode b]
  | .specification a b => .node .specification [encode a, encode b]
  | .prototype a b => .node .prototype [encode a, encode b]
  | .reflect a => .node .reflect [encode a]
  | .metadata a => .node .metadata [encode a]
  | .project a => .node .project [encode a]
  | .ifBool a b c => .node .ifBool [encode a, encode b, encode c]
  | .perform a => .node .perform [encode a]
  | .done a => .node .done [encode a]
  | .nat n => .node (.nat n) []
  | .boolean b => .node (.boolean b) []
  | .label l => .node (.label l) []
  | .binary p a b => .node (.binary p) [encode a, encode b]
  | .extend a fs => .node .extend (encode a :: fs.map (fun f => .node (.field f.1) [encode f.2]))
  | .record fs => .node .record (fs.map (fun f => .node (.field f.1) [encode f.2]))
  | .get a n => .node (.get n) [encode a]
  | .ifZero a b c => .node .ifZero [encode a, encode b, .bind (encode c)]
  | .inject n a => .node (.inject n) [encode a]
  | .case a fs => .node .case (encode a :: fs.map (fun f => .node (.field f.1) [.bind (encode f.2)]))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf f.snd < sizeOf f := by cases f; simp +arith
       omega)

/-- Decode is total; malformed shapes are irrelevant to the left inverse. -/
def decode : Shape → Term
  | .node (.hole n) σ => .hole n (σ.map decode)
  | .var i => .bound i
  | .bind b => .lam (decode b)
  | .node .app [a, b] => .app (decode a) (decode b)
  | .node .mix [a, b] => .mix (decode a) (decode b)
  | .node .fix [a, b] => .fix (decode a) (decode b)
  | .node .specification [a, b] => .specification (decode a) (decode b)
  | .node .prototype [a, b] => .prototype (decode a) (decode b)
  | .node .reflect [a] => .reflect (decode a)
  | .node .metadata [a] => .metadata (decode a)
  | .node .project [a] => .project (decode a)
  | .node .ifBool [a, b, c] => .ifBool (decode a) (decode b) (decode c)
  | .node .perform [a] => .perform (decode a)
  | .node .done [a] => .done (decode a)
  | .node (.nat n) [] => .nat n
  | .node (.boolean b) [] => .boolean b
  | .node (.label l) [] => .label l
  | .node (.binary p) [a,b] => .binary p (decode a) (decode b)
  | .node .extend (a :: fs) => .extend (decode a) (fs.map fun f => match decode f with
      | .get b n => (n, b)
      | _ => ("", .bound 0))
  | .node .record fs => .record (fs.map fun f => match decode f with
      | .get b n => (n, b)
      | _ => ("", .bound 0))
  | .node (.field n) [a] => .get (decode a) n
  | .node (.get n) [a] => .get (decode a) n
  | .node .ifZero [a,b,.bind c] => .ifZero (decode a) (decode b) (decode c)
  | .node (.inject n) [a] => .inject n (decode a)
  | .node .case (a :: fs) => .case (decode a) (fs.map fun f => match decode f with
      | .get (.lam b) n => (n, b)
      | _ => ("", .bound 0))
  | _ => .bound 0
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       omega)

theorem map_self {α : Type} (f : α → α) (xs : List α)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs :=
  (List.map_congr_left h).trans (List.map_id xs)

theorem decode_encode (t : Term) : decode (encode t) = t := by
  obend_cases t with []
  all_goals simp only [encode, decode, List.map_map]
  all_goals first
    | rfl
    | (congr 1 <;> first
        | exact decode_encode _
        | (apply map_self; intro f hf
           simp only [Function.comp_apply, decode]
           rw [decode_encode f.2])
        | (apply map_self; intro a ha
           simp only [Function.comp_apply]
           exact decode_encode a))
termination_by sizeOf t
decreasing_by
  all_goals simp_all
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have hlist := List.sizeOf_lt_of_mem hf
       have hpair : sizeOf f.snd < sizeOf f := by cases f; simp +arith
       omega)

theorem encode_injective {a b : Term} (h : encode a = encode b) : a = b := by
  rw [← decode_encode a, ← decode_encode b, h]

@[simp] theorem encode_rename (t : Term) (f : Nat → Nat) :
    encode (t.rename f) = Tree.rename f (encode t) := by
  obend_cases t with []
  all_goals simp only [Term.rename, encode, Tree.rename, Tree.traverse, List.map_cons,
    List.map_nil, List.map_map]
  all_goals
    repeat first
      | rfl
      | exact encode_rename _ _
      | (apply List.map_congr_left; intro a ha
         exact encode_rename a f)
      | (apply List.map_congr_left; intro a ha
         simp only [Function.comp_apply, Tree.traverse, List.map_cons, List.map_nil]
         rw [encode_rename a.2])
      | congr 1
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have hlist := List.sizeOf_lt_of_mem ha
       have hpair : sizeOf a.snd < sizeOf a := by cases a; simp +arith
       omega)

@[simp] theorem encode_liftSubstitution (σ : Nat → Term) :
    (fun i => encode (liftSubstitution σ i)) = Tree.liftSubst (fun i => encode (σ i)) := by
  funext i; cases i <;> simp [liftSubstitution, Tree.liftSubst, encode]

@[simp] theorem encode_substitute (t : Term) (σ : Nat → Term) :
    encode (t.substitute σ) = Tree.substitute (fun i => encode (σ i)) (encode t) := by
  obend_cases t with []
  all_goals simp only [Term.substitute, encode, Tree.substitute, Tree.traverse, List.map_cons,
    List.map_nil, List.map_map, Tree.node.injEq, Tree.bind.injEq, List.cons.injEq,
    and_true, true_and]
  all_goals
    repeat first
      | rfl
      | exact encode_substitute _ _
      | (rw [← encode_liftSubstitution]; exact encode_substitute _ _)
      | (apply List.map_congr_left; intro a ha
         exact encode_substitute a σ)
      | (apply List.map_congr_left; intro a ha
         simp only [Function.comp_apply, Tree.traverse, List.map_cons, List.map_nil]
         rw [encode_substitute a.2]
         try simp only [encode_liftSubstitution])
      | constructor
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have hlist := List.sizeOf_lt_of_mem ha
       have hpair : sizeOf a.snd < sizeOf a := by cases a; simp +arith
       omega)

/-- Derived traversals share the generic rebuilding recursion. The existing
Term equations remain a compatibility interface, with equality proved below. -/
def derivedRename (f : Nat → Nat) (t : Term) : Term := decode (Tree.rename f (encode t))
def derivedSubstitute (σ : Nat → Term) (t : Term) : Term :=
  decode (Tree.substitute (fun i => encode (σ i)) (encode t))

theorem rename_eq_derived (t : Term) (f : Nat → Nat) : t.rename f = derivedRename f t := by
  rw [derivedRename, ← encode_rename, decode_encode]

theorem substitute_eq_derived (t : Term) (σ : Nat → Term) : t.substitute σ = derivedSubstitute σ t := by
  rw [derivedSubstitute, ← encode_substitute, decode_encode]

theorem rename_comp (t : Term) (f g : Nat → Nat) :
    (t.rename f).rename g = t.rename (fun i => g (f i)) := by
  apply encode_injective
  simpa only [encode_rename] using Tree.rename_comp (encode t) f g

theorem substitute_rename (t : Term) (σ : Nat → Term) (f : Nat → Nat) :
    (t.substitute σ).rename f = t.substitute (fun i => (σ i).rename f) := by
  apply encode_injective
  simpa only [encode_rename, encode_substitute] using
    Tree.substitute_rename (encode t) (fun i => encode (σ i)) f

theorem rename_substitute (t : Term) (f : Nat → Nat) (σ : Nat → Term) :
    (t.rename f).substitute σ = t.substitute (fun i => σ (f i)) := by
  apply encode_injective
  simpa only [encode_rename, encode_substitute] using
    Tree.rename_substitute (encode t) f (fun i => encode (σ i))

theorem substitute_comp (t : Term) (σ τ : Nat → Term) :
    (t.substitute σ).substitute τ = t.substitute (fun i => (σ i).substitute τ) := by
  apply encode_injective
  simpa only [encode_substitute] using
    Tree.substitute_comp (encode t) (fun i => encode (σ i)) (fun i => encode (τ i))

/-- The generic free-variable predicate, available without the machine layer. -/
abbrev All (p : Nat → Prop) (t : Term) : Prop := Tree.All p (encode t)
abbrev Scoped (n : Nat) (t : Term) : Prop := Tree.Scoped n (encode t)

theorem scoped_rename_identity (t : Term) (n : Nat) (h : Scoped n t)
    (f : Nat → Nat) (same : ∀ i, i < n → f i = i) : t.rename f = t := by
  apply encode_injective
  simpa only [encode_rename] using Tree.scoped_rename_identity (encode t) n h f same

theorem scoped_substitution_congr (t : Term) (n : Nat) (h : Scoped n t)
    (σ τ : Nat → Term) (same : ∀ i, i < n → σ i = τ i) : t.substitute σ = t.substitute τ := by
  apply encode_injective
  simp only [encode_substitute]
  apply Tree.substitute_congr_on (encode t) (fun i => i < n) h
  intro i hi; rw [same i hi]

theorem scoped_substitute_identity (t : Term) (n : Nat) (h : Scoped n t)
    (σ : Nat → Term) (same : ∀ i, i < n → σ i = .bound i) : t.substitute σ = t := by
  apply encode_injective
  simp only [encode_substitute]
  apply Tree.scoped_substitute_identity (encode t) n h
  intro i hi; rw [same i hi]; simp only [encode]

theorem scoped_rename (t : Term) (n m : Nat) (h : Scoped n t)
    (f : Nat → Nat) (maps : ∀ i, i < n → f i < m) : Scoped m (t.rename f) := by
  simpa only [Scoped, encode_rename] using Tree.scoped_rename (encode t) n m h f maps

theorem scoped_substitute (t : Term) (n m : Nat) (h : Scoped n t)
    (σ : Nat → Term) (maps : ∀ i, i < n → Scoped m (σ i)) : Scoped m (t.substitute σ) := by
  simpa only [Scoped, encode_substitute] using
    Tree.scoped_substitute (encode t) n m h (fun i => encode (σ i)) maps

#assert_axioms rename_eq_derived substitute_eq_derived decode_encode encode_injective encode_rename encode_liftSubstitution encode_substitute
  rename_comp rename_substitute substitute_rename substitute_comp
  scoped_rename_identity scoped_substitution_congr scoped_substitute_identity scoped_rename scoped_substitute

end Obend.Core.TermTraverse
end
