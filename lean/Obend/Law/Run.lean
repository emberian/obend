module
/-
# Obend.Law.Run — one step of Core4's reference semantics, as a function

`step?` computes the unique `Step` successor of a term (`Obend.Law.Proofs.Run.step_iff`), and
`run fuel` iterates it to a value. Neither is a meaning: they exist so that a concrete law on
concrete data can be run inside the kernel (`decide +kernel`) and the result read back as an
`Evaluates` fact (`run_sound`). That is how the meaning theorems' teeth are cut: an instance where
the hypothesis holds, and one where the law refuses.
-/
public import Obend.Core.Term
public section
namespace Obend.Law
open Obend.Core.Term
set_option autoImplicit false

@[expose] def isValueB : Term → Bool
  | .lam _ | .nat _ | .boolean _ | .label _ | .record _ | .specification _ _ | .prototype _ _
  | .inject _ _ => true
  | _ => false

/-- The reference semantics' successor, rule by rule (`Term.Step`). -/
@[expose] def step? : Term → Option Term
  | .app f a =>
    match f with
    | .lam b => some (instantiate b a)
    | .specification _ e => some (.app e a)
    | _ => (step? f).map (fun f' => .app f' a)
  | .mix l u => some (mixBody l u)
  | .fix s i => some (.app (.app s (.fix s i)) i)
  | .reflect t =>
    match t with
    | .prototype s _ => some s
    | _ => (step? t).map .reflect
  | .metadata t =>
    match t with
    | .specification m _ => some m
    | _ => (step? t).map .metadata
  | .project t =>
    match t with
    | .prototype _ x => some x
    | _ => (step? t).map .project
  | .get t n =>
    match t with
    | .record fs => (fs.find? (fun field => field.1 == n)).map (·.2)
    | _ => (step? t).map (fun t' => .get t' n)
  | .extend t fs =>
    match t with
    | .record gs => some (.record (extendFields gs fs))
    | _ => (step? t).map (fun t' => .extend t' fs)
  | .binary p l r =>
    match step? l with
    | some l' => some (.binary p l' r)
    | none =>
      if isValueB l then
        match step? r with
        | some r' => some (.binary p l r')
        | none => if isValueB r then primitiveResult p l r else none
      else none
  | .ifZero v z s =>
    match v with
    | .nat 0 => some z
    | .nat (k + 1) => some (instantiate s (.nat k))
    | _ => (step? v).map (fun v' => .ifZero v' z s)
  | .case t arms =>
    match t with
    | .inject l p => (arms.find? (fun arm => arm.1 == l)).map (fun arm => instantiate arm.2 p)
    | _ => (step? t).map (fun t' => .case t' arms)
  | .ifBool c x y =>
    match c with
    | .boolean true => some x
    | .boolean false => some y
    | _ => (step? c).map (fun c' => .ifBool c' x y)
  | .done v => some v
  | _ => none

/-- At most `fuel` steps to a value. -/
@[expose] def run : Nat → Term → Option Term
  | 0, t => if isValueB t then some t else none
  | fuel + 1, t =>
    if isValueB t then some t else
    match step? t with
    | some t' => run fuel t'
    | none => none

/-- The run reached `ok`. -/
@[expose] def okB : Option Term → Bool
  | some (.inject "ok" _) => true
  | _ => false

/-- The run reached a refusal, and its reason. -/
@[expose] def refusalOf : Option Term → Option String
  | some (.inject "refused" (.label why)) => some why
  | _ => none

end Obend.Law
