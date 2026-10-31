module
/-
# Obend.Spec.C4 — C4 linearization (ltuo §7.4.4): C3 plus the suffix property

C4 orders a node's ancestors: the node, then every ancestor once, most specific first. It is C3
(Barrett et al. 1996) with SUFFIX nodes (pommette.scm `c4-linearize`): a suffix node's own
precedence list must end every list it appears in. Written structurally, in four steps:

1. The SUFFIX TAIL. Each parent's precedence list, from its first suffix node on, is that parent's
   suffix tail (`Graph.tailAt`). The tails must lie on one chain, each a list suffix of the next
   (`joinTail`); the longest is the node's suffix tail. Two tails off one chain are refused.
2. The CANDIDATES. Every parent's precedence list and every local chain of parents, each with its
   trailing part in the suffix tail removed (`clean`); what is removed must keep the tail's order,
   and nothing before it may be in the tail. Otherwise refused.
3. The C3 MERGE (`merge`): repeatedly take the first head, in candidate order, that is in no
   candidate's tail, and remove it from the front of every candidate it heads. When none is
   available, refused. Each step removes an element, so the merge's bound is the candidates' total
   length (`mergeN`'s first argument): never a refusal of its own, and the merge is reducible in the
   kernel.
4. The result: the head, the merge, the suffix tail. A head that is its own ancestor, or a suffix
   tail that repeats a name, is refused.

What a result is, proved in `Obend.Spec.Proofs.C4` for every graph: it starts with the head, names
nothing twice, keeps every local chain in order (LOCAL PRECEDENCE), keeps every parent's own
precedence list in order (MONOTONICITY), and ends with the suffix tail, which is a parent's tail and
has every parent's tail as a list suffix; and, when the graph's own lists are C4 lists (`Coherent`),
every suffix node after the head has its whole precedence list as a suffix of the result (the
SUFFIX PROPERTY). pommette's published vectors, its refusals and 4000 seeded DAGs are compiled
tests in `Obend.Spec.Proofs.C4Vectors`.
-/
public section
namespace Obend.Spec.C4
set_option autoImplicit false

/-- Why a linearization refuses: the graph has no C4 linearization at `head`. -/
inductive Refusal where
  | inconsistent (head : List String) (detail : String)
  deriving @[expose] DecidableEq, Repr

def Refusal.message : Refusal → String
  | .inconsistent head detail => "inconsistent precedence graph at " ++ String.intercalate "," head ++ ": " ++ detail

def inconsistent {α : Type} (head : List String) (detail : String) : Except Refusal α :=
  .error (.inconsistent head detail)

/-- A precedence oracle: `precedence x` is `x`'s own precedence list (it starts with `x`, for a
coherent graph), `isSuffix x` whether `x` is a suffix node. -/
structure Graph where
  precedence : String → List String
  isSuffix : String → Bool

/-- A list from its first suffix node on. -/
@[expose] def Graph.suffixPart (g : Graph) (l : List String) : List String := l.dropWhile fun x => !g.isSuffix x

/-- A parent's suffix tail: its precedence list from its first suffix node on. -/
@[expose] def Graph.tailAt (g : Graph) (p : String) : List String := g.suffixPart (g.precedence p)

/-- No name twice. -/
@[expose] def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-! ## 1. The suffix tail -/

/-- Two suffix tails on one chain: the longer, which has the other as a list suffix. -/
@[expose] def joinTail (a b : List String) : Option (List String) :=
  if b.isSuffixOf a then some a else if a.isSuffixOf b then some b else none

/-- The suffix tail of a node with these parents: every parent's tail joined, in order. -/
@[expose] def tailOf (g : Graph) (head : List String) : List String → List String → Except Refusal (List String)
  | acc, [] => .ok acc
  | acc, p :: ps =>
    match joinTail acc (g.tailAt p) with
    | some t => tailOf g head t ps
    | none => inconsistent head ("suffix incompatibility: " ++ String.intercalate "," (g.tailAt p) ++
        " is not on the suffix chain of " ++ String.intercalate "," acc)

/-! ## 2. The candidates -/

/-- A candidate with its trailing suffix-tail part removed, when that part keeps the tail's order
and nothing before it is in the tail. -/
@[expose] def clean (tail l : List String) : Option (List String) :=
  if (l.dropWhile fun x => !tail.contains x).isSublist tail then some (l.takeWhile fun x => !tail.contains x)
  else none

@[expose] def cleanAll (tail : List String) : List (List String) → Option (List (List String))
  | [] => some []
  | l :: ls =>
    match clean tail l, cleanAll tail ls with
    | some c, some cs => some (c :: cs)
    | _, _ => none

/-! ## 3. The C3 merge -/

/-- The first head, in candidate order, that is in no candidate's tail. -/
@[expose] def nextHead (ls : List (List String)) : Option String :=
  ls.findSome? fun l => match l with
    | c :: _ => if ls.any (fun l' => l'.tail.contains c) then none else some c
    | [] => none

/-- `l` without `c` at its front. -/
@[expose] def popOne (c : String) : List String → List String
  | x :: t => if x == c then t else x :: t
  | [] => []

/-- Remove `c` from the front of every candidate it heads. -/
@[expose] def pop (c : String) (ls : List (List String)) : List (List String) := ls.map (popOne c)

/-- The merge, bounded by `n`; `merge` passes the candidates' total length, which no merge exceeds
(each step removes an element). -/
@[expose] def mergeN (head : List String) : Nat → List (List String) → Except Refusal (List String)
  | 0, ls => if ls.all List.isEmpty then .ok [] else inconsistent head "merge bound"
  | n + 1, ls =>
    if ls.all List.isEmpty then .ok [] else
    match nextHead ls with
    | none => inconsistent head "no C3 candidate"
    | some c =>
      match mergeN head n (pop c ls) with
      | .ok m => .ok (c :: m)
      | .error e => .error e

/-- The C3 merge of the candidates. -/
@[expose] def merge (head : List String) (ls : List (List String)) : Except Refusal (List String) :=
  mergeN head (ls.map List.length).sum ls

/-! ## 4. The linearization -/

/-- The C4 precedence list of `head` (usually `[x]`) whose parents are given as local chains, and
its most specific suffix node. -/
@[expose] def linearize (g : Graph) (head : List String) (parents : List (List String)) :
    Except Refusal (List String × Option String) :=
  let ps := parents.flatten
  match tailOf g head [] ps with
  | .error e => .error e
  | .ok tail =>
    match cleanAll tail (ps.map g.precedence ++ parents) with
    | none => inconsistent head "an ancestor is out of order versus the suffix tail"
    | some cands =>
      if nodupB (head ++ tail) && head.all (fun h => !cands.any (·.contains h)) then
        match merge head cands with
        | .ok m => .ok (head ++ m ++ tail, tail.head?)
        | .error e => .error e
      else inconsistent head "a node is its own ancestor, or the suffix tail repeats a name"

/-- An oracle whose lists are C4 lists: each starts at its node, repeats nothing, and has the
suffix property itself. Every oracle built by memoizing `linearize` is (`Obend.Spec.Proofs.C4`). -/
def Coherent (g : Graph) : Prop :=
  ∀ p, (∃ t, g.precedence p = p :: t) ∧ (g.precedence p).Nodup ∧
    ∀ s ∈ g.precedence p, g.isSuffix s = true → (g.precedence s).IsSuffix (g.precedence p)

/-- A graph with `x`'s list replaced by `lin`: memoizing a linearization. -/
def Graph.extend (g : Graph) (x : String) (lin : List String) : Graph :=
  ⟨fun y => if y = x then lin else g.precedence y, g.isSuffix⟩

/-- Renaming a graph along a bijection (`to`, with inverse `back`). -/
def Graph.rename (g : Graph) (to back : String → String) : Graph :=
  ⟨fun y => (g.precedence (back y)).map to, fun y => g.isSuffix (back y)⟩

/-- ORDERED-PRESENTATION INVARIANCE (scholar §5): linearization commutes with every renaming of
specification identities, a refusal staying a refusal. It is a claim about the ORDERED presentation
(local parent sequences and suffix marks), not about a bare DAG: a bare symmetric poset admits no
equivariant strict order. Checked (compiled) on 4000 seeded random DAGs by
`Obend.Spec.Proofs.C4Vectors.ordered_presentation_invariance_4000`. -/
def OrderedPresentationInvariant : Prop :=
  ∀ (g : Graph) (to back : String → String),
    (∀ x, back (to x) = x) → (∀ y, to (back y) = y) →
    ∀ (head : List String) (parents : List (List String)),
      (linearize (g.rename to back) (head.map to) (parents.map (·.map to))).toOption =
        (linearize g head parents).toOption.map (fun r => (r.1.map to, r.2.map to))

end Obend.Spec.C4

end
