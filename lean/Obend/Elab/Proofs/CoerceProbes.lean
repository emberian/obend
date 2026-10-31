module
/- Teeth for `Obend.Elab.Coerce`, run by the build on the actual checker. -/
public import Obend.Elab.Coerce
public meta import Obend.Elab.Coerce

@[expose] public section
namespace Obend.Elab.Proofs.CoerceProbes
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Elab.Coerce
open Obend.Core.Proofs.BidirectionalCompleteness
open Obend.Core.Term (Term)

def quantities : List Quantity := [.erased, .affine, .linear, .unrestricted]

/-- Astra's η-wrapper experiment: `λx. f x` at a `q'` parameter, `f` an unrestricted reusable
`q → Nat` function in the context. -/
def wrapperMeasured (q q' : Quantity) : Bool :=
  (checkAgainst ⟨.lam (.app (.bound 1) (.bound 0)),
      fun path => if path = [] then some ⟨.natural, .natural, q', .reusable⟩ else none, {}⟩
    [⟨.arrow .reusable q .natural .natural, .unrestricted⟩]
    (.arrow .reusable q' .natural .natural)).toBool

-- the measured matrix, row by row, is Astra's: [[F,T,T,T],[F,T,T,T],[F,T,T,T],[F,F,F,T]]
#guard (quantities.map fun q => quantities.map fun q' => wrapperMeasured q q') =
  [[false, true, true, true], [false, true, true, true], [false, true, true, true], [false, false, false, true]]
-- and `wrapperAllowed` is that matrix
#guard quantities.all fun q => quantities.all fun q' => wrapperMeasured q q' == wrapperAllowed q q'

/-- Astra line 57's source row: a custody handle, a natural, and a once closure. -/
def custodyRow : Ty :=
  .field "handle" (.custody 0) (.field "tag" .natural
    (.field "extra" (.arrow .once .affine .natural .natural) .emptyRow))

def projection (q : Quantity) (kept : List String) : Bool :=
  let target := kept.foldr (fun name row => Ty.field name
    (if name == "handle" then .custody 0 else .natural) row) .emptyRow
  (checkAgainst ⟨.lam (.record (kept.map fun name => (name, .get (.bound 0) name))),
      fun path => if path = [] then some ⟨custodyRow, target, q, .once⟩ else none, {}⟩
    [] (.arrow .once q custodyRow target)).toBool

-- one kept field consumes the receiver once: accepted with an affine binder
#guard projection .affine ["handle"]
#guard projection .affine ["tag"]
-- two kept fields mention it twice; it cannot be unrestricted: refused at every quantity
#guard quantities.all fun q => !projection q ["handle", "tag"]

-- `coerce` agrees: the one-field width coercion is emitted and checks, the two-field one is the
-- named sharing obstruction
#guard (coerce {} custodyRow (.field "handle" (.custody 0) .emptyRow)).toBool
#guard (match coerce {} custodyRow (.field "handle" (.custody 0) (.field "tag" .natural .emptyRow)) with
  | .error (.needsSharing _) => true | _ => false)

-- a shareable seed with an extra member coerces to the row without it
def seedRow : Ty := .field "x" .natural (.field "extra" .boolean .emptyRow)
#guard (coerce {} seedRow (.field "x" .natural .emptyRow)).toBool
#guard (coerce {} seedRow (.field "extra" .boolean (.field "x" .natural .emptyRow))).toBool

-- depth: a nested record member is coerced in place
#guard (coerce {} (.field "p" seedRow .emptyRow) (.field "p" (.field "x" .natural .emptyRow) .emptyRow)).toBool

-- sums widen, payloads coerced inside their arms
#guard (coerce {} (.variant (.field "a" .natural .emptyRow))
  (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))).toBool
#guard (match coerce {} (.variant (.field "a" .natural (.field "b" .boolean .emptyRow)))
  (.variant (.field "a" .natural .emptyRow)) with
  | .error (.missingLabel "b" _) => true | _ => false)

-- functions: the η-wrapper inside the measured matrix, refusals outside it
#guard (coerce {} (.arrow .reusable .affine .natural seedRow)
  (.arrow .reusable .linear .natural (.field "x" .natural .emptyRow))).toBool
#guard (match coerce {} (.arrow .reusable .unrestricted .natural .natural) (.arrow .reusable .affine .natural .natural) with
  | .error (.quantityNotWrappable .unrestricted .affine) => true | _ => false)
#guard (match coerce {} (.arrow .reusable .affine .natural .natural) (.arrow .reusable .erased .natural .natural) with
  | .error (.quantityNotWrappable .affine .erased) => true | _ => false)
#guard (match coerce {} (.arrow .once .affine .natural .natural) (.arrow .reusable .affine .natural .natural) with
  | .error (.reuseChanged .once .reusable) => true | _ => false)

-- coercions into an alias whose unfolding differs are refused by name (no recursive wrappers)
#guard (match coerce ⟨[(0, .variant (.field "a" .boolean .emptyRow))], [], []⟩
    (.variant (.field "a" .natural .emptyRow)) (.variable 0) with
  | .error (.recursive _ _) => true | _ => false)

end Obend.Elab.Proofs.CoerceProbes
end
