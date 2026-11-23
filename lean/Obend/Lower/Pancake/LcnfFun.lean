module
public import Obend.Lower.Pancake
import all Obend.Lower.Pancake
import all Obend.Lower.Pancake.LcnfSimHelpers
import all Obend.Lower.Pancake.LcnfEmit

public section
namespace Obend.Lower.Pancake
open Obend.Lower.LCNF
set_option autoImplicit false

/-- Parameter i occupies bvar i; generated temporaries start after all parameters. -/
def wordParams (n : Nat) : List (String × Shape) :=
  (List.finRange n).map fun i => (mkSlot 'v' i.val, .One)

def paramTypes (bounds : List Nat) : List FoTy := bounds.map (fun b => .one (.scalar b))

def lowerLcnfFun (name : String) (bounds : List Nat) (c : LcnfCode) : Option (PFun × Nat) := do
  let tags := collectTags c
  guard (tags.length < 2^64 && bounds.all (· < 2^64))
  let limit ← checkFoCode tags (paramTypes bounds) [] c
  let ps := wordParams bounds.length
  return (⟨name, ps, (compileCode tags ps [] bounds.length c).1, false⟩, limit)

theorem lowerLcnfFun_correct {τ : Type} (name : String) (bounds : List Nat) (c : LcnfCode)
    (f : PFun) (bound : Nat) (h : lowerLcnfFun name bounds c = some (f,bound))
    (s : PanState τ) (env : List LcnfVal) (wf : StateWF s) (clk : synthLcnfClk c ≤ s.clock)
    (args : EnvMatches (collectTags c) env (paramTypes bounds) (wordParams bounds.length) s.locals) :
    ∃ n t, n ≤ bound ∧ evalFoBlock env c = some (.returned (.scalar n)) ∧
      evaluate f.body s = (.ret (.word (BitVec.ofNat 64 n)), t) := by
  unfold lowerLcnfFun at h
  simp only [bind, Option.bind, pure] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i check
  cases h
  have slots : VarSlotsWF bounds.length (wordParams bounds.length) := by
    intro pair mem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact ⟨i, i.isLt, rfl⟩
  obtain ⟨out, r, t, hs, he, _, _, post⟩ := compileCode_sim (collectTags c)
    c env (paramTypes bounds) (wordParams bounds.length) [] [] bounds.length _ s
    check wf clk slots (.nil _) args (fun _ hh => by cases hh)
  cases out with
  | jumped _ _ => cases post.2.1
  | returned v =>
    obtain ⟨n, rfl, hn, _, rfl⟩ := post
    exact ⟨n, t, hn, hs, he⟩

end Obend.Lower.Pancake
