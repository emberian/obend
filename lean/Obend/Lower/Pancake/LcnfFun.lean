module
public import Obend.Lower.Pancake
public import Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake
import all Obend.Lower.Pancake.EmitPnk
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

/-- Lower an LCNF block to a Pancake function and emit its concrete `.pnk` source text. -/
def lowerAndEmitLcnfFun (name : String) (bounds : List Nat) (c : LcnfCode) :
    Option (PFun × String × Nat) := do
  let (f, limit) ← lowerLcnfFun name bounds c
  let src ← emitPnkFun f
  return (f, src, limit)

/-- End-to-end LCNF-to-Pancake lowering + concrete syntax emission soundness:
    any accepted `(f, src, bound)` satisfies concrete delimiter balance (`pnkBalanced src = true`)
    and semantic simulation (`evalFoBlock` agrees with `PanSem.evaluate f.body` within `bound`). -/
theorem lowerAndEmitLcnfFun_sound {τ : Type} (name : String) (bounds : List Nat) (c : LcnfCode)
    (f : PFun) (src : String) (bound : Nat)
    (h : lowerAndEmitLcnfFun name bounds c = some (f, src, bound))
    (s : PanState τ) (env : List LcnfVal) (wf : StateWF s) (clk : synthLcnfClk c ≤ s.clock)
    (args : EnvMatches (collectTags c) env (paramTypes bounds) (wordParams bounds.length) s.locals) :
    pnkBalanced src = true ∧
    ∃ n t, n ≤ bound ∧ evalFoBlock env c = some (.returned (.scalar n)) ∧
      evaluate f.body s = (.ret (.word (BitVec.ofNat 64 n)), t) := by
  unfold lowerAndEmitLcnfFun at h
  simp only [bind, Option.bind, pure] at h
  cases hl : lowerLcnfFun name bounds c with
  | none => rw [hl] at h; cases h
  | some fl =>
    rcases fl with ⟨f', lim⟩; rw [hl] at h; dsimp only at h
    cases he : emitPnkFun f' with
    | none => rw [he] at h; cases h
    | some src' =>
      rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨emitPnkProg_balanced [f'] src' he, lowerLcnfFun_correct name bounds c f' lim hl s env wf clk args⟩

private theorem lowerAndEmitLcnfFun_inhabited :
    ∃ f src bound, lowerAndEmitLcnfFun "second" [4, 9] (.return (.bvar 1)) = some (f, src, bound) ∧
      pnkBalanced src = true ∧
      ∃ n t, n ≤ bound ∧ evalFoBlock [.scalar 3, .scalar 8] (.return (.bvar 1)) = some (.returned (.scalar n)) ∧
        evaluate f.body
          { emptyPanState () 0 with locals := FUPDATE (FUPDATE FEMPTY (mkSlot 'v' 1, .word 8)) (mkSlot 'v' 0, .word 3) } =
          (.ret (.word (BitVec.ofNat 64 n)), t) := by
  let f : PFun := ⟨"second", [("v", .One), ("v_", .One)], .ret (.lvar "v_"), false⟩
  let src : String := "fun second(1 v, 1 v_) {\nreturn v_;\n}\n"
  have hLower : lowerLcnfFun "second" [4, 9] (.return (.bvar 1)) = some (f, 9) := rfl
  have hName : pnkIdentifier "second" = some "second" := by unfold pnkIdentifier; decide +kernel
  have hV0 : pnkIdentifier "v" = some "v" := by unfold pnkIdentifier; decide +kernel
  have hV1 : pnkIdentifier "v_" = some "v_" := by unfold pnkIdentifier; decide +kernel
  have hFunText : funText f = some src := by
    simp [f, src, funText, shapeText, stmtText, exprText, scopedVar, hName, hV0, hV1, block, guard]
  have hBal : pnkBalanced src = true := by unfold pnkBalanced; decide +kernel
  have hEmit : emitPnkFun f = some src := by
    simp [emitPnkFun, emitPnkProg, hFunText, hBal, f, guard]
  have hBoth : lowerAndEmitLcnfFun "second" [4, 9] (.return (.bvar 1)) = some (f, src, 9) := by
    simp [lowerAndEmitLcnfFun, hLower, hEmit]
  let s : PanState Unit :=
    { emptyPanState () 0 with locals := FUPDATE (FUPDATE FEMPTY (mkSlot 'v' 1, .word 8)) (mkSlot 'v' 0, .word 3) }
  have hwf : StateWF s := ⟨by decide, fun _ _ _ hc => by cases hc⟩
  have hArgs : EnvMatches (collectTags (.return (.bvar 1))) [.scalar 3, .scalar 8]
      (paramTypes [4, 9]) (wordParams 2) s.locals :=
    .cons (pv := .word 3) (by decide) ⟨by decide, by decide, rfl⟩
      (.cons (pv := .word 8) (by decide) ⟨by decide, by decide, rfl⟩ (.nil _))
  exact ⟨f, src, 9, hBoth,
    lowerAndEmitLcnfFun_sound "second" [4, 9] (.return (.bvar 1)) f src 9 hBoth s
      [.scalar 3, .scalar 8] hwf (Nat.le_refl _) hArgs⟩

end Obend.Lower.Pancake
