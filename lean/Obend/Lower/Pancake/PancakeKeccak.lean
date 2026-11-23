module
public import Obend.Lower.Pancake.EmitPnk
import all Obend.Lower.Pancake.EmitPnk
public import Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.PanSem
import all Obend.Digest.Cshake256.Spec

public section
namespace Obend.Lower.Pancake
open WordBuffer
namespace Keccak
open Obend.Digest

private def idx (x y : Nat) : Fin 25 :=
  ⟨x%5 + 5*(y%5), by
    have := Nat.mod_lt x (by decide : 0 < 5)
    have := Nat.mod_lt y (by decide : 0 < 5)
    omega⟩

private def col (x : Nat) : Expr :=
  (List.range 5).foldl (fun acc y => .xor acc (.lane (idx x y))) (.lit 0)

def thetaStage (i : Fin 25) : Expr :=
  let x := i.val % 5
  .xor (.xor (.lane i) (col (x+4))) (.rot (col (x+1)) 1)

/-- Invert the pi coordinate map to generate the source of each output lane. -/
def rhoPiStage (i : Fin 25) : Expr :=
  let y := i.val % 5
  let x := (3*(i.val/5) + y) % 5
  .rot (.lane (idx x y)) ⟨Cshake256.rotationOffset x y % 64, Nat.mod_lt _ (by decide)⟩

def chiIotaStage (rc : Word) (i : Fin 25) : Expr :=
  let x := i.val % 5
  let y := i.val / 5
  let a := Expr.lane (idx (x+1) y)
  let z := Expr.xor (.lane i) (.and (.xor a (.lit (BitVec.allOnes 64))) (.lane (idx (x+2) y)))
  if i.val = 0 then .xor z (.lit rc) else z

def lanes (s : Cshake256.State) (i : Fin 25) := s.getD i.val Cshake256.zeroLane

private theorem read_xy (s : Cshake256.State) (x y : Nat) :
    lanes s (idx x y) = Cshake256.lane s x y := rfl

private theorem read_self (s : Cshake256.State) (i : Fin 25) :
    lanes s i = Cshake256.lane s (i.val%5) (i.val/5) := by
  unfold lanes Cshake256.lane
  congr 1
  have := i.isLt
  omega

private theorem read_ofFn (f : Fin 25 → Word) (i : Fin 25) :
    lanes (Array.ofFn f) i = f i := by
  simp [lanes, Array.getD_eq_getD_getElem?, i.isLt]

private theorem col_value (s : Cshake256.State) (x : Nat) :
    Expr.value (lanes s) (col x) = Cshake256.xorColumn s x := by
  unfold col Cshake256.xorColumn
  generalize List.range 5 = ys
  suffices ∀ e : Expr, Expr.value (lanes s)
      (ys.foldl (fun acc y => acc.xor (.lane (idx x y))) e) =
      ys.foldl (fun acc y => acc ^^^ Cshake256.lane s x y) (Expr.value (lanes s) e) from this _
  induction ys with
  | nil => intro e; rfl
  | cons y ys ih => intro e; simp only [List.foldl_cons, ih, Expr.value, read_xy]

private theorem theta_agrees (s : Cshake256.State) (i : Fin 25) :
    runStage thetaStage (lanes s) i = lanes (Cshake256.theta s) i := by
  rw [Cshake256.theta, read_ofFn]
  simp only [runStage, thetaStage, Expr.value, col_value, read_self]
  rfl

private def srcX (i : Fin 25) := (3*(i.val/5) + i.val%5)%5

private theorem source_coordinates : ∀ i : Fin 25,
    Cshake256.Fast.rpSource i.val % 5 = srcX i ∧ Cshake256.Fast.rpSource i.val / 5 = i.val%5 := by decide

private theorem rhoPi_agrees (s : Cshake256.State) (i : Fin 25) :
    runStage rhoPiStage (lanes s) i = lanes (Cshake256.rhoPi s) i := by
  change (lanes s (idx (srcX i) (i.val%5))).rotateLeft _ = _
  rw [read_xy, lanes, Array.getD_eq_getD_getElem?, Cshake256.Fast.rhoPi_getElem? s i i.isLt]
  simp only [Option.getD_some, Cshake256.Fast.rpValue, (source_coordinates i).1,
    (source_coordinates i).2, srcX, BitVec.rotateLeft, Nat.mod_mod]

private def chiIota (s : Cshake256.State) (rc : Word) :=
  let mixed := Cshake256.chi s
  mixed.setIfInBounds 0 (Cshake256.lane mixed 0 0 ^^^ rc)

private theorem chi_lane (s : Cshake256.State) (i : Fin 25) :
    lanes (Cshake256.chi s) i = lanes s i ^^^
      ((~~~Cshake256.lane s (i.val%5+1) (i.val/5)) &&& Cshake256.lane s (i.val%5+2) (i.val/5)) := by
  rw [Cshake256.chi, read_ofFn, read_self s]

private theorem at_zero (s : Cshake256.State) (v : Word) (h : 0 < s.size) :
    lanes (s.setIfInBounds 0 v) 0 = v := by
  simp [lanes, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]

private theorem at_other (s : Cshake256.State) (v : Word) (i : Fin 25) (h : 0 ≠ i.val) :
    lanes (s.setIfInBounds 0 v) i = lanes s i := by
  simp only [lanes, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

private theorem chiIota_agrees (s : Cshake256.State) (rc : Word) (i : Fin 25) :
    runStage (chiIotaStage rc) (lanes s) i = lanes (chiIota s rc) i := by
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext h
    subst i
    have hz : 0 < (Cshake256.chi s).size := by simp [Cshake256.chi]
    have lr : Cshake256.lane (Cshake256.chi s) 0 0 = lanes (Cshake256.chi s) 0 := rfl
    simp only [runStage, chiIotaStage, chiIota, h, ↓reduceIte, Expr.value, read_xy,
      BitVec.xor_allOnes, at_zero _ _ hz, lr, chi_lane]
  · simp only [runStage, chiIotaStage, chiIota, h, ↓reduceIte, Expr.value, read_xy,
      BitVec.xor_allOnes, at_other _ _ i (Ne.symm h), chi_lane]

def roundsThen (p : String) (next : PStmt) : List Word → PStmt
  | [] => next
  | rc :: cs => .seq (lowerStage p thetaStage)
      (.seq (lowerStage p rhoPiStage) (.seq (lowerStage p (chiIotaStage rc)) (roundsThen p next cs)))

def rounds (p : String) := roundsThen p (.ret (.const 0))

def roundFunction (cs : List Word) : PFun :=
  ⟨"keccakF1600", [("base", .One)], rounds "base" cs, true⟩

def kernel : PFun := roundFunction Cshake256.roundConstants

/-- The same array specification used by Obend's cSHAKE256 implementation. -/
abbrev keccakF1600Words := Cshake256.keccakF1600

private theorem stage_step {τ : Type} (s : PanState τ) (p : String) (b : Word)
    (hp : s.locals p = some (.word b)) (hm : Mapped s b)
    (src dst : Cshake256.State) (reads : ∀ i : Fin 25, s.memory (address b i) = lanes src i)
    (f : Stage) (law : ∀ i, runStage f (lanes src) i = lanes dst i) :
    ∃ m, evaluate (lowerStage p f) s = (.normal, {s with memory := m}) ∧
      (∀ i : Fin 25, m (address b i) = lanes dst i) ∧
      ∀ a, (∀ i : Fin 25, a ≠ address b i) → m a = s.memory a := by
  obtain ⟨m, he, hr, hf⟩ := lowerStage_correct s p b hp hm f
  refine ⟨m, he, fun i => ?_, hf⟩
  rw [hr, funext reads, law]

private theorem seq3_eval {τ : Type} {st₁ st₂ st₃ rest : PStmt} {s t : PanState τ} {m₁ m₂ m₃ : Word → Word} {res : PanResult}
    (h₁ : evaluate st₁ s = (.normal, { s with memory := m₁ }))
    (h₂ : evaluate st₂ { s with memory := m₁ } = (.normal, { s with memory := m₂ }))
    (h₃ : evaluate st₃ { s with memory := m₂ } = (.normal, { s with memory := m₃ }))
    (h₄ : evaluate rest { s with memory := m₃ } = (res, t)) :
    evaluate (.seq st₁ (.seq st₂ (.seq st₃ rest))) s = (res, t) := by
  rw [evaluate_seq, h₁]
  change evaluate (.seq st₂ (.seq st₃ rest)) { s with memory := m₁ } = (res, t)
  rw [evaluate_seq, h₂]
  change evaluate (.seq st₃ rest) { s with memory := m₂ } = (res, t)
  rw [evaluate_seq, h₃]
  exact h₄

private theorem chiIota_eq_round (src : Cshake256.State) (rc : Word) :
    chiIota (Cshake256.rhoPi (Cshake256.theta src)) rc = Cshake256.round src rc := by
  unfold chiIota Cshake256.round; rfl

theorem roundsThen_correct {τ : Type} (cs : List Word) (s : PanState τ) (p : String) (next : PStmt)
    (b : Word) (hp : s.locals p = some (.word b)) (hm : Mapped s b)
    (src : Cshake256.State) (reads : ∀ i : Fin 25, s.memory (address b i) = lanes src i) :
    ∃ m, evaluate (roundsThen p next cs) s = evaluate next {s with memory := m} ∧
      (∀ i : Fin 25, m (address b i) = lanes (cs.foldl Cshake256.round src) i) ∧
      ∀ a, (∀ i : Fin 25, a ≠ address b i) → m a = s.memory a := by
  induction cs generalizing s src with
  | nil =>
    exact ⟨s.memory, rfl, reads, fun _ _ => rfl⟩
  | cons rc cs ih =>
    obtain ⟨m₁, h₁, r₁, f₁⟩ := stage_step s p b hp hm src (Cshake256.theta src) reads thetaStage (theta_agrees src)
    obtain ⟨m₂, h₂, r₂, f₂⟩ := stage_step {s with memory := m₁} p b hp hm (Cshake256.theta src) (Cshake256.rhoPi (Cshake256.theta src)) r₁ rhoPiStage
      (rhoPi_agrees _)
    obtain ⟨m₃, h₃, r₃, f₃⟩ := stage_step {s with memory := m₂} p b hp hm (Cshake256.rhoPi (Cshake256.theta src)) (Cshake256.round src rc) r₂ (chiIotaStage rc)
      (fun i => (chiIota_agrees _ rc i).trans (by rw [chiIota_eq_round]))
    obtain ⟨t, ht, rt, ft⟩ := ih {s with memory := m₃} hp hm (Cshake256.round src rc) r₃
    simp only [List.foldl_cons, roundsThen]
    refine ⟨t, ?_, rt, fun a ha => (ft a ha).trans ((f₃ a ha).trans ((f₂ a ha).trans (f₁ a ha)))⟩
    generalize hu : evaluate next {s with memory := t} = result
    cases result with
    | mk res u => exact seq3_eval h₁ h₂ h₃ (ht.trans hu)

/-- All 24 rounds, for any mapped input buffer, preserving every other memory address. -/
theorem pancakeKeccakF1600_correct {τ : Type} (s : PanState τ) (b : Word) (src : Cshake256.State)
    (hp : s.locals "base" = some (.word b)) (hm : Mapped s b)
    (reads : ∀ i : Fin 25, s.memory (address b i) = lanes src i) :
    ∃ t, evaluate kernel.body s = (.ret (.word 0), t) ∧
      (∀ i : Fin 25, t.memory (address b i) = lanes (keccakF1600Words src) i) ∧
      ∀ a, (∀ i : Fin 25, a ≠ address b i) → t.memory a = s.memory a := by
  obtain ⟨m, h, r, f⟩ := roundsThen_correct Cshake256.roundConstants s "base" (.ret (.const 0)) b hp hm src reads
  exact ⟨_, h.trans (evaluate_ret _ _), r, f⟩

/-- Concrete syntax of a straight-line buffer kernel. Each store takes exactly 25
    grammatical word expressions; the final statement returns a word. -/
inductive BodyText : String → Prop where
  | done (w : Word) : BodyText ("return " ++ toString w.toNat ++ ";\n")
  | stage (xs : Fin 25 → String) {rest : String}
      (fields : ∀ i, WordText "base" (xs i)) (cont : BodyText rest) :
      BodyText (("st base, < " ++ String.intercalate ", " ((List.finRange 25).map xs) ++ " >;\n") ++ rest)

private def printed (f : Stage) (i : Fin 25) := (emitWordExpr "base" (f i)).getD ""

private theorem printed_field (f : Stage) (i : Fin 25) :
    exprText ["base"] ((f i).lower "base") = some (printed f i) ∧ WordText "base" (printed f i) := by
  obtain ⟨s, h, hg⟩ := emitWordExpr_grammar (f i) "base" (by unfold pnkIdentifier; decide +kernel)
  change emitWordExpr "base" (f i) = some _ ∧ _
  simp only [printed, h, Option.getD_some, true_and, hg]

private theorem printed_fields (f : Stage) (is : List (Fin 25)) :
    exprsText ["base"] (is.map fun i => (f i).lower "base") = some (is.map (printed f)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [exprsText, (printed_field f i).1, ih]

private theorem print_stage (f : Stage) :
    stmtText ["base"] (lowerStage "base" f) =
      some ("st base, < " ++ String.intercalate ", " ((List.finRange 25).map (printed f)) ++ " >;\n") := by
  have hv : scopedVar ["base"] .Local "base" = some "base" := by unfold scopedVar pnkIdentifier; decide +kernel
  have tuple (e : PExp) (es : List PExp) :
      exprText ["base"] (.rstruct (e::es)) =
      (exprsText ["base"] (e::es)).map (fun ss => "< " ++ String.intercalate ", " ss ++ " >") := by
    simp only [exprText]
    cases exprsText ["base"] (e::es) <;> rfl
  have ne : ((List.finRange 25).map fun i => (f i).lower "base") ≠ [] := by simp only [ne_eq, List.map_eq_nil_iff]; decide
  have htuple : ∀ es : List PExp, es ≠ [] → exprText ["base"] (.rstruct es) =
      (exprsText ["base"] es).map (fun ss => "< " ++ String.intercalate ", " ss ++ " >") := by
    rintro (_ | ⟨e,es⟩) h
    · contradiction
    · exact tuple e es
  simp [lowerStage, stmtText, htuple _ ne, printed_fields, exprText, hv, ← String.append_assoc]
  simp [String.append_assoc]

private theorem rounds_grammar (cs : List Word) :
    ∃ body, stmtText ["base"] (rounds "base" cs) = some body ∧ BodyText body := by
  induction cs with
  | nil => exact ⟨_, rfl, .done 0⟩
  | cons rc cs ih =>
    obtain ⟨s, hs, grammar⟩ := ih
    refine ⟨_, ?_, .stage _ (fun i => (printed_field thetaStage i).2)
      (.stage _ (fun i => (printed_field rhoPiStage i).2)
        (.stage _ (fun i => (printed_field (chiIotaStage rc) i).2) grammar))⟩
    change stmtText ["base"] (.seq _ (.seq _ (.seq _ (rounds "base" cs)))) = _
    simp [stmtText, print_stage, hs]

/-- Grammar derivation for the actual emitted function, down to every lane expression. -/
theorem kernel_text_grammar (cs : List Word) {src : String} (h : emitPnkFun (roundFunction cs) = some src) :
    ∃ body, BodyText body ∧ src = "export fun keccakF1600(1 base) {\n" ++ body ++ "}\n" := by
  obtain ⟨body, hb, hg⟩ := rounds_grammar cs
  refine ⟨body, hg, ?_⟩
  have header : funText (roundFunction cs) = some ("export fun keccakF1600(1 base) {\n" ++ body ++ "}\n") := by
    have baseOK : pnkIdentifier "base" = some "base" := by unfold pnkIdentifier; decide +kernel
    have nameOK : pnkIdentifier "keccakF1600" = some "keccakF1600" := by unfold pnkIdentifier; decide +kernel
    simp [funText, roundFunction, shapeText, baseOK, nameOK, hb, block, guard, ← String.append_assoc]
    simp [String.append_assoc]
  simp [emitPnkFun, emitPnkProg, guard, header] at h
  exact h.2.symm

end Keccak
end Obend.Lower.Pancake
