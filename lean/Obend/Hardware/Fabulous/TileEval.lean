module
/-
# Obend.Hardware.Fabulous.TileEval — the switch matrix the LEC checks is the one the readback uses

`Obend.Hardware.Fabulous.Tile` gives the switch matrix two readings: `SmPrim.eval`, the selected input
of each primitive at the data level (what `pip_sound` and the grid semantics use), and `smModule`, an
`RtlModule` over the user ports and `ConfigBits` in 64-bit words (what `obend-emit-sv lut4ab-sm` emits and
`hardware/fabulous/lec_tile.sh` proves equal to FABulous's `LUT4AB_switch_matrix.v`).
`smModule_eval_eq_SmPrim_eval` says they compute the same function: for every input vector that
carries the switch-matrix inputs as 0/1 words and the configuration bit by bit, the module's output
for each primitive is that primitive's `SmPrim.eval`. The multiplexer tree (`muxTree`) is handled level
by level (`muxPairs_getD`): level `j` pairs neighbours under select bit `base + j`, and the select
value is read lowest bit first (`selFrom`).
-/
public import Obend.Hardware.Fabulous.Tile
@[expose] public section

namespace Obend.Hardware.Fabulous

open Obend.Hardware.HDL

/-- A bit as a 0/1 word. -/
def boolBV (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

theorem boolBV_ne_zero (b : Bool) : (boolBV b != 0#64) = b := by cases b <;> decide

theorem truncToWidth_one (v : BitVec 64) : truncToWidth 1 v = boolBV (v.getLsbD 0) := by
  have h1 : BitVec.allOnes 64 >>> (64 - 1) = 1#64 := by decide
  rw [truncToWidth, h1, boolBV]
  cases h : v.getLsbD 0 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rcases j with _ | j <;> simp_all

theorem truncToWidth_one_boolBV (b : Bool) : truncToWidth 1 (boolBV b) = boolBV b := by
  cases b <;> decide

/-- Configuration bit `i` of an input vector whose words after the `nIn` user ports hold `ConfigBits`. -/
def cfgBitOf (ins : Nat → BitVec 64) (nIn i : Nat) : Bool := (ins (nIn + i / 64)).getLsbD (i % 64)

theorem eval_cfgBitExpr (ins w r : Nat → BitVec 64) (nIn i : Nat) :
    evalRtlExpr ins w r (cfgBitExpr nIn i) = boolBV (cfgBitOf ins nIn i) := by
  simp only [cfgBitExpr, evalRtlExpr, evalWidthOp, cfgBitOf]
  rw [show i % 64 + 1 - i % 64 = 1 by omega, truncToWidth_one]
  simp

/-- The select value of `k` select bits from `base + j`, lowest first. -/
def selFrom (bit : Nat → Bool) (base : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | j, k + 1 => (if bit (base + j) then 1 else 0) + 2 * selFrom bit base (j + 1) k

theorem selFrom_lt (bit : Nat → Bool) (base : Nat) : ∀ j k, selFrom bit base j k < 2 ^ k
  | _, 0 => by simp [selFrom]
  | j, k + 1 => by
    have := selFrom_lt bit base (j + 1) k
    simp only [selFrom, Nat.pow_succ]
    split <;> omega

theorem length_muxPairs (nIn i : Nat) : ∀ (xs : List RtlExpr) (n : Nat), xs.length = 2 * n →
    (muxPairs nIn i xs).length = n
  | [], n, h => by simp at h; simp [muxPairs]; omega
  | [_], _, h => by simp at h; omega
  | _ :: _ :: rest, n, h => by
    simp only [List.length_cons] at h
    have := length_muxPairs nIn i rest (n - 1) (by omega)
    simp only [muxPairs, List.length_cons]; omega

/-- One level of the tree: entry `m` is entry `2m` or `2m+1` of the level below, by select bit `i`. -/
theorem muxPairs_getD (ins w r : Nat → BitVec 64) (nIn i : Nat) :
    ∀ (xs : List RtlExpr) (m : Nat), 2 * m + 1 < xs.length →
      ((muxPairs nIn i xs).map (evalRtlExpr ins w r)).getD m 0#64 =
        (xs.map (evalRtlExpr ins w r)).getD (2 * m + (if cfgBitOf ins nIn i then 1 else 0)) 0#64
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: rest, 0, _ => by
    simp only [muxPairs, List.map_cons, List.getD_cons_zero, evalRtlExpr, eval_cfgBitExpr, boolBV_ne_zero]
    cases cfgBitOf ins nIn i <;> simp
  | a :: b :: rest, m + 1, h => by
    simp only [List.length_cons] at h
    have := muxPairs_getD ins w r nIn i rest m (by omega)
    simp only [muxPairs, List.map_cons, List.getD_cons_succ] at this ⊢
    rw [this, show 2 * (m + 1) + (if cfgBitOf ins nIn i then 1 else 0) =
      (2 * m + (if cfgBitOf ins nIn i then 1 else 0)) + 1 + 1 by split <;> omega]
    simp only [List.getD_cons_succ]

/-- The multiplexer tree selects entry `selFrom` of its leaves. -/
theorem eval_muxTree (ins w r : Nat → BitVec 64) (nIn base : Nat) :
    ∀ (j k : Nat) (xs : List RtlExpr), xs.length = 2 ^ k →
      evalRtlExpr ins w r (muxTree nIn base j k xs) =
        (xs.map (evalRtlExpr ins w r)).getD (selFrom (cfgBitOf ins nIn) base j k) 0#64
  | j, 0, xs, h => by
    match xs, h with
    | [x], _ => simp [muxTree, selFrom]
  | j, k + 1, xs, h => by
    have hl := length_muxPairs nIn (base + j) xs (2 ^ k) (by rw [h, Nat.pow_succ]; omega)
    have hs := selFrom_lt (cfgBitOf ins nIn) base (j + 1) k
    simp only [muxTree, selFrom]
    rw [eval_muxTree ins w r nIn base (j + 1) k _ hl,
      muxPairs_getD ins w r nIn (base + j) xs _ (by rw [h, Nat.pow_succ]; omega)]
    congr 1; omega

theorem SmPrim.sel_eq_selFrom (p : SmPrim) (cfg : Nat → Bool) :
    p.sel cfg = selFrom cfg p.base 0 p.selBits := by
  cases p with
  | assign s => rfl
  | mux21 ins b =>
    simp only [SmPrim.sel, SmPrim.selBits, SmPrim.base, selFrom]
    cases h0 : cfg b <;> simp [h0]
  | mux41 ins b =>
    simp only [SmPrim.sel, SmPrim.selBits, SmPrim.base, selFrom]
    cases h0 : cfg b <;> cases h1 : cfg (b + 1) <;> simp [List.range_succ, h0, h1]
  | mux81 ins b =>
    simp only [SmPrim.sel, SmPrim.selBits, SmPrim.base, selFrom]
    cases h0 : cfg b <;> cases h1 : cfg (b + 1) <;> cases h2 : cfg (b + 2) <;> simp [List.range_succ, h0, h1, h2]
  | mux161 ins b =>
    simp only [SmPrim.sel, SmPrim.selBits, SmPrim.base, selFrom]
    cases h0 : cfg b <;> cases h1 : cfg (b + 1) <;> cases h2 : cfg (b + 2) <;> cases h3 : cfg (b + 3) <;>
      simp [List.range_succ, h0, h1, h2, h3]

/-! ## Well-formedness and the input encoding -/

/-- Each multiplexer has exactly `2^selBits` inputs, its select bits are configuration bits, and every
input it reads is a port of the switch matrix. `parseSwitchMatrix` refuses the first and last otherwise. -/
def SwitchMatrix.wf (sm : SwitchMatrix) : Bool :=
  sm.prims.all fun (_, p) =>
    (p.selBits == 0 || p.ins.length == 2 ^ p.selBits) && p.base + p.selBits ≤ sm.nCfg &&
      p.ins.all fun s => match s with
        | .port n => sm.inputs.contains n
        | .const _ => true

/-- `ins` carries input `inp` and configuration `cfg` as `smModule sm` reads them: switch-matrix input
`k` as a 0/1 word at index `k`, configuration bit `i` at bit `i % 64` of word `nIn + i / 64`. -/
def SmEncodes (sm : SwitchMatrix) (cfg : Nat → Bool) (inp : String → Bool) (ins : Nat → BitVec 64) : Prop :=
  (∀ k (h : k < sm.inputs.length), ins k = boolBV (inp sm.inputs[k])) ∧
    ∀ i < sm.nCfg, cfgBitOf ins sm.inputs.length i = cfg i

/-- The input vector `obend-emit-sv lut4ab-sm`'s ports take for an input and a configuration. -/
def smIns (sm : SwitchMatrix) (cfg : Nat → Bool) (inp : String → Bool) (k : Nat) : BitVec 64 :=
  if h : k < sm.inputs.length then boolBV (inp sm.inputs[k])
  else
    let wd := k - sm.inputs.length
    (BitVec.ofBoolListLE ((List.range 64).map fun c => decide (64 * wd + c < sm.nCfg) && cfg (64 * wd + c))).setWidth 64

theorem smIns_encodes (sm : SwitchMatrix) (cfg : Nat → Bool) (inp : String → Bool) :
    SmEncodes sm cfg inp (smIns sm cfg inp) := by
  refine ⟨fun k h => by simp [smIns, h], fun i hi => ?_⟩
  have hm : i % 64 < 64 := Nat.mod_lt _ (by omega)
  have hn : ¬ sm.inputs.length + i / 64 < sm.inputs.length := by omega
  simp only [cfgBitOf, smIns, hn, dite_false, Nat.add_sub_cancel_left, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  have : 64 * (i / 64) + i % 64 = i := Nat.div_add_mod i 64
  simp [this, hi, hm]

theorem eval_SmSrc_expr (sm : SwitchMatrix) (cfg : Nat → Bool) (inp : String → Bool) (ins w r : Nat → BitVec 64)
    (hE : SmEncodes sm cfg inp ins) (s : SmSrc)
    (hs : match s with | .port n => sm.inputs.contains n = true | .const _ => True) :
    evalRtlExpr ins w r (s.expr sm) = boolBV (s.eval inp) := by
  cases s with
  | const b => cases b <;> rfl
  | port n =>
    simp only [List.contains_iff_mem] at hs
    obtain ⟨i, hi⟩ : ∃ i, sm.inputs.idxOf? n = some i := by
      cases h : sm.inputs.idxOf? n with
      | none => exact absurd hs (by simpa using h)
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hlt, hget, _⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [SmSrc.expr, evalRtlExpr, SwitchMatrix.inputIdx, hi, Option.getD_some, SmSrc.eval,
      hE.1 _ hlt, hget]

theorem selFrom_congr (b1 b2 : Nat → Bool) (base : Nat) :
    ∀ j k, (∀ c < k, b1 (base + j + c) = b2 (base + j + c)) → selFrom b1 base j k = selFrom b2 base j k
  | _, 0, _ => rfl
  | j, k + 1, h => by
    simp only [selFrom]
    rw [show b1 (base + j) = b2 (base + j) from h 0 (by omega),
      selFrom_congr b1 b2 base (j + 1) k (fun c hc => by
        have := h (c + 1) (by omega); rwa [show base + j + (c + 1) = base + (j + 1) + c by omega] at this)]

/-- Every primitive's expression computes its `SmPrim.eval`, as a 0/1 word. -/
theorem eval_SmPrim_expr (sm : SwitchMatrix) (cfg : Nat → Bool) (inp : String → Bool) (ins w r : Nat → BitVec 64)
    (hE : SmEncodes sm cfg inp ins) (p : SmPrim)
    (hLen : (p.selBits == 0 || p.ins.length == 2 ^ p.selBits) = true) (hBase : p.base + p.selBits ≤ sm.nCfg)
    (hPorts : ∀ s ∈ p.ins, match s with | .port n => sm.inputs.contains n = true | .const _ => True) :
    evalRtlExpr ins w r (p.expr sm) = boolBV (p.eval cfg inp) := by
  have hSrc := fun s (hs : s ∈ p.ins) => eval_SmSrc_expr sm cfg inp ins w r hE s (hPorts s hs)
  cases p with
  | assign s =>
    simp only [SmPrim.expr, SmPrim.eval, SmPrim.sel, SmPrim.selBits, List.range_zero, List.map_nil,
      List.sum_nil, SmPrim.ins]
    simp [hSrc s (by simp [SmPrim.ins])]
  | _ xs b =>
    simp only [SmPrim.selBits, SmPrim.ins, SmPrim.base, beq_iff_eq, Bool.or_eq_true, ] at hLen hBase hPorts hSrc ⊢
    simp only [false_or, reduceCtorEq] at hLen
    rw [SmPrim.eval, SmPrim.sel_eq_selFrom]
    simp only [SmPrim.expr, SmPrim.selBits, SmPrim.base, SmPrim.ins]
    rw [eval_muxTree ins w r _ b 0 _ _ (by simp [hLen])]
    rw [selFrom_congr (cfgBitOf ins sm.inputs.length) cfg b 0 _ (fun c hc => hE.2 _ (by omega))]
    have hlt := selFrom_lt cfg b 0
    rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map]
    first
    | (have hs := hlt 1; rw [← hLen] at hs)
    | (have hs := hlt 2; rw [← hLen] at hs)
    | (have hs := hlt 3; rw [← hLen] at hs)
    | (have hs := hlt 4; rw [← hLen] at hs)
    rw [List.getElem?_eq_getElem hs]
    simp only [Option.map_some, Option.getD_some, Function.comp]
    exact hSrc _ (List.getElem_mem hs)

/-- The wire table of `smModule`: wire `k` is primitive `k`'s value. -/
theorem foldl_smWires (sm : SwitchMatrix) (ins regs : Nat → BitVec 64) (val : String × SmPrim → BitVec 64)
    (hv : ∀ q ∈ sm.prims, ∀ env, evalRtlExpr ins env regs (q.2.expr sm) = val q) :
    ∀ (L : List (String × SmPrim)) (n : Nat) (e : Nat → BitVec 64), (∀ q ∈ L, q ∈ sm.prims) → ∀ i,
      (((L.zipIdx n).map fun ((o, p), k) => ({ wireIdx := k, name := o, width := 1, expr := p.expr sm } : WireAssign)).foldl
        (fun (env : Nat → BitVec 64) a =>
          let v := evalRtlExpr ins env regs a.expr
          fun i => if i == a.wireIdx then v else env i) e) i =
        if n ≤ i then ((L[i - n]?).map val).getD (e i) else e i
  | [], n, e, _, i => by simp
  | q :: L, n, e, hL, i => by
    simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons]
    rw [foldl_smWires sm ins regs val hv L (n + 1) _ (fun q h => hL q (List.mem_cons_of_mem _ h)) i]
    simp only [hv q (hL q (List.mem_cons_self ..))]
    rcases Nat.lt_trichotomy i n with h | h | h
    · have h1 : ¬ n + 1 ≤ i := by omega
      have h2 : ¬ n ≤ i := by omega
      have h3 : (i == n) = false := by simp; omega
      simp [h1, h2, h3]
    · subst h; simp; omega
    · have h1 : n + 1 ≤ i := by omega
      have h3 : (i == n) = false := by simp; omega
      rw [show i - n = (i - (n + 1)) + 1 by omega]
      simp [h1, h3, show n ≤ i by omega]

/-- **The LEC'd module is the data-level switch matrix.** For a well-formed switch matrix and any input
vector carrying the switch-matrix inputs `inp` and configuration `cfg` (`SmEncodes`; `smIns` is one),
`smModule`'s outputs are, primitive by primitive, `SmPrim.eval cfg inp` as 0/1 words. -/
theorem smModule_eval_eq_SmPrim_eval (sm : SwitchMatrix) (hWF : sm.wf = true) (cfg : Nat → Bool)
    (inp : String → Bool) (ins regs : Nat → BitVec 64) (hE : SmEncodes sm cfg inp ins) :
    evalModuleOutputsW (smModule sm) ins regs = sm.prims.map fun (o, p) => (o, boolBV (p.eval cfg inp)) := by
  have hP : ∀ q ∈ sm.prims, ∀ env, evalRtlExpr ins env regs (q.2.expr sm) = boolBV (q.2.eval cfg inp) := by
    intro q hq env
    have h := List.all_eq_true.mp hWF q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact eval_SmPrim_expr sm cfg inp ins env regs hE q.2 h.1.1 h.1.2 (fun s hs => by
      have := h.2 s hs
      cases s with
      | port n => simpa using this
      | const _ => trivial)
  have hW := foldl_smWires sm ins regs (fun q => boolBV (q.2.eval cfg inp)) hP sm.prims 0 (fun _ => 0#64)
    (fun _ h => h)
  simp only [evalModuleOutputsW, smModule, evalWireTable]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, evalRtlExpr, Nat.zero_add]
  simp only [List.length_map, List.length_zipIdx] at h1
  rw [hW i]
  simp [List.getElem?_eq_getElem h1, truncToWidth_one_boolBV]

end Obend.Hardware.Fabulous
