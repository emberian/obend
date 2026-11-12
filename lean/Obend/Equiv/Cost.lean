module
/- `≈c` and `mix_assoc_cost`. `Sim` (`Obend.Equiv.Improvement`) is a cost simulation: a clairvoyant
derivation of cost `k` of one side is matched by a derivation of the other of cost at most `8k`
(and at most `8k - 7` when `k > 0`), with related results (`sim_cv`). The two association cases are
where the work is: the left body `c s ((mix a b) s u)` binds `self` twice (for `c`, and for
`mix a b`, which shares it between `b` and `a`); the right body `(mix b c) s (a s u)` shares it
between `c` and `b` and binds it again for `a`. Every binding is moved out of its application
(`hoist_arg`, `hoist_fun`), matched on the other side, and moved back (`unhoist_arg`,
`unhoist_fun`).

`CostWithin A t t'` is Moran and Sands' improvement within a constant factor (Def. 4.1) for the
clairvoyant semantics: for every substitution and context, a derivation of `C[t]` of cost `k` gives
one of `C[t']` of cost at most `A * k`, with the same result if it is a literal. `t ≈c t'` asks it in
both directions. `mix_assoc_cost`: the two associations of `mix` are within a factor of 8 of each
other in every context. The factor is a constant, not an additive bound: a context that applies
the association `n` times pays the per-application difference `n` times. -/
public import Obend.Equiv.Improvement
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Clairvoyant
public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

/-! ## Inversions of `Sim` at value forms -/

theorem sim_lam_inv {b w : Term} (h : Sim (.lam b) w) : ∃ b', w = .lam b' ∧ Sim b b' := by
  cases h with | lam h => exact ⟨_, rfl, h⟩

theorem sim_record_inv {fs : List (String × Term)} {w : Term} (h : Sim (.record fs) w) :
    ∃ fs', w = .record fs' ∧ fs.map Prod.fst = fs'.map Prod.fst ∧ ∀ p ∈ fs.zip fs', Sim p.1.2 p.2.2 := by
  cases h with | record names rel => exact ⟨_, rfl, names, rel⟩

theorem sim_spec_inv {m e w : Term} (h : Sim (.specification m e) w) :
    ∃ m' e', w = .specification m' e' ∧ Sim m m' ∧ Sim e e' := by
  cases h with | specification h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

theorem sim_proto_inv {s g w : Term} (h : Sim (.prototype s g) w) :
    ∃ s' g', w = .prototype s' g' ∧ Sim s s' ∧ Sim g g' := by
  cases h with | prototype h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

theorem sim_inject_inv {l : String} {p w : Term} (h : Sim (.inject l p) w) : ∃ p', w = .inject l p' ∧ Sim p p' := by
  cases h with | inject _ h1 => exact ⟨_, rfl, h1⟩

theorem sim_literal_inv {v w : Term} (lit : Literal v) (h : Sim v w) : w = v := by
  cases lit <;> cases h <;> rfl

theorem cv_app_pos {r : Tail} {f a v : Term} {k : Nat} (h : Run (.tail r) (.app f a) v k) : 1 ≤ k := by
  cases h with
  | value h => exact absurd h app_not_ready
  | apply => omega
  | applySpec => omega
  | headEval h =>
    cases h with
    | value h => exact absurd h app_not_ready
    | apply => omega
    | applySpec => omega

theorem sim_mixBody {l l' u u' : Term} (hl : Sim l l') (hu : Sim u u') :
    Sim (mixBody l u) (mixBody l' u') :=
  .lam (.lam (.app (.app (hu.rename _) (.bound 1)) (.app (.app (hl.rename _) (.bound 1)) (.bound 0))))

theorem sim_selfBody {s s' i i' : Term} (hs : Sim s s') (hi : Sim i i') :
    Sim (selfBody s i) (selfBody s' i') :=
  .app (.app (hs.rename _) (.bound 0)) (hi.rename _)

theorem sim_knot {V V' : Term} (h : Sim V V') : Sim (knot V) (knot V') :=
  .fix (.lam (.lam (h.rename _))) (.refl _)

theorem sim_single {x x' : Term} (h : Sim x x') : ∀ n, Sim (single x n) (single x' n)
  | 0 => h
  | n + 1 => .bound n

/-! ## The bound -/

/-- The cost `k'` on the right is within a factor of 8 of the cost `k` on the left, and 7 less
than `8k` when `k > 0`. -/
@[expose] def Within (k k' : Nat) : Prop := k' + 7 * min k 1 ≤ 8 * k

theorem Within.add {a a' b b' : Nat} (h1 : Within a a') (h2 : Within b b') : Within (a + b) (a' + b') := by
  unfold Within at *; omega

theorem Within.zero : Within 0 0 := by simp [Within]

/-- The simulation, for every evaluation or template derivation cheaper than `n`. -/
@[expose] def SimBelow (n : Nat) : Prop :=
  ∀ (r : Tail), ∀ j < n, ∀ {t t' v : Term}, Sim t t' → Run (.tail r) t v j →
    ∃ v' j', Run (.tail r) t' v' j' ∧ Sim v v' ∧ Within j j'

theorem bind_sim {n j : Nat} (ih : SimBelow n) (hj : j ≤ n) {a a' x : Term} (h : Run .bind a x j)
    (hs : Sim a a') : ∃ x' j', Run .bind a' x' j' ∧ Sim x x' ∧ Within j j' := by
  cases h with
  | keep hset => exact ⟨a', 0, .keep (Sim.ready_fwd hset hs), hs, by simp [Within]⟩
  | skip => exact ⟨skipped, 1, .skip _, .refl _, by simp [Within]⟩
  | eval hn e =>
    obtain ⟨v', j', r, sv, b⟩ := ih .eval _ (by omega) hs e
    exact ⟨v', j' + 1, .eval (fun c => hn (Sim.ready_bwd c hs)) r, sv, by unfold Within at *; omega⟩

theorem fields_sim {n : Nat} (ih : SimBelow n) :
    ∀ {fs fs' gs : List (String × Term)} {j : Nat}, Run .fields (.record fs) (.record fs') j → j ≤ n →
      fs.map Prod.fst = gs.map Prod.fst → (∀ p ∈ fs.zip gs, Sim p.1.2 p.2.2) →
      ∃ gs' j', Run .fields (.record gs) (.record gs') j' ∧ fs'.map Prod.fst = gs'.map Prod.fst ∧
        (∀ p ∈ fs'.zip gs', Sim p.1.2 p.2.2) ∧ Within j j'
  | [], fs', gs, j, h, hj, names, _ => by
    cases h
    cases gs with
    | nil => exact ⟨[], 0, .nil, rfl, by simp, by simp [Within]⟩
    | cons _ _ => simp at names
  | (n0, t) :: fs, fs', gs, j, h, hj, names, rel => by
    cases h with
    | cons hb hr =>
      cases gs with
      | nil => simp at names
      | cons g gs =>
        obtain ⟨gn, gt⟩ := g
        simp only [List.map_cons, List.cons.injEq] at names
        obtain ⟨rfl, names⟩ := names
        have relHead : Sim t gt := rel ((n0, t), (n0, gt)) (by simp)
        have relTail : ∀ p ∈ fs.zip gs, Sim p.1.2 p.2.2 := fun p hp => rel p (by simp [hp])
        obtain ⟨x', j1, r1, s1, b1⟩ := bind_sim ih (by omega) hb relHead
        obtain ⟨gs', j2, r2, n2, s2, b2⟩ := fields_sim ih hr (by omega) names relTail
        refine ⟨(n0, x') :: gs', _, .cons r1 r2, by simp [n2], ?_, by unfold Within at *; omega⟩
        intro p hp
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact s1
        · exact s2 p hp

/-- A `self` bound twice in a row on one side, once on the other. -/
theorem bind2_settled {s s' s2 x : Term} {k1 k2 : Nat} (hset : Settled s) (hs : Sim s s')
    (h1 : Run .bind s s2 k1) (h2 : Run .bind s2 x k2) :
    ∃ x' k', Run .bind s' x' k' ∧ Sim x x' ∧ k' ≤ k1 + k2 := by
  have hset' : Settled s' := Sim.ready_fwd hset hs
  rcases bind_of_settled hset h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases bind_of_settled hset h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨s', 0, .keep hset', hs, by omega⟩
    · exact ⟨skipped, 1, .skip _, .refl _, by omega⟩
  · rcases bind_of_settled .skipped h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨skipped, 1, .skip _, .refl _, by omega⟩
    · exact ⟨skipped, 1, .skip _, .refl _, by omega⟩

/-- An argument bound twice in a row on one side (its value is then kept or skipped), once on
the other. -/
theorem bind2_sim {n : Nat} (ih : SimBelow n) {u u' u1 x : Term} {k1 k2 : Nat} (hk : k1 ≤ n)
    (h1 : Run .bind u u1 k1) (h2 : Run .bind u1 x k2) (hs : Sim u u') :
    ∃ x' k', Run .bind u' x' k' ∧ Sim x x' ∧ Within (k1 + k2) k' := by
  rcases bind_of_settled (bind_settled h1) h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨x', k', r, sx, b⟩ := bind_sim ih hk h1 hs
    exact ⟨x', k', r, sx, by simpa using b⟩
  · exact ⟨skipped, 1, .skip _, .refl _, by unfold Within; omega⟩

/-! ## The association cases -/

theorem bodyLR_case {r : Tail} {n : Nat} (ih : SimBelow n) {a a' b b' c c' s s' u u' v : Term}
    (hset : Settled s) (ha : Sim a a') (hb : Sim b b') (hc : Sim c c') (hss : Sim s s') (hu : Sim u u')
    (h : Run (.tail r) (.app (.app c s) (.app (.app (.mix a b) s) u)) v n) :
    ∃ v' n', Run (.tail r) (.app (.app (.mix b' c') s') (.app (.app a' s') u')) v' n' ∧ Sim v v' ∧ Within n n' := by
  have hset' : Settled s' := Sim.ready_fwd hset hss
  obtain ⟨x, kx, k1, hX, hC, rfl⟩ := hoist_arg h
  have k1pos := cv_app_pos hC
  rcases bind_of_unsettled app_not_ready hX with ⟨rfl, rfl⟩ | ⟨j, hXr, rfl⟩
  · -- `mix a b` is skipped: the right skips `a s u` and `b s _`, and pays only the unfolding
    obtain ⟨v', k1', r1, s1, b1⟩ := ih r k1 (by omega) (.app (.app hc hss) (.refl _)) hC
    obtain ⟨K, rK, le⟩ := unhoist_arg (Run.skip (Term.app (.app b' s') skipped)) r1
    have run := mk_mix_app_app (Run.keep hset') (Run.skip (Term.app (.app a' s') u')) rK
    exact ⟨v', _, run, s1, by unfold Within at *; omega⟩
  · obtain ⟨s2, ks, u1, ku, kb, hS, hU, hB, rfl⟩ := cv_mix_app_app_eval hXr
    obtain ⟨y, ky, k4, hY, hB2, rfl⟩ := hoist_arg hB
    obtain ⟨xb, kxb, k4', hXb, hB3, rfl⟩ := hoist_fun hB2
    obtain ⟨xb', kxb', hXb', sxb, lxb⟩ := bind2_settled hset hss hS hXb
    -- the argument `a s u` on the right, matching `a s₂ u₁` on the left
    have yside : ∃ y' ky', Run .bind (Term.app (.app a' s') u') y' ky' ∧ Sim y y' ∧
        ky' + 7 * min (ku + ky) 1 ≤ 8 * (ku + ky) + ks := by
      rcases bind_of_unsettled app_not_ready hY with ⟨rfl, rfl⟩ | ⟨jy, hYr, rfl⟩
      · exact ⟨skipped, 1, .skip _, .refl _, by omega⟩
      · obtain ⟨xa, kxa, j1, hXa, hA1, rfl⟩ := hoist_fun hYr
        obtain ⟨xu, kxu, j2, hXu, hA2, rfl⟩ := hoist_arg hA1
        obtain ⟨xa', kxa', hXa', sxa, lxa⟩ := bind2_settled hset hss hS hXa
        obtain ⟨xu', kxu', hXu', sxu, bxu⟩ := bind2_sim ih (by omega) hU hXu hu
        obtain ⟨y', j2', r2, sy, by2⟩ := ih .eval j2 (by omega) (.app (.app ha sxa) sxu) hA2
        have j2pos := cv_app_pos hA2
        obtain ⟨K1, rK1, le1⟩ := unhoist_arg hXu' r2
        obtain ⟨K2, rK2, le2⟩ := unhoist_fun hXa' rK1
        exact ⟨y', K2 + 1, .eval app_not_ready rK2, sy, by unfold Within at *; omega⟩
    obtain ⟨y', ky', hY', sy, by'⟩ := yside
    -- the argument `b s y` on the right, matching `mix a b` applied on the left
    obtain ⟨z, k4'', rz, sz, bz⟩ := ih .eval k4' (by omega) (.app (.app hb sxb) sy) hB3
    obtain ⟨Kb, rKb, leb⟩ := unhoist_fun hXb' rz
    have hZ' : Run .bind (Term.app (.app b' s') y') z (Kb + 1) := .eval app_not_ready rKb
    obtain ⟨v', k1', r1, s1, b1⟩ := ih r k1 (by omega) (.app (.app hc hss) sz) hC
    obtain ⟨K, rK, le⟩ := unhoist_arg hZ' r1
    have run := mk_mix_app_app (Run.keep hset') hY' rK
    have hBpos := cv_app_pos hB3
    exact ⟨v', _, run, s1, by unfold Within at *; omega⟩

theorem bodyRL_case {r : Tail} {n : Nat} (ih : SimBelow n) {a a' b b' c c' s s' u u' v : Term}
    (hset : Settled s) (ha : Sim a a') (hb : Sim b b') (hc : Sim c c') (hss : Sim s s') (hu : Sim u u')
    (h : Run (.tail r) (.app (.app (.mix b c) s) (.app (.app a s) u)) v n) :
    ∃ v' n', Run (.tail r) (.app (.app c' s') (.app (.app (.mix a' b') s') u')) v' n' ∧ Sim v v' ∧ Within n n' := by
  have hset' : Settled s' := Sim.ready_fwd hset hss
  obtain ⟨s2, ks, y, ky, kb, hS, hY, hB, rfl⟩ := cv_mix_app_app h
  obtain ⟨z, kz, k1, hZ, hC, rfl⟩ := hoist_arg hB
  obtain ⟨xc, kxc, k1', hXc, hC2, rfl⟩ := hoist_fun hC
  obtain ⟨xc', kxc', hXc', sxc, lxc⟩ := bind2_settled hset hss hS hXc
  have kypos : 1 ≤ ky := by
    rcases bind_of_unsettled app_not_ready hY with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> omega
  -- the argument `mix a b` applied, on the right, matching `b s₂ y` on the left
  have xside : ∃ x' kx', Run .bind (Term.app (.app (.mix a' b') s') u') x' kx' ∧ Sim z x' ∧
      kx' + 10 ≤ 8 * (ky + kz) + ks := by
    rcases bind_of_unsettled app_not_ready hZ with ⟨rfl, rfl⟩ | ⟨jz, hZr, rfl⟩
    · exact ⟨skipped, 1, .skip _, .refl _, by omega⟩
    · obtain ⟨xb, kxb, j1, hXb, hZ2, rfl⟩ := hoist_fun hZr
      obtain ⟨yb, kyb, j2, hYb, hZ3, rfl⟩ := hoist_arg hZ2
      obtain ⟨xb', kxb', hXb', sxb, lxb⟩ := bind2_settled hset hss hS hXb
      -- what `b` receives for `super` on the right: `a s u`, its value, or `skipped`
      have yb_side : ∃ u1' ku1' yb' kyb', Run .bind u' u1' ku1' ∧
          Run .bind (Term.app (.app a' s') u1') yb' kyb' ∧ Sim yb yb' ∧
          ku1' + kyb' + 7 * min (ky + kyb) 1 ≤ 8 * (ky + kyb) + 1 := by
        rcases bind_of_settled (bind_settled hY) hYb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases bind_of_unsettled app_not_ready hY with ⟨rfl, rfl⟩ | ⟨jy, hYr, rfl⟩
          · exact ⟨skipped, 1, skipped, 1, .skip _, .skip _, .refl _, by omega⟩
          · obtain ⟨xa, kxa, j3, hXa, hA1, rfl⟩ := hoist_fun hYr
            obtain ⟨xu, kxu, j4, hXu, hA2, rfl⟩ := hoist_arg hA1
            obtain ⟨xa', kxa', hXa', sxa, bxa⟩ := bind_sim ih (by omega) hXa hss
            obtain ⟨xu', kxu', hXu', sxu, bxu⟩ := bind_sim ih (by omega) hXu hu
            obtain ⟨y', j4', r4, sy, by4⟩ := ih .eval j4 (by omega) (.app (.app ha sxa) sxu) hA2
            obtain ⟨K, rK, le⟩ := unhoist_fun hXa' r4
            exact ⟨xu', kxu', y', K + 1, hXu', .eval app_not_ready rK, sy, by unfold Within at *; omega⟩
        · exact ⟨skipped, 1, skipped, 1, .skip _, .skip _, .refl _, by omega⟩
      obtain ⟨u1', ku1', yb', kyb', hU1', hYb', syb, byb⟩ := yb_side
      obtain ⟨z', j2', r2, sz, bz⟩ := ih .eval j2 (by omega) (.app (.app hb sxb) syb) hZ3
      obtain ⟨K1, rK1, le1⟩ := unhoist_arg hYb' r2
      obtain ⟨K2, rK2, le2⟩ := unhoist_fun hXb' rK1
      have run := mk_mix_app_app (Run.keep hset') hU1' rK2
      have hZpos := cv_app_pos hZ3
      exact ⟨z', _, .eval app_not_ready run, sz, by unfold Within at *; omega⟩
  obtain ⟨x', kx', hX', sx, bx⟩ := xside
  obtain ⟨v', k1'', r1, s1, b1⟩ := ih r k1' (by omega) (.app (.app hc sxc) sx) hC2
  obtain ⟨K1, rK1, le1⟩ := unhoist_fun hXc' r1
  obtain ⟨K2, rK2, le2⟩ := unhoist_arg hX' rK1
  have hCpos := cv_app_pos hC2
  exact ⟨v', K2, rK2, s1, by unfold Within at *; omega⟩

/-! ## The knot: cells, waves, approximants -/

theorem sim_skipped_right {x : Term} (h : Sim skipped x) : x = skipped := by
  unfold skipped at h
  cases h with
  | hole n len rel =>
    rename_i σ'
    cases σ' with
    | nil => rfl
    | cons _ _ => simp at len

theorem sim_skipped_left {x : Term} (h : Sim x skipped) : x = skipped := by
  unfold skipped at h
  cases h with
  | hole n len rel =>
    rename_i σ
    cases σ with
    | nil => rfl
    | cons _ _ => simp at len

theorem pending_names {fs fs' : List (String × Term)} (h : fs.map Prod.fst = fs'.map Prod.fst) :
    (fs.map fun f => (f.1, skipped)) = fs'.map fun f => (f.1, skipped) := by
  have e1 : (fs.map fun f => (f.1, skipped)) = (fs.map Prod.fst).map fun n => (n, skipped) := by
    simp [List.map_map, Function.comp_def]
  have e2 : (fs'.map fun f => (f.1, skipped)) = (fs'.map Prod.fst).map fun n => (n, skipped) := by
    simp [List.map_map, Function.comp_def]
  rw [e1, e2, h]

theorem zip_self_sim : ∀ (l : List (String × Term)), ∀ q ∈ l.zip l, Sim q.1.2 q.2.2
  | [] => by simp
  | a :: l => by
    intro q hq
    simp only [List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · exact zip_self_sim l q hq

theorem cell_sim {n j : Nat} (ih : SimBelow n) (hj : j ≤ n) {t t' S S' p p' q : Term}
    (h : Run .cell (.app (.app t S) p) q j) (ht : Sim t t') (hS : Sim S S') (hSs : Settled S)
    (hp : Sim p p') : ∃ q' j', Run .cell (.app (.app t' S') p') q' j' ∧ Sim q q' ∧ Within j j' := by
  have hsub : Sim (t.substitute (single S)) (t'.substitute (single S')) :=
    ht.subst (sim_single hS) (settled_single hSs)
  cases h with
  | cellValue hset => exact ⟨_, 0, .cellValue (Sim.ready_fwd hset hsub), hsub, Within.zero⟩
  | cellKeep hn hset hne =>
    refine ⟨p', 0, .cellKeep (fun c => hn (Sim.ready_bwd c hsub)) (Sim.ready_fwd hset hp) ?_, hp, Within.zero⟩
    intro e; subst e; exact hne (sim_skipped_left hp)
  | cellWait hn =>
    rw [sim_skipped_right hp]
    exact ⟨skipped, 0, .cellWait (fun c => hn (Sim.ready_bwd c hsub)), .refl _, Within.zero⟩
  | cellEval hn e =>
    rw [sim_skipped_right hp]
    obtain ⟨v', j', r, sv, b⟩ := ih .eval _ (by omega) hsub e
    exact ⟨v', j' + 1, .cellEval (fun c => hn (Sim.ready_bwd c hsub)) r, sv, by unfold Within at *; omega⟩

theorem wave_sim {n : Nat} (ih : SimBelow n) {S S' : Term} (hS : Sim S S') (hSs : Settled S) :
    ∀ {fs fs' ps ps' : List (String × Term)} {P : Term} {j : Nat},
      Run .wave (.app (.app (.record fs) S) (.record ps)) P j → j ≤ n →
      fs.map Prod.fst = fs'.map Prod.fst → (∀ q ∈ fs.zip fs', Sim q.1.2 q.2.2) →
      ps.map Prod.fst = ps'.map Prod.fst → (∀ q ∈ ps.zip ps', Sim q.1.2 q.2.2) →
      ∃ P' j', Run .wave (.app (.app (.record fs') S') (.record ps')) P' j' ∧ Sim P P' ∧ Within j j'
  | [], fs', ps, ps', P, j, h, _, nf, _, np, _ => by
    cases h
    cases fs' with
    | cons _ _ => simp at nf
    | nil =>
      cases ps' with
      | cons _ _ => simp at np
      | nil => exact ⟨_, 0, .waveNil, .refl _, Within.zero⟩
  | (n0, t) :: fs, fs', ps, ps', P, j, h, hj, nf, rf, np, rp => by
    cases h with
    | @waveCons _ _ _ p q _ ps0 qs k1 k2 hc hw =>
      cases fs' with
      | nil => simp at nf
      | cons g fs' =>
        cases ps' with
        | nil => simp at np
        | cons g' ps' =>
          obtain ⟨gn, gt⟩ := g
          obtain ⟨gn', gp⟩ := g'
          simp only [List.map_cons, List.cons.injEq] at nf np
          obtain ⟨rfl, nf⟩ := nf
          obtain ⟨rfl, np⟩ := np
          have rt : Sim t gt := rf ((n0, t), (n0, gt)) (by simp)
          have rp0 : Sim p gp := rp ((n0, p), (n0, gp)) (by simp)
          obtain ⟨q', j1, r1, s1, b1⟩ := cell_sim ih (by omega) hc rt hS hSs rp0
          obtain ⟨P', j2, r2, s2, b2⟩ := wave_sim ih hS hSs hw (by omega) nf
            (fun x hx => rf x (by simp [hx])) np (fun x hx => rp x (by simp [hx]))
          obtain ⟨qs', rfl, nq, rq⟩ := sim_record_inv s2
          refine ⟨_, _, .waveCons r1 r2, .record (by simp [nq]) ?_, Within.add b1 b2⟩
          intro x hx
          simp only [List.zip_cons_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact s1
          · exact rq x hx

theorem knot_sim_aux {n : Nat} (ih : SimBelow n) {m : Mode} {a V : Term} {j : Nat} (h : Run m a V j) :
    m = .knot → j ≤ n → ∀ {T S T' S' : Term}, a = .app T S → Sim T T' → Sim S S' → Settled S →
      ∃ V' j', Run .knot (.app T' S') V' j' ∧ Sim V V' ∧ Within j j' := by
  induction h with
  | knotDone hP =>
    intro _ _ T S T' S' e hT hS _
    cases e
    exact ⟨S', 0, .knotDone (Sim.ready_fwd hP hS), hS, Within.zero⟩
  | @knotFirst fs P V k1 k2 hw hk _ ihk =>
    intro _ hj T S T' S' e hT hS _
    cases e
    obtain ⟨fs', rfl, nf, rf⟩ := sim_record_inv hT
    rw [sim_skipped_right hS]
    obtain ⟨P', j1, r1, s1, b1⟩ := wave_sim ih (.refl skipped) .skipped hw (by omega) nf rf rfl
      (zip_self_sim _)
    have hP : Settled P := by
      obtain ⟨qs, rfl, hq⟩ := run_produced hw
      exact .value (.record hq)
    obtain ⟨V', j2, r2, s2, b2⟩ := ihk rfl (by omega) rfl (.record nf rf) s1 hP
    have e : pending fs' = pending fs := by unfold pending; rw [pending_names nf]
    refine ⟨V', _, .knotFirst (by rw [e]; exact r1) r2, s2, Within.add b1 b2⟩
  | @knotWave fs ps P V k1 k2 hw hk _ ihk =>
    intro _ hj T S T' S' e hT hS hSs
    cases e
    obtain ⟨fs', rfl, nf, rf⟩ := sim_record_inv hT
    obtain ⟨ps', rfl, np, rp⟩ := sim_record_inv hS
    obtain ⟨P', j1, r1, s1, b1⟩ := wave_sim ih hS hSs hw (by omega) nf rf np rp
    have hP : Settled P := by
      obtain ⟨qs, rfl, hq⟩ := run_produced hw
      exact .value (.record hq)
    obtain ⟨V', j2, r2, s2, b2⟩ := ihk rfl (by omega) rfl (.record nf rf) s1 hP
    exact ⟨V', _, .knotWave r1 r2, s2, Within.add b1 b2⟩
  | knotUnroll hT0 hk ihk =>
    intro _ hj T S T' S' e hT hS hSs
    cases e
    have hsub := hT.subst (sim_single hS) (settled_single hSs)
    obtain ⟨V', j', r, sV, b⟩ := ihk rfl hj rfl hT hsub (Ready.substitute hT0 (settled_single hSs)).settled
    exact ⟨V', j', .knotUnroll (Sim.ready_fwd hT0 hT) r, sV, b⟩
  | _ => intro hm; cases hm

theorem knot_sim {n j : Nat} (ih : SimBelow n) {T T' S S' V : Term} (h : Run .knot (.app T S) V j)
    (hj : j ≤ n) (hT : Sim T T') (hS : Sim S S') (hSs : Settled S) :
    ∃ V' j', Run .knot (.app T' S') V' j' ∧ Sim V V' ∧ Within j j' :=
  knot_sim_aux ih h rfl hj rfl hT hS hSs

/-! ## The simulation -/

theorem run_value {r : Tail} {v : Term} (hv : CValue v) : Run (.tail r) v v 0 := by
  cases r
  · exact .value hv
  · exact .headEval (.value hv)

/-- One step of the simulation at cost `n`, in either tail mode; a template settled by evaluation
(`headEval`) is the evaluation at the same cost, given as `heval`. -/
theorem sim_step {r : Tail} {n : Nat} (ih : SimBelow n)
    (heval : r = .head → ∀ {t t' v : Term}, Sim t t' → CV t v n → ∃ v' n', CV t' v' n' ∧ Sim v v' ∧ Within n n')
    {t t' v : Term} (hs : Sim t t') (h : Run (.tail r) t v n) :
    ∃ v' n', Run (.tail r) t' v' n' ∧ Sim v v' ∧ Within n n' := by
  have hs0 := hs
  have lift : ∀ {t t' v : Term}, Sim t t' → CV t v n → r = .head →
      ∃ v' n', Run .head t' v' n' ∧ Sim v v' ∧ Within n n' := by
    intro t t' v hs h e
    obtain ⟨v', n', r', sv, b⟩ := heval e hs h
    exact ⟨v', n', .headEval r', sv, b⟩
  by_cases hv : CValue t
  · obtain ⟨rfl, rfl⟩ := run_of_value hv h
    exact ⟨t', 0, run_value (Sim.ready_fwd hv hs), hs, by simp [Within]⟩
  cases hs with
  | hole n len rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
  | bound i =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
  | lam hb => exact absurd (.lam _) hv
  | nat m => exact absurd (.nat m) hv
  | boolean b => exact absurd (.boolean b) hv
  | label l => exact absurd (.label l) hv
  | perform hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
  | split names hg hf =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
  | app hf ha =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | apply h1 h2 h3 =>
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hf h1
      obtain ⟨b', rfl, sb⟩ := sim_lam_inv s1
      obtain ⟨x', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 ha
      obtain ⟨v', k3', r3, s3, b3⟩ := ih r _ (by omega) (Sim.instantiate sb s2 (bind_settled h2)) h3
      exact ⟨v', _, .apply r1 r2 r3, s3, by unfold Within at *; omega⟩
    | applySpec h1 h2 =>
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hf h1
      obtain ⟨m', e', rfl, _, se⟩ := sim_spec_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) (.app se ha) h2
      exact ⟨v', _, .applySpec r1 r2, s2, by unfold Within at *; omega⟩
  | mix hl hu =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | mix => exact ⟨_, 1, .mix _ _, sim_mixBody hl hu, by simp [Within]⟩
  | fix hs1 hi =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | fix h1 h2 =>
      obtain ⟨T', k1', r1, sT, b1⟩ := ih .head _ (by omega) (sim_selfBody hs1 hi) h1
      obtain ⟨V', k2', r2, sV, b2⟩ := knot_sim ih h2 (by omega) sT (.refl _) .skipped
      exact ⟨V', _, .fix r1 r2, sV, by unfold Within at *; omega⟩
  | specification hm he =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | specification hn h1 h2 =>
      obtain ⟨m', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hm
      obtain ⟨e', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 he
      exact ⟨_, _, .specification (fun c => hn (Sim.ready_bwd c (.specification hm he))) r1 r2,
        .specification s1 s2, by unfold Within at *; omega⟩
  | prototype hm he =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | prototype hn h1 h2 =>
      obtain ⟨m', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hm
      obtain ⟨e', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 he
      exact ⟨_, _, .prototype (fun c => hn (Sim.ready_bwd c (.prototype hm he))) r1 r2,
        .prototype s1 s2, by unfold Within at *; omega⟩
  | inject l hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | inject hn h1 =>
      obtain ⟨p', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hp
      exact ⟨_, _, .inject (fun c => hn (Sim.ready_bwd c (.inject l hp))) r1, .inject l s1,
        by unfold Within at *; omega⟩
  | reflect hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | reflect h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hp h1
      obtain ⟨s', g', rfl, ss, _⟩ := sim_proto_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) ss h2
      exact ⟨v', _, .reflect r1 r2, s2, by unfold Within at *; omega⟩
  | metadata hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | metadata h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hp h1
      obtain ⟨m', e', rfl, sm, _⟩ := sim_spec_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) sm h2
      exact ⟨v', _, .metadata r1 r2, s2, by unfold Within at *; omega⟩
  | project hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | project h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hp h1
      obtain ⟨s', g', rfl, _, sg⟩ := sim_proto_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) sg h2
      exact ⟨v', _, .project r1 r2, s2, by unfold Within at *; omega⟩
  | binary op hl hr =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | binary h1 h2 hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hl h1
      obtain ⟨w2, k2', r2, s2, b2⟩ := ih .eval _ (by omega) hr h2
      rw [sim_literal_inv ll s1] at r1
      rw [sim_literal_inv lr s2] at r2
      exact ⟨_, _, .binary r1 r2 hit, .refl _, by unfold Within at *; omega⟩
  | extend hi names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | extend h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hi h1
      obtain ⟨inh', rfl, nI, rI⟩ := sim_record_inv s1
      obtain ⟨gs', k2', r2, nF, rF, b2⟩ := fields_sim ih h2 (by omega) names rel
      obtain ⟨n3, r3⟩ := extendFields_rel nI rI nF rF
      exact ⟨_, _, .extend r1 r2, .record n3 r3, by unfold Within at *; omega⟩
    | headExtend h1 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .head _ (by omega) hi h1
      obtain ⟨inh', rfl, nI, rI⟩ := sim_record_inv s1
      obtain ⟨n3, r3⟩ := extendFields_rel nI rI names rel
      exact ⟨_, _, .headExtend r1, .record n3 r3, by unfold Within at *; omega⟩
  | record names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | record hn h1 =>
      obtain ⟨gs', k1', r1, nF, rF, b1⟩ := fields_sim ih h1 (by omega) names rel
      exact ⟨_, _, .record (fun c => hn (Sim.ready_bwd c (.record names rel))) r1, .record nF rF,
        by unfold Within at *; omega⟩
    | headRecord hn =>
      exact ⟨_, 1, .headRecord (fun c => hn (Sim.ready_bwd c (.record names rel))), .record names rel,
        by simp [Within]⟩
  | get name hg =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | get h1 hit h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hg h1
      obtain ⟨fs', rfl, n1, rl1⟩ := sim_record_inv s1
      obtain ⟨x', hit', sx⟩ := find_left n1 rl1 hit
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) sx h2
      exact ⟨v', _, .get r1 hit' r2, s2, by unfold Within at *; omega⟩
  | ifZero hc hz hsb =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | zero h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hc h1
      rw [sim_literal_inv (.nat 0) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) hz h2
      exact ⟨v', _, .zero r1 r2, s2, by unfold Within at *; omega⟩
    | succ h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hc h1
      rw [sim_literal_inv (.nat _) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) (Sim.instantiate hsb (.nat _) (.value (.nat _))) h2
      exact ⟨v', _, .succ r1 r2, s2, by unfold Within at *; omega⟩
  | case hsc names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | case h1 hit h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hsc h1
      obtain ⟨p', rfl, sp⟩ := sim_inject_inv s1
      obtain ⟨body', hit', sb⟩ := find_left names rel hit
      obtain ⟨v', k2', r2, s2, b2⟩ :=
        ih r _ (by omega) (Sim.instantiate sb sp (inject_value_payload (cv_value h1))) h2
      exact ⟨v', _, .case r1 hit' r2, s2, by unfold Within at *; omega⟩
  | ifBool hc hx hy =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | ifTrue h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hc h1
      rw [sim_literal_inv (.boolean true) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) hx h2
      exact ⟨v', _, .ifTrue r1 r2, s2, by unfold Within at *; omega⟩
    | ifFalse h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih .eval _ (by omega) hc h1
      rw [sim_literal_inv (.boolean false) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih r _ (by omega) hy h2
      exact ⟨v', _, .ifFalse r1 r2, s2, by unfold Within at *; omega⟩
  | done hd =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | done h1 =>
      obtain ⟨v', k1', r1, s1, b1⟩ := ih r _ (by omega) hd h1
      exact ⟨v', _, .done r1, s1, by unfold Within at *; omega⟩
  | assocLR ha hb hc =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | mix =>
      refine ⟨_, 1, .mix _ _, ?_, by simp [Within]⟩
      simp only [mixBody, Term.rename]
      exact .lam (.lam (.bodyLR (.bound 1) (ha.rename _) (hb.rename _) (hc.rename _) (.bound 1) (.bound 0)))
  | assocRL ha hb hc =>
    cases h with
    | value h0 => exact absurd h0 hv
    | headEval h' => exact lift hs0 h' rfl
    | mix =>
      refine ⟨_, 1, .mix _ _, ?_, by simp [Within]⟩
      simp only [mixBody, Term.rename]
      exact .lam (.lam (.bodyRL (.bound 1) (ha.rename _) (hb.rename _) (hc.rename _) (.bound 1) (.bound 0)))
  | bodyLR hset ha hb hc hss hu => exact bodyLR_case ih hset ha hb hc hss hu h
  | bodyRL hset ha hb hc hss hu => exact bodyRL_case ih hset ha hb hc hss hu h

theorem sim_below : ∀ n, SimBelow n
  | 0 => fun _ j hj => absurd hj (Nat.not_lt_zero _)
  | n + 1 => fun r j hj _ _ _ hs h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with lt | rfl
    · exact sim_below n r j lt hs h
    · exact sim_step (sim_below j) (fun _ {_ _ _} hs h => sim_step (sim_below j) (fun e' => by cases e') hs h) hs h

/-- **`Sim` is a cost simulation**: a derivation of cost `k` is matched by one of cost at most
`8k` (and `8k - 7` when `k > 0`), with related results. -/
theorem sim_cv {t t' v : Term} {k : Nat} (hs : Sim t t') (h : CV t v k) :
    ∃ v' k', CV t' v' k' ∧ Sim v v' ∧ k' + 7 * min k 1 ≤ 8 * k :=
  sim_below (k + 1) .eval k (Nat.lt_succ_self k) hs h

/-! ## `≈c` -/

/-- Improvement within a constant factor (Moran–Sands Def. 4.1) for the clairvoyant semantics: in
every substitution and context, a derivation of `C[t]` of cost `k` gives one of `C[t']` of cost at
most `A * k`, with the same result when the result is a literal. -/
@[expose] def CostWithin (A : Nat) (t t' : Term) : Prop :=
  ∀ (ρ : Nat → Term) (C v : Term) (k : Nat), CV (instantiate C (t.substitute ρ)) v k →
    ∃ v' k', CV (instantiate C (t'.substitute ρ)) v' k' ∧ k' ≤ A * k ∧ (Literal v → v' = v)

/-- `t ≈c t'`: each is within a constant factor of the other, in every context. -/
@[expose] def CEquiv (t t' : Term) : Prop := ∃ A, CostWithin A t t' ∧ CostWithin A t' t

@[inherit_doc] infix:50 " ≈c " => CEquiv

theorem CostWithin.of_sim {t t' : Term} (hs : ∀ ρ : Nat → Term, Sim (t.substitute ρ) (t'.substitute ρ)) :
    CostWithin 8 t t' := by
  intro ρ C v k h
  have hc : Sim (instantiate C (t.substitute ρ)) (instantiate C (t'.substitute ρ)) := by
    rw [instantiate_eq, instantiate_eq]
    exact Sim.substRefl C (sim_single (hs ρ))
  obtain ⟨v', k', r, sv, b⟩ := sim_cv hc h
  exact ⟨v', k', r, by omega, fun lit => sim_literal_inv lit sv⟩

/-- **`mix` is associative up to `≈c`, with factor 8 both ways**: in every context and under every
substitution, a clairvoyant derivation of one association of cost `k` gives one of the other of cost
at most `8k`, with the same literal result. -/
theorem mix_assoc_cost (a b c : Term) :
    CostWithin 8 (.mix (.mix a b) c) (.mix a (.mix b c)) ∧
      CostWithin 8 (.mix a (.mix b c)) (.mix (.mix a b) c) :=
  ⟨CostWithin.of_sim fun ρ => by
      simp only [Term.substitute]; exact .assocLR (.refl _) (.refl _) (.refl _),
   CostWithin.of_sim fun ρ => by
      simp only [Term.substitute]; exact .assocRL (.refl _) (.refl _) (.refl _)⟩

theorem mix_assoc_cequiv (a b c : Term) : .mix (.mix a b) c ≈c .mix a (.mix b c) :=
  ⟨8, mix_assoc_cost a b c⟩

/-! ## Quantitative Clairvoyant Call-by-Need vs. Call-by-Value Cost Bounds -/

/-- Any `evalClairvoyantMinCost` witness within `bound` establishes `CV t v k` and `CostAtMost t bound`. -/
theorem costAtMost_of_evalClairvoyantMinCost {fuel bound : Nat} {t v : Term} {k : Nat}
    (heval : evalClairvoyantMinCost fuel t = some (v, k)) (hle : k ≤ bound) :
    CV t v k ∧ CostAtMost t bound := by
  have hcv := evalClairvoyantMinCost_sound fuel t v k heval
  exact ⟨hcv, v, k, hcv, hle⟩

/-- Any `evalCBV` witness within `bound` establishes `CV t v k` and `CostAtMost t bound`. -/
theorem costAtMost_of_evalCBV {fuel bound : Nat} {t v : Term} {k : Nat}
    (heval : evalCBV fuel t = some (v, k)) (hle : k ≤ bound) :
    CV t v k ∧ CostAtMost t bound := by
  have hcv := evalCBV_sound fuel t v k heval
  exact ⟨hcv, v, k, hcv, hle⟩

/-- Exact contextual `SandsImproves` embeds into `CostWithin 1`. -/
theorem CostWithin.of_sandsImproves {t t' : Term} (h : SandsImproves t t') :
    CostWithin 1 t t' := by
  intro ρ C v k hcv
  obtain ⟨v', k', r, hle, hlit⟩ := h ρ C v k hcv
  exact ⟨v', k', r, by omega, hlit⟩

/-- Call-by-need sharing on duplicated variables (`dupAdd = λ x => x + x`): an unsettled
argument `a` that evaluates to `.nat n` at cost `ka` is evaluated ONCE in `Run .bind`
(`Let′`, cost `ka + 1`), and its value `.nat n` is read twice at cost `0`, achieving
total derivation cost `ka + 3`. -/
theorem cv_dupAdd_shared {a : Term} {n ka : Nat}
    (hnsa : ¬ Settled a) (ha : CV a (.nat n) ka) :
    CV (.app dupAdd a) (.nat (n + n)) (ka + 3) := by
  have hbind : Run .bind a (.nat n) (ka + 1) := .eval hnsa ha
  have hbody : CV (instantiate (.binary .add (.bound 0) (.bound 0)) (.nat n)) (.nat (n + n)) 1 := by
    rw [instantiate_dupAdd_body]
    have hadd := Run.binary (op := .add) (Run.value (.nat n)) (Run.value (.nat n)) rfl
    simpa using hadd
  have happ := Run.apply (Run.value (.lam (.binary .add (.bound 0) (.bound 0)))) hbind hbody
  have heq : 0 + (ka + 1) + 1 + 1 = ka + 3 := by omega
  rwa [heq] at happ

/-- Quantitative comparison between `evalClairvoyantMinCost` (`Skip`) and `evalCBV` (`Let′`)
on an unused unsettled argument `a`: `evalCBV` pays `ka + 2` while `evalClairvoyantMinCost`
pays `2`, saving `ka` ticks (`2 < ka + 2` whenever `0 < ka`). -/
theorem cv_skip_vs_cbv_unused_arg {a va : Term} {ka fuel : Nat}
    (ha : ¬ Settled a) (hcbv : evalCBV fuel a = some (va, ka)) :
    evalClairvoyantMinCost (fuel + 1) (.app (.lam (.nat 42)) a) = some (.nat 42, 2) ∧
      evalCBV (fuel + 1) (.app (.lam (.nat 42)) a) = some (.nat 42, ka + 2) ∧
      2 ≤ ka + 2 ∧
      (0 < ka → 2 < ka + 2) := by
  have hclair := (evalClairvoyant_skip_unused_arg_saves_cost a ha fuel).1
  have hnsa : isSettled a = false := by
    cases h : isSettled a with
    | false => rfl
    | true => exact absurd (isSettled_sound a h) ha
  have hncv : isCValue (.app (.lam (.nat 42)) a) = false := isCValue_app (.lam (.nat 42)) a
  have hlam : evalCBV fuel (.lam (.nat 42)) = some (.lam (.nat 42), 0) := by
    unfold evalCBV; simp [CValue.isCValue_eq_true (.lam (.nat 42))]
  have hinst : instantiate (.nat 42) va = .nat 42 := by
    simp [instantiate, Term.substitute]
  have hnat : evalCBV fuel (.nat 42) = some (.nat 42, 0) := by
    unfold evalCBV; simp [CValue.isCValue_eq_true (.nat 42)]
  have hcbv_app : evalCBV (fuel + 1) (.app (.lam (.nat 42)) a) = some (.nat 42, ka + 2) := by
    unfold evalCBV
    simp [hncv, hlam, hnsa, hcbv, hinst, hnat]
  exact ⟨hclair, hcbv_app, by omega, fun hpos => by omega⟩

/-! ## Compositional Cost-Improvement Category, `≈c` Equivalence Algebra & Slot Cost Contracts -/

/-- Identity cost improvement (`CostWithin 1 t t`). -/
theorem CostWithin.refl (t : Term) : CostWithin 1 t t := by
  intro ρ C v k hcv
  exact ⟨v, k, hcv, by omega, fun _ => rfl⟩

/-- Factor weakening: `CostWithin A t t'` lifts to `CostWithin B t t'` whenever `A ≤ B`. -/
theorem CostWithin.mono {A B : Nat} (hAB : A ≤ B) {t t' : Term}
    (h : CostWithin A t t') : CostWithin B t t' := by
  intro ρ C v k hcv
  obtain ⟨v', k', r, hle, hlit⟩ := h ρ C v k hcv
  refine ⟨v', k', r, Nat.le_trans hle (Nat.mul_le_mul_right k hAB), hlit⟩

/-- Multiplicative composition of constant-factor cost simulations across pipeline stages. -/
theorem CostWithin.trans {A B : Nat} {t₁ t₂ t₃ : Term}
    (h₁₂ : CostWithin A t₁ t₂) (h₂₃ : CostWithin B t₂ t₃) :
    CostWithin (B * A) t₁ t₃ := by
  intro ρ C v k hcv
  obtain ⟨v₂, k₂, r₂, hle₁₂, hlit₁₂⟩ := h₁₂ ρ C v k hcv
  obtain ⟨v₃, k₃, r₃, hle₂₃, hlit₂₃⟩ := h₂₃ ρ C v₂ k₂ r₂
  have hmul : k₃ ≤ (B * A) * k := by
    calc
      k₃ ≤ B * k₂ := hle₂₃
      _ ≤ B * (A * k) := Nat.mul_le_mul_left B hle₁₂
      _ = (B * A) * k := (Nat.mul_assoc B A k).symm
  refine ⟨v₃, k₃, r₃, hmul, fun hlit => ?_⟩
  have hv₂ := hlit₁₂ hlit
  subst hv₂
  exact hlit₂₃ hlit

/-- `≈c` is reflexive (`factor = 1`). -/
theorem CEquiv.refl (t : Term) : t ≈c t :=
  ⟨1, CostWithin.refl t, CostWithin.refl t⟩

/-- `≈c` is symmetric. -/
theorem CEquiv.symm {t t' : Term} (h : t ≈c t') : t' ≈c t := by
  obtain ⟨A, h1, h2⟩ := h
  exact ⟨A, h2, h1⟩

/-- `≈c` is transitive (`factor = B * A`, symmetric via `Nat.mul_comm`). -/
theorem CEquiv.trans {t₁ t₂ t₃ : Term} (h₁₂ : t₁ ≈c t₂) (h₂₃ : t₂ ≈c t₃) : t₁ ≈c t₃ := by
  obtain ⟨A, f₁₂, b₂₁⟩ := h₁₂
  obtain ⟨B, f₂₃, b₃₂⟩ := h₂₃
  refine ⟨B * A, CostWithin.trans f₁₂ f₂₃, ?_⟩
  have hb : CostWithin (A * B) t₃ t₁ := CostWithin.trans b₃₂ b₂₁
  rwa [Nat.mul_comm A B] at hb

/-- Specializing `CostWithin A t t'` to the empty context `C = .bound 0` and identity
substitution `Term.bound` transports any `CostAtMost t bound` budget directly to
`CostAtMost t' (A * bound)`. -/
theorem CostWithin.costAtMost_closed {A : Nat} {t t' : Term}
    (h : CostWithin A t t') {bound : Nat} (hb : CostAtMost t bound) :
    CostAtMost t' (A * bound) := by
  obtain ⟨v, k, hcv, hkle⟩ := hb
  have hid_t : instantiate (.bound 0) (t.substitute Term.bound) = t := by
    simp [instantiate, Term.substitute, substitute_bound]
  have hid_t' : instantiate (.bound 0) (t'.substitute Term.bound) = t' := by
    simp [instantiate, Term.substitute, substitute_bound]
  have hcv' : CV (instantiate (.bound 0) (t.substitute Term.bound)) v k := by
    rwa [hid_t]
  obtain ⟨v', k', r', hk', _⟩ := h Term.bound (.bound 0) v k hcv'
  rw [hid_t'] at r'
  exact ⟨v', k', r', Nat.le_trans hk' (Nat.mul_le_mul_left A hkle)⟩

/-- Ground literal preservation under `CostWithin A t t'`: if `t` evaluates to literal `v`
at cost `k`, then `t'` evaluates to the exact same literal `v` at cost `k' ≤ A * k`. -/
theorem CostWithin.sameLiteral {A : Nat} {t t' v : Term} {k : Nat}
    (h : CostWithin A t t') (hlit : Literal v) (hcv : CV t v k) :
    ∃ k', CV t' v k' ∧ k' ≤ A * k := by
  have hid_t : instantiate (.bound 0) (t.substitute Term.bound) = t := by
    simp [instantiate, Term.substitute, substitute_bound]
  have hid_t' : instantiate (.bound 0) (t'.substitute Term.bound) = t' := by
    simp [instantiate, Term.substitute, substitute_bound]
  have hcv0 : CV (instantiate (.bound 0) (t.substitute Term.bound)) v k := by
    rwa [hid_t]
  obtain ⟨v', k', r', hk', hveq⟩ := h Term.bound (.bound 0) v k hcv0
  rw [hid_t', hveq hlit] at r'
  exact ⟨k', r', hk'⟩

/-- Decidable equality check on observed literal results (`.nat`, `.boolean`, `.label`). -/
@[expose] def sameObservedLiteral : Term → Term → Bool
  | .nat n, .nat m => n == m
  | .boolean b, .boolean c => b == c
  | .label s, .label t => s == t
  | _, _ => false

theorem sameObservedLiteral_inhabited :
    sameObservedLiteral (.nat 7) (.nat 7) = true := by
  unfold sameObservedLiteral
  rfl

theorem sameObservedLiteral_sound {v₁ v₂ : Term} (h : sameObservedLiteral v₁ v₂ = true) :
    v₁ = v₂ ∧ Literal v₁ := by
  cases v₁ <;> cases v₂ <;> simp [sameObservedLiteral] at h <;> subst h
  · exact ⟨rfl, .nat _⟩
  · exact ⟨rfl, .boolean _⟩
  · exact ⟨rfl, .label _⟩

/-- Executable Clairvoyant slot-binding cost & observation contract checker:
verifies that `impl` evaluates under `evalClairvoyantMinCost fuel` within `budget` ticks
to the exact same observed literal value produced by `spec`. -/
@[expose] def checkSlotCostContract (fuel budget : Nat) (impl spec : Term) : Bool :=
  match evalClairvoyantMinCost fuel impl, evalClairvoyantMinCost fuel spec with
  | some (vi, ki), some (vs, _) => decide (ki ≤ budget) && sameObservedLiteral vi vs
  | _, _ => false

theorem checkSlotCostContract_inhabited :
    checkSlotCostContract 1 2 (.nat 7) (.nat 7) = true := by
  unfold checkSlotCostContract evalClairvoyantMinCost evalClairvoyantWithHint sameObservedLiteral
  decide

/-- Soundness of `checkSlotCostContract`: acceptance certifies a genuine Clairvoyant
derivation of `impl` within `budget` (`CostAtMost impl budget`) agreeing in value with `spec`. -/
theorem checkSlotCostContract_sound {fuel budget : Nat} {impl spec : Term}
    (h : checkSlotCostContract fuel budget impl spec = true) :
    ∃ v ki ks, CV impl v ki ∧ CV spec v ks ∧ ki ≤ budget ∧ CostAtMost impl budget := by
  unfold checkSlotCostContract at h
  split at h
  · rename_i vi ki vs ks hi hs
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hle, heq_lit⟩ := h
    obtain ⟨heq, _⟩ := sameObservedLiteral_sound heq_lit
    subst heq
    have hcvi := evalClairvoyantMinCost_sound fuel impl vi ki hi
    have hcvs := evalClairvoyantMinCost_sound fuel spec vi ks hs
    exact ⟨vi, ki, ks, hcvi, hcvs, hle, vi, ki, hcvi, hle⟩
  · cases h

/-- Transport of a certified `checkSlotCostContract` across any `CostWithin A impl impl'`
improvement pass: `impl'` evaluates to the exact same literal `v` as `spec` at cost `≤ A * budget`. -/
theorem checkSlotCostContract_costWithin_transport {fuel budget A : Nat} {impl impl' spec : Term}
    (hContract : checkSlotCostContract fuel budget impl spec = true)
    (hImp : CostWithin A impl impl') :
    ∃ v ks k', Literal v ∧ CV spec v ks ∧ CV impl' v k' ∧ k' ≤ A * budget ∧
      CostAtMost impl' (A * budget) := by
  unfold checkSlotCostContract at hContract
  split at hContract
  · rename_i vi ki vs ks hi hs
    rw [Bool.and_eq_true, decide_eq_true_eq] at hContract
    obtain ⟨hle, heq_lit⟩ := hContract
    obtain ⟨rfl, hlit⟩ := sameObservedLiteral_sound heq_lit
    have hcvi := evalClairvoyantMinCost_sound fuel impl vi ki hi
    have hcvs := evalClairvoyantMinCost_sound fuel spec vi ks hs
    obtain ⟨k', hcv', hk'⟩ := hImp.sameLiteral hlit hcvi
    have hbound : k' ≤ A * budget := Nat.le_trans hk' (Nat.mul_le_mul_left A hle)
    exact ⟨vi, ks, k', hlit, hcvs, hcv', hbound, vi, k', hcv', hbound⟩
  · cases hContract

end Obend.Equiv
end
