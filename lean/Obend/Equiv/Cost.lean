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
@[expose] public section
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

theorem cv_app_pos {f a v : Term} {k : Nat} (h : CV (.app f a) v k) : 1 ≤ k := by
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
def Within (k k' : Nat) : Prop := k' + 7 * min k 1 ≤ 8 * k

/-- The simulation, for every derivation cheaper than `n`. -/
def SimBelow (n : Nat) : Prop :=
  ∀ j < n, ∀ {t t' v : Term}, Sim t t' → CV t v j → ∃ v' j', CV t' v' j' ∧ Sim v v' ∧ Within j j'

theorem bind_sim {n j : Nat} (ih : SimBelow n) (hj : j ≤ n) {a a' x : Term} (h : Run .bind a x j)
    (hs : Sim a a') : ∃ x' j', Run .bind a' x' j' ∧ Sim x x' ∧ Within j j' := by
  cases h with
  | keep hset => exact ⟨a', 0, .keep (Sim.ready_fwd hset hs), hs, by simp [Within]⟩
  | skip => exact ⟨skipped, 1, .skip _, .refl _, by simp [Within]⟩
  | eval hn e =>
    obtain ⟨v', j', r, sv, b⟩ := ih _ (by omega) hs e
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

theorem bodyLR_case {n : Nat} (ih : SimBelow n) {a a' b b' c c' s s' u u' v : Term}
    (hset : Settled s) (ha : Sim a a') (hb : Sim b b') (hc : Sim c c') (hss : Sim s s') (hu : Sim u u')
    (h : CV (.app (.app c s) (.app (.app (.mix a b) s) u)) v n) :
    ∃ v' n', CV (.app (.app (.mix b' c') s') (.app (.app a' s') u')) v' n' ∧ Sim v v' ∧ Within n n' := by
  have hset' : Settled s' := Sim.ready_fwd hset hss
  obtain ⟨x, kx, k1, hX, hC, rfl⟩ := hoist_arg h
  have k1pos := cv_app_pos hC
  rcases bind_of_unsettled app_not_ready hX with ⟨rfl, rfl⟩ | ⟨j, hXr, rfl⟩
  · -- `mix a b` is skipped: the right skips `a s u` and `b s _`, and pays only the unfolding
    obtain ⟨v', k1', r1, s1, b1⟩ := ih k1 (by omega) (.app (.app hc hss) (.refl _)) hC
    obtain ⟨K, rK, le⟩ := unhoist_arg (Run.skip (Term.app (.app b' s') skipped)) r1
    have r := mk_mix_app_app (Run.keep hset') (Run.skip (Term.app (.app a' s') u')) rK
    exact ⟨v', _, r, s1, by unfold Within at *; omega⟩
  · obtain ⟨s2, ks, u1, ku, kb, hS, hU, hB, rfl⟩ := cv_mix_app_app hXr
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
        obtain ⟨y', j2', r2, sy, by2⟩ := ih j2 (by omega) (.app (.app ha sxa) sxu) hA2
        have j2pos := cv_app_pos hA2
        obtain ⟨K1, rK1, le1⟩ := unhoist_arg hXu' r2
        obtain ⟨K2, rK2, le2⟩ := unhoist_fun hXa' rK1
        exact ⟨y', K2 + 1, .eval app_not_ready rK2, sy, by unfold Within at *; omega⟩
    obtain ⟨y', ky', hY', sy, by'⟩ := yside
    -- the argument `b s y` on the right, matching `mix a b` applied on the left
    obtain ⟨z, k4'', rz, sz, bz⟩ := ih k4' (by omega) (.app (.app hb sxb) sy) hB3
    obtain ⟨Kb, rKb, leb⟩ := unhoist_fun hXb' rz
    have hZ' : Run .bind (Term.app (.app b' s') y') z (Kb + 1) := .eval app_not_ready rKb
    obtain ⟨v', k1', r1, s1, b1⟩ := ih k1 (by omega) (.app (.app hc hss) sz) hC
    obtain ⟨K, rK, le⟩ := unhoist_arg hZ' r1
    have r := mk_mix_app_app (Run.keep hset') hY' rK
    have hBpos := cv_app_pos hB3
    exact ⟨v', _, r, s1, by unfold Within at *; omega⟩

theorem bodyRL_case {n : Nat} (ih : SimBelow n) {a a' b b' c c' s s' u u' v : Term}
    (hset : Settled s) (ha : Sim a a') (hb : Sim b b') (hc : Sim c c') (hss : Sim s s') (hu : Sim u u')
    (h : CV (.app (.app (.mix b c) s) (.app (.app a s) u)) v n) :
    ∃ v' n', CV (.app (.app c' s') (.app (.app (.mix a' b') s') u')) v' n' ∧ Sim v v' ∧ Within n n' := by
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
            obtain ⟨y', j4', r4, sy, by4⟩ := ih j4 (by omega) (.app (.app ha sxa) sxu) hA2
            obtain ⟨K, rK, le⟩ := unhoist_fun hXa' r4
            exact ⟨xu', kxu', y', K + 1, hXu', .eval app_not_ready rK, sy, by unfold Within at *; omega⟩
        · exact ⟨skipped, 1, skipped, 1, .skip _, .skip _, .refl _, by omega⟩
      obtain ⟨u1', ku1', yb', kyb', hU1', hYb', syb, byb⟩ := yb_side
      obtain ⟨z', j2', r2, sz, bz⟩ := ih j2 (by omega) (.app (.app hb sxb) syb) hZ3
      obtain ⟨K1, rK1, le1⟩ := unhoist_arg hYb' r2
      obtain ⟨K2, rK2, le2⟩ := unhoist_fun hXb' rK1
      have r := mk_mix_app_app (Run.keep hset') hU1' rK2
      have hZpos := cv_app_pos hZ3
      exact ⟨z', _, .eval app_not_ready r, sz, by unfold Within at *; omega⟩
  obtain ⟨x', kx', hX', sx, bx⟩ := xside
  obtain ⟨v', k1'', r1, s1, b1⟩ := ih k1' (by omega) (.app (.app hc sxc) sx) hC2
  obtain ⟨K1, rK1, le1⟩ := unhoist_fun hXc' r1
  obtain ⟨K2, rK2, le2⟩ := unhoist_arg hX' rK1
  have hCpos := cv_app_pos hC2
  exact ⟨v', K2, rK2, s1, by unfold Within at *; omega⟩

/-! ## The simulation -/

theorem sim_step {n : Nat} (ih : SimBelow n) {t t' v : Term} (hs : Sim t t') (h : CV t v n) :
    ∃ v' n', CV t' v' n' ∧ Sim v v' ∧ Within n n' := by
  by_cases hv : CValue t
  · obtain ⟨rfl, rfl⟩ := cv_of_value hv h
    exact ⟨t', 0, .value (Sim.ready_fwd hv hs), hs, by simp [Within]⟩
  cases hs with
  | hole n len rel => cases h with | value h0 => exact absurd h0 hv
  | bound i => cases h with | value h0 => exact absurd h0 hv
  | lam hb => exact absurd (.lam _) hv
  | nat m => exact absurd (.nat m) hv
  | boolean b => exact absurd (.boolean b) hv
  | label l => exact absurd (.label l) hv
  | perform hp => cases h with | value h0 => exact absurd h0 hv
  | app hf ha =>
    cases h with
    | value h0 => exact absurd h0 hv
    | apply h1 h2 h3 =>
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih _ (by omega) hf h1
      obtain ⟨b', rfl, sb⟩ := sim_lam_inv s1
      obtain ⟨x', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 ha
      obtain ⟨v', k3', r3, s3, b3⟩ := ih _ (by omega) (Sim.instantiate sb s2 (bind_settled h2)) h3
      exact ⟨v', _, .apply r1 r2 r3, s3, by unfold Within at *; omega⟩
    | applySpec h1 h2 =>
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih _ (by omega) hf h1
      obtain ⟨m', e', rfl, _, se⟩ := sim_spec_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) (.app se ha) h2
      exact ⟨v', _, .applySpec r1 r2, s2, by unfold Within at *; omega⟩
  | mix hl hu =>
    cases h with
    | value h0 => exact absurd h0 hv
    | mix => exact ⟨_, 1, .mix _ _, sim_mixBody hl hu, by simp [Within]⟩
  | fix hs1 hi =>
    cases h with
    | value h0 => exact absurd h0 hv
    | fixLet h1 =>
      obtain ⟨V', k', r, sV, b⟩ := ih _ (by omega) (sim_selfBody hs1 hi) h1
      refine ⟨_, _, .fixLet r, ?_, by unfold Within at *; omega⟩
      exact sV.subst (sim_single (sim_knot sV)) (settled_single (knot_settled (cv_value h1)))
    | fixSkip h1 =>
      obtain ⟨V', k', r, sV, b⟩ := ih _ (by omega) (sim_selfBody hs1 hi) h1
      refine ⟨_, _, .fixSkip r, ?_, by unfold Within at *; omega⟩
      exact sV.subst (sim_single (.refl _)) (settled_single .skipped)
  | specification hm he =>
    cases h with
    | value h0 => exact absurd h0 hv
    | specification hn h1 h2 =>
      obtain ⟨m', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hm
      obtain ⟨e', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 he
      exact ⟨_, _, .specification (fun c => hn (Sim.ready_bwd c (.specification hm he))) r1 r2,
        .specification s1 s2, by unfold Within at *; omega⟩
  | prototype hm he =>
    cases h with
    | value h0 => exact absurd h0 hv
    | prototype hn h1 h2 =>
      obtain ⟨m', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hm
      obtain ⟨e', k2', r2, s2, b2⟩ := bind_sim ih (by omega) h2 he
      exact ⟨_, _, .prototype (fun c => hn (Sim.ready_bwd c (.prototype hm he))) r1 r2,
        .prototype s1 s2, by unfold Within at *; omega⟩
  | inject l hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | inject hn h1 =>
      obtain ⟨p', k1', r1, s1, b1⟩ := bind_sim ih (by omega) h1 hp
      exact ⟨_, _, .inject (fun c => hn (Sim.ready_bwd c (.inject l hp))) r1, .inject l s1,
        by unfold Within at *; omega⟩
  | reflect hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | reflect h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hp h1
      obtain ⟨s', g', rfl, ss, _⟩ := sim_proto_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) ss h2
      exact ⟨v', _, .reflect r1 r2, s2, by unfold Within at *; omega⟩
  | metadata hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | metadata h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hp h1
      obtain ⟨m', e', rfl, sm, _⟩ := sim_spec_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) sm h2
      exact ⟨v', _, .metadata r1 r2, s2, by unfold Within at *; omega⟩
  | project hp =>
    cases h with
    | value h0 => exact absurd h0 hv
    | project h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hp h1
      obtain ⟨s', g', rfl, _, sg⟩ := sim_proto_inv s1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) sg h2
      exact ⟨v', _, .project r1 r2, s2, by unfold Within at *; omega⟩
  | binary op hl hr =>
    cases h with
    | value h0 => exact absurd h0 hv
    | binary h1 h2 hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      obtain ⟨w1, k1', r1, s1, b1⟩ := ih _ (by omega) hl h1
      obtain ⟨w2, k2', r2, s2, b2⟩ := ih _ (by omega) hr h2
      rw [sim_literal_inv ll s1] at r1
      rw [sim_literal_inv lr s2] at r2
      exact ⟨_, _, .binary r1 r2 hit, .refl _, by unfold Within at *; omega⟩
  | extend hi names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | extend h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hi h1
      obtain ⟨inh', rfl, nI, rI⟩ := sim_record_inv s1
      obtain ⟨gs', k2', r2, nF, rF, b2⟩ := fields_sim ih h2 (by omega) names rel
      obtain ⟨n3, r3⟩ := extendFields_rel nI rI nF rF
      exact ⟨_, _, .extend r1 r2, .record n3 r3, by unfold Within at *; omega⟩
  | record names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | record hn h1 =>
      obtain ⟨gs', k1', r1, nF, rF, b1⟩ := fields_sim ih h1 (by omega) names rel
      exact ⟨_, _, .record (fun c => hn (Sim.ready_bwd c (.record names rel))) r1, .record nF rF,
        by unfold Within at *; omega⟩
  | get name hg =>
    cases h with
    | value h0 => exact absurd h0 hv
    | get h1 hit h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hg h1
      obtain ⟨fs', rfl, n1, rl1⟩ := sim_record_inv s1
      obtain ⟨x', hit', sx⟩ := find_left n1 rl1 hit
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) sx h2
      exact ⟨v', _, .get r1 hit' r2, s2, by unfold Within at *; omega⟩
  | ifZero hc hz hsb =>
    cases h with
    | value h0 => exact absurd h0 hv
    | zero h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hc h1
      rw [sim_literal_inv (.nat 0) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) hz h2
      exact ⟨v', _, .zero r1 r2, s2, by unfold Within at *; omega⟩
    | succ h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hc h1
      rw [sim_literal_inv (.nat _) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) (Sim.instantiate hsb (.nat _) (.value (.nat _))) h2
      exact ⟨v', _, .succ r1 r2, s2, by unfold Within at *; omega⟩
  | case hsc names rel =>
    cases h with
    | value h0 => exact absurd h0 hv
    | case h1 hit h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hsc h1
      obtain ⟨p', rfl, sp⟩ := sim_inject_inv s1
      obtain ⟨body', hit', sb⟩ := find_left names rel hit
      obtain ⟨v', k2', r2, s2, b2⟩ :=
        ih _ (by omega) (Sim.instantiate sb sp (inject_value_payload (cv_value h1))) h2
      exact ⟨v', _, .case r1 hit' r2, s2, by unfold Within at *; omega⟩
  | ifBool hc hx hy =>
    cases h with
    | value h0 => exact absurd h0 hv
    | ifTrue h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hc h1
      rw [sim_literal_inv (.boolean true) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) hx h2
      exact ⟨v', _, .ifTrue r1 r2, s2, by unfold Within at *; omega⟩
    | ifFalse h1 h2 =>
      obtain ⟨w, k1', r1, s1, b1⟩ := ih _ (by omega) hc h1
      rw [sim_literal_inv (.boolean false) s1] at r1
      obtain ⟨v', k2', r2, s2, b2⟩ := ih _ (by omega) hy h2
      exact ⟨v', _, .ifFalse r1 r2, s2, by unfold Within at *; omega⟩
  | done hd =>
    cases h with
    | value h0 => exact absurd h0 hv
    | done h1 =>
      obtain ⟨v', k1', r1, s1, b1⟩ := ih _ (by omega) hd h1
      exact ⟨v', _, .done r1, s1, by unfold Within at *; omega⟩
  | assocLR ha hb hc =>
    obtain ⟨rfl, rfl⟩ := cv_mix h
    refine ⟨_, 1, .mix _ _, ?_, by simp [Within]⟩
    simp only [mixBody, Term.rename]
    exact .lam (.lam (.bodyLR (.bound 1) (ha.rename _) (hb.rename _) (hc.rename _) (.bound 1) (.bound 0)))
  | assocRL ha hb hc =>
    obtain ⟨rfl, rfl⟩ := cv_mix h
    refine ⟨_, 1, .mix _ _, ?_, by simp [Within]⟩
    simp only [mixBody, Term.rename]
    exact .lam (.lam (.bodyRL (.bound 1) (ha.rename _) (hb.rename _) (hc.rename _) (.bound 1) (.bound 0)))
  | bodyLR hset ha hb hc hss hu => exact bodyLR_case ih hset ha hb hc hss hu h
  | bodyRL hset ha hb hc hss hu => exact bodyRL_case ih hset ha hb hc hss hu h

theorem sim_below : ∀ n, SimBelow n
  | 0 => fun j hj => absurd hj (Nat.not_lt_zero _)
  | n + 1 => fun j hj _ _ _ hs h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with lt | rfl
    · exact sim_below n j lt hs h
    · exact sim_step (sim_below j) hs h

/-- **`Sim` is a cost simulation**: a derivation of cost `k` is matched by one of cost at most
`8k` (and `8k - 7` when `k > 0`), with related results. -/
theorem sim_cv {t t' v : Term} {k : Nat} (hs : Sim t t') (h : CV t v k) :
    ∃ v' k', CV t' v' k' ∧ Sim v v' ∧ k' + 7 * min k 1 ≤ 8 * k :=
  sim_below (k + 1) k (Nat.lt_succ_self k) hs h

/-! ## `≈c` -/

/-- Improvement within a constant factor (Moran–Sands Def. 4.1) for the clairvoyant semantics: in
every substitution and context, a derivation of `C[t]` of cost `k` gives one of `C[t']` of cost at
most `A * k`, with the same result when the result is a literal. -/
def CostWithin (A : Nat) (t t' : Term) : Prop :=
  ∀ (ρ : Nat → Term) (C v : Term) (k : Nat), CV (instantiate C (t.substitute ρ)) v k →
    ∃ v' k', CV (instantiate C (t'.substitute ρ)) v' k' ∧ k' ≤ A * k ∧ (Literal v → v' = v)

/-- `t ≈c t'`: each is within a constant factor of the other, in every context. -/
def CEquiv (t t' : Term) : Prop := ∃ A, CostWithin A t t' ∧ CostWithin A t' t

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

end Obend.Equiv
end
