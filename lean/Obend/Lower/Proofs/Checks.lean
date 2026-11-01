module
/-
# Obend.Lower.Proofs.Checks — the lowered term checks

`lower_typed`: a fragment term of type `T` (`LTyped`) lowers to a Core4 term with a derivation of
`PartialTyping {} Γ (lowerT e) T` in the lowered context, every binder `unrestricted` at a shareable
type, every λ `reusable`. `lower_checks`: so `checkAgainst` accepts it at `T` (through
`annotated_complete`, the checker's completeness): the lowered program is a checked `Code` the
judges apply to.
-/
public import Obend.Lower.Lower
public import Obend.Lower.Typing
public import Obend.Core.Proofs.BidirectionalCompleteness
public import Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Check
@[expose] public section
namespace Obend.Lower
open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.Bidirectional
open Obend.Core.TermTraverse (rename_comp)
set_option autoImplicit false

/-- The lowered context: every binder unrestricted. -/
def ctxOf (Γ : List Ty) : Context := Γ.map fun T => ⟨T, .unrestricted⟩

theorem good_shareable : ∀ {T : Ty}, good T = true → T.shareable = true
  | .natural, _ | .boolean, _ | .emptyRow, _ => rfl
  | .arrow .reusable .unrestricted _ _, _ => rfl
  | .field _ m t, h => by
    simp only [good, Bool.and_eq_true] at h
    simp [Ty.shareable, good_shareable h.1, good_shareable h.2]
  | .variant r, h => by simp only [good] at h; simp [Ty.shareable, good_shareable h]
  | .label, h | .variable _, h | .specification _ _, h | .prototype _ _, h | .custody _, h
  | .computation _ _ _, h => by simp [good] at h
  | .arrow .once _ _ _, h => by simp [good] at h
  | .arrow .reusable .erased _ _, h | .arrow .reusable .affine _ _, h | .arrow .reusable .linear _ _, h => by
    simp [good] at h

theorem good_not_computation {T : Ty} (h : good T = true) : T.isComputation = false :=
  Ty.shareable_not_computation T (good_shareable h)

/-! ## The usage side conditions hold in a lowered context -/

section Uses
variable {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true)
include hΓ

theorem mem_ctxOf {b : Binding} (h : b ∈ ctxOf Γ) : b.quantity = .unrestricted ∧ b.type.shareable = true := by
  simp only [ctxOf, List.mem_map] at h
  obtain ⟨T, hT, rfl⟩ := h
  exact ⟨rfl, good_shareable (hΓ T hT)⟩

theorem ctx_safe {u : Uses} (hu : u.length = Γ.length) : safeUses (ctxOf Γ) u = true := by
  simp only [safeUses, ctxOf, List.length_map, hu, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro p hp
  have := mem_ctxOf hΓ (List.of_mem_zip hp).1
  rw [this.1]; rfl

theorem ctx_linearFree (u : Uses) : linearFree (ctxOf Γ) u = true := by
  simp only [linearFree, List.all_eq_true]
  intro p hp
  have := mem_ctxOf hΓ (List.of_mem_zip hp).1
  simp [this.1]

theorem ctx_reusable {u : Uses} (hu : u.length = Γ.length) : reusableCaptures [] (ctxOf Γ) u = true := by
  simp only [reusableCaptures, ctxOf, List.length_map, hu, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro p hp
  have := mem_ctxOf hΓ (List.of_mem_zip hp).1
  simp [this.1, this.2]

theorem ctx_valid : validContext [] (ctxOf Γ) = true := by
  simp only [validContext, List.all_eq_true]
  intro b hb
  have := mem_ctxOf hΓ hb
  simp [this.2]

end Uses

theorem branches_unrestricted : ∀ (Γ : List Ty) (u v : Uses), branchesAgree (ctxOf Γ) u v = true
  | [], _, _ => by simp [ctxOf, branchesAgree]
  | _ :: _, [], _ => by simp [ctxOf, branchesAgree]
  | _ :: _, _ :: _, [] => by simp [ctxOf, branchesAgree]
  | T :: Γ, a :: u, b :: v => by
    simp only [ctxOf, List.map_cons, branchesAgree, Quantity.agrees, Bool.true_and]
    exact branches_unrestricted Γ u v

theorem cons_good {Γ : List Ty} {A : Ty} (hA : good A = true) (hΓ : ∀ T ∈ Γ, good T = true) :
    ∀ T ∈ A :: Γ, good T = true := by
  intro T h; rcases List.mem_cons.1 h with rfl | h
  · exact hA
  · exact hΓ T h

theorem argument_ok {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {A : Ty} (hA : good A = true) {u : Uses}
    (hu : u.length = Γ.length) : argumentAllowed {} .unrestricted (ctxOf Γ) A u = true := by
  simp only [argumentAllowed, good_not_computation hA, Bool.not_false, Bool.true_and,
    ctx_linearFree hΓ, Bool.or_true]
  simp [Ty.shareableUnder_empty, good_shareable hA, ctx_reusable hΓ hu]

theorem lam_typed {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {A B : Ty} (hA : good A = true) {body : Term}
    {u : Uses} (h : PartialTyping {} (ctxOf (A :: Γ)) body B u) :
    PartialTyping {} (ctxOf Γ) (.lam body) (fn A B) u.tail := by
  have hl := Obend.Core.MachineTyping.source_uses_length h
  have hΓ' := cons_good hA hΓ
  refine .lambda (annotation := ⟨A, B, .unrestricted, .reusable⟩) h (ctx_safe hΓ' (by simpa [ctxOf] using hl))
    (ctx_valid hΓ') ?_ (by simp [Quantity.fits])
  simp only [reusableAllowed, bne_self_eq_false, Bool.false_or]
  apply ctx_reusable hΓ
  simp only [ctxOf, List.length_map, List.length_cons] at hl
  simp [hl]

theorem app_typed {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {A B : Ty} (hA : good A = true) {f a : Term}
    {u v : Uses} (hf : PartialTyping {} (ctxOf Γ) f (fn A B) u) (ha : PartialTyping {} (ctxOf Γ) a A v) :
    PartialTyping {} (ctxOf Γ) (.app f a) B (addUses u v) := by
  have hl := Obend.Core.MachineTyping.source_uses_length ha
  exact .application hf ha rfl rfl (argument_ok hΓ hA (by simpa [ctxOf] using hl))

/-- Weakening by one unrestricted binder of a good type. -/
theorem weaken1 {Γ : List Ty} {A T : Ty} (hA : good A = true) {t : Term} {u : Uses}
    (h : PartialTyping {} (ctxOf Γ) t T u) : PartialTyping {} (ctxOf (A :: Γ)) (t.rename Nat.succ) T (0 :: u) :=
  Obend.Core.Proofs.Preservation.source_weaken h ⟨A, .unrestricted⟩ (by simp [validContext, good_shareable hA])

/-! ## Rows -/

theorem labels_of_nodup : ∀ {l : List (String × Term)}, (l.map Prod.fst).Nodup → labelsDistinct l = true
  | [], _ => rfl
  | (n, _) :: rest, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [labelsDistinct, labels_of_nodup h.2, Bool.and_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.any_eq_false]
    intro x hx e
    exact h.1 (by simp only [beq_iff_eq] at e; rw [← e]; exact List.mem_map_of_mem hx)

theorem good_fieldRow : ∀ (ns : List String) (Ts : List Ty), (∀ T ∈ Ts, good T = true) →
    good (fieldRow (ns.zip Ts)) = true
  | [], _, _ | _ :: _, [], _ => rfl
  | n :: ns, T :: Ts, h => by
    simp only [List.zip_cons_cons, fieldRow, good, Bool.and_eq_true]
    exact ⟨h T (by simp), good_fieldRow ns Ts (fun T' m => h T' (by simp [m]))⟩

theorem fieldRow_tail : ∀ (l : List (String × Ty)), (fieldRow l).tail = .emptyRow
  | [] => rfl
  | (_, _) :: l => by simp only [fieldRow, Ty.tail]; exact fieldRow_tail l

theorem fieldRow_labels : ∀ (l : List (String × Ty)), spineLabels (fieldRow l) = l.map Prod.fst
  | [] => rfl
  | (_, _) :: l => by simp only [fieldRow, spineLabels, List.map_cons, fieldRow_labels l]

theorem lookup_fieldRow : ∀ (l : List (String × Ty)) (n : String) (T : Ty), (l.map Prod.fst).Nodup →
    (n, T) ∈ l → (fieldRow l).lookup [] l.length n = some T
  | [], _, _, _, h => by simp at h
  | (m, U) :: l, n, T, nd, h => by
    simp only [List.map_cons, List.nodup_cons] at nd
    simp only [fieldRow, List.length_cons, Ty.lookup]
    rcases List.mem_cons.1 h with e | h
    · cases e; simp
    · have hne : m ≠ n := fun e => nd.1 (by rw [e]; exact List.mem_map_of_mem (f := Prod.fst) h)
      simp only [hne, ite_false]; exact lookup_fieldRow l n T nd.2 h

theorem zip_fst {ns : List String} {Ts : List Ty} (h : ns.length = Ts.length) : (ns.zip Ts).map Prod.fst = ns := by
  rw [List.map_fst_zip]; omega

theorem armsRow_good : ∀ (arms : List (String × List String × LExpr)) (sig : List (List Ty)),
    (∀ p ∈ arms.zip sig, ∀ T ∈ p.2, good T = true) → good (armsRow arms sig) = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | (l, ns, M) :: arms, Ts :: sig, h => by
    simp only [armsRow, good, Bool.and_eq_true]
    exact ⟨good_fieldRow ns Ts (h ((l, ns, M), Ts) (by simp)), armsRow_good arms sig (fun p m => h p (by simp [m]))⟩

/-! ## The destructor's spine -/

theorem caseAllowed_ok {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {u : Uses} (hu : u.length = Γ.length) :
    caseAllowed {} .unrestricted (ctxOf Γ) u = true := by
  simp [caseAllowed, ctx_linearFree hΓ, ctx_reusable hΓ hu]

theorem spine_ok {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {u : Uses} (hu : u.length = Γ.length) (row R : Ty) :
    ∀ (ns : List String) (Ts : List Ty), ns.length = Ts.length → (∀ T ∈ Ts, good T = true) →
      (∀ p ∈ ns.zip Ts, ∃ fuel, row.lookup [] fuel p.1 = some p.2) →
      SplitSpine {} (ctxOf Γ) u row ns (curry Ts R) R
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp at h
  | n :: ns, T :: Ts, hl, hg, hk => by
    obtain ⟨fuel, hf⟩ := hk (n, T) (by simp)
    refine ⟨.reusable, .unrestricted, T, curry Ts R, rfl, ⟨fuel, T, hf, sameType_refl _ _⟩,
      good_not_computation (hg T (by simp)), caseAllowed_ok hΓ hu, ?_, ?_⟩
    · simp [good_shareable (hg T (by simp))]
    · exact spine_ok hΓ hu row R ns Ts (by simpa using hl) (fun T' m => hg T' (by simp [m]))
        (fun p m => hk p (by simp [m]))

theorem split_typed {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {ns : List String} {Ts : List Ty} {R : Ty}
    (hl : ns.length = Ts.length) (nd : ns.Nodup) (hg : ∀ T ∈ Ts, good T = true) {m F : Term} {u v : Uses}
    (hm : PartialTyping {} (ctxOf Γ) m (fieldRow (ns.zip Ts)) u) (hF : PartialTyping {} (ctxOf Γ) F (curry Ts R) v) :
    PartialTyping {} (ctxOf Γ) (.split m ns F) R (addUses u v) := by
  have hu := Obend.Core.MachineTyping.source_uses_length hm
  refine .split hm hF nd ?_ (spine_ok hΓ (by simpa [ctxOf] using hu) _ R ns Ts hl hg ?_)
  · simp only [SplitCovers, fieldRow_tail, beq_self_eq_true, fieldRow_labels, zip_fst hl, Bool.true_and,
      List.all_eq_true]
    intro x hx; simpa using hx
  · intro p hp
    exact ⟨_, lookup_fieldRow _ _ _ (by rw [zip_fst hl]; exact nd) hp⟩

/-! ## Fields and arms -/

theorem fields_typed {Γ : List Ty} : ∀ (fs : List (String × LExpr)) (Ts : List Ty), fs.length = Ts.length →
    (∀ T ∈ Ts, good T = true) → (∀ p ∈ fs.zip Ts, ∃ u, PartialTyping {} (ctxOf Γ) (lowerT p.1.2) p.2 u) →
    ∃ u, FieldsTyping {} (ctxOf Γ) (fs.map fun x => (x.1, lowerT x.2)) (fieldRow ((fs.map Prod.fst).zip Ts)) u
  | [], [], _, _, _ => ⟨_, .nil _⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp at h
  | (n, e) :: fs, T :: Ts, hl, hg, ih => by
    obtain ⟨u, he⟩ := ih ((n, e), T) (by simp)
    obtain ⟨v, hr⟩ := fields_typed fs Ts (by simpa using hl) (fun T' m => hg T' (by simp [m]))
      (fun p m => ih p (by simp [m]))
    exact ⟨_, .cons he hr (good_not_computation (hg T (by simp)))⟩

theorem arms_typed {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {R : Ty} :
    ∀ (arms : List (String × List String × LExpr)) (sig : List (List Ty)), arms.length = sig.length →
      (∀ p ∈ arms.zip sig, p.1.2.1.length = p.2.length) → (∀ p ∈ arms.zip sig, p.1.2.1.Nodup) →
      (∀ p ∈ arms.zip sig, ∀ T ∈ p.2, good T = true) →
      (∀ p ∈ arms.zip sig, ∃ u, PartialTyping {} (ctxOf Γ) (lowerT p.1.2.2) (curry p.2 R) u) →
      ∃ u, ArmsTyping {} (ctxOf Γ) .unrestricted (arms.map fun x => (x.1, caseArm x.2.1 (lowerT x.2.2)))
        (armsRow arms sig) R u
  | [], [], _, _, _, _, _ => ⟨_, .nil _ _ _⟩
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => by simp at h
  | (l, ns, M) :: arms, Ts :: sig, hl, hlen, hnd, hg, ih => by
    have hgTs := hg ((l, ns, M), Ts) (by simp)
    have hP := good_fieldRow ns Ts hgTs
    have hΓ' := cons_good hP hΓ
    obtain ⟨u, hM⟩ := ih ((l, ns, M), Ts) (by simp)
    have hM' := weaken1 (A := fieldRow (ns.zip Ts)) hP hM
    have hb : PartialTyping {} (ctxOf (fieldRow (ns.zip Ts) :: Γ)) (.bound 0) (fieldRow (ns.zip Ts))
        (variableUses (ctxOf (fieldRow (ns.zip Ts) :: Γ)) 0) := .bound (binding := ⟨_, .unrestricted⟩) rfl
    have body := split_typed hΓ' (hlen ((l, ns, M), Ts) (by simp)) (hnd ((l, ns, M), Ts) (by simp)) hgTs hb hM'
    obtain ⟨w, hr⟩ := arms_typed hΓ arms sig (by simpa using hl) (fun p m => hlen p (by simp [m]))
      (fun p m => hnd p (by simp [m])) (fun p m => hg p (by simp [m])) (fun p m => ih p (by simp [m]))
    have hbl := Obend.Core.MachineTyping.source_uses_length body
    refine ⟨_, .cons body (ctx_safe hΓ' (by simpa [ctxOf] using hbl)) ?_ (by simp [Quantity.fits]) hr ?_⟩
    · simp [validContext, good_shareable hP]
    · simp [branches_unrestricted]

/-! ## The lowered term is typed -/

theorem bound_typed {Γ : List Ty} {i : Nat} {T : Ty} (h : Γ[i]? = some T) :
    PartialTyping {} (ctxOf Γ) (.bound i) T (variableUses (ctxOf Γ) i) :=
  .bound (binding := ⟨T, .unrestricted⟩) (by simp [ctxOf, h])


/-! ## The lowered term is typed -/

theorem shift3 (t : Term) : ((t.rename Nat.succ).rename Nat.succ).rename Nat.succ = t.rename (· + 3) := by
  rw [rename_comp, rename_comp]

theorem shift4 (t : Term) :
    (((t.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ = t.rename (· + 4) := by
  rw [rename_comp, rename_comp, rename_comp]

theorem natOp_types (op : NatOp) : primitiveTypes op.prim = (.natural, op.resultTy) := by
  cases op <;> rfl

/-- `Nat.rec z s m` lowered is typed at the motive's type. -/
theorem natRec_typed {Γ : List Ty} (hΓ : ∀ T ∈ Γ, good T = true) {T : Ty} (hT : good T = true)
    {Z S M : Term} {zu su mu : Uses}
    (hZ : PartialTyping {} (ctxOf Γ) Z T zu) (hS : PartialTyping {} (ctxOf Γ) S (fn .natural (fn T T)) su)
    (hM : PartialTyping {} (ctxOf Γ) M .natural mu) :
    ∃ u, PartialTyping {} (ctxOf Γ) (.app (.fix (natRecSpec Z S) box) M) T u := by
  have gN : good .natural = true := rfl
  have gE : good .emptyRow = true := rfl
  have gF : good (fn .natural T) = true := by simp [good, hT]
  have Γ1 := cons_good gF hΓ
  have Γ2 := cons_good gE Γ1
  have Γ3 := cons_good gN Γ2
  have Γ4 := cons_good gN Γ3
  have Z3 := weaken1 gN (weaken1 gE (weaken1 gF hZ))
  rw [shift3] at Z3
  have S4 := weaken1 gN (weaken1 gN (weaken1 gE (weaken1 gF hS)))
  rw [shift4] at S4
  have p0 : PartialTyping {} (ctxOf (.natural :: .natural :: .emptyRow :: fn .natural T :: Γ)) (.bound 0) .natural _ :=
    bound_typed rfl
  have self3 : PartialTyping {} (ctxOf (.natural :: .natural :: .emptyRow :: fn .natural T :: Γ)) (.bound 3)
      (fn .natural T) _ := bound_typed rfl
  have step := app_typed Γ4 hT (app_typed Γ4 gN S4 p0) (app_typed Γ4 gN self3 p0)
  have k0 : PartialTyping {} (ctxOf (.natural :: .emptyRow :: fn .natural T :: Γ)) (.bound 0) .natural _ :=
    bound_typed rfl
  have hl := Obend.Core.MachineTyping.source_uses_length step
  have body : PartialTyping {} (ctxOf (.natural :: .emptyRow :: fn .natural T :: Γ))
      (.ifZero (.bound 0) (Z.rename (· + 3))
        (.app (.app (S.rename (· + 4)) (.bound 0)) (.app (.bound 3) (.bound 0)))) T _ :=
    .ifZero k0 Z3 step (ctx_safe Γ4 (by simpa [ctxOf] using hl)) (branches_unrestricted _ _ _)
  have spec := lam_typed hΓ gF (lam_typed Γ1 gE (lam_typed Γ2 gN body))
  have boxT : PartialTyping {} (ctxOf Γ) box .emptyRow (zeroUses (ctxOf Γ)) := .record (.nil _) rfl
  have sl := Obend.Core.MachineTyping.source_uses_length spec
  have fixT : PartialTyping {} (ctxOf Γ) (.fix (natRecSpec Z S) box) (fn .natural T) _ :=
    .fix spec rfl boxT (by simp [good_shareable gF])
      (argument_ok hΓ gE (by simp [zeroUses, ctxOf]))
      (ctx_reusable hΓ (by simpa [ctxOf] using sl))
  exact ⟨_, app_typed hΓ gN fixT hM⟩

/-- **The lowering is type-correct**: a fragment term of type `T` lowers to a Core4 term of type `T`
in the lowered context. -/
theorem lower_typed {Γ : List Ty} {e : LExpr} {T : Ty} (h : LTyped Γ e T) :
    (∀ T ∈ Γ, good T = true) → ∃ u, PartialTyping {} (ctxOf Γ) (lowerT e) T u := by
  induction h with
  | bvar hi => intro hΓ; simp only [lowerT]; exact ⟨_, bound_typed hi⟩
  | erased Γ => intro hΓ; simp only [lowerT, box]; exact ⟨_, .record (.nil _) rfl⟩
  | const _ ih => intro hΓ; simp only [lowerT]; exact ih hΓ
  | app _ _ hA ihf iha =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hf⟩ := ihf hΓ; obtain ⟨v, ha⟩ := iha hΓ
    exact ⟨_, app_typed hΓ hA hf ha⟩
  | lam hA _ ih =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hb⟩ := ih (cons_good hA hΓ)
    exact ⟨_, lam_typed hΓ hA hb⟩
  | letE hA _ _ ihv ihb =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hv⟩ := ihv hΓ; obtain ⟨w, hb⟩ := ihb (cons_good hA hΓ)
    exact ⟨_, app_typed hΓ hA (lam_typed hΓ hA hb) hv⟩
  | lit Γ n => intro hΓ; simp only [lowerT]; exact ⟨_, .natural _ _⟩
  | natSucc _ ih =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, ha⟩ := ih hΓ
    exact ⟨_, .binary rfl ha (.natural _ _)⟩
  | natBin op _ _ ihl ihr =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hl⟩ := ihl hΓ; obtain ⟨v, hr⟩ := ihr hΓ
    exact ⟨_, .binary (natOp_types op) hl hr⟩
  | boolLit Γ b => intro hΓ; simp only [lowerT]; exact ⟨_, .boolean _ _⟩
  | natRec hT _ _ _ ihz ihs ihm =>
    intro hΓ; simp only [lowerT]
    obtain ⟨_, hz⟩ := ihz hΓ; obtain ⟨_, hs⟩ := ihs hΓ; obtain ⟨_, hm⟩ := ihm hΓ
    exact natRec_typed hΓ hT hz hs hm
  | boolRec _ _ _ ihx ihy ihm =>
    intro hΓ; simp only [lowerT]
    obtain ⟨_, hx⟩ := ihx hΓ; obtain ⟨_, hy⟩ := ihy hΓ; obtain ⟨_, hm⟩ := ihm hΓ
    exact ⟨_, .ifBool hm hy hx (branches_unrestricted _ _ _)⟩
  | record hl nd hg _ ih =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hf⟩ := fields_typed _ _ hl hg (fun p m => ih p m hΓ)
    exact ⟨_, .record hf (labels_of_nodup (by simpa [List.map_map, Function.comp_def] using nd))⟩
  | split hl nd hg _ _ ihm ihF =>
    intro hΓ; simp only [lowerT]
    obtain ⟨_, hm⟩ := ihm hΓ; obtain ⟨_, hF⟩ := ihF hΓ
    exact ⟨_, split_typed hΓ hl nd hg hm hF⟩
  | proj _ hk ih =>
    intro hΓ; simp only [lowerT]
    obtain ⟨_, ht⟩ := ih hΓ
    exact ⟨_, .get ht hk (ctx_linearFree hΓ _)⟩
  | inject hl nd hg _ hk ih =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hf⟩ := fields_typed _ _ hl hg (fun p m => ih p m hΓ)
    refine ⟨_, .inject (.record hf (labels_of_nodup (by simpa [List.map_map, Function.comp_def] using nd))) hk ?_⟩
    exact good_not_computation (good_fieldRow _ _ hg)
  | cases hl nd _ hlen hnd hg hR _ ihm iharms =>
    intro hΓ; simp only [lowerT]
    obtain ⟨u, hm⟩ := ihm hΓ
    obtain ⟨v, ha⟩ := arms_typed hΓ _ _ hl hlen hnd hg (fun p m => iharms p m hΓ)
    have hu := Obend.Core.MachineTyping.source_uses_length hm
    exact ⟨_, .case hm ha (labels_of_nodup (by simpa [List.map_map, Function.comp_def] using nd))
      (caseAllowed_ok hΓ (by simpa [ctxOf] using hu))⟩

/-- **`lower_checks`**: a closed fragment term of type `T` lowers to a term `checkAgainst` accepts at
`T`, with every binder unrestricted and every λ reusable. -/
theorem lower_checks {e : LExpr} {T : Ty} (h : LTyped [] e T) :
    ∃ annotations checked, checkAgainst ⟨lowerT e, annotations, {}⟩ [] T = .ok checked := by
  obtain ⟨u, typed⟩ := lower_typed h (by simp)
  have hu := Obend.Core.MachineTyping.source_uses_length typed
  obtain ⟨annotations, checked, accepted, _⟩ :=
    Obend.Core.Proofs.BidirectionalCompleteness.annotated_complete (source := ⟨lowerT e, fun _ => none, {}⟩)
      typed (ctx_safe (Γ := []) (by simp) (by simpa [ctxOf] using hu)) (ctx_valid (Γ := []) (by simp))
      (by simp [Assumptions.valid])
  exact ⟨annotations, checked, accepted⟩

end Obend.Lower
end
