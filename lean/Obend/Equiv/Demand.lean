module
/- The demand semantics of first-order objects (Xia, Israel, Kramarz, Coltharp, Claessen, Weirich,
Li, ICFP 2024, Thms 3.8 and 3.9), for the knot of `Obend.Equiv.Clairvoyant`.

The fragment: an object `fix (λself. λsuper. {n₁ = e₁, …}) {}` whose fields are literals or
selections from `self` (`FE`), with distinct names, and the program that selects one of its fields.
It contains the three measured programs (`{good = 7, bad = self.bad}.good`, `.bad`, and
`{a = 7, b = self.a}.b`) and every chain of fields reading fields.

`demand fs x` is a function of the demand: it follows the chain from `x` to a literal and charges
each link once (`chase`). Against the clairvoyant relation:
- `demand_exists` (Thm 3.8 shape): when the demand is defined, a derivation of that cost exists, with
  the demanded value;
- `demand_minimal` (Thm 3.9 shape, with totality): every derivation of the selection has a defined
  demand, the same value, and costs at least the demand.
So `demand fs x` is the least clairvoyant cost of the selection (`demand_is_least`).

The proof of minimality reads any derivation: the template is settled once (`head_template`, at
least `headCost`), and across the waves a field reading `self` is evaluated at most once, at cost
2, after the field it reads (`knot_invariant`): the evaluated fields are closed under reading and
their values are the chase's. -/
public import Obend.Equiv.CostTests
@[expose] public section
namespace Obend.Equiv.Demand
open Obend.Core.Term
open Obend.Equiv
open Obend.Equiv.CostTests (record_nil_settled cv_beta_value get_not_settled)
set_option autoImplicit false

/-! ## The fragment -/

/-- A field: a literal, or the selection of a field of `self`. -/
inductive FE where
  | lit (v : Nat)
  | ref (m : String)

/-- The field as a term, `self` being `s`. -/
def FE.at (s : Term) : FE → Term
  | .lit v => .nat v
  | .ref m => .get s m

theorem FE.at_substitute (e : FE) (s : Term) (σ : Nat → Term) :
    (e.at s).substitute σ = e.at (s.substitute σ) := by
  cases e <;> simp [FE.at, Term.substitute]

theorem FE.at_rename (e : FE) (s : Term) (f : Nat → Nat) : (e.at s).rename f = e.at (s.rename f) := by
  cases e <;> simp [FE.at, Term.rename]

/-- The record's fields, `self` being `s`. -/
def entries (s : Term) (fs : List (String × FE)) : List (String × Term) := fs.map fun f => (f.1, f.2.at s)

theorem entries_substitute (s : Term) (fs : List (String × FE)) (σ : Nat → Term) :
    (entries s fs).map (fun f => (f.1, f.2.substitute σ)) = entries (s.substitute σ) fs := by
  simp [entries, FE.at_substitute]

theorem entries_rename (s : Term) (fs : List (String × FE)) (r : Nat → Nat) :
    (entries s fs).map (fun f => (f.1, f.2.rename r)) = entries (s.rename r) fs := by
  simp [entries, FE.at_rename]

def objLam (fs : List (String × FE)) : Term := .lam (.lam (.record (entries (.bound 1) fs)))

/-- The object. -/
def obj (fs : List (String × FE)) : Term := .fix (objLam fs) (.record [])

def look (fs : List (String × FE)) (x : String) : Option FE := (fs.find? (·.1 == x)).map (·.2)

/-- Follow the chain from `x` to a literal: its value and the number of selections on the way. -/
def chase (fs : List (String × FE)) : Nat → String → Option (Nat × Nat)
  | 0, _ => none
  | k + 1, x => match look fs x with
    | some (.lit v) => some (v, 0)
    | some (.ref m) => (chase fs k m).map fun p => (p.1, p.2 + 1)
    | none => none

def hasRef (fs : List (String × FE)) : Bool := fs.any fun f => match f.2 with | .ref _ => true | .lit _ => false

/-- What settling the template costs: two β steps, and the head record unless it is a value. -/
def headCost (fs : List (String × FE)) : Nat := if hasRef fs then 3 else 2

/-- **The demand semantics**: the value of `x` and the cost of the selection, the template once,
each selection on the chain once (2), the knot and the selection (2). -/
def demand (fs : List (String × FE)) (x : String) : Option (Nat × Nat) :=
  (chase fs fs.length x).map fun p => (p.1, headCost fs + 2 * p.2 + 2)

/-! ## The chase -/

theorem chase_fuel {fs : List (String × FE)} : ∀ {k x u d}, chase fs k x = some (u, d) →
    d + 1 ≤ k ∧ ∀ k', d + 1 ≤ k' → chase fs k' x = some (u, d)
  | 0, x, u, d, h => by simp [chase] at h
  | k + 1, x, u, d, h => by
    simp only [chase] at h
    split at h
    · rename_i v hl
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, fun k' hk => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
      simp [chase, hl]
    · rename_i m hl
      obtain ⟨⟨u', d'⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨b, f⟩ := chase_fuel hc
      refine ⟨by omega, fun k' hk => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
      simp [chase, hl, f j (by omega)]
    · cases h

theorem chase_unique {fs : List (String × FE)} {k k' : Nat} {x : String} {a b : Nat × Nat}
    (h : chase fs k x = some a) (h' : chase fs k' x = some b) : a = b := by
  obtain ⟨u, d⟩ := a
  obtain ⟨u', d'⟩ := b
  obtain ⟨b1, f1⟩ := chase_fuel h
  obtain ⟨b2, f2⟩ := chase_fuel h'
  have := f1 (max k k') (by omega)
  rw [f2 (max k k') (by omega)] at this
  exact (Option.some.inj this).symm

/-- `j` steps along the selections. -/
def walk (fs : List (String × FE)) : Nat → String → Option String
  | 0, x => some x
  | j + 1, x => match look fs x with
    | some (.ref m) => walk fs j m
    | _ => none

theorem walk_add (fs : List (String × FE)) : ∀ (a b : Nat) (x : String),
    walk fs (a + b) x = (walk fs a x).bind (walk fs b)
  | 0, b, x => by simp [walk]
  | a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [walk]
    split
    · exact walk_add fs a b _
    · rfl

/-- A successful chase walks `d` selections to a literal, through selections. -/
theorem chase_walk {fs : List (String × FE)} : ∀ {k x u d}, chase fs k x = some (u, d) →
    (∃ z, walk fs d x = some z ∧ look fs z = some (.lit u)) ∧
      ∀ i < d, ∃ z m, walk fs i x = some z ∧ look fs z = some (.ref m)
  | 0, x, u, d, h => by simp [chase] at h
  | k + 1, x, u, d, h => by
    simp only [chase] at h
    split at h
    · rename_i v hl
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨x, rfl, hl⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rename_i m hl
      obtain ⟨⟨u', d'⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨⟨z, hz, hlz⟩, hi⟩ := chase_walk hc
      refine ⟨⟨z, by simp [walk, hl, hz], hlz⟩, fun i hlt => ?_⟩
      cases i with
      | zero => exact ⟨x, m, rfl, hl⟩
      | succ i =>
        obtain ⟨z', m', h1, h2⟩ := hi i (by omega)
        exact ⟨z', m', by simp [walk, hl, h1], h2⟩
    · cases h

theorem walk_beyond {fs : List (String × FE)} {d : Nat} {x z : String} {u : Nat}
    (hz : walk fs d x = some z) (hl : look fs z = some (.lit u)) : ∀ j, walk fs (d + j + 1) x = none := by
  intro j
  rw [show d + j + 1 = d + (j + 1) by omega, walk_add, hz]
  simp only [Option.bind_some]
  rw [show j + 1 = 0 + j + 1 by omega]
  induction j with
  | zero => simp [walk, hl]
  | succ j _ => rw [show 0 + (j + 1) + 1 = (j + 1) + 1 by omega]; simp [walk, hl]

/-- The walk of a successful chase visits distinct fields. -/
theorem chase_walk_injective {fs : List (String × FE)} {k : Nat} {x : String} {u d : Nat}
    (h : chase fs k x = some (u, d)) {i j : Nat} {z : String} (hi : walk fs i x = some z)
    (hj : walk fs j x = some z) : i = j := by
  obtain ⟨⟨zd, hzd, hld⟩, refs⟩ := chase_walk h
  have le : ∀ {i z}, walk fs i x = some z → i ≤ d := by
    intro i z hw
    rcases Nat.lt_or_ge d i with hc | hc
    · have := walk_beyond hzd hld (i - d - 1)
      rw [show d + (i - d - 1) + 1 = i by omega, hw] at this
      cases this
    · exact hc
  have hi' := le hi
  have hj' := le hj
  -- from equal points, the walk to the literal is shorter on the later side
  have key : ∀ {a b}, a < b → walk fs a x = some z → walk fs b x = some z → b ≤ d → False := by
    intro a b hab ha hb hbd
    have e1 : walk fs d x = (walk fs b x).bind (walk fs (d - b)) := by
      rw [← walk_add]; congr 1; omega
    have e2 : walk fs (a + (d - b)) x = (walk fs a x).bind (walk fs (d - b)) := walk_add fs a (d - b) x
    rw [hb] at e1
    rw [ha, ← e1, hzd] at e2
    obtain ⟨z', m', hw', hl'⟩ := refs (a + (d - b)) (by omega)
    rw [hw'] at e2
    cases e2
    rw [hl'] at hld
    cases hld
  rcases Nat.lt_trichotomy i j with lt | eq | gt
  · exact absurd (key lt hi hj hj') id
  · exact eq
  · exact absurd (key gt hj hi hi') id

theorem look_mem {fs : List (String × FE)} {z : String} {e : FE} (h : look fs z = some e) :
    z ∈ fs.map Prod.fst := by
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hf
  have hn := List.find?_some hf
  simp at hn
  exact List.mem_map.2 ⟨f, hm, hn⟩

/-- The points of the walk, as names. -/
def path (fs : List (String × FE)) (x : String) (d : Nat) : List String :=
  (List.range d).map fun i => (walk fs i x).getD ""

theorem path_nodup {fs : List (String × FE)} {k : Nat} {x : String} {u d : Nat}
    (h : chase fs k x = some (u, d)) {e : Nat}
    (some_of : ∀ i < e, ∃ z, walk fs i x = some z) : (path fs x e).Nodup := by
  unfold path List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro i j hi hj ne eq
  apply ne
  simp only [List.mem_range] at hi hj
  obtain ⟨zi, hzi⟩ := some_of i hi
  obtain ⟨zj, hzj⟩ := some_of j hj
  rw [hzi, hzj] at eq
  simp only [Option.getD_some] at eq
  subst eq
  exact chase_walk_injective h hzi hzj

/-- A successful chase is no longer than the object. -/
theorem chase_short {fs : List (String × FE)} {k : Nat} {x : String} {u d : Nat}
    (h : chase fs k x = some (u, d)) : d + 1 ≤ fs.length := by
  obtain ⟨⟨zd, hzd, hld⟩, refs⟩ := chase_walk h
  have some_of : ∀ i < d + 1, ∃ z, walk fs i x = some z := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with lt | rfl
    · obtain ⟨z, _, hz, _⟩ := refs i lt; exact ⟨z, hz⟩
    · exact ⟨zd, hzd⟩
  have nd := path_nodup h some_of
  have sub : path fs x (d + 1) ⊆ fs.map Prod.fst := by
    intro n hn
    simp only [path, List.mem_map, List.mem_range] at hn
    obtain ⟨i, hi, rfl⟩ := hn
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with lt | rfl
    · obtain ⟨z, m, hz, hl⟩ := refs i lt
      rw [hz]; exact look_mem hl
    · rw [hzd]; exact look_mem hld
  have := nd.length_le_of_subset sub
  simpa [path] using this


/-! ## What any derivation settles: the template, then the waves -/

def isSkipped : Term → Bool
  | .hole 0 [] => true
  | _ => false

theorem isSkipped_iff {t : Term} : isSkipped t = true ↔ t = skipped := by
  constructor
  · intro h
    unfold isSkipped at h
    split at h
    · rfl
    · cases h
  · intro h; subst h; rfl

theorem not_isSkipped {t : Term} (h : t ≠ skipped) : isSkipped t = false := by
  cases hb : isSkipped t
  · rfl
  · exact absurd (isSkipped_iff.1 hb) h

/-- A template entry: the field with `self` open or skipped, or skipped altogether. -/
def EntryOK (e : FE) (t : Term) : Prop := t = e.at (.bound 0) ∨ t = e.at skipped ∨ t = skipped

inductive TplOK : List (String × FE) → List (String × Term) → Prop where
  | nil : TplOK [] []
  | cons {n : String} {e : FE} {t : Term} {fs : List (String × FE)} {ts : List (String × Term)} :
      EntryOK e t → TplOK fs ts → TplOK ((n, e) :: fs) ((n, t) :: ts)

/-- An approximant entry: a literal's is its template entry; a selection's is `skipped`, or the
value of the field it reads in `G`, which is its chase's. -/
def CellOK (FS : List (String × FE)) (G : List (String × Term)) (n : String) : FE → Term → Term → Prop
  | .lit _, t, p => p = t
  | .ref m, t, p => p = skipped ∨ (t = .get (.bound 0) m ∧ ∃ u, p = .nat u ∧
      G.find? (·.1 == m) = some (m, .nat u) ∧ ∃ k d, chase FS k n = some (u, d))

inductive AppOK (FS : List (String × FE)) (G : List (String × Term)) :
    List (String × FE) → List (String × Term) → List (String × Term) → Prop where
  | nil : AppOK FS G [] [] []
  | cons {n : String} {e : FE} {t p : Term} {fs : List (String × FE)} {ts ps : List (String × Term)} :
      CellOK FS G n e t p → AppOK FS G fs ts ps → AppOK FS G ((n, e) :: fs) ((n, t) :: ts) ((n, p) :: ps)

/-- The selections evaluated in an approximant. -/
def knownNames : List (String × FE) → List (String × Term) → List String
  | (n, .ref _) :: fs, (_, p) :: ps => if isSkipped p then knownNames fs ps else n :: knownNames fs ps
  | (_, .lit _) :: fs, _ :: ps => knownNames fs ps
  | _, _ => []

/-- A later approximant keeps every entry the earlier one knows. -/
inductive Ext : List (String × Term) → List (String × Term) → Prop where
  | nil : Ext [] []
  | cons {n : String} {p q : Term} {ps qs : List (String × Term)} :
      (p ≠ skipped → q = p) → Ext ps qs → Ext ((n, p) :: ps) ((n, q) :: qs)

theorem find_ext {G G' : List (String × Term)} (h : Ext G G') {m : String} {x : Term}
    (hf : G.find? (·.1 == m) = some (m, x)) (hx : x ≠ skipped) : G'.find? (·.1 == m) = some (m, x) := by
  induction h with
  | nil => simp at hf
  | @cons n p q ps qs hpq _ ih =>
    by_cases hn : n = m
    · subst hn
      simp only [List.find?_cons, beq_self_eq_true] at hf ⊢
      cases hf
      rw [hpq hx]
    · have hb : (n == m) = false := by simpa using hn
      simp only [List.find?_cons, hb] at hf ⊢
      exact ih hf

theorem cellOK_ext {FS : List (String × FE)} {G G' : List (String × Term)} (hx : Ext G G') {n : String}
    {e : FE} {t p : Term} (h : CellOK FS G n e t p) : CellOK FS G' n e t p := by
  cases e with
  | lit v => exact h
  | ref m =>
    rcases h with h | ⟨ht, u, hp, hf, hc⟩
    · exact .inl h
    · exact .inr ⟨ht, u, hp, find_ext hx hf (by intro e; cases e), hc⟩

theorem appOK_ext {FS : List (String × FE)} {G G' : List (String × Term)} (hx : Ext G G')
    {fs : List (String × FE)} {ts ps : List (String × Term)} (h : AppOK FS G fs ts ps) : AppOK FS G' fs ts ps := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (cellOK_ext hx hc) ih

theorem entry_settled {FS : List (String × FE)} {G : List (String × Term)} {n : String} {e : FE}
    {t p : Term} (he : EntryOK e t) (h : CellOK FS G n e t p) : Settled p := by
  cases e with
  | lit v =>
    have hp : p = t := h
    subst hp
    rcases he with rfl | rfl | rfl <;> first | exact .skipped | exact .value (.nat v)
  | ref m =>
    rcases h with rfl | ⟨_, u, rfl, _⟩
    · exact .skipped
    · exact .value (.nat u)

theorem appOK_value {FS : List (String × FE)} {G : List (String × Term)} {fs : List (String × FE)}
    {ts ps : List (String × Term)} (ht : TplOK fs ts) (h : AppOK FS G fs ts ps) : CValue (.record ps) := by
  refine .record ?_
  induction h with
  | nil => simp
  | cons hc _ ih =>
    cases ht with
    | cons he ht' =>
      intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact entry_settled he hc
      · exact ih ht' f hf

/-- Reading a name in an approximant: the field, its template entry, its invariant. -/
theorem find_appOK {FS : List (String × FE)} {G : List (String × Term)} :
    ∀ {fs : List (String × FE)} {ts ps : List (String × Term)}, TplOK fs ts → AppOK FS G fs ts ps →
      ∀ {z : String} {q : Term}, ps.find? (·.1 == z) = some (z, q) →
        ∃ e t, fs.find? (·.1 == z) = some (z, e) ∧ EntryOK e t ∧ CellOK FS G z e t q ∧
          (∀ m, e = .ref m → q ≠ skipped → z ∈ knownNames fs ps)
  | [], [], [], _, _, z, q, hf => by simp at hf
  | (n, e) :: fs, (_, t) :: ts, (_, p) :: ps, .cons he ht, .cons hc hr, z, q, hf => by
    by_cases hn : n = z
    · subst hn
      simp only [List.find?_cons, beq_self_eq_true] at hf
      cases hf
      refine ⟨e, t, by simp, he, hc, ?_⟩
      intro m hm hq
      subst hm
      simp [knownNames, not_isSkipped hq]
    · have hb : (n == z) = false := by simpa using hn
      simp only [List.find?_cons, hb] at hf
      obtain ⟨e', t', h1, h2, h3, h4⟩ := find_appOK ht hr hf
      refine ⟨e', t', by simp [hb, h1], h2, h3, ?_⟩
      intro m hm hq
      have := h4 m hm hq
      cases e with
      | lit v => simpa [knownNames] using this
      | ref m' =>
        simp only [knownNames]
        split
        · exact this
        · exact List.mem_cons_of_mem _ this

theorem look_of_find {fs : List (String × FE)} {z : String} {e : FE}
    (h : fs.find? (·.1 == z) = some (z, e)) : look fs z = some e := by
  simp [look, h]

/-- One evaluated selection counts 1. -/
def kn : FE → Term → Nat
  | .ref _, p => if isSkipped p then 0 else 1
  | .lit _, _ => 0

theorem get_stuck_skipped {m : String} {v : Term} {k : Nat} : ¬ CV (.get skipped m) v k := by
  intro h
  cases h with
  | value h0 => cases h0
  | get h1 _ _ => exact cv_skipped_false h1

theorem entry_lit_closed {v : Nat} {t : Term} (he : EntryOK (.lit v) t) (σ : Nat → Term) :
    t.substitute σ = t := by
  rcases he with rfl | rfl | rfl <;> simp [FE.at, Term.substitute, substitute_skipped]

/-- **One cell**: a literal is its template entry; a selection is kept, waits, or is evaluated
once, at cost 2, to the value of the field it reads, which the chase agrees with. -/
theorem cell_inv {FS : List (String × FE)} {G : List (String × Term)} {TS : List (String × Term)}
    (hT : TplOK FS TS) (hG : AppOK FS G FS TS G) {n : String} {e : FE} {t p q : Term} {k : Nat}
    (he : EntryOK e t) (hp : CellOK FS G n e t p) (hlook : look FS n = some e)
    (h : Run .cell (.app (.app t (.record G)) p) q k) :
    CellOK FS G n e t q ∧ (p ≠ skipped → q = p) ∧ 2 * kn e q ≤ k + 2 * kn e p := by
  cases e with
  | lit v =>
    have hpt : p = t := hp
    have hc := entry_lit_closed he (single (.record G))
    have hset : Settled t := entry_settled (G := G) (FS := FS) (n := n) he rfl
    cases h with
    | cellValue _ => exact ⟨by rw [hc]; rfl, fun _ => by rw [hc, hpt], by simp [kn]⟩
    | cellKeep hn _ _ => rw [hc] at hn; exact absurd hset hn
    | cellWait hn => rw [hc] at hn; exact absurd hset hn
    | cellEval hn _ => rw [hc] at hn; exact absurd hset hn
  | ref m =>
    rcases he with rfl | rfl | rfl
    · -- the selection from `self`, read against the approximant
      simp only [FE.at] at hp ⊢
      cases h with
      | cellValue hs => simp only [FE.at, Term.substitute] at hs; exact absurd hs get_not_settled
      | cellKeep _ _ _ => exact ⟨hp, fun _ => rfl, by omega⟩
      | cellWait _ => exact ⟨.inl rfl, fun h => absurd rfl h, by simp [kn, isSkipped, skipped]⟩
      | cellEval _ he2 =>
        simp only [FE.at, Term.substitute, single] at he2
        cases he2 with
        | value h0 => cases h0
        | get h1 hit h2 =>
          obtain ⟨e0, rfl⟩ := cv_of_value (appOK_value hT hG) h1
          cases e0
          obtain ⟨e', t', hfind, he', hc', _⟩ := find_appOK hT hG hit
          rename_i x _ _
          -- the entry read is `skipped` or a value whose chase the invariant records
          have hread : x = skipped ∨ ∃ u, x = .nat u ∧ ∃ k d, chase FS k m = some (u, d) := by
            cases e' with
            | lit v =>
              have hx : x = t' := hc'
              subst hx
              rcases he' with rfl | rfl | rfl
              · exact .inr ⟨v, rfl, 1, 0, by simp [chase, look_of_find hfind]⟩
              · exact .inr ⟨v, rfl, 1, 0, by simp [chase, look_of_find hfind]⟩
              · exact .inl rfl
            | ref m' =>
              rcases hc' with rfl | ⟨_, u, rfl, _, hc⟩
              · exact .inl rfl
              · exact .inr ⟨u, rfl, hc⟩
          rcases hread with rfl | hread
          · exact absurd h2 cv_skipped_false
          obtain ⟨u, rfl, k0, d0, hch⟩ := hread
          obtain ⟨rfl, rfl⟩ := cv_of_value (.nat u) h2
          refine ⟨.inr ⟨rfl, u, rfl, hit, k0 + 1, d0 + 1, ?_⟩, fun h => absurd rfl h, by simp [kn, isSkipped, skipped]⟩
          simp [chase, hlook, hch]
    · -- the selection from a skipped `self`: stuck
      simp only [FE.at] at hp ⊢
      have hps : p = skipped := by
        rcases hp with h | ⟨h, _⟩
        · exact h
        · simp [skipped] at h
      subst hps
      cases h with
      | cellValue hs => simp only [FE.at, Term.substitute] at hs; exact absurd hs get_not_settled
      | cellKeep _ _ hne => exact absurd rfl hne
      | cellWait _ => exact ⟨.inl rfl, fun h => absurd rfl h, by simp [kn, isSkipped, skipped]⟩
      | cellEval _ he2 =>
        simp only [FE.at, Term.substitute, substitute_skipped] at he2
        exact absurd he2 get_stuck_skipped
    · -- skipped in the template
      have hps : p = skipped := by
        rcases hp with h | ⟨h, _⟩
        · exact h
        · simp [skipped] at h
      subst hps
      cases h with
      | cellValue _ =>
        rw [substitute_skipped]; exact ⟨.inl rfl, fun h => absurd rfl h, by simp [kn, isSkipped, skipped]⟩
      | cellKeep _ _ hne => exact absurd rfl hne
      | cellWait _ => exact ⟨.inl rfl, fun h => absurd rfl h, by simp [kn, isSkipped, skipped]⟩
      | cellEval hn _ => rw [substitute_skipped] at hn; exact absurd .skipped hn

/-- **One wave**: every entry keeps its invariant, known entries are kept, and each selection
evaluated now costs 2. -/
theorem wave_inv {FS : List (String × FE)} {G TS : List (String × Term)} (hT : TplOK FS TS)
    (hG : AppOK FS G FS TS G) :
    ∀ {fs : List (String × FE)} {ts ps : List (String × Term)} {P : Term} {k : Nat},
      Run .wave (.app (.app (.record ts) (.record G)) (.record ps)) P k → TplOK fs ts → AppOK FS G fs ts ps →
      (∀ f ∈ fs, look FS f.1 = some f.2) →
      ∃ qs, P = .record qs ∧ AppOK FS G fs ts qs ∧ Ext ps qs ∧
        2 * (knownNames fs qs).length ≤ k + 2 * (knownNames fs ps).length
  | [], ts, ps, P, k, h, ht, hp, _ => by
    cases ht; cases hp; cases h
    exact ⟨[], rfl, .nil, .nil, by simp [knownNames]⟩
  | (n, e) :: fs, ts, ps, P, k, h, ht, hp, hpos => by
    cases ht with
    | @cons _ _ t _ ts' he ht' =>
      cases hp with
      | @cons _ _ _ p _ _ ps' hc hp' =>
        cases h with
        | waveCons hcell hw =>
          obtain ⟨c1, c2, c3⟩ := cell_inv hT hG he hc (hpos (n, e) (by simp)) hcell
          obtain ⟨qs, eq, h1, h2, h3⟩ := wave_inv hT hG hw ht' hp' (fun f hf => hpos f (by simp [hf]))
          cases eq
          refine ⟨_, rfl, .cons c1 h1, .cons c2 h2, ?_⟩
          cases e with
          | lit v => simp only [knownNames, kn] at c3 ⊢; omega
          | ref m =>
            simp only [knownNames, kn] at c3 ⊢
            split <;> split <;> simp_all <;> omega

/-- The first wave reads `self` as `skipped`: literals are filled, no selection is known. -/
theorem first_wave {FS : List (String × FE)} :
    ∀ {fs : List (String × FE)} {ts : List (String × Term)} {P : Term} {k : Nat},
      Run .wave (.app (.app (.record ts) skipped) (.record (ts.map fun f => (f.1, skipped)))) P k →
      TplOK fs ts → ∃ qs, P = .record qs ∧ (∀ G, AppOK FS G fs ts qs) ∧ knownNames fs qs = []
  | [], ts, P, k, h, ht => by
    cases ht; cases h
    exact ⟨[], rfl, fun _ => .nil, by simp [knownNames]⟩
  | (n, e) :: fs, ts, P, k, h, ht => by
    cases ht with
    | @cons _ _ t _ ts' he ht' =>
      simp only [List.map_cons] at h
      cases h with
      | @waveCons _ _ _ _ q _ _ _ _ _ hcell hw =>
        obtain ⟨qs, eq, h1, h2⟩ := first_wave (FS := FS) hw ht'
        cases eq
        have hq : CellOK FS [] n e t q ∧ kn e q = 0 := by
          cases e with
          | lit v =>
            have hc := entry_lit_closed he (single skipped)
            have hset : Settled t := entry_settled (G := []) (FS := FS) (n := n) he rfl
            cases hcell with
            | cellValue _ => exact ⟨by rw [hc]; rfl, rfl⟩
            | cellKeep hn _ _ => rw [hc] at hn; exact absurd hset hn
            | cellWait hn => rw [hc] at hn; exact absurd hset hn
            | cellEval hn _ => rw [hc] at hn; exact absurd hset hn
          | ref m =>
            have sub : t.substitute (single skipped) = .get skipped m ∨ t.substitute (single skipped) = skipped := by
              rcases he with rfl | rfl | rfl
              · exact .inl (by simp [FE.at, Term.substitute, single])
              · exact .inl (by simp [FE.at, Term.substitute, substitute_skipped])
              · exact .inr (substitute_skipped _)
            cases hcell with
            | cellValue hs =>
              rcases sub with e1 | e1 <;> rw [e1] at hs ⊢
              · exact absurd hs get_not_settled
              · exact ⟨.inl rfl, by simp [kn, isSkipped, skipped]⟩
            | cellKeep _ _ hne => exact absurd rfl hne
            | cellWait _ => exact ⟨.inl rfl, by simp [kn, isSkipped, skipped]⟩
            | cellEval hn he2 =>
              rcases sub with e1 | e1 <;> rw [e1] at hn he2
              · exact absurd he2 get_stuck_skipped
              · exact absurd .skipped hn
        refine ⟨_, rfl, fun G => .cons ?_ (h1 G), ?_⟩
        · cases e with
          | lit v => exact hq.1
          | ref m =>
            rcases hq.1 with h | ⟨_, _, _, hf, _⟩
            · exact .inl h
            · simp at hf
        · cases e with
          | lit v => simpa [knownNames] using h2
          | ref m =>
            have := hq.2
            simp only [kn] at this
            simp only [knownNames]
            split
            · exact h2
            · simp_all

theorem entry_ref_settled {m : String} {t : Term} (he : EntryOK (.ref m) t) (hs : Settled t) : t = skipped := by
  rcases he with rfl | rfl | rfl
  · exact absurd hs get_not_settled
  · exact absurd hs get_not_settled
  · rfl

/-- A template that is a value: its selections are skipped, it is closed, and it is its own
approximant with nothing known. -/
theorem tpl_value {FS : List (String × FE)} {G : List (String × Term)} :
    ∀ {fs : List (String × FE)} {ts : List (String × Term)}, TplOK fs ts → (∀ f ∈ ts, Settled f.2) →
      (∀ σ : Nat → Term, ts.map (fun f => (f.1, f.2.substitute σ)) = ts) ∧ AppOK FS G fs ts ts ∧
        knownNames fs ts = []
  | [], [], .nil, _ => ⟨fun _ => rfl, .nil, by simp [knownNames]⟩
  | (n, e) :: fs, (_, t) :: ts, .cons he ht, hs => by
    obtain ⟨c1, c2, c3⟩ := tpl_value (FS := FS) (G := G) ht (fun f hf => hs f (by simp [hf]))
    have hst : Settled t := hs (n, t) (by simp)
    cases e with
    | lit v =>
      exact ⟨fun σ => by simp [entry_lit_closed he σ, c1 σ], .cons rfl c2, by simpa [knownNames] using c3⟩
    | ref m =>
      have e1 := entry_ref_settled he hst
      subst e1
      refine ⟨fun σ => by simp [substitute_skipped, c1 σ], .cons (.inl rfl) c2, ?_⟩
      simp [knownNames, isSkipped, skipped, c3]

/-- What an approximant knows. -/
def knownOf (FS : List (String × FE)) : Term → Nat
  | .record G => (knownNames FS G).length
  | _ => 0

/-- **The waves**: from `skipped` or an approximant, the knot reaches an approximant whose every
evaluated selection was paid 2, once. -/
theorem knot_inv {FS : List (String × FE)} {TS : List (String × Term)} (hT : TplOK FS TS)
    (hpos : ∀ f ∈ FS, look FS f.1 = some f.2) {mo : Mode} {a V : Term} {k : Nat} (h : Run mo a V k) :
    mo = .knot → ∀ {S : Term}, a = .app (.record TS) S →
      (S = skipped ∨ ∃ G, S = .record G ∧ AppOK FS G FS TS G) →
      ∃ G', V = .record G' ∧ AppOK FS G' FS TS G' ∧ 2 * (knownNames FS G').length ≤ k + 2 * knownOf FS S := by
  induction h with
  | knotDone hP =>
    intro _ S e hS
    cases e
    rcases hS with rfl | ⟨G, rfl, hG⟩
    · exact absurd hP skipped_not_value
    · exact ⟨G, rfl, hG, by simp [knownOf]⟩
  | knotFirst hw _ _ ihk =>
    intro _ S e hS
    cases e
    obtain ⟨qs, eq, h1, h2⟩ := first_wave (FS := FS) hw hT
    cases eq
    obtain ⟨G', rfl, hG', hc⟩ := ihk rfl rfl (.inr ⟨qs, rfl, h1 qs⟩)
    exact ⟨G', rfl, hG', by simp [knownOf, h2] at hc ⊢; omega⟩
  | knotWave hw _ _ ihk =>
    intro _ S e hS
    cases e
    rcases hS with e | ⟨G, e, hG⟩
    · cases e
    · cases e
      obtain ⟨qs, eq, h1, h2, h3⟩ := wave_inv hT hG hw hT hG hpos
      cases eq
      obtain ⟨G', rfl, hG', hc⟩ := ihk rfl rfl (.inr ⟨qs, rfl, appOK_ext h2 h1⟩)
      exact ⟨G', rfl, hG', by simp only [knownOf] at hc ⊢; omega⟩
  | knotUnroll hT0 _ ihk =>
    intro _ S e hS
    cases e
    obtain ⟨c1, c2, c3⟩ := tpl_value (FS := FS) (G := TS) hT (record_value_fields hT0)
    have hsub : ∀ σ : Nat → Term, (Term.record TS).substitute σ = .record TS := by
      intro σ; simp only [Term.substitute]; rw [c1 σ]
    rw [hsub] at ihk
    obtain ⟨G', rfl, hG', hc⟩ := ihk rfl rfl (.inr ⟨TS, rfl, c2⟩)
    exact ⟨G', rfl, hG', by simp [knownOf, c3] at hc ⊢; omega⟩
  | _ => intro hm; cases hm

/-! ## The template -/

theorem objLam_selfBody (FS : List (String × FE)) :
    selfBody (objLam FS) (.record []) = .app (.app (objLam FS) (.bound 0)) (.record []) := by
  simp only [selfBody, objLam, Term.rename, entries_rename, List.map_nil]
  rfl

theorem objLam_inner (FS : List (String × FE)) (x : Term) :
    instantiate (.lam (.record (entries (.bound 1) FS))) x = .lam (.record (entries (x.rename .succ) FS)) := by
  simp only [instantiate, Term.substitute, entries_substitute]
  rfl

theorem objLam_outer (FS : List (String × FE)) (x y : Term) :
    instantiate (.record (entries (x.rename .succ) FS)) y = .record (entries x FS) := by
  rw [instantiate_eq]
  simp only [Term.substitute, entries_substitute, shift_one_cancel]

theorem tpl_entries {x0 : Term} (hx : x0 = .bound 0 ∨ x0 = skipped) : ∀ (FS : List (String × FE)),
    TplOK FS (entries x0 FS)
  | [] => .nil
  | (n, e) :: FS => by
    refine .cons ?_ (tpl_entries hx FS)
    rcases hx with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

theorem get_stuck_of {x0 : Term} (hx : x0 = .bound 0 ∨ x0 = skipped) {m : String} {v : Term} {k : Nat} :
    ¬ CV (.get x0 m) v k := by
  rcases hx with rfl | rfl
  · intro h
    cases h with
    | value h0 => cases h0
    | get h1 _ _ => exact cv_bound_false h1
  · exact get_stuck_skipped

theorem fields_tpl {x0 : Term} (hx : x0 = .bound 0 ∨ x0 = skipped) : ∀ {FS : List (String × FE)}
    {ts : List (String × Term)} {k : Nat}, Run .fields (.record (entries x0 FS)) (.record ts) k → TplOK FS ts
  | [], ts, k, h => by cases h; exact .nil
  | (n, e) :: FS, ts, k, h => by
    simp only [entries, List.map_cons] at h
    cases h with
    | cons hb hr =>
      refine .cons ?_ (fields_tpl hx hr)
      cases e with
      | lit v =>
        rcases bind_of_settled (.value (.nat v)) hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact .inl rfl
        · exact .inr (.inr rfl)
      | ref m =>
        rcases bind_of_unsettled get_not_settled hb with ⟨rfl, _⟩ | ⟨j, e, _⟩
        · exact .inr (.inr rfl)
        · exact absurd e (get_stuck_of hx)

theorem hasRef_not_value {x0 : Term} {FS : List (String × FE)} (hr : hasRef FS = true) :
    ¬ CValue (.record (entries x0 FS)) := by
  intro hv
  have hf := record_value_fields hv
  simp only [hasRef, List.any_eq_true] at hr
  obtain ⟨⟨n, e⟩, hm, he⟩ := hr
  cases e with
  | lit v => cases he
  | ref m =>
    exact get_not_settled (hf (n, FE.at x0 (.ref m)) (List.mem_map.2 ⟨(n, .ref m), hm, rfl⟩))

theorem inner_head {x0 : Term} (hx : x0 = .bound 0 ∨ x0 = skipped) {FS : List (String × FE)} {T : Term}
    {k : Nat} (h : Run .head (.record (entries x0 FS)) T k) :
    ∃ TS, T = .record TS ∧ TplOK FS TS ∧ (hasRef FS = true → 1 ≤ k) := by
  cases h with
  | headRecord _ => exact ⟨_, rfl, tpl_entries hx FS, fun _ => by omega⟩
  | headEval h =>
    cases h with
    | value hv => exact ⟨_, rfl, tpl_entries hx FS, fun hr => absurd hv (hasRef_not_value hr)⟩
    | record _ hf => exact ⟨_, rfl, fields_tpl hx hf, fun _ => by omega⟩

theorem objLam_app {FS : List (String × FE)} {w : Term} {k : Nat}
    (h : CV (.app (objLam FS) (.bound 0)) w k) :
    ∃ x0, (x0 = .bound 0 ∨ x0 = skipped) ∧ w = .lam (.record (entries (x0.rename .succ) FS)) ∧ 1 ≤ k := by
  cases h with
  | value h0 => exact absurd h0 app_not_ready
  | apply ha hb hc =>
    obtain ⟨e, rfl⟩ := cv_lam ha
    cases e
    rw [objLam_inner] at hc
    obtain ⟨rfl, rfl⟩ := cv_lam hc
    refine ⟨_, ?_, rfl, by omega⟩
    rcases bind_of_settled (.bound 0) hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact .inl rfl
    · exact .inr rfl
  | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e

/-- **The template is settled once**, at cost at least `headCost`, into the record of fields with
`self` open or skipped, or bound with `self` open (each selection skipped). -/
theorem head_template {FS : List (String × FE)} {T : Term} {k : Nat}
    (h : Run .head (selfBody (objLam FS) (.record [])) T k) :
    ∃ TS, T = .record TS ∧ TplOK FS TS ∧ headCost FS ≤ k := by
  rw [objLam_selfBody] at h
  have cost : ∀ {k1 k3 : Nat}, 1 ≤ k1 → (hasRef FS = true → 1 ≤ k3) → ∀ k2, headCost FS ≤ k1 + k2 + k3 + 1 := by
    intro k1 k3 h1 h3 k2
    unfold headCost
    split
    · have := h3 ‹_›; omega
    · omega
  cases h with
  | headEval h =>
    cases h with
    | value h0 => exact absurd h0 app_not_ready
    | apply h1 _ h3 =>
      obtain ⟨x0, hx, e, c1⟩ := objLam_app h1
      cases e
      rw [objLam_outer] at h3
      obtain ⟨TS, rfl, ht, c3⟩ := inner_head hx (.headEval h3)
      exact ⟨TS, rfl, ht, cost c1 c3 _⟩
    | applySpec h1 _ => obtain ⟨_, _, e, _⟩ := objLam_app h1; cases e
  | apply h1 _ h3 =>
    obtain ⟨x0, hx, e, c1⟩ := objLam_app h1
    cases e
    rw [objLam_outer] at h3
    obtain ⟨TS, rfl, ht, c3⟩ := inner_head hx h3
    exact ⟨TS, rfl, ht, cost c1 c3 _⟩
  | applySpec h1 _ => obtain ⟨_, _, e, _⟩ := objLam_app h1; cases e

/-! ## Minimality -/

theorem look_of_mem {FS : List (String × FE)} (nd : (FS.map Prod.fst).Nodup) :
    ∀ f ∈ FS, look FS f.1 = some f.2 := by
  induction FS with
  | nil => simp
  | cons g FS ih =>
    intro f hf
    simp only [List.map_cons, List.nodup_cons] at nd
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp [look]
    · have hne : (g.1 == f.1) = false := by
        have : g.1 ≠ f.1 := fun e => nd.1 (e ▸ List.mem_map.2 ⟨f, hf, rfl⟩)
        simpa using this
      have := ih nd.2 f hf
      simp only [look, List.find?_cons, hne] at this ⊢
      exact this

/-- Every selection on the chase from an evaluated `x` was evaluated. -/
theorem path_known {FS : List (String × FE)} {G TS : List (String × Term)} (hT : TplOK FS TS)
    (hG : AppOK FS G FS TS G) {x : String} {q : Term} (hx : G.find? (·.1 == x) = some (x, q))
    (hq : q ≠ skipped) {k u d : Nat} (hc : chase FS k x = some (u, d)) :
    path FS x d ⊆ knownNames FS G := by
  obtain ⟨_, refs⟩ := chase_walk hc
  have step : ∀ i, i < d → ∃ z q, walk FS i x = some z ∧ G.find? (·.1 == z) = some (z, q) ∧ q ≠ skipped := by
    intro i
    induction i with
    | zero => intro _; exact ⟨x, q, rfl, hx, hq⟩
    | succ i ih =>
      intro hi
      obtain ⟨z, q, hw, hz, hqz⟩ := ih (by omega)
      obtain ⟨z0, m0, hw0, hl0⟩ := refs i (by omega)
      rw [hw] at hw0; cases hw0
      obtain ⟨e, t, hf, _, hcell, _⟩ := find_appOK hT hG hz
      rw [look_of_find hf] at hl0; cases hl0
      rcases hcell with h | ⟨_, u', rfl, hm, _⟩
      · exact absurd h hqz
      · refine ⟨m0, .nat u', ?_, hm, by intro e; cases e⟩
        rw [show i + 1 = i + 1 by rfl, walk_add, hw]
        simp [walk, look_of_find hf]
  intro n hn
  simp only [path, List.mem_map, List.mem_range] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  obtain ⟨z, q', hw, hz, hq'⟩ := step i hi
  obtain ⟨z0, m0, hw0, hl0⟩ := refs i hi
  rw [hw] at hw0; cases hw0
  obtain ⟨e, t, hf, _, _, hkn⟩ := find_appOK hT hG hz
  rw [look_of_find hf] at hl0; cases hl0
  rw [hw]
  exact hkn m0 rfl hq'

/-- **Minimality and totality (Xia Thm 3.9 shape)**: every derivation of the selection has a
defined demand, with the same value, and costs at least the demand. -/
theorem demand_minimal {FS : List (String × FE)} (nd : (FS.map Prod.fst).Nodup) {x : String} {w : Term}
    {k : Nat} (h : CV (.get (obj FS) x) w k) : ∃ v n, demand FS x = some (v, n) ∧ w = .nat v ∧ n ≤ k := by
  cases h with
  | value h0 => cases h0
  | get h1 hit h2 =>
    cases h1 with
    | fix hh hk =>
      obtain ⟨TS, rfl, hT, hc⟩ := head_template hh
      obtain ⟨G, eq, hG, hk2⟩ := knot_inv hT (look_of_mem nd) hk rfl rfl (.inl rfl)
      cases eq
      obtain ⟨e, t, hf, he, hcell, _⟩ := find_appOK hT hG hit
      have hlx := look_of_find hf
      have hlen : 1 ≤ FS.length := by
        have := look_mem hlx
        cases FS with
        | nil => simp at this
        | cons _ _ => simp
      simp only [knownOf, skipped] at hk2
      cases e with
      | lit v =>
        have hp : _ = t := hcell
        rw [hp] at h2
        have ht : t = .nat v ∨ t = skipped := by rcases he with rfl | rfl | rfl <;> simp [FE.at]
        rcases ht with rfl | rfl
        · obtain ⟨rfl, rfl⟩ := cv_of_value (.nat v) h2
          have hch : chase FS 1 x = some (v, 0) := by simp [chase, hlx]
          exact ⟨v, headCost FS + 2 * 0 + 2, by simp [demand, (chase_fuel hch).2 _ hlen], rfl, by omega⟩
        · exact absurd h2 cv_skipped_false
      | ref m =>
        rcases hcell with rfl | ⟨_, u, rfl, _, k0, d, hch⟩
        · exact absurd h2 cv_skipped_false
        · obtain ⟨rfl, rfl⟩ := cv_of_value (.nat u) h2
          have hshort := chase_short hch
          have hfuel := (chase_fuel hch).2 FS.length hshort
          refine ⟨u, headCost FS + 2 * d + 2, by simp [demand, hfuel], rfl, ?_⟩
          obtain ⟨⟨zd, hzd, hld⟩, refs⟩ := chase_walk hch
          have some_of : ∀ i < d, ∃ z, walk FS i x = some z := by
            intro i hi; obtain ⟨z, _, hz, _⟩ := refs i hi; exact ⟨z, hz⟩
          have hknown := (path_nodup hch some_of).length_le_of_subset
            (path_known hT hG hit (by intro e; cases e) hch)
          simp only [path, List.length_map, List.length_range] at hknown
          omega

/-! ## Existence -/

/-- An approximant built from known values of selections. -/
def ent (κ : List (String × Nat)) : String × FE → Term
  | (_, .lit v) => .nat v
  | (n, .ref _) => match κ.lookup n with
    | some u => .nat u
    | none => skipped

def approxL (κ : List (String × Nat)) (fs : List (String × FE)) : List (String × Term) :=
  fs.map fun f => (f.1, ent κ f)

theorem ent_settled (κ : List (String × Nat)) (f : String × FE) : Settled (ent κ f) := by
  obtain ⟨n, e⟩ := f
  cases e with
  | lit v => exact .value (.nat v)
  | ref m =>
    simp only [ent]
    split
    · exact .value (.nat _)
    · exact .skipped

theorem approxL_value (κ : List (String × Nat)) (fs : List (String × FE)) : CValue (.record (approxL κ fs)) := by
  refine .record ?_
  intro f hf
  simp only [approxL, List.mem_map] at hf
  obtain ⟨g, _, rfl⟩ := hf
  exact ent_settled κ g

theorem find_approxL (κ : List (String × Nat)) {fs : List (String × FE)} {z : String} {e : FE}
    (h : fs.find? (·.1 == z) = some (z, e)) : (approxL κ fs).find? (·.1 == z) = some (z, ent κ (z, e)) := by
  simp only [approxL, List.find?_map]
  have : ((fun x : String × Term => x.1 == z) ∘ fun f : String × FE => (f.1, ent κ f)) = (·.1 == z) := by
    funext f; rfl
  rw [this, h]; rfl

theorem first_wave_exists : ∀ (fs : List (String × FE)),
    Run .wave (.app (.app (.record (entries (.bound 0) fs)) skipped)
      (.record ((entries (.bound 0) fs).map fun f => (f.1, skipped)))) (.record (approxL [] fs)) 0
  | [] => .waveNil
  | (n, e) :: fs => by
    have rest := first_wave_exists fs
    cases e with
    | lit v =>
      have := Run.waveCons (n := n) (Obend.Equiv.CostTests.cell_nat v skipped skipped) rest
      simpa [entries, approxL, ent, FE.at] using this
    | ref m =>
      have c := Obend.Equiv.CostTests.cell_get_wait skipped skipped m
      have := Run.waveCons (n := n) (t := .get (.bound 0) m)
        (Run.cellWait (S := skipped) (by simp only [Term.substitute, single]; exact get_not_settled)) rest
      simpa [entries, approxL, ent, FE.at, List.lookup] using this

/-- One wave evaluates the selection `y` (not yet known), reading its field's value `u` from the
approximant, at cost 2; every other entry stays. -/
theorem wave_exists {FS : List (String × FE)} {κ : List (String × Nat)} {y m : String} {u : Nat}
    (hy : κ.lookup y = none) (hm : (approxL κ FS).find? (·.1 == m) = some (m, .nat u)) :
    ∀ {fs : List (String × FE)}, (fs.map Prod.fst).Nodup → (∀ f ∈ fs, f.1 = y → f.2 = .ref m) →
      Run .wave (.app (.app (.record (entries (.bound 0) fs)) (.record (approxL κ FS)))
        (.record (approxL κ fs))) (.record (approxL ((y, u) :: κ) fs))
        (if y ∈ fs.map Prod.fst then 2 else 0)
  | [], _, _ => by simpa [entries, approxL] using Run.waveNil
  | (n, e) :: fs, nd, hyf => by
    simp only [List.map_cons, List.nodup_cons] at nd
    have rest := wave_exists hy hm nd.2 (fun f hf => hyf f (by simp [hf]))
    have hS := approxL_value κ FS
    by_cases hn : n = y
    · subst hn
      have he := hyf (n, e) (by simp) rfl
      subst he
      have hc : (if n ∈ (n :: fs.map Prod.fst) then 2 else 0) = 2 + (if n ∈ fs.map Prod.fst then 2 else 0) := by
        simp [nd.1]
      have get : CV (.get (.record (approxL κ FS)) m) (.nat u) 1 :=
        Run.get (Run.value hS) hm (Run.value (.nat u))
      have cell : Run .cell (.app (.app (FE.at (.bound 0) (.ref m)) (.record (approxL κ FS))) skipped) (.nat u) 2 :=
        Run.cellEval (by simp only [FE.at, Term.substitute, single]; exact get_not_settled)
          (by simp only [FE.at, Term.substitute, single]; exact get)
      have := Run.waveCons (n := n) cell rest
      have e1 : ent κ (n, .ref m) = skipped := by simp [ent, hy]
      have e2 : ent ((n, u) :: κ) (n, .ref m) = .nat u := by simp [ent, List.lookup]
      simp only [List.map_cons, hc]
      simpa [entries, approxL, e1, e2] using this
    · have hc : (if y ∈ (n :: fs.map Prod.fst) then 2 else 0) = 0 + (if y ∈ fs.map Prod.fst then 2 else 0) := by
        have : y ≠ n := fun h => hn h.symm
        simp only [List.mem_cons, this, false_or, Nat.zero_add]
      simp only [List.map_cons, hc]
      cases e with
      | lit v =>
        have := Run.waveCons (n := n) (Obend.Equiv.CostTests.cell_nat v (.record (approxL κ FS)) (.nat v)) rest
        simpa [entries, approxL, ent, FE.at] using this
      | ref m' =>
        have hb : (n == y) = false := by simpa using hn
        have e2 : ent ((y, u) :: κ) (n, .ref m') = ent κ (n, .ref m') := by
          simp [ent, List.lookup, hb]
        have hns : ¬ Settled ((FE.at (.bound 0) (.ref m')).substitute (single (.record (approxL κ FS)))) := by
          simp only [FE.at, Term.substitute, single]; exact get_not_settled
        have cell : Run .cell (.app (.app (FE.at (.bound 0) (.ref m')) (.record (approxL κ FS))) (ent κ (n, .ref m')))
            (ent κ (n, .ref m')) 0 := by
          cases hl : κ.lookup n with
          | none =>
            have : ent κ (n, .ref m') = skipped := by simp [ent, hl]
            rw [this]; exact .cellWait hns
          | some u' =>
            have : ent κ (n, .ref m') = .nat u' := by simp [ent, hl]
            rw [this]; exact .cellKeep hns (.value (.nat u')) (by intro e; cases e)
        have := Run.waveCons (n := n) cell rest
        simp only [entries, approxL, List.map_cons, e2] at this ⊢
        exact this

theorem find_of_look {fs : List (String × FE)} {x : String} {e : FE} (h : look fs x = some e) :
    fs.find? (·.1 == x) = some (x, e) := by
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  have hn := List.find?_some hf
  simp at hn
  obtain ⟨n, e'⟩ := f
  simp only at hn
  subst hn
  exact hf

/-- The known values agree with the chase. -/
def Good (FS : List (String × FE)) (κ : List (String × Nat)) : Prop :=
  ∀ n u, κ.lookup n = some u → ∃ k d, chase FS k n = some (u, d)

/-- From any good approximant, the waves make `x` known with its chase value, paying 2 for each
selection on its chase not yet known. -/
theorem reach {FS : List (String × FE)} (nd : (FS.map Prod.fst).Nodup) : ∀ {k : Nat} {x : String} {u d : Nat},
    chase FS k x = some (u, d) → ∀ κ, Good FS κ →
      ∃ κ' c, c ≤ 2 * d ∧ Good FS κ' ∧ (approxL κ' FS).find? (·.1 == x) = some (x, .nat u) ∧
        ∀ V c2, Run .knot (.app (.record (entries (.bound 0) FS)) (.record (approxL κ' FS))) V c2 →
          Run .knot (.app (.record (entries (.bound 0) FS)) (.record (approxL κ FS))) V (c + c2)
  | 0, x, u, d, h => by simp [chase] at h
  | k + 1, x, u, d, h => by
    intro κ hκ
    simp only [chase] at h
    split at h
    · rename_i v hl
      simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨κ, 0, by omega, hκ, ?_, fun V c2 r => by simpa using r⟩
      rw [find_approxL κ (find_of_look hl)]; rfl
    · rename_i m hl
      obtain ⟨⟨u', d'⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨κ1, c1, hc1, hg1, hm1, r1⟩ := reach nd hc κ hκ
      have hx1 := find_approxL κ1 (find_of_look hl)
      cases hlx : κ1.lookup x with
      | some u0 =>
        obtain ⟨k0, d0, h0⟩ := hg1 x u0 hlx
        have hxu : chase FS (k + 1) x = some (u', d' + 1) := by simp [chase, hl, hc]
        have := chase_unique h0 hxu
        simp at this; obtain ⟨rfl, rfl⟩ := this
        refine ⟨κ1, c1, by omega, hg1, ?_, r1⟩
        rw [hx1]; simp [ent, hlx]
      | none =>
        have hyf : ∀ f ∈ FS, f.1 = x → f.2 = .ref m := by
          intro f hf e; have := look_of_mem nd f hf; rw [e, hl] at this; exact (Option.some.inj this).symm
        have w := wave_exists hlx hm1 nd hyf
        have hmem : x ∈ FS.map Prod.fst := look_mem hl
        simp only [hmem, ite_true] at w
        refine ⟨(x, u') :: κ1, c1 + 2, by omega, ?_, ?_, ?_⟩
        · intro n u2 hn
          by_cases e : n = x
          · subst e
            simp [List.lookup] at hn
            subst hn
            exact ⟨k + 1, d' + 1, by simp [chase, hl, hc]⟩
          · have hb : (n == x) = false := by simpa using e
            simp [List.lookup, hb] at hn
            exact hg1 n u2 hn
        · rw [find_approxL _ (find_of_look hl)]; simp [ent, List.lookup]
        · intro V c2 rv
          have := r1 V (2 + c2) (Run.knotWave w rv)
          rw [show c1 + (2 + c2) = c1 + 2 + c2 by omega] at this
          exact this
    · cases h

theorem noRef_value {x0 : Term} : ∀ {FS : List (String × FE)}, hasRef FS = false →
    CValue (.record (entries x0 FS))
  | [], _ => .record (by simp [entries])
  | (n, e) :: FS, h => by
    cases e with
    | ref m => simp [hasRef] at h
    | lit v =>
      have h' : hasRef FS = false := by simpa [hasRef] using h
      have rest := record_value_fields (noRef_value (x0 := x0) h')
      refine .record ?_
      intro f hf
      simp only [entries, List.map_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact .value (.nat v)
      · exact rest f hf

/-- The template, settled at `headCost`. -/
theorem head_exists (FS : List (String × FE)) :
    Run .head (selfBody (objLam FS) (.record [])) (.record (entries (.bound 0) FS)) (headCost FS) := by
  have h1 : CV (.app (objLam FS) (.bound 0)) (.lam (.record (entries ((Term.bound 0).rename .succ) FS))) 1 := by
    have := cv_beta_value (W := .lam (.record (entries (.bound 1) FS))) (.bound 0)
      (by rw [objLam_inner]; exact .lam _)
    rw [objLam_inner] at this; exact this
  rw [objLam_selfBody]
  unfold headCost
  split
  · rename_i hr
    have h3 : Run .head (instantiate (.record (entries ((Term.bound 0).rename .succ) FS)) (.record []))
        (.record (entries (.bound 0) FS)) 1 := by
      rw [objLam_outer]; exact .headRecord (hasRef_not_value hr)
    exact Run.apply h1 (Run.keep record_nil_settled) h3
  · rename_i hr
    have h3 : Run .head (instantiate (.record (entries ((Term.bound 0).rename .succ) FS)) (.record []))
        (.record (entries (.bound 0) FS)) 0 := by
      rw [objLam_outer]; exact .headEval (.value (noRef_value (by simpa using hr)))
    exact Run.apply h1 (Run.keep record_nil_settled) h3

/-- **Existence (Xia Thm 3.8 shape)**: when the demand is defined, a derivation of exactly that
cost exists, with the demanded value. -/
theorem demand_exists {FS : List (String × FE)} (nd : (FS.map Prod.fst).Nodup) {x : String} {v n : Nat}
    (h : demand FS x = some (v, n)) : CV (.get (obj FS) x) (.nat v) n := by
  obtain ⟨⟨u, d⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
  simp at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨κ', c, hcd, _, hx, r⟩ := reach nd hc [] (by intro n u h; simp at h)
  have knot : Run .knot (.app (.record (entries (.bound 0) FS)) skipped) (.record (approxL κ' FS)) (0 + (c + 0)) :=
    Run.knotFirst (by simpa [pending] using first_wave_exists FS) (r _ 0 (.knotDone (approxL_value κ' FS)))
  have run := Run.get (Run.fix (head_exists FS) knot) hx (Run.value (.nat u))
  have hd : demand FS x = some (u, headCost FS + 2 * d + 2) := by simp [demand, hc]
  obtain ⟨v', n', hd', _, le⟩ := demand_minimal nd run
  rw [hd] at hd'
  simp at hd'; obtain ⟨rfl, rfl⟩ := hd'
  have e : headCost FS + (0 + (c + 0)) + 1 + 0 + 1 = headCost FS + 2 * d + 2 := by omega
  rw [e] at run
  exact run

/-- **The demand is the least clairvoyant cost**, and the derivations' values are the demand's. -/
theorem demand_is_least {FS : List (String × FE)} (nd : (FS.map Prod.fst).Nodup) (x : String) (v n : Nat) :
    demand FS x = some (v, n) ↔ CV (.get (obj FS) x) (.nat v) n ∧ ∀ w k, CV (.get (obj FS) x) w k → n ≤ k := by
  constructor
  · intro h
    refine ⟨demand_exists nd h, fun w k r => ?_⟩
    obtain ⟨v', n', h', _, le⟩ := demand_minimal nd r
    rw [h] at h'; cases h'; exact le
  · rintro ⟨r, least⟩
    obtain ⟨v', n', h', ew, le⟩ := demand_minimal nd r
    cases ew
    have := least _ _ (demand_exists nd h')
    rw [h']; congr; omega

/-! ## The measured programs -/

/-- `{good = 7, bad = self.bad}`. -/
def goodBadFields : List (String × FE) := [("good", .lit 7), ("bad", .ref "bad")]
/-- `{a = 7, b = self.a}`. -/
def selfFieldFields : List (String × FE) := [("a", .lit 7), ("b", .ref "a")]

theorem object_is_obj : FareTests.object = obj goodBadFields := rfl
theorem selfField_is_obj : CostTests.selfField = obj selfFieldFields := rfl

/-- The demands: `.good` costs 5, `.b` costs 7, `.bad` is undefined. -/
theorem measured_demands :
    demand goodBadFields "good" = some (7, 5) ∧ demand selfFieldFields "b" = some (7, 7) ∧
      demand goodBadFields "bad" = none := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **The least costs of the measured programs**: `.good` 5, `.b` 7, and `.bad` none at all. -/
theorem measured_least :
    (CV (.get FareTests.object "good") (.nat 7) 5 ∧ ∀ w k, CV (.get FareTests.object "good") w k → 5 ≤ k) ∧
      (CV (.get CostTests.selfField "b") (.nat 7) 7 ∧ ∀ w k, CV (.get CostTests.selfField "b") w k → 7 ≤ k) ∧
      (∀ w k, ¬ CV (.get FareTests.object "bad") w k) := by
  have nd1 : (goodBadFields.map Prod.fst).Nodup := by decide
  have nd2 : (selfFieldFields.map Prod.fst).Nodup := by decide
  obtain ⟨d1, d2, d3⟩ := measured_demands
  refine ⟨(demand_is_least nd1 "good" 7 5).1 d1, (demand_is_least nd2 "b" 7 7).1 d2, ?_⟩
  intro w k r
  rw [object_is_obj] at r
  obtain ⟨v, n, h, _, _⟩ := demand_minimal nd1 r
  rw [d3] at h; cases h

end Obend.Equiv.Demand
end
