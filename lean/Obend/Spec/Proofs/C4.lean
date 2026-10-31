module
/-
# Obend.Spec.Proofs.C4 — what a C4 linearization is, for every graph

About `Obend.Spec.C4.linearize`, with no hypothesis on the graph:

* `linearize_head`, `linearize_nodup`: a result is the head followed by the rest, and names nothing
  twice.
* `linearize_local` (LOCAL PRECEDENCE, Barrett et al. 1996): every local chain of parents is a
  sublist of the result.
* `linearize_monotone` (MONOTONICITY): every parent's own precedence list is a sublist of the
  result.
* `linearize_mem`: every name of the result is in the head, a local chain or a parent's list.
* `linearize_tail` (the suffix tail): the result ends with a suffix tail that is empty or a
  parent's own tail, has every parent's tail as a list suffix, and whose first name is the
  returned suffix node.
* `suffix_property` (the C4 SUFFIX PROPERTY): when the graph's lists are C4 lists (`Coherent`),
  every suffix node after the head has its whole precedence list as a suffix of the result; and
  `coherent_extend`: memoizing a result keeps the graph coherent, so the property holds of every
  oracle built the way the elaborator and the ecosystem build theirs.

`c3_tree_is_chain` (`Obend.Law.Proofs.Inherit`) is a corollary: on an acyclic tree the result is
the chain to the root.
-/
public import Obend.Spec.C4
import all Obend.Spec.C4
public import Obend.Tactic.Tooth
namespace Obend.Spec.C4
set_option autoImplicit false

public theorem nodupB_sound {l : List String} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have h' : x ∉ xs ∧ nodupB xs = true := by simpa [nodupB] using h
    exact List.nodup_cons.2 ⟨h'.1, ih h'.2⟩

public theorem nodupB_complete : ∀ {l : List String}, l.Nodup → nodupB l = true
  | [], _ => rfl
  | x :: xs, h => by
      obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h
      simp [nodupB, hx, nodupB_complete hxs]

/-! ## The merge -/

theorem nextHead_spec {ls : List (List String)} {c : String} (h : nextHead ls = some c) :
    (∃ t, c :: t ∈ ls) ∧ ∀ l ∈ ls, c ∉ l.tail := by
  unfold nextHead at h
  obtain ⟨l₁, a, l₂, hls, ha, _⟩ := List.findSome?_eq_some_iff.1 h
  have hmem : a ∈ ls := by rw [hls]; simp
  match a, ha with
  | x :: t, ha =>
    simp only at ha
    split at ha
    · cases ha
    · rename_i hany
      cases ha
      refine ⟨⟨t, hmem⟩, fun l hl hc => hany ?_⟩
      rw [List.any_eq_true]
      exact ⟨l, hl, by simpa using hc⟩

theorem popOne_cases (c : String) (l : List String) :
    (∃ t, l = c :: t ∧ popOne c l = t) ∨ popOne c l = l := by
  cases l with
  | nil => exact .inr rfl
  | cons x t =>
    by_cases hx : x = c
    · subst hx; exact .inl ⟨t, rfl, by simp [popOne]⟩
    · exact .inr (by simp [popOne, hx])

theorem popOne_subset (c : String) (l : List String) : ∀ x ∈ popOne c l, x ∈ l := by
  intro x hx
  rcases popOne_cases c l with ⟨t, rfl, he⟩ | he
  · rw [he] at hx; exact List.mem_cons_of_mem _ hx
  · rwa [he] at hx

theorem all_empty {ls : List (List String)} (h : ls.all List.isEmpty = true) : ∀ l ∈ ls, l = [] := by
  intro l hl
  have := (List.all_eq_true.1 h) l hl
  simpa using this

/-- Every candidate is a sublist of the merge. -/
theorem mergeN_sublist {head : List String} :
    ∀ (n : Nat) (ls : List (List String)) (m : List String), mergeN head n ls = .ok m → ∀ l ∈ ls, l.Sublist m
  | 0, ls, m, h, l, hl => by
    unfold mergeN at h
    split at h
    · rename_i he; rw [all_empty he l hl]; exact List.nil_sublist _
    · cases h
  | n + 1, ls, m, h, l, hl => by
    unfold mergeN at h
    split at h
    · rename_i he; rw [all_empty he l hl]; exact List.nil_sublist _
    · split at h
      · cases h
      · rename_i c _
        split at h
        · rename_i m' hm
          cases h
          have ih := mergeN_sublist n (pop c ls) m' hm (popOne c l) (List.mem_map_of_mem hl)
          rcases popOne_cases c l with ⟨t, rfl, he⟩ | he
          · rw [he] at ih; exact ih.cons_cons c
          · rw [he] at ih; exact ih.cons c
        · cases h

/-- Every name of the merge is in a candidate. -/
theorem mergeN_mem {head : List String} :
    ∀ (n : Nat) (ls : List (List String)) (m : List String), mergeN head n ls = .ok m →
      ∀ x ∈ m, ∃ l ∈ ls, x ∈ l
  | 0, ls, m, h, x, hx => by
    unfold mergeN at h
    split at h
    · cases h; cases hx
    · cases h
  | n + 1, ls, m, h, x, hx => by
    unfold mergeN at h
    split at h
    · cases h; cases hx
    · split at h
      · cases h
      · rename_i c hc
        split at h
        · rename_i m' hm
          cases h
          rcases List.mem_cons.1 hx with rfl | hx
          · obtain ⟨⟨t, ht⟩, _⟩ := nextHead_spec hc
            exact ⟨_, ht, List.mem_cons_self⟩
          · obtain ⟨l', hl', hxl'⟩ := mergeN_mem n (pop c ls) m' hm x hx
            obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
            exact ⟨l, hl, popOne_subset c l x hxl'⟩
        · cases h

/-- The merge names nothing twice. -/
theorem mergeN_nodup {head : List String} :
    ∀ (n : Nat) (ls : List (List String)) (m : List String), mergeN head n ls = .ok m → m.Nodup
  | 0, ls, m, h => by
    unfold mergeN at h
    split at h
    · cases h; exact List.nodup_nil
    · cases h
  | n + 1, ls, m, h => by
    unfold mergeN at h
    split at h
    · cases h; exact List.nodup_nil
    · split at h
      · cases h
      · rename_i c hc
        split at h
        · rename_i m' hm
          cases h
          refine List.nodup_cons.2 ⟨fun hcm => ?_, mergeN_nodup n (pop c ls) m' hm⟩
          obtain ⟨l', hl', hcl'⟩ := mergeN_mem n (pop c ls) m' hm c hcm
          obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
          have hnt := (nextHead_spec hc).2 l hl
          rcases popOne_cases c l with ⟨t, rfl, he⟩ | he
          · rw [he] at hcl'; exact hnt hcl'
          · rw [he] at hcl'
            cases l with
            | nil => cases hcl'
            | cons x t =>
              rcases List.mem_cons.1 hcl' with rfl | hct
              · simp [popOne] at he
              · exact hnt hct
        · cases h

theorem merge_sublist {head : List String} {ls : List (List String)} {m : List String}
    (h : merge head ls = .ok m) : ∀ l ∈ ls, l.Sublist m := mergeN_sublist _ _ _ h
theorem merge_mem {head : List String} {ls : List (List String)} {m : List String}
    (h : merge head ls = .ok m) : ∀ x ∈ m, ∃ l ∈ ls, x ∈ l := mergeN_mem _ _ _ h
theorem merge_nodup {head : List String} {ls : List (List String)} {m : List String}
    (h : merge head ls = .ok m) : m.Nodup := mergeN_nodup _ _ _ h

/-! ## Cleaning and the suffix tail -/

theorem clean_spec {tail l c : List String} (h : clean tail l = some c) :
    ∃ r, l = c ++ r ∧ r.Sublist tail ∧ ∀ x ∈ c, x ∉ tail := by
  unfold clean at h
  split at h
  · rename_i hs
    cases h
    refine ⟨_, List.takeWhile_append_dropWhile.symm, List.isSublist_iff_sublist.1 hs, fun x hx hxt => ?_⟩
    have := List.all_eq_true.1 List.all_takeWhile x hx
    simp [hxt] at this
  · cases h

theorem cleanAll_spec {tail : List String} {ls cs : List (List String)} (h : cleanAll tail ls = some cs) :
    (∀ l ∈ ls, ∃ c ∈ cs, ∃ r, l = c ++ r ∧ r.Sublist tail) ∧ ∀ c ∈ cs, ∃ l ∈ ls, ∃ r, l = c ++ r ∧ ∀ x ∈ c, x ∉ tail := by
  induction ls generalizing cs with
  | nil =>
    simp only [cleanAll, Option.some.injEq] at h
    subst h; simp
  | cons l ls ih =>
    simp only [cleanAll] at h
    split at h
    · rename_i c cs' hc hcs
      cases h
      obtain ⟨r, hl, hr, hnt⟩ := clean_spec hc
      obtain ⟨ih1, ih2⟩ := ih hcs
      refine ⟨fun l' hl' => ?_, fun c' hc' => ?_⟩
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · exact ⟨c, List.mem_cons_self, r, hl, hr⟩
        · obtain ⟨c'', hc'', r', h1, h2⟩ := ih1 l' hl'
          exact ⟨c'', List.mem_cons_of_mem _ hc'', r', h1, h2⟩
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨l, List.mem_cons_self, r, hl, hnt⟩
        · obtain ⟨l'', hl'', r', h1, h2⟩ := ih2 c' hc'
          exact ⟨l'', List.mem_cons_of_mem _ hl'', r', h1, h2⟩
    · cases h

theorem joinTail_spec {a b t : List String} (h : joinTail a b = some t) :
    a.IsSuffix t ∧ b.IsSuffix t ∧ (t = a ∨ t = b) := by
  unfold joinTail at h
  split at h
  · rename_i hb; cases h
    exact ⟨List.suffix_refl _, List.isSuffixOf_iff_suffix.1 hb, .inl rfl⟩
  · split at h
    · rename_i ha; cases h
      exact ⟨List.isSuffixOf_iff_suffix.1 ha, List.suffix_refl _, .inr rfl⟩
    · cases h

theorem tailOf_spec (g : Graph) (head : List String) {acc ps t : List String}
    (h : tailOf g head acc ps = .ok t) :
    acc.IsSuffix t ∧ (∀ p ∈ ps, (g.tailAt p).IsSuffix t) ∧ (t = acc ∨ ∃ p ∈ ps, t = g.tailAt p) := by
  induction ps generalizing acc with
  | nil =>
    simp only [tailOf, Except.ok.injEq] at h
    subst h; exact ⟨List.suffix_refl _, by simp, .inl rfl⟩
  | cons p ps ih =>
    simp only [tailOf] at h
    split at h
    · rename_i t' ht'
      obtain ⟨h1, h2, h3⟩ := joinTail_spec ht'
      obtain ⟨i1, i2, i3⟩ := ih h
      refine ⟨h1.trans i1, fun q hq => ?_, ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact h2.trans i1
        · exact i2 q hq
      · rcases i3 with rfl | ⟨q, hq, rfl⟩
        · rcases h3 with rfl | rfl
          · exact .inl rfl
          · exact .inr ⟨p, List.mem_cons_self, rfl⟩
        · exact .inr ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
    · cases h

/-! ## The linearization -/

/-- What a result is made of: the head, the merge of the cleaned candidates, the suffix tail. -/
theorem linearize_parts {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∃ tail cands m, tailOf g head [] parents.flatten = .ok tail ∧
      cleanAll tail (parents.flatten.map g.precedence ++ parents) = some cands ∧
      (head ++ tail).Nodup ∧ (∀ x ∈ head, ∀ c ∈ cands, x ∉ c) ∧ merge head cands = .ok m ∧
      lin = head ++ m ++ tail ∧ s = tail.head? := by
  unfold linearize at h
  simp only at h
  split at h
  · cases h
  · rename_i tail htail
    split at h
    · cases h
    · rename_i cands hc
      split at h
      · rename_i hchk
        split at h
        · rename_i m hm
          cases h
          simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.any_eq_false] at hchk
          refine ⟨tail, cands, m, htail, hc, nodupB_sound hchk.1, fun x hx c hcm hxc => ?_, hm, rfl, rfl⟩
          have := hchk.2 x hx c hcm
          simp [hxc] at this
        · cases h
      · cases h

/-- **A result starts with the head.** -/
public theorem linearize_head {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∃ rest, lin = head ++ rest := by
  obtain ⟨tail, _, m, _, _, _, _, _, rfl, _⟩ := linearize_parts h
  exact ⟨m ++ tail, by simp⟩

/-- **Monotonicity and local precedence, together**: every parent's precedence list and every local
chain is a sublist of the result. -/
public theorem linearize_candidates {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∀ l ∈ parents.flatten.map g.precedence ++ parents, l.Sublist lin := by
  obtain ⟨tail, cands, m, _, hc, _, _, hm, rfl, _⟩ := linearize_parts h
  intro l hl
  obtain ⟨c, hcm, r, hlr, hr⟩ := (cleanAll_spec hc).1 l hl
  have hcs : c.Sublist m := merge_sublist hm c hcm
  rw [hlr, List.append_assoc]
  exact (hcs.append hr).trans (List.sublist_append_right _ _)

/-- **Local precedence** (Barrett et al. 1996): every local chain of parents is kept, in order. -/
public theorem linearize_local {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∀ chain ∈ parents, chain.Sublist lin :=
  fun chain hc => linearize_candidates h chain (List.mem_append_right _ hc)

/-- **Monotonicity** (Barrett et al. 1996): every parent's own precedence list is kept, in order. -/
public theorem linearize_monotone {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∀ chain ∈ parents, ∀ p ∈ chain, (g.precedence p).Sublist lin :=
  fun chain hc _ hq => linearize_candidates h _
    (List.mem_append_left _ (List.mem_map_of_mem (List.mem_flatten.2 ⟨chain, hc, hq⟩)))

/-- **The head is no ancestor**: no name of the head is on a local chain or a parent's list. -/
public theorem linearize_fresh {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∀ x ∈ head, ∀ l ∈ parents.flatten.map g.precedence ++ parents, x ∉ l := by
  obtain ⟨tail, cands, m, _, hc, hht, hhc, _, _, _⟩ := linearize_parts h
  intro x hx l hl hxl
  obtain ⟨c, hcm, r, hlr, hr⟩ := (cleanAll_spec hc).1 l hl
  rw [hlr] at hxl
  rcases List.mem_append.1 hxl with hxc | hxr
  · exact hhc x hx c hcm hxc
  · exact (List.nodup_append.1 hht).2.2 x hx x (hr.subset hxr) rfl

/-- Every name of a cleaned candidate is outside the suffix tail. -/
theorem cands_off_tail {tail : List String} {ls cands : List (List String)}
    (hc : cleanAll tail ls = some cands) : ∀ c ∈ cands, ∀ x ∈ c, x ∉ tail := by
  intro c hcm x hx
  obtain ⟨_, _, _, _, hnt⟩ := (cleanAll_spec hc).2 c hcm
  exact hnt x hx

/-- **A result names nothing twice.** -/
public theorem linearize_nodup {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    lin.Nodup := by
  obtain ⟨tail, cands, m, _, hc, hht, hhc, hm, rfl, _⟩ := linearize_parts h
  have hmn := merge_nodup hm
  have hmt : ∀ x ∈ m, x ∉ tail := fun x hx => by
    obtain ⟨c, hcm, hxc⟩ := merge_mem hm x hx
    exact cands_off_tail hc c hcm x hxc
  have hmh : ∀ x ∈ head, x ∉ m := fun x hx hxm => by
    obtain ⟨c, hcm, hxc⟩ := merge_mem hm x hxm
    exact hhc x hx c hcm hxc
  rw [List.nodup_append] at hht ⊢
  rw [List.nodup_append]
  refine ⟨⟨hht.1, hmn, fun a ha b hb hab => hmh a ha (hab ▸ hb)⟩, hht.2.1, fun a ha b hb hab => ?_⟩
  subst hab
  rcases List.mem_append.1 ha with ha | ha
  · exact hht.2.2 a ha a hb rfl
  · exact hmt a ha hb

/-- **Every name of a result comes from the head, a local chain or a parent's list.** -/
public theorem linearize_mem {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∀ x ∈ lin, x ∈ head ∨ (∃ chain ∈ parents, x ∈ chain) ∨ ∃ p ∈ parents.flatten, x ∈ g.precedence p := by
  obtain ⟨tail, cands, m, ht, hc, _, _, hm, rfl, _⟩ := linearize_parts h
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact .inl hx
    · obtain ⟨c, hcm, hxc⟩ := merge_mem hm x hx
      obtain ⟨l, hl, r, hlr, _⟩ := (cleanAll_spec hc).2 c hcm
      have hxl : x ∈ l := hlr ▸ List.mem_append_left _ hxc
      rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
        exact .inr (.inr ⟨p, hp, hxl⟩)
      · exact .inr (.inl ⟨_, hl, hxl⟩)
  · obtain ⟨_, _, h3⟩ := tailOf_spec g head ht
    rcases h3 with rfl | ⟨p, hp, rfl⟩
    · cases hx
    · exact .inr (.inr ⟨p, hp, (List.dropWhile_suffix _).subset hx⟩)

/-- **The suffix tail.** A result ends with its suffix tail, which is empty or a parent's own tail
(its precedence list from its first suffix node), has every parent's tail as a list suffix (the
parents' suffix nodes lie on one chain), and starts with the returned suffix node. -/
public theorem linearize_tail {g : Graph} {head : List String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g head parents = .ok (lin, s)) :
    ∃ pre tail, lin = pre ++ tail ∧ s = tail.head? ∧ (tail = [] ∨ ∃ p ∈ parents.flatten, tail = g.tailAt p) ∧
      ∀ p ∈ parents.flatten, (g.tailAt p).IsSuffix tail := by
  obtain ⟨tail, cands, m, ht, _, _, _, _, rfl, rfl⟩ := linearize_parts h
  obtain ⟨_, h2, h3⟩ := tailOf_spec g head ht
  exact ⟨head ++ m, tail, rfl, rfl, h3, h2⟩

/-! ## The suffix property -/

theorem suffixPart_mem_not_suffix {g : Graph} {l : List String} {x : String}
    (hx : x ∈ l.takeWhile fun y => !g.isSuffix y) : g.isSuffix x = false := by
  have := List.all_eq_true.1 List.all_takeWhile x hx
  simpa using this

/-- In `A ++ B = X ++ Y` where `Y` starts with a name outside `A`, `Y` is a suffix of `B`. -/
theorem suffix_of_split {A B X Y : List String} {s : String} {t : List String}
    (he : A ++ B = X ++ Y) (hY : Y = s :: t) (hs : s ∉ A) : Y.IsSuffix B := by
  rcases List.append_eq_append_iff.1 he with ⟨a', _, hB⟩ | ⟨c', hA, hYc⟩
  · exact ⟨a', hB.symm⟩
  · cases c' with
    | nil => simp at hYc; exact hYc ▸ List.suffix_refl _
    | cons c cs =>
      rw [hY] at hYc
      simp only [List.cons_append, List.cons.injEq] at hYc
      exact absurd (hA ▸ List.mem_append_right _ (hYc.1 ▸ List.mem_cons_self)) hs

/-- In a coherent graph, a suffix node of a parent's tail has its precedence list as a suffix of
that tail. -/
theorem coherent_tail {g : Graph} (hg : Coherent g) {p s : String} (hs : s ∈ g.tailAt p)
    (hsuf : g.isSuffix s = true) : (g.precedence s).IsSuffix (g.tailAt p) := by
  obtain ⟨_, hnd, hsp⟩ := hg p
  obtain ⟨⟨t, ht⟩, _, _⟩ := hg s
  have hmem : s ∈ g.precedence p := (List.dropWhile_suffix _).subset hs
  obtain ⟨X, hX⟩ := hsp s hmem hsuf
  have hsplit := (List.takeWhile_append_dropWhile (p := fun x => !g.isSuffix x) (l := g.precedence p))
  have hnA : s ∉ (g.precedence p).takeWhile fun x => !g.isSuffix x := fun h => by
    rw [suffixPart_mem_not_suffix h] at hsuf; cases hsuf
  exact suffix_of_split (hsplit.trans hX.symm) ht hnA

/-- **The suffix property** (C4, ltuo §7.4.4). When the graph's lists are C4 lists, every suffix
node of a result after its head has its whole precedence list as a suffix of the result. -/
public theorem suffix_property {g : Graph} (hg : Coherent g) {head : List String}
    {parents : List (List String)} {lin : List String} {s : Option String}
    (h : linearize g head parents = .ok (lin, s)) :
    ∀ rest, lin = head ++ rest → ∀ x ∈ rest, g.isSuffix x = true → (g.precedence x).IsSuffix lin := by
  obtain ⟨tail, cands, m, ht, hc, _, _, hm, rfl, _⟩ := linearize_parts h
  obtain ⟨_, h2, h3⟩ := tailOf_spec g head ht
  -- every suffix node of a parent's own list, or a parent that is a suffix node, is in the tail
  have tail_has : ∀ p ∈ parents.flatten, ∀ x ∈ g.precedence p, g.isSuffix x = true → x ∈ tail := by
    intro p hp x hx hxs
    have hsplit := (List.takeWhile_append_dropWhile (p := fun y => !g.isSuffix y) (l := g.precedence p))
    rw [← hsplit] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [suffixPart_mem_not_suffix hx] at hxs; cases hxs
    · exact (h2 p hp).subset hx
  intro rest hrest x hx hxs
  rw [List.append_assoc, List.append_cancel_left_eq] at hrest
  subst hrest
  rcases List.mem_append.1 hx with hx | hx
  · exfalso
    obtain ⟨c, hcm, hxc⟩ := merge_mem hm x hx
    obtain ⟨l, hl, r, hlr, _⟩ := (cleanAll_spec hc).2 c hcm
    have hxl : x ∈ l := hlr ▸ List.mem_append_left _ hxc
    apply cands_off_tail hc _ hcm x hxc
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      exact tail_has p hp x hxl hxs
    · have hxp : x ∈ parents.flatten := List.mem_flatten.2 ⟨_, hl, hxl⟩
      obtain ⟨⟨t, ht'⟩, _, _⟩ := hg x
      exact tail_has x hxp x (by rw [ht']; exact List.mem_cons_self) hxs
  · rcases h3 with rfl | ⟨p, _, rfl⟩
    · cases hx
    · exact (coherent_tail hg hx hxs).trans (List.suffix_append _ _)

/-- **Memoizing a result keeps a graph coherent**: the linearization of a new node `x` (one not on
any list of the graph) over a coherent graph is itself a C4 list, so the oracle the elaborator and
the ecosystem build one node at a time stays coherent, and `suffix_property` applies at every node. -/
public theorem coherent_extend {g : Graph} (hg : Coherent g) {x : String} {parents : List (List String)}
    {lin : List String} {s : Option String} (h : linearize g [x] parents = .ok (lin, s))
    (fresh : ∀ y, y ≠ x → x ∉ g.precedence y) : Coherent (g.extend x lin) := by
  intro p
  by_cases hp : p = x
  · subst hp
    simp only [Graph.extend, ite_true]
    obtain ⟨rest, hr⟩ := linearize_head h
    refine ⟨⟨rest, hr⟩, linearize_nodup h, fun s' hs' hsuf => ?_⟩
    by_cases hsx : s' = p
    · subst hsx; simp
    · have hs'r : s' ∈ rest := by
        rw [hr] at hs'
        rcases List.mem_cons.1 hs' with rfl | h'
        · exact absurd rfl hsx
        · exact h'
      simp only [hsx, ite_false]
      exact suffix_property hg h rest hr s' hs'r hsuf
  · simp only [Graph.extend, hp, ite_false]
    obtain ⟨h1, h2, h3⟩ := hg p
    refine ⟨h1, h2, fun s' hs' hsuf => ?_⟩
    have hsx : s' ≠ x := fun e => fresh p hp (e ▸ hs')
    simp only [hsx, ite_false]
    exact h3 s' hs' hsuf

end Obend.Spec.C4
