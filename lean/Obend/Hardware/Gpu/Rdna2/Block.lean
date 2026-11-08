/-
# Obend.Hardware.Gpu.Rdna2.Block — a block dispatch as a certified stage

A block program (`Obend.Hardware.ArrayKernel.Program`, the NTT's source) is emitted by `BlockEmit`: its
device space is the wire buffer `w` (word `bufferBase + i`), its constant space the buffer `c`, its shared
space the workgroup's LDS, a phase a loop over the workgroup's lanes and a barrier, a dispatch one
workgroup of one wave64 per group. `blockSpec` reads one dispatch as a certificate stage (`Cert.Spec`) over
flat memory (`BlockLower.FlatMemory`): its table is the dispatch run symbolically group by group, phase
by phase as `BlockLower.lowerPhase` runs it (every lane's loads from the memory before the phase, its code
by `Lower.pElem`, its writes after), each load from the group's own writes, else from the dispatch's start
(a device word no earlier group of the dispatch wrote; a constant as the literal the host binds), never
from shared memory the group has not written, so the meaning cannot depend on what another group or an
earlier dispatch left in LDS. A word two groups of the dispatch write, a constant written, or a device word
outside the buffer is refused. `blockSpec_sound` is `Spec.Sound` for it, and `certifyBlock_sound` composes
the certificate over every dispatch with `BlockLower.lowerProgram`.
-/
module

public import Obend.Hardware.Gpu.Rdna2.CertSound
public import Obend.Hardware.Gpu.BlockLower
public import Obend.Hardware.Gpu.BlockEmit

@[expose] public section

namespace Obend.Hardware.Gpu.Rdna2.Block

open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.Rdna2 Tm

/-! ## 1. Lanes and phases, symbolically -/

def scode : Storage → Nat
  | .device => 0
  | .shared => 1
  | .constant => 2

def key (a : Address) : Nat × Nat := (scode a.1, a.2)

theorem key_inj {a b : Address} (h : key a = key b) : a = b := by
  obtain ⟨s, i⟩ := a; obtain ⟨t, j⟩ := b
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  cases s <;> cases t <;> simp_all [scode]

abbrev Regs := Std.HashMap Nat TP

def rget (m : Regs) (k : Nat) : TP := m.getD k (pLit 0)

def sLoads (p : ArrayKernel.Program) (look : Address → Option TP) (g l : Nat) : List Read → Regs → Option Regs
  | [], m => some m
  | r :: rs, m => (look (address p r.array (r.index.eval g l))).bind fun t => sLoads p look g l rs (m.insert r.dst t)

def sRegs : List Instr → Regs → Option Regs
  | [], m => some m
  | i :: is, m => (pElem i.op (i.args.map (rget m))).bind fun t => sRegs is (m.insert i.dst t)

def sLane (p : ArrayKernel.Program) (ph : Phase) (look : Address → Option TP) (g l : Nat) : Option (List (Address × TP)) :=
  (sLoads p look g l ph.reads {}).bind fun m0 => (sRegs ph.code m0).map fun m =>
    ph.writes.map fun w => (address p w.array (w.index.eval g l), rget m w.value)

def allSome {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => (f x).bind fun y => (allSome f xs).map (y :: ·)

def sPhase (p : ArrayKernel.Program) (ph : Phase) (look : Address → Option TP) (g : Nat) : Option (List (Address × TP)) :=
  (allSome (sLane p ph look g) (List.range ph.lanes)).map List.flatten

variable {env : UInt64 → UInt32}

def RelR (env : UInt64 → UInt32) (m : Regs) (c : Registers) : Prop := ∀ k, (rget m k).ev env = c.getD k 0#64

def LookOk (env : UInt64 → UInt32) (look : Address → Option TP) (flat : FlatMemory) : Prop :=
  ∀ a t, look a = some t → t.ev env = flat a

theorem relR_empty : RelR env {} ∅ := by
  intro k; simp [rget, ev_lit]

theorem relR_insert {m : Regs} {c : Registers} (h : RelR env m c) (k : Nat) (t : TP) (v : Word) (ht : t.ev env = v) :
    RelR env (m.insert k t) (c.insert k v) := by
  intro k'
  simp only [rget, Std.HashMap.getD_insert]
  split
  · exact ht
  · exact h k'

theorem sLoads_sound {p : ArrayKernel.Program} {look : Address → Option TP} {flat : FlatMemory} (hl : LookOk env look flat) (g l : Nat) :
    ∀ (rs : List Read) (m m' : Regs) (c : Registers), RelR env m c → sLoads p look g l rs m = some m' →
      RelR env m' (lowerLoads p flat g l rs c)
  | [], m, m', c, hr, h => by simp only [sLoads, Option.some.injEq] at h; subst h; exact hr
  | r :: rs, m, m', c, hr, h => by
    simp only [sLoads, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    exact sLoads_sound hl g l rs _ m' _ (relR_insert hr r.dst t _ (hl _ t ht)) h

theorem sRegs_sound : ∀ (code : List Instr) (m m' : Regs) (c : Registers), RelR env m c → sRegs code m = some m' →
    RelR env m' (runRegisters code c)
  | [], m, m', c, hr, h => by simp only [sRegs, Option.some.injEq] at h; subst h; exact hr
  | i :: is, m, m', c, hr, h => by
    simp only [sRegs, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    have he := pElem_sound (env := env) i.op _ t ht
    rw [List.map_map] at he
    have hargs : (i.args.map ((fun x => x.ev env) ∘ rget m)) = i.args.map fun a => c.getD a 0#64 :=
      List.map_congr_left fun a _ => hr a
    rw [hargs] at he
    exact sRegs_sound is _ m' _ (relR_insert hr i.dst t _ he) h

/-- A lane's writes, symbolically, mean `BlockLower`'s. -/
theorem sLane_sound {p : ArrayKernel.Program} {ph : Phase} {look : Address → Option TP} {flat : FlatMemory} (hl : LookOk env look flat)
    (g l : Nat) (ws : List (Address × TP)) (h : sLane p ph look g l = some ws) :
    ws.map (fun x => (x.1, x.2.ev env)) = lowerLaneWrites p ph flat g l := by
  unfold sLane at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨m0, h0, m, h1, rfl⟩ := h
  have r0 := sLoads_sound hl g l ph.reads {} m0 ∅ relR_empty h0
  have r1 := sRegs_sound ph.code m0 m _ r0 h1
  simp only [lowerLaneWrites, List.map_map]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp, Prod.mk.injEq, true_and]
  exact r1 w.value

theorem allSome_map {α β γ : Type} (f : α → Option β) (G : β → γ) (F : α → γ) (hf : ∀ x y, f x = some y → G y = F x) :
    ∀ (xs : List α) (ys : List β), allSome f xs = some ys → ys.map G = xs.map F
  | [], ys, h => by simp only [allSome, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, ys', h', rfl⟩ := h
    simp only [List.map_cons, hf x y hy, allSome_map f G F hf xs ys' h']

/-- A phase's writes, symbolically, mean `BlockLower.lowerPhaseWrites`. -/
theorem sPhase_sound {p : ArrayKernel.Program} {ph : Phase} {look : Address → Option TP} {flat : FlatMemory} (hl : LookOk env look flat)
    (g : Nat) (ws : List (Address × TP)) (h : sPhase p ph look g = some ws) :
    ws.map (fun x => (x.1, x.2.ev env)) = lowerPhaseWrites p ph flat g := by
  unfold sPhase at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨yss, hy, rfl⟩ := h
  have := allSome_map (sLane p ph look g) (List.map fun x => (x.1, x.2.ev env)) (lowerLaneWrites p ph flat g)
    (fun l ws h => sLane_sound hl g l ws h) _ yss hy
  simp only [lowerPhaseWrites, List.map_flatten, this, List.flatMap_def]

/-! ## 2. A group: its phases in order -/

abbrev WMap := Std.HashMap (Nat × Nat) TP

def insW (wr : WMap) (ws : List (Address × TP)) : WMap := ws.foldl (fun m x => m.insert (key x.1) x.2) wr

/-- The group's view: its own writes so far, else the dispatch's start (`base`). -/
def look (base : Address → Option TP) (wr : WMap) (a : Address) : Option TP :=
  match wr[key a]? with
  | some t => some t
  | none => base a

def sGroup (p : ArrayKernel.Program) (base : Address → Option TP) (g : Nat) : List Phase → WMap → Option WMap
  | [], wr => some wr
  | ph :: phs, wr => (sPhase p ph (look base wr) g).bind fun ws => sGroup p base g phs (insW wr ws)

/-- A group's writes `wr` against the flat memory `f` it has made of `f0`: each write is what `f` holds,
the start view is right where the group has not written, and it has changed nothing else. -/
structure GInv (env : UInt64 → UInt32) (base : Address → Option TP) (f0 : FlatMemory) (wr : WMap) (f : FlatMemory) : Prop where
  wrote : ∀ a t, wr[key a]? = some t → t.ev env = f a
  view : ∀ a t, wr[key a]? = none → base a = some t → t.ev env = f a
  frame : ∀ a, wr[key a]? = none → f a = f0 a

theorem key_beq (a b : Address) : (key a == key b) = true ↔ a = b := by
  rw [beq_iff_eq]; exact ⟨key_inj, fun h => h ▸ rfl⟩

theorem insW_spec : ∀ (ws : List (Address × TP)) (wr : WMap) (f : FlatMemory),
    (∀ a t, wr[key a]? = some t → t.ev env = f a) →
    (∀ a t, (insW wr ws)[key a]? = some t → t.ev env = (ws.map fun x => (x.1, x.2.ev env)).foldl flatStore f a) ∧
    (∀ a, (insW wr ws)[key a]? = none → wr[key a]? = none ∧ (ws.map fun x => (x.1, x.2.ev env)).foldl flatStore f a = f a)
  | [], wr, f, h => ⟨h, fun a ha => ⟨ha, rfl⟩⟩
  | (b, u) :: ws, wr, f, h => by
    have ih := insW_spec ws (wr.insert (key b) u) (flatStore f (b, u.ev env)) (by
      intro a t ht
      rw [Std.HashMap.getElem?_insert] at ht
      simp only [flatStore]
      split at ht
      · rename_i e; rw [key_beq] at e; subst e; simp only [Option.some.injEq] at ht; subst ht; simp
      · rename_i e; rw [key_beq] at e; rw [ite_eq_right (Ne.symm e)]; exact h a t ht)
    simp only [insW, List.foldl_cons, List.map_cons] at ih ⊢
    refine ⟨ih.1, fun a ha => ?_⟩
    obtain ⟨h1, h2⟩ := ih.2 a ha
    rw [Std.HashMap.getElem?_insert] at h1
    split at h1
    · simp at h1
    · rename_i e; rw [key_beq] at e
      refine ⟨h1, ?_⟩
      rw [h2]; simp only [flatStore]; rw [ite_eq_right (Ne.symm e)]

theorem gInv_phase {p : ArrayKernel.Program} {ph : Phase} {base : Address → Option TP} {f0 : FlatMemory} {wr : WMap}
    {f : FlatMemory} (hi : GInv env base f0 wr f) (g : Nat) (ws : List (Address × TP))
    (h : sPhase p ph (look base wr) g = some ws) : GInv env base f0 (insW wr ws) (lowerPhase p ph g f) := by
  have hl : LookOk env (look base wr) f := by
    intro a t ht; unfold look at ht
    split at ht
    · rename_i t' e; simp only [Option.some.injEq] at ht; subst ht; exact hi.wrote a _ e
    · rename_i e; exact hi.view a t e ht
  have hws := sPhase_sound hl g ws h
  have hf : lowerPhase p ph g f = (ws.map fun x => (x.1, x.2.ev env)).foldl flatStore f := by
    unfold lowerPhase; rw [hws]
  obtain ⟨s1, s2⟩ := insW_spec ws wr f hi.wrote
  rw [hf]
  refine ⟨s1, fun a t ha hb => ?_, fun a ha => ?_⟩
  · obtain ⟨e1, e2⟩ := s2 a ha; rw [e2]; exact hi.view a t e1 hb
  · obtain ⟨e1, e2⟩ := s2 a ha; rw [e2]; exact hi.frame a e1

theorem sGroup_sound {p : ArrayKernel.Program} {base : Address → Option TP} {f0 : FlatMemory} (g : Nat) :
    ∀ (phs : List Phase) (wr wr' : WMap) (f : FlatMemory), GInv env base f0 wr f → sGroup p base g phs wr = some wr' →
      GInv env base f0 wr' (lowerPhases p phs g f)
  | [], wr, wr', f, hi, h => by simp only [sGroup, Option.some.injEq] at h; subst h; exact hi
  | ph :: phs, wr, wr', f, hi, h => by
    simp only [sGroup, Option.bind_eq_some_iff] at h
    obtain ⟨ws, hws, h⟩ := h
    exact sGroup_sound g phs _ wr' _ (gInv_phase hi g ws hws) h

/-! ## 3. A dispatch: its groups in order -/

/-- The dispatch's start for a group: a device word inside the buffer no earlier group of the dispatch
wrote (`D`), as the start's term; a constant as the literal the host binds; nothing of shared memory. -/
def base (words : Nat) (cv : Array Word) (rd : Nat → TP) (D : Std.HashMap Nat TP) (a : Address) : Option TP :=
  match a.1 with
  | .device => if a.2 < words && !D.contains a.2 then some (rd a.2) else none
  | .constant => cv[a.2]?.map pLit
  | .shared => none

/-- A group's writes into the dispatch's table: shared ones are its own; a device word inside the buffer
and not yet written is added; anything else (a constant, a word outside, a word written twice) refused. -/
def merge (words : Nat) : List ((Nat × Nat) × TP) → Std.HashMap Nat TP → Option (Std.HashMap Nat TP)
  | [], D => some D
  | ((c, j), t) :: rest, D =>
    if c = 1 then merge words rest D
    else if c = 0 ∧ j < words ∧ D.contains j = false then merge words rest (D.insert j t) else none

def sDispatch (p : ArrayKernel.Program) (phs : List Phase) (words : Nat) (cv : Array Word) (rd : Nat → TP) :
    List Nat → Std.HashMap Nat TP → Option (Std.HashMap Nat TP)
  | [], D => some D
  | g :: gs, D => (sGroup p (base words cv rd D) g phs {}).bind fun wr =>
      (merge words wr.toList D).bind (sDispatch p phs words cv rd gs)

theorem merge_spec (words : Nat) : ∀ (L : List ((Nat × Nat) × TP)) (D D' : Std.HashMap Nat TP), merge words L D = some D' →
    (∀ (c j : Nat) (t : TP), ((c, j), t) ∈ L → c = 1 ∨ (c = 0 ∧ j < words ∧ D.contains j = false)) ∧
    (∀ (j : Nat) (t : TP), D'[j]? = some t → D[j]? = some t ∨ ((0, j), t) ∈ L) ∧
    (∀ j : Nat, D'.contains j = false → D.contains j = false ∧ ∀ t : TP, ((0, j), t) ∉ L) ∧
    (∀ (j : Nat) (t : TP), D[j]? = some t → D'[j]? = some t)
  | [], D, D', h => by
    simp only [merge, Option.some.injEq] at h; subst h; simp
  | ((c, j), t) :: rest, D, D', h => by
    unfold merge at h
    split at h
    · rename_i hc
      obtain ⟨m1, m2, m3, m4⟩ := merge_spec words rest D D' h
      refine ⟨fun c' j' t' hm => ?_, fun j' t' h' => ?_, fun j' h' => ?_, m4⟩
      · rcases List.mem_cons.mp hm with e | e
        · simp only [Prod.mk.injEq] at e; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e; exact Or.inl hc
        · exact m1 c' j' t' e
      · rcases m2 j' t' h' with e | e
        · exact Or.inl e
        · exact Or.inr (List.mem_cons_of_mem _ e)
      · obtain ⟨e1, e2⟩ := m3 j' h'
        refine ⟨e1, fun t' hm => ?_⟩
        rcases List.mem_cons.mp hm with e | e
        · simp only [Prod.mk.injEq] at e; omega
        · exact e2 t' e
    · rename_i hc
      split at h
      · rename_i hd
        obtain ⟨h0, hj, hfree⟩ := hd
        obtain ⟨m1, m2, m3, m4⟩ := merge_spec words rest _ D' h
        have hins : ∀ k, (D.insert j t).contains k = true ↔ j = k ∨ D.contains k = true := by
          intro k; rw [Std.HashMap.contains_insert]; simp
        refine ⟨fun c' j' t' hm => ?_, fun j' t' h' => ?_, fun j' h' => ?_, fun j' t' h' => m4 j' t' ?_⟩
        · rcases List.mem_cons.mp hm with e | e
          · simp only [Prod.mk.injEq] at e; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e; exact Or.inr ⟨h0, hj, hfree⟩
          · rcases m1 c' j' t' e with e1 | ⟨e1, e2, e3⟩
            · exact Or.inl e1
            · refine Or.inr ⟨e1, e2, ?_⟩
              rw [Bool.eq_false_iff] at e3 ⊢; intro hc'; exact e3 ((hins j').mpr (Or.inr hc'))
        · rcases m2 j' t' h' with e | e
          · rw [Std.HashMap.getElem?_insert] at e
            split at e
            · rename_i e'; simp only [beq_iff_eq] at e'; subst e'; subst h0
              simp only [Option.some.injEq] at e; subst e; exact Or.inr List.mem_cons_self
            · exact Or.inl e
          · exact Or.inr (List.mem_cons_of_mem _ e)
        · obtain ⟨e1, e2⟩ := m3 j' h'
          have e1' : j ≠ j' ∧ D.contains j' = false := by
            rw [Bool.eq_false_iff] at e1
            refine ⟨fun e => e1 ((hins j').mpr (Or.inl e)), ?_⟩
            rw [Bool.eq_false_iff]; intro hc'; exact e1 ((hins j').mpr (Or.inr hc'))
          refine ⟨e1'.2, fun t' hm => ?_⟩
          rcases List.mem_cons.mp hm with e | e
          · simp only [Prod.mk.injEq] at e; exact e1'.1 e.1.2.symm
          · exact e2 t' e
        · rw [Std.HashMap.getElem?_insert]
          split
          · rename_i e'; simp only [beq_iff_eq] at e'; subst e'
            rw [Std.HashMap.contains_eq_isSome_getElem?, h'] at hfree; simp at hfree
          · exact h'
      · simp at h

/-- The dispatch so far, against the flat memory `f` it has made of the start `f0`. -/
structure DInv (env : UInt64 → UInt32) (words : Nat) (f0 : FlatMemory) (D : Std.HashMap Nat TP) (f : FlatMemory) : Prop where
  untouched : ∀ j, j < words → D.contains j = false → f (.device, j) = f0 (.device, j)
  consts : ∀ j, f (.constant, j) = f0 (.constant, j)
  table : ∀ j t, D[j]? = some t → j < words ∧ t.ev env = f (.device, j)
  past : ∀ j, words ≤ j → f (.device, j) = f0 (.device, j)

theorem sDispatch_sound {p : ArrayKernel.Program} {phs : List Phase} {words : Nat} {cv : Array Word} {rd : Nat → TP}
    {f0 : FlatMemory} (hrd : ∀ j, j < words → (rd j).ev env = f0 (.device, j))
    (hcv : ∀ j (h : j < cv.size), f0 (.constant, j) = cv[j]) :
    ∀ (gs : List Nat) (D D' : Std.HashMap Nat TP) (f : FlatMemory), DInv env words f0 D f →
      sDispatch p phs words cv rd gs D = some D' →
      DInv env words f0 D' (gs.foldl (fun f g => lowerPhases p phs g f) f)
  | [], D, D', f, hi, h => by simp only [sDispatch, Option.some.injEq] at h; subst h; exact hi
  | g :: gs, D, D', f, hi, h => by
    simp only [sDispatch, Option.bind_eq_some_iff] at h
    obtain ⟨wr, hwr, D1, hm, h⟩ := h
    have hbase : ∀ a t, base words cv rd D a = some t → t.ev env = f a := by
      intro a t ht
      obtain ⟨s, j⟩ := a
      cases s with
      | device =>
        simp only [base] at ht
        split at ht
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
          simp only [Option.some.injEq] at ht; subst ht
          rw [hrd j hc.1, hi.untouched j hc.1 hc.2]
        · simp at ht
      | constant =>
        simp only [base, Option.map_eq_some_iff] at ht
        obtain ⟨w, hw, rfl⟩ := ht
        rw [ev_lit, hi.consts j]
        obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hw
        exact (hcv j hj).symm
      | shared => simp [base] at ht
    have g0 : GInv env (base words cv rd D) f {} f :=
      ⟨fun a t h => by simp at h, fun a t _ h => hbase a t h, fun _ _ => rfl⟩
    have gi := sGroup_sound g phs {} wr f g0 hwr
    obtain ⟨m1, m2, m3, m4⟩ := merge_spec words wr.toList D D1 hm
    have mem : ∀ k t, (k, t) ∈ wr.toList ↔ wr[k]? = some t := fun k t => Std.HashMap.mem_toList_iff_getElem?_eq_some
    have nodev : ∀ j, (D.contains j = true ∨ words ≤ j) → wr[key (.device, j)]? = none := by
      intro j hj
      cases e : wr[key (.device, j)]? with
      | none => rfl
      | some t =>
        rcases m1 0 j t ((mem _ _).mpr e) with e1 | ⟨-, e2, e3⟩
        · simp at e1
        · rcases hj with hj | hj
          · rw [hj] at e3; simp at e3
          · omega
    have noconst : ∀ j, wr[key (.constant, j)]? = none := by
      intro j
      cases e : wr[key (.constant, j)]? with
      | none => rfl
      | some t =>
        rcases m1 2 j t ((mem _ _).mpr e) with e1 | ⟨e1, -⟩ <;> simp at e1
    have hi1 : DInv env words f0 D1 (lowerPhases p phs g f) := by
      refine ⟨fun j hj hc => ?_, fun j => ?_, fun j t ht => ?_, fun j hj => ?_⟩
      · obtain ⟨e1, e2⟩ := m3 j hc
        have hn : wr[key (.device, j)]? = none := by
          cases e : wr[key (.device, j)]? with
          | none => rfl
          | some t => exact absurd ((mem _ _).mpr e) (e2 t)
        rw [gi.frame _ hn]; exact hi.untouched j hj e1
      · rw [gi.frame _ (noconst j)]; exact hi.consts j
      · rcases m2 j t ht with e | e
        · have hc : D.contains j = true := by rw [Std.HashMap.contains_eq_isSome_getElem?, e]; rfl
          obtain ⟨e1, e2⟩ := hi.table j t e
          exact ⟨e1, by rw [gi.frame _ (nodev j (Or.inl hc))]; exact e2⟩
        · rcases m1 0 j t e with e1 | ⟨-, e2, -⟩
          · simp at e1
          · exact ⟨e2, gi.wrote _ t ((mem _ _).mp e)⟩
      · rw [gi.frame _ (nodev j (Or.inr hj))]; exact hi.past j hj
    simp only [List.foldl_cons]
    exact sDispatch_sound hrd hcv gs D1 D' _ hi1 h

/-! ## 4. The stage -/

/-- The wire buffer of a flat memory: the device space's words, `0` past the buffer. -/
def projB (words : Nat) (f : FlatMemory) (j : Nat) : Word := if j < words then f (.device, j) else 0

/-- The host binds the constants `cv` as the constant space. -/
def ConstsOk (cv : Array Word) (f : FlatMemory) : Prop := ∀ j (h : j < cv.size), f (.constant, j) = cv[j]

def blockTable (p : ArrayKernel.Program) (d : Dispatch) (words : Nat) (cv : Array Word) (rd : Nat → TP) :
    Option (Std.HashMap Nat TP) :=
  sDispatch p d.phases words cv rd (List.range d.groups) {}

/-- A block dispatch as a certificate stage: one wave per group with `lds` dwords of LDS. -/
def blockSpec (p : ArrayKernel.Program) (d : Dispatch) (words : Nat) (cv : Array Word) (lds : Nat) : Spec FlatMemory where
  threads := d.groups * lanes
  lds := lds
  table := blockTable p d words cv
  den := lowerDispatch p d

theorem blockSpec_sound (p : ArrayKernel.Program) (d : Dispatch) (words : Nat) (cv : Array Word) (lds : Nat) :
    (blockSpec p d words cv lds).Sound words (projB words) (ConstsOk cv) := by
  intro rd env x T hx hrd hT
  have hrd' : ∀ j, j < words → (rd j).ev env = x (.device, j) := by
    intro j hj; rw [hrd j]; simp [projB, hj]
  have d0 : DInv env words x {} x := ⟨fun _ _ _ => rfl, fun _ => rfl, fun j t h => by simp at h, fun _ _ => rfl⟩
  have hd := sDispatch_sound (p := p) (phs := d.phases) hrd' hx (List.range d.groups) {} T x d0 hT
  have hden : (blockSpec p d words cv lds).den x = (List.range d.groups).foldl (fun f g => lowerPhases p d.phases g f) x := rfl
  rw [hden]
  refine ⟨fun j hj => by rw [hd.consts j]; exact hx j hj, fun i t ht => ?_, fun i hi => ?_⟩
  · obtain ⟨e1, e2⟩ := hd.table i t ht
    exact ⟨e1, by simp only [projB, e1, ite_true]; exact e2⟩
  · unfold projB
    by_cases h : i < words
    · simp only [h, ite_true]
      exact hd.untouched i h (by rw [Std.HashMap.contains_eq_isSome_getElem?, hi]; rfl)
    · simp only [h, ite_false]

/-! ## 5. Every dispatch of a block program -/

/-- The wire buffer's words and the constants, as the plan gives them to the host (`BlockEmit.emitPlan`). -/
def blockWords (p : ArrayKernel.Program) : Nat := BlockEmit.spaceSize p .device

def blockSpecs (p : ArrayKernel.Program) (ldss : List Nat) : List (Spec FlatMemory) :=
  (p.dispatches.zip ldss).map fun x => blockSpec p x.1 (blockWords p) (BlockEmit.constWords p).toArray x.2

/-- The certificate of a block program's dumps `progs` (dispatch `k` with `ldss[k]` dwords of LDS): every
device array lies in the wire buffer, and every dispatch checks with the residuals in `rs`. -/
def certifyBlock (p : ArrayKernel.Program) (ldss : List Nat) (progs : List Program) (rs : List Residual) : Bool :=
  blockWords p < 2 ^ 29 && p.dispatches.length == ldss.length &&
  (List.range p.buffers.length).all (fun a =>
    (buffer p a).storage != .device || decide (bufferBase p a + (buffer p a).size ≤ blockWords p)) &&
  match checkProgram (blockWords p) (layoutMem (blockWords p) (BlockEmit.constWords p) []) (blockSpecs p ldss) progs {} {} with
  | some need => need.toList.all rs.contains
  | none => false

theorem blockSpecs_foldl (p : ArrayKernel.Program) (words : Nat) (cv : Array Word) :
    ∀ (ds : List Dispatch) (ls : List Nat) (x : FlatMemory), ds.length = ls.length →
      ((ds.zip ls).map fun y => blockSpec p y.1 words cv y.2).foldl (fun x s => s.den x) x
        = ds.foldl (fun f d => lowerDispatch p d f) x
  | [], [], _, _ => rfl
  | d :: ds, l :: ls, x, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
    exact blockSpecs_foldl p words cv ds ls _ (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- If the certificate is accepted and its residuals hold, then for every flat memory whose constant space
holds the plan's constants, the dumped programs run on the model as the host dispatches them succeed and
leave in every word of the wire buffer what `BlockLower.lowerProgram` leaves in the device space. -/
theorem certifyBlock_sound (p : ArrayKernel.Program) (ldss : List Nat) (progs : List Program) (rs : List Residual)
    (hc : certifyBlock p ldss progs rs = true) (hrs : ∀ r ∈ rs, r.Holds) (flat : FlatMemory)
    (hk : ConstsOk (BlockEmit.constWords p).toArray flat) :
    ∃ m, runDispatch (dispatchesOf (blockSpecs p ldss) progs)
        (memOf (blockWords p) (BlockEmit.constWords p) [] (fun j => flat (.device, j))) = some m ∧
      ∀ i, i < blockWords p → wordAt m i = lowerProgram p flat (.device, i) := by
  unfold certifyBlock at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hw, hlen⟩, -⟩, hcp⟩ := hc
  split at hcp
  · rename_i need hneed
    have hfin : ∀ r, need.contains r = true → r.Holds := by
      intro r hr
      apply hrs
      have := List.all_eq_true.mp hcp r (by rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]; exact hr)
      simpa using this
    have hss : ∀ s ∈ blockSpecs p ldss, s.Sound (blockWords p) (projB (blockWords p)) (ConstsOk (BlockEmit.constWords p).toArray) := by
      intro s hs
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hs
      exact blockSpec_sound p y.1 _ _ y.2
    have h0 := memOf_start (blockWords p) (BlockEmit.constWords p) [] hw (fun j => flat (.device, j))
    obtain ⟨m, known', hrun, hend, -⟩ := checkProgram_sound (x := flat) hw _ progs {} {} need _ hss hneed hfin h0 hk
    refine ⟨m, hrun, fun i hi => ?_⟩
    obtain ⟨lo, hi', e0, e1, e⟩ := hend.word i hi
    have a0 : wDw + UInt64.ofNat (2 * i) = dwLo i := rfl
    unfold wordAt
    rw [a0, e0, e1]
    simp only [Option.getD_some]
    rw [e]
    unfold blockSpecs
    rw [blockSpecs_foldl p _ _ p.dispatches ldss flat hlen]
    simp only [projB, hi, ite_true]
    rfl
  · simp at hcp

/-- Composed with the block program's lowering (`BlockLower.checkedProgram_sound`): for an admitted
program, every element of every device array, read from the model's final memory, is `evalProgram`'s. -/
theorem certifyBlock_eval (p : ArrayKernel.Program) (hchk : p.check = .ok ()) (ldss : List Nat) (progs : List Program)
    (rs : List Residual) (hc : certifyBlock p ldss progs rs = true) (hrs : ∀ r ∈ rs, r.Holds)
    (mem : ArrayKernel.Memory) (flat : FlatMemory) (hg : BlockLower.Good p mem) (hf : Represents p mem flat)
    (hk : ConstsOk (BlockEmit.constWords p).toArray flat) :
    ∃ m, runDispatch (dispatchesOf (blockSpecs p ldss) progs)
        (memOf (blockWords p) (BlockEmit.constWords p) [] (fun j => flat (.device, j))) = some m ∧
      ∀ a i, Valid p a i → (buffer p a).storage = .device →
        wordAt m (bufferBase p a + i) = ((evalProgram p mem).getD a #[]).getD i 0#64 := by
  obtain ⟨m, hrun, hw⟩ := certifyBlock_sound p ldss progs rs hc hrs flat hk
  refine ⟨m, hrun, fun a i hv hs => ?_⟩
  have hb : bufferBase p a + (buffer p a).size ≤ blockWords p := by
    unfold certifyBlock at hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
    have := hc.1.2 a hv.1
    simp only [hs, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this
    exact this
  rw [hw _ (by have := hv.2; omega)]
  have := checkedProgram_sound p mem flat hg hf hchk a i hv
  simp only [address, hs] at this
  exact this

end Obend.Hardware.Gpu.Rdna2.Block
