module

public import Aeneas.Std.Types

public section

universe u v

namespace Aeneas

namespace Std

open Result ControlFlow Error

def Usize.max : Nat := 18446744073709551615

theorem Usize.val_le_max (x : Usize) : x.val ≤ Usize.max := by
  have hlt : x.bv.toNat < 18446744073709551616 := x.bv.isLt
  change x.bv.toNat ≤ 18446744073709551615
  exact Nat.le_pred_of_lt hlt

/-- Fixed-length Rust array `[T; N]`. -/
structure Array (α : Type u) (n : Usize) where
  val : List α
  property : val.length = n.val
  deriving Repr

instance {α : Type u} {n : Usize} [DecidableEq α] : DecidableEq (Array α n) := fun a b =>
  match decEq a.val b.val with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun e => h (congrArg Array.val e))

theorem Array.ext {α : Type u} {n : Usize} {a b : Array α n} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

@[expose]
def Array.empty (α : Type u) : Array α 0#usize :=
  ⟨[], rfl⟩

@[expose]
def Array.make {α : Type u} (n : Usize) (ls : List α) (h : ls.length = n.val := by rfl) :
    Array α n :=
  ⟨ls, h⟩

@[expose]
def Array.repeat {α : Type u} (n : Usize) (x : α) : Array α n :=
  ⟨List.replicate n.val x, List.length_replicate⟩

@[expose]
def Array.index_usize {α : Type u} {n : Usize} (a : Array α n) (i : Usize) : Result α :=
  if h : i.val < a.val.length then
    .ok (a.val[i.val]'h)
  else
    .fail .arrayOutOfBounds

@[expose]
def Array.update {α : Type u} {n : Usize} (a : Array α n) (i : Usize) (v : α) :
    Result (Array α n) :=
  if _h : i.val < a.val.length then
    .ok ⟨a.val.set i.val v, by rw [List.length_set]; exact a.property⟩
  else
    .fail .arrayOutOfBounds

@[expose]
def Array.index_mut_usize {α : Type u} {n : Usize} (a : Array α n) (i : Usize) :
    Result (α × (α → Array α n)) :=
  if h : i.val < a.val.length then
    .ok (a.val[i.val]'h, fun v => ⟨a.val.set i.val v, by rw [List.length_set]; exact a.property⟩)
  else
    .fail .arrayOutOfBounds

/-- Borrowed Rust slice `&[T]` / `&mut [T]`. -/
structure Slice (α : Type u) where
  val : List α
  property : val.length ≤ Usize.max
  deriving Repr

instance {α : Type u} [DecidableEq α] : DecidableEq (Slice α) := fun a b =>
  match decEq a.val b.val with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun e => h (congrArg Slice.val e))

theorem Slice.ext {α : Type u} {a b : Slice α} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

@[expose]
def Slice.len {α : Type u} (s : Slice α) : Usize :=
  ⟨BitVec.ofNat 64 s.val.length⟩

@[simp]
theorem Slice.len_val {α : Type u} (s : Slice α) : (Slice.len s).val = s.val.length := by
  have hle : s.val.length ≤ 18446744073709551615 := s.property
  have hlt : s.val.length < 2 ^ 64 := Nat.lt_succ_of_le hle
  change (BitVec.ofNat 64 s.val.length).toNat = s.val.length
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

@[expose]
def Slice.index_usize {α : Type u} (s : Slice α) (i : Usize) : Result α :=
  if h : i.val < s.val.length then
    .ok (s.val[i.val]'h)
  else
    .fail .arrayOutOfBounds

@[expose]
def Slice.update {α : Type u} (s : Slice α) (i : Usize) (v : α) : Result (Slice α) :=
  if _h : i.val < s.val.length then
    .ok ⟨s.val.set i.val v, by rw [List.length_set]; exact s.property⟩
  else
    .fail .arrayOutOfBounds

@[expose]
def Array.to_slice {α : Type u} {n : Usize} (a : Array α n) : Slice α :=
  ⟨a.val, by rw [a.property]; exact Usize.val_le_max n⟩

@[expose]
def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h : s.val.length = n.val then ⟨s.val, h⟩ else a

@[expose]
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
    Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

end Std

end Aeneas
