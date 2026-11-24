module

public import Aeneas.Std.Types
public import Aeneas.Std.Containers
public import Aeneas.Elab.Attrs

public section

universe u v

namespace Aeneas

namespace Std

open Result ControlFlow Error

@[simp]
theorem bind_eq_result_bind {α β : Type u}
    (x : Result α) (f : α → Result β) : x >>= f = Result.bind x f := rfl

@[simp]
theorem pure_eq_ok {α : Type u} (x : α) : (pure x : Result α) = .ok x := rfl

@[simp]
theorem result_bind_ok {α : Type u} {β : Type v} (x : α) (f : α → Result β) :
    Result.bind (.ok x) f = f x := rfl

@[simp]
theorem lift_eq_ok {α : Type u} (x : α) : lift x = .ok x := rfl

theorem massert_pos {b : Prop} [Decidable b] (h : b) : massert b = .ok () := by
  unfold massert
  split
  · rfl
  · contradiction

theorem massert_neg {b : Prop} [Decidable b] (h : ¬ b) :
    massert b = .fail .assertionFailure := by
  unfold massert
  split
  · contradiction
  · rfl

/-- The guard `assert!(!flag)` passes on a cleared flag. -/
theorem massert_not_of_eq_false {b : Bool} (h : b = false) :
    massert (¬ (b = true)) = .ok () :=
  massert_pos (by rw [h]; exact Bool.false_ne_true)

/-- The guard `assert!(!flag)` fails on a set flag. -/
theorem massert_not_of_eq_true {b : Bool} (h : b = true) :
    massert (¬ (b = true)) = .fail .assertionFailure :=
  massert_neg (fun hn => hn h)

@[simp]
theorem UScalar.val_ofNat (ty : UScalarTy) (n : Nat) :
    (UScalar.ofNat ty n).val = n % (2 ^ ty.numBits) :=
  BitVec.toNat_ofNat n ty.numBits

/-! ## Scalar Extensionality, Bounds, and Checked Rust Arithmetic -/

theorem UScalar.ext {ty : UScalarTy} {a b : UScalar ty} (h : a.bv = b.bv) : a = b := by
  cases a; cases b; cases h; rfl

theorem UScalar.eq_of_val_eq {ty : UScalarTy} {a b : UScalar ty} (h : a.val = b.val) : a = b :=
  UScalar.ext (BitVec.eq_of_toNat_eq h)

theorem UScalar.val_lt {ty : UScalarTy} (x : UScalar ty) : x.val < 2 ^ ty.numBits :=
  x.bv.isLt

/-- Checked Rust unsigned addition: fails with `.integerOverflow` iff `a + b >= 2^W`. -/
instance {ty : UScalarTy} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd a b :=
    if a.val + b.val < 2 ^ ty.numBits then
      .ok ⟨a.bv + b.bv⟩
    else
      .fail .integerOverflow

/-- Checked Rust unsigned subtraction: fails with `.integerOverflow` iff `a < b`. -/
instance {ty : UScalarTy} : HSub (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hSub a b :=
    if b.val ≤ a.val then
      .ok ⟨a.bv - b.bv⟩
    else
      .fail .integerOverflow

/-- Checked Rust unsigned multiplication: fails with `.integerOverflow` iff `a * b >= 2^W`. -/
instance {ty : UScalarTy} : HMul (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMul a b :=
    if a.val * b.val < 2 ^ ty.numBits then
      .ok ⟨a.bv * b.bv⟩
    else
      .fail .integerOverflow

/-- Checked Rust unsigned division: fails with `.divisionByZero` iff `b == 0`. -/
instance {ty : UScalarTy} : HDiv (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hDiv a b :=
    if b.val = 0 then
      .fail .divisionByZero
    else
      .ok ⟨a.bv / b.bv⟩

/-- Checked Rust unsigned remainder: fails with `.divisionByZero` iff `b == 0`. -/
instance {ty : UScalarTy} : HMod (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMod a b :=
    if b.val = 0 then
      .fail .divisionByZero
    else
      .ok ⟨a.bv % b.bv⟩

/-- Checked Rust left shift by unsigned shift count: fails iff `rhs >= bitWidth`. -/
instance {ty rhsTy : UScalarTy} : HShiftLeft (UScalar ty) (UScalar rhsTy) (Result (UScalar ty)) where
  hShiftLeft a s :=
    if s.val < ty.numBits then
      .ok ⟨a.bv <<< s.val⟩
    else
      .fail .integerOverflow

/-- Checked Rust right shift by unsigned shift count: fails iff `rhs >= bitWidth`. -/
instance {ty rhsTy : UScalarTy} : HShiftRight (UScalar ty) (UScalar rhsTy) (Result (UScalar ty)) where
  hShiftRight a s :=
    if s.val < ty.numBits then
      .ok ⟨a.bv >>> s.val⟩
    else
      .fail .integerOverflow

/-- Checked Rust left shift by signed shift count: fails iff `rhs < 0` or `rhs >= bitWidth`. -/
instance {ty : UScalarTy} {rhsTy : IScalarTy} :
    HShiftLeft (UScalar ty) (IScalar rhsTy) (Result (UScalar ty)) where
  hShiftLeft a s :=
    if !s.bv.msb && s.bv.toNat < ty.numBits then
      .ok ⟨a.bv <<< s.bv.toNat⟩
    else
      .fail .integerOverflow

/-- Checked Rust right shift by signed shift count: fails iff `rhs < 0` or `rhs >= bitWidth`. -/
instance {ty : UScalarTy} {rhsTy : IScalarTy} :
    HShiftRight (UScalar ty) (IScalar rhsTy) (Result (UScalar ty)) where
  hShiftRight a s :=
    if !s.bv.msb && s.bv.toNat < ty.numBits then
      .ok ⟨a.bv >>> s.bv.toNat⟩
    else
      .fail .integerOverflow

instance {ty : UScalarTy} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd a b := ⟨a.bv &&& b.bv⟩

instance {ty : UScalarTy} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr a b := ⟨a.bv ||| b.bv⟩

instance {ty : UScalarTy} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor a b := ⟨a.bv ^^^ b.bv⟩

instance {ty : UScalarTy} : Complement (UScalar ty) where
  complement a := ⟨~~~ a.bv⟩

instance {ty : UScalarTy} : LT (UScalar ty) where
  lt a b := a.bv < b.bv

instance {ty : UScalarTy} : LE (UScalar ty) where
  le a b := a.bv ≤ b.bv

instance {ty : UScalarTy} (a b : UScalar ty) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.bv < b.bv))

instance {ty : UScalarTy} (a b : UScalar ty) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.bv ≤ b.bv))

@[simp]
theorem UScalar.lt_irrefl {ty : UScalarTy} (x : UScalar ty) : ¬ (x < x) :=
  BitVec.lt_irrefl x.bv

@[simp] theorem UScalar.lt_iff_val {ty : UScalarTy} (a b : UScalar ty) :
    (a < b) ↔ a.val < b.val :=
  BitVec.lt_def

@[simp] theorem UScalar.le_iff_val {ty : UScalarTy} (a b : UScalar ty) :
    (a ≤ b) ↔ a.val ≤ b.val :=
  BitVec.le_def

@[simp] theorem UScalarTy.numBits_usize : UScalarTy.Usize.numBits = 64 := rfl
@[simp] theorem UScalarTy.numBits_u8 : UScalarTy.U8.numBits = 8 := rfl
@[simp] theorem UScalarTy.numBits_u16 : UScalarTy.U16.numBits = 16 := rfl
@[simp] theorem UScalarTy.numBits_u32 : UScalarTy.U32.numBits = 32 := rfl
@[simp] theorem UScalarTy.numBits_u64 : UScalarTy.U64.numBits = 64 := rfl
@[simp] theorem UScalarTy.numBits_u128 : UScalarTy.U128.numBits = 128 := rfl
@[simp] theorem UScalar.bv_ofNat (ty : UScalarTy) (n : Nat) :
    (UScalar.ofNat ty n).bv = BitVec.ofNat ty.numBits n := rfl

@[simp] theorem UScalar.bv_and {ty : UScalarTy} (a b : UScalar ty) : (a &&& b).bv = a.bv &&& b.bv := rfl
@[simp] theorem UScalar.bv_or {ty : UScalarTy} (a b : UScalar ty) : (a ||| b).bv = a.bv ||| b.bv := rfl
@[simp] theorem UScalar.bv_xor {ty : UScalarTy} (a b : UScalar ty) : (a ^^^ b).bv = a.bv ^^^ b.bv := rfl
@[simp] theorem UScalar.bv_not {ty : UScalarTy} (a : UScalar ty) : (~~~ a).bv = ~~~ a.bv := rfl

/-- Rust `as` integer cast (`setWidth`: zero-extends when widening, truncates low bits when narrowing). -/
@[expose]
def UScalar.cast (dst : UScalarTy) {src : UScalarTy} (x : UScalar src) : UScalar dst :=
  ⟨x.bv.setWidth dst.numBits⟩

@[simp]
theorem hAdd_uscalar_eq {ty : UScalarTy} (a b : UScalar ty) :
    (a + b : Result (UScalar ty)) =
      if a.val + b.val < 2 ^ ty.numBits then .ok ⟨a.bv + b.bv⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hSub_uscalar_eq {ty : UScalarTy} (a b : UScalar ty) :
    (a - b : Result (UScalar ty)) =
      if b.val ≤ a.val then .ok ⟨a.bv - b.bv⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hMul_uscalar_eq {ty : UScalarTy} (a b : UScalar ty) :
    (a * b : Result (UScalar ty)) =
      if a.val * b.val < 2 ^ ty.numBits then .ok ⟨a.bv * b.bv⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hDiv_uscalar_eq {ty : UScalarTy} (a b : UScalar ty) :
    (a / b : Result (UScalar ty)) =
      if b.val = 0 then .fail .divisionByZero else .ok ⟨a.bv / b.bv⟩ := rfl

@[simp]
theorem hMod_uscalar_eq {ty : UScalarTy} (a b : UScalar ty) :
    (a % b : Result (UScalar ty)) =
      if b.val = 0 then .fail .divisionByZero else .ok ⟨a.bv % b.bv⟩ := rfl

@[simp]
theorem hShlI_uscalar_eq {ty : UScalarTy} {rhsTy : IScalarTy} (a : UScalar ty) (s : IScalar rhsTy) :
    (a <<< s : Result (UScalar ty)) =
      if !s.bv.msb && s.bv.toNat < ty.numBits then .ok ⟨a.bv <<< s.bv.toNat⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hShrI_uscalar_eq {ty : UScalarTy} {rhsTy : IScalarTy} (a : UScalar ty) (s : IScalar rhsTy) :
    (a >>> s : Result (UScalar ty)) =
      if !s.bv.msb && s.bv.toNat < ty.numBits then .ok ⟨a.bv >>> s.bv.toNat⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hShlU_uscalar_eq {ty rhsTy : UScalarTy} (a : UScalar ty) (s : UScalar rhsTy) :
    (a <<< s : Result (UScalar ty)) =
      if s.val < ty.numBits then .ok ⟨a.bv <<< s.val⟩ else .fail .integerOverflow := rfl

@[simp]
theorem hShrU_uscalar_eq {ty rhsTy : UScalarTy} (a : UScalar ty) (s : UScalar rhsTy) :
    (a >>> s : Result (UScalar ty)) =
      if s.val < ty.numBits then .ok ⟨a.bv >>> s.val⟩ else .fail .integerOverflow := rfl

/-! ## Constructive Fuel-Bounded Loop Evaluator -/

@[expose]
def loopFuel {α : Type u} {β : Type v} (fuel : Nat)
    (body : α → Result (ControlFlow α β)) (x : α) : Result β :=
  match fuel with
  | 0 => .div
  | fuel' + 1 =>
    Result.bind (body x) fun r =>
      match r with
      | .cont x' => loopFuel fuel' body x'
      | .done y => .ok y
termination_by structural fuel

@[expose]
def loopMaxFuel : Nat := Nat.pow 2 65

@[simp]
theorem usize_lt_loopMaxFuel (x : Usize) : x.val + 1 ≤ loopMaxFuel := by
  have h : x.val < 2 ^ 64 := x.bv.isLt
  change x.val + 1 ≤ 2 ^ 65
  exact Nat.le_trans h (by decide)

@[expose]
def loop {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) : Result β :=
  loopFuel loopMaxFuel body x

@[simp]
theorem loopFuel_zero {α : Type u} {β : Type v} (body : α → Result (ControlFlow α β)) (x : α) :
    loopFuel 0 body x = .div := rfl

@[simp]
theorem loopFuel_succ {α : Type u} {β : Type v} (fuel : Nat)
    (body : α → Result (ControlFlow α β)) (x : α) :
    loopFuel (fuel + 1) body x =
      Result.bind (body x) (fun r =>
        match r with
        | .cont x' => loopFuel fuel body x'
        | .done y => .ok y) := rfl

theorem loop_eq_loopFuel {α : Type u} {β : Type v}
    (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = loopFuel loopMaxFuel body x := rfl

theorem loopFuel_mono {α : Type u} {β : Type v}
    {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    {f1 f2 : Nat} (hle : f1 ≤ f2) (hok : loopFuel f1 body x = .ok y) :
    loopFuel f2 body x = .ok y := by
  induction f1 generalizing f2 x with
  | zero =>
    simp at hok
  | succ f1' ih =>
    cases f2 with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hle)
    | succ f2' =>
      simp only [loopFuel_succ] at hok ⊢
      cases hbody : body x with
      | fail e => simp [hbody, Result.bind] at hok
      | div => simp [hbody, Result.bind] at hok
      | ok cf =>
        simp only [hbody, Result.bind] at hok ⊢
        cases cf with
        | done v => exact hok
        | cont x' => exact ih (Nat.le_of_succ_le_succ hle) hok

theorem loop_ok_of_loopFuel {α : Type u} {β : Type v}
    {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    {fuel : Nat} (hle : fuel ≤ loopMaxFuel) (hok : loopFuel fuel body x = .ok y) :
    loop body x = .ok y :=
  loopFuel_mono hle hok

/-! ## `core::*` Trait/Function Dictionary Surface -/

namespace core

namespace clone
structure Clone (T : Type) where
  clone : T → Result T

abbrev impls.CloneUsize.clone (x : Usize) : Usize := x
abbrev impls.CloneU8.clone (x : U8) : U8 := x
abbrev impls.CloneBool.clone (x : Bool) : Bool := x
abbrev CloneU64 : Clone U64 := ⟨fun x => .ok x⟩
abbrev CloneU8 : Clone U8 := ⟨fun x => .ok x⟩
end clone

private def cloneList {α : Type} (inst : clone.Clone α) :
    (xs : List α) → Result { ys : List α // ys.length = xs.length }
  | [] => .ok ⟨[], rfl⟩
  | x :: xs => do
    let y ← inst.clone x
    let ys ← cloneList inst xs
    .ok ⟨y :: ys.val, congrArg Nat.succ ys.property⟩

/-- Array cloning traverses the supplied element cloning dictionary. -/
def array.CloneArray.clone {α : Type} {n : Usize}
    (inst : clone.Clone α) (a : Array α n) : Result (Array α n) := do
  let ys ← cloneList inst a.val
  .ok ⟨ys.val, ys.property.trans a.property⟩

namespace ops.drop
structure Drop (T : Type) where
  drop : T → Aeneas.Std.Result T
end ops.drop

namespace default
structure Default (T : Type) where
  default : Result T

@[expose]
def DefaultU8.default : U8 := 0#u8
@[expose]
def DefaultU64.default : U64 := 0#u64
end default

namespace slice
@[expose]
def Slice.is_empty {T : Type} (s : Aeneas.Std.Slice T) : Aeneas.Std.Result Bool :=
  .ok s.val.isEmpty
end slice

namespace num
@[expose]
def U64.MAX : U64 := ⟨BitVec.allOnes 64⟩

abbrev U64.rotate_left (x : U64) (n : U32) : U64 :=
  ⟨x.bv.rotateLeft (n.val % 64)⟩
end num

end core

/-! ## Mutation-Sensitivity / Non-Vacuity Witnesses on Checked Rust Semantics -/

/-- Checked `u64` addition genuinely rejects overflow (`u64::MAX + 1 = .fail .integerOverflow`). -/
theorem tooth_u64_add_overflows :
    (18446744073709551615#u64 + 1#u64 : Result U64) = .fail .integerOverflow := by
  rfl

/-- Checked `u64` subtraction genuinely rejects underflow (`0 - 1 = .fail .integerOverflow`). -/
theorem tooth_u64_sub_underflows :
    (0#u64 - 1#u64 : Result U64) = .fail .integerOverflow := by
  rfl

/-- Checked `u64` shift genuinely rejects out-of-range shift (`1 >>> 64 = .fail .integerOverflow`). -/
theorem tooth_u64_shr_out_of_range :
    (1#u64 >>> 64#i32 : Result U64) = .fail .integerOverflow := by
  rfl

/-- Checked array indexing genuinely rejects out-of-bounds indices (`[42][1] = .fail .arrayOutOfBounds`). -/
theorem tooth_array_index_oob :
    Array.index_usize (Array.make 1#usize [42#u8]) 1#usize = .fail .arrayOutOfBounds := by
  rfl

theorem bind_ok_step {α β : Type} {r : Result α} {f : α → Result β}
    {v : α} {out : β} (hr : r = .ok v) (hf : f v = .ok out) :
    (r >>= f) = .ok out := by
  rw [hr]
  exact hf

end Std

end Aeneas
