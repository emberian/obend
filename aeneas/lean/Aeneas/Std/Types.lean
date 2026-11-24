module

public section

universe u v

namespace Aeneas

namespace Std

/-- Rust runtime failure modes modeled explicitly by Aeneas's error monad. -/
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
  deriving Repr, BEq

instance : DecidableEq Error := fun a b => by
  cases a <;> cases b <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- Constructive Aeneas evaluation monad:
    every Rust expression evaluates to `.ok v`, `.fail err` (panic/overflow/OOB/div-by-zero),
    or `.div` (non-termination). -/
inductive Result (α : Type u) : Type u where
  | ok : α → Result α
  | fail : Error → Result α
  | div : Result α
  deriving Repr, BEq

instance {α : Type u} [DecidableEq α] : DecidableEq (Result α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    match decEq x y with
    | isTrue h => isTrue (congrArg Result.ok h)
    | isFalse h => isFalse (fun e => h (Result.ok.inj e))
  | .fail x, .fail y =>
    match decEq x y with
    | isTrue h => isTrue (congrArg Result.fail h)
    | isFalse h => isFalse (fun e => h (Result.fail.inj e))
  | .div, .div => isTrue rfl
  | .ok _, .fail _ | .ok _, .div | .fail _, .ok _ |
    .fail _, .div | .div, .ok _ | .div, .fail _ =>
    isFalse (by intro h; cases h)

@[expose]
def Result.bind {α : Type u} {β : Type v} (x : Result α) (f : α → Result β) : Result β :=
  match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance : Monad Result where
  pure := Result.ok
  bind := Result.bind

/-- Lift a pure value into `Result` (`let x ← lift expr` in Aeneas-generated Lean code). -/
@[expose]
def lift {α : Type u} (x : α) : Result α :=
  Result.ok x

/-- Rust `assert!(b)`: `.ok ()` when `b` holds, `.fail .assertionFailure` otherwise. -/
@[expose]
def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then Result.ok () else Result.fail Error.assertionFailure

/-- Loop step control flow (`cont` continues with updated state, `done` exits loop). -/
inductive ControlFlow (α : Type u) (β : Type v) where
  | cont : α → ControlFlow α β
  | done : β → ControlFlow α β
  deriving Repr, BEq

instance {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] :
    DecidableEq (ControlFlow α β) := fun a b =>
  match a, b with
  | .cont x, .cont y =>
    match decEq x y with
    | isTrue h => isTrue (congrArg ControlFlow.cont h)
    | isFalse h => isFalse (fun e => h (ControlFlow.cont.inj e))
  | .done x, .done y =>
    match decEq x y with
    | isTrue h => isTrue (congrArg ControlFlow.done h)
    | isFalse h => isFalse (fun e => h (ControlFlow.done.inj e))
  | .cont _, .done _ | .done _, .cont _ => isFalse (by intro h; cases h)

/-- Unsigned Rust machine-integer kinds (`usize` fixed to 64-bit `x86_64` / `aarch64` target). -/
inductive UScalarTy where
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128
  deriving Repr, BEq

instance : DecidableEq UScalarTy := fun a b => by
  cases a <;> cases b <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- Signed Rust machine-integer kinds (`isize` fixed to 64-bit `x86_64` / `aarch64` target). -/
inductive IScalarTy where
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  deriving Repr, BEq

instance : DecidableEq IScalarTy := fun a b => by
  cases a <;> cases b <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

@[reducible, expose]
def UScalarTy.numBits : UScalarTy → Nat
  | .Usize => 64
  | .U8 => 8
  | .U16 => 16
  | .U32 => 32
  | .U64 => 64
  | .U128 => 128

@[reducible, expose]
def IScalarTy.numBits : IScalarTy → Nat
  | .Isize => 64
  | .I8 => 8
  | .I16 => 16
  | .I32 => 32
  | .I64 => 64
  | .I128 => 128

/-- Fixed-width unsigned Rust scalar backed by `BitVec ty.numBits`. -/
structure UScalar (ty : UScalarTy) where
  bv : BitVec ty.numBits
  deriving Repr, BEq

instance {ty : UScalarTy} : DecidableEq (UScalar ty) := fun a b =>
  match decEq a.bv b.bv with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun heq => h (congrArg UScalar.bv heq))

/-- Fixed-width signed Rust scalar backed by `BitVec ty.numBits`. -/
structure IScalar (ty : IScalarTy) where
  bv : BitVec ty.numBits
  deriving Repr, BEq

instance {ty : IScalarTy} : DecidableEq (IScalar ty) := fun a b =>
  match decEq a.bv b.bv with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun heq => h (congrArg IScalar.bv heq))

instance {ty : UScalarTy} : LawfulBEq (UScalar ty) where
  eq_of_beq := by
    intro a b h
    change (a.bv == b.bv) = true at h
    change (a.bv.toNat == b.bv.toNat) = true at h
    rw [Nat.beq_eq_true_eq] at h
    have e : a.bv = b.bv := BitVec.toNat_inj.mp h
    cases a; cases b; cases e; rfl
  rfl := by
    intro a
    change (a.bv.toNat == a.bv.toNat) = true
    exact Nat.beq_refl _

instance {ty : IScalarTy} : LawfulBEq (IScalar ty) where
  eq_of_beq := by
    intro a b h
    change (a.bv == b.bv) = true at h
    change (a.bv.toNat == b.bv.toNat) = true at h
    rw [Nat.beq_eq_true_eq] at h
    have e : a.bv = b.bv := BitVec.toNat_inj.mp h
    cases a; cases b; cases e; rfl
  rfl := by
    intro a
    change (a.bv.toNat == a.bv.toNat) = true
    exact Nat.beq_refl _

@[reducible, expose]
def UScalar.val {ty : UScalarTy} (x : UScalar ty) : Nat :=
  x.bv.toNat

@[reducible, expose]
def IScalar.val {ty : IScalarTy} (x : IScalar ty) : Int :=
  x.bv.toInt

abbrev Usize := UScalar .Usize
abbrev U8 := UScalar .U8
abbrev U16 := UScalar .U16
abbrev U32 := UScalar .U32
abbrev U64 := UScalar .U64
abbrev U128 := UScalar .U128

abbrev Isize := IScalar .Isize
abbrev I8 := IScalar .I8
abbrev I16 := IScalar .I16
abbrev I32 := IScalar .I32
abbrev I64 := IScalar .I64
abbrev I128 := IScalar .I128

@[reducible, expose]
def UScalar.ofNat (ty : UScalarTy) (n : Nat) : UScalar ty :=
  ⟨BitVec.ofNat ty.numBits n⟩

@[reducible, expose]
def IScalar.ofInt (ty : IScalarTy) (z : Int) : IScalar ty :=
  ⟨BitVec.ofInt ty.numBits z⟩

def U8.ofNat (n : Nat) : U8 := UScalar.ofNat .U8 n
def U16.ofNat (n : Nat) : U16 := UScalar.ofNat .U16 n
def U32.ofNat (n : Nat) : U32 := UScalar.ofNat .U32 n
def U64.ofNat (n : Nat) : U64 := UScalar.ofNat .U64 n
def U128.ofNat (n : Nat) : U128 := UScalar.ofNat .U128 n
def Usize.ofNat (n : Nat) : Usize := UScalar.ofNat .Usize n

def I8.ofInt (z : Int) : I8 := IScalar.ofInt .I8 z
def I16.ofInt (z : Int) : I16 := IScalar.ofInt .I16 z
def I32.ofInt (z : Int) : I32 := IScalar.ofInt .I32 z
def I64.ofInt (z : Int) : I64 := IScalar.ofInt .I64 z
def Isize.ofInt (z : Int) : Isize := IScalar.ofInt .Isize z

macro:max x:term:max noWs "#u8"    : term => `(Aeneas.Std.UScalar.ofNat .U8 $x)
macro:max x:term:max noWs "#u16"   : term => `(Aeneas.Std.UScalar.ofNat .U16 $x)
macro:max x:term:max noWs "#u32"   : term => `(Aeneas.Std.UScalar.ofNat .U32 $x)
macro:max x:term:max noWs "#u64"   : term => `(Aeneas.Std.UScalar.ofNat .U64 $x)
macro:max x:term:max noWs "#u128"  : term => `(Aeneas.Std.UScalar.ofNat .U128 $x)
macro:max x:term:max noWs "#usize" : term => `(Aeneas.Std.UScalar.ofNat .Usize $x)

macro:max x:term:max noWs "#i8"    : term => `(Aeneas.Std.IScalar.ofInt .I8 $x)
macro:max x:term:max noWs "#i16"   : term => `(Aeneas.Std.IScalar.ofInt .I16 $x)
macro:max x:term:max noWs "#i32"   : term => `(Aeneas.Std.IScalar.ofInt .I32 $x)
macro:max x:term:max noWs "#i64"   : term => `(Aeneas.Std.IScalar.ofInt .I64 $x)
macro:max x:term:max noWs "#isize" : term => `(Aeneas.Std.IScalar.ofInt .Isize $x)

notation:70 a:70 "#uscalar" => Aeneas.Std.UScalar.mk (a)
notation:70 a:70 "#iscalar" => Aeneas.Std.IScalar.mk (a)

/-- Enum discriminant projection generated by `@[discriminant ...]`. -/
class Discriminant (α : Type u) (β : outParam (Type v)) where
  read_discriminant : α → β

export Discriminant (read_discriminant)

end Std

end Aeneas
