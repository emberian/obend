module
public import Obend.Hardware.Gpu.Rdna2.Semantics
public import Obend.Apps.ZkNtt.Goldilocks
import Init.Data.Vector.Lemmas
import Init.Data.Fin.Lemmas

public section
namespace Obend.Hardware.Gpu.Rdna2
namespace Dpp
set_option autoImplicit false

/-!
DPP source routing, with architectural availability kept separate from lane algebra.
RDNA2 uses DPP16: quad permutations, row shifts/rotate and row mirrors. The older
wave shifts and row broadcasts are modelled for comparison but `rdna2Supported`
refuses them. In particular the classic six-step GCN reduction is NOT six RDNA2
DPP instructions. See LLVM AMDGPUModifierSyntax, dpp_ctrl versus dpp16_ctrl;
AMD RDNA2 ISA sections 6.4 and 12.12 (V_PERMLANE16/ V_PERMLANEX16).

`bound_ctrl` below is the encoded hardware bit, not LLVM's historical textual
`bound_ctrl:0` spelling. With FI clear, an inactive source is invalid. Invalid
sources supply zero when BC is set and suppress the destination write otherwise.
Destination EXEC, row_mask and bank_mask always suppress writes. Masks apply to
DESTINATIONS; they do not prevent fetching a masked row or bank's source.
-/

abbrev Lane := Fin 64
abbrev Lanes (α : Type) := Lane → α

inductive DppOp where
  | quad_perm (p0 p1 p2 p3 : Fin 4)
  | row_shl (k : Fin 16)
  | row_shr (k : Fin 16)
  | row_ror (k : Fin 16)
  | row_mirror
  | row_half_mirror
  | row_bcast15
  | row_bcast31
  | wave_shl1
  | wave_shr1
  deriving DecidableEq, Repr

structure DppCtrl where
  op : DppOp
  row_mask : BitVec 4 := 15
  bank_mask : BitVec 4 := 15
  bound_ctrl : Bool := false
  fetch_inactive : Bool := false
  deriving DecidableEq, Repr

/-- Zero shifts are reserved, not silently interpreted as legal identity instructions. -/
def rdna2Supported : DppOp → Bool
  | .row_bcast15 | .row_bcast31 | .wave_shl1 | .wave_shr1 => false
  | .row_shl k | .row_shr k | .row_ror k => k != 0
  | _ => true

/-- Natural source index, before range and EXEC validation. -/
def sourceIndex (op : DppOp) (i : Lane) : Option Nat :=
  let n := i.val
  let r := n / 16 * 16
  let c := n % 16
  match op with
  | .quad_perm a b c d =>
    some (n / 4 * 4 + (match n % 4 with | 0 => a.val | 1 => b.val | 2 => c.val | _ => d.val))
  | .row_shl k => if c + k.val < 16 then some (n + k.val) else none
  | .row_shr k => if k.val ≤ c then some (n - k.val) else none
  | .row_ror k => some (r + (c + 16 - k.val) % 16)
  | .row_mirror => some (r + (15 - c))
  | .row_half_mirror => some (n / 8 * 8 + (7 - n % 8))
  | .row_bcast15 => if n < 16 then none else some (r - 1)
  | .row_bcast31 => if 32 ≤ n then some 31 else none
  | .wave_shl1 => if n + 1 < 64 then some (n + 1) else none
  | .wave_shr1 => if 0 < n then some (n - 1) else none

/-- The selected source, or an invalid source (including EXEC masking when FI is clear). -/
def sourceLane (ctrl : DppCtrl) (exec : BitVec 64) (i : Lane) : Option Lane := do
  let n ← sourceIndex ctrl.op i
  if h : n < 64 then
    if ctrl.fetch_inactive || exec.getLsbD n then some ⟨n, h⟩ else none
  else none

def writesLane (ctrl : DppCtrl) (exec : BitVec 64) (i : Lane) : Bool :=
  exec.getLsbD i.val && ctrl.row_mask.getLsbD (i.val / 16) &&
    ctrl.bank_mask.getLsbD (i.val % 16 / 4)

/-- A V_MOV DPP, or the routing part of a VOP. The caller supplies old destination. -/
def shuffle {α : Type} (zero : α) (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Lanes α) (i : Lane) : α :=
  if writesLane ctrl exec i then
    match sourceLane ctrl exec i with
    | some j => src j
    | none => if ctrl.bound_ctrl then zero else old i
  else old i

/-- Unboxed array execution of all 64 independent lane transfers. -/
def shuffleExec (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Vector UInt32 64) : Vector UInt32 64 :=
  Vector.ofFn (shuffle 0 ctrl exec src.get old.get)

theorem shuffleExec_eq_spec (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Vector UInt32 64) (i : Lane) :
    (shuffleExec ctrl exec src old).get i = shuffle 0 ctrl exec src.get old.get i := by
  simp [shuffleExec, Vector.get, Vector.ofFn, Fin.cast]

theorem masked_holds {α : Type} (zero : α) (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Lanes α) (i : Lane) (h : writesLane ctrl exec i = false) :
    shuffle zero ctrl exec src old i = old i := by simp [shuffle, h]

theorem invalid_source_behavior {α : Type} (zero : α) (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Lanes α) (i : Lane) (hw : writesLane ctrl exec i = true)
    (hs : sourceLane ctrl exec i = none) :
    shuffle zero ctrl exec src old i = if ctrl.bound_ctrl then zero else old i := by
  simp [shuffle, hw, hs]

/-- Two 32-bit VGPR instructions, with identical control and destination masks. -/
def dppShuffleU64 (ctrl : DppCtrl) (exec : BitVec 64) (src old : Lanes UInt64) : Lanes UInt64 :=
  fun i => join64
    (shuffle 0 ctrl exec (fun j => (src j).toUInt32) (fun j => (old j).toUInt32) i)
    (shuffle 0 ctrl exec (fun j => (src j >>> 32).toUInt32) (fun j => (old j >>> 32).toUInt32) i)

private theorem join_halves (v : UInt64) : join64 v.toUInt32 (v >>> 32).toUInt32 = v := by
  unfold join64
  bv_decide

theorem dppShuffleU64_eq_spec (ctrl : DppCtrl) (exec : BitVec 64) (src old : Lanes UInt64) :
    dppShuffleU64 ctrl exec src old = shuffle 0 ctrl exec src old := by
  funext i
  unfold dppShuffleU64 shuffle
  split
  · split
    · exact join_halves _
    · split
      · rfl
      · exact join_halves _
  · exact join_halves _

/-- All EXEC bits enabled; invalid shifts supply zero for additive accumulation. -/
def fullCtrl (op : DppOp) : DppCtrl := { op, bound_ctrl := true }
def allExec : BitVec 64 := 0xffffffffffffffff

def route {α : Type} (zero : α) (op : DppOp) (x : Lanes α) : Lanes α :=
  shuffle zero (fullCtrl op) allExec x (fun _ => zero)

/-- XOR partners for the four row-local butterfly distances. Distance four uses
quad reversal followed by half-row reversal: XOR 3 followed by XOR 7 is XOR 4. -/
def rowPartner {α : Type} (zero : α) (stage : Fin 4) (x : Lanes α) : Lanes α :=
  match stage.val with
  | 0 => route zero (.quad_perm 1 0 3 2) x
  | 1 => route zero (.quad_perm 2 3 0 1) x
  | 2 => route zero .row_half_mirror (route zero (.quad_perm 3 2 1 0) x)
  | _ => route zero (.row_ror 8) x

/-- The proof reduces only 4×64 route indices; lane VALUES remain universally quantified. -/
theorem rowPartner_eq_xor {α : Type} (zero : α) (stage : Fin 4) (x : Lanes α) (i : Lane) :
    rowPartner zero stage x i = x ⟨i.val ^^^ (2 ^ stage.val), by
      have : ∀ (s : Fin 4) (j : Fin 64), j.val ^^^ (2 ^ s.val) < 64 := by decide
      exact this stage i⟩ := by
  have routing : ∀ (s : Fin 4) (j : Fin 64),
      rowPartner zero s x j = x ⟨j.val ^^^ (2 ^ s.val), by
        have : ∀ (s : Fin 4) (j : Fin 64), j.val ^^^ (2 ^ s.val) < 64 := by decide
        exact this s j⟩ := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    repeat' first | constructor | rfl
  exact routing stage i

/-- Goldilocks radix-2 butterfly: lower partner adds, upper partner subtracts.
The twiddle is supplied per pair (same value at both endpoints). -/
def butterfly (a b twiddle : Nat) (upper : Bool) : Nat :=
  let t := Obend.Apps.ZkNtt.goldilocksMulSpec twiddle b
  if upper then Obend.Apps.ZkNtt.goldilocksSubSpec a t
  else Obend.Apps.ZkNtt.goldilocksAddSpec a t

def dppRowButterfly (stage : Fin 4) (x twiddle : Lanes Nat) : Lanes Nat :=
  let partner := rowPartner 0 stage x
  fun i => if i.val / (2 ^ stage.val) % 2 == 0
    then butterfly (x i) (partner i) (twiddle i) false
    else butterfly (partner i) (x i) (twiddle i) true

def rowButterflySpec (stage : Fin 4) (x twiddle : Lanes Nat) : Lanes Nat :=
  fun i =>
    let j : Lane := ⟨i.val ^^^ (2 ^ stage.val), by
      have : ∀ (s : Fin 4) (j : Fin 64), j.val ^^^ (2 ^ s.val) < 64 := by decide
      exact this stage i⟩
    if i.val / (2 ^ stage.val) % 2 == 0
    then butterfly (x i) (x j) (twiddle i) false
    else butterfly (x j) (x i) (twiddle i) true

theorem dppRowButterfly_eq_spec (stage : Fin 4) (x twiddle : Lanes Nat) :
    dppRowButterfly stage x twiddle = rowButterflySpec stage x twiddle := by
  funext i
  simp only [dppRowButterfly, rowButterflySpec, rowPartner_eq_xor]

def dppQuadButterfly (stage : Fin 2) (x twiddle : Lanes Nat) : Lanes Nat :=
  dppRowButterfly ⟨stage.val, by omega⟩ x twiddle

theorem dppQuadButterfly_eq_spec (stage : Fin 2) (x twiddle : Lanes Nat) :
    dppQuadButterfly stage x twiddle = rowButterflySpec ⟨stage.val, by omega⟩ x twiddle :=
  dppRowButterfly_eq_spec _ _ _

/-- A shuffle-and-add semantic step. This is not a claim that modular 64-bit
addition plus two 32-bit transfers is one machine instruction. -/
def addStep {α : Type} (op : α → α → α) (zero : α) (ctrl : DppCtrl) (x : Lanes α) : Lanes α :=
  fun i => if writesLane ctrl allExec i then
    match sourceLane ctrl allExec i with
    | some j => op (x j) (x i)
    | none => if ctrl.bound_ctrl then op zero (x i) else x i
  else x i

/-- Legacy six-stage GCN network, useful as a mathematical reference only.
Rows 1 and 3 take the previous row's total, then rows 2 and 3 take lane 31.
RDNA2 requires a different cross-row lowering (see `rdna2Supported`). -/
def dppWave64ReduceAdd {α : Type} (op : α → α → α) (zero : α) (x : Lanes α) : Lanes α :=
  let a := addStep op zero (fullCtrl (.row_shr 1)) x
  let b := addStep op zero (fullCtrl (.row_shr 2)) a
  let c := addStep op zero (fullCtrl (.row_shr 4)) b
  let d := addStep op zero (fullCtrl (.row_shr 8)) c
  let e := addStep op zero { fullCtrl .row_bcast15 with row_mask := 10 } d
  addStep op zero { fullCtrl .row_bcast31 with row_mask := 12 } e

/-- Left-to-right associative fold, independent of the shuffle implementation. -/
def sumLanes {α : Type} (op : α → α → α) (zero : α) (x : Lanes α) : α :=
  (List.ofFn x).foldr op zero

private theorem tree8 {α : Type} (op : α → α → α)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (x0 x1 x2 x3 x4 x5 x6 x7 r : α) :
    op (op (op (op x0 x1) (op x2 x3)) (op (op x4 x5) (op x6 x7))) r =
      op x0 (op x1 (op x2 (op x3 (op x4 (op x5 (op x6 (op x7 r))))))) := by
  simp only [assoc]

set_option maxRecDepth 8192 in
theorem dppWave64ReduceAdd_eq_sum {α : Type} (op : α → α → α) (zero : α)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (right_id : ∀ a, op a zero = a) (x : Lanes α) :
    dppWave64ReduceAdd op zero x 63 = sumLanes op zero x := by
  have h63 := right_id (x 63)
  change op (op (op (op (op (op (x 0) (x 1)) (op (x 2) (x 3))) (op (op (x 4) (x 5)) (op (x 6) (x 7)))) (op (op (op (x 8) (x 9)) (op (x 10) (x 11))) (op (op (x 12) (x 13)) (op (x 14) (x 15))))) (op (op (op (op (x 16) (x 17)) (op (x 18) (x 19))) (op (op (x 20) (x 21)) (op (x 22) (x 23)))) (op (op (op (x 24) (x 25)) (op (x 26) (x 27))) (op (op (x 28) (x 29)) (op (x 30) (x 31)))))) (op (op (op (op (op (x 32) (x 33)) (op (x 34) (x 35))) (op (op (x 36) (x 37)) (op (x 38) (x 39)))) (op (op (op (x 40) (x 41)) (op (x 42) (x 43))) (op (op (x 44) (x 45)) (op (x 46) (x 47))))) (op (op (op (op (x 48) (x 49)) (op (x 50) (x 51))) (op (op (x 52) (x 53)) (op (x 54) (x 55)))) (op (op (op (x 56) (x 57)) (op (x 58) (x 59))) (op (op (x 60) (x 61)) (op (x 62) (x 63)))))) =
    op (x 0) (op (x 1) (op (x 2) (op (x 3) (op (x 4) (op (x 5) (op (x 6) (op (x 7) (op (x 8) (op (x 9) (op (x 10) (op (x 11) (op (x 12) (op (x 13) (op (x 14) (op (x 15) (op (x 16) (op (x 17) (op (x 18) (op (x 19) (op (x 20) (op (x 21) (op (x 22) (op (x 23) (op (x 24) (op (x 25) (op (x 26) (op (x 27) (op (x 28) (op (x 29) (op (x 30) (op (x 31) (op (x 32) (op (x 33) (op (x 34) (op (x 35) (op (x 36) (op (x 37) (op (x 38) (op (x 39) (op (x 40) (op (x 41) (op (x 42) (op (x 43) (op (x 44) (op (x 45) (op (x 46) (op (x 47) (op (x 48) (op (x 49) (op (x 50) (op (x 51) (op (x 52) (op (x 53) (op (x 54) (op (x 55) (op (x 56) (op (x 57) (op (x 58) (op (x 59) (op (x 60) (op (x 61) (op (x 62) (op (x 63) (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  rw [h63]
  repeat rw [assoc]

/-- A genuine RDNA2 cross-row primitive: V_PERMLANEX16 with identity selectors.
It exchanges rows 0↔1 and 2↔3, and cannot exchange the two 32-lane halves. -/
def permlanex16 {α : Type} (x : Lanes α) (i : Lane) : α :=
  x ⟨i.val ^^^ 16, by
    have : ∀ j : Fin 64, j.val ^^^ 16 < 64 := by decide
    exact this i⟩

/-- Cross-half transfer via scalar V_READLANE + V_WRITELANE pairs (64 pairs per
32-bit word), not DPP. No LDS, but substantially more instructions than a DPP.
This explicit fallback avoids pretending a DPP16 row route can implement XOR 32. -/
def readWriteLaneExchange32 {α : Type} (x : Lanes α) (i : Lane) : α :=
  x ⟨i.val ^^^ 32, by
    have : ∀ j : Fin 64, j.val ^^^ 32 < 64 := by decide
    exact this i⟩

/-- All six XOR partners, with the cross-row/cross-half implementation named. -/
def wavePartner {α : Type} (zero : α) (stage : Fin 6) (x : Lanes α) : Lanes α :=
  if h : stage.val < 4 then rowPartner zero ⟨stage.val, h⟩ x
  else if stage.val = 4 then permlanex16 x else readWriteLaneExchange32 x

/-- RDNA2 replacement for the legacy broadcast stages. The final stage uses the
explicit scalar lane-transfer fallback above. Six algorithmic stages, NOT six
DPP instructions; for UInt64 every lane transfer is performed on both halves. -/
def rdna2Wave64ReduceAdd {α : Type} (op : α → α → α) (zero : α) (x : Lanes α) : Lanes α :=
  let a := addStep op zero (fullCtrl (.row_shr 1)) x
  let b := addStep op zero (fullCtrl (.row_shr 2)) a
  let c := addStep op zero (fullCtrl (.row_shr 4)) b
  let d := addStep op zero (fullCtrl (.row_shr 8)) c
  let e := fun i => op (permlanex16 d i) (d i)
  fun i => op (readWriteLaneExchange32 e i) (e i)

theorem rdna2Wave64ReduceAdd_eq_sum {α : Type} (op : α → α → α) (zero : α)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (right_id : ∀ a, op a zero = a) (x : Lanes α) :
    rdna2Wave64ReduceAdd op zero x 63 = sumLanes op zero x := by
  change dppWave64ReduceAdd op zero x 63 = _
  exact dppWave64ReduceAdd_eq_sum op zero assoc right_id x

/-- Complete wave64 XOR partner specification; stages four and five explicitly
leave the DPP16 instruction subset. -/
theorem wavePartner_eq_xor {α : Type} (zero : α) (stage : Fin 6) (x : Lanes α) (i : Lane) :
    wavePartner zero stage x i = x ⟨i.val ^^^ (2 ^ stage.val), by
      have : ∀ (s : Fin 6) (j : Fin 64), j.val ^^^ (2 ^ s.val) < 64 := by decide
      exact this stage i⟩ := by
  unfold wavePartner
  split
  · exact rowPartner_eq_xor zero _ x i
  · split
    · rename_i h
      simp only [h]
      rfl
    · rename_i hlt hne
      have hv : stage.val = 5 := by omega
      simp only [hv]
      rfl

/-- No reserved or legacy cross-row operation enters the RDNA2 executable path. -/
def shuffleRdna2Exec (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Vector UInt32 64) : Except String (Vector UInt32 64) :=
  if rdna2Supported ctrl.op then .ok (shuffleExec ctrl exec src old)
  else .error "unsupported RDNA2 DPP16 control"

theorem shuffleRdna2Exec_refuses (ctrl : DppCtrl) (exec : BitVec 64)
    (src old : Vector UInt32 64) (h : rdna2Supported ctrl.op = false) :
    shuffleRdna2Exec ctrl exec src old = .error "unsupported RDNA2 DPP16 control" := by
  simp [shuffleRdna2Exec, h]

/-- Canonical Goldilocks lanes make modular addition a genuine associative
operation with zero identity, including values close to the 64-bit modulus. -/
abbrev GoldilocksLane := Fin Obend.Apps.ZkNtt.goldilocksPrime

instance : NeZero Obend.Apps.ZkNtt.goldilocksPrime := ⟨by decide⟩

def goldilocksAdd (a b : GoldilocksLane) : GoldilocksLane :=
  ⟨(a.val + b.val) % Obend.Apps.ZkNtt.goldilocksPrime, Nat.mod_lt _ (by decide)⟩

theorem goldilocksAdd_assoc (a b c : GoldilocksLane) :
    goldilocksAdd (goldilocksAdd a b) c = goldilocksAdd a (goldilocksAdd b c) := by
  apply Fin.ext
  simp only [goldilocksAdd, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem goldilocksAdd_zero (a : GoldilocksLane) : goldilocksAdd a 0 = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

theorem dppGoldilocksReduce_eq_sum (x : Lanes GoldilocksLane) :
    rdna2Wave64ReduceAdd goldilocksAdd 0 x 63 = sumLanes goldilocksAdd 0 x :=
  rdna2Wave64ReduceAdd_eq_sum goldilocksAdd 0 goldilocksAdd_assoc goldilocksAdd_zero x

/-- Radix-2 stages through distance 32, exposing the non-DPP cross-row fallback. -/
def waveButterfly (stage : Fin 6) (x twiddle : Lanes Nat) : Lanes Nat :=
  let partner := wavePartner 0 stage x
  fun i => if i.val / (2 ^ stage.val) % 2 == 0
    then butterfly (x i) (partner i) (twiddle i) false
    else butterfly (partner i) (x i) (twiddle i) true

def waveButterflySpec (stage : Fin 6) (x twiddle : Lanes Nat) : Lanes Nat :=
  fun i =>
    let j : Lane := ⟨i.val ^^^ (2 ^ stage.val), by
      have : ∀ (s : Fin 6) (j : Fin 64), j.val ^^^ (2 ^ s.val) < 64 := by decide
      exact this stage i⟩
    if i.val / (2 ^ stage.val) % 2 == 0
    then butterfly (x i) (x j) (twiddle i) false
    else butterfly (x j) (x i) (twiddle i) true

theorem waveButterfly_eq_spec (stage : Fin 6) (x twiddle : Lanes Nat) :
    waveButterfly stage x twiddle = waveButterflySpec stage x twiddle := by
  funext i
  simp only [waveButterfly, waveButterflySpec, wavePartner_eq_xor]

/-!
## The DPP16 modifier dword

A VOP1/VOP2 instruction selects DPP by `SRC0 = 0xFA`; its second dword then carries the real source and the
control. Field positions are those of AMD's `VOP1_VOP_DPP16` / `VOP2_VOP_DPP16` encodings (`Encodings.lean`, bits
32–63 of the instruction): `VSRC0` [7:0], `DPP_CTRL` [16:8], `FI` [18], `BOUND_CTRL` [19], the float `NEG`/`ABS`
modifiers [23:20], `BANK_MASK` [27:24], `ROW_MASK` [31:28]. `DPP_CTRL` values are LLVM's `AMDGPU::DppCtrl`
(`SIDefines.h`): quad permutations `0x00–0xFF`, `row_shl` `0x100 + k`, `row_shr` `0x110 + k`, `row_ror`
`0x120 + k`, `wave_shl1` `0x130`, `wave_shr1` `0x138`, `row_mirror` `0x140`, `row_half_mirror` `0x141`,
`row_bcast15` `0x142`, `row_bcast31` `0x143`. A word with bit 17 or a float modifier set is refused, since
`DppCtrl` carries neither.
-/

/-- The marker `SRC0 = 0xFA` of the first dword. -/
def dppSrc0Marker : Nat := 0xFA

def encodeDppOp : DppOp → Nat
  | .quad_perm a b c d => a.val + 4 * b.val + 16 * c.val + 64 * d.val
  | .row_shl k => 0x100 + k.val
  | .row_shr k => 0x110 + k.val
  | .row_ror k => 0x120 + k.val
  | .wave_shl1 => 0x130
  | .wave_shr1 => 0x138
  | .row_mirror => 0x140
  | .row_half_mirror => 0x141
  | .row_bcast15 => 0x142
  | .row_bcast31 => 0x143

def decodeDppOp (c : Nat) : Option DppOp :=
  if c < 0x100 then
    some (.quad_perm ⟨c % 4, Nat.mod_lt _ (by decide)⟩ ⟨c / 4 % 4, Nat.mod_lt _ (by decide)⟩
      ⟨c / 16 % 4, Nat.mod_lt _ (by decide)⟩ ⟨c / 64 % 4, Nat.mod_lt _ (by decide)⟩)
  else if c < 0x110 then some (.row_shl ⟨c % 16, Nat.mod_lt _ (by decide)⟩)
  else if c < 0x120 then some (.row_shr ⟨c % 16, Nat.mod_lt _ (by decide)⟩)
  else if c < 0x130 then some (.row_ror ⟨c % 16, Nat.mod_lt _ (by decide)⟩)
  else if c = 0x130 then some .wave_shl1
  else if c = 0x138 then some .wave_shr1
  else if c = 0x140 then some .row_mirror
  else if c = 0x141 then some .row_half_mirror
  else if c = 0x142 then some .row_bcast15
  else if c = 0x143 then some .row_bcast31
  else none

theorem encodeDppOp_lt (op : DppOp) : encodeDppOp op < 512 := by
  cases op <;> simp only [encodeDppOp] <;> omega

theorem decodeDppOp_encode (op : DppOp) : decodeDppOp (encodeDppOp op) = some op := by
  cases op with
  | quad_perm a b c d => revert a b c d; decide
  | row_shl k => revert k; decide
  | row_shr k => revert k; decide
  | row_ror k => revert k; decide
  | _ => rfl

/-- The modifier dword as a number. -/
def dppModifierNat (vsrc0 : Nat) (ctrl : DppCtrl) : Nat :=
  vsrc0 % 256 + 256 * encodeDppOp ctrl.op + 262144 * ctrl.fetch_inactive.toNat + 524288 * ctrl.bound_ctrl.toNat +
    16777216 * ctrl.bank_mask.toNat + 268435456 * ctrl.row_mask.toNat

def encodeDppWord32 (vsrc0 : Nat) (ctrl : DppCtrl) : UInt32 := UInt32.ofNat (dppModifierNat vsrc0 ctrl)

def decodeDppModifierNat (n : Nat) : Option (Nat × DppCtrl) :=
  if n / 131072 % 2 = 0 ∧ n / 1048576 % 16 = 0 then
    (decodeDppOp (n / 256 % 512)).map fun op =>
      (n % 256, { op, row_mask := BitVec.ofNat 4 (n / 268435456 % 16), bank_mask := BitVec.ofNat 4 (n / 16777216 % 16)
                , bound_ctrl := decide (n / 524288 % 2 = 1), fetch_inactive := decide (n / 262144 % 2 = 1) })
  else none

/-- Decode a DPP16 modifier dword to its source VGPR and control. -/
def decodeDppModifierWord (w : UInt32) : Option (Nat × DppCtrl) := decodeDppModifierNat w.toNat

private theorem dppFields (n x c f b bk rw : Nat) (hx : x < 256) (hc : c < 512) (hf : f < 2) (hb : b < 2)
    (hbk : bk < 16) (hrw : rw < 16)
    (hn : n = x + 256 * c + 262144 * f + 524288 * b + 16777216 * bk + 268435456 * rw) :
    n % 256 = x ∧ n / 256 % 512 = c ∧ n / 131072 % 2 = 0 ∧ n / 262144 % 2 = f ∧ n / 524288 % 2 = b ∧
    n / 1048576 % 16 = 0 ∧ n / 16777216 % 16 = bk ∧ n / 268435456 % 16 = rw ∧ n < 4294967296 := by
  subst hn; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dppModifierNat_lt (vsrc0 : Nat) (ctrl : DppCtrl) : dppModifierNat vsrc0 ctrl < 4294967296 :=
  (dppFields _ (vsrc0 % 256) (encodeDppOp ctrl.op) ctrl.fetch_inactive.toNat ctrl.bound_ctrl.toNat
    ctrl.bank_mask.toNat ctrl.row_mask.toNat (Nat.mod_lt _ (by decide)) (encodeDppOp_lt _) (Bool.toNat_lt _)
    (Bool.toNat_lt _) ctrl.bank_mask.isLt ctrl.row_mask.isLt rfl).2.2.2.2.2.2.2.2

/-- **Round trip of the modifier dword**: decoding an encoded source and control returns them. -/
theorem decodeDppModifierWord_encode (vsrc0 : Nat) (ctrl : DppCtrl) :
    decodeDppModifierWord (encodeDppWord32 vsrc0 ctrl) = some (vsrc0 % 256, ctrl) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := dppFields (dppModifierNat vsrc0 ctrl) (vsrc0 % 256)
    (encodeDppOp ctrl.op) ctrl.fetch_inactive.toNat ctrl.bound_ctrl.toNat ctrl.bank_mask.toNat ctrl.row_mask.toNat
    (Nat.mod_lt _ (by decide)) (encodeDppOp_lt _) (Bool.toNat_lt _) (Bool.toNat_lt _) ctrl.bank_mask.isLt
    ctrl.row_mask.isLt rfl
  have hw : (encodeDppWord32 vsrc0 ctrl).toNat = dppModifierNat vsrc0 ctrl := by
    simp only [encodeDppWord32, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h9
  simp only [decodeDppModifierWord, decodeDppModifierNat, hw, h1, h2, h3, h4, h5, h6, h7, h8, decodeDppOp_encode,
    and_self, ↓reduceIte, Option.map_some, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  cases ctrl with
  | mk op rm bm bc fi => cases bc <;> cases fi <;> rfl

/-- Decode the modifier dword, refuse anything outside RDNA2's DPP16 set, and route the 64 lanes of `src`. -/
def verifyDppWordShuffle (w : UInt32) (exec : BitVec 64) (src old : Vector UInt32 64) : Option (Vector UInt32 64) :=
  match decodeDppModifierWord w with
  | some (_, ctrl) => if rdna2Supported ctrl.op then some (shuffleExec ctrl exec src old) else none
  | none => none

example : (verifyDppWordShuffle (encodeDppWord32 3 (fullCtrl .row_mirror)) allExec
    (Vector.replicate 64 7) (Vector.replicate 64 0)).isSome = true := by
  simp [verifyDppWordShuffle, decodeDppModifierWord_encode, rdna2Supported, fullCtrl]

/-- **Lane footprint of an accepted modifier dword.** The word decodes to a supported control; a lane masked by
EXEC, `ROW_MASK` or `BANK_MASK` keeps its old value; a written lane takes its routed source lane, or, when the
source is invalid, zero under `BOUND_CTRL` and its old value otherwise. -/
theorem verifyDppWordShuffle_sound (w : UInt32) (exec : BitVec 64) (src old out : Vector UInt32 64)
    (h : verifyDppWordShuffle w exec src old = some out) :
    ∃ vsrc0 ctrl, decodeDppModifierWord w = some (vsrc0, ctrl) ∧ rdna2Supported ctrl.op = true ∧
      (∀ i : Lane, writesLane ctrl exec i = false → out.get i = old.get i) ∧
      (∀ (i j : Lane), writesLane ctrl exec i = true → sourceLane ctrl exec i = some j → out.get i = src.get j) ∧
      (∀ i : Lane, writesLane ctrl exec i = true → sourceLane ctrl exec i = none →
        out.get i = if ctrl.bound_ctrl then 0 else old.get i) := by
  unfold verifyDppWordShuffle at h
  split at h
  · rename_i v ctrl hd
    split at h
    · rename_i hs; injection h with ho; subst ho
      refine ⟨v, ctrl, hd, hs, fun i hw => ?_, fun i j hw hj => ?_, fun i hw hn => ?_⟩
      · rw [shuffleExec_eq_spec]; exact masked_holds 0 ctrl exec _ _ i hw
      · rw [shuffleExec_eq_spec]; simp [shuffle, hw, hj]
      · rw [shuffleExec_eq_spec]; exact invalid_source_behavior 0 ctrl exec _ _ i hw hn
    · cases h
  · cases h

/-- An encoded supported control shuffles exactly as the lane specification says. -/
theorem verifyDppWordShuffle_encode (vsrc0 : Nat) (ctrl : DppCtrl) (exec : BitVec 64) (src old : Vector UInt32 64)
    (hs : rdna2Supported ctrl.op = true) :
    verifyDppWordShuffle (encodeDppWord32 vsrc0 ctrl) exec src old = some (shuffleExec ctrl exec src old) := by
  simp [verifyDppWordShuffle, decodeDppModifierWord_encode, hs]

/-- Checked DPP16 modifier dword encoder refusing out-of-range VGPR indices `vsrc0 ≥ 256`. -/
def encodeDppWord32Checked? (vsrc0 : Nat) (ctrl : DppCtrl) : Option UInt32 :=
  if vsrc0 < 256 then some (encodeDppWord32 vsrc0 ctrl) else none

theorem decodeDppModifierWord_encodeChecked (vsrc0 : Nat) (ctrl : DppCtrl) (w : UInt32)
    (hEnc : encodeDppWord32Checked? vsrc0 ctrl = some w) :
    vsrc0 < 256 ∧ decodeDppModifierWord w = some (vsrc0, ctrl) := by
  unfold encodeDppWord32Checked? at hEnc
  split at hEnc
  · rename_i hLt; injection hEnc with hw; subst hw
    rw [decodeDppModifierWord_encode, Nat.mod_eq_of_lt hLt]
    exact ⟨hLt, rfl⟩
  · cases hEnc

/-- VGPR-file-aware DPP16 shuffle verifier selecting `vgprs vsrc0` from the decoded `vsrc0 < 256` field. -/
def verifyDppWordShuffleFromFile (w : UInt32) (exec : BitVec 64)
    (vgprs : Nat → Vector UInt32 64) (old : Vector UInt32 64) : Option (Vector UInt32 64) :=
  match decodeDppModifierWord w with
  | some (vsrc0, ctrl) => if rdna2Supported ctrl.op then some (shuffleExec ctrl exec (vgprs vsrc0) old) else none
  | none => none

theorem verifyDppWordShuffleFromFile_sound (w : UInt32) (exec : BitVec 64)
    (vgprs : Nat → Vector UInt32 64) (old out : Vector UInt32 64)
    (h : verifyDppWordShuffleFromFile w exec vgprs old = some out) :
    ∃ vsrc0 ctrl, vsrc0 < 256 ∧ decodeDppModifierWord w = some (vsrc0, ctrl) ∧ rdna2Supported ctrl.op = true ∧
      (∀ i : Lane, writesLane ctrl exec i = false → out.get i = old.get i) ∧
      (∀ (i j : Lane), writesLane ctrl exec i = true → sourceLane ctrl exec i = some j →
        out.get i = (vgprs vsrc0).get j) ∧
      (∀ i : Lane, writesLane ctrl exec i = true → sourceLane ctrl exec i = none →
        out.get i = if ctrl.bound_ctrl then 0 else old.get i) := by
  unfold verifyDppWordShuffleFromFile at h
  split at h
  · rename_i v ctrl hd
    have hvLt : v < 256 := by
      unfold decodeDppModifierWord decodeDppModifierNat at hd
      split at hd
      · obtain ⟨op, _, hEq⟩ := Option.map_eq_some_iff.mp hd
        have h1 : w.toNat % 256 = v := congrArg Prod.fst hEq
        rw [← h1]; exact Nat.mod_lt _ (by decide)
      · cases hd
    split at h
    · rename_i hs; injection h with ho; subst ho
      refine ⟨v, ctrl, hvLt, hd, hs, fun i hw => ?_, fun i j hw hj => ?_, fun i hw hn => ?_⟩
      · rw [shuffleExec_eq_spec]; exact masked_holds 0 ctrl exec _ _ i hw
      · rw [shuffleExec_eq_spec]; simp [shuffle, hw, hj]
      · rw [shuffleExec_eq_spec]; exact invalid_source_behavior 0 ctrl exec _ _ i hw hn
    · cases h
  · cases h

example : (verifyDppWordShuffleFromFile 0xff014000 allExec (fun _ => Vector.replicate 64 7)
    (Vector.replicate 64 0)).isSome = true := by decide

end Dpp
end Obend.Hardware.Gpu.Rdna2
