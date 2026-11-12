module
public import Obend.Crypto.PikkuFoldLayered
public import Obend.Crypto.PCS
import all Obend.Crypto.PikkuFoldLayered

public section
namespace Obend.Crypto.Fast.Canopy
open Obend.Digest.Cshake256

/-- A collision is returned as data, never eliminated from a Prop existential. -/
structure HashCollisionPair where
  x : ByteArray
  y : ByteArray
  different : x ≠ y
  equalHash : cshake256Bytes canopyMerkleCustomization x.data.toList =
    cshake256Bytes canopyMerkleCustomization y.data.toList

abbrev HashCollisionWitness := HashCollisionPair

def hashBytes (b : ByteArray) : Digest32 := evalDigest32 deployedCanopyHash32 b.data.toList
def node (l r : Digest32) : Digest32 := hashNode32 deployedCanopyHash32 l r

private def collisionOfDigest (x y : List UInt8) (hne : x ≠ y)
    (heq : evalDigest32 deployedCanopyHash32 x = evalDigest32 deployedCanopyHash32 y) : HashCollisionPair where
  x := Native.bytesOfList x
  y := Native.bytesOfList y
  different := by
    intro h; apply hne
    simpa only [Native.bytesOfList_toList] using congrArg (fun b => b.data.toList) h
  equalHash := by
    have h := congrArg (fun d => d.bytes.data.toList) heq
    simpa only [evalDigest32, Native.bytesOfList_toList, deployedCanopyHash32] using h

/-- LEB128 of canonical representatives is injective, unlike reduction of arbitrary 64-bit words. -/
def encodeRowList : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => leb128 x.val ++ encodeRowList xs

theorem encodeRowList_injective {xs ys : List Goldilocks} (hlen : xs.length = ys.length)
    (h : encodeRowList xs = encodeRowList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; exfalso; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; exfalso; omega
    | cons y ys =>
      obtain ⟨hv, ht⟩ := leb128_prefix_inj h
      have he : x = y := Goldilocks.ext hv
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [he, ih hlen ht]

def rowPreimage (idx : Nat) (row : Array Goldilocks) : List UInt8 :=
  [0] ++ leb128 idx ++ leb128 row.size ++ encodeRowList row.toList
def hashRow (idx : Nat) (row : Array Goldilocks) : Digest32 :=
  evalDigest32 deployedCanopyHash32 (rowPreimage idx row)

theorem rowPreimage_injective {i j : Nat} {a b : Array Goldilocks}
    (h : rowPreimage i a = rowPreimage j b) : i = j ∧ a = b := by
  simp only [rowPreimage, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  obtain ⟨hi, h⟩ := leb128_prefix_inj h
  obtain ⟨hs, h⟩ := leb128_prefix_inj h
  exact ⟨hi, Array.toList_inj.mp (encodeRowList_injective (by simpa using hs) h)⟩

abbrev Level (d : Nat) := Sized Digest32 (2^d)
abbrev Path (h : Nat) := Sized Digest32 h

private theorem pow_step (n : Nat) : 2^(n+1) = 2 * 2^n := by rw [Nat.pow_succ, Nat.mul_comm]

def parentLevel {d : Nat} (xs : Level (d+1)) : Level d :=
  Sized.ofFn fun i => node (xs.spec ⟨2*i.val, by have := i.isLt; rw [pow_step]; omega⟩)
    (xs.spec ⟨2*i.val+1, by have := i.isLt; rw [pow_step]; omega⟩)

def parentIndex {d : Nat} (i : Fin (2^(d+1))) : Fin (2^d) :=
  ⟨i.val / 2, by have := i.isLt; have hp := pow_step d; omega⟩

def siblingIndex {d : Nat} (i : Fin (2^(d+1))) : Fin (2^(d+1)) :=
  ⟨if i.val % 2 = 0 then i.val+1 else i.val-1, by
    have := i.isLt; have hp := pow_step d; split <;> omega⟩

def joinAt (idx : Nat) (value sibling : Digest32) : Digest32 :=
  if idx % 2 = 0 then node value sibling else node sibling value

theorem parentLevel_spec {d : Nat} (xs : Level (d+1)) (i : Fin (2^(d+1))) :
    (parentLevel xs).spec (parentIndex i) = joinAt i.val (xs.spec i) (xs.spec (siblingIndex i)) := by
  simp only [parentLevel, Sized.spec_ofFn, parentIndex, joinAt, siblingIndex]
  split <;> congr 2 <;> apply Fin.ext <;> simp only <;> omega

def pathHead {h : Nat} (p : Path (h+1)) : Digest32 := p.spec ⟨0, by omega⟩
def pathTail {h : Nat} (p : Path (h+1)) : Path h :=
  Sized.ofFn fun i => p.spec ⟨i.val+1, by omega⟩
def pathCons {h : Nat} (x : Digest32) (p : Path h) : Path (h+1) :=
  Sized.ofFn fun i => if hz : i.val = 0 then x else p.spec ⟨i.val-1, by omega⟩

@[simp] theorem pathHead_cons {h : Nat} (x : Digest32) (p : Path h) : pathHead (pathCons x p) = x := by
  simp [pathHead, pathCons]
@[simp] theorem pathTail_cons {h : Nat} (x : Digest32) (p : Path h) : pathTail (pathCons x p) = p := by
  apply Sized.ext; funext i; simp [pathTail, pathCons]

/-- Bottom-up array reduction. Each level allocates one contiguous array. -/
def reduceLevels : (h t : Nat) → Level (h+t) → Level t
  | 0, t, xs => ⟨xs.coeffs, by simpa using xs.size_eq⟩
  | h+1, t, xs => reduceLevels h t (parentLevel (d := h+t) ⟨xs.coeffs, by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using xs.size_eq⟩)

def capIndex : (h t : Nat) → Fin (2^(h+t)) → Fin (2^t)
  | 0, t, i => ⟨i.val, by simpa using i.isLt⟩
  | h+1, t, i => capIndex h t (parentIndex (d := h+t) ⟨i.val, by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using i.isLt⟩)

def openPath : (h t : Nat) → (xs : Level (h+t)) → Fin (2^(h+t)) → Path h
  | 0, _, _, _ => ⟨#[], rfl⟩
  | h+1, t, xs, i =>
    let ys : Level ((h+t)+1) := ⟨xs.coeffs, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using xs.size_eq⟩
    let j : Fin (2^((h+t)+1)) := ⟨i.val, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using i.isLt⟩
    pathCons (ys.spec (siblingIndex j)) (openPath h t (parentLevel ys) (parentIndex j))

def climb : (h : Nat) → Nat → Digest32 → Path h → Digest32
  | 0, _, value, _ => value
  | h+1, idx, value, p => climb h (idx/2) (joinAt idx value (pathHead p)) (pathTail p)

theorem openPath_complete (h t : Nat) (xs : Level (h+t)) (i : Fin (2^(h+t))) :
    climb h i.val (xs.spec i) (openPath h t xs i) = (reduceLevels h t xs).spec (capIndex h t i) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [openPath, climb, pathHead_cons, pathTail_cons, reduceLevels, capIndex]
    have hh := ih (parentLevel (d := h+t) ⟨xs.coeffs, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using xs.size_eq⟩)
      (parentIndex (d := h+t) ⟨i.val, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using i.isLt⟩)
    rw [parentLevel_spec] at hh
    exact hh

def root (t : Nat) (xs : Level t) : Digest32 :=
  (reduceLevels t 0 ⟨xs.coeffs, by simpa using xs.size_eq⟩).spec ⟨0, by simp⟩

theorem openRoot_complete (t : Nat) (xs : Level t) (i : Fin (2^t)) :
    climb t i.val (xs.spec i)
      (openPath t 0 ⟨xs.coeffs, by simpa using xs.size_eq⟩ ⟨i.val, by simp⟩) = root t xs := by
  have hh := openPath_complete t 0 ⟨xs.coeffs, by simpa using xs.size_eq⟩ ⟨i.val, by simp⟩
  change climb t i.val (xs.spec i) _ = _ at hh
  exact hh.trans (congrArg ((reduceLevels t 0 ⟨xs.coeffs, by simpa using xs.size_eq⟩).spec) (by
    apply Fin.ext
    have := (capIndex t 0 ⟨i.val, by simp⟩).isLt
    simp only [Nat.pow_zero] at this
    omega))

/-- Follow a disagreement upward until equal digests have distinct node preimages. -/
def climb_collision : (h : Nat) → (idx : Nat) → (x y : Digest32) → (p q : Path h) →
    x ≠ y → climb h idx x p = climb h idx y q → HashCollisionPair
  | 0, _, _, _, _, _, hne, heq => False.elim (hne heq)
  | h+1, idx, x, y, p, q, hne, heq =>
    if hn : joinAt idx x (pathHead p) = joinAt idx y (pathHead q) then
      if even : idx % 2 = 0 then
        collisionOfDigest (merkleNodePreimage x (pathHead p)) (merkleNodePreimage y (pathHead q))
          (fun hp => hne (merkleNodePreimage_injective hp).1)
          (by simpa [joinAt, even, node, hashNode32] using hn)
      else
        collisionOfDigest (merkleNodePreimage (pathHead p) x) (merkleNodePreimage (pathHead q) y)
          (fun hp => hne (merkleNodePreimage_injective hp).2)
          (by simpa [joinAt, even, node, hashNode32] using hn)
    else climb_collision h (idx/2) _ _ (pathTail p) (pathTail q) hn heq

/-- Shared cap authenticates every query's subtree once. -/
structure Config where
  bottomDepth : Nat
  capDepth : Nat
  positiveCap : 0 < capDepth
  width : Nat
  domain : DomainKind
  regime : ProximityRegime
  valid : ValidProximityConfig domain regime

abbrev Table (cfg : Config) := Sized (Sized Goldilocks cfg.width) (2^(cfg.bottomDepth+cfg.capDepth))
abbrev Query (cfg : Config) := Fin (2^(cfg.bottomDepth+cfg.capDepth))

def leaves (cfg : Config) (table : Table cfg) : Level (cfg.bottomDepth+cfg.capDepth) :=
  Sized.ofFn fun i => hashRow i.val (table.spec i).coeffs

structure BatchOpening (cfg : Config) (qs : Array (Query cfg)) where
  cap : Level cfg.capDepth
  rows : Sized (Sized Goldilocks cfg.width) qs.size
  paths : Sized (Path cfg.bottomDepth) qs.size

@[expose] def commit (cfg : Config) (table : Table cfg) : Digest32 :=
  root cfg.capDepth (reduceLevels cfg.bottomDepth cfg.capDepth (leaves cfg table))

def openBatchCanopy (cfg : Config) (table : Table cfg) (qs : Array (Query cfg)) : BatchOpening cfg qs where
  cap := reduceLevels cfg.bottomDepth cfg.capDepth (leaves cfg table)
  rows := Sized.ofFn fun j => table.spec qs[j.val]
  paths := Sized.ofFn fun j => openPath cfg.bottomDepth cfg.capDepth (leaves cfg table) qs[j.val]

@[expose] def verifyBatchCanopy (cfg : Config) (digest : Digest32) (qs : Array (Query cfg))
    (p : BatchOpening cfg qs) : Bool :=
  decide (root cfg.capDepth p.cap = digest) &&
    (Array.ofFn fun j : Fin qs.size =>
      decide (climb cfg.bottomDepth qs[j.val].val (hashRow qs[j.val].val (p.rows.spec j).coeffs)
        (p.paths.spec j) = p.cap.spec (capIndex cfg.bottomDepth cfg.capDepth qs[j.val]))).all id

theorem verifyBatchCanopy_complete (cfg : Config) (table : Table cfg) (qs : Array (Query cfg)) :
    verifyBatchCanopy cfg (commit cfg table) qs (openBatchCanopy cfg table qs) = true := by
  simp only [verifyBatchCanopy, openBatchCanopy, commit, Sized.spec_ofFn, decide_true, Bool.true_and]
  apply Array.all_eq_true.mpr
  intro j hj
  have hjq : j < qs.size := by simpa only [Array.size_ofFn] using hj
  rw [arrayOfFn_get _ ⟨j, hjq⟩]
  apply decide_eq_true
  simpa only [leaves, Sized.spec_ofFn] using
    openPath_complete cfg.bottomDepth cfg.capDepth (leaves cfg table) qs[j]

theorem recover_exact_row (cfg : Config) (table : Table cfg) (qs : Array (Query cfg)) (j : Fin qs.size) :
    ((openBatchCanopy cfg table qs).rows.spec j) = table.spec qs[j.val] := by
  simp [openBatchCanopy]

private theorem accepted_query (cfg : Config) (digest : Digest32) (qs : Array (Query cfg))
    (p : BatchOpening cfg qs) (h : verifyBatchCanopy cfg digest qs p = true) (j : Fin qs.size) :
    climb cfg.bottomDepth qs[j.val].val (hashRow qs[j.val].val (p.rows.spec j).coeffs) (p.paths.spec j) =
      p.cap.spec (capIndex cfg.bottomDepth cfg.capDepth qs[j.val]) := by
  simp only [verifyBatchCanopy, Bool.and_eq_true] at h
  have hx := Array.all_eq_true.mp h.2 j.val (by simp)
  rw [arrayOfFn_get _ j] at hx
  exact of_decide_eq_true hx

/-- Two distinct caps authenticating to the same root constructively exhibit a cSHAKE collision. -/
def capRoot_binding_collision (t : Nat) (digest : Digest32) (cap₁ cap₂ : Level t)
    (h₁ : root t cap₁ = digest) (h₂ : root t cap₂ = digest) (hne : cap₁ ≠ cap₂) :
    HashCollisionPair :=
  have specNe : cap₁.spec ≠ cap₂.spec := fun h => hne (Sized.ext h)
  let diff := findDifference (2^t) cap₁.spec cap₂.spec specNe
  let ci := diff.val
  let pp := openPath t 0 ⟨cap₁.coeffs, by simpa using cap₁.size_eq⟩ ⟨ci.val, by simp⟩
  let qp := openPath t 0 ⟨cap₂.coeffs, by simpa using cap₂.size_eq⟩ ⟨ci.val, by simp⟩
  climb_collision t ci.val (cap₁.spec ci) (cap₂.spec ci) pp qp diff.property
    ((openRoot_complete t cap₁ ci).trans (h₁.trans (h₂.symm.trans (openRoot_complete t cap₂ ci).symm)))

/-- Two accepted rows at the same query constructively yield an actual cSHAKE collision. -/
def verifyBatchCanopy_binding_collision (cfg : Config) (digest : Digest32) (qs : Array (Query cfg))
    (p q : BatchOpening cfg qs) (hp : verifyBatchCanopy cfg digest qs p = true)
    (hq : verifyBatchCanopy cfg digest qs q = true) (j : Fin qs.size)
    (hne : p.rows.spec j ≠ q.rows.spec j) : HashCollisionPair := by
  let idx := qs[j.val]
  let x := hashRow idx.val (p.rows.spec j).coeffs
  let y := hashRow idx.val (q.rows.spec j).coeffs
  if hxy : x = y then
    exact collisionOfDigest _ _ (fun h => hne (by
      have hh := (rowPreimage_injective h).2
      cases hp' : p.rows.spec j; cases hq' : q.rows.spec j
      simp only [hp', hq'] at hh
      cases hh; rfl)) hxy
  else
    let ci := capIndex cfg.bottomDepth cfg.capDepth idx
    if hc : p.cap.spec ci = q.cap.spec ci then
      exact climb_collision cfg.bottomDepth idx.val x y (p.paths.spec j) (q.paths.spec j) hxy
        ((accepted_query cfg digest qs p hp j).trans (hc.trans (accepted_query cfg digest qs q hq j).symm))
    else
      let pp := openPath cfg.capDepth 0 ⟨p.cap.coeffs, by simpa using p.cap.size_eq⟩ ⟨ci.val, by simp⟩
      let qp := openPath cfg.capDepth 0 ⟨q.cap.coeffs, by simpa using q.cap.size_eq⟩ ⟨ci.val, by simp⟩
      apply climb_collision cfg.capDepth ci.val (p.cap.spec ci) (q.cap.spec ci) pp qp hc
      rw [openRoot_complete, openRoot_complete]
      have hpRoot : root cfg.capDepth p.cap = digest := by
        simp only [verifyBatchCanopy, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1
      have hqRoot : root cfg.capDepth q.cap = digest := by
        simp only [verifyBatchCanopy, Bool.and_eq_true, decide_eq_true_eq] at hq; exact hq.1
      exact hpRoot.trans hqRoot.symm

@[expose] def naiveMerkleBatchHashes (q d : Nat) : Nat := q*d
@[expose] def canopyBatchHashes (q d t : Nat) : Nat := 2^t-1 + q*(d-t)

theorem canopy_hash_count_strictly_less (q d t : Nat) (ht : t ≤ d) (hsave : 2^t ≤ q*t) :
    canopyBatchHashes q d t < naiveMerkleBatchHashes q d := by
  have hpos : 0 < 2^t := Nat.pow_pos (by decide)
  have hsplit : q*d = q*(d-t) + q*t := by rw [← Nat.mul_add]; congr; omega
  unfold canopyBatchHashes naiveMerkleBatchHashes
  omega

/-- Canonical modular multiplication keeps the verifier and its L0 reductions choice-free. -/
def canopyMul (a b : Goldilocks) : Goldilocks := Goldilocks.ofNat (a.val*b.val)

theorem canopyMul_eq (a b : Goldilocks) : canopyMul a b = Goldilocks.mul a b := by
  apply Goldilocks.ext
  exact (Goldilocks.mul_val a b).symm

def rowScale {w : Nat} (c : Goldilocks) (row : Sized Goldilocks w) : Sized Goldilocks w :=
  Sized.ofFn fun i => canopyMul c (row.spec i)

theorem rowScale_eq {w : Nat} (c : Goldilocks) (row : Sized Goldilocks w) :
    rowScale c row = FastGoldilocksRing.scalarMulFast c row := by
  apply Sized.ext; funext i
  simp only [rowScale, FastGoldilocksRing.scalarMulFast, Sized.spec_ofFn, canopyMul_eq]

/-- Array dot product, with dimensions checked by the carrier. -/
def evalRow {w : Nat} (weights row : Sized Goldilocks w) : Goldilocks :=
  (Array.ofFn fun i : Fin w => canopyMul (weights.spec i) (row.spec i)).foldl Goldilocks.add Goldilocks.zero

/-- Adjacent even/odd codeword folding, not barycentric MLE folding. -/
def ifold {n : Nat} (α : Goldilocks) (codeword : Sized Goldilocks (2*n)) : Sized Goldilocks n :=
  Sized.ofFn fun i => Goldilocks.add (codeword.spec ⟨2*i.val, by omega⟩)
    (canopyMul α (codeword.spec ⟨2*i.val+1, by omega⟩))

/-- Horner accumulation over rows. The accumulator is one contiguous row. -/
def iacc {n w : Nat} (c : Goldilocks) (rows : Sized (Sized Goldilocks w) n) : Sized Goldilocks w :=
  rows.coeffs.foldl (fun acc row => FastGoldilocksRing.addFast
    (rowScale c acc) row) (FastGoldilocksRing.zeroFast w)

private theorem evalRow_zero {w : Nat} (weights : Sized Goldilocks w) :
    evalRow weights (FastGoldilocksRing.zeroFast w) = Goldilocks.zero := by
  unfold evalRow
  apply Array.foldl_induction (motive := fun _ acc => acc = Goldilocks.zero) rfl
  intro i acc h
  rw [h]
  change Goldilocks.add Goldilocks.zero
    ((Array.ofFn fun j : Fin w => canopyMul (weights.spec j) ((FastGoldilocksRing.zeroFast w).spec j))[i.val]) = _
  rw [Array.getElem_ofFn]
  simp only [FastGoldilocksRing.zeroFast, Sized.spec_ofFn]
  rw [canopyMul_eq]
  change CommRingOps.add (R := Goldilocks) CommRingOps.zero (CommRingOps.mul _ CommRingOps.zero) = _
  rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  rfl

private theorem evalRow_linear {w : Nat} (weights a b : Sized Goldilocks w) (c : Goldilocks) :
    evalRow weights (FastGoldilocksRing.addFast (rowScale c a) b) =
      Goldilocks.add (canopyMul c (evalRow weights a)) (evalRow weights b) := by
  simp only [canopyMul_eq, rowScale_eq]
  have aux (xs : List (Fin w)) (z x y : Goldilocks)
      (hz : z = Goldilocks.add (Goldilocks.mul c x) y) :
      xs.foldl (fun acc i => Goldilocks.add acc (Goldilocks.mul (weights.spec i)
        (Goldilocks.add (Goldilocks.mul c (a.spec i)) (b.spec i)))) z =
      Goldilocks.add
        (Goldilocks.mul c (xs.foldl (fun acc i => Goldilocks.add acc (Goldilocks.mul (weights.spec i) (a.spec i))) x))
        (xs.foldl (fun acc i => Goldilocks.add acc (Goldilocks.mul (weights.spec i) (b.spec i))) y) := by
    induction xs generalizing z x y with
    | nil => exact hz
    | cons i xs ih =>
      apply ih
      rw [hz]
      change CommRingOps.add (CommRingOps.add (CommRingOps.mul c x) y)
        (CommRingOps.mul _ (CommRingOps.add (CommRingOps.mul c _) _)) =
        CommRingOps.add (CommRingOps.mul c (CommRingOps.add x _)) (CommRingOps.add y _)
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
        LawfulCommRing.add_add_add_comm]
      congr 2
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (weights.spec i) c,
        LawfulCommRing.mul_assoc]
      rfl
  have repr (row : Sized Goldilocks w) : evalRow weights row =
      (Array.ofFn (fun i : Fin w => i)).toList.foldl
        (fun acc i => Goldilocks.add acc (Goldilocks.mul (weights.spec i) (row.spec i))) Goldilocks.zero := by
    unfold evalRow
    simp only [canopyMul_eq]
    rw [show (Array.ofFn fun i : Fin w => Goldilocks.mul (weights.spec i) (row.spec i)) =
        (Array.ofFn fun i : Fin w => i).map (fun i => Goldilocks.mul (weights.spec i) (row.spec i)) by
      simp only [Array.map_ofFn]; rfl]
    rw [Array.foldl_map, ← Array.foldl_toList]
  rw [repr, repr, repr]
  simp only [FastGoldilocksRing.addFast, FastGoldilocksRing.scalarMulFast, Sized.spec_ofFn]
  apply aux
  change CommRingOps.zero = CommRingOps.add (CommRingOps.mul c CommRingOps.zero) CommRingOps.zero
  rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]

theorem evalRow_iacc {n w : Nat} (weights : Sized Goldilocks w) (c : Goldilocks)
    (rows : Sized (Sized Goldilocks w) n) :
    evalRow weights (iacc c rows) = rows.coeffs.foldl
      (fun acc row => Goldilocks.add (canopyMul c acc) (evalRow weights row)) Goldilocks.zero := by
  unfold iacc
  have h := Array.foldl_hom (evalRow weights)
    (xs := rows.coeffs) (init := FastGoldilocksRing.zeroFast w)
    (g₁ := fun acc row => FastGoldilocksRing.addFast (rowScale c acc) row)
    (g₂ := fun acc row => Goldilocks.add (canopyMul c acc) (evalRow weights row))
    (fun acc row => (evalRow_linear weights acc row c).symm)
  rw [evalRow_zero] at h
  exact h.symm

private theorem butterfly_linear (α c x y u v : Goldilocks) :
    Goldilocks.add (Goldilocks.add (canopyMul c x) u)
      (canopyMul α (Goldilocks.add (canopyMul c y) v)) =
    Goldilocks.add (canopyMul c (Goldilocks.add x (canopyMul α y)))
      (Goldilocks.add u (canopyMul α v)) := by
  simp only [canopyMul_eq]
  change CommRingOps.add (CommRingOps.add (CommRingOps.mul c x) u)
    (CommRingOps.mul α (CommRingOps.add (CommRingOps.mul c y) v)) =
    CommRingOps.add (CommRingOps.mul c (CommRingOps.add x (CommRingOps.mul α y)))
      (CommRingOps.add u (CommRingOps.mul α v))
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]
  congr 2
  rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm α c, LawfulCommRing.mul_assoc]

theorem ifold_linear {w : Nat} (α c : Goldilocks) (a b : Sized Goldilocks (2*w)) :
    ifold α (FastGoldilocksRing.addFast (rowScale c a) b) =
      FastGoldilocksRing.addFast (rowScale c (ifold α a)) (ifold α b) := by
  apply Sized.ext; funext i
  simp only [ifold, FastGoldilocksRing.addFast, rowScale, Sized.spec_ofFn]
  exact butterfly_linear α c _ _ _ _

def foldRows {n w : Nat} (α : Goldilocks) (rows : Sized (Sized Goldilocks (2*w)) n) :
    Sized (Sized Goldilocks w) n := ⟨rows.coeffs.map (ifold α), by simp [rows.size_eq]⟩

theorem ifold_iacc {n w : Nat} (α c : Goldilocks) (rows : Sized (Sized Goldilocks (2*w)) n) :
    ifold α (iacc c rows) = iacc c (foldRows α rows) := by
  have hz : ifold α (FastGoldilocksRing.zeroFast (2*w)) = FastGoldilocksRing.zeroFast w := by
    apply Sized.ext; funext i
    simp only [ifold, FastGoldilocksRing.zeroFast, Sized.spec_ofFn]
    rw [canopyMul_eq]
    change CommRingOps.add (R := Goldilocks) CommRingOps.zero (CommRingOps.mul α CommRingOps.zero) = CommRingOps.zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  unfold iacc foldRows
  simp only [Array.foldl_map]
  have h := Array.foldl_hom (ifold α) (xs := rows.coeffs) (init := FastGoldilocksRing.zeroFast (2*w))
    (g₁ := fun acc row => FastGoldilocksRing.addFast (rowScale c acc) row)
    (g₂ := fun acc row => FastGoldilocksRing.addFast (rowScale c acc) (ifold α row))
    (fun acc row => (ifold_linear α c acc row).symm)
  rw [hz] at h
  exact h.symm

def pairedRows {n w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (rows : Sized (Sized Goldilocks cfg.width) n) : Sized (Sized Goldilocks (2*w)) n :=
  ⟨rows.coeffs.map (fun row => ⟨row.coeffs, row.size_eq.trans hw⟩), by simp [rows.size_eq]⟩

/-- Core algebraic & Merkle check given challenges `(α, c, weights)`; for end-to-end Fenzi-safe
    Fiat–Shamir challenge derivation from the absorbed instance & cap, use `verifyCanopyCommitAndReduceTranscript`. -/
@[expose] def verifyCanopyCommitAndReduce {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (digest : Digest32) (qs : Array (Query cfg)) (p : BatchOpening cfg qs)
    (α c : Goldilocks) (weights : Sized Goldilocks w) (claim : Goldilocks) : Bool :=
  verifyBatchCanopy cfg digest qs p &&
    decide (evalRow weights (ifold α (iacc c (pairedRows (w := w) cfg hw p.rows))) = claim)

theorem verifyCanopyCommitAndReduce_complete {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (table : Table cfg) (qs : Array (Query cfg)) (α c : Goldilocks) (weights : Sized Goldilocks w) :
    verifyCanopyCommitAndReduce (w := w) cfg hw (commit cfg table) qs (openBatchCanopy cfg table qs) α c weights
      ((foldRows α (pairedRows cfg hw (openBatchCanopy cfg table qs).rows)).coeffs.foldl
        (fun acc row => Goldilocks.add (canopyMul c acc) (evalRow weights row)) Goldilocks.zero) = true := by
  simp only [verifyCanopyCommitAndReduce, verifyBatchCanopy_complete, ifold_iacc, evalRow_iacc, decide_true, Bool.and_self]

/-- Two accepted, different evaluation claims constructively locate a differing
row and return a cSHAKE collision, without a global no-collision hypothesis. -/
def verifyCanopyCommitAndReduce_binding {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (digest : Digest32) (qs : Array (Query cfg)) (p r : BatchOpening cfg qs)
    (α c : Goldilocks) (weights : Sized Goldilocks w) (claim₁ claim₂ : Goldilocks)
    (hp : verifyCanopyCommitAndReduce cfg hw digest qs p α c weights claim₁ = true)
    (hr : verifyCanopyCommitAndReduce cfg hw digest qs r α c weights claim₂ = true)
    (hne : claim₁ ≠ claim₂) : HashCollisionPair := by
  have hpParts : verifyBatchCanopy cfg digest qs p = true ∧
      evalRow weights (ifold α (iacc c (pairedRows (w := w) cfg hw p.rows))) = claim₁ := by
    simpa only [verifyCanopyCommitAndReduce, Bool.and_eq_true, decide_eq_true_eq] using hp
  have hrParts : verifyBatchCanopy cfg digest qs r = true ∧
      evalRow weights (ifold α (iacc c (pairedRows (w := w) cfg hw r.rows))) = claim₂ := by
    simpa only [verifyCanopyCommitAndReduce, Bool.and_eq_true, decide_eq_true_eq] using hr
  have rowsNe : p.rows.spec ≠ r.rows.spec := by
    intro h
    have he := Sized.ext h
    apply hne
    rw [← hpParts.2, ← hrParts.2, he]
  let diff := findDifference qs.size p.rows.spec r.rows.spec rowsNe
  exact verifyBatchCanopy_binding_collision cfg digest qs p r hpParts.1 hrParts.1 diff.val diff.property

def accumulatorTranscript (cfg : Config) (digest : Digest32) (queryBytes pointBytes : ByteArray)
    (descriptor : ByteArray) : Transcript .relationBound :=
  bindRelation "OBEND.CANOPY.IACC/v1"
    (encodeFrame descriptor (Native.bytesOfList (leb128 cfg.bottomDepth ++ leb128 cfg.capDepth ++ leb128 cfg.width)) ByteArray.empty)
    (encodeFrame digest.bytes queryBytes pointBytes) (Transcript.newUnseeded ByteArray.empty)

/-- Canonical byte serialization of Canopy query indices. -/
def encodeQueryIndices (cfg : Config) (qs : Array (Query cfg)) : ByteArray :=
  Native.bytesOfList (leb128 qs.size ++ qs.toList.flatMap (fun q => leb128 q.val))

/-- Canonical byte serialization of a Canopy subtree cap. -/
def encodeCapDigests {t : Nat} (cap : Level t) : ByteArray :=
  Native.bytesOfList (leb128 cap.coeffs.size ++ cap.coeffs.toList.flatMap (fun d => encodeListField d.bytes.data.toList))

/-- Squeeze `k` canonical Goldilocks words from an `.instanceBound` transcript. -/
def squeezeGoldilocksList : (k : Nat) → Transcript .instanceBound → List Goldilocks × Transcript .instanceBound
  | 0, tr => ([], tr)
  | k + 1, tr =>
    let (g, tr₁) := squeezeGoldilocks tr
    let (gs, tr₂) := squeezeGoldilocksList k tr₁
    (g :: gs, tr₂)

theorem squeezeGoldilocksList_length :
    ∀ (k : Nat) (tr : Transcript .instanceBound), (squeezeGoldilocksList k tr).1.length = k
  | 0, _ => rfl
  | k + 1, tr => by
    simp [squeezeGoldilocksList, squeezeGoldilocksList_length k (squeezeGoldilocks tr).2]

/-- Squeeze `(α, c, weights)` strictly from an `.instanceBound` transcript after absorbing `(cfg, digest, qs, cap)`. -/
def deriveCanopyChallenges (w : Nat) (cfg : Config) (descriptor pointBytes : ByteArray)
    (digest : Digest32) (qs : Array (Query cfg)) (cap : Level cfg.capDepth) :
    Goldilocks × Goldilocks × Sized Goldilocks w :=
  let trRel := accumulatorTranscript cfg digest (encodeQueryIndices cfg qs) pointBytes descriptor
  let bTr := bindInstance (encodeCapDigests cap) trRel
  let (α, tr₁) := squeezeGoldilocks bTr.transcript
  let (c, tr₂) := squeezeGoldilocks tr₁
  let ws := (squeezeGoldilocksList w tr₂).1
  (α, c, ⟨ws.toArray, by simpa [ws] using squeezeGoldilocksList_length w tr₂⟩)

/-- **Constructive `0 Classical` Transcript-State & Cap Binding Extractor (`extractCanopyTranscriptCollisionOrEq`)**:
    Equal `.instanceBound` sponge states in `deriveCanopyChallenges` either arise from identical
    encoded relation frames AND identical serialized caps (`encodeCapDigests cap₁ = encodeCapDigests cap₂`),
    or constructively produce a bounded `cSHAKE256` collision witness on `fsInstanceCustomization` or `fsBindCustomization`. -/
def extractCanopyTranscriptCollisionOrEq (cfg₁ cfg₂ : Config)
    (desc₁ pt₁ desc₂ pt₂ : ByteArray) (d₁ d₂ : Digest32)
    (qs₁ : Array (Query cfg₁)) (qs₂ : Array (Query cfg₂))
    (cap₁ : Level cfg₁.capDepth) (cap₂ : Level cfg₂.capDepth)
    (hState : (bindInstance (encodeCapDigests cap₁)
                (accumulatorTranscript cfg₁ d₁ (encodeQueryIndices cfg₁ qs₁) pt₁ desc₁)).transcript.state =
              (bindInstance (encodeCapDigests cap₂)
                (accumulatorTranscript cfg₂ d₂ (encodeQueryIndices cfg₂ qs₂) pt₂ desc₂)).transcript.state) :
    PSum
      (encodeFrame desc₁ (Native.bytesOfList (leb128 cfg₁.bottomDepth ++ leb128 cfg₁.capDepth ++ leb128 cfg₁.width)) ByteArray.empty =
         encodeFrame desc₂ (Native.bytesOfList (leb128 cfg₂.bottomDepth ++ leb128 cfg₂.capDepth ++ leb128 cfg₂.width)) ByteArray.empty ∧
       encodeFrame d₁.bytes (encodeQueryIndices cfg₁ qs₁) pt₁ =
         encodeFrame d₂.bytes (encodeQueryIndices cfg₂ qs₂) pt₂ ∧
       encodeCapDigests cap₁ = encodeCapDigests cap₂)
      (PSum
        (Obend.Judge.Computational.HashCollisionWitness
          (cshake256Bytes fsInstanceCustomization)
          (Nat.max
            (instancePreimageList
              (accumulatorTranscript cfg₁ d₁ (encodeQueryIndices cfg₁ qs₁) pt₁ desc₁).state
              (accumulatorTranscript cfg₁ d₁ (encodeQueryIndices cfg₁ qs₁) pt₁ desc₁).stepCount
              (TranscriptEncode.encodeTranscriptBytes (encodeCapDigests cap₁))).length
            (instancePreimageList
              (accumulatorTranscript cfg₂ d₂ (encodeQueryIndices cfg₂ qs₂) pt₂ desc₂).state
              (accumulatorTranscript cfg₂ d₂ (encodeQueryIndices cfg₂ qs₂) pt₂ desc₂).stepCount
              (TranscriptEncode.encodeTranscriptBytes (encodeCapDigests cap₂))).length))
        (Obend.Judge.Computational.HashCollisionWitness
          (cshake256Bytes fsBindCustomization)
          (Nat.max
            (bindPreimageList (Transcript.newUnseeded ByteArray.empty).state "OBEND.CANOPY.IACC/v1"
              (encodeFrame desc₁ (Native.bytesOfList (leb128 cfg₁.bottomDepth ++ leb128 cfg₁.capDepth ++ leb128 cfg₁.width)) ByteArray.empty)
              (encodeFrame d₁.bytes (encodeQueryIndices cfg₁ qs₁) pt₁)).length
            (bindPreimageList (Transcript.newUnseeded ByteArray.empty).state "OBEND.CANOPY.IACC/v1"
              (encodeFrame desc₂ (Native.bytesOfList (leb128 cfg₂.bottomDepth ++ leb128 cfg₂.capDepth ++ leb128 cfg₂.width)) ByteArray.empty)
              (encodeFrame d₂.bytes (encodeQueryIndices cfg₂ qs₂) pt₂)).length))) :=
  match extractBindInstanceOrEq
      (encodeCapDigests cap₁) (encodeCapDigests cap₂)
      (accumulatorTranscript cfg₁ d₁ (encodeQueryIndices cfg₁ qs₁) pt₁ desc₁)
      (accumulatorTranscript cfg₂ d₂ (encodeQueryIndices cfg₂ qs₂) pt₂ desc₂) hState with
  | .inr wInst => .inr (.inl wInst)
  | .inl ⟨hTrRel, hCapEq⟩ =>
    match extractBindRelationOrEq
        (Transcript.newUnseeded ByteArray.empty) (Transcript.newUnseeded ByteArray.empty)
        "OBEND.CANOPY.IACC/v1" "OBEND.CANOPY.IACC/v1"
        (encodeFrame desc₁ (Native.bytesOfList (leb128 cfg₁.bottomDepth ++ leb128 cfg₁.capDepth ++ leb128 cfg₁.width)) ByteArray.empty)
        (encodeFrame desc₂ (Native.bytesOfList (leb128 cfg₂.bottomDepth ++ leb128 cfg₂.capDepth ++ leb128 cfg₂.width)) ByteArray.empty)
        (encodeFrame d₁.bytes (encodeQueryIndices cfg₁ qs₁) pt₁)
        (encodeFrame d₂.bytes (encodeQueryIndices cfg₂ qs₂) pt₂)
        (congrArg Transcript.state hTrRel) with
    | .inr wBind => .inr (.inr wBind)
    | .inl ⟨_, _, hRelEq, hInstFrameEq⟩ => .inl ⟨hRelEq, hInstFrameEq, hCapEq⟩

/-- **Fenzi-Safe Transcript-Bound Canopy Verifier (`verifyCanopyCommitAndReduceTranscript`)**:
    Absorbs `(descriptor, cfg, digest, qs, pointBytes)` and binds `p.cap` into `.instanceBound`
    *before* squeezing `(α, c, weights)`, closing out-of-transcript challenge quantification. -/
@[expose] def verifyCanopyCommitAndReduceTranscript {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (descriptor pointBytes : ByteArray) (digest : Digest32)
    (qs : Array (Query cfg)) (p : BatchOpening cfg qs) (claim : Goldilocks) : Bool :=
  let (α, c, weights) := deriveCanopyChallenges w cfg descriptor pointBytes digest qs p.cap
  verifyCanopyCommitAndReduce cfg hw digest qs p α c weights claim

theorem verifyCanopyCommitAndReduceTranscript_complete {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (descriptor pointBytes : ByteArray) (table : Table cfg) (qs : Array (Query cfg)) :
    let digest := commit cfg table
    let p := openBatchCanopy cfg table qs
    let (α, c, weights) := deriveCanopyChallenges w cfg descriptor pointBytes digest qs p.cap
    let claim := (foldRows α (pairedRows cfg hw p.rows)).coeffs.foldl
      (fun acc row => Goldilocks.add (canopyMul c acc) (evalRow weights row)) Goldilocks.zero
    verifyCanopyCommitAndReduceTranscript cfg hw descriptor pointBytes digest qs p claim = true := by
  dsimp only [verifyCanopyCommitAndReduceTranscript]
  exact verifyCanopyCommitAndReduce_complete cfg hw table qs _ _ _

/-- **Constructive `0 Classical` Transcript-Bound Binding Extractor**:
    Any two openings `p`, `r` accepted by `verifyCanopyCommitAndReduceTranscript` for `claim₁ ≠ claim₂`
    constructively yield a `HashCollisionPair` — either in the cap commitment (`p.cap ≠ r.cap`)
    or in the authenticated row/path openings under the identical squeezed `(α, c, weights)` (`p.cap = r.cap`). -/
def verifyCanopyCommitAndReduceTranscript_binding {w : Nat} (cfg : Config) (hw : cfg.width = 2*w)
    (descriptor pointBytes : ByteArray) (digest : Digest32) (qs : Array (Query cfg))
    (p r : BatchOpening cfg qs) (claim₁ claim₂ : Goldilocks)
    (hp : verifyCanopyCommitAndReduceTranscript cfg hw descriptor pointBytes digest qs p claim₁ = true)
    (hr : verifyCanopyCommitAndReduceTranscript cfg hw descriptor pointBytes digest qs r claim₂ = true)
    (hne : claim₁ ≠ claim₂) : HashCollisionPair :=
  if hCap : p.cap = r.cap then
    let ch := deriveCanopyChallenges w cfg descriptor pointBytes digest qs p.cap
    verifyCanopyCommitAndReduce_binding cfg hw digest qs p r ch.1 ch.2.1 ch.2.2 claim₁ claim₂
      hp (by dsimp only [verifyCanopyCommitAndReduceTranscript] at hr; rw [← hCap] at hr; exact hr) hne
  else
    have hpRoot : root cfg.capDepth p.cap = digest := by
      simp only [verifyCanopyCommitAndReduceTranscript, verifyCanopyCommitAndReduce, verifyBatchCanopy,
        Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp.1.1
    have hrRoot : root cfg.capDepth r.cap = digest := by
      simp only [verifyCanopyCommitAndReduceTranscript, verifyCanopyCommitAndReduce, verifyBatchCanopy,
        Bool.and_eq_true, decide_eq_true_eq] at hr
      exact hr.1.1
    capRoot_binding_collision cfg.capDepth digest p.cap r.cap hpRoot hrRoot hCap

/-- Offset signed encoding is injective on [-β,β] when 2β<p. -/
def encodeSignedCanonical (β : Nat) (z : Int) : Goldilocks := goldOfInt (z + β)

theorem encodeSignedCanonical_injective (β : Nat) (hβ : 2*β < Obend.Apps.ZkNtt.goldilocksPrime)
    (x y : Int) (hx : x.natAbs ≤ β) (hy : y.natAbs ≤ β)
    (h : encodeSignedCanonical β x = encodeSignedCanonical β y) : x = y := by
  have ax : x ≤ (x.natAbs : Int) := Int.le_natAbs
  have bx : -x ≤ (x.natAbs : Int) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -x))
  have ay : y ≤ (y.natAbs : Int) := Int.le_natAbs
  have by' : -y ≤ (y.natAbs : Int) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -y))
  have hv := congrArg (fun a : Goldilocks => (a.val : Int)) h
  simp only [encodeSignedCanonical, goldOfInt_val] at hv
  rw [Int.emod_eq_of_lt (by omega) (by dsimp only [goldP]; omega),
      Int.emod_eq_of_lt (by omega) (by dsimp only [goldP]; omega)] at hv
  omega

abbrev Witness (cfg : Config) := FastIntPoly (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)

def witnessRow (cfg : Config) (u : Witness cfg) (i : Query cfg) : FastIntPoly cfg.width :=
  Sized.ofFn fun j => u.spec ⟨i.val*cfg.width+j.val, by
    have := i.isLt
    have := Nat.mul_le_mul_right cfg.width (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at *
    omega⟩

def encodeRowOf (cfg : Config) (β : Nat) (u : Witness cfg) (i : Query cfg) : Sized Goldilocks cfg.width :=
  Sized.ofFn fun j => encodeSignedCanonical β ((witnessRow cfg u i).spec j)

def encodeWitness (cfg : Config) (β : Nat) (u : Witness cfg) : Table cfg :=
  Sized.ofFn (encodeRowOf cfg β u)

@[expose] def commitDual {m : Nat} (cfg : Config) (β : Nat)
    (A : IntMatrix m (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)) (q : Nat) (u : Witness cfg) :
    Digest32 × FastIntPoly m := (commit cfg (encodeWitness cfg β u), matVecModQ A q u)

theorem encodeRowOf_injective (cfg : Config) (β : Nat)
    (hβ : 2*β < Obend.Apps.ZkNtt.goldilocksPrime) (u v : Witness cfg) (i : Query cfg)
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β)
    (h : encodeRowOf cfg β u i = encodeRowOf cfg β v i) : witnessRow cfg u i = witnessRow cfg v i := by
  apply Sized.ext; funext j
  apply encodeSignedCanonical_injective β hβ
  · simp only [witnessRow, Sized.spec_ofFn]
    exact Nat.le_trans (coeff_le_norm u _) hu
  · simp only [witnessRow, Sized.spec_ofFn]
    exact Nat.le_trans (coeff_le_norm v _) hv
  · simpa only [encodeRowOf, Sized.spec_ofFn] using congrArg (fun a => a.spec j) h

/-- The query explicitly covers a differing witness row. Both reductions are returned. -/
def extractDualDoubleOpening {m : Nat} (cfg : Config) (β : Nat)
    (hβ : 2*β < Obend.Apps.ZkNtt.goldilocksPrime)
    (A : IntMatrix m (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)) (q : Nat)
    (u v : Witness cfg) (digest : Digest32) (qs : Array (Query cfg)) (j : Fin qs.size)
    (p r : BatchOpening cfg qs)
    (hpu : p.rows.spec j = encodeRowOf cfg β u qs[j.val])
    (hrv : r.rows.spec j = encodeRowOf cfg β v qs[j.val])
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β)
    (hp : verifyBatchCanopy cfg digest qs p = true)
    (hr : verifyBatchCanopy cfg digest qs r = true)
    (hne : witnessRow cfg u qs[j.val] ≠ witnessRow cfg v qs[j.val])
    (hcm : matVecModQ A q u = matVecModQ A q v) :
    HashCollisionPair × ShortSISKernelVec A q (2*β) := by
  have he : encodeRowOf cfg β u qs[j.val] ≠ encodeRowOf cfg β v qs[j.val] :=
    fun h => hne (encodeRowOf_injective cfg β hβ u v qs[j.val] hu hv h)
  exact ⟨verifyBatchCanopy_binding_collision cfg digest qs p r hp hr j
      (by rw [hpu, hrv]; exact he),
    foldTwoInstances_binding_reduction A q β u v
      (fun h => hne (congrArg (fun w => witnessRow cfg w qs[j.val]) h)) hcm hu hv⟩

/-- Compare the authenticated row with the reference first. A false hash opening
returns a collision; an honest row inconsistent with the lattice witness returns SIS. -/
def extractDualDiscrepancy {m : Nat} (cfg : Config) (β : Nat)
    (A : IntMatrix m (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)) (q : Nat)
    (wRef u : Witness cfg) (digest : Digest32) (cmLat : FastIntPoly m)
    (hRef : commitDual cfg β A q wRef = (digest, cmLat))
    (qs : Array (Query cfg)) (p : BatchOpening cfg qs) (j : Fin qs.size)
    (hp : verifyBatchCanopy cfg digest qs p = true)
    (hLat : matVecModQ A q u = cmLat)
    (hu : normInfFast u.coeffs ≤ β) (hr : normInfFast wRef.coeffs ≤ β)
    (hne : p.rows.spec j ≠ encodeRowOf cfg β u qs[j.val]) :
    HashCollisionPair ⊕ ShortSISKernelVec A q (2*β) := by
  have hDigest := congrArg Prod.fst hRef
  have hCm := congrArg Prod.snd hRef
  dsimp only [commitDual] at hDigest hCm
  have hOpen : verifyBatchCanopy cfg digest qs (openBatchCanopy cfg (encodeWitness cfg β wRef) qs) = true := by
    rw [← hDigest]; exact verifyBatchCanopy_complete cfg _ qs
  if he : p.rows.spec j = encodeRowOf cfg β wRef qs[j.val] then
    exact .inr (foldTwoInstances_binding_reduction A q β u wRef
      (fun h => hne (by rw [h]; exact he)) (hLat.trans hCm.symm) hu hr)
  else
    exact .inl (verifyBatchCanopy_binding_collision cfg digest qs p _ hp hOpen j
      (by simpa only [recover_exact_row, encodeWitness, Sized.spec_ofFn] using he))

end Obend.Crypto.Fast.Canopy
