module
public import Obend.Hardware.ArrayBuild
public import Obend.Hardware.Gpu.LimbsGoldilocks
public import Obend.Hardware.Gpu.LimbsShift

/-! Goldilocks source construction and its register-program field semantics.
This is the shared source used by array graphs and BlockNtt register networks. -/
@[expose] public section
namespace Obend.Hardware.Gpu.GoldilocksSource
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild

def goldilocksP : Nat := 18446744069414584321

/-- The field constants a vector of length `n` needs: `p`, the low mask and the shift. -/
structure GlConsts where
  p    : Nat
  mask : Nat
  s32  : Nat

def glConsts (n : Nat) : BuildM GlConsts := do
  let p ← broadcast n (BitVec.ofNat 64 goldilocksP)
  let mask ← broadcast n 0xFFFFFFFF#64
  let s32 ← broadcast n 32#64
  pure ⟨p, mask, s32⟩

/-- `x < p ? x : x - p`. -/
def glCanon (n : Nat) (k : GlConsts) (x : Nat) : BuildM Nat := do
  let lt ← map2 n .ult x k.p
  let sub ← map2 n (.scalar .sub) x k.p
  map3 n (.scalar .mux) lt x sub

/-- `(a + b) mod p` for canonical `a b`, without a 65th bit. -/
def glAdd (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let remP ← map2 n (.scalar .sub) k.p b
  let lt ← map2 n .ult a remP
  let sum ← map2 n (.scalar .add) a b
  let wrap ← map2 n (.scalar .sub) a remP
  map3 n (.scalar .mux) lt sum wrap

/-- `(a - b) mod p` for canonical `a b`. -/
def glSub (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let lt ← map2 n .ult a b
  let pb ← map2 n (.scalar .sub) k.p b
  let wrap ← map2 n (.scalar .add) pb a
  let diff ← map2 n (.scalar .sub) a b
  map3 n (.scalar .mux) lt wrap diff

/-- `(a * b) mod p` for any 64-bit `a b`: four 32×32 limb products, the 128-bit product `(lo, hi)`, then
the shift/mask reduction (`goldilocksReduce128Spec`). -/
def glMul (n : Nat) (k : GlConsts) (a b : Nat) : BuildM Nat := do
  let aLo ← map2 n .band a k.mask
  let aHi ← map2 n .shr a k.s32
  let bLo ← map2 n .band b k.mask
  let bHi ← map2 n .shr b k.s32
  let p00 ← map2 n (.scalar .mul) aLo bLo
  let p01 ← map2 n (.scalar .mul) aLo bHi
  let p10 ← map2 n (.scalar .mul) aHi bLo
  let p11 ← map2 n (.scalar .mul) aHi bHi
  let p00Hi ← map2 n .shr p00 k.s32
  let p01Lo ← map2 n .band p01 k.mask
  let p10Lo ← map2 n .band p10 k.mask
  let mid32a ← map2 n (.scalar .add) p00Hi p01Lo
  let mid32 ← map2 n (.scalar .add) mid32a p10Lo
  let p00Lo ← map2 n .band p00 k.mask
  let mid32Lo ← map2 n .band mid32 k.mask
  let mid32LoSh ← map2 n .shl mid32Lo k.s32
  let lo ← map2 n .bor p00Lo mid32LoSh
  let p01Hi ← map2 n .shr p01 k.s32
  let p10Hi ← map2 n .shr p10 k.s32
  let mid32Hi ← map2 n .shr mid32 k.s32
  let hi1 ← map2 n (.scalar .add) p11 p01Hi
  let hi2 ← map2 n (.scalar .add) hi1 p10Hi
  let hi ← map2 n (.scalar .add) hi2 mid32Hi
  let hiLo ← map2 n .band hi k.mask
  let hiHi ← map2 n .shr hi k.s32
  let hiLoSh ← map2 n .shl hiLo k.s32
  let mid ← map2 n (.scalar .sub) hiLoSh hiLo
  let loC ← glCanon n k lo
  let t1 ← glAdd n k loC mid
  glSub n k t1 hiHi

theorem glCanon_run (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a : Nat)
    (ha : a < st.lengths.size) (hp : k.p < st.lengths.size) :
    let out := (glCanon n k a).run st
    evalBuild out.2 env out.1 =
      if (evalBuild st env a).ult (evalBuild st env k.p) then evalBuild st env a
      else evalBuild st env a - evalBuild st env k.p := by
  let r1 := (mapN n .ult [a, k.p]).run st
  let r2 := (mapN n (.scalar .sub) [a, k.p]).run r1.2
  let r3 := (mapN n (.scalar .mux) [r1.1, a, r2.1]).run r2.2
  change evalBuild r3.2 env r3.1 = _
  simp only [r3, evalBuild_mapN, r2, r1]
  simp only [mapN_run, Array.size_push]
  have hA0 : a ≠ st.lengths.size := by omega
  have hA1 : a ≠ st.lengths.size + 1 := by omega
  have hP0 : k.p ≠ st.lengths.size := by omega
  simp [stepInstr, evalElemOp, evalHypergraphOpBv, hA0, hA1, hP0]

end Obend.Hardware.Gpu.GoldilocksSource
