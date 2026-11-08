module
public import Obend.Hardware.Gpu.GoldilocksSource
@[expose] public section

/-! Universal field semantics of the shared source builder. Every theorem below
interprets the actual ArrayBuild.registerCode/evalBuild; the arithmetic network
is the source definition used by both vector graphs and register kernels. -/
namespace Obend.Hardware.Gpu.GoldilocksSourceCorrect
open Obend.Hardware.OpenHypergraph Obend.Hardware.ArrayHypergraph
open Obend.Hardware.ArrayBuild Obend.Hardware.Gpu.GoldilocksSource
open Obend.Apps.ZkNtt
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096


theorem bind_run {α β : Type} (x : BuildM α) (f : α → BuildM β) (st : Build) :
    ((x >>= f).run st) = (f (x.run st).1).run (x.run st).2 := rfl

theorem pure_run {α : Type} (x : α) (st : Build) :
    ((pure x : BuildM α).run st) = (x,st) := rfl

theorem evalBuild_mapN_value (st : Build) (env : Nat → Word) (n : Nat)
    (op : ElemOp) (args : List Nat) :
    evalBuild ((mapN n op args).run st).2 env ((mapN n op args).run st).1 =
      evalElemOp op (args.map (evalBuild st env)) := by
  rw [evalBuild_mapN,mapN_run]
  simp [stepInstr]

theorem evalBuild_mapN_frame (st : Build) (env : Nat → Word) (n : Nat)
    (op : ElemOp) (args : List Nat) (w : Nat) (hw : w < st.lengths.size) :
    evalBuild ((mapN n op args).run st).2 env w = evalBuild st env w := by
  rw [evalBuild_mapN]
  simp [stepInstr,show w ≠ st.lengths.size by omega]

theorem old_ne_fresh (st : Build) (a : Nat) (ha : a < st.lengths.size) (k : Nat) :
    a ≠ st.lengths.size+k := by omega

theorem glAdd_run (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hp : k.p < st.lengths.size) :
    let out := (glAdd n k a b).run st
    evalBuild out.2 env out.1 =
      if (evalBuild st env a).ult (evalBuild st env k.p-evalBuild st env b) then
        evalBuild st env a+evalBuild st env b
      else evalBuild st env a-(evalBuild st env k.p-evalBuild st env b) := by
  let r1 := (mapN n (.scalar .sub) [k.p,b]).run st
  let r2 := (mapN n .ult [a,r1.1]).run r1.2
  let r3 := (mapN n (.scalar .add) [a,b]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,r1.1]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r2.1,r3.1,r4.1]).run r4.2
  change evalBuild r5.2 env r5.1 = _
  simp only [r5,evalBuild_mapN,r4,r3,r2,r1]
  simp only [mapN_run,Array.size_push]
  have hA0 : a ≠ st.lengths.size := by omega
  have hB0 : b ≠ st.lengths.size := by omega
  have hP0 : k.p ≠ st.lengths.size := by omega
  simp [stepInstr,evalElemOp,evalHypergraphOpBv,old_ne_fresh st a ha,
    old_ne_fresh st b hb,old_ne_fresh st k.p hp,hA0,hB0,hP0,Nat.add_assoc]

theorem glSub_run (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hp : k.p < st.lengths.size) :
    let out := (glSub n k a b).run st
    evalBuild out.2 env out.1 =
      if (evalBuild st env a).ult (evalBuild st env b) then
        (evalBuild st env k.p-evalBuild st env b)+evalBuild st env a
      else evalBuild st env a-evalBuild st env b := by
  let r1 := (mapN n .ult [a,b]).run st
  let r2 := (mapN n (.scalar .sub) [k.p,b]).run r1.2
  let r3 := (mapN n (.scalar .add) [r2.1,a]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,b]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r1.1,r3.1,r4.1]).run r4.2
  change evalBuild r5.2 env r5.1 = _
  simp only [r5,evalBuild_mapN,r4,r3,r2,r1]
  simp only [mapN_run,Array.size_push]
  have hA0 : a ≠ st.lengths.size := by omega
  have hB0 : b ≠ st.lengths.size := by omega
  have hP0 : k.p ≠ st.lengths.size := by omega
  simp [stepInstr,evalElemOp,evalHypergraphOpBv,old_ne_fresh st a ha,
    old_ne_fresh st b hb,old_ne_fresh st k.p hp,hA0,hB0,hP0,Nat.add_assoc]

/-- Receipt for the concrete constant registers consumed by every field builder. -/
structure ConstsAt (st : Build) (env : Nat → Word) (k : GlConsts) : Prop where
  p_lt : k.p < st.lengths.size
  mask_lt : k.mask < st.lengths.size
  s32_lt : k.s32 < st.lengths.size
  p_value : evalBuild st env k.p = BitVec.ofNat 64 goldilocksP
  mask_value : evalBuild st env k.mask = 0xFFFFFFFF#64
  s32_value : evalBuild st env k.s32 = 32#64

theorem broadcast_run (st : Build) (n : Nat) (v : Word) :
    (broadcast n v).run st =
      (st.lengths.size,⟨st.lengths.push n,
        st.edges.push ⟨st.edges.size,.const (List.replicate n v),[],st.lengths.size⟩⟩) := by
  change (st.lengths.size,(⟨st.lengths.push (List.replicate n v).length,
    st.edges.push ⟨st.edges.size,.const (List.replicate n v),[],st.lengths.size⟩⟩ : Build)) = _
  simp

theorem registerCode_broadcast (st : Build) (n : Nat) (v : Word) (hn : 0 < n) :
    registerCode ((broadcast n v).run st).2 =
      registerCode st ++ [⟨.scalar (.const v.toInt),[],st.lengths.size⟩] := by
  rw [broadcast_run]
  cases n with
  | zero => omega
  | succ n => simp [registerCode]

theorem evalBuild_broadcast (st : Build) (env : Nat → Word) (n : Nat) (v : Word) (hn : 0 < n) :
    evalBuild ((broadcast n v).run st).2 env =
      stepInstr (evalBuild st env) ⟨.scalar (.const v.toInt),[],st.lengths.size⟩ := by
  simp only [evalBuild,registerCode_broadcast st n v hn,runCode,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem glConsts_sound (st : Build) (env : Nat → Word) (n : Nat) (hn : 0 < n) :
    let out := (glConsts n).run st
    ConstsAt out.2 env out.1 := by
  let r1 := (broadcast n (BitVec.ofNat 64 goldilocksP)).run st
  let r2 := (broadcast n 0xFFFFFFFF#64).run r1.2
  let r3 := (broadcast n 32#64).run r2.2
  change ConstsAt r3.2 env ⟨r1.1,r2.1,r3.1⟩
  constructor
  · simp [r3,r2,r1,broadcast_run] <;> omega
  · simp [r3,r2,r1,broadcast_run] <;> omega
  · simp [r3,r2,r1,broadcast_run] <;> omega
  all_goals
    simp only [r3,evalBuild_broadcast _ _ _ _ hn,r2,r1]
    simp only [broadcast_run,Array.size_push]
    simp [stepInstr,evalElemOp,evalHypergraphOpBv,Nat.add_assoc]

/-- Constants do not overwrite any preceding register in the actual code. -/
theorem glConsts_frame (st : Build) (env : Nat → Word) (n : Nat) (hn : 0 < n)
    (a : Nat) (ha : a < st.lengths.size) :
    evalBuild ((glConsts n).run st).2 env a = evalBuild st env a := by
  let r1 := (broadcast n (BitVec.ofNat 64 goldilocksP)).run st
  let r2 := (broadcast n 0xFFFFFFFF#64).run r1.2
  let r3 := (broadcast n 32#64).run r2.2
  change evalBuild r3.2 env a = _
  simp only [r3,evalBuild_broadcast _ _ _ _ hn,r2,r1]
  simp only [broadcast_run,Array.size_push]
  simp [stepInstr,show a ≠ st.lengths.size by omega,old_ne_fresh st a ha,Nat.add_assoc]

/-- Representation view only; no arithmetic is executed by this proof adapter. -/
def limbs (x : Word) : Limbs.Word := Limbs.ofNat x.toNat

theorem limbs_val (x : Word) : (limbs x).val = x.toNat := by
  rw [limbs,Limbs.ofNat_val]
  exact Nat.mod_eq_of_lt x.isLt

theorem limbs_bits (x : Word) : (limbs x).bits = x := by
  apply BitVec.eq_of_toNat_eq
  rw [Limbs.Word.bits_val,limbs_val]

theorem prime_bits : Limbs.Goldilocks.prime.bits = BitVec.ofNat 64 goldilocksP := by
  apply BitVec.eq_of_toNat_eq
  rw [Limbs.Word.bits_val,Limbs.Goldilocks.prime_val]
  rfl

theorem canon_bits (a : Limbs.Word) : (Limbs.Goldilocks.canon a).bits =
    if a.bits.ult (BitVec.ofNat 64 goldilocksP) then a.bits else a.bits-BitVec.ofNat 64 goldilocksP := by
  unfold Limbs.Goldilocks.canon
  rw [Limbs.lt_bits,prime_bits]
  split <;> simp [Limbs.sub_bits,prime_bits]

theorem addCanonical_bits (a b : Limbs.Word) : (Limbs.Goldilocks.addCanonical a b).bits =
    if a.bits.ult (BitVec.ofNat 64 goldilocksP-b.bits) then a.bits+b.bits
    else a.bits-(BitVec.ofNat 64 goldilocksP-b.bits) := by
  unfold Limbs.Goldilocks.addCanonical
  simp only [Limbs.lt_bits,Limbs.sub_bits,prime_bits]
  split <;> simp [Limbs.add_bits,Limbs.sub_bits,prime_bits]

theorem subCanonical_bits (a b : Limbs.Word) : (Limbs.Goldilocks.subCanonical a b).bits =
    if a.bits.ult b.bits then (BitVec.ofNat 64 goldilocksP-b.bits)+a.bits else a.bits-b.bits := by
  unfold Limbs.Goldilocks.subCanonical
  rw [Limbs.lt_bits]
  split <;> simp [Limbs.add_bits,Limbs.sub_bits,prime_bits]

theorem glCanon_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a : Nat)
    (ha : a < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glCanon n k a).run st
    evalBuild out.2 env out.1 = (Limbs.Goldilocks.canon (limbs (evalBuild st env a))).bits := by
  dsimp only
  rw [glCanon_run st env n k a ha hk.p_lt,canon_bits,limbs_bits,hk.p_value]

theorem glAdd_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glAdd n k a b).run st
    evalBuild out.2 env out.1 =
      (Limbs.Goldilocks.addCanonical (limbs (evalBuild st env a)) (limbs (evalBuild st env b))).bits := by
  dsimp only
  rw [glAdd_run st env n k a b ha hb hk.p_lt,addCanonical_bits,limbs_bits,limbs_bits,hk.p_value]

theorem glSub_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glSub n k a b).run st
    evalBuild out.2 env out.1 =
      (Limbs.Goldilocks.subCanonical (limbs (evalBuild st env a)) (limbs (evalBuild st env b))).bits := by
  dsimp only
  rw [glSub_run st env n k a b ha hb hk.p_lt,subCanonical_bits,limbs_bits,limbs_bits,hk.p_value]

/-- Canonicalization accepts every input word and returns its field residue. -/
theorem glCanon_sound (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a : Nat)
    (ha : a < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glCanon n k a).run st
    (evalBuild out.2 env out.1).toNat < goldilocksPrime ∧
      (evalBuild out.2 env out.1).toNat = (evalBuild st env a).toNat % goldilocksPrime := by
  dsimp only
  rw [glCanon_limbs st env n k a ha hk,Limbs.Word.bits_val,Limbs.Goldilocks.canon_val,limbs_val]
  exact goldilocksCanon64_spec (evalBuild st env a).isLt

/-- Canonical addition assumptions are explicit; the returned word is canonical. -/
theorem glAdd_sound (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k)
    (hca : (evalBuild st env a).toNat < goldilocksPrime)
    (hcb : (evalBuild st env b).toNat < goldilocksPrime) :
    let out := (glAdd n k a b).run st
    (evalBuild out.2 env out.1).toNat < goldilocksPrime ∧
      (evalBuild out.2 env out.1).toNat =
        ((evalBuild st env a).toNat+(evalBuild st env b).toNat) % goldilocksPrime := by
  dsimp only
  rw [glAdd_limbs st env n k a b ha hb hk,Limbs.Word.bits_val]
  have hla : (limbs (evalBuild st env a)).val < goldilocksPrime := by simpa [limbs_val] using hca
  have hlb : (limbs (evalBuild st env b)).val < goldilocksPrime := by simpa [limbs_val] using hcb
  have he := Limbs.Goldilocks.add_val (limbs (evalBuild st env a)) (limbs (evalBuild st env b))
  simp only [Limbs.Goldilocks.add,Limbs.Goldilocks.canon_eq hla,Limbs.Goldilocks.canon_eq hlb,limbs_val] at he
  rw [he]
  exact goldilocksAddSpec_spec (evalBuild st env a).isLt (evalBuild st env b).isLt

/-- Canonical subtraction returns the canonical field difference. -/
theorem glSub_sound (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k)
    (hca : (evalBuild st env a).toNat < goldilocksPrime)
    (hcb : (evalBuild st env b).toNat < goldilocksPrime) :
    let out := (glSub n k a b).run st
    (evalBuild out.2 env out.1).toNat < goldilocksPrime ∧
      (evalBuild out.2 env out.1).toNat =
        ((evalBuild st env a).toNat+goldilocksPrime-(evalBuild st env b).toNat) % goldilocksPrime := by
  dsimp only
  rw [glSub_limbs st env n k a b ha hb hk,Limbs.Word.bits_val]
  have hla : (limbs (evalBuild st env a)).val < goldilocksPrime := by simpa [limbs_val] using hca
  have hlb : (limbs (evalBuild st env b)).val < goldilocksPrime := by simpa [limbs_val] using hcb
  have he := Limbs.Goldilocks.sub_val (limbs (evalBuild st env a)) (limbs (evalBuild st env b))
  simp only [Limbs.Goldilocks.sub,Limbs.Goldilocks.canon_eq hla,Limbs.Goldilocks.canon_eq hlb,limbs_val] at he
  rw [he]
  have h := goldilocksSubSpec_spec (evalBuild st env a).isLt (evalBuild st env b).isLt
  have hcanA : goldilocksCanon64 (evalBuild st env a).toNat = (evalBuild st env a).toNat := by
    unfold goldilocksCanon64; split <;> omega
  have hcanB : goldilocksCanon64 (evalBuild st env b).toNat = (evalBuild st env b).toNat := by
    unfold goldilocksCanon64; split <;> omega
  simpa only [hcanA,hcanB] using h

/-- A real code extension preserves every previously allocated register. -/
structure BuildExtends (before after : Build) : Prop where
  size_le : before.lengths.size ≤ after.lengths.size
  frame : ∀ env w, w < before.lengths.size → evalBuild after env w = evalBuild before env w
  future_frame : ∀ env w, after.lengths.size ≤ w → evalBuild after env w = evalBuild before env w

theorem BuildExtends.trans {a b c : Build} (hab : BuildExtends a b) (hbc : BuildExtends b c) :
    BuildExtends a c := by
  refine ⟨Nat.le_trans hab.size_le hbc.size_le,?_,?_⟩
  · intro env w hw
    exact (hbc.frame env w (Nat.lt_of_lt_of_le hw hab.size_le)).trans (hab.frame env w hw)
  · intro env w hw
    exact (hbc.future_frame env w hw).trans
      (hab.future_frame env w (Nat.le_trans hbc.size_le hw))

theorem mapN_extends (st : Build) (n : Nat) (op : ElemOp) (args : List Nat) :
    BuildExtends st ((mapN n op args).run st).2 := by
  constructor
  · simp [mapN_run]
  · intro env w hw
    exact evalBuild_mapN_frame st env n op args w hw
  · intro env w hw
    rw [mapN_run] at hw
    simp only [Array.size_push] at hw
    rw [evalBuild_mapN]
    simp [stepInstr,show w ≠ st.lengths.size by omega]

theorem ConstsAt.mono {st after : Build} {env : Nat → Word} {k : GlConsts}
    (hk : ConstsAt st env k) (he : BuildExtends st after) : ConstsAt after env k := by
  exact ⟨Nat.lt_of_lt_of_le hk.p_lt he.size_le,Nat.lt_of_lt_of_le hk.mask_lt he.size_le,
    Nat.lt_of_lt_of_le hk.s32_lt he.size_le,(he.frame env k.p hk.p_lt).trans hk.p_value,
    (he.frame env k.mask hk.mask_lt).trans hk.mask_value,(he.frame env k.s32 hk.s32_lt).trans hk.s32_value⟩

theorem glCanon_extends (st : Build) (n : Nat) (k : GlConsts) (a : Nat) :
    BuildExtends st ((glCanon n k a).run st).2 := by
  let r1 := (mapN n .ult [a,k.p]).run st
  let r2 := (mapN n (.scalar .sub) [a,k.p]).run r1.2
  let r3 := (mapN n (.scalar .mux) [r1.1,a,r2.1]).run r2.2
  change BuildExtends st r3.2
  have he1 : BuildExtends st r1.2 := mapN_extends st n .ult [a,k.p]
  have he2 : BuildExtends r1.2 r2.2 := mapN_extends r1.2 n (.scalar .sub) [a,k.p]
  have he3 : BuildExtends r2.2 r3.2 := mapN_extends r2.2 n (.scalar .mux) [r1.1,a,r2.1]
  exact ((he1.trans he2).trans he3)

theorem glAdd_extends (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    BuildExtends st ((glAdd n k a b).run st).2 := by
  let r1 := (mapN n (.scalar .sub) [k.p,b]).run st
  let r2 := (mapN n .ult [a,r1.1]).run r1.2
  let r3 := (mapN n (.scalar .add) [a,b]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,r1.1]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r2.1,r3.1,r4.1]).run r4.2
  change BuildExtends st r5.2
  have he1 : BuildExtends st r1.2 := mapN_extends st n (.scalar .sub) [k.p,b]
  have he2 : BuildExtends r1.2 r2.2 := mapN_extends r1.2 n .ult [a,r1.1]
  have he3 : BuildExtends r2.2 r3.2 := mapN_extends r2.2 n (.scalar .add) [a,b]
  have he4 : BuildExtends r3.2 r4.2 := mapN_extends r3.2 n (.scalar .sub) [a,r1.1]
  have he5 : BuildExtends r4.2 r5.2 := mapN_extends r4.2 n (.scalar .mux) [r2.1,r3.1,r4.1]
  exact ((((he1.trans he2).trans he3).trans he4).trans he5)

theorem glSub_extends (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    BuildExtends st ((glSub n k a b).run st).2 := by
  let r1 := (mapN n .ult [a,b]).run st
  let r2 := (mapN n (.scalar .sub) [k.p,b]).run r1.2
  let r3 := (mapN n (.scalar .add) [r2.1,a]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,b]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r1.1,r3.1,r4.1]).run r4.2
  change BuildExtends st r5.2
  have he1 : BuildExtends st r1.2 := mapN_extends st n .ult [a,b]
  have he2 : BuildExtends r1.2 r2.2 := mapN_extends r1.2 n (.scalar .sub) [k.p,b]
  have he3 : BuildExtends r2.2 r3.2 := mapN_extends r2.2 n (.scalar .add) [r2.1,a]
  have he4 : BuildExtends r3.2 r4.2 := mapN_extends r3.2 n (.scalar .sub) [a,b]
  have he5 : BuildExtends r4.2 r5.2 := mapN_extends r4.2 n (.scalar .mux) [r1.1,r3.1,r4.1]
  exact ((((he1.trans he2).trans he3).trans he4).trans he5)

theorem glMulWide_extends (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    BuildExtends st ((glMulWide n k a b).run st).2 := by
  obtain ⟨r1,hr1⟩ : ∃ r : Nat × Build, (mapN n .band [a,k.mask]).run st = r := ⟨_,rfl⟩
  obtain ⟨r2,hr2⟩ : ∃ r : Nat × Build, (mapN n .shr [a,k.s32]).run r1.2 = r := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r : Nat × Build, (mapN n .band [b,k.mask]).run r2.2 = r := ⟨_,rfl⟩
  obtain ⟨r4,hr4⟩ : ∃ r : Nat × Build, (mapN n .shr [b,k.s32]).run r3.2 = r := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r3.1]).run r4.2 = r := ⟨_,rfl⟩
  obtain ⟨r6,hr6⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r4.1]).run r5.2 = r := ⟨_,rfl⟩
  obtain ⟨r7,hr7⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r3.1]).run r6.2 = r := ⟨_,rfl⟩
  obtain ⟨r8,hr8⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r4.1]).run r7.2 = r := ⟨_,rfl⟩
  obtain ⟨r9,hr9⟩ : ∃ r : Nat × Build, (mapN n .shr [r5.1,k.s32]).run r8.2 = r := ⟨_,rfl⟩
  obtain ⟨r10,hr10⟩ : ∃ r : Nat × Build, (mapN n .band [r6.1,k.mask]).run r9.2 = r := ⟨_,rfl⟩
  obtain ⟨r11,hr11⟩ : ∃ r : Nat × Build, (mapN n .band [r7.1,k.mask]).run r10.2 = r := ⟨_,rfl⟩
  obtain ⟨r12,hr12⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r9.1,r10.1]).run r11.2 = r := ⟨_,rfl⟩
  obtain ⟨r13,hr13⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r12.1,r11.1]).run r12.2 = r := ⟨_,rfl⟩
  obtain ⟨r14,hr14⟩ : ∃ r : Nat × Build, (mapN n .band [r5.1,k.mask]).run r13.2 = r := ⟨_,rfl⟩
  obtain ⟨r15,hr15⟩ : ∃ r : Nat × Build, (mapN n .band [r13.1,k.mask]).run r14.2 = r := ⟨_,rfl⟩
  obtain ⟨r16,hr16⟩ : ∃ r : Nat × Build, (mapN n .shl [r15.1,k.s32]).run r15.2 = r := ⟨_,rfl⟩
  obtain ⟨r17,hr17⟩ : ∃ r : Nat × Build, (mapN n .bor [r14.1,r16.1]).run r16.2 = r := ⟨_,rfl⟩
  obtain ⟨r18,hr18⟩ : ∃ r : Nat × Build, (mapN n .shr [r6.1,k.s32]).run r17.2 = r := ⟨_,rfl⟩
  obtain ⟨r19,hr19⟩ : ∃ r : Nat × Build, (mapN n .shr [r7.1,k.s32]).run r18.2 = r := ⟨_,rfl⟩
  obtain ⟨r20,hr20⟩ : ∃ r : Nat × Build, (mapN n .shr [r13.1,k.s32]).run r19.2 = r := ⟨_,rfl⟩
  obtain ⟨r21,hr21⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r8.1,r18.1]).run r20.2 = r := ⟨_,rfl⟩
  obtain ⟨r22,hr22⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r21.1,r19.1]).run r21.2 = r := ⟨_,rfl⟩
  obtain ⟨r23,hr23⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r22.1,r20.1]).run r22.2 = r := ⟨_,rfl⟩
  simp only [glMulWide,map2,map3,bind_run,pure_run,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17,hr18,hr19,hr20,hr21,hr22,hr23]
  change BuildExtends st r23.2
  have he1 : BuildExtends st r1.2 := by
    rw [← hr1]; exact mapN_extends st n .band [a,k.mask]
  have he2 : BuildExtends r1.2 r2.2 := by
    rw [← hr2]; exact mapN_extends r1.2 n .shr [a,k.s32]
  have he3 : BuildExtends r2.2 r3.2 := by
    rw [← hr3]; exact mapN_extends r2.2 n .band [b,k.mask]
  have he4 : BuildExtends r3.2 r4.2 := by
    rw [← hr4]; exact mapN_extends r3.2 n .shr [b,k.s32]
  have he5 : BuildExtends r4.2 r5.2 := by
    rw [← hr5]; exact mapN_extends r4.2 n (.scalar .mul) [r1.1,r3.1]
  have he6 : BuildExtends r5.2 r6.2 := by
    rw [← hr6]; exact mapN_extends r5.2 n (.scalar .mul) [r1.1,r4.1]
  have he7 : BuildExtends r6.2 r7.2 := by
    rw [← hr7]; exact mapN_extends r6.2 n (.scalar .mul) [r2.1,r3.1]
  have he8 : BuildExtends r7.2 r8.2 := by
    rw [← hr8]; exact mapN_extends r7.2 n (.scalar .mul) [r2.1,r4.1]
  have he9 : BuildExtends r8.2 r9.2 := by
    rw [← hr9]; exact mapN_extends r8.2 n .shr [r5.1,k.s32]
  have he10 : BuildExtends r9.2 r10.2 := by
    rw [← hr10]; exact mapN_extends r9.2 n .band [r6.1,k.mask]
  have he11 : BuildExtends r10.2 r11.2 := by
    rw [← hr11]; exact mapN_extends r10.2 n .band [r7.1,k.mask]
  have he12 : BuildExtends r11.2 r12.2 := by
    rw [← hr12]; exact mapN_extends r11.2 n (.scalar .add) [r9.1,r10.1]
  have he13 : BuildExtends r12.2 r13.2 := by
    rw [← hr13]; exact mapN_extends r12.2 n (.scalar .add) [r12.1,r11.1]
  have he14 : BuildExtends r13.2 r14.2 := by
    rw [← hr14]; exact mapN_extends r13.2 n .band [r5.1,k.mask]
  have he15 : BuildExtends r14.2 r15.2 := by
    rw [← hr15]; exact mapN_extends r14.2 n .band [r13.1,k.mask]
  have he16 : BuildExtends r15.2 r16.2 := by
    rw [← hr16]; exact mapN_extends r15.2 n .shl [r15.1,k.s32]
  have he17 : BuildExtends r16.2 r17.2 := by
    rw [← hr17]; exact mapN_extends r16.2 n .bor [r14.1,r16.1]
  have he18 : BuildExtends r17.2 r18.2 := by
    rw [← hr18]; exact mapN_extends r17.2 n .shr [r6.1,k.s32]
  have he19 : BuildExtends r18.2 r19.2 := by
    rw [← hr19]; exact mapN_extends r18.2 n .shr [r7.1,k.s32]
  have he20 : BuildExtends r19.2 r20.2 := by
    rw [← hr20]; exact mapN_extends r19.2 n .shr [r13.1,k.s32]
  have he21 : BuildExtends r20.2 r21.2 := by
    rw [← hr21]; exact mapN_extends r20.2 n (.scalar .add) [r8.1,r18.1]
  have he22 : BuildExtends r21.2 r22.2 := by
    rw [← hr22]; exact mapN_extends r21.2 n (.scalar .add) [r21.1,r19.1]
  have he23 : BuildExtends r22.2 r23.2 := by
    rw [← hr23]; exact mapN_extends r22.2 n (.scalar .add) [r22.1,r20.1]
  exact ((((((((((((((((((((((he1.trans he2).trans he3).trans he4).trans he5).trans he6).trans he7).trans he8).trans he9).trans he10).trans he11).trans he12).trans he13).trans he14).trans he15).trans he16).trans he17).trans he18).trans he19).trans he20).trans he21).trans he22).trans he23)

theorem glCanon_coordinates (st : Build) (n : Nat) (k : GlConsts) (a : Nat) :
    ((glCanon n k a).run st).1 = st.lengths.size+2 ∧ ((glCanon n k a).run st).2.lengths.size = st.lengths.size+3 := by
  let r1 := (mapN n .ult [a,k.p]).run st
  let r2 := (mapN n (.scalar .sub) [a,k.p]).run r1.2
  let r3 := (mapN n (.scalar .mux) [r1.1,a,r2.1]).run r2.2
  change r3.1 = st.lengths.size+2 ∧ r3.2.lengths.size = st.lengths.size+3
  simp [r3,r2,r1,mapN_run,Nat.add_assoc]

theorem glAdd_coordinates (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    ((glAdd n k a b).run st).1 = st.lengths.size+4 ∧ ((glAdd n k a b).run st).2.lengths.size = st.lengths.size+5 := by
  let r1 := (mapN n (.scalar .sub) [k.p,b]).run st
  let r2 := (mapN n .ult [a,r1.1]).run r1.2
  let r3 := (mapN n (.scalar .add) [a,b]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,r1.1]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r2.1,r3.1,r4.1]).run r4.2
  change r5.1 = st.lengths.size+4 ∧ r5.2.lengths.size = st.lengths.size+5
  simp [r5,r4,r3,r2,r1,mapN_run,Nat.add_assoc]

theorem glSub_coordinates (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    ((glSub n k a b).run st).1 = st.lengths.size+4 ∧ ((glSub n k a b).run st).2.lengths.size = st.lengths.size+5 := by
  let r1 := (mapN n .ult [a,b]).run st
  let r2 := (mapN n (.scalar .sub) [k.p,b]).run r1.2
  let r3 := (mapN n (.scalar .add) [r2.1,a]).run r2.2
  let r4 := (mapN n (.scalar .sub) [a,b]).run r3.2
  let r5 := (mapN n (.scalar .mux) [r1.1,r3.1,r4.1]).run r4.2
  change r5.1 = st.lengths.size+4 ∧ r5.2.lengths.size = st.lengths.size+5
  simp [r5,r4,r3,r2,r1,mapN_run,Nat.add_assoc]

theorem glMulWide_coordinates (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    ((glMulWide n k a b).run st).1.1 = st.lengths.size+16 ∧ ((glMulWide n k a b).run st).1.2 = st.lengths.size+22 ∧ ((glMulWide n k a b).run st).2.lengths.size = st.lengths.size+23 := by
  obtain ⟨r1,hr1⟩ : ∃ r : Nat × Build, (mapN n .band [a,k.mask]).run st = r := ⟨_,rfl⟩
  obtain ⟨r2,hr2⟩ : ∃ r : Nat × Build, (mapN n .shr [a,k.s32]).run r1.2 = r := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r : Nat × Build, (mapN n .band [b,k.mask]).run r2.2 = r := ⟨_,rfl⟩
  obtain ⟨r4,hr4⟩ : ∃ r : Nat × Build, (mapN n .shr [b,k.s32]).run r3.2 = r := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r3.1]).run r4.2 = r := ⟨_,rfl⟩
  obtain ⟨r6,hr6⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r4.1]).run r5.2 = r := ⟨_,rfl⟩
  obtain ⟨r7,hr7⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r3.1]).run r6.2 = r := ⟨_,rfl⟩
  obtain ⟨r8,hr8⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r4.1]).run r7.2 = r := ⟨_,rfl⟩
  obtain ⟨r9,hr9⟩ : ∃ r : Nat × Build, (mapN n .shr [r5.1,k.s32]).run r8.2 = r := ⟨_,rfl⟩
  obtain ⟨r10,hr10⟩ : ∃ r : Nat × Build, (mapN n .band [r6.1,k.mask]).run r9.2 = r := ⟨_,rfl⟩
  obtain ⟨r11,hr11⟩ : ∃ r : Nat × Build, (mapN n .band [r7.1,k.mask]).run r10.2 = r := ⟨_,rfl⟩
  obtain ⟨r12,hr12⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r9.1,r10.1]).run r11.2 = r := ⟨_,rfl⟩
  obtain ⟨r13,hr13⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r12.1,r11.1]).run r12.2 = r := ⟨_,rfl⟩
  obtain ⟨r14,hr14⟩ : ∃ r : Nat × Build, (mapN n .band [r5.1,k.mask]).run r13.2 = r := ⟨_,rfl⟩
  obtain ⟨r15,hr15⟩ : ∃ r : Nat × Build, (mapN n .band [r13.1,k.mask]).run r14.2 = r := ⟨_,rfl⟩
  obtain ⟨r16,hr16⟩ : ∃ r : Nat × Build, (mapN n .shl [r15.1,k.s32]).run r15.2 = r := ⟨_,rfl⟩
  obtain ⟨r17,hr17⟩ : ∃ r : Nat × Build, (mapN n .bor [r14.1,r16.1]).run r16.2 = r := ⟨_,rfl⟩
  obtain ⟨r18,hr18⟩ : ∃ r : Nat × Build, (mapN n .shr [r6.1,k.s32]).run r17.2 = r := ⟨_,rfl⟩
  obtain ⟨r19,hr19⟩ : ∃ r : Nat × Build, (mapN n .shr [r7.1,k.s32]).run r18.2 = r := ⟨_,rfl⟩
  obtain ⟨r20,hr20⟩ : ∃ r : Nat × Build, (mapN n .shr [r13.1,k.s32]).run r19.2 = r := ⟨_,rfl⟩
  obtain ⟨r21,hr21⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r8.1,r18.1]).run r20.2 = r := ⟨_,rfl⟩
  obtain ⟨r22,hr22⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r21.1,r19.1]).run r21.2 = r := ⟨_,rfl⟩
  obtain ⟨r23,hr23⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r22.1,r20.1]).run r22.2 = r := ⟨_,rfl⟩
  simp only [glMulWide,map2,map3,bind_run,pure_run,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17,hr18,hr19,hr20,hr21,hr22,hr23]
  change r17.1 = st.lengths.size+16 ∧ r23.1 = st.lengths.size+22 ∧ r23.2.lengths.size = st.lengths.size+23
  have hc1 : r1.1 = st.lengths.size ∧ r1.2.lengths.size = st.lengths.size+1 := by
    rw [← hr1,mapN_run]; simp
  have hc2 : r2.1 = r1.2.lengths.size ∧ r2.2.lengths.size = r1.2.lengths.size+1 := by
    rw [← hr2,mapN_run]; simp
  have hc3 : r3.1 = r2.2.lengths.size ∧ r3.2.lengths.size = r2.2.lengths.size+1 := by
    rw [← hr3,mapN_run]; simp
  have hc4 : r4.1 = r3.2.lengths.size ∧ r4.2.lengths.size = r3.2.lengths.size+1 := by
    rw [← hr4,mapN_run]; simp
  have hc5 : r5.1 = r4.2.lengths.size ∧ r5.2.lengths.size = r4.2.lengths.size+1 := by
    rw [← hr5,mapN_run]; simp
  have hc6 : r6.1 = r5.2.lengths.size ∧ r6.2.lengths.size = r5.2.lengths.size+1 := by
    rw [← hr6,mapN_run]; simp
  have hc7 : r7.1 = r6.2.lengths.size ∧ r7.2.lengths.size = r6.2.lengths.size+1 := by
    rw [← hr7,mapN_run]; simp
  have hc8 : r8.1 = r7.2.lengths.size ∧ r8.2.lengths.size = r7.2.lengths.size+1 := by
    rw [← hr8,mapN_run]; simp
  have hc9 : r9.1 = r8.2.lengths.size ∧ r9.2.lengths.size = r8.2.lengths.size+1 := by
    rw [← hr9,mapN_run]; simp
  have hc10 : r10.1 = r9.2.lengths.size ∧ r10.2.lengths.size = r9.2.lengths.size+1 := by
    rw [← hr10,mapN_run]; simp
  have hc11 : r11.1 = r10.2.lengths.size ∧ r11.2.lengths.size = r10.2.lengths.size+1 := by
    rw [← hr11,mapN_run]; simp
  have hc12 : r12.1 = r11.2.lengths.size ∧ r12.2.lengths.size = r11.2.lengths.size+1 := by
    rw [← hr12,mapN_run]; simp
  have hc13 : r13.1 = r12.2.lengths.size ∧ r13.2.lengths.size = r12.2.lengths.size+1 := by
    rw [← hr13,mapN_run]; simp
  have hc14 : r14.1 = r13.2.lengths.size ∧ r14.2.lengths.size = r13.2.lengths.size+1 := by
    rw [← hr14,mapN_run]; simp
  have hc15 : r15.1 = r14.2.lengths.size ∧ r15.2.lengths.size = r14.2.lengths.size+1 := by
    rw [← hr15,mapN_run]; simp
  have hc16 : r16.1 = r15.2.lengths.size ∧ r16.2.lengths.size = r15.2.lengths.size+1 := by
    rw [← hr16,mapN_run]; simp
  have hc17 : r17.1 = r16.2.lengths.size ∧ r17.2.lengths.size = r16.2.lengths.size+1 := by
    rw [← hr17,mapN_run]; simp
  have hc18 : r18.1 = r17.2.lengths.size ∧ r18.2.lengths.size = r17.2.lengths.size+1 := by
    rw [← hr18,mapN_run]; simp
  have hc19 : r19.1 = r18.2.lengths.size ∧ r19.2.lengths.size = r18.2.lengths.size+1 := by
    rw [← hr19,mapN_run]; simp
  have hc20 : r20.1 = r19.2.lengths.size ∧ r20.2.lengths.size = r19.2.lengths.size+1 := by
    rw [← hr20,mapN_run]; simp
  have hc21 : r21.1 = r20.2.lengths.size ∧ r21.2.lengths.size = r20.2.lengths.size+1 := by
    rw [← hr21,mapN_run]; simp
  have hc22 : r22.1 = r21.2.lengths.size ∧ r22.2.lengths.size = r21.2.lengths.size+1 := by
    rw [← hr22,mapN_run]; simp
  have hc23 : r23.1 = r22.2.lengths.size ∧ r23.2.lengths.size = r22.2.lengths.size+1 := by
    rw [← hr23,mapN_run]; simp
  omega

/-- The actual 23 emitted maps compute the existing proved wide limb network. -/
theorem glMulWide_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glMulWide n k a b).run st
    let wide := Limbs.mulNetwork (limbs (evalBuild st env a)) (limbs (evalBuild st env b))
    evalBuild out.2 env out.1.1 = wide.lo.bits ∧
      evalBuild out.2 env out.1.2 = wide.hi.bits := by
  obtain ⟨r1,hr1⟩ : ∃ r : Nat × Build, (mapN n .band [a,k.mask]).run st = r := ⟨_,rfl⟩
  obtain ⟨r2,hr2⟩ : ∃ r : Nat × Build, (mapN n .shr [a,k.s32]).run r1.2 = r := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r : Nat × Build, (mapN n .band [b,k.mask]).run r2.2 = r := ⟨_,rfl⟩
  obtain ⟨r4,hr4⟩ : ∃ r : Nat × Build, (mapN n .shr [b,k.s32]).run r3.2 = r := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r3.1]).run r4.2 = r := ⟨_,rfl⟩
  obtain ⟨r6,hr6⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r1.1,r4.1]).run r5.2 = r := ⟨_,rfl⟩
  obtain ⟨r7,hr7⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r3.1]).run r6.2 = r := ⟨_,rfl⟩
  obtain ⟨r8,hr8⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mul) [r2.1,r4.1]).run r7.2 = r := ⟨_,rfl⟩
  obtain ⟨r9,hr9⟩ : ∃ r : Nat × Build, (mapN n .shr [r5.1,k.s32]).run r8.2 = r := ⟨_,rfl⟩
  obtain ⟨r10,hr10⟩ : ∃ r : Nat × Build, (mapN n .band [r6.1,k.mask]).run r9.2 = r := ⟨_,rfl⟩
  obtain ⟨r11,hr11⟩ : ∃ r : Nat × Build, (mapN n .band [r7.1,k.mask]).run r10.2 = r := ⟨_,rfl⟩
  obtain ⟨r12,hr12⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r9.1,r10.1]).run r11.2 = r := ⟨_,rfl⟩
  obtain ⟨r13,hr13⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r12.1,r11.1]).run r12.2 = r := ⟨_,rfl⟩
  obtain ⟨r14,hr14⟩ : ∃ r : Nat × Build, (mapN n .band [r5.1,k.mask]).run r13.2 = r := ⟨_,rfl⟩
  obtain ⟨r15,hr15⟩ : ∃ r : Nat × Build, (mapN n .band [r13.1,k.mask]).run r14.2 = r := ⟨_,rfl⟩
  obtain ⟨r16,hr16⟩ : ∃ r : Nat × Build, (mapN n .shl [r15.1,k.s32]).run r15.2 = r := ⟨_,rfl⟩
  obtain ⟨r17,hr17⟩ : ∃ r : Nat × Build, (mapN n .bor [r14.1,r16.1]).run r16.2 = r := ⟨_,rfl⟩
  obtain ⟨r18,hr18⟩ : ∃ r : Nat × Build, (mapN n .shr [r6.1,k.s32]).run r17.2 = r := ⟨_,rfl⟩
  obtain ⟨r19,hr19⟩ : ∃ r : Nat × Build, (mapN n .shr [r7.1,k.s32]).run r18.2 = r := ⟨_,rfl⟩
  obtain ⟨r20,hr20⟩ : ∃ r : Nat × Build, (mapN n .shr [r13.1,k.s32]).run r19.2 = r := ⟨_,rfl⟩
  obtain ⟨r21,hr21⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r8.1,r18.1]).run r20.2 = r := ⟨_,rfl⟩
  obtain ⟨r22,hr22⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r21.1,r19.1]).run r21.2 = r := ⟨_,rfl⟩
  obtain ⟨r23,hr23⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r22.1,r20.1]).run r22.2 = r := ⟨_,rfl⟩
  simp only [glMulWide,map2,map3,bind_run,pure_run,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17,hr18,hr19,hr20,hr21,hr22,hr23]
  change evalBuild r23.2 env r17.1 = _ ∧ evalBuild r23.2 env r23.1 = _
  have hc1 : r1.1 = st.lengths.size ∧ r1.2.lengths.size = st.lengths.size+1 := by
    rw [← hr1,mapN_run]; simp
  have hc2 : r2.1 = r1.2.lengths.size ∧ r2.2.lengths.size = r1.2.lengths.size+1 := by
    rw [← hr2,mapN_run]; simp
  have hc3 : r3.1 = r2.2.lengths.size ∧ r3.2.lengths.size = r2.2.lengths.size+1 := by
    rw [← hr3,mapN_run]; simp
  have hc4 : r4.1 = r3.2.lengths.size ∧ r4.2.lengths.size = r3.2.lengths.size+1 := by
    rw [← hr4,mapN_run]; simp
  have hc5 : r5.1 = r4.2.lengths.size ∧ r5.2.lengths.size = r4.2.lengths.size+1 := by
    rw [← hr5,mapN_run]; simp
  have hc6 : r6.1 = r5.2.lengths.size ∧ r6.2.lengths.size = r5.2.lengths.size+1 := by
    rw [← hr6,mapN_run]; simp
  have hc7 : r7.1 = r6.2.lengths.size ∧ r7.2.lengths.size = r6.2.lengths.size+1 := by
    rw [← hr7,mapN_run]; simp
  have hc8 : r8.1 = r7.2.lengths.size ∧ r8.2.lengths.size = r7.2.lengths.size+1 := by
    rw [← hr8,mapN_run]; simp
  have hc9 : r9.1 = r8.2.lengths.size ∧ r9.2.lengths.size = r8.2.lengths.size+1 := by
    rw [← hr9,mapN_run]; simp
  have hc10 : r10.1 = r9.2.lengths.size ∧ r10.2.lengths.size = r9.2.lengths.size+1 := by
    rw [← hr10,mapN_run]; simp
  have hc11 : r11.1 = r10.2.lengths.size ∧ r11.2.lengths.size = r10.2.lengths.size+1 := by
    rw [← hr11,mapN_run]; simp
  have hc12 : r12.1 = r11.2.lengths.size ∧ r12.2.lengths.size = r11.2.lengths.size+1 := by
    rw [← hr12,mapN_run]; simp
  have hc13 : r13.1 = r12.2.lengths.size ∧ r13.2.lengths.size = r12.2.lengths.size+1 := by
    rw [← hr13,mapN_run]; simp
  have hc14 : r14.1 = r13.2.lengths.size ∧ r14.2.lengths.size = r13.2.lengths.size+1 := by
    rw [← hr14,mapN_run]; simp
  have hc15 : r15.1 = r14.2.lengths.size ∧ r15.2.lengths.size = r14.2.lengths.size+1 := by
    rw [← hr15,mapN_run]; simp
  have hc16 : r16.1 = r15.2.lengths.size ∧ r16.2.lengths.size = r15.2.lengths.size+1 := by
    rw [← hr16,mapN_run]; simp
  have hc17 : r17.1 = r16.2.lengths.size ∧ r17.2.lengths.size = r16.2.lengths.size+1 := by
    rw [← hr17,mapN_run]; simp
  have hc18 : r18.1 = r17.2.lengths.size ∧ r18.2.lengths.size = r17.2.lengths.size+1 := by
    rw [← hr18,mapN_run]; simp
  have hc19 : r19.1 = r18.2.lengths.size ∧ r19.2.lengths.size = r18.2.lengths.size+1 := by
    rw [← hr19,mapN_run]; simp
  have hc20 : r20.1 = r19.2.lengths.size ∧ r20.2.lengths.size = r19.2.lengths.size+1 := by
    rw [← hr20,mapN_run]; simp
  have hc21 : r21.1 = r20.2.lengths.size ∧ r21.2.lengths.size = r20.2.lengths.size+1 := by
    rw [← hr21,mapN_run]; simp
  have hc22 : r22.1 = r21.2.lengths.size ∧ r22.2.lengths.size = r21.2.lengths.size+1 := by
    rw [← hr22,mapN_run]; simp
  have hc23 : r23.1 = r22.2.lengths.size ∧ r23.2.lengths.size = r22.2.lengths.size+1 := by
    rw [← hr23,mapN_run]; simp
  have hv1 (w : Nat) : evalBuild r1.2 env w =
      if w == st.lengths.size then evalElemOp .band ([a,k.mask].map (evalBuild st env))
      else evalBuild st env w := by
    have h := evalBuild_mapN st n .band [a,k.mask] env
    rw [hr1] at h
    exact congrFun h w
  have hv2 (w : Nat) : evalBuild r2.2 env w =
      if w == r1.2.lengths.size then evalElemOp .shr ([a,k.s32].map (evalBuild r1.2 env))
      else evalBuild r1.2 env w := by
    have h := evalBuild_mapN r1.2 n .shr [a,k.s32] env
    rw [hr2] at h
    exact congrFun h w
  have hv3 (w : Nat) : evalBuild r3.2 env w =
      if w == r2.2.lengths.size then evalElemOp .band ([b,k.mask].map (evalBuild r2.2 env))
      else evalBuild r2.2 env w := by
    have h := evalBuild_mapN r2.2 n .band [b,k.mask] env
    rw [hr3] at h
    exact congrFun h w
  have hv4 (w : Nat) : evalBuild r4.2 env w =
      if w == r3.2.lengths.size then evalElemOp .shr ([b,k.s32].map (evalBuild r3.2 env))
      else evalBuild r3.2 env w := by
    have h := evalBuild_mapN r3.2 n .shr [b,k.s32] env
    rw [hr4] at h
    exact congrFun h w
  have hv5 (w : Nat) : evalBuild r5.2 env w =
      if w == r4.2.lengths.size then evalElemOp (.scalar .mul) ([r1.1,r3.1].map (evalBuild r4.2 env))
      else evalBuild r4.2 env w := by
    have h := evalBuild_mapN r4.2 n (.scalar .mul) [r1.1,r3.1] env
    rw [hr5] at h
    exact congrFun h w
  have hv6 (w : Nat) : evalBuild r6.2 env w =
      if w == r5.2.lengths.size then evalElemOp (.scalar .mul) ([r1.1,r4.1].map (evalBuild r5.2 env))
      else evalBuild r5.2 env w := by
    have h := evalBuild_mapN r5.2 n (.scalar .mul) [r1.1,r4.1] env
    rw [hr6] at h
    exact congrFun h w
  have hv7 (w : Nat) : evalBuild r7.2 env w =
      if w == r6.2.lengths.size then evalElemOp (.scalar .mul) ([r2.1,r3.1].map (evalBuild r6.2 env))
      else evalBuild r6.2 env w := by
    have h := evalBuild_mapN r6.2 n (.scalar .mul) [r2.1,r3.1] env
    rw [hr7] at h
    exact congrFun h w
  have hv8 (w : Nat) : evalBuild r8.2 env w =
      if w == r7.2.lengths.size then evalElemOp (.scalar .mul) ([r2.1,r4.1].map (evalBuild r7.2 env))
      else evalBuild r7.2 env w := by
    have h := evalBuild_mapN r7.2 n (.scalar .mul) [r2.1,r4.1] env
    rw [hr8] at h
    exact congrFun h w
  have hv9 (w : Nat) : evalBuild r9.2 env w =
      if w == r8.2.lengths.size then evalElemOp .shr ([r5.1,k.s32].map (evalBuild r8.2 env))
      else evalBuild r8.2 env w := by
    have h := evalBuild_mapN r8.2 n .shr [r5.1,k.s32] env
    rw [hr9] at h
    exact congrFun h w
  have hv10 (w : Nat) : evalBuild r10.2 env w =
      if w == r9.2.lengths.size then evalElemOp .band ([r6.1,k.mask].map (evalBuild r9.2 env))
      else evalBuild r9.2 env w := by
    have h := evalBuild_mapN r9.2 n .band [r6.1,k.mask] env
    rw [hr10] at h
    exact congrFun h w
  have hv11 (w : Nat) : evalBuild r11.2 env w =
      if w == r10.2.lengths.size then evalElemOp .band ([r7.1,k.mask].map (evalBuild r10.2 env))
      else evalBuild r10.2 env w := by
    have h := evalBuild_mapN r10.2 n .band [r7.1,k.mask] env
    rw [hr11] at h
    exact congrFun h w
  have hv12 (w : Nat) : evalBuild r12.2 env w =
      if w == r11.2.lengths.size then evalElemOp (.scalar .add) ([r9.1,r10.1].map (evalBuild r11.2 env))
      else evalBuild r11.2 env w := by
    have h := evalBuild_mapN r11.2 n (.scalar .add) [r9.1,r10.1] env
    rw [hr12] at h
    exact congrFun h w
  have hv13 (w : Nat) : evalBuild r13.2 env w =
      if w == r12.2.lengths.size then evalElemOp (.scalar .add) ([r12.1,r11.1].map (evalBuild r12.2 env))
      else evalBuild r12.2 env w := by
    have h := evalBuild_mapN r12.2 n (.scalar .add) [r12.1,r11.1] env
    rw [hr13] at h
    exact congrFun h w
  have hv14 (w : Nat) : evalBuild r14.2 env w =
      if w == r13.2.lengths.size then evalElemOp .band ([r5.1,k.mask].map (evalBuild r13.2 env))
      else evalBuild r13.2 env w := by
    have h := evalBuild_mapN r13.2 n .band [r5.1,k.mask] env
    rw [hr14] at h
    exact congrFun h w
  have hv15 (w : Nat) : evalBuild r15.2 env w =
      if w == r14.2.lengths.size then evalElemOp .band ([r13.1,k.mask].map (evalBuild r14.2 env))
      else evalBuild r14.2 env w := by
    have h := evalBuild_mapN r14.2 n .band [r13.1,k.mask] env
    rw [hr15] at h
    exact congrFun h w
  have hv16 (w : Nat) : evalBuild r16.2 env w =
      if w == r15.2.lengths.size then evalElemOp .shl ([r15.1,k.s32].map (evalBuild r15.2 env))
      else evalBuild r15.2 env w := by
    have h := evalBuild_mapN r15.2 n .shl [r15.1,k.s32] env
    rw [hr16] at h
    exact congrFun h w
  have hv17 (w : Nat) : evalBuild r17.2 env w =
      if w == r16.2.lengths.size then evalElemOp .bor ([r14.1,r16.1].map (evalBuild r16.2 env))
      else evalBuild r16.2 env w := by
    have h := evalBuild_mapN r16.2 n .bor [r14.1,r16.1] env
    rw [hr17] at h
    exact congrFun h w
  have hv18 (w : Nat) : evalBuild r18.2 env w =
      if w == r17.2.lengths.size then evalElemOp .shr ([r6.1,k.s32].map (evalBuild r17.2 env))
      else evalBuild r17.2 env w := by
    have h := evalBuild_mapN r17.2 n .shr [r6.1,k.s32] env
    rw [hr18] at h
    exact congrFun h w
  have hv19 (w : Nat) : evalBuild r19.2 env w =
      if w == r18.2.lengths.size then evalElemOp .shr ([r7.1,k.s32].map (evalBuild r18.2 env))
      else evalBuild r18.2 env w := by
    have h := evalBuild_mapN r18.2 n .shr [r7.1,k.s32] env
    rw [hr19] at h
    exact congrFun h w
  have hv20 (w : Nat) : evalBuild r20.2 env w =
      if w == r19.2.lengths.size then evalElemOp .shr ([r13.1,k.s32].map (evalBuild r19.2 env))
      else evalBuild r19.2 env w := by
    have h := evalBuild_mapN r19.2 n .shr [r13.1,k.s32] env
    rw [hr20] at h
    exact congrFun h w
  have hv21 (w : Nat) : evalBuild r21.2 env w =
      if w == r20.2.lengths.size then evalElemOp (.scalar .add) ([r8.1,r18.1].map (evalBuild r20.2 env))
      else evalBuild r20.2 env w := by
    have h := evalBuild_mapN r20.2 n (.scalar .add) [r8.1,r18.1] env
    rw [hr21] at h
    exact congrFun h w
  have hv22 (w : Nat) : evalBuild r22.2 env w =
      if w == r21.2.lengths.size then evalElemOp (.scalar .add) ([r21.1,r19.1].map (evalBuild r21.2 env))
      else evalBuild r21.2 env w := by
    have h := evalBuild_mapN r21.2 n (.scalar .add) [r21.1,r19.1] env
    rw [hr22] at h
    exact congrFun h w
  have hv23 (w : Nat) : evalBuild r23.2 env w =
      if w == r22.2.lengths.size then evalElemOp (.scalar .add) ([r22.1,r20.1].map (evalBuild r22.2 env))
      else evalBuild r22.2 env w := by
    have h := evalBuild_mapN r22.2 n (.scalar .add) [r22.1,r20.1] env
    rw [hr23] at h
    exact congrFun h w
  have hA0 : a ≠ st.lengths.size := by omega
  have hB0 : b ≠ st.lengths.size := by omega
  have hM0 : k.mask ≠ st.lengths.size := by have := hk.mask_lt; omega
  have hS0 : k.s32 ≠ st.lengths.size := by have := hk.s32_lt; omega
  simp [hv23,hv22,hv21,hv20,hv19,hv18,hv17,hv16,hv15,hv14,hv13,hv12,hv11,hv10,hv9,hv8,hv7,hv6,hv5,hv4,hv3,hv2,hv1,hc23.1,hc23.2,hc22.1,hc22.2,hc21.1,hc21.2,hc20.1,hc20.2,hc19.1,hc19.2,hc18.1,hc18.2,hc17.1,hc17.2,hc16.1,hc16.2,hc15.1,hc15.2,hc14.1,hc14.2,hc13.1,hc13.2,hc12.1,hc12.2,hc11.1,hc11.2,hc10.1,hc10.2,hc9.1,hc9.2,hc8.1,hc8.2,hc7.1,hc7.2,hc6.1,hc6.2,hc5.1,hc5.2,hc4.1,hc4.2,hc3.1,hc3.2,hc2.1,hc2.2,hc1.1,hc1.2,Nat.add_assoc,stepInstr,evalElemOp,evalHypergraphOpBv,old_ne_fresh st a ha,
    old_ne_fresh st b hb,old_ne_fresh st k.mask hk.mask_lt,
    old_ne_fresh st k.s32 hk.s32_lt,hA0,hB0,hM0,hS0,
    hk.mask_value,hk.s32_value,wordShr_eq,wordShl_eq,
    Limbs.mulNetwork,Limbs.assemble,Limbs.pack32_bits,Limbs.add_bits,
    Limbs.mul_bits,Limbs.mask32_bits,Limbs.shr32_bits,limbs_bits]

theorem glReduceWide_extends (st : Build) (n : Nat) (k : GlConsts) (lo hi : Nat) :
    BuildExtends st ((glReduceWide n k lo hi).run st).2 := by
  obtain ⟨r1,hr1⟩ : ∃ r : Nat × Build, (mapN n .band [hi,k.mask]).run st = r := ⟨_,rfl⟩
  obtain ⟨r2,hr2⟩ : ∃ r : Nat × Build, (mapN n .shr [hi,k.s32]).run r1.2 = r := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r : Nat × Build, (mapN n .shl [r1.1,k.s32]).run r2.2 = r := ⟨_,rfl⟩
  obtain ⟨r4,hr4⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r3.1,r1.1]).run r3.2 = r := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r : Nat × Build, (mapN n .ult [lo,k.p]).run r4.2 = r := ⟨_,rfl⟩
  obtain ⟨r6,hr6⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [lo,k.p]).run r5.2 = r := ⟨_,rfl⟩
  obtain ⟨r7,hr7⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r5.1,lo,r6.1]).run r6.2 = r := ⟨_,rfl⟩
  obtain ⟨r8,hr8⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [k.p,r4.1]).run r7.2 = r := ⟨_,rfl⟩
  obtain ⟨r9,hr9⟩ : ∃ r : Nat × Build, (mapN n .ult [r7.1,r8.1]).run r8.2 = r := ⟨_,rfl⟩
  obtain ⟨r10,hr10⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r7.1,r4.1]).run r9.2 = r := ⟨_,rfl⟩
  obtain ⟨r11,hr11⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r7.1,r8.1]).run r10.2 = r := ⟨_,rfl⟩
  obtain ⟨r12,hr12⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r9.1,r10.1,r11.1]).run r11.2 = r := ⟨_,rfl⟩
  obtain ⟨r13,hr13⟩ : ∃ r : Nat × Build, (mapN n .ult [r12.1,r2.1]).run r12.2 = r := ⟨_,rfl⟩
  obtain ⟨r14,hr14⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [k.p,r2.1]).run r13.2 = r := ⟨_,rfl⟩
  obtain ⟨r15,hr15⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r14.1,r12.1]).run r14.2 = r := ⟨_,rfl⟩
  obtain ⟨r16,hr16⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r12.1,r2.1]).run r15.2 = r := ⟨_,rfl⟩
  obtain ⟨r17,hr17⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r13.1,r15.1,r16.1]).run r16.2 = r := ⟨_,rfl⟩
  simp only [glReduceWide,map2,map3,bind_run,pure_run,glCanon,glAdd,glSub,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17]
  change BuildExtends st r17.2
  have he1 : BuildExtends st r1.2 := by
    rw [← hr1]; exact mapN_extends st n .band [hi,k.mask]
  have he2 : BuildExtends r1.2 r2.2 := by
    rw [← hr2]; exact mapN_extends r1.2 n .shr [hi,k.s32]
  have he3 : BuildExtends r2.2 r3.2 := by
    rw [← hr3]; exact mapN_extends r2.2 n .shl [r1.1,k.s32]
  have he4 : BuildExtends r3.2 r4.2 := by
    rw [← hr4]; exact mapN_extends r3.2 n (.scalar .sub) [r3.1,r1.1]
  have he5 : BuildExtends r4.2 r5.2 := by
    rw [← hr5]; exact mapN_extends r4.2 n .ult [lo,k.p]
  have he6 : BuildExtends r5.2 r6.2 := by
    rw [← hr6]; exact mapN_extends r5.2 n (.scalar .sub) [lo,k.p]
  have he7 : BuildExtends r6.2 r7.2 := by
    rw [← hr7]; exact mapN_extends r6.2 n (.scalar .mux) [r5.1,lo,r6.1]
  have he8 : BuildExtends r7.2 r8.2 := by
    rw [← hr8]; exact mapN_extends r7.2 n (.scalar .sub) [k.p,r4.1]
  have he9 : BuildExtends r8.2 r9.2 := by
    rw [← hr9]; exact mapN_extends r8.2 n .ult [r7.1,r8.1]
  have he10 : BuildExtends r9.2 r10.2 := by
    rw [← hr10]; exact mapN_extends r9.2 n (.scalar .add) [r7.1,r4.1]
  have he11 : BuildExtends r10.2 r11.2 := by
    rw [← hr11]; exact mapN_extends r10.2 n (.scalar .sub) [r7.1,r8.1]
  have he12 : BuildExtends r11.2 r12.2 := by
    rw [← hr12]; exact mapN_extends r11.2 n (.scalar .mux) [r9.1,r10.1,r11.1]
  have he13 : BuildExtends r12.2 r13.2 := by
    rw [← hr13]; exact mapN_extends r12.2 n .ult [r12.1,r2.1]
  have he14 : BuildExtends r13.2 r14.2 := by
    rw [← hr14]; exact mapN_extends r13.2 n (.scalar .sub) [k.p,r2.1]
  have he15 : BuildExtends r14.2 r15.2 := by
    rw [← hr15]; exact mapN_extends r14.2 n (.scalar .add) [r14.1,r12.1]
  have he16 : BuildExtends r15.2 r16.2 := by
    rw [← hr16]; exact mapN_extends r15.2 n (.scalar .sub) [r12.1,r2.1]
  have he17 : BuildExtends r16.2 r17.2 := by
    rw [← hr17]; exact mapN_extends r16.2 n (.scalar .mux) [r13.1,r15.1,r16.1]
  exact ((((((((((((((((he1.trans he2).trans he3).trans he4).trans he5).trans he6).trans he7).trans he8).trans he9).trans he10).trans he11).trans he12).trans he13).trans he14).trans he15).trans he16).trans he17)

theorem glReduceWide_coordinates (st : Build) (n : Nat) (k : GlConsts) (lo hi : Nat) :
    ((glReduceWide n k lo hi).run st).1 = st.lengths.size+16 ∧
    ((glReduceWide n k lo hi).run st).2.lengths.size = st.lengths.size+17 := by
  obtain ⟨r1,hr1⟩ : ∃ r : Nat × Build, (mapN n .band [hi,k.mask]).run st = r := ⟨_,rfl⟩
  obtain ⟨r2,hr2⟩ : ∃ r : Nat × Build, (mapN n .shr [hi,k.s32]).run r1.2 = r := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r : Nat × Build, (mapN n .shl [r1.1,k.s32]).run r2.2 = r := ⟨_,rfl⟩
  obtain ⟨r4,hr4⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r3.1,r1.1]).run r3.2 = r := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r : Nat × Build, (mapN n .ult [lo,k.p]).run r4.2 = r := ⟨_,rfl⟩
  obtain ⟨r6,hr6⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [lo,k.p]).run r5.2 = r := ⟨_,rfl⟩
  obtain ⟨r7,hr7⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r5.1,lo,r6.1]).run r6.2 = r := ⟨_,rfl⟩
  obtain ⟨r8,hr8⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [k.p,r4.1]).run r7.2 = r := ⟨_,rfl⟩
  obtain ⟨r9,hr9⟩ : ∃ r : Nat × Build, (mapN n .ult [r7.1,r8.1]).run r8.2 = r := ⟨_,rfl⟩
  obtain ⟨r10,hr10⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r7.1,r4.1]).run r9.2 = r := ⟨_,rfl⟩
  obtain ⟨r11,hr11⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r7.1,r8.1]).run r10.2 = r := ⟨_,rfl⟩
  obtain ⟨r12,hr12⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r9.1,r10.1,r11.1]).run r11.2 = r := ⟨_,rfl⟩
  obtain ⟨r13,hr13⟩ : ∃ r : Nat × Build, (mapN n .ult [r12.1,r2.1]).run r12.2 = r := ⟨_,rfl⟩
  obtain ⟨r14,hr14⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [k.p,r2.1]).run r13.2 = r := ⟨_,rfl⟩
  obtain ⟨r15,hr15⟩ : ∃ r : Nat × Build, (mapN n (.scalar .add) [r14.1,r12.1]).run r14.2 = r := ⟨_,rfl⟩
  obtain ⟨r16,hr16⟩ : ∃ r : Nat × Build, (mapN n (.scalar .sub) [r12.1,r2.1]).run r15.2 = r := ⟨_,rfl⟩
  obtain ⟨r17,hr17⟩ : ∃ r : Nat × Build, (mapN n (.scalar .mux) [r13.1,r15.1,r16.1]).run r16.2 = r := ⟨_,rfl⟩
  simp only [glReduceWide,map2,map3,bind_run,pure_run,glCanon,glAdd,glSub,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17]
  change r17.1 = st.lengths.size+16 ∧ r17.2.lengths.size = st.lengths.size+17
  have hc1 : r1.1 = st.lengths.size ∧ r1.2.lengths.size = st.lengths.size+1 := by
    rw [← hr1,mapN_run]; simp
  have hc2 : r2.1 = r1.2.lengths.size ∧ r2.2.lengths.size = r1.2.lengths.size+1 := by
    rw [← hr2,mapN_run]; simp
  have hc3 : r3.1 = r2.2.lengths.size ∧ r3.2.lengths.size = r2.2.lengths.size+1 := by
    rw [← hr3,mapN_run]; simp
  have hc4 : r4.1 = r3.2.lengths.size ∧ r4.2.lengths.size = r3.2.lengths.size+1 := by
    rw [← hr4,mapN_run]; simp
  have hc5 : r5.1 = r4.2.lengths.size ∧ r5.2.lengths.size = r4.2.lengths.size+1 := by
    rw [← hr5,mapN_run]; simp
  have hc6 : r6.1 = r5.2.lengths.size ∧ r6.2.lengths.size = r5.2.lengths.size+1 := by
    rw [← hr6,mapN_run]; simp
  have hc7 : r7.1 = r6.2.lengths.size ∧ r7.2.lengths.size = r6.2.lengths.size+1 := by
    rw [← hr7,mapN_run]; simp
  have hc8 : r8.1 = r7.2.lengths.size ∧ r8.2.lengths.size = r7.2.lengths.size+1 := by
    rw [← hr8,mapN_run]; simp
  have hc9 : r9.1 = r8.2.lengths.size ∧ r9.2.lengths.size = r8.2.lengths.size+1 := by
    rw [← hr9,mapN_run]; simp
  have hc10 : r10.1 = r9.2.lengths.size ∧ r10.2.lengths.size = r9.2.lengths.size+1 := by
    rw [← hr10,mapN_run]; simp
  have hc11 : r11.1 = r10.2.lengths.size ∧ r11.2.lengths.size = r10.2.lengths.size+1 := by
    rw [← hr11,mapN_run]; simp
  have hc12 : r12.1 = r11.2.lengths.size ∧ r12.2.lengths.size = r11.2.lengths.size+1 := by
    rw [← hr12,mapN_run]; simp
  have hc13 : r13.1 = r12.2.lengths.size ∧ r13.2.lengths.size = r12.2.lengths.size+1 := by
    rw [← hr13,mapN_run]; simp
  have hc14 : r14.1 = r13.2.lengths.size ∧ r14.2.lengths.size = r13.2.lengths.size+1 := by
    rw [← hr14,mapN_run]; simp
  have hc15 : r15.1 = r14.2.lengths.size ∧ r15.2.lengths.size = r14.2.lengths.size+1 := by
    rw [← hr15,mapN_run]; simp
  have hc16 : r16.1 = r15.2.lengths.size ∧ r16.2.lengths.size = r15.2.lengths.size+1 := by
    rw [← hr16,mapN_run]; simp
  have hc17 : r17.1 = r16.2.lengths.size ∧ r17.2.lengths.size = r16.2.lengths.size+1 := by
    rw [← hr17,mapN_run]; simp
  omega

theorem masked_shl32 (x : Word) : (x &&& 0xFFFFFFFF#64) <<< 32 = x <<< 32 := by bv_decide


theorem limbs_inverse (x : Limbs.Word) : limbs x.bits = x := by
  apply (Limbs.Word.val_inj _ _).mp
  rw [limbs_val,Limbs.Word.bits_val]

theorem glReduceWide_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (lo hi : Nat)
    (hlo : lo < st.lengths.size) (hhi : hi < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glReduceWide n k lo hi).run st
    evalBuild out.2 env out.1 =
      (Limbs.Goldilocks.reduceNetwork ⟨limbs (evalBuild st env lo),limbs (evalBuild st env hi)⟩).bits := by
  let r1 := (mapN n .band [hi,k.mask]).run st
  let r2 := (mapN n .shr [hi,k.s32]).run r1.2
  let r3 := (mapN n .shl [r1.1,k.s32]).run r2.2
  let r4 := (mapN n (.scalar .sub) [r3.1,r1.1]).run r3.2
  let r5 := (glCanon n k lo).run r4.2
  let r6 := (glAdd n k r5.1 r4.1).run r5.2
  let r7 := (glSub n k r6.1 r2.1).run r6.2
  let upper := limbs (evalBuild st env hi)
  let lower := limbs (evalBuild st env lo)
  let middle := Limbs.sub (⟨0#32,upper.lo⟩ : Limbs.Word) ⟨upper.lo,0#32⟩
  have he1 : BuildExtends st r1.2 := mapN_extends st n .band [hi,k.mask]
  have he2 : BuildExtends r1.2 r2.2 := mapN_extends r1.2 n .shr [hi,k.s32]
  have he3 : BuildExtends r2.2 r3.2 := mapN_extends r2.2 n .shl [r1.1,k.s32]
  have he4 : BuildExtends r3.2 r4.2 := mapN_extends r3.2 n (.scalar .sub) [r3.1,r1.1]
  have he := ((he1.trans he2).trans he3).trans he4
  have hc := glCanon_extends r4.2 n k lo
  have ha := glAdd_extends r5.2 n k r5.1 r4.1
  have hs := glSub_extends r6.2 n k r6.1 r2.1
  have h4 : r4.1 < r4.2.lengths.size := by simp [r4,mapN_run]
  have h2 : r2.1 < r4.2.lengths.size := by simp [r4,r3,r2,mapN_run]; omega
  have h5 : r5.1 < r5.2.lengths.size := by
    have h := glCanon_coordinates r4.2 n k lo; dsimp only [r5]; omega
  have h6 : r6.1 < r6.2.lengths.size := by
    have h := glAdd_coordinates r5.2 n k r5.1 r4.1; dsimp only [r6]; omega
  have hv2 : evalBuild r4.2 env r2.1 = (⟨upper.hi,0#32⟩ : Limbs.Word).bits := by
    simp only [r4,evalBuild_mapN,r3,r2,r1]
    simp only [mapN_run,Array.size_push]
    simp [stepInstr,evalElemOp,evalHypergraphOpBv,
      old_ne_fresh st hi hhi,old_ne_fresh st k.s32 hk.s32_lt,
      show hi ≠ st.lengths.size by omega,
      show k.s32 ≠ st.lengths.size by have := hk.s32_lt; omega,
      hk.s32_value,wordShr_eq,upper,Limbs.shr32_bits,limbs_bits,Nat.add_assoc]
  have hv4 : evalBuild r4.2 env r4.1 = middle.bits := by
    simp only [r4,evalBuild_mapN,r3,r2,r1]
    simp only [mapN_run,Array.size_push]
    simp [stepInstr,evalElemOp,evalHypergraphOpBv,
      old_ne_fresh st hi hhi,old_ne_fresh st k.mask hk.mask_lt,
      old_ne_fresh st k.s32 hk.s32_lt,
      show hi ≠ st.lengths.size by omega,
      show k.mask ≠ st.lengths.size by have := hk.mask_lt; omega,
      show k.s32 ≠ st.lengths.size by have := hk.s32_lt; omega,
      hk.mask_value,hk.s32_value,wordShl_eq,middle,upper,Limbs.sub_bits,
      Limbs.shl32_bits,Limbs.mask32_bits,limbs_bits,masked_shl32,Nat.add_assoc]
  have hv5 : evalBuild r5.2 env r5.1 = (Limbs.Goldilocks.canon lower).bits := by
    have h := glCanon_limbs r4.2 env n k lo (Nat.lt_of_lt_of_le hlo he.size_le) (hk.mono he)
    dsimp only at h
    rw [he.frame env lo hlo] at h
    exact h
  have hv6 : evalBuild r6.2 env r6.1 =
      (Limbs.Goldilocks.addCanonical (Limbs.Goldilocks.canon lower) middle).bits := by
    have h := glAdd_limbs r5.2 env n k r5.1 r4.1 h5
      (Nat.lt_of_lt_of_le h4 hc.size_le) ((hk.mono he).mono hc)
    dsimp only at h
    rw [hv5,hc.frame env r4.1 h4,hv4,limbs_inverse,limbs_inverse] at h
    exact h
  have h := glSub_limbs r6.2 env n k r6.1 r2.1 h6
    (Nat.lt_of_lt_of_le h2 (hc.trans ha).size_le) (((hk.mono he).mono hc).mono ha)
  dsimp only at h
  rw [hv6,(hc.trans ha).frame env r2.1 h2,hv2,limbs_inverse,limbs_inverse] at h
  simp only [glReduceWide,bind_run,map2]
  change evalBuild r7.2 env r7.1 = _
  exact h

theorem glMul_extends (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    BuildExtends st ((glMul n k a b).run st).2 := by
  let wide := (glMulWide n k a b).run st
  simp only [glMul,bind_run]
  exact (glMulWide_extends st n k a b).trans
    (glReduceWide_extends wide.2 n k wide.1.1 wide.1.2)

theorem glMul_coordinates (st : Build) (n : Nat) (k : GlConsts) (a b : Nat) :
    ((glMul n k a b).run st).1 = st.lengths.size+39 ∧
      ((glMul n k a b).run st).2.lengths.size = st.lengths.size+40 := by
  let wide := (glMulWide n k a b).run st
  have hw := glMulWide_coordinates st n k a b
  have hr := glReduceWide_coordinates wide.2 n k wide.1.1 wide.1.2
  simp only [glMul,bind_run]
  change _ ∧ _
  dsimp only [wide] at hr
  constructor <;> omega

/-- The emitted source instruction sequence is the proved limb multiply network,
for arbitrary 64-bit operands. -/
theorem glMul_limbs (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glMul n k a b).run st
    evalBuild out.2 env out.1 =
      (Limbs.Goldilocks.mul (limbs (evalBuild st env a)) (limbs (evalBuild st env b))).bits := by
  let wide := (glMulWide n k a b).run st
  have hw := glMulWide_limbs st env n k a b ha hb hk
  have hc := glMulWide_coordinates st n k a b
  have hlo : wide.1.1 < wide.2.lengths.size := by dsimp only [wide]; omega
  have hhi : wide.1.2 < wide.2.lengths.size := by dsimp only [wide]; omega
  have hr := glReduceWide_limbs wide.2 env n k wide.1.1 wide.1.2 hlo hhi
    (hk.mono (glMulWide_extends st n k a b))
  simp only [glMul,bind_run]
  change evalBuild ((glReduceWide n k wide.1.1 wide.1.2).run wide.2).2 env
    ((glReduceWide n k wide.1.1 wide.1.2).run wide.2).1 = _
  rw [hr]
  change _ = (Limbs.Goldilocks.reduceNetwork _).bits
  dsimp only at hw
  change evalBuild wide.2 env wide.1.1 = _ ∧ evalBuild wide.2 env wide.1.2 = _ at hw
  rw [hw.1,hw.2,limbs_inverse,limbs_inverse]

/-- Universal field multiply through the actual builder/register interpreter.
The operand words need not be canonical; the result always is. -/
theorem glMul_sound (st : Build) (env : Nat → Word) (n : Nat) (k : GlConsts) (a b : Nat)
    (ha : a < st.lengths.size) (hb : b < st.lengths.size) (hk : ConstsAt st env k) :
    let out := (glMul n k a b).run st
    (evalBuild out.2 env out.1).toNat < goldilocksPrime ∧
      (evalBuild out.2 env out.1).toNat =
        ((evalBuild st env a).toNat*(evalBuild st env b).toNat) % goldilocksPrime := by
  dsimp only
  rw [glMul_limbs st env n k a b ha hb hk,Limbs.Word.bits_val,
    Limbs.Goldilocks.mul_sound,limbs_val,limbs_val]
  simp only [goldilocksMulSpec,glN,← Nat.mul_mod]
  exact ⟨Nat.mod_lt _ (by decide),True.intro⟩

theorem BuildExtends.refl (st : Build) : BuildExtends st st :=
  ⟨Nat.le_refl _,fun _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem newWire_run (st : Build) (n : Nat) :
    (newWire n).run st = (st.lengths.size,{st with lengths := st.lengths.push n}) := rfl

theorem newWire_extends (st : Build) (n : Nat) :
    BuildExtends st ((newWire n).run st).2 := by
  constructor
  · simp [newWire_run]
  · intro env w _; rfl
  · intro env w _; rfl

theorem broadcast_extends (st : Build) (n : Nat) (v : Word) (hn : 0 < n) :
    BuildExtends st ((broadcast n v).run st).2 := by
  constructor
  · simp [broadcast_run]
  · intro env w hw
    rw [evalBuild_broadcast st env n v hn]
    simp [stepInstr,show w ≠ st.lengths.size by omega]
  · intro env w hw
    rw [broadcast_run] at hw
    simp only [Array.size_push] at hw
    rw [evalBuild_broadcast st env n v hn]
    simp [stepInstr,show w ≠ st.lengths.size by omega]

theorem glConsts_extends (st : Build) (n : Nat) (hn : 0 < n) :
    BuildExtends st ((glConsts n).run st).2 := by
  let r1 := (broadcast n (BitVec.ofNat 64 goldilocksP)).run st
  let r2 := (broadcast n 0xFFFFFFFF#64).run r1.2
  let r3 := (broadcast n 32#64).run r2.2
  change BuildExtends st r3.2
  exact ((broadcast_extends st n _ hn).trans (broadcast_extends r1.2 n _ hn)).trans
    (broadcast_extends r2.2 n _ hn)

theorem glConsts_coordinates (st : Build) (n : Nat) :
    ((glConsts n).run st).2.lengths.size = st.lengths.size+3 := by
  simp only [glConsts,bind_run,pure_run,broadcast_run,Array.size_push]

/-- In a builder constructed from the empty state, not-yet-allocated load
registers still contain their supplied environment values. -/
theorem BuildExtends.fresh_value {st : Build} (h : BuildExtends {} st)
    (env : Nat → Word) (w : Nat) (hw : st.lengths.size ≤ w) :
    evalBuild st env w = env w := by
  exact h.future_frame env w hw

end Obend.Hardware.Gpu.GoldilocksSourceCorrect
end
