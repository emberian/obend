module
public import Obend.Hardware.Gpu.NttDispatchCorrect
public import Obend.Hardware.Gpu.NttPhaseMetadata
public import Obend.Hardware.Gpu.NttMemory
public import Obend.Hardware.Gpu.NttReadBounds
@[expose] public section

/-! Source-derived scatter geometry. These facts establish uniqueness from the
actual lane/register permutation, without evaluating an admission checker. -/
namespace Obend.Hardware.Gpu.NttDispatchGeometry
open Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel
open Obend.Hardware.Gpu.Ntt Obend.Hardware.Gpu.Ntt.BlockNtt
open Obend.Hardware.Gpu.NttBatchCorrect Obend.Hardware.Gpu.NttDispatchCorrect
set_option autoImplicit false

theorem grid_nodup {α : Type} (rows cols : Nat) (f : Nat → Nat → α)
    (hi : ∀ a < rows, ∀ b < cols, ∀ c < rows, ∀ d < cols,
      f a b = f c d → a=c ∧ b=d) :
    ((List.range rows).flatMap fun a => (List.range cols).map (f a)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := cols))
    intro b d hb hd hne he
    exact hne (hi a (List.mem_range.mp ha) b (List.mem_range.mp hb)
      a (List.mem_range.mp ha) d (List.mem_range.mp hd) he).2
  · apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := rows))
    intro a c ha hc hne x hx y hy he
    obtain ⟨b,hb,hx⟩ := List.mem_map.mp hx
    obtain ⟨d,hd,hy⟩ := List.mem_map.mp hy
    have hxy : f a b = f c d := hx.trans (he.trans hy.symm)
    exact hne (hi a (List.mem_range.mp ha) b (List.mem_range.mp hb)
      c (List.mem_range.mp hc) d (List.mem_range.mp hd) hxy).1

theorem map_zipIdx_second {α β : Type} (xs : List α) (f : Nat → β) :
    xs.zipIdx.map (fun item => f item.2) = (List.range xs.length).map f := by
  calc
    _ = (xs.zipIdx.map Prod.snd).map f := by simp only [List.map_map,Function.comp_def]
    _ = _ := by rw [List.zipIdx_map_snd,←List.range_eq_range']

/-- Exact address enumeration follows from the real phaseAction output length. -/
theorem phase_addresses (n count bits p done degree src dst : Nat) (first last : Bool) (g : Nat) :
    (phase n count bits p done degree src dst first last).writeAddresses g =
      (List.range (count/2^degree)).flatMap fun l =>
        (List.range (2^degree)).map fun r =>
          (dst,(phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r).eval g l) := by
  unfold Phase.writeAddresses
  change (List.range (count/2^degree)).flatMap (fun l => _) = _
  apply congrArg (fun f => (List.range (count/2^degree)).flatMap f)
  funext l
  change ((((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).map fun w => (w.array,w.index.eval g l)) = _
  simp only [List.map_map,Function.comp_def]
  have hm := map_zipIdx_second ((phaseAction n count p done degree src first).run {}).1.2
    (fun r => (dst,(phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r).eval g l))
  simpa only [PhaseMetadata.phaseAction_length] using hm

theorem phaseSaveIndex_injective (bits p done degree g l l' r r' : Nat) (last : Bool)
    (hp : 0 < p) (hd : done+degree ≤ bits)
    (hl : l < 2^bits/2^degree) (hl' : l' < 2^bits/2^degree)
    (hr : r < 2^degree) (hr' : r' < 2^degree)
    (he : (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r).eval g l =
      (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r').eval g l') :
    l=l' ∧ r=r' := by
  have hs : 0 < 2^bits/(2^done*2^degree) := by rw [phase_stride bits done degree hd]; exact Nat.two_pow_pos _
  have hi := phase_index_lt bits done degree l r hd hl hr
  have hi' := phase_index_lt bits done degree l' r' hd hl' hr'
  rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hi,
    phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hi'] at he
  have heq : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) l r =
      laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) l' r' := by
    cases last with
    | false => exact he
    | true =>
      change outputAddress p (2^bits) g _ = outputAddress p (2^bits) g _ at he
      have hr := (outputAddress_injective p (2^bits) g g _ _ hp
        (reverseIndex_lt bits _ hi) (reverseIndex_lt bits _ hi') he).2
      have hx := congrArg (reverseIndex bits) hr
      simpa only [reverseIndex_involution bits _ hi,reverseIndex_involution bits _ hi'] using hx
  exact laneRegisterIndex_injective _ _ _ _ _ _ hs hr hr' heq

/-- Every original phase has a unique scatter for all supported layer positions. -/
theorem phase_addresses_nodup (n bits p done degree src dst : Nat) (first last : Bool) (g : Nat)
    (hp : 0 < p) (hd : done+degree ≤ bits) :
    ((phase n (2^bits) bits p done degree src dst first last).writeAddresses g).Nodup := by
  rw [phase_addresses]
  apply grid_nodup
  intro l hl r hr l' hl' r' hr' he
  exact phaseSaveIndex_injective bits p done degree g l l' r r' last hp hd hl hl' hr hr'
    (congrArg Prod.snd he)

/-- A real phase spans its entire upload tile, independently of its fused radix. -/
theorem phase_tile_size (n bits p done degree src dst : Nat) (first last : Bool)
    (hd : degree ≤ bits) :
    (phase n (2^bits) bits p done degree src dst first last).lanes *
      (phase n (2^bits) bits p done degree src dst first last).writes.length = 2^bits := by
  rw [PhaseMetadata.phase_writes_length]
  change (2^bits/2^degree)*2^degree = _
  exact Nat.div_mul_cancel (Nat.pow_dvd_pow 2 hd)


theorem batch_phase_addresses (n count bits p done degree src dst stride k : Nat)
    (first last : Bool) (g : Nat) :
    (batchPhase stride k (phase n count bits p done degree src dst first last)).writeAddresses g =
      (List.range ((count/2^degree)*k)).flatMap fun l =>
        (List.range (2^degree)).map fun r => (dst,
          (batchIndex stride k (count/2^degree) dst
            (phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r)).eval g l) := by
  unfold Phase.writeAddresses
  change (List.range ((count/2^degree)*k)).flatMap (fun l => _) = _
  apply congrArg (fun f => (List.range ((count/2^degree)*k)).flatMap f)
  funext l
  change (((((phaseAction n count p done degree src first).run {}).1.2.zipIdx.map
    fun (value,r) => (⟨dst,phaseSaveIndex count bits p (2^degree)
      (count/(2^done*2^degree)) last r,value⟩ : Write)).map fun w =>
      {w with index := batchIndex stride k (count/2^degree) w.array w.index}).map
        fun w => (w.array,w.index.eval g l)) = _
  simp only [List.map_map,Function.comp_def]
  have hm := map_zipIdx_second ((phaseAction n count p done degree src first).run {}).1.2
    (fun r => (dst,(batchIndex stride k (count/2^degree) dst
      (phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r)).eval g l))
  simpa only [PhaseMetadata.phaseAction_length] using hm

theorem batch_save_injective (bits p done degree dst stride k g l l' r r' : Nat)
    (last : Bool) (hp : 0 < p) (hd : done+degree ≤ bits) (hstride : 2^bits ≤ stride)
    (hdevice : last = true → dst ≤ 1) (hshared : last = false → dst=2 ∨ dst=3)
    (hl : l < (2^bits/2^degree)*k) (hl' : l' < (2^bits/2^degree)*k)
    (hr : r < 2^degree) (hr' : r' < 2^degree)
    (he : (batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r)).eval g l =
      (batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r')).eval g l') :
    l=l' ∧ r=r' := by
  let lanes := 2^bits/2^degree
  have hlanes : 0 < lanes := by
    dsimp [lanes]
    rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
    exact Nat.two_pow_pos _
  have hm := Nat.mod_lt l hlanes
  have hm' := Nat.mod_lt l' hlanes
  have hi := phase_index_lt bits done degree (l%lanes) r hd hm hr
  have hi' := phase_index_lt bits done degree (l'%lanes) r' hd hm' hr'
  rw [batchIndex_eval,batchIndex_eval] at he
  change tileIndex stride (l/lanes) dst _ = tileIndex stride (l'/lanes) dst _ at he
  have htile : l/lanes = l'/lanes := by
    cases last with
    | true =>
      have hdst := hdevice rfl
      have h2 : dst ≠ 2 := by omega
      have h3 : dst ≠ 3 := by omega
      simp only [tileIndex,show (dst == 2 || dst == 3) = false by simp [h2,h3],Bool.false_eq_true,ite_false] at he
      rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hi,
        phaseSaveIndex_eval _ _ _ _ _ _ _ _ true hi'] at he
      change outputAddress p (2^bits) (g*k+l/lanes) _ = outputAddress p (2^bits) (g*k+l'/lanes) _ at he
      have hx := (outputAddress_injective p (2^bits) _ _ _ _ hp
        (reverseIndex_lt bits _ hi) (reverseIndex_lt bits _ hi') he).1
      omega
    | false =>
      have hdst := hshared rfl
      have hh : (dst == 2 || dst == 3) = true := by simpa using hdst
      simp only [tileIndex,hh,ite_true] at he
      rw [phaseSaveIndex_eval _ _ _ _ _ _ _ _ false hi,
        phaseSaveIndex_eval _ _ _ _ _ _ _ _ false hi'] at he
      simp only [Bool.false_eq_true,ite_false] at he
      have hx := congrArg (fun x => x/stride) he
      have hpos : 0 < stride := by have := Nat.two_pow_pos bits; omega
      rw [Nat.add_mul_div_right _ _ hpos,Nat.add_mul_div_right _ _ hpos,
        Nat.div_eq_of_lt (by omega : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l%lanes) r < stride),
        Nat.div_eq_of_lt (by omega : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l'%lanes) r' < stride)] at hx
      simpa using hx
  have hsave : (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r).eval (g*k+l/lanes) (l%lanes) =
      (phaseSaveIndex (2^bits) bits p (2^degree) (2^bits/(2^done*2^degree)) last r').eval (g*k+l/lanes) (l'%lanes) := by
    rw [←htile] at he
    dsimp only [lanes] at he ⊢
    unfold tileIndex at he
    split at he <;> omega
  have hx := phaseSaveIndex_injective bits p done degree (g*k+l/lanes)
    (l%lanes) (l'%lanes) r r' last hp hd hm hm' hr hr' hsave
  constructor
  · have h1 := Nat.div_add_mod l lanes
    have h2 := Nat.div_add_mod l' lanes
    rw [htile,hx.1] at h1
    omega
  · exact hx.2

/-- Packed phases have a unique scatter by construction, including independent
shared tile coordinates and the final global Stockham permutation. -/
theorem batch_phase_addresses_nodup (n bits p done degree src dst stride k : Nat)
    (first last : Bool) (g : Nat) (hp : 0 < p) (hd : done+degree ≤ bits)
    (hstride : 2^bits ≤ stride) (hdevice : last=true → dst≤1)
    (hshared : last=false → dst=2 ∨ dst=3) :
    ((batchPhase stride k (phase n (2^bits) bits p done degree src dst first last)).writeAddresses g).Nodup := by
  rw [batch_phase_addresses]
  apply grid_nodup
  intro l hl r hr l' hl' r' hr' he
  exact batch_save_injective bits p done degree dst stride k g l l' r r' last hp hd hstride
    hdevice hshared hl hl' hr hr' (congrArg Prod.snd he)

/-- The allocator's chosen tile stride covers the complete transform tile. -/
theorem dispatch_tileSize_lower (n logP bits src dst : Nat) (hb : 0 < bits) :
    2^bits ≤ tileSize (dispatch n logP bits src dst) := by
  have hn := phaseDegrees_ne_nil bits hb
  cases he : phaseDegrees bits with
  | nil => exact False.elim (hn he)
  | cons c cs =>
    have hsum := phaseDegrees_sum bits
    rw [he] at hsum
    have hc : c ≤ bits := by simp only [List.sum_cons] at hsum; omega
    have hm : phase n (2^bits) bits (2^logP) 0 c src
        (phaseOutput bits dst 0 src c) true (0+c==bits) ∈
        (dispatch n logP bits src dst).phases := by
      simp [dispatch,he,buildPhases,phaseOutput]
    have h := maxFold_member (fun ph : Phase => ph.lanes*ph.writes.length)
      (dispatch n logP bits src dst).phases 1 _ hm
    rw [phase_tile_size _ _ _ _ _ _ _ _ _ hc] at h
    exact h

/-- Bounds for every concrete packed store, derived from its actual slot and
Stockham address rather than a finite checker receipt. -/
theorem packed_phase_writes_valid (total bits logP done degree src dst stride k group : Nat)
    (first last : Bool) (hp : logP+bits ≤ total) (hd : done+degree ≤ bits)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    ∀ lane < (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).lanes,
      ∀ w ∈ (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).writes,
        BlockLower.Valid (nttBlockProgram (2^total)) w.array (w.index.eval group lane) := by
  intro lane hl w hw
  have hm : (w.array,w.index.eval group lane) ∈
      (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)).writeAddresses group :=
    List.mem_flatMap.mpr ⟨lane,List.mem_range.mpr hl,List.mem_map.mpr ⟨w,hw,rfl⟩⟩
  rw [batch_phase_addresses] at hm
  obtain ⟨l,hl,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  have hvalid : BlockLower.Valid (nttBlockProgram (2^total)) dst
      ((batchIndex stride k (2^bits/2^degree) dst
        (phaseSaveIndex (2^bits) bits (2^logP) (2^degree) (2^bits/(2^done*2^degree)) last r)).eval group l) := by
    have hl := List.mem_range.mp hl
    have hr := List.mem_range.mp hr
    let lanes := 2^bits/2^degree
    have hlanes : 0 < lanes := by
      dsimp only [lanes]
      rw [Nat.pow_div (by omega : degree ≤ bits) (by decide)]
      exact Nat.two_pow_pos _
    have htile : l/lanes < k := (Nat.div_lt_iff_lt_mul hlanes).mpr (by simpa [Nat.mul_comm] using hl)
    have hidx := phase_index_lt bits done degree (l%lanes) r hd (Nat.mod_lt _ hlanes) hr
    rw [batchIndex_eval,phaseSaveIndex_eval _ _ _ _ _ _ _ _ last hidx]
    cases last with
    | false =>
      have ha := hlocal rfl
      have hh : (dst==2 || dst==3)=true := by simpa using ha
      simp only [Bool.false_eq_true,ite_false,tileIndex,hh,ite_true]
      have hm := Nat.mul_le_mul_right stride (by omega : l/lanes+1 ≤ k)
      rw [Nat.add_mul,Nat.one_mul] at hm
      have hi : laneRegisterIndex (2^degree) (2^bits/(2^done*2^degree)) (l%lanes) r +
          (l/lanes)*stride < sharedWords (2^total) := by
        rw [Nat.mul_comm stride k] at hshared
        omega
      rcases ha with rfl | rfl <;>
        simpa [BlockLower.Valid,BlockLower.buffer,nttBlockProgram] using hi
    | true =>
      have ha := hdevice rfl
      have hh : (dst==2 || dst==3)=false := by simp; omega
      simp only [ite_true,tileIndex,hh,ite_false]
      have hf : 2^total = 2^logP*2^bits*2^(total-(logP+bits)) := by
        rw [←Nat.pow_add,←Nat.pow_add,Nat.add_sub_of_le hp]
      have hg : group*k+l/lanes < 2^logP*2^(total-(logP+bits)) := by
        have hg := hgroups _ htile
        rw [hf] at hg
        simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_div_cancel,
          Nat.two_pow_pos] using hg
      have hi := outputAddress_bound (2^logP) (2^bits) (2^(total-(logP+bits)))
        (group*k+l/lanes) _ (Nat.two_pow_pos _) hg (reverseIndex_lt bits _ hidx)
      rw [←hf] at hi
      have hcases : dst=0 ∨ dst=1 := by omega
      rcases hcases with rfl | rfl <;>
        simpa [BlockLower.Valid,BlockLower.buffer,nttBlockProgram,outputAddress] using hi
  have ha := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  dsimp only [Prod.fst,Prod.snd] at ha hi
  rw [←ha,←hi]
  exact hvalid

/-- Each logical result slot is one of the actual phase's stores. -/
theorem phase_slot_write (n count bits p done degree src dst : Nat) (first last : Bool)
    (r : Nat) (hr : r<2^degree) :
    (⟨dst,phaseSaveIndex count bits p (2^degree) (count/(2^done*2^degree)) last r,
      ((phaseAction n count p done degree src first).run {}).1.2.getD r 0⟩ : Write) ∈
      (phase n count bits p done degree src dst first last).writes := by
  let regs := ((phaseAction n count p done degree src first).run {}).1.2
  have hlen : r < regs.length := by
    dsimp only [regs]
    rw [PhaseMetadata.phaseAction_length]
    exact hr
  apply List.mem_map.mpr
  refine ⟨(regs.getD r 0,r),?_,rfl⟩
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  change regs[r]? = some (regs.getD r 0)
  rw [List.getElem?_eq_getElem hlen]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlen,Option.getD_some]

/-- Both sides of packed-phase memory safety follow from actual metadata. -/
theorem packed_phase_inBounds (total bits logP done degree src dst stride k group : Nat)
    (first last : Bool) (hp : logP+bits ≤ total) (hd : done+degree ≤ bits)
    (hsrc : src≤3) (hfirst : first=true → src≤1)
    (hstride : 2^bits ≤ stride) (hshared : stride*k ≤ sharedWords (2^total))
    (hdevice : last=true → dst≤1) (hlocal : last=false → dst=2 ∨ dst=3)
    (hgroups : ∀ tile, tile<k → group*k+tile < 2^total/2^bits) :
    BlockLower.PhaseInBounds (nttBlockProgram (2^total))
      (batchPhase stride k (phase (2^total) (2^bits) bits (2^logP) done degree src dst first last)) group :=
  ⟨packed_phase_reads_valid total bits (2^logP) done degree src dst stride k group first last
    (by omega) hd hsrc hfirst hstride hshared hgroups,
   packed_phase_writes_valid total bits logP done degree src dst stride k group first last hp hd
    hstride hshared hdevice hlocal hgroups⟩

end Obend.Hardware.Gpu.NttDispatchGeometry
end
