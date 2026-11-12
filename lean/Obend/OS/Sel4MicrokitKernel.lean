module
/-
# Obend.OS.Sel4MicrokitKernel — temporal isolation, copy-before-verify, and the verifier loop

Over the kernel of `Obend.OS.Sel4MicrokitKernelCore` (capabilities and their derivation tree,
address translation, memory confinement):

1. `mcs_temporal_isolation_bound`: a domain's scheduling context is a sporadic server, and in any
   window of `ΔT` ticks the domain runs at most `⌈ΔT / period⌉ · budget + budget` of them.
2. `copy_into_private_pd_frame_before_verify`: the verifier domain copies the shared ring slot
   into a frame only it can reach, and what it later reads there is what the ring held at the
   copy instant, whatever every other domain and device did in between.
3. `ValidVerifierLoop` runs that ingress turn after turn against three machines at once: the
   kernel, the irreversible outbox (`Obend.Vault.IrreversibleOutbox`) and the grain powerbox
   (`Obend.Polis.GrainPowerbox`). The request the gatekeeper is handed carries what the verifier
   read from its private frame at dispatch time. `sel4_microkit_verifier_loop_safe` concludes,
   for every actuation ever dispatched, that its payload is the ring content at the copy instant
   of the turn that requested it, that the powerbox logged an invocation of exactly those bytes
   by the requesting grain, and that the outbox's finality and at-most-once guarantees hold;
   and for the kernel, that the derivation tree, the mapping backing, the frame's privacy and
   every scheduling context's budget survived the whole run with no authority amplified.

`ValidVerifierLoop` is a recursive definition, so `#tooth` can replay the loop theorems against a
mutated kernel step.
-/
public import Obend.OS.Sel4MicrokitKernelCore
public import Obend.Vault.IrreversibleOutbox
public import Obend.Polis.GrainPowerbox
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.Vault.IrreversibleOutbox
import all Obend.Polis.GrainPowerbox

public section
namespace Obend.OS.Sel4MicrokitKernel

open Obend.Consensus.SimplexProtocol
open Obend.Digest.Cshake256.Native (bytesOfList)
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (SeL4MicrokitPartition checkMicrokitIsolation Sel4CapDlNonInterfering)
open Obend.Polis.GrainPowerbox (PowerboxHost PowerboxTurn stepPowerboxHost ValidPowerboxTrace
  GrainId Accountable AuditAttributionEntry actionDigest PrincipalId step_invoke trace_ext
  trace_accountable)

set_option autoImplicit false

/-! ## 1. Temporal isolation -/

/-- Domain `p` ran during this event: the tick offered it the processor and its context paid. -/
def ranAt (k : KState) (p : PdId) : KEvent → Bool
  | .tick (some q) => q == p && ((k.scs[p]?).bind (·.charge k.now)).isSome
  | _ => false

def isTick : KEvent → Bool
  | .tick _ => true
  | _ => false

def ticksIn : List KEvent → Nat
  | [] => 0
  | ev :: evs => (if isTick ev then 1 else 0) + ticksIn evs

/-- The event replaces domain `p`'s scheduling context. -/
def reconfigures (p : PdId) : KEvent → Bool
  | .syscall _ (.schedConfigure _ t _ _) => t == p
  | _ => false

/-- The ticks of the trace during which domain `p` ran. -/
def ranCount (p : PdId) : KState → List KEvent → Nat
  | _, [] => 0
  | k, ev :: evs => (if ranAt k p ev then 1 else 0) + ranCount p (kstep k ev) evs

theorem ksyscall_sched {k k' : KState} {pd p : PdId} {call : Syscall}
    (h : ksyscall k pd call = some k') (hr : reconfigures p (.syscall pd call) = false) :
    k'.now = k.now ∧ k'.scs[p]? = k.scs[p]? := by
  cases call with
  | schedConfigure ctl t b per =>
    simp only [ksyscall] at h
    split at h
    · split at h
      · cases h
        simp only [reconfigures, beq_eq_false_iff_ne, ne_eq] at hr
        refine ⟨rfl, ?_⟩
        show (k.scs.setIfInBounds t _)[p]? = _
        rw [Array.getElem?_setIfInBounds]
        simp only [hr, ↓reduceIte]
      · cases h
    · cases h
  | mint src dst cap =>
    simp only [ksyscall] at h
    repeat' (split at h)
    all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h
  | delete slot =>
    simp only [ksyscall] at h
    repeat' (split at h)
    all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h
  | revoke slot =>
    simp only [ksyscall] at h
    repeat' (split at h)
    all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h
  | map sp authSlot frameSlot vpage pfn w =>
    simp only [ksyscall] at h
    repeat' (split at h)
    all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h
  | unmap sp vpage =>
    simp only [ksyscall] at h
    cases h; exact ⟨rfl, rfl⟩

theorem tickSched_other {k : KState} {p q : PdId} (hq : ¬ q = p) :
    (tickSched k q)[p]? = k.scs[p]? := by
  unfold tickSched
  split
  · rw [Array.getElem?_setIfInBounds]
    simp only [hq, ↓reduceIte]
  · rfl

theorem tickSched_self {k : KState} {p : PdId} {sc : SchedContext} (hsc : k.scs[p]? = some sc) :
    (tickSched k p)[p]? = some ((sc.charge k.now).getD sc) := by
  have hlt : p < k.scs.size := (Array.getElem?_eq_some_iff.mp hsc).1
  cases hc : sc.charge k.now with
  | none => simp [tickSched, hsc, hc]
  | some sc' =>
    rw [show tickSched k p = k.scs.setIfInBounds p sc' by simp [tickSched, hsc, hc]]
    simp [hlt]

/-- What one event does to domain `p`'s scheduling context. -/
theorem kstep_sched {k : KState} {p : PdId} {sc : SchedContext} (ev : KEvent)
    (hsc : k.scs[p]? = some sc) (hr : reconfigures p ev = false) :
    (isTick ev = false ∧ ranAt k p ev = false ∧ (kstep k ev).now = k.now ∧
        (kstep k ev).scs[p]? = some sc) ∨
      (isTick ev = true ∧ (kstep k ev).now = k.now + 1 ∧
        ((ranAt k p ev = false ∧ (kstep k ev).scs[p]? = some sc) ∨
          (ranAt k p ev = true ∧ ∃ sc', sc.charge k.now = some sc' ∧
            (kstep k ev).scs[p]? = some sc'))) := by
  have hlt : p < k.scs.size := (Array.getElem?_eq_some_iff.mp hsc).1
  cases ev with
  | syscall pd call =>
    left
    cases hk : ksyscall k pd call with
    | some k' =>
      obtain ⟨h1, h2⟩ := ksyscall_sched hk hr
      have e : kstep k (.syscall pd call) = k' := by simp [kstep, hk]
      rw [e]
      exact ⟨rfl, rfl, h1, h2.trans hsc⟩
    | none =>
      have e : kstep k (.syscall pd call) = k := by simp [kstep, hk]
      rw [e]
      exact ⟨rfl, rfl, rfl, hsc⟩
  | pdWrite pd va val =>
    exact .inl ⟨rfl, rfl, (storeVia_frame ..).2.2.2, by
      show (storeVia k (.cpu pd) va val).scs[p]? = _
      rw [(storeVia_frame ..).2.2.1]; exact hsc⟩
  | pdCopy pd s d len =>
    exact .inl ⟨rfl, rfl, (copyVia_frame ..).2.2.2, by
      show (copyVia k pd s d len).scs[p]? = _
      rw [(copyVia_frame ..).2.2.1]; exact hsc⟩
  | dma sid iova val =>
    exact .inl ⟨rfl, rfl, (storeVia_frame ..).2.2.2, by
      show (storeVia k (.dev sid) iova val).scs[p]? = _
      rw [(storeVia_frame ..).2.2.1]; exact hsc⟩
  | tick run =>
    right
    refine ⟨rfl, rfl, ?_⟩
    cases run with
    | none => exact .inl ⟨rfl, hsc⟩
    | some q =>
      have hstep : (kstep k (.tick (some q))).scs = tickSched k q := rfl
      rw [hstep]
      by_cases hq : q = p
      · subst hq
        have hself := tickSched_self hsc
        cases hc : sc.charge k.now with
        | none =>
          left
          rw [hc] at hself
          exact ⟨by simp [ranAt, hsc, hc], hself⟩
        | some sc' =>
          right
          rw [hc] at hself
          exact ⟨by simp [ranAt, hsc, hc], sc', rfl, hself⟩
      · left
        exact ⟨by simp [ranAt, hq], (tickSched_other hq).trans hsc⟩

theorem ranCount_le_window {p : PdId} (evs : List KEvent) :
    ∀ (k : KState) (sc : SchedContext) (r : Nat), k.scs[p]? = some sc → SchedOk sc →
      r < sc.period → (∀ ev ∈ evs, reconfigures p ev = false) →
      ranCount p k evs ≤ availBefore (k.now + (sc.period - r)) sc.refills +
        (r + ticksIn evs) / sc.period * sc.budget := by
  induction evs with
  | nil => intro k sc r _ _ _ _; simp [ranCount]
  | cons ev evs ih =>
    intro k sc r hsc hok hr hno
    have hno' : ∀ e ∈ evs, reconfigures p e = false :=
      fun e he => hno e (List.mem_cons_of_mem _ he)
    simp only [ranCount, ticksIn]
    rcases kstep_sched ev hsc (hno ev List.mem_cons_self) with
      ⟨ht, hran, hnow, hsc'⟩ | ⟨ht, hnow, hcase⟩
    · have h := ih (kstep k ev) sc r hsc' hok hr hno'
      rw [hnow] at h
      simp only [hran, ht, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact h
    · simp only [ht, ↓reduceIte]
      by_cases hr1 : r + 1 < sc.period
      · have e1 : k.now + 1 + (sc.period - (r + 1)) = k.now + (sc.period - r) := by omega
        have e2 : r + 1 + ticksIn evs = r + (1 + ticksIn evs) := by omega
        rcases hcase with ⟨hran, hsc'⟩ | ⟨hran, sc', hch, hsc'⟩
        · have h := ih (kstep k ev) sc (r + 1) hsc' hok hr1 hno'
          rw [hnow, e1, e2] at h
          simp only [hran, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          exact h
        · obtain ⟨hb, hp, t, htl, heq⟩ := charge_some hch
          have h := ih (kstep k ev) sc' (r + 1) hsc' (charge_schedOk hok hch) (hp ▸ hr1) hno'
          rw [hnow, hp, hb, e1, e2] at h
          have h3 := heq (k.now + (sc.period - r))
          have c1 : t < k.now + (sc.period - r) := by omega
          have c2 : ¬ k.now + sc.period < k.now + (sc.period - r) := by omega
          simp only [c1, c2, ↓reduceIte, Nat.add_zero] at h3
          simp only [hran, ↓reduceIte]
          omega
      · have hT : r + 1 = sc.period := by omega
        have hdiv : (r + (1 + ticksIn evs)) / sc.period = ticksIn evs / sc.period + 1 := by
          rw [show r + (1 + ticksIn evs) = ticksIn evs + sc.period by omega]
          exact Nat.add_div_right _ hok.1
        rw [hdiv, Nat.add_mul, Nat.one_mul]
        rcases hcase with ⟨hran, hsc'⟩ | ⟨hran, sc', hch, hsc'⟩
        · have h := ih (kstep k ev) sc 0 hsc' hok hok.1 hno'
          simp only [Nat.zero_add, Nat.sub_zero] at h
          have hcap := hok.2 ((kstep k ev).now + sc.period)
          simp only [hran, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          omega
        · obtain ⟨hb, hp, t, htl, heq⟩ := charge_some hch
          have hok' := charge_schedOk hok hch
          have h := ih (kstep k ev) sc' 0 hsc' hok' hok'.1 hno'
          simp only [Nat.zero_add, Nat.sub_zero] at h
          have hcap := hok'.2 ((kstep k ev).now + sc'.period)
          rw [hp, hb] at h
          rw [hp, hb] at hcap
          have h3 := heq (k.now + (sc.period - r))
          have c1 : t < k.now + (sc.period - r) := by omega
          have c2 : ¬ k.now + sc.period < k.now + (sc.period - r) := by omega
          simp only [c1, c2, ↓reduceIte, Nat.add_zero] at h3
          simp only [hran, ↓reduceIte]
          omega

/-- **Temporal isolation.** Take any state in which domain `p`'s context is well formed, and any
trace from it that does not reconfigure that context. However the scheduler and the domain
behave (offered the processor on every tick, never yielding), the ticks `p` runs are at most
`⌈ΔT / period⌉ · budget + budget`, where `ΔT` is the number of ticks in the trace. -/
theorem mcs_temporal_isolation_bound {k : KState} {p : PdId} {sc : SchedContext}
    (hsc : k.scs[p]? = some sc) (hok : SchedOk sc) (evs : List KEvent)
    (hno : ∀ ev ∈ evs, reconfigures p ev = false) :
    ranCount p k evs ≤ (ticksIn evs + sc.period - 1) / sc.period * sc.budget + sc.budget := by
  have h := ranCount_le_window (p := p) evs k sc 0 hsc hok hok.1 hno
  simp only [Nat.zero_add, Nat.sub_zero] at h
  have h1 := hok.2 (k.now + sc.period)
  have h2 : ticksIn evs / sc.period * sc.budget ≤
      (ticksIn evs + sc.period - 1) / sc.period * sc.budget :=
    Nat.mul_le_mul_right _ (Nat.div_le_div_right (by have := hok.1; omega))
  omega

/-- Every scheduling context is well formed. -/
def KSched (k : KState) : Prop :=
  ∀ (p : PdId) (sc : SchedContext), k.scs[p]? = some sc → SchedOk sc

/-- **Budgets are conserved.** Charging and refilling never give a context more than its budget,
and a reconfiguration installs a well-formed context. -/
theorem kstep_ksched {k : KState} (h : KSched k) (ev : KEvent) : KSched (kstep k ev) := by
  intro p sc hsc
  cases ev with
  | syscall pd call =>
    cases hk : ksyscall k pd call with
    | none =>
      simp only [kstep, hk, Option.getD_none] at hsc
      exact h p sc hsc
    | some k' =>
      simp only [kstep, hk, Option.getD_some] at hsc
      by_cases hr : reconfigures p (.syscall pd call) = false
      · exact h p sc ((ksyscall_sched hk hr).2 ▸ hsc)
      · cases call with
        | schedConfigure ctl t b per =>
          simp only [ksyscall] at hk
          split at hk
          · split at hk
            · rename_i hc
              cases hk
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              have hsc' : (k.scs.setIfInBounds t ⟨b, per, [⟨k.now, b⟩]⟩)[p]? = some sc := hsc
              rw [Array.getElem?_setIfInBounds] at hsc'
              split at hsc'
              · split at hsc'
                · cases hsc'
                  refine ⟨hc.1.2, fun hz => ?_⟩
                  simp only [availBefore]
                  split <;> omega
                · cases hsc'
              · exact h p sc hsc'
            · cases hk
          · cases hk
        | _ => exact absurd rfl hr
  | pdWrite pd va val =>
    exact h p sc (by
      have : (storeVia k (.cpu pd) va val).scs[p]? = some sc := hsc
      rw [(storeVia_frame ..).2.2.1] at this; exact this)
  | pdCopy pd s d len =>
    exact h p sc (by
      have : (copyVia k pd s d len).scs[p]? = some sc := hsc
      rw [(copyVia_frame ..).2.2.1] at this; exact this)
  | dma sid iova val =>
    exact h p sc (by
      have : (storeVia k (.dev sid) iova val).scs[p]? = some sc := hsc
      rw [(storeVia_frame ..).2.2.1] at this; exact this)
  | tick run =>
    cases run with
    | none => exact h p sc hsc
    | some q =>
      have hsc' : (tickSched k q)[p]? = some sc := hsc
      by_cases hq : q = p
      · subst hq
        cases hq' : k.scs[q]? with
        | none => simp [tickSched, hq'] at hsc'
        | some sc₀ =>
          rw [tickSched_self hq'] at hsc'
          cases hc : sc₀.charge k.now with
          | none =>
            rw [hc] at hsc'
            exact h q sc (hq'.trans hsc')
          | some sc₁ =>
            rw [hc] at hsc'
            cases hsc'
            exact charge_schedOk (h q sc₀ hq') hc
      · exact h p sc ((tickSched_other hq).symm.trans hsc')

theorem runK_ksched {k : KState} (h : KSched k) (evs : List KEvent) : KSched (runK k evs) := by
  induction evs generalizing k with
  | nil => exact h
  | cons ev evs ih => exact ih (kstep_ksched h ev)

/-! ## 2. A private frame, and the copy that precedes verification -/

/-- The object reaches frame `pfn` or edits domain `vpd`'s address space. -/
def guarded (vpd : PdId) (pfn : Nat) (o : CapObj) : Bool :=
  o.touches pfn || o == .pageTableCap vpd

theorem guarded_mono {vpd : PdId} {pfn : Nat} {c p : CapObj} (hw : c.within p = true)
    (hg : guarded vpd pfn c = true) : guarded vpd pfn p = true := by
  cases c <;> cases p <;> simp_all [CapObj.within, guarded, CapObj.touches] <;> omega

/-- Frame `pfn` is private to domain `vpd`: only `vpd` holds a capability that reaches the frame
or edits `vpd`'s address space, and the frame is mapped nowhere but in that address space. -/
def Exclusive (k : KState) (vpd : PdId) (pfn : Nat) : Prop :=
  (∀ i n, capAt k.cspace i = some n → guarded vpd pfn n.cap.obj = true → n.owner = vpd) ∧
    (∀ e ∈ k.maps, e.pfn = pfn → e.space = .cpu vpd)

/-- What every event not run by `vpd` preserves: the kernel invariant, the privacy of the frame,
and that `vpd`'s address space gains no mapping over `k₀`'s. -/
def PrivInv (k₀ : KState) (vpd : PdId) (pfn : Nat) (k : KState) : Prop :=
  KInv k ∧ Exclusive k vpd pfn ∧ ∀ e ∈ k.maps, e.space = .cpu vpd → e ∈ k₀.maps

theorem privInv_step {k₀ k : KState} {vpd : PdId} {pfn : Nat} {ev : KEvent}
    (h : PrivInv k₀ vpd pfn k) (hAdv : ev.actor ≠ some vpd) :
    PrivInv k₀ vpd pfn (kstep k ev) ∧
      ∀ a, a / pageSize = pfn → (kstep k ev).mem a = k.mem a := by
  obtain ⟨hInv, ⟨hCaps, hMaps⟩, hSub⟩ := h
  have hMem : ∀ a, a / pageSize = pfn → (kstep k ev).mem a = k.mem a := by
    intro a ha
    by_cases hne : (kstep k ev).mem a = k.mem a
    · exact hne
    · obtain ⟨sp, e, hsp, he, hes, -, hpfn⟩ := kstep_mem_changed hne
      have hs := hMaps e he (hpfn.trans ha)
      rw [hes] at hs
      exact absurd (space_actor (hs ▸ hsp)) hAdv
  refine ⟨?_, hMem⟩
  rcases kstep_frame k ev with ⟨pd, call, k', rfl, hk, hstep⟩ | ⟨hc, hm⟩
  · rw [hstep]
    have hpd : pd ≠ vpd := fun e => hAdv (by simp [KEvent.actor, e])
    have hE := ksyscall_effect hk
    refine ⟨kinv_syscall hInv hE, ?_⟩
    obtain ⟨-, -, hE⟩ := hE
    rcases hE with ⟨src, n, dst, cap, hn, hown, hle, hcs, hm⟩ | ⟨hS, hm⟩ |
      ⟨hcs, e, hm, hown, -, f, a, hf, hfo, hfobj, -, ha, hao, haobj⟩ | ⟨hcs, hsub⟩
    · refine ⟨⟨?_, hm ▸ hMaps⟩, hm ▸ hSub⟩
      intro i x hx hg
      rw [hcs] at hx
      rcases capAt_mintCap hx with hx | rfl
      · exact hCaps i x hx hg
      · exact absurd ((hCaps src n hn (guarded_mono (Cap.le_iff.mp hle).1 hg)).symm.trans hown)
          (fun e => hpd e.symm)
    · have hin : ∀ e ∈ k'.maps, e ∈ k.maps := fun e he => by
        rw [hm] at he; exact (List.mem_filter.mp he).1
      exact ⟨⟨fun i x hx hg => hCaps i x ((hS hInv.1).1 i x hx) hg,
        fun e he => hMaps e (hin e he)⟩, fun e he => hSub e (hin e he)⟩
    · have hfv : ¬ e.pfn = pfn := fun hp => hpd (hown.symm.trans (hfo.symm.trans
        (hCaps _ f hf (by rw [hfobj, hp]; simp [guarded, CapObj.touches]))))
      have hav : ¬ e.space = .cpu vpd := fun hs => hpd (hown.symm.trans (hao.symm.trans
        (hCaps _ a ha (by rw [haobj, hs]; simp [guarded, Space.authObj]))))
      refine ⟨⟨hcs ▸ hCaps, ?_⟩, ?_⟩
      · intro x hx hp
        rw [hm] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hp hfv
        · exact hMaps x hx hp
      · intro x hx hs
        rw [hm] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hs hav
        · exact hSub x hx hs
    · exact ⟨⟨hcs ▸ hCaps, fun e he => hMaps e (hsub e he)⟩, fun e he => hSub e (hsub e he)⟩
  · refine ⟨?_, ⟨hc ▸ hCaps, hm ▸ hMaps⟩, hm ▸ hSub⟩
    unfold KInv; rw [hc, hm]; exact hInv

theorem privInv_run {k₀ : KState} {vpd : PdId} {pfn : Nat} (evs : List KEvent) :
    ∀ k : KState, PrivInv k₀ vpd pfn k → (∀ ev ∈ evs, ev.actor ≠ some vpd) →
      PrivInv k₀ vpd pfn (runK k evs) ∧
        ∀ a, a / pageSize = pfn → (runK k evs).mem a = k.mem a := by
  induction evs with
  | nil => intro k h _; exact ⟨h, fun _ _ => rfl⟩
  | cons ev evs ih =>
    intro k h hAdv
    obtain ⟨h1, m1⟩ := privInv_step h (hAdv ev List.mem_cons_self)
    obtain ⟨h2, m2⟩ := ih _ h1 (fun e he => hAdv e (List.mem_cons_of_mem _ he))
    exact ⟨h2, fun a ha => (m2 a ha).trans (m1 a ha)⟩

/-- A page of `vpd`'s address space that is still mapped is mapped where it was in `k₀`. -/
theorem priv_translate {k₀ k : KState} {vpd : PdId} {va : Nat} {w₀ w : Bool} {da₀ da : Nat}
    (hU : VUnique k₀.maps) (h₀ : translate k₀.maps (.cpu vpd) va w₀ = some da₀)
    (hSub : ∀ e ∈ k.maps, e.space = .cpu vpd → e ∈ k₀.maps)
    (h : translate k.maps (.cpu vpd) va w = some da) : da = da₀ := by
  obtain ⟨e₀, hl₀, -, rfl⟩ := translate_some h₀
  obtain ⟨e, hl, -, rfl⟩ := translate_some h
  obtain ⟨hmem, hsp, hvp⟩ := lookupMap_some hl
  have h1 := lookupMap_of_mem hU (hSub e hmem hsp)
  rw [hsp, hvp, hl₀] at h1
  cases h1; rfl

/-- The verifier domain's ring: where the shared slot and its private copy sit in its address
space, and the slot length. -/
structure IngressCfg where
  vpd : PdId
  sharedV : Nat
  privV : Nat
  len : Nat

/-- Step one of every turn: copy the shared slot into the private frame. -/
def ingressCopy (cfg : IngressCfg) (k : KState) : KState :=
  kstep k (.pdCopy cfg.vpd cfg.sharedV cfg.privV cfg.len)

/-- The address the dispatcher reads its payload from: the private copy. -/
def dispatchVaddr (cfg : IngressCfg) : Nat := cfg.privV

def readPhys (mem : Nat → UInt8) (pa len : Nat) : ByteArray :=
  bytesOfList ((List.range len).map fun i => mem (pa + i))

/-- What domain `pd` reads at `va`: `len` bytes inside one mapped page. -/
def readVia (k : KState) (pd : PdId) (va len : Nat) : Option ByteArray :=
  if va % pageSize + len ≤ pageSize then
    (translate k.maps (.cpu pd) va false).map fun pa => readPhys k.mem pa len
  else none

theorem readVia_some {k : KState} {pd : PdId} {va len : Nat} {b : ByteArray}
    (h : readVia k pd va len = some b) :
    va % pageSize + len ≤ pageSize ∧
      ∃ pa, translate k.maps (.cpu pd) va false = some pa ∧ b = readPhys k.mem pa len := by
  unfold readVia at h
  split at h
  · rename_i hfit
    cases ht : translate k.maps (.cpu pd) va false with
    | none => rw [ht] at h; cases h
    | some pa =>
      rw [ht] at h
      exact ⟨hfit, pa, rfl, (Option.some.inj h).symm⟩
  · cases h

/-- **Copy before verify.** `k₀` fixes where the verifier's private page is mapped; `k₁` is any
later state in which that frame is still private. The verifier copies the shared ring slot
(`ring` is what the slot holds at that instant), then every other domain and every device does
anything at all (`mid`), racing writes to the shared ring included. Whatever the verifier then
reads at its dispatch address is `ring`. Checking the private copy at any moment in between reads
the same bytes, so what was verified is what is dispatched. -/
theorem copy_into_private_pd_frame_before_verify {k₀ k₁ : KState} {cfg : IngressCfg}
    {da₀ : Nat} {ring d : ByteArray}
    (hU : VUnique k₀.maps)
    (hP₀ : translate k₀.maps (.cpu cfg.vpd) cfg.privV true = some da₀)
    (hInv : PrivInv k₀ cfg.vpd (da₀ / pageSize) k₁)
    (hRing : readVia k₁ cfg.vpd cfg.sharedV cfg.len = some ring)
    (hCopy : (translate k₁.maps (.cpu cfg.vpd) cfg.privV true).isSome = true)
    (mid : List KEvent) (hAdv : ∀ ev ∈ mid, ev.actor ≠ some cfg.vpd)
    (hD : readVia (runK (ingressCopy cfg k₁) mid) cfg.vpd (dispatchVaddr cfg) cfg.len = some d) :
    d = ring ∧ PrivInv k₀ cfg.vpd (da₀ / pageSize) (runK (ingressCopy cfg k₁) mid) := by
  obtain ⟨hfitS, sa, hsa, rfl⟩ := readVia_some hRing
  obtain ⟨hfitP, da', hda', rfl⟩ := readVia_some hD
  obtain ⟨da, hda⟩ := Option.isSome_iff_exists.mp hCopy
  have e1 : da = da₀ := priv_translate hU hP₀ hInv.2.2 hda
  subst e1
  have hk₂ : ingressCopy cfg k₁ = { k₁ with mem := fun a =>
      if da ≤ a ∧ a < da + cfg.len then k₁.mem (sa + (a - da)) else k₁.mem a } := by
    have hfit : cfg.sharedV % pageSize + cfg.len ≤ pageSize ∧
        cfg.privV % pageSize + cfg.len ≤ pageSize := ⟨hfitS, hfitP⟩
    simp only [ingressCopy, kstep, copyVia, hfit, and_self, ↓reduceIte, hsa, hda]
  have hInv₂ : PrivInv k₀ cfg.vpd (da / pageSize) (ingressCopy cfg k₁) := by
    rw [hk₂]; exact hInv
  obtain ⟨hInv₃, hMem⟩ := privInv_run mid _ hInv₂ hAdv
  have e2 : da' = da := priv_translate hU hP₀ hInv₃.2.2 hda'
  subst e2
  refine ⟨?_, hInv₃⟩
  obtain ⟨e, -, -, hpa⟩ := translate_some hP₀
  unfold readPhys
  refine congrArg bytesOfList (List.map_congr_left fun i hi => ?_)
  have hi' := List.mem_range.mp hi
  have hpage : (da' + i) / pageSize = da' / pageSize := by
    have := hfitP
    simp only [dispatchVaddr] at this
    unfold pageSize at *
    omega
  rw [hMem _ hpage, hk₂]
  have hin : da' ≤ da' + i ∧ da' + i < da' + cfg.len := ⟨by omega, by omega⟩
  simp only [hin, and_self, ↓reduceIte]
  congr 1
  omega
/-! ## 3. The verifier loop: kernel, outbox and powerbox, turn after turn -/

theorem runK_append (k : KState) (a b : List KEvent) : runK k (a ++ b) = runK (runK k a) b := by
  induction a generalizing k with
  | nil => rfl
  | cons ev evs ih => exact ih (kstep k ev)

/-- One turn of the verifier domain's loop. -/
structure VerifierTurn where
  /-- What every other domain and every device does before the copy. -/
  pre : List KEvent
  /-- What they do between the copy and the dispatch. -/
  mid : List KEvent
  /-- The shared ring slot at the copy instant. -/
  ringAtCopy : ByteArray
  /-- The consensus advance and the request handed to the outbox gatekeeper. -/
  out : OutboxTurn
  /-- The client grain and the capability slot it invokes for this request. -/
  grain : GrainId
  slot : Nat
  need : UInt64

structure LoopState where
  kernel : KState
  sent : Sent
  outbox : OutboxState
  host : PowerboxHost

/-- The kernel at the copy instant of turn `t`. -/
def copyState (k : KState) (t : VerifierTurn) : KState := runK k t.pre

/-- The kernel when turn `t` dispatches. -/
def dispatchState (cfg : IngressCfg) (k : KState) (t : VerifierTurn) : KState :=
  runK (ingressCopy cfg (copyState k t)) t.mid

/-- The powerbox turn of `t`: the grain invokes its capability on the request bytes. -/
def invokeOf (t : VerifierTurn) : PowerboxTurn :=
  .invoke t.grain t.slot t.need t.out.req.spsc.sharedRingBeforeCopy

/-- Every kernel event of a run of the loop, in order. -/
def loopEvents (cfg : IngressCfg) : List VerifierTurn → List KEvent
  | [] => []
  | t :: ts =>
    t.pre ++ .pdCopy cfg.vpd cfg.sharedV cfg.privV cfg.len :: (t.mid ++ loopEvents cfg ts)

/-- A run of the verifier loop. In each turn the other domains and devices act (`pre`), the
verifier copies the ring slot, they act again (`mid`), and then the verifier hands the gatekeeper
a request whose snapshot is what it reads from its private frame at that moment; the powerbox
must accept the grain's invocation of the snapshot, and the outbox must accept the request. -/
def ValidVerifierLoop (P : Protocol) (part : SeL4MicrokitPartition) (cfg : IngressCfg) :
    LoopState → List VerifierTurn → LoopState → Prop
  | s, [], f => f = s ∧ Reach P s.sent ∧ checkMicrokitIsolation part = true
  | s, t :: ts, f =>
    (∀ ev ∈ t.pre, ev.actor ≠ some cfg.vpd) ∧ (∀ ev ∈ t.mid, ev.actor ≠ some cfg.vpd) ∧
    readVia (copyState s.kernel t) cfg.vpd cfg.sharedV cfg.len = some t.ringAtCopy ∧
    (translate (copyState s.kernel t).maps (.cpu cfg.vpd) cfg.privV true).isSome = true ∧
    readVia (dispatchState cfg s.kernel t) cfg.vpd (dispatchVaddr cfg) cfg.len =
      some t.out.req.spsc.sharedRingBeforeCopy ∧
    Reach P s.sent ∧ SentSteps P s.sent t.out.nextSent ∧
    ∃ (h₁ : PowerboxHost) (stMid st₁ : OutboxState),
      stepPowerboxHost s.host (invokeOf t) = some h₁ ∧
      stepOutbox P part t.out.nextSent s.outbox t.out.req = some stMid ∧
      (match t.out.reconcileCert? with
       | none => st₁ = stMid
       | some cert => reconcileEscrowsWithCert P t.out.nextSent cert stMid = some st₁) ∧
      ValidVerifierLoop P part cfg ⟨dispatchState cfg s.kernel t, t.out.nextSent, st₁, h₁⟩ ts f

variable {P : Protocol} {part : SeL4MicrokitPartition} {cfg : IngressCfg}

/-- The outbox's side of a loop run is a valid outbox trace. -/
theorem loop_outboxTrace {turns : List VerifierTurn} {s f : LoopState}
    (h : ValidVerifierLoop P part cfg s turns f) :
    ValidOutboxTrace P part s.sent s.outbox (turns.map (·.out)) f.sent f.outbox := by
  induction turns generalizing s with
  | nil =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨rfl, hr, hi⟩ := h
    exact ⟨rfl, rfl, hr, hi⟩
  | cons t ts ih =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨-, -, -, -, -, hr, hs, h₁, stMid, st₁, -, hstep, hrec, hrest⟩ := h
    exact ⟨hr, hs, stMid, st₁, hstep, hrec, ih hrest⟩

/-- The powerbox's side of a loop run is a valid powerbox trace of invocations. -/
theorem loop_powerboxTrace {turns : List VerifierTurn} {s f : LoopState}
    (h : ValidVerifierLoop P part cfg s turns f) :
    ValidPowerboxTrace s.host (turns.map invokeOf) f.host := by
  induction turns generalizing s with
  | nil =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨rfl, -, -⟩ := h
    rfl
  | cons t ts ih =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨-, -, -, -, -, -, -, h₁, stMid, st₁, hinv, -, -, hrest⟩ := h
    exact ⟨h₁, hinv, ih hrest⟩

/-- The kernel's side of a loop run is one kernel trace. -/
theorem loop_kernel_run {turns : List VerifierTurn} {s f : LoopState}
    (h : ValidVerifierLoop P part cfg s turns f) :
    f.kernel = runK s.kernel (loopEvents cfg turns) := by
  induction turns generalizing s with
  | nil =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨rfl, -, -⟩ := h
    rfl
  | cons t ts ih =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨-, -, -, -, -, -, -, h₁, stMid, st₁, -, -, -, hrest⟩ := h
    rw [ih hrest]
    simp only [loopEvents, runK_append, runK, dispatchState, copyState, ingressCopy]

/-- Through a whole run the private frame stays private, and in every turn the snapshot handed to
the gatekeeper is the ring content at that turn's copy instant. -/
theorem loop_ingress {k₀ : KState} {da₀ : Nat} (hU : VUnique k₀.maps)
    (hP₀ : translate k₀.maps (.cpu cfg.vpd) cfg.privV true = some da₀)
    {turns : List VerifierTurn} {s f : LoopState}
    (hInv : PrivInv k₀ cfg.vpd (da₀ / pageSize) s.kernel)
    (h : ValidVerifierLoop P part cfg s turns f) :
    PrivInv k₀ cfg.vpd (da₀ / pageSize) f.kernel ∧
      ∀ t ∈ turns, t.out.req.spsc.sharedRingBeforeCopy = t.ringAtCopy := by
  induction turns generalizing s with
  | nil =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨hInv, fun _ ht => by cases ht⟩
  | cons t ts ih =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨hpre, hmid, hring, hcopy, hdisp, -, -, h₁, stMid, st₁, -, -, -, hrest⟩ := h
    obtain ⟨hInv₁, -⟩ := privInv_run t.pre s.kernel hInv hpre
    obtain ⟨heq, hInv₃⟩ :=
      copy_into_private_pd_frame_before_verify hU hP₀ hInv₁ hring hcopy t.mid hmid hdisp
    obtain ⟨hF, hall⟩ := ih (s := ⟨dispatchState cfg s.kernel t, t.out.nextSent, st₁, h₁⟩) hInv₃ hrest
    refine ⟨hF, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact heq
    · exact hall x hx

/-- Every turn leaves a powerbox log entry: the grain, and the digest of the request bytes. -/
theorem loop_audit {turns : List VerifierTurn} {s f : LoopState}
    (h : ValidVerifierLoop P part cfg s turns f) :
    ∀ t ∈ turns, ∃ entry ∈ f.host.audit, entry.whoInvoked = .grain t.grain ∧
      entry.actionDigest = actionDigest t.out.req.spsc.sharedRingBeforeCopy := by
  induction turns generalizing s with
  | nil => intro t ht; cases ht
  | cons t ts ih =>
    simp only [ValidVerifierLoop] at h
    obtain ⟨-, -, -, -, -, -, -, h₁, stMid, st₁, hinv, -, -, hrest⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨c, -, -, rfl⟩ := step_invoke hinv
      have hext := trace_ext (loop_powerboxTrace hrest)
      exact ⟨_, hext.audit _ List.mem_cons_self, rfl, rfl⟩
    · exact ih hrest x hx

/-- **The verifier loop is safe.** Start with a well-formed kernel in which the verifier's
private page is mapped writable to a frame private to it, an outbox that has dispatched nothing,
and an accountable powerbox. After any run of the loop, with every other domain and every device
acting arbitrarily in every turn:

1. *Kernel.* The invariant and the frame's privacy hold; every scheduling context is well formed;
   every live capability attenuates one that was live at the start.
2. *Ingress.* Every actuation the outbox dispatched came from a turn of this run, and its payload
   is the content of the shared ring at that turn's copy instant: no write racing the
   verification changed what was dispatched.
3. *Authority.* The powerbox logged an invocation by that turn's grain of exactly the dispatched
   bytes, and the powerbox is still accountable.
4. *Settlement.* The partition is non-interfering, nullifiers are distinct, and every dispatched
   actuation is finalized and is a prefix of every later finalized chain. -/
theorem sel4_microkit_verifier_loop_safe {turns : List VerifierTurn} {s f : LoopState} {da₀ : Nat}
    (hK : KInv s.kernel) (hS : KSched s.kernel)
    (hP₀ : translate s.kernel.maps (.cpu cfg.vpd) cfg.privV true = some da₀)
    (hEx : Exclusive s.kernel cfg.vpd (da₀ / pageSize))
    (hClean : s.outbox.dispatchedActuations = []) (hAcc : Accountable s.host)
    (h : ValidVerifierLoop P part cfg s turns f) :
    (KInv f.kernel ∧ Exclusive f.kernel cfg.vpd (da₀ / pageSize) ∧ KSched f.kernel ∧
      ∀ i n, capAt f.kernel.cspace i = some n →
        ∃ j r, capAt s.kernel.cspace j = some r ∧ n.cap.le r.cap = true) ∧
    Accountable f.host ∧
    Sel4CapDlNonInterfering part ∧
    (f.outbox.dispatchedActuations.map DispatchedActuation.nullifierId).Nodup ∧
    ∀ a ∈ f.outbox.dispatchedActuations,
      Finalized P f.sent a.view a.chain ∧
      (∀ (vCanon : Nat) (cCanon : Chain),
        Finalized P f.sent vCanon cCanon → a.view ≤ vCanon → a.chain <+: cCanon) ∧
      ∃ t ∈ turns, t.out.req.effectClass = .irreversibleActuation ∧
        a.nullifierId = t.out.req.nullifierId ∧ a.dispatchedPayload = t.ringAtCopy ∧
        ∃ entry ∈ f.host.audit, entry.whoInvoked = .grain t.grain ∧
          entry.actionDigest = actionDigest a.dispatchedPayload := by
  obtain ⟨hPriv, hSnap⟩ := loop_ingress hK.2.2 hP₀ ⟨hK, hEx, fun _ he _ => he⟩ h
  have hRun := loop_kernel_run h
  obtain ⟨hIso, -, hNodup, -, hActs, -⟩ :=
    firmament_sel4_copy_before_verify_and_irreversible_outbox_safe hClean (loop_outboxTrace h)
  refine ⟨⟨hPriv.1, hPriv.2.1, hRun ▸ runK_ksched hS _, fun i n hn => ?_⟩,
    trace_accountable hAcc (loop_powerboxTrace h), hIso, hNodup, fun a ha => ?_⟩
  · rw [hRun] at hn
    exact no_authority_amplification_across_syscalls hK _ i n hn
  · obtain ⟨-, hFin, -, ⟨o, ho, hcls, hid, hpay⟩, hCanon⟩ := hActs a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
    obtain ⟨entry, he, hwho, hdig⟩ := loop_audit h t ht
    exact ⟨hFin, hCanon, t, ht, hcls, hid, hpay.trans (hSnap t ht), entry, he, hwho,
      by rw [hdig, hpay]⟩

/-! ## 4. The caller contract of a system call -/

/-- What a caller must hold for the kernel to serve a system call, stated over the capability
space and the mapping table. -/
def SyscallContract (k : KState) (pd : PdId) : Syscall → Prop
  | .mint src dst cap => ∃ n, capAt k.cspace src = some n ∧ n.owner = pd ∧ cap.le n.cap = true ∧
      (dst = pd ∨ n.cap.rights.grant = true)
  | .delete slot => ∃ n, capAt k.cspace slot = some n ∧ n.owner = pd
  | .revoke slot => ∃ n, capAt k.cspace slot = some n ∧ n.owner = pd
  | .map sp authSlot frameSlot vpage pfn w => ∃ a f, capAt k.cspace authSlot = some a ∧
      capAt k.cspace frameSlot = some f ∧ a.owner = pd ∧ f.owner = pd ∧
      a.cap.obj = sp.authObj ∧ a.cap.rights.write = true ∧ f.cap.obj = .frameCap pfn ∧
      f.cap.rights.read = true ∧ (w = false ∨ f.cap.rights.write = true) ∧
      lookupMap k.maps sp vpage = none
  | .unmap _ _ => True
  | .schedConfigure ctl _ budget period => ∃ c, capAt k.cspace ctl = some c ∧ c.owner = pd ∧
      (∃ core, c.cap.obj = .schedControlCap core) ∧ 0 < period ∧ budget ≤ period

theorem isSchedControl_iff (o : CapObj) : o.isSchedControl = true ↔ ∃ core, o = .schedControlCap core := by
  cases o <;> simp [CapObj.isSchedControl]

/-- **The kernel serves exactly the calls that meet the contract.** -/
theorem ksyscall_accepts_iff_contract (k : KState) (pd : PdId) (call : Syscall) :
    (∃ k', ksyscall k pd call = some k') ↔ SyscallContract k pd call := by
  cases call with
  | mint src dst cap =>
    cases hn : capAt k.cspace src <;>
      simp [ksyscall, SyscallContract, hn, mintOk, and_assoc]
  | delete slot =>
    cases hn : capAt k.cspace slot <;> simp [ksyscall, SyscallContract, hn]
  | revoke slot =>
    cases hn : capAt k.cspace slot <;> simp [ksyscall, SyscallContract, hn]
  | map sp authSlot frameSlot vpage pfn w =>
    cases ha : capAt k.cspace authSlot <;> cases hf : capAt k.cspace frameSlot <;>
      simp [ksyscall, SyscallContract, ha, hf, mapOk, and_assoc]
  | unmap sp vpage => simp [ksyscall, SyscallContract]
  | schedConfigure ctl target budget period =>
    cases hc : capAt k.cspace ctl <;>
      simp [ksyscall, SyscallContract, hc, isSchedControl_iff, and_assoc]

/-- **A refused call violated the contract**: the kernel never skips a call it should serve. -/
theorem ksyscall_skip_implies_contract_violation {k : KState} {pd : PdId} {call : Syscall}
    (h : ksyscall k pd call = none) : ¬ SyscallContract k pd call := by
  intro hc
  obtain ⟨k', hk⟩ := (ksyscall_accepts_iff_contract k pd call).mpr hc
  rw [h] at hk; cases hk

/-! ## 5. The premises are inhabited, and checkable -/

/-- Executable check that every node is a root. -/
def allRoots (cs : CSpace) : Bool :=
  (List.range cs.size).all fun i =>
    match nodeAt cs i with
    | some n => n.parent.isNone
    | none => true

theorem allRoots_iff (cs : CSpace) :
    allRoots cs = true ↔ ∀ i n, nodeAt cs i = some n → n.parent = none := by
  unfold allRoots
  rw [List.all_eq_true]
  constructor
  · intro h i n hn
    have hi := h i (List.mem_range.mpr (nodeAt_lt hn))
    rw [hn] at hi
    exact Option.isNone_iff_eq_none.mp hi
  · intro h i _
    cases hn : nodeAt cs i with
    | none => rfl
    | some n => simp [h i n hn]

/-- Executable check of `Exclusive`: one pass over the slots, one over the mappings. -/
def exclusiveB (k : KState) (vpd : PdId) (pfn : Nat) : Bool :=
  ((List.range k.cspace.size).all fun i =>
    match capAt k.cspace i with
    | some n => !guarded vpd pfn n.cap.obj || n.owner == vpd
    | none => true) &&
  k.maps.all fun e => e.pfn != pfn || e.space == .cpu vpd

theorem exclusiveB_iff (k : KState) (vpd : PdId) (pfn : Nat) :
    exclusiveB k vpd pfn = true ↔ Exclusive k vpd pfn := by
  unfold exclusiveB Exclusive
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i n hn hg => ?_, fun e he hp => ?_⟩
    · have hi := h1 i (List.mem_range.mpr (nodeAt_lt (capAt_eq_some.mp hn).1))
      rw [hn] at hi
      simpa [hg] using hi
    · simpa [hp] using h2 e he
  · rintro ⟨h1, h2⟩
    refine ⟨fun i _ => ?_, fun e he => ?_⟩
    · cases hn : capAt k.cspace i with
      | none => rfl
      | some n =>
        cases hg : guarded vpd pfn n.cap.obj
        · simp [hg]
        · simp [h1 i n hn hg]
    · by_cases hp : e.pfn = pfn
      · simp [h2 e he hp]
      · simp [hp]

/-! ## 5b. Inhabitants -/

/-- Any boot image of root capabilities with no mappings satisfies the kernel invariant. -/
theorem kinv_of_roots (cs : CSpace) (mem : Nat → UInt8) (scs : Array SchedContext) (now : Nat)
    (hRoots : ∀ i n, nodeAt cs i = some n → n.parent = none) :
    KInv ⟨cs, [], mem, scs, now⟩ := by
  refine ⟨fun i n hn p hp => ?_, fun _ he => ?_, fun _ ha => ?_⟩
  · rw [hRoots i n hn] at hp; cases hp
  · cases he
  · cases ha

/-- A full context that has not run yet is well formed. -/
theorem schedOk_fresh (budget period now : Nat) (hT : 0 < period) :
    SchedOk ⟨budget, period, [⟨now, budget⟩]⟩ :=
  ⟨hT, fun hz => by simp only [availBefore]; split <;> omega⟩

/-- The empty run is a run, from any reachable consensus state. -/
theorem loop_nil_inhabited (s : LoopState) (hr : Reach P s.sent)
    (hi : checkMicrokitIsolation part = true) : ValidVerifierLoop P part cfg s [] s :=
  ⟨rfl, hr, hi⟩

end Obend.OS.Sel4MicrokitKernel

end
