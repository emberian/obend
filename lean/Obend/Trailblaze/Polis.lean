module
/-
# Obend.Trailblaze.Polis — Organ O3: Polis-Realizability DeOS, Multi-Turn Trace Safety & `seL4` Microkit

Implements the executable Silver workflow, algebraic realizability, isolation, commitment binding,
and stateful multi-turn session safety proofs for Organ O3 (re-exporting Blum `UMem` from
`Obend.Trailblaze.PolisBlum`):
1. **Choice-Free `Asm(P)` Realizability & Pullbacks (`PCA`, `PairedPCA`, `Assembly.trackedPullback`)**:
   - Separates erased existence (`existent : ∀ x, ∃ c, realizes c x` in `Prop`) from computational
     `TrackedMorphism`s (`tracker : P.Code → Option P.Code`, `0 Classical.choice`, `0 Quot.sound`).
   - Upgrades `DeosCapCode` and `evalDeosCapApply` with fuel-bounded `S`-combinator saturation
     (`(S f g) x = (f x) (g x)`, `S K K x = x`) and pairing (`pairCode`, `fstCode`, `sndCode`).
   - Constructs `Assembly.trackedPullback f g` (`pbFst`, `pbSnd`, `trackedPullback_comm`, `pbLift`)
     and **unconditionally proves `regularCoveragePullbackStable`**.
2. **`seL4` Microkit Isolation & Constructive Salted Commitment Binding**:
   - Discharges `checkMicrokitIsolation_implies_capDlNonInterfering` unconditionally (`0` open
     obligations for `Sel4CapDlNonInterfering`).
   - Proves bijective 256-bit preimage framing (`unpack_pack_saltedBidPreimage`) and constructive
     commitment binding (`commitSaltedBid_binding`).
3. **Single-Turn & Stateful Multi-Turn DeOS Safety (`apex_polis_deos_turn_safe`, `apex_polis_deos_trace_safe`)**:
   - Tracks monotonic capability revocation (`revokedCodes` growth & `List.Nodup` anti-replay),
     exact `Mandate` settlement budget conservation, and cross-turn persistent `UMem` chronological
     causality across arbitrary `List (PolisTurn A B)` traces (`ValidTrace`), paired with open-world
     environment completeness (`polisSessionStep_skip_implies_violation`, `polisSessionStep_complete`).
-/
public import Obend.Trailblaze.Obligations
public import Obend.Trailblaze.PolisBlum
public import Obend.Tactic.Tooth

public section
namespace Obend.Trailblaze.Polis
open Obend.Trailblaze
set_option autoImplicit false

private theorem of_bool_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · cases h
  · rfl

/-! ## 1. Choice-Free `Asm(P)` Realizability, `PairedPCA` & Categorical Pullbacks -/

/-- Partial Combinatory Algebra (`PCA`) substrate for choice-free `Asm(P)` realizability,
    requiring both `K`-projection (`K a b = a`) and `S`-combinator identity (`S K K x = x`). -/
structure PCA where
  Code     : Type
  apply    : Code → Code → Option Code
  kComb    : Code
  sComb    : Code
  k_step   : ∀ a b : Code, ∃ ka : Code, apply kComb a = some ka ∧ apply ka b = some a
  skk_step : ∀ x : Code, ∃ sk skk : Code,
    apply sComb kComb = some sk ∧
    apply sk kComb = some skk ∧
    apply skk x = some x

/-- `PCA` equipped with a computational pairing combinator (`pairCode`, `fstCode`, `sndCode`)
    supporting finite limits and pullbacks in `Asm(P)`. -/
structure PairedPCA extends PCA where
  pairCode : Code → Code → Code
  fstCode  : Code
  sndCode  : Code
  fst_step : ∀ a b : Code, apply fstCode (pairCode a b) = some a
  snd_step : ∀ a b : Code, apply sndCode (pairCode a b) = some b

/-- Concrete executable realizer code for DeOS capability, combinator, pairing & settlement turns. -/
inductive DeosCapCode where
  | k
  | k1 (held : DeosCapCode)
  | s
  | s1 (f : DeosCapCode)
  | s2 (f g : DeosCapCode)
  | pairComb
  | pair1 (left : DeosCapCode)
  | pair (left right : DeosCapCode)
  | fst
  | snd
  | capToken (pdId : Nat) (rightsMask : Nat) (epoch : Nat)
  | settledSeat (seatId : Nat) (payoutAmount : Nat)
  deriving DecidableEq, Repr

/-- Fuel-bounded partial combinator evaluation on `DeosCapCode`, implementing genuine `S`-combinator
    saturation `(.s2 f g) x ↦ (f x) (g x)`, `K`-projection, pairing, and capability settlement. -/
def evalDeosCapApplyFuel : Nat → DeosCapCode → DeosCapCode → Option DeosCapCode
  | 0, _, _ => none
  | _ + 1, .k, a => some (.k1 a)
  | _ + 1, .k1 a, _b => some a
  | _ + 1, .s, f => some (.s1 f)
  | _ + 1, .s1 f, g => some (.s2 f g)
  | fuel + 1, .s2 f g, x =>
      match evalDeosCapApplyFuel fuel f x, evalDeosCapApplyFuel fuel g x with
      | some fx, some gx => evalDeosCapApplyFuel fuel fx gx
      | _, _ => none
  | _ + 1, .pairComb, a => some (.pair1 a)
  | _ + 1, .pair1 a, b => some (.pair a b)
  | _ + 1, .fst, .pair a _b => some a
  | _ + 1, .snd, .pair _a b => some b
  | _ + 1, .capToken pdId rights epoch, .settledSeat _seatId amt =>
      if rights > 0 then some (.settledSeat pdId (amt + epoch)) else none
  | _ + 1, _, _ => none

/-- Default bounded combinator application (`16` reduction steps) for `deosCapPCA`. -/
def evalDeosCapApply : DeosCapCode → DeosCapCode → Option DeosCapCode :=
  evalDeosCapApplyFuel 16

/-- General `S`-combinator saturation law `(S f g) x = (f x) (g x)` at fuel `fuel + 1`. -/
theorem evalDeosCapApplyFuel_s2
    (fuel : Nat) (f g x fx gx out : DeosCapCode)
    (hFx : evalDeosCapApplyFuel fuel f x = some fx)
    (hGx : evalDeosCapApplyFuel fuel g x = some gx)
    (hOut : evalDeosCapApplyFuel fuel fx gx = some out) :
    evalDeosCapApplyFuel (fuel + 1) (.s2 f g) x = some out := by
  simp [evalDeosCapApplyFuel, hFx, hGx, hOut]

/-- Concrete executable `PCA` over `DeosCapCode`. -/
@[expose] def deosCapPCA : PCA where
  Code := DeosCapCode
  apply := evalDeosCapApply
  kComb := .k
  sComb := .s
  k_step := by
    intro a _b
    refine ⟨.k1 a, ?_, ?_⟩ <;> rfl
  skk_step := by
    intro _x
    refine ⟨.s1 .k, .s2 .k .k, ?_, ?_, ?_⟩ <;> rfl

instance : DecidableEq deosCapPCA.Code := inferInstanceAs (DecidableEq DeosCapCode)

/-- Concrete executable `PairedPCA` over `DeosCapCode`. -/
@[expose] def deosCapPairedPCA : PairedPCA where
  toPCA := deosCapPCA
  pairCode := .pair
  fstCode := .fst
  sndCode := .snd
  fst_step := by
    intro _a _b
    rfl
  snd_step := by
    intro _a _b
    rfl

/-- An Assembly `A ∈ Asm(P)` over `P : PCA`: `existent` lives purely in `Prop` so computation never
    branches on erased witnesses. -/
structure Assembly (P : PCA) where
  Carrier  : Type
  realizes : P.Code → Carrier → Prop
  existent : ∀ x : Carrier, ∃ c : P.Code, realizes c x

/-- Choice-free morphism in `Asm(P)`: carries an explicit executable `tracker : P.Code → Option P.Code`
    that computes directly in `Type` with zero `Quot.sound` or `Classical.choice` casts. -/
structure TrackedMorphism {P : PCA} (A B : Assembly P) where
  map     : A.Carrier → B.Carrier
  tracker : P.Code → Option P.Code
  tracks  : ∀ (c : P.Code) (x : A.Carrier),
    A.realizes c x → ∃ c' : P.Code, tracker c = some c' ∧ B.realizes c' (map x)

/-- Extensionality for `TrackedMorphism`: determined uniquely by `map` and `tracker` (`tracks` is proof-irrelevant). -/
@[ext] theorem TrackedMorphism.ext {P : PCA} {A B : Assembly P}
    {f g : TrackedMorphism A B}
    (hMap : f.map = g.map)
    (hTracker : f.tracker = g.tracker) :
    f = g := by
  cases f
  cases g
  cases hMap
  cases hTracker
  rfl

/-- Identity `TrackedMorphism` in `Asm(P)`. -/
def TrackedMorphism.id {P : PCA} (A : Assembly P) : TrackedMorphism A A where
  map := fun x => x
  tracker := fun c => some c
  tracks := fun c _x hReal => ⟨c, rfl, hReal⟩

/-- Composition of `TrackedMorphism`s in `Asm(P)`, chaining `Option.bind` on raw realizer codes. -/
def TrackedMorphism.comp {P : PCA} {A B C : Assembly P}
    (g : TrackedMorphism B C) (f : TrackedMorphism A B) : TrackedMorphism A C where
  map := fun x => g.map (f.map x)
  tracker := fun c => (f.tracker c).bind g.tracker
  tracks := by
    intro c x hA
    rcases f.tracks c x hA with ⟨c₁, hf, hB⟩
    rcases g.tracks c₁ (f.map x) hB with ⟨c₂, hg, hC⟩
    refine ⟨c₂, ?_, hC⟩
    rw [hf]
    exact hg

/-- Left identity law in `Asm(P)`: `(id B).comp f = f`. -/
theorem TrackedMorphism.id_comp {P : PCA} {A B : Assembly P}
    (f : TrackedMorphism A B) :
    (TrackedMorphism.id B).comp f = f := by
  apply TrackedMorphism.ext
  · rfl
  · funext c
    dsimp only [comp, id]
    cases f.tracker c <;> rfl

/-- Right identity law in `Asm(P)`: `f.comp (id A) = f`. -/
theorem TrackedMorphism.comp_id {P : PCA} {A B : Assembly P}
    (f : TrackedMorphism A B) :
    f.comp (TrackedMorphism.id A) = f := by
  apply TrackedMorphism.ext <;> rfl

/-- Associativity law in `Asm(P)`: `(h.comp g).comp f = h.comp (g.comp f)`. -/
theorem TrackedMorphism.comp_assoc {P : PCA} {A B C D : Assembly P}
    (h : TrackedMorphism C D) (g : TrackedMorphism B C) (f : TrackedMorphism A B) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply TrackedMorphism.ext
  · rfl
  · funext c
    dsimp only [comp]
    cases f.tracker c <;> rfl

/-- **Choice-Free Categorical Pullback `A ×_C B` in `Asm(P)`**:
    Carries pairs `(a, b)` with `f.map a = g.map b` realized by `P.pairCode ca cb`. -/
@[expose] def Assembly.trackedPullback {P : PairedPCA} {A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C) : Assembly P.toPCA where
  Carrier := { p : A.Carrier × B.Carrier // f.map p.1 = g.map p.2 }
  realizes := fun code w =>
    ∃ ca cb : P.Code,
      code = P.pairCode ca cb ∧
      A.realizes ca w.val.1 ∧
      B.realizes cb w.val.2
  existent := by
    rintro ⟨⟨a, b⟩, _hEq⟩
    rcases A.existent a with ⟨ca, hA⟩
    rcases B.existent b with ⟨cb, hB⟩
    exact ⟨P.pairCode ca cb, ca, cb, rfl, hA, hB⟩

/-- First pullback projection `pbFst : A ×_C B → A`, tracked computationally by `P.fstCode`. -/
def Assembly.pbFst {P : PairedPCA} {A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C) :
    TrackedMorphism (Assembly.trackedPullback f g) A where
  map := fun w => w.val.1
  tracker := fun code => P.apply P.fstCode code
  tracks := by
    rintro c w ⟨ca, cb, rfl, hA, _hB⟩
    exact ⟨ca, P.fst_step ca cb, hA⟩

/-- Second pullback projection `pbSnd : A ×_C B → B`, tracked computationally by `P.sndCode`. -/
def Assembly.pbSnd {P : PairedPCA} {A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C) :
    TrackedMorphism (Assembly.trackedPullback f g) B where
  map := fun w => w.val.2
  tracker := fun code => P.apply P.sndCode code
  tracks := by
    rintro c w ⟨ca, cb, rfl, _hA, hB⟩
    exact ⟨cb, P.snd_step ca cb, hB⟩

/-- Pullback square commutativity: `(f ∘ pbFst).map = (g ∘ pbSnd).map`. -/
theorem Assembly.trackedPullback_comm {P : PairedPCA} {A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C) :
    (f.comp (Assembly.pbFst f g)).map = (g.comp (Assembly.pbSnd f g)).map := by
  funext w
  exact w.property

/-- Universal mediating `TrackedMorphism` `pbLift : X → A ×_C B` for any cone `(hA, hB)` with
    `f ∘ hA = g ∘ hB`, pairing realized outputs via `P.pairCode` with zero choice axioms. -/
def Assembly.pbLift {P : PairedPCA} {X A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C)
    (hA : TrackedMorphism X A) (hB : TrackedMorphism X B)
    (hComm : ∀ x : X.Carrier, f.map (hA.map x) = g.map (hB.map x)) :
    TrackedMorphism X (Assembly.trackedPullback f g) where
  map := fun x => ⟨(hA.map x, hB.map x), hComm x⟩
  tracker := fun c =>
    match hA.tracker c, hB.tracker c with
    | some ca, some cb => some (P.pairCode ca cb)
    | _, _ => none
  tracks := by
    intro c x hX
    rcases hA.tracks c x hX with ⟨ca, hTrkA, hRealA⟩
    rcases hB.tracks c x hX with ⟨cb, hTrkB, hRealB⟩
    refine ⟨P.pairCode ca cb, ?_, ca, cb, rfl, hRealA, hRealB⟩
    simp [hTrkA, hTrkB]

/-- First universal pullback triangle: `(pbFst ∘ pbLift).map = hA.map`. -/
theorem Assembly.pbFst_comp_pbLift_map {P : PairedPCA} {X A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C)
    (hA : TrackedMorphism X A) (hB : TrackedMorphism X B)
    (hComm : ∀ x : X.Carrier, f.map (hA.map x) = g.map (hB.map x)) :
    ((Assembly.pbFst f g).comp (Assembly.pbLift f g hA hB hComm)).map = hA.map := by
  unfold TrackedMorphism.comp pbFst pbLift
  rfl

/-- Second universal pullback triangle: `(pbSnd ∘ pbLift).map = hB.map`. -/
theorem Assembly.pbSnd_comp_pbLift_map {P : PairedPCA} {X A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C)
    (hA : TrackedMorphism X A) (hB : TrackedMorphism X B)
    (hComm : ∀ x : X.Carrier, f.map (hA.map x) = g.map (hB.map x)) :
    ((Assembly.pbSnd f g).comp (Assembly.pbLift f g hA hB hComm)).map = hB.map := by
  unfold TrackedMorphism.comp pbSnd pbLift
  rfl

/-- Uniqueness of the universal pullback mediator on underlying carrier maps. -/
theorem Assembly.pbLift_map_unique {P : PairedPCA} {X A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C)
    (hA : TrackedMorphism X A) (hB : TrackedMorphism X B)
    (hComm : ∀ x : X.Carrier, f.map (hA.map x) = g.map (hB.map x))
    (u : TrackedMorphism X (Assembly.trackedPullback f g))
    (hU₁ : ((Assembly.pbFst f g).comp u).map = hA.map)
    (hU₂ : ((Assembly.pbSnd f g).comp u).map = hB.map) :
    u.map = (Assembly.pbLift f g hA hB hComm).map := by
  funext x
  have h1 : (u.map x).val.1 = hA.map x := congrFun hU₁ x
  have h2 : (u.map x).val.2 = hB.map x := congrFun hU₂ x
  exact Subtype.ext (Prod.ext h1 h2)

/-- Effective regular epimorphism in `Asm(P)` (van Oosten Prop. 1.5.2): `f : A → C` admits a
    computational realizer-lifting tracker `liftTracker : P.Code → Option P.Code` witnessing
    fiberwise surjectivity on both carriers and realizers. -/
def TrackedMorphism.IsRegularEpi {P : PCA} {A C : Assembly P} (f : TrackedMorphism A C) : Prop :=
  ∃ liftTracker : P.Code → Option P.Code,
    ∀ (cc : P.Code) (z : C.Carrier),
      C.realizes cc z →
      ∃ (ca : P.Code) (x : A.Carrier),
        liftTracker cc = some ca ∧ A.realizes ca x ∧ f.map x = z

/-- **Unconditional Pullback Stability of Regular Covers in `Asm(P)` (`regularCoveragePullbackStable`)**:
    Pulling back any regular epimorphism `f : A → C` along any `g : B → C` in `Asm(P)` over a
    `PairedPCA` yields a regular epimorphism `Assembly.pbSnd f g : A ×_C B → B` with an explicit
    computational realizer lift (`0` choice axioms, `0` open obligations). -/
theorem regularCoveragePullbackStable
    {P : PairedPCA} {A B C : Assembly P.toPCA}
    (f : TrackedMorphism A C) (g : TrackedMorphism B C)
    (hEpi : f.IsRegularEpi) :
    (Assembly.pbSnd f g).IsRegularEpi := by
  rcases hEpi with ⟨liftTracker, hLift⟩
  refine ⟨fun cb =>
    match g.tracker cb with
    | some cc =>
      match liftTracker cc with
      | some ca => some (P.pairCode ca cb)
      | none => none
    | none => none, ?_⟩
  intro cb y hRealB
  rcases g.tracks cb y hRealB with ⟨cc, hTrkG, hRealC⟩
  rcases hLift cc (g.map y) hRealC with ⟨ca, x, hLiftC, hRealA, hMapEq⟩
  refine ⟨P.pairCode ca cb, ⟨(x, y), hMapEq⟩, ?_, ⟨ca, cb, rfl, hRealA, hRealB⟩, rfl⟩
  simp [hTrkG, hLiftC]

/-! ## 2. `seL4` Microkit Isolation, Salted Commitment Binding & `PolisTurn` -/

/-- Physical MMIO aperture mapped into a `seL4` Microkit Protection Domain. -/
structure MmioRegion where
  regionId         : Nat
  basePhysAddr     : Nat
  byteSize         : Nat
  writable         : Bool
  isFocHilWatchdog : Bool
  deriving DecidableEq, Repr

/-- Disjointness of two non-empty physical MMIO address ranges. -/
def mmioRangesDisjoint (r₁ r₂ : MmioRegion) : Bool :=
  decide (0 < r₁.byteSize) &&
  decide (0 < r₂.byteSize) &&
  (decide (r₁.basePhysAddr + r₁.byteSize ≤ r₂.basePhysAddr) ||
   decide (r₂.basePhysAddr + r₂.byteSize ≤ r₁.basePhysAddr))

/-- Membership of physical byte address `physAddr` inside `r`. -/
def mmioContainsAddr (r : MmioRegion) (physAddr : Nat) : Bool :=
  decide (r.basePhysAddr ≤ physAddr) && decide (physAddr < r.basePhysAddr + r.byteSize)

/-- Static `seL4` Microkit Protection Domain (`PD`) with MMIO apertures and untyped cap children. -/
structure ProtectionDomain where
  pdId               : Nat
  name               : String
  mappedMmio         : List MmioRegion
  untypedCapChildren : List Nat
  deriving DecidableEq, Repr

/-- Static SPSC shared-memory IPC channel between two Microkit Protection Domains. -/
structure IpcChannel where
  channelId       : Nat
  srcPd           : Nat
  dstPd           : Nat
  maxPayloadBytes : Nat
  deriving DecidableEq, Repr

/-- Complete `seL4` Microkit system partition for a cyber-physical DeOS node. -/
structure SeL4MicrokitPartition where
  domains      : List ProtectionDomain
  channels     : List IpcChannel
  watchdogPdId : Nat
  deriving DecidableEq, Repr

/-- Check that `domains` is non-empty and has pairwise distinct `pdId`s. -/
def checkDistinctPdIds : List ProtectionDomain → Bool
  | [] => false
  | [d] => !d.name.isEmpty
  | d :: rest =>
    !d.name.isEmpty &&
    rest.all (fun other => d.pdId != other.pdId) &&
    checkDistinctPdIds rest

/-- Check that no two distinct PDs map overlapping physical MMIO when either mapping is writable. -/
def checkNoSharedWritableMmio (domains : List ProtectionDomain) : Bool :=
  domains.all fun d₁ =>
    domains.all fun d₂ =>
      (d₁.pdId == d₂.pdId) ||
      d₁.mappedMmio.all fun r₁ =>
        d₂.mappedMmio.all fun r₂ =>
          (!r₁.writable && !r₂.writable) || mmioRangesDisjoint r₁ r₂

/-- Check that `watchdogPdId` exists, maps a writable `FocHil` watchdog MMIO aperture, and no other
    PD maps any `FocHil` watchdog region. -/
def checkWatchdogConfinement (part : SeL4MicrokitPartition) : Bool :=
  part.domains.any (fun d =>
    (d.pdId == part.watchdogPdId) &&
    d.mappedMmio.any (fun r => r.isFocHilWatchdog && r.writable && decide (0 < r.byteSize))) &&
  part.domains.all (fun d =>
    (d.pdId == part.watchdogPdId) ||
    d.mappedMmio.all (fun r => !r.isFocHilWatchdog))

/-- Check strict topological DAG ordering `parent.pdId < childId` on untyped capability derivation,
    ruling out cyclic capability authority of any length. -/
def checkAcyclicUntypedCaps (domains : List ProtectionDomain) : Bool :=
  domains.all fun d =>
    d.untypedCapChildren.all fun childId =>
      decide (d.pdId < childId) && domains.any (fun c => c.pdId == childId)

/-- Check that every IPC channel connects distinct registered PDs with a bounded `1..4096` byte slot. -/
def checkBoundedIpcChannels (part : SeL4MicrokitPartition) : Bool :=
  part.channels.all fun ch =>
    (ch.srcPd != ch.dstPd) &&
    part.domains.any (fun d => d.pdId == ch.srcPd) &&
    part.domains.any (fun d => d.pdId == ch.dstPd) &&
    decide (0 < ch.maxPayloadBytes) &&
    decide (ch.maxPayloadBytes ≤ 4096)

/-- Constructive named refusal for `SeL4MicrokitPartition` isolation checks. -/
def refuseMicrokitIsolation (part : SeL4MicrokitPartition) : Option String :=
  if !checkDistinctPdIds part.domains then
    some "refused: duplicate-or-empty-pd"
  else if !checkNoSharedWritableMmio part.domains then
    some "refused: shared-writable-mmio"
  else if !checkWatchdogConfinement part then
    some "refused: foc-hil-watchdog-leak"
  else if !checkAcyclicUntypedCaps part.domains then
    some "refused: cyclic-untyped-cap-authority"
  else if !checkBoundedIpcChannels part then
    some "refused: invalid-ipc-channel"
  else
    none

/-- Boolean `seL4` Microkit partition isolation checker. -/
def checkMicrokitIsolation (part : SeL4MicrokitPartition) : Bool :=
  (refuseMicrokitIsolation part).isNone

/-- Soundness of `checkMicrokitIsolation`: guarantees writable MMIO disjointness across distinct PDs,
    exclusive `FocHil` watchdog ownership by `watchdogPdId`, and strictly increasing untyped capability
    derivation IDs (precluding cyclic untyped authority). -/
theorem checkMicrokitIsolation_sound
    (part : SeL4MicrokitPartition)
    (d₁ d₂ : ProtectionDomain)
    (r₁ r₂ : MmioRegion)
    (hIso : checkMicrokitIsolation part = true)
    (hMem₁ : d₁ ∈ part.domains)
    (hMem₂ : d₂ ∈ part.domains)
    (hR₁ : r₁ ∈ d₁.mappedMmio)
    (hR₂ : r₂ ∈ d₂.mappedMmio) :
    ((d₁.pdId ≠ d₂.pdId → (r₁.writable = true ∨ r₂.writable = true) → mmioRangesDisjoint r₁ r₂ = true) ∧
     (r₁.isFocHilWatchdog = true → d₁.pdId = part.watchdogPdId) ∧
     (∀ childId ∈ d₁.untypedCapChildren, d₁.pdId < childId)) := by
  unfold checkMicrokitIsolation refuseMicrokitIsolation at hIso
  split at hIso
  · cases hIso
  · split at hIso
    · cases hIso
    · rename_i hNoSharedNeg
      split at hIso
      · cases hIso
      · rename_i hWdogNeg
        split at hIso
        · cases hIso
        · rename_i hAcycNeg
          have hNoShared : checkNoSharedWritableMmio part.domains = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hNoSharedNeg)
          have hWdog : checkWatchdogConfinement part = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hWdogNeg)
          have hAcyc : checkAcyclicUntypedCaps part.domains = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hAcycNeg)
          refine ⟨?_, ?_, ?_⟩
          · intro hNe hWr
            unfold checkNoSharedWritableMmio at hNoShared
            rw [List.all_eq_true] at hNoShared
            have hPair := hNoShared d₁ hMem₁
            rw [List.all_eq_true] at hPair
            have hD12 := hPair d₂ hMem₂
            have hBeqF : (d₁.pdId == d₂.pdId) = false := beq_false_of_ne hNe
            rw [hBeqF, Bool.false_or, List.all_eq_true] at hD12
            have hReg1 := hD12 r₁ hR₁
            rw [List.all_eq_true] at hReg1
            have hReg2 := hReg1 r₂ hR₂
            rcases hWr with hw1 | hw2
            · rw [hw1] at hReg2
              exact hReg2
            · rw [hw2] at hReg2
              cases hr1 : r₁.writable <;> rw [hr1] at hReg2 <;> exact hReg2
          · intro hIsWdog
            unfold checkWatchdogConfinement at hWdog
            simp only [Bool.and_eq_true, List.all_eq_true] at hWdog
            have hDom := hWdog.2 d₁ hMem₁
            by_cases hEq : d₁.pdId = part.watchdogPdId
            · exact hEq
            · have hBeqF : (d₁.pdId == part.watchdogPdId) = false := beq_false_of_ne hEq
              rw [hBeqF, Bool.false_or, List.all_eq_true] at hDom
              have hNotW := hDom r₁ hR₁
              rw [hIsWdog] at hNotW
              cases hNotW
          · intro childId hChild
            unfold checkAcyclicUntypedCaps at hAcyc
            rw [List.all_eq_true] at hAcyc
            have hChildren := hAcyc d₁ hMem₁
            rw [List.all_eq_true] at hChildren
            have hLt := hChildren childId hChild
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hLt
            exact hLt.1

/-- Declarative `seL4` capDL capability-table non-interference target refined by `SeL4MicrokitPartition`. -/
def Sel4CapDlNonInterfering (part : SeL4MicrokitPartition) : Prop :=
  (∃ wpd ∈ part.domains, wpd.pdId = part.watchdogPdId ∧
    ∃ r ∈ wpd.mappedMmio, r.isFocHilWatchdog = true ∧ r.writable = true ∧ 0 < r.byteSize) ∧
  (∀ d₁ ∈ part.domains, ∀ d₂ ∈ part.domains, d₁.pdId ≠ d₂.pdId →
    ∀ r₁ ∈ d₁.mappedMmio, ∀ r₂ ∈ d₂.mappedMmio,
      (r₁.writable = true ∨ r₂.writable = true) → mmioRangesDisjoint r₁ r₂ = true) ∧
  (∀ ch ∈ part.channels,
    ch.srcPd ≠ ch.dstPd ∧
    (∃ dSrc ∈ part.domains, dSrc.pdId = ch.srcPd) ∧
    (∃ dDst ∈ part.domains, dDst.pdId = ch.dstPd) ∧
    0 < ch.maxPayloadBytes ∧
    ch.maxPayloadBytes ≤ 4096)

/-- **Unconditional `seL4` Microkit capDL Refinement (`checkMicrokitIsolation_implies_capDlNonInterfering`)**:
    Discharges `sel4MicrokitBinaryRefinesSpec` unconditionally from `checkMicrokitIsolation part = true`. -/
theorem checkMicrokitIsolation_implies_capDlNonInterfering
    (part : SeL4MicrokitPartition)
    (hIso : checkMicrokitIsolation part = true) :
    Sel4CapDlNonInterfering part := by
  have hIsoOrig := hIso
  unfold checkMicrokitIsolation refuseMicrokitIsolation at hIso
  split at hIso
  · cases hIso
  · split at hIso
    · cases hIso
    · split at hIso
      · cases hIso
      · rename_i hWdogNeg
        split at hIso
        · cases hIso
        · split at hIso
          · cases hIso
          · rename_i hChanNeg
            have hWdog : checkWatchdogConfinement part = true :=
              of_bool_not_eq_false (Bool.eq_false_iff.mpr hWdogNeg)
            have hChan : checkBoundedIpcChannels part = true :=
              of_bool_not_eq_false (Bool.eq_false_iff.mpr hChanNeg)
            refine ⟨?_, ?_, ?_⟩
            · unfold checkWatchdogConfinement at hWdog
              simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at hWdog
              rcases hWdog.1 with ⟨wpd, hMemW, hIdW, r, hMemR, ⟨hIsFoc, hWrR⟩, hSzR⟩
              exact ⟨wpd, hMemW, hIdW, r, hMemR, hIsFoc, hWrR, hSzR⟩
            · intro d₁ hMem₁ d₂ hMem₂ hNe r₁ hR₁ r₂ hR₂ hWr
              exact (checkMicrokitIsolation_sound part d₁ d₂ r₁ r₂ hIsoOrig hMem₁ hMem₂ hR₁ hR₂).1 hNe hWr
            · unfold checkBoundedIpcChannels at hChan
              rw [List.all_eq_true] at hChan
              intro ch hCh
              have hC := hChan ch hCh
              simp only [Bool.and_eq_true, bne_iff_ne, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at hC
              exact ⟨hC.1.1.1.1, hC.1.1.1.2, hC.1.1.2, hC.1.2, hC.2⟩

/-- Salted dark-bazaar bid opening `(seatId, bidPrice, salt128)`. -/
structure SaltedBidOpening where
  seatId   : BitVec 64
  bidPrice : BitVec 64
  salt128  : BitVec 128
  deriving DecidableEq, Repr

@[ext] theorem SaltedBidOpening.ext {a b : SaltedBidOpening}
    (hSeat : a.seatId = b.seatId)
    (hPrice : a.bidPrice = b.bidPrice)
    (hSalt : a.salt128 = b.salt128) :
    a = b := by
  cases a
  cases b
  cases hSeat
  cases hPrice
  cases hSalt
  rfl

/-- Bijective 256-bit preimage packing for a `SaltedBidOpening` (`seatId` in `[63:0]`,
    `bidPrice` in `[127:64]`, `salt128` in `[255:128]`). -/
def packSaltedBidPreimage (o : SaltedBidOpening) : BitVec 256 :=
  BitVec.ofNat 256
    (o.seatId.toNat +
     18446744073709551616 * o.bidPrice.toNat +
     340282366920938463463374607431768211456 * o.salt128.toNat)

/-- Unpack a 256-bit preimage back into a `SaltedBidOpening`. -/
def unpackSaltedBidPreimage (w : BitVec 256) : SaltedBidOpening where
  seatId   := BitVec.ofNat 64  (w.toNat % 18446744073709551616)
  bidPrice := BitVec.ofNat 64  ((w.toNat / 18446744073709551616) % 18446744073709551616)
  salt128  := BitVec.ofNat 128 (w.toNat / 340282366920938463463374607431768211456)

/-- Exact round-trip bijection `unpackSaltedBidPreimage (packSaltedBidPreimage o) = o`. -/
theorem unpack_pack_saltedBidPreimage (o : SaltedBidOpening) :
    unpackSaltedBidPreimage (packSaltedBidPreimage o) = o := by
  rcases o with ⟨seat, price, salt⟩
  have hSeat : seat.toNat < 18446744073709551616 := seat.isLt
  have hPrice : price.toNat < 18446744073709551616 := price.isLt
  have hSalt : salt.toNat < 340282366920938463463374607431768211456 := salt.isLt
  have hW : (packSaltedBidPreimage ⟨seat, price, salt⟩).toNat =
      seat.toNat + 18446744073709551616 * price.toNat +
      340282366920938463463374607431768211456 * salt.toNat := by
    unfold packSaltedBidPreimage
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  apply SaltedBidOpening.ext
  · apply BitVec.eq_of_toNat_eq
    dsimp only [unpackSaltedBidPreimage]
    rw [BitVec.toNat_ofNat, hW]
    omega
  · apply BitVec.eq_of_toNat_eq
    dsimp only [unpackSaltedBidPreimage]
    rw [BitVec.toNat_ofNat, hW]
    omega
  · apply BitVec.eq_of_toNat_eq
    dsimp only [unpackSaltedBidPreimage]
    rw [BitVec.toNat_ofNat, hW]
    omega

/-- Domain-separated salted bid commitment under a 256-bit cryptographic hash oracle. -/
def commitSaltedBid (hash256 : BitVec 256 → BitVec 256) (o : SaltedBidOpening) : BitVec 256 :=
  hash256 (packSaltedBidPreimage o)

/-- Explicit 256-bit hash collision witness on distinct packed preimages. -/
def HashCollision256 (hash256 : BitVec 256 → BitVec 256) (x y : BitVec 256) : Prop :=
  x ≠ y ∧ hash256 x = hash256 y

/-- **Constructive Computational Commitment Binding (`commitSaltedBid_binding`)**:
    Equal commitments either come from identical `(seatId, bidPrice, salt128)` openings or exhibit a
    concrete 256-bit hash collision (`0` `Classical.choice`, decided constructively). -/
theorem commitSaltedBid_binding
    (hash256 : BitVec 256 → BitVec 256)
    (o₁ o₂ : SaltedBidOpening)
    (hCommitEq : commitSaltedBid hash256 o₁ = commitSaltedBid hash256 o₂) :
    o₁ = o₂ ∨ HashCollision256 hash256 (packSaltedBidPreimage o₁) (packSaltedBidPreimage o₂) := by
  by_cases hEq : o₁ = o₂
  · exact Or.inl hEq
  · refine Or.inr ⟨?_, hCommitEq⟩
    intro hPackEq
    apply hEq
    have hUnpack := congrArg unpackSaltedBidPreimage hPackEq
    rw [unpack_pack_saltedBidPreimage, unpack_pack_saltedBidPreimage] at hUnpack
    exact hUnpack

/-- Cyber-physical viability & ZoE offer-safety envelope for a DeOS turn. -/
structure ViabilityEnvelope where
  lyapunovValMilli    : Nat
  lyapunovCapMilli    : Nat
  focCurrentMilliAmp  : Nat
  maxSafeCurrentMilli : Nat
  escrowWantSatisfied : Bool
  escrowGiveRefunded  : Bool
  deriving DecidableEq, Repr

/-- Executable viability and ZoE offer-safety check. -/
def checkViabilityEnvelope (env : ViabilityEnvelope) : Bool :=
  decide (env.lyapunovValMilli ≤ env.lyapunovCapMilli) &&
  decide (env.focCurrentMilliAmp ≤ env.maxSafeCurrentMilli) &&
  (env.escrowWantSatisfied || env.escrowGiveRefunded)

/-- Parametric `PolisTurn` combining a choice-free `TrackedMorphism`, Blum `UMem` check,
    `SeL4MicrokitPartition` isolation, physical viability envelope, and 256-bit state receipt. -/
structure PolisTurn {P : PCA} (A B : Assembly P) where
  morphism         : TrackedMorphism A B
  inputCode        : P.Code
  onlineMem        : List MemOp
  offlineSortedMem : List MemOp
  partition        : SeL4MicrokitPartition
  viability        : ViabilityEnvelope
  receiptRoot256   : BitVec 256

/-- Constructive named refusal for `PolisTurn` (runs the $O(N \log N)$ `verifyBlumMemoryFast` engine). -/
def refusePolisTurn {P : PCA} {A B : Assembly P} (turn : PolisTurn A B) : Option String :=
  if !(turn.morphism.tracker turn.inputCode).isSome then
    some "refused: tracker-stuck"
  else if !verifyBlumMemoryFast turn.onlineMem.toArray turn.offlineSortedMem.toArray then
    some "refused: blum-memory-mismatch"
  else
    match refuseMicrokitIsolation turn.partition with
    | some reason => some reason
    | none =>
      if !checkViabilityEnvelope turn.viability then
        some "refused: viability-envelope-breach"
      else
        none

/-- Executable Silver gate for a `PolisTurn`. -/
def checkPolisTurn {P : PCA} {A B : Assembly P} (turn : PolisTurn A B) : Bool :=
  (refusePolisTurn turn).isNone

/-! ## 3. External-Oracle `PolisObligations`, Single-Turn & Multi-Turn Trace Safety -/

/-- Peripheral DMA bus write transaction initiated by `srcPd` toward `physAddr`. -/
structure DmaWriteReq where
  srcPd    : Nat
  physAddr : Nat
  payload  : BitVec 64
  deriving DecidableEq, Repr

/-- Whether `physAddr` lies inside a `FocHil` hardware-watchdog MMIO aperture of `part`. -/
def isWatchdogProtectedAddr (part : SeL4MicrokitPartition) (physAddr : Nat) : Bool :=
  part.domains.any fun d =>
    (d.pdId == part.watchdogPdId) &&
    d.mappedMmio.any fun r => r.isFocHilWatchdog && r.writable && mmioContainsAddr r physAddr

/-- Single SMMU-filtered physical DMA bus write step. -/
def stepSmmuDmaBus (part : SeL4MicrokitPartition) (busMem : Nat → BitVec 64) (req : DmaWriteReq) :
    Nat → BitVec 64 :=
  let permitted :=
    part.domains.any fun d =>
      (d.pdId == req.srcPd) &&
      d.mappedMmio.any fun r => r.writable && mmioContainsAddr r req.physAddr
  if permitted then
    fun addr => if addr == req.physAddr then req.payload else busMem addr
  else
    busMem

/-- Replay a trace of SMMU-filtered peripheral DMA writes across the physical bus. -/
def runPhysicalDmaTrace (part : SeL4MicrokitPartition) (initBus : Nat → BitVec 64)
    (trace : List DmaWriteReq) : Nat → BitVec 64 :=
  trace.foldl (stepSmmuDmaBus part) initBus

/-- `Tulva` 256-bit Rényi smudging transcript view over a packed salted bid opening. -/
def tulvaSmudgedView (o : SaltedBidOpening) (smudgeMask : BitVec 256) : BitVec 256 :=
  packSaltedBidPreimage o ^^^ smudgeMask

/-- Manifest of deep external-oracle Wave-4 Golden proof obligations for Organ O3 (`Polis`). -/
def polisObligationManifest : ObligationManifest where
  organ := .o3PolisDeos
  entries :=
    [ { organ := .o3PolisDeos
      , theoremId := "sel4PhysicalDmaBusNonInterference"
      , waveOwner := "wave4-firmament-sel4"
      , externalOracle := "verify_foc_hil.sh"
      , summary := "seL4 SMMU physical DMA bus confinement of FocHil watchdog MMIO" }
    , { organ := .o3PolisDeos
      , theoremId := "darkBazaarRenyiSmudgingHiding"
      , waveOwner := "wave4-darkbazaar-zkfhe"
      , externalOracle := "verify_gpu.sh"
      , summary := "Tulva Renyi smudging transcript hiding across salted dark-bazaar openings" } ]

/-- Explicit `Prop` obligation typeclass packaging Organ O3's remaining external-oracle loops
    (`regularCoveragePullbackStable`, `blumPermutationComplete`, `checkMicrokitIsolation_implies_capDlNonInterfering`,
    and `commitSaltedBid_binding` are all discharged unconditionally). -/
class PolisObligations : Prop where
  /-- `seL4` SMMU physical DMA bus non-interference (`verify_foc_hil.sh`):
      no peripheral DMA trace originating outside `part.watchdogPdId` alters any `FocHil` watchdog word. -/
  sel4PhysicalDmaBusNonInterference :
    ∀ (part : SeL4MicrokitPartition) (initBus : Nat → BitVec 64)
      (trace : List DmaWriteReq) (physAddr : Nat),
      checkMicrokitIsolation part = true →
      isWatchdogProtectedAddr part physAddr = true →
      (∀ req ∈ trace, req.srcPd ≠ part.watchdogPdId) →
      runPhysicalDmaTrace part initBus trace physAddr = initBus physAddr
  /-- `Tulva`/`BitZ` Rényi smudging hiding (`verify_gpu.sh`):
      for any two salted openings on the same auction seat and any smudging mask `mask₁`, there
      exists an indistinguishable twin mask `mask₂` producing the identical smudged transcript view. -/
  darkBazaarRenyiSmudgingHiding :
    ∀ (o₁ o₂ : SaltedBidOpening) (mask₁ : BitVec 256),
      o₁.seatId = o₂.seatId →
      ∃ mask₂ : BitVec 256,
        tulvaSmudgedView o₁ mask₁ = tulvaSmudgedView o₂ mask₂ ∧
        (mask₁ != mask₂) = decide (o₁ ≠ o₂)

private theorem checkPolisTurn_implies_chrono {P : PCA} {A B : Assembly P}
    {turn : PolisTurn A B} (hTurn : checkPolisTurn turn = true) :
    checkChronologicalLog turn.onlineMem = true := by
  unfold checkPolisTurn refusePolisTurn at hTurn
  split at hTurn
  · cases hTurn
  · split at hTurn
    · cases hTurn
    · rename_i _ hBlumNeg
      have hBlumFast : verifyBlumMemoryFast turn.onlineMem.toArray turn.offlineSortedMem.toArray = true :=
        of_bool_not_eq_false (Bool.eq_false_iff.mpr hBlumNeg)
      have hBlum : verifyBlumMemory turn.onlineMem turn.offlineSortedMem = true := by
        rw [← verifyBlumMemoryFast_eq_verifyBlumMemory turn.onlineMem.toArray turn.offlineSortedMem.toArray]
        exact hBlumFast
      exact (verifyBlumMemory_sound turn.onlineMem turn.offlineSortedMem ⟨0, 0, false, 0#64, 0#256⟩ hBlum).2.2.1

/-- **Organ O3 Single-Turn Apex Step Theorem (`apex_polis_deos_turn_safe`)**:
    Certifies choice-free `Asm(P)` tracker output, $O(N \log N)$ Blum `UMem` soundness,
    `Sel4CapDlNonInterfering` + SMMU physical DMA watchdog confinement, and physical/ZoE viability
    on a single `PolisTurn` (paired below with multi-turn `apex_polis_deos_trace_safe`). -/
theorem apex_polis_deos_turn_safe
    [hOb : PolisObligations]
    {P : PCA} {A B : Assembly P}
    (turn : PolisTurn A B)
    (x : A.Carrier)
    (probeOp : MemOp)
    (hReal : A.realizes turn.inputCode x)
    (hTurn : checkPolisTurn turn = true) :
    (∃ outCode : P.Code,
      turn.morphism.tracker turn.inputCode = some outCode ∧
      B.realizes outCode (turn.morphism.map x)) ∧
    turn.onlineMem.length = turn.offlineSortedMem.length ∧
    countMemOp probeOp turn.onlineMem = countMemOp probeOp turn.offlineSortedMem ∧
    checkLocalReadWriteConsistency turn.offlineSortedMem = true ∧
    Sel4CapDlNonInterfering turn.partition ∧
    (∀ (initBus : Nat → BitVec 64) (trace : List DmaWriteReq) (physAddr : Nat),
      isWatchdogProtectedAddr turn.partition physAddr = true →
      (∀ req ∈ trace, req.srcPd ≠ turn.partition.watchdogPdId) →
      runPhysicalDmaTrace turn.partition initBus trace physAddr = initBus physAddr) ∧
    turn.viability.lyapunovValMilli ≤ turn.viability.lyapunovCapMilli ∧
    turn.viability.focCurrentMilliAmp ≤ turn.viability.maxSafeCurrentMilli ∧
    (turn.viability.escrowWantSatisfied = true ∨ turn.viability.escrowGiveRefunded = true) := by
  unfold checkPolisTurn refusePolisTurn at hTurn
  split at hTurn
  · cases hTurn
  · split at hTurn
    · cases hTurn
    · rename_i _hTracker hBlumNeg
      have hBlumFast : verifyBlumMemoryFast turn.onlineMem.toArray turn.offlineSortedMem.toArray = true :=
        of_bool_not_eq_false (Bool.eq_false_iff.mpr hBlumNeg)
      have hBlum : verifyBlumMemory turn.onlineMem turn.offlineSortedMem = true := by
        rw [← verifyBlumMemoryFast_eq_verifyBlumMemory turn.onlineMem.toArray turn.offlineSortedMem.toArray]
        exact hBlumFast
      cases hRefIso : refuseMicrokitIsolation turn.partition with
      | some reason =>
        rw [hRefIso] at hTurn
        cases hTurn
      | none =>
        rw [hRefIso] at hTurn
        dsimp only at hTurn
        split at hTurn
        · cases hTurn
        · rename_i hViabNeg
          have hViab : checkViabilityEnvelope turn.viability = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hViabNeg)
          have hIso : checkMicrokitIsolation turn.partition = true := by
            unfold checkMicrokitIsolation
            rw [hRefIso]
            rfl
          have hBlumSound := verifyBlumMemory_sound turn.onlineMem turn.offlineSortedMem probeOp hBlum
          unfold checkViabilityEnvelope at hViab
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hViab
          exact ⟨turn.morphism.tracks turn.inputCode x hReal,
                 hBlumSound.1,
                 hBlumSound.2.1,
                 hBlumSound.2.2.2.2,
                 checkMicrokitIsolation_implies_capDlNonInterfering turn.partition hIso,
                 fun initBus trace physAddr hProt hNonWdog =>
                   hOb.sel4PhysicalDmaBusNonInterference turn.partition initBus trace physAddr hIso hProt hNonWdog,
                 hViab.1.1,
                 hViab.1.2,
                 hViab.2⟩

/-! ### 3B. Multi-Turn DeOS Session State, `ValidTrace` & Stateful Trace Invariants -/

/-- Persistent multi-turn DeOS session state tracking monotonically growing capability revocations
    (`revokedCodes`), depleting `Mandate` settlement budget (`mandateBudget`), and strictly
    advancing persistent `UMem` causal timestamp horizon (`lastTimestamp`). -/
structure PolisSessionState (Code : Type) where
  revokedCodes  : List Code
  mandateBudget : Nat
  lastTimestamp : Nat
  deriving DecidableEq, Repr

/-- Positive `Mandate` settlement cost expended by `turn` (`|onlineMem| + 1 ≥ 1`). -/
def turnMandateCost {P : PCA} {A B : Assembly P} (turn : PolisTurn A B) : Nat :=
  turn.onlineMem.length + 1

/-- Total `Mandate` settlement cost expended across a multi-turn DeOS trace. -/
def totalTraceMandateCost {P : PCA} {A B : Assembly P} : List (PolisTurn A B) → Nat
  | [] => 0
  | t :: ts => turnMandateCost t + totalTraceMandateCost ts

/-- Check that every online `MemOp` in `ops` occurs strictly after `horizonTs`. -/
def checkMemAfterHorizon (horizonTs : Nat) (ops : List MemOp) : Bool :=
  ops.all fun op => decide (horizonTs < op.timestamp)

/-- Advance persistent `UMem` causal timestamp horizon across `ops`. -/
def advanceMemHorizon (horizonTs : Nat) : List MemOp → Nat
  | [] => horizonTs
  | [op] => op.timestamp
  | _ :: b :: rest => advanceMemHorizon horizonTs (b :: rest)

/-- Concatenated persistent online `UMem` log across an entire multi-turn session trace. -/
def concatTraceOnlineMem {P : PCA} {A B : Assembly P} : List (PolisTurn A B) → List MemOp
  | [] => []
  | t :: ts => t.onlineMem ++ concatTraceOnlineMem ts

/-- Constructive named refusal for a stateful multi-turn DeOS session step. -/
def refusePolisSessionStep {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st : PolisSessionState P.Code) (turn : PolisTurn A B) : Option String :=
  if decide (turn.inputCode ∈ st.revokedCodes) then
    some "refused: revoked-or-replayed-cap"
  else if !decide (turnMandateCost turn ≤ st.mandateBudget) then
    some "refused: mandate-budget-exhausted"
  else if !checkMemAfterHorizon st.lastTimestamp turn.onlineMem then
    some "refused: umem-timestamp-regression"
  else
    refusePolisTurn turn

/-- Execute one stateful DeOS session turn, growing `revokedCodes`, depleting `mandateBudget`,
    and advancing the persistent `UMem` causal timestamp horizon. -/
def stepPolisSession {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st : PolisSessionState P.Code) (turn : PolisTurn A B) : Option (PolisSessionState P.Code) :=
  match refusePolisSessionStep st turn with
  | some _ => none
  | none =>
    some
      { revokedCodes  := turn.inputCode :: st.revokedCodes
      , mandateBudget := st.mandateBudget - turnMandateCost turn
      , lastTimestamp := advanceMemHorizon st.lastTimestamp turn.onlineMem }

/-- Execute an arbitrary multi-turn DeOS trace `List (PolisTurn A B)` from `st`. -/
def runPolisTrace {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st : PolisSessionState P.Code) : List (PolisTurn A B) → Option (PolisSessionState P.Code)
  | [] => some st
  | turn :: rest =>
    match stepPolisSession st turn with
    | none => none
    | some st' => runPolisTrace st' rest

/-- Relational multi-turn trace reachability predicate (`ValidTrace st₀ trace stF`). -/
def ValidTrace {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st₀ : PolisSessionState P.Code) (trace : List (PolisTurn A B))
    (stF : PolisSessionState P.Code) : Prop :=
  runPolisTrace st₀ trace = some stF

/-- Environment anti-narrowing completeness: whenever `stepPolisSession st turn = none`, an
    explicit named refusal is emitted and a concrete session or turn contract is violated. -/
theorem polisSessionStep_skip_implies_violation
    {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st : PolisSessionState P.Code) (turn : PolisTurn A B)
    (hSkip : stepPolisSession st turn = none) :
    (refusePolisSessionStep st turn).isSome = true ∧
    (turn.inputCode ∈ st.revokedCodes ∨
     st.mandateBudget < turnMandateCost turn ∨
     checkMemAfterHorizon st.lastTimestamp turn.onlineMem = false ∨
     checkPolisTurn turn = false) := by
  unfold stepPolisSession at hSkip
  cases hRef : refusePolisSessionStep st turn with
  | none =>
    rw [hRef] at hSkip
    cases hSkip
  | some reason =>
    refine ⟨rfl, ?_⟩
    unfold refusePolisSessionStep at hRef
    split at hRef
    · rename_i hInDec
      exact Or.inl (of_decide_eq_true hInDec)
    · split at hRef
      · rename_i _ hBudNeg
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hBudNeg
        exact Or.inr (Or.inl (by omega))
      · split at hRef
        · rename_i _ _ hHorNeg
          cases hChk : checkMemAfterHorizon st.lastTimestamp turn.onlineMem with
          | false => exact Or.inr (Or.inr (Or.inl rfl))
          | true => rw [hChk] at hHorNeg; cases hHorNeg
        · refine Or.inr (Or.inr (Or.inr ?_))
          unfold checkPolisTurn
          rw [hRef]
          rfl

/-- Converse step completeness: every non-revoked turn within `mandateBudget` and `UMem` causal
    horizon that passes `checkPolisTurn` advances `stepPolisSession` to `some st'`. -/
theorem polisSessionStep_complete
    {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st : PolisSessionState P.Code) (turn : PolisTurn A B)
    (hFresh : turn.inputCode ∉ st.revokedCodes)
    (hBudget : turnMandateCost turn ≤ st.mandateBudget)
    (hHorizon : checkMemAfterHorizon st.lastTimestamp turn.onlineMem = true)
    (hTurn : checkPolisTurn turn = true) :
    ∃ st' : PolisSessionState P.Code, stepPolisSession st turn = some st' := by
  unfold stepPolisSession refusePolisSessionStep
  have hDecFresh : decide (turn.inputCode ∈ st.revokedCodes) = false :=
    decide_eq_false hFresh
  have hDecBud : decide (turnMandateCost turn ≤ st.mandateBudget) = true :=
    decide_eq_true hBudget
  have hRefTurn : refusePolisTurn turn = none := by
    unfold checkPolisTurn at hTurn
    cases hOpt : refusePolisTurn turn with
    | none => rfl
    | some _ =>
      rw [hOpt] at hTurn
      cases hTurn
  rw [hDecFresh, hDecBud, hHorizon, hRefTurn]
  exact ⟨_, rfl⟩

private theorem advanceMemHorizon_ge (h : Nat) (ops : List MemOp)
    (hAfter : checkMemAfterHorizon h ops = true) :
    h ≤ advanceMemHorizon h ops := by
  match ops with
  | [] => exact Nat.le_refl h
  | [op] =>
    unfold checkMemAfterHorizon at hAfter
    simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hAfter
    dsimp only [advanceMemHorizon]
    omega
  | op :: b :: rest =>
    have hTail : checkMemAfterHorizon h (b :: rest) = true := by
      unfold checkMemAfterHorizon at hAfter ⊢
      simp only [List.all_cons, Bool.and_eq_true] at hAfter ⊢
      exact hAfter.2
    exact advanceMemHorizon_ge h (b :: rest) hTail

private theorem mem_ts_le_advanceMemHorizon (h : Nat) (ops : List MemOp)
    (hPw : List.Pairwise (fun a b => a.timestamp < b.timestamp) ops) :
    ∀ z ∈ ops, z.timestamp ≤ advanceMemHorizon h ops := by
  match ops with
  | [] => intro _ hMem; nomatch hMem
  | [op] =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hNil
    · exact Nat.le_refl _
    · nomatch hNil
  | op :: b :: rest =>
    cases hPw with
    | cons hOpLt hTailPw =>
      dsimp only [advanceMemHorizon]
      have ih := mem_ts_le_advanceMemHorizon h (b :: rest) hTailPw
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hzTail
      · have hOpB : z.timestamp < b.timestamp := hOpLt b (List.mem_cons_self ..)
        have hBLe : b.timestamp ≤ advanceMemHorizon h (b :: rest) := ih b (List.mem_cons_self ..)
        omega
      · exact ih z hzTail

private theorem stepPolisSession_dest {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    {st st' : PolisSessionState P.Code} {turn : PolisTurn A B}
    (hStep : stepPolisSession st turn = some st') :
    turn.inputCode ∉ st.revokedCodes ∧
    turnMandateCost turn ≤ st.mandateBudget ∧
    checkMemAfterHorizon st.lastTimestamp turn.onlineMem = true ∧
    checkPolisTurn turn = true ∧
    st' = { revokedCodes := turn.inputCode :: st.revokedCodes
          , mandateBudget := st.mandateBudget - turnMandateCost turn
          , lastTimestamp := advanceMemHorizon st.lastTimestamp turn.onlineMem } := by
  unfold stepPolisSession at hStep
  cases hRef : refusePolisSessionStep st turn with
  | some _ =>
    rw [hRef] at hStep
    cases hStep
  | none =>
    rw [hRef] at hStep
    injection hStep with hEqSt
    unfold refusePolisSessionStep at hRef
    split at hRef
    · cases hRef
    · rename_i hNotRev
      split at hRef
      · cases hRef
      · rename_i hBudgetNeg
        split at hRef
        · cases hRef
        · rename_i hHorNeg
          have hBudget : turnMandateCost turn ≤ st.mandateBudget :=
            of_decide_eq_true (of_bool_not_eq_false (Bool.eq_false_iff.mpr hBudgetNeg))
          have hHor : checkMemAfterHorizon st.lastTimestamp turn.onlineMem = true :=
            of_bool_not_eq_false (Bool.eq_false_iff.mpr hHorNeg)
          have hTurn : checkPolisTurn turn = true := by
            unfold checkPolisTurn
            rw [hRef]
            rfl
          have hFresh : turn.inputCode ∉ st.revokedCodes := by
            intro hIn
            exact hNotRev (decide_eq_true hIn)
          exact ⟨hFresh, hBudget, hHor, hTurn, hEqSt.symm⟩

private theorem mem_concatTraceOnlineMem {P : PCA} {A B : Assembly P}
    {op : MemOp} {trace : List (PolisTurn A B)}
    (hMem : op ∈ concatTraceOnlineMem trace) :
    ∃ t ∈ trace, op ∈ t.onlineMem := by
  induction trace with
  | nil => cases hMem
  | cons t rest ih =>
    dsimp only [concatTraceOnlineMem] at hMem
    rcases List.mem_append.mp hMem with hInT | hInRest
    · exact ⟨t, List.mem_cons_self .., hInT⟩
    · rcases ih hInRest with ⟨t', ht', hop'⟩
      exact ⟨t', List.mem_cons_of_mem t ht', hop'⟩

private theorem validTrace_invariants {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st₀ : PolisSessionState P.Code) (trace : List (PolisTurn A B)) (stF : PolisSessionState P.Code)
    (hValid : ValidTrace st₀ trace stF) :
    (∀ c ∈ st₀.revokedCodes, c ∈ stF.revokedCodes) ∧
    (∀ t ∈ trace, t.inputCode ∈ stF.revokedCodes ∧ t.inputCode ∉ st₀.revokedCodes ∧ checkPolisTurn t = true) ∧
    List.Nodup (trace.map PolisTurn.inputCode) ∧
    stF.mandateBudget + totalTraceMandateCost trace = st₀.mandateBudget ∧
    st₀.lastTimestamp ≤ stF.lastTimestamp ∧
    (∀ t ∈ trace, ∀ op ∈ t.onlineMem, st₀.lastTimestamp < op.timestamp ∧ op.timestamp ≤ stF.lastTimestamp) ∧
    checkChronologicalLog (concatTraceOnlineMem trace) = true := by
  induction trace generalizing st₀ with
  | nil =>
    unfold ValidTrace runPolisTrace at hValid
    injection hValid with hEq
    subst hEq
    exact ⟨fun _ h => h,
           fun _ h => False.elim (List.not_mem_nil h),
           List.Pairwise.nil,
           Nat.add_zero st₀.mandateBudget,
           Nat.le_refl st₀.lastTimestamp,
           fun _ h => False.elim (List.not_mem_nil h),
           (checkChronologicalLog_iff_pairwise []).mpr List.Pairwise.nil⟩
  | cons t rest ih =>
    unfold ValidTrace runPolisTrace at hValid
    cases hStep : stepPolisSession st₀ t with
    | none =>
      rw [hStep] at hValid
      cases hValid
    | some st₁ =>
      rw [hStep] at hValid
      rcases stepPolisSession_dest hStep with ⟨hFreshT, hBudT, hHorT, hTurnT, hSt₁Eq⟩
      rcases ih st₁ hValid with
        ⟨ihRevMono, ihTurns, ihNodup, ihBudget, ihTsMono, ihOpsBounds, ihChronoRest⟩
      have hChronoT : checkChronologicalLog t.onlineMem = true :=
        checkPolisTurn_implies_chrono hTurnT
      have hHorAdv : st₀.lastTimestamp ≤ st₁.lastTimestamp := by
        rw [hSt₁Eq]
        exact advanceMemHorizon_ge st₀.lastTimestamp t.onlineMem hHorT
      refine ⟨?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
      · intro c hc
        apply ihRevMono
        rw [hSt₁Eq]
        exact List.mem_cons_of_mem t.inputCode hc
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | huRest
        · refine ⟨?_, hFreshT, hTurnT⟩
          apply ihRevMono
          rw [hSt₁Eq]
          exact List.mem_cons_self ..
        · rcases ihTurns u huRest with ⟨huInF, huNotSt₁, huOk⟩
          rw [hSt₁Eq] at huNotSt₁
          exact ⟨huInF, fun hIn0 => huNotSt₁ (List.mem_cons_of_mem t.inputCode hIn0), huOk⟩
      · dsimp only [List.map]
        refine List.Pairwise.cons ?_ ihNodup
        intro code hCodeMem hEqCode
        rcases List.mem_map.mp hCodeMem with ⟨u, huRest, rfl⟩
        have huNotSt₁ := (ihTurns u huRest).2.1
        rw [hSt₁Eq, ← hEqCode] at huNotSt₁
        exact huNotSt₁ (List.mem_cons_self ..)
      · dsimp only [totalTraceMandateCost]
        have hBud₁ : st₁.mandateBudget = st₀.mandateBudget - turnMandateCost t := by
          rw [hSt₁Eq]
        omega
      · intro u hu op hop
        rcases List.mem_cons.mp hu with rfl | huRest
        · have hAfterAll := List.all_eq_true.mp hHorT op hop
          simp only [decide_eq_true_eq] at hAfterAll
          have hLe₁ : op.timestamp ≤ st₁.lastTimestamp := by
            rw [hSt₁Eq]
            exact mem_ts_le_advanceMemHorizon st₀.lastTimestamp u.onlineMem
              ((checkChronologicalLog_iff_pairwise _).mp hChronoT) op hop
          exact ⟨hAfterAll, by omega⟩
        · rcases ihOpsBounds u huRest op hop with ⟨hGt₁, hLeF⟩
          exact ⟨by omega, hLeF⟩
      · dsimp only [concatTraceOnlineMem]
        apply checkChronologicalLog_append hChronoT ihChronoRest
        intro op₁ hop₁ op₂ hop₂
        have hLe₁ : op₁.timestamp ≤ st₁.lastTimestamp := by
          rw [hSt₁Eq]
          exact mem_ts_le_advanceMemHorizon st₀.lastTimestamp t.onlineMem
            ((checkChronologicalLog_iff_pairwise _).mp hChronoT) op₁ hop₁
        rcases mem_concatTraceOnlineMem hop₂ with ⟨u, huRest, hop₂U⟩
        have hGt₁ : st₁.lastTimestamp < op₂.timestamp := (ihOpsBounds u huRest op₂ hop₂U).1
        omega

/-- **Organ O3 Multi-Turn Apex Trace Theorem (`apex_polis_deos_trace_safe`)**:
    Across any arbitrary-length DeOS session `trace : List (PolisTurn A B)` with `ValidTrace st₀ trace stF`:
    1. **Revocation Irreversibility & Zero Replay**: `st₀.revokedCodes ⊆ stF.revokedCodes`, every
       executed turn's capability enters `stF.revokedCodes`, was fresh against `st₀.revokedCodes`,
       and `List.Nodup (trace.map PolisTurn.inputCode)` forbids replay across any two turns;
    2. **Exact `Mandate` Budget Conservation**: `stF.mandateBudget + totalTraceMandateCost trace = st₀.mandateBudget`;
    3. **Persistent `UMem` Causal Chronology**: `st₀.lastTimestamp ≤ stF.lastTimestamp` and the
       concatenated multi-turn memory trace `concatTraceOnlineMem trace` is globally chronological;
    4. **Universal Per-Turn Safety**: every `turn ∈ trace` satisfies all 9 guarantees of
       `apex_polis_deos_turn_safe` (choice-free `B`-realizer, Blum `UMem` permutation/RAW,
       `Sel4CapDlNonInterfering`, SMMU physical DMA watchdog confinement, and viability/ZoE bounds). -/
theorem apex_polis_deos_trace_safe
    [PolisObligations]
    {P : PCA} [DecidableEq P.Code] {A B : Assembly P}
    (st₀ : PolisSessionState P.Code)
    (trace : List (PolisTurn A B))
    (stF : PolisSessionState P.Code)
    (hValid : ValidTrace st₀ trace stF) :
    (∀ c ∈ st₀.revokedCodes, c ∈ stF.revokedCodes) ∧
    (∀ t ∈ trace, t.inputCode ∈ stF.revokedCodes ∧ t.inputCode ∉ st₀.revokedCodes) ∧
    List.Nodup (trace.map PolisTurn.inputCode) ∧
    stF.mandateBudget + totalTraceMandateCost trace = st₀.mandateBudget ∧
    st₀.lastTimestamp ≤ stF.lastTimestamp ∧
    checkChronologicalLog (concatTraceOnlineMem trace) = true ∧
    (∀ turn ∈ trace, ∀ (x : A.Carrier) (probeOp : MemOp),
      A.realizes turn.inputCode x →
      (∃ outCode : P.Code,
        turn.morphism.tracker turn.inputCode = some outCode ∧
        B.realizes outCode (turn.morphism.map x)) ∧
      turn.onlineMem.length = turn.offlineSortedMem.length ∧
      countMemOp probeOp turn.onlineMem = countMemOp probeOp turn.offlineSortedMem ∧
      checkLocalReadWriteConsistency turn.offlineSortedMem = true ∧
      Sel4CapDlNonInterfering turn.partition ∧
      (∀ (initBus : Nat → BitVec 64) (dmaTrace : List DmaWriteReq) (physAddr : Nat),
        isWatchdogProtectedAddr turn.partition physAddr = true →
        (∀ req ∈ dmaTrace, req.srcPd ≠ turn.partition.watchdogPdId) →
        runPhysicalDmaTrace turn.partition initBus dmaTrace physAddr = initBus physAddr) ∧
      turn.viability.lyapunovValMilli ≤ turn.viability.lyapunovCapMilli ∧
      turn.viability.focCurrentMilliAmp ≤ turn.viability.maxSafeCurrentMilli ∧
      (turn.viability.escrowWantSatisfied = true ∨ turn.viability.escrowGiveRefunded = true)) := by
  rcases validTrace_invariants st₀ trace stF hValid with
    ⟨hRevMono, hTurns, hNodup, hBudget, hTsMono, _hBounds, hChronoAll⟩
  refine ⟨hRevMono,
          fun t ht => ⟨(hTurns t ht).1, (hTurns t ht).2.1⟩,
          hNodup,
          hBudget,
          hTsMono,
          hChronoAll,
          ?_⟩
  intro turn hMem x probeOp hReal
  exact apex_polis_deos_turn_safe turn x probeOp hReal (hTurns turn hMem).2.2

/-! ## 4. Concrete `deosCapPCA` Assemblies, `SilverWorkflow` Instance & `silverPolisSmoke` -/

/-- Concrete Assembly of authorized custody capabilities `(pdId, epoch)`. -/
@[expose] def custodyAssembly : Assembly deosCapPCA where
  Carrier := Nat × Nat
  realizes := fun code pair => code = .capToken pair.1 1 pair.2
  existent := fun pair => ⟨.capToken pair.1 1 pair.2, rfl⟩

/-- Concrete Assembly of settled ZoE payout seats `(pdId, totalPayout)`. -/
@[expose] def settledSeatAssembly : Assembly deosCapPCA where
  Carrier := Nat × Nat
  realizes := fun code pair => code = .settledSeat pair.1 pair.2
  existent := fun pair => ⟨.settledSeat pair.1 pair.2, rfl⟩

/-- Choice-free `TrackedMorphism` clearing a custody capability into a settled ZoE seat payout. -/
def clearCustodyToSeat (baseAmount : Nat) :
    TrackedMorphism custodyAssembly settledSeatAssembly where
  map := fun pair => (pair.1, baseAmount + pair.2)
  tracker := fun code => evalDeosCapApply code (.settledSeat 0 baseAmount)
  tracks := by
    intro c pair hReal
    dsimp only [custodyAssembly] at hReal
    subst hReal
    refine ⟨.settledSeat pair.1 (baseAmount + pair.2), rfl, rfl⟩

/-- Concrete `PolisTurn` carrier over `deosCapPCA` for `SilverWorkflow` registration. -/
abbrev ConcretePolisTurn := PolisTurn custodyAssembly settledSeatAssembly

private theorem domains_nonempty_of_checkDistinctPdIds {ds : List ProtectionDomain}
    (h : checkDistinctPdIds ds = true) :
    (!ds.isEmpty) = true := by
  cases ds with
  | nil => cases h
  | cons _ _ => rfl

/-- `SilverWorkflow` instance for `ConcretePolisTurn` with non-empty `CompleteOn` domain
    (covering both admitted turns and planted bad turns) and exact refutation completeness. -/
instance instSilverWorkflowPolis : SilverWorkflow ConcretePolisTurn where
  CompleteOn := fun turn => (!turn.partition.domains.isEmpty) = true
  Spec := fun turn =>
    (turn.morphism.tracker turn.inputCode).isSome = true ∧
    verifyBlumMemory turn.onlineMem turn.offlineSortedMem = true ∧
    checkMicrokitIsolation turn.partition = true ∧
    turn.viability.lyapunovValMilli ≤ turn.viability.lyapunovCapMilli ∧
    turn.viability.focCurrentMilliAmp ≤ turn.viability.maxSafeCurrentMilli ∧
    (turn.viability.escrowWantSatisfied = true ∨ turn.viability.escrowGiveRefunded = true)
  runValid := checkPolisTurn
  refuseInvalid := refusePolisTurn
  refuse_iff := by
    intro turn
    unfold checkPolisTurn
    cases refusePolisTurn turn <;> simp
  silverSound := by
    intro turn hRun
    unfold checkPolisTurn refusePolisTurn at hRun
    split at hRun
    · cases hRun
    · rename_i hTrkNeg
      split at hRun
      · cases hRun
      · rename_i hBlumNeg
        have hTrk : (turn.morphism.tracker turn.inputCode).isSome = true :=
          of_bool_not_eq_false (Bool.eq_false_iff.mpr hTrkNeg)
        have hBlumFast : verifyBlumMemoryFast turn.onlineMem.toArray turn.offlineSortedMem.toArray = true :=
          of_bool_not_eq_false (Bool.eq_false_iff.mpr hBlumNeg)
        have hBlum : verifyBlumMemory turn.onlineMem turn.offlineSortedMem = true := by
          rw [← verifyBlumMemoryFast_eq_verifyBlumMemory turn.onlineMem.toArray turn.offlineSortedMem.toArray]
          exact hBlumFast
        cases hIsoOpt : refuseMicrokitIsolation turn.partition with
        | some r =>
          rw [hIsoOpt] at hRun
          cases hRun
        | none =>
          rw [hIsoOpt] at hRun
          dsimp only at hRun
          split at hRun
          · cases hRun
          · rename_i hViabNeg
            have hViab : checkViabilityEnvelope turn.viability = true :=
              of_bool_not_eq_false (Bool.eq_false_iff.mpr hViabNeg)
            unfold checkViabilityEnvelope at hViab
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hViab
            refine ⟨hTrk, hBlum, ?_, hViab.1.1, hViab.1.2, hViab.2⟩
            unfold checkMicrokitIsolation
            rw [hIsoOpt]
            rfl
  silverCompleteDomain := by
    intro turn hRun
    unfold checkPolisTurn refusePolisTurn at hRun
    split at hRun
    · cases hRun
    · split at hRun
      · cases hRun
      · cases hIsoOpt : refuseMicrokitIsolation turn.partition with
        | some _ =>
          rw [hIsoOpt] at hRun
          cases hRun
        | none =>
          unfold refuseMicrokitIsolation at hIsoOpt
          split at hIsoOpt
          · cases hIsoOpt
          · rename_i hDistNeg
            exact domains_nonempty_of_checkDistinctPdIds
              (of_bool_not_eq_false (Bool.eq_false_iff.mpr hDistNeg))
  silverComplete := by
    intro turn _hDom ⟨hTrk, hBlum, hIso, hLyap, hCurr, hEsc⟩
    unfold checkPolisTurn refusePolisTurn
    have hBlumFast : verifyBlumMemoryFast turn.onlineMem.toArray turn.offlineSortedMem.toArray = true := by
      rw [verifyBlumMemoryFast_eq_verifyBlumMemory]
      exact hBlum
    have hIsoNone : refuseMicrokitIsolation turn.partition = none := by
      unfold checkMicrokitIsolation at hIso
      cases hOpt : refuseMicrokitIsolation turn.partition with
      | none => rfl
      | some _ =>
        rw [hOpt] at hIso
        cases hIso
    have hViab : checkViabilityEnvelope turn.viability = true := by
      unfold checkViabilityEnvelope
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨⟨hLyap, hCurr⟩, hEsc⟩
    rw [hTrk, hBlumFast, hIsoNone, hViab]
    rfl

/-- Canonical isolated 3-PD `seL4` Microkit partition (`ariadne-nic-pd`, `lean-executor-pd`, `simplex-watchdog-pd`). -/
def sampleValidPartition : SeL4MicrokitPartition where
  watchdogPdId := 4
  domains :=
    [ { pdId := 1
      , name := "ariadne-nic-pd"
      , mappedMmio := [⟨10, 0x4000_0000, 0x1000, true, false⟩]
      , untypedCapChildren := [3, 4] }
    , { pdId := 3
      , name := "lean-executor-pd"
      , mappedMmio := [⟨11, 0x4001_0000, 0x1000, true, false⟩]
      , untypedCapChildren := [4] }
    , { pdId := 4
      , name := "simplex-watchdog-pd"
      , mappedMmio := [⟨12, 0x5000_0000, 0x1000, true, true⟩]
      , untypedCapChildren := [] } ]
  channels :=
    [ ⟨0, 1, 3, 2048⟩
    , ⟨1, 3, 4, 512⟩ ]

/-- Admitted end-to-end `ConcretePolisTurn` (epoch `25`, timestamps `1..7`). -/
def sampleValidPolisTurn : ConcretePolisTurn where
  morphism := (TrackedMorphism.id settledSeatAssembly).comp (clearCustodyToSeat 1000)
  inputCode := .capToken 3 1 25
  onlineMem := sampleOnlineMem
  offlineSortedMem := sampleOfflineSortedMem
  partition := sampleValidPartition
  viability := ⟨120, 500, 3200, 8000, true, false⟩
  receiptRoot256 := 0x1234_5678_9ABC_DEF0#256

/-- Second admitted `ConcretePolisTurn` (fresh capability epoch `40`, timestamps `10..12`). -/
def sampleSecondPolisTurn : ConcretePolisTurn where
  morphism := clearCustodyToSeat 2000
  inputCode := .capToken 3 1 40
  onlineMem := sampleSecondOnlineMem
  offlineSortedMem := sampleSecondOfflineSortedMem
  partition := sampleValidPartition
  viability := ⟨150, 500, 3100, 8000, true, false⟩
  receiptRoot256 := 0xCAFE_BABE_1122_3344#256

/-- Initial DeOS session state with pre-revoked epoch `9` and `32` `Mandate` budget units. -/
def sampleInitSessionState : PolisSessionState DeosCapCode where
  revokedCodes  := [.capToken 3 1 9]
  mandateBudget := 32
  lastTimestamp := 0

/-- Canonical 2-turn valid DeOS trace exercising persistent `RevokedSet`, `Mandate` depletion,
    and advancing `UMem` timestamps across `[sampleValidPolisTurn, sampleSecondPolisTurn]`. -/
def sampleValidPolisTrace : List ConcretePolisTurn :=
  [sampleValidPolisTurn, sampleSecondPolisTurn]

/-- Planted bad turn 1: `lean-executor-pd` illegally maps a `FocHil` hardware-watchdog MMIO aperture. -/
def plantedWatchdogLeakTurn : ConcretePolisTurn :=
  { sampleValidPolisTurn with
    partition :=
      { sampleValidPartition with
        domains :=
          [ { pdId := 1
            , name := "ariadne-nic-pd"
            , mappedMmio := [⟨10, 0x4000_0000, 0x1000, true, false⟩]
            , untypedCapChildren := [3, 4] }
          , { pdId := 3
            , name := "lean-executor-pd"
            , mappedMmio := [⟨99, 0x6000_0000, 0x1000, false, true⟩]
            , untypedCapChildren := [] }
          , { pdId := 4
            , name := "simplex-watchdog-pd"
            , mappedMmio := [⟨12, 0x5000_0000, 0x1000, true, true⟩]
            , untypedCapChildren := [] } ] } }

/-- Planted bad turn 2: two PDs share overlapping writable MMIO (`0x4000_0800` inside `[0x4000_0000, 0x4000_1000)`). -/
def plantedSharedMmioTurn : ConcretePolisTurn :=
  { sampleValidPolisTurn with
    partition :=
      { sampleValidPartition with
        domains :=
          [ { pdId := 1
            , name := "ariadne-nic-pd"
            , mappedMmio := [⟨10, 0x4000_0000, 0x1000, true, false⟩]
            , untypedCapChildren := [3, 4] }
          , { pdId := 3
            , name := "lean-executor-pd"
            , mappedMmio := [⟨11, 0x4000_0800, 0x1000, true, false⟩]
            , untypedCapChildren := [] }
          , { pdId := 4
            , name := "simplex-watchdog-pd"
            , mappedMmio := [⟨12, 0x5000_0000, 0x1000, true, true⟩]
            , untypedCapChildren := [] } ] } }

/-- Planted bad turn 3: cyclic untyped capability derivation (`PD 4 → PD 1` while `PD 1 → PD 4`). -/
def plantedCyclicCapTurn : ConcretePolisTurn :=
  { sampleValidPolisTurn with
    partition :=
      { sampleValidPartition with
        domains :=
          [ { pdId := 1
            , name := "ariadne-nic-pd"
            , mappedMmio := [⟨10, 0x4000_0000, 0x1000, true, false⟩]
            , untypedCapChildren := [4] }
          , { pdId := 4
            , name := "simplex-watchdog-pd"
            , mappedMmio := [⟨12, 0x5000_0000, 0x1000, true, true⟩]
            , untypedCapChildren := [1] } ]
        channels := [] } }

/-- Planted bad turn 4: forged Blum `UMem` read (`99#64` instead of written `42#64` at addr `100`). -/
def plantedForgedBlumTurn : ConcretePolisTurn :=
  let badOnline : List MemOp :=
    [ ⟨200, 1, true,  77#64, 0xAA#256⟩
    , ⟨100, 2, true,  42#64, 0xBB#256⟩
    , ⟨200, 3, false, 77#64, 0xAA#256⟩
    , ⟨100, 4, false, 99#64, 0xBB#256⟩ ]
  { sampleValidPolisTurn with
    onlineMem := badOnline
    offlineSortedMem := sortMemOpsByAddrTime badOnline }

/-- Executable Organ O3 Silver Smoke Suite: exercises `S`-combinator saturation, pairing, choice-free
    tracker output, $O(N \log N)$ Blum `UMem` sorting, multi-turn `runPolisTrace` state progression,
    replay/budget refusals, and single-turn named refusals. -/
def silverPolisSmoke : Bool :=
  let trackedOut : Option DeosCapCode :=
    sampleValidPolisTurn.morphism.tracker sampleValidPolisTurn.inputCode
  let skkCheck : Bool :=
    evalDeosCapApply (.s2 .k .k) (.settledSeat 9 333) == some (.settledSeat 9 333)
  let pairCheck : Bool :=
    (evalDeosCapApply .fst (.pair (.settledSeat 1 10) (.settledSeat 2 20)) == some (.settledSeat 1 10)) &&
    (evalDeosCapApply .snd (.pair (.settledSeat 1 10) (.settledSeat 2 20)) == some (.settledSeat 2 20))
  let traceOut : Option (PolisSessionState DeosCapCode) :=
    runPolisTrace sampleInitSessionState sampleValidPolisTrace
  let replayCheck : Bool :=
    runPolisTrace sampleInitSessionState [sampleValidPolisTurn, sampleValidPolisTurn] == none
  checkManifestWellFormed polisObligationManifest &&
  skkCheck &&
  pairCheck &&
  checkValidOnlineRamLog sampleOnlineMem &&
  verifyBlumMemoryFast sampleOnlineMem.toArray sampleOfflineSortedMem.toArray &&
  (trackedOut == some (.settledSeat 3 1025)) &&
  checkPolisTurn sampleValidPolisTurn &&
  traceOut.isSome &&
  replayCheck &&
  (refusePolisTurn sampleValidPolisTurn == none) &&
  (refusePolisTurn plantedWatchdogLeakTurn == some "refused: foc-hil-watchdog-leak") &&
  (refusePolisTurn plantedSharedMmioTurn == some "refused: shared-writable-mmio") &&
  (refusePolisTurn plantedCyclicCapTurn == some "refused: cyclic-untyped-cap-authority") &&
  (refusePolisTurn plantedForgedBlumTurn == some "refused: blum-memory-mismatch")

example : checkMicrokitIsolation sampleValidPartition = true := by decide

end Obend.Trailblaze.Polis
end
