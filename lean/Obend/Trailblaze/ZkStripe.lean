module
/-
# Obend.Trailblaze.ZkStripe — Organ O5: Boolean-Closed `PredRE`, String-Aware `VpaOver` & Domain-Bound `tlsn` `CallTree` Audit

Concrete executable Silver/Gold spine and kernel-checked algebraic & cryptographic binding laws for
Organ O5 (`zkStripe`):

1. **Boolean-Closed Byte Regular Expressions (`PredRE`)**:
   Supports empty language (`emp`), empty word (`eps`), byte intervals (`charRange`), alternation
   (`alt`), concatenation (`seq`), Kleene star (`star`), **boolean complement (`compl`)**, and
   **conjunction (`inter`)**. Executed via Brzozowski byte derivatives (`nullable`, `deriv`,
   `matchesBytes`) with unconditionally proved complement (`matchesBytes_compl`), intersection
   (`matchesBytes_inter`), alternation (`matchesBytes_alt`), and De Morgan laws.
2. **Visibly Pushdown Automata (`VpaOver` / `VpaMachine`, Alur–Madhusudan) & Stateful String-Aware JSON Lexer**:
   Tagged call/return/internal byte alphabet (`VpaSymbol`), deterministic pushdown evaluator
   (`runVpa`) with unconditionally proved stack-tag well-matchedness (`runVpa_balanced_stack`), and
   a 2-bit `(inString, escaped)` string-aware JSON lexer (`lexJsonBytesSpec`) paired with an
   unboxed `ByteArray` `Exec` fast path (`lexJsonByteArrayExec`) and proved `Spec ↔ Exec`
   equivalence (`lexJsonByteArrayExec_eq_spec`), defeating escaped-quote delimiter smuggling.
3. **Domain-Bound Multi-Hop `tlsn` HTTPS `CallTree` Merkle Commitment & Full-Tree Audit**:
   Commits `notaryKeyHash`, `serverDomain` UTF-8 bytes, `redactedRequest`, `redactedResponse`, and
   child session digests via length-prefixed `frameBytes`, **proving `callTreeDigestBytes_binding`
   and `callTreeDigest_binding` unconditionally in Lean's kernel with `0` `Classical.choice` and
   `0` Stage-A obligations**, alongside recursive full-subtree soundness (`auditNodes_all_hops_sound`)
   across every hop `node ∈ allSessionNodes tree`.
-/
public import Obend.Reasons
public import Obend.Digest.HashBytes
public import Obend.Judge.Class

public section
namespace Obend.Trailblaze.ZkStripe

open Obend.Digest.HashBytes (Hash ofBE be length_be be_injective Collision)

set_option autoImplicit false

/-! ## §1. Boolean-Closed Regular Expressions (`PredRE`) & Brzozowski Derivatives -/

/-- Byte-level boolean-closed regular expression supporting complement (`compl`) and
    conjunction (`inter`) alongside standard regular operators. -/
inductive PredRE where
  | emp : PredRE
  | eps : PredRE
  | charRange (lo hi : UInt8) : PredRE
  | alt (r₁ r₂ : PredRE) : PredRE
  | seq (r₁ r₂ : PredRE) : PredRE
  | star (r : PredRE) : PredRE
  | compl (r : PredRE) : PredRE
  | inter (r₁ r₂ : PredRE) : PredRE
  deriving DecidableEq, Repr

namespace PredRE

/-- Match a single exact byte `b`. -/
def byte (b : UInt8) : PredRE :=
  .charRange b b

/-- Match any byte `0x00 .. 0xFF`. -/
def anyByte : PredRE :=
  .charRange 0 255

/-- Match an exact sequence of literal bytes. -/
def litBytes : List UInt8 → PredRE
  | [] => .eps
  | b :: bs => .seq (.byte b) (litBytes bs)

/-- Match any byte slice containing `pat` as a contiguous substring (`Σ* · pat · Σ*`). -/
def containsSubseq (pat : List UInt8) : PredRE :=
  .seq (.star anyByte) (.seq (litBytes pat) (.star anyByte))

/-- Redaction confinement regex: accepts iff `pat` NEVER occurs in the byte stream (`¬(Σ* · pat · Σ*)`). -/
def forbidSubseq (pat : List UInt8) : PredRE :=
  .compl (containsSubseq pat)

end PredRE

/-- Brzozowski nullability test: `true` iff the empty byte string `[]` belongs to `L(r)`. -/
def nullable : PredRE → Bool
  | .emp => false
  | .eps => true
  | .charRange _ _ => false
  | .alt r₁ r₂ => nullable r₁ || nullable r₂
  | .seq r₁ r₂ => nullable r₁ && nullable r₂
  | .star _ => true
  | .compl r => !nullable r
  | .inter r₁ r₂ => nullable r₁ && nullable r₂

/-- Smart concatenation constructor collapsing absorbing `.emp` and identity `.eps` (Owens–Reppy–Turon),
    preventing exponential derivative AST blowup on Kleene star (`∂_b (any*) = any*`). -/
def mkSeq : PredRE → PredRE → PredRE
  | .emp, _ => .emp
  | _, .emp => .emp
  | .eps, r₂ => r₂
  | r₁, .eps => r₁
  | r₁, r₂ => .seq r₁ r₂

/-- Brzozowski single-byte derivative `∂_b r`. -/
def deriv : PredRE → UInt8 → PredRE
  | .emp, _ => .emp
  | .eps, _ => .emp
  | .charRange lo hi, b =>
    if decide (lo ≤ b ∧ b ≤ hi) then .eps else .emp
  | .alt r₁ r₂, b => .alt (deriv r₁ b) (deriv r₂ b)
  | .seq r₁ r₂, b =>
    if nullable r₁ then
      .alt (mkSeq (deriv r₁ b) r₂) (deriv r₂ b)
    else
      mkSeq (deriv r₁ b) r₂
  | .star r, b => mkSeq (deriv r b) (.star r)
  | .compl r, b => .compl (deriv r b)
  | .inter r₁ r₂, b => .inter (deriv r₁ b) (deriv r₂ b)

/-- Total Brzozowski byte-stream matcher. -/
def matchesBytes : PredRE → List UInt8 → Bool
  | r, [] => nullable r
  | r, b :: bs => matchesBytes (deriv r b) bs

/-- Empty regex rejects every byte string. -/
theorem matchesBytes_emp (bs : List UInt8) :
    matchesBytes .emp bs = false := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simpa [matchesBytes, deriv] using ih

/-- **Exact Boolean Complement Law**: `matchesBytes (.compl r) bs` is the exact boolean
    negation of `matchesBytes r bs` on every byte string `bs`. -/
theorem matchesBytes_compl (r : PredRE) (bs : List UInt8) :
    matchesBytes (.compl r) bs = !matchesBytes r bs := by
  induction bs generalizing r with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r b)

/-- **Exact Boolean Conjunction Law**: `matchesBytes (.inter r₁ r₂) bs` equals the boolean
    conjunction of `matchesBytes r₁ bs` and `matchesBytes r₂ bs` on every byte string `bs`. -/
theorem matchesBytes_inter (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.inter r₁ r₂) bs = (matchesBytes r₁ bs && matchesBytes r₂ bs) := by
  induction bs generalizing r₁ r₂ with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r₁ b) (deriv r₂ b)

/-- **Exact Boolean Disjunction Law**: `matchesBytes (.alt r₁ r₂) bs` equals the boolean
    disjunction of `matchesBytes r₁ bs` and `matchesBytes r₂ bs` on every byte string `bs`. -/
theorem matchesBytes_alt (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.alt r₁ r₂) bs = (matchesBytes r₁ bs || matchesBytes r₂ bs) := by
  induction bs generalizing r₁ r₂ with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r₁ b) (deriv r₂ b)

/-- Double complement involutivity on `matchesBytes`. -/
theorem matchesBytes_compl_compl (r : PredRE) (bs : List UInt8) :
    matchesBytes (.compl (.compl r)) bs = matchesBytes r bs := by
  rw [matchesBytes_compl, matchesBytes_compl, Bool.not_not]

/-- De Morgan duality for `PredRE` complement over alternation. -/
theorem matchesBytes_deMorgan_alt (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.compl (.alt r₁ r₂)) bs = matchesBytes (.inter (.compl r₁) (.compl r₂)) bs := by
  rw [matchesBytes_compl, matchesBytes_alt, matchesBytes_inter, matchesBytes_compl,
      matchesBytes_compl, Bool.not_or]


/-! ## §2. Visibly Pushdown Automata (`VpaOver`), Stateful JSON Lexer & `Spec ↔ Exec` Refinement -/

/-- Partitioned visibly pushdown input alphabet (`Σ = Σ_c ⊎ Σ_r ⊎ Σ_i`). -/
inductive VpaSymbol where
  | call (tag : UInt8) (sym : UInt8)
  | ret (tag : UInt8) (sym : UInt8)
  | internal (sym : UInt8)
  deriving DecidableEq, Repr

/-- Pushdown stack frame saving the caller state and structural delimiter tag. -/
structure VpaStackFrame where
  savedState : Nat
  callTag    : UInt8
  deriving DecidableEq, Repr

/-- Deterministic Visibly Pushdown Automaton (`VpaOver` / `VpaMachine`, Alur–Madhusudan). -/
structure VpaOver where
  initState    : Nat
  acceptStates : List Nat
  onCall       : Nat → UInt8 → UInt8 → Option Nat
  onRet        : Nat → Nat → UInt8 → UInt8 → Option Nat
  onInternal   : Nat → UInt8 → Option Nat

abbrev VpaMachine := VpaOver

/-- Single-symbol VPA transition: calls push `⟨q, tag⟩`, returns require a matching top-of-stack
    `callTag` and pop, and internals leave the stack untouched. -/
def stepVpa (m : VpaMachine) (q : Nat) (stk : List VpaStackFrame)
    (sym : VpaSymbol) : Option (Nat × List VpaStackFrame) :=
  match sym with
  | .internal b =>
    (m.onInternal q b).map fun q' => (q', stk)
  | .call tag b =>
    (m.onCall q tag b).map fun q' => (q', ⟨q, tag⟩ :: stk)
  | .ret tag b =>
    match stk with
    | [] => none
    | top :: rest =>
      if top.callTag == tag then
        (m.onRet q top.savedState tag b).map fun q' => (q', rest)
      else
        none

/-- Multi-step deterministic VPA execution over a symbol trace. -/
def execVpa (m : VpaMachine) (q : Nat) (stk : List VpaStackFrame) (trace : List VpaSymbol) :
    Option (Nat × List VpaStackFrame) :=
  match trace with
  | [] => some (q, stk)
  | sym :: rest =>
    match stepVpa m q stk sym with
    | none => none
    | some p => execVpa m p.1 p.2 rest
termination_by structural trace

/-- Accept iff execution finishes in an accepting control state with an empty call stack. -/
def runVpa (m : VpaMachine) (trace : List VpaSymbol) : Bool :=
  match execVpa m m.initState [] trace with
  | none => false
  | some p =>
    match p.2 with
    | [] => m.acceptStates.any (· == p.1)
    | _ :: _ => false

/-- Machine-independent structural nesting tracker over open call tags: returns `some finalTags`
    iff no return underflows or mismatches its enclosing open call tag. -/
def wellMatchedTags (openTags : List UInt8) (trace : List VpaSymbol) : Option (List UInt8) :=
  match trace with
  | [] => some openTags
  | .internal _ :: rest => wellMatchedTags openTags rest
  | .call tag _ :: rest => wellMatchedTags (tag :: openTags) rest
  | .ret tag _ :: rest =>
    match openTags with
    | [] => none
    | top :: stkRest =>
      if top == tag then wellMatchedTags stkRest rest else none
termination_by structural trace

/-- A VPA symbol stream is structurally well-nested iff all calls and returns match and close. -/
@[expose] def IsBalancedVpaTrace (trace : List VpaSymbol) : Prop :=
  wellMatchedTags [] trace = some []

private theorem uint8_beq_self (b : UInt8) : (b == b) = true :=
  Nat.beq_refl b.toBitVec.toNat

private theorem uint8_eq_of_beq {a b : UInt8} (h : (a == b) = true) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  cases va with | ofFin fa =>
  cases vb with | ofFin fb =>
  have hNat : fa.val = fb.val := Nat.eq_of_beq_eq_true h
  cases fa; cases fb; subst hNat; rfl

def StepTagRel (stk stk' : List VpaStackFrame) : VpaSymbol → Prop
  | .internal _ => stk'.map VpaStackFrame.callTag = stk.map VpaStackFrame.callTag
  | .call tag _ => stk'.map VpaStackFrame.callTag = tag :: stk.map VpaStackFrame.callTag
  | .ret tag _ => stk.map VpaStackFrame.callTag = tag :: stk'.map VpaStackFrame.callTag

theorem stepVpa_preserves_tag_stack (m : VpaMachine) (q q' : Nat)
    (stk stk' : List VpaStackFrame) (sym : VpaSymbol)
    (h : stepVpa m q stk sym = some (q', stk')) :
    StepTagRel stk stk' sym := by
  cases sym with
  | internal b =>
    dsimp only [stepVpa, StepTagRel] at h ⊢
    cases hInt : m.onInternal q b with
    | none => rw [hInt] at h; cases h
    | some qn =>
      rw [hInt] at h
      injection h with hPair
      injection hPair with _ hStk
      subst hStk
      rfl
  | call tag b =>
    dsimp only [stepVpa, StepTagRel] at h ⊢
    cases hCall : m.onCall q tag b with
    | none => rw [hCall] at h; cases h
    | some qn =>
      rw [hCall] at h
      injection h with hPair
      injection hPair with _ hStk
      subst hStk
      exact List.map_cons
  | ret tag b =>
    dsimp only [StepTagRel]
    cases stk with
    | nil => dsimp only [stepVpa] at h; cases h
    | cons top rest =>
      dsimp only [stepVpa] at h
      cases hTag : (top.callTag == tag)
      · rw [hTag] at h; cases h
      · rw [hTag] at h
        cases hRet : m.onRet q top.savedState tag b with
        | none => rw [hRet] at h; cases h
        | some qn =>
          rw [hRet] at h
          injection h with hPair
          injection hPair with _ hStk
          subst hStk
          have hTagEq : top.callTag = tag := uint8_eq_of_beq hTag
          rw [List.map_cons, hTagEq]

/-- **VPA Stack-Tag Invariant**: Every accepted or partial execution of *any* `VpaMachine`
    tracks the exact structural call-tag stack of `wellMatchedTags`. -/
theorem execVpa_preserves_tag_stack (m : VpaMachine) (trace : List VpaSymbol)
    (q qf : Nat) (stk stkf : List VpaStackFrame)
    (h : execVpa m q stk trace = some (qf, stkf)) :
    wellMatchedTags (stk.map VpaStackFrame.callTag) trace =
      some (stkf.map VpaStackFrame.callTag) := by
  induction trace generalizing q stk with
  | nil =>
    injection h with hPair
    injection hPair with _ hStk
    subst hStk
    rfl
  | cons sym rest ih =>
    dsimp only [execVpa] at h
    revert h
    cases hStep : stepVpa m q stk sym with
    | none => intro h; cases h
    | some pair =>
      cases pair with
      | mk q' stk' =>
        intro h
        have hTag := stepVpa_preserves_tag_stack m q q' stk stk' sym hStep
        have ihRes := ih q' stk' h
        cases sym with
        | internal b =>
          dsimp only [StepTagRel] at hTag
          dsimp only [wellMatchedTags]
          rw [← hTag]
          exact ihRes
        | call tag b =>
          dsimp only [StepTagRel] at hTag
          dsimp only [wellMatchedTags]
          rw [← hTag]
          exact ihRes
        | ret tag b =>
          dsimp only [StepTagRel] at hTag
          cases stk with
          | nil => dsimp only [stepVpa] at hStep; cases hStep
          | cons top stkRest =>
            injection hTag with hTopEq hRestEq
            rw [List.map_cons]
            dsimp only [wellMatchedTags]
            have hBeq : (top.callTag == tag) = true := hTopEq ▸ uint8_beq_self tag
            have hIf :
                (if (top.callTag == tag) = true then
                  wellMatchedTags (stkRest.map VpaStackFrame.callTag) rest
                else none) =
                wellMatchedTags (stkRest.map VpaStackFrame.callTag) rest :=
              @ite_eq_left_of_eq_true _ _ (instDecidableEqBool _ _) _ _ (eq_true hBeq)
            rw [hIf, hRestEq]
            exact ihRes

/-- **Balanced Stack Theorem**: Any trace accepted by `runVpa m` has strictly balanced,
    tag-matched calls and returns (`wellMatchedTags [] trace = some []`). -/
theorem runVpa_balanced_stack (m : VpaMachine) (trace : List VpaSymbol) :
    runVpa m trace = true →
    IsBalancedVpaTrace trace := by
  unfold runVpa
  cases hExec : execVpa m m.initState [] trace with
  | none => intro h; cases h
  | some pair =>
    cases pair with
    | mk qf stkf =>
      cases stkf with
      | nil =>
        intro _
        exact execVpa_preserves_tag_stack m trace m.initState qf [] [] hExec
      | cons _ _ =>
        intro h; cases h

/-- Leading unmatched return symbol is unconditionally rejected by every `VpaMachine`. -/
theorem runVpa_rejects_unmatched_ret (m : VpaMachine) (tag b : UInt8) (rest : List VpaSymbol) :
    runVpa m (.ret tag b :: rest) = false := by
  rfl

/-- 2-bit `(inString, escaped)` single-byte JSON VPA lexer step:
    - Inside `"..."` (`inString = true`), `{`, `}`, `[`, `]` emit `.internal b`; backslash `\` (`92`)
      arms `escaped := true` for the immediately following byte (handling both `\"` and `\\`), and
      an unescaped `"` (`34`) exits the string literal.
    - Outside `"..."` (`inString = false`), `"` enters `inString := true`, `{`/`}` map to tag `1`,
      and `[`/`]` map to tag `2`. -/
def lexJsonStep (inString escaped : Bool) (b : UInt8) : Bool × Bool × VpaSymbol :=
  if inString then
    if escaped then
      (true, false, .internal b)
    else if b == 92 then      -- '\\'
      (true, true, .internal b)
    else if b == 34 then      -- '"'
      (false, false, .internal b)
    else
      (true, false, .internal b)
  else
    if b == 34 then           -- '"'
      (true, false, .internal b)
    else if b == 123 then     -- '{'
      (false, false, .call 1 b)
    else if b == 125 then     -- '}'
      (false, false, .ret 1 b)
    else if b == 91 then      -- '['
      (false, false, .call 2 b)
    else if b == 93 then      -- ']'
      (false, false, .ret 2 b)
    else
      (false, false, .internal b)

/-- Stateful 2-bit `(inString, escaped)` `List UInt8` JSON VPA lexer specification:
    rejects (`none`) any payload with an unclosed string literal or trailing escape at EOF. -/
def lexJsonBytesSpec (inString escaped : Bool) : List UInt8 → Option (List VpaSymbol)
  | [] =>
    if inString || escaped then none else some []
  | b :: bs =>
    let stepOut := lexJsonStep inString escaped b
    (lexJsonBytesSpec stepOut.1 stepOut.2.1 bs).map (stepOut.2.2 :: ·)

/-- Stateful string-aware JSON VPA lexer from ground initial state `(false, false)`. -/
def lexJsonVpaSymbols (bs : List UInt8) : Option (List VpaSymbol) :=
  lexJsonBytesSpec false false bs

/-- Structural index loop for the unboxed `ByteArray` `Exec` JSON VPA lexer fast path. -/
def lexJsonArrayLoop (arr : Array UInt8) (idx : Nat) :
    Nat → Bool → Bool → Array VpaSymbol → Option (Array VpaSymbol)
  | 0, inString, escaped, acc =>
    if inString || escaped then none else some acc
  | rem + 1, inString, escaped, acc =>
    if h : idx < arr.size then
      let stepOut := lexJsonStep inString escaped arr[idx]
      lexJsonArrayLoop arr (idx + 1) rem stepOut.1 stepOut.2.1 (acc.push stepOut.2.2)
    else
      if inString || escaped then none else some acc

/-- Unboxed `ByteArray → Option (Array VpaSymbol)` `Exec` fast path for JSON VPA lexing. -/
def lexJsonByteArrayExec (bs : ByteArray) : Option (Array VpaSymbol) :=
  lexJsonArrayLoop bs.data 0 bs.data.size false false (Array.emptyWithCapacity bs.data.size)

theorem lexJsonArrayLoop_eq_spec (arr : Array UInt8) (idx rem : Nat)
    (hRem : idx + rem = arr.size) (inString escaped : Bool) (acc : Array VpaSymbol) :
    (lexJsonArrayLoop arr idx rem inString escaped acc).map Array.toList =
      (lexJsonBytesSpec inString escaped (arr.toList.drop idx)).map (acc.toList ++ ·) := by
  induction rem generalizing idx inString escaped acc with
  | zero =>
    have hIdx : idx = arr.toList.length := by
      rw [Array.length_toList]
      omega
    have hDrop : arr.toList.drop idx = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hIdx.symm)
    rw [hDrop]
    unfold lexJsonArrayLoop lexJsonBytesSpec
    cases inString || escaped <;> simp
  | succ r ih =>
    have hLt : idx < arr.size := by omega
    have hLtList : idx < arr.toList.length := by
      rw [Array.length_toList]
      exact hLt
    have hDropCons : arr.toList.drop idx = arr[idx] :: arr.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hLtList]
      rfl
    unfold lexJsonArrayLoop
    simp only [hLt, ↓reduceDIte]
    rw [hDropCons]
    unfold lexJsonBytesSpec
    let stepOut := lexJsonStep inString escaped arr[idx]
    have hNext : (idx + 1) + r = arr.size := by omega
    have hRec := ih (idx + 1) hNext stepOut.1 stepOut.2.1 (acc.push stepOut.2.2)
    change (lexJsonArrayLoop arr (idx + 1) r stepOut.1 stepOut.2.1 (acc.push stepOut.2.2)).map Array.toList =
      ((lexJsonBytesSpec stepOut.1 stepOut.2.1 (arr.toList.drop (idx + 1))).map (stepOut.2.2 :: ·)).map (acc.toList ++ ·)
    rw [hRec]
    cases lexJsonBytesSpec stepOut.1 stepOut.2.1 (arr.toList.drop (idx + 1)) with
    | none => rfl
    | some tail =>
      simp [Array.toList_push, List.append_assoc]

/-- **`Spec ↔ Exec` Lexer Equivalence**: `lexJsonByteArrayExec` over an unboxed `ByteArray`
    produces the exact same `Option` symbol stream as `lexJsonBytesSpec false false`. -/
theorem lexJsonByteArrayExec_eq_spec (bs : ByteArray) :
    (lexJsonByteArrayExec bs).map Array.toList =
      lexJsonBytesSpec false false bs.data.toList := by
  unfold lexJsonByteArrayExec
  have h := lexJsonArrayLoop_eq_spec bs.data 0 bs.data.size (Nat.zero_add _) false false
    (Array.emptyWithCapacity bs.data.size)
  simpa using h

/-- Canonical deterministic VPA accepting non-empty well-balanced JSON/HTTP framed payloads. -/
def jsonFramingVpa : VpaMachine where
  initState    := 0
  acceptStates := [1]
  onCall       := fun _ _ _ => some 1
  onRet        := fun _ _ _ _ => some 1
  onInternal   := fun q _ => some q

/-- Run a `VpaMachine` over `List UInt8` after string-aware JSON lexing. -/
def runJsonFramingVpa (m : VpaMachine) (bs : List UInt8) : Bool :=
  match lexJsonBytesSpec false false bs with
  | none => false
  | some syms => runVpa m syms

/-- Run a `VpaMachine` over an unboxed `ByteArray` via `lexJsonByteArrayExec`. -/
def runJsonFramingVpaExec (m : VpaMachine) (bs : ByteArray) : Bool :=
  match lexJsonByteArrayExec bs with
  | none => false
  | some syms => runVpa m syms.toList

/-- **`Spec ↔ Exec` VPA Framing Equivalence**: `runJsonFramingVpaExec` agrees identically with
    `runJsonFramingVpa` on every `VpaMachine` and `ByteArray`. -/
theorem runJsonFramingVpaExec_eq_spec (m : VpaMachine) (bs : ByteArray) :
    runJsonFramingVpaExec m bs = runJsonFramingVpa m bs.data.toList := by
  unfold runJsonFramingVpaExec runJsonFramingVpa
  have hEq := lexJsonByteArrayExec_eq_spec bs
  cases hExec : lexJsonByteArrayExec bs with
  | none =>
    rw [hExec] at hEq
    cases hSpec : lexJsonBytesSpec false false bs.data.toList with
    | none => rfl
    | some syms => rw [hSpec] at hEq; cases hEq
  | some arr =>
    rw [hExec] at hEq
    cases hSpec : lexJsonBytesSpec false false bs.data.toList with
    | none => rw [hSpec] at hEq; cases hEq
    | some syms =>
      rw [hSpec] at hEq
      simp only [Option.map_some, Option.some.injEq] at hEq
      simp [hEq]


/-! ## §3. UTF-8 Bytes, Domain-Bound `HttpsSessionNode` Merkle Binding (`0` `Classical`) & Full-Tree Audit -/

/-- Kernel-reducible, `0`-axiom UTF-8 byte projection of `s : String` (`s.toByteArray.data.toList`). -/
def utf8Bytes (s : String) : List UInt8 :=
  s.toByteArray.data.toList

/-- `utf8Bytes` is unconditionally injective (`0` axioms: pure `String.ofByteArray` structure
    eta + proof irrelevance on `ByteArray.IsValidUTF8`). -/
theorem utf8Bytes_injective {s₁ s₂ : String} (h : utf8Bytes s₁ = utf8Bytes s₂) : s₁ = s₂ := by
  cases s₁ with
  | ofByteArray b₁ v₁ =>
    cases s₂ with
    | ofByteArray b₂ v₂ =>
      cases b₁ with
      | mk a₁ =>
        cases b₂ with
        | mk a₂ =>
          cases a₁ with
          | mk l₁ =>
            cases a₂ with
            | mk l₂ =>
              change l₁ = l₂ at h
              subst h
              rfl

/-- **Universal String-Literal Delimiter Confinement**:
    Every JSON structural delimiter (`{`, `}`, `[`, `]`) encountered inside `"..."` (`inString = true`)
    keeps `inString = true` and emits `.internal b` rather than `.call` or `.ret`. -/
theorem lexJsonStep_brace_inside_string_internal (escaped : Bool) (b : UInt8)
    (hb : b = 123 ∨ b = 125 ∨ b = 91 ∨ b = 93) :
    (lexJsonStep true escaped b).1 = true ∧
      (lexJsonStep true escaped b).2.2 = .internal b := by
  rcases hb with rfl | rfl | rfl | rfl <;> cases escaped <;> decide

/-- Plain string characters (`b ≠ 34` and `b ≠ 92`) inside `"..."` (`inString = true, escaped = false`)
    emit `.internal b` without leaving the string literal or arming `escaped`. -/
theorem lexJsonBytesSpec_plain_string_chars (chars tail : List UInt8)
    (hPlain : ∀ b ∈ chars, b ≠ 34 ∧ b ≠ 92) :
    lexJsonBytesSpec true false (chars ++ tail) =
      (lexJsonBytesSpec true false tail).map (chars.map VpaSymbol.internal ++ ·) := by
  induction chars with
  | nil => simp
  | cons b cs ih =>
    have hb := hPlain b (.head _)
    have hRest : ∀ c ∈ cs, c ≠ 34 ∧ c ≠ 92 := fun c hc => hPlain c (.tail _ hc)
    have hNe92 : (b == 92) = false := by
      cases h92 : (b == 92)
      · rfl
      · exact False.elim (hb.2 (uint8_eq_of_beq h92))
    have hNe34 : (b == 34) = false := by
      cases h34 : (b == 34)
      · rfl
      · exact False.elim (hb.1 (uint8_eq_of_beq h34))
    have hStep : lexJsonStep true false b = (true, false, .internal b) := by
      unfold lexJsonStep
      simp [hNe92, hNe34]
    dsimp only [List.cons_append, lexJsonBytesSpec]
    rw [hStep]
    dsimp only
    rw [ih hRest]
    cases lexJsonBytesSpec true false tail with
    | none => rfl
    | some syms => rfl

/-- **Universal Escaped-Quote Delimiter-Smuggling Refusal (`runJsonFramingVpa_rejects_escaped_quote_smuggle`)**:
    For **every** `VpaMachine` `m` and **every** plain JSON key `key` (`{"<key>":"\"}`),
    backslash-escaped `\"` (`92, 34`) leaves `inString = true` across `}`, so `lexJsonBytesSpec`
    returns `none` at EOF and `runJsonFramingVpa m` unconditionally returns `false`. -/
theorem runJsonFramingVpa_rejects_escaped_quote_smuggle (m : VpaMachine) (key : List UInt8)
    (hPlain : ∀ b ∈ key, b ≠ 34 ∧ b ≠ 92) :
    lexJsonBytesSpec false false ((123 : UInt8) :: (34 : UInt8) :: (key ++ [34, 58, 34, 92, 34, 125])) = none ∧
      runJsonFramingVpa m ((123 : UInt8) :: (34 : UInt8) :: (key ++ [34, 58, 34, 92, 34, 125])) = false := by
  have h123 : lexJsonStep false false 123 = (false, false, .call 1 123) := by decide
  have h34 : lexJsonStep false false 34 = (true, false, .internal 34) := by decide
  have hTail : lexJsonBytesSpec true false ([34, 58, 34, 92, 34, 125] : List UInt8) = none := by
    decide
  have hMid :
      lexJsonBytesSpec true false (key ++ [34, 58, 34, 92, 34, 125]) = none := by
    rw [lexJsonBytesSpec_plain_string_chars key [34, 58, 34, 92, 34, 125] hPlain, hTail]
    rfl
  have hFull :
      lexJsonBytesSpec false false
        ((123 : UInt8) :: (34 : UInt8) :: (key ++ [34, 58, 34, 92, 34, 125])) = none := by
    dsimp only [lexJsonBytesSpec]
    rw [h123]
    dsimp only [lexJsonBytesSpec]
    rw [h34]
    dsimp only
    rw [hMid]
    rfl
  refine ⟨hFull, ?_⟩
  unfold runJsonFramingVpa
  rw [hFull]

/-- Universal theorem guarding both `inString` and backslash `escaped` tracking in `lexJsonStep`:
    every payload accepted by `runJsonFramingVpa m` rejects all `{"<key>":"\"}` escaped-quote
    smuggling payloads and produces a balanced VPA symbol stream. -/
theorem runJsonFramingVpa_string_escape_sound (m : VpaMachine) (bs key : List UInt8)
    (hPlain : ∀ b ∈ key, b ≠ 34 ∧ b ≠ 92)
    (hOk : runJsonFramingVpa m bs = true) :
    bs ≠ ((123 : UInt8) :: (34 : UInt8) :: (key ++ [34, 58, 34, 92, 34, 125])) ∧
      ∃ syms, lexJsonBytesSpec false false bs = some syms ∧ IsBalancedVpaTrace syms := by
  refine ⟨?_, ?_⟩
  · intro hBad
    subst hBad
    have hRef := (runJsonFramingVpa_rejects_escaped_quote_smuggle m key hPlain).2
    exact Bool.false_ne_true (hRef.symm.trans hOk)
  · unfold runJsonFramingVpa at hOk
    cases hLex : lexJsonBytesSpec false false bs with
    | none => rw [hLex] at hOk; cases hOk
    | some syms =>
      rw [hLex] at hOk
      exact ⟨syms, rfl, runVpa_balanced_stack m syms hOk⟩

-- Concrete String-Aware Acceptance & Escaped-Quote Smuggling Refusal Witnesses
example : runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"msg\":\"unmatched } inside string\"}") = true := by
  decide

example :
    lexJsonBytesSpec false false (utf8Bytes "{\"smuggle\":\"\\\"}") = none ∧
      runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\"}") = false := by
  decide

example : runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\"}\"}") = true := by
  decide

example : runJsonFramingVpa jsonFramingVpa (utf8Bytes "{\"smuggle\":\"\\\\\"}}") = false := by
  decide

/-- A node in an authenticated `tlsn` HTTPS session tree (`CallTree`):
    commits the MPC-TLS notary public-key hash, target server domain, redacted request/response
    byte slices, and downstream causal child sessions (e.g. webhook → auth → manifest → shard). -/
inductive HttpsSessionNode where
  | mk
    (notaryKeyHash    : Nat)
    (serverDomain     : String)
    (redactedRequest  : List UInt8)
    (redactedResponse : List UInt8)
    (children         : List HttpsSessionNode)
  deriving Repr

mutual
def decEqHttpsSessionNode (a b : HttpsSessionNode) : Decidable (a = b) :=
  match a, b with
  | .mk h₁ d₁ req₁ resp₁ cs₁, .mk h₂ d₂ req₂ resp₂ cs₂ =>
    if hh : h₁ = h₂ then
      if hd : d₁ = d₂ then
        if hreq : req₁ = req₂ then
          if hresp : resp₁ = resp₂ then
            match decEqHttpsSessionChildren cs₁ cs₂ with
            | isTrue hcs => isTrue (by subst hh hd hreq hresp hcs; rfl)
            | isFalse hncs => isFalse (by intro hEq; cases hEq; exact hncs rfl)
          else isFalse (by intro hEq; cases hEq; exact hresp rfl)
        else isFalse (by intro hEq; cases hEq; exact hreq rfl)
      else isFalse (by intro hEq; cases hEq; exact hd rfl)
    else isFalse (by intro hEq; cases hEq; exact hh rfl)
termination_by structural a

def decEqHttpsSessionChildren (xs ys : List HttpsSessionNode) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs', y :: ys' =>
    match decEqHttpsSessionNode x y with
    | isTrue hx =>
      match decEqHttpsSessionChildren xs' ys' with
      | isTrue hxs => isTrue (by subst hx hxs; rfl)
      | isFalse hnxs => isFalse (by intro h; cases h; exact hnxs rfl)
    | isFalse hnx => isFalse (by intro h; cases h; exact hnx rfl)
termination_by structural xs
end

instance : DecidableEq HttpsSessionNode := decEqHttpsSessionNode

namespace HttpsSessionNode

@[expose] def notaryKeyHash : HttpsSessionNode → Nat
  | .mk h _ _ _ _ => h

@[expose] def serverDomain : HttpsSessionNode → String
  | .mk _ d _ _ _ => d

@[expose] def redactedRequest : HttpsSessionNode → List UInt8
  | .mk _ _ req _ _ => req

@[expose] def redactedResponse : HttpsSessionNode → List UInt8
  | .mk _ _ _ resp _ => resp

def children : HttpsSessionNode → List HttpsSessionNode
  | .mk _ _ _ _ cs => cs

end HttpsSessionNode

/-- Length-prefixed canonical framing (`len:4 ‖ payload`) for byte slices inside Merkle nodes. -/
def frameBytes (xs : List UInt8) : List UInt8 :=
  be 4 xs.length ++ xs

/-- **Prefix-Free Framing Injectivity**: Two 32-bit length-prefixed slices (`len < 2^32 = 256^4`)
    followed by arbitrary suffixes are equal iff both the slices and suffixes match identically. -/
theorem frameBytes_append_inj {xs ys rest₁ rest₂ : List UInt8}
    (hxs : xs.length < 2 ^ 32) (hys : ys.length < 2 ^ 32)
    (hEq : frameBytes xs ++ rest₁ = frameBytes ys ++ rest₂) :
    xs = ys ∧ rest₁ = rest₂ := by
  have hPow : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  unfold frameBytes at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  have hLenBe : (be 4 xs.length).length = (be 4 ys.length).length := by
    rw [length_be, length_be]
  obtain ⟨hBeEq, hTailEq⟩ := List.append_inj hEq hLenBe
  have hLenEq : xs.length = ys.length :=
    be_injective (hPow ▸ hxs) (hPow ▸ hys) hBeEq
  exact List.append_inj hTailEq hLenEq

/-- Canonical domain-separated Merkle preimage for one `HttpsSessionNode` hop:
    commits `notaryKeyHash` (`be 8`), length-prefixed `serverDomain` UTF-8 bytes,
    length-prefixed `redactedRequest` and `redactedResponse`, and `childrenBytes`. -/
def sessionNodePreimage (notaryHash : Nat) (domain : String)
    (req resp childrenBytes : List UInt8) : List UInt8 :=
  (0x01 : UInt8) ::
  (be 8 notaryHash ++
   (frameBytes (utf8Bytes domain) ++
    (frameBytes req ++
     (frameBytes resp ++
      childrenBytes))))

/-- **Domain-Bound Preimage Injectivity (`sessionNodePreimage_inj`)**:
    Under canonical 64-bit/32-bit framing bounds, identical `sessionNodePreimage` byte lists
    uniquely determine `notaryHash`, `serverDomain`, `redactedRequest`, `redactedResponse`,
    and `childrenBytes`. -/
theorem sessionNodePreimage_inj
    {h₁ h₂ : Nat} {d₁ d₂ : String}
    {req₁ req₂ resp₁ resp₂ kidsBytes₁ kidsBytes₂ : List UInt8}
    (hh₁ : h₁ < 2 ^ 64) (hh₂ : h₂ < 2 ^ 64)
    (hd₁ : (utf8Bytes d₁).length < 2 ^ 32) (hd₂ : (utf8Bytes d₂).length < 2 ^ 32)
    (hreq₁ : req₁.length < 2 ^ 32) (hreq₂ : req₂.length < 2 ^ 32)
    (hresp₁ : resp₁.length < 2 ^ 32) (hresp₂ : resp₂.length < 2 ^ 32)
    (hPre : sessionNodePreimage h₁ d₁ req₁ resp₁ kidsBytes₁ =
            sessionNodePreimage h₂ d₂ req₂ resp₂ kidsBytes₂) :
    h₁ = h₂ ∧ d₁ = d₂ ∧ req₁ = req₂ ∧ resp₁ = resp₂ ∧ kidsBytes₁ = kidsBytes₂ := by
  unfold sessionNodePreimage at hPre
  have hBody := (List.cons.inj hPre).2
  have hPow64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hBeLen : (be 8 h₁).length = (be 8 h₂).length := by rw [length_be, length_be]
  obtain ⟨hBeH, hRest1⟩ := List.append_inj hBody hBeLen
  have hNotaryEq : h₁ = h₂ := be_injective (hPow64 ▸ hh₁) (hPow64 ▸ hh₂) hBeH
  obtain ⟨hDomBytes, hRest2⟩ := frameBytes_append_inj hd₁ hd₂ hRest1
  have hDomEq : d₁ = d₂ := utf8Bytes_injective hDomBytes
  obtain ⟨hReqEq, hRest3⟩ := frameBytes_append_inj hreq₁ hreq₂ hRest2
  obtain ⟨hRespEq, hKidsBytes⟩ := frameBytes_append_inj hresp₁ hresp₂ hRest3
  exact ⟨hNotaryEq, hDomEq, hReqEq, hRespEq, hKidsBytes⟩

mutual
/-- Domain-bound recursive Merkle commitment bytes of an `HttpsSessionNode` over byte hash `H`:
    commits `notaryKeyHash`, `serverDomain` UTF-8 bytes, `redactedRequest` bytes,
    `redactedResponse` bytes, and framed child session subtree digests. -/
def callTreeDigestBytes (H : Hash) (n : HttpsSessionNode) : List UInt8 :=
  match n with
  | .mk notaryHash domain req resp kids =>
    H (sessionNodePreimage notaryHash domain req resp (callTreeChildrenDigestBytes H kids))
termination_by structural n

def callTreeChildrenDigestBytes (H : Hash) (ns : List HttpsSessionNode) : List UInt8 :=
  match ns with
  | [] => [(0x00 : UInt8)]
  | c :: cs =>
    (0x02 : UInt8) :: (frameBytes (callTreeDigestBytes H c) ++ callTreeChildrenDigestBytes H cs)
termination_by structural ns
end

/-- 256-bit integer reading (`ofBE`) of `callTreeDigestBytes H`. -/
def callTreeDigest (H : Hash) (node : HttpsSessionNode) : Nat :=
  ofBE (callTreeDigestBytes H node)

mutual
/-- Executable canonical framing bound checker on an `HttpsSessionNode` for hash `H`:
    verifies 64-bit `notaryKeyHash < 2^64`, 32-bit slice lengths `< 2^32`, and 32-bit child
    digest framing `(callTreeDigestBytes H c).length < 2^32` across every hop. -/
def checkCanonicalSessionTree (H : Hash) (n : HttpsSessionNode) : Bool :=
  match n with
  | .mk notaryHash domain req resp kids =>
    decide (notaryHash < 2 ^ 64) &&
    decide ((utf8Bytes domain).length < 2 ^ 32) &&
    decide (req.length < 2 ^ 32) &&
    decide (resp.length < 2 ^ 32) &&
    checkCanonicalSessionChildren H kids
termination_by structural n

def checkCanonicalSessionChildren (H : Hash) (ns : List HttpsSessionNode) : Bool :=
  match ns with
  | [] => true
  | c :: cs =>
    decide ((callTreeDigestBytes H c).length < 2 ^ 32) &&
    checkCanonicalSessionTree H c &&
    checkCanonicalSessionChildren H cs
termination_by structural ns
end

/-- Declarative canonical framing predicate matching `checkCanonicalSessionTree`. -/
def CanonicalSessionTree (H : Hash) (t : HttpsSessionNode) : Prop :=
  checkCanonicalSessionTree H t = true

mutual
theorem callTreeDigest_binding_aux (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : ofBE (callTreeDigestBytes H t₁) = ofBE (callTreeDigestBytes H t₂)) :
    t₁ = t₂ ∨ Collision H := by
  cases t₁ with
  | mk h₁ d₁ req₁ resp₁ kids₁ =>
    cases t₂ with
    | mk h₂ d₂ req₂ resp₂ kids₂ =>
      simp only [checkCanonicalSessionTree, Bool.and_eq_true, decide_eq_true_eq] at hCan₁ hCan₂
      rcases hCan₁ with ⟨⟨⟨⟨hh₁, hd₁⟩, hreq₁⟩, hresp₁⟩, hkids₁⟩
      rcases hCan₂ with ⟨⟨⟨⟨hh₂, hd₂⟩, hreq₂⟩, hresp₂⟩, hkids₂⟩
      let pre₁ : List UInt8 :=
        sessionNodePreimage h₁ d₁ req₁ resp₁ (callTreeChildrenDigestBytes H kids₁)
      let pre₂ : List UInt8 :=
        sessionNodePreimage h₂ d₂ req₂ resp₂ (callTreeChildrenDigestBytes H kids₂)
      change ofBE (H pre₁) = ofBE (H pre₂) at hEq
      if hPre : pre₁ = pre₂ then
        obtain ⟨hNotaryEq, hDomEq, hReqEq, hRespEq, hKidsBytes⟩ :=
          sessionNodePreimage_inj hh₁ hh₂ hd₁ hd₂ hreq₁ hreq₂ hresp₁ hresp₂ hPre
        rcases callTreeChildrenDigestBytes_binding_aux H kids₁ kids₂ hkids₁ hkids₂ hKidsBytes with
          hKidsEq | hCol
        · subst hNotaryEq hDomEq hReqEq hRespEq hKidsEq
          exact Or.inl rfl
        · exact Or.inr hCol
      else
        exact Or.inr ⟨pre₁, pre₂, hPre, hEq⟩
termination_by structural t₁

theorem callTreeChildrenDigestBytes_binding_aux (H : Hash)
    (ns₁ ns₂ : List HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionChildren H ns₁ = true)
    (hCan₂ : checkCanonicalSessionChildren H ns₂ = true)
    (hEq : callTreeChildrenDigestBytes H ns₁ = callTreeChildrenDigestBytes H ns₂) :
    ns₁ = ns₂ ∨ Collision H := by
  cases ns₁ with
  | nil =>
    cases ns₂ with
    | nil => exact Or.inl rfl
    | cons c₂ cs₂ =>
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      exact absurd hEq.1 (by decide)
  | cons c₁ cs₁ =>
    cases ns₂ with
    | nil =>
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      exact absurd hEq.1 (by decide)
    | cons c₂ cs₂ =>
      simp only [checkCanonicalSessionChildren, Bool.and_eq_true, decide_eq_true_eq] at hCan₁ hCan₂
      rcases hCan₁ with ⟨⟨hcd₁, hc₁⟩, hcs₁⟩
      rcases hCan₂ with ⟨⟨hcd₂, hc₂⟩, hcs₂⟩
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      obtain ⟨hChildDigestEq, hRestEq⟩ := frameBytes_append_inj hcd₁ hcd₂ hEq.2
      rcases callTreeDigest_binding_aux H c₁ c₂ hc₁ hc₂ (congrArg ofBE hChildDigestEq) with
        hCEq | hCol
      · rcases callTreeChildrenDigestBytes_binding_aux H cs₁ cs₂ hcs₁ hcs₂ hRestEq with
          hCsEq | hCol
        · subst hCEq hCsEq
          exact Or.inl rfl
        · exact Or.inr hCol
      · exact Or.inr hCol
termination_by structural ns₁
end

/-- **Unconditional Domain-Bound `callTreeDigestBytes` Binding (`0` Obligations, `0` `Classical`)**:
    Any two canonical `HttpsSessionNode` trees with identical `callTreeDigestBytes H` are either
    structurally identical (`t₁ = t₂`, including every hop's `serverDomain`, `notaryKeyHash`,
    `redactedRequest`, `redactedResponse`, and `children`) or constructively exhibit `Collision H`. -/
theorem callTreeDigestBytes_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂) :
    t₁ = t₂ ∨ Collision H :=
  callTreeDigest_binding_aux H t₁ t₂ hCan₁ hCan₂ (congrArg ofBE hEq)

/-- **Unconditional Domain-Bound `callTreeDigest` Binding (`0` Obligations, `0` `Classical`)**:
    Any two canonical `HttpsSessionNode` trees with equal integer `callTreeDigest H` (`ofBE`) are
    either structurally identical (`t₁ = t₂`) or constructively exhibit `Collision H`. -/
theorem callTreeDigest_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigest H t₁ = callTreeDigest H t₂) :
    t₁ = t₂ ∨ Collision H :=
  callTreeDigest_binding_aux H t₁ t₂ hCan₁ hCan₂ hEq

mutual
/-- Pre-order traversal collecting every `HttpsSessionNode` hop in a `CallTree`. -/
def allSessionNodes (n : HttpsSessionNode) : List HttpsSessionNode :=
  match n with
  | .mk h d req resp kids => .mk h d req resp kids :: allChildrenSessionNodes kids
termination_by structural n

def allChildrenSessionNodes (ns : List HttpsSessionNode) : List HttpsSessionNode :=
  match ns with
  | [] => []
  | c :: cs => allSessionNodes c ++ allChildrenSessionNodes cs
termination_by structural ns
end

theorem root_mem_allSessionNodes (tree : HttpsSessionNode) :
    tree ∈ allSessionNodes tree := by
  cases tree
  simp [allSessionNodes]

mutual
/-- Count total notarized HTTPS hops in a `CallTree`. -/
def callTreeHopCount : HttpsSessionNode → Nat
  | .mk _ _ _ _ kids => 1 + callTreeChildrenHopCount kids

def callTreeChildrenHopCount : List HttpsSessionNode → Nat
  | [] => 0
  | c :: cs => callTreeHopCount c + callTreeChildrenHopCount cs
end

/-- `zkStripe` audit policy combining notary trust roots, boolean-closed `PredRE` request/response
    confinement, visibly pushdown framing (`VpaMachine`), and `Obend.Reasons` policy rules. -/
structure ZkStripePolicy where
  trustedNotaryHashes : List Nat
  allowedRequestRe    : PredRE
  allowedResponseRe   : PredRE
  framingVpa          : VpaMachine
  policyRules         : List Obend.Reasons.Rule
  targetConclusion    : String

/-- Named refusal diagnostic for `zkStripe` `CallTree` verification. -/
inductive ZkStripeRefusal where
  | untrustedNotary (domain : String) (notaryHash : Nat)
  | nonCanonicalBounds (domain : String)
  | requestRegexViolation (domain : String)
  | responseRegexViolation (domain : String)
  | unbalancedFraming (domain : String)
  | policyUnsupported (conclusion : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Executable check that a single hop's fields fit canonical 64-bit / 32-bit framing widths. -/
def checkHopCanonicalBounds (notaryHash : Nat) (domain : String)
    (req resp : List UInt8) : Bool :=
  decide (notaryHash < 2 ^ 64) &&
  decide ((utf8Bytes domain).length < 2 ^ 32) &&
  decide (req.length < 2 ^ 32) &&
  decide (resp.length < 2 ^ 32)

mutual
/-- Extract ground `Obend.Reasons` facts from an authenticated `HttpsSessionNode` subtree:
    one `"hop_verified:<domain>"` fact per notarized, canonically bounded, regex-clean,
    string-aware VPA-framed session hop. -/
def extractCallTreeFacts (pol : ZkStripePolicy) : HttpsSessionNode → List String
  | .mk notaryHash domain req resp kids =>
    let hopFact :=
      if pol.trustedNotaryHashes.contains notaryHash &&
         checkHopCanonicalBounds notaryHash domain req resp &&
         matchesBytes pol.allowedRequestRe req &&
         matchesBytes pol.allowedResponseRe resp &&
         runJsonFramingVpa pol.framingVpa resp then
        ["hop_verified:" ++ domain]
      else []
    hopFact ++ extractChildrenFacts pol kids

def extractChildrenFacts (pol : ZkStripePolicy) : List HttpsSessionNode → List String
  | [] => []
  | c :: cs => extractCallTreeFacts pol c ++ extractChildrenFacts pol cs
end

/-- Assemble the `Obend.Reasons.Program` induced by a `ZkStripePolicy` and `CallTree`. -/
def buildCallTreeProgram (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Obend.Reasons.Program where
  facts := extractCallTreeFacts pol root
  rules := pol.policyRules

mutual
/-- Check every node in the `CallTree` against notary trust, canonical framing bounds,
    `PredRE` request/response confinement, and string-aware `VpaOver` framing. -/
def auditNodes (pol : ZkStripePolicy) : HttpsSessionNode → Except ZkStripeRefusal Unit
  | .mk notaryHash domain req resp kids =>
    if !pol.trustedNotaryHashes.contains notaryHash then
      .error (.untrustedNotary domain notaryHash)
    else if !checkHopCanonicalBounds notaryHash domain req resp then
      .error (.nonCanonicalBounds domain)
    else if !matchesBytes pol.allowedRequestRe req then
      .error (.requestRegexViolation domain)
    else if !matchesBytes pol.allowedResponseRe resp then
      .error (.responseRegexViolation domain)
    else if !runJsonFramingVpa pol.framingVpa resp then
      .error (.unbalancedFraming domain)
    else
      auditChildren pol kids

def auditChildren (pol : ZkStripePolicy) :
    List HttpsSessionNode → Except ZkStripeRefusal Unit
  | [] => .ok ()
  | c :: cs =>
    match auditNodes pol c with
    | .error e => .error e
    | .ok () => auditChildren pol cs
end

/-- Full `zkStripe` `CallTree` audit: checks every hop's notary root, canonical framing bounds,
    `PredRE` request/response confinement, string-aware `VpaMachine` structural framing, and
    `Obend.Reasons.wf` policy support. -/
def auditZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Except ZkStripeRefusal Unit :=
  match auditNodes pol root with
  | .error e => .error e
  | .ok () =>
    let prog := buildCallTreeProgram pol root
    let st := Obend.Reasons.statusIn (Obend.Reasons.wf prog) pol.targetConclusion
    if st == .supported then
      .ok ()
    else
      .error (.policyUnsupported pol.targetConclusion st)

/-- Boolean decision wrapper for `auditZkStripeCallTree`. -/
def verifyZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) : Bool :=
  (auditZkStripeCallTree pol root).isOk

theorem auditZkStripeCallTree_ok_imp_verify {pol : ZkStripePolicy} {root : HttpsSessionNode}
    (h : auditZkStripeCallTree pol root = .ok ()) :
    verifyZkStripeCallTree pol root = true := by
  simp [verifyZkStripeCallTree, h, Except.isOk, Except.toBool]

/-- Certified per-hop audit invariant established across every hop in `allSessionNodes tree`. -/
structure HopAudited (pol : ZkStripePolicy) (node : HttpsSessionNode) : Prop where
  trustedNotary    : pol.trustedNotaryHashes.contains node.notaryKeyHash = true
  canonicalKey     : node.notaryKeyHash < 2 ^ 64
  canonicalDomain  : (utf8Bytes node.serverDomain).length < 2 ^ 32
  canonicalReqLen  : node.redactedRequest.length < 2 ^ 32
  canonicalRespLen : node.redactedResponse.length < 2 ^ 32
  requestMatches   : matchesBytes pol.allowedRequestRe node.redactedRequest = true
  responseMatches  : matchesBytes pol.allowedResponseRe node.redactedResponse = true
  execFramingOk    : runJsonFramingVpaExec pol.framingVpa ⟨node.redactedResponse.toArray⟩ = true
  framedResponse   : ∃ syms, lexJsonBytesSpec false false node.redactedResponse = some syms ∧
                       runVpa pol.framingVpa syms = true ∧
                       IsBalancedVpaTrace syms

mutual
/-- **Recursive Full-Tree Audit Soundness (`auditNodes_all_hops_sound`)**:
    Passing `auditNodes pol tree = .ok ()` certifies notary trust, canonical 64-bit/32-bit framing
    bounds, `PredRE` request/response confinement, and balanced string-aware `ByteArray` / `List`
    VPA framing on **every hop `node ∈ allSessionNodes tree`**, not merely the root hop. -/
theorem auditNodes_all_hops_sound {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hOk : auditNodes pol tree = .ok ()) :
    ∀ node ∈ allSessionNodes tree, HopAudited pol node := by
  cases tree with
  | mk notaryHash domain req resp kids =>
    unfold auditNodes at hOk
    cases hNotary : pol.trustedNotaryHashes.contains notaryHash
    · rw [hNotary] at hOk; cases hOk
    · rw [hNotary] at hOk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hCanBool : checkHopCanonicalBounds notaryHash domain req resp
      · rw [hCanBool] at hOk; cases hOk
      · rw [hCanBool] at hOk
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        have hCanProps := hCanBool
        simp only [checkHopCanonicalBounds, Bool.and_eq_true, decide_eq_true_eq] at hCanProps
        rcases hCanProps with ⟨⟨⟨hKey, hDom⟩, hReqLen⟩, hRespLen⟩
        cases hReq : matchesBytes pol.allowedRequestRe req
        · rw [hReq] at hOk; cases hOk
        · rw [hReq] at hOk
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hResp : matchesBytes pol.allowedResponseRe resp
          · rw [hResp] at hOk; cases hOk
          · rw [hResp] at hOk
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            cases hVpa : runJsonFramingVpa pol.framingVpa resp
            · rw [hVpa] at hOk; cases hOk
            · rw [hVpa] at hOk
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
              have hExecVpa : runJsonFramingVpaExec pol.framingVpa ⟨resp.toArray⟩ = true := by
                rw [runJsonFramingVpaExec_eq_spec]
                simpa using hVpa
              have hFramed :
                  ∃ syms, lexJsonBytesSpec false false resp = some syms ∧
                    runVpa pol.framingVpa syms = true ∧ IsBalancedVpaTrace syms := by
                unfold runJsonFramingVpa at hVpa
                cases hLex : lexJsonBytesSpec false false resp with
                | none => rw [hLex] at hVpa; cases hVpa
                | some syms =>
                  rw [hLex] at hVpa
                  exact ⟨syms, rfl, hVpa, runVpa_balanced_stack pol.framingVpa syms hVpa⟩
              intro node hMem
              simp only [allSessionNodes, List.mem_cons] at hMem
              rcases hMem with rfl | hInKids
              · exact {
                  trustedNotary    := hNotary
                  canonicalKey     := hKey
                  canonicalDomain  := hDom
                  canonicalReqLen  := hReqLen
                  canonicalRespLen := hRespLen
                  requestMatches   := hReq
                  responseMatches  := hResp
                  execFramingOk    := hExecVpa
                  framedResponse   := hFramed
                }
              · exact auditChildren_all_hops_sound hOk node hInKids
termination_by structural tree

theorem auditChildren_all_hops_sound {pol : ZkStripePolicy} {kids : List HttpsSessionNode}
    (hOk : auditChildren pol kids = .ok ()) :
    ∀ node ∈ allChildrenSessionNodes kids, HopAudited pol node := by
  cases kids with
  | nil =>
    intro node hMem
    cases hMem
  | cons c cs =>
    unfold auditChildren at hOk
    cases hC : auditNodes pol c with
    | error e => rw [hC] at hOk; cases hOk
    | ok u =>
      rw [hC] at hOk
      intro node hMem
      simp only [allChildrenSessionNodes, List.mem_append] at hMem
      rcases hMem with hInC | hInCs
      · exact auditNodes_all_hops_sound hC node hInC
      · exact auditChildren_all_hops_sound hOk node hInCs
termination_by structural kids
end

theorem auditZkStripeCallTree_all_hops_sound {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hAudit : auditZkStripeCallTree pol tree = .ok ()) :
    (∀ node ∈ allSessionNodes tree, HopAudited pol node) ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion = .supported := by
  unfold auditZkStripeCallTree at hAudit
  cases hNodes : auditNodes pol tree with
  | error e => rw [hNodes] at hAudit; cases hAudit
  | ok u =>
    rw [hNodes] at hAudit
    simp only at hAudit
    cases hSt : (Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion == .supported)
    · rw [hSt] at hAudit; cases hAudit
    · exact ⟨auditNodes_all_hops_sound hNodes, beq_iff_eq.mp hSt⟩

/-- Root-hop projection corollary of `auditNodes_all_hops_sound`. -/
theorem auditNodes_root_props {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hOk : auditNodes pol tree = .ok ()) :
    HopAudited pol tree :=
  auditNodes_all_hops_sound hOk tree (root_mem_allSessionNodes tree)

/-- Succinct `DualPCS` (`HashUDR` ∨ `LatticeSIS`) receipt envelope for a redacted `CallTree`. -/
structure DualPcsCallTreeReceipt where
  committedTreeRoot  : Nat
  notaryQuorumDigest : Nat
  proofBytes         : List UInt8
  deriving DecidableEq, Repr

/-- MPC-TLS 2-of-3 quorum notary signature envelope over an HTTPS session digest. -/
structure MpcTlsNotaryAttestation where
  notaryKeyHash   : Nat
  sessionDigest   : Nat
  signatureBytes  : List UInt8
  deriving DecidableEq, Repr

/-- Structural envelope check on an `MpcTlsNotaryAttestation`. -/
def checkMpcTlsNotaryEnvelope (trustedNotaryHashes : List Nat)
    (att : MpcTlsNotaryAttestation) : Bool :=
  trustedNotaryHashes.contains att.notaryKeyHash &&
  decide (att.notaryKeyHash < 2 ^ 64) &&
  decide (att.sessionDigest ≠ 0) &&
  decide (att.signatureBytes.length == 64)

/-- Structural envelope check on a succinct `DualPcsCallTreeReceipt`. -/
def checkDualPcsReceiptEnvelope (pol : ZkStripePolicy)
    (rcpt : DualPcsCallTreeReceipt) : Bool :=
  pol.trustedNotaryHashes.contains rcpt.notaryQuorumDigest &&
  decide (rcpt.committedTreeRoot ≠ 0) &&
  decide (32 ≤ rcpt.proofBytes.length)

/-- Explicit Stage-A external cryptographic obligations for Organ O5 (`zkStripe`):
    (`tlsnAeadCommitmentBinding` is **discharged** unconditionally as `callTreeDigestBytes_binding`
    and `callTreeDigest_binding`!)
    1. `mpcTlsNotarySignatureOrigin`: every accepted 64-byte MPC-TLS quorum attestation under
       `trustedNotaryHashes` originates from a canonically framed `HttpsSessionNode` matching
       `att.notaryKeyHash` and `att.sessionDigest`;
    2. `dualPcsWitnessExtraction`: `DualPCS` knowledge soundness extracts a canonically framed
       `HttpsSessionNode` matching `rcpt.committedTreeRoot` and `rcpt.notaryQuorumDigest` that
       passes full `auditZkStripeCallTree pol`. -/
class ZkStripeObligations : Prop where
  mpcTlsNotarySignatureOrigin :
    ∀ (H : Hash) (trustedKeys : List Nat) (att : MpcTlsNotaryAttestation),
      checkMpcTlsNotaryEnvelope trustedKeys att = true →
      ∃ session : HttpsSessionNode,
        checkCanonicalSessionTree H session = true ∧
        trustedKeys.contains session.notaryKeyHash = true ∧
        session.notaryKeyHash = att.notaryKeyHash ∧
        callTreeDigest H session = att.sessionDigest ∧
        att.signatureBytes.length = 64
  dualPcsWitnessExtraction :
    ∀ (H : Hash) (pol : ZkStripePolicy) (rcpt : DualPcsCallTreeReceipt),
      checkDualPcsReceiptEnvelope pol rcpt = true →
      ∃ tree : HttpsSessionNode,
        checkCanonicalSessionTree H tree = true ∧
        callTreeDigest H tree = rcpt.committedTreeRoot ∧
        tree.notaryKeyHash = rcpt.notaryQuorumDigest ∧
        32 ≤ rcpt.proofBytes.length ∧
        auditZkStripeCallTree pol tree = .ok ()

/-- **Organ O5 Unconditional Apex Audit Theorem (`apex_zkstripe_calltree_audit`)**:
    With **zero open obligations** and **zero `Classical.choice`**, whenever `auditZkStripeCallTree`
    admits a canonical `CallTree` under a policy whose request regex enforces
    `.inter reqSchema (.compl forbiddenSecretRe)`, Lean's kernel guarantees across **every hop**
    `node ∈ allSessionNodes tree`:
    1. Trusted notary membership, canonical 64-bit/32-bit framing bounds, and balanced string-aware
       `ByteArray` / `List UInt8` VPA response framing (`HopAudited pol node`),
    2. Zero forbidden secret pattern match (`matchesBytes forbiddenSecretRe node.redactedRequest = false`)
       on **every hop** via `matchesBytes_inter` and `matchesBytes_compl`,
    3. Well-founded `Obend.Reasons.wf` support for `pol.targetConclusion`, and
    4. Unconditional domain-bound Merkle commitment binding (`tree = otherTree ∨ Collision H`). -/
theorem apex_zkstripe_calltree_audit
    (H : Hash) (reqSchema forbiddenSecretRe : PredRE)
    (pol : ZkStripePolicy) (tree otherTree : HttpsSessionNode)
    (hReqPolicy : pol.allowedRequestRe = .inter reqSchema (.compl forbiddenSecretRe))
    (hAudit : auditZkStripeCallTree pol tree = .ok ())
    (hCan₁ : checkCanonicalSessionTree H tree = true)
    (hCan₂ : checkCanonicalSessionTree H otherTree = true)
    (hSameDigest : callTreeDigest H tree = callTreeDigest H otherTree) :
    (∀ node ∈ allSessionNodes tree,
        HopAudited pol node ∧
        matchesBytes forbiddenSecretRe node.redactedRequest = false) ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion = .supported ∧
      (tree = otherTree ∨ Collision H) := by
  obtain ⟨hAllHops, hSupported⟩ := auditZkStripeCallTree_all_hops_sound hAudit
  refine ⟨?_, hSupported, callTreeDigest_binding H tree otherTree hCan₁ hCan₂ hSameDigest⟩
  intro node hMem
  have hHop := hAllHops node hMem
  have hReq := hHop.requestMatches
  rw [hReqPolicy, matchesBytes_inter, matchesBytes_compl, Bool.and_eq_true,
      Bool.not_eq_true'] at hReq
  exact ⟨hHop, hReq.2⟩


/-! ## §4. Concrete 4-Hop `tlsn` HTTPS `CallTree` Fixtures & Silver Smoke Runner -/

/-- 4-byte-strided structural mixer (`termination_by structural`) so 130+-byte Merkle & FPGA
    receipt preimages reduce in `O(N/4)` WHNF stack depth well inside default `maxRecDepth`. -/
def hashMixBytes4 : List UInt8 → Nat
  | [] => 0x5A3C9E11
  | [b0] => Nat.xor 0x5A3C9E11 (b0.toBitVec.toNat + 1)
  | [b0, b1] =>
    Nat.xor 0x5A3C9E11 (b0.toBitVec.toNat * 256 + b1.toBitVec.toNat + 2)
  | [b0, b1, b2] =>
    Nat.xor 0x5A3C9E11
      (b0.toBitVec.toNat * 65536 + b1.toBitVec.toNat * 256 + b2.toBitVec.toNat + 3)
  | b0 :: b1 :: b2 :: b3 :: bs =>
    let word :=
      b0.toBitVec.toNat * 16777216 + b1.toBitVec.toNat * 65536 +
        b2.toBitVec.toNat * 256 + b3.toBitVec.toNat
    Nat.xor (hashMixBytes4 bs + 0x9E37) word
termination_by structural bs => bs

/-- Fast deterministic 32-bit XOR-bijection `Hash` for `O(N/4)`-WHNF kernel smoke checks
    (preserves single-byte sensitivity across multi-hop Merkle trees; production callers
    instantiate `H := Obend.Core.Digest.deployed` cSHAKE256). -/
def fastMerkleHash : Hash := fun bs =>
  let h : Nat := hashMixBytes4 bs
  [0xA5,
   UInt8.ofNat (h / 16777216),
   UInt8.ofNat (h / 65536),
   UInt8.ofNat (h / 256),
   UInt8.ofNat h]

/-- Forbidden live Stripe secret prefix `"sk_"` (`[115, 107, 95]`). -/
def stripeLiveKeyPrefix : List UInt8 := [115, 107, 95]

/-- Required HTTP `GET` prefix (`[71, 69, 84]`). -/
def httpGetPrefix : List UInt8 := [71, 69, 84]

/-- Canonical `ZkStripePolicy`: requires trusted notary `0xA11CE`, HTTP `GET` prefix, zero `"sk_"`
    secret-key leakage in both requests and responses via `.compl`, balanced string-aware JSON VPA
    framing, and 4-hop `Reasons` causal chain
    `api.stripe.com → auth.obend.org → registry.hf.co → cdn.dataset.org`. -/
def defaultZkStripePolicy : ZkStripePolicy where
  trustedNotaryHashes := [0xA11CE]
  allowedRequestRe    := .inter (.seq (PredRE.litBytes httpGetPrefix) (.star PredRE.anyByte))
                                (PredRE.forbidSubseq stripeLiveKeyPrefix)
  allowedResponseRe   := PredRE.forbidSubseq stripeLiveKeyPrefix
  framingVpa          := jsonFramingVpa
  policyRules := [
    { name  := "admit_four_hop_calltree"
      concl := "calltree_admitted"
      pos   := ["hop_verified:api.stripe.com", "hop_verified:auth.obend.org",
                "hop_verified:registry.hf.co", "hop_verified:cdn.dataset.org"]
      neg   := ["emergency_freeze"] }
  ]
  targetConclusion := "calltree_admitted"

/-- Valid 4-hop `tlsn`-notarized HTTPS `CallTree` (including a JSON string containing an unmatched
    `}` in hop 2 to exercise stateful string-aware VPA lexing across multi-hop verification):
    1. `api.stripe.com` → 2. `auth.obend.org` → 3. `registry.hf.co` → 4. `cdn.dataset.org`. -/
def validFourHopCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107]
      (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 50, 93] []
      ]
    ]
  ]

/-- Planted bad `CallTree` #1: leaks `"sk_"` (`[115, 107, 95]`) in hop 3's request header,
    caught by `PredRE.forbidSubseq` (`.compl`). -/
def leakedSecretCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 115, 107, 95, 57] [123, 125] []
    ]
  ]

/-- Planted bad `CallTree` #2: escaped-quote delimiter smuggling `{"smuggle":"\"}` in hop 4,
    caught by stateful 2-bit `lexJsonBytesSpec` + `jsonFramingVpa`. -/
def unbalancedVpaCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100]
          (utf8Bytes "{\"smuggle\":\"\\\"}") []
      ]
    ]
  ]

/-- Planted bad `CallTree` #3: swaps ONLY `serverDomain` on hop 1 (`"evil.stripe.io"` vs
    `"api.stripe.com"`), verifying that `callTreeDigest` now commits `serverDomain`. -/
def spoofedDomainCallTree : HttpsSessionNode :=
  match validFourHopCallTree with
  | .mk h _ req resp kids => .mk h "evil.stripe.io" req resp kids

private def decEqExceptUnit (a b : Except ZkStripeRefusal Unit) : Decidable (a = b) :=
  match a, b with
  | .ok (), .ok () => isTrue rfl
  | .ok (), .error _ => isFalse (by intro h; cases h)
  | .error _, .ok () => isFalse (by intro h; cases h)
  | .error e₁, .error e₂ =>
    if he : e₁ = e₂ then isTrue (by subst he; rfl)
    else isFalse (by intro h; cases h; exact he rfl)

example :
    auditNodes defaultZkStripePolicy validFourHopCallTree = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example :
    auditChildren defaultZkStripePolicy validFourHopCallTree.children = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example :
    auditZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example :
    checkCanonicalSessionTree fastMerkleHash validFourHopCallTree = true := by
  decide

example :
    callTreeDigest fastMerkleHash validFourHopCallTree ≠ 0 := by
  decide

example :
    callTreeDigest fastMerkleHash validFourHopCallTree ≠
      callTreeDigest fastMerkleHash spoofedDomainCallTree := by
  decide

/-- Executable Silver end-to-end smoke runner for Organ O5 (`ZkStripe`). -/
def silverZkStripeSmoke : Bool :=
  let hopCountOk := callTreeHopCount validFourHopCallTree == 4
  let validAdmitted := verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree
  let canonicalOk := checkCanonicalSessionTree fastMerkleHash validFourHopCallTree
  let domainBoundOk :=
    callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash spoofedDomainCallTree
  let stringBraceOk :=
    runJsonFramingVpaExec jsonFramingVpa ("{\"msg\":\"unmatched } inside string\"}".toByteArray)
  let escapeSmuggleRefused :=
    !runJsonFramingVpaExec jsonFramingVpa ("{\"smuggle\":\"\\\"}".toByteArray)
  let leakRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree with
    | .error e => e == .requestRegexViolation "registry.hf.co"
    | .ok () => false
  let vpaRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy unbalancedVpaCallTree with
    | .error e => e == .unbalancedFraming "cdn.dataset.org"
    | .ok () => false
  let digestNonZero := callTreeDigest fastMerkleHash validFourHopCallTree != 0
  hopCountOk && validAdmitted && canonicalOk && domainBoundOk &&
    stringBraceOk && escapeSmuggleRefused && leakRefused && vpaRefused && digestNonZero

example : silverZkStripeSmoke = true := by
  decide

end Obend.Trailblaze.ZkStripe
end
