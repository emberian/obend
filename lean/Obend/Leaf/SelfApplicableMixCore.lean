module
/-
# `Obend.Leaf.SelfApplicableMixCore` — Two-Level `MixProg` AST, Quotation, Semantics & `mixProg`

Core syntax, lossless S-expression quotation (`quoteProg`, `unquoteProg?`, `unquote_quote`,
`quote_of_unquoteProg`), total fuel-indexed semantics (`evalMix`), the 9-procedure self-applicable
specializer `mixProg : MixProg` encoded inside `MixProg` itself, and the sound specialization
validator (`specShadow`, `checkSpecializesProg`, `checkSpecializesProg_sound`).
-/

public section
namespace Obend.Leaf.SelfApplicableMix

set_option autoImplicit false

/-! ## 1. First-Order Value Domain (`MixSym`, `MixVal`) & Primitive Operations -/

/-- Open-ended symbol alphabet for AST tags, procedure identifiers, and user symbols. -/
inductive MixSym where
  | fst | snd | isPair | isZero | notB
  | cons | eq | add | sub | mul | lt
  | sVar | sLit | sUnary | sBin | sIfS | sLetS
  | dVar | dLit | dLift | dUnary | dBin | dIf | dWhile | dWithEnv | dCall
  | sIf | sLet | sCall | spCall
  | entry | eval | mem | append | evalS | specExpr | findAndSpec | specProc | dispatchCallee | processReqs
  | lit | var0 | var1 | ifPos | let1 | whilePos
  | user (id : Nat)
  deriving Repr

/-- Injective numeric code for `MixSym` enabling O(1) kernel comparison and `Core4` lowering. -/
@[expose] def MixSym.toCode : MixSym → Nat
  | .fst => 0 | .snd => 1 | .isPair => 2 | .isZero => 3 | .notB => 4
  | .cons => 5 | .eq => 6 | .add => 7 | .sub => 8 | .mul => 9 | .lt => 10
  | .sVar => 11 | .sLit => 12 | .sUnary => 13 | .sBin => 14 | .sIfS => 15 | .sLetS => 16
  | .dVar => 17 | .dLit => 18 | .dLift => 19 | .dUnary => 20 | .dBin => 21
  | .dIf => 22 | .dWhile => 23 | .dWithEnv => 24 | .dCall => 25
  | .sIf => 26 | .sLet => 27 | .sCall => 28 | .spCall => 29
  | .entry => 30 | .eval => 31 | .mem => 32 | .append => 33 | .evalS => 34
  | .specExpr => 35 | .findAndSpec => 36 | .specProc => 37 | .dispatchCallee => 38 | .processReqs => 39
  | .lit => 40 | .var0 => 41 | .var1 => 42 | .ifPos => 43 | .let1 => 44 | .whilePos => 45
  | .user k => 46 + k

private def MixSym.ofCode : Nat → MixSym
  | 0 => .fst | 1 => .snd | 2 => .isPair | 3 => .isZero | 4 => .notB
  | 5 => .cons | 6 => .eq | 7 => .add | 8 => .sub | 9 => .mul | 10 => .lt
  | 11 => .sVar | 12 => .sLit | 13 => .sUnary | 14 => .sBin | 15 => .sIfS | 16 => .sLetS
  | 17 => .dVar | 18 => .dLit | 19 => .dLift | 20 => .dUnary | 21 => .dBin
  | 22 => .dIf | 23 => .dWhile | 24 => .dWithEnv | 25 => .dCall
  | 26 => .sIf | 27 => .sLet | 28 => .sCall | 29 => .spCall
  | 30 => .entry | 31 => .eval | 32 => .mem | 33 => .append | 34 => .evalS
  | 35 => .specExpr | 36 => .findAndSpec | 37 => .specProc | 38 => .dispatchCallee | 39 => .processReqs
  | 40 => .lit | 41 => .var0 | 42 => .var1 | 43 => .ifPos | 44 => .let1 | 45 => .whilePos
  | n + 46 => .user n

private theorem MixSym.ofCode_toCode (t : MixSym) : MixSym.ofCode t.toCode = t := by
  cases t with
  | user k =>
    have hk : 46 + k = k + 46 := Nat.add_comm 46 k
    simp [MixSym.toCode, hk, MixSym.ofCode]
  | _ => rfl

private theorem MixSym.toCode_inj {a b : MixSym} (h : a.toCode = b.toCode) : a = b := by
  have := congrArg MixSym.ofCode h
  rwa [MixSym.ofCode_toCode, MixSym.ofCode_toCode] at this

instance : BEq MixSym where
  beq a b := Nat.beq a.toCode b.toCode

instance : LawfulBEq MixSym where
  rfl {a} := Nat.beq_refl a.toCode
  eq_of_beq {_ _} h := MixSym.toCode_inj (Nat.eq_of_beq_eq_true h)

instance : DecidableEq MixSym := fun a b =>
  if h : a == b then isTrue (eq_of_beq h) else isFalse (fun hab => h (hab ▸ Nat.beq_refl a.toCode))

/-- Universal S-expression value domain carrying scalars, symbols, pairs, and quoted `MixProg` ASTs. -/
inductive MixVal where
  | nil : MixVal
  | num (n : Nat) : MixVal
  | sym (s : MixSym) : MixVal
  | pair (fst snd : MixVal) : MixVal
  deriving Repr

/-- Proof-free structural `Bool` equality on `MixVal`. -/
@[expose] def MixVal.beq : MixVal → MixVal → Bool
  | .nil, .nil => true
  | .num a, .num b => Nat.beq a b
  | .sym a, .sym b => Nat.beq a.toCode b.toCode
  | .pair a1 a2, .pair b1 b2 => MixVal.beq a1 b1 && MixVal.beq a2 b2
  | _, _ => false

instance : BEq MixVal where
  beq := MixVal.beq

private theorem mixVal_beq_refl (v : MixVal) : MixVal.beq v v = true := by
  induction v with
  | nil => rfl
  | num n => exact Nat.beq_refl n
  | sym s => exact Nat.beq_refl s.toCode
  | pair a b iha ihb => simp [MixVal.beq, iha, ihb]

private theorem mixVal_eq_of_beq : {a b : MixVal} → MixVal.beq a b = true → a = b
  | .nil, .nil, _ => rfl
  | .num a, .num b, h => congrArg MixVal.num (Nat.eq_of_beq_eq_true h)
  | .sym a, .sym b, h => congrArg MixVal.sym (MixSym.toCode_inj (Nat.eq_of_beq_eq_true h))
  | .pair a1 a2, .pair b1 b2, h => by
    simp only [MixVal.beq, Bool.and_eq_true] at h
    rw [mixVal_eq_of_beq h.1, mixVal_eq_of_beq h.2]

instance : LawfulBEq MixVal where
  rfl {a} := mixVal_beq_refl a
  eq_of_beq := mixVal_eq_of_beq

instance : DecidableEq MixVal := fun a b =>
  if h : a == b then isTrue (eq_of_beq h) else isFalse (fun hab => h (hab ▸ beq_self_eq_true a))

/-- Truthiness test on `MixVal`: `.nil` and `.num 0` are false; all other values are true. -/
@[expose] def MixVal.isTrue : MixVal → Bool
  | .nil => false
  | .num 0 => false
  | _ => true

/-- Unary operations on `MixVal`. -/
inductive MixUnaryOp where
  | fst | snd | isPair | isZero | notB
  deriving DecidableEq, Repr

/-- Binary operations on `MixVal`. -/
inductive MixBinOp where
  | cons | eq | add | sub | mul | lt
  deriving DecidableEq, Repr

/-- Total evaluation of unary operations on `MixVal`. -/
@[expose] def evalUnary : MixUnaryOp → MixVal → MixVal
  | .fst, .pair a _ => a
  | .fst, _ => .nil
  | .snd, .pair _ b => b
  | .snd, _ => .nil
  | .isPair, .pair _ _ => .num 1
  | .isPair, _ => .num 0
  | .isZero, .num 0 => .num 1
  | .isZero, _ => .num 0
  | .notB, v => if v.isTrue then .num 0 else .num 1

/-- Total evaluation of binary operations on `MixVal`. -/
@[expose] def evalBin : MixBinOp → MixVal → MixVal → MixVal
  | .cons, a, b => .pair a b
  | .eq, a, b => if a == b then .num 1 else .num 0
  | .add, .num a, .num b => .num (a + b)
  | .add, _, _ => .num 0
  | .sub, .num a, .num b => .num (a - b)
  | .sub, _, _ => .num 0
  | .mul, .num a, .num b => .num (a * b)
  | .mul, _, _ => .num 0
  | .lt, .num a, .num b => if a < b then .num 1 else .num 0
  | .lt, _, _ => .num 0

/-! ## 2. Two-Level Object Language (`SExpr`, `MixExpr`, `MixProc`, `MixProg`) -/

/-- Purely static expressions evaluated over the static environment `s : MixVal`. -/
inductive SExpr where
  | var : SExpr
  | lit (v : MixVal) : SExpr
  | unary (op : MixUnaryOp) (e : SExpr) : SExpr
  | bin (op : MixBinOp) (e1 e2 : SExpr) : SExpr
  | ifS (cond eThen eElse : SExpr) : SExpr
  | letS (bound body : SExpr) : SExpr
  deriving DecidableEq, Repr

/-- Two-level Binding-Time-Annotated expressions over `(s, d : MixVal)`. -/
inductive MixExpr where
  | dVar : MixExpr
  | dLit (v : MixVal) : MixExpr
  | dLift (se : SExpr) : MixExpr
  | dUnary (op : MixUnaryOp) (e : MixExpr) : MixExpr
  | dBin (op : MixBinOp) (e1 e2 : MixExpr) : MixExpr
  | dIf (cond eThen eElse : MixExpr) : MixExpr
  | dWhile (cond body : MixExpr) : MixExpr
  | dWithEnv (envExpr body : MixExpr) : MixExpr
  | dCall (callee : MixVal) (dArg : MixExpr) : MixExpr
  | sIf (cond : SExpr) (eThen eElse : MixExpr) : MixExpr
  | sLet (bound : SExpr) (body : MixExpr) : MixExpr
  | sCall (callee : MixVal) (sArg : SExpr) (dArg : MixExpr) : MixExpr
  | spCall (callee : MixVal) (sKey : SExpr) (dArg : MixExpr) : MixExpr
  deriving DecidableEq, Repr

/-- Named first-order procedure taking `(s, d : MixVal)`. -/
structure MixProc where
  name : MixVal
  body : MixExpr
  deriving DecidableEq, Repr

/-- Complete `MixProg` program: entry procedure identifier and procedure table. -/
structure MixProg where
  entry : MixVal
  procs : List MixProc
  deriving DecidableEq, Repr

def sexprSize : SExpr → Nat
  | .var | .lit _ => 1
  | .unary _ e => 1 + sexprSize e
  | .bin _ e1 e2 | .letS e1 e2 => 1 + sexprSize e1 + sexprSize e2
  | .ifS c t f => 1 + sexprSize c + sexprSize t + sexprSize f

def exprSize : MixExpr → Nat
  | .dVar | .dLit _ => 1
  | .dLift se => 1 + sexprSize se
  | .dUnary _ e | .dCall _ e => 1 + exprSize e
  | .dBin _ e1 e2 | .dWhile e1 e2 | .dWithEnv e1 e2 => 1 + exprSize e1 + exprSize e2
  | .dIf c t f => 1 + exprSize c + exprSize t + exprSize f
  | .sIf c t f => 1 + sexprSize c + exprSize t + exprSize f
  | .sLet b body => 1 + sexprSize b + exprSize body
  | .sCall _ sArg dArg | .spCall _ sArg dArg => 1 + sexprSize sArg + exprSize dArg

def progSize (p : MixProg) : Nat :=
  p.procs.foldl (fun acc pr => acc + exprSize pr.body) 0

def exprHasStatic : MixExpr → Bool
  | .dVar | .dLit _ => false
  | .dUnary _ e | .dCall _ e => exprHasStatic e
  | .dBin _ e1 e2 | .dWhile e1 e2 | .dWithEnv e1 e2 => exprHasStatic e1 || exprHasStatic e2
  | .dIf c t f => exprHasStatic c || exprHasStatic t || exprHasStatic f
  | .dLift _ | .sIf _ _ _ | .sLet _ _ | .sCall _ _ _ | .spCall _ _ _ => true

def hasStaticConstruct (p : MixProg) : Bool :=
  p.procs.any fun pr => exprHasStatic pr.body

/-! ## 3. Canonical Quotation (`quoteProg`) & Primitive-Fuel Unquotation (`unquoteProg?`, `unquote_quote`) -/

def quoteUnaryOp : MixUnaryOp → MixVal
  | .fst => .sym .fst | .snd => .sym .snd | .isPair => .sym .isPair
  | .isZero => .sym .isZero | .notB => .sym .notB

def unquoteUnaryOp? : MixVal → Option MixUnaryOp
  | .sym .fst => some .fst | .sym .snd => some .snd | .sym .isPair => some .isPair
  | .sym .isZero => some .isZero | .sym .notB => some .notB
  | _ => none

def quoteBinOp : MixBinOp → MixVal
  | .cons => .sym .cons | .eq => .sym .eq | .add => .sym .add
  | .sub => .sym .sub | .mul => .sym .mul | .lt => .sym .lt

def unquoteBinOp? : MixVal → Option MixBinOp
  | .sym .cons => some .cons | .sym .eq => some .eq | .sym .add => some .add
  | .sym .sub => some .sub | .sym .mul => some .mul | .sym .lt => some .lt
  | _ => none

def quoteSExpr : SExpr → MixVal
  | .var => .pair (.sym .sVar) .nil
  | .lit v => .pair (.sym .sLit) v
  | .unary op e => .pair (.sym .sUnary) (.pair (quoteUnaryOp op) (quoteSExpr e))
  | .bin op e1 e2 => .pair (.sym .sBin) (.pair (quoteBinOp op) (.pair (quoteSExpr e1) (quoteSExpr e2)))
  | .ifS c t f => .pair (.sym .sIfS) (.pair (quoteSExpr c) (.pair (quoteSExpr t) (quoteSExpr f)))
  | .letS b body => .pair (.sym .sLetS) (.pair (quoteSExpr b) (quoteSExpr body))

def quoteExpr : MixExpr → MixVal
  | .dVar => .pair (.sym .dVar) .nil
  | .dLit v => .pair (.sym .dLit) v
  | .dLift se => .pair (.sym .dLift) (quoteSExpr se)
  | .dUnary op e => .pair (.sym .dUnary) (.pair (quoteUnaryOp op) (quoteExpr e))
  | .dBin op e1 e2 => .pair (.sym .dBin) (.pair (quoteBinOp op) (.pair (quoteExpr e1) (quoteExpr e2)))
  | .dIf c t f => .pair (.sym .dIf) (.pair (quoteExpr c) (.pair (quoteExpr t) (quoteExpr f)))
  | .dWhile c b => .pair (.sym .dWhile) (.pair (quoteExpr c) (quoteExpr b))
  | .dWithEnv e1 e2 => .pair (.sym .dWithEnv) (.pair (quoteExpr e1) (quoteExpr e2))
  | .dCall c dArg => .pair (.sym .dCall) (.pair c (quoteExpr dArg))
  | .sIf c t f => .pair (.sym .sIf) (.pair (quoteSExpr c) (.pair (quoteExpr t) (quoteExpr f)))
  | .sLet b body => .pair (.sym .sLet) (.pair (quoteSExpr b) (quoteExpr body))
  | .sCall c sArg dArg => .pair (.sym .sCall) (.pair c (.pair (quoteSExpr sArg) (quoteExpr dArg)))
  | .spCall c sKey dArg => .pair (.sym .spCall) (.pair c (.pair (quoteSExpr sKey) (quoteExpr dArg)))

def quoteProc (p : MixProc) : MixVal := .pair p.name (quoteExpr p.body)

def quoteProcs : List MixProc → MixVal
  | [] => .nil
  | p :: ps => .pair (quoteProc p) (quoteProcs ps)

/-- Encode a `MixProg` AST as a first-order `MixVal` datum. -/
def quoteProg (p : MixProg) : MixVal := .pair p.entry (quoteProcs p.procs)

private def mixValDepth : MixVal → Nat
  | .pair a b => max (mixValDepth a) (mixValDepth b) + 1
  | _ => 0

private def unquoteSExprAux : Nat → MixVal → Option SExpr
  | 0, _ => none
  | k + 1, .pair (.sym tag) pay =>
    match tag, pay with
    | .sVar, .nil => some .var
    | .sLit, p => some (.lit p)
    | .sUnary, .pair qOp qE =>
      match unquoteUnaryOp? qOp, unquoteSExprAux k qE with
      | some op, some e => some (.unary op e) | _, _ => none
    | .sBin, .pair qOp (.pair qE1 qE2) =>
      match unquoteBinOp? qOp, unquoteSExprAux k qE1, unquoteSExprAux k qE2 with
      | some op, some e1, some e2 => some (.bin op e1 e2) | _, _, _ => none
    | .sIfS, .pair qC (.pair qT qF) =>
      match unquoteSExprAux k qC, unquoteSExprAux k qT, unquoteSExprAux k qF with
      | some c, some t, some f => some (.ifS c t f) | _, _, _ => none
    | .sLetS, .pair qB qBody =>
      match unquoteSExprAux k qB, unquoteSExprAux k qBody with
      | some b, some body => some (.letS b body) | _, _ => none
    | _, _ => none
  | _ + 1, _ => none

def unquoteSExpr? (v : MixVal) : Option SExpr := unquoteSExprAux (mixValDepth v + 1) v

private def unquoteExprAux : Nat → MixVal → Option MixExpr
  | 0, _ => none
  | k + 1, .pair (.sym tag) pay =>
    match tag, pay with
    | .dVar, .nil => some .dVar
    | .dLit, p => some (.dLit p)
    | .dLift, p => match unquoteSExpr? p with | some se => some (.dLift se) | none => none
    | .dUnary, .pair qOp qE =>
      match unquoteUnaryOp? qOp, unquoteExprAux k qE with
      | some op, some e => some (.dUnary op e) | _, _ => none
    | .dBin, .pair qOp (.pair qE1 qE2) =>
      match unquoteBinOp? qOp, unquoteExprAux k qE1, unquoteExprAux k qE2 with
      | some op, some e1, some e2 => some (.dBin op e1 e2) | _, _, _ => none
    | .dIf, .pair qC (.pair qT qF) =>
      match unquoteExprAux k qC, unquoteExprAux k qT, unquoteExprAux k qF with
      | some c, some t, some f => some (.dIf c t f) | _, _, _ => none
    | .dWhile, .pair qC qB =>
      match unquoteExprAux k qC, unquoteExprAux k qB with
      | some c, some b => some (.dWhile c b) | _, _ => none
    | .dWithEnv, .pair qE1 qE2 =>
      match unquoteExprAux k qE1, unquoteExprAux k qE2 with
      | some e1, some e2 => some (.dWithEnv e1 e2) | _, _ => none
    | .dCall, .pair c qDArg =>
      match unquoteExprAux k qDArg with | some dArg => some (.dCall c dArg) | none => none
    | .sIf, .pair qC (.pair qT qF) =>
      match unquoteSExpr? qC, unquoteExprAux k qT, unquoteExprAux k qF with
      | some c, some t, some f => some (.sIf c t f) | _, _, _ => none
    | .sLet, .pair qB qBody =>
      match unquoteSExpr? qB, unquoteExprAux k qBody with
      | some b, some body => some (.sLet b body) | _, _ => none
    | .sCall, .pair c (.pair qSArg qDArg) =>
      match unquoteSExpr? qSArg, unquoteExprAux k qDArg with
      | some sArg, some dArg => some (.sCall c sArg dArg) | _, _ => none
    | .spCall, .pair c (.pair qSKey qDArg) =>
      match unquoteSExpr? qSKey, unquoteExprAux k qDArg with
      | some sKey, some dArg => some (.spCall c sKey dArg) | _, _ => none
    | _, _ => none
  | _ + 1, _ => none

def unquoteExpr? (v : MixVal) : Option MixExpr := unquoteExprAux (mixValDepth v + 1) v

def unquoteProc? : MixVal → Option MixProc
  | .pair name qBody =>
    match unquoteExpr? qBody with
    | some body => some { name := name, body := body }
    | none => none
  | _ => none

private def unquoteProcsAux : Nat → MixVal → Option (List MixProc)
  | 0, _ => none
  | _ + 1, .nil => some []
  | k + 1, .pair qP qPs =>
    match unquoteProc? qP, unquoteProcsAux k qPs with
    | some p, some ps => some (p :: ps)
    | _, _ => none
  | _ + 1, _ => none

def unquoteProcs? (v : MixVal) : Option (List MixProc) := unquoteProcsAux (mixValDepth v + 1) v

/-- Decode a `MixProg` AST from a `MixVal` datum. -/
def unquoteProg? : MixVal → Option MixProg
  | .pair entry qProcs =>
    match unquoteProcs? qProcs with
    | some procs => some { entry := entry, procs := procs }
    | none => none
  | _ => none

private theorem unquote_quoteUnaryOp (op : MixUnaryOp) : unquoteUnaryOp? (quoteUnaryOp op) = some op := by
  cases op <;> rfl

private theorem unquote_quoteBinOp (op : MixBinOp) : unquoteBinOp? (quoteBinOp op) = some op := by
  cases op <;> rfl

private theorem unquoteSExprAux_quote (se : SExpr) :
    ∀ k, mixValDepth (quoteSExpr se) < k → unquoteSExprAux k (quoteSExpr se) = some se := by
  induction se with
  | var | lit _ => intro k hk; cases k; omega; rfl
  | unary op e ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteSExpr, mixValDepth] at hk
      simp [quoteSExpr, unquoteSExprAux, unquote_quoteUnaryOp, ih k (by omega)]
  | bin op e1 e2 ih1 ih2 =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteSExpr, mixValDepth] at hk
      simp [quoteSExpr, unquoteSExprAux, unquote_quoteBinOp, ih1 k (by omega), ih2 k (by omega)]
  | ifS c t f ihc iht ihf =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteSExpr, mixValDepth] at hk
      simp [quoteSExpr, unquoteSExprAux, ihc k (by omega), iht k (by omega), ihf k (by omega)]
  | letS b body ihb ihbody =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteSExpr, mixValDepth] at hk
      simp [quoteSExpr, unquoteSExprAux, ihb k (by omega), ihbody k (by omega)]

theorem unquote_quoteSExpr (se : SExpr) : unquoteSExpr? (quoteSExpr se) = some se :=
  unquoteSExprAux_quote se _ (Nat.lt_succ_self _)

private theorem unquoteExprAux_quote (e : MixExpr) :
    ∀ k, mixValDepth (quoteExpr e) < k → unquoteExprAux k (quoteExpr e) = some e := by
  induction e with
  | dVar | dLit _ => intro k hk; cases k; omega; rfl
  | dLift se => intro k hk; cases k; omega; simp [quoteExpr, unquoteExprAux, unquote_quoteSExpr]
  | dUnary op e ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteUnaryOp, ih k (by omega)]
  | dBin op e1 e2 ih1 ih2 =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteBinOp, ih1 k (by omega), ih2 k (by omega)]
  | dIf c t f ihc iht ihf =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, ihc k (by omega), iht k (by omega), ihf k (by omega)]
  | dWhile c b ihc ihb =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, ihc k (by omega), ihb k (by omega)]
  | dWithEnv e1 e2 ih1 ih2 =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, ih1 k (by omega), ih2 k (by omega)]
  | dCall c dArg ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, ih k (by omega)]
  | sIf c t f iht ihf =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteSExpr, iht k (by omega), ihf k (by omega)]
  | sLet b body ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteSExpr, ih k (by omega)]
  | sCall c sArg dArg ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteSExpr, ih k (by omega)]
  | spCall c sKey dArg ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      simp only [quoteExpr, mixValDepth] at hk
      simp [quoteExpr, unquoteExprAux, unquote_quoteSExpr, ih k (by omega)]

theorem unquote_quoteExpr (e : MixExpr) : unquoteExpr? (quoteExpr e) = some e :=
  unquoteExprAux_quote e _ (Nat.lt_succ_self _)

instance : BEq MixExpr where
  beq a b := MixVal.beq (quoteExpr a) (quoteExpr b)

instance : LawfulBEq MixExpr where
  rfl {a} := mixVal_beq_refl (quoteExpr a)
  eq_of_beq {a b} h := by
    have hu := congrArg unquoteExpr? (mixVal_eq_of_beq h)
    rw [unquote_quoteExpr, unquote_quoteExpr] at hu
    injection hu

private theorem unquoteProcsAux_quote (ps : List MixProc) :
    ∀ k, mixValDepth (quoteProcs ps) < k → unquoteProcsAux k (quoteProcs ps) = some ps := by
  induction ps with
  | nil => intro k hk; cases k; omega; rfl
  | cons p rest ih =>
    intro k hk; cases k with | zero => omega | succ k =>
      cases p; simp only [quoteProcs, mixValDepth] at hk
      simp [quoteProcs, quoteProc, unquoteProcsAux, unquoteProc?, unquote_quoteExpr, ih k (by omega)]

/-- **Quotation Round-Trip (`unquote_quote`)**: Every `MixProg` encodes losslessly into `MixVal`. -/
theorem unquote_quote (p : MixProg) : unquoteProg? (quoteProg p) = some p := by
  cases p; simp [quoteProg, unquoteProg?, unquoteProcs?, unquoteProcsAux_quote _ _ (Nat.lt_succ_self _)]

private theorem quote_of_unquoteUnaryOp {v : MixVal} {op : MixUnaryOp}
    (h : unquoteUnaryOp? v = some op) : v = quoteUnaryOp op := by
  cases v with
  | sym t => cases t <;> simp [unquoteUnaryOp?] at h <;> subst h <;> rfl
  | _ => simp [unquoteUnaryOp?] at h

private theorem quote_of_unquoteBinOp {v : MixVal} {op : MixBinOp}
    (h : unquoteBinOp? v = some op) : v = quoteBinOp op := by
  cases v with
  | sym t => cases t <;> simp [unquoteBinOp?] at h <;> subst h <;> rfl
  | _ => simp [unquoteBinOp?] at h

private theorem quote_of_unquoteSExprAux :
    ∀ (k : Nat) {v : MixVal} {se : SExpr}, unquoteSExprAux k v = some se → v = quoteSExpr se
  | 0, _, _, h => by simp [unquoteSExprAux] at h
  | k + 1, v, se, h => by
    cases v with
    | nil | num _ | sym _ => simp [unquoteSExprAux] at h
    | pair a pay =>
      cases a with
      | nil | num _ | pair _ _ => simp [unquoteSExprAux] at h
      | sym tag =>
        cases tag with
        | sVar => cases pay <;> simp [unquoteSExprAux] at h; subst h; rfl
        | sLit => simp [unquoteSExprAux] at h; subst h; rfl
        | sUnary =>
          cases pay with
          | pair qOp qE =>
            simp only [unquoteSExprAux] at h
            cases hop : unquoteUnaryOp? qOp <;> cases he : unquoteSExprAux k qE <;> simp [hop, he] at h
            subst h; rw [quote_of_unquoteUnaryOp hop, quote_of_unquoteSExprAux k he]; rfl
          | _ => simp [unquoteSExprAux] at h
        | sBin =>
          cases pay with
          | pair qOp rest =>
            cases rest with
            | pair qE1 qE2 =>
              simp only [unquoteSExprAux] at h
              cases hop : unquoteBinOp? qOp <;> cases he1 : unquoteSExprAux k qE1 <;>
                cases he2 : unquoteSExprAux k qE2 <;> simp [hop, he1, he2] at h
              subst h
              rw [quote_of_unquoteBinOp hop, quote_of_unquoteSExprAux k he1, quote_of_unquoteSExprAux k he2]; rfl
            | _ => simp [unquoteSExprAux] at h
          | _ => simp [unquoteSExprAux] at h
        | sIfS =>
          cases pay with
          | pair qC rest =>
            cases rest with
            | pair qT qF =>
              simp only [unquoteSExprAux] at h
              cases hc : unquoteSExprAux k qC <;> cases ht : unquoteSExprAux k qT <;>
                cases hf : unquoteSExprAux k qF <;> simp [hc, ht, hf] at h
              subst h
              rw [quote_of_unquoteSExprAux k hc, quote_of_unquoteSExprAux k ht, quote_of_unquoteSExprAux k hf]; rfl
            | _ => simp [unquoteSExprAux] at h
          | _ => simp [unquoteSExprAux] at h
        | sLetS =>
          cases pay with
          | pair qB qBody =>
            simp only [unquoteSExprAux] at h
            cases hb : unquoteSExprAux k qB <;> cases hbody : unquoteSExprAux k qBody <;> simp [hb, hbody] at h
            subst h; rw [quote_of_unquoteSExprAux k hb, quote_of_unquoteSExprAux k hbody]; rfl
          | _ => simp [unquoteSExprAux] at h
        | _ => simp [unquoteSExprAux] at h

private theorem quote_of_unquoteSExpr {v : MixVal} {se : SExpr}
    (h : unquoteSExpr? v = some se) : v = quoteSExpr se :=
  quote_of_unquoteSExprAux _ h

private theorem quote_of_unquoteExprAux :
    ∀ (k : Nat) {v : MixVal} {e : MixExpr}, unquoteExprAux k v = some e → v = quoteExpr e
  | 0, _, _, h => by simp [unquoteExprAux] at h
  | k + 1, v, e, h => by
    cases v with
    | nil | num _ | sym _ => simp [unquoteExprAux] at h
    | pair a pay =>
      cases a with
      | nil | num _ | pair _ _ => simp [unquoteExprAux] at h
      | sym tag =>
        cases tag with
        | dVar => cases pay <;> simp [unquoteExprAux] at h; subst h; rfl
        | dLit => simp [unquoteExprAux] at h; subst h; rfl
        | dLift =>
          simp only [unquoteExprAux] at h
          cases hse : unquoteSExpr? pay <;> simp [hse] at h
          subst h; rw [quote_of_unquoteSExpr hse]; rfl
        | dUnary =>
          cases pay with
          | pair qOp qE =>
            simp only [unquoteExprAux] at h
            cases hop : unquoteUnaryOp? qOp <;> cases he : unquoteExprAux k qE <;> simp [hop, he] at h
            subst h; rw [quote_of_unquoteUnaryOp hop, quote_of_unquoteExprAux k he]; rfl
          | _ => simp [unquoteExprAux] at h
        | dBin =>
          cases pay with
          | pair qOp rest =>
            cases rest with
            | pair qE1 qE2 =>
              simp only [unquoteExprAux] at h
              cases hop : unquoteBinOp? qOp <;> cases he1 : unquoteExprAux k qE1 <;>
                cases he2 : unquoteExprAux k qE2 <;> simp [hop, he1, he2] at h
              subst h
              rw [quote_of_unquoteBinOp hop, quote_of_unquoteExprAux k he1, quote_of_unquoteExprAux k he2]; rfl
            | _ => simp [unquoteExprAux] at h
          | _ => simp [unquoteExprAux] at h
        | dIf =>
          cases pay with
          | pair qC rest =>
            cases rest with
            | pair qT qF =>
              simp only [unquoteExprAux] at h
              cases hc : unquoteExprAux k qC <;> cases ht : unquoteExprAux k qT <;>
                cases hf : unquoteExprAux k qF <;> simp [hc, ht, hf] at h
              subst h
              rw [quote_of_unquoteExprAux k hc, quote_of_unquoteExprAux k ht, quote_of_unquoteExprAux k hf]; rfl
            | _ => simp [unquoteExprAux] at h
          | _ => simp [unquoteExprAux] at h
        | dWhile =>
          cases pay with
          | pair qC qB =>
            simp only [unquoteExprAux] at h
            cases hc : unquoteExprAux k qC <;> cases hb : unquoteExprAux k qB <;> simp [hc, hb] at h
            subst h; rw [quote_of_unquoteExprAux k hc, quote_of_unquoteExprAux k hb]; rfl
          | _ => simp [unquoteExprAux] at h
        | dWithEnv =>
          cases pay with
          | pair qE1 qE2 =>
            simp only [unquoteExprAux] at h
            cases he1 : unquoteExprAux k qE1 <;> cases he2 : unquoteExprAux k qE2 <;> simp [he1, he2] at h
            subst h; rw [quote_of_unquoteExprAux k he1, quote_of_unquoteExprAux k he2]; rfl
          | _ => simp [unquoteExprAux] at h
        | dCall =>
          cases pay with
          | pair c qDArg =>
            simp only [unquoteExprAux] at h
            cases hd : unquoteExprAux k qDArg <;> simp [hd] at h
            subst h; rw [quote_of_unquoteExprAux k hd]; rfl
          | _ => simp [unquoteExprAux] at h
        | sIf =>
          cases pay with
          | pair qC rest =>
            cases rest with
            | pair qT qF =>
              simp only [unquoteExprAux] at h
              cases hc : unquoteSExpr? qC <;> cases ht : unquoteExprAux k qT <;>
                cases hf : unquoteExprAux k qF <;> simp [hc, ht, hf] at h
              subst h
              rw [quote_of_unquoteSExpr hc, quote_of_unquoteExprAux k ht, quote_of_unquoteExprAux k hf]; rfl
            | _ => simp [unquoteExprAux] at h
          | _ => simp [unquoteExprAux] at h
        | sLet =>
          cases pay with
          | pair qB qBody =>
            simp only [unquoteExprAux] at h
            cases hb : unquoteSExpr? qB <;> cases hbody : unquoteExprAux k qBody <;> simp [hb, hbody] at h
            subst h; rw [quote_of_unquoteSExpr hb, quote_of_unquoteExprAux k hbody]; rfl
          | _ => simp [unquoteExprAux] at h
        | sCall =>
          cases pay with
          | pair c rest =>
            cases rest with
            | pair qSArg qDArg =>
              simp only [unquoteExprAux] at h
              cases hs : unquoteSExpr? qSArg <;> cases hd : unquoteExprAux k qDArg <;> simp [hs, hd] at h
              subst h; rw [quote_of_unquoteSExpr hs, quote_of_unquoteExprAux k hd]; rfl
            | _ => simp [unquoteExprAux] at h
          | _ => simp [unquoteExprAux] at h
        | spCall =>
          cases pay with
          | pair c rest =>
            cases rest with
            | pair qSKey qDArg =>
              simp only [unquoteExprAux] at h
              cases hs : unquoteSExpr? qSKey <;> cases hd : unquoteExprAux k qDArg <;> simp [hs, hd] at h
              subst h; rw [quote_of_unquoteSExpr hs, quote_of_unquoteExprAux k hd]; rfl
            | _ => simp [unquoteExprAux] at h
          | _ => simp [unquoteExprAux] at h
        | _ => simp [unquoteExprAux] at h

private theorem quote_of_unquoteProcsAux :
    ∀ (k : Nat) {v : MixVal} {ps : List MixProc}, unquoteProcsAux k v = some ps → v = quoteProcs ps
  | 0, _, _, h => by simp [unquoteProcsAux] at h
  | k + 1, v, ps, h => by
    cases v with
    | nil => simp only [unquoteProcsAux, Option.some.injEq] at h; subst h; rfl
    | num _ | sym _ => simp [unquoteProcsAux] at h
    | pair qP qPs =>
      simp only [unquoteProcsAux] at h
      cases hp : unquoteProc? qP <;> cases hps : unquoteProcsAux k qPs <;> simp [hp, hps] at h
      rename_i pr rest; subst h
      have hqp : qP = quoteProc pr := by
        cases qP <;> simp [unquoteProc?] at hp
        rename_i nm qb
        cases he : unquoteExpr? qb <;> simp [he] at hp
        subst hp; rw [quote_of_unquoteExprAux _ he]; rfl
      rw [hqp, quote_of_unquoteProcsAux k hps]; rfl

theorem quote_of_unquoteProg {v : MixVal} {p : MixProg}
    (h : unquoteProg? v = some p) : v = quoteProg p := by
  cases v <;> simp [unquoteProg?] at h
  rename_i entry qProcs
  cases hps : unquoteProcs? qProcs <;> simp [hps] at h
  subst h; rw [quote_of_unquoteProcsAux _ hps]; rfl

/-! ## 4. Total Fuel-Indexed Semantics (`evalSExpr`, `evalExpr`, `evalMix`) -/

/-- Total structural evaluator for static expressions `SExpr`. -/
@[expose] def evalSExpr : SExpr → MixVal → MixVal
  | .var, s => s
  | .lit v, _ => v
  | .unary op e, s => evalUnary op (evalSExpr e s)
  | .bin op e1 e2, s => evalBin op (evalSExpr e1 s) (evalSExpr e2 s)
  | .ifS c t f, s => if (evalSExpr c s).isTrue then evalSExpr t s else evalSExpr f s
  | .letS b body, s => evalSExpr body (.pair (evalSExpr b s) s)

/-- First-match procedure table lookup by `MixVal` procedure identifier. -/
@[expose] def lookupProc : List MixProc → MixVal → Option MixExpr
  | [], _ => none
  | p :: rest, name => if p.name == name then some p.body else lookupProc rest name

/-- Fuel-indexed evaluator for two-level `MixExpr` expressions. -/
@[expose] def evalExpr : Nat → List MixProc → MixExpr → MixVal → MixVal → Option MixVal
  | 0, _, _, _, _ => none
  | fuel + 1, procs, e, s, d =>
    match e with
    | .dVar => some d
    | .dLit v => some v
    | .dLift se => some (evalSExpr se s)
    | .dUnary op e1 =>
      match evalExpr fuel procs e1 s d with
      | some v1 => some (evalUnary op v1) | none => none
    | .dBin op e1 e2 =>
      match evalExpr fuel procs e1 s d with
      | some v1 =>
        match evalExpr fuel procs e2 s d with
        | some v2 => some (evalBin op v1 v2) | none => none
      | none => none
    | .dIf c t f =>
      match evalExpr fuel procs c s d with
      | some vc => if vc.isTrue then evalExpr fuel procs t s d else evalExpr fuel procs f s d
      | none => none
    | .dWhile c body =>
      match evalExpr fuel procs c s d with
      | some vc =>
        if vc.isTrue then
          match evalExpr fuel procs body s d with
          | some d' => evalExpr fuel procs (.dWhile c body) s d'
          | none => none
        else some d
      | none => none
    | .dWithEnv envE body =>
      match evalExpr fuel procs envE s d with
      | some d' => evalExpr fuel procs body s d' | none => none
    | .dCall callee dArg =>
      match evalExpr fuel procs dArg s d, lookupProc procs callee with
      | some dv, some body => evalExpr fuel procs body .nil dv | _, _ => none
    | .sIf c t f =>
      if (evalSExpr c s).isTrue then evalExpr fuel procs t s d else evalExpr fuel procs f s d
    | .sLet b body =>
      evalExpr fuel procs body (.pair (evalSExpr b s) s) d
    | .sCall callee sArg dArg =>
      match evalExpr fuel procs dArg s d, lookupProc procs callee with
      | some dv, some body => evalExpr fuel procs body (evalSExpr sArg s) dv | _, _ => none
    | .spCall callee sKey dArg =>
      match evalExpr fuel procs dArg s d, lookupProc procs callee with
      | some dv, some body => evalExpr fuel procs body (evalSExpr sKey s) dv | _, _ => none

/-- Total fuel-indexed interpreter for `MixProg` (`evalMix fuel p staticIn dynamicIn`). -/
@[expose] def evalMix (fuel : Nat) (p : MixProg) (staticIn dynamicIn : MixVal) : Option MixVal :=
  match lookupProc p.procs p.entry with
  | none => none
  | some body => evalExpr fuel p.procs body staticIn dynamicIn

theorem evalExpr_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (procs : List MixProc) (e : MixExpr) (s d v : MixVal)
    (h : evalExpr fuel procs e s d = some v) :
    evalExpr fuel' procs e s d = some v := by
  induction fuel generalizing fuel' e s d v with
  | zero => simp [evalExpr] at h
  | succ k ih =>
    cases fuel' with
    | zero => omega
    | succ k' =>
      have hk : k ≤ k' := by omega
      cases e <;> simp only [evalExpr] at h ⊢
      · exact h
      · exact h
      · exact h
      · rename_i op e1
        cases h1 : evalExpr k procs e1 s d <;> simp [h1] at h
        rw [ih hk e1 s d _ h1]; exact congrArg some h
      · rename_i op e1 e2
        cases h1 : evalExpr k procs e1 s d <;> simp [h1] at h
        cases h2 : evalExpr k procs e2 s d <;> simp [h2] at h
        rw [ih hk e1 s d _ h1, ih hk e2 s d _ h2]; exact congrArg some h
      · rename_i c t f
        cases hc : evalExpr k procs c s d <;> simp [hc] at h
        rename_i vc; rw [ih hk c s d vc hc]; dsimp only
        by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at h ⊢
        · exact ih hk t s d v h
        · exact ih hk f s d v h
      · rename_i c body
        cases hc : evalExpr k procs c s d <;> simp [hc] at h
        rename_i vc; rw [ih hk c s d vc hc]; dsimp only
        by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at h ⊢
        · cases hb : evalExpr k procs body s d <;> simp [hb] at h
          rename_i d'; rw [ih hk body s d d' hb]; dsimp only
          exact ih hk (.dWhile c body) s d' v h
        · exact h
      · rename_i e1 e2
        cases h1 : evalExpr k procs e1 s d <;> simp [h1] at h
        rename_i d'; rw [ih hk e1 s d d' h1]; dsimp only
        exact ih hk e2 s d' v h
      · rename_i callee dArg
        cases hd : evalExpr k procs dArg s d <;> cases hl : lookupProc procs callee <;> simp [hd, hl] at h
        rename_i dv body; rw [ih hk dArg s d dv hd]; exact ih hk body .nil dv v h
      · rename_i c t f
        by_cases hct : (evalSExpr c s).isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at h ⊢
        · exact ih hk t s d v h
        · exact ih hk f s d v h
      · rename_i b body
        exact ih hk body (.pair (evalSExpr b s) s) d v h
      · rename_i callee sArg dArg
        cases hd : evalExpr k procs dArg s d <;> cases hl : lookupProc procs callee <;> simp [hd, hl] at h
        rename_i dv body; rw [ih hk dArg s d dv hd]; exact ih hk body (evalSExpr sArg s) dv v h
      · rename_i callee sKey dArg
        cases hd : evalExpr k procs dArg s d <;> cases hl : lookupProc procs callee <;> simp [hd, hl] at h
        rename_i dv body; rw [ih hk dArg s d dv hd]; exact ih hk body (evalSExpr sKey s) dv v h

theorem evalMix_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (p : MixProg) (s d v : MixVal) (h : evalMix fuel p s d = some v) :
    evalMix fuel' p s d = some v := by
  unfold evalMix at h ⊢
  cases hl : lookupProc p.procs p.entry <;> simp [hl] at h ⊢
  exact evalExpr_mono hle p.procs _ s d v h

/-! ## 5. Encoding the Self-Applicable Two-Level Specializer `mixProg : MixProg` INSIDE `MixProg` -/

def sFst (e : SExpr) : SExpr := .unary .fst e
def sSnd (e : SExpr) : SExpr := .unary .snd e
def sEqSym (e : SExpr) (tag : MixSym) : SExpr := .bin .eq e (.lit (.sym tag))
def dFst (e : MixExpr) : MixExpr := .dUnary .fst e
def dSnd (e : MixExpr) : MixExpr := .dUnary .snd e
def dCons (a b : MixExpr) : MixExpr := .dBin .cons a b
private def dLet (val body : MixExpr) : MixExpr := .dWithEnv (dCons val .dVar) body

private def mkQuotedDLit (vExpr : MixExpr) : MixExpr := dCons (.dLit (.sym .dLit)) vExpr
private def mkQuotedDUnary (opVal : SExpr) (eExpr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dUnary)) (dCons (.dLift opVal) eExpr)
private def mkQuotedDBin (opVal : SExpr) (e1Expr e2Expr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dBin)) (dCons (.dLift opVal) (dCons e1Expr e2Expr))
private def mkQuotedDIf (cExpr tExpr fExpr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dIf)) (dCons cExpr (dCons tExpr fExpr))
private def mkQuotedDWhile (cExpr bExpr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dWhile)) (dCons cExpr bExpr)
private def mkQuotedDWithEnv (e1Expr e2Expr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dWithEnv)) (dCons e1Expr e2Expr)
private def mkQuotedDCall (cExpr dArgExpr : MixExpr) : MixExpr :=
  dCons (.dLit (.sym .dCall)) (dCons cExpr dArgExpr)
private def callAppend (xs ys : MixExpr) : MixExpr :=
  .spCall (.sym .append) (.lit .nil) (dCons xs ys)
private def callMem (x xs : MixExpr) : MixExpr :=
  .spCall (.sym .mem) (.lit .nil) (dCons x xs)

private def mixProcMem : MixProc :=
  { name := .sym .mem
  , body :=
      .dIf (.dUnary .isPair (dSnd .dVar))
        (.dIf (.dBin .eq (dFst .dVar) (dFst (dSnd .dVar)))
          (.dLit (.num 1))
          (callMem (dFst .dVar) (dSnd (dSnd .dVar))))
        (.dLit (.num 0)) }

private def mixProcAppend : MixProc :=
  { name := .sym .append
  , body :=
      .dIf (.dUnary .isPair (dFst .dVar))
        (.dIf (callMem (dFst (dFst .dVar)) (dSnd .dVar))
          (callAppend (dSnd (dFst .dVar)) (dSnd .dVar))
          (dCons (dFst (dFst .dVar)) (callAppend (dSnd (dFst .dVar)) (dSnd .dVar))))
        (dSnd .dVar) }

private def mixProcEvalS : MixProc :=
  let tag := sFst .var; let pay := sSnd .var; let opSym := sFst pay
  let sub1 := MixExpr.sCall (.sym .evalS) (sSnd pay) .dVar
  let subL := MixExpr.sCall (.sym .evalS) (sFst (sSnd pay)) .dVar
  let subR := MixExpr.sCall (.sym .evalS) (sSnd (sSnd pay)) .dVar
  { name := .sym .evalS
  , body :=
      .sIf (sEqSym tag .sVar) .dVar
      (.sIf (sEqSym tag .sLit) (.dLift pay)
      (.sIf (sEqSym tag .sUnary)
        (.sIf (sEqSym opSym .fst) (.dUnary .fst sub1)
        (.sIf (sEqSym opSym .snd) (.dUnary .snd sub1)
        (.sIf (sEqSym opSym .isPair) (.dUnary .isPair sub1)
        (.sIf (sEqSym opSym .isZero) (.dUnary .isZero sub1) (.dUnary .notB sub1)))))
      (.sIf (sEqSym tag .sBin)
        (.sIf (sEqSym opSym .cons) (.dBin .cons subL subR)
        (.sIf (sEqSym opSym .eq) (.dBin .eq subL subR)
        (.sIf (sEqSym opSym .add) (.dBin .add subL subR)
        (.sIf (sEqSym opSym .sub) (.dBin .sub subL subR)
        (.sIf (sEqSym opSym .mul) (.dBin .mul subL subR) (.dBin .lt subL subR))))))
      (.sIf (sEqSym tag .sIfS)
        (.dIf (.sCall (.sym .evalS) (sFst pay) .dVar) subL subR)
        (.dWithEnv (dCons (.sCall (.sym .evalS) (sFst pay) .dVar) .dVar) sub1))))) }

private def mixProcSpecExpr : MixProc :=
  let qExpr := sFst .var; let qProcs := sSnd .var
  let tag := sFst qExpr; let pay := sSnd qExpr
  let specSub (subS : SExpr) (envD : MixExpr) : MixExpr :=
    .sCall (.sym .specExpr) (.bin .cons subS qProcs) envD
  { name := .sym .specExpr
  , body :=
      .sIf (sEqSym tag .dVar) (.dLit (.pair (quoteExpr .dVar) .nil))
      (.sIf (sEqSym tag .dLit) (dCons (mkQuotedDLit (.dLift pay)) (.dLit .nil))
      (.sIf (sEqSym tag .dLift) (dCons (mkQuotedDLit (.sCall (.sym .evalS) pay .dVar)) (.dLit .nil))
      (.sIf (sEqSym tag .dUnary)
        (dLet (specSub (sSnd pay) .dVar)
          (dCons (mkQuotedDUnary (sFst pay) (dFst (dFst .dVar))) (dSnd (dFst .dVar))))
      (.sIf (sEqSym tag .dBin)
        (dLet (specSub (sFst (sSnd pay)) .dVar)
          (dLet (specSub (sSnd (sSnd pay)) (dSnd .dVar))
            (dCons
              (mkQuotedDBin (sFst pay) (dFst (dFst (dSnd .dVar))) (dFst (dFst .dVar)))
              (callAppend (dSnd (dFst (dSnd .dVar))) (dSnd (dFst .dVar))))))
      (.sIf (sEqSym tag .dIf)
        (dLet (specSub (sFst pay) .dVar)
          (dLet (specSub (sFst (sSnd pay)) (dSnd .dVar))
            (dLet (specSub (sSnd (sSnd pay)) (dSnd (dSnd .dVar)))
              (let rc := dFst (dSnd (dSnd .dVar)); let rt := dFst (dSnd .dVar); let rf := dFst .dVar
               dCons (mkQuotedDIf (dFst rc) (dFst rt) (dFst rf))
                (callAppend (dSnd rc) (callAppend (dSnd rt) (dSnd rf)))))))
      (.sIf (sEqSym tag .dWhile)
        (dLet (specSub (sFst pay) .dVar)
          (dLet (specSub (sSnd pay) (dSnd .dVar))
            (let rc := dFst (dSnd .dVar); let rb := dFst .dVar
             dCons (mkQuotedDWhile (dFst rc) (dFst rb)) (callAppend (dSnd rc) (dSnd rb)))))
      (.sIf (sEqSym tag .dWithEnv)
        (dLet (specSub (sFst pay) .dVar)
          (dLet (specSub (sSnd pay) (dSnd .dVar))
            (let r1 := dFst (dSnd .dVar); let r2 := dFst .dVar
             dCons (mkQuotedDWithEnv (dFst r1) (dFst r2)) (callAppend (dSnd r1) (dSnd r2)))))
      (.sIf (sEqSym tag .dCall)
        (dLet (specSub (sSnd pay) .dVar)
          (let rd := dFst .dVar; let req := dCons (.dLift (sFst pay)) (.dLit .nil)
           dCons (mkQuotedDCall req (dFst rd)) (dCons req (dSnd rd))))
      (.sIf (sEqSym tag .sIf)
        (.dIf (.sCall (.sym .evalS) (sFst pay) .dVar)
          (specSub (sFst (sSnd pay)) .dVar) (specSub (sSnd (sSnd pay)) .dVar))
      (.sIf (sEqSym tag .sLet)
        (.dWithEnv (dCons (.sCall (.sym .evalS) (sFst pay) .dVar) .dVar) (specSub (sSnd pay) .dVar))
      (.sIf (sEqSym tag .sCall)
        (.sIf (.bin .eq (sSnd (sSnd pay)) (.lit (quoteExpr .dVar)))
          (.spCall (.sym .specProc) (.bin .cons (sFst pay) qProcs)
            (.sCall (.sym .evalS) (sFst (sSnd pay)) .dVar))
          (dLet (specSub (sSnd (sSnd pay)) .dVar)
            (dLet
              (.spCall (.sym .specProc) (.bin .cons (sFst pay) qProcs)
                (.sCall (.sym .evalS) (sFst (sSnd pay)) (dSnd .dVar)))
              (let rd := dFst (dSnd .dVar); let rb := dFst .dVar
               dCons (mkQuotedDWithEnv (dFst rd) (dFst rb)) (callAppend (dSnd rd) (dSnd rb))))))
        (dLet (specSub (sSnd (sSnd pay)) .dVar)
          (dLet (.sCall (.sym .evalS) (sFst (sSnd pay)) (dSnd .dVar))
            (let kv := dFst .dVar; let rd := dFst (dSnd .dVar)
             let req := dCons (.dLift (sFst pay)) kv
             dCons (mkQuotedDCall req (dFst rd)) (dCons req (dSnd rd)))))))))))))))) }

private def mixProcFindAndSpec : MixProc :=
  let callee := sFst .var; let qRest := sFst (sSnd .var); let qAll := sSnd (sSnd .var)
  let curProc := sFst qRest
  { name := .sym .findAndSpec
  , body :=
      .sIf (.unary .isPair qRest)
        (.sIf (.bin .eq (sFst curProc) callee)
          (.sCall (.sym .specExpr) (.bin .cons (sSnd curProc) qAll) .dVar)
          (.sCall (.sym .findAndSpec) (.bin .cons callee (.bin .cons (sSnd qRest) qAll)) .dVar))
        (.dLit (.pair (quoteExpr (.dLit .nil)) .nil)) }

private def mixProcSpecProc : MixProc :=
  { name := .sym .specProc
  , body :=
      .sCall (.sym .findAndSpec)
        (.bin .cons (sFst .var) (.bin .cons (sSnd .var) (sSnd .var))) .dVar }

private def mixProcDispatchCallee : MixProc :=
  let qRest := sFst .var; let qAll := sSnd .var; let curName := sFst (sFst qRest)
  { name := .sym .dispatchCallee
  , body :=
      .sIf (.unary .isPair qRest)
        (.dIf (.dBin .eq (dFst .dVar) (.dLift curName))
          (.spCall (.sym .specProc) (.bin .cons curName qAll) (dSnd .dVar))
          (.sCall (.sym .dispatchCallee) (.bin .cons (sSnd qRest) qAll) .dVar))
        (.dLit (.pair (quoteExpr (.dLit .nil)) .nil)) }

private def mixProcProcessReqs : MixProc :=
  let pending := dFst .dVar; let visited := dFst (dSnd .dVar); let acc := dSnd (dSnd .dVar)
  { name := .sym .processReqs
  , body :=
      dSnd (dSnd
        (.dWhile (.dUnary .isPair pending)
          (.dIf (callMem (dFst pending) visited)
            (dCons (dSnd pending) (dCons visited acc))
            (dLet (.sCall (.sym .dispatchCallee) (.bin .cons .var .var) (dFst pending))
              (let res := dFst .dVar; let oldSt := dSnd .dVar
               let rReq := dFst (dFst oldSt); let rRest := dSnd (dFst oldSt)
               let rVis := dFst (dSnd oldSt); let rAcc := dSnd (dSnd oldSt)
               dCons (callAppend (dSnd res) rRest)
                (dCons (dCons rReq rVis) (dCons (dCons rReq (dFst res)) rAcc))))))) }

private def mixProcEntry : MixProc :=
  { name := .sym .entry
  , body :=
      dLet (.spCall (.sym .specProc) (.bin .cons (sFst .var) (sSnd .var)) .dVar)
        (let r0 := dFst .dVar
         let entryProc := dCons (.dLit (.sym .entry)) (dFst r0)
         let extraProcs :=
           MixExpr.spCall (.sym .processReqs) (sSnd .var)
             (dCons (dSnd r0) (dCons (.dLit .nil) (.dLit .nil)))
         dCons (.dLit (.sym .entry)) (dCons entryProc extraProcs)) }

/-- **The Genuine Self-Applicable Two-Level Specializer (`mixProg : MixProg`)**:
    Encoded directly as a 9-procedure `MixProg` data value inside the object language itself. -/
def mixProg : MixProg :=
  { entry := .sym .entry
  , procs :=
      [ mixProcEntry, mixProcProcessReqs, mixProcDispatchCallee, mixProcSpecProc
      , mixProcFindAndSpec, mixProcSpecExpr, mixProcEvalS, mixProcMem, mixProcAppend ] }

/-! ## 6. Verified Specialization Certificate (`specShadow`, `checkSpecializesProg`) & Soundness -/

def specShadow : Nat → List MixProc → MixVal → MixExpr → Option MixExpr
  | 0, _, _, _ => none
  | kd + 1, origProcs, s, e =>
    match e with
    | .dVar => some .dVar
    | .dLit v => some (.dLit v)
    | .dLift se => some (.dLit (evalSExpr se s))
    | .dUnary op e1 =>
      match specShadow kd origProcs s e1 with | some r1 => some (.dUnary op r1) | none => none
    | .dBin op e1 e2 =>
      match specShadow kd origProcs s e1, specShadow kd origProcs s e2 with
      | some r1, some r2 => some (.dBin op r1 r2) | _, _ => none
    | .dIf c t f =>
      match specShadow kd origProcs s c, specShadow kd origProcs s t, specShadow kd origProcs s f with
      | some rc, some rt, some rf => some (.dIf rc rt rf) | _, _, _ => none
    | .dWhile c b =>
      match specShadow kd origProcs s c, specShadow kd origProcs s b with
      | some rc, some rb => some (.dWhile rc rb) | _, _ => none
    | .dWithEnv e1 e2 =>
      match specShadow kd origProcs s e1, specShadow kd origProcs s e2 with
      | some r1, some r2 => some (.dWithEnv r1 r2) | _, _ => none
    | .dCall c dArg =>
      match specShadow kd origProcs s dArg with
      | some rd => some (.dCall (.pair c .nil) rd) | none => none
    | .sIf c t f =>
      if (evalSExpr c s).isTrue then specShadow kd origProcs s t else specShadow kd origProcs s f
    | .sLet b body =>
      specShadow kd origProcs (.pair (evalSExpr b s) s) body
    | .sCall c sArg dArg =>
      match lookupProc origProcs c with
      | none => none
      | some origBody =>
        match specShadow kd origProcs (evalSExpr sArg s) origBody with
        | none => none
        | some rb =>
          if dArg = .dVar then some rb
          else match specShadow kd origProcs s dArg with
            | some rd => some (.dWithEnv rd rb) | none => none
    | .spCall c sKey dArg =>
      match specShadow kd origProcs s dArg with
      | some rd => some (.dCall (.pair c (evalSExpr sKey s)) rd) | none => none

def exprCallsClosed (resProcs : List MixProc) : MixExpr → Bool
  | .dVar | .dLit _ | .dLift _ => true
  | .dUnary _ e | .sLet _ e => exprCallsClosed resProcs e
  | .dBin _ e1 e2 | .dWhile e1 e2 | .dWithEnv e1 e2 | .sIf _ e1 e2 =>
    exprCallsClosed resProcs e1 && exprCallsClosed resProcs e2
  | .dIf c t f => exprCallsClosed resProcs c && exprCallsClosed resProcs t && exprCallsClosed resProcs f
  | .dCall target dArg =>
    (match target with | .pair _ _ => (lookupProc resProcs target).isSome | _ => false) &&
      exprCallsClosed resProcs dArg
  | .sCall _ _ dArg | .spCall _ _ dArg => exprCallsClosed resProcs dArg

def checkResProc (kd : Nat) (orig : MixProg) (s0 : MixVal) (resProcs : List MixProc) (pr : MixProc) : Bool :=
  (lookupProc resProcs pr.name == some pr.body) &&
  !exprHasStatic pr.body &&
  exprCallsClosed resProcs pr.body &&
  if pr.name == .sym .entry then
    match lookupProc orig.procs orig.entry with
    | some origEntry => specShadow kd orig.procs s0 origEntry == some pr.body
    | none => false
  else
    match pr.name with
    | .pair callee kv =>
      match lookupProc orig.procs callee with
      | some origBody => specShadow kd orig.procs kv origBody == some pr.body
      | none => false
    | _ => false

/-- Decidable specialization validator certifying that `res` is a sound, purely dynamic specialization of `orig` at `s0`. -/
def checkSpecializesProg (kd : Nat) (orig : MixProg) (s0 : MixVal) (res : MixProg) : Bool :=
  (res.entry == .sym .entry) &&
  !hasStaticConstruct res &&
  (match lookupProc orig.procs orig.entry, lookupProc res.procs (.sym .entry) with
   | some origEntry, some resEntry => specShadow kd orig.procs s0 origEntry == some resEntry
   | _, _ => false) &&
  res.procs.all (checkResProc kd orig s0 res.procs)

/-- Execute `mixProg` inside `evalMix` to specialize `p` at `s0` and unquote the emitted `MixProg`. -/
def runMixSpecialize (fuel : Nat) (p : MixProg) (s0 : MixVal) : Option MixProg :=
  match evalMix fuel mixProg (quoteProg p) s0 with
  | some qRes => unquoteProg? qRes
  | none => none

private theorem lookupProc_mem_of_some {procs : List MixProc} {name : MixVal} {body : MixExpr}
    (h : lookupProc procs name = some body) :
    ({ name := name, body := body } : MixProc) ∈ procs := by
  induction procs with
  | nil => simp [lookupProc] at h
  | cons p rest ih =>
    simp only [lookupProc] at h
    by_cases hEq : p.name == name
    · simp only [hEq, ↓reduceIte, Option.some.injEq] at h
      have hp : p.name = name := eq_of_beq hEq
      cases p; subst hp; subst h; exact List.Mem.head _
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h
      exact List.Mem.tail _ (ih h)

private theorem checkResProc_of_lookup {kd : Nat} {orig : MixProg} {s0 : MixVal} {res : MixProg}
    {c kv : MixVal} {resBody : MixExpr}
    (hProg : checkSpecializesProg kd orig s0 res = true)
    (hLook : lookupProc res.procs (.pair c kv) = some resBody) :
    ∃ origBody,
      lookupProc orig.procs c = some origBody ∧
      specShadow kd orig.procs kv origBody = some resBody ∧
      exprCallsClosed res.procs resBody = true := by
  have hMem := lookupProc_mem_of_some hLook
  unfold checkSpecializesProg at hProg
  simp only [Bool.and_eq_true, List.all_eq_true] at hProg
  have hPr := hProg.2 _ hMem
  unfold checkResProc at hPr
  have hNotEntry : ((MixVal.pair c kv == MixVal.sym .entry) = false) := rfl
  simp only [hNotEntry, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hPr
  cases hOrig : lookupProc orig.procs c with
  | none => simp [hOrig] at hPr
  | some origBody =>
    simp only [hOrig, beq_iff_eq] at hPr
    exact ⟨origBody, rfl, hPr.2, hPr.1.2⟩

private theorem specShadow_eval_forward
    {kd : Nat} {orig : MixProg} {s0 : MixVal} {res : MixProg}
    (hProg : checkSpecializesProg kd orig s0 res = true) :
    ∀ (fuel k : Nat) (s d v : MixVal) (e eRes : MixExpr),
      specShadow k orig.procs s e = some eRes →
      exprCallsClosed res.procs eRes = true →
      evalExpr fuel orig.procs e s d = some v →
      ∃ resFuel, evalExpr resFuel res.procs eRes .nil d = some v
  | 0, _, _, _, _, _, _, _, _, hEval => by simp [evalExpr] at hEval
  | _ + 1, 0, _, _, _, _, _, hSpec, _, _ => by simp [specShadow] at hSpec
  | fuel + 1, k + 1, s, d, v, e, eRes, hSpec, hClosed, hEval => by
    cases e <;> simp only [evalExpr] at hEval
    · simp only [specShadow, Option.some.injEq] at hSpec hEval; subst hSpec; subst hEval; exact ⟨1, rfl⟩
    · simp only [specShadow, Option.some.injEq] at hSpec hEval; subst hSpec; subst hEval; exact ⟨1, rfl⟩
    · simp only [specShadow, Option.some.injEq] at hSpec hEval; subst hSpec; subst hEval; exact ⟨1, rfl⟩
    · rename_i op e1; simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> simp [hs1] at hSpec; subst hSpec
      cases he1 : evalExpr fuel orig.procs e1 s d <;> simp [he1] at hEval; subst hEval
      obtain ⟨rf1, hrf1⟩ := specShadow_eval_forward hProg fuel k s d _ e1 _ hs1 hClosed he1
      exact ⟨rf1 + 1, by simp [evalExpr, hrf1]⟩
    · rename_i op e1 e2; simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> cases hs2 : specShadow k orig.procs s e2 <;> simp [hs1, hs2] at hSpec
      subst hSpec; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
      cases he1 : evalExpr fuel orig.procs e1 s d <;> cases he2 : evalExpr fuel orig.procs e2 s d <;> simp [he1, he2] at hEval
      subst hEval
      obtain ⟨rf1, hrf1⟩ := specShadow_eval_forward hProg fuel k s d _ e1 _ hs1 hClosed.1 he1
      obtain ⟨rf2, hrf2⟩ := specShadow_eval_forward hProg fuel k s d _ e2 _ hs2 hClosed.2 he2
      exact ⟨max rf1 rf2 + 1, by simp [evalExpr, evalExpr_mono (by omega : rf1 ≤ max rf1 rf2) _ _ _ _ _ hrf1,
        evalExpr_mono (by omega : rf2 ≤ max rf1 rf2) _ _ _ _ _ hrf2]⟩
    · rename_i c t f; simp only [specShadow] at hSpec
      cases hsc : specShadow k orig.procs s c <;> cases hst : specShadow k orig.procs s t <;>
        cases hsf : specShadow k orig.procs s f <;> simp [hsc, hst, hsf] at hSpec
      subst hSpec; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
      cases hec : evalExpr fuel orig.procs c s d <;> simp [hec] at hEval
      rename_i vc
      obtain ⟨rfc, hrfc⟩ := specShadow_eval_forward hProg fuel k s d vc c _ hsc hClosed.1.1 hec
      by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hEval
      · obtain ⟨rft, hrft⟩ := specShadow_eval_forward hProg fuel k s d v t _ hst hClosed.1.2 hEval
        exact ⟨max rfc rft + 1, by simp [evalExpr, evalExpr_mono (by omega : rfc ≤ max rfc rft) _ _ _ _ _ hrfc, hct,
          evalExpr_mono (by omega : rft ≤ max rfc rft) _ _ _ _ _ hrft]⟩
      · obtain ⟨rff, hrff⟩ := specShadow_eval_forward hProg fuel k s d v f _ hsf hClosed.2 hEval
        exact ⟨max rfc rff + 1, by simp [evalExpr, evalExpr_mono (by omega : rfc ≤ max rfc rff) _ _ _ _ _ hrfc, hct,
          evalExpr_mono (by omega : rff ≤ max rfc rff) _ _ _ _ _ hrff]⟩
    · rename_i c body; have hSpecOrig := hSpec; simp only [specShadow] at hSpec
      cases hsc : specShadow k orig.procs s c <;> cases hsb : specShadow k orig.procs s body <;> simp [hsc, hsb] at hSpec
      subst hSpec; have hClosedOrig := hClosed; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
      cases hec : evalExpr fuel orig.procs c s d <;> simp [hec] at hEval
      rename_i vc
      obtain ⟨rfc, hrfc⟩ := specShadow_eval_forward hProg fuel k s d vc c _ hsc hClosed.1 hec
      by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hEval
      · cases heb : evalExpr fuel orig.procs body s d <;> simp [heb] at hEval
        rename_i d'
        obtain ⟨rfb, hrfb⟩ := specShadow_eval_forward hProg fuel k s d d' body _ hsb hClosed.2 heb
        obtain ⟨rfL, hrfL⟩ := specShadow_eval_forward hProg fuel (k + 1) s d' v (.dWhile c body) _ hSpecOrig hClosedOrig hEval
        let m := max rfc (max rfb rfL)
        exact ⟨m + 1, by simp [evalExpr, evalExpr_mono (by omega : rfc ≤ m) _ _ _ _ _ hrfc, hct,
          evalExpr_mono (by omega : rfb ≤ m) _ _ _ _ _ hrfb, evalExpr_mono (by omega : rfL ≤ m) _ _ _ _ _ hrfL]⟩
      · injection hEval with hEq; subst hEq; exact ⟨rfc + 1, by simp [evalExpr, hrfc, hct]⟩
    · rename_i e1 e2; simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> cases hs2 : specShadow k orig.procs s e2 <;> simp [hs1, hs2] at hSpec
      subst hSpec; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
      cases he1 : evalExpr fuel orig.procs e1 s d <;> simp [he1] at hEval
      obtain ⟨rf1, hrf1⟩ := specShadow_eval_forward hProg fuel k s d _ e1 _ hs1 hClosed.1 he1
      obtain ⟨rf2, hrf2⟩ := specShadow_eval_forward hProg fuel k s _ v e2 _ hs2 hClosed.2 hEval
      exact ⟨max rf1 rf2 + 1, by simp [evalExpr, evalExpr_mono (by omega : rf1 ≤ max rf1 rf2) _ _ _ _ _ hrf1,
        evalExpr_mono (by omega : rf2 ≤ max rf1 rf2) _ _ _ _ _ hrf2]⟩
    · rename_i callee dArg; simp only [specShadow] at hSpec
      cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec; subst hSpec
      simp only [exprCallsClosed, Bool.and_eq_true, Option.isSome_iff_exists] at hClosed
      obtain ⟨⟨resBody, hLookRes⟩, hClosedArg⟩ := hClosed
      obtain ⟨origBody, hLookOrig, hSpecBody, hClosedBody⟩ := checkResProc_of_lookup hProg hLookRes
      cases hed : evalExpr fuel orig.procs dArg s d <;> simp [hed, hLookOrig] at hEval
      obtain ⟨rfd, hrfd⟩ := specShadow_eval_forward hProg fuel k s d _ dArg _ hsd hClosedArg hed
      obtain ⟨rfb, hrfb⟩ := specShadow_eval_forward hProg fuel kd .nil _ v origBody resBody hSpecBody hClosedBody hEval
      exact ⟨max rfd rfb + 1, by simp [evalExpr, evalExpr_mono (by omega : rfd ≤ max rfd rfb) _ _ _ _ _ hrfd, hLookRes,
        evalExpr_mono (by omega : rfb ≤ max rfd rfb) _ _ _ _ _ hrfb]⟩
    · rename_i c t f; simp only [specShadow] at hSpec
      by_cases hct : (evalSExpr c s).isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hSpec hEval
      · exact specShadow_eval_forward hProg fuel k s d v t eRes hSpec hClosed hEval
      · exact specShadow_eval_forward hProg fuel k s d v f eRes hSpec hClosed hEval
    · rename_i b body; simp only [specShadow] at hSpec
      exact specShadow_eval_forward hProg fuel k (.pair (evalSExpr b s) s) d v body eRes hSpec hClosed hEval
    · rename_i callee sArg dArg; simp only [specShadow] at hSpec
      cases hLook : lookupProc orig.procs callee <;> simp [hLook] at hSpec
      rename_i origBody
      cases hsb : specShadow k orig.procs (evalSExpr sArg s) origBody <;> simp [hsb] at hSpec
      rename_i rb
      by_cases hdEq : dArg = .dVar
      · subst hdEq
        simp only [↓reduceIte, Option.some.injEq] at hSpec; subst rb
        cases fuel with
        | zero => simp [evalExpr] at hEval
        | succ f2 =>
          have hdEv : evalExpr (f2 + 1) orig.procs .dVar s d = some d := rfl
          rw [hdEv, hLook] at hEval
          exact specShadow_eval_forward hProg (f2 + 1) k (evalSExpr sArg s) d v origBody eRes hsb hClosed hEval
      · simp only [hdEq, ↓reduceIte] at hSpec
        cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec; subst hSpec
        simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
        cases hed : evalExpr fuel orig.procs dArg s d <;> simp [hed, hLook] at hEval
        obtain ⟨rfd, hrfd⟩ := specShadow_eval_forward hProg fuel k s d _ dArg _ hsd hClosed.1 hed
        obtain ⟨rfb, hrfb⟩ := specShadow_eval_forward hProg fuel k (evalSExpr sArg s) _ v origBody rb hsb hClosed.2 hEval
        exact ⟨max rfd rfb + 1, by simp [evalExpr, evalExpr_mono (by omega : rfd ≤ max rfd rfb) _ _ _ _ _ hrfd,
          evalExpr_mono (by omega : rfb ≤ max rfd rfb) _ _ _ _ _ hrfb]⟩
    · rename_i callee sKey dArg; simp only [specShadow] at hSpec
      cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec; subst hSpec
      simp only [exprCallsClosed, Bool.and_eq_true, Option.isSome_iff_exists] at hClosed
      obtain ⟨⟨resBody, hLookRes⟩, hClosedArg⟩ := hClosed
      obtain ⟨origBody, hLookOrig, hSpecBody, hClosedBody⟩ := checkResProc_of_lookup hProg hLookRes
      cases hed : evalExpr fuel orig.procs dArg s d <;> simp [hed, hLookOrig] at hEval
      obtain ⟨rfd, hrfd⟩ := specShadow_eval_forward hProg fuel k s d _ dArg _ hsd hClosedArg hed
      obtain ⟨rfb, hrfb⟩ := specShadow_eval_forward hProg fuel kd (evalSExpr sKey s) _ v origBody resBody hSpecBody hClosedBody hEval
      exact ⟨max rfd rfb + 1, by simp [evalExpr, evalExpr_mono (by omega : rfd ≤ max rfd rfb) _ _ _ _ _ hrfd, hLookRes,
        evalExpr_mono (by omega : rfb ≤ max rfd rfb) _ _ _ _ _ hrfb]⟩
termination_by fuel k => (fuel, k)

private theorem specShadow_eval_backward
    {kd : Nat} {orig : MixProg} {s0 : MixVal} {res : MixProg}
    (hProg : checkSpecializesProg kd orig s0 res = true) :
    ∀ (resFuel k : Nat) (s d v : MixVal) (e eRes : MixExpr),
      specShadow k orig.procs s e = some eRes →
      exprCallsClosed res.procs eRes = true →
      evalExpr resFuel res.procs eRes .nil d = some v →
      ∃ fuel, evalExpr fuel orig.procs e s d = some v
  | _, 0, _, _, _, _, _, hSpec, _, _ => by simp [specShadow] at hSpec
  | resFuel, k + 1, s, d, v, e, eRes, hSpec, hClosed, hEval => by
    cases e with
    | sIf c t f =>
      simp only [specShadow] at hSpec
      by_cases hct : (evalSExpr c s).isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hSpec
      · obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg resFuel k s d v t eRes hSpec hClosed hEval
        exact ⟨f1 + 1, by simp [evalExpr, hct, hf1]⟩
      · obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg resFuel k s d v f eRes hSpec hClosed hEval
        exact ⟨f1 + 1, by simp [evalExpr, hct, hf1]⟩
    | sLet b body =>
      simp only [specShadow] at hSpec
      obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg resFuel k (.pair (evalSExpr b s) s) d v body eRes hSpec hClosed hEval
      exact ⟨f1 + 1, by simp [evalExpr, hf1]⟩
    | sCall callee sArg dArg =>
      simp only [specShadow] at hSpec
      cases hLook : lookupProc orig.procs callee <;> simp [hLook] at hSpec
      rename_i origBody
      cases hsb : specShadow k orig.procs (evalSExpr sArg s) origBody <;> simp [hsb] at hSpec
      rename_i rb
      by_cases hdEq : dArg = .dVar
      · subst hdEq
        simp only [↓reduceIte, Option.some.injEq] at hSpec; subst rb
        obtain ⟨fb, hfb⟩ := specShadow_eval_backward hProg resFuel k (evalSExpr sArg s) d v origBody eRes hsb hClosed hEval
        have md : evalExpr (max 1 fb) orig.procs .dVar s d = some d :=
          evalExpr_mono (by omega : 1 ≤ max 1 fb) orig.procs .dVar s d d rfl
        exact ⟨max 1 fb + 1, by simp [evalExpr, md, hLook, evalExpr_mono (by omega : fb ≤ max 1 fb) _ _ _ _ _ hfb]⟩
      · simp only [hdEq, ↓reduceIte] at hSpec
        cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec
        rename_i rd; subst hSpec
        cases resFuel with
        | zero => simp [evalExpr] at hEval
        | succ rf =>
          simp only [evalExpr] at hEval; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
          cases hed : evalExpr rf res.procs rd .nil d <;> simp [hed] at hEval
          obtain ⟨fd, hfd⟩ := specShadow_eval_backward hProg rf k s d _ dArg rd hsd hClosed.1 hed
          obtain ⟨fb, hfb⟩ := specShadow_eval_backward hProg rf k (evalSExpr sArg s) _ v origBody rb hsb hClosed.2 hEval
          exact ⟨max fd fb + 1, by simp [evalExpr, evalExpr_mono (by omega : fd ≤ max fd fb) _ _ _ _ _ hfd, hLook,
            evalExpr_mono (by omega : fb ≤ max fd fb) _ _ _ _ _ hfb]⟩
    | dVar | dLit _ | dLift _ =>
      simp only [specShadow, Option.some.injEq] at hSpec; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf => simp only [evalExpr, Option.some.injEq] at hEval; subst hEval; exact ⟨1, rfl⟩
    | dUnary op e1 =>
      simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> simp [hs1] at hSpec
      rename_i r1; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval
        cases he1 : evalExpr rf res.procs r1 .nil d <;> simp [he1] at hEval; subst hEval
        obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg rf k s d _ e1 r1 hs1 hClosed he1
        exact ⟨f1 + 1, by simp [evalExpr, hf1]⟩
    | dBin op e1 e2 =>
      simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> cases hs2 : specShadow k orig.procs s e2 <;> simp [hs1, hs2] at hSpec
      rename_i r1 r2; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
        cases he1 : evalExpr rf res.procs r1 .nil d <;> cases he2 : evalExpr rf res.procs r2 .nil d <;> simp [he1, he2] at hEval
        subst hEval
        obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg rf k s d _ e1 r1 hs1 hClosed.1 he1
        obtain ⟨f2, hf2⟩ := specShadow_eval_backward hProg rf k s d _ e2 r2 hs2 hClosed.2 he2
        exact ⟨max f1 f2 + 1, by simp [evalExpr, evalExpr_mono (by omega : f1 ≤ max f1 f2) _ _ _ _ _ hf1,
          evalExpr_mono (by omega : f2 ≤ max f1 f2) _ _ _ _ _ hf2]⟩
    | dIf c t f =>
      simp only [specShadow] at hSpec
      cases hsc : specShadow k orig.procs s c <;> cases hst : specShadow k orig.procs s t <;>
        cases hsf : specShadow k orig.procs s f <;> simp [hsc, hst, hsf] at hSpec
      rename_i rc rt rfE; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
        cases hec : evalExpr rf res.procs rc .nil d <;> simp [hec] at hEval
        rename_i vc
        obtain ⟨fc, hfc⟩ := specShadow_eval_backward hProg rf k s d vc c rc hsc hClosed.1.1 hec
        by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hEval
        · obtain ⟨ft, hft⟩ := specShadow_eval_backward hProg rf k s d v t rt hst hClosed.1.2 hEval
          exact ⟨max fc ft + 1, by simp [evalExpr, evalExpr_mono (by omega : fc ≤ max fc ft) _ _ _ _ _ hfc, hct,
            evalExpr_mono (by omega : ft ≤ max fc ft) _ _ _ _ _ hft]⟩
        · obtain ⟨ff, hff⟩ := specShadow_eval_backward hProg rf k s d v f rfE hsf hClosed.2 hEval
          exact ⟨max fc ff + 1, by simp [evalExpr, evalExpr_mono (by omega : fc ≤ max fc ff) _ _ _ _ _ hfc, hct,
            evalExpr_mono (by omega : ff ≤ max fc ff) _ _ _ _ _ hff]⟩
    | dWhile c body =>
      have hSpecOrig := hSpec; simp only [specShadow] at hSpec
      cases hsc : specShadow k orig.procs s c <;> cases hsb : specShadow k orig.procs s body <;> simp [hsc, hsb] at hSpec
      rename_i rc rb; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval; have hClosedOrig := hClosed
        simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
        cases hec : evalExpr rf res.procs rc .nil d <;> simp [hec] at hEval
        rename_i vc
        obtain ⟨fc, hfc⟩ := specShadow_eval_backward hProg rf k s d vc c rc hsc hClosed.1 hec
        by_cases hct : vc.isTrue <;> simp only [hct, ↓reduceIte, Bool.false_eq_true] at hEval
        · cases heb : evalExpr rf res.procs rb .nil d <;> simp [heb] at hEval
          rename_i d'
          obtain ⟨fb, hfb⟩ := specShadow_eval_backward hProg rf k s d d' body rb hsb hClosed.2 heb
          obtain ⟨fL, hfL⟩ := specShadow_eval_backward hProg rf (k + 1) s d' v (.dWhile c body) (.dWhile rc rb) hSpecOrig hClosedOrig hEval
          let m := max fc (max fb fL)
          exact ⟨m + 1, by simp [evalExpr, evalExpr_mono (by omega : fc ≤ m) _ _ _ _ _ hfc, hct,
            evalExpr_mono (by omega : fb ≤ m) _ _ _ _ _ hfb, evalExpr_mono (by omega : fL ≤ m) _ _ _ _ _ hfL]⟩
        · injection hEval with hEq; subst hEq; exact ⟨fc + 1, by simp [evalExpr, hfc, hct]⟩
    | dWithEnv e1 e2 =>
      simp only [specShadow] at hSpec
      cases hs1 : specShadow k orig.procs s e1 <;> cases hs2 : specShadow k orig.procs s e2 <;> simp [hs1, hs2] at hSpec
      rename_i r1 r2; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval; simp only [exprCallsClosed, Bool.and_eq_true] at hClosed
        cases he1 : evalExpr rf res.procs r1 .nil d <;> simp [he1] at hEval
        obtain ⟨f1, hf1⟩ := specShadow_eval_backward hProg rf k s d _ e1 r1 hs1 hClosed.1 he1
        obtain ⟨f2, hf2⟩ := specShadow_eval_backward hProg rf k s _ v e2 r2 hs2 hClosed.2 hEval
        exact ⟨max f1 f2 + 1, by simp [evalExpr, evalExpr_mono (by omega : f1 ≤ max f1 f2) _ _ _ _ _ hf1,
          evalExpr_mono (by omega : f2 ≤ max f1 f2) _ _ _ _ _ hf2]⟩
    | dCall callee dArg =>
      simp only [specShadow] at hSpec
      cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec
      rename_i rd; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval
        simp only [exprCallsClosed, Bool.and_eq_true, Option.isSome_iff_exists] at hClosed
        obtain ⟨⟨resBody, hLookRes⟩, hClosedArg⟩ := hClosed
        obtain ⟨origBody, hLookOrig, hSpecBody, hClosedBody⟩ := checkResProc_of_lookup hProg hLookRes
        cases hed : evalExpr rf res.procs rd .nil d <;> simp [hed, hLookRes] at hEval
        obtain ⟨fd, hfd⟩ := specShadow_eval_backward hProg rf k s d _ dArg rd hsd hClosedArg hed
        obtain ⟨fb, hfb⟩ := specShadow_eval_backward hProg rf kd .nil _ v origBody resBody hSpecBody hClosedBody hEval
        exact ⟨max fd fb + 1, by simp [evalExpr, evalExpr_mono (by omega : fd ≤ max fd fb) _ _ _ _ _ hfd, hLookOrig,
          evalExpr_mono (by omega : fb ≤ max fd fb) _ _ _ _ _ hfb]⟩
    | spCall callee sKey dArg =>
      simp only [specShadow] at hSpec
      cases hsd : specShadow k orig.procs s dArg <;> simp [hsd] at hSpec
      rename_i rd; subst hSpec
      cases resFuel with
      | zero => simp [evalExpr] at hEval
      | succ rf =>
        simp only [evalExpr] at hEval
        simp only [exprCallsClosed, Bool.and_eq_true, Option.isSome_iff_exists] at hClosed
        obtain ⟨⟨resBody, hLookRes⟩, hClosedArg⟩ := hClosed
        obtain ⟨origBody, hLookOrig, hSpecBody, hClosedBody⟩ := checkResProc_of_lookup hProg hLookRes
        cases hed : evalExpr rf res.procs rd .nil d <;> simp [hed, hLookRes] at hEval
        obtain ⟨fd, hfd⟩ := specShadow_eval_backward hProg rf k s d _ dArg rd hsd hClosedArg hed
        obtain ⟨fb, hfb⟩ := specShadow_eval_backward hProg rf kd (evalSExpr sKey s) _ v origBody resBody hSpecBody hClosedBody hEval
        exact ⟨max fd fb + 1, by simp [evalExpr, evalExpr_mono (by omega : fd ≤ max fd fb) _ _ _ _ _ hfd, hLookOrig,
          evalExpr_mono (by omega : fb ≤ max fd fb) _ _ _ _ _ hfb]⟩
termination_by resFuel k => (resFuel, k)

theorem checkSpecializesProg_sound
    {kd : Nat} {orig : MixProg} {s0 : MixVal} {res : MixProg}
    (hProg : checkSpecializesProg kd orig s0 res = true) :
    hasStaticConstruct res = false ∧
    (∀ (d v : MixVal),
      (∃ fuel, evalMix fuel orig s0 d = some v) ↔
      (∃ resFuel, evalMix resFuel res .nil d = some v)) := by
  have hCopy := hProg
  unfold checkSpecializesProg at hCopy
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true] at hCopy
  have hResEntry : res.entry = .sym .entry := hCopy.1.1.1
  have hStrip : hasStaticConstruct res = false := hCopy.1.1.2
  cases hOrigLook : lookupProc orig.procs orig.entry <;>
    cases hResLook : lookupProc res.procs (.sym .entry) <;>
    simp [hOrigLook, hResLook] at hCopy
  rename_i origEntry resEntry
  have hPrEntry := hCopy.2 _ (lookupProc_mem_of_some hResLook)
  unfold checkResProc at hPrEntry; simp only [Bool.and_eq_true] at hPrEntry
  refine ⟨hStrip, fun d v => ⟨?_, ?_⟩⟩
  · rintro ⟨fuel, hEval⟩
    unfold evalMix at hEval; rw [hOrigLook] at hEval
    obtain ⟨rf, hrf⟩ := specShadow_eval_forward hProg fuel kd s0 d v origEntry resEntry hCopy.1.2 hPrEntry.1.2 hEval
    exact ⟨rf, by simp [evalMix, hResEntry, hResLook, hrf]⟩
  · rintro ⟨resFuel, hEval⟩
    unfold evalMix at hEval; rw [hResEntry, hResLook] at hEval
    obtain ⟨f, hf⟩ := specShadow_eval_backward hProg resFuel kd s0 d v origEntry resEntry hCopy.1.2 hPrEntry.1.2 hEval
    exact ⟨f, by simp [evalMix, hOrigLook, hf]⟩

theorem checkSpecializesProg_inhabited :
    ∃ p : MixProg, checkSpecializesProg 4 p .nil p = true :=
  ⟨{ entry := .sym .entry, procs := [{ name := .sym .entry, body := .dVar }] }, by decide⟩

end Obend.Leaf.SelfApplicableMix
end
