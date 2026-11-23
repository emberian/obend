module
public import Obend.Lower.Pancake.WordBuffer
import all Obend.Lower.Pancake.WordBuffer

public section
namespace Obend.Lower.Pancake
set_option autoImplicit false

def pnkIdentifier (s : String) : Option String := do
  let c :: cs := s.toList | none
  guard (c.isAlpha && cs.all (fun x => x.isAlphanum || x == '_'))
  let reserved := ["skip", "st", "stw", "st8", "st16", "st32", "if", "else", "while", "break", "continue", "raise", "return", "tick",
    "var", "in", "with", "handle", "lds", "ldw", "ld8", "ld16", "ld32", "true", "false", "fun", "export", "inline",
    "struct"]
  guard (!reserved.contains s)
  return s

private def scopedVar (scope : List String) (kind : VarKind) (name : String) := do
  guard (scope.contains name == (kind == VarKind.Local))
  pnkIdentifier name

mutual
private def shapeText : Shape → Option String
  | .One => some "1"
  | .Comb [] => none
  | .Comb ss => do return "{" ++ String.intercalate "," (← shapesText ss) ++ "}"
termination_by structural sh => sh
private def shapesText : List Shape → Option (List String)
  | [] => some []
  | s :: ss => do return (← shapeText s) :: (← shapesText ss)
termination_by structural ss => ss
end

private def binary (a op b : String) := "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")"

mutual
private def exprText (scope : List String) : PExp → Option String
  | .const w => some (toString w.toNat)
  | .var k n => scopedVar scope k n
  | .load sh a => do return "(lds " ++ (← shapeText sh) ++ " " ++ (← exprText scope a) ++ ")"
  | .loadByte a => do return "(ld8 " ++ (← exprText scope a) ++ ")"
  | .rstruct [] => none
  | .rstruct es => do return "< " ++ String.intercalate ", " (← exprsText scope es) ++ " >"
  | .rfield n a => do return "(" ++ (← exprText scope a) ++ ")." ++ toString n
  | .binop op es => do
    let args ← exprsText scope es
    let sym := match op with
      | .Add => "+" | .Sub => "-" | .Xor => "^" | .And => "&" | .Or => "|"
    if op == .Sub then guard (args.length == 2)
    match args with
    | [] => return if op == .And then "18446744073709551615" else "0"
    | [a] => return binary a sym (if op == .And then "18446744073709551615" else "0")
    | a :: b :: rest => return binary a sym (rest.foldl (fun acc x => binary acc sym x) b)
  | .panop .Mul [a,b] => do return binary (← exprText scope a) "*" (← exprText scope b)
  | .panop _ _ => none
  | .cmp c a b => do
    let l ← exprText scope a
    let r ← exprText scope b
    return match c with
    | .Equal => binary l "==" r | .NotEqual => binary l "!=" r
    | .Lower => binary l "<+" r | .NotLower => binary l ">=+" r
    | .Less => binary l "<" r | .NotLess => binary l ">=" r
    | .Test => binary (binary l "&" r) "==" "0"
    | .NotTest => binary (binary l "&" r) "!=" "0"
  | .shift sh e n => do
    let op := match sh with
      | .Lsl => "<<" | .Lsr => ">>>" | .Asr => ">>" | .Ror => "#>>"
    return binary (← exprText scope e) op (toString n)
  | .baseAddr => some "@base"
  | .bytesInWord => some "@biw"
  | .topAddr => none  -- ed31510b's lexer maps @top to BaseK.
termination_by structural e => e
private def exprsText (scope : List String) : List PExp → Option (List String)
  | [] => some []
  | e :: es => do return (← exprText scope e) :: (← exprsText scope es)
termination_by structural es => es
end

/-- Concrete productions for the word expressions in buffer kernels. The base parameter
    is supplied by the enclosing function. Literals and immediate shifts are decimal. -/
inductive WordText (p : String) : String → Prop where
  | literal (w : Word) : WordText p (toString w.toNat)
  | base : WordText p p
  | load {a} : WordText p a → WordText p ("(lds 1 " ++ a ++ ")")
  | add {a b} : WordText p a → WordText p b → WordText p ("(" ++ a ++ " " ++ "+" ++ " " ++ b ++ ")")
  | xor {a b} : WordText p a → WordText p b → WordText p ("(" ++ a ++ " " ++ "^" ++ " " ++ b ++ ")")
  | and {a b} : WordText p a → WordText p b → WordText p ("(" ++ a ++ " " ++ "&" ++ " " ++ b ++ ")")
  | rotate {a} (n : Fin 64) : WordText p a → WordText p ("(" ++ a ++ " " ++ "#>>" ++ " " ++ (toString n.val) ++ ")")

def emitWordExpr (p : String) (e : WordBuffer.Expr) := exprText [p] (e.lower p)

/-- Every bounded word expression prints, with a derivation in the concrete grammar. -/
theorem emitWordExpr_grammar (e : WordBuffer.Expr) (p : String)
    (name : pnkIdentifier p = some p) : ∃ src, emitWordExpr p e = some src ∧ WordText p src := by
  unfold emitWordExpr
  induction e with
  | lane i =>
    let w := BitVec.ofNat 64 (8*i.val)
    refine ⟨_, ?_, WordText.load (WordText.add .base (.literal w))⟩
    simp [WordBuffer.Expr.lower, exprText, exprsText, shapeText, scopedVar, name, w, guard, binary]
  | lit w => exact ⟨_, rfl, .literal w⟩
  | xor a b ia ib =>
    obtain ⟨x,hx,gx⟩ := ia
    obtain ⟨y,hy,gy⟩ := ib
    exact ⟨_, by simp [WordBuffer.Expr.lower, exprText, exprsText, hx, hy, binary], .xor gx gy⟩
  | and a b ia ib =>
    obtain ⟨x,hx,gx⟩ := ia
    obtain ⟨y,hy,gy⟩ := ib
    exact ⟨_, by simp [WordBuffer.Expr.lower, exprText, exprsText, hx, hy, binary], .and gx gy⟩
  | rot a n ih =>
    obtain ⟨x,hx,gx⟩ := ih
    by_cases h : n.val = 0
    · exact ⟨_, by simpa [WordBuffer.Expr.lower, h] using hx, gx⟩
    · refine ⟨_, ?_, WordText.rotate ⟨64-n.val, by omega⟩ gx⟩
      simp [WordBuffer.Expr.lower, h, exprText, hx, binary]

private def block (s : String) := "{\n" ++ s ++ "}"

/-- Declarations are explicitly scoped, including in the left arm of a sequence. -/
private def stmtText (scope : List String) : PStmt → Option String
  | .skip => some "skip;\n"
  | .ret e => do return "return " ++ (← exprText scope e) ++ ";\n"
  | .dec v sh e k => do return block ("var " ++ (← shapeText sh) ++ " " ++ (← pnkIdentifier v) ++
      " = " ++ (← exprText scope e) ++ ";\n" ++ (← stmtText (v::scope) k)) ++ ";\n"
  | .assign vk v e => do return (← scopedVar scope vk v) ++ " = " ++ (← exprText scope e) ++ ";\n"
  | .store a e => do return "st " ++ (← exprText scope a) ++ ", " ++ (← exprText scope e) ++ ";\n"
  | .storeByte a e => do return "st8 " ++ (← exprText scope a) ++ ", " ++ (← exprText scope e) ++ ";\n"
  | .seq a b => do return (← stmtText scope a) ++ (← stmtText scope b)
  | .ite e a b => do return "if " ++ (← exprText scope e) ++ " " ++ block (← stmtText scope a) ++
      " else " ++ block (← stmtText scope b) ++ "\n"
  | .while_ e a => do return "while " ++ (← exprText scope e) ++ " " ++ block (← stmtText scope a) ++ "\n"
  | .break_ => some "break;\n"
  | .continue_ => some "continue;\n"
  | .tick => some "tick;\n"
  | .annot .. => some "skip;\n"
  | .call dst fn args => do
    let head ← match dst with
      | none => pure "return "
      | some (vk, v) => do return (← scopedVar scope vk v) ++ " = "
    return head ++ (← pnkIdentifier fn) ++ "(" ++ String.intercalate ", " (← exprsText scope args) ++ ");\n"
  | .decCall v sh fn args k => do return block ("var " ++ (← shapeText sh) ++ " " ++
      (← pnkIdentifier v) ++ " = " ++ (← pnkIdentifier fn) ++ "(" ++ String.intercalate ", " (← exprsText scope args) ++
      ");\n" ++ (← stmtText (v::scope) k)) ++ ";\n"
  | .extCall fn a b c d => do
    let foreign ← pnkIdentifier fn
    guard (!(["base", "top", "biw"] : List String).contains foreign)
    let args ← exprsText scope [a,b,c,d]
    return "@" ++ foreign ++ "(" ++ String.intercalate ", " args ++ ");\n"

/-- Check nesting of concrete block and parenthesis delimiters in rendered source. -/
def pnkBalanced (s : String) : Bool := go [] s.toList where
  go : List Char → List Char → Bool
    | stack, [] => stack.isEmpty
    | stack, '(' :: cs => go (')' :: stack) cs
    | stack, '{' :: cs => go ('}' :: stack) cs
    | stack, c :: cs =>
      if c == ')' || c == '}' then
        match stack with
        | d :: ds => c == d && go ds cs
        | [] => false
      else go stack cs

private def funText (f : PFun) : Option String := do
  let params ← f.params.mapM fun (n, sh) => do return (← shapeText sh) ++ " " ++ (← pnkIdentifier n)
  let names := f.params.map Prod.fst
  guard names.Nodup
  return (if f.exported then "export " else "") ++ "fun " ++ (← pnkIdentifier f.name) ++
    "(" ++ String.intercalate ", " params ++ ") " ++ block (← stmtText names f.body) ++ "\n"

/-- Produce source for the printable fragment. Fail explicitly on unrepresentable ASTs. -/
def emitPnkProg (fs : List PFun) : Option String := do
  guard (!(fs.isEmpty) && decide (fs.map PFun.name).Nodup)
  let src := String.intercalate "\n" (← fs.mapM funText)
  if pnkBalanced src then some src else none

def emitPnkFun (f : PFun) : Option String := emitPnkProg [f]

theorem emitPnkProg_balanced (fs : List PFun) (s : String) (h : emitPnkProg fs = some s) :
    pnkBalanced s = true := by
  unfold emitPnkProg at h
  simp only [bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  obtain ⟨hb, rfl⟩ := h
  exact hb

end Obend.Lower.Pancake
