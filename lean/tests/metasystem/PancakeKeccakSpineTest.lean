import Obend.Lower.Pancake.PancakeKeccak
import Obend.Lower.Pancake.EmitPnk
import Obend.Lower.Pancake.LcnfFun
import Obend.Digest.Cshake256.Spec
import Obend.Lower.Pancake.WordBuffer
import Obend.Tactic.Tooth

open Obend.Lower.Pancake Obend.Digest
namespace PancakeSpineTest

/-- Reference the two FIPS parameter tables independently of the shared permutation spec. -/
private theorem rho_one (w : Word) :
    w.rotateLeft (Cshake256.rotationOffset 1 0) = w.rotateLeft 1 := by rfl

private theorem iota_first (w : Word) :
    (w ^^^ Cshake256.roundConstants.head!) = w ^^^ 1 := by rfl

#tooth rho_one by mutation Cshake256.rotationOffsets :=
  #[0, 2, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

#tooth iota_first by mutation Cshake256.roundConstants :=
  [0, 0x8082, 0x800000000000808a, 0x8000000080008000, 0x808b, 0x80000001,
   0x8000000080008081, 0x8000000000008009, 0x8a, 0x88, 0x80008009, 0x8000000a,
   0x8000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
   0x8000000000008002, 0x8000000000000080, 0x800a, 0x800000008000000a,
   0x8000000080008081, 0x8000000000008080, 0x80000001, 0x8000000080008008]

#tooth Keccak.pancakeKeccakF1600_correct by mutation Keccak.kernel :=
  ⟨"keccakF1600", [("base", .One)], .ret (.const 0), true⟩

#tooth Keccak.kernel_text_grammar by mutation emitPnkFun := fun _ => some "return"
#tooth emitWordExpr_grammar by mutation emitWordExpr := fun _ _ => none
#tooth WordBuffer.eval_lower by mutation WordBuffer.Expr.lower := fun _ _ => .const 0
#tooth WordBuffer.lowerStage_correct by mutation WordBuffer.lowerStage := fun _ _ => .skip
#tooth lowerLcnfFun_correct by mutation lowerLcnfFun := fun name _ _ =>
  some (⟨name, [], .ret (.const 0), false⟩, 0)
#tooth lowerAndEmitLcnfFun_sound by mutation lowerAndEmitLcnfFun := fun name _ _ =>
  some (⟨name, [], .ret (.const 0), false⟩, "{)", 0)
#tooth emitPnkProg_balanced by mutation emitPnkProg := fun _ => some "{)"

private def inputState (words : Array Word) (clk count : Nat) : PanState Unit :=
  { emptyPanState () clk with
    locals := FUPDATE FEMPTY ("base", .word 256)
    memory := fun a => words.getD ((a.toNat - 256)/8) 0
    memaddrs := fun a => decide (256 ≤ a.toNat ∧ a.toNat < 256+8*count ∧ a.toNat%8 = 0) }

example (words : Array Word) : WordBuffer.Mapped (inputState words 0 25) 256 := by
  intro i
  have h : ∀ j : Fin 25, (inputState #[] 0 25).memaddrs (WordBuffer.address 256 j) = true := by decide
  exact h i

example : ((lowerLcnfFun "second" [4, 9] (.return (.bvar 1))).map Prod.snd) = some 9 := by decide
example : (lowerLcnfFun "missing" [4] (.return (.bvar 1))).isNone := by decide
#guard (lowerAndEmitLcnfFun "second" [4, 9] (.return (.bvar 1))).isSome
#guard (lowerAndEmitLcnfFun "return" [4] (.return (.bvar 0))).isNone

#guard (emitPnkFun ⟨"return", [], .skip, false⟩).isNone
#guard (emitPnkFun ⟨"bad", [("x", .One), ("x", .One)], .skip, false⟩).isNone
#guard (emitPnkFun ⟨"bad", [], .ret .topAddr, false⟩).isNone
#guard !pnkBalanced "({)}"
#guard (do
  let (f, _) ← lowerLcnfFun "second" [4,9] (.return (.bvar 1))
  let s := {emptyPanState () 0 with locals := mkCalleeLocals f.params [.word 3, .word 8]}
  return (evaluate f.body s).1 == .ret (.word 8)) == some true

private def binary (op : Binop) (a b : PExp) := PExp.binop op [a,b]
private def base := PExp.lvar "base"
private def testFun (name : String) (p : PStmt) : PFun := ⟨name, [("base", .One)], p, false⟩
private def probe : PFun := testFun "probe" <|
  .dec "n" .One (.const 3) <| .seq
    (.while_ (.lvar "n") (.seq
      (.store base (binary .Xor (.shift .Ror (.load .One base) 7) (.lvar "n")))
      (.lassign "n" (binary .Sub (.lvar "n") (.const 1)))))
    (.ret (binary .Or (.shift .Lsr (.load .One base) 63)
      (binary .And (.shift .Asr (.const 0x8000000000000000) 63) (.const 0xff00))))

private def observe (f : PFun) (words : Array Word) (clock count : Nat) :=
  let (r,t) := evaluate f.body (inputState words clock count)
  (r, t.clock, Array.ofFn fun i : Fin 25 => t.memory (WordBuffer.address 256 i))

private def padded (w : Word) : Array Word :=
  ((Array.replicate 25 (0 : Word)).set! 0 w).set! 16 0x8000000000000000

private def zero := Array.replicate 25 (0 : Word)
private def empty := padded 6
private def abc := padded 0x06636261

-- XKCP KeccakF-1600-IntermediateValues, all 1600 bits of the zero-state permutation.
private def zeroOutput : Array Word := #[
  0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee, 0xbd1547306f80494d,
  0x8b284e056253d057, 0xff97a42d7f8e6fd4, 0x90fee5a0a44647c4, 0x8c5bda0cd6192e76,
  0xad30a6f71b19059c, 0x30935ab7d08ffc64, 0xeb5aa93f2317d635, 0xa9a6e6260d712103,
  0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x01f22f1a11a5569f, 0x05e5635a21d9ae61,
  0x64befef28cc970f2, 0x613670957bc46611, 0xb87c5a554fd00ecb, 0x8c3ee88a1ccf32c8,
  0x940c7922ae3a2614, 0x1841f924a2c509e4, 0x16f53526e70465c2, 0x75f644e97f30a13b,
  0xeaf1ff7b5ceca249]

private def vectorOK (input expected : Array Word) : Bool :=
  let (r,clk,out) := observe Keccak.kernel input 0 25
  r == .ret (.word 0) && clk == 0 && out == Keccak.keccakF1600Words input &&
    out.extract 0 expected.size == expected

#guard vectorOK zero zeroOutput
#guard vectorOK empty #[0x66d71ebff8c6ffa7, 0x62d661a05647c151, 0xfa493be44dff80f5, 0x4a43f8804b0ad882]
#guard vectorOK abc #[0xb225e24fa75d983a, 0xbd90d36b2d175c04, 0x5b529d3e6e085f85, 0x3215431145e2bf46]

/- Serialize the exact expression trees for kernel-side HOL evaluation of the large kernel. -/
mutual
private def holExp : PExp → Option String
  | .const w => some s!"(Const {w.toNat}w)"
  | .var .Local "base" => some "(Var Local «base»)"
  | .load .One a => do return "(Load One " ++ (← holExp a) ++ ")"
  | .shift .Ror a n => do return "(Shift Ror " ++ (← holExp a) ++ s!" {n})"
  | .binop op es => do
    let sym := match op with
      | .Add => "Add" | .Sub => "Sub" | .And => "And" | .Xor => "Xor" | .Or => "Or"
    return "(Op " ++ sym ++ " [" ++ String.intercalate ";" (← holList es) ++ "])"
  | .rstruct es => do return "(SpineTuple [" ++ String.intercalate ";" (← holList es) ++ "])"
  | _ => none
termination_by structural e => e
private def holList : List PExp → Option (List String)
  | [] => some []
  | e::es => do return (← holExp e) :: (← holList es)
termination_by structural es => es
end

private def holSteps : PStmt → Option (List String)
  | .seq p q => do return (← holSteps p) ++ (← holSteps q)
  | .store a v => do return ["Store " ++ (← holExp a) ++ " " ++ (← holExp v)]
  | .ret e => do return ["panLang$Return " ++ (← holExp e)]
  | _ => none

private def csv (ws : Array Word) := String.intercalate "," (ws.toList.map (toString ·.toNat))

def exportCorpus (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let cases := [("zero", Keccak.kernel, zero, 0, 25), ("empty", Keccak.kernel, empty, 0, 25),
    ("abc", Keccak.kernel, abc, 0, 25), ("loop", probe, abc, 3, 25), ("timeout", probe, abc, 2, 25),
    ("unmapped", probe, abc, 3, 0),
    ("badshift", testFun "badshift" (.ret (.shift .Lsl (.const 1) 64)), zero, 0, 25)]
  let mut rows := #[]
  for (id, f, input, clk, count) in cases do
    let some src := emitPnkFun f | throw (IO.userError s!"cannot print {f.name}")
    IO.FS.writeFile (dir / (f.name ++ ".pnk")) src
    let (r,t,out) := observe f input clk count
    let result ← match r with
      | .ret (.word w) => pure (toString w.toNat)
      | .TimeOut => pure "timeout"
      | .Error => pure "error"
      | _ => throw (IO.userError "unexpected outcome")
    rows := rows.push (String.intercalate "\t" [id, f.name, toString clk, toString count,
      csv input, result, toString t, csv out])
  let some steps := holSteps Keccak.kernel.body | throw (IO.userError "unsupported AST in HOL export")
  IO.FS.writeFile (dir / "keccakF1600.hol") (String.intercalate "\n" steps ++ "\n")
  IO.FS.writeFile (dir / "cases.tsv") (String.intercalate "\n" rows.toList ++ "\n")

#print axioms Keccak.pancakeKeccakF1600_correct
#print axioms Keccak.kernel_text_grammar
#assert_axioms_tree
end PancakeSpineTest

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "expected an output directory")
  PancakeSpineTest.exportCorpus dir
