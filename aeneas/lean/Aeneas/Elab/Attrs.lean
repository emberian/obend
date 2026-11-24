module

public import Lean
public import Aeneas.Std.Types

open Lean Elab Command Term Meta

private meta def generateDiscriminantInst (declName : Name) (tyIdent : Ident) : CommandElabM Unit := do
  let indVal ← liftCoreM (getConstInfoInduct declName)
  if indVal.numParams > 0 || indVal.numIndices > 0 then
    throwError "discriminant: indexed/parametric inductives not needed for {declName}"
  let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  for idx in [:indVal.ctors.length] do
    let ctorName := indVal.ctors[idx]!
    let ctorInfo ← liftCoreM (getConstInfoCtor ctorName)
    let mut holes : Array Term := #[]
    for _ in [:ctorInfo.numFields] do
      holes := holes.push (← `(_))
    let pat ← `($(mkCIdent ctorName):ident $holes:term*)
    let lit := Syntax.mkNumLit (toString idx)
    let rhs : Term ← match tyIdent.getId with
      | `isize => `(Aeneas.Std.IScalar.ofInt .Isize (Int.ofNat $lit))
      | `usize => `(Aeneas.Std.UScalar.ofNat .Usize $lit)
      | `u8    => `(Aeneas.Std.UScalar.ofNat .U8 $lit)
      | `u32   => `(Aeneas.Std.UScalar.ofNat .U32 $lit)
      | other  => throwError "discriminant: unsupported scalar kind {other}"
    let alt ← `(Parser.Term.matchAltExpr| | $pat => $rhs)
    alts := alts.push alt
  let discrTy : Term ← match tyIdent.getId with
    | `isize => `(Aeneas.Std.Isize)
    | `usize => `(Aeneas.Std.Usize)
    | `u8    => `(Aeneas.Std.U8)
    | `u32   => `(Aeneas.Std.U32)
    | other  => throwError "discriminant: unsupported scalar kind {other}"
  let cmd ← `(
    @[reducible]
    public instance : Aeneas.Std.Discriminant $(mkCIdent declName) $discrTy where
      read_discriminant x := match x with $alts:matchAlt*
  )
  elabCommand cmd

public section

meta section

register_option linter.dupNamespace : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.whitespace : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.setOption : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.longLine : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.internalConstructors : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

end

syntax (name := aeneasGlobalSimps) "global_simps" : attr
syntax (name := aeneasRustLoopBody) "rust_loop_body" : attr
syntax (name := aeneasRustLoop) "rust_loop" : attr
syntax (name := aeneasDiscriminant) "discriminant " ident : attr

meta initialize
  registerBuiltinAttribute {
    name := `aeneasGlobalSimps
    descr := "Marker attribute emitted by Aeneas on global constants"
    add := fun _ _ _ => pure ()
  }
  registerBuiltinAttribute {
    name := `aeneasRustLoopBody
    descr := "Marker attribute emitted by Aeneas on extracted MIR loop bodies"
    add := fun _ _ _ => pure ()
  }
  registerBuiltinAttribute {
    name := `aeneasRustLoop
    descr := "Marker attribute emitted by Aeneas on extracted MIR loops"
    add := fun _ _ _ => pure ()
  }
  registerBuiltinAttribute {
    name := `aeneasDiscriminant
    descr := "Generates a faithful `Aeneas.Std.Discriminant` instance for a Rust enum"
    add := fun declName stx _ => do
      match stx with
      | `(attr| discriminant $ty:ident) =>
        liftCommandElabM (generateDiscriminantInst declName ty)
      | _ => throwUnsupportedSyntax
  }
