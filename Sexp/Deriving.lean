import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Sexp.Codec

namespace Sexp.Deriving

open Lean Elab Command Term Meta
open Lean.Parser.Term

private def mkInstance (declName : Name) : TermElabM Command := do
  let env ← getEnv
  unless isStructure env declName do
    throwError "SExprCodec deriving currently supports structures only"
  let info ← getConstInfoInduct declName
  unless info.numParams = 0 do
    throwError "SExprCodec deriving currently supports non-parameterized structures only"
  let fields := getStructureFieldsFlattened env declName (includeSubobjectFields := false)
  let locals := fields.map fun field => mkIdent ((`v).appendAfter field.getString!)
  let input := mkIdent `input
  let value := mkIdent `value
  let decoders ← locals.mapM fun localId =>
    `(doElem| let ($localId:ident, $input:ident) ← (Sexp.codec (α := _)).decode $input:ident)
  let encoders ← fields.mapM fun field =>
    let fieldId := mkIdent field
    `((Sexp.codec (α := _)).encode $value:ident.$fieldId:ident)
  let assignments ← fields.zip locals |>.mapM fun (field, localId) =>
    `(structInstField| $(mkIdent field):ident := $localId:ident)
  let tag := Syntax.mkStrLit declName.eraseMacroScopes.getString!
  let encoded ← match encoders.toList with
    | [] => `([])
    | first :: rest => rest.foldlM (fun acc next => `($acc ++ $next)) first
  let typeId := mkIdent declName
  `(instance : Sexp.SExprCodec $typeId:ident where
      codec := Sexp.Codec.tagged $tag {
        decode := fun $input:ident => do
          $[$decoders:doElem]*
          return ({ $assignments:structInstField,* }, $input:ident)
        encode := fun $value:ident => $encoded
      })

private def deriveSExprCodec (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then return false
  for declName in declNames do
    let command ← liftTermElabM <| mkInstance declName
    elabCommand command
  return true

initialize
  registerDerivingHandler ``Sexp.SExprCodec deriveSExprCodec

end Sexp.Deriving
