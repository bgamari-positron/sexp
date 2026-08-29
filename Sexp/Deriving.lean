import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Sexp.Codec

namespace Sexp.Deriving

open Lean Elab Command Term Meta
open Lean.Parser.Term
open Lean.Elab.Deriving

private def mkCodecBody (indVal : InductiveVal) : TermElabM Term := do
  let env ← getEnv
  unless isStructure env indVal.name do
    throwError "SExprCodec deriving currently supports structures only"
  let fields := getStructureFieldsFlattened env indVal.name (includeSubobjectFields := false)
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
  let tag := Syntax.mkStrLit indVal.name.eraseMacroScopes.getString!
  let encoded ← match encoders.toList with
    | [] => `([])
    | first :: rest => rest.foldlM (fun acc next => `($acc ++ $next)) first
  `(Sexp.Codec.tagged $tag {
      decode := fun $input:ident => do
        $[$decoders:doElem]*
        return ({ $assignments:structInstField,* }, $input:ident)
      encode := fun $value:ident => $encoded
    })

private def mkAuxFunction (ctx : Lean.Elab.Deriving.Context) : TermElabM Command := do
  let indVal := ctx.typeInfos[0]!
  let auxName := ctx.auxFunNames[0]!
  let header ← mkHeader ``Sexp.SExprCodec 0 indVal
  let binders := header.binders
  let body ← mkCodecBody indVal
  `(def $(mkIdent auxName):ident $binders:bracketedBinder* : Sexp.Codec $(header.targetType) :=
      $body:term)

private def mkCommands (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``Sexp.SExprCodec "codec" declName
  if ctx.typeInfos.size != 1 then
    throwError "SExprCodec deriving does not yet support mutually recursive structures"
  if ctx.typeInfos[0]!.isRec then
    throwError "SExprCodec deriving does not yet support recursive structures"
  let aux ← mkAuxFunction ctx
  let instances ← mkInstanceCmds ctx ``Sexp.SExprCodec #[declName]
  pure (#[aux] ++ instances)

private def deriveSExprCodec (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then return false
  for declName in declNames do
    let commands ← liftTermElabM <| mkCommands declName
    commands.forM elabCommand
  return true

initialize
  registerDerivingHandler ``Sexp.SExprCodec deriveSExprCodec

end Sexp.Deriving
