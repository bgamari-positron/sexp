import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Sexp.Codec

namespace Sexp.Deriving

open Lean Elab Command Term Meta
open Lean.Parser.Term
open Lean.Elab.Deriving

private def mkCodecBody (indVal : InductiveVal) (argNames : Array Name) : TermElabM Term := do
  let env ← getEnv
  unless isStructure env indVal.name do
    throwError "SExprCodec deriving currently supports structures only"
  let fields := getStructureFieldsFlattened env indVal.name (includeSubobjectFields := false)
  let locals := fields.map fun field => mkIdent ((`v).appendAfter field.getString!)
  let input := mkIdent `input
  let value := mkIdent `value
  let proofTypes ← forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let mut lctx ← getLCtx
    for param in params, name in argNames do
      lctx := lctx.setUserName param.fvarId! name
    withLCtx lctx (← getLocalInstances) do
      let target := mkAppN (mkConst indVal.name (indVal.levelParams.map Level.param)) params
      withLocalDeclD `self target fun self => do
        let projections ← fields.mapM (fun field => liftMetaM <| mkProjection self field)
        let rec collect (i : Nat) (values : Array Expr) : TermElabM (Array (Option Term)) := do
          if i < fields.size then
            let type ← inferType projections[i]!
            let type := type.replace fun e =>
              (projections.zip values).findSome? fun (projection, value) =>
                if e == projection then some value else none
            let proofType ← if ← isProp type then
                pure (some (← PrettyPrinter.delab type))
              else pure none
            withLocalDeclD locals[i]!.getId type fun value => do
              return #[proofType] ++ (← collect (i + 1) (values.push value))
          else
            return #[]
        collect 0 #[]
  let assignments ← fields.zip locals |>.mapM fun (field, localId) =>
    `(structInstField| $(mkIdent field):ident := $localId:ident)
  let mut decoder ← `(pure ({ $assignments:structInstField,* }, $input:ident))
  let mut encoders := #[]
  for i in (List.range fields.size).reverse do
    let field := fields[i]!
    let localId := locals[i]!
    if let some proposition := proofTypes[i]! then
      let message := Syntax.mkStrLit s!"proof field {field} failed"
      decoder ← `(if $localId:ident : $proposition then $decoder
        else throw { message := $message })
    else
      decoder ← `(do
        let ($localId:ident, $input:ident) ← (Sexp.codec (α := _)).decode $input:ident
        return ← $decoder)
      let fieldId := mkIdent field
      encoders := #[← `((Sexp.codec (α := _)).encode $value:ident.$fieldId:ident)] ++ encoders
  let tag := Syntax.mkStrLit indVal.name.eraseMacroScopes.getString!
  let encoded ← match encoders.toList with
    | [] => `([])
    | first :: rest => rest.foldlM (fun acc next => `($acc ++ $next)) first
  `(Sexp.Codec.tagged $tag {
      decode := fun $input:ident => $decoder
      encode := fun $value:ident => $encoded
    })

private partial def paramTypeSyntax (xs : Array Expr) (argNames : Array Name)
    (type : Expr) : TermElabM Term := do
  match type with
  | .fvar id =>
      for h : i in *...xs.size do
        if xs[i] == .fvar id then return mkIdent argNames[i]!
      throwError "SExprCodec deriving encountered an unknown parameter in an instance type"
  | .const name _ =>
      `(@$(mkCIdent name))
  | .app fn arg =>
      `($(← paramTypeSyntax xs argNames fn) $(← paramTypeSyntax xs argNames arg))
  | .mdata _ type =>
      paramTypeSyntax xs argNames type
  | type =>
      throwError "SExprCodec deriving does not support structure instance parameter type {type}"

private def fieldsHaveCodecs (indVal : InductiveVal) (params : Array Expr) : TermElabM Bool := do
  let ctor ← getConstInfoCtor indVal.ctors[0]!
  let type ← liftMetaM <| instantiateForall ctor.type params
  try
    forallBoundedTelescope type ctor.numFields fun fields _ => do
      for field in fields do
        let fieldType ← inferType field
        unless ← isProp fieldType do
          let _ ← liftMetaM <| synthInstance (← mkAppM ``Sexp.SExprCodec #[fieldType])
    pure true
  catch _ =>
    pure false

/-- Preserve instance parameters from the structure and add only non-duplicate
codec parameters accepted by `SExprCodec`. -/
private def mkCodecHeader (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let targetType ← mkInductiveApp indVal argNames
  let binders ← forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut binders : Array Syntax := #[]
    let mut instanceTypes : Array Expr := #[]
    for h : i in *...xs.size do
      let localDecl ← xs[i].fvarId!.getDecl
      let argName := argNames[i]!
      if localDecl.binderInfo.isInstImplicit then
        let type ← paramTypeSyntax xs argNames localDecl.type
        binders := binders.push (← `(instBinderF| [$(mkIdent argName) : $type])).raw
        instanceTypes := instanceTypes.push localDecl.type
      else
        binders := binders.push (← `(implicitBinderF| {$(mkIdent argName)})).raw
    unless ← fieldsHaveCodecs indVal xs do
      for h : i in *...xs.size do
        try
          let type ← mkAppM ``Sexp.SExprCodec #[xs[i]]
          if (← isTypeCorrect type) && !(← instanceTypes.anyM fun instanceType => liftMetaM <| isDefEqGuarded type instanceType) then
            binders := binders.push (← `(instBinderF| [Sexp.SExprCodec $(mkIdent argNames[i]!) ])).raw
        catch _ => pure ()
    pure (binders.map fun binder => ⟨binder⟩)
  pure { binders, argNames, targetNames := #[], targetType }

private def mkAuxFunction (ctx : Lean.Elab.Deriving.Context) : TermElabM Command := do
  let indVal := ctx.typeInfos[0]!
  let auxName := ctx.auxFunNames[0]!
  let header ← mkCodecHeader indVal
  let body ← mkCodecBody indVal header.argNames
  `(def $(mkIdent auxName):ident $[$(header.binders):bracketedBinder]* :
      Sexp.TermCodec $(header.targetType) := $body:term)

private def mkInstance (ctx : Lean.Elab.Deriving.Context) : TermElabM Command := do
  let indVal := ctx.typeInfos[0]!
  let header ← mkCodecHeader indVal
  `(instance $(mkIdent ctx.instName):ident $[$(header.binders):bracketedBinder]* :
      Sexp.SExprCodec $(header.targetType) := ⟨$(mkIdent ctx.auxFunNames[0]!):ident⟩)

private def mkCommands (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``Sexp.SExprCodec "codec" declName
  if ctx.typeInfos.size != 1 then
    throwError "SExprCodec deriving does not yet support mutually recursive structures"
  if ctx.typeInfos[0]!.isRec then
    throwError "SExprCodec deriving does not yet support recursive structures"
  pure #[← mkAuxFunction ctx, ← mkInstance ctx]

private def deriveSExprCodec (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then return false
  for declName in declNames do
    let commands ← liftTermElabM <| mkCommands declName
    commands.forM elabCommand
  return true

initialize
  registerDerivingHandler ``Sexp.SExprCodec deriveSExprCodec

end Sexp.Deriving
