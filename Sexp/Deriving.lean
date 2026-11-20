import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Sexp.Codec

namespace Sexp.Deriving

open Lean Elab Command Term Meta
open Lean.Parser.Term
open Lean.Elab.Deriving

private def mkFieldDecoder (fields : Array Name) (locals : Array Ident)
    (proofTypes : Array (Option Term)) (result : Term) : TermElabM Term := do
  let input := mkIdent `input
  let mut decoder ← `(pure ($result, $input:ident))
  for i in (List.range fields.size).reverse do
    let localId := locals[i]!
    if let some proposition := proofTypes[i]! then
      let message := Syntax.mkStrLit s!"proof field {fields[i]!} failed"
      decoder ← `(if $localId:ident : $proposition then $decoder
        else throw { message := $message })
    else
      decoder ← `(do
        let ($localId:ident, $input:ident) ← (Sexp.codec (α := _)).decode $input:ident
        return ← $decoder)
  return decoder

private def mkFieldEncoder (values : Array Term) (proofTypes : Array (Option Term)) :
    TermElabM Term := do
  let mut encoded ← `([])
  for i in (List.range values.size).reverse do
    if proofTypes[i]!.isNone then
      encoded ← `((Sexp.codec (α := _)).encode $(values[i]!) ++ $encoded)
  return encoded

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
  let decoder ← mkFieldDecoder fields locals proofTypes (← `({ $assignments:structInstField,* }))
  let values ← fields.mapM fun field => `($value:ident.$(mkIdent field):ident)
  let encoded ← mkFieldEncoder values proofTypes
  let tag := Syntax.mkStrLit indVal.name.eraseMacroScopes.getString!
  `(Sexp.Codec.tagged $tag {
      decode := fun $input:ident => $decoder
      encode := fun $value:ident => $encoded
    })

private def mkInductiveCodecBody (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM Term := do
  let input := mkIdent `input
  let tag := mkIdent `tag
  let typeName := Syntax.mkStrLit indVal.name.toString
  let mut decode ← `(throw { message := "unknown constructor tag for " ++ $typeName ++ ": " ++ $tag:ident })
  let mut alternatives := #[]
  for ctorName in indVal.ctors.reverse do
    let ctor ← getConstInfoCtor ctorName
    let (fields, locals, proofTypes) ← forallBoundedTelescope ctor.type indVal.numParams fun params type => do
      forallBoundedTelescope type ctor.numFields fun fields _ => do
        let names ← fields.mapM fun field => return (← field.fvarId!.getDecl).userName
        let locals := fields.mapIdx fun i _ => mkIdent (Name.mkSimple s!"v{i}")
        let mut lctx ← getLCtx
        for param in params, name in argNames do
          lctx := lctx.setUserName param.fvarId! name
        for field in fields, localId in locals do
          lctx := lctx.setUserName field.fvarId! localId.getId
        let proofTypes ← withLCtx lctx (← getLocalInstances) do
          fields.mapM fun field => do
            let type ← inferType field
            if ← isProp type then return some (← PrettyPrinter.delab type)
            else return none
        return (names, locals, proofTypes)
    let params ← argNames.mapM fun _ => `(_)
    let args : Array Term := locals.map fun localId => ⟨localId.raw⟩
    let constructor ← `(@$(mkCIdent ctorName) $params* $args*)
    let decoder ← mkFieldDecoder fields locals proofTypes constructor
    let encoded ← mkFieldEncoder args proofTypes
    let ctorTag := Syntax.mkStrLit ctorName.eraseMacroScopes.getString!
    decode ← `(if $tag:ident == $ctorTag then
      (Sexp.Codec.tagged $ctorTag {
        decode := fun $input:ident => $decoder
        encode := fun _ => [] }).decodeTerm $input:ident
      else $decode)
    alternatives := alternatives.push (← `(matchAltExpr|
      | $constructor => Sexp.SExpr.list (Sexp.SExpr.string $ctorTag :: $encoded)))
  let encoder ← if alternatives.isEmpty then `(fun value => nomatch value)
    else `(fun value => match value with $alternatives:matchAlt*)
  `({ decodeTerm := fun $input:ident =>
        match $input:ident with
        | .list (.str _ $tag:ident :: _) => $decode
        | _ => throw { message := "expected constructor list for " ++ $typeName }
      encodeTerm := $encoder })

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
  try
    for ctorName in indVal.ctors do
      let ctor ← getConstInfoCtor ctorName
      let type ← liftMetaM <| instantiateForall ctor.type params
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
  let body ← if isStructure (← getEnv) indVal.name then mkCodecBody indVal header.argNames
    else mkInductiveCodecBody indVal header.argNames
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
    throwError "SExprCodec deriving does not yet support mutually recursive types"
  if ctx.typeInfos[0]!.isRec then
    throwError "SExprCodec deriving does not yet support recursive types"
  if ctx.typeInfos[0]!.numIndices != 0 then
    throwError "SExprCodec deriving does not yet support indexed inductives"
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
