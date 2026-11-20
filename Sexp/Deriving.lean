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

private partial def mkIndexPattern (index : Expr) (fields : Array Expr)
    (locals : Array Ident) (seen : Array FVarId := #[]) : TermElabM (Term × Array FVarId × Bool) := do
  match (← whnf index).consumeMData with
  | .fvar id =>
    unless fields.contains (.fvar id) && !seen.contains id do
      throwError "SExprCodec deriving requires distinct constructor fields in index patterns"
    let some i := fields.idxOf? (.fvar id) | unreachable!
    return (⟨locals[i]!.raw⟩, seen.push id, false)
  | .lit (.natVal n) => return (Syntax.mkNumLit (toString n), seen, true)
  | index =>
    let .const name _ := index.getAppFn
      | throwError "SExprCodec deriving requires constructor-shaped indices"
    let .ctorInfo ctor ← getConstInfo name
      | throwError "SExprCodec deriving requires constructor-shaped indices"
    let args := index.getAppArgs
    let mut patterns ← (List.range ctor.numParams).toArray.mapM fun _ => `(_)
    let mut seen := seen
    let mut mayFail : Bool := (← getConstInfoInduct ctor.induct).ctors.length > 1
    for arg in args.extract ctor.numParams args.size do
      let (pattern, nextSeen, argMayFail) ← mkIndexPattern arg fields locals seen
      patterns := patterns.push pattern
      seen := nextSeen
      mayFail := mayFail || argMayFail
    return (← `(@$(mkCIdent name) $patterns*), seen, mayFail)

private def mkInductiveCodecBody (indVal : InductiveVal) (argNames : Array Name) :
    TermElabM Term := do
  let input := mkIdent `input
  let tag := mkIdent `tag
  let typeName := Syntax.mkStrLit indVal.name.toString
  let mut decode ← `(throw { message := "unknown constructor tag for " ++ $typeName ++ ": " ++ $tag:ident })
  let mut alternatives := #[]
  for ctorName in indVal.ctors.reverse do
    let ctor ← getConstInfoCtor ctorName
    let (fields, locals, proofTypes, indexPattern, stored) ← forallBoundedTelescope ctor.type indVal.numParams fun params type => do
      forallBoundedTelescope type ctor.numFields fun fields result => do
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
        let (indexPattern, recovered) ← if indVal.numIndices == 0 then pure (none, #[]) else do
          let (pattern, recovered, mayFail) ← mkIndexPattern result.getAppArgs[indVal.numParams]! fields locals
          pure (some (pattern, mayFail), recovered)
        let stored := (List.range fields.size).toArray.filter fun i => !recovered.contains fields[i]!.fvarId!
        return (names, locals, proofTypes, indexPattern, stored)
    let params ← (argNames.extract 0 indVal.numParams).mapM fun _ => `(_)
    let args : Array Term := locals.map fun localId => ⟨localId.raw⟩
    let constructor ← `(@$(mkCIdent ctorName) $params* $args*)
    let decoder ← mkFieldDecoder (stored.map (fields[·]!)) (stored.map (locals[·]!))
      (stored.map (proofTypes[·]!)) constructor
    let encoded ← mkFieldEncoder (stored.map (args[·]!)) (stored.map (proofTypes[·]!))
    let ctorTag := Syntax.mkStrLit ctorName.eraseMacroScopes.getString!
    let mut branch ← `((Sexp.Codec.tagged $ctorTag {
      decode := fun $input:ident => $decoder
      encode := fun _ => [] }).decodeTerm $input:ident)
    if let some (pattern, mayFail) := indexPattern then
      let index := mkIdent argNames[indVal.numParams]!
      if !mayFail then
        branch ← `(match $index:ident with | $pattern => $branch)
      else
        branch ← `(match $index:ident with
          | $pattern => $branch
          | _ => throw { context := [$ctorTag], message := "constructor incompatible with expected index" })
    decode ← `(if $tag:ident == $ctorTag then $branch else $decode)
    alternatives := alternatives.push (← `(matchAltExpr|
      | $constructor => Sexp.SExpr.list (Sexp.SExpr.string $ctorTag :: $encoded)))
  let encoder ← if alternatives.isEmpty then `(fun value => nomatch value)
    else `(fun value => match value with $alternatives:matchAlt*)
  `({ decodeTerm := fun $input:ident =>
        match $input:ident with
        | .list (.str _ $tag:ident :: _) => $decode
        | _ => throw { message := "expected constructor list for " ++ $typeName }
      encodeTerm := $encoder })

private def paramTypeSyntax (xs : Array Expr) (argNames : Array Name)
    (type : Expr) : TermElabM Term := do
  let mut lctx ← getLCtx
  for param in xs, name in argNames do
    lctx := lctx.setUserName param.fvarId! name
  withLCtx lctx (← getLocalInstances) do
    PrettyPrinter.delab type

private def codecConstraint (param : Expr) : TermElabM Expr := do
  forallTelescope (← inferType param) fun args _ => do
    let type ← mkAppM ``Sexp.SExprCodec #[mkAppN param args]
    unless ← isTypeCorrect type do
      throwError "parameter does not produce a type"
    mkForallFVars args type

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

/-- Preserve instance parameters from the type and add only non-duplicate
codec parameters accepted by `SExprCodec`. -/
private def mkCodecHeader (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let targetType ← mkInductiveApp indVal argNames
  let binders ← forallTelescope indVal.type fun xs _ => do
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
    unless ← fieldsHaveCodecs indVal (xs.extract 0 indVal.numParams) do
      for h : i in *...indVal.numParams do
        try
          let type ← codecConstraint xs[i]!
          if !(← instanceTypes.anyM fun instanceType => liftMetaM <| isDefEqGuarded type instanceType) then
            let typeSyntax ← paramTypeSyntax xs argNames type
            binders := binders.push (← `(instBinderF| [$typeSyntax])).raw
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
  if ctx.typeInfos[0]!.numIndices > 1 then
    throwError "SExprCodec deriving does not yet support multiple indices"
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
