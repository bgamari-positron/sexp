import Sexp

namespace Sexp.Tests.Recursive

inductive Ty where
  | unsigned (width : Nat)
  | array (element : Ty)
  deriving SExprCodec

inductive Expr (ν : Ty → Type) : Ty → Type where
  | literal {width : Nat} (value : Nat) (fits : value < 2 ^ width) : Expr ν (.unsigned width)
  | var {t : Ty} (name : ν t) : Expr ν t
  | checkedMul {width : Nat} (left right : Expr ν (.unsigned width)) : Expr ν (.unsigned width)
  | index {t : Ty} (array : Expr ν (.array t)) (offset : Expr ν (.unsigned 32)) : Expr ν t
  deriving SExprCodec

def encode {ν : Ty → Type} [∀ t, SExprCodec (ν t)] {t : Ty} : Expr ν t → SExpr
  | .literal value _ => .list [.str .bare "literal", Codec.natural.encodeTerm value]
  | .var name => .list [.str .bare "var", SExprCodec.encode name]
  | .checkedMul left right => .list [.str .bare "checkedMul", encode left, encode right]
  | .index array offset => .list [.str .bare "index", encode array, encode offset]

def decode {ν : Ty → Type} [∀ t, SExprCodec (ν t)] (t : Ty) (input : SExpr) : DecodeM (Expr ν t) :=
  match t, input with
  | .unsigned width, .list [.str _ "literal", value] => do
    let value ← Codec.natural.decodeTerm value
    if h : value < 2 ^ width then return .literal value h
    else throw { message := "literal out of range" }
  | _, .list [.str _ "var", name] => return .var (← SExprCodec.decode name)
  | .unsigned width, .list [.str _ "checkedMul", left, right] =>
    return .checkedMul (← decode (.unsigned width) left) (← decode (.unsigned width) right)
  | t, .list [.str _ "index", array, offset] =>
    return .index (← decode (.array t) array) (← decode (.unsigned 32) offset)
  | _, _ => throw { message := "invalid expression for expected type" }
termination_by sizeOf input

private theorem natural_roundTrips (n : Nat) :
    Codec.natural.decodeTerm (Codec.natural.encodeTerm n) = .ok n := rfl

theorem roundTrips {ν : Ty → Type} [∀ t, SExprCodec (ν t)]
    (names : ∀ t, Codec.TermRoundTrips (codec (α := ν t))) {t : Ty} (value : Expr ν t) :
    decode t (encode value) = .ok value := by
  induction value with
  | literal value fits => simp [encode, decode, natural_roundTrips, fits, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | var name =>
    simp [encode, decode, SExprCodec.encode, SExprCodec.decode, TermCodec.run,
      TermCodec.encode, TermCodec.decode, TermCodec.toCodec, names _ name,
      Bind.bind, Pure.pure, Except.bind, Except.pure]
  | checkedMul left right ihLeft ihRight => simp [encode, decode, ihLeft, ihRight, Bind.bind, Pure.pure, Except.bind, Except.pure]
  | index array offset ihArray ihOffset => simp [encode, decode, ihArray, ihOffset, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem natCodec_roundTrips (n : Nat) :
    (codec (α := Nat)).decodeTerm ((codec (α := Nat)).encodeTerm n) = .ok n := rfl

theorem derived_roundTrips {ν : Ty → Type} [∀ t, SExprCodec (ν t)]
    (names : ∀ t, Codec.TermRoundTrips (codec (α := ν t))) {t : Ty} :
    Codec.TermRoundTrips (codec (α := Expr ν t)) := by
  intro value
  change instSExprCodecExpr.codec.decode (instSExprCodecExpr.codec.encode value) = .ok value
  induction value with
  | literal value fits =>
    simp [instSExprCodecExpr.codec.encode, instSExprCodecExpr.codec.decode, SExpr.string,
      natCodec_roundTrips, fits, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.mapError]
  | var name =>
    simp [instSExprCodecExpr.codec.encode, instSExprCodecExpr.codec.decode, SExpr.string,
      names _ name, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.mapError]
  | checkedMul left right ihLeft ihRight =>
    simp [instSExprCodecExpr.codec.encode, instSExprCodecExpr.codec.decode, SExpr.string,
      ihLeft, ihRight, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.mapError]
  | index array offset ihArray ihOffset =>
    simp [instSExprCodecExpr.codec.encode, instSExprCodecExpr.codec.decode, SExpr.string,
      ihArray, ihOffset, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.mapError]

def exprCodec {ν : Ty → Type} [∀ t, SExprCodec (ν t)] (t : Ty) : TermCodec (Expr ν t) :=
  { encodeTerm := encode, decodeTerm := decode t }

inductive CheckedChain where
  | stop
  | step (child : CheckedChain) (count : Nat) (valid : count < 4)
  deriving DecidableEq, SExprCodec

def check : IO Unit := do
  let expression : Expr (fun _ => String) (.unsigned 8) :=
    .checkedMul (.literal 3 (by decide)) (.index (.var "values") (.literal 2 (by decide)))
  for codec in [exprCodec (ν := fun _ => String) (.unsigned 8),
      Sexp.codec (α := Expr (fun _ => String) (.unsigned 8))] do
    let rendered := SExpr.render (codec.encodeTerm expression)
    assert! rendered == "(checkedMul (literal 3) (index (var values) (literal 2)))"
    let decoded ← IO.ofExcept ((codec.decodeTerm (← IO.ofExcept (SExpr.parse rendered))).mapError toString)
    assert! SExpr.render (codec.encodeTerm decoded) == rendered
    for invalid in ["(literal 256)", "(checkedMul (literal 1))",
        "(checkedMul (literal 1) (literal 2) extra)",
        "(index (literal 0) (literal 1))", "(index (var values) (literal 4294967296))",
        "(checkedMul (literal 1) (unknown))"] do
      let input ← IO.ofExcept (SExpr.parse invalid)
      assert! (codec.decodeTerm input).toOption.isNone
  let nestedError ← IO.ofExcept (SExpr.parse "(checkedMul (literal 1) (literal 256))")
  assert! (match SExprCodec.decode (α := Expr (fun _ => String) (.unsigned 8)) nestedError with
    | .error error => error.context == ["checkedMul", "literal"] && error.message == "proof field fits failed"
    | .ok _ => false : Bool)
  let deep := (List.range 128).foldl (fun acc _ => Expr.checkedMul acc (.literal 1 (by decide))) expression
  let decoded : Expr (fun _ => String) (.unsigned 8) ←
    IO.ofExcept (SExprCodec.parse (SExprCodec.render deep))
  assert! SExprCodec.render decoded == SExprCodec.render deep
  let ty := Ty.array (.array (.unsigned 8))
  let decodedTy : Ty ← IO.ofExcept (SExprCodec.parse (SExprCodec.render ty))
  assert! SExprCodec.render decodedTy == "(array (array (unsigned 8)))"
  let chain := CheckedChain.step (.step .stop 2 (by decide)) 1 (by decide)
  let decodedChain : CheckedChain ← IO.ofExcept (SExprCodec.parse (SExprCodec.render chain))
  assert! SExprCodec.render decodedChain == "(step (step (stop) 2) 1)"

/-- error: SExprCodec deriving supports only direct recursive fields -/
#guard_msgs in
inductive Nested where
  | node (children : List Nested)
  deriving SExprCodec

/-- error: SExprCodec deriving supports only direct recursive fields -/
#guard_msgs in
inductive FunctionRecursive where
  | node (children : Nat → FunctionRecursive)
  deriving SExprCodec

end Sexp.Tests.Recursive
