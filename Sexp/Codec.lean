import Sexp.SExpr

namespace Sexp

structure DecodeError where
  context : List String := []
  message : String
  deriving Repr, BEq

instance : ToString DecodeError := ⟨reprStr⟩

abbrev DecodeM := Except DecodeError
abbrev Input := List SExpr

/-- Bidirectional codec over an S-expression stream. -/
structure Codec (α : Type) where
  decode : Input → DecodeM (α × Input)
  encode : α → Input

namespace Codec

private def expected (wanted : String) (found : SExpr) : DecodeM α :=
  throw { message := s!"expected {wanted}; found {repr found}" }

/-- Decode a complete stream. -/
def run (codec : Codec α) (input : Input) : DecodeM α := do
  let (value, rest) ← codec.decode input
  unless rest.isEmpty do
    throw { message := s!"unparsed terms: {repr rest}" }
  pure value

/-- Transport a codec through a retraction. Round-tripping needs `to (back x) = x`. -/
def imap (to : α → β) (back : β → α) (codec : Codec α) : Codec β where
  decode := fun input => do
    let (value, rest) ← codec.decode input
    pure (to value, rest)
  encode := codec.encode ∘ back

/-- Codec consuming and emitting nothing. -/
def constant (value : α) : Codec α where
  decode := fun input => .ok (value, input)
  encode := fun _ => []

/-- Sequential composition. -/
def product (left : Codec α) (right : Codec β) : Codec (α × β) where
  decode := fun input => do
    let (a, input) ← left.decode input
    let (b, input) ← right.decode input
    pure ((a, b), input)
  encode := fun (a, b) => left.encode a ++ right.encode b

infixr:35 " ×ₚ " => Codec.product

/-- Lift a codec for one term into stream composition. -/
def term (decodeTerm : SExpr → DecodeM α) (encodeTerm : α → SExpr) : Codec α where
  decode
    | [] => throw { message := "expected term; found end of input" }
    | value :: rest => return (← decodeTerm value, rest)
  encode := fun value => [encodeTerm value]

/-- Parenthesize a body codec. -/
def list (body : Codec α) : Codec α :=
  term
    (fun value => match value with
      | .list children => body.run children
      | found => expected "list" found)
    (.list ∘ body.encode)

/-- Prefix a parenthesized body with a tag. -/
def tagged (tag : String) (body : Codec α) : Codec α :=
  term
    (fun value => match value with
      | .list (.str .bare foundTag :: children) => do
          unless foundTag = tag do
            throw { context := [tag], message := s!"expected tag {tag}; found {foundTag}" }
          (body.run children).mapError fun error =>
            { error with context := tag :: error.context }
      | found => expected s!"({tag} ...)" found)
    (fun value => .list (.str .bare tag :: body.encode value))

def string : Codec String :=
  term
    (fun value => match value with
      | .str _ string => pure string
      | found => expected "string" found)
    SExpr.string

def quotedString : Codec String :=
  term
    (fun value => match value with
      | .str _ string => pure string
      | found => expected "string" found)
    (.str .quoted)

def bareString : Codec String :=
  term
    (fun value => match value with
      | .str .bare string => pure string
      | found => expected "bare string" found)
    (.str .bare)

def decimal : Codec Decimal :=
  term
    (fun value => match value with
      | .num number => pure number
      | found => expected "decimal" found)
    .num

def natural : Codec Nat :=
  term
    (fun value => match value with
      | .num { mantissa, scale := 0 } =>
          if mantissa ≥ 0 then pure mantissa.natAbs
          else expected "natural number" value
      | found => expected "natural number" found)
    (fun value => .num { mantissa := Int.ofNat value, scale := 0 })

def integer : Codec Int :=
  term
    (fun value => match value with
      | .num { mantissa, scale := 0 } => pure mantissa
      | found => expected "integer" found)
    (fun value => .num { mantissa := value, scale := 0 })

def hex : Codec Nat :=
  term
    (fun value => match value with
      | .hex number => pure number
      | found => expected "hexadecimal integer" found)
    .hex

def bool : Codec Bool :=
  term
    (fun value => match value with
      | .str .bare "yes" => pure true
      | .str .bare "no" => pure false
      | found => expected "yes or no" found)
    (fun value => .str .bare (if value then "yes" else "no"))

/-- Explicit option grammar: `(none)` or `(some VALUE...)`. -/
def option (codec : Codec α) : Codec (Option α) where
  decode
    | .list [.str .bare "none"] :: rest => pure (none, rest)
    | .list (.str .bare "some" :: children) :: rest =>
        return (some (← codec.run children), rest)
    | found :: _ => expected "(none) or (some ...)" found
    | [] => throw { message := "expected option; found end of input" }
  encode
    | none => [.list [.str .bare "none"]]
    | some value => [.list (.str .bare "some" :: codec.encode value)]

/-- Explicit list grammar: `(list VALUE...)`. -/
def many (codec : Codec α) : Codec (List α) where
  decode
    | .list (.str .bare "list" :: children) :: rest => do
        let rec loop (fuel : Nat) (input : Input) (acc : List α) : DecodeM (List α) := do
          if input.isEmpty then pure acc.reverse
          else match fuel with
            | 0 => throw { message := "list element codec consumed no input" }
            | fuel + 1 =>
                let (value, next) ← codec.decode input
                if next.length < input.length then loop fuel next (value :: acc)
                else throw { message := "list element codec consumed no input" }
        pure (← loop children.length children [], rest)
    | found :: _ => expected "(list ...)" found
    | [] => throw { message := "expected list; found end of input" }
  encode := fun values => [.list (.str .bare "list" :: values.flatMap codec.encode)]

/-- Decoder accepts encoder output and leaves following input untouched. -/
def RoundTrips (codec : Codec α) : Prop :=
  ∀ value rest, codec.decode (codec.encode value ++ rest) = .ok (value, rest)

end Codec

/-- Canonical codec used by generic derivation. Instances must encode one term. -/
class SExprCodec (α : Type) where
  codec : Codec α

export SExprCodec (codec)

instance : SExprCodec String := ⟨Codec.string⟩
instance : SExprCodec Bool := ⟨Codec.bool⟩
instance : SExprCodec Nat := ⟨Codec.natural⟩
instance : SExprCodec Int := ⟨Codec.integer⟩
instance : SExprCodec Decimal := ⟨Codec.decimal⟩
instance [SExprCodec α] : SExprCodec (Option α) := ⟨Codec.option (codec (α := α))⟩
instance [SExprCodec α] : SExprCodec (List α) := ⟨Codec.many (codec (α := α))⟩

namespace SExprCodec

def encode [SExprCodec α] (value : α) : SExpr :=
  match (codec (α := α)).encode value with
  | [result] => result
  | results => .list results

def decode [SExprCodec α] (value : SExpr) : DecodeM α :=
  (codec (α := α)).run [value]

def parse [SExprCodec α] (input : String) : Except String α := do
  let value ← (SExpr.parse input).mapError toString
  (decode value).mapError toString

def render [SExprCodec α] (value : α) : String :=
  SExpr.render (encode value)

end SExprCodec
end Sexp
