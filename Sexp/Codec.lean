import Sexp.SExpr

namespace Sexp

universe u v

structure DecodeError where
  context : List String := []
  message : String
  deriving Repr, BEq

instance : ToString DecodeError := ⟨reprStr⟩

abbrev DecodeM := Except DecodeError
abbrev Input := List SExpr

/-- Bidirectional codec over an S-expression stream. -/
structure Codec (α : Type u) where
  decode : Input → DecodeM (α × Input)
  encode : α → Input

/-- Codec whose representation is exactly one S-expression term. -/
structure TermCodec (α : Type u) where
  decodeTerm : SExpr → DecodeM α
  encodeTerm : α → SExpr

namespace TermCodec

/-- Forget that a codec consumes exactly one term. -/
def toCodec {α : Type u} (codec : TermCodec α) : Codec α where
  decode
    | [] => throw { message := "expected term; found end of input" }
    | value :: rest => return (← codec.decodeTerm value, rest)
  encode := fun value => [codec.encodeTerm value]

instance {α : Type u} : Coe (TermCodec α) (Codec α) := ⟨toCodec⟩

def decode {α : Type u} (codec : TermCodec α) : Input → DecodeM (α × Input) :=
  codec.toCodec.decode

def encode {α : Type u} (codec : TermCodec α) : α → Input :=
  codec.toCodec.encode

def run {α : Type u} (codec : TermCodec α) (input : Input) : DecodeM α := do
  let (value, rest) ← codec.decode input
  unless rest.isEmpty do
    throw { message := s!"unparsed terms: {repr rest}" }
  pure value

/-- Transport a one-term codec through a retraction. -/
def imap {α : Type u} {β : Type v} (to : α → β) (back : β → α)
    (codec : TermCodec α) : TermCodec β where
  decodeTerm := fun value => codec.decodeTerm value |>.map to
  encodeTerm := codec.encodeTerm ∘ back

/-- Validate decoded values and use the reverse projection for encoding. -/
def emap {α : Type u} {β : Type v} (to : α → DecodeM β) (back : β → α)
    (codec : TermCodec α) : TermCodec β where
  decodeTerm := fun value =>
    match codec.decodeTerm value with
    | .ok decoded => to decoded
    | .error error => .error error
  encodeTerm := codec.encodeTerm ∘ back

/-- Encode only the value; check the predicate when decoding. -/
def subtype {α : Type u} (p : α → Prop) [DecidablePred p]
    (codec : TermCodec α) : TermCodec {x : α // p x} where
  encodeTerm := fun value => codec.encodeTerm value.val
  decodeTerm := fun input => do
    let value ← codec.decodeTerm input
    if h : p value then
      return ⟨value, h⟩
    else
      throw { message := "subtype predicate failed" }

end TermCodec

namespace Codec

private def expected {α : Type u} (wanted : String) (found : SExpr) : DecodeM α :=
  throw { message := s!"expected {wanted}; found {repr found}" }

/-- Decode a complete stream. -/
def run {α : Type u} (codec : Codec α) (input : Input) : DecodeM α := do
  let (value, rest) ← codec.decode input
  unless rest.isEmpty do
    throw { message := s!"unparsed terms: {repr rest}" }
  pure value

/-- Transport a codec through a retraction. Round-tripping needs `to (back x) = x`. -/
def imap {α : Type u} {β : Type v} (to : α → β) (back : β → α) (codec : Codec α) : Codec β where
  decode := fun input =>
    match codec.decode input with
    | .ok (value, rest) => .ok (to value, rest)
    | .error error => .error error
  encode := codec.encode ∘ back

/-- Codec consuming and emitting nothing. -/
def constant {α : Type u} (value : α) : Codec α where
  decode := fun input => .ok (value, input)
  encode := fun _ => []

/-- Sequential composition. -/
def product {α : Type u} {β : Type v} (left : Codec α) (right : Codec β) : Codec (α × β) where
  decode := fun input =>
    match left.decode input with
    | .error error => .error error
    | .ok (a, input) =>
      match right.decode input with
      | .error error => .error error
      | .ok (b, input) => .ok ((a, b), input)
  encode := fun (a, b) => left.encode a ++ right.encode b

infixr:35 " ×ₚ " => Codec.product

/-- Lift a codec for one term into stream composition. -/
def term {α : Type u} (decodeTerm : SExpr → DecodeM α)
    (encodeTerm : α → SExpr) : TermCodec α where
  decodeTerm := decodeTerm
  encodeTerm := encodeTerm

/-- Parenthesize a body codec. -/
def list {α : Type u} (body : Codec α) : TermCodec α :=
  term
    (fun value => match value with
      | .list children => body.run children
      | found => expected "list" found)
    (.list ∘ body.encode)

/-- Prefix a parenthesized body with a tag. -/
def tagged {α : Type u} (tag : String) (body : Codec α) : TermCodec α :=
  term
    (fun value => match value with
      | .list (.str _ foundTag :: children) => do
          unless foundTag = tag do
            throw { context := [tag], message := s!"expected tag {tag}; found {foundTag}" }
          (body.run children).mapError fun error =>
            { error with context := tag :: error.context }
      | found => expected s!"({tag} ...)" found)
    (fun value => .list (SExpr.string tag :: body.encode value))

def string : TermCodec String :=
  term
    (fun value => match value with
      | .str _ string => pure string
      | found => expected "string" found)
    SExpr.string

def quotedString : TermCodec String :=
  term
    (fun value => match value with
      | .str _ string => pure string
      | found => expected "string" found)
    (.str .quoted)

/-- String codec preferring bare spelling and quoting when bare would be ambiguous. -/
def bareString : TermCodec String := string

def decimal : TermCodec Decimal :=
  term
    (fun value => match value with
      | .num number => pure number
      | found => expected "decimal" found)
    .num

def natural : TermCodec Nat :=
  term
    (fun value => match value with
      | .num number =>
          if number.scale = 0 && number.mantissa ≥ 0 then pure number.mantissa.natAbs
          else expected "natural number" value
      | found => expected "natural number" found)
    (fun value => .num (Decimal.ofScientific (Int.ofNat value) 0))

def integer : TermCodec Int :=
  term
    (fun value => match value with
      | .num number =>
          if number.scale = 0 then pure number.mantissa
          else expected "integer" value
      | found => expected "integer" found)
    (fun value => .num (Decimal.ofScientific value 0))

def hex : TermCodec Nat :=
  term
    (fun value => match value with
      | .hex number => pure number
      | found => expected "hexadecimal integer" found)
    .hex

def bool : TermCodec Bool :=
  term
    (fun value => match value with
      | .str .bare "yes" => pure true
      | .str .bare "no" => pure false
      | found => expected "yes or no" found)
    (fun value => .str .bare (if value then "yes" else "no"))

/-- Explicit option grammar: `(none)` or `(some VALUE...)`. -/
def option {α : Type u} (codec : Codec α) : TermCodec (Option α) :=
  term
    (fun value => match value with
      | .list [.str .bare "none"] => pure none
      | .list (.str .bare "some" :: children) => some <$> codec.run children
      | found => expected "(none) or (some ...)" found)
    (fun
      | none => .list [.str .bare "none"]
      | some value => .list (.str .bare "some" :: codec.encode value))

private def decodeManyAux {α : Type u} (codec : TermCodec α) :
    List SExpr → List α → DecodeM (List α)
  | [], acc => pure acc.reverse
  | value :: rest, acc =>
      match codec.decodeTerm value with
      | .ok decoded => decodeManyAux codec rest (decoded :: acc)
      | .error error => .error error

private def decodeMany {α : Type u} (codec : TermCodec α) (values : List SExpr) :
    DecodeM (List α) :=
  decodeManyAux codec values []

/-- Explicit list grammar: `(list VALUE...)`. Element codecs must consume one term. -/
def many {α : Type u} (codec : TermCodec α) : TermCodec (List α) :=
  term
    (fun value => match value with
      | .list (.str .bare "list" :: children) => decodeMany codec children
      | found => expected "(list ...)" found)
    (fun values => .list (.str .bare "list" :: values.map codec.encodeTerm))

/-- Decoder accepts encoder output and leaves following input untouched. -/
def RoundTrips {α : Type u} (codec : Codec α) : Prop :=
  ∀ value rest, codec.decode (codec.encode value ++ rest) = .ok (value, rest)

/-- One-term round-trip law. -/
def TermRoundTrips {α : Type u} (codec : TermCodec α) : Prop :=
  ∀ value, codec.decodeTerm (codec.encodeTerm value) = .ok value

/-- Fallible mapping preserves round trips if validation accepts every encoded value. -/
theorem emap_termRoundTrips {α : Type u} {β : Type v} {codec : TermCodec α}
    {to : α → DecodeM β} {back : β → α}
    (h : TermRoundTrips codec) (hback : ∀ value, to (back value) = .ok value) :
    TermRoundTrips (TermCodec.emap to back codec) := by
  intro value
  change (match codec.decodeTerm (codec.encodeTerm (back value)) with
    | .ok decoded => to decoded
    | .error error => .error error) = .ok value
  rw [h (back value)]
  exact hback value

theorem termRoundTrips_iff {α : Type u} {codec : TermCodec α} :
    RoundTrips (codec : Codec α) ↔ TermRoundTrips codec := by
  constructor
  · intro h value
    have hs := h value []
    change (do
      let decoded ← codec.decodeTerm (codec.encodeTerm value)
      pure (decoded, [])) = .ok (value, []) at hs
    cases hc : codec.decodeTerm (codec.encodeTerm value) with
    | error error =>
      rw [hc] at hs
      contradiction
    | ok decoded =>
      rw [hc] at hs
      change Except.ok (decoded, []) = Except.ok (value, []) at hs
      injection hs with pairEq
      have decodedEq : decoded = value := congrArg Prod.fst pairEq
      rw [decodedEq]
  · intro h value rest
    change (do
      let decoded ← codec.decodeTerm (codec.encodeTerm value)
      pure (decoded, rest)) = .ok (value, rest)
    rw [h value]
    rfl

private theorem decodeManyAux_map {α : Type u} {codec : TermCodec α}
    (h : TermRoundTrips codec) (values acc : List α) :
    decodeManyAux codec (values.map codec.encodeTerm) acc = .ok (acc.reverse ++ values) := by
  induction values generalizing acc with
  | nil =>
      change Except.ok acc.reverse = Except.ok (acc.reverse ++ [])
      rw [List.append_nil]
  | cons value values ih =>
      simp [decodeManyAux, h value, ih, List.append_assoc]

/-- Repetition preserves round trips when its element codec does. -/
theorem many_termRoundTrips {α : Type u} {codec : TermCodec α}
    (h : TermRoundTrips codec) : TermRoundTrips (many codec) := by
  intro values
  simp [many, term, decodeMany, decodeManyAux_map h]

/-- Stream-level round trips compose through repetition. -/
theorem many_roundTrips {α : Type u} {codec : TermCodec α}
    (h : RoundTrips (codec : Codec α)) : RoundTrips (many codec : Codec (List α)) :=
  termRoundTrips_iff.mpr (many_termRoundTrips (termRoundTrips_iff.mp h))

end Codec

/-- Canonical one-term codec used by generic derivation. -/
class SExprCodec (α : Type u) where
  codec : TermCodec α

export SExprCodec (codec)

instance : SExprCodec String := ⟨Codec.string⟩
instance : SExprCodec Bool := ⟨Codec.bool⟩
instance : SExprCodec Nat := ⟨Codec.natural⟩
instance : SExprCodec Int := ⟨Codec.integer⟩
instance : SExprCodec Decimal := ⟨Codec.decimal⟩
instance {α : Type u} [SExprCodec α] : SExprCodec (Option α) := ⟨Codec.option (codec (α := α))⟩
instance {α : Type u} [SExprCodec α] : SExprCodec (List α) := ⟨Codec.many (codec (α := α))⟩
instance {α : Type u} {p : α → Prop} [SExprCodec α] [DecidablePred p] :
    SExprCodec {x : α // p x} := ⟨TermCodec.subtype p (codec (α := α))⟩

namespace SExprCodec

def encode {α : Type u} [SExprCodec α] (value : α) : SExpr :=
  match (codec (α := α)).encode value with
  | [result] => result
  | results => .list results

def decode {α : Type u} [SExprCodec α] (value : SExpr) : DecodeM α :=
  (codec (α := α)).run [value]

def parse {α : Type u} [SExprCodec α] (input : String) : Except String α :=
  match SExpr.parse input with
  | .error error => .error (toString error)
  | .ok value => (decode value).mapError toString

def render {α : Type u} [SExprCodec α] (value : α) : String :=
  SExpr.render (encode value)

end SExprCodec
end Sexp
