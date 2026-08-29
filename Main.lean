import Sexp

open Sexp

universe u v

inductive Higher : Type 1 where
  | value
  deriving BEq

instance : SExprCodec Higher where
  codec := TermCodec.imap (fun _ => .value) (fun _ => "higher") Codec.string

structure Item where
  name : String
  enabled : Bool
  aliases : List String
  deriving Repr, BEq, SExprCodec

structure UBox (α : Type u) where
  value : α
  deriving SExprCodec

structure CodecParam (α : Type u) [SExprCodec α] where
  value : α
  deriving SExprCodec

structure HK (f : Type u → Type v) (α : Type u) [SExprCodec (f α)] where
  value : f α
  deriving SExprCodec

inductive NoCodec

abbrev NatF (_ : Type) := Nat

structure Box (α : Type) where
  value : α
  deriving Repr, BEq, SExprCodec

structure PairBox (α β : Type) where
  left : α
  right : β
  deriving Repr, BEq, SExprCodec

/--
error: Application type mismatch: The argument
  Codec.constant ()
has type
  Codec Unit
but is expected to have type
  TermCodec ?m.1
in the application
  Codec.many (Codec.constant ())
-/
#guard_msgs(error) in
#check Codec.many (Codec.constant ())

example : Codec.TermRoundTrips Codec.natural := by
  intro value
  rfl

example : Codec.RoundTrips (Codec.many Codec.natural : Codec (List Nat)) :=
  Codec.many_roundTrips (Codec.termRoundTrips_iff.mpr (by intro value; rfl))

private def checkDecimal : IO Unit := do
  let decimal := Decimal.ofScientific 10 1
  assert! decimal.mantissa == 1
  assert! decimal.scale == 0
  assert! decimal.render == "1"
  assert! Decimal.parse? "1.0" == some decimal
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render decimal))) == decimal

private def checkDeriving : IO Unit := do
  let original : Item := {
    name := "hello world"
    enabled := true
    aliases := ["short", "h"]
  }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render original))) == original

  let boxed : Box (List Nat) := { value := [1, 2, 3] }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render boxed))) == boxed

  let uboxed : UBox (List Higher) := { value := [.value] }
  assert! match (SExprCodec.parse (SExprCodec.render uboxed) : Except String (UBox (List Higher))) with
    | .ok decoded => decoded.value == uboxed.value
    | .error _ => false

  let codecParam : CodecParam (List Higher) := { value := [.value] }
  assert! match (SExprCodec.parse (SExprCodec.render codecParam) : Except String (CodecParam (List Higher))) with
    | .ok decoded => decoded.value == codecParam.value
    | .error _ => false

  let higherKinded : HK NatF NoCodec := { value := 42 }
  assert! match (SExprCodec.parse (SExprCodec.render higherKinded) : Except String (HK NatF NoCodec)) with
    | .ok decoded => decoded.value == higherKinded.value
    | .error _ => false

  let pair : PairBox String Bool := { left := "ready", right := true }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render pair))) == pair

private def checkStringSafety : IO Unit := do
  for value in ["hello world", "123", ""] do
    let renderedBare := SExpr.render (.str .bare value)
    assert! renderedBare == SExpr.render (.str .quoted value)
    assert! (← IO.ofExcept (SExpr.parse renderedBare)) == .str .quoted value
    let [term] := Codec.bareString.encode value
      | throw (IO.userError "bare string codec did not encode one term")
    let parsed ← IO.ofExcept (SExpr.parse (SExpr.render term))
    assert! (← IO.ofExcept (Codec.bareString.run [parsed])) == value

private def checkTagRoundTrip (tag : String) : IO Unit := do
  let codec := Codec.tagged tag Codec.string
  let [encoded] := codec.encode "payload"
    | throw (IO.userError "tagged codec did not encode one term")
  let parsed ← IO.ofExcept (SExpr.parse (SExpr.render encoded))
  assert! (← IO.ofExcept (codec.run [parsed])) == "payload"

private def checkLargeList : IO Unit := do
  let count := 200_000
  let input := .list (.str .bare "list" :: List.replicate count (.str .bare "value"))
  let decoded ← IO.ofExcept (Codec.many Codec.string |>.decodeTerm input)
  assert! decoded.length == count

def main : IO Unit := do
  checkDecimal
  checkDeriving
  checkStringSafety
  checkTagRoundTrip "hello world"
  checkTagRoundTrip "123"
  checkLargeList
