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

structure Even where
  n : Nat
  isEven : n % 2 = 0
  deriving SExprCodec

structure BoundedEven extends Even where
  label : String
  small : n < 10
  deriving SExprCodec

structure Checked (α : Type u) (p : α → Prop) [SExprCodec α] [DecidablePred p] where
  value : α
  valid : p value
  deriving SExprCodec
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

private def checkProofs : IO Unit := do
  let even : Even := ⟨4, by decide⟩
  assert! SExprCodec.render even == "(Even 4)"
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render even)) : Even).n == 4
  assert! (SExprCodec.parse "(Even 3)" : Except String Even).toOption.isNone
  assert! (SExprCodec.parse "(Even 4 proof)" : Except String Even).toOption.isNone
  let bounded : BoundedEven := { n := 4, isEven := by decide, label := "ok", small := by decide }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render bounded)) : BoundedEven).label == "ok"
  assert! (SExprCodec.parse "(BoundedEven 12 ok)" : Except String BoundedEven).toOption.isNone
  assert! (SExprCodec.parse "(BoundedEven 3 ok)" : Except String BoundedEven).toOption.isNone
  let checked : Checked Nat (fun n => n % 2 = 0) := ⟨4, by decide⟩
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render checked)) : Checked Nat (fun n => n % 2 = 0)).value == 4
  assert! (SExprCodec.parse "(Checked 3)" : Except String (Checked Nat (fun n => n % 2 = 0))).toOption.isNone
  let refined : {n : Nat // n % 2 = 0} := ⟨4, by decide⟩
  assert! SExprCodec.render refined == "4"
  assert! (← IO.ofExcept (SExprCodec.parse "4") : {n : Nat // n % 2 = 0}).val == 4
  assert! (SExprCodec.parse "3" : Except String {n : Nat // n % 2 = 0}).toOption.isNone
  assert! (SExprCodec.parse "nope" : Except String {n : Nat // n % 2 = 0}).toOption.isNone

def main : IO Unit := do
  checkProofs
  checkDecimal
  checkDeriving
  checkStringSafety
  checkTagRoundTrip "hello world"
  checkTagRoundTrip "123"
  checkLargeList
