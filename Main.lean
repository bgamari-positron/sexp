import Sexp

open Sexp

structure Item where
  name : String
  enabled : Bool
  aliases : List String
  deriving Repr, BEq, SExprCodec

structure Box (α : Type) where
  value : α
  deriving Repr, BEq, SExprCodec

structure PairBox (α β : Type) where
  left : α
  right : β
  deriving Repr, BEq, SExprCodec

def main : IO Unit := do
  let original : Item := {
    name := "hello world"
    enabled := true
    aliases := ["short", "h"]
  }
  let encoded := SExprCodec.render original
  let decoded ← IO.ofExcept (SExprCodec.parse encoded)
  assert! decoded == original

  let boxed : Box (List Nat) := { value := [1, 2, 3] }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render boxed))) == boxed

  let pair : PairBox String Bool := { left := "ready", right := true }
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render pair))) == pair

  IO.println encoded
  IO.println (SExprCodec.render boxed)
  IO.println (SExprCodec.render pair)
