import Sexp

open Sexp

structure Item where
  name : String
  enabled : Bool
  aliases : List String
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
  IO.println encoded
