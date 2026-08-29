namespace Sexp

inductive Quoting where
  | quoted
  | bare
  deriving Repr, BEq, Ord

/-- Exact, canonical decimal value: `mantissa * 10⁻scale`. -/
structure Decimal where
  mantissa : Int
  scale : Nat
  deriving Repr, BEq, Ord

namespace Decimal

private def normalizeAux (mantissa : Int) : (scale : Nat) → Decimal
  | 0 => { mantissa, scale := 0 }
  | scale + 1 =>
      if mantissa % 10 = 0 then
        normalizeAux (mantissa / 10) scale
      else
        { mantissa, scale := scale + 1 }

protected def normalize (d : Decimal) : Decimal :=
  normalizeAux d.mantissa d.scale

private def digit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none

private def digits? (cs : List Char) : Option Nat := do
  if cs.isEmpty then none else pure ()
  cs.foldlM (fun n c => return n * 10 + (← digit? c)) 0

protected def parse? (s : String) : Option Decimal := do
  let chars := s.toList
  let (negative, chars) := match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  let (whole, suffix) := chars.span (· != '.')
  let wholeValue ← digits? whole
  let (fraction, scale) ← match suffix with
    | [] => some (0, 0)
    | '.' :: rest =>
        match digits? rest with
        | some n => some (n, rest.length)
        | none => none
    | _ => none
  let magnitude := wholeValue * 10 ^ scale + fraction
  let mantissa : Int := if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude
  pure (Decimal.normalize { mantissa, scale })

protected def render (d : Decimal) : String :=
  let d := d.normalize
  let sign := if d.mantissa < 0 then "-" else ""
  let digits := toString d.mantissa.natAbs
  if d.scale = 0 then
    sign ++ digits
  else
    let padded := String.ofList (List.replicate (d.scale + 1 - digits.length) '0') ++ digits
    let split := padded.length - d.scale
    sign ++ padded.take split ++ "." ++ padded.drop split

end Decimal

inductive SExpr where
  | str (quoting : Quoting) (value : String)
  | num (value : Decimal)
  | hex (value : Nat)
  | list (children : List SExpr)
  deriving Repr, BEq

structure ParseError where
  offset : Nat
  message : String
  deriving Repr, BEq, Inhabited

instance : ToString ParseError := ⟨reprStr⟩

namespace SExpr

private structure Cursor where
  input : List Char
  offset : Nat := 0

private abbrev Parser := StateT Cursor (Except ParseError)

private def failAt (message : String) : Parser α := fun cursor =>
  Except.error ({ offset := cursor.offset, message } : ParseError)

private def next? : Parser (Option Char) := do
  let cursor ← get
  match cursor.input with
  | [] => pure none
  | c :: rest =>
      set ({ input := rest, offset := cursor.offset + 1 } : Cursor)
      pure (some c)

private def peek? : Parser (Option Char) :=
  return (← get).input.head?

private def whitespace (c : Char) : Bool :=
  c = ' ' || c = '\n' || c = '\r' || c = '\t'

private def delimiter (c : Char) : Bool :=
  whitespace c || c = '(' || c = ')' || c = '"'

private def skipWhitespace : Parser Unit := do
  while (← peek?).any whitespace do
    discard next?

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def hex? (chars : List Char) : Option Nat := do
  let digits := chars.filter (· != '_')
  if digits.isEmpty then none else pure ()
  digits.foldlM (fun n c => return n * 16 + (← hexDigit? c)) 0

private def classify (token : String) : SExpr :=
  match token.toList with
  | '0' :: 'x' :: rest =>
      match hex? rest with
      | some n => .hex n
      | none => .str .bare token
  | _ =>
      match Decimal.parse? token with
      | some n => .num n
      | none => .str .bare token

private partial def parseQuotedLoop (acc : List Char) : Parser String := do
  match ← next? with
  | none => failAt "unterminated quoted string"
  | some '"' => pure (String.ofList acc.reverse)
  | some '\\' =>
      match ← next? with
      | none => failAt "unterminated escape"
      | some 'n' => parseQuotedLoop ('\n' :: acc)
      | some 'r' => parseQuotedLoop ('\r' :: acc)
      | some 't' => parseQuotedLoop ('\t' :: acc)
      | some '"' => parseQuotedLoop ('"' :: acc)
      | some '\\' => parseQuotedLoop ('\\' :: acc)
      | some c => failAt s!"unknown escape \\{c}"
  | some c => parseQuotedLoop (c :: acc)

private def parseQuoted : Parser SExpr := do
  pure (.str .quoted (← parseQuotedLoop []))

private partial def parseTokenLoop (acc : List Char) : Parser String := do
  match ← peek? with
  | some c =>
      if delimiter c then pure (String.ofList acc.reverse)
      else
        discard next?
        parseTokenLoop (c :: acc)
  | none => pure (String.ofList acc.reverse)

private def parseToken (first : Char) : Parser SExpr := do
  pure (classify (← parseTokenLoop [first]))
mutual
  private partial def parseOne : Parser SExpr := do
    skipWhitespace
    match ← next? with
    | none => failAt "expected S-expression"
    | some '(' => parseList []
    | some ')' => failAt "unexpected ')'"
    | some '"' => parseQuoted
    | some c => parseToken c

  private partial def parseList (acc : List SExpr) : Parser SExpr := do
    skipWhitespace
    match ← peek? with
    | none => failAt "unterminated list"
    | some ')' =>
        discard next?
        pure (.list acc.reverse)
    | _ => parseList ((← parseOne) :: acc)
end

/-- Parse exactly one S-expression, rejecting trailing input. -/
def parse (input : String) : Except ParseError SExpr := do
  let (value, cursor) ← parseOne.run { input := input.toList }
  let (_, cursor) ← skipWhitespace.run cursor
  unless cursor.input.isEmpty do
    throw { offset := cursor.offset, message := "trailing input" }
  pure value

private def escape (s : String) : String :=
  s.toList.foldl (fun out c => out ++ match c with
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | '"' => "\\\""
    | '\\' => "\\\\"
    | c => String.singleton c) ""

private def renderHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def renderHex (n : Nat) : String :=
  if n < 16 then String.singleton (renderHexDigit n)
  else renderHex (n / 16) ++ String.singleton (renderHexDigit (n % 16))
termination_by n

/-- Render in compact canonical form. -/
def render : SExpr → String
  | .str .quoted value => "\"" ++ escape value ++ "\""
  | .str .bare value => value
  | .num value => value.render
  | .hex value => "0x" ++ renderHex value
  | .list children => "(" ++ " ".intercalate (children.map render) ++ ")"

private def canBeBare (value : String) : Bool :=
  !value.isEmpty && value.toList.all (fun c => !delimiter c) &&
    match classify value with
    | .str .bare _ => true
    | _ => false

/-- Construct a string atom, quoting only when required for unambiguous parsing. -/
def string (value : String) : SExpr :=
  .str (if canBeBare value then .bare else .quoted) value

end SExpr
end Sexp
