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

inductive Shape where
  | plain
  | mla (heads chunks : Nat) (fits : heads * chunks ≤ 4096) (label : String)
  | bounded {n : Nat} (fits : n < 10)
  | certified (valid : True)
  deriving SExprCodec

inductive Choice (α : Type u) : Type u where
  | empty
  | value (value : α)
  deriving SExprCodec

inductive CheckedChoice (α : Type u) (p : α → Prop) [SExprCodec α] [DecidablePred p] : Type u where
  | value (value : α) (valid : p value)
  deriving SExprCodec

inductive EmptyChoice where
  deriving SExprCodec

inductive ExprTy where
  | unsigned (bits : Nat)
  | flag

structure FamilyCommand (E : ExprTy → Type u) where
  count : E (.unsigned 13)
  enabled : E .flag
  deriving SExprCodec

inductive FamilyAction (E : ExprTy → Type u) : Type u where
  | idle
  | run (count : E (.unsigned 13))
  deriving SExprCodec

structure ExplicitFamily (E : ExprTy → Type u) [∀ t, SExprCodec (E t)] where
  count : E (.unsigned 13)
  deriving SExprCodec

structure DependentFamily (E : (n : Nat) → Fin n → Type u) where
  value : E 2 ⟨0, by decide⟩
  deriving SExprCodec

example (E : ExprTy → Type u) [∀ t, SExprCodec (E t)] :
    SExprCodec (FamilyCommand E) := inferInstance
example (E : ExprTy → Type u) [∀ t, SExprCodec (E t)] :
    SExprCodec (FamilyAction E) := inferInstance
example (E : ExprTy → Type u) [∀ t, SExprCodec (E t)] :
    SExprCodec (ExplicitFamily E) := inferInstance
example (E : (n : Nat) → Fin n → Type u) [∀ n i, SExprCodec (E n i)] :
    SExprCodec (DependentFamily E) := inferInstance

private def checkedEnd (base count : Nat) : Except String Nat :=
  if base + count ≤ 256 then .ok (base + count) else .error "out of bounds"

private def WritebackFits (destination : Option Nat) (count : Nat) : Prop :=
  ∀ base ∈ destination, ∃ endOffset, checkedEnd base count = .ok endOffset

private instance (destination : Option Nat) (count : Nat) : Decidable (WritebackFits destination count) := by
  letI (base : Nat) : Decidable (∃ endOffset, checkedEnd base count = .ok endOffset) :=
    match checkedEnd base count with
    | .ok endOffset => isTrue ⟨endOffset, rfl⟩
    | .error error => isFalse (by simp)
  unfold WritebackFits
  infer_instance

private def SingleReads (a b c : Option Nat) : Prop :=
  ∀ step, step ∈ a ∨ step ∈ b ∨ step ∈ c → step = 1

private instance (a b c : Option Nat) : Decidable (SingleReads a b c) :=
  decidable_of_iff ((∀ step ∈ a, step = 1) ∧ (∀ step ∈ b, step = 1) ∧ (∀ step ∈ c, step = 1)) (by
    simp only [SingleReads, or_imp, forall_and])

private structure CheckedTransfer (E : ExprTy → Type) where
  destination : Option Nat
  count : Nat
  inBounds : WritebackFits destination count
  a : Option Nat
  b : Option Nat
  c : Option Nat
  singleReads : SingleReads a b c
  trigger : E (.unsigned 13)
  deriving SExprCodec

inductive IndexedChoice : Nat → Type where
  | zero : IndexedChoice 0
  deriving SExprCodec

inductive IndexedValue (ν : ExprTy → Type) : ExprTy → Type where
  | unsigned {width : Nat} (value : Nat) (fits : value < width) : IndexedValue ν (.unsigned width)
  | flag (value : Bool) : IndexedValue ν .flag
  | var {t : ExprTy} (name : ν t) : IndexedValue ν t
  deriving SExprCodec

private def IndexedNames : ExprTy → Type
  | .unsigned _ => String
  | .flag => Bool

private instance (t : ExprTy) : SExprCodec (IndexedNames t) :=
  match t with
  | .unsigned _ => inferInstanceAs (SExprCodec String)
  | .flag => inferInstanceAs (SExprCodec Bool)

inductive IndexedPair : Nat × Nat → Type where
  | value (a b : Nat) (payload : String) : IndexedPair (a, b)
  deriving SExprCodec

/-- error: SExprCodec deriving requires distinct constructor fields in index patterns -/
#guard_msgs in
inductive RepeatedIndex : Nat × Nat → Type where
  | value (n : Nat) : RepeatedIndex (n, n)
  deriving SExprCodec

/-- error: SExprCodec deriving does not yet support multiple indices -/
#guard_msgs in
inductive MultiIndexed : Nat → Nat → Type where
  | zero : MultiIndexed 0 0
  deriving SExprCodec

/-- error: SExprCodec deriving requires constructor-shaped indices -/
#guard_msgs in
inductive ComputedIndex : Nat → Type where
  | value (a b : Nat) : ComputedIndex (a + b)
  deriving SExprCodec

/-- error: SExprCodec deriving does not yet support recursive types -/
#guard_msgs in
inductive RecursiveChoice where
  | next (value : RecursiveChoice)
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

private def validateEven (n : Nat) : DecodeM Even :=
  if h : n % 2 = 0 then .ok ⟨n, h⟩
  else .error { context := ["Even", "n"], message := "expected an even natural number" }

example : Codec.TermRoundTrips (TermCodec.emap validateEven Even.n Codec.natural) := by
  apply Codec.emap_termRoundTrips (by intro value; rfl)
  intro value
  simp [validateEven, value.isEven]

private def checkEmap : IO Unit := do
  let codec := TermCodec.emap validateEven Even.n Codec.natural
  let value : Even := ⟨4, by decide⟩
  assert! codec.encodeTerm value == Codec.natural.encodeTerm 4
  assert! (match codec.decodeTerm (codec.encodeTerm value) with
    | .ok decoded => decoded.n == 4
    | .error _ => false : Bool)
  assert! (match codec.decodeTerm (Codec.natural.encodeTerm 3) with
    | .error error => error == { context := ["Even", "n"], message := "expected an even natural number" }
    | .ok _ => false : Bool)
  let malformed := SExpr.string "not a number"
  assert! (match codec.decodeTerm malformed, Codec.natural.decodeTerm malformed with
    | .error actual, .error expected => actual == expected
    | _, _ => false : Bool)

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

private def checkInductives : IO Unit := do
  let shape := Shape.mla 4 8 (by decide) "ok"
  assert! SExprCodec.render shape == "(mla 4 8 ok)"
  let decoded : Shape ← IO.ofExcept (SExprCodec.parse (SExprCodec.render shape))
  assert! SExprCodec.render decoded == SExprCodec.render shape
  assert! SExprCodec.render Shape.plain == "(plain)"
  assert! SExprCodec.render (← IO.ofExcept (SExprCodec.parse "(plain)") : Shape) == "(plain)"
  assert! SExprCodec.render (Shape.bounded (n := 4) (by decide)) == "(bounded 4)"
  assert! SExprCodec.render (← IO.ofExcept (SExprCodec.parse "(bounded 4)") : Shape) == "(bounded 4)"
  assert! SExprCodec.render (← IO.ofExcept (SExprCodec.parse "(certified)") : Shape) == "(certified)"
  assert! (SExprCodec.parse "(bounded 10)" : Except String Shape).toOption.isNone
  for invalid in ["(unknown)", "plain", "()", "(plain extra)", "(mla 4 8)",
      "(mla nope 8 ok)", "(mla 4 8 ok extra)", "(mla 4096 2 ok)"] do
    assert! (SExprCodec.parse invalid : Except String Shape).toOption.isNone
  assert! (match SExprCodec.decode (.list [.string "mla", Codec.natural.encodeTerm 4096,
      Codec.natural.encodeTerm 2, .string "ok"]) with
    | .error error => error.context == ["mla"] && error.message == "proof field fits failed"
    | .ok (_ : Shape) => false : Bool)
  let chosen := Choice.value ([Higher.value] : List Higher)
  assert! (match (SExprCodec.parse (SExprCodec.render chosen) : Except String (Choice (List Higher))) with
    | .ok (.value values) => values == [.value]
    | _ => false : Bool)
  assert! SExprCodec.render (Choice.empty : Choice Nat) == "(empty)"
  let checked : CheckedChoice Nat (fun n => n % 2 = 0) := .value 4 (by decide)
  let decoded : CheckedChoice Nat (fun n => n % 2 = 0) ←
    IO.ofExcept (SExprCodec.parse (SExprCodec.render checked))
  assert! SExprCodec.render decoded == "(value 4)"
  assert! (SExprCodec.parse "(value 3)" : Except String (CheckedChoice Nat (fun n => n % 2 = 0))).toOption.isNone
  assert! (SExprCodec.parse "(anything)" : Except String EmptyChoice).toOption.isNone

private def checkFamilies : IO Unit := do
  let command : FamilyCommand (fun _ => Nat) := ⟨13, 1⟩
  assert! SExprCodec.render command == "(FamilyCommand 13 1)"
  let decoded : FamilyCommand (fun _ => Nat) ← IO.ofExcept (SExprCodec.parse (SExprCodec.render command))
  assert! decoded.count == 13 && decoded.enabled == 1
  let action : FamilyAction (fun _ => Nat) := .run 42
  let decoded : FamilyAction (fun _ => Nat) ← IO.ofExcept (SExprCodec.parse (SExprCodec.render action))
  assert! SExprCodec.render decoded == "(run 42)"
  let explicit : ExplicitFamily (fun _ => Nat) := ⟨7⟩
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render explicit)) : ExplicitFamily (fun _ => Nat)).count == 7
  let dependent : DependentFamily (fun _ _ => Nat) := ⟨9⟩
  assert! (← IO.ofExcept (SExprCodec.parse (SExprCodec.render dependent)) : DependentFamily (fun _ _ => Nat)).value == 9

private def checkQuantifiedProofs : IO Unit := do
  let transfer : CheckedTransfer (fun _ => Nat) := {
    destination := some 250, count := 6, inBounds := by decide
    a := some 1, b := none, c := some 1, singleReads := by decide
    trigger := 7
  }
  let rendered := SExprCodec.render transfer
  assert! rendered == "(CheckedTransfer (some 250) 6 (some 1) (none) (some 1) 7)"
  let decoded : CheckedTransfer (fun _ => Nat) ← IO.ofExcept (SExprCodec.parse rendered)
  assert! SExprCodec.render decoded == rendered
  let absent := "(CheckedTransfer (none) 1000 (none) (none) (none) 9)"
  let decoded : CheckedTransfer (fun _ => Nat) ← IO.ofExcept (SExprCodec.parse absent)
  assert! decoded.destination.isNone && decoded.trigger == 9
  for (input, field) in [
      ("(CheckedTransfer (some 250) 7 (none) (none) (none) 7)", "inBounds"),
      ("(CheckedTransfer (none) 0 (some 2) (none) (none) 7)", "singleReads"),
      ("(CheckedTransfer (none) 0 (none) (some 2) (none) 7)", "singleReads"),
      ("(CheckedTransfer (none) 0 (none) (none) (some 2) 7)", "singleReads")] do
    let term ← IO.ofExcept (SExpr.parse input)
    assert! (match (SExprCodec.decode term : DecodeM (CheckedTransfer (fun _ => Nat))) with
      | .error error => error.context == ["CheckedTransfer"] && error.message == s!"proof field {field} failed"
      | .ok _ => false : Bool)

private def checkIndexed : IO Unit := do
  let value : IndexedValue (fun _ => String) (.unsigned 8) := .unsigned 7 (by decide)
  assert! SExprCodec.render value == "(unsigned 7)"
  let decoded : IndexedValue (fun _ => String) (.unsigned 8) ← IO.ofExcept (SExprCodec.parse "(unsigned 7)")
  assert! SExprCodec.render decoded == "(unsigned 7)"
  assert! (SExprCodec.parse "(unsigned 7)" : Except String (IndexedValue (fun _ => String) (.unsigned 4))).toOption.isNone
  assert! (SExprCodec.parse "(unsigned 7)" : Except String (IndexedValue (fun _ => String) .flag)).toOption.isNone
  assert! (SExprCodec.parse "(flag yes)" : Except String (IndexedValue (fun _ => String) (.unsigned 8))).toOption.isNone
  assert! (SExprCodec.parse "(unsigned 8 7)" : Except String (IndexedValue (fun _ => String) (.unsigned 8))).toOption.isNone
  let flag : IndexedValue (fun _ => String) .flag ← IO.ofExcept (SExprCodec.parse "(flag yes)")
  assert! SExprCodec.render flag == "(flag yes)"
  let name : IndexedValue (fun _ => String) (.unsigned 8) ← IO.ofExcept (SExprCodec.parse "(var counter)")
  assert! SExprCodec.render name == "(var counter)"
  let typedName : IndexedValue IndexedNames .flag ← IO.ofExcept (SExprCodec.parse "(var yes)")
  assert! SExprCodec.render typedName == "(var yes)"
  assert! (SExprCodec.parse "(var counter)" : Except String (IndexedValue IndexedNames .flag)).toOption.isNone
  let typedName : IndexedValue IndexedNames (.unsigned 8) ← IO.ofExcept (SExprCodec.parse "(var counter)")
  assert! SExprCodec.render typedName == "(var counter)"
  let pair : IndexedPair (2, 3) ← IO.ofExcept (SExprCodec.parse "(value payload)")
  assert! SExprCodec.render pair == "(value payload)"
  let decodedZero : IndexedChoice 0 ← IO.ofExcept (SExprCodec.parse "(zero)")
  assert! SExprCodec.render decodedZero == "(zero)"
  assert! (SExprCodec.parse "(zero)" : Except String (IndexedChoice 1)).toOption.isNone

def main : IO Unit := do
  checkIndexed
  checkQuantifiedProofs
  checkFamilies
  checkInductives
  checkEmap
  checkProofs
  checkDecimal
  checkDeriving
  checkStringSafety
  checkTagRoundTrip "hello world"
  checkTagRoundTrip "123"
  checkLargeList
