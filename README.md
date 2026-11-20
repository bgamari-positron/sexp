# sexp

Small Lean 4 S-expression parser and compositional bidirectional codec library.

```lean
import Sexp

open Sexp

structure Item where
  name : String
  enabled : Bool
  aliases : List String
  deriving Repr, BEq, SExprCodec

#eval SExprCodec.render ({
  name := "hello world"
  enabled := true
  aliases := ["short", "h"]
} : Item)
-- (Item "hello world" yes (list short h))
```

`Codec α` consumes and emits S-expression streams. Core composition:

```lean
Codec.product : Codec α → Codec β → Codec (α × β)
Codec.imap    : (α → β) → (β → α) → Codec α → Codec β
Codec.tagged  : String → Codec α → Codec α
```

Derived grammar is positional and canonical:

- structures: `(TypeName FIELD...)`
- other inductives: `(constructorName FIELD...)`, including `(constructorName)` for nullary constructors
- options: `(none)` or `(some VALUE...)`
- lists: `(list VALUE...)`
- booleans: `yes` or `no`

Construct decimals with `Decimal.ofScientific mantissa scale`. It canonicalizes trailing
fractional zeroes while retaining read-only `mantissa` and `scale` accessors; for example,
`Decimal.ofScientific 10 1` has mantissa `1` and scale `0`.

Current deriving support covers non-recursive structures and non-recursive, non-indexed inductives, including parameterized types. Existing `SExprCodec` instance parameters are reused (including codecs for higher-kinded fields); otherwise deriving adds type-correct codec constraints for type parameters when field codecs are not already available.

## Codec families

Deriving can infer codec constraints for type families without adding instance
parameters to the original type:

```lean
structure Command (E : Nat → Type) where
  count : E 13
  address : E 32
  deriving SExprCodec

example (E : Nat → Type) [∀ bits, SExprCodec (E bits)] :
    SExprCodec (Command E) := inferInstance
```

The generated instance requires `[∀ bits, SExprCodec (E bits)]`. Families with
multiple dependent arguments also work. Existing quantified instance parameters
are preserved. If existing instances already provide all field codecs, deriving
adds no further constraints. Otherwise, inferred family constraints cover every
index, not just the indices used by the fields.

This supports fields of indexed types; it does not add deriving for indexed
inductives themselves or construct codecs for the expression family.

## Proof-bearing values

Subtype codecs reuse the representation of the underlying value. Decoding checks
its predicate with `[DecidablePred p]` and rejects values that fail the check.
Use `TermCodec.subtype p codec` directly, or the `SExprCodec {x : α // p x}` instance.

Deriving omits proof fields from the representation and checks their propositions
after decoding the preceding fields:

```lean
structure Even where
  n : Nat
  isEven : n % 2 = 0
  deriving SExprCodec

-- Encodes as (Even 4); decoding (Even 3) fails.
#eval SExprCodec.render (⟨4, by decide⟩ : Even)
```

Constructor proof fields work the same way:

```lean
inductive Shape where
  | plain
  | mla (heads chunks : Nat) (fits : heads * chunks ≤ 4096)
  deriving SExprCodec

-- Encodes as (mla 4 8); decoding (mla 4096 2) fails.
#eval SExprCodec.render (Shape.mla 4 8 (by decide))
```

Constructor tags use the final component of the constructor name. Decoding rejects
unknown tags, missing fields, extra fields, and failed proof checks.

Each proof field needs a computable `Decidable` instance. Predicate parameters can
supply this through `[DecidablePred p]`. Arbitrary propositions need a custom
codec with a proof-producing validator; proofs are not serialized.

For quantified invariants, define a named predicate and a computable `Decidable`
instance. For example, a writeback-bounds check can inspect an `Option` destination,
run a bounds checker, and construct an existential witness from its successful
result. A universal constraint over three optional inputs can instead decide
three bounded checks. `Main.lean` tests both patterns together with a codec family.
Default proof-field values are not validators; deriving checks the proposition
against the decoded data.

## Development

With direnv:

```sh
direnv allow
lake build
lake test
```

Without direnv:

```sh
nix develop -c lake build
nix develop -c lake test
```
