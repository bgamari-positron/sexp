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
- options: `(none)` or `(some VALUE...)`
- lists: `(list VALUE...)`
- booleans: `yes` or `no`

Construct decimals with `Decimal.ofScientific mantissa scale`. It canonicalizes trailing
fractional zeroes while retaining read-only `mantissa` and `scale` accessors; for example,
`Decimal.ofScientific 10 1` has mantissa `1` and scale `0`.

Current deriving support covers non-recursive structures, including parameterized structures. Existing `SExprCodec` instance parameters are reused (including codecs for higher-kinded fields); otherwise deriving adds type-correct codec constraints for type parameters when field codecs are not already available.

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

Each proof field needs a computable `Decidable` instance. Predicate parameters can
supply this through `[DecidablePred p]`. Arbitrary propositions need a custom
codec with a proof-producing validator; proofs are not serialized.

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
