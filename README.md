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
