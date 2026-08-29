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

Current deriving support covers non-parameterized structures. Each field type needs an `SExprCodec` instance.

## Development

With direnv:

```sh
direnv allow
lake build
lake exe sexp
```

Without direnv:

```sh
nix develop -c lake build
nix develop -c lake exe sexp
```
