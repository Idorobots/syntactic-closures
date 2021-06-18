# Syntactic Closures
An exploration of a higienic macro system based on Bawden & Rees syntactic closures implemented in a subset of Scheme.

Differences from the Bawden & Rees paper:
- Uses an `a-list` format for the environments and separates macro expansion logic into a separate `macro-expand` function.
- Uses a more modern convention for expander params - `exp`, `use-env`, `def-env`, that you might find in some Scheme implementations.
- It's not relying on Scheme `eval` for transformer interpretation, and instead provides a simple meta-circular `evaluate`.
- Replaces `with-macro` from the original paper with `define-syntax`.
- Implements `syntax-rules` from scratch (using macro definitions borrowed from Chibi Scheme).

Caveats:
- No attempt is made to validate input code whatsoever. It's all happy path all the way.
- Both `macro-expand` and `evaluate` functions use continuation passing style to facilitate effects such as `define-syntax` and `define`, making them a bit hard to understand. The proper way would be to reorder the definitions and transform them into a `letrec` and/or `letrec-syntax` form.
- All variables are boxed in the interpreter. The proper way would be to run an assignment conversion first.
- Runtime functions that are ment to be available to macros need a `define-for-syntax` declaration instead of just `define`, they are still available during runtime as normal defines.
- This code currently only runs in Racket.
- `er-macro-transformer`-renamed variables are handled in a hacky fashion. Technically all the renamed identifiers have a unique environment attached to them, so a post-processing step that replaces these names with something unique could be implemented.
