# Syntactic Closures
An exploration of a higienic macro system based on Bawden & Rees syntactic closures implemented in a subset of Scheme.

Differences from the Bawden & Rees paper:
- Uses an `a-list` format for the environments and separates macro expansion logic into a separate `expand` function.
- Uses a more modern convention for expander params - `exp`, `use-env`, `def-env`, that you might find in some Scheme implementations.
- It's not relying on Scheme `eval` for transformer interpretation.
