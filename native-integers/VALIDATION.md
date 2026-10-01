# Standard OCaml validation

Standalone runtime checks passed with OCaml 5.5.2 in native and bytecode modes:
144,096 independent wide-integer oracle rows per engine, all 65,536 pairs of
8-bit operands, 16-bit boundary products, GC and polymorphic comparison/hash,
width distinction, invalid access, and canonical cross-engine serialization.
Malformed custom identifiers and truncated streams are rejected.

Rocq runtime, Corelib, Ltac2, compatibility binaries and the command-line IDE
server build successfully. The Corelib primitive smoke test passes.

Full integration validation is run after the array commit. Reproduce with
`python3 native-integers/build.py check`. Rocq's native evaluator is disabled.
Detailed runtime artifacts are in `_build/port-runtime`.
