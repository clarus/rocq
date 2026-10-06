# Standard OCaml validation

Validated on 2026-11-03 with OCaml 5.5.2. All 138 integer checks passed.
Rocq runtime, Corelib, Ltac2, compatibility binaries, the command-line IDE
server, pinned Stdlib and the native integer/array proof libraries build.

Coverage includes 144,096 wide-integer oracle rows and 48,954 public API
properties per engine, native and bytecode extraction, 60 evaluator witnesses,
75 existing primitive/extraction regressions, GC and polymorphic boundaries,
canonical cross-engine serialization, malformed streams, and bidirectional
stock/fork object rejection. Additional tests cover every pair of 8-bit
operands and 16-bit boundary products. The trust audit reports six primitive
types, 120 operations, six law constants and zero admissions.

Reproduce with `NATIVE_INTEGER_STOCK_ROCQ=/path/to/stock/rocq python3
native-arrays/build.py check --benchmark` (on one shell line). The array helper
adds recursive proof checking, persistence tests and runtime/VM benchmarks.
See `native-arrays/RUNTIME.md` for the current runtime measurements.

Rocq's native evaluator remains disabled; native host tests refer to OCaml
extraction. Optional Gecko adapters were not run. Validation targets the
installed 64-bit Linux compiler, not every supported compiler/platform.
Logs and check summaries are under `_build/native-integers/tests` and
`_build/native-arrays/checks`.
