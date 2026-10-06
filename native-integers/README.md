# Native integers in the OCaml Rocq fork

This fork adds distinct 8-, 16-, 32-, 64-, 128-, and 256-bit primitive
bit-pattern types to Rocq 9.3.0. Signed and unsigned operations use the same
type at each width. Arithmetic is implemented with standard OCaml scalar operations
and fixed two-/four-limb paths for the wide types.

The primitive declarations and literal scopes are built into Corelib:

```coq
From Corelib.Numbers.Primitive Require Import Word32.

Example wrapping_addition :
  Word32.add 4294967295%word32 1%word32 = 0%word32.
Proof. reflexivity. Qed.
```

The separate `Rocq.PrimitiveWords` library provides the full API, checked
arithmetic, conversions, extraction declarations, and specification proofs:

```coq
From Rocq.PrimitiveWords Require Import Word128 Conversions.

Example wrapping_wide_addition :
  Word128.add Word128.max_unsigned Word128.one = Word128.zero.
Proof. vm_compute. reflexivity. Qed.
```

Import `ScalarExtraction` when extracting these APIs to OCaml. The generated
program links to the fork's `rocq-runtime.kernel`; programs observing Z values also need Zarith.
The optional adapters in `compat` additionally require freshly rebuilt
`Gecko.Word` libraries.

## Build and check

Install Dune >= 3.21, ocamlfind and Zarith in your active standard OCaml switch.
From the repository root, run `python3 native-integers/build.py check`.
The helper uses the active opam switch; `NATIVE_INTEGER_SWITCH` and
`NATIVE_INTEGER_OPAMROOT` can override selection. It builds the pinned Stdlib
revision from a public checkout under `_build`, or `NATIVE_INTEGER_STDLIB_SOURCE`.
Optional compatibility adapters require `--gecko-word PATH`.

After a build, use the staged binaries and theories:

```sh
source _build/native-integers/env.sh
rocq c Example.v
```

The helper checks that the selected kernel is this checkout's kernel. Tests
and detailed logs are under `_build/native-integers/tests`; a successful
complete check writes `summary.json` there. Set `NATIVE_INTEGER_STOCK_ROCQ` to an unmodified Rocq 9.3 executable for
bidirectional compiled-object rejection checks.

## Semantics and trust

The API preserves wrapping construction, checked signed/unsigned bounds,
oversized shift sign fill, signed division toward zero, and dividend-signed
remainders. Public division by zero returns `None`. Checked division of the
signed minimum by −1 returns `None`, while its remainder is `Some zero`.
Raw primitive division operations are total; their zero-divisor behavior is
specified in `PrimitiveWordSpec`.

Exactly six primitive types, 120 raw operations, and six specification law
constants containing 156 clauses are trusted. Derived theorems and conversion
proofs compile through the kernel without admissions. Finite runtime tests
check the implementation against independent Python bigint oracles; they do
not prove the trusted laws. The higher-level API exposes 45 named cross-width
conversion directions.

Kernel reduction, `cbv`, VM evaluation, and generated OCaml native/custom
bytecode extraction are supported. Rocq's native evaluator remains disabled:
the accepted implementation's native Corelib build failed with stack overflow
under the pinned compiler. Generated native OCaml extraction is supported
independently. Ltac2 reflection of primitive words and Haskell/Scheme
extraction of these primitives remain unsupported.

Compiled objects use private format **90348**, rejecting stock format 90300
and the earlier fork formats 90346 and 90347. Rebuild all dependencies with this
fork. Opam distribution and installation into a dedicated switch are deferred.

Source origins and imported hashes are recorded in `source-manifest.json` and
`PROVENANCE.md`. Historical performance campaigns remain in the original
experiment; the integration's correctness checks do not repeat those campaigns.
