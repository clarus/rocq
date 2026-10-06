# Dense native arrays for Rust verification

This fork provides `Corelib.Array.PrimArray64.array A`, a persistent sequence
with native unsigned 64-bit lengths and indices. It is distinct from the
existing `PrimArray.array`; existing APIs retain their behavior.

```coq
From Corelib.Array Require Import Array64.

Definition original := repeat 1024%word64 0%word64.
Definition changed := fill original 128%word64 256%word64 7%word64.

Example filled_element :
  match changed with
  | Some a => get a 200%word64
  | None => None
  end = Some 7%word64.
Proof. vm_compute. reflexivity. Qed.
```

## Operations

The eight primitive operations are `empty`, `repeat`, `length`, `get`, `set`,
`slice`, `replace`, and `concat`. Reads and updates return `option` results;
`empty`, `repeat`, and `length` have direct results. There is no default element.

`Array64` additionally provides `copy`, `fill`, `blit`, `copy_within`, `split_at`,
`swap`, `push`, `pop`, `map`, both folds, and checked list construction. Ranges
use a start and an element count. Replacement preserves destination length;
blits observe a source snapshot, so overlapping copies have defined behavior.
Invalid ranges and overflowing concatenations return `None`.

Some argument and result conventions differ from similarly named list functions:

| Call | Result and ordering |
| --- | --- |
| `copy a` | `array A`, sharing immutable storage |
| `map f a` | `array B`, with the same length as `a` |
| `fold_left f a acc` | `B`, applying `f : B -> A -> B` from left to right |
| `fold_right f a acc` | `B`, applying `f : A -> B -> B` from right to left |
| `split_at a index` | `option (array A * array A)`, prefix then suffix |
| `pop a` | `option (array A * A)`, remaining prefix then last element |
| `of_list values` | `option (array A)`, checking total length |

The printer's `PrimArray64.literal_of_list` helper reconstructs known-bounded
literals. Use the checked `Array64.of_list` constructor for application code.

Every element slot in `repeat` and `fill` is allocated eagerly. Runtime trees
share existing chunks when slicing or copying ranges. The logical length can
reach `2^64 - 1`; actual construction and quotation remain limited by available
resources. Resource exhaustion stops execution rather than returning a
machine-dependent logical result. Printing or saving a computed array enumerates
its contents and can be much more expensive than computing a small observation.
Saved term payloads stay chunked, but display currently reconstructs a flat Rocq
list. Its nested-cons syntax can reach printer or term-traversal stack-depth
limits even when the array itself fits in memory; runtime indexing does not
traverse that display representation.

This models sequence contents. Rust pointer width, layout, borrowing, element
cloning effects, and allocation success belong in the surrounding Rust model.

## Proofs and trust

`Array64Axioms` explicitly supplies 23 primitive specification laws, including
extensionality. The executable API does not import these laws. `Array64Properties`
proves checked-operation properties and supplies `get_bounded`/`set_bounded`
wrappers. `Rocq.NativeArrays` contains arithmetic-dependent slice/replacement,
traversal, and checked list-conversion proofs, using the existing native Word64
specification. `ListProperties` proves list-construction bounds and overflow,
indexed reads, and both array/list round trips.

The bounded wrappers take a proof of `Word64.ltu index (length a) = true`.
They return an element or updated array directly, while their accompanying
theorems connect these results to the checked primitive operations. Importing
these wrappers therefore opts into the explicit primitive specification.

The new trusted implementation includes the primitive type, eight reductions,
term typing and conversion, evaluator representations, and serialization handling.
The OCaml container is tested against a separate flat-array model; those tests
do not constitute a formal proof of its implementation. Derived proofs add no
admissions or additional axioms.

Kernel reduction, `cbv`, `cbn`, and `vm_compute` are supported. Import
`Corelib.Array.ExtrOCamlArray64` for OCaml extraction, linking the fork's
`rocq-runtime.kernel`. The existing disabled native evaluator remains disabled.
Arrays can occur positively in inductive datatypes; the guard checker does not
recognize recursive access through checked `get` as a structural subterm.
Objects use private format **90348**; dependencies must be rebuilt.

## Build and validation

Use the active standard OCaml switch:

```sh
python3 native-arrays/build.py check --benchmark
```

The helper defaults to one job and a 4 GiB per-process address-space limit.
Override with `--jobs` and `--memory-limit-mib`. Build dependencies and source
selection are documented in the native integer guide.

Benchmarks additionally require GNU `time` (`/usr/bin/time`) and `taskset`.
