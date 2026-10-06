# Array64 runtime and experiments

The runtime uses an immutable AVL tree with dense leaves of at most 128 boxed
element slots. Every slot requested by `repeat` is allocated eagerly; there are
no uniform-region, repeat, or lazy-element nodes. Concatenation, slicing, and
replacement share existing subtrees. Partial boundary leaves are copied, and
adjacent boundary leaves are merged when they fit in one leaf.

Lengths and indices use native `Word64` values. Cached internal lengths use
unsigned `Int64` arithmetic; the conversion between these representations is
lossless. Bounds checks test `start <= length` followed by
`count <= length - start`. Concatenation checks available length before adding.
`None` means an invalid mathematical range or a length overflow. Allocation
failure propagates as a runtime resource failure, never as `None` or truncation.

With `c` chunks and leaf capacity `B`, reads take `O(log c)`, point updates take
`O(log c + B)`, and slicing and concatenation take logarithmic structural work
plus boundary copies. Repeat and fill allocate all written slots. History
branching never changes previously published nodes or reverses update chains.
Leaves are explicitly uniform `Obj.t` arrays, so boxed float elements cannot
silently change their runtime representation.

Term payloads use a separate immutable list of dense chunks with no cached
length or height metadata. Equality, hashing, and paired folds observe element
order, independently of chunk boundaries. Conversion-facing paired folds and
`equal_norefl` invoke their callback even for physically identical inputs.
Input/output runtime conversions copy chunks rather than expose mutable leaves.

Structural sharing makes it possible to build huge logical values by repeatedly
concatenating a value with itself, despite repeat being eager. Reads, updates,
and slices work up to length `2^64 - 1`. Quoting such a value enumerates its
logical contents into term chunks; it can therefore exhaust resources. Computing
a small observation such as its length or an indexed element does not quote the
entire value. This version does not compress serialized array literals.
Elementwise conversion between separately represented values also has linear
worst-case work in the logical length; tree identity is not used to bypass
comparisons under potentially different substitutions.

Saved term payloads remain chunked. Display currently reconstructs a flat Rocq
list using `PrimArray64.literal_of_list`; that additional nested-cons syntax can
hit printer or term-traversal stack-depth limits for large arrays, even when the
chunked value fits in memory. This is a display limitation, distinct from the
runtime tree's logarithmic depth and the chunked saved representation.

## Validation

`run_runtime.py` compiles both public interfaces, then compiles isolated copies
whose constructors are visible only to invariant tests. Tests cover 10,000
deterministically randomized operations against flat OCaml arrays, retained
historical versions, tree balance and cached metadata, float elements, copying
boundaries, traversal order, heterogeneous paired folds, different chunkings,
and arrays larger than the former 4,194,303-element limit. Tests also construct
shared values of length `2^63` and `2^64 - 1` and check unsigned boundary access,
overflow, persistent updates, and small tail slices without massive allocation.

Run after building the standard OCaml runtime:

```sh
source _build/native-integers/env.sh
python3 native-arrays/run_runtime.py --benchmark
```

The harness always selects the current staged kernel. Measurements are written
under `_build/native-arrays/runtime` and retained in `runtime-results.json`.
Leaf capacity remains 128.

## Standard OCaml measurements

Validated with OCaml 5.5.2 on 2026-11-03. The array suite passes 48 checks,
including recursive proof checking, native/bytecode extraction, print/reparse,
and 1,109,410 runtime assertions with 10,000 randomized persistent operations.
The runtime benchmark uses seven measured rounds after warm-up; all checksums
agree. Allocation uses `Gc.allocated_bytes`, avoiding sampled GC counters.
The VM benchmark also passes seven rounds across all five workloads.

| Runtime workload | Array64 (128 slots), ms | Legacy Parray, ms | Array64 allocated MiB |
| --- | ---: | ---: | ---: |
| concat_1024x64 | 0.011 | 24.502 | 0.032 |
| fill_8192x512 | 6.409 | 336.084 | 41.617 |
| history_alternation_1000 | 0.371 | 38.076 | 2.186 |
| read_262144 | 25.293 | 1.661 | 58.000 |
| repeat_65536 | 7.629 | 10.754 | 38.524 |
| slice_replace_8192x512 | 2.249 | 447.488 | 8.166 |
| update_32768 | 9.620 | 0.366 | 59.500 |

These compare different array APIs and persistence strategies within this build.
They do not establish performance parity with another compiler. The capacity
scoring experiment currently selects avl256; the port deliberately keeps the
existing 128-slot capacity. VM measurements and logs remain under `_build/native-arrays`.
