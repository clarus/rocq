# Array64 VM benchmarks

Paired measurements from actual `vm_compute` on the same modified Rocq binary.
Legacy slice/replacement/fill use loops over `PrimArray.get/set`; Array64 uses its checked range operations.
Elements are `int63` in both variants. Indices use each datatype's native index type.

7 measured rounds after one warmup; CPU 0; GC `s=256k,o=120,l=32M,d=1`; 256 MiB process stack. Case and variant order are shuffled with a fixed seed.

| Workload | Legacy median (s) | Array64 median (s) | Array64 / legacy |
|---|---:|---:|---:|
| point | 0.055 | 0.154 | 2.800 |
| history | 0.351 | 0.004 | 0.011 |
| slice | 1.449 | 0.009 | 0.006 |
| bulk | 0.258 | 0.011 | 0.043 |
| quote | 0.005 | 0.006 | 1.200 |

Workloads:

- Point: 262,144 sequential persistent updates and reads, wrapping over 65,536 elements; checksum 655,360.
- History: retain an original and a version after 512 updates, then alternate 16,384 reads of both; checksum 16,384.
- Slice: 4,096 iterations taking 1,024 elements, updating the first, and replacing a disjoint range in a 4,096-element array; checksum 32,768.
- Bulk: 256 eager constructions of 16,384 elements and eager fills of an 8,192-element range; checksum 1,536.
- Quote: normalize and save an 8,192-element literal, then recompile it through a checked read. Its timed command includes construction and quotation; it is reported separately from the four operational workloads.

The four operation cases return scalar checksums and prove their expected values, avoiding full-array quotation. Peak RSS and complete-process time include loading and checking, so they are recorded in JSON as process measurements, not as operation allocation counts. The standalone runtime benchmark measures allocation more directly. Rocq's timer has millisecond resolution; very small differences should not be interpreted as wins.

The fixed 128-slot leaf capacity is retained from the existing implementation. These measurements compare the public checked Array64 interface with the old unchecked/default-valued interface; their costs include that difference. They do not compare against Rust or claim that point updates improve over the legacy mutable-difference representation.

Reproduce after building and sourcing `_build/native-integers/env.sh`:

```sh
  bash -c 'source _build/native-integers/env.sh; python3 native-arrays/vm_bench.py'
```
