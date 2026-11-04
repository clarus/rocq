#!/usr/bin/env python3
"""Mechanically audit fixed-limb wide algorithm and C-boundary structure."""

from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: pw024_static_audit.py RUNTIME.ml RUNTIME.c")

runtime = Path(sys.argv[1]).read_text()
c_runtime = Path(sys.argv[2]).read_text()


def module(name: str, next_name: str | None) -> str:
    start = runtime.index(f"module {name} = struct")
    end = runtime.index(f"\nmodule {next_name} = struct", start) \
        if next_name is not None else len(runtime)
    return runtime[start:end]


word128 = module("Word128", "Word256")
word256 = module("Word256", None)

for width, body in ((128, word128), (256, word256)):
    forbidden = re.findall(r"\b(?:Zarith|Big_int|Bigint|Z\.|Num\.)", body)
    if forbidden:
        raise SystemExit(f"Word{width}: bigint dependency: {forbidden[0]}")
    required = (
        "let shift = bit_length dividend - bit_length divisor",
        "let aligned = shift_left_raw divisor shift",
        "let rec loop index quotient remainder aligned",
        "loop (index - 1)",
        "loop shift",
    )
    for phrase in required:
        if phrase not in body:
            raise SystemExit(f"Word{width}: missing normalized-divider phrase: {phrase}")
    if body.count("loop (index - 1)") != 2:
        raise SystemExit(f"Word{width}: division loop must have exactly two descending arms")

mul_start = word256.index("let[@inline always] mul_raw")
mul_end = word256.index("\n  let neg x", mul_start)
multiplier = word256[mul_start:mul_end]
if "let rec" in multiplier or "Array" in multiplier:
    raise SystemExit("Word256 multiplier is not a fixed unrolled schedule")
if multiplier.count("add_at") != 16:
    raise SystemExit("Word256 multiplier must contain exactly 16 limb contributions")
if multiplier.count("U.mul") != 10:
    raise SystemExit("Word256 multiplier must contain exactly 10 low products")
if multiplier.count("mul_high_unsigned") != 6:
    raise SystemExit("Word256 multiplier must contain exactly 6 retained high products")

for width in (128, 256):
    arithmetic = re.search(
        rf"^CAMLprim[^\n]*rocq_primitive_word{width}_"
        r"(?:add|sub|mul|div|rem|shift|log)", c_runtime, re.MULTILINE)
    if arithmetic:
        raise SystemExit(f"Word{width}: arithmetic C entry point found")

print("word128_division_loop_upper_bound=128")
print("word256_division_loop_upper_bound=256")
print("word256_mul_low_products=10")
print("word256_mul_retained_high_products=6")
print("word256_mul_total_contributions=16")
print("wide_bigint_dependencies=0")
print("wide_c_arithmetic_entrypoints=0")
print("wide_static_audit=passed")
