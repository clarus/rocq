#!/usr/bin/env python3
"""Generate frozen wide inputs and an independent Python-bigint oracle."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys

if len(sys.argv) != 4:
    raise SystemExit("usage: pw024_vectors.py VECTORS ORACLE SUMMARY")

vectors_path, oracle_path, summary_path = map(Path, sys.argv[1:])
counts: dict[str, int] = {}
pair_categories: dict[tuple[int, str], int] = {}
leading_positions = {128: set(), 256: set()}
unsigned_invariants = 0
signed_invariants = 0


def bits(value: int, width: int) -> str:
    return f"{value & ((1 << width) - 1):0{width // 4}x}"


def signed(value: int, width: int) -> int:
    value &= (1 << width) - 1
    return value if value < (1 << (width - 1)) else value - (1 << width)


def trunc_div(left: int, right: int) -> int:
    quotient = abs(left) // abs(right)
    return -quotient if (left < 0) != (right < 0) else quotient


def record(vector, expected) -> None:
    kind = vector[0]
    counts[kind] = counts.get(kind, 0) + 1
    vectors.write("\t".join(map(str, vector)) + "\n")
    oracle.write("\t".join(map(str, (*vector, *expected))) + "\n")


def emit_unary(width: int, category: str, index: int, value: int) -> None:
    record(("unary", width, category, index, bits(value, width)),
           (f"neg={bits(-value, width)}", f"not={bits(~value, width)}"))


def emit_pair(width: int, category: str, index: int,
              left: int, right: int) -> None:
    global unsigned_invariants, signed_invariants
    pair_categories[(width, category)] = \
        pair_categories.get((width, category), 0) + 1
    modulus = 1 << width
    mask = modulus - 1
    left &= mask
    right &= mask
    total = left + right
    if right == 0:
        qu, ru = 0, left
    else:
        qu, ru = divmod(left, right)
        assert qu * right + ru == left and 0 <= ru < right
        unsigned_invariants += 1
    sl, sr = signed(left, width), signed(right, width)
    if sr == 0:
        qs, rs = 0, sl
    else:
        qs = trunc_div(sl, sr)
        rs = sl - qs * sr
        if not (sl == -(1 << (width - 1)) and sr == -1):
            assert qs * sr + rs == sl
            assert abs(rs) < abs(sr)
            assert rs == 0 or (rs < 0) == (sl < 0)
            signed_invariants += 1
    record(("pair", width, category, index, bits(left, width), bits(right, width)),
           (f"add={bits(total, width)}", f"sub={bits(left - right, width)}",
            f"mul={bits(left * right, width)}",
            f"carry={int(total >= modulus)}", f"borrow={int(left < right)}",
            f"divu={bits(qu, width)}", f"modu={bits(ru, width)}",
            f"divs={bits(qs, width)}", f"rems={bits(rs, width)}"))


def emit_shift(width: int, category: str, index: int,
               value: int, count: int, word_count: bool) -> None:
    mask = (1 << width) - 1
    value &= mask
    # A word-valued count is constructed modulo its own width before the
    # runtime applies the count cap.  Keep that boundary distinct from a host
    # integer count (notably 2^128 becomes Word128 zero, rather than 128).
    encoded_value = count & mask if word_count else count
    amount = min(encoded_value, width)
    left = 0 if amount >= width else value << amount
    logical = 0 if amount >= width else value >> amount
    arithmetic = (mask if signed(value, width) < 0 else 0) if amount >= width \
        else signed(value, width) >> amount
    kind = "word_shift" if word_count else "shift"
    encoded_count = bits(encoded_value, width) if word_count else str(count)
    record((kind, width, category, index, bits(value, width), encoded_count),
           (f"left={bits(left, width)}", f"logical={bits(logical, width)}",
            f"arithmetic={bits(arithmetic, width)}"))


def emit_cross(category: str, index: int, left: int, right: int) -> None:
    # Inputs are at most 64 bits, so sum and product fit exactly in Word128 and
    # Word256. Subtraction is compared only when it does not wrap at either width.
    assert left.bit_length() <= 64 and right.bit_length() <= 64
    sub = "1" if left >= right else "na"
    record(("cross", category, index, bits(left, 128), bits(right, 128)),
           ("add=1", f"sub={sub}", "mul=1", "and=1", "or=1", "xor=1",
            "divu=1", "modu=1", "cmpu=1"))


with vectors_path.open("w", encoding="ascii") as vectors, \
     oracle_path.open("w", encoding="ascii") as oracle:
    for width in (128, 256):
        mask = (1 << width) - 1
        sign = 1 << (width - 1)
        limbs = width // 64

        unary_values = {0, 1, mask, sign, sign - 1, sign + 1}
        for limb in range(limbs):
            boundary = 1 << (64 * limb)
            unary_values.update((boundary, boundary - 1,
                                 (boundary + 1) & mask))
        for index, value in enumerate(sorted(unary_values)):
            emit_unary(width, "ripple", index, value)

        index = 0
        for left in range(256):
            for right in range(256):
                emit_pair(width, "exhaustive8", index, left, right)
                index += 1

        ripple_pairs = []
        for limb in range(1, limbs + 1):
            boundary = 1 << (64 * limb)
            ripple_pairs.extend(((boundary - 1, 1), (0, boundary - 1),
                                 (boundary & mask, 1),
                                 ((boundary - 1) & mask, boundary - 1)))
        for index, (left, right) in enumerate(ripple_pairs):
            emit_pair(width, "ripple", index, left, right)

        digits = (1, 0xFFFFFFFF, 1 << 63, (1 << 64) - 1)
        index = 0
        for left_limb in range(limbs):
            for right_limb in range(limbs - left_limb):
                for left_digit in digits:
                    for right_digit in digits:
                        emit_pair(width, "mulcell", index,
                                  left_digit << (64 * left_limb),
                                  right_digit << (64 * right_limb))
                        index += 1

        index = 0
        for leading in range(width):
            base = 1 << leading
            divisors = (base, base | ((base - 1) >> 1)) if leading else (1,)
            for divisor in divisors:
                leading_positions[width].add(divisor.bit_length() - 1)
                dividends = {divisor - 1, divisor, divisor + 1, mask}
                for quotient in (1, 3, (1 << min(8, width - leading)) - 1):
                    multiple = quotient * divisor
                    if multiple <= mask:
                        dividends.add(multiple)
                        if multiple > 0:
                            dividends.add(multiple - 1)
                        if multiple < mask:
                            dividends.add(multiple + 1)
                for dividend in sorted(dividends):
                    emit_pair(width, "leading", index, dividend, divisor)
                    index += 1

        signed_values = (0, 1, 2, mask, mask - 1, sign, sign + 1,
                         sign - 1, 1 << (width - 2),
                         (-1 << (width - 2)) & mask)
        index = 0
        for left in signed_values:
            for right in signed_values:
                emit_pair(width, "signed", index, left, right)
                index += 1

        shift_values = (0, 1, mask, sign, sign - 1, sign + 1,
                        int("a5" * (width // 8), 16))
        counts_for_shift = {0, 1, width, width + 1, width + 63}
        for lane in range(0, width + 1, 64):
            counts_for_shift.update(c for c in (lane - 1, lane, lane + 1) if c >= 0)
        counts_for_shift = sorted(counts_for_shift)
        index = 0
        for value in shift_values:
            for count in counts_for_shift:
                emit_shift(width, "lanes", index, value, count, False)
                index += 1
        word_counts = counts_for_shift + [1 << 64, 1 << 128, mask]
        index = 0
        for value in shift_values:
            for count in word_counts:
                emit_shift(width, "lanes", index, value, count, True)
                index += 1

    index = 0
    for left in range(64):
        for right in range(64):
            emit_cross("exhaustive6", index, left, right)
            index += 1
    state = 0x13198A2E03707344
    for index in range(512):
        state = (state * 0x5851F42D4C957F2D + 0x14057B7EF767814F) \
            & ((1 << 64) - 1)
        left = state
        state = (state * 0x5851F42D4C957F2D + 0x14057B7EF767814F) \
            & ((1 << 64) - 1)
        emit_cross("lcg64", index, left, state)

vector_sha = hashlib.sha256(vectors_path.read_bytes()).hexdigest()
oracle_sha = hashlib.sha256(oracle_path.read_bytes()).hexdigest()
total = sum(counts.values())
for width in (128, 256):
    assert leading_positions[width] == set(range(width))
summary_path.write_text(
    f"total_rows={total}\n"
    + "".join(f"{kind}_rows={counts[kind]}\n" for kind in sorted(counts))
    + f"unsigned_invariants={unsigned_invariants}\n"
    + f"signed_invariants={signed_invariants}\n"
    + "".join(
        f"word{width}_{category}_pair_rows={pair_categories[(width, category)]}\n"
        for width in (128, 256)
        for category in ("exhaustive8", "ripple", "mulcell", "leading", "signed"))
    + "word128_divisor_leading_positions=128\n"
    + "word256_divisor_leading_positions=256\n"
    + f"vectors_sha256={vector_sha}\n"
    + f"oracle_sha256={oracle_sha}\n"
    + "generator=Python bigint direct arithmetic/divmod; no runtime control-flow translation\n",
    encoding="ascii")
