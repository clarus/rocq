#!/usr/bin/env python3
"""Independent PW031 vectors, mathematical oracle, and coverage audit.

This file intentionally imports no earlier primitive-word oracle.  Inputs use a
SHA-256 counter stream so their provenance is independent of the LCG campaigns.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

WIDTHS = (8, 16, 32, 64, 128, 256)
SEED = b"Gecko/PW031/independent-differential/v1"


def u(w: int, x: int) -> int:
    return x & ((1 << w) - 1)


def s(w: int, x: int) -> int:
    x = u(w, x)
    return x - (1 << w) if x & (1 << (w - 1)) else x


def trunc_div(a: int, b: int) -> int:
    assert b
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


def raw_shift(w: int, kind: str, x: int, count: int) -> int:
    x, count = u(w, x), u(w, count)
    if count >= w:
        return ((1 << w) - 1 if kind == "asr" and s(w, x) < 0 else 0)
    if kind == "lsl":
        return u(w, x << count)
    if kind == "lsr":
        return x >> count
    return u(w, s(w, x) >> count)


def raw_row(w: int, x0: int, y0: int) -> list[int]:
    x, y, m = u(w, x0), u(w, y0), (1 << w) - 1
    sx, sy = s(w, x), s(w, y)
    if y == 0:
        du, mu = 0, x
        ds, rs = 0, x
    else:
        du, mu = divmod(x, y)
        ds = trunc_div(sx, sy)
        rs = sx - ds * sy
    return [
        u(w, -x), u(w, x + y), u(w, x - y), u(w, x * y),
        x & y, x | y, x ^ y, x ^ m,
        int(x == y), int(x < y), int(x <= y), int(sx < sy), int(sx <= sy),
        raw_shift(w, "lsl", x, y), raw_shift(w, "lsr", x, y),
        raw_shift(w, "asr", x, y), du, mu, u(w, ds), u(w, rs),
    ]


def option(value: int | None, w: int) -> list[int]:
    return [0, 0] if value is None else [1, u(w, value)]


def public_row(w: int, x0: int, y0: int, amount: int) -> list[int]:
    x, y, m = u(w, x0), u(w, y0), (1 << w) - 1
    sx, sy = s(w, x), s(w, y)
    signed_min, signed_max = -(1 << (w - 1)), (1 << (w - 1)) - 1
    add = u(w, x + y)
    sub = u(w, x - y)
    def checked(z: int) -> int | None:
        return z if signed_min <= z <= signed_max else None
    def nat_shift(kind: str) -> int:
        if amount >= w:
            return m if kind == "asr" and sx < 0 else 0
        return raw_shift(w, kind, x, amount)
    count = s(w, y)
    magnitude = -count if count < 0 else count
    left_signed = raw_shift(w, "asr" if count < 0 else "lsl", x, magnitude)
    right_signed = raw_shift(w, "lsl" if count < 0 else "asr", x, magnitude)
    result = [
        u(w, -x), add, sub, u(w, x * y), x & y, x | y, x ^ y, x ^ m,
        int(x == y), int(x < y), int(x <= y), int(sx < sy), int(sx <= sy),
        int(x + y > m), add, int(x < y), sub,
    ]
    result += option(None if sx == signed_min else -sx, w)
    result += option(checked(sx + sy), w)
    result += option(checked(sx - sy), w)
    result += option(checked(sx * sy), w)
    result += option(None if y == 0 else x // y, w)
    result += option(None if y == 0 else x % y, w)
    result += ([0, 0, 0] if y == 0 else [1, x // y, x % y])
    result += option(None if y == 0 or (sx == signed_min and sy == -1)
                     else trunc_div(sx, sy), w)
    result += option(None if y == 0 else sx - trunc_div(sx, sy) * sy, w)
    result += [nat_shift("lsl"), nat_shift("lsr"), nat_shift("asr"),
               left_signed, right_signed]
    assert len(result) == 41
    return result


def meta_row(w: int, x0: int, y0: int, amount: int) -> list[int]:
    x, y = u(w, x0), u(w, y0)
    left = raw_shift(w, "lsl", x, amount)
    right = raw_shift(w, "lsr", x, amount)
    return [x, x, x, 0,
            raw_shift(w, "lsr", left, amount),
            raw_shift(w, "lsl", right, amount),
            u(w, x * (y + 1)),
            int((x < y) == (not (y <= x)))]


def conversion_row(w: int, z: int, n: int, natural: int) -> list[int]:
    m, lo, hi = 1 << w, -(1 << (w - 1)), (1 << (w - 1)) - 1
    wz, wn, wt = z % m, n % m, natural % m
    return [wz, s(w, wz), wz] + option(wz if 0 <= z < m else None, w) + \
        option(wz if lo <= z <= hi else None, w) + [wn] + \
        option(wn if 0 <= n < m else None, w) + [wt, wt] + \
        option(wt if 0 <= natural < m else None, w)


def cross_row(src: int, dst: int, z: int) -> list[int]:
    x = u(src, z)
    signed_x = s(src, x)
    dst_x = u(dst, z)
    narrowed = u(src, dst_x)
    return [x, u(dst, signed_x), x, x,
            u(dst, narrowed), u(dst, s(src, narrowed))]


def counter_value(w: int, index: int) -> int:
    digest = hashlib.sha256(SEED + w.to_bytes(2, "big") + index.to_bytes(8, "big")).digest()
    return int.from_bytes(digest, "big") & ((1 << w) - 1)


def edges(w: int) -> list[int]:
    m, h = (1 << w) - 1, 1 << (w - 1)
    values = [0, 1, 2, 3, h - 2, h - 1, h, h + 1, m - 1, m]
    for lane in range(0, w, 64):
        values += [1 << lane, u(w, (1 << lane) - 1), u(w, 0xA5A5A5A5A5A5A5A5 << lane)]
    return list(dict.fromkeys(u(w, x) for x in values))


def normalization_cases(w: int) -> list[tuple[int, int]]:
    """One independently selected, nontrivial division per normalization shift."""
    m = (1 << w) - 1
    rows = []
    for shift in range(w):
        lead = w - 1 - shift
        # Dense, non-power-of-two divisor with this exact leading position.
        d = (1 << lead) | ((1 << lead) - 1 if lead else 0)
        # Search a tiny fixed dividend family for positive q and nonzero r.
        candidates = [m, m - 1, m - 3, u(w, d * ((1 << shift) | 1) + 1)]
        chosen = next((n for n in candidates if n >= d and n // d > 0 and n % d != 0), None)
        if chosen is None:
            # d=1 necessarily has zero remainder; preserve entry and report it.
            chosen = m
        assert chosen >= d and chosen // d > 0
        assert chosen.bit_length() - d.bit_length() == shift
        rows.append((chosen, d))
    assert {n.bit_length() - d.bit_length() for n, d in rows} == set(range(w))
    return rows


def pair_vectors(w: int) -> list[tuple[int, int, int, str]]:
    es = edges(w)
    rows: list[tuple[int, int, int, str]] = []
    # Cross key boundary values without copying earlier Cartesian corpora.
    for i, x in enumerate(es):
        y = es[(i * 7 + 3) % len(es)]
        for amount in (0, 1, w - 1, w, w + 1):
            rows.append((x, y, amount, "edge"))
    for i in range(48):
        x, y = counter_value(w, 2 * i), counter_value(w, 2 * i + 1)
        amount = (counter_value(16, 10000 + w + i) % (w + 3))
        rows.append((x, y, amount, "sha256"))
    # Explicit signed-count directions and minimum-count magnitude.
    for x in (1, 1 << (w - 1), (1 << w) - 1):
        for y in (1, (1 << w) - 1, 1 << (w - 1)):
            rows.append((x, y, 1, "signed-count"))
    if w in (128, 256):
        rows += [(n, d, (n ^ d) % (w + 3), "normalized")
                 for n, d in normalization_cases(w)]
    return list(dict.fromkeys(rows))


def properties(w: int, x: int, y: int, raw: list[int], public: list[int],
               meta: list[int] | None = None) -> int:
    m = (1 << w) - 1
    checks = [
        raw[1] == u(w, x + y), raw[2] == u(w, x - y),
        raw[4] & raw[5] == raw[4], raw[6] == (u(w, x) ^ u(w, y)),
        raw[8] == int(u(w, x) == u(w, y)),
        raw[9] + int(u(w, x) >= u(w, y)) == 1,
        public[13] == int(u(w, x) + u(w, y) > m),
        public[15] == int(u(w, x) < u(w, y)),
        u(w, raw[1] - y) == u(w, x),
        u(w, raw[2] + y) == u(w, x),
        raw[4] | raw[6] == raw[5],
        u(w, ~raw[4]) == (u(w, ~x) | u(w, ~y)),
        raw[10] == int(raw[9] or raw[8]),
        raw[12] == int(raw[11] or raw[8]),
        public[14] == raw[1] and public[16] == raw[2],
    ]
    if u(w, y):
        q, r = raw[16], raw[17]
        checks += [q * u(w, y) + r == u(w, x), 0 <= r < u(w, y)]
        sq, sr = s(w, raw[18]), s(w, raw[19])
        # The raw min/-1 quotient is the target's one wrapping overflow case.
        if not (s(w, x) == -(1 << (w - 1)) and s(w, y) == -1):
            checks += [sq * s(w, y) + sr == s(w, x)]
        checks += [abs(sr) < abs(s(w, y)),
                   sr == 0 or (sr < 0) == (s(w, x) < 0)]
        checks += [public[25] == 1, public[27] == 1, public[29] == 1,
                   public[30] * u(w, y) + public[31] == u(w, x),
                   0 <= public[31] < u(w, y)]
    else:
        checks += [public[25] == 0, public[27] == 0, public[29] == 0,
                   public[32] == 0, public[34] == 0]
    signed_min, signed_max = -(1 << (w - 1)), (1 << (w - 1)) - 1
    checked_cases = [
        (17, None if s(w, x) == signed_min else -s(w, x)),
        (19, s(w, x) + s(w, y)), (21, s(w, x) - s(w, y)),
        (23, s(w, x) * s(w, y)),
    ]
    for index, mathematical in checked_cases:
        success = mathematical is not None and signed_min <= mathematical <= signed_max
        checks.append(public[index] == int(success))
        if success:
            checks += [signed_min <= s(w, public[index + 1]) <= signed_max,
                       s(w, public[index + 1]) == mathematical]
    if meta is not None:
        checks += [len(meta) == 8, meta[0] == u(w, x), meta[1] == u(w, x),
                   meta[2] == u(w, x), meta[3] == 0,
                   meta[6] == u(w, x * (u(w, y) + 1)), meta[7] == 1]
    assert all(checks)
    return len(checks)


def conversion_properties(w: int, z: int, n: int, natural: int,
                          row: list[int]) -> int:
    m, lo, hi = 1 << w, -(1 << (w - 1)), (1 << (w - 1)) - 1
    checks = [
        len(row) == 14, row[0] == z % m, row[1] == s(w, z), row[2] == z % m,
        row[3] == int(0 <= z < m), row[5] == int(lo <= z <= hi),
        row[7] == n % m, row[8] == int(0 <= n < m),
        row[10] == natural % m, row[11] == natural % m,
        row[12] == int(0 <= natural < m),
    ]
    assert all(checks)
    return len(checks)


def cross_properties(src: int, dst: int, z: int, row: list[int]) -> int:
    x, y = u(src, z), u(dst, z)
    checks = [
        len(row) == 6, row[0] == x, row[1] == u(dst, s(src, x)),
        row[2] == x, row[3] == x,
        row[4] == u(src, y), row[5] == u(dst, s(src, u(src, y))),
    ]
    # Both reverse shapes become true round trips precisely on their ranges.
    if y < (1 << src):
        checks.append(row[4] == y)
    if -(1 << (src - 1)) <= s(dst, y) < (1 << (src - 1)):
        checks.append(s(dst, row[5]) == s(dst, y))
    assert all(checks)
    return len(checks)


def rocq_api(width: int) -> str:
    w = f"Word{width}"
    return f"""Definition api{width} : scalar_api :=
  {{| api_word := {w}.t; api_zero := {w}.zero;
     api_neg := {w}.neg; api_add := {w}.add; api_sub := {w}.sub;
     api_mul := {w}.mul; api_logand := {w}.logand; api_logor := {w}.logor;
     api_logxor := {w}.logxor; api_lognot := {w}.lognot;
     api_eqb := {w}.eqb; api_ltu := {w}.ltu; api_leu := {w}.leu;
     api_lts := {w}.lts; api_les := {w}.les;
     api_addc := {w}.add_with_carry; api_subb := {w}.sub_with_borrow;
     api_neg_checked := {w}.neg_checked; api_add_checked := {w}.add_checked;
     api_sub_checked := {w}.sub_checked; api_mul_checked := {w}.mul_checked;
     api_divu := {w}.divu; api_modu := {w}.modu;
     api_divmodu := {w}.divmodu; api_divs := {w}.divs_checked;
     api_rems := {w}.rems; api_shift_left := {w}.shift_left;
     api_shift_right_logical := {w}.shift_right_logical;
     api_shift_right_arithmetic := {w}.shift_right_arithmetic;
     api_shift_left_signed := {w}.shift_left_signed;
     api_shift_right_signed := {w}.shift_right_signed;
     api_of_Z := {w}.of_Z;
     api_of_Z_unsigned_checked := {w}.of_Z_unsigned_checked;
     api_of_Z_signed_checked := {w}.of_Z_signed_checked;
     api_of_N := {w}.of_N; api_of_N_checked := {w}.of_N_checked;
     api_of_nat := {w}.of_nat; api_of_nat_checked := {w}.of_nat_checked;
     api_to_Z_unsigned := {w}.to_Z_unsigned;
     api_to_Z_signed := {w}.to_Z_signed; api_to_N := {w}.to_N;
     api_to_nat := {w}.to_nat |}}.
"""


def rocq_raw(width: int) -> str:
    w = f"Word{width}"
    return f"""Definition pw031_constants{width} : list Z :=
  [ {w}.to_Z_unsigned {w}.zero; {w}.to_Z_unsigned {w}.one
  ; {w}.to_Z_unsigned {w}.max_unsigned; {w}.to_Z_unsigned {w}.min_signed ].

Definition pw031_raw{width} (zx zy : Z) : list Z :=
  let x := {w}.of_Z zx in let y := {w}.of_Z zy in
  [ {w}.to_Z_unsigned ({w}.Raw.neg x)
  ; {w}.to_Z_unsigned ({w}.Raw.add x y)
  ; {w}.to_Z_unsigned ({w}.Raw.sub x y)
  ; {w}.to_Z_unsigned ({w}.Raw.mul x y)
  ; {w}.to_Z_unsigned ({w}.Raw.land x y)
  ; {w}.to_Z_unsigned ({w}.Raw.lor x y)
  ; {w}.to_Z_unsigned ({w}.Raw.lxor x y)
  ; {w}.to_Z_unsigned ({w}.Raw.lnot x)
  ; bool_Z ({w}.Raw.eqb x y); bool_Z ({w}.Raw.ltu x y)
  ; bool_Z ({w}.Raw.leu x y); bool_Z ({w}.Raw.lts x y)
  ; bool_Z ({w}.Raw.les x y)
  ; {w}.to_Z_unsigned ({w}.Raw.lsl x y)
  ; {w}.to_Z_unsigned ({w}.Raw.lsr x y)
  ; {w}.to_Z_unsigned ({w}.Raw.asr x y)
  ; {w}.to_Z_unsigned ({w}.Raw.divu x y)
  ; {w}.to_Z_unsigned ({w}.Raw.modu x y)
  ; {w}.to_Z_unsigned ({w}.Raw.divs x y)
  ; {w}.to_Z_unsigned ({w}.Raw.rems x y) ].

Definition pw031_public{width} (zx zy : Z) (amount : nat) : list Z :=
  pair_row api{width} ({w}.of_Z zx) ({w}.of_Z zy) amount.

Definition pw031_meta{width} (zx zy : Z) (amount : nat) : list Z :=
  let x := {w}.of_Z zx in let y := {w}.of_Z zy in
  let count := {w}.of_nat amount in
  [ {w}.to_Z_unsigned ({w}.Raw.sub ({w}.Raw.add x y) y)
  ; {w}.to_Z_unsigned ({w}.Raw.add ({w}.Raw.sub x y) y)
  ; {w}.to_Z_unsigned ({w}.Raw.lnot ({w}.Raw.lnot x))
  ; {w}.to_Z_unsigned ({w}.Raw.lxor x x)
  ; {w}.to_Z_unsigned ({w}.Raw.lsr ({w}.Raw.lsl x count) count)
  ; {w}.to_Z_unsigned ({w}.Raw.lsl ({w}.Raw.lsr x count) count)
  ; {w}.to_Z_unsigned ({w}.Raw.add ({w}.Raw.mul x y) x)
  ; bool_Z (Bool.eqb ({w}.Raw.ltu x y) (negb ({w}.Raw.leu y x))) ].

Definition pw031_conversion{width} (z : Z) (n : N) (natural : nat) : list Z :=
  conversion_row api{width} z n ++ nat_row api{width} natural.
"""


def rocq_cross(src: int, dst: int) -> str:
    sname, dname = f"Word{src}", f"Word{dst}"
    return f"""Definition pw031_cross_{src}_{dst} (z : Z) : list Z :=
  let x := {sname}.of_Z z in let y := {dname}.of_Z z in
  [ {dname}.to_Z_unsigned (zero_extend_{src}_{dst} x)
  ; {dname}.to_Z_unsigned (sign_extend_{src}_{dst} x)
  ; {sname}.to_Z_unsigned (narrow_{dst}_{src} (zero_extend_{src}_{dst} x))
  ; {sname}.to_Z_unsigned (narrow_{dst}_{src} (sign_extend_{src}_{dst} x))
  ; {dname}.to_Z_unsigned (zero_extend_{src}_{dst} (narrow_{dst}_{src} y))
  ; {dname}.to_Z_unsigned (sign_extend_{src}_{dst} (narrow_{dst}_{src} y)) ].
"""


def write_rocq_campaign(out: Path) -> None:
    api_defs = "\n".join(rocq_api(w) for w in (128, 256))
    raw_defs = "\n".join(rocq_raw(w) for w in WIDTHS)
    cross_defs = "\n".join(
        rocq_cross(src, dst) for i, src in enumerate(WIDTHS) for dst in WIDTHS[i + 1:])
    roots = [f"pw031_constants{w}" for w in WIDTHS] + \
            [f"pw031_raw{w}" for w in WIDTHS] + \
            [f"pw031_public{w}" for w in WIDTHS] + \
            [f"pw031_meta{w}" for w in WIDTHS] + \
            [f"pw031_conversion{w}" for w in WIDTHS] + \
            [f"pw031_cross_{s}_{d}" for i, s in enumerate(WIDTHS) for d in WIDTHS[i + 1:]]
    text = f"""(* Generated by pw031_campaign.py; do not edit. *)
From Stdlib Require Import ZArith NArith List Extraction.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 Word128 Word256 Conversions ScalarExtraction
  PW020Differential.
Import ListNotations.

{api_defs}
{raw_defs}
{cross_defs}
Extraction "PW031Extracted.ml" {' '.join(roots)}.
"""
    (out / "PW031Campaign.v").write_text(text)


def zlist(values: list[int]) -> str:
    return "[" + "; ".join(map(str, values)) + "]%Z"


def write_rocq_evaluators(out: Path) -> None:
    chunks = ["""(* Generated by pw031_campaign.py from its independent oracle. *)
From Stdlib Require Import ZArith List.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 Word128 Word256 PW031Campaign.
Import ListNotations.
Open Scope Z_scope.
Module PW8 := PrimitiveWords.Word8.
Module PW16 := PrimitiveWords.Word16.
Module PW32 := PrimitiveWords.Word32.
Module PW64 := PrimitiveWords.Word64.
Module PW128 := PrimitiveWords.Word128.
Module PW256 := PrimitiveWords.Word256.
"""]
    for w in WIDTHS:
        m, h = (1 << w) - 1, 1 << (w - 1)
        x, y, amount = m, 1, 1
        expected = (f"({zlist(raw_row(w, x, y))}, "
                    f"({zlist(public_row(w, x, y, amount))}, "
                    f"{zlist(meta_row(w, x, y, amount))}))")
        term = (f"(pw031_raw{w} {x} {y}, "
                f"(pw031_public{w} {x} {y} {amount}, "
                f"pw031_meta{w} {x} {y} {amount}))")
        chunks.append(f"""Example pw031_sample_{w}_cbv : {term} = {expected}.
Proof. cbv. reflexivity. Qed.
Example pw031_sample_{w}_vm : {term} = {expected}.
Proof. vm_compute. reflexivity. Qed.
Example pw031_signed_right_distinct_{w} :
  (PW{w}.to_Z_unsigned
     (PW{w}.shift_right_signed (PW{w}.of_Z (-1)) PW{w}.one),
   PW{w}.to_Z_unsigned
     (PW{w}.shift_right_logical (PW{w}.of_Z (-1)) 1)) =
  ({m}, {h - 1}).
Proof. cbv. reflexivity. Qed.
""")
    for w, positions in ((128, (0, 63, 64, 127)),
                         (256, (0, 63, 64, 127, 128, 191, 255))):
        rows = normalization_cases(w)
        for pos in positions:
            n, d = rows[pos]
            expected = zlist(raw_row(w, n, d))
            chunks.append(f"""Example pw031_normalized_{w}_{pos}_vm :
  pw031_raw{w} {n} {d} = {expected}.
Proof. vm_compute. reflexivity. Qed.
""")
    chunks.append("""Print Assumptions pw031_sample_8_cbv.
Print Assumptions pw031_sample_256_vm.
""")
    (out / "PW031Evaluators.v").write_text("\n".join(chunks))

    adapters = ["""(* Generated independent adapter observations. *)
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import PrimitiveWordAdapters.
From Rocq.PrimitiveWords Require Import Word8 Word16 Word32 Word64.
"""]
    for w in (8, 16, 32, 64):
        zval = (1 << w) + 3
        adapters.append(f"""Example pw031_adapter_{w}_cbv :
  Word{w}.to_Z_unsigned
    (ProductionWord{w}Adapter.to_primitive
      (Gecko.Word.Word{w}.of_Z {zval})) = 3.
Proof. cbv. reflexivity. Qed.
Example pw031_adapter_{w}_vm :
  Word{w}.to_Z_unsigned
    (ProductionWord{w}Adapter.to_primitive
      (Gecko.Word.Word{w}.of_Z {zval})) = 3.
Proof. vm_compute. reflexivity. Qed.
""")
    adapters.append("Print Assumptions pw031_adapter_8_cbv.\n")
    (out / "PW031Adapters.v").write_text("\n".join(adapters))


def generate(out: Path) -> dict[str, object]:
    out.mkdir(parents=True, exist_ok=True)
    vectors: list[str] = []
    oracle: list[str] = []
    raw_rows = public_rows = prop_checks = 0
    normalized: dict[str, dict[str, object]] = {}
    for w in WIDTHS:
        vectors.append(f"constants\t{w}")
        oracle.append("\t".join(["constants", str(w),
                                  ",".join(map(str, [0, 1, (1 << w) - 1, 1 << (w - 1)]))]))
        prop_checks += 4
        rows = pair_vectors(w)
        for index, (x, y, amount, family) in enumerate(rows):
            vectors.append(f"pair\t{w}\t{x}\t{y}\t{amount}\t{family}")
            rr, pr, mr = raw_row(w, x, y), public_row(w, x, y, amount), meta_row(w, x, y, amount)
            oracle.append("\t".join(["pair", str(w), str(x), str(y), str(amount), family,
                                      ",".join(map(str, rr + pr + mr))]))
            raw_rows += 1
            public_rows += 1
            prop_checks += properties(w, x, y, rr, pr, mr)
        zs = [-(1 << w) - 1, -(1 << w), -(1 << (w - 1)) - 1,
              -(1 << (w - 1)), -1, 0, 1, (1 << (w - 1)) - 1,
              1 << (w - 1), (1 << w) - 1, 1 << w, (1 << w) + 1]
        for i, z in enumerate(zs):
            n = abs(zs[-1 - i])
            natural = abs(z) if abs(z) <= 1024 else (i * 17 + w)
            vectors.append(f"conv\t{w}\t{z}\t{n}\t{natural}")
            cr = conversion_row(w, z, n, natural)
            prop_checks += conversion_properties(w, z, n, natural, cr)
            oracle.append("\t".join(["conv", str(w), str(z), str(n), str(natural),
                                      ",".join(map(str, cr))]))
    for si, src in enumerate(WIDTHS):
        for dst in WIDTHS[si + 1:]:
            for z in (-1, 0, 1, (1 << (src - 1)) - 1, 1 << (src - 1),
                      (1 << src) - 1, counter_value(src, 50000 + dst)):
                vectors.append(f"cross\t{src}\t{dst}\t{z}")
                xr = cross_row(src, dst, z)
                prop_checks += cross_properties(src, dst, z, xr)
                oracle.append("\t".join(["cross", str(src), str(dst), str(z),
                                          ",".join(map(str, xr))]))
    for w in (128, 256):
        nr = normalization_cases(w)
        shifts = [n.bit_length() - d.bit_length() for n, d in nr]
        normalized[str(w)] = {
            "rows": len(nr), "shift_min": min(shifts), "shift_max": max(shifts),
            "shift_count": len(set(shifts)), "entered": sum(n >= d for n, d in nr),
            "positive_quotient": sum(n // d > 0 for n, d in nr),
            "nonzero_remainder": sum(n % d != 0 for n, d in nr),
            "dense_divisor": sum(d & (d - 1) != 0 for n, d in nr),
        }
        assert normalized[str(w)]["entered"] == w
        assert normalized[str(w)]["positive_quotient"] == w
        assert normalized[str(w)]["shift_count"] == w
    # Oracle-specific independent guards against both prior correlation bugs.
    shift_guards = 0
    for w in WIDTHS:
        m, h = (1 << w) - 1, 1 << (w - 1)
        assert raw_shift(w, "asr", m, 1) == m
        assert raw_shift(w, "lsr", m, 1) == h - 1
        assert raw_shift(w, "asr", h, 1) == h + (h >> 1)
        shift_guards += 3
    (out / "vectors.tsv").write_text("\n".join(vectors) + "\n")
    (out / "oracle.tsv").write_text("\n".join(oracle) + "\n")
    summary = {
        "format": "PW031-independent-v1", "seed_hex": SEED.hex(),
        "widths": list(WIDTHS), "constant_rows": 6,
        "raw_rows": raw_rows, "public_rows": public_rows,
        "conversion_rows": sum(line.startswith("conv\t") for line in vectors),
        "cross_rows": sum(line.startswith("cross\t") for line in vectors),
        "oracle_property_checks": prop_checks, "signed_right_guards": shift_guards,
        "normalization": normalized,
        "vectors_sha256": hashlib.sha256((out / "vectors.tsv").read_bytes()).hexdigest(),
        "oracle_sha256": hashlib.sha256((out / "oracle.tsv").read_bytes()).hexdigest(),
    }
    matrix = ["surface\twidth_or_direction\toperation\trows\tnative\tbytecode\tcbv\tvm\tproof_gate"]
    raw_ops = ("neg add sub mul land lor lxor lnot eqb ltu leu lts les "
               "lsl lsr asr divu modu divs rems").split()
    public_ops = ("neg add sub mul logand logor logxor lognot eqb ltu leu lts les "
                  "add_with_carry sub_with_borrow neg_checked add_checked sub_checked "
                  "mul_checked divu modu divmodu divs_checked rems shift_left "
                  "shift_right_logical shift_right_arithmetic shift_left_signed "
                  "shift_right_signed").split()
    for w in WIDTHS:
        count = len(pair_vectors(w))
        for op in ("zero", "one", "max_unsigned", "min_signed"):
            matrix.append(f"constant\t{w}\t{op}\t1\tyes\tyes\tindirect\tindirect\tPW030")
        for op in raw_ops:
            matrix.append(f"raw\t{w}\t{op}\t{count}\tyes\tyes\tsample\tsample\tPW030")
        for op in public_ops:
            matrix.append(f"public\t{w}\t{op}\t{count}\tyes\tyes\tsample\tsample\tPW030")
        for op in "of_Z/to_Z of_N/to_N of_nat/to_nat checked_unsigned checked_signed".split():
            matrix.append(f"conversion\t{w}\t{op}\t12\tyes\tyes\tindirect\tindirect\tPW030")
    for i, src in enumerate(WIDTHS):
        for dst in WIDTHS[i + 1:]:
            for op in ("zero_extend", "sign_extend", "narrow"):
                matrix.append(f"cross-width\t{src}->{dst}\t{op}\t7\tyes\tyes\tPW030\tPW030\tPW030")
            matrix.append(f"roundtrip\t{src}<->{dst}\tnarrow_after_extend+bounded_reverse\t7\tyes\tyes\tPW030\tPW030\tPW030")
    for w in (8, 16, 32, 64):
        matrix.append(f"adapter\t{w}\tproduction_observation\t1\tno\tno\tyes\tyes\tPW030")
    (out / "coverage.tsv").write_text("\n".join(matrix) + "\n")
    summary["coverage_rows"] = len(matrix) - 1
    (out / "coverage.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_rocq_campaign(out)
    write_rocq_evaluators(out)
    summary["campaign_v_sha256"] = hashlib.sha256((out / "PW031Campaign.v").read_bytes()).hexdigest()
    summary["evaluators_v_sha256"] = hashlib.sha256((out / "PW031Evaluators.v").read_bytes()).hexdigest()
    summary["adapters_v_sha256"] = hashlib.sha256((out / "PW031Adapters.v").read_bytes()).hexdigest()
    summary["coverage_tsv_sha256"] = hashlib.sha256((out / "coverage.tsv").read_bytes()).hexdigest()
    (out / "coverage.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    return summary


def verify(actual: Path, expected: Path) -> None:
    a, e = actual.read_text().splitlines(), expected.read_text().splitlines()
    if a != e:
        for i, (aa, ee) in enumerate(zip(a, e), 1):
            if aa != ee:
                raise SystemExit(f"row {i} mismatch\nactual: {aa}\nexpect: {ee}")
        raise SystemExit(f"row count mismatch actual={len(a)} expected={len(e)}")
    property_checks = 0
    for line in a:
        fields = line.split("\t")
        values = list(map(int, fields[-1].split(",")))
        if fields[0] == "pair":
            w, x, y = map(int, fields[1:4])
            property_checks += properties(w, x, y, values[:20], values[20:61], values[61:])
        elif fields[0] == "conv":
            w, zv, nv, natural = map(int, fields[1:5])
            property_checks += conversion_properties(w, zv, nv, natural, values)
        elif fields[0] == "cross":
            src, dst, zv = map(int, fields[1:4])
            property_checks += cross_properties(src, dst, zv, values)
        elif fields[0] == "constants":
            w = int(fields[1])
            assert values == [0, 1, (1 << w) - 1, 1 << (w - 1)]
            property_checks += 4
        else:
            raise SystemExit(f"unknown row kind: {fields[0]}")
    print(f"verified_rows={len(a)}")
    print(f"verified_property_checks={property_checks}")
    print(f"actual_sha256={hashlib.sha256(actual.read_bytes()).hexdigest()}")


def main() -> None:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="mode", required=True)
    g = sub.add_parser("generate"); g.add_argument("out", type=Path)
    v = sub.add_parser("verify"); v.add_argument("actual", type=Path); v.add_argument("expected", type=Path)
    args = p.parse_args()
    if args.mode == "generate":
        print(json.dumps(generate(args.out), sort_keys=True))
    else:
        verify(args.actual, args.expected)


if __name__ == "__main__":
    main()
