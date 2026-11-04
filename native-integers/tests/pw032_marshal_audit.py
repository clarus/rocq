#!/usr/bin/env python3
"""Check stable six-width payloads and generate defensive malformed streams."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("stream", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
data = args.stream.read_bytes()
args.output.mkdir(parents=True, exist_ok=True)

payloads = {
    8: bytes.fromhex("a5"), 16: bytes.fromhex("a55a"),
    32: bytes.fromhex("a55aa55a"), 64: bytes.fromhex("fedcba9876543210"),
    128: bytes.fromhex("fedcba98765432100123456789abcdef"),
    256: bytes.fromhex(
        "fedcba9876543210aaaabbbbccccdddd11112222333344440123456789abcdef"),
}
for width, expected in payloads.items():
    identifier = f"_gecko_primitive_words_word{width}_v1".encode()
    offsets = [index for index in range(len(data)) if data.startswith(identifier, index)]
    # Marshal shares repetitions but writes the original and incremented
    # custom values independently in this archive.
    if len(offsets) != 2:
        raise SystemExit(f"Word{width}: custom identifier count {len(offsets)} != 2")
    identifier_offset = offsets[0]
    payload_offset = identifier_offset + len(identifier) + 1
    actual = data[payload_offset:payload_offset + len(expected)]
    advanced_offset = offsets[1] + len(identifier) + 1
    advanced = data[advanced_offset:advanced_offset + len(expected)]
    expected_advanced = ((int.from_bytes(expected, "big") + 1)
                         % (1 << width)).to_bytes(len(expected), "big")
    if actual != expected or advanced != expected_advanced:
        raise SystemExit(
            f"Word{width}: endian payloads {actual.hex()},{advanced.hex()} != "
            f"{expected.hex()},{expected_advanced.hex()}")
    wrong = bytearray(data)
    wrong[identifier_offset + len(identifier) - 1] = ord("2")
    (args.output / f"wrong-word{width}-id.bin").write_bytes(wrong)
    print(f"word{width}_payload_bytes={len(actual)}")
    print(f"word{width}_payload_hex={actual.hex()}")
    print(f"word{width}_advanced_payload_hex={advanced.hex()}")

(args.output / "truncated.bin").write_bytes(data[:-1])
print(f"marshal_sha256={hashlib.sha256(data).hexdigest()}")
print("mutations=6_wrong_ids+truncated")
