#!/usr/bin/env python3
"""Run the migrated independent six-width correctness and representation gates."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import time

API = Path(__file__).resolve().parent
ROOT = API.parent
WORK = ROOT / "_build/native-integers/tests"
WIDTHS = (8, 16, 32, 64, 128, 256)
RESULTS = {}


def run(label, argv, *, cwd=WORK, env=None, output=None, fail=False, timeout=3600):
    print(f"[{time.strftime('%H:%M:%S')}] {label}", flush=True)
    log = WORK / "logs" / (label + ".txt")
    start = time.monotonic()
    with log.open("wb") as stream:
        result = subprocess.run(list(map(str, argv)), cwd=cwd, env=env, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=timeout)
    text = log.read_text(errors="replace")
    if (result.returncode != 0) != fail:
        raise SystemExit(f"{label} failed (rc={result.returncode}):\n{text[-8000:]}")
    if output:
        shutil.copyfile(log, WORK / output)
    RESULTS[label] = {"returncode": result.returncode, "seconds": round(time.monotonic() - start, 3),
                      "sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
    return text


def rocq(name):
    return run("compile-" + name, ["rocq", "c", "-q", "-Q", ".", "Rocq.PrimitiveWords", name + ".v"])


def check_equal(left, right):
    if (WORK / left).read_bytes() != (WORK / right).read_bytes():
        raise SystemExit(f"Oracle mismatch: {left} != {right}")


def trust_audit():
    texts = [p.read_text() for p in (API / "theories").glob("*.v")]
    all_text = "\n".join(texts)
    if re.search(r"\b(?:Admitted|admit)\b", all_text):
        raise SystemExit("Admission in integer API")
    axioms = re.findall(r"^Axiom\s+(\w+)\s*:", all_text, re.M)
    if sorted(axioms) != sorted(f"word{w}_laws" for w in WIDTHS):
        raise SystemExit(f"Unexpected law assumptions: {axioms}")
    fields = re.findall(r"^  law_\w+\s*:", (API / "theories/PrimitiveWordSpec.v").read_text(), re.M)
    if len(fields) != 26:
        raise SystemExit("Law specification cardinality drift")
    primitive_count = sum(len(re.findall(r"^Primitive ", p.read_text(), re.M)) for p in
                          (ROOT / "theories/Corelib/Numbers/Primitive").glob("Word*.v"))
    if primitive_count != 126:
        raise SystemExit(f"Expected six types and 120 operations, found {primitive_count}")
    runtime = (ROOT / "kernel/primitive_words_runtime.ml").read_text()
    if re.search(r"\bZ\.|Zarith", runtime):
        raise SystemExit("Bigint arithmetic in primitive runtime")
    return {"primitive_types": 6, "raw_operations": 120, "law_constants": 6,
            "law_clauses": 156, "admissions": 0}


def primitive_smoke():
    shutil.copyfile(ROOT / "test-suite/success/primitive_words.v", WORK / "PrimitiveSmoke.v")
    rocq("PrimitiveSmoke")


def object_versions():
    original = (WORK / "PrimitiveSmoke.vo").read_bytes()
    if struct.unpack(">I", original[4:8])[0] != 90347:
        raise SystemExit("New object has incorrect version header")
    for version in (90300, 90346):
        name = f"Version{version}.vo"
        (WORK / name).write_bytes(original[:4] + struct.pack(">I", version) + original[8:])
        log = run(f"reject-format-{version}", ["rocq", "check", WORK / name], fail=True)
        if f"{version}" not in log or "90347" not in log:
            raise SystemExit("Missing object version rejection diagnostic")
    stock = Path(os.environ.get("NATIVE_INTEGER_STOCK_ROCQ", "/home/fedora/.opam/rocq-9.3.0/bin/rocq"))
    if not stock.is_file():
        raise SystemExit("Set NATIVE_INTEGER_STOCK_ROCQ to a stock Rocq executable")
    stock_env = os.environ.copy()
    for name in ("OCAMLPATH", "ROCQLIB", "ROCQPATH", "COQLIB", "COQPATH"):
        stock_env.pop(name, None)
    (WORK / "StockObject.v").write_text("Definition identity (n : nat) := n.\n")
    run("stock-object-compile", [stock, "c", "-q", "StockObject.v"], env=stock_env)
    run("fork-reject-stock", ["rocq", "check", WORK / "StockObject.vo"], fail=True)
    run("stock-reject-fork", [stock, "check", WORK / "PrimitiveSmoke.vo"], env=stock_env, fail=True)


def host_program(label, sources, *, zarith=False):
    packages = ["-package", "rocq-runtime.engine" if label == "identity" else "rocq-runtime.kernel"]
    if zarith:
        packages += ["-package", "zarith"]
    for engine, compiler, flags in (("native", "ocamlopt", ["-O3"]), ("bytecode", "ocamlc", ["-custom"])):
        executable = WORK / (label + "-" + engine)
        run(label + "-compile-" + engine,
            ["ocamlfind", compiler, *flags, "-linkpkg", *packages, *sources, "-o", executable])
    return [WORK / (label + "-" + engine) for engine in ("native", "bytecode")]


def existing_regressions():
    regressions = WORK / "regressions"
    regressions.mkdir(exist_ok=True)
    # Signed Int63 regressions import the test suite's auxiliary theory.
    auxiliary = ROOT / "test-suite/prerequisite/sint63.v"
    shutil.copyfile(auxiliary, regressions / "sint63.v")
    run("regression-sint63-helper", ["rocq", "c", "-q", "-Q", ".", "TestSuite", "sint63.v"], cwd=regressions)
    files = sorted((ROOT / "test-suite/primitive").rglob("*.v"))
    files += [ROOT / "test-suite/success" / name for name in
              ("primitive.v", "extraction_impl.v", "extraction_dep.v", "sort_poly_extraction.v")]
    for source in files:
        relative = source.relative_to(ROOT / "test-suite")
        destination = regressions / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        run("regression-" + str(relative.with_suffix("")).replace("/", "-"),
            ["rocq", "c", "-q", "-Q", regressions, "TestSuite", destination.name], cwd=destination.parent)
    return len(files)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / "logs").mkdir(exist_ok=True)
    # A failed rerun must never leave an earlier success marker.
    (WORK / "summary.json").unlink(missing_ok=True)
    for p in (API / "tests").iterdir():
        if p.is_file():
            shutil.copyfile(p, WORK / p.name)
    trust = trust_audit()
    run("wide-static-audit", ["python3", "pw024_static_audit.py", ROOT / "kernel/primitive_words_runtime.ml",
                              ROOT / "kernel/byterun/rocq_primitive_words_runtime.c"])
    kernel = run("select-kernel", ["ocamlfind", "query", "rocq-runtime.kernel"]).strip()
    if Path(kernel).resolve() != (ROOT / "_build/install/default/lib/rocq-runtime/kernel").resolve():
        raise SystemExit(f"Selected wrong kernel: {kernel}")
    primitive_smoke()
    object_versions()
    run("wide-oracle-generate", ["python3", "pw024_vectors.py", "pw024-vectors.tsv", "pw024-oracle.tsv", "pw024-summary.txt"])
    run("six-width-oracle-generate", ["python3", "pw046_generate.py", "--pw031", "pw031_campaign.py",
                                     "--pw032", "pw032_matrix.py", "--output", "."])
    generated = json.loads((WORK / "pw046-generation.json").read_text())
    if (generated["pw031_rows"], generated["pw031_property_checks"], generated["evaluator_witnesses"]) != (1299, 48954, 60):
        raise SystemExit("Oracle coverage drift")
    for name in ("PW020Differential", "PW031Campaign", "PW032Matrix", "PW046Evaluators",
                 "PW032FreshLoad", "PW045Use", "PW020SignedShiftRegression"):
        rocq(name)
    run("checker-evaluators", ["rocq", "check", "-silent", "-R", ".", "Rocq.PrimitiveWords",
                               "-norec", "Rocq.PrimitiveWords.PW046Evaluators",
                               "-norec", "Rocq.PrimitiveWords.PW032FreshLoad"])
    for name in ("PrimitiveWordSpec", "PrimitiveWordAxioms", "PrimitiveWordBounds"):
        run("checker-" + name, ["rocq", "check", "-silent", "-norec", "Rocq.PrimitiveWords." + name])

    for exe in host_program("wide", ["pw024_wide_check.ml"]):
        name = exe.name
        run(name + "-run", [exe, "pw024-vectors.tsv"], output=name + ".tsv")
        check_equal("pw024-oracle.tsv", name + ".tsv")
    for stem, driver, arguments, expected in (
        ("PW031Extracted", "pw031_extracted_main.ml", ["vectors.tsv"], "oracle.tsv"),
        ("PW032Extracted", "pw032_extracted_main.ml", [], "pw032-expected.tsv"),
    ):
        if "AXIOM TO BE REALIZED" in (WORK / (stem + ".ml")).read_text():
            raise SystemExit("Unrealized extraction axiom")
        for exe in host_program(stem, [stem + ".mli", stem + ".ml", driver], zarith=True):
            run(exe.name + "-run", [exe, *arguments], output=exe.name + ".tsv")
            check_equal(expected, exe.name + ".tsv")
            if stem == "PW031Extracted":
                run(exe.name + "-verify", ["python3", "pw031_campaign.py", "verify", exe.name + ".tsv", expected])
    for exe in host_program("portable-small", ["portable_small_check.ml"]):
        run(exe.name + "-run", [exe])
    boundary = host_program("boundary", ["pw032_boundary_check.ml"])
    for exe in boundary:
        output = run(exe.name + "-run", [exe, "boundary"])
        if "six_width_polymorphic_gc_compare_hash_wrong_access=passed" not in output:
            raise SystemExit("Representation test did not report success")
    run("marshal-write-native", [boundary[0], "write", "native.bin"])
    run("marshal-read-bytecode", [boundary[1], "read", "native.bin"])
    run("marshal-write-bytecode", [boundary[1], "write", "bytecode.bin"])
    run("marshal-read-native", [boundary[0], "read", "bytecode.bin"])
    check_equal("native.bin", "bytecode.bin")
    run("marshal-audit", ["python3", "pw032_marshal_audit.py", "native.bin", "malformed"])
    for width in WIDTHS:
        output = run(f"marshal-reject-{width}", [boundary[0], "reject", f"malformed/wrong-word{width}-id.bin"])
        if "unknown custom block identifier" not in output:
            raise SystemExit("Missing malformed identifier rejection")
    run("marshal-reject-truncated", [boundary[1], "reject", "malformed/truncated.bin"])
    for exe in host_program("identity", ["pw025_identity_check.ml"]):
        run(exe.name + "-run", [exe])
    symbols = run("runtime-symbols", ["nm", "-u", ROOT / "_build/default/kernel/.kernel.objs/native/primitive_words_runtime.o"])
    if re.search(r"zarith|caml_z", symbols, re.I):
        raise SystemExit("Bigint dependency in hot runtime")
    regression_count = existing_regressions()
    summary = {"widths": list(WIDTHS), "object_format": 90347, "trust": trust,
               "wide_oracle_rows_per_engine": 144096, "public_oracle_rows_per_engine": 1299,
               "public_oracle_properties_per_engine": 48954, "evaluator_witnesses": 60,
               "native_evaluator": "disabled", "existing_regressions": regression_count, "checks": RESULTS}
    (WORK / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("All native integer correctness gates passed.", flush=True)


if __name__ == "__main__":
    main()
