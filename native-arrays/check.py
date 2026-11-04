#!/usr/bin/env python3
"""Validate Array64 using the locally staged fork and freshly rebuilt libraries."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time
from check_interop import check_interop

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / "_build/native-arrays/checks"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / "summary.json").unlink(missing_ok=True)
    results = {}

    def run(label, command):
        print(label, flush=True)
        log = WORK / (label + ".log")
        start = time.monotonic()
        with log.open("wb") as output:
            result = subprocess.run(list(map(str, command)), cwd=WORK,
                                    stdout=output, stderr=subprocess.STDOUT, timeout=3600)
        if result.returncode:
            raise SystemExit(f"{label}:\n{log.read_text(errors='replace')[-8000:]}")
        results[label] = {"seconds": time.monotonic() - start,
                          "sha256": hashlib.sha256(log.read_bytes()).hexdigest()}

    declarations = ROOT / "theories/Corelib/Array/PrimArray64.v"
    if len(re.findall(r"^Primitive ", declarations.read_text(), re.M)) != 9:
        raise SystemExit("Expected one Array64 type and eight primitive operations")
    specs = ROOT / "theories/Corelib/Array/Array64Axioms.v"
    axioms = re.findall(r"^Axiom\s+(\w+)", specs.read_text(), re.M)
    if len(axioms) != 23:
        raise SystemExit("Array64 primitive specification cardinality changed")
    sources = list((ROOT / "theories/Corelib/Array").glob("*Array64*.v"))
    sources += list((ROOT / "native-arrays/theories").glob("*.v"))
    for source in sources:
        text = source.read_text()
        if re.search(r"\b(?:Admitted|admit)\b", text):
            raise SystemExit(f"Admission in {source}")
        if source != specs and re.search(r"^Axiom\s", text, re.M):
            raise SystemExit(f"Unexpected trusted assumption in {source}")

    tests = sorted((ROOT / "test-suite/primitive/arrays64").glob("*.v"))
    tests.append(ROOT / "test-suite/success/primitive_array64_types.v")
    for source in tests:
        shutil.copyfile(source, WORK / source.name)
        run("compile-" + source.stem,
            ["rocq", "c", "-q", "-Q", ".", "Array64Tests", source.name])
        run("check-" + source.stem,
            ["rocq", "check", "-silent", "-Q", ".", "Array64Tests",
             "Array64Tests." + source.stem])
    proof_modules = ["Corelib.Array.Array64Properties", "Rocq.NativeArrays.Array64Laws",
                     "Rocq.NativeArrays.MapFoldProperties", "Rocq.NativeArrays.ListProperties"]
    # Check shared dependencies once, retaining the complete recursive check.
    # Keep the trace in the log so a slow proof can be identified immediately.
    run("check-array64-proofs", ["rocq", "check", *proof_modules])
    for name in ("cbn_primitive_alias", "cbn", "cbn2", "cbn3", "cbn_refold_after_iota_alias"):
        shutil.copyfile(ROOT / "test-suite/success" / (name + ".v"), WORK / (name + ".v"))
        run("regression-" + name, ["rocq", "c", "-q", name + ".v"])
    for name in ("literal", "nested", "univs"):
        target = "LegacyArray_" + name
        shutil.copyfile(ROOT / "test-suite/primitive/arrays" / (name + ".v"),
                        WORK / (target + ".v"))
        run("regression-" + target,
            ["rocq", "c", "-q", "-Q", ".", "Array64Tests", target + ".v"])
        run("check-" + target,
            ["rocq", "check", "-silent", "-Q", ".", "Array64Tests", "Array64Tests." + target])
    check_interop(WORK, run)
    command = ["python3", ROOT / "native-arrays/run_runtime.py"]
    if args.benchmark:
        command.append("--benchmark")
    run("runtime", command)
    if args.benchmark:
        run("vm-benchmark", ["python3", ROOT / "native-arrays/vm_bench.py"])
    (WORK / "summary.json").write_text(json.dumps({
        "primitive_types": 1, "primitive_operations": 8,
        "proof_modules": proof_modules,
        "primitive_laws": axioms, "admissions": 0, "checks": results,
    }, indent=2) + "\n")
    print("Array64 checks passed.", flush=True)


if __name__ == "__main__":
    main()
