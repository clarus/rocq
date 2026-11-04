#!/usr/bin/env python3
"""Build standalone array tests/experiments against the existing standard OCaml kernel.

Run inside the workspace's managed command wrapper after sourcing
_build/native-integers/env.sh. All compiler outputs stay under _build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
WORK = ROOT / "_build/native-arrays/runtime"


def selection_scores(summary):
    families = {
        "point": ["read_262144", "update_32768"],
        "history": ["history_alternation_1000"],
        "slices": ["slice_replace_8192x512"],
        "bulk": ["repeat_65536", "concat_1024x64", "fill_8192x512"],
    }
    indexed = {(x["implementation"], x["case"]): x for x in summary}
    def geometric_mean(xs):
        values = list(xs)
        if any(x < 0 for x in values):
            raise ValueError("Negative benchmark measurement")
        return 0.0 if 0 in values else math.exp(statistics.mean(math.log(x) for x in values))
    scores = []
    for implementation in ("avl32", "avl128", "avl256"):
        times = {family: geometric_mean([
            indexed[implementation, case]["median_seconds"] /
            indexed["parray", case]["median_seconds"] for case in cases])
            for family, cases in families.items()}
        allocations = [geometric_mean([indexed[implementation, case]["median_bytes"]
                                       for case in cases]) for cases in families.values()]
        scores.append({"implementation": implementation, "family_time_ratios": times,
                       "time_score": geometric_mean(times.values()),
                       "allocation_score_bytes": geometric_mean(allocations)})
    best = min(x["time_score"] for x in scores)
    selected = min((x for x in scores if x["time_score"] <= best * 1.05),
                   key=lambda x: x["allocation_score_bytes"])
    return {"families": families, "scores": scores,
            "within_best_fraction": 0.05, "selected": selected["implementation"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["OCAMLRUNPARAM"] = "s=256k,o=120,d=1"
    runtime = (ROOT / "kernel/parray64.ml").read_text()
    (WORK / "parray64_candidate.ml").write_text(runtime)
    shutil.copyfile(ROOT / "kernel/array64chunks.ml", WORK / "array64chunks_candidate.ml")
    shutil.copyfile(HERE / "runtime_tests.ml", WORK / "runtime_tests.ml")
    base = ["ocamlfind", "ocamlopt", "-O3", "-linkpkg", "-package",
            "rocq-runtime.kernel,unix", "-I", str(WORK)]
    # Check the installed signatures separately; candidate copies expose the
    # representation solely so the unit tests can assert balancing invariants.
    interfaces = []
    for name in ("parray64", "array64chunks"):
        for suffix in ("mli", "ml"):
            target = f"{name}_interface.{suffix}"
            shutil.copyfile(ROOT / "kernel" / f"{name}.{suffix}", WORK / target)
            interfaces.append(target)
    subprocess.run(base + ["-c"] + interfaces, cwd=WORK, env=env, check=True)
    subprocess.run(base + ["parray64_candidate.ml", "array64chunks_candidate.ml",
                          "runtime_tests.ml", "-o", "runtime_tests"],
                   cwd=WORK, env=env, check=True)
    subprocess.run([str(WORK / "runtime_tests")], cwd=WORK, env=env, check=True)
    if not args.benchmark:
        return
    for capacity in (32, 128, 256):
        (WORK / f"parray64_{capacity}.ml").write_text(
            re.sub(r"let leaf_capacity = [0-9]+", f"let leaf_capacity = {capacity}", runtime))
    shutil.copyfile(HERE / "runtime_bench.ml", WORK / "runtime_bench.ml")
    subprocess.run(base + [f"parray64_{n}.ml" for n in (32, 128, 256)] +
                   ["runtime_bench.ml", "-o", "runtime_bench"], cwd=WORK, env=env, check=True)
    rows = []
    cpu = min(os.sched_getaffinity(0))
    for round_no in range(args.rounds + 1):
        data = subprocess.check_output(["taskset", "-c", str(cpu),
                                       str(WORK / "runtime_bench"), str(round_no)],
                                       cwd=WORK, env=env, text=True)
        if round_no:
            rows.extend(dict(json.loads(line), round=round_no) for line in data.splitlines())
    summary = []
    for case in sorted({row["case"] for row in rows}):
        for implementation in sorted({row["implementation"] for row in rows}):
            samples = [row for row in rows if row["case"] == case and
                       row["implementation"] == implementation]
            if samples:
                summary.append({"case": case, "implementation": implementation,
                                "median_seconds": statistics.median(x["seconds"] for x in samples),
                                "median_bytes": statistics.median(x["bytes"] for x in samples),
                                "median_retained_bytes": statistics.median(x["retained_bytes"] for x in samples)})
    for case in {row["case"] for row in rows}:
        if len({row["checksum"] for row in rows if row["case"] == case}) != 1:
            raise RuntimeError(f"implementations disagree on {case}")
    result = {"rounds": args.rounds, "gc": env["OCAMLRUNPARAM"], "cpu": cpu,
              "runtime_sha256": hashlib.sha256(runtime.encode()).hexdigest(),
              "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in [ROOT / "kernel/parray64.ml", ROOT / "kernel/parray64.mli",
                                             ROOT / "kernel/array64chunks.ml", ROOT / "kernel/array64chunks.mli",
                                             HERE / "runtime_tests.ml", HERE / "runtime_bench.ml",
                                             HERE / "run_runtime.py"]},
              "compiler": subprocess.check_output(["ocamlopt", "-version"], env=env, text=True).strip(),
              "samples": rows, "summary": summary, "selection": selection_scores(summary)}
    output = args.output or WORK / "results.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    print(f"Results: {output}")


if __name__ == "__main__":
    main()
