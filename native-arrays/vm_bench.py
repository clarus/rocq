#!/usr/bin/env python3
"""Compare Array64 and legacy primitive arrays using actual vm_compute terms.

Run after sourcing the standard OCaml
environment. All generated Rocq sources and compiler products stay in _build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import resource
import statistics
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
WORK = ROOT / "_build/native-arrays/vm"
VARIANTS = ("legacy", "array64")


def source(variant: str, case: str) -> str:
    modern = variant == "array64"
    scope = "word64" if modern else "uint63"
    index = "Word64.word64" if modern else "PrimInt63.int"
    integer = "Word64" if modern else "PrimInt63"
    arr = "PrimArray64.array" if modern else "PrimArray.array"
    make = "PrimArray64.repeat" if modern else "PrimArray.make"
    get = ("match PrimArray64.get a i with Some x => x | None => 0%uint63 end"
           if modern else "PrimArray.get a i")
    update = ("match PrimArray64.set a i x with Some b => b | None => a end"
              if modern else "PrimArray.set a i x")
    prefix = f"""From Corelib.Array Require Import PrimArray Array64.
From Corelib.Numbers.Cyclic.Int63 Require Import PrimInt63.
Definition idx := {index}.
Definition arr := {arr} PrimInt63.int.
Definition izero : idx := 0%{scope}.
Definition ione : idx := 1%{scope}.
Definition incr (i : idx) := {integer}.add i ione.
Definition next (i : idx) := {integer}.land (incr i) 65535%{scope}.
Definition rmake (n : idx) (x : PrimInt63.int) : arr := {make} n x.
Definition rget (a : arr) (i : idx) := {get}.
Definition rset (a : arr) (i : idx) (x : PrimInt63.int) : arr := {update}.
Fixpoint iterate {{A}} (depth : nat) (f : A -> A) (x : A) : A :=
  match depth with O => f x | S k => iterate k f (iterate k f x) end.
Definition point_step (state : arr * (idx * PrimInt63.int)) :=
  let '(a, (i, checksum)) := state in
  let x := PrimInt63.add (rget a i) 1%uint63 in
  (rset a i x, (next i, PrimInt63.add checksum x)).
Definition initial : arr := rmake 65536%{scope} 0%uint63.
Definition copy_step (src : arr) (state : idx * (arr * idx)) :=
  let '(si, (dst, di)) := state in
  (incr si, (rset dst di (rget src si), incr di)).
Definition copy_pow (depth : nat) (src : arr) (si : idx) (dst : arr) (di : idx) :=
  fst (snd (iterate depth (copy_step src) (si, (dst, di)))).
"""
    if modern:
        prefix += """Definition rslice (a : arr) :=
  match PrimArray64.slice a 1024%word64 1024%word64 with
  | Some b => b | None => PrimArray64.empty end.
Definition rreplace (a part : arr) :=
  match PrimArray64.replace a 2048%word64 part with Some b => b | None => a end.
Definition rfill (a : arr) :=
  match Array64.fill a 4096%word64 8192%word64 2%uint63 with
  | Some b => b | None => a end.
"""
    else:
        prefix += """Definition rslice (a : arr) :=
  copy_pow 10 a 1024%uint63 (rmake 1024%uint63 0%uint63) izero.
Definition rreplace (a part : arr) := copy_pow 10 part izero a 2048%uint63.
Definition fill_step (state : arr * idx) :=
  let '(a, i) := state in (rset a i 2%uint63, incr i).
Definition rfill (a : arr) := fst (iterate 13 fill_step (a, 4096%uint63)).
"""
    bodies = {
        "point": ("snd (snd (iterate 18 point_step (initial, (izero, 0%uint63))))", 655360),
        "history": ("""let recent := fst (iterate 9 point_step (initial, (izero, 0%uint63))) in
  iterate 14 (fun checksum =>
    PrimInt63.add (PrimInt63.add checksum (rget initial izero)) (rget recent izero))
    0%uint63""", 16384),
        "slice": (f"""snd (iterate 12 (fun state : arr * PrimInt63.int =>
    let '(a, checksum) := state in
    let part := rslice a in
    let part := rset part izero (PrimInt63.add (rget part izero) 1%uint63) in
    let a := rreplace a part in
    (a, PrimInt63.add checksum (rget a 2048%{scope})))
    (rmake 4096%{scope} 7%uint63, 0%uint63))""", 32768),
        "bulk": (f"""iterate 8 (fun checksum =>
    let a := rfill (rmake 16384%{scope} 1%uint63) in
    PrimInt63.add checksum
      (PrimInt63.add (PrimInt63.add (rget a izero) (rget a 4096%{scope}))
                    (PrimInt63.add (rget a 12287%{scope}) (rget a 12288%{scope}))))
    0%uint63""", 1536),
    }
    if case == "quote":
        return prefix + f"""Time Definition quoted := Eval vm_compute in rmake 8192%{scope} 1%uint63.
Goal rget quoted 8191%{scope} = 1%uint63.
Proof. vm_compute; reflexivity. Qed.
"""
    term, checksum = bodies[case]
    return prefix + f"""Definition workload : PrimInt63.int := {term}.
Goal workload = {checksum}%uint63.
Proof. Time vm_compute. reflexivity. Qed.
"""


def execute(path: Path, case: str, variant: str, round_id: int) -> dict:
    log = WORK / "logs" / f"{round_id}-{case}-{variant}.log"
    metrics = log.with_suffix(".metrics")
    env = os.environ.copy()
    env["OCAMLRUNPARAM"] = "s=256k,o=120,l=32M,d=1"
    cmd = ["/usr/bin/time", "-f", "%e %U %S %M", "-o", str(metrics),
           "rocq", "compile", "-q", "-Q", str(WORK / "sources"), "Array64Bench", str(path)]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=WORK, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    process_seconds = time.monotonic() - start
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{path.name} failed; see {log}\n{result.stdout[-2500:]}")
    times = re.findall(r"Finished transaction in ([\d.]+) secs \(([\d.]+)u,([\d.]+)s\)", result.stdout)
    if len(times) != 1:
        raise RuntimeError(f"Expected one Time result in {log}, found {times}")
    _, user, system, rss = metrics.read_text().split()
    return {"case": case, "variant": variant, "round": round_id,
            "vm_seconds": float(times[0][0]), "vm_user_seconds": float(times[0][1]),
            "vm_system_seconds": float(times[0][2]), "process_seconds": process_seconds,
            "process_user_seconds": float(user), "process_system_seconds": float(system),
            "max_rss_kib": int(rss)}


def report(results: dict) -> str:
    lines = ["# Array64 VM benchmarks", "",
             "Paired measurements from actual `vm_compute` on the same modified Rocq binary.",
             "Legacy slice/replacement/fill use loops over `PrimArray.get/set`; Array64 uses its checked range operations.",
             "Elements are `int63` in both variants. Indices use each datatype's native index type.", "",
             f"{results['rounds']} measured rounds after one warmup; CPU {results['cpu']}; "
             "GC `s=256k,o=120,l=32M,d=1`; 256 MiB process stack. Case and variant order are shuffled with a fixed seed.", "",
             "| Workload | Legacy median (s) | Array64 median (s) | Array64 / legacy |",
             "|---|---:|---:|---:|"]
    for case, row in results["summary"].items():
        a, b = row["legacy_vm_median"], row["array64_vm_median"]
        ratio = f"{b/a:.3f}" if a else "below timer resolution"
        lines.append(f"| {case} | {a:.3f} | {b:.3f} | {ratio} |")
    lines += ["", "Workloads:", "",
              "- Point: 262,144 sequential persistent updates and reads, wrapping over 65,536 elements; checksum 655,360.",
              "- History: retain an original and a version after 512 updates, then alternate 16,384 reads of both; checksum 16,384.",
              "- Slice: 4,096 iterations taking 1,024 elements, updating the first, and replacing a disjoint range in a 4,096-element array; checksum 32,768.",
              "- Bulk: 256 eager constructions of 16,384 elements and eager fills of an 8,192-element range; checksum 1,536.",
              "- Quote: normalize and save an 8,192-element literal, then recompile it through a checked read. Its timed command includes construction and quotation; it is reported separately from the four operational workloads.", "",
              "The four operation cases return scalar checksums and prove their expected values, avoiding full-array quotation. "
              "Peak RSS and complete-process time include loading and checking, so they are recorded in JSON as process measurements, not as operation allocation counts. "
              "The standalone runtime benchmark measures allocation more directly. "
              "Rocq's timer has millisecond resolution; very small differences should not be interpreted as wins.", "",
              "The fixed 128-slot leaf capacity is retained from the existing implementation. "
              "These measurements compare the public checked Array64 interface with the old unchecked/default-valued interface; their costs include that difference. "
              "They do not compare against Rust or claim that point updates improve over the legacy mutable-difference representation.", "",
              "Reproduce after building and sourcing `_build/native-integers/env.sh`:", "",
              "```sh",
              "  bash -c 'source _build/native-integers/env.sh; python3 native-arrays/vm_bench.py'", "```", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--case", choices=("point", "history", "slice", "bulk", "quote"), action="append")
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    cases = args.case or ["point", "history", "slice", "bulk", "quote"]
    (WORK / "sources").mkdir(parents=True, exist_ok=True)
    (WORK / "logs").mkdir(exist_ok=True)
    paths = {}
    for case in cases:
        for variant in VARIANTS:
            path = WORK / "sources" / f"{case}_{variant}.v"
            path.write_text(source(variant, case))
            paths[case, variant] = path
    if args.generate_only:
        return
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    stack = 256 * 1024 * 1024
    if hard != resource.RLIM_INFINITY:
        stack = min(stack, hard)
    resource.setrlimit(resource.RLIMIT_STACK, (stack, hard))
    rng, rows = random.Random(640128), []
    for round_id in range(-1, args.rounds):
        order = cases[:]
        rng.shuffle(order)
        for case in order:
            variants = list(VARIANTS)
            rng.shuffle(variants)
            for variant in variants:
                row = execute(paths[case, variant], case, variant, round_id)
                if round_id >= 0:
                    rows.append(row)
                print(f"round {round_id}: {case} {variant} {row['vm_seconds']:.3f}s", flush=True)
            (WORK / "raw.json").write_text(json.dumps(rows, indent=2) + "\n")
    summary = {}
    for case in cases:
        summary[case] = {}
        for variant in VARIANTS:
            samples = [r for r in rows if r["case"] == case and r["variant"] == variant]
            for metric in ("vm_seconds", "process_seconds", "max_rss_kib"):
                name = {"vm_seconds": "vm", "process_seconds": "process", "max_rss_kib": "max_rss_kib"}[metric]
                summary[case][f"{variant}_{name}_median"] = statistics.median(r[metric] for r in samples)
    worker = ROOT / "_build/install/default/lib/rocq-runtime/rocqworker"
    results = {"rounds": args.rounds, "cpu": cpu, "c_stack_limit_bytes": stack,
               "date": time.strftime("%Y-%m-%d"), "summary": summary, "rows": rows,
               "worker_sha256": hashlib.sha256(worker.read_bytes()).hexdigest(),
               "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "sources": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths.values()}}
    (HERE / "vm-results.json").write_text(json.dumps(results, indent=2) + "\n")
    (HERE / "VM-RESULTS.md").write_text(report(results))


if __name__ == "__main__":
    main()
