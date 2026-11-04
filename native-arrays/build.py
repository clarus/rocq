#!/usr/bin/env python3
"""Build and validate Array64 with the fork's existing isolated standard OCaml switch."""
import argparse
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("build", "check"), nargs="?", default="check")
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("-j", "--jobs", type=int, choices=range(1, 5), default=1,
                        help="Concurrent build jobs (default: 1)")
    parser.add_argument("--memory-limit-mib", type=int, default=4096,
                        help="Per-process address-space limit, inherited by all checks (default: 4096 MiB)")
    args = parser.parse_args()
    if args.memory_limit_mib <= 0:
        parser.error("--memory-limit-mib must be positive")
    os.environ["OCAMLRUNPARAM"] = os.environ.get("OCAMLRUNPARAM", "") + ",d=1"
    limit = args.memory_limit_mib * 1024 * 1024
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    limit = min(value for value in (limit, soft, hard) if value != resource.RLIM_INFINITY)
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    print(f"Using {args.jobs} build job(s), {limit // (1024 * 1024)} MiB per-process limit.",
          flush=True)
    subprocess.run(["python3", str(ROOT / "native-integers/build.py"), args.action,
                    "--jobs", str(args.jobs)],
                   cwd=ROOT, check=True)
    if args.action == "check":
        command = ["python3", str(ROOT / "native-arrays/check.py")]
        if args.benchmark:
            command.append("--benchmark")
        subprocess.run(["bash", "-c", 'source "$1"; shift; exec "$@"',
                        "array64", str(ROOT / "_build/native-integers/env.sh"), *command],
                       cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
