#!/usr/bin/env python3
"""Build the fork, fresh Stdlib, and native integer/array libraries without installing opam packages."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import tarfile
import time

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / "_build/native-integers"
STDLIB_REV = "b1c45dfc593b83371bdc996376de5b4ed66c5085"
DEFAULT_TOOLCHAIN = WORK / "sources"


def run(argv, *, cwd=ROOT, timeout=7200, env=None):
    print(f"[{time.strftime('%H:%M:%S')}] {' '.join(map(str, argv))}", flush=True)
    subprocess.run(list(map(str, argv)), cwd=cwd, env=env, check=True, timeout=timeout)


def environment():
    env = os.environ.copy()
    # Do not inherit an installed Rocq's theory paths.
    for name in ("COQLIB", "COQPATH", "ROCQLIB", "ROCQPATH", "OCAMLPATH"):
        env.pop(name, None)
    for source, target in (("NATIVE_INTEGER_OPAMROOT", "OPAMROOT"), ("NATIVE_INTEGER_SWITCH", "OPAMSWITCH")):
        if source in env:
            env[target] = env[source]
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("build", "check"), nargs="?", default="check")
    parser.add_argument("-j", "--jobs", type=int, choices=range(1, 5), default=1,
                        help="Concurrent build jobs (default: 1)")
    parser.add_argument("--gecko-word", type=Path,
                        help="Optionally build compatibility adapters against this Gecko.Word source directory")
    args = parser.parse_args()
    env = environment()
    if os.environ.get("NATIVE_INTEGER_IN_SWITCH") != "1":
        env["NATIVE_INTEGER_IN_SWITCH"] = "1"
        options = ["--root=" + env["OPAMROOT"]] if "OPAMROOT" in env else []
        if "OPAMSWITCH" in env:
            options.append("--switch=" + env["OPAMSWITCH"])
        import sys
        os.execvpe("opam", ["opam", "exec", *options, "--", "python3", str(Path(__file__).resolve()), *sys.argv[1:]], env)
    compiler = subprocess.check_output(["ocamlopt", "-version"], env=env, text=True).strip()
    env["OCAMLRUNPARAM"] = env.get("OCAMLRUNPARAM", "") + (",d=1" if int(compiler.split(".")[0]) >= 5 else "")
    WORK.mkdir(parents=True, exist_ok=True)
    if args.action == "check":
        (WORK / "tests/summary.json").unlink(missing_ok=True)
    (WORK / "compiler.txt").write_text(compiler + "\n")

    jobs = f"-j{args.jobs}"
    run(["dune", "build", "--profile=release", jobs, "tools/configure/configure.exe"], env=env)
    run([ROOT / "_build/default/tools/configure/configure.exe", "-quiet", "-relocatable",
         "-native-compiler", "no"], env=env)
    run(["make", "dunestrap", f"DUNEOPT=--profile=release {jobs}"], env=env)
    run(["dune", "build", "--profile=release", jobs, "rocq-runtime.install", "coq-core.install",
         "rocq-core.install", "coqide-server.install"], env=env)
    core = ROOT / "_build/install/default"
    if "let vo_version = 90348l" not in (ROOT / "_build/default/config/coq_config.ml").read_text():
        raise SystemExit("Unexpected compiled-object identity")
    env["PATH"] = str(core / "bin") + os.pathsep + env["PATH"]
    env["OCAMLPATH"] = str(core / "lib")
    env["ROCQLIB"] = str(core / "lib/coq")

    stdlib = WORK / "stdlib"
    if not stdlib.exists():
        source = Path(env.get("NATIVE_INTEGER_STDLIB_SOURCE", str(DEFAULT_TOOLCHAIN / "stdlib"))).resolve()
        if not source.exists():
            source.parent.mkdir(parents=True, exist_ok=True)
            run(["git", "clone", "https://github.com/rocq-prover/stdlib.git", source], env=env)
        archive = WORK / "stdlib-source.tar"
        with archive.open("wb") as stream:
            subprocess.run(["git", "-C", str(source), "archive", STDLIB_REV], stdout=stream, check=True)
        stdlib.mkdir()
        with tarfile.open(archive) as tar:
            tar.extractall(stdlib, filter="data")
        (stdlib / ".source-revision").write_text(STDLIB_REV + "\n")
    if (stdlib / ".source-revision").read_text().strip() != STDLIB_REV:
        raise SystemExit("Stdlib source revision mismatch")
    stdlib_stage = stdlib / "_build/install/default"
    env["ROCQPATH"] = str(stdlib_stage / "lib/coq/user-contrib")
    run(["dune", "build", "--root", stdlib, "--profile=release", jobs, "@install"], cwd=stdlib, env=env)
    api = ROOT / "native-integers"
    run(["dune", "build", "--root", api, "--profile=release", jobs, "@install"], cwd=api, env=env)
    api_stage = api / "_build/install/default"
    env["ROCQPATH"] += os.pathsep + str(api_stage / "lib/coq/user-contrib")
    arrays = ROOT / "native-arrays"
    run(["dune", "build", "--root", arrays, "--profile=release", jobs, "@install"], cwd=arrays, env=env)
    arrays_stage = arrays / "_build/install/default"
    env["ROCQPATH"] += os.pathsep + str(arrays_stage / "lib/coq/user-contrib")
    # This environment is also convenient for external consumers of the local build.
    import shlex
    assignments = {name: env[name] for name in ("PATH", "OCAMLPATH", "ROCQLIB", "ROCQPATH", "OPAMROOT", "OPAMSWITCH", "OCAMLRUNPARAM") if name in env}
    (WORK / "env.sh").write_text("\n".join(f"export {name}={shlex.quote(value)}" for name, value in assignments.items()) + "\n")
    if args.gecko_word:
        import shutil
        word = WORK / "compat/word"
        word.mkdir(parents=True, exist_ok=True)
        for name in ("Small", "Word8", "Word16", "Word32", "Word64"):
            shutil.copyfile(args.gecko_word / (name + ".v"), word / (name + ".v"))
            run([core / "bin/rocq", "c", "-q", "-Q", ".", "Gecko.Word", name + ".v"], cwd=word, env=env)
        adapters = word.parent / "adapters"
        adapters.mkdir(exist_ok=True)
        adapter = adapters / "PrimitiveWordAdapters.v"
        shutil.copyfile(api / "compat/PrimitiveWordAdapters.v", adapter)
        run([core / "bin/rocq", "c", "-q", "-Q", word, "Gecko.Word", "-Q", ".",
             "Rocq.PrimitiveWords", adapter.name], cwd=adapter.parent, env=env)
        run([core / "bin/rocq", "check", "-silent", "-Q", word, "Gecko.Word", "-Q", ".",
             "Rocq.PrimitiveWords", "-norec", "Rocq.PrimitiveWords.PrimitiveWordAdapters"],
            cwd=adapter.parent, env=env)
    if args.action == "check":
        run(["python3", api / "check.py"], cwd=api, env=env, timeout=14400)
    print("Native integer and array " + args.action + " completed.", flush=True)


if __name__ == "__main__":
    main()
