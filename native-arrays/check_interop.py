#!/usr/bin/env python3
"""OCaml extraction and print/reparse checks for primitive Array64 literals."""
from pathlib import Path
import re
import subprocess


def check_interop(work: Path, run) -> None:
    """Use the check.py runner (label, argv), whose working directory is work."""
    check_extraction(work, run)
    check_printing(work, run)


def check_extraction(work: Path, run) -> None:
    extraction = work / "Array64Extraction.v"
    extraction.write_text(r"""From Corelib.Array Require Import Array64 ExtrOCamlArray64.

Definition literal := Eval vm_compute in repeat 3%word64 7%word64.
Definition empty_literal {A} : array A := Eval vm_compute in @empty A.
Definition fresh := repeat 3%word64 7%word64.
Definition exercise (a : array word64) : word64 :=
  match set a 1%word64 9%word64 with
  | Some b =>
    match slice b 1%word64 1%word64 with
    | Some s =>
      match replace a 2%word64 s with
      | Some c =>
        match concat c c with
        | Some d => fold_left Word64.add d 0%word64
        | None => 0%word64 end
      | None => 0%word64 end
    | None => 0%word64 end
  | None => 0%word64 end.
Definition result := exercise literal.
Definition fresh_result := exercise fresh.
Definition mapped := map (fun x => Word64.add x 1%word64) literal.
Definition no_element := get (@empty word64) 0%word64.
Goal result = 46%word64 /\ fresh_result = 46%word64.
Proof. vm_compute; split; reflexivity. Qed.
Extraction "array64_interop.ml" literal empty_literal exercise result fresh_result mapped no_element.
""")
    run("interop-extract", ["rocq", "c", "-q", extraction.name])
    emitted = (work / "array64_interop.ml").read_text()
    if "Parray64.of_chunks" not in emitted:
        raise RuntimeError("Extraction did not exercise the primitive literal emitter")
    driver = work / "array64_interop_driver.ml"
    driver.write_text("""module W = Primitive_words_runtime.Word64
let word = W.of_int64
let equal expected actual = assert (W.equal (word expected) actual)
let () =
  equal 46L Array64_interop.result;
  equal 46L Array64_interop.fresh_result;
  equal 46L (Array64_interop.exercise Array64_interop.literal);
  equal 3L (Parray64.length Array64_interop.literal);
  equal 0L (Parray64.length (Array64_interop.empty_literal : int Parray64.t));
  equal 0L (Parray64.length (Array64_interop.empty_literal : string Parray64.t));
  assert (Array64_interop.no_element = None);
  begin match Parray64.get Array64_interop.mapped (word 2L) with
  | Some value -> equal 8L value
  | None -> assert false end;
  begin match Parray64.get Array64_interop.literal (word 1L) with
  | Some value -> equal 7L value
  | None -> assert false end;
  print_endline "Array64 extracted literal and operations passed"
""")
    for engine, compiler, flags in (("native", "ocamlopt", []), ("bytecode", "ocamlc", ["-custom"])):
        executable = "array64_interop_" + engine + ".exe"
        run("interop-ocaml-compile-" + engine, ["ocamlfind", compiler, *flags, "-linkpkg", "-package",
            "rocq-runtime.kernel", "array64_interop.mli",
            "array64_interop.ml", driver.name, "-o", executable])
        run("interop-ocaml-run-" + engine, [work / executable])


def check_printing(work: Path, run) -> None:
    examples = [
        ("Nat", "array nat", "repeat 3%word64 7%nat"),
        ("Types", "array Type", "@repeat Type 2%word64 nat"),
        ("EmptyTypes", "array Type", "@empty Type"),
        ("Empty", "array False", "@empty False"),
        ("Binder", "nat -> array nat", "fun x : nat => repeat 2%word64 x"),
    ]
    for name, typ, term in examples:
        printer = work / f"PrintArray64{name}.v"
        printer.write_text("From Corelib.Array Require Import PrimArray64.\n"
                           "Set Printing Width 100000.\nSet Printing Depth 100000.\n"
                           f"Eval vm_compute in ({term}).\n")
        label = "interop-print-" + name
        run(label, ["rocq", "c", "-q", printer.name])
        output = (work / (label + ".log")).read_text()
        match = re.search(r"(?ms)^\s*=\s*(.*?)\n\s*:\s*[^\n]+", output)
        if not match or "literal_of_list" not in match.group(1):
            raise RuntimeError(f"Unexpected Array64 pretty-printer output:\n{output}")
        printed = match.group(1)
        reparsed = work / f"ReparseArray64{name}.v"
        reparsed.write_text("From Corelib.Array Require Import PrimArray64.\n"
            f"Definition reparsed : {typ} := {printed}.\n"
            f"Example reparsed_kernel : reparsed = ({term}).\n"
            "Proof. exact eq_refl. Qed.\n"
            f"Example reparsed_vm : reparsed = ({term}).\n"
            "Proof. vm_compute; reflexivity. Qed.\n")
        run("interop-reparse-" + name,
            ["rocq", "c", "-q", "-Q", ".", "Array64Interop", reparsed.name])
        run("interop-check-" + name,
            ["rocq", "check", "-silent", "-Q", ".", "Array64Interop",
             "Array64Interop." + reparsed.stem])


if __name__ == "__main__":
    work = Path(__file__).resolve().parent.parent / "_build/native-arrays/interop"
    work.mkdir(parents=True, exist_ok=True)

    def run(label, command):
        print(label, flush=True)
        log = work / (label + ".log")
        with log.open("w") as output:
            result = subprocess.run(list(map(str, command)), cwd=work,
                                    stdout=output, stderr=subprocess.STDOUT, timeout=300)
        if result.returncode:
            raise SystemExit(log.read_text())

    check_interop(work, run)
