From Corelib.Array Require Import PrimArray64.
From Ltac2 Require Import Ltac2.

Definition reflected_array := Eval vm_compute in repeat 3%word64 7%nat.

Ltac2 check_array64 () :=
  let a := eval cbv in reflected_array in
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Array64 u chunks ty =>
      let b := Constr.Unsafe.make (Constr.Unsafe.Array64 u chunks ty) in
      if Constr.equal a b then () else Control.throw Assertion_failure
  | _ => Control.throw Assertion_failure
  end.

Goal True.
Proof. check_array64 (); constructor. Qed.

(* An empty reflected array requires neither an element nor a default. *)
Ltac2 check_empty () :=
  let a := eval cbv in (@empty nat) in
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Array64 _ chunks _ =>
      match chunks with
      | [] => ()
      | _ :: _ => Control.throw Assertion_failure
      end
  | _ => Control.throw Assertion_failure
  end.

Goal True.
Proof. check_empty (); constructor. Qed.

Ltac2 expect_rejected c :=
  match Constr.Unsafe.check c with
  | Err _ => ()
  | Val _ => Control.throw Assertion_failure
  end.

Ltac2 check_unsafe_boundaries () :=
  let a := eval cbv in reflected_array in
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Array64 u _ ty =>
      let ill_typed := Constr.Unsafe.make
        (Constr.Unsafe.Array64 u [Array.make 1 '(true)] ty) in
      expect_rejected ill_typed;
      let empty_instance := match Constr.Unsafe.kind '(nat) with
        | Constr.Unsafe.Ind _ empty_instance => empty_instance
        | _ => Control.throw Assertion_failure end in
      let bad_instance := Constr.Unsafe.make
        (Constr.Unsafe.Array64 empty_instance [] ty) in
      expect_rejected bad_instance;
      let differently_chunked := Constr.Unsafe.make
        (Constr.Unsafe.Array64 u [Array.make 1 '(7%nat); Array.make 2 '(7%nat)] ty) in
      match Constr.Unsafe.check differently_chunked with
      | Val b => if Constr.equal a b then () else Control.throw Assertion_failure
      | Err e => Control.throw e
      end
  | _ => Control.throw Assertion_failure
  end.

Goal True.
Proof. check_unsafe_boundaries (); constructor. Qed.
