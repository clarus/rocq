(* Regression for #22550: after computing a primitive, cbn must not refold
   its result to an alias of the primitive function. *)
From Corelib Require Import PrimInt63 PrimFloat PrimString PrimArray.

Open Scope uint63_scope.
Open Scope array_scope.

(* Conversion alone would also accept an unreduced application. Check the
   actual cbn output, including under binders and in surrounding contexts. *)
Ltac check_cbn term expected :=
  let actual := eval cbn in term in constr_eq actual expected.

Definition add_alias := PrimInt63.add.
Definition add_alias_twice := add_alias.
Definition one := 1.
Definition eq_alias := PrimInt63.eqb.
Definition pair_alias := PrimInt63.diveucl.
Definition float_alias := PrimFloat.add.
Definition string_alias := PrimString.cat.

(* The original reproducer, including an explicitly typed definition checked
   by the kernel. The broken reducer returned [add_alias : int -> int -> int]. *)
Definition reduced_add : int := Eval cbn in add_alias 1 2.
Example reduced_add_correct : reduced_add = 3.
Proof. reflexivity. Qed.

Goal True.
Proof.
  check_cbn (add_alias 1 2) 3.
  check_cbn (add_alias_twice one 2) 3.
  check_cbn ((fun f => f 1 2) add_alias) 3.
  check_cbn (fun n : nat => add_alias 1 2) (fun _ : nat => 3).
  check_cbn (PrimInt63.add (add_alias 1 2) (add_alias 3 4)) 10.
  check_cbn (fun n : int => add_alias (add_alias 1 2) n)
            (fun n : int => PrimInt63.add 3 n).
  check_cbn (eq_alias 1 2) false.
  check_cbn (if eq_alias 1 1 then 4 else 5) 4.
  check_cbn (pair_alias 7 3) (2, 1).
  check_cbn (float_alias 1%float 2%float) 3%float.
  check_cbn (string_alias "ab"%pstring "cd"%pstring) "abcd"%pstring.
  exact I.
Qed.

(* Successful array operations use a separate, closure-preserving path. *)
Definition get_alias := @PrimArray.get.
Definition default_alias := @PrimArray.default.
Definition make_alias := @PrimArray.make.
Definition set_alias := @PrimArray.set.
Definition copy_alias := @PrimArray.copy.
Definition length_alias := @PrimArray.length.

Definition reduced_get : nat := Eval cbn in get_alias nat [| 1%nat | 2%nat |] 0.
Example reduced_get_correct : reduced_get = 1%nat.
Proof. reflexivity. Qed.

Goal True.
Proof.
  check_cbn (get_alias nat [| 1%nat; 2%nat | 3%nat |] 0) 1%nat.
  check_cbn (get_alias nat [| 1%nat; 2%nat | 3%nat |] 9) 3%nat.
  check_cbn (default_alias nat [| 1%nat | 3%nat |]) 3%nat.
  check_cbn (make_alias nat 2 3%nat) [| 3%nat; 3%nat | 3%nat |].
  check_cbn (set_alias nat [| 1%nat; 2%nat | 3%nat |] 0 4%nat)
            [| 4%nat; 2%nat | 3%nat |].
  check_cbn (copy_alias nat [| 1%nat | 3%nat |]) [| 1%nat | 3%nat |].
  check_cbn (length_alias nat [| 1%nat; 2%nat | 3%nat |]) 2.
  (* A primitive can return a function. Its extra arguments must still be
     applied, and delayed substitutions in the selected value must survive. *)
  check_cbn (get_alias (nat -> nat) [| S | (fun n => n) |] 0 2%nat) 3%nat.
  check_cbn ((fun n : nat => get_alias nat [| n | O |] 0) 4%nat) 4%nat.
  check_cbn (fun n : nat => get_alias nat [| n | O |] 0) (fun n : nat => n).
  exact I.
Qed.

(* Insufficient or blocked arguments do not perform a primitive step. Keep
   their previous behavior, and respect explicit reduction restrictions. *)
Goal True.
Proof.
  check_cbn add_alias add_alias.
  check_cbn (add_alias 1) (add_alias 1).
  check_cbn (fun n : int => add_alias n 2) (fun n : int => PrimInt63.add n 2).
  check_cbn (fun n : int => add_alias 1 n) (fun n : int => PrimInt63.add 1 n).
  check_cbn (@get_alias nat) (@get_alias nat).
  let t := eval cbn -[PrimInt63.add] in (add_alias 1 2) in
  constr_eq t (add_alias 1 2).
  exact I.
Qed.

Module NeverUnfold.
  Definition add := PrimInt63.add.
  Arguments add _ _ : simpl never.
  Goal True.
  Proof. check_cbn (add 1 2) (add 1 2). exact I. Qed.
End NeverUnfold.

(* Exercise tactic reduction and check the resulting proof in the kernel. *)
Example alias_in_goal : add_alias 1 2 = 3.
Proof.
  cbn.
  lazymatch goal with |- 3 = 3 => reflexivity end.
Qed.
