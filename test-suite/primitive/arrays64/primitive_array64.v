From Corelib.Array Require Import PrimArray64.
From Corelib.Floats Require Import PrimFloat.

Open Scope word64_scope.

Ltac check_vm term expected :=
  let actual := eval vm_compute in term in constr_eq actual expected.
Ltac check_cbv term expected :=
  let actual := eval cbv in term in constr_eq actual expected.
Ltac check_cbn term expected :=
  let actual := eval cbn in term in constr_eq actual expected.

Definition get_alias := @get.
Definition repeat_alias := @repeat.
Definition empty_alias := @empty.

(* Tactics also use the generic weak-head reducer. In particular, injection
   must reduce a primitive with only a type parameter without looking for a
   nonexistent computational argument. *)
Goal forall A (a : array A), Some (@empty A) = Some a -> empty = a.
Proof. intros A a H. injection H as H. exact H. Qed.
Goal forall A (a : array A), Some (@empty_alias A) = Some a -> empty = a.
Proof. intros A a H. injection H as H. exact H. Qed.

Goal True.
Proof.
  check_vm (length (@empty nat)) 0%word64.
  check_cbv (length (@empty nat)) 0%word64.
  check_cbn (length (@empty_alias nat)) 0%word64.
  check_vm (get (@empty nat) 0) (@None nat).
  check_vm (get_alias nat (repeat 3 7%nat) 2) (Some 7%nat).
  check_cbv (get_alias nat (repeat_alias nat 3 7%nat) 2) (Some 7%nat).
  check_cbn (get_alias nat (repeat_alias nat 3 7%nat) 2) (Some 7%nat).
  check_vm (get (repeat 3 7%nat) 3) (@None nat).
  check_vm (get (repeat 3 7%nat) 18446744073709551615) (@None nat).
  check_vm (set (repeat 3 7%nat) 3 1%nat) (@None (array nat)).
  check_vm (slice (repeat 3 7%nat) 4 0) (@None (array nat)).
  check_vm (slice (repeat 3 7%nat) 1 18446744073709551615)
    (@None (array nat)).
  check_vm (slice (repeat 3 7%nat) 18446744073709551615 2)
    (@None (array nat)).
  check_vm (replace (repeat 3 7%nat) 3 (repeat 1 2%nat))
    (@None (array nat)).
  exact I.
Qed.

Example get_kernel : get (repeat 3 7%nat) 2 = Some 7%nat.
Proof. exact eq_refl. Qed.

Example empty_repeat_kernel : repeat 0 7%nat = empty.
Proof. exact eq_refl. Qed.

Example empty_uninhabited : get (@empty False) 0 = None.
Proof. exact eq_refl. Qed.
Example empty_uninhabited_vm : get (@empty False) 0 = None.
Proof. vm_compute; reflexivity. Qed.

Definition original := Eval vm_compute in repeat 257 7%nat.
Definition altered := Eval vm_compute in
  match set original 128 42%nat with Some a => a | None => empty end.
Definition fragment := Eval vm_compute in
  match slice altered 127 3 with Some a => a | None => empty end.
Definition joined := Eval vm_compute in
  match concat fragment fragment with Some a => a | None => empty end.
Definition replaced := Eval vm_compute in
  match replace original 126 joined with Some a => a | None => empty end.

(* These constants contain serialized literals, exercising their VM compiler
   separately from primitive construction and quotation. *)
Goal True.
Proof.
  check_vm (length original) 257%word64.
  check_vm (get original 128) (Some 7%nat).
  check_vm (get altered 127) (Some 7%nat).
  check_vm (get altered 128) (Some 42%nat).
  check_vm (get altered 129) (Some 7%nat).
  check_vm (length fragment) 3%word64.
  check_vm (get fragment 0) (Some 7%nat).
  check_vm (get fragment 1) (Some 42%nat).
  check_vm (get fragment 2) (Some 7%nat).
  check_vm (length joined) 6%word64.
  check_vm (get joined 4) (Some 42%nat).
  check_vm (length replaced) 257%word64.
  check_vm (get replaced 125) (Some 7%nat).
  check_vm (get replaced 127) (Some 42%nat).
  check_vm (get replaced 130) (Some 42%nat).
  check_vm (get replaced 132) (Some 7%nat).
  check_vm (get original 128) (Some 7%nat).
  exact I.
Qed.

Example empty_end : slice original 257 0 = Some empty.
Proof. vm_compute; reflexivity. Qed.
Example replace_empty : replace original 257 empty = Some original.
Proof. vm_compute; reflexivity. Qed.
Example concat_empty : concat empty original = Some original.
Proof. vm_compute; reflexivity. Qed.
Example concat_empty_right : concat original empty = Some original.
Proof. vm_compute; reflexivity. Qed.

(* Definitional equality is independent of the runtime tree's partition. *)
Example differently_shaped :
  concat (repeat 100 7%nat) (repeat 157 7%nat) = Some original.
Proof. exact eq_refl. Qed.
Example differently_shaped_vm :
  concat (repeat 100 7%nat) (repeat 157 7%nat) = Some original.
Proof. vm_compute; reflexivity. Qed.

Section OpenElements.
  Variable x : nat.
  Goal True.
  Proof.
    check_vm (get (repeat 2 x) 1) (Some x).
    check_cbv (get (repeat 2 x) 1) (Some x).
    check_cbn (get (repeat 2 x) 1) (Some x).
    check_vm (match set (repeat 2 7%nat) 1 x with
              | Some a => get a 1 | None => None end) (Some x).
    exact I.
  Qed.
End OpenElements.

Example under_binder : (fun x : nat => get (repeat 1 x) 0) = @Some nat.
Proof. vm_compute; reflexivity. Qed.

Definition functions := Eval vm_compute in repeat 2 S.
Example function_element :
  match get functions 1 with Some f => f 2%nat | None => 0%nat end = 3%nat.
Proof. vm_compute; reflexivity. Qed.

Definition floats := Eval vm_compute in repeat 2 1.5%float.
Example float_element : get floats 1 = Some 1.5%float.
Proof. vm_compute; reflexivity. Qed.

Definition nested := Eval vm_compute in repeat 2 original.
Example nested_element :
  match get nested 1 with Some a => get a 256 | None => None end = Some 7%nat.
Proof. vm_compute; reflexivity. Qed.

Definition types : array Type := Eval vm_compute in @repeat Type 2 nat.
Example higher_universe : get types 1 = @Some Type nat.
Proof. vm_compute; reflexivity. Qed.

(* Blocked arguments must remain blocked rather than passing an accumulator
   to the OCaml array callbacks. *)
Section Blocked.
  Variable a : array nat.
  Variable i : word64.
  Goal True.
  Proof.
    check_vm (get a 0) (get a 0).
    check_vm (get a i) (get a i).
    check_vm (slice a 0 1) (slice a 0 1).
    check_vm (replace a 0 a) (replace a 0 a).
    check_vm (concat a a) (concat a a).
    exact I.
  Qed.
End Blocked.
