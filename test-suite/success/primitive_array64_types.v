(** Registering a primitive option must check constructor order and payloads. *)
Module ReversedOption.
  #[universes(template)]
  Inductive bad_option (A : Type) : Type :=
  | None : bad_option A
  | Some : A -> bad_option A.
  Fail Register bad_option as kernel.ind_option.
End ReversedOption.

Module MissingPayload.
  Inductive bad_option (A : Type) : Type :=
  | Some : bad_option A
  | None : bad_option A.
  Fail Register bad_option as kernel.ind_option.
End MissingPayload.

(** Constructor shapes alone do not justify a primitive signature quantified
    over every element universe. *)
Module FixedUniverseOption.
  #[universes(template=no)]
  Inductive bad_option (A : Type) : Type :=
  | Some : A -> bad_option A
  | None : bad_option A.
  Fail Register bad_option as kernel.ind_option.
End FixedUniverseOption.

Module PropositionOption.
  #[universes(template)]
  Inductive bad_option (A : Type) : Prop :=
  | Some : A -> bad_option A
  | None : bad_option A.
  Fail Register bad_option as kernel.ind_option.
End PropositionOption.

Module CoinductiveOption.
  #[universes(template)]
  CoInductive bad_option (A : Type) : Type :=
  | Some : A -> bad_option A
  | None : bad_option A.
  Fail Register bad_option as kernel.ind_option.
End CoinductiveOption.

(** The standard unconstrained template option is accepted. *)
Register option as kernel.ind_option.

From Corelib.Array Require Import Array64Properties.

Set Universe Polymorphism.

(** Empty arrays require no inhabitant of the element type. *)
Definition empty_false : array False := empty.
Goal get empty_false 0%word64 = None.
Proof. reflexivity. Qed.
Fail Definition impossible : False := get empty_false 0%word64.

(** A parameter-only primitive reduces without forcing its type argument. *)
Goal forall A, length (@empty A) = 0%word64.
Proof. intro A. reflexivity. Qed.
Goal forall A, length (@empty A) = 0%word64.
Proof. intro A. vm_compute. reflexivity. Qed.

Section HigherUniverses.
  Universe u.
  Definition empty_types : array Type@{u} := empty.
  Definition repeated_type (A : Type@{u}) : array Type@{u} := repeat 1%word64 A.

  Goal forall A : Type@{u}, get (repeated_type A) 0%word64 = Some A.
  Proof. intro A. reflexivity. Qed.
  Goal forall A : Type@{u}, get (repeated_type A) 0%word64 = Some A.
  Proof. intro A. vm_compute. reflexivity. Qed.
End HigherUniverses.

(** The arbitrary element argument can remain an accumulator in the VM. *)
Goal forall value : nat, get (repeat 1%word64 value) 0%word64 = Some value.
Proof. intro value. vm_compute. reflexivity. Qed.

Goal get_bounded (repeat 1%word64 7) 0%word64 eq_refl = 7.
Proof. vm_compute. reflexivity. Qed.
Goal get (set_bounded (repeat 1%word64 7) 0%word64 9 eq_refl) 0%word64 = Some 9.
Proof. vm_compute. reflexivity. Qed.
