From Stdlib Require Import List.
From Rocq.PrimitiveWords Require Import PW032Matrix.

Import ListNotations.

Example pw032_fresh_polymorphic_vm :
  pw032_polymorphic_checks =
    [true; true; true; true; true; true; true; true; true; true].
Proof. vm_compute. reflexivity. Qed.

Example pw032_fresh_polymorphic_cbv :
  pw032_polymorphic_checks =
    [true; true; true; true; true; true; true; true; true; true].
Proof. cbv. reflexivity. Qed.

Print Assumptions pw032_fresh_polymorphic_vm.
