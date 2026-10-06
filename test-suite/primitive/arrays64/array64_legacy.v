From Corelib.Numbers.Cyclic.Int63 Require Import PrimInt63.
From Corelib.Array Require Import PrimArray PrimArray64.

Definition legacy := Eval vm_compute in PrimArray.make 3%uint63 7%nat.

Definition legacy_observation :=
  let updated := PrimArray.set legacy 1%uint63 9%nat in
  (PrimArray.length updated, PrimArray.get updated 1%uint63,
   PrimArray.get legacy 1%uint63, PrimArray.get updated 3%uint63,
   PrimArray.default updated).

Goal legacy_observation = (3%uint63, 9%nat, 7%nat, 7%nat, 7%nat).
Proof. vm_compute; reflexivity. Qed.
Goal legacy_observation = (3%uint63, 9%nat, 7%nat, 7%nat, 7%nat).
Proof. cbv; reflexivity. Qed.
Goal legacy_observation = (3%uint63, 9%nat, 7%nat, 7%nat, 7%nat).
Proof. cbn; reflexivity. Qed.

(* Both VM array representations can occur inside each other. *)
Definition old_in_new := Eval vm_compute in repeat 2%word64 legacy.
Definition new_in_old := Eval vm_compute in
  PrimArray.make 2%uint63 (repeat 3%word64 11%nat).

Goal (match get old_in_new 1%word64 with
      | Some a => Some (PrimArray.get a 0%uint63)
      | None => None end) = Some 7%nat.
Proof. vm_compute; reflexivity. Qed.
Goal get (PrimArray.get new_in_old 1%uint63) 2%word64 = Some 11%nat.
Proof. vm_compute; reflexivity. Qed.

(* The old limit is unchanged; Array64 has its own length semantics. *)
Goal PrimArray.max_length = 4194303%uint63.
Proof. exact eq_refl. Qed.
