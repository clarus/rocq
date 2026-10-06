From Corelib.Array Require Import Array64.

Open Scope word64_scope.
Open Scope list_scope.

Definition sequence :=
  match of_list (0%nat :: 1%nat :: 2%nat :: 3%nat :: 4%nat :: nil) with
  | Some a => a | None => empty
  end.

Definition contents (a : option (array nat)) : option (list nat) :=
  match a with Some a => Some (to_list a) | None => None end.

Example fill_middle :
  contents (fill sequence 1 3 9%nat) =
  Some (0%nat :: 9%nat :: 9%nat :: 9%nat :: 4%nat :: nil).
Proof. vm_compute; reflexivity. Qed.

Example fill_zero_end : fill sequence 5 0 9%nat = Some sequence.
Proof. vm_compute; reflexivity. Qed.

(* Bounds must be rejected before trying to allocate an impossible fill. *)
Example fill_rejects_first :
  fill sequence 0 18446744073709551615 9%nat = None.
Proof. vm_compute; reflexivity. Qed.

Example overlap_right :
  contents (copy_within sequence 0 1 4) =
  Some (0%nat :: 0%nat :: 1%nat :: 2%nat :: 3%nat :: nil).
Proof. vm_compute; reflexivity. Qed.

Example overlap_left :
  contents (copy_within sequence 1 0 4) =
  Some (1%nat :: 2%nat :: 3%nat :: 4%nat :: 4%nat :: nil).
Proof. vm_compute; reflexivity. Qed.

Example blit_distinct :
  contents (blit sequence 1 (repeat 4 9%nat) 1 2) =
  Some (9%nat :: 1%nat :: 2%nat :: 9%nat :: nil).
Proof. vm_compute; reflexivity. Qed.

Example blit_bad_source : blit sequence 4 sequence 0 2 = None.
Proof. vm_compute; reflexivity. Qed.
Example blit_bad_destination : blit sequence 0 sequence 4 2 = None.
Proof. vm_compute; reflexivity. Qed.

Example split_middle :
  match split_at sequence 2 with
  | Some (prefix, suffix) => (to_list prefix, to_list suffix)
  | None => (nil, nil)
  end = (0%nat :: 1%nat :: nil, 2%nat :: 3%nat :: 4%nat :: nil).
Proof. vm_compute; reflexivity. Qed.

Example split_start : split_at sequence 0 = Some (empty, sequence).
Proof. vm_compute; reflexivity. Qed.
Example split_end : split_at sequence 5 = Some (sequence, empty).
Proof. vm_compute; reflexivity. Qed.
Example split_invalid : split_at sequence 6 = None.
Proof. vm_compute; reflexivity. Qed.

Example swap_ends :
  contents (swap sequence 0 4) =
  Some (4%nat :: 1%nat :: 2%nat :: 3%nat :: 0%nat :: nil).
Proof. vm_compute; reflexivity. Qed.
Example swap_same : swap sequence 2 2 = Some sequence.
Proof. vm_compute; reflexivity. Qed.
Example swap_invalid : swap sequence 0 5 = None.
Proof. vm_compute; reflexivity. Qed.

Example push_pop :
  match push sequence 9%nat with Some a => pop a | None => None end =
  Some (sequence, 9%nat).
Proof. vm_compute; reflexivity. Qed.
Example pop_empty : pop (@empty nat) = None.
Proof. vm_compute; reflexivity. Qed.
Example copy_identity : copy sequence = sequence.
Proof. exact eq_refl. Qed.

Example map_successor :
  to_list (map S sequence) = 1%nat :: 2%nat :: 3%nat :: 4%nat :: 5%nat :: nil.
Proof. vm_compute; reflexivity. Qed.
Example fold_left_order :
  fold_left (fun acc x => x :: acc) sequence nil =
  4%nat :: 3%nat :: 2%nat :: 1%nat :: 0%nat :: nil.
Proof. vm_compute; reflexivity. Qed.
Example fold_right_order :
  fold_right (@cons nat) sequence nil =
  0%nat :: 1%nat :: 2%nat :: 3%nat :: 4%nat :: nil.
Proof. vm_compute; reflexivity. Qed.

(* Shared immutable concatenation permits testing unsigned lengths without
   allocating an impossibly large expanded repeat. *)
Fixpoint double_n (n : nat) (a : array nat) : array nat :=
  match n with
  | O => a
  | S n =>
    match concat a a with Some b => double_n n b | None => empty end
  end.

Example high_bit_length :
  length (double_n 63 (repeat 1 7%nat)) = 9223372036854775808.
Proof. vm_compute; reflexivity. Qed.

Example unsigned_get :
  get (double_n 63 (repeat 1 7%nat)) 9223372036854775807 = Some 7%nat.
Proof. vm_compute; reflexivity. Qed.

Example overflowing_concat :
  let a := double_n 63 (repeat 1 7%nat) in
  match concat a a with Some _ => false | None => true end = true.
Proof. vm_compute; reflexivity. Qed.

Example maximum_length :
  let a := double_n 63 (repeat 1 7%nat) in
  match slice a 0 9223372036854775807 with
  | Some b =>
    match concat a b with
    | Some c => (length c, get c 18446744073709551614,
                         get c 18446744073709551615)
    | None => (0%word64, None, None)
    end
  | None => (0%word64, None, None)
  end = (18446744073709551615%word64, Some 7%nat, @None nat).
Proof. vm_compute; reflexivity. Qed.
