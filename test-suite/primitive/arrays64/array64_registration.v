(* Option registration is part of the trusted primitive-result interface.
   Reject shape, ordering, and universe mismatches before registering the
   ordinary template-polymorphic option type. *)
From Corelib.Numbers.Primitive Require Import Word64.

Module BadOrder.
  Inductive option (A : Type) := None | Some (x : A).
  Fail Register option as kernel.ind_option.
End BadOrder.

Module BadArgument.
  Inductive option (A : Type) := Some (x : list A) | None.
  Fail Register option as kernel.ind_option.
End BadArgument.

Module BadArity.
  Inductive option := Some (x : nat) | None.
  Fail Register option as kernel.ind_option.
End BadArity.

Module BadUniverse.
  Set Universe Polymorphism.
  Inductive option (A : Type) := Some (x : A) | None.
  Fail Register option as kernel.ind_option.
End BadUniverse.

Register option as kernel.ind_option.
From Corelib.Array Require Import PrimArray64.

Example registered_empty : get (@empty False) 0%word64 = None.
Proof. vm_compute; reflexivity. Qed.
Example registered_present : get (repeat 1%word64 7%nat) 0%word64 = Some 7%nat.
Proof. vm_compute; reflexivity. Qed.

(* Array64 is a positive container, while recursive access through [get] is
   deliberately not given a new structural-recursion rule. *)
Inductive tree : Type := Node : array tree -> tree.
Definition leaf : tree := Node empty.
Fail Fixpoint unsupported_array_recursion (t : tree) : nat :=
  match t with
  | Node children =>
    match get children 0%word64 with
    | Some child => unsupported_array_recursion child
    | None => 0%nat
    end
  end.
