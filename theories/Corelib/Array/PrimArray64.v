(************************************************************************)
(* Persistent dense arrays with unsigned 64-bit lengths and indices.     *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Export Word64.

Register option as kernel.ind_option.

Set Universe Polymorphism.

Primitive array := #array64_type.

Primitive empty : forall A, array A := #array64_empty.
Arguments empty {_}.

(** Every element is allocated. Resource exhaustion never truncates the length. *)
Primitive repeat : forall A, word64 -> A -> array A := #array64_repeat.
Arguments repeat {_} _ _.

Primitive length : forall A, array A -> word64 := #array64_length.
Arguments length {_} _.

Primitive get : forall A, array A -> word64 -> option A := #array64_get.
Arguments get {_} _ _.

Primitive set : forall A, array A -> word64 -> A -> option (array A)
  := #array64_set.
Arguments set {_} _ _ _.

(** Ranges are described by a start and a length. Empty ranges at the end
    are valid. All bounds are checked before subtraction or addition. *)
Primitive slice : forall A, array A -> word64 -> word64 -> option (array A)
  := #array64_slice.
Arguments slice {_} _ _ _.

(** Replace exactly the source length, preserving the destination length. *)
Primitive replace : forall A, array A -> word64 -> array A -> option (array A)
  := #array64_replace.
Arguments replace {_} _ _ _.

(** Return [None] if the sum of the two lengths exceeds [2^64 - 1]. *)
Primitive concat : forall A, array A -> array A -> option (array A)
  := #array64_concat.
Arguments concat {_} _ _.

(** Construction used when printing a literal. Printed literals always fit
    the length bound; the overflow branch makes this helper total on arbitrary
    mathematical lists as well. The checked library offers [Array64.of_list]. *)
Fixpoint literal_of_list {A} (values : list A) : array A :=
  match values with
  | nil => empty
  | cons value tail =>
    match concat (repeat 1%word64 value) (literal_of_list tail) with
    | Some a => a
    | None => empty
    end
  end.
Arguments literal_of_list A values : clear implicits.
Register literal_of_list as core.array64.literal_of_list.
