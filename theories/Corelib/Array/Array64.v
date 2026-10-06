(************************************************************************)
(* Checked operations on persistent arrays and fixed-length slices.     *)
(************************************************************************)

From Corelib.Array Require Export PrimArray64.

Set Universe Polymorphism.

Definition range_valid {A} (a : array A) (start count : word64) : bool :=
  if Word64.leu start (length a)
  then Word64.leu count (Word64.sub (length a) start)
  else false.

Definition is_empty {A} (a : array A) : bool :=
  Word64.eqb (length a) 0%word64.

(** Copies may share immutable storage. *)
Definition copy {A} (a : array A) : array A := a.

(** Check bounds before eagerly allocating the replacement. *)
Definition fill {A} (a : array A) (start count : word64) (value : A)
    : option (array A) :=
  if range_valid a start count
  then replace a start (repeat count value)
  else None.

(** The source is the original snapshot, including overlapping self-copies. *)
Definition blit {A} (src : array A) (src_start : word64)
    (dst : array A) (dst_start count : word64) : option (array A) :=
  if range_valid src src_start count then
    if range_valid dst dst_start count then
      match slice src src_start count with
      | Some part => replace dst dst_start part
      | None => None
      end
    else None
  else None.

Definition copy_within {A} (a : array A) (src_start dst_start count : word64)
    : option (array A) :=
  blit a src_start a dst_start count.

Definition split_at {A} (a : array A) (split_index : word64)
    : option (array A * array A) :=
  match slice a 0%word64 split_index with
  | Some prefix =>
    match slice a split_index (Word64.sub (length a) split_index) with
    | Some suffix => Some (prefix, suffix)
    | None => None
    end
  | None => None
  end.

Definition swap {A} (a : array A) (i j : word64) : option (array A) :=
  match get a i, get a j with
  | Some vi, Some vj =>
    match set a i vj with
    | Some updated => set updated j vi
    | None => None
    end
  | _, _ => None
  end.

Definition push {A} (a : array A) (value : A) : option (array A) :=
  concat a (repeat 1%word64 value).

Definition pop {A} (a : array A) : option (array A * A) :=
  if is_empty a then None else
    let last := Word64.sub (length a) 1%word64 in
    match get a last, slice a 0%word64 last with
    | Some value, Some prefix => Some (prefix, value)
    | _, _ => None
    end.

(** Binary subdivision gives a structural recursion depth of at most 64,
    without converting a length to a host-sized integer or unary natural.
    The fallback branches are unreachable for valid primitive arrays with
    the initial fuel and ranges used by the public functions below. *)
Fixpoint map_range {A B} (fuel : nat) (f : A -> B) (a : array A)
    (start count : word64) : array B :=
  if Word64.eqb count 0%word64 then empty else
  if Word64.eqb count 1%word64 then
    match get a start with
    | Some value => repeat 1%word64 (f value)
    | None => empty
    end
  else match fuel with
  | O => empty
  | S fuel =>
    let left_count := Word64.lsr count 1%word64 in
    let right_count := Word64.sub count left_count in
    let left := map_range fuel f a start left_count in
    let right := map_range fuel f a (Word64.add start left_count) right_count in
    match concat left right with
    | Some result => result
    | None => empty
    end
  end.

Definition map {A B} (f : A -> B) (a : array A) : array B :=
  map_range 64%nat f a 0%word64 (length a).

Fixpoint fold_left_range {A B} (fuel : nat) (f : B -> A -> B)
    (a : array A) (start count : word64) (acc : B) : B :=
  if Word64.eqb count 0%word64 then acc else
  if Word64.eqb count 1%word64 then
    match get a start with Some value => f acc value | None => acc end
  else match fuel with
  | O => acc
  | S fuel =>
    let left_count := Word64.lsr count 1%word64 in
    let right_count := Word64.sub count left_count in
    let acc := fold_left_range fuel f a start left_count acc in
    fold_left_range fuel f a (Word64.add start left_count) right_count acc
  end.

Definition fold_left {A B} (f : B -> A -> B) (a : array A) (acc : B) : B :=
  fold_left_range 64%nat f a 0%word64 (length a) acc.

Fixpoint fold_right_range {A B} (fuel : nat) (f : A -> B -> B)
    (a : array A) (start count : word64) (acc : B) : B :=
  if Word64.eqb count 0%word64 then acc else
  if Word64.eqb count 1%word64 then
    match get a start with Some value => f value acc | None => acc end
  else match fuel with
  | O => acc
  | S fuel =>
    let left_count := Word64.lsr count 1%word64 in
    let right_count := Word64.sub count left_count in
    let acc := fold_right_range fuel f a (Word64.add start left_count) right_count acc in
    fold_right_range fuel f a start left_count acc
  end.

Definition fold_right {A B} (f : A -> B -> B) (a : array A) (acc : B) : B :=
  fold_right_range 64%nat f a 0%word64 (length a) acc.

Definition to_list {A} (a : array A) : list A :=
  fold_right (@cons A) a nil.

Fixpoint of_list {A} (values : list A) : option (array A) :=
  match values with
  | nil => Some empty
  | cons value tail =>
    match of_list tail with
    | Some a => concat (repeat 1%word64 value) a
    | None => None
    end
  end.
