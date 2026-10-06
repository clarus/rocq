(************************************************************************)
(* Logical specification of the trusted primitive array operations.     *)
(* These axioms describe the runtime implementation; importing the       *)
(* executable Array64 API alone does not import any of these axioms.     *)
(************************************************************************)

From Corelib.Array Require Export Array64.

Set Universe Polymorphism.

Axiom length_empty : forall A, length (@empty A) = 0%word64.
Axiom get_empty : forall A i, get (@empty A) i = None.

Axiom length_repeat : forall A n (value : A), length (repeat n value) = n.
Axiom get_repeat : forall A n (value : A) i,
  get (repeat n value) i = if Word64.ltu i n then Some value else None.

Axiom get_in_bounds : forall A (a : array A) i,
  Word64.ltu i (length a) = true -> exists value, get a i = Some value.
Axiom get_out_of_bounds : forall A (a : array A) i,
  Word64.ltu i (length a) = false -> get a i = None.

Axiom set_in_bounds : forall A (a : array A) i value,
  Word64.ltu i (length a) = true -> exists b, set a i value = Some b.
Axiom set_out_of_bounds : forall A (a : array A) i value,
  Word64.ltu i (length a) = false -> set a i value = None.
Axiom length_set : forall A (a b : array A) i value,
  set a i value = Some b -> length b = length a.
Axiom get_set : forall A (a b : array A) i value j,
  set a i value = Some b ->
  get b j = if Word64.eqb j i then Some value else get a j.

Axiom slice_in_bounds : forall A (a : array A) start count,
  range_valid a start count = true ->
  exists b, slice a start count = Some b.
Axiom slice_out_of_bounds : forall A (a : array A) start count,
  range_valid a start count = false -> slice a start count = None.
Axiom length_slice : forall A (a b : array A) start count,
  slice a start count = Some b -> length b = count.
Axiom get_slice : forall A (a b : array A) start count i,
  slice a start count = Some b ->
  get b i = if Word64.ltu i count
    then get a (Word64.add start i) else None.

Axiom replace_in_bounds : forall A (dst src : array A) start,
  range_valid dst start (length src) = true ->
  exists b, replace dst start src = Some b.
Axiom replace_out_of_bounds : forall A (dst src : array A) start,
  range_valid dst start (length src) = false -> replace dst start src = None.
Axiom length_replace : forall A (dst src result : array A) start,
  replace dst start src = Some result -> length result = length dst.
Axiom get_replace : forall A (dst src result : array A) start i,
  replace dst start src = Some result ->
  get result i =
    if Word64.leu start i then
      if Word64.ltu (Word64.sub i start) (length src)
      then get src (Word64.sub i start) else get dst i
    else get dst i.

Definition concat_valid {A} (left right : array A) : bool :=
  Word64.leu (length right)
    (Word64.sub 18446744073709551615%word64 (length left)).

Axiom concat_no_overflow : forall A (left right : array A),
  concat_valid left right = true -> exists b, concat left right = Some b.
Axiom concat_overflow : forall A (left right : array A),
  concat_valid left right = false -> concat left right = None.
Axiom length_concat : forall A (left right result : array A),
  concat left right = Some result ->
  length result = Word64.add (length left) (length right).
Axiom get_concat : forall A (left right result : array A) i,
  concat left right = Some result ->
  get result i = if Word64.ltu i (length left)
    then get left i else get right (Word64.sub i (length left)).

(** No default element or allocation history is observable. *)
Axiom array_ext : forall A (left right : array A),
  length left = length right ->
  (forall i, get left i = get right i) -> left = right.
