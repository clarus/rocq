(************************************************************************)
(* Derived laws, proved from the explicitly imported primitive axioms.   *)
(************************************************************************)

From Corelib.Array Require Export Array64Axioms.

Set Universe Polymorphism.

(** Optional proof-oriented accessors. Successful computation is the same
    primitive lookup/update; the bound proof rules out the [None] branch. *)
Definition get_bounded_result {A} (a : array A) i
    (bound : Word64.ltu i (length a) = true)
    : { value : A | get a i = Some value }.
Proof.
  destruct (get a i) as [value|] eqn:Hget.
  - exists value. reflexivity.
  - exfalso. destruct (get_in_bounds _ _ _ bound) as [value Hvalue].
    rewrite Hget in Hvalue. discriminate.
Defined.

Definition get_bounded {A} (a : array A) i
    (bound : Word64.ltu i (length a) = true) : A :=
  proj1_sig (get_bounded_result a i bound).

Lemma get_bounded_spec : forall A (a : array A) i bound,
  get a i = Some (get_bounded a i bound).
Proof. intros. apply (proj2_sig (get_bounded_result a i bound)). Qed.

Definition set_bounded_result {A} (a : array A) i value
    (bound : Word64.ltu i (length a) = true)
    : { result : array A | set a i value = Some result }.
Proof.
  destruct (set a i value) as [result|] eqn:Hset.
  - exists result. reflexivity.
  - exfalso. destruct (set_in_bounds _ _ _ value bound) as [result Hresult].
    rewrite Hset in Hresult. discriminate.
Defined.

Definition set_bounded {A} (a : array A) i value
    (bound : Word64.ltu i (length a) = true) : array A :=
  proj1_sig (set_bounded_result a i value bound).

Lemma set_bounded_spec : forall A (a : array A) i value bound,
  set a i value = Some (set_bounded a i value bound).
Proof. intros. apply (proj2_sig (set_bounded_result a i value bound)). Qed.

Lemma copy_eq : forall A (a : array A), copy a = a.
Proof. reflexivity. Qed.

Lemma get_bounds : forall A (a : array A) i value,
  get a i = Some value -> Word64.ltu i (length a) = true.
Proof.
  intros A a i value H. destruct (Word64.ltu i (length a)) eqn:E; [reflexivity|].
  rewrite (get_out_of_bounds _ _ _ E) in H. discriminate.
Qed.

Lemma set_bounds : forall A (a b : array A) i value,
  set a i value = Some b -> Word64.ltu i (length a) = true.
Proof.
  intros A a b i value H. destruct (Word64.ltu i (length a)) eqn:E; [reflexivity|].
  rewrite (set_out_of_bounds _ _ _ _ E) in H. discriminate.
Qed.

Lemma slice_bounds : forall A (a b : array A) start count,
  slice a start count = Some b -> range_valid a start count = true.
Proof.
  intros A a b start count H. destruct (range_valid a start count) eqn:E; [reflexivity|].
  rewrite (slice_out_of_bounds _ _ _ _ E) in H. discriminate.
Qed.

Lemma replace_bounds : forall A (dst src result : array A) start,
  replace dst start src = Some result -> range_valid dst start (length src) = true.
Proof.
  intros A dst src result start H.
  destruct (range_valid dst start (length src)) eqn:E; [reflexivity|].
  rewrite (replace_out_of_bounds _ _ _ _ E) in H. discriminate.
Qed.

Lemma concat_bounds : forall A (left right result : array A),
  concat left right = Some result -> concat_valid left right = true.
Proof.
  intros A left right result H. destruct (concat_valid left right) eqn:E; [reflexivity|].
  rewrite (concat_overflow _ _ _ E) in H. discriminate.
Qed.

Lemma fill_out_of_bounds : forall A (a : array A) start count value,
  range_valid a start count = false -> fill a start count value = None.
Proof. intros A a start count value H. unfold fill. rewrite H. reflexivity. Qed.

Lemma fill_in_bounds : forall A (a : array A) start count value,
  range_valid a start count = true ->
  exists b, fill a start count value = Some b.
Proof.
  intros A a start count value H. unfold fill. rewrite H.
  apply replace_in_bounds. rewrite length_repeat. exact H.
Qed.

Lemma length_fill : forall A (a b : array A) start count value,
  fill a start count value = Some b -> length b = length a.
Proof.
  intros A a b start count value H. unfold fill in H.
  destruct (range_valid a start count); [eapply length_replace; exact H | discriminate].
Qed.

Lemma get_fill : forall A (a b : array A) start count value i,
  fill a start count value = Some b ->
  get b i =
    if Word64.leu start i then
      if Word64.ltu (Word64.sub i start) count then Some value else get a i
    else get a i.
Proof.
  intros A a b start count value i H. unfold fill in H.
  destruct (range_valid a start count); [|discriminate].
  rewrite (get_replace _ _ _ _ _ _ H), length_repeat, get_repeat.
  destruct (Word64.leu start i); [destruct (Word64.ltu (Word64.sub i start) count)|]; reflexivity.
Qed.

Lemma blit_out_of_source : forall A (src dst : array A) src_start dst_start count,
  range_valid src src_start count = false ->
  blit src src_start dst dst_start count = None.
Proof.
  intros A src dst src_start dst_start count H. unfold blit. rewrite H. reflexivity.
Qed.

Lemma blit_out_of_destination : forall A (src dst : array A) src_start dst_start count,
  range_valid dst dst_start count = false ->
  blit src src_start dst dst_start count = None.
Proof.
  intros A src dst src_start dst_start count H. unfold blit. rewrite H.
  destruct (range_valid src src_start count); reflexivity.
Qed.

Lemma blit_in_bounds : forall A (src dst : array A) src_start dst_start count,
  range_valid src src_start count = true ->
  range_valid dst dst_start count = true ->
  exists b, blit src src_start dst dst_start count = Some b.
Proof.
  intros A src dst src_start dst_start count Hsrc Hdst.
  unfold blit. rewrite Hsrc, Hdst.
  destruct (slice_in_bounds _ _ _ _ Hsrc) as [part Hpart]. rewrite Hpart.
  apply replace_in_bounds. rewrite (length_slice _ _ _ _ _ Hpart). exact Hdst.
Qed.

Lemma length_blit : forall A (src dst result : array A) src_start dst_start count,
  blit src src_start dst dst_start count = Some result ->
  length result = length dst.
Proof.
  intros A src dst result src_start dst_start count H. unfold blit in H.
  destruct (range_valid src src_start count); [|discriminate].
  destruct (range_valid dst dst_start count); [|discriminate].
  destruct (slice src src_start count) as [part|]; [|discriminate].
  eapply length_replace. exact H.
Qed.

Lemma get_blit : forall A (src dst result : array A) src_start dst_start count i,
  blit src src_start dst dst_start count = Some result ->
  get result i =
    if Word64.leu dst_start i then
      if Word64.ltu (Word64.sub i dst_start) count
      then get src (Word64.add src_start (Word64.sub i dst_start)) else get dst i
    else get dst i.
Proof.
  intros A src dst result src_start dst_start count i H. unfold blit in H.
  destruct (range_valid src src_start count); [|discriminate].
  destruct (range_valid dst dst_start count); [|discriminate].
  destruct (slice src src_start count) as [part|] eqn:Hpart; [|discriminate].
  rewrite (get_replace _ _ _ _ _ _ H), (length_slice _ _ _ _ _ Hpart).
  rewrite (get_slice _ _ _ _ _ _ Hpart).
  destruct (Word64.leu dst_start i); [destruct (Word64.ltu (Word64.sub i dst_start) count)|]; reflexivity.
Qed.

Lemma length_copy_within : forall A (a result : array A) src_start dst_start count,
  copy_within a src_start dst_start count = Some result ->
  length result = length a.
Proof. intros A a result src_start dst_start count. apply length_blit. Qed.

Lemma split_at_parts : forall A (a left right : array A) split_index,
  split_at a split_index = Some (left, right) ->
  slice a 0%word64 split_index = Some left /\
  slice a split_index (Word64.sub (length a) split_index) = Some right.
Proof.
  intros A a left right split_index H. unfold split_at in H.
  destruct (slice a 0%word64 split_index) as [l|] eqn:Hl; [|discriminate].
  destruct (slice a split_index (Word64.sub (length a) split_index)) as [r|] eqn:Hr; [|discriminate].
  inversion H; subst. split; reflexivity.
Qed.

Lemma length_split_at : forall A (a left right : array A) split_index,
  split_at a split_index = Some (left, right) ->
  length left = split_index /\ length right = Word64.sub (length a) split_index.
Proof.
  intros A a left right split_index H. destruct (split_at_parts _ _ _ _ _ H) as [Hl Hr].
  split; eapply length_slice; eassumption.
Qed.

Lemma length_swap : forall A (a result : array A) i j,
  swap a i j = Some result -> length result = length a.
Proof.
  intros A a result i j H. unfold swap in H.
  destruct (get a i) as [vi|]; [|discriminate].
  destruct (get a j) as [vj|]; [|discriminate].
  destruct (set a i vj) as [updated|] eqn:Hupdated; [|discriminate].
  rewrite (length_set _ _ _ _ _ H), (length_set _ _ _ _ _ Hupdated).
  reflexivity.
Qed.

Lemma get_swap : forall A (a result : array A) i j k,
  swap a i j = Some result ->
  get result k = if Word64.eqb k j then get a i
    else if Word64.eqb k i then get a j else get a k.
Proof.
  intros A a result i j k H. unfold swap in H.
  destruct (get a i) as [vi|] eqn:Hi; [|discriminate].
  destruct (get a j) as [vj|] eqn:Hj; [|discriminate].
  destruct (set a i vj) as [updated|] eqn:Hupdated; [|discriminate].
  rewrite (get_set _ _ _ _ _ _ H), (get_set _ _ _ _ _ _ Hupdated).
  reflexivity.
Qed.

Lemma length_push : forall A (a result : array A) value,
  push a value = Some result -> length result = Word64.add (length a) 1%word64.
Proof.
  intros A a result value H. unfold push in H.
  rewrite (length_concat _ _ _ _ H), length_repeat. reflexivity.
Qed.

Lemma pop_parts : forall A (a prefix : array A) value,
  pop a = Some (prefix, value) ->
  get a (Word64.sub (length a) 1%word64) = Some value /\
  slice a 0%word64 (Word64.sub (length a) 1%word64) = Some prefix.
Proof.
  intros A a prefix value H. unfold pop in H.
  destruct (is_empty a); [discriminate|].
  destruct (get a (Word64.sub (length a) 1%word64)) as [v|] eqn:Hv; [|discriminate].
  destruct (slice a 0%word64 (Word64.sub (length a) 1%word64)) as [p|] eqn:Hp; [|discriminate].
  inversion H; subst. split; reflexivity.
Qed.

Lemma length_pop : forall A (a prefix : array A) value,
  pop a = Some (prefix, value) ->
  length prefix = Word64.sub (length a) 1%word64.
Proof.
  intros A a prefix value H. destruct (pop_parts _ _ _ _ H) as [_ Hp].
  eapply length_slice. exact Hp.
Qed.
