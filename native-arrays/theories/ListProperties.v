(************************************************************************)
(* Checked list construction and array/list round trips.                 *)
(************************************************************************)

From Stdlib Require Import ZArith Lia List.
From Rocq.NativeArrays Require Export Array64Laws MapFoldProperties.

Set Universe Polymorphism.
Local Opaque D.unsigned.
Open Scope Z_scope.

Lemma reads_nth_error : forall A (a : array A) count start k,
  0 <= start -> start + Z.of_nat count <= U (length a) ->
  (k < count)%nat ->
  List.nth_error (reads a start count) k = get a (index (start + Z.of_nat k)).
Proof.
  intros A a count. induction count as [|count IH]; intros start k Hstart Hvalid Hk.
  - lia.
  - assert (Hindex : U (index start) = start)
      by (apply index_small; pose proof (range (length a)); lia).
    assert (Hget : W.ltu (index start) (length a) = true)
      by (apply ltu_true; rewrite Hindex; lia).
    destruct (get_in_bounds _ _ _ Hget) as [value Hvalue].
    cbn [reads]. rewrite Hvalue. destruct k as [|k].
    + cbn [List.nth_error]. rewrite Z.add_0_r. symmetry. exact Hvalue.
    + cbn [List.nth_error]. rewrite IH by lia.
      rewrite Nat2Z.inj_succ. f_equal. f_equal. lia.
Qed.

Lemma get_contents : forall A (a : array A) i,
  get a i = List.nth_error (contents a) (Z.to_nat (U i)).
Proof.
  intros A a i. destruct (W.ltu i (length a)) eqn:E.
  - apply ltu_true in E. unfold contents.
    rewrite reads_nth_error.
    + rewrite Z2Nat.id by (apply (proj1 (range _))).
      rewrite Z.add_0_l, index_unsigned. reflexivity.
    + lia.
    + rewrite Z2Nat.id by (apply (proj1 (range _))). lia.
    + apply Z2Nat.inj_lt; try (apply (proj1 (range _))); exact E.
  - rewrite (get_out_of_bounds _ _ _ E). symmetry. apply List.nth_error_None.
    apply ltu_false in E. pose proof (contents_length A a).
    pose proof (Z2Nat.id (U i) (proj1 (range i))). lia.
Qed.

Lemma contents_injective : forall A (a b : array A),
  contents a = contents b -> a = b.
Proof.
  intros A a b H. apply array_ext.
  - apply unsigned_injective. rewrite <- !contents_length. now rewrite H.
  - intro i. rewrite !get_contents. now rewrite H.
Qed.

Lemma of_list_spec : forall A (values : list A) a,
  of_list values = Some a ->
  U (length a) = Z.of_nat (List.length values) /\
  (forall i, get a i = List.nth_error values (Z.to_nat (U i))).
Proof.
  intros A values. induction values as [|value values IH]; intros a H.
  - cbn [of_list] in H. injection H as <-. split.
    + rewrite length_empty, zero. reflexivity.
    + intro i. rewrite get_empty. destruct (Z.to_nat (U i)); reflexivity.
  - cbn [of_list] in H. destruct (of_list values) as [tail|] eqn:Etail; [|discriminate].
    destruct (IH tail eq_refl) as [Hlen Hget].
    pose proof (concat_bounds _ _ _ _ H) as Hbound.
    apply concat_valid_spec in Hbound. rewrite length_repeat, one in Hbound.
    split.
    + rewrite (length_concat _ _ _ _ H), length_repeat.
      rewrite add_small by (rewrite one; exact Hbound).
      rewrite one, Hlen. cbn [List.length]. rewrite Nat2Z.inj_succ. lia.
    + intro i. rewrite (get_concat _ _ _ _ _ H), length_repeat.
      destruct (W.ltu i 1%word64) eqn:Ei.
      * assert (Hz : U i = 0) by
          (apply ltu_true in Ei; rewrite one in Ei; pose proof (range i); lia).
        rewrite get_repeat, Ei, Hz. reflexivity.
      * apply ltu_false in Ei. rewrite one in Ei.
        rewrite Hget, sub_small by (rewrite one; exact Ei).
        rewrite one. replace (Z.to_nat (U i)) with (S (Z.to_nat (U i - 1)))
          by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
        symmetry. apply List.nth_error_cons_succ.
Qed.

Lemma of_list_in_bounds : forall A (values : list A),
  Z.of_nat (List.length values) < modulus -> exists a, of_list values = Some a.
Proof.
  intros A values. induction values as [|value values IH]; intro Hbound.
  - exists empty. reflexivity.
  - cbn [List.length] in Hbound. rewrite Nat2Z.inj_succ in Hbound.
    destruct (IH ltac:(lia)) as [tail Etail].
    cbn [of_list]. rewrite Etail. apply concat_no_overflow, concat_valid_spec.
    rewrite length_repeat, one, (proj1 (of_list_spec _ _ _ Etail)). lia.
Qed.

Lemma of_list_overflow : forall A (values : list A),
  modulus <= Z.of_nat (List.length values) -> of_list values = None.
Proof.
  intros A values Hbound. destruct (of_list values) as [a|] eqn:E; [|reflexivity].
  pose proof (proj1 (of_list_spec _ _ _ E)). pose proof (range (length a)). lia.
Qed.

Lemma of_list_to_list : forall A (values : list A) a,
  of_list values = Some a -> to_list a = values.
Proof.
  intros A values a H. rewrite to_list_contents.
  destruct (of_list_spec _ _ _ H) as [Hlen Hget].
  apply List.nth_error_ext. intro n.
  destruct (Nat.lt_ge_cases n (List.length values)) as [Hn|Hn].
  - assert (Hindex : U (index (Z.of_nat n)) = Z.of_nat n)
      by (apply index_small; pose proof (range (length a)); lia).
    specialize (Hget (index (Z.of_nat n))). rewrite get_contents in Hget.
    rewrite Hindex, Nat2Z.id in Hget. exact Hget.
  - assert (Hcontents : (List.length (contents a) <= n)%nat)
      by (pose proof (contents_length A a); lia).
    apply List.nth_error_None in Hn. apply List.nth_error_None in Hcontents.
    now rewrite Hn, Hcontents.
Qed.

Lemma to_list_of_list : forall A (a : array A), of_list (to_list a) = Some a.
Proof.
  intros A a.
  assert (Hbound : Z.of_nat (List.length (to_list a)) < modulus).
  { rewrite to_list_contents, contents_length. apply (proj2 (range _)). }
  destruct (of_list_in_bounds _ _ Hbound) as [b Hb].
  assert (E : b = a).
  { apply contents_injective. rewrite <- !to_list_contents. now apply of_list_to_list. }
  now subst b.
Qed.
