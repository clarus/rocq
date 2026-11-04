(************************************************************************)
(* Structural slice laws derived from primitive array and Word64 laws.  *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Corelib.Array Require Export Array64Properties.
From Rocq.NativeArrays Require Export Word64Facts.

Set Universe Polymorphism.
Open Scope Z_scope.

Lemma range_valid_spec : forall A (a : array A) start count,
  range_valid a start count = true <-> U start + U count <= U (length a).
Proof.
  intros A a start count. unfold range_valid.
  destruct (W.leu start (length a)) eqn:Hstart.
  - apply leu_true in Hstart. rewrite leu_true, sub_small by assumption. lia.
  - apply leu_false in Hstart. pose proof (range count).
    split; [discriminate|lia].
Qed.

Lemma concat_valid_spec : forall A (left right : array A),
  concat_valid left right = true <->
  U (length left) + U (length right) < modulus.
Proof.
  intros A left right. unfold concat_valid. rewrite leu_true.
  rewrite sub_small, maximum; [lia|].
  rewrite maximum. pose proof (range (length left)). lia.
Qed.

Lemma get_outside : forall A (a : array A) i,
  U (length a) <= U i -> get a i = None.
Proof. intros A a i H. apply get_out_of_bounds. apply ltu_false. exact H. Qed.

Lemma slice_whole : forall A (a : array A),
  slice a 0%word64 (length a) = Some a.
Proof.
  intros A a.
  assert (Hv : range_valid a 0%word64 (length a) = true).
  { apply range_valid_spec. rewrite zero. lia. }
  destruct (slice_in_bounds _ _ _ _ Hv) as [b Hb].
  assert (Hb' : b = a).
  { apply array_ext.
    - eapply length_slice. exact Hb.
    - intro i. rewrite (get_slice _ _ _ _ _ _ Hb), add_zero_left.
      destruct (W.ltu i (length a)) eqn:Hi; [reflexivity|].
      symmetry. apply get_out_of_bounds. exact Hi. }
  now subst b.
Qed.

Lemma slice_zero : forall A (a : array A) start,
  U start <= U (length a) -> slice a start 0%word64 = Some empty.
Proof.
  intros A a start H.
  assert (Hv : range_valid a start 0%word64 = true).
  { apply range_valid_spec. rewrite zero. lia. }
  destruct (slice_in_bounds _ _ _ _ Hv) as [b Hb].
  assert (Hb' : b = @empty A).
  { apply array_ext.
    - rewrite length_empty. eapply length_slice. exact Hb.
    - intro i. rewrite (get_slice _ _ _ _ _ _ Hb), get_empty.
      destruct (W.ltu i 0%word64) eqn:Hi; [|reflexivity].
      apply ltu_true in Hi. rewrite zero in Hi. pose proof (range i). lia. }
  now subst b.
Qed.

Lemma replace_slice_identity : forall A (a part result : array A) start count,
  slice a start count = Some part ->
  replace a start part = Some result -> result = a.
Proof.
  intros A a part result start count Hslice Hreplace. apply array_ext.
  - eapply length_replace. exact Hreplace.
  - intro i. rewrite (get_replace _ _ _ _ _ _ Hreplace).
    rewrite (length_slice _ _ _ _ _ Hslice).
    destruct (W.leu start i) eqn:Hstart; [|reflexivity].
    destruct (W.ltu (W.sub i start) count) eqn:Hi; [|reflexivity].
    rewrite (get_slice _ _ _ _ _ _ Hslice), Hi.
    rewrite add_sub_cancel; [reflexivity|]. apply leu_true. exact Hstart.
Qed.

Lemma replace_slice : forall A (a part : array A) start count,
  slice a start count = Some part -> replace a start part = Some a.
Proof.
  intros A a part start count Hslice.
  assert (Hv : range_valid a start (length part) = true).
  { rewrite (length_slice _ _ _ _ _ Hslice). eapply slice_bounds. exact Hslice. }
  destruct (replace_in_bounds _ _ _ _ Hv) as [b Hb].
  rewrite (replace_slice_identity _ _ _ _ _ _ Hslice Hb) in Hb. exact Hb.
Qed.

Lemma slice_nested : forall A (a part result : array A) start count offset amount,
  slice a start count = Some part ->
  slice part offset amount = Some result ->
  slice a (W.add start offset) amount = Some result.
Proof.
  intros A a part result start count offset amount Hp Hr.
  pose proof (slice_bounds _ _ _ _ _ Hp) as Hpr.
  pose proof (slice_bounds _ _ _ _ _ Hr) as Hrr.
  apply range_valid_spec in Hpr. apply range_valid_spec in Hrr.
  rewrite (length_slice _ _ _ _ _ Hp) in Hrr.
  pose proof (range (length a)) as Ha.
  pose proof (range start) as Hs.
  pose proof (range offset) as Ho.
  pose proof (range amount) as Hm.
  assert (Hso : U start + U offset < modulus) by lia.
  assert (Hv : range_valid a (W.add start offset) amount = true).
  { apply range_valid_spec. rewrite add_small by exact Hso. lia. }
  destruct (slice_in_bounds _ _ _ _ Hv) as [b Hb].
  assert (Hb' : b = result).
  { apply array_ext.
    - rewrite (length_slice _ _ _ _ _ Hb), (length_slice _ _ _ _ _ Hr). reflexivity.
    - intro i. rewrite (get_slice _ _ _ _ _ _ Hb), (get_slice _ _ _ _ _ _ Hr).
      destruct (W.ltu i amount) eqn:Hi; [|reflexivity].
      apply ltu_true in Hi. pose proof (range i) as Hir.
      assert (Hoi : U offset + U i < modulus) by lia.
      assert (Hinside : W.ltu (W.add offset i) count = true).
      { apply ltu_true. rewrite add_small by exact Hoi. lia. }
      rewrite (get_slice _ _ _ _ _ _ Hp), Hinside.
      rewrite add_assoc_small; [reflexivity|lia]. }
  now subst b.
Qed.

Lemma replace_disjoint_commute : forall A
    (a first second a_first a_second left right : array A) start_first start_second,
  U start_first + U (length first) <= U start_second ->
  replace a start_first first = Some a_first ->
  replace a start_second second = Some a_second ->
  replace a_first start_second second = Some left ->
  replace a_second start_first first = Some right ->
  left = right.
Proof.
  intros A a first second a_first a_second left right sf ss Hdisjoint Hf Hs Hl Hr.
  apply array_ext.
  - rewrite (length_replace _ _ _ _ _ Hl), (length_replace _ _ _ _ _ Hr).
    rewrite (length_replace _ _ _ _ _ Hf), (length_replace _ _ _ _ _ Hs). reflexivity.
  - intro i. rewrite (get_replace _ _ _ _ _ _ Hl), (get_replace _ _ _ _ _ _ Hr).
    rewrite (get_replace _ _ _ _ _ _ Hf), (get_replace _ _ _ _ _ _ Hs).
    destruct (W.leu sf i) eqn:Hfi; destruct (W.leu ss i) eqn:Hsi;
      destruct (W.ltu (W.sub i sf) (length first)) eqn:Hif;
      destruct (W.ltu (W.sub i ss) (length second)) eqn:His;
      try reflexivity.
    apply leu_true in Hfi. apply leu_true in Hsi. apply ltu_true in Hif.
    rewrite sub_small in Hif by exact Hfi. lia.
Qed.

Lemma replace_same_range : forall A
    (a first second a_first left right : array A) start,
  length first = length second ->
  replace a start first = Some a_first ->
  replace a_first start second = Some left ->
  replace a start second = Some right -> left = right.
Proof.
  intros A a first second a_first left right start Hlength Hfirst Hleft Hright.
  apply array_ext.
  - rewrite (length_replace _ _ _ _ _ Hleft), (length_replace _ _ _ _ _ Hright).
    eapply length_replace. exact Hfirst.
  - intro i. rewrite (get_replace _ _ _ _ _ _ Hleft), (get_replace _ _ _ _ _ _ Hright).
    rewrite (get_replace _ _ _ _ _ _ Hfirst), Hlength.
    destruct (W.leu start i); destruct (W.ltu (W.sub i start) (length second)); reflexivity.
Qed.

Lemma slice_replace : forall A (a source result : array A) start,
  replace a start source = Some result ->
  slice result start (length source) = Some source.
Proof.
  intros A a source result start Hreplace.
  pose proof (replace_bounds _ _ _ _ _ Hreplace) as Hbounds.
  assert (Hvalid : range_valid result start (length source) = true).
  { unfold range_valid in *. rewrite (length_replace _ _ _ _ _ Hreplace). exact Hbounds. }
  destruct (slice_in_bounds _ _ _ _ Hvalid) as [part Hpart].
  apply range_valid_spec in Hbounds.
  pose proof (range (length a)) as Ha.
  assert (Hpart' : part = source).
  { apply array_ext.
    - eapply length_slice. exact Hpart.
    - intro i. rewrite (get_slice _ _ _ _ _ _ Hpart).
      destruct (W.ltu i (length source)) eqn:Hi.
      + apply ltu_true in Hi. pose proof (range i) as Hir. pose proof (range start) as Hsr.
        assert (Hadd : U start + U i < modulus) by lia.
        assert (Hstart : W.leu start (W.add start i) = true).
        { apply leu_true. rewrite add_small by exact Hadd. lia. }
        rewrite (get_replace _ _ _ _ _ _ Hreplace), Hstart.
        rewrite sub_add_cancel by exact Hadd.
        assert (Hi' : W.ltu i (length source) = true) by (apply ltu_true; exact Hi).
        rewrite Hi'. reflexivity.
      + symmetry. apply get_out_of_bounds. exact Hi. }
  now subst part.
Qed.

Lemma split_at_reassemble : forall A (a left right : array A) split_index,
  split_at a split_index = Some (left, right) -> concat left right = Some a.
Proof.
  intros A a left right split_index Hsplit.
  destruct (split_at_parts _ _ _ _ _ Hsplit) as [Hl Hr].
  pose proof (slice_bounds _ _ _ _ _ Hl) as Hb.
  apply range_valid_spec in Hb. rewrite zero in Hb.
  pose proof (range (length a)) as Ha.
  assert (Hvalid : concat_valid left right = true).
  { apply concat_valid_spec.
    rewrite (length_slice _ _ _ _ _ Hl), (length_slice _ _ _ _ _ Hr).
    rewrite sub_small by lia. lia. }
  destruct (concat_no_overflow _ _ _ Hvalid) as [result Hresult].
  assert (Heq : result = a).
  { apply array_ext.
    - rewrite (length_concat _ _ _ _ Hresult).
      rewrite (length_slice _ _ _ _ _ Hl), (length_slice _ _ _ _ _ Hr).
      apply add_sub_cancel. lia.
    - intro i. rewrite (get_concat _ _ _ _ _ Hresult).
      rewrite (length_slice _ _ _ _ _ Hl).
      destruct (W.ltu i split_index) eqn:Hi.
      + rewrite (get_slice _ _ _ _ _ _ Hl), Hi, add_zero_left. reflexivity.
      + apply ltu_false in Hi.
        rewrite (get_slice _ _ _ _ _ _ Hr).
        destruct (W.ltu (W.sub i split_index) (W.sub (length a) split_index)) eqn:Hright.
        * rewrite add_sub_cancel by exact Hi. reflexivity.
        * apply ltu_false in Hright.
          rewrite !sub_small in Hright by lia.
          symmetry. apply get_outside. lia. }
  now subst result.
Qed.
