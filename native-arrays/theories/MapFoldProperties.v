(************************************************************************)
(* Binary traversal correctness, derived from the primitive array laws. *)
(************************************************************************)

From Stdlib Require Import ZArith Lia List.
From Corelib.Array Require Import Array64Properties.
From Rocq.NativeArrays Require Import Word64Facts Array64Laws.

Set Universe Polymorphism.
Local Opaque D.unsigned.
Open Scope Z_scope.

Definition index (z : Z) : word64 := D.API.of_Z z.

Lemma index_small : forall z, 0 <= z < modulus -> U (index z) = z.
Proof. intros z H. unfold U, index. rewrite D.of_Z_spec. now apply D.repr_small. Qed.

Lemma index_unsigned : forall i, index (U i) = i.
Proof. intro i. apply unsigned_injective. apply index_small, range. Qed.

(** A conventional list model. It is specification-only: the executable API
    never converts an array length to a unary natural. *)
Fixpoint reads {A} (a : array A) (start : Z) (count : nat) : list A :=
  match count with
  | O => nil
  | S count =>
    match get a (index start) with
    | Some value => value :: reads a (start + 1) count
    | None => reads a (start + 1) count
    end
  end.

Definition contents {A} (a : array A) : list A :=
  reads a 0 (Z.to_nat (U (length a))).

Lemma reads_length : forall A (a : array A) count start,
  0 <= start -> start + Z.of_nat count <= U (length a) ->
  List.length (reads a start count) = count.
Proof.
  intros A a count. induction count as [|count IH]; intros start Hstart Hvalid.
  - reflexivity.
  - rewrite Nat2Z.inj_succ in Hvalid.
    assert (Hindex : U (index start) = start)
      by (apply index_small; pose proof (range (length a)); lia).
    assert (Hget : W.ltu (index start) (length a) = true)
      by (apply ltu_true; rewrite Hindex; lia).
    destruct (get_in_bounds _ _ _ Hget) as [value Hvalue].
    cbn [reads]. rewrite Hvalue. cbn [List.length].
    f_equal. apply IH; lia.
Qed.

Lemma contents_length : forall A (a : array A),
  Z.of_nat (List.length (contents a)) = U (length a).
Proof.
  intros A a. unfold contents. rewrite reads_length.
  - apply Z2Nat.id, (proj1 (range _)).
  - lia.
  - rewrite Z2Nat.id by (apply (proj1 (range _))). lia.
Qed.

Lemma reads_app : forall A (a : array A) n m start,
  reads a start (n + m)%nat =
  reads a start n ++ reads a (start + Z.of_nat n) m.
Proof.
  intros A a n. induction n as [|n IH]; intros m start.
  - cbn. now rewrite Z.add_0_r.
  - cbn [reads Nat.add]. rewrite IH.
    replace (start + Z.of_nat (S n)) with (start + 1 + Z.of_nat n)
      by (rewrite Nat2Z.inj_succ; lia).
    destruct (get a (index start)); reflexivity.
Qed.

Lemma half_bounds : forall count fuel,
  1 < U count -> U count <= D.pow2_nat (S fuel) ->
  let left := W.lsr count 1%word64 in
  let right := W.sub count left in
  0 < U left /\ U left < U count /\
  U right = U count - U left /\
  0 < U right /\ U left <= D.pow2_nat fuel /\ U right <= D.pow2_nat fuel.
Proof.
  intros count fuel Hcount Hfuel. cbv zeta.
  rewrite D.pow2_nat_succ in Hfuel.
  pose proof (Z.div_mod (U count) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (U count) 2 ltac:(lia)) as Hmod.
  assert (Hleft : U (W.lsr count 1%word64) = U count / 2) by apply half.
  assert (Hsub : U (W.sub count (W.lsr count 1%word64)) =
      U count - U (W.lsr count 1%word64)).
  { apply sub_small. rewrite Hleft. lia. }
  rewrite Hsub, Hleft. repeat split; lia.
Qed.

Lemma reads_split : forall A (a : array A) start count left right,
  U count = U left + U right ->
  U start + U left < modulus ->
  reads a (U start) (Z.to_nat (U count)) =
    reads a (U start) (Z.to_nat (U left)) ++
    reads a (U (W.add start left)) (Z.to_nat (U right)).
Proof.
  intros A a start count left right Hsum Hbound.
  rewrite Hsum, Z2Nat.inj_add by (apply (proj1 (range _))).
  rewrite reads_app, Z2Nat.id by (apply (proj1 (range _))).
  now rewrite add_small by assumption.
Qed.

Lemma map_range_spec : forall A B fuel (f : A -> B) a start count,
  U start + U count <= U (length a) ->
  U count <= D.pow2_nat fuel ->
  length (map_range fuel f a start count) = count /\
  (forall i, U i < U count ->
    get (map_range fuel f a start count) i =
      option_map f (get a (W.add start i))).
Proof.
  intros A B fuel. induction fuel as [|fuel IH]; intros f a start count Hvalid Hfuel.
  all: cbn [map_range].
  all: destruct (W.eqb count 0%word64) eqn:Ezero.
  all: try (apply eqb_true in Ezero; subst count; split;
    [apply length_empty | intros i Hi; rewrite zero in Hi; pose proof (range i); lia]).
  all: destruct (W.eqb count 1%word64) eqn:Eone.
  all: try (apply eqb_true in Eone; subst count;
    assert (Hget : W.ltu start (length a) = true)
      by (apply ltu_true; rewrite one in Hvalid; lia);
    destruct (get_in_bounds _ _ _ Hget) as [value Hvalue]; rewrite Hvalue;
    split; [apply length_repeat | intros i Hi;
      assert (Ei : i = 0%word64) by
        (apply unsigned_injective; rewrite zero; rewrite one in Hi; pose proof (range i); lia);
      subst i; rewrite get_repeat, add_zero_right, Hvalue;
      assert (E : W.ltu 0%word64 1%word64 = true)
        by (apply ltu_true; rewrite zero, one; lia);
      now rewrite E]).
  all: assert (Hcount : 1 < U count) by
    (rewrite eqb_value, zero in Ezero; apply Z.eqb_neq in Ezero;
     rewrite eqb_value, one in Eone; apply Z.eqb_neq in Eone;
     pose proof (range count); lia).
  - change (U count <= 1) in Hfuel. lia.
  - pose proof (half_bounds count fuel Hcount Hfuel) as Hparts.
    cbv zeta in Hparts.
    set (left := W.lsr count 1%word64) in *.
    set (right := W.sub count left) in *.
    destruct Hparts as [Hlpos [Hlcount [Hr [Hrpos [Hlfuel Hrfuel]]]]].
    pose proof (range (length a)) as Hlen.
    assert (Hnext : U (W.add start left) = U start + U left)
      by (apply add_small; lia).
    destruct (IH f a start left ltac:(lia) Hlfuel) as [Hl Hgl].
    destruct (IH f a (W.add start left) right ltac:(rewrite Hnext; lia) Hrfuel)
      as [Hrlen Hgr].
    assert (Hconcat : concat_valid (map_range fuel f a start left)
        (map_range fuel f a (W.add start left) right) = true).
    { apply concat_valid_spec. rewrite Hl, Hrlen. pose proof (range count). lia. }
    destruct (concat_no_overflow _ _ _ Hconcat) as [result Hresult].
    rewrite Hresult. split.
    + rewrite (length_concat _ _ _ _ Hresult), Hl, Hrlen.
      apply unsigned_injective. rewrite add_small by (pose proof (range count); lia). lia.
    + intros i Hi. rewrite (get_concat _ _ _ _ _ Hresult), Hl.
      destruct (W.ltu i left) eqn:Eleft.
      * apply ltu_true in Eleft. apply Hgl. exact Eleft.
      * apply ltu_false in Eleft.
        assert (Hoffset : U (W.sub i left) = U i - U left) by now apply sub_small.
        rewrite Hgr by (rewrite Hoffset; lia).
        assert (Eindex : W.add (W.add start left) (W.sub i left) = W.add start i).
        { assert (Hsi : U start + U i < modulus) by lia.
          assert (Hni : U (W.add start left) + U (W.sub i left) < modulus)
            by (rewrite Hnext, Hoffset; lia).
          apply unsigned_injective.
          rewrite (add_small _ _ Hni), (add_small _ _ Hsi), Hnext, Hoffset. lia. }
        now rewrite Eindex.
Qed.

Lemma length_map : forall A B (f : A -> B) (a : array A),
  length (map f a) = length a.
Proof.
  intros A B f a. unfold map.
  apply (proj1 (map_range_spec A B 64%nat f a 0%word64 (length a)
    ltac:(rewrite zero; lia)
    ltac:(change (U (length a) <= modulus); pose proof (range (length a)); lia))).
Qed.

Lemma get_map : forall A B (f : A -> B) (a : array A) i,
  get (map f a) i = option_map f (get a i).
Proof.
  intros A B f a i. destruct (W.ltu i (length a)) eqn:E.
  - apply ltu_true in E.
    assert (Hvalid : U 0%word64 + U (length a) <= U (length a)) by (rewrite zero; lia).
    assert (Hfuel : U (length a) <= D.pow2_nat 64%nat)
      by (change (U (length a) <= modulus); pose proof (range (length a)); lia).
    pose proof (proj2 (map_range_spec A B 64%nat f a 0%word64 (length a) Hvalid Hfuel) i E) as H.
    rewrite add_zero_left in H. exact H.
  - rewrite (get_out_of_bounds _ a i E).
    rewrite get_out_of_bounds; [reflexivity|]. now rewrite length_map.
Qed.

Lemma reads_map : forall A B (f : A -> B) (a : array A) start count,
  reads (map f a) start count = List.map f (reads a start count).
Proof.
  intros A B f a start count. revert start. induction count; intro start; cbn [reads].
  - reflexivity.
  - rewrite get_map, IHcount. destruct (get a (index start)); reflexivity.
Qed.

Lemma contents_map : forall A B (f : A -> B) (a : array A),
  contents (map f a) = List.map f (contents a).
Proof. intros. unfold contents. rewrite length_map. apply reads_map. Qed.

Lemma fold_left_range_spec : forall A B fuel (f : B -> A -> B) a start count acc,
  U start + U count <= U (length a) ->
  U count <= D.pow2_nat fuel ->
  fold_left_range fuel f a start count acc =
    List.fold_left f (reads a (U start) (Z.to_nat (U count))) acc.
Proof.
  intros A B fuel. induction fuel as [|fuel IH]; intros f a start count acc Hvalid Hfuel.
  all: cbn [fold_left_range].
  all: destruct (W.eqb count 0%word64) eqn:Ezero.
  all: try (apply eqb_true in Ezero; subst count; rewrite zero; reflexivity).
  all: destruct (W.eqb count 1%word64) eqn:Eone.
  all: tryif apply eqb_true in Eone then
    (subst count; rewrite one; replace (Z.to_nat 1) with 1%nat by reflexivity; cbn [reads];
     rewrite index_unsigned; destruct (get a start); reflexivity) else idtac.
  all: assert (Hcount : 1 < U count) by
    (rewrite eqb_value, zero in Ezero; apply Z.eqb_neq in Ezero;
     rewrite eqb_value, one in Eone; apply Z.eqb_neq in Eone;
     pose proof (range count); lia).
  - change (U count <= 1) in Hfuel. lia.
  - pose proof (half_bounds count fuel Hcount Hfuel) as Hparts.
    cbv zeta in Hparts.
    set (left := W.lsr count 1%word64) in *.
    set (right := W.sub count left) in *.
    destruct Hparts as [Hlpos [Hlcount [Hr [Hrpos [Hlfuel Hrfuel]]]]].
    pose proof (range (length a)) as Hlen.
    assert (Hnext : U (W.add start left) = U start + U left)
      by (apply add_small; lia).
    rewrite (IH f a start left acc ltac:(lia) Hlfuel).
    rewrite (IH f a (W.add start left) right _ ltac:(rewrite Hnext; lia) Hrfuel).
    rewrite (reads_split _ _ start count left right ltac:(lia) ltac:(lia)).
    now rewrite List.fold_left_app.
Qed.

Lemma fold_right_range_spec : forall A B fuel (f : A -> B -> B) a start count acc,
  U start + U count <= U (length a) ->
  U count <= D.pow2_nat fuel ->
  fold_right_range fuel f a start count acc =
    List.fold_right f acc (reads a (U start) (Z.to_nat (U count))).
Proof.
  intros A B fuel. induction fuel as [|fuel IH]; intros f a start count acc Hvalid Hfuel.
  all: cbn [fold_right_range].
  all: destruct (W.eqb count 0%word64) eqn:Ezero.
  all: try (apply eqb_true in Ezero; subst count; rewrite zero; reflexivity).
  all: destruct (W.eqb count 1%word64) eqn:Eone.
  all: tryif apply eqb_true in Eone then
    (subst count; rewrite one; replace (Z.to_nat 1) with 1%nat by reflexivity; cbn [reads];
     rewrite index_unsigned; destruct (get a start); reflexivity) else idtac.
  all: assert (Hcount : 1 < U count) by
    (rewrite eqb_value, zero in Ezero; apply Z.eqb_neq in Ezero;
     rewrite eqb_value, one in Eone; apply Z.eqb_neq in Eone;
     pose proof (range count); lia).
  - change (U count <= 1) in Hfuel. lia.
  - pose proof (half_bounds count fuel Hcount Hfuel) as Hparts.
    cbv zeta in Hparts.
    set (left := W.lsr count 1%word64) in *.
    set (right := W.sub count left) in *.
    destruct Hparts as [Hlpos [Hlcount [Hr [Hrpos [Hlfuel Hrfuel]]]]].
    pose proof (range (length a)) as Hlen.
    assert (Hnext : U (W.add start left) = U start + U left)
      by (apply add_small; lia).
    rewrite (IH f a (W.add start left) right acc ltac:(rewrite Hnext; lia) Hrfuel).
    rewrite (IH f a start left _ ltac:(lia) Hlfuel).
    rewrite (reads_split _ _ start count left right ltac:(lia) ltac:(lia)).
    now rewrite List.fold_right_app.
Qed.

Lemma fold_left_contents : forall A B (f : B -> A -> B) (a : array A) acc,
  fold_left f a acc = List.fold_left f (contents a) acc.
Proof.
  intros A B f a acc. unfold fold_left, contents.
  rewrite fold_left_range_spec.
  - now rewrite zero.
  - rewrite zero. lia.
  - change (U (length a) <= modulus). pose proof (range (length a)); lia.
Qed.

Lemma fold_right_contents : forall A B (f : A -> B -> B) (a : array A) acc,
  fold_right f a acc = List.fold_right f acc (contents a).
Proof.
  intros A B f a acc. unfold fold_right, contents.
  rewrite fold_right_range_spec.
  - now rewrite zero.
  - rewrite zero. lia.
  - change (U (length a) <= modulus). pose proof (range (length a)); lia.
Qed.

Lemma to_list_contents : forall A (a : array A), to_list a = contents a.
Proof.
  intros A a. unfold to_list. rewrite fold_right_contents.
  induction (contents a); cbn; congruence.
Qed.
