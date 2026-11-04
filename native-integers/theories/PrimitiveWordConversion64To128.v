(************************************************************************)
(* Observable conversion proofs with Word64 as the smaller width.      *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Rocq.PrimitiveWords Require Import
  PrimitiveWordSpec PrimitiveWordDerived PrimitiveWordBounds Conversions
  Word8 Word16 Word32 Word64 Word128 Word256.
Open Scope Z_scope.

Opaque Word8.to_N Word16.to_N Word32.to_N Word64.to_N
  Word128.to_N Word256.to_N.

Lemma zero_extend_64_128_spec : forall x,
    Word128Derived.unsigned (zero_extend_64_128 x) = Word64Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_64_128.
  transitivity (repr Word128Derived.P (Z.of_N (Word64.to_N x))).
  - apply Word128Derived.of_N_spec.
  - apply Word128Derived.repr_small.
  pose proof (Word64Derived.unsigned_range x) as Hrange.
  change (0 <= Word64Derived.unsigned x < 340282366920938463463374607431768211456).
  change (0 <= Word64Derived.unsigned x < 18446744073709551616) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 18446744073709551616);
    [exact (proj2 Hrange)|exact modulus_64_lt_128].
Qed.

Lemma sign_extend_64_128_spec : forall x,
    Word128Derived.unsigned (sign_extend_64_128 x) =
    repr Word128Derived.P (Word64.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_64_128. apply Word128Derived.of_Z_spec.
Qed.

Lemma narrow_128_64_spec : forall x,
    Word64Derived.unsigned (narrow_128_64 x) =
    repr Word64Derived.P (Word128Derived.unsigned x).
Proof.
  intro x. unfold narrow_128_64.
  transitivity (repr Word64Derived.P (Z.of_N (Word128.to_N x))).
  - apply Word64Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_64_128_observed : forall x,
    Word64Derived.unsigned (narrow_128_64 (zero_extend_64_128 x)) =
    Word64Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word64Derived.P
    (Word128Derived.unsigned (zero_extend_64_128 x))).
  - apply narrow_128_64_spec.
  - rewrite zero_extend_64_128_spec.
    apply Word64Derived.repr_small.
    apply Word64Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_64_128_observed : forall x,
    Word128Derived.unsigned x < Word64.Raw.modulus ->
    Word128Derived.unsigned (zero_extend_64_128 (narrow_128_64 x)) =
    Word128Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_64_128_spec, narrow_128_64_spec.
  apply Word64Derived.repr_small.
  split; [apply Word128Derived.unsigned_range | exact H].
Qed.
