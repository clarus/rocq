(************************************************************************)
(* Observable conversion proofs with Word8 as the smaller width.      *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Rocq.PrimitiveWords Require Import
  PrimitiveWordSpec PrimitiveWordDerived PrimitiveWordBounds Conversions
  Word8 Word16 Word32 Word64 Word128 Word256.
Open Scope Z_scope.

Opaque Word8.to_N Word16.to_N Word32.to_N Word64.to_N
  Word128.to_N Word256.to_N.

Lemma zero_extend_8_64_spec : forall x,
    Word64Derived.unsigned (zero_extend_8_64 x) = Word8Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_8_64.
  transitivity (repr Word64Derived.P (Z.of_N (Word8.to_N x))).
  - apply Word64Derived.of_N_spec.
  - apply Word64Derived.repr_small.
  pose proof (Word8Derived.unsigned_range x) as Hrange.
  change (0 <= Word8Derived.unsigned x < 18446744073709551616).
  change (0 <= Word8Derived.unsigned x < 256) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 256);
    [exact (proj2 Hrange)|exact modulus_8_lt_64].
Qed.

Lemma sign_extend_8_64_spec : forall x,
    Word64Derived.unsigned (sign_extend_8_64 x) =
    repr Word64Derived.P (Word8.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_8_64. apply Word64Derived.of_Z_spec.
Qed.

Lemma narrow_64_8_spec : forall x,
    Word8Derived.unsigned (narrow_64_8 x) =
    repr Word8Derived.P (Word64Derived.unsigned x).
Proof.
  intro x. unfold narrow_64_8.
  transitivity (repr Word8Derived.P (Z.of_N (Word64.to_N x))).
  - apply Word8Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_8_64_observed : forall x,
    Word8Derived.unsigned (narrow_64_8 (zero_extend_8_64 x)) =
    Word8Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word8Derived.P
    (Word64Derived.unsigned (zero_extend_8_64 x))).
  - apply narrow_64_8_spec.
  - rewrite zero_extend_8_64_spec.
    apply Word8Derived.repr_small.
    apply Word8Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_8_64_observed : forall x,
    Word64Derived.unsigned x < Word8.Raw.modulus ->
    Word64Derived.unsigned (zero_extend_8_64 (narrow_64_8 x)) =
    Word64Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_8_64_spec, narrow_64_8_spec.
  apply Word8Derived.repr_small.
  split; [apply Word64Derived.unsigned_range | exact H].
Qed.
