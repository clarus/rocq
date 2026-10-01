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

Lemma zero_extend_8_256_spec : forall x,
    Word256Derived.unsigned (zero_extend_8_256 x) = Word8Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_8_256.
  transitivity (repr Word256Derived.P (Z.of_N (Word8.to_N x))).
  - apply Word256Derived.of_N_spec.
  - apply Word256Derived.repr_small.
  pose proof (Word8Derived.unsigned_range x) as Hrange.
  change (0 <= Word8Derived.unsigned x < 115792089237316195423570985008687907853269984665640564039457584007913129639936).
  change (0 <= Word8Derived.unsigned x < 256) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 256);
    [exact (proj2 Hrange)|exact modulus_8_lt_256].
Qed.

Lemma sign_extend_8_256_spec : forall x,
    Word256Derived.unsigned (sign_extend_8_256 x) =
    repr Word256Derived.P (Word8.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_8_256. apply Word256Derived.of_Z_spec.
Qed.

Lemma narrow_256_8_spec : forall x,
    Word8Derived.unsigned (narrow_256_8 x) =
    repr Word8Derived.P (Word256Derived.unsigned x).
Proof.
  intro x. unfold narrow_256_8.
  transitivity (repr Word8Derived.P (Z.of_N (Word256.to_N x))).
  - apply Word8Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_8_256_observed : forall x,
    Word8Derived.unsigned (narrow_256_8 (zero_extend_8_256 x)) =
    Word8Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word8Derived.P
    (Word256Derived.unsigned (zero_extend_8_256 x))).
  - apply narrow_256_8_spec.
  - rewrite zero_extend_8_256_spec.
    apply Word8Derived.repr_small.
    apply Word8Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_8_256_observed : forall x,
    Word256Derived.unsigned x < Word8.Raw.modulus ->
    Word256Derived.unsigned (zero_extend_8_256 (narrow_256_8 x)) =
    Word256Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_8_256_spec, narrow_256_8_spec.
  apply Word8Derived.repr_small.
  split; [apply Word256Derived.unsigned_range | exact H].
Qed.
