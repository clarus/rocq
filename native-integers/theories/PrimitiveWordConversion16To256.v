(************************************************************************)
(* Observable conversion proofs with Word16 as the smaller width.      *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Rocq.PrimitiveWords Require Import
  PrimitiveWordSpec PrimitiveWordDerived PrimitiveWordBounds Conversions
  Word8 Word16 Word32 Word64 Word128 Word256.
Open Scope Z_scope.

Opaque Word8.to_N Word16.to_N Word32.to_N Word64.to_N
  Word128.to_N Word256.to_N.

Lemma zero_extend_16_256_spec : forall x,
    Word256Derived.unsigned (zero_extend_16_256 x) = Word16Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_16_256.
  transitivity (repr Word256Derived.P (Z.of_N (Word16.to_N x))).
  - apply Word256Derived.of_N_spec.
  - apply Word256Derived.repr_small.
  pose proof (Word16Derived.unsigned_range x) as Hrange.
  change (0 <= Word16Derived.unsigned x < 115792089237316195423570985008687907853269984665640564039457584007913129639936).
  change (0 <= Word16Derived.unsigned x < 65536) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 65536);
    [exact (proj2 Hrange)|exact modulus_16_lt_256].
Qed.

Lemma sign_extend_16_256_spec : forall x,
    Word256Derived.unsigned (sign_extend_16_256 x) =
    repr Word256Derived.P (Word16.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_16_256. apply Word256Derived.of_Z_spec.
Qed.

Lemma narrow_256_16_spec : forall x,
    Word16Derived.unsigned (narrow_256_16 x) =
    repr Word16Derived.P (Word256Derived.unsigned x).
Proof.
  intro x. unfold narrow_256_16.
  transitivity (repr Word16Derived.P (Z.of_N (Word256.to_N x))).
  - apply Word16Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_16_256_observed : forall x,
    Word16Derived.unsigned (narrow_256_16 (zero_extend_16_256 x)) =
    Word16Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word16Derived.P
    (Word256Derived.unsigned (zero_extend_16_256 x))).
  - apply narrow_256_16_spec.
  - rewrite zero_extend_16_256_spec.
    apply Word16Derived.repr_small.
    apply Word16Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_16_256_observed : forall x,
    Word256Derived.unsigned x < Word16.Raw.modulus ->
    Word256Derived.unsigned (zero_extend_16_256 (narrow_256_16 x)) =
    Word256Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_16_256_spec, narrow_256_16_spec.
  apply Word16Derived.repr_small.
  split; [apply Word256Derived.unsigned_range | exact H].
Qed.
