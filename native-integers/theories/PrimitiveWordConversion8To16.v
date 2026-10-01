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

Lemma zero_extend_8_16_spec : forall x,
    Word16Derived.unsigned (zero_extend_8_16 x) = Word8Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_8_16.
  transitivity (repr Word16Derived.P (Z.of_N (Word8.to_N x))).
  - apply Word16Derived.of_N_spec.
  - apply Word16Derived.repr_small.
  pose proof (Word8Derived.unsigned_range x) as Hrange.
  change (0 <= Word8Derived.unsigned x < 65536).
  change (0 <= Word8Derived.unsigned x < 256) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 256);
    [exact (proj2 Hrange)|exact modulus_8_lt_16].
Qed.

Lemma sign_extend_8_16_spec : forall x,
    Word16Derived.unsigned (sign_extend_8_16 x) =
    repr Word16Derived.P (Word8.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_8_16. apply Word16Derived.of_Z_spec.
Qed.

Lemma narrow_16_8_spec : forall x,
    Word8Derived.unsigned (narrow_16_8 x) =
    repr Word8Derived.P (Word16Derived.unsigned x).
Proof.
  intro x. unfold narrow_16_8.
  transitivity (repr Word8Derived.P (Z.of_N (Word16.to_N x))).
  - apply Word8Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_8_16_observed : forall x,
    Word8Derived.unsigned (narrow_16_8 (zero_extend_8_16 x)) =
    Word8Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word8Derived.P
    (Word16Derived.unsigned (zero_extend_8_16 x))).
  - apply narrow_16_8_spec.
  - rewrite zero_extend_8_16_spec.
    apply Word8Derived.repr_small.
    apply Word8Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_8_16_observed : forall x,
    Word16Derived.unsigned x < Word8.Raw.modulus ->
    Word16Derived.unsigned (zero_extend_8_16 (narrow_16_8 x)) =
    Word16Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_8_16_spec, narrow_16_8_spec.
  apply Word8Derived.repr_small.
  split; [apply Word16Derived.unsigned_range | exact H].
Qed.
