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

Lemma zero_extend_8_32_spec : forall x,
    Word32Derived.unsigned (zero_extend_8_32 x) = Word8Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_8_32.
  transitivity (repr Word32Derived.P (Z.of_N (Word8.to_N x))).
  - apply Word32Derived.of_N_spec.
  - apply Word32Derived.repr_small.
  pose proof (Word8Derived.unsigned_range x) as Hrange.
  change (0 <= Word8Derived.unsigned x < 4294967296).
  change (0 <= Word8Derived.unsigned x < 256) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 256);
    [exact (proj2 Hrange)|exact modulus_8_lt_32].
Qed.

Lemma sign_extend_8_32_spec : forall x,
    Word32Derived.unsigned (sign_extend_8_32 x) =
    repr Word32Derived.P (Word8.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_8_32. apply Word32Derived.of_Z_spec.
Qed.

Lemma narrow_32_8_spec : forall x,
    Word8Derived.unsigned (narrow_32_8 x) =
    repr Word8Derived.P (Word32Derived.unsigned x).
Proof.
  intro x. unfold narrow_32_8.
  transitivity (repr Word8Derived.P (Z.of_N (Word32.to_N x))).
  - apply Word8Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_8_32_observed : forall x,
    Word8Derived.unsigned (narrow_32_8 (zero_extend_8_32 x)) =
    Word8Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word8Derived.P
    (Word32Derived.unsigned (zero_extend_8_32 x))).
  - apply narrow_32_8_spec.
  - rewrite zero_extend_8_32_spec.
    apply Word8Derived.repr_small.
    apply Word8Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_8_32_observed : forall x,
    Word32Derived.unsigned x < Word8.Raw.modulus ->
    Word32Derived.unsigned (zero_extend_8_32 (narrow_32_8 x)) =
    Word32Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_8_32_spec, narrow_32_8_spec.
  apply Word8Derived.repr_small.
  split; [apply Word32Derived.unsigned_range | exact H].
Qed.
