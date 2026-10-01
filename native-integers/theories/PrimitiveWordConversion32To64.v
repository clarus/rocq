(************************************************************************)
(* Observable conversion proofs with Word32 as the smaller width.      *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Rocq.PrimitiveWords Require Import
  PrimitiveWordSpec PrimitiveWordDerived PrimitiveWordBounds Conversions
  Word8 Word16 Word32 Word64 Word128 Word256.
Open Scope Z_scope.

Opaque Word8.to_N Word16.to_N Word32.to_N Word64.to_N
  Word128.to_N Word256.to_N.

Lemma zero_extend_32_64_spec : forall x,
    Word64Derived.unsigned (zero_extend_32_64 x) = Word32Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_32_64.
  transitivity (repr Word64Derived.P (Z.of_N (Word32.to_N x))).
  - apply Word64Derived.of_N_spec.
  - apply Word64Derived.repr_small.
  pose proof (Word32Derived.unsigned_range x) as Hrange.
  change (0 <= Word32Derived.unsigned x < 18446744073709551616).
  change (0 <= Word32Derived.unsigned x < 4294967296) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 4294967296);
    [exact (proj2 Hrange)|exact modulus_32_lt_64].
Qed.

Lemma sign_extend_32_64_spec : forall x,
    Word64Derived.unsigned (sign_extend_32_64 x) =
    repr Word64Derived.P (Word32.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_32_64. apply Word64Derived.of_Z_spec.
Qed.

Lemma narrow_64_32_spec : forall x,
    Word32Derived.unsigned (narrow_64_32 x) =
    repr Word32Derived.P (Word64Derived.unsigned x).
Proof.
  intro x. unfold narrow_64_32.
  transitivity (repr Word32Derived.P (Z.of_N (Word64.to_N x))).
  - apply Word32Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_32_64_observed : forall x,
    Word32Derived.unsigned (narrow_64_32 (zero_extend_32_64 x)) =
    Word32Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word32Derived.P
    (Word64Derived.unsigned (zero_extend_32_64 x))).
  - apply narrow_64_32_spec.
  - rewrite zero_extend_32_64_spec.
    apply Word32Derived.repr_small.
    apply Word32Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_32_64_observed : forall x,
    Word64Derived.unsigned x < Word32.Raw.modulus ->
    Word64Derived.unsigned (zero_extend_32_64 (narrow_64_32 x)) =
    Word64Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_32_64_spec, narrow_64_32_spec.
  apply Word32Derived.repr_small.
  split; [apply Word64Derived.unsigned_range | exact H].
Qed.
