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

Lemma zero_extend_32_128_spec : forall x,
    Word128Derived.unsigned (zero_extend_32_128 x) = Word32Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_32_128.
  transitivity (repr Word128Derived.P (Z.of_N (Word32.to_N x))).
  - apply Word128Derived.of_N_spec.
  - apply Word128Derived.repr_small.
  pose proof (Word32Derived.unsigned_range x) as Hrange.
  change (0 <= Word32Derived.unsigned x < 340282366920938463463374607431768211456).
  change (0 <= Word32Derived.unsigned x < 4294967296) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 4294967296);
    [exact (proj2 Hrange)|exact modulus_32_lt_128].
Qed.

Lemma sign_extend_32_128_spec : forall x,
    Word128Derived.unsigned (sign_extend_32_128 x) =
    repr Word128Derived.P (Word32.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_32_128. apply Word128Derived.of_Z_spec.
Qed.

Lemma narrow_128_32_spec : forall x,
    Word32Derived.unsigned (narrow_128_32 x) =
    repr Word32Derived.P (Word128Derived.unsigned x).
Proof.
  intro x. unfold narrow_128_32.
  transitivity (repr Word32Derived.P (Z.of_N (Word128.to_N x))).
  - apply Word32Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_32_128_observed : forall x,
    Word32Derived.unsigned (narrow_128_32 (zero_extend_32_128 x)) =
    Word32Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word32Derived.P
    (Word128Derived.unsigned (zero_extend_32_128 x))).
  - apply narrow_128_32_spec.
  - rewrite zero_extend_32_128_spec.
    apply Word32Derived.repr_small.
    apply Word32Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_32_128_observed : forall x,
    Word128Derived.unsigned x < Word32.Raw.modulus ->
    Word128Derived.unsigned (zero_extend_32_128 (narrow_128_32 x)) =
    Word128Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_32_128_spec, narrow_128_32_spec.
  apply Word32Derived.repr_small.
  split; [apply Word128Derived.unsigned_range | exact H].
Qed.
