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

Lemma zero_extend_16_128_spec : forall x,
    Word128Derived.unsigned (zero_extend_16_128 x) = Word16Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_16_128.
  transitivity (repr Word128Derived.P (Z.of_N (Word16.to_N x))).
  - apply Word128Derived.of_N_spec.
  - apply Word128Derived.repr_small.
  pose proof (Word16Derived.unsigned_range x) as Hrange.
  change (0 <= Word16Derived.unsigned x < 340282366920938463463374607431768211456).
  change (0 <= Word16Derived.unsigned x < 65536) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 65536);
    [exact (proj2 Hrange)|exact modulus_16_lt_128].
Qed.

Lemma sign_extend_16_128_spec : forall x,
    Word128Derived.unsigned (sign_extend_16_128 x) =
    repr Word128Derived.P (Word16.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_16_128. apply Word128Derived.of_Z_spec.
Qed.

Lemma narrow_128_16_spec : forall x,
    Word16Derived.unsigned (narrow_128_16 x) =
    repr Word16Derived.P (Word128Derived.unsigned x).
Proof.
  intro x. unfold narrow_128_16.
  transitivity (repr Word16Derived.P (Z.of_N (Word128.to_N x))).
  - apply Word16Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_16_128_observed : forall x,
    Word16Derived.unsigned (narrow_128_16 (zero_extend_16_128 x)) =
    Word16Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word16Derived.P
    (Word128Derived.unsigned (zero_extend_16_128 x))).
  - apply narrow_128_16_spec.
  - rewrite zero_extend_16_128_spec.
    apply Word16Derived.repr_small.
    apply Word16Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_16_128_observed : forall x,
    Word128Derived.unsigned x < Word16.Raw.modulus ->
    Word128Derived.unsigned (zero_extend_16_128 (narrow_128_16 x)) =
    Word128Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_16_128_spec, narrow_128_16_spec.
  apply Word16Derived.repr_small.
  split; [apply Word128Derived.unsigned_range | exact H].
Qed.
