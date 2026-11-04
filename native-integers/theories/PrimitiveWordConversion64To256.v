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

Lemma zero_extend_64_256_spec : forall x,
    Word256Derived.unsigned (zero_extend_64_256 x) = Word64Derived.unsigned x.
Proof.
  intro x. unfold zero_extend_64_256.
  transitivity (repr Word256Derived.P (Z.of_N (Word64.to_N x))).
  - apply Word256Derived.of_N_spec.
  - apply Word256Derived.repr_small.
  pose proof (Word64Derived.unsigned_range x) as Hrange.
  change (0 <= Word64Derived.unsigned x < 115792089237316195423570985008687907853269984665640564039457584007913129639936).
  change (0 <= Word64Derived.unsigned x < 18446744073709551616) in Hrange.
  split; [exact (proj1 Hrange)|].
  eapply Z.lt_trans with (m := 18446744073709551616);
    [exact (proj2 Hrange)|exact modulus_64_lt_256].
Qed.

Lemma sign_extend_64_256_spec : forall x,
    Word256Derived.unsigned (sign_extend_64_256 x) =
    repr Word256Derived.P (Word64.to_Z_signed x).
Proof.
  intro x. unfold sign_extend_64_256. apply Word256Derived.of_Z_spec.
Qed.

Lemma narrow_256_64_spec : forall x,
    Word64Derived.unsigned (narrow_256_64 x) =
    repr Word64Derived.P (Word256Derived.unsigned x).
Proof.
  intro x. unfold narrow_256_64.
  transitivity (repr Word64Derived.P (Z.of_N (Word256.to_N x))).
  - apply Word64Derived.of_N_spec.
  - reflexivity.
Qed.

Lemma narrow_zero_extend_64_256_observed : forall x,
    Word64Derived.unsigned (narrow_256_64 (zero_extend_64_256 x)) =
    Word64Derived.unsigned x.
Proof.
  intro x.
  transitivity (repr Word64Derived.P
    (Word256Derived.unsigned (zero_extend_64_256 x))).
  - apply narrow_256_64_spec.
  - rewrite zero_extend_64_256_spec.
    apply Word64Derived.repr_small.
    apply Word64Derived.unsigned_range.
Qed.

Lemma zero_extend_narrow_64_256_observed : forall x,
    Word256Derived.unsigned x < Word64.Raw.modulus ->
    Word256Derived.unsigned (zero_extend_64_256 (narrow_256_64 x)) =
    Word256Derived.unsigned x.
Proof.
  intros x H. rewrite zero_extend_64_256_spec, narrow_256_64_spec.
  apply Word64Derived.repr_small.
  split; [apply Word256Derived.unsigned_range | exact H].
Qed.
