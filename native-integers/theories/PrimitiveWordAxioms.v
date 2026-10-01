(************************************************************************)
(* Concrete six-width primitive-word specification assumptions.         *)
(************************************************************************)

From Rocq.PrimitiveWords Require Import
  Scalar PrimitiveWordSpec Word8 Word16 Word32 Word64 Word128 Word256.
From Stdlib Require Import ZArith Lia.

Module Type OBSERVATION (P : RAW_SCALAR).
  Parameter unsigned : P.t -> Z.
End OBSERVATION.

Module BuildModel (P : RAW_SCALAR) (O : OBSERVATION P).
  Definition value : model :=
    {| carrier := P.t;
       bit_count := P.bits;
       PrimitiveWordSpec.modulus := P.modulus;
       PrimitiveWordSpec.sign_bit := P.sign_bit;
       raw_zero := P.zero;
       raw_one := P.one;
       raw_max_unsigned := P.max_unsigned;
       raw_min_signed := P.min_signed;
       raw_neg := P.neg;
       raw_add := P.add;
       raw_sub := P.sub;
       raw_mul := P.mul;
       raw_land := P.land;
       raw_lor := P.lor;
       raw_lxor := P.lxor;
       raw_lnot := P.lnot;
       raw_eqb := P.eqb;
       raw_ltu := P.ltu;
       raw_leu := P.leu;
       raw_lts := P.lts;
       raw_les := P.les;
       raw_lsl := P.lsl;
       raw_lsr := P.lsr;
       raw_asr := P.asr;
       raw_divu := P.divu;
       raw_modu := P.modu;
       raw_divs := P.divs;
       raw_rems := P.rems;
       observe_unsigned := O.unsigned |}.
End BuildModel.

Module Word8Observation <: OBSERVATION Word8.Raw.
  Definition unsigned := Word8.to_Z_unsigned.
End Word8Observation.
Module Word8Model := BuildModel Word8.Raw Word8Observation.
Definition word8_model := Word8Model.value.
Lemma word8_model_well_formed : well_formed word8_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word8_laws : laws word8_model.
Module Word8Instance <: INSTANCE.
  Definition primitive_model := word8_model.
  Definition primitive_model_well_formed := word8_model_well_formed.
  Definition primitive_model_laws := word8_laws.
End Word8Instance.
Module Word8Spec := Present Word8Instance.

Module Word16Observation <: OBSERVATION Word16.Raw.
  Definition unsigned := Word16.to_Z_unsigned.
End Word16Observation.
Module Word16Model := BuildModel Word16.Raw Word16Observation.
Definition word16_model := Word16Model.value.
Lemma word16_model_well_formed : well_formed word16_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word16_laws : laws word16_model.
Module Word16Instance <: INSTANCE.
  Definition primitive_model := word16_model.
  Definition primitive_model_well_formed := word16_model_well_formed.
  Definition primitive_model_laws := word16_laws.
End Word16Instance.
Module Word16Spec := Present Word16Instance.

Module Word32Observation <: OBSERVATION Word32.Raw.
  Definition unsigned := Word32.to_Z_unsigned.
End Word32Observation.
Module Word32Model := BuildModel Word32.Raw Word32Observation.
Definition word32_model := Word32Model.value.
Lemma word32_model_well_formed : well_formed word32_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word32_laws : laws word32_model.
Module Word32Instance <: INSTANCE.
  Definition primitive_model := word32_model.
  Definition primitive_model_well_formed := word32_model_well_formed.
  Definition primitive_model_laws := word32_laws.
End Word32Instance.
Module Word32Spec := Present Word32Instance.

Module Word64Observation <: OBSERVATION Word64.Raw.
  Definition unsigned := Word64.to_Z_unsigned.
End Word64Observation.
Module Word64Model := BuildModel Word64.Raw Word64Observation.
Definition word64_model := Word64Model.value.
Lemma word64_model_well_formed : well_formed word64_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word64_laws : laws word64_model.
Module Word64Instance <: INSTANCE.
  Definition primitive_model := word64_model.
  Definition primitive_model_well_formed := word64_model_well_formed.
  Definition primitive_model_laws := word64_laws.
End Word64Instance.
Module Word64Spec := Present Word64Instance.

Module Word128Observation <: OBSERVATION Word128.Raw.
  Definition unsigned := Word128.to_Z_unsigned.
End Word128Observation.
Module Word128Model := BuildModel Word128.Raw Word128Observation.
Definition word128_model := Word128Model.value.
Lemma word128_model_well_formed : well_formed word128_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word128_laws : laws word128_model.
Module Word128Instance <: INSTANCE.
  Definition primitive_model := word128_model.
  Definition primitive_model_well_formed := word128_model_well_formed.
  Definition primitive_model_laws := word128_laws.
End Word128Instance.
Module Word128Spec := Present Word128Instance.

Module Word256Observation <: OBSERVATION Word256.Raw.
  Definition unsigned := Word256.to_Z_unsigned.
End Word256Observation.
Module Word256Model := BuildModel Word256.Raw Word256Observation.
Definition word256_model := Word256Model.value.
Lemma word256_model_well_formed : well_formed word256_model.
Proof. constructor; vm_compute; lia. Qed.
Axiom word256_laws : laws word256_model.
Module Word256Instance <: INSTANCE.
  Definition primitive_model := word256_model.
  Definition primitive_model_well_formed := word256_model_well_formed.
  Definition primitive_model_laws := word256_laws.
End Word256Instance.
Module Word256Spec := Present Word256Instance.
