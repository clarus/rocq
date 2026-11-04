(************************************************************************)
(* Observation bridges to the existing production scalar Word modules. *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
Require Gecko.Word.Word8 Gecko.Word.Word16 Gecko.Word.Word32 Gecko.Word.Word64.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 PrimitiveWordSpec PrimitiveWordAxioms
  PrimitiveWordDerived.

Open Scope Z_scope.

Opaque Word8.to_N Word16.to_N Word32.to_N Word64.to_N.
Opaque Gecko.Word.Word8.to_Z_unsigned Gecko.Word.Word16.to_Z_unsigned
  Gecko.Word.Word32.to_Z_unsigned Gecko.Word.Word64.to_Z_unsigned.

Module ProductionWord8Adapter.
  Definition primitive_unsigned : Word8.t -> Z :=
    PrimitiveWordAxioms.Word8Spec.unsigned.
  Definition related (p : Word8.t) (q : Gecko.Word.Word8.t) : Prop :=
    primitive_unsigned p = Gecko.Word.Word8.to_Z_unsigned q.
  Definition to_production (p : Word8.t) : Gecko.Word.Word8.t :=
    Gecko.Word.Word8.of_Z (primitive_unsigned p).
  Definition to_primitive (q : Gecko.Word.Word8.t) : Word8.t :=
    Word8.of_Z (Gecko.Word.Word8.to_Z_unsigned q).

  Lemma to_production_related : forall p, related p (to_production p).
  Proof.
    intro p. unfold related, to_production.
    rewrite Gecko.Word.Word8.of_Z_spec, Z.mod_small; [reflexivity|].
    exact (PrimitiveWordAxioms.Word8Spec.unsigned_range p).
  Qed.
  Lemma to_primitive_related : forall q, related (to_primitive q) q.
  Proof.
    intro q. unfold related, to_primitive, primitive_unsigned.
    change (Word8Derived.unsigned
      (Word8.of_Z (Gecko.Word.Word8.to_Z_unsigned q)) =
      Gecko.Word.Word8.to_Z_unsigned q).
    transitivity (repr Word8Derived.P (Gecko.Word.Word8.to_Z_unsigned q)).
    - exact (Word8Derived.of_Z_spec (Gecko.Word.Word8.to_Z_unsigned q)).
    - apply Word8Derived.repr_small.
      exact (Gecko.Word.Word8.unsigned_range q).
  Qed.
  Lemma primitive_roundtrip_observed : forall p,
      primitive_unsigned (to_primitive (to_production p)) =
      primitive_unsigned p.
  Proof.
    intro p. pose proof (to_primitive_related (to_production p)) as Hback.
    pose proof (to_production_related p) as Hforward.
    unfold related in *. now rewrite Hback, <- Hforward.
  Qed.
  Lemma production_roundtrip_observed : forall q,
      Gecko.Word.Word8.to_Z_unsigned (to_production (to_primitive q)) =
      Gecko.Word.Word8.to_Z_unsigned q.
  Proof.
    intro q. pose proof (to_production_related (to_primitive q)) as Hforward.
    pose proof (to_primitive_related q) as Hback.
    unfold related in *. now rewrite <- Hforward, Hback.
  Qed.
  Lemma primitive_observational_extensional : forall p1 p2 q,
      related p1 q -> related p2 q ->
      primitive_unsigned p1 = primitive_unsigned p2.
  Proof.
    intros p1 p2 q H1 H2. unfold related in *.
    now transitivity (Gecko.Word.Word8.to_Z_unsigned q).
  Qed.
  Lemma add_agrees : forall p1 p2 q1 q2,
      related p1 q1 -> related p2 q2 ->
      related (PrimitiveWordSpec.raw_add PrimitiveWordAxioms.Word8Spec.P p1 p2)
              (Gecko.Word.Word8.add q1 q2).
  Proof.
    intros p1 p2 q1 q2 H1 H2. unfold related in *.
    transitivity ((primitive_unsigned p1 + primitive_unsigned p2) mod 256).
    - exact (PrimitiveWordAxioms.Word8Spec.add_spec p1 p2).
    - rewrite H1, H2. symmetry. apply Gecko.Word.Word8.add_spec.
  Qed.
  Lemma sub_agrees : forall p1 p2 q1 q2,
      related p1 q1 -> related p2 q2 ->
      related (PrimitiveWordSpec.raw_sub PrimitiveWordAxioms.Word8Spec.P p1 p2)
              (Gecko.Word.Word8.sub q1 q2).
  Proof.
    intros p1 p2 q1 q2 H1 H2. unfold related in *.
    transitivity ((primitive_unsigned p1 - primitive_unsigned p2) mod 256).
    - exact (PrimitiveWordAxioms.Word8Spec.sub_spec p1 p2).
    - rewrite H1, H2. symmetry. apply Gecko.Word.Word8.sub_spec.
  Qed.
  Lemma mul_agrees : forall p1 p2 q1 q2,
      related p1 q1 -> related p2 q2 ->
      related (PrimitiveWordSpec.raw_mul PrimitiveWordAxioms.Word8Spec.P p1 p2)
              (Gecko.Word.Word8.mul q1 q2).
  Proof.
    intros p1 p2 q1 q2 H1 H2. unfold related in *.
    transitivity ((primitive_unsigned p1 * primitive_unsigned p2) mod 256).
    - exact (PrimitiveWordAxioms.Word8Spec.mul_spec p1 p2).
    - rewrite H1, H2. symmetry. apply Gecko.Word.Word8.mul_spec.
  Qed.
End ProductionWord8Adapter.

Module ProductionWord16Adapter.
  Definition primitive_unsigned : Word16.t -> Z :=
    PrimitiveWordAxioms.Word16Spec.unsigned.
  Definition related (p : Word16.t) (q : Gecko.Word.Word16.t) : Prop :=
    primitive_unsigned p = Gecko.Word.Word16.to_Z_unsigned q.
  Definition to_production (p : Word16.t) : Gecko.Word.Word16.t :=
    Gecko.Word.Word16.of_Z (primitive_unsigned p).
  Definition to_primitive (q : Gecko.Word.Word16.t) : Word16.t :=
    Word16.of_Z (Gecko.Word.Word16.to_Z_unsigned q).

  Lemma to_production_related : forall p, related p (to_production p).
  Proof.
    intro p. unfold related, to_production.
    rewrite Gecko.Word.Word16.of_Z_spec, Z.mod_small; [reflexivity|].
    exact (PrimitiveWordAxioms.Word16Spec.unsigned_range p).
  Qed.
  Lemma to_primitive_related : forall q, related (to_primitive q) q.
  Proof.
    intro q. unfold related, to_primitive, primitive_unsigned.
    change (Word16Derived.unsigned
      (Word16.of_Z (Gecko.Word.Word16.to_Z_unsigned q)) =
      Gecko.Word.Word16.to_Z_unsigned q).
    transitivity (repr Word16Derived.P (Gecko.Word.Word16.to_Z_unsigned q)).
    - exact (Word16Derived.of_Z_spec (Gecko.Word.Word16.to_Z_unsigned q)).
    - apply Word16Derived.repr_small.
      exact (Gecko.Word.Word16.unsigned_range q).
  Qed.
  Lemma primitive_roundtrip_observed : forall p,
      primitive_unsigned (to_primitive (to_production p)) =
      primitive_unsigned p.
  Proof.
    intro p. pose proof (to_primitive_related (to_production p)) as Hback.
    pose proof (to_production_related p) as Hforward.
    unfold related in *. now rewrite Hback, <- Hforward.
  Qed.
  Lemma production_roundtrip_observed : forall q,
      Gecko.Word.Word16.to_Z_unsigned (to_production (to_primitive q)) =
      Gecko.Word.Word16.to_Z_unsigned q.
  Proof.
    intro q. pose proof (to_production_related (to_primitive q)) as Hforward.
    pose proof (to_primitive_related q) as Hback.
    unfold related in *. now rewrite <- Hforward, Hback.
  Qed.
  Lemma primitive_observational_extensional : forall p1 p2 q,
      related p1 q -> related p2 q ->
      primitive_unsigned p1 = primitive_unsigned p2.
  Proof.
    intros p1 p2 q H1 H2. unfold related in *.
    now transitivity (Gecko.Word.Word16.to_Z_unsigned q).
  Qed.
End ProductionWord16Adapter.

Module ProductionWord32Adapter.
  Definition primitive_unsigned : Word32.t -> Z :=
    PrimitiveWordAxioms.Word32Spec.unsigned.
  Definition related (p : Word32.t) (q : Gecko.Word.Word32.t) : Prop :=
    primitive_unsigned p = Gecko.Word.Word32.to_Z_unsigned q.
  Definition to_production (p : Word32.t) : Gecko.Word.Word32.t :=
    Gecko.Word.Word32.of_Z (primitive_unsigned p).
  Definition to_primitive (q : Gecko.Word.Word32.t) : Word32.t :=
    Word32.of_Z (Gecko.Word.Word32.to_Z_unsigned q).
  Lemma to_production_related : forall p, related p (to_production p).
  Proof.
    intro p. unfold related, to_production.
    rewrite Gecko.Word.Word32.of_Z_spec, Z.mod_small; [reflexivity|].
    exact (PrimitiveWordAxioms.Word32Spec.unsigned_range p).
  Qed.
  Lemma to_primitive_related : forall q, related (to_primitive q) q.
  Proof.
    intro q. unfold related, to_primitive, primitive_unsigned.
    change (Word32Derived.unsigned
      (Word32.of_Z (Gecko.Word.Word32.to_Z_unsigned q)) =
      Gecko.Word.Word32.to_Z_unsigned q).
    transitivity (repr Word32Derived.P (Gecko.Word.Word32.to_Z_unsigned q)).
    - exact (Word32Derived.of_Z_spec (Gecko.Word.Word32.to_Z_unsigned q)).
    - apply Word32Derived.repr_small.
      exact (Gecko.Word.Word32.unsigned_range q).
  Qed.
  Lemma primitive_roundtrip_observed : forall p,
      primitive_unsigned (to_primitive (to_production p)) =
      primitive_unsigned p.
  Proof.
    intro p. pose proof (to_primitive_related (to_production p)) as Hback.
    pose proof (to_production_related p) as Hforward.
    unfold related in *. now rewrite Hback, <- Hforward.
  Qed.
  Lemma production_roundtrip_observed : forall q,
      Gecko.Word.Word32.to_Z_unsigned (to_production (to_primitive q)) =
      Gecko.Word.Word32.to_Z_unsigned q.
  Proof.
    intro q. pose proof (to_production_related (to_primitive q)) as Hforward.
    pose proof (to_primitive_related q) as Hback.
    unfold related in *. now rewrite <- Hforward, Hback.
  Qed.
  Lemma primitive_observational_extensional : forall p1 p2 q,
      related p1 q -> related p2 q ->
      primitive_unsigned p1 = primitive_unsigned p2.
  Proof.
    intros p1 p2 q H1 H2. unfold related in *.
    now transitivity (Gecko.Word.Word32.to_Z_unsigned q).
  Qed.
End ProductionWord32Adapter.

Module ProductionWord64Adapter.
  Definition primitive_unsigned : Word64.t -> Z :=
    PrimitiveWordAxioms.Word64Spec.unsigned.
  Definition related (p : Word64.t) (q : Gecko.Word.Word64.t) : Prop :=
    primitive_unsigned p = Gecko.Word.Word64.to_Z_unsigned q.
  Definition to_production (p : Word64.t) : Gecko.Word.Word64.t :=
    Gecko.Word.Word64.of_Z (primitive_unsigned p).
  Definition to_primitive (q : Gecko.Word.Word64.t) : Word64.t :=
    Word64.of_Z (Gecko.Word.Word64.to_Z_unsigned q).
  Lemma to_production_related : forall p, related p (to_production p).
  Proof.
    intro p. unfold related, to_production.
    rewrite Gecko.Word.Word64.of_Z_spec, Z.mod_small; [reflexivity|].
    exact (PrimitiveWordAxioms.Word64Spec.unsigned_range p).
  Qed.
  Lemma to_primitive_related : forall q, related (to_primitive q) q.
  Proof.
    intro q. unfold related, to_primitive, primitive_unsigned.
    change (Word64Derived.unsigned
      (Word64.of_Z (Gecko.Word.Word64.to_Z_unsigned q)) =
      Gecko.Word.Word64.to_Z_unsigned q).
    transitivity (repr Word64Derived.P (Gecko.Word.Word64.to_Z_unsigned q)).
    - exact (Word64Derived.of_Z_spec (Gecko.Word.Word64.to_Z_unsigned q)).
    - apply Word64Derived.repr_small.
      exact (Gecko.Word.Word64.unsigned_range q).
  Qed.
  Lemma primitive_roundtrip_observed : forall p,
      primitive_unsigned (to_primitive (to_production p)) =
      primitive_unsigned p.
  Proof.
    intro p. pose proof (to_primitive_related (to_production p)) as Hback.
    pose proof (to_production_related p) as Hforward.
    unfold related in *. now rewrite Hback, <- Hforward.
  Qed.
  Lemma production_roundtrip_observed : forall q,
      Gecko.Word.Word64.to_Z_unsigned (to_production (to_primitive q)) =
      Gecko.Word.Word64.to_Z_unsigned q.
  Proof.
    intro q. pose proof (to_production_related (to_primitive q)) as Hforward.
    pose proof (to_primitive_related q) as Hback.
    unfold related in *. now rewrite <- Hforward, Hback.
  Qed.
  Lemma primitive_observational_extensional : forall p1 p2 q,
      related p1 q -> related p2 q ->
      primitive_unsigned p1 = primitive_unsigned p2.
  Proof.
    intros p1 p2 q H1 H2. unfold related in *.
    now transitivity (Gecko.Word.Word64.to_Z_unsigned q).
  Qed.
End ProductionWord64Adapter.

(** Word128 and Word256 deliberately have no production peer. *)
