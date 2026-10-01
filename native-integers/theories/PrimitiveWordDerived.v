(************************************************************************)
(* Derived observable facts for the six experimental primitive words.  *)
(************************************************************************)

From Stdlib Require Import ZArith NArith Bool Lia.
From Rocq.PrimitiveWords Require Import
  Scalar PrimitiveWordSpec PrimitiveWordAxioms
  Word8 Word16 Word32 Word64 Word128 Word256 Conversions.

Open Scope Z_scope.

Definition signed_of_unsigned (P : model) (u : Z) : Z :=
  if Z.ltb u (PrimitiveWordSpec.sign_bit P) then u
  else u - PrimitiveWordSpec.modulus P.

Definition observe_option {A} (observe : A -> Z) (value : option A)
    : option Z :=
  match value with Some x => Some (observe x) | None => None end.

Definition observe_pair {A} (observe : A -> Z) (value : bool * A)
    : bool * Z := (fst value, observe (snd value)).

Definition observe_divmod {A} (observe : A -> Z)
    (value : option (A * A)) : option (Z * Z) :=
  match value with
  | Some (q, r) => Some (observe q, observe r)
  | None => None
  end.

Module Type DERIVED_INPUT.
  Declare Module Raw : RAW_SCALAR.
  Declare Module Observation : PrimitiveWordAxioms.OBSERVATION Raw.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := Model.value.
  Parameter primitive_laws : laws primitive_model.
  Parameter bits_at_least_two : (2 <= Raw.bits)%nat.
  Parameter modulus_power :
    Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Parameter modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Parameter signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Parameter sign_bit_positive : 0 < Raw.sign_bit.
End DERIVED_INPUT.

Module Prove (I : DERIVED_INPUT).
  Module API := Scalar.Make I.Raw.
  Definition P := I.primitive_model.
  Definition unsigned : API.t -> Z := I.Observation.unsigned.
  Definition signed (x : API.t) : Z := signed_of_unsigned P (unsigned x).

  Lemma unsigned_range : forall x, 0 <= unsigned x < I.Raw.modulus.
  Proof. exact (law_unsigned_range P I.primitive_laws). Qed.

  Lemma unsigned_injective : forall x y, unsigned x = unsigned y -> x = y.
  Proof. exact (law_unsigned_injective P I.primitive_laws). Qed.

  Lemma signed_range : forall x, - I.Raw.sign_bit <= signed x < I.Raw.sign_bit.
  Proof.
    intros x. unfold signed, signed_of_unsigned.
    change (- I.Raw.sign_bit <=
      (if Z.ltb (unsigned x) I.Raw.sign_bit then unsigned x
       else unsigned x - I.Raw.modulus) < I.Raw.sign_bit).
    pose proof (unsigned_range x).
    pose proof I.sign_bit_positive.
    rewrite I.modulus_twice_sign_bit in H |- *.
    destruct (Z.ltb (unsigned x) I.Raw.sign_bit) eqn:E.
    - apply Z.ltb_lt in E. lia.
    - apply Z.ltb_ge in E. lia.
  Qed.

  Lemma signed_negative : forall x,
      Z.ltb (signed x) 0 = negb (Z.ltb (unsigned x) I.Raw.sign_bit).
  Proof.
    intro x. unfold signed, signed_of_unsigned.
    change (Z.ltb
      (if Z.ltb (unsigned x) I.Raw.sign_bit then unsigned x
       else unsigned x - I.Raw.modulus) 0 =
      negb (Z.ltb (unsigned x) I.Raw.sign_bit)).
    pose proof (unsigned_range x) as Hrange.
    destruct (Z.ltb (unsigned x) I.Raw.sign_bit) eqn:E; simpl.
    - apply Z.ltb_ge. exact (proj1 Hrange).
    - apply Z.ltb_lt. apply Z.sub_neg. exact (proj2 Hrange).
  Qed.

  Lemma zero_spec : unsigned API.zero = 0.
  Proof. exact (law_zero P I.primitive_laws). Qed.
  Lemma one_spec : unsigned API.one = 1.
  Proof. exact (law_one P I.primitive_laws). Qed.
  Lemma max_unsigned_spec : unsigned API.max_unsigned = I.Raw.modulus - 1.
  Proof. exact (law_max_unsigned P I.primitive_laws). Qed.
  Lemma min_signed_spec : unsigned API.min_signed = I.Raw.sign_bit.
  Proof. exact (law_min_signed P I.primitive_laws). Qed.

  Lemma signed_zero : signed API.zero = 0.
  Proof.
    unfold signed, signed_of_unsigned.
    change ((if Z.ltb (unsigned API.zero) I.Raw.sign_bit
             then unsigned API.zero else unsigned API.zero - I.Raw.modulus) = 0).
    rewrite zero_spec.
    pose proof I.sign_bit_positive.
    destruct (Z.ltb 0 I.Raw.sign_bit) eqn:E.
    - reflexivity.
    - apply Z.ltb_ge in E; lia.
  Qed.
  Lemma signed_min : signed API.min_signed = - I.Raw.sign_bit.
  Proof.
    unfold signed, signed_of_unsigned.
    change ((if Z.ltb (unsigned API.min_signed) I.Raw.sign_bit
             then unsigned API.min_signed
             else unsigned API.min_signed - I.Raw.modulus) = - I.Raw.sign_bit).
    rewrite min_signed_spec.
    rewrite I.modulus_twice_sign_bit.
    pose proof I.sign_bit_positive.
    destruct (Z.ltb I.Raw.sign_bit I.Raw.sign_bit) eqn:E.
    - apply Z.ltb_lt in E; lia.
    - lia.
  Qed.
  Lemma signed_max : signed API.max_unsigned = -1.
  Proof.
    unfold signed, signed_of_unsigned.
    change ((if Z.ltb (unsigned API.max_unsigned) I.Raw.sign_bit
             then unsigned API.max_unsigned
             else unsigned API.max_unsigned - I.Raw.modulus) = -1).
    rewrite max_unsigned_spec.
    rewrite I.modulus_twice_sign_bit.
    pose proof I.sign_bit_positive.
    destruct (Z.ltb (2 * I.Raw.sign_bit - 1) I.Raw.sign_bit) eqn:E.
    - apply Z.ltb_lt in E; lia.
    - lia.
  Qed.

  Lemma eqb_spec : forall x y, API.eqb x y = true <-> x = y.
  Proof.
    intros x y. unfold API.eqb.
    rewrite (law_eqb P I.primitive_laws), Z.eqb_eq.
    split; [apply unsigned_injective | now intros ->].
  Qed.
  Lemma eqb_value : forall x y,
      API.eqb x y = Z.eqb (unsigned x) (unsigned y).
  Proof. exact (law_eqb P I.primitive_laws). Qed.
  Lemma ltu_spec : forall x y,
      API.ltu x y = Z.ltb (unsigned x) (unsigned y).
  Proof. exact (law_ltu P I.primitive_laws). Qed.
  Lemma leu_spec : forall x y,
      API.leu x y = Z.leb (unsigned x) (unsigned y).
  Proof. exact (law_leu P I.primitive_laws). Qed.
  Lemma lts_spec : forall x y,
      API.lts x y = Z.ltb (signed x) (signed y).
  Proof. exact (law_lts P I.primitive_laws). Qed.
  Lemma les_spec : forall x y,
      API.les x y = Z.leb (signed x) (signed y).
  Proof. exact (law_les P I.primitive_laws). Qed.

  Lemma neg_spec : forall x,
      unsigned (API.neg x) = repr P (- unsigned x).
  Proof. exact (law_neg P I.primitive_laws). Qed.
  Lemma add_spec : forall x y,
      unsigned (API.add x y) = repr P (unsigned x + unsigned y).
  Proof. exact (law_add P I.primitive_laws). Qed.
  Lemma sub_spec : forall x y,
      unsigned (API.sub x y) = repr P (unsigned x - unsigned y).
  Proof. exact (law_sub P I.primitive_laws). Qed.
  Lemma mul_spec : forall x y,
      unsigned (API.mul x y) = repr P (unsigned x * unsigned y).
  Proof. exact (law_mul P I.primitive_laws). Qed.
  Lemma logand_spec : forall x y,
      unsigned (API.logand x y) = repr P (Z.land (unsigned x) (unsigned y)).
  Proof. exact (law_land P I.primitive_laws). Qed.
  Lemma logor_spec : forall x y,
      unsigned (API.logor x y) = repr P (Z.lor (unsigned x) (unsigned y)).
  Proof. exact (law_lor P I.primitive_laws). Qed.
  Lemma logxor_spec : forall x y,
      unsigned (API.logxor x y) = repr P (Z.lxor (unsigned x) (unsigned y)).
  Proof. exact (law_lxor P I.primitive_laws). Qed.
  Lemma lognot_spec : forall x,
      unsigned (API.lognot x) = repr P (Z.lnot (unsigned x)).
  Proof. exact (law_lnot P I.primitive_laws). Qed.

  Lemma raw_lsl_spec : forall x count,
      unsigned (I.Raw.lsl x count) = expected_lsl P x count.
  Proof. exact (law_lsl P I.primitive_laws). Qed.
  Lemma raw_lsr_spec : forall x count,
      unsigned (I.Raw.lsr x count) = expected_lsr P x count.
  Proof. exact (law_lsr P I.primitive_laws). Qed.
  Lemma raw_asr_spec : forall x count,
      unsigned (I.Raw.asr x count) = expected_asr P x count.
  Proof. exact (law_asr P I.primitive_laws). Qed.

  Lemma repr_small : forall z,
      0 <= z < I.Raw.modulus -> repr P z = z.
  Proof.
    intros z Hz. unfold repr.
    change (z mod I.Raw.modulus = z). now apply Z.mod_small.
  Qed.

  Lemma lsl_one_spec : forall x,
      unsigned (I.Raw.lsl x API.one) = repr P (2 * unsigned x).
  Proof.
    intro x. rewrite raw_lsl_spec.
    unfold expected_lsl, raw_shift_amount, width_Z.
    change ((if Z.leb (Z.of_nat I.Raw.bits) (unsigned API.one)
             then 0
             else repr P (Z.shiftl (unsigned x) (unsigned API.one))) =
            repr P (2 * unsigned x)).
    rewrite one_spec.
    assert (Z.leb (Z.of_nat I.Raw.bits) 1 = false) as Hwidth.
    { apply Z.leb_gt. pose proof I.bits_at_least_two as Hbits.
      apply Nat2Z.inj_le in Hbits. lia. }
    rewrite Hwidth. rewrite Z.shiftl_mul_pow2 by lia.
    cbn. replace (unsigned x * 2) with (2 * unsigned x) by lia.
    reflexivity.
  Qed.

  Lemma lsr_one_spec : forall x,
      unsigned (I.Raw.lsr x API.one) = Z.div (unsigned x) 2.
  Proof.
    intro x. rewrite raw_lsr_spec.
    unfold expected_lsr, raw_shift_amount, width_Z.
    change ((if Z.leb (Z.of_nat I.Raw.bits) (unsigned API.one)
             then 0 else Z.shiftr (unsigned x) (unsigned API.one)) =
            Z.div (unsigned x) 2).
    rewrite one_spec.
    assert (Z.leb (Z.of_nat I.Raw.bits) 1 = false) as Hwidth.
    { apply Z.leb_gt. pose proof I.bits_at_least_two as Hbits.
      apply Nat2Z.inj_le in Hbits. lia. }
    rewrite Hwidth, Z.shiftr_div_pow2 by lia. cbn. reflexivity.
  Qed.

  Lemma land_one_spec : forall x,
      unsigned (API.logand x API.one) = Z.modulo (unsigned x) 2.
  Proof.
    intro x. rewrite logand_spec, one_spec.
    rewrite repr_small.
    - change (Z.land (unsigned x) (Z.ones 1) = unsigned x mod 2).
      rewrite Z.land_ones by lia. reflexivity.
    - change (0 <= Z.land (unsigned x) 1 < I.Raw.modulus).
      replace (Z.land (unsigned x) 1) with (unsigned x mod 2).
      + pose proof I.bits_at_least_two as Hbits.
        assert (2 <= I.Raw.modulus).
        { rewrite I.modulus_power. replace 2 with (2 ^ 1) by reflexivity.
          apply Z.pow_le_mono_r; lia. }
        pose proof (Z.mod_pos_bound (unsigned x) 2 ltac:(lia)). lia.
      + replace 1 with (Z.ones 1) by reflexivity.
        rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Definition pow2_nat (fuel : nat) : Z := 2 ^ Z.of_nat fuel.

  Lemma pow2_nat_positive : forall fuel, 0 < pow2_nat fuel.
  Proof.
    intro fuel. unfold pow2_nat. apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma pow2_nat_succ : forall fuel,
      pow2_nat (S fuel) = 2 * pow2_nat fuel.
  Proof.
    intro fuel. unfold pow2_nat. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg. ring.
  Qed.

  Lemma pow2_bits_is_modulus :
      pow2_nat I.Raw.bits = I.Raw.modulus.
  Proof. unfold pow2_nat. symmetry. exact I.modulus_power. Qed.

  Lemma pow2_nat_le_modulus : forall fuel,
      (fuel <= I.Raw.bits)%nat -> pow2_nat fuel <= I.Raw.modulus.
  Proof.
    intros fuel Hfuel. rewrite I.modulus_power. unfold pow2_nat.
    apply Z.pow_le_mono_r; try lia.
  Qed.

  Lemma N_decompose_Z : forall n,
      Z.of_N n =
      (if N.odd n then 1 else 0) + 2 * Z.of_N (N.div2 n).
  Proof.
    intro n. destruct (N.odd n) eqn:E.
    - pose proof (N.div2_odd n) as H. rewrite E in H. cbn in H.
      rewrite H at 1. rewrite N2Z.inj_add. cbn.
      destruct (N.div2 n); reflexivity.
    - pose proof (N.div2_odd n) as H. rewrite E in H. cbn in H.
      rewrite H at 1. rewrite N2Z.inj_add. cbn.
      destruct (N.div2 n); reflexivity.
  Qed.

  Lemma Z_of_N_double : forall n,
      Z.of_N (N.double n) = 2 * Z.of_N n.
  Proof. intro n. destruct n; reflexivity. Qed.

  Lemma Z_of_N_succ_double : forall n,
      Z.of_N (N.succ_double n) = 2 * Z.of_N n + 1.
  Proof. intro n. destruct n; reflexivity. Qed.

  Lemma of_N_fuel_spec : forall fuel,
      (fuel <= I.Raw.bits)%nat -> forall n,
      unsigned (API.of_N_fuel fuel n) =
      Z.of_N n mod pow2_nat fuel.
  Proof.
    induction fuel as [|fuel IH]; intros Hfuel n.
    - cbn [pow2_nat]. rewrite Z.mod_1_r. exact zero_spec.
    - cbn -[pow2_nat]. rewrite add_spec, lsl_one_spec.
      rewrite IH by lia.
      set (m := pow2_nat fuel).
      assert (Hm : 0 < m) by (unfold m; apply pow2_nat_positive).
      assert (Hmn : m <> 0) by lia.
      assert (Hmod : 0 <= Z.of_N (N.div2 n) mod m < m)
        by now apply Z.mod_pos_bound.
      assert (Hpow : pow2_nat (S fuel) = 2 * m)
        by (unfold m; apply pow2_nat_succ).
      assert (Hcap : 2 * m <= I.Raw.modulus).
      { rewrite <- Hpow. apply pow2_nat_le_modulus. exact Hfuel. }
      rewrite (repr_small (2 * (Z.of_N (N.div2 n) mod m))) by lia.
      destruct (N.odd n) eqn:Hodd.
      + rewrite one_spec. rewrite repr_small by lia.
        rewrite Hpow.
        apply Z.mod_unique_pos with (q := Z.of_N (N.div2 n) / m).
        * lia.
        * pose proof (N_decompose_Z n) as Hdecomp.
          rewrite Hodd in Hdecomp.
          pose proof (Z.div_mod (Z.of_N (N.div2 n)) m Hmn) as Hdiv.
          rewrite Hdecomp. rewrite Hdiv at 1. ring.
      + rewrite zero_spec. rewrite repr_small by lia.
        rewrite Hpow.
        apply Z.mod_unique_pos with (q := Z.of_N (N.div2 n) / m).
        * lia.
        * pose proof (N_decompose_Z n) as Hdecomp.
          rewrite Hodd in Hdecomp.
          pose proof (Z.div_mod (Z.of_N (N.div2 n)) m Hmn) as Hdiv.
          rewrite Hdecomp. rewrite Hdiv at 1. ring.
  Qed.

  Lemma of_N_spec : forall n,
      unsigned (API.of_N n) = repr P (Z.of_N n).
  Proof.
    intro n. unfold API.of_N.
    rewrite of_N_fuel_spec; [|apply Nat.le_refl].
    unfold pow2_nat, repr.
    change (Z.of_N n mod (2 ^ Z.of_nat I.Raw.bits) =
            Z.of_N n mod I.Raw.modulus).
    now rewrite I.modulus_power.
  Qed.

  Lemma of_nat_spec : forall n,
      unsigned (API.of_nat n) = repr P (Z.of_nat n).
  Proof.
    intro n. unfold API.of_nat. rewrite of_N_spec.
    now rewrite nat_N_Z.
  Qed.

  Lemma of_Z_spec : forall z,
      unsigned (API.of_Z z) = repr P z.
  Proof.
    intro z. destruct z as [|p|p]; cbn.
    - apply zero_spec.
    - apply of_N_spec.
    - rewrite neg_spec, of_N_spec. unfold repr.
      change ((- (Z.pos p mod I.Raw.modulus)) mod I.Raw.modulus =
              Z.neg p mod I.Raw.modulus).
      replace (Z.neg p) with (- Z.pos p) by reflexivity.
      pose proof (Z.mod_opp_mod_opp (- Z.pos p) I.Raw.modulus) as H.
      replace (- - Z.pos p) with (Z.pos p) in H by ring.
      exact H.
  Qed.

  Lemma to_N_fuel_spec : forall fuel,
      (fuel <= I.Raw.bits)%nat -> forall x,
      Z.of_N (API.to_N_fuel fuel x) =
      unsigned x mod pow2_nat fuel.
  Proof.
    induction fuel as [|fuel IH]; intros Hfuel x.
    - change (0 = unsigned x mod 1). symmetry. apply Z.mod_1_r.
    - change (Z.of_N
        (let high := API.to_N_fuel fuel (I.Raw.lsr x API.one) in
         if I.Raw.eqb (I.Raw.land x API.one) API.zero
         then N.double high else N.succ_double high) =
        unsigned x mod pow2_nat (S fuel)).
      cbv zeta.
      fold API.eqb; fold API.logand; fold API.zero.
      rewrite eqb_value, land_one_spec, zero_spec.
      destruct (Z.eqb (unsigned x mod 2) 0) eqn:Hbit.
      + rewrite Z_of_N_double, IH by lia. rewrite lsr_one_spec.
        set (u := unsigned x). set (m := pow2_nat fuel).
        assert (Hu : 0 <= u)
          by (unfold u; apply (proj1 (unsigned_range x))).
        assert (Hm : 0 < m) by (unfold m; apply pow2_nat_positive).
        assert (Hmn : m <> 0) by lia.
        assert (Hlow : 0 <= u mod 2 < 2) by now apply Z.mod_pos_bound.
        assert (Hhighmod : 0 <= (u / 2) mod m < m)
          by now apply Z.mod_pos_bound.
        assert (Hpow : pow2_nat (S fuel) = 2 * m)
          by (unfold m; apply pow2_nat_succ).
        change ((u mod 2 =? 0)%Z = true) in Hbit.
        apply Z.eqb_eq in Hbit. rewrite Hpow.
        apply Z.mod_unique_pos with (q := (u / 2) / m).
        * lia.
        * pose proof (Z.div_mod u 2 ltac:(lia)) as Hu2.
          pose proof (Z.div_mod (u / 2) m Hmn) as Hdiv. lia.
      + rewrite Z_of_N_succ_double, IH by lia. rewrite lsr_one_spec.
        set (u := unsigned x). set (m := pow2_nat fuel).
        assert (Hu : 0 <= u)
          by (unfold u; apply (proj1 (unsigned_range x))).
        assert (Hm : 0 < m) by (unfold m; apply pow2_nat_positive).
        assert (Hmn : m <> 0) by lia.
        assert (Hlow : 0 <= u mod 2 < 2) by now apply Z.mod_pos_bound.
        assert (Hhighmod : 0 <= (u / 2) mod m < m)
          by now apply Z.mod_pos_bound.
        assert (Hpow : pow2_nat (S fuel) = 2 * m)
          by (unfold m; apply pow2_nat_succ).
        change ((u mod 2 =? 0)%Z = false) in Hbit.
        apply Z.eqb_neq in Hbit.
        assert (u mod 2 = 1) by lia.
        rewrite Hpow.
        apply Z.mod_unique_pos with (q := (u / 2) / m).
        * lia.
        * pose proof (Z.div_mod u 2 ltac:(lia)) as Hu2.
          pose proof (Z.div_mod (u / 2) m Hmn) as Hdiv. lia.
  Qed.

  Lemma to_N_spec : forall x,
      Z.of_N (API.to_N x) = unsigned x.
  Proof.
    intro x. unfold API.to_N. rewrite to_N_fuel_spec; [|apply Nat.le_refl].
    apply Z.mod_small. pose proof (unsigned_range x) as Hrange.
    rewrite I.modulus_power in Hrange. exact Hrange.
  Qed.

  Lemma to_N_range : forall x,
      (API.to_N x < Z.to_N I.Raw.modulus)%N.
  Proof.
    intro x. apply N2Z.inj_lt.
    rewrite to_N_spec, Z2N.id.
    - apply (proj2 (unsigned_range x)).
    - rewrite I.modulus_power. apply Z.pow_nonneg; lia.
  Qed.

  Lemma to_nat_spec : forall x,
      Z.of_nat (API.to_nat x) = unsigned x.
  Proof.
    intro x. unfold API.to_nat. rewrite N_nat_Z. apply to_N_spec.
  Qed.

  Lemma to_Z_unsigned_spec : forall x,
      API.to_Z_unsigned x = unsigned x.
  Proof.
    intro x. unfold API.to_Z_unsigned. apply to_N_spec.
  Qed.

  Lemma to_Z_signed_spec : forall x,
      API.to_Z_signed x = signed x.
  Proof.
    intro x. unfold API.to_Z_signed.
    rewrite to_Z_unsigned_spec. fold API.lts; fold API.zero.
    rewrite lts_spec, signed_zero, signed_negative.
    unfold signed, signed_of_unsigned.
    change ((if negb (Z.ltb (unsigned x) I.Raw.sign_bit)
             then unsigned x - I.Raw.modulus else unsigned x) =
            (if Z.ltb (unsigned x) I.Raw.sign_bit
             then unsigned x else unsigned x - I.Raw.modulus)).
    destruct (Z.ltb (unsigned x) I.Raw.sign_bit); reflexivity.
  Qed.

  Lemma of_N_to_N : forall x, API.of_N (API.to_N x) = x.
  Proof.
    intro x. apply unsigned_injective. rewrite of_N_spec, to_N_spec.
    apply repr_small. apply unsigned_range.
  Qed.

  Lemma to_N_of_N_bounded : forall n,
      (n < Z.to_N I.Raw.modulus)%N -> API.to_N (API.of_N n) = n.
  Proof.
    intros n Hn. apply N2Z.inj.
    rewrite to_N_spec, of_N_spec.
    unfold repr. rewrite Z.mod_small; [reflexivity|].
    split; [apply N2Z.is_nonneg|].
    apply N2Z.inj_lt in Hn. rewrite Z2N.id in Hn.
    - exact Hn.
    - rewrite I.modulus_power. apply Z.pow_nonneg; lia.
  Qed.

  Lemma raw_divu_nonzero : forall x y, unsigned y <> 0 ->
      unsigned (I.Raw.divu x y) = Z.div (unsigned x) (unsigned y).
  Proof.
    intros x y Hy. rewrite (law_divu P I.primitive_laws).
    unfold expected_divu.
    change ((if Z.eqb (unsigned y) 0 then 0
             else Z.div (unsigned x) (unsigned y)) =
            Z.div (unsigned x) (unsigned y)).
    destruct (Z.eqb (unsigned y) 0) eqn:E; [|reflexivity].
    now apply Z.eqb_eq in E.
  Qed.

  Lemma add_with_carry_spec : forall x y,
      observe_pair unsigned (API.add_with_carry x y) =
      (Z.ltb (repr P (unsigned x + unsigned y)) (unsigned x),
       repr P (unsigned x + unsigned y)).
  Proof.
    intros x y. unfold observe_pair, API.add_with_carry; cbn.
    rewrite ltu_spec, add_spec. reflexivity.
  Qed.

  Lemma sub_with_borrow_spec : forall x y,
      observe_pair unsigned (API.sub_with_borrow x y) =
      (Z.ltb (unsigned x) (unsigned y),
       repr P (unsigned x - unsigned y)).
  Proof.
    intros x y. unfold observe_pair, API.sub_with_borrow; cbn.
    rewrite ltu_spec, sub_spec. reflexivity.
  Qed.

  Lemma neg_checked_spec : forall x,
      observe_option unsigned (API.neg_checked x) =
      if Z.eqb (unsigned x) I.Raw.sign_bit then None
      else Some (repr P (- unsigned x)).
  Proof.
    intros x. unfold API.neg_checked, API.is_min_signed.
    change (observe_option unsigned
      (if I.Raw.eqb x I.Raw.min_signed then None else Some (I.Raw.neg x)) =
      if Z.eqb (unsigned x) I.Raw.sign_bit then None
      else Some (repr P (- unsigned x))).
    pose proof (law_eqb P I.primitive_laws x I.Raw.min_signed) as Heq.
    pose proof (law_min_signed P I.primitive_laws) as Hmin.
    change (I.Raw.eqb x I.Raw.min_signed =
      Z.eqb (unsigned x) (unsigned I.Raw.min_signed)) in Heq.
    change (unsigned I.Raw.min_signed = I.Raw.sign_bit) in Hmin.
    rewrite Heq, Hmin.
    destruct (Z.eqb (unsigned x) I.Raw.sign_bit); simpl.
    - reflexivity.
    - f_equal. exact (law_neg P I.primitive_laws x).
  Qed.

  Lemma add_checked_spec : forall x y,
      observe_option unsigned (API.add_checked x y) =
      let r := repr P (unsigned x + unsigned y) in
      let sx := Z.ltb (signed x) 0 in
      let sy := Z.ltb (signed y) 0 in
      let sr := Z.ltb (signed_of_unsigned P r) 0 in
      if andb (Bool.eqb sx sy) (negb (Bool.eqb sx sr))
      then None else Some r.
  Proof.
    intros x y. unfold API.add_checked, observe_option.
    fold API.add; fold API.lts; fold API.zero.
    rewrite !lts_spec, signed_zero.
    unfold signed. rewrite add_spec.
    destruct (Z.ltb (signed_of_unsigned P (unsigned x)) 0),
      (Z.ltb (signed_of_unsigned P (unsigned y)) 0),
      (Z.ltb (signed_of_unsigned P (repr P (unsigned x + unsigned y))) 0);
      simpl; rewrite ?add_spec; reflexivity.
  Qed.

  Lemma sub_checked_spec : forall x y,
      observe_option unsigned (API.sub_checked x y) =
      let r := repr P (unsigned x - unsigned y) in
      let sx := Z.ltb (signed x) 0 in
      let sy := Z.ltb (signed y) 0 in
      let sr := Z.ltb (signed_of_unsigned P r) 0 in
      if andb (negb (Bool.eqb sx sy)) (negb (Bool.eqb sx sr))
      then None else Some r.
  Proof.
    intros x y. unfold API.sub_checked, observe_option.
    fold API.sub; fold API.lts; fold API.zero.
    rewrite !lts_spec, signed_zero.
    unfold signed. rewrite sub_spec.
    destruct (Z.ltb (signed_of_unsigned P (unsigned x)) 0),
      (Z.ltb (signed_of_unsigned P (unsigned y)) 0),
      (Z.ltb (signed_of_unsigned P (repr P (unsigned x - unsigned y))) 0);
      simpl; rewrite ?sub_spec; reflexivity.
  Qed.

  Definition checked_mul_operand (x : API.t) (negative : bool) : API.t :=
    if negative then API.neg x else x.

  Definition checked_mul_limit (negative : bool) : API.t :=
    if negative then API.min_signed else API.sub API.min_signed API.one.

  Lemma mul_checked_control_spec : forall x y,
      observe_option unsigned (API.mul_checked x y) =
      let sx := Z.ltb (signed x) 0 in
      let sy := Z.ltb (signed y) 0 in
      let ax := checked_mul_operand x sx in
      let ay := checked_mul_operand y sy in
      let limit := checked_mul_limit (xorb sx sy) in
      if Z.eqb (unsigned ay) 0 then Some 0
      else if Z.ltb (unsigned (I.Raw.divu limit ay)) (unsigned ax) then None
      else Some (repr P (unsigned x * unsigned y)).
  Proof.
    intros x y. unfold API.mul_checked, observe_option,
      checked_mul_operand, checked_mul_limit.
    fold API.lts; fold API.zero; fold API.eqb; fold API.mul.
    rewrite !lts_spec, signed_zero.
    repeat rewrite eqb_value. rewrite zero_spec. repeat rewrite ltu_spec.
    all: repeat match goal with
      | |- context [if ?b then _ else _] => destruct b eqn:E; simpl
      end;
      repeat match goal with
      | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:El; simpl
      end;
      try rewrite zero_spec;
      try rewrite mul_spec;
      reflexivity.
  Qed.

  Lemma shift_left_spec : forall x amount,
      unsigned (API.shift_left x amount) =
      if Nat.leb API.bits amount then 0
      else expected_lsl P x (API.of_nat amount).
  Proof.
    intros x amount. unfold API.shift_left.
    destruct (Nat.leb API.bits amount); simpl.
    - apply zero_spec.
    - apply raw_lsl_spec.
  Qed.

  Lemma shift_right_logical_spec : forall x amount,
      unsigned (API.shift_right_logical x amount) =
      if Nat.leb API.bits amount then 0
      else expected_lsr P x (API.of_nat amount).
  Proof.
    intros x amount. unfold API.shift_right_logical.
    destruct (Nat.leb API.bits amount); simpl.
    - apply zero_spec.
    - apply raw_lsr_spec.
  Qed.

  Lemma shift_right_arithmetic_spec : forall x amount,
      unsigned (API.shift_right_arithmetic x amount) =
      if Nat.leb API.bits amount
      then if Z.ltb (signed x) 0 then I.Raw.modulus - 1 else 0
      else expected_asr P x (API.of_nat amount).
  Proof.
    intros x amount. unfold API.shift_right_arithmetic.
    fold API.lts; fold API.zero; fold API.max_unsigned.
    rewrite lts_spec, signed_zero.
    destruct (Nat.leb API.bits amount) eqn:Ea; simpl.
    - destruct (Z.ltb (signed x) 0); [apply max_unsigned_spec | apply zero_spec].
    - apply raw_asr_spec.
  Qed.

  Lemma divu_spec : forall x y,
      observe_option unsigned (API.divu x y) =
      if Z.eqb (unsigned y) 0 then None
      else Some (Z.div (unsigned x) (unsigned y)).
  Proof.
    intros x y. unfold API.divu, observe_option.
    fold API.eqb; fold API.zero.
    rewrite eqb_value, zero_spec.
    destruct (Z.eqb (unsigned y) 0) eqn:E; simpl; auto.
    f_equal.
    change (unsigned (I.Raw.divu x y) = Z.div (unsigned x) (unsigned y)).
    rewrite (law_divu P I.primitive_laws). unfold expected_divu.
    change ((if Z.eqb (unsigned y) 0 then 0
             else Z.div (unsigned x) (unsigned y)) =
            Z.div (unsigned x) (unsigned y)).
    now rewrite E.
  Qed.

  Lemma modu_spec : forall x y,
      observe_option unsigned (API.modu x y) =
      if Z.eqb (unsigned y) 0 then None
      else Some (Z.modulo (unsigned x) (unsigned y)).
  Proof.
    intros x y. unfold API.modu, observe_option.
    fold API.eqb; fold API.zero.
    rewrite eqb_value, zero_spec.
    destruct (Z.eqb (unsigned y) 0) eqn:E; simpl; auto.
    f_equal.
    change (unsigned (I.Raw.modu x y) = Z.modulo (unsigned x) (unsigned y)).
    rewrite (law_modu P I.primitive_laws). unfold expected_modu.
    change ((if Z.eqb (unsigned y) 0 then unsigned x
             else Z.modulo (unsigned x) (unsigned y)) =
            Z.modulo (unsigned x) (unsigned y)).
    now rewrite E.
  Qed.

  Lemma divmodu_spec : forall x y,
      observe_divmod unsigned (API.divmodu x y) =
      if Z.eqb (unsigned y) 0 then None
      else Some (Z.div (unsigned x) (unsigned y),
                 Z.modulo (unsigned x) (unsigned y)).
  Proof.
    intros x y. unfold API.divmodu, observe_divmod.
    fold API.eqb; fold API.zero.
    rewrite eqb_value, zero_spec.
    destruct (Z.eqb (unsigned y) 0) eqn:E; simpl; auto.
    rewrite (law_divu P I.primitive_laws), (law_modu P I.primitive_laws).
    unfold expected_divu, expected_modu.
    change (Some
      ((if Z.eqb (unsigned y) 0 then 0
        else Z.div (unsigned x) (unsigned y)),
       (if Z.eqb (unsigned y) 0 then unsigned x
        else Z.modulo (unsigned x) (unsigned y))) =
      Some (Z.div (unsigned x) (unsigned y),
            Z.modulo (unsigned x) (unsigned y))).
    now rewrite E.
  Qed.

  Lemma divs_checked_spec : forall x y,
      observe_option unsigned (API.divs_checked x y) =
      if Z.eqb (unsigned y) 0 then None
      else if andb (Z.eqb (unsigned x) I.Raw.sign_bit)
                       (Z.eqb (unsigned y) (I.Raw.modulus - 1))
           then None
           else Some (repr P (Z.quot (signed x) (signed y))).
  Proof.
    intros x y. unfold API.divs_checked, API.is_min_signed,
      API.is_minus_one, observe_option.
    fold API.eqb; fold API.zero; fold API.min_signed; fold API.max_unsigned.
    repeat rewrite eqb_value.
    rewrite zero_spec, min_signed_spec, max_unsigned_spec.
    destruct (Z.eqb (unsigned y) 0) eqn:Ey; simpl; auto.
    destruct (andb (Z.eqb (unsigned x) I.Raw.sign_bit)
                   (Z.eqb (unsigned y) (I.Raw.modulus - 1))) eqn:Eo;
      simpl; auto.
    f_equal.
    change (unsigned (I.Raw.divs x y) = repr P (Z.quot (signed x) (signed y))).
    rewrite (law_divs P I.primitive_laws). unfold expected_divs.
    assert (signed y <> 0).
    { apply Z.eqb_neq in Ey. intro Hs.
      unfold signed, signed_of_unsigned in Hs.
      change ((if Z.ltb (unsigned y) I.Raw.sign_bit then unsigned y
               else unsigned y - I.Raw.modulus) = 0) in Hs.
      pose proof (unsigned_range y).
      destruct (Z.ltb (unsigned y) I.Raw.sign_bit); lia. }
    change ((if Z.eqb (signed y) 0 then 0
             else repr P (Z.quot (signed x) (signed y))) =
            repr P (Z.quot (signed x) (signed y))).
    destruct (Z.eqb (signed y) 0) eqn:Es; [|reflexivity].
    apply Z.eqb_eq in Es. contradiction.
  Qed.

  Lemma rems_spec : forall x y,
      observe_option unsigned (API.rems x y) =
      if Z.eqb (unsigned y) 0 then None
      else Some (repr P (Z.rem (signed x) (signed y))).
  Proof.
    intros x y. unfold API.rems, observe_option.
    fold API.eqb; fold API.zero.
    rewrite eqb_value, zero_spec.
    destruct (Z.eqb (unsigned y) 0) eqn:Ey; simpl; auto.
    f_equal.
    change (unsigned (I.Raw.rems x y) = repr P (Z.rem (signed x) (signed y))).
    rewrite (law_rems P I.primitive_laws). unfold expected_rems.
    assert (signed y <> 0).
    { apply Z.eqb_neq in Ey. intro Hs.
      unfold signed, signed_of_unsigned in Hs.
      change ((if Z.ltb (unsigned y) I.Raw.sign_bit then unsigned y
               else unsigned y - I.Raw.modulus) = 0) in Hs.
      pose proof (unsigned_range y).
      destruct (Z.ltb (unsigned y) I.Raw.sign_bit); lia. }
    change ((if Z.eqb (signed y) 0 then unsigned x
             else repr P (Z.rem (signed x) (signed y))) =
            repr P (Z.rem (signed x) (signed y))).
    destruct (Z.eqb (signed y) 0) eqn:Es; [|reflexivity].
    apply Z.eqb_eq in Es. contradiction.
  Qed.

  Lemma of_Z_unsigned_checked_none : forall z,
      API.of_Z_unsigned_checked z = None <->
      z < 0 \/ I.Raw.modulus <= z.
  Proof.
    intro z. unfold API.of_Z_unsigned_checked.
    change ((if (Z.leb 0 z && Z.ltb z I.Raw.modulus)%bool
             then Some (API.of_Z z) else None) = None <->
            z < 0 \/ I.Raw.modulus <= z).
    destruct (Z.leb 0 z) eqn:L; destruct (Z.ltb z I.Raw.modulus) eqn:U;
      simpl.
    - split; [discriminate|].
      intro H. apply Z.leb_le in L. apply Z.ltb_lt in U. lia.
    - split; [intro; right; now apply Z.ltb_ge|tauto].
    - split; [intro; left; now apply Z.leb_gt|tauto].
    - split; [intro; left; now apply Z.leb_gt|tauto].
  Qed.

  Lemma of_Z_signed_checked_none : forall z,
      API.of_Z_signed_checked z = None <->
      z < - I.Raw.sign_bit \/ I.Raw.sign_bit - 1 < z.
  Proof.
    intro z. unfold API.of_Z_signed_checked, API.signed_min, API.signed_max.
    rewrite I.signed_max_spec.
    change ((if (Z.leb (- I.Raw.sign_bit) z &&
                 Z.leb z (I.Raw.sign_bit - 1))%bool
             then Some (API.of_Z z) else None) = None <->
            z < - I.Raw.sign_bit \/ I.Raw.sign_bit - 1 < z).
    destruct (Z.leb (- I.Raw.sign_bit) z) eqn:L;
      destruct (Z.leb z (I.Raw.sign_bit - 1)) eqn:U; simpl.
    - split; [discriminate|].
      intro H. apply Z.leb_le in L. apply Z.leb_le in U. lia.
    - split; [intro; right; now apply Z.leb_gt|tauto].
    - split; [intro; left; now apply Z.leb_gt|tauto].
    - split; [intro; left; now apply Z.leb_gt|tauto].
  Qed.

  Lemma of_Z_unsigned_checked_some : forall z,
      0 <= z < I.Raw.modulus ->
      API.of_Z_unsigned_checked z = Some (API.of_Z z).
  Proof.
    intros z [L U]. unfold API.of_Z_unsigned_checked.
    change ((if (Z.leb 0 z && Z.ltb z I.Raw.modulus)%bool
             then Some (API.of_Z z) else None) = Some (API.of_Z z)).
    assert (Z.leb 0 z = true) as HL by now apply Z.leb_le.
    assert (Z.ltb z I.Raw.modulus = true) as HU by now apply Z.ltb_lt.
    now rewrite HL, HU.
  Qed.

  Lemma of_Z_signed_checked_some : forall z,
      - I.Raw.sign_bit <= z <= I.Raw.sign_bit - 1 ->
      API.of_Z_signed_checked z = Some (API.of_Z z).
  Proof.
    intros z [L U]. unfold API.of_Z_signed_checked,
      API.signed_min, API.signed_max.
    rewrite I.signed_max_spec.
    change ((if (Z.leb (- I.Raw.sign_bit) z &&
                 Z.leb z (I.Raw.sign_bit - 1))%bool
             then Some (API.of_Z z) else None) = Some (API.of_Z z)).
    assert (Z.leb (- I.Raw.sign_bit) z = true) as HL by now apply Z.leb_le.
    assert (Z.leb z (I.Raw.sign_bit - 1) = true) as HU by now apply Z.leb_le.
    now rewrite HL, HU.
  Qed.

  Lemma of_N_checked_none : forall n,
      (Z.to_N I.Raw.modulus <= n)%N ->
      API.of_N_checked n = None.
  Proof.
    intros n Hn. unfold API.of_N_checked.
    change ((if (n <? Z.to_N I.Raw.modulus)%N
             then Some (API.of_N n) else None) = None).
    destruct (n <? Z.to_N I.Raw.modulus)%N eqn:E.
    - apply N.ltb_lt in E. lia.
    - reflexivity.
  Qed.

  Lemma of_N_checked_some : forall n,
      (n < Z.to_N I.Raw.modulus)%N ->
      API.of_N_checked n = Some (API.of_N n).
  Proof.
    intros n Hn. unfold API.of_N_checked.
    change ((if (n <? Z.to_N I.Raw.modulus)%N
             then Some (API.of_N n) else None) = Some (API.of_N n)).
    destruct (n <? Z.to_N I.Raw.modulus)%N eqn:E.
    - reflexivity.
    - apply N.ltb_ge in E. lia.
  Qed.

  Lemma of_nat_checked_none : forall n,
      (Z.to_N I.Raw.modulus <= N.of_nat n)%N ->
      API.of_nat_checked n = None.
  Proof.
    intros n Hn. unfold API.of_nat_checked. now apply of_N_checked_none.
  Qed.

  Lemma of_nat_checked_some : forall n,
      (N.of_nat n < Z.to_N I.Raw.modulus)%N ->
      API.of_nat_checked n = Some (API.of_nat n).
  Proof.
    intros n Hn. unfold API.of_nat_checked, API.of_nat.
    now apply of_N_checked_some.
  Qed.

  Lemma shift_left_signed_spec : forall x count,
      unsigned (API.shift_left_signed x count) =
      if Z.ltb (signed count) 0
      then expected_asr P x (API.neg count)
      else expected_lsl P x count.
  Proof.
    intros x count. unfold API.shift_left_signed.
    rewrite lts_spec, signed_zero.
    destruct (Z.ltb (signed count) 0); simpl;
      [apply (law_asr P I.primitive_laws) | apply (law_lsl P I.primitive_laws)].
  Qed.

  Lemma shift_right_signed_spec : forall x count,
      unsigned (API.shift_right_signed x count) =
      if Z.ltb (signed count) 0
      then expected_lsl P x (API.neg count)
      else expected_asr P x count.
  Proof.
    intros x count. unfold API.shift_right_signed.
    rewrite lts_spec, signed_zero.
    destruct (Z.ltb (signed count) 0); simpl;
      [apply (law_lsl P I.primitive_laws) | apply (law_asr P I.primitive_laws)].
  Qed.
End Prove.

Module Word8DerivedInput.
  Module Raw := Word8.Raw. Module Observation := Word8Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word8_model.
  Definition primitive_laws := word8_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 8)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit. Proof. change (0 < 128); lia. Qed.
End Word8DerivedInput.
Module Word8Derived := Prove Word8DerivedInput.

Module Word16DerivedInput.
  Module Raw := Word16.Raw. Module Observation := Word16Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word16_model.
  Definition primitive_laws := word16_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 16)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit. Proof. change (0 < 32768); lia. Qed.
End Word16DerivedInput.
Module Word16Derived := Prove Word16DerivedInput.

Module Word32DerivedInput.
  Module Raw := Word32.Raw. Module Observation := Word32Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word32_model.
  Definition primitive_laws := word32_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 32)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit.
  Proof. change (0 < 2147483648); lia. Qed.
End Word32DerivedInput.
Module Word32Derived := Prove Word32DerivedInput.

Module Word64DerivedInput.
  Module Raw := Word64.Raw. Module Observation := Word64Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word64_model.
  Definition primitive_laws := word64_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 64)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit.
  Proof. change (0 < 9223372036854775808); lia. Qed.
End Word64DerivedInput.
Module Word64Derived := Prove Word64DerivedInput.

Module Word128DerivedInput.
  Module Raw := Word128.Raw. Module Observation := Word128Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word128_model.
  Definition primitive_laws := word128_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 128)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit.
  Proof. change (0 < 170141183460469231731687303715884105728); lia. Qed.
End Word128DerivedInput.
Module Word128Derived := Prove Word128DerivedInput.

Module Word256DerivedInput.
  Module Raw := Word256.Raw. Module Observation := Word256Observation.
  Module Model := PrimitiveWordAxioms.BuildModel Raw Observation.
  Definition primitive_model := word256_model.
  Definition primitive_laws := word256_laws.
  Lemma bits_at_least_two : (2 <= Raw.bits)%nat.
  Proof. change (2 <= 256)%nat; lia. Qed.
  Lemma modulus_power : Raw.modulus = 2 ^ Z.of_nat Raw.bits.
  Proof. reflexivity. Qed.
  Lemma modulus_twice_sign_bit : Raw.modulus = 2 * Raw.sign_bit.
  Proof. reflexivity. Qed.
  Lemma signed_max_spec : Raw.signed_max = Raw.sign_bit - 1.
  Proof. reflexivity. Qed.
  Lemma sign_bit_positive : 0 < Raw.sign_bit.
  Proof. change (0 < 57896044618658097711785492504343953926634992332820282019728792003956564819968); lia. Qed.
End Word256DerivedInput.
Module Word256Derived := Prove Word256DerivedInput.
