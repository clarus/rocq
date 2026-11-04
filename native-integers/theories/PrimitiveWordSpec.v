(************************************************************************)
(* Shared mathematical contract for the experimental primitive words.   *)
(************************************************************************)

From Stdlib Require Import ZArith Bool.

Open Scope Z_scope.

(** This is a logical view of the twenty-operation [Raw] interface.  The
    records below are definitions/interfaces; concrete trust enters only at
    the six [word*_laws] declarations in [PrimitiveWordAxioms]. *)
Record model := {
  carrier : Set;
  bit_count : nat;
  modulus : Z;
  sign_bit : Z;

  raw_zero : carrier;
  raw_one : carrier;
  raw_max_unsigned : carrier;
  raw_min_signed : carrier;

  raw_neg : carrier -> carrier;
  raw_add : carrier -> carrier -> carrier;
  raw_sub : carrier -> carrier -> carrier;
  raw_mul : carrier -> carrier -> carrier;
  raw_land : carrier -> carrier -> carrier;
  raw_lor : carrier -> carrier -> carrier;
  raw_lxor : carrier -> carrier -> carrier;
  raw_lnot : carrier -> carrier;
  raw_eqb : carrier -> carrier -> bool;
  raw_ltu : carrier -> carrier -> bool;
  raw_leu : carrier -> carrier -> bool;
  raw_lts : carrier -> carrier -> bool;
  raw_les : carrier -> carrier -> bool;
  raw_lsl : carrier -> carrier -> carrier;
  raw_lsr : carrier -> carrier -> carrier;
  raw_asr : carrier -> carrier -> carrier;
  raw_divu : carrier -> carrier -> carrier;
  raw_modu : carrier -> carrier -> carrier;
  raw_divs : carrier -> carrier -> carrier;
  raw_rems : carrier -> carrier -> carrier;

  observe_unsigned : carrier -> Z
}.

Arguments carrier _ : clear implicits.

Definition width_Z (P : model) : Z := Z.of_nat (bit_count P).

Definition repr (P : model) (z : Z) : Z := Z.modulo z (modulus P).

Definition observe_signed (P : model) (x : carrier P) : Z :=
  let u := observe_unsigned P x in
  if Z.ltb u (sign_bit P) then u else (u - modulus P)%Z.

(** Raw shift counts are unsigned words, not signed-count API arguments. *)
Definition raw_shift_amount (P : model) (count : carrier P) : Z :=
  observe_unsigned P count.

Definition expected_lsl (P : model) (x count : carrier P) : Z :=
  let amount := raw_shift_amount P count in
  if Z.leb (width_Z P) amount then 0
  else repr P (Z.shiftl (observe_unsigned P x) amount).

Definition expected_lsr (P : model) (x count : carrier P) : Z :=
  let amount := raw_shift_amount P count in
  if Z.leb (width_Z P) amount then 0
  else Z.shiftr (observe_unsigned P x) amount.

Definition expected_asr (P : model) (x count : carrier P) : Z :=
  let amount := raw_shift_amount P count in
  let signed := observe_signed P x in
  if Z.leb (width_Z P) amount then
    if Z.ltb signed 0 then repr P (-1) else 0
  else repr P (Z.shiftr signed amount).

Definition expected_divu (P : model) (x y : carrier P) : Z :=
  let divisor := observe_unsigned P y in
  if Z.eqb divisor 0 then 0
  else Z.div (observe_unsigned P x) divisor.

Definition expected_modu (P : model) (x y : carrier P) : Z :=
  let divisor := observe_unsigned P y in
  if Z.eqb divisor 0 then observe_unsigned P x
  else Z.modulo (observe_unsigned P x) divisor.

Definition expected_divs (P : model) (x y : carrier P) : Z :=
  let divisor := observe_signed P y in
  if Z.eqb divisor 0 then 0
  else repr P (Z.quot (observe_signed P x) divisor).

Definition expected_rems (P : model) (x y : carrier P) : Z :=
  let divisor := observe_signed P y in
  if Z.eqb divisor 0 then observe_unsigned P x
  else repr P (Z.rem (observe_signed P x) divisor).

(** These facts contain no primitive assumptions.  Every concrete instance
    proves them from its literal width constants. *)
Record well_formed (P : model) : Prop := {
  bit_count_positive : (0 < bit_count P)%nat;
  modulus_is_power : modulus P = (2 ^ width_Z P)%Z;
  sign_bit_is_power :
    sign_bit P = (2 ^ Z.of_nat (Nat.pred (bit_count P)))%Z
}.

(** One concrete value of this record is the Int63-style specification
    assumption for one primitive width.  There are six such values, and each
    has exactly 26 named clauses: six representation clauses and one clause
    for each of the twenty raw operations. *)
Record laws (P : model) : Prop := {
  law_unsigned_range : forall x : carrier P,
      (0 <= observe_unsigned P x < modulus P)%Z;
  law_unsigned_injective : forall x y : carrier P,
      observe_unsigned P x = observe_unsigned P y -> x = y;
  law_zero : observe_unsigned P (raw_zero P) = 0;
  law_one : observe_unsigned P (raw_one P) = 1;
  law_max_unsigned :
      observe_unsigned P (raw_max_unsigned P) = (modulus P - 1)%Z;
  law_min_signed : observe_unsigned P (raw_min_signed P) = sign_bit P;

  law_neg : forall x,
      observe_unsigned P (raw_neg P x) =
      repr P (- observe_unsigned P x);
  law_add : forall x y,
      observe_unsigned P (raw_add P x y) =
      repr P (observe_unsigned P x + observe_unsigned P y);
  law_sub : forall x y,
      observe_unsigned P (raw_sub P x y) =
      repr P (observe_unsigned P x - observe_unsigned P y);
  law_mul : forall x y,
      observe_unsigned P (raw_mul P x y) =
      repr P (observe_unsigned P x * observe_unsigned P y);
  law_land : forall x y,
      observe_unsigned P (raw_land P x y) =
      repr P (Z.land (observe_unsigned P x) (observe_unsigned P y));
  law_lor : forall x y,
      observe_unsigned P (raw_lor P x y) =
      repr P (Z.lor (observe_unsigned P x) (observe_unsigned P y));
  law_lxor : forall x y,
      observe_unsigned P (raw_lxor P x y) =
      repr P (Z.lxor (observe_unsigned P x) (observe_unsigned P y));
  law_lnot : forall x,
      observe_unsigned P (raw_lnot P x) =
      repr P (Z.lnot (observe_unsigned P x));
  law_eqb : forall x y,
      raw_eqb P x y = Z.eqb (observe_unsigned P x) (observe_unsigned P y);
  law_ltu : forall x y,
      raw_ltu P x y = Z.ltb (observe_unsigned P x) (observe_unsigned P y);
  law_leu : forall x y,
      raw_leu P x y = Z.leb (observe_unsigned P x) (observe_unsigned P y);
  law_lts : forall x y,
      raw_lts P x y = Z.ltb (observe_signed P x) (observe_signed P y);
  law_les : forall x y,
      raw_les P x y = Z.leb (observe_signed P x) (observe_signed P y);
  law_lsl : forall x count,
      observe_unsigned P (raw_lsl P x count) = expected_lsl P x count;
  law_lsr : forall x count,
      observe_unsigned P (raw_lsr P x count) = expected_lsr P x count;
  law_asr : forall x count,
      observe_unsigned P (raw_asr P x count) = expected_asr P x count;
  law_divu : forall x y,
      observe_unsigned P (raw_divu P x y) = expected_divu P x y;
  law_modu : forall x y,
      observe_unsigned P (raw_modu P x y) = expected_modu P x y;
  law_divs : forall x y,
      observe_unsigned P (raw_divs P x y) = expected_divs P x y;
  law_rems : forall x y,
      observe_unsigned P (raw_rems P x y) = expected_rems P x y
}.

(** The presentation functor only names record projections.  Its module
    parameters are an abstract interface and are discharged by each concrete
    width instance; they are not additional global axioms. *)
Module Type INSTANCE.
  Parameter primitive_model : model.
  Parameter primitive_model_well_formed : well_formed primitive_model.
  Parameter primitive_model_laws : laws primitive_model.
End INSTANCE.

Module Present (I : INSTANCE).
  Definition P := I.primitive_model.
  Definition t := carrier P.
  Definition unsigned := observe_unsigned P.
  Definition signed := observe_signed P.
  Definition well_formed := I.primitive_model_well_formed.

  Definition unsigned_range := law_unsigned_range P I.primitive_model_laws.
  Definition unsigned_injective :=
    law_unsigned_injective P I.primitive_model_laws.
  Definition zero_spec := law_zero P I.primitive_model_laws.
  Definition one_spec := law_one P I.primitive_model_laws.
  Definition max_unsigned_spec := law_max_unsigned P I.primitive_model_laws.
  Definition min_signed_spec := law_min_signed P I.primitive_model_laws.
  Definition neg_spec := law_neg P I.primitive_model_laws.
  Definition add_spec := law_add P I.primitive_model_laws.
  Definition sub_spec := law_sub P I.primitive_model_laws.
  Definition mul_spec := law_mul P I.primitive_model_laws.
  Definition land_spec := law_land P I.primitive_model_laws.
  Definition lor_spec := law_lor P I.primitive_model_laws.
  Definition lxor_spec := law_lxor P I.primitive_model_laws.
  Definition lnot_spec := law_lnot P I.primitive_model_laws.
  Definition eqb_spec := law_eqb P I.primitive_model_laws.
  Definition ltu_spec := law_ltu P I.primitive_model_laws.
  Definition leu_spec := law_leu P I.primitive_model_laws.
  Definition lts_spec := law_lts P I.primitive_model_laws.
  Definition les_spec := law_les P I.primitive_model_laws.
  Definition lsl_spec := law_lsl P I.primitive_model_laws.
  Definition lsr_spec := law_lsr P I.primitive_model_laws.
  Definition asr_spec := law_asr P I.primitive_model_laws.
  Definition divu_spec := law_divu P I.primitive_model_laws.
  Definition modu_spec := law_modu P I.primitive_model_laws.
  Definition divs_spec := law_divs P I.primitive_model_laws.
  Definition rems_spec := law_rems P I.primitive_model_laws.
End Present.
