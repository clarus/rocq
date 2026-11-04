(************************************************************************)
(* Shared public definitions for the experimental scalar primitive words. *)
(************************************************************************)

From Stdlib Require Import ZArith NArith Bool.

Module Type RAW_SCALAR.
  Parameter t : Set.
  Parameter bits : nat.
  Parameter modulus : Z.
  Parameter sign_bit : Z.
  Parameter signed_max : Z.

  Parameter zero one max_unsigned min_signed : t.
  Parameter neg : t -> t.
  Parameter add sub mul land lor lxor : t -> t -> t.
  Parameter lnot : t -> t.
  Parameter eqb ltu leu lts les : t -> t -> bool.
  Parameter lsl lsr asr : t -> t -> t.
  Parameter divu modu divs rems : t -> t -> t.
End RAW_SCALAR.

Module Make (P : RAW_SCALAR).
  Definition t : Set := P.t.

  Definition bits : nat := P.bits.
  Definition modulus : Z := P.modulus.
  Definition sign_bit : Z := P.sign_bit.
  Definition signed_min : Z := (- P.sign_bit)%Z.
  Definition signed_max : Z := P.signed_max.

  Definition zero : t := P.zero.
  Definition one : t := P.one.
  Definition max_unsigned : t := P.max_unsigned.
  Definition min_signed : t := P.min_signed.

  Definition eqb : t -> t -> bool := P.eqb.
  Definition ltu : t -> t -> bool := P.ltu.
  Definition leu : t -> t -> bool := P.leu.
  Definition lts : t -> t -> bool := P.lts.
  Definition les : t -> t -> bool := P.les.
  Definition ltb_unsigned : t -> t -> bool := P.ltu.
  Definition leb_unsigned : t -> t -> bool := P.leu.
  Definition ltb_signed : t -> t -> bool := P.lts.
  Definition leb_signed : t -> t -> bool := P.les.

  Definition neg : t -> t := P.neg.
  Definition add : t -> t -> t := P.add.
  Definition sub : t -> t -> t := P.sub.
  Definition mul : t -> t -> t := P.mul.
  Definition logand : t -> t -> t := P.land.
  Definition logor : t -> t -> t := P.lor.
  Definition logxor : t -> t -> t := P.lxor.
  Definition lognot : t -> t := P.lnot.

  Definition add_with_carry (x y : t) : bool * t :=
    let r := add x y in (ltu r x, r).

  Definition sub_with_borrow (x y : t) : bool * t :=
    let r := sub x y in (ltu x y, r).

  Definition is_min_signed (x : t) : bool := eqb x min_signed.
  Definition is_minus_one (x : t) : bool := eqb x max_unsigned.

  Definition neg_checked (x : t) : option t :=
    if is_min_signed x then None else Some (neg x).

  Definition add_checked (x y : t) : option t :=
    let r := add x y in
    let sx := lts x zero in
    let sy := lts y zero in
    let sr := lts r zero in
    if andb (Bool.eqb sx sy) (negb (Bool.eqb sx sr))
    then None else Some r.

  Definition sub_checked (x y : t) : option t :=
    let r := sub x y in
    let sx := lts x zero in
    let sy := lts y zero in
    let sr := lts r zero in
    if andb (negb (Bool.eqb sx sy)) (negb (Bool.eqb sx sr))
    then None else Some r.

  Definition unsigned_abs (x : t) : t :=
    if lts x zero then neg x else x.

  Definition mul_checked (x y : t) : option t :=
    let sx := lts x zero in
    let sy := lts y zero in
    let ax := if sx then neg x else x in
    let ay := if sy then neg y else y in
    let negative := xorb sx sy in
    let limit := if negative then min_signed else sub min_signed one in
    if eqb ay zero then Some zero
    else if ltu (P.divu limit ay) ax then None
    else Some (mul x y).

  Definition divmodu (x y : t) : option (t * t) :=
    if eqb y zero then None else Some (P.divu x y, P.modu x y).

  Definition divu (x y : t) : option t :=
    if eqb y zero then None else Some (P.divu x y).

  Definition modu (x y : t) : option t :=
    if eqb y zero then None else Some (P.modu x y).

  Definition divs_checked (x y : t) : option t :=
    if eqb y zero then None
    else if andb (is_min_signed x) (is_minus_one y) then None
    else Some (P.divs x y).

  Definition rems (x y : t) : option t :=
    if eqb y zero then None else Some (P.rems x y).

  Fixpoint of_N_fuel (fuel : nat) (value : N) : t :=
    match fuel with
    | O => zero
    | S fuel' =>
        let low := if N.odd value then one else zero in
        add low (P.lsl (of_N_fuel fuel' (N.div2 value)) one)
    end.

  Definition of_N (value : N) : t := of_N_fuel bits value.

  Definition of_Z (value : Z) : t :=
    match value with
    | Z0 => zero
    | Zpos p => of_N (Npos p)
    | Zneg p => neg (of_N (Npos p))
    end.

  Definition of_nat (value : nat) : t := of_N (N.of_nat value).

  Fixpoint to_N_fuel (fuel : nat) (value : t) : N :=
    match fuel with
    | O => 0%N
    | S fuel' =>
        (* Keep the recursive call outside the symbolic branches. Otherwise
           conversion can duplicate it at every bit when checking proofs. *)
        (if eqb (logand value one) zero then N.double else N.succ_double)
          (to_N_fuel fuel' (P.lsr value one))
    end.

  Definition to_N (value : t) : N := to_N_fuel bits value.
  Definition to_Z_unsigned (value : t) : Z := Z.of_N (to_N value).
  Definition to_Z_signed (value : t) : Z :=
    let unsigned := to_Z_unsigned value in
    if lts value zero then (unsigned - modulus)%Z else unsigned.
  Definition to_nat (value : t) : nat := N.to_nat (to_N value).

  Definition of_Z_unsigned_checked (value : Z) : option t :=
    if ((0 <=? value)%Z && (value <? modulus)%Z)%bool
    then Some (of_Z value) else None.

  Definition of_Z_signed_checked (value : Z) : option t :=
    if ((signed_min <=? value)%Z && (value <=? signed_max)%Z)%bool
    then Some (of_Z value) else None.

  Definition of_N_checked (value : N) : option t :=
    if (value <? Z.to_N modulus)%N then Some (of_N value) else None.

  Definition of_nat_checked (value : nat) : option t :=
    of_N_checked (N.of_nat value).

  Definition shift_left (value : t) (amount : nat) : t :=
    if Nat.leb bits amount then zero else P.lsl value (of_nat amount).

  Definition shift_right_logical (value : t) (amount : nat) : t :=
    if Nat.leb bits amount then zero else P.lsr value (of_nat amount).

  Definition shift_right_arithmetic (value : t) (amount : nat) : t :=
    if Nat.leb bits amount
    then if lts value zero then max_unsigned else zero
    else P.asr value (of_nat amount).

  Definition shift_left_signed (value count : t) : t :=
    if lts count zero then P.asr value (neg count) else P.lsl value count.

  Definition shift_right_signed (value count : t) : t :=
    if lts count zero then P.lsl value (neg count) else P.asr value count.
End Make.
