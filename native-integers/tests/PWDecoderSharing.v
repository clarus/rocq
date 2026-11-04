From Stdlib Require Import NArith.
From Rocq.PrimitiveWords Require Import Scalar.

(* Compare against the original decoder for every fuel and every raw scalar
   implementation, without using the primitive word specification axioms. *)
Module DecoderEquivalence (P : RAW_SCALAR).
  Module API := Scalar.Make P.

  Fixpoint reference (fuel : nat) (value : P.t) : N :=
    match fuel with
    | O => 0%N
    | S fuel' =>
        let high := reference fuel' (P.lsr value API.one) in
        if API.eqb (API.logand value API.one) API.zero
        then N.double high else N.succ_double high
    end.

  Theorem decoder_equivalent : forall fuel value,
    API.to_N_fuel fuel value = reference fuel value.
  Proof.
    induction fuel as [|fuel IH]; intro value; cbn [API.to_N_fuel reference].
    - reflexivity.
    - rewrite IH.
      destruct (API.eqb (API.logand value API.one) API.zero); reflexivity.
  Qed.
End DecoderEquivalence.
