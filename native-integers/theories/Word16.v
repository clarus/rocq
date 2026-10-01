(************************************************************************)
(* Public experimental 16-bit primitive word.                          *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word16.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word16.word16.
  Definition bits := 16%nat.
  Definition modulus := 65536%Z.
  Definition sign_bit := 32768%Z.
  Definition signed_max := 32767%Z.
  Definition zero : t := 0%word16.
  Definition one : t := 1%word16.
  Definition max_unsigned : t := 65535%word16.
  Definition min_signed : t := 32768%word16.
  Definition neg := Corelib.Numbers.Primitive.Word16.neg.
  Definition add := Corelib.Numbers.Primitive.Word16.add.
  Definition sub := Corelib.Numbers.Primitive.Word16.sub.
  Definition mul := Corelib.Numbers.Primitive.Word16.mul.
  Definition land := Corelib.Numbers.Primitive.Word16.land.
  Definition lor := Corelib.Numbers.Primitive.Word16.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word16.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word16.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word16.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word16.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word16.leu.
  Definition lts := Corelib.Numbers.Primitive.Word16.lts.
  Definition les := Corelib.Numbers.Primitive.Word16.les.
  Definition lsl := Corelib.Numbers.Primitive.Word16.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word16.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word16.asr.
  Definition divu := Corelib.Numbers.Primitive.Word16.divu.
  Definition modu := Corelib.Numbers.Primitive.Word16.modu.
  Definition divs := Corelib.Numbers.Primitive.Word16.divs.
  Definition rems := Corelib.Numbers.Primitive.Word16.rems.
End Raw.

Include Scalar.Make Raw.
