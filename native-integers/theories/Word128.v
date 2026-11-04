(************************************************************************)
(* Public experimental 128-bit primitive word.                         *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word128.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word128.word128.
  Definition bits := 128%nat.
  Definition modulus := 340282366920938463463374607431768211456%Z.
  Definition sign_bit := 170141183460469231731687303715884105728%Z.
  Definition signed_max := 170141183460469231731687303715884105727%Z.
  Definition zero : t := 0%word128.
  Definition one : t := 1%word128.
  Definition max_unsigned : t := 340282366920938463463374607431768211455%word128.
  Definition min_signed : t := 170141183460469231731687303715884105728%word128.
  Definition neg := Corelib.Numbers.Primitive.Word128.neg.
  Definition add := Corelib.Numbers.Primitive.Word128.add.
  Definition sub := Corelib.Numbers.Primitive.Word128.sub.
  Definition mul := Corelib.Numbers.Primitive.Word128.mul.
  Definition land := Corelib.Numbers.Primitive.Word128.land.
  Definition lor := Corelib.Numbers.Primitive.Word128.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word128.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word128.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word128.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word128.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word128.leu.
  Definition lts := Corelib.Numbers.Primitive.Word128.lts.
  Definition les := Corelib.Numbers.Primitive.Word128.les.
  Definition lsl := Corelib.Numbers.Primitive.Word128.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word128.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word128.asr.
  Definition divu := Corelib.Numbers.Primitive.Word128.divu.
  Definition modu := Corelib.Numbers.Primitive.Word128.modu.
  Definition divs := Corelib.Numbers.Primitive.Word128.divs.
  Definition rems := Corelib.Numbers.Primitive.Word128.rems.
End Raw.

Include Scalar.Make Raw.
