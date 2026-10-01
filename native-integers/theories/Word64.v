(************************************************************************)
(* Public experimental 64-bit primitive word.                          *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word64.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word64.word64.
  Definition bits := 64%nat.
  Definition modulus := 18446744073709551616%Z.
  Definition sign_bit := 9223372036854775808%Z.
  Definition signed_max := 9223372036854775807%Z.
  Definition zero : t := 0%word64.
  Definition one : t := 1%word64.
  Definition max_unsigned : t := 18446744073709551615%word64.
  Definition min_signed : t := 9223372036854775808%word64.
  Definition neg := Corelib.Numbers.Primitive.Word64.neg.
  Definition add := Corelib.Numbers.Primitive.Word64.add.
  Definition sub := Corelib.Numbers.Primitive.Word64.sub.
  Definition mul := Corelib.Numbers.Primitive.Word64.mul.
  Definition land := Corelib.Numbers.Primitive.Word64.land.
  Definition lor := Corelib.Numbers.Primitive.Word64.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word64.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word64.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word64.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word64.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word64.leu.
  Definition lts := Corelib.Numbers.Primitive.Word64.lts.
  Definition les := Corelib.Numbers.Primitive.Word64.les.
  Definition lsl := Corelib.Numbers.Primitive.Word64.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word64.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word64.asr.
  Definition divu := Corelib.Numbers.Primitive.Word64.divu.
  Definition modu := Corelib.Numbers.Primitive.Word64.modu.
  Definition divs := Corelib.Numbers.Primitive.Word64.divs.
  Definition rems := Corelib.Numbers.Primitive.Word64.rems.
End Raw.

Include Scalar.Make Raw.
