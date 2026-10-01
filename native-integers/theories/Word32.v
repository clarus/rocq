(************************************************************************)
(* Public experimental 32-bit primitive word.                          *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word32.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word32.word32.
  Definition bits := 32%nat.
  Definition modulus := 4294967296%Z.
  Definition sign_bit := 2147483648%Z.
  Definition signed_max := 2147483647%Z.
  Definition zero : t := 0%word32.
  Definition one : t := 1%word32.
  Definition max_unsigned : t := 4294967295%word32.
  Definition min_signed : t := 2147483648%word32.
  Definition neg := Corelib.Numbers.Primitive.Word32.neg.
  Definition add := Corelib.Numbers.Primitive.Word32.add.
  Definition sub := Corelib.Numbers.Primitive.Word32.sub.
  Definition mul := Corelib.Numbers.Primitive.Word32.mul.
  Definition land := Corelib.Numbers.Primitive.Word32.land.
  Definition lor := Corelib.Numbers.Primitive.Word32.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word32.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word32.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word32.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word32.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word32.leu.
  Definition lts := Corelib.Numbers.Primitive.Word32.lts.
  Definition les := Corelib.Numbers.Primitive.Word32.les.
  Definition lsl := Corelib.Numbers.Primitive.Word32.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word32.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word32.asr.
  Definition divu := Corelib.Numbers.Primitive.Word32.divu.
  Definition modu := Corelib.Numbers.Primitive.Word32.modu.
  Definition divs := Corelib.Numbers.Primitive.Word32.divs.
  Definition rems := Corelib.Numbers.Primitive.Word32.rems.
End Raw.

Include Scalar.Make Raw.
