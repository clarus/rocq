(************************************************************************)
(* Public experimental 8-bit primitive word.                           *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word8.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word8.word8.
  Definition bits := 8%nat.
  Definition modulus := 256%Z.
  Definition sign_bit := 128%Z.
  Definition signed_max := 127%Z.
  Definition zero : t := 0%word8.
  Definition one : t := 1%word8.
  Definition max_unsigned : t := 255%word8.
  Definition min_signed : t := 128%word8.
  Definition neg := Corelib.Numbers.Primitive.Word8.neg.
  Definition add := Corelib.Numbers.Primitive.Word8.add.
  Definition sub := Corelib.Numbers.Primitive.Word8.sub.
  Definition mul := Corelib.Numbers.Primitive.Word8.mul.
  Definition land := Corelib.Numbers.Primitive.Word8.land.
  Definition lor := Corelib.Numbers.Primitive.Word8.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word8.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word8.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word8.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word8.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word8.leu.
  Definition lts := Corelib.Numbers.Primitive.Word8.lts.
  Definition les := Corelib.Numbers.Primitive.Word8.les.
  Definition lsl := Corelib.Numbers.Primitive.Word8.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word8.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word8.asr.
  Definition divu := Corelib.Numbers.Primitive.Word8.divu.
  Definition modu := Corelib.Numbers.Primitive.Word8.modu.
  Definition divs := Corelib.Numbers.Primitive.Word8.divs.
  Definition rems := Corelib.Numbers.Primitive.Word8.rems.
End Raw.

Include Scalar.Make Raw.
