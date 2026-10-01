(************************************************************************)
(* Public experimental 256-bit primitive word.                         *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word256.
From Stdlib Require Import ZArith.
From Rocq.PrimitiveWords Require Import Scalar.

Module Raw <: RAW_SCALAR.
  Definition t := Corelib.Numbers.Primitive.Word256.word256.
  Definition bits := 256%nat.
  Definition modulus := 115792089237316195423570985008687907853269984665640564039457584007913129639936%Z.
  Definition sign_bit := 57896044618658097711785492504343953926634992332820282019728792003956564819968%Z.
  Definition signed_max := 57896044618658097711785492504343953926634992332820282019728792003956564819967%Z.
  Definition zero : t := 0%word256.
  Definition one : t := 1%word256.
  Definition max_unsigned : t := 115792089237316195423570985008687907853269984665640564039457584007913129639935%word256.
  Definition min_signed : t := 57896044618658097711785492504343953926634992332820282019728792003956564819968%word256.
  Definition neg := Corelib.Numbers.Primitive.Word256.neg.
  Definition add := Corelib.Numbers.Primitive.Word256.add.
  Definition sub := Corelib.Numbers.Primitive.Word256.sub.
  Definition mul := Corelib.Numbers.Primitive.Word256.mul.
  Definition land := Corelib.Numbers.Primitive.Word256.land.
  Definition lor := Corelib.Numbers.Primitive.Word256.lor.
  Definition lxor := Corelib.Numbers.Primitive.Word256.lxor.
  Definition lnot := Corelib.Numbers.Primitive.Word256.lnot.
  Definition eqb := Corelib.Numbers.Primitive.Word256.eqb.
  Definition ltu := Corelib.Numbers.Primitive.Word256.ltu.
  Definition leu := Corelib.Numbers.Primitive.Word256.leu.
  Definition lts := Corelib.Numbers.Primitive.Word256.lts.
  Definition les := Corelib.Numbers.Primitive.Word256.les.
  Definition lsl := Corelib.Numbers.Primitive.Word256.lsl.
  Definition lsr := Corelib.Numbers.Primitive.Word256.lsr.
  Definition asr := Corelib.Numbers.Primitive.Word256.asr.
  Definition divu := Corelib.Numbers.Primitive.Word256.divu.
  Definition modu := Corelib.Numbers.Primitive.Word256.modu.
  Definition divs := Corelib.Numbers.Primitive.Word256.divs.
  Definition rems := Corelib.Numbers.Primitive.Word256.rems.
End Raw.

Include Scalar.Make Raw.
