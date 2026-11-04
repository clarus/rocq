(************************************************************************)
(* Unsigned 8-bit primitive word.             *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word8 := #word8_type.
Register word8 as num.word8.type.

Variant pos_neg_word8 := Pos8 (d : word8) | Neg8 (d : word8).
Register pos_neg_word8 as num.word8.pos_neg_word8.

Record word8_wrapper := wrap_word8 { word8_wrap : word8 }.
Register word8_wrapper as num.word8.word8_wrapper.
Register wrap_word8 as num.word8.wrap_word8.

Definition word8_printer (x : word8_wrapper) : pos_neg_word8 :=
  Pos8 (word8_wrap x).

Definition word8_parser (x : pos_neg_word8) : option word8 :=
  match x with
  | Pos8 p => Some p
  | Neg8 _ => None
  end.

Declare Scope word8_scope.
Module Import Word8NotationsInternal.
Delimit Scope word8_scope with word8.
Bind Scope word8_scope with word8.
End Word8NotationsInternal.
Number Notation word8 word8_parser word8_printer : word8_scope.

Primitive neg := #word8_neg.
Primitive add := #word8_add.
Primitive sub := #word8_sub.
Primitive mul := #word8_mul.
Primitive land := #word8_land.
Primitive lor := #word8_lor.
Primitive lxor := #word8_lxor.
Primitive lnot := #word8_lnot.
Primitive eqb := #word8_eq.
Primitive ltu := #word8_ltu.
Primitive leu := #word8_leu.
Primitive lts := #word8_lts.
Primitive les := #word8_les.
Primitive lsl := #word8_lsl.
Primitive lsr := #word8_lsr.
Primitive asr := #word8_asr.
Primitive divu := #word8_divu.
Primitive modu := #word8_modu.
Primitive divs := #word8_divs.
Primitive rems := #word8_rems.

Module Export Word8Notations.
  Export Word8NotationsInternal.
End Word8Notations.
