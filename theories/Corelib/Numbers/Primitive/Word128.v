(************************************************************************)
(* Unsigned 128-bit primitive word.         *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word128 := #word128_type.
Register word128 as num.word128.type.

Variant pos_neg_word128 := Pos128 (d : word128) | Neg128 (d : word128).
Register pos_neg_word128 as num.word128.pos_neg_word128.

Record word128_wrapper := wrap_word128 { word128_wrap : word128 }.
Register word128_wrapper as num.word128.word128_wrapper.
Register wrap_word128 as num.word128.wrap_word128.

Definition word128_printer (x : word128_wrapper) : pos_neg_word128 :=
  Pos128 (word128_wrap x).

Definition word128_parser (x : pos_neg_word128) : option word128 :=
  match x with
  | Pos128 p => Some p
  | Neg128 _ => None
  end.

Declare Scope word128_scope.
Module Import Word128NotationsInternal.
Delimit Scope word128_scope with word128.
Bind Scope word128_scope with word128.
End Word128NotationsInternal.
Number Notation word128 word128_parser word128_printer : word128_scope.

Primitive neg := #word128_neg.
Primitive add := #word128_add.
Primitive sub := #word128_sub.
Primitive mul := #word128_mul.
Primitive land := #word128_land.
Primitive lor := #word128_lor.
Primitive lxor := #word128_lxor.
Primitive lnot := #word128_lnot.
Primitive eqb := #word128_eq.
Primitive ltu := #word128_ltu.
Primitive leu := #word128_leu.
Primitive lts := #word128_lts.
Primitive les := #word128_les.
Primitive lsl := #word128_lsl.
Primitive lsr := #word128_lsr.
Primitive asr := #word128_asr.
Primitive divu := #word128_divu.
Primitive modu := #word128_modu.
Primitive divs := #word128_divs.
Primitive rems := #word128_rems.

Module Export Word128Notations.
  Export Word128NotationsInternal.
End Word128Notations.
