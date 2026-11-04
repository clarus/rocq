(************************************************************************)
(* Unsigned 16-bit primitive word.             *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word16 := #word16_type.
Register word16 as num.word16.type.

Variant pos_neg_word16 := Pos16 (d : word16) | Neg16 (d : word16).
Register pos_neg_word16 as num.word16.pos_neg_word16.

Record word16_wrapper := wrap_word16 { word16_wrap : word16 }.
Register word16_wrapper as num.word16.word16_wrapper.
Register wrap_word16 as num.word16.wrap_word16.

Definition word16_printer (x : word16_wrapper) : pos_neg_word16 :=
  Pos16 (word16_wrap x).

Definition word16_parser (x : pos_neg_word16) : option word16 :=
  match x with
  | Pos16 p => Some p
  | Neg16 _ => None
  end.

Declare Scope word16_scope.
Module Import Word16NotationsInternal.
Delimit Scope word16_scope with word16.
Bind Scope word16_scope with word16.
End Word16NotationsInternal.
Number Notation word16 word16_parser word16_printer : word16_scope.

Primitive neg := #word16_neg.
Primitive add := #word16_add.
Primitive sub := #word16_sub.
Primitive mul := #word16_mul.
Primitive land := #word16_land.
Primitive lor := #word16_lor.
Primitive lxor := #word16_lxor.
Primitive lnot := #word16_lnot.
Primitive eqb := #word16_eq.
Primitive ltu := #word16_ltu.
Primitive leu := #word16_leu.
Primitive lts := #word16_lts.
Primitive les := #word16_les.
Primitive lsl := #word16_lsl.
Primitive lsr := #word16_lsr.
Primitive asr := #word16_asr.
Primitive divu := #word16_divu.
Primitive modu := #word16_modu.
Primitive divs := #word16_divs.
Primitive rems := #word16_rems.

Module Export Word16Notations.
  Export Word16NotationsInternal.
End Word16Notations.
