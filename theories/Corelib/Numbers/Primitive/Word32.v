(************************************************************************)
(* Unsigned 32-bit primitive word.             *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word32 := #word32_type.
Register word32 as num.word32.type.

Variant pos_neg_word32 := Pos32 (d : word32) | Neg32 (d : word32).
Register pos_neg_word32 as num.word32.pos_neg_word32.

Record word32_wrapper := wrap_word32 { word32_wrap : word32 }.
Register word32_wrapper as num.word32.word32_wrapper.
Register wrap_word32 as num.word32.wrap_word32.

Definition word32_printer (x : word32_wrapper) : pos_neg_word32 :=
  Pos32 (word32_wrap x).

Definition word32_parser (x : pos_neg_word32) : option word32 :=
  match x with
  | Pos32 p => Some p
  | Neg32 _ => None
  end.

Declare Scope word32_scope.
Module Import Word32NotationsInternal.
Delimit Scope word32_scope with word32.
Bind Scope word32_scope with word32.
End Word32NotationsInternal.
Number Notation word32 word32_parser word32_printer : word32_scope.

Primitive neg := #word32_neg.
Primitive add := #word32_add.
Primitive sub := #word32_sub.
Primitive mul := #word32_mul.
Primitive land := #word32_land.
Primitive lor := #word32_lor.
Primitive lxor := #word32_lxor.
Primitive lnot := #word32_lnot.
Primitive eqb := #word32_eq.
Primitive ltu := #word32_ltu.
Primitive leu := #word32_leu.
Primitive lts := #word32_lts.
Primitive les := #word32_les.
Primitive lsl := #word32_lsl.
Primitive lsr := #word32_lsr.
Primitive asr := #word32_asr.
Primitive divu := #word32_divu.
Primitive modu := #word32_modu.
Primitive divs := #word32_divs.
Primitive rems := #word32_rems.

Module Export Word32Notations.
  Export Word32NotationsInternal.
End Word32Notations.
