(************************************************************************)
(* Unsigned 256-bit primitive word.         *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word256 := #word256_type.
Register word256 as num.word256.type.

Variant pos_neg_word256 := Pos256 (d : word256) | Neg256 (d : word256).
Register pos_neg_word256 as num.word256.pos_neg_word256.

Record word256_wrapper := wrap_word256 { word256_wrap : word256 }.
Register word256_wrapper as num.word256.word256_wrapper.
Register wrap_word256 as num.word256.wrap_word256.

Definition word256_printer (x : word256_wrapper) : pos_neg_word256 :=
  Pos256 (word256_wrap x).

Definition word256_parser (x : pos_neg_word256) : option word256 :=
  match x with
  | Pos256 p => Some p
  | Neg256 _ => None
  end.

Declare Scope word256_scope.
Module Import Word256NotationsInternal.
Delimit Scope word256_scope with word256.
Bind Scope word256_scope with word256.
End Word256NotationsInternal.
Number Notation word256 word256_parser word256_printer : word256_scope.

Primitive neg := #word256_neg.
Primitive add := #word256_add.
Primitive sub := #word256_sub.
Primitive mul := #word256_mul.
Primitive land := #word256_land.
Primitive lor := #word256_lor.
Primitive lxor := #word256_lxor.
Primitive lnot := #word256_lnot.
Primitive eqb := #word256_eq.
Primitive ltu := #word256_ltu.
Primitive leu := #word256_leu.
Primitive lts := #word256_lts.
Primitive les := #word256_les.
Primitive lsl := #word256_lsl.
Primitive lsr := #word256_lsr.
Primitive asr := #word256_asr.
Primitive divu := #word256_divu.
Primitive modu := #word256_modu.
Primitive divs := #word256_divs.
Primitive rems := #word256_rems.

Module Export Word256Notations.
  Export Word256NotationsInternal.
End Word256Notations.
