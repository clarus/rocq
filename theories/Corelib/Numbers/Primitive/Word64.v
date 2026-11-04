(************************************************************************)
(* Unsigned 64-bit primitive word.          *)
(************************************************************************)

From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63.

Primitive word64 := #word64_type.
Register word64 as num.word64.type.

Variant pos_neg_word64 := Pos64 (d : word64) | Neg64 (d : word64).
Register pos_neg_word64 as num.word64.pos_neg_word64.

Record word64_wrapper := wrap_word64 { word64_wrap : word64 }.
Register word64_wrapper as num.word64.word64_wrapper.
Register wrap_word64 as num.word64.wrap_word64.

Definition word64_printer (x : word64_wrapper) : pos_neg_word64 :=
  Pos64 (word64_wrap x).

Definition word64_parser (x : pos_neg_word64) : option word64 :=
  match x with
  | Pos64 p => Some p
  | Neg64 _ => None
  end.

Declare Scope word64_scope.
Module Import Word64NotationsInternal.
Delimit Scope word64_scope with word64.
Bind Scope word64_scope with word64.
End Word64NotationsInternal.
Number Notation word64 word64_parser word64_printer : word64_scope.

Primitive neg := #word64_neg.
Primitive add := #word64_add.
Primitive sub := #word64_sub.
Primitive mul := #word64_mul.
Primitive land := #word64_land.
Primitive lor := #word64_lor.
Primitive lxor := #word64_lxor.
Primitive lnot := #word64_lnot.
Primitive eqb := #word64_eq.
Primitive ltu := #word64_ltu.
Primitive leu := #word64_leu.
Primitive lts := #word64_lts.
Primitive les := #word64_les.
Primitive lsl := #word64_lsl.
Primitive lsr := #word64_lsr.
Primitive asr := #word64_asr.
Primitive divu := #word64_divu.
Primitive modu := #word64_modu.
Primitive divs := #word64_divs.
Primitive rems := #word64_rems.

Module Export Word64Notations.
  Export Word64NotationsInternal.
End Word64Notations.
