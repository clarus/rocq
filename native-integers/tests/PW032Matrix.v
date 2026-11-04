(************************************************************************)
(* Focused all-engine and polymorphic regression overlay for PW032.     *)
(************************************************************************)

From Stdlib Require Import ZArith NArith List Extraction.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 Word128 Word256 Conversions ScalarExtraction
  PW031Campaign.

Import ListNotations.
Local Open Scope bool_scope.

Definition pw032_engine_rows : list (list Z) :=
  [ pw031_raw8 255 1 ++ pw031_public8 255 1 1 ++ pw031_meta8 255 1 1
  ; pw031_raw16 65535 1 ++ pw031_public16 65535 1 1 ++ pw031_meta16 65535 1 1
  ; pw031_raw32 4294967295 1 ++
      pw031_public32 4294967295 1 1 ++ pw031_meta32 4294967295 1 1
  ; pw031_raw64 18446744073709551615 1 ++
      pw031_public64 18446744073709551615 1 1 ++
      pw031_meta64 18446744073709551615 1 1
  ; pw031_raw128 340282366920938463463374607431768211455 1 ++
      pw031_public128 340282366920938463463374607431768211455 1 1 ++
      pw031_meta128 340282366920938463463374607431768211455 1 1
  ; pw031_raw256
      115792089237316195423570985008687907853269984665640564039457584007913129639935 1 ++
      pw031_public256
      115792089237316195423570985008687907853269984665640564039457584007913129639935 1 1 ++
      pw031_meta256
      115792089237316195423570985008687907853269984665640564039457584007913129639935 1 1
  ].

Definition pw032_normalized_rows : list (list Z) :=
  [ pw031_raw128 340282366920938463463374607431768211455
      170141183460469231731687303715884105731 ++
    pw031_public128 340282366920938463463374607431768211455
      170141183460469231731687303715884105731 1
  ; pw031_raw256
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      57896044618658097711785492504343953926634992332820282019728792003956564819971 ++
    pw031_public256
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      57896044618658097711785492504343953926634992332820282019728792003956564819971 1
  ].

Definition pw032_conversion_rows : list (list Z) :=
  [ pw031_conversion8 (-1) 256 9
  ; pw031_conversion16 (-1) 65536 17
  ; pw031_conversion32 (-1) 4294967296 33
  ; pw031_conversion64 (-1) 18446744073709551616 65
  ; pw031_conversion128 (-1) 340282366920938463463374607431768211456 129
  ; pw031_conversion256 (-1)
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      257
  ].

Definition pw032_cross_rows : list (list Z) :=
  [ pw031_cross_8_16 (-1); pw031_cross_8_32 (-1)
  ; pw031_cross_8_64 (-1); pw031_cross_8_128 (-1)
  ; pw031_cross_8_256 (-1); pw031_cross_16_32 (-1)
  ; pw031_cross_16_64 (-1); pw031_cross_16_128 (-1)
  ; pw031_cross_16_256 (-1); pw031_cross_32_64 (-1)
  ; pw031_cross_32_128 (-1); pw031_cross_32_256 (-1)
  ; pw031_cross_64_128 (-1); pw031_cross_64_256 (-1)
  ; pw031_cross_128_256 (-1)
  ].

Inductive any_word : Type :=
| Any8 : Word8.t -> any_word
| Any16 : Word16.t -> any_word
| Any32 : Word32.t -> any_word
| Any64 : Word64.t -> any_word
| Any128 : Word128.t -> any_word
| Any256 : Word256.t -> any_word.

Definition any_increment (value : any_word) : any_word :=
  match value with
  | Any8 x => Any8 (Word8.add x Word8.one)
  | Any16 x => Any16 (Word16.add x Word16.one)
  | Any32 x => Any32 (Word32.add x Word32.one)
  | Any64 x => Any64 (Word64.add x Word64.one)
  | Any128 x => Any128 (Word128.add x Word128.one)
  | Any256 x => Any256 (Word256.add x Word256.one)
  end.

Definition any_is_two (value : any_word) : bool :=
  match value with
  | Any8 x => Word8.eqb x (Word8.of_Z 2)
  | Any16 x => Word16.eqb x (Word16.of_Z 2)
  | Any32 x => Word32.eqb x (Word32.of_Z 2)
  | Any64 x => Word64.eqb x (Word64.of_Z 2)
  | Any128 x => Word128.eqb x (Word128.of_Z 2)
  | Any256 x => Word256.eqb x (Word256.of_Z 2)
  end.

Definition mixed_words : list any_word :=
  [ Any8 Word8.one; Any16 Word16.one; Any32 Word32.one
  ; Any64 Word64.one; Any128 Word128.one; Any256 Word256.one ].

Fixpoint repeat_apply {A : Type} (fuel : nat) (f : A -> A) (x : A) : A :=
  match fuel with O => x | S n => repeat_apply n f (f x) end.

Definition nested_words : option ((list any_word * list any_word) * list bool) :=
  let mapped := List.map any_increment mixed_words in
  Some ((mixed_words, mapped), List.map any_is_two mapped).

Definition fold_count : nat :=
  List.fold_left (fun count value => if any_is_two value then S count else count)
    (List.map any_increment mixed_words) O.

Module Type WORD_CALLBACK.
  Parameter t : Type.
  Parameter one : t.
  Parameter add : t -> t -> t.
  Parameter eqb : t -> t -> bool.
End WORD_CALLBACK.

Module Callback (W : WORD_CALLBACK).
  Definition captured_add (captured : W.t) : W.t -> W.t :=
    fun value => W.add value captured.
  Definition twice (value : W.t) : W.t :=
    repeat_apply 2 (captured_add W.one) value.
  Definition check (value : W.t) : bool := W.eqb (twice value) (W.add (W.add value W.one) W.one).
End Callback.

Module Callback8Input <: WORD_CALLBACK.
  Definition t := Word8.t.
  Definition one := Word8.one.
  Definition add := Word8.add.
  Definition eqb := Word8.eqb.
End Callback8Input.
Module Callback256Input <: WORD_CALLBACK.
  Definition t := Word256.t.
  Definition one := Word256.one.
  Definition add := Word256.add.
  Definition eqb := Word256.eqb.
End Callback256Input.
Module Callback8 := Callback Callback8Input.
Module Callback256 := Callback Callback256Input.

Definition pw032_polymorphic_checks : list bool :=
  [ match nested_words with
    | Some ((before, after), checks) =>
        Nat.eqb (List.length before) 6 &&
        Nat.eqb (List.length after) 6 &&
        List.forallb (fun x => x) checks
    | None => false
    end
  ; Nat.eqb fold_count 6
  ; Callback8.check (Word8.of_Z 250)
  ; Callback256.check Word256.max_unsigned
  ; match Word8.divu Word8.one Word8.zero with None => true | Some _ => false end
  ; match Word256.divs_checked Word256.min_signed Word256.max_unsigned with
    | None => true | Some _ => false
    end
  ; match Word256.rems Word256.min_signed Word256.max_unsigned with
    | Some x => Word256.eqb x Word256.zero | None => false
    end
  ; match Word8.neg_checked Word8.min_signed with None => true | Some _ => false end
  ; match Word256.add_checked
      (Word256.of_Z
        57896044618658097711785492504343953926634992332820282019728792003956564819967)
      Word256.one with
    | None => true | Some _ => false
    end
  ; Word8.eqb (repeat_apply 258 (fun x => Word8.add x Word8.one) Word8.zero)
      (Word8.of_Z 2)
  ].

Extraction "PW032Extracted.ml"
  pw032_engine_rows pw032_normalized_rows pw032_conversion_rows
  pw032_cross_rows mixed_words nested_words fold_count
  pw032_polymorphic_checks.
