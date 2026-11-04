From Stdlib Require Import ZArith List.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 Word128 Word256 Conversions.

Import ListNotations.

Definition six_width_values :=
  ( Word8.add Word8.max_unsigned Word8.one
  , Word16.add Word16.max_unsigned Word16.one
  , Word32.add Word32.max_unsigned Word32.one
  , Word64.add Word64.max_unsigned Word64.one
  , Word128.add Word128.max_unsigned Word128.one
  , Word256.add Word256.max_unsigned Word256.one ).

Example six_width_values_cbv :
  six_width_values =
  (Word8.zero, Word16.zero, Word32.zero, Word64.zero,
   Word128.zero, Word256.zero).
Proof. cbv. reflexivity. Qed.

Definition fresh_wide_identity :=
  ( Word128.of_Z 340282366920938463463374607431768211455
  , Word256.of_Z
      115792089237316195423570985008687907853269984665640564039457584007913129639935 ).

Example fresh_wide_identity_vm :
  fresh_wide_identity = (Word128.max_unsigned, Word256.max_unsigned).
Proof. vm_compute. reflexivity. Qed.

Definition fresh_conversion_edges : list bool :=
  [ Word128.eqb (zero_extend_64_128 Word64.max_unsigned)
      (Word128.of_Z 18446744073709551615)
  ; Word128.eqb (sign_extend_64_128 Word64.max_unsigned) Word128.max_unsigned
  ; Word256.eqb (zero_extend_128_256 Word128.max_unsigned)
      (Word256.of_Z 340282366920938463463374607431768211455)
  ; Word256.eqb (sign_extend_128_256 Word128.max_unsigned) Word256.max_unsigned
  ; Word128.eqb (narrow_256_128 Word256.max_unsigned) Word128.max_unsigned
  ; Word8.eqb (narrow_256_8 Word256.max_unsigned) Word8.max_unsigned ].

Example fresh_conversion_edges_vm :
  fresh_conversion_edges = List.repeat true 6.
Proof. vm_compute. reflexivity. Qed.

Definition fresh_boundary_values :=
  ( Word128.divmodu Word128.max_unsigned (Word128.of_Z 17)
  , Word256.rems Word256.min_signed Word256.max_unsigned
  , List.map (fun value => Word256.add value Word256.one)
      [Word256.zero; Word256.max_unsigned] ).

Example fresh_boundary_values_vm :
  fresh_boundary_values =
  ( Some (Word128.of_Z 20016609818878733144904388672456953615,
          Word128.zero)
  , Some Word256.zero
  , [Word256.one; Word256.zero] ).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions six_width_values_cbv.
Print Assumptions fresh_wide_identity_vm.
Print Assumptions fresh_conversion_edges_vm.
Print Assumptions fresh_boundary_values_vm.
