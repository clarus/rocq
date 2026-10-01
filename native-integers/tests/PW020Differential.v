From Stdlib Require Import ZArith NArith List Extraction.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 Conversions ScalarExtraction.

Import ListNotations.

Record scalar_api := {
  api_word : Type;
  api_zero : api_word;
  api_neg : api_word -> api_word;
  api_add : api_word -> api_word -> api_word;
  api_sub : api_word -> api_word -> api_word;
  api_mul : api_word -> api_word -> api_word;
  api_logand : api_word -> api_word -> api_word;
  api_logor : api_word -> api_word -> api_word;
  api_logxor : api_word -> api_word -> api_word;
  api_lognot : api_word -> api_word;
  api_eqb : api_word -> api_word -> bool;
  api_ltu : api_word -> api_word -> bool;
  api_leu : api_word -> api_word -> bool;
  api_lts : api_word -> api_word -> bool;
  api_les : api_word -> api_word -> bool;
  api_addc : api_word -> api_word -> bool * api_word;
  api_subb : api_word -> api_word -> bool * api_word;
  api_neg_checked : api_word -> option api_word;
  api_add_checked : api_word -> api_word -> option api_word;
  api_sub_checked : api_word -> api_word -> option api_word;
  api_mul_checked : api_word -> api_word -> option api_word;
  api_divu : api_word -> api_word -> option api_word;
  api_modu : api_word -> api_word -> option api_word;
  api_divmodu : api_word -> api_word -> option (api_word * api_word);
  api_divs : api_word -> api_word -> option api_word;
  api_rems : api_word -> api_word -> option api_word;
  api_shift_left : api_word -> nat -> api_word;
  api_shift_right_logical : api_word -> nat -> api_word;
  api_shift_right_arithmetic : api_word -> nat -> api_word;
  api_shift_left_signed : api_word -> api_word -> api_word;
  api_shift_right_signed : api_word -> api_word -> api_word;
  api_of_Z : Z -> api_word;
  api_of_Z_unsigned_checked : Z -> option api_word;
  api_of_Z_signed_checked : Z -> option api_word;
  api_of_N : N -> api_word;
  api_of_N_checked : N -> option api_word;
  api_of_nat : nat -> api_word;
  api_of_nat_checked : nat -> option api_word;
  api_to_Z_unsigned : api_word -> Z;
  api_to_Z_signed : api_word -> Z;
  api_to_N : api_word -> N;
  api_to_nat : api_word -> nat;
}.

Definition bool_Z (value : bool) : Z := if value then 1 else 0.

Definition option_row (api : scalar_api) (value : option (api_word api))
  : list Z :=
  match value with
  | None => [0; 0]%Z
  | Some word => [1; api_to_Z_unsigned api word]%Z
  end.

Definition divmod_row (api : scalar_api)
  (value : option (api_word api * api_word api)) : list Z :=
  match value with
  | None => [0; 0; 0]%Z
  | Some (quotient, remainder) =>
      [1; api_to_Z_unsigned api quotient;
          api_to_Z_unsigned api remainder]%Z
  end.

Definition carry_row (api : scalar_api) (value : bool * api_word api) : list Z :=
  [bool_Z (fst value); api_to_Z_unsigned api (snd value)].

Definition pair_row (api : scalar_api) (x y : api_word api) (amount : nat)
  : list Z :=
  [ api_to_Z_unsigned api (api_neg api x)
  ; api_to_Z_unsigned api (api_add api x y)
  ; api_to_Z_unsigned api (api_sub api x y)
  ; api_to_Z_unsigned api (api_mul api x y)
  ; api_to_Z_unsigned api (api_logand api x y)
  ; api_to_Z_unsigned api (api_logor api x y)
  ; api_to_Z_unsigned api (api_logxor api x y)
  ; api_to_Z_unsigned api (api_lognot api x)
  ; bool_Z (api_eqb api x y)
  ; bool_Z (api_ltu api x y)
  ; bool_Z (api_leu api x y)
  ; bool_Z (api_lts api x y)
  ; bool_Z (api_les api x y)
  ] ++
  carry_row api (api_addc api x y) ++
  carry_row api (api_subb api x y) ++
  option_row api (api_neg_checked api x) ++
  option_row api (api_add_checked api x y) ++
  option_row api (api_sub_checked api x y) ++
  option_row api (api_mul_checked api x y) ++
  option_row api (api_divu api x y) ++
  option_row api (api_modu api x y) ++
  divmod_row api (api_divmodu api x y) ++
  option_row api (api_divs api x y) ++
  option_row api (api_rems api x y) ++
  [ api_to_Z_unsigned api (api_shift_left api x amount)
  ; api_to_Z_unsigned api (api_shift_right_logical api x amount)
  ; api_to_Z_unsigned api (api_shift_right_arithmetic api x amount)
  ; api_to_Z_unsigned api (api_shift_left_signed api x y)
  ; api_to_Z_unsigned api (api_shift_right_signed api x y)
  ].

Definition conversion_row (api : scalar_api) (z : Z) (n : N) : list Z :=
  let modular_z := api_of_Z api z in
  let modular_n := api_of_N api n in
  [ api_to_Z_unsigned api modular_z
  ; api_to_Z_signed api modular_z
  ; Z.of_N (api_to_N api modular_z)
  ] ++
  option_row api (api_of_Z_unsigned_checked api z) ++
  option_row api (api_of_Z_signed_checked api z) ++
  [api_to_Z_unsigned api modular_n] ++
  option_row api (api_of_N_checked api n).

Definition nat_row (api : scalar_api) (natural : nat) : list Z :=
  let modular := api_of_nat api natural in
  [ api_to_Z_unsigned api modular
  ; Z.of_N (N.of_nat (api_to_nat api modular))
  ] ++ option_row api (api_of_nat_checked api natural).

Definition api8 : scalar_api :=
  {| api_word := Word8.t; api_zero := Word8.zero;
     api_neg := Word8.neg; api_add := Word8.add; api_sub := Word8.sub;
     api_mul := Word8.mul; api_logand := Word8.logand; api_logor := Word8.logor;
     api_logxor := Word8.logxor; api_lognot := Word8.lognot;
     api_eqb := Word8.eqb; api_ltu := Word8.ltu; api_leu := Word8.leu;
     api_lts := Word8.lts; api_les := Word8.les;
     api_addc := Word8.add_with_carry; api_subb := Word8.sub_with_borrow;
     api_neg_checked := Word8.neg_checked; api_add_checked := Word8.add_checked;
     api_sub_checked := Word8.sub_checked; api_mul_checked := Word8.mul_checked;
     api_divu := Word8.divu; api_modu := Word8.modu;
     api_divmodu := Word8.divmodu; api_divs := Word8.divs_checked;
     api_rems := Word8.rems; api_shift_left := Word8.shift_left;
     api_shift_right_logical := Word8.shift_right_logical;
     api_shift_right_arithmetic := Word8.shift_right_arithmetic;
     api_shift_left_signed := Word8.shift_left_signed;
     api_shift_right_signed := Word8.shift_right_signed;
     api_of_Z := Word8.of_Z;
     api_of_Z_unsigned_checked := Word8.of_Z_unsigned_checked;
     api_of_Z_signed_checked := Word8.of_Z_signed_checked;
     api_of_N := Word8.of_N; api_of_N_checked := Word8.of_N_checked;
     api_of_nat := Word8.of_nat; api_of_nat_checked := Word8.of_nat_checked;
     api_to_Z_unsigned := Word8.to_Z_unsigned;
     api_to_Z_signed := Word8.to_Z_signed; api_to_N := Word8.to_N;
     api_to_nat := Word8.to_nat |}.

Definition api16 : scalar_api :=
  {| api_word := Word16.t; api_zero := Word16.zero;
     api_neg := Word16.neg; api_add := Word16.add; api_sub := Word16.sub;
     api_mul := Word16.mul; api_logand := Word16.logand; api_logor := Word16.logor;
     api_logxor := Word16.logxor; api_lognot := Word16.lognot;
     api_eqb := Word16.eqb; api_ltu := Word16.ltu; api_leu := Word16.leu;
     api_lts := Word16.lts; api_les := Word16.les;
     api_addc := Word16.add_with_carry; api_subb := Word16.sub_with_borrow;
     api_neg_checked := Word16.neg_checked; api_add_checked := Word16.add_checked;
     api_sub_checked := Word16.sub_checked; api_mul_checked := Word16.mul_checked;
     api_divu := Word16.divu; api_modu := Word16.modu;
     api_divmodu := Word16.divmodu; api_divs := Word16.divs_checked;
     api_rems := Word16.rems; api_shift_left := Word16.shift_left;
     api_shift_right_logical := Word16.shift_right_logical;
     api_shift_right_arithmetic := Word16.shift_right_arithmetic;
     api_shift_left_signed := Word16.shift_left_signed;
     api_shift_right_signed := Word16.shift_right_signed;
     api_of_Z := Word16.of_Z;
     api_of_Z_unsigned_checked := Word16.of_Z_unsigned_checked;
     api_of_Z_signed_checked := Word16.of_Z_signed_checked;
     api_of_N := Word16.of_N; api_of_N_checked := Word16.of_N_checked;
     api_of_nat := Word16.of_nat; api_of_nat_checked := Word16.of_nat_checked;
     api_to_Z_unsigned := Word16.to_Z_unsigned;
     api_to_Z_signed := Word16.to_Z_signed; api_to_N := Word16.to_N;
     api_to_nat := Word16.to_nat |}.

Definition api32 : scalar_api :=
  {| api_word := Word32.t; api_zero := Word32.zero;
     api_neg := Word32.neg; api_add := Word32.add; api_sub := Word32.sub;
     api_mul := Word32.mul; api_logand := Word32.logand; api_logor := Word32.logor;
     api_logxor := Word32.logxor; api_lognot := Word32.lognot;
     api_eqb := Word32.eqb; api_ltu := Word32.ltu; api_leu := Word32.leu;
     api_lts := Word32.lts; api_les := Word32.les;
     api_addc := Word32.add_with_carry; api_subb := Word32.sub_with_borrow;
     api_neg_checked := Word32.neg_checked; api_add_checked := Word32.add_checked;
     api_sub_checked := Word32.sub_checked; api_mul_checked := Word32.mul_checked;
     api_divu := Word32.divu; api_modu := Word32.modu;
     api_divmodu := Word32.divmodu; api_divs := Word32.divs_checked;
     api_rems := Word32.rems; api_shift_left := Word32.shift_left;
     api_shift_right_logical := Word32.shift_right_logical;
     api_shift_right_arithmetic := Word32.shift_right_arithmetic;
     api_shift_left_signed := Word32.shift_left_signed;
     api_shift_right_signed := Word32.shift_right_signed;
     api_of_Z := Word32.of_Z;
     api_of_Z_unsigned_checked := Word32.of_Z_unsigned_checked;
     api_of_Z_signed_checked := Word32.of_Z_signed_checked;
     api_of_N := Word32.of_N; api_of_N_checked := Word32.of_N_checked;
     api_of_nat := Word32.of_nat; api_of_nat_checked := Word32.of_nat_checked;
     api_to_Z_unsigned := Word32.to_Z_unsigned;
     api_to_Z_signed := Word32.to_Z_signed; api_to_N := Word32.to_N;
     api_to_nat := Word32.to_nat |}.

Definition api64 : scalar_api :=
  {| api_word := Word64.t; api_zero := Word64.zero;
     api_neg := Word64.neg; api_add := Word64.add; api_sub := Word64.sub;
     api_mul := Word64.mul; api_logand := Word64.logand; api_logor := Word64.logor;
     api_logxor := Word64.logxor; api_lognot := Word64.lognot;
     api_eqb := Word64.eqb; api_ltu := Word64.ltu; api_leu := Word64.leu;
     api_lts := Word64.lts; api_les := Word64.les;
     api_addc := Word64.add_with_carry; api_subb := Word64.sub_with_borrow;
     api_neg_checked := Word64.neg_checked; api_add_checked := Word64.add_checked;
     api_sub_checked := Word64.sub_checked; api_mul_checked := Word64.mul_checked;
     api_divu := Word64.divu; api_modu := Word64.modu;
     api_divmodu := Word64.divmodu; api_divs := Word64.divs_checked;
     api_rems := Word64.rems; api_shift_left := Word64.shift_left;
     api_shift_right_logical := Word64.shift_right_logical;
     api_shift_right_arithmetic := Word64.shift_right_arithmetic;
     api_shift_left_signed := Word64.shift_left_signed;
     api_shift_right_signed := Word64.shift_right_signed;
     api_of_Z := Word64.of_Z;
     api_of_Z_unsigned_checked := Word64.of_Z_unsigned_checked;
     api_of_Z_signed_checked := Word64.of_Z_signed_checked;
     api_of_N := Word64.of_N; api_of_N_checked := Word64.of_N_checked;
     api_of_nat := Word64.of_nat; api_of_nat_checked := Word64.of_nat_checked;
     api_to_Z_unsigned := Word64.to_Z_unsigned;
     api_to_Z_signed := Word64.to_Z_signed; api_to_N := Word64.to_N;
     api_to_nat := Word64.to_nat |}.

Definition pw020_word8_pair := pair_row api8.
Definition pw020_word16_pair := pair_row api16.
Definition pw020_word32_pair := pair_row api32.
Definition pw020_word64_pair := pair_row api64.
Definition pw020_word8_conversion := conversion_row api8.
Definition pw020_word16_conversion := conversion_row api16.
Definition pw020_word32_conversion := conversion_row api32.
Definition pw020_word64_conversion := conversion_row api64.
Definition pw020_word8_nat := nat_row api8.
Definition pw020_word16_nat := nat_row api16.
Definition pw020_word32_nat := nat_row api32.
Definition pw020_word64_nat := nat_row api64.

Definition pw020_cross_width : list Z :=
  [ Word16.to_Z_unsigned (zero_extend_8_16 (Word8.of_Z 255))
  ; Word16.to_Z_signed (sign_extend_8_16 (Word8.of_Z 255))
  ; Word32.to_Z_unsigned (zero_extend_8_32 (Word8.of_Z 255))
  ; Word32.to_Z_signed (sign_extend_8_32 (Word8.of_Z 255))
  ; Word64.to_Z_unsigned (zero_extend_8_64 (Word8.of_Z 255))
  ; Word64.to_Z_signed (sign_extend_8_64 (Word8.of_Z 255))
  ; Word32.to_Z_unsigned (zero_extend_16_32 (Word16.of_Z 65535))
  ; Word32.to_Z_signed (sign_extend_16_32 (Word16.of_Z 65535))
  ; Word64.to_Z_unsigned (zero_extend_16_64 (Word16.of_Z 65535))
  ; Word64.to_Z_signed (sign_extend_16_64 (Word16.of_Z 65535))
  ; Word64.to_Z_unsigned (zero_extend_32_64 (Word32.of_Z 4294967295))
  ; Word64.to_Z_signed (sign_extend_32_64 (Word32.of_Z 4294967295))
  ; Word8.to_Z_unsigned (narrow_16_8 (Word16.of_Z 65535))
  ; Word8.to_Z_unsigned (narrow_32_8 (Word32.of_Z 4294967295))
  ; Word16.to_Z_unsigned (narrow_32_16 (Word32.of_Z 4294967295))
  ; Word8.to_Z_unsigned (narrow_64_8 (Word64.of_Z 18446744073709551615))
  ; Word16.to_Z_unsigned (narrow_64_16 (Word64.of_Z 18446744073709551615))
  ; Word32.to_Z_unsigned (narrow_64_32 (Word64.of_Z 18446744073709551615))
  ].

Extraction "PW020Extracted.ml"
  pw020_word8_pair pw020_word16_pair pw020_word32_pair pw020_word64_pair
  pw020_word8_conversion pw020_word16_conversion
  pw020_word32_conversion pw020_word64_conversion
  pw020_word8_nat pw020_word16_nat pw020_word32_nat pw020_word64_nat
  pw020_cross_width.
