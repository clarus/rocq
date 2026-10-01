(************************************************************************)
(* OCaml extraction bindings for all scalar primitive-word descriptors. *)
(************************************************************************)

From Corelib.Numbers.Primitive Require Import Word8 Word16 Word32 Word64 Word128 Word256.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt.

Extract Constant Corelib.Numbers.Primitive.Word8.word8 =>
  "Primitive_words_runtime.Word8.t".
Extraction Inline Corelib.Numbers.Primitive.Word8.word8.
Extract Constant Corelib.Numbers.Primitive.Word8.neg => "Primitive_words_runtime.Word8.neg".
Extract Constant Corelib.Numbers.Primitive.Word8.add => "Primitive_words_runtime.Word8.add".
Extract Constant Corelib.Numbers.Primitive.Word8.sub => "Primitive_words_runtime.Word8.sub".
Extract Constant Corelib.Numbers.Primitive.Word8.mul => "Primitive_words_runtime.Word8.mul".
Extract Constant Corelib.Numbers.Primitive.Word8.land => "Primitive_words_runtime.Word8.logand".
Extract Constant Corelib.Numbers.Primitive.Word8.lor => "Primitive_words_runtime.Word8.logor".
Extract Constant Corelib.Numbers.Primitive.Word8.lxor => "Primitive_words_runtime.Word8.logxor".
Extract Constant Corelib.Numbers.Primitive.Word8.lnot => "Primitive_words_runtime.Word8.lognot".
Extract Constant Corelib.Numbers.Primitive.Word8.eqb => "Primitive_words_runtime.Word8.equal".
Extract Constant Corelib.Numbers.Primitive.Word8.ltu => "Primitive_words_runtime.Word8.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word8.leu => "Primitive_words_runtime.Word8.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word8.lts => "Primitive_words_runtime.Word8.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word8.les => "Primitive_words_runtime.Word8.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word8.lsl => "Primitive_words_runtime.Word8.shift_left".
Extract Constant Corelib.Numbers.Primitive.Word8.lsr => "Primitive_words_runtime.Word8.shift_right_logical".
Extract Constant Corelib.Numbers.Primitive.Word8.asr => "Primitive_words_runtime.Word8.shift_right_arithmetic".
Extract Constant Corelib.Numbers.Primitive.Word8.divu => "Primitive_words_runtime.Word8.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word8.modu => "Primitive_words_runtime.Word8.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word8.divs => "Primitive_words_runtime.Word8.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word8.rems => "Primitive_words_runtime.Word8.rems_total".

Extract Constant Corelib.Numbers.Primitive.Word16.word16 =>
  "Primitive_words_runtime.Word16.t".
Extraction Inline Corelib.Numbers.Primitive.Word16.word16.
Extract Constant Corelib.Numbers.Primitive.Word16.neg => "Primitive_words_runtime.Word16.neg".
Extract Constant Corelib.Numbers.Primitive.Word16.add => "Primitive_words_runtime.Word16.add".
Extract Constant Corelib.Numbers.Primitive.Word16.sub => "Primitive_words_runtime.Word16.sub".
Extract Constant Corelib.Numbers.Primitive.Word16.mul => "Primitive_words_runtime.Word16.mul".
Extract Constant Corelib.Numbers.Primitive.Word16.land => "Primitive_words_runtime.Word16.logand".
Extract Constant Corelib.Numbers.Primitive.Word16.lor => "Primitive_words_runtime.Word16.logor".
Extract Constant Corelib.Numbers.Primitive.Word16.lxor => "Primitive_words_runtime.Word16.logxor".
Extract Constant Corelib.Numbers.Primitive.Word16.lnot => "Primitive_words_runtime.Word16.lognot".
Extract Constant Corelib.Numbers.Primitive.Word16.eqb => "Primitive_words_runtime.Word16.equal".
Extract Constant Corelib.Numbers.Primitive.Word16.ltu => "Primitive_words_runtime.Word16.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word16.leu => "Primitive_words_runtime.Word16.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word16.lts => "Primitive_words_runtime.Word16.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word16.les => "Primitive_words_runtime.Word16.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word16.lsl => "Primitive_words_runtime.Word16.shift_left".
Extract Constant Corelib.Numbers.Primitive.Word16.lsr => "Primitive_words_runtime.Word16.shift_right_logical".
Extract Constant Corelib.Numbers.Primitive.Word16.asr => "Primitive_words_runtime.Word16.shift_right_arithmetic".
Extract Constant Corelib.Numbers.Primitive.Word16.divu => "Primitive_words_runtime.Word16.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word16.modu => "Primitive_words_runtime.Word16.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word16.divs => "Primitive_words_runtime.Word16.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word16.rems => "Primitive_words_runtime.Word16.rems_total".

Extract Constant Corelib.Numbers.Primitive.Word32.word32 =>
  "Primitive_words_runtime.Word32.t".
Extraction Inline Corelib.Numbers.Primitive.Word32.word32.
Extract Constant Corelib.Numbers.Primitive.Word32.neg => "Primitive_words_runtime.Word32.neg".
Extract Constant Corelib.Numbers.Primitive.Word32.add => "Primitive_words_runtime.Word32.add".
Extract Constant Corelib.Numbers.Primitive.Word32.sub => "Primitive_words_runtime.Word32.sub".
Extract Constant Corelib.Numbers.Primitive.Word32.mul => "Primitive_words_runtime.Word32.mul".
Extract Constant Corelib.Numbers.Primitive.Word32.land => "Primitive_words_runtime.Word32.logand".
Extract Constant Corelib.Numbers.Primitive.Word32.lor => "Primitive_words_runtime.Word32.logor".
Extract Constant Corelib.Numbers.Primitive.Word32.lxor => "Primitive_words_runtime.Word32.logxor".
Extract Constant Corelib.Numbers.Primitive.Word32.lnot => "Primitive_words_runtime.Word32.lognot".
Extract Constant Corelib.Numbers.Primitive.Word32.eqb => "Primitive_words_runtime.Word32.equal".
Extract Constant Corelib.Numbers.Primitive.Word32.ltu => "Primitive_words_runtime.Word32.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word32.leu => "Primitive_words_runtime.Word32.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word32.lts => "Primitive_words_runtime.Word32.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word32.les => "Primitive_words_runtime.Word32.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word32.lsl => "Primitive_words_runtime.Word32.shift_left".
Extract Constant Corelib.Numbers.Primitive.Word32.lsr => "Primitive_words_runtime.Word32.shift_right_logical".
Extract Constant Corelib.Numbers.Primitive.Word32.asr => "Primitive_words_runtime.Word32.shift_right_arithmetic".
Extract Constant Corelib.Numbers.Primitive.Word32.divu => "Primitive_words_runtime.Word32.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word32.modu => "Primitive_words_runtime.Word32.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word32.divs => "Primitive_words_runtime.Word32.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word32.rems => "Primitive_words_runtime.Word32.rems_total".

Extract Constant Corelib.Numbers.Primitive.Word64.word64 =>
  "Primitive_words_runtime.Word64.t".
Extraction Inline Corelib.Numbers.Primitive.Word64.word64.
Extract Constant Corelib.Numbers.Primitive.Word64.neg => "Primitive_words_runtime.Word64.neg".
Extract Constant Corelib.Numbers.Primitive.Word64.add => "Primitive_words_runtime.Word64.add".
Extract Constant Corelib.Numbers.Primitive.Word64.sub => "Primitive_words_runtime.Word64.sub".
Extract Constant Corelib.Numbers.Primitive.Word64.mul => "Primitive_words_runtime.Word64.mul".
Extract Constant Corelib.Numbers.Primitive.Word64.land => "Primitive_words_runtime.Word64.logand".
Extract Constant Corelib.Numbers.Primitive.Word64.lor => "Primitive_words_runtime.Word64.logor".
Extract Constant Corelib.Numbers.Primitive.Word64.lxor => "Primitive_words_runtime.Word64.logxor".
Extract Constant Corelib.Numbers.Primitive.Word64.lnot => "Primitive_words_runtime.Word64.lognot".
Extract Constant Corelib.Numbers.Primitive.Word64.eqb => "Primitive_words_runtime.Word64.equal".
Extract Constant Corelib.Numbers.Primitive.Word64.ltu => "Primitive_words_runtime.Word64.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word64.leu => "Primitive_words_runtime.Word64.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word64.lts => "Primitive_words_runtime.Word64.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word64.les => "Primitive_words_runtime.Word64.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word64.lsl => "Primitive_words_runtime.Word64.shift_left_word".
Extract Constant Corelib.Numbers.Primitive.Word64.lsr => "Primitive_words_runtime.Word64.shift_right_logical_word".
Extract Constant Corelib.Numbers.Primitive.Word64.asr => "Primitive_words_runtime.Word64.shift_right_arithmetic_word".
Extract Constant Corelib.Numbers.Primitive.Word64.divu => "Primitive_words_runtime.Word64.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word64.modu => "Primitive_words_runtime.Word64.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word64.divs => "Primitive_words_runtime.Word64.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word64.rems => "Primitive_words_runtime.Word64.rems_total".

Extract Constant Corelib.Numbers.Primitive.Word128.word128 =>
  "Primitive_words_runtime.Word128.t".
Extraction Inline Corelib.Numbers.Primitive.Word128.word128.
Extract Constant Corelib.Numbers.Primitive.Word128.neg => "Primitive_words_runtime.Word128.neg".
Extract Constant Corelib.Numbers.Primitive.Word128.add => "Primitive_words_runtime.Word128.add".
Extract Constant Corelib.Numbers.Primitive.Word128.sub => "Primitive_words_runtime.Word128.sub".
Extract Constant Corelib.Numbers.Primitive.Word128.mul => "Primitive_words_runtime.Word128.mul".
Extract Constant Corelib.Numbers.Primitive.Word128.land => "Primitive_words_runtime.Word128.logand".
Extract Constant Corelib.Numbers.Primitive.Word128.lor => "Primitive_words_runtime.Word128.logor".
Extract Constant Corelib.Numbers.Primitive.Word128.lxor => "Primitive_words_runtime.Word128.logxor".
Extract Constant Corelib.Numbers.Primitive.Word128.lnot => "Primitive_words_runtime.Word128.lognot".
Extract Constant Corelib.Numbers.Primitive.Word128.eqb => "Primitive_words_runtime.Word128.equal".
Extract Constant Corelib.Numbers.Primitive.Word128.ltu => "Primitive_words_runtime.Word128.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word128.leu => "Primitive_words_runtime.Word128.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word128.lts => "Primitive_words_runtime.Word128.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word128.les => "Primitive_words_runtime.Word128.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word128.lsl => "Primitive_words_runtime.Word128.shift_left_word".
Extract Constant Corelib.Numbers.Primitive.Word128.lsr => "Primitive_words_runtime.Word128.shift_right_logical_word".
Extract Constant Corelib.Numbers.Primitive.Word128.asr => "Primitive_words_runtime.Word128.shift_right_arithmetic_word".
Extract Constant Corelib.Numbers.Primitive.Word128.divu => "Primitive_words_runtime.Word128.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word128.modu => "Primitive_words_runtime.Word128.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word128.divs => "Primitive_words_runtime.Word128.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word128.rems => "Primitive_words_runtime.Word128.rems_total".

Extract Constant Corelib.Numbers.Primitive.Word256.word256 =>
  "Primitive_words_runtime.Word256.t".
Extraction Inline Corelib.Numbers.Primitive.Word256.word256.
Extract Constant Corelib.Numbers.Primitive.Word256.neg => "Primitive_words_runtime.Word256.neg".
Extract Constant Corelib.Numbers.Primitive.Word256.add => "Primitive_words_runtime.Word256.add".
Extract Constant Corelib.Numbers.Primitive.Word256.sub => "Primitive_words_runtime.Word256.sub".
Extract Constant Corelib.Numbers.Primitive.Word256.mul => "Primitive_words_runtime.Word256.mul".
Extract Constant Corelib.Numbers.Primitive.Word256.land => "Primitive_words_runtime.Word256.logand".
Extract Constant Corelib.Numbers.Primitive.Word256.lor => "Primitive_words_runtime.Word256.logor".
Extract Constant Corelib.Numbers.Primitive.Word256.lxor => "Primitive_words_runtime.Word256.logxor".
Extract Constant Corelib.Numbers.Primitive.Word256.lnot => "Primitive_words_runtime.Word256.lognot".
Extract Constant Corelib.Numbers.Primitive.Word256.eqb => "Primitive_words_runtime.Word256.equal".
Extract Constant Corelib.Numbers.Primitive.Word256.ltu => "Primitive_words_runtime.Word256.ltb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word256.leu => "Primitive_words_runtime.Word256.leb_unsigned".
Extract Constant Corelib.Numbers.Primitive.Word256.lts => "Primitive_words_runtime.Word256.ltb_signed".
Extract Constant Corelib.Numbers.Primitive.Word256.les => "Primitive_words_runtime.Word256.leb_signed".
Extract Constant Corelib.Numbers.Primitive.Word256.lsl => "Primitive_words_runtime.Word256.shift_left_word".
Extract Constant Corelib.Numbers.Primitive.Word256.lsr => "Primitive_words_runtime.Word256.shift_right_logical_word".
Extract Constant Corelib.Numbers.Primitive.Word256.asr => "Primitive_words_runtime.Word256.shift_right_arithmetic_word".
Extract Constant Corelib.Numbers.Primitive.Word256.divu => "Primitive_words_runtime.Word256.divu_total".
Extract Constant Corelib.Numbers.Primitive.Word256.modu => "Primitive_words_runtime.Word256.modu_total".
Extract Constant Corelib.Numbers.Primitive.Word256.divs => "Primitive_words_runtime.Word256.divs_total".
Extract Constant Corelib.Numbers.Primitive.Word256.rems => "Primitive_words_runtime.Word256.rems_total".
