(************************************************************************)
(* Explicit scalar primitive-word width conversions.                   *)
(************************************************************************)

From Rocq.PrimitiveWords Require Import Word8 Word16 Word32 Word64 Word128 Word256.

(* Widening preserves either the unsigned value or the signed value. *)
Definition zero_extend_8_16 (x : Word8.t) : Word16.t :=
  Word16.of_N (Word8.to_N x).
Definition sign_extend_8_16 (x : Word8.t) : Word16.t :=
  Word16.of_Z (Word8.to_Z_signed x).
Definition zero_extend_8_32 (x : Word8.t) : Word32.t :=
  Word32.of_N (Word8.to_N x).
Definition sign_extend_8_32 (x : Word8.t) : Word32.t :=
  Word32.of_Z (Word8.to_Z_signed x).
Definition zero_extend_8_64 (x : Word8.t) : Word64.t :=
  Word64.of_N (Word8.to_N x).
Definition sign_extend_8_64 (x : Word8.t) : Word64.t :=
  Word64.of_Z (Word8.to_Z_signed x).
Definition zero_extend_8_128 (x : Word8.t) : Word128.t :=
  Word128.of_N (Word8.to_N x).
Definition sign_extend_8_128 (x : Word8.t) : Word128.t :=
  Word128.of_Z (Word8.to_Z_signed x).
Definition zero_extend_8_256 (x : Word8.t) : Word256.t :=
  Word256.of_N (Word8.to_N x).
Definition sign_extend_8_256 (x : Word8.t) : Word256.t :=
  Word256.of_Z (Word8.to_Z_signed x).

Definition zero_extend_16_32 (x : Word16.t) : Word32.t :=
  Word32.of_N (Word16.to_N x).
Definition sign_extend_16_32 (x : Word16.t) : Word32.t :=
  Word32.of_Z (Word16.to_Z_signed x).
Definition zero_extend_16_64 (x : Word16.t) : Word64.t :=
  Word64.of_N (Word16.to_N x).
Definition sign_extend_16_64 (x : Word16.t) : Word64.t :=
  Word64.of_Z (Word16.to_Z_signed x).
Definition zero_extend_16_128 (x : Word16.t) : Word128.t :=
  Word128.of_N (Word16.to_N x).
Definition sign_extend_16_128 (x : Word16.t) : Word128.t :=
  Word128.of_Z (Word16.to_Z_signed x).
Definition zero_extend_16_256 (x : Word16.t) : Word256.t :=
  Word256.of_N (Word16.to_N x).
Definition sign_extend_16_256 (x : Word16.t) : Word256.t :=
  Word256.of_Z (Word16.to_Z_signed x).

Definition zero_extend_32_64 (x : Word32.t) : Word64.t :=
  Word64.of_N (Word32.to_N x).
Definition sign_extend_32_64 (x : Word32.t) : Word64.t :=
  Word64.of_Z (Word32.to_Z_signed x).
Definition zero_extend_32_128 (x : Word32.t) : Word128.t :=
  Word128.of_N (Word32.to_N x).
Definition sign_extend_32_128 (x : Word32.t) : Word128.t :=
  Word128.of_Z (Word32.to_Z_signed x).
Definition zero_extend_32_256 (x : Word32.t) : Word256.t :=
  Word256.of_N (Word32.to_N x).
Definition sign_extend_32_256 (x : Word32.t) : Word256.t :=
  Word256.of_Z (Word32.to_Z_signed x).

Definition zero_extend_64_128 (x : Word64.t) : Word128.t :=
  Word128.of_N (Word64.to_N x).
Definition sign_extend_64_128 (x : Word64.t) : Word128.t :=
  Word128.of_Z (Word64.to_Z_signed x).
Definition zero_extend_64_256 (x : Word64.t) : Word256.t :=
  Word256.of_N (Word64.to_N x).
Definition sign_extend_64_256 (x : Word64.t) : Word256.t :=
  Word256.of_Z (Word64.to_Z_signed x).

Definition zero_extend_128_256 (x : Word128.t) : Word256.t :=
  Word256.of_N (Word128.to_N x).
Definition sign_extend_128_256 (x : Word128.t) : Word256.t :=
  Word256.of_Z (Word128.to_Z_signed x).

(* Narrowing always retains the low destination-width bits. *)
Definition narrow_16_8 (x : Word16.t) : Word8.t :=
  Word8.of_N (Word16.to_N x).
Definition narrow_32_8 (x : Word32.t) : Word8.t :=
  Word8.of_N (Word32.to_N x).
Definition narrow_32_16 (x : Word32.t) : Word16.t :=
  Word16.of_N (Word32.to_N x).
Definition narrow_64_8 (x : Word64.t) : Word8.t :=
  Word8.of_N (Word64.to_N x).
Definition narrow_64_16 (x : Word64.t) : Word16.t :=
  Word16.of_N (Word64.to_N x).
Definition narrow_64_32 (x : Word64.t) : Word32.t :=
  Word32.of_N (Word64.to_N x).
Definition narrow_128_8 (x : Word128.t) : Word8.t :=
  Word8.of_N (Word128.to_N x).
Definition narrow_128_16 (x : Word128.t) : Word16.t :=
  Word16.of_N (Word128.to_N x).
Definition narrow_128_32 (x : Word128.t) : Word32.t :=
  Word32.of_N (Word128.to_N x).
Definition narrow_128_64 (x : Word128.t) : Word64.t :=
  Word64.of_N (Word128.to_N x).
Definition narrow_256_8 (x : Word256.t) : Word8.t :=
  Word8.of_N (Word256.to_N x).
Definition narrow_256_16 (x : Word256.t) : Word16.t :=
  Word16.of_N (Word256.to_N x).
Definition narrow_256_32 (x : Word256.t) : Word32.t :=
  Word32.of_N (Word256.to_N x).
Definition narrow_256_64 (x : Word256.t) : Word64.t :=
  Word64.of_N (Word256.to_N x).
Definition narrow_256_128 (x : Word256.t) : Word128.t :=
  Word128.of_N (Word256.to_N x).
