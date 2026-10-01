From Stdlib Require Import ZArith List Extraction.
From Rocq.PrimitiveWords Require Import
  Word8 Word16 Word32 Word64 ScalarExtraction.

Import ListNotations.

Definition signed_right8 (value count : Word8.t) : Z :=
  Word8.to_Z_unsigned (Word8.shift_right_signed value count).
Definition signed_right16 (value count : Word16.t) : Z :=
  Word16.to_Z_unsigned (Word16.shift_right_signed value count).
Definition signed_right32 (value count : Word32.t) : Z :=
  Word32.to_Z_unsigned (Word32.shift_right_signed value count).
Definition signed_right64 (value count : Word64.t) : Z :=
  Word64.to_Z_unsigned (Word64.shift_right_signed value count).

(* Each width uses both negative-value boundary patterns.  Counts are
   +0, +1, +width, +(width+1), -1 and minimum signed respectively. *)
Definition pw020_signed_shift_witnesses : list Z :=
  [ signed_right8 Word8.max_unsigned Word8.zero
  ; signed_right8 Word8.max_unsigned Word8.one
  ; signed_right8 Word8.max_unsigned (Word8.of_Z 8)
  ; signed_right8 Word8.max_unsigned (Word8.of_Z 9)
  ; signed_right8 Word8.max_unsigned Word8.max_unsigned
  ; signed_right8 Word8.max_unsigned Word8.min_signed
  ; signed_right8 Word8.min_signed Word8.zero
  ; signed_right8 Word8.min_signed Word8.one
  ; signed_right8 Word8.min_signed (Word8.of_Z 8)
  ; signed_right8 Word8.min_signed (Word8.of_Z 9)
  ; signed_right8 Word8.min_signed Word8.max_unsigned
  ; signed_right8 Word8.min_signed Word8.min_signed
  ; signed_right16 Word16.max_unsigned Word16.zero
  ; signed_right16 Word16.max_unsigned Word16.one
  ; signed_right16 Word16.max_unsigned (Word16.of_Z 16)
  ; signed_right16 Word16.max_unsigned (Word16.of_Z 17)
  ; signed_right16 Word16.max_unsigned Word16.max_unsigned
  ; signed_right16 Word16.max_unsigned Word16.min_signed
  ; signed_right16 Word16.min_signed Word16.zero
  ; signed_right16 Word16.min_signed Word16.one
  ; signed_right16 Word16.min_signed (Word16.of_Z 16)
  ; signed_right16 Word16.min_signed (Word16.of_Z 17)
  ; signed_right16 Word16.min_signed Word16.max_unsigned
  ; signed_right16 Word16.min_signed Word16.min_signed
  ; signed_right32 Word32.max_unsigned Word32.zero
  ; signed_right32 Word32.max_unsigned Word32.one
  ; signed_right32 Word32.max_unsigned (Word32.of_Z 32)
  ; signed_right32 Word32.max_unsigned (Word32.of_Z 33)
  ; signed_right32 Word32.max_unsigned Word32.max_unsigned
  ; signed_right32 Word32.max_unsigned Word32.min_signed
  ; signed_right32 Word32.min_signed Word32.zero
  ; signed_right32 Word32.min_signed Word32.one
  ; signed_right32 Word32.min_signed (Word32.of_Z 32)
  ; signed_right32 Word32.min_signed (Word32.of_Z 33)
  ; signed_right32 Word32.min_signed Word32.max_unsigned
  ; signed_right32 Word32.min_signed Word32.min_signed
  ; signed_right64 Word64.max_unsigned Word64.zero
  ; signed_right64 Word64.max_unsigned Word64.one
  ; signed_right64 Word64.max_unsigned (Word64.of_Z 64)
  ; signed_right64 Word64.max_unsigned (Word64.of_Z 65)
  ; signed_right64 Word64.max_unsigned Word64.max_unsigned
  ; signed_right64 Word64.max_unsigned Word64.min_signed
  ; signed_right64 Word64.min_signed Word64.zero
  ; signed_right64 Word64.min_signed Word64.one
  ; signed_right64 Word64.min_signed (Word64.of_Z 64)
  ; signed_right64 Word64.min_signed (Word64.of_Z 65)
  ; signed_right64 Word64.min_signed Word64.max_unsigned
  ; signed_right64 Word64.min_signed Word64.min_signed
  ].

(* Independent, explicit bit-pattern expectations from TARGET.md and the
   production Word64 arithmetic-right signed-count contract. *)
Definition pw020_signed_shift_expected : list Z :=
  [ 255; 255; 255; 255; 254; 0
  ; 128; 192; 255; 255; 0; 0
  ; 65535; 65535; 65535; 65535; 65534; 0
  ; 32768; 49152; 65535; 65535; 0; 0
  ; 4294967295; 4294967295; 4294967295; 4294967295; 4294967294; 0
  ; 2147483648; 3221225472; 4294967295; 4294967295; 0; 0
  ; 18446744073709551615; 18446744073709551615
  ; 18446744073709551615; 18446744073709551615
  ; 18446744073709551614; 0
  ; 9223372036854775808; 13835058055282163712
  ; 18446744073709551615; 18446744073709551615; 0; 0
  ]%Z.

Example pw020_signed_shift_cbv_ok :
  pw020_signed_shift_witnesses = pw020_signed_shift_expected.
Proof. cbv. reflexivity. Qed.

Example pw020_signed_shift_vm_ok :
  pw020_signed_shift_witnesses = pw020_signed_shift_expected.
Proof. vm_compute. reflexivity. Qed.

Extraction "PW020SignedShiftExtracted.ml" pw020_signed_shift_witnesses.
