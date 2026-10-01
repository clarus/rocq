(* Fixed-width primitive literals, kernel reduction, cbv, and VM agreement. *)
From Corelib.Numbers.Primitive Require Import Word8 Word16 Word32 Word64 Word128 Word256.
Example primitive_wrap_8_kernel : Word8.add 255%word8 1%word8 = 0%word8.
Proof. exact eq_refl. Qed.
Example primitive_wrap_8_cbv : Word8.add 255%word8 1%word8 = 0%word8.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_8_vm : Word8.add 255%word8 1%word8 = 0%word8.
Proof. vm_compute; reflexivity. Qed.
Fail Check 256%word8.
Fail Check (-1)%word8.
Example primitive_wrap_16_kernel : Word16.add 65535%word16 1%word16 = 0%word16.
Proof. exact eq_refl. Qed.
Example primitive_wrap_16_cbv : Word16.add 65535%word16 1%word16 = 0%word16.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_16_vm : Word16.add 65535%word16 1%word16 = 0%word16.
Proof. vm_compute; reflexivity. Qed.
Fail Check 65536%word16.
Fail Check (-1)%word16.
Example primitive_wrap_32_kernel : Word32.add 4294967295%word32 1%word32 = 0%word32.
Proof. exact eq_refl. Qed.
Example primitive_wrap_32_cbv : Word32.add 4294967295%word32 1%word32 = 0%word32.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_32_vm : Word32.add 4294967295%word32 1%word32 = 0%word32.
Proof. vm_compute; reflexivity. Qed.
Fail Check 4294967296%word32.
Fail Check (-1)%word32.
Example primitive_wrap_64_kernel : Word64.add 18446744073709551615%word64 1%word64 = 0%word64.
Proof. exact eq_refl. Qed.
Example primitive_wrap_64_cbv : Word64.add 18446744073709551615%word64 1%word64 = 0%word64.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_64_vm : Word64.add 18446744073709551615%word64 1%word64 = 0%word64.
Proof. vm_compute; reflexivity. Qed.
Fail Check 18446744073709551616%word64.
Fail Check (-1)%word64.
Example primitive_wrap_128_kernel : Word128.add 340282366920938463463374607431768211455%word128 1%word128 = 0%word128.
Proof. exact eq_refl. Qed.
Example primitive_wrap_128_cbv : Word128.add 340282366920938463463374607431768211455%word128 1%word128 = 0%word128.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_128_vm : Word128.add 340282366920938463463374607431768211455%word128 1%word128 = 0%word128.
Proof. vm_compute; reflexivity. Qed.
Fail Check 340282366920938463463374607431768211456%word128.
Fail Check (-1)%word128.
Example primitive_wrap_256_kernel : Word256.add 115792089237316195423570985008687907853269984665640564039457584007913129639935%word256 1%word256 = 0%word256.
Proof. exact eq_refl. Qed.
Example primitive_wrap_256_cbv : Word256.add 115792089237316195423570985008687907853269984665640564039457584007913129639935%word256 1%word256 = 0%word256.
Proof. cbv; reflexivity. Qed.
Example primitive_wrap_256_vm : Word256.add 115792089237316195423570985008687907853269984665640564039457584007913129639935%word256 1%word256 = 0%word256.
Proof. vm_compute; reflexivity. Qed.
Fail Check 115792089237316195423570985008687907853269984665640564039457584007913129639936%word256.
Fail Check (-1)%word256.
Fail Check (0%word8 : Word16.word16).
