(************************************************************************)
(* Opaque closed width bounds used by cross-width proof units.         *)
(************************************************************************)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Lemma modulus_8_lt_16 : 256 < 65536.
Proof. reflexivity. Qed.
Lemma modulus_8_lt_32 : 256 < 4294967296.
Proof. reflexivity. Qed.
Lemma modulus_8_lt_64 : 256 < 18446744073709551616.
Proof. reflexivity. Qed.
Lemma modulus_8_lt_128 :
    256 < 340282366920938463463374607431768211456.
Proof. reflexivity. Qed.
Lemma modulus_8_lt_256 :
    256 <
    115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.

Lemma modulus_16_lt_32 : 65536 < 4294967296.
Proof. reflexivity. Qed.
Lemma modulus_16_lt_64 : 65536 < 18446744073709551616.
Proof. reflexivity. Qed.
Lemma modulus_16_lt_128 :
    65536 < 340282366920938463463374607431768211456.
Proof. reflexivity. Qed.
Lemma modulus_16_lt_256 :
    65536 <
    115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.

Lemma modulus_32_lt_64 : 4294967296 < 18446744073709551616.
Proof. reflexivity. Qed.
Lemma modulus_32_lt_128 :
    4294967296 < 340282366920938463463374607431768211456.
Proof. reflexivity. Qed.
Lemma modulus_32_lt_256 :
    4294967296 <
    115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.

Lemma modulus_64_lt_128 :
    18446744073709551616 < 340282366920938463463374607431768211456.
Proof. reflexivity. Qed.
Lemma modulus_64_lt_256 :
    18446744073709551616 <
    115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.

Lemma modulus_128_lt_256 :
    340282366920938463463374607431768211456 <
    115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.
