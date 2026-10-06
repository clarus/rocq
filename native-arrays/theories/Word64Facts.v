(************************************************************************)
(* Ordinary arithmetic facts derived from the existing Word64 laws.     *)
(************************************************************************)

From Stdlib Require Import ZArith Lia.
From Corelib.Numbers.Primitive Require Import Word64.
From Rocq.PrimitiveWords Require Import PrimitiveWordDerived.

Module W := Corelib.Numbers.Primitive.Word64.
Module D := PrimitiveWordDerived.Word64Derived.

(* Preserve the arithmetic observation as a symbol during proof search. Its
   implementation is a 64-step conversion, which unification need not expand. *)
Local Opaque D.unsigned.

Definition U : W.word64 -> Z := D.unsigned.
Definition modulus : Z := 18446744073709551616.

Open Scope Z_scope.

Lemma range : forall x, 0 <= U x < modulus.
Proof. exact D.unsigned_range. Qed.

Lemma unsigned_injective : forall x y, U x = U y -> x = y.
Proof. exact D.unsigned_injective. Qed.

Lemma zero : U 0%word64 = 0.
Proof. exact D.zero_spec. Qed.

Lemma one : U 1%word64 = 1.
Proof. exact D.one_spec. Qed.

Lemma maximum : U 18446744073709551615%word64 = modulus - 1.
Proof. exact D.max_unsigned_spec. Qed.

Lemma eqb_value : forall x y, W.eqb x y = Z.eqb (U x) (U y).
Proof. exact D.eqb_value. Qed.

Lemma eqb_true : forall x y, W.eqb x y = true <-> x = y.
Proof. exact D.eqb_spec. Qed.

Lemma ltu_true : forall x y, W.ltu x y = true <-> U x < U y.
Proof. intros x y. unfold U. rewrite D.ltu_spec. exact (Z.ltb_lt (D.unsigned x) (D.unsigned y)). Qed.

Lemma ltu_false : forall x y, W.ltu x y = false <-> U y <= U x.
Proof. intros x y. unfold U. rewrite D.ltu_spec. exact (Z.ltb_ge (D.unsigned x) (D.unsigned y)). Qed.

Lemma leu_true : forall x y, W.leu x y = true <-> U x <= U y.
Proof. intros x y. unfold U. rewrite D.leu_spec. exact (Z.leb_le (D.unsigned x) (D.unsigned y)). Qed.

Lemma leu_false : forall x y, W.leu x y = false <-> U y < U x.
Proof. intros x y. unfold U. rewrite D.leu_spec. exact (Z.leb_gt (D.unsigned x) (D.unsigned y)). Qed.

Lemma add_small : forall x y, U x + U y < modulus ->
  U (W.add x y) = U x + U y.
Proof.
  intros x y H. unfold U. rewrite D.add_spec. apply D.repr_small.
  pose proof (range x). pose proof (range y). change (0 <= U x + U y < modulus). lia.
Qed.

Lemma sub_small : forall x y, U y <= U x ->
  U (W.sub x y) = U x - U y.
Proof.
  intros x y H. unfold U. rewrite D.sub_spec. apply D.repr_small.
  pose proof (range x). pose proof (range y). change (0 <= U x - U y < modulus). lia.
Qed.

Lemma half : forall x, U (W.lsr x 1%word64) = U x / 2.
Proof. exact D.lsr_one_spec. Qed.

Lemma add_zero_left : forall x, W.add 0%word64 x = x.
Proof.
  intro x. apply unsigned_injective. rewrite add_small, zero; [lia|].
  rewrite zero. apply (proj2 (range x)).
Qed.

Lemma add_zero_right : forall x, W.add x 0%word64 = x.
Proof.
  intro x. apply unsigned_injective. rewrite add_small, zero; [lia|].
  rewrite zero. pose proof (range x). lia.
Qed.

Lemma sub_zero : forall x, W.sub x 0%word64 = x.
Proof.
  intro x. apply unsigned_injective. rewrite sub_small, zero; [lia|].
  rewrite zero. apply (proj1 (range x)).
Qed.

Lemma add_sub_cancel : forall x y, U x <= U y -> W.add x (W.sub y x) = y.
Proof.
  intros x y H. apply unsigned_injective.
  rewrite add_small, sub_small by (try assumption; rewrite sub_small by assumption; pose proof (range y); lia).
  lia.
Qed.

Lemma sub_add_cancel : forall x y, U x + U y < modulus -> W.sub (W.add x y) x = y.
Proof.
  intros x y H. apply unsigned_injective.
  rewrite sub_small, add_small by (try assumption; rewrite add_small by assumption; pose proof (range y); lia).
  lia.
Qed.

Lemma add_assoc_small : forall x y z, U x + U y + U z < modulus ->
  W.add x (W.add y z) = W.add (W.add x y) z.
Proof.
  intros x y z H. pose proof (range x). pose proof (range y). pose proof (range z).
  apply unsigned_injective.
  assert (Hxy : U x + U y < modulus) by lia.
  assert (Hyz : U y + U z < modulus) by lia.
  rewrite !add_small by (try lia; rewrite add_small by lia; lia).
  lia.
Qed.
