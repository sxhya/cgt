Require Import ssreflect ssrnat ssrbool seq eqtype.

Module RingFacts.
Variable (R : Type).
Variable (plus mul : R -> R -> R) (inv : R -> R) (zero unit : R).

Notation "x + y" := (plus x y) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "0" := zero : ring_scope.
Notation "1" := unit : ring_scope.
Notation "- x" := (inv x) : ring_scope.

Open Scope ring_scope.

Axiom plus_assoc: forall a b c, (a + b) + c = a + (b + c).
Axiom mul_assoc: forall a b c, (a * b) * c = a * (b * c).
Axiom dist_l: forall a b c, a * (b + c) = (a * b) + (a * c).
Axiom dist_r: forall c a b, (a + b) * c = (a * c) + (b * c).
Axiom plus_comm: forall a b, a + b = b + a.
Axiom mul_comm: forall a b, a * b = b * a.
Axiom mul_1_r: forall a, a * 1 = a.
Axiom mul_1_l: forall a, 1 * a = a.
Axiom plus_0_r: forall a, a + 0 = a.
Axiom plus_0_l: forall a, 0 + a = a.
Axiom inv_r: forall a, a + (-a) = 0.
Axiom inv_l: forall a, (-a) + a = 0.

Lemma canc_r a b c: a + b = a + c -> b = c.
intros. have: (-a+(a+b) = -a+(a+c)) by rewrite H.
by rewrite -?plus_assoc ?inv_l ?plus_0_l. Qed.

Lemma canc_l a b c: b + a = c + a -> b = c.
intros. have: ((b+a)+(-a)) = (c+a)+(-a) by rewrite H.
by rewrite ?plus_assoc ?inv_r ?plus_0_r. Qed.

Lemma mul_0_r a: a * 0 = 0.
apply (canc_r (a * 0)). by rewrite -dist_l ?plus_0_r. Qed.

Lemma mul_0_l a: 0 * a = 0.
apply (canc_l (0 * a)). by rewrite -dist_r ?plus_0_l. Qed.

Lemma inv_mul a b: -a * b = -(a * b).
apply (canc_r (a * b)). by rewrite -dist_r ?inv_r mul_0_l. Qed.

Lemma mul_inv a b: a * (-b) = -(a * b).
apply (canc_l (a * b)). by rewrite -dist_l ?inv_l mul_0_r. Qed.

Lemma invI a: -(-a) = a.
apply (canc_r (-a)). by rewrite inv_l inv_r. Qed.

Ltac rsimpl := rewrite ?mul_inv ?inv_mul ?mul_1_r ?mul_1_l -?mul_assoc ?invI.

End RingFacts.