Require Import ssreflect ssrnat ssrbool seq eqtype.

Context (ZZ : Type) (R : Set).
Context (plus mul : R -> R -> R) (inv : R -> R) (zero unit : R).
Context (group_mul : ZZ -> ZZ -> ZZ) (groupinv : ZZ -> ZZ) (Id : ZZ).

Notation "x + y" := (plus x y) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "0" := zero : ring_scope.
Notation "1" := unit : ring_scope.
Notation "- x" := (inv x) : ring_scope.
Notation "x ^-1" := (groupinv x) (at level 40).
Notation "x .* y " := (group_mul x y) (at level 50, left associativity).

Definition Comm (x y : ZZ) : ZZ := (x .* y .* x^-1 .* y^-1).
Notation "[ ~ x1 , x2 , .. , xn ]" :=
  (Comm .. (Comm x1 x2) .. xn) (at level 29, left associativity).

Open Scope ring_scope.

Axiom plus_assoc: forall a b c, (a + b) + c = a + (b + c).
Axiom mul_assoc: forall a b c, (a * b) * c = a * (b * c).
Axiom dist_l: forall a b c, a * (b + c) = (a * b) + (a * c).
Axiom dist_r: forall c a b, (a + b) * c = (a * c) + (b * c).
Axiom plus_comm: forall a b, a + b = b + a.
Axiom mul_comm: forall a b, a * b = b * a.
Axiom mul_1_r: forall a, a * 1 = a.
Axiom mul_1_l: forall a, 1 * a = a.
Axiom plus_1_r: forall a, a + 0 = a.
Axiom plus_1_l: forall a, 0 + a = a.
Axiom inv_r: forall a, a + (-a) = 0.
Axiom inv_l: forall a, (-a) + a = 0.
Lemma inv_mul: forall a b, -a * b = -(a * b). Admitted.
Lemma mul_inv: forall a b, a * (-b) = -(a * b). Admitted.
Lemma invI: forall a, -(-a) = a. Admitted.

Axiom GId: forall g, g .* Id = g.
Axiom IdG: forall g, Id .* g = g.
Axiom GA : forall g1 g2 g3, g1 .* g2 .* g3 = g1 .* (g2 .* g3).
Axiom GI : forall g, g .* (g ^-1) = Id.
Axiom IG: forall g, (g ^-1) .* g = Id.

Lemma GC: forall g3 g1 g2, g1 .* g3 = g2 .* g3 -> g1 = g2.
intros. have: (g1 .* g3 .* g3 ^-1 = g2 .* g3 .* g3 ^-1) by rewrite H.
by rewrite ?GA ?GI ?GId. Qed.

Lemma GIM: forall g1 g2, (g1 .* g2) ^-1 = g2 ^-1 .* g1 ^-1.
intros. apply (GC (g1 .* g2)). by rewrite IG GA -(GA (g1 ^-1)) IG IdG IG. Qed.

Lemma GII: forall g, g ^-1 ^-1 = g.
intros. apply (GC (g^-1)). by rewrite IG GI. Qed.

Lemma IdI: Id ^-1 = Id. apply (GC Id). by rewrite IG IdG. Qed.

Lemma Comm_inv: forall x y, [~ x, y] ^-1 = [~y, x].
intros. by rewrite /Comm ?GIM ?GII -?GA. Qed.

(* ********************************************** *)

Definition swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym. Defined.

Axiom X: forall {i j : nat}, (i != j) -> R -> ZZ.
Definition pow (h g : ZZ) := (g ^-1) .* h .* g.
Notation "h ^ g" := (pow h g).

Lemma pow_mul h g1 g2: h ^ (g1 .* g2) = (h ^ g1) ^ g2.
by rewrite /pow ?GIM ?GA. Qed.
Lemma mul_pow g h1 h2: (h1 .* h2) ^ g = h1 ^ g .* h2 ^ g.
by rewrite /pow ?GA -(GA g) GI IdG. Qed.

Definition Z {i j : nat} (p : i != j) (r s : R) := (X p r) ^ (X (swap_neq p) s).

Lemma Zdef {i j} (p : i!= j) r s: (X p r) ^ (X (swap_neq p) s) = Z p r s.
by rewrite /Z. Qed.
Lemma Zdef'{i j} (p : i!= j) r s: (X (swap_neq p) r) ^ (X p s) = Z (swap_neq p) r s.
rewrite /Z /=.

Axiom ST0: forall {i j : nat} (ij : (i != j)) r s, X ij (r + s) = X ij r .* X ij s.
Axiom ST1: forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X ij r , X jk s ] = X ik (r * s).
Axiom ST2: forall {i j k l : nat} (ij : (i != j)) (kl : (k != l)) r s, j != k -> i != l ->
 [~ X ij r, X kl s ] = Id.

Lemma Xzero: forall {i j : nat} (ij : (i != j)), X ij 0 = Id.
intros. apply (GC (X ij 0)). by rewrite -{3}(plus_1_l 0) ST0 IdG. Qed.

Lemma ST0': forall {i j : nat} (ij : (i != j)) r, X ij (- r) = (X ij r) ^-1.
intros. apply (GC (X ij r)). by rewrite -ST0 IG (inv_l) Xzero. Qed.

Lemma ST1': forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X jk r , X ij s ] = X ik (- s * r).
intros. by rewrite -Comm_inv ST1 -ST0' inv_mul. Qed.

Lemma pow_com: forall a b, a ^ b = [~ b ^-1, a] .* a. 
intros. rewrite /pow. apply (GC Id). by rewrite -{1}(IG a) -GA /Comm GII GId. Qed. 

Lemma ZLEMMA i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
 Z ij a (b * c) = Id.
intros. rewrite /Z. set ji := swap_neq ij. set ki := swap_neq ik.  set kj := swap_neq jk.
rewrite -(ST1 jk ji ki) /Comm ?pow_mul (pow_com (X ij a)) -ST0' ST1' mul_pow inv_mul mul_inv invI.
rewrite (pow_com (X ij a)) -ST0' (ST1 ki kj ij) inv_mul Zdef.
rewrite 2!(mul_pow (X jk (-b))). Check Zdef.