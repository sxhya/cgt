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
Corollary GI' g A: g .* ((g ^-1) .* A) = A. by rewrite -GA GI IdG. Qed.
Axiom IG: forall g, (g ^-1) .* g = Id.
Corollary IG' g A: (g^-1) .* (g .* A) = A. by rewrite -GA IG IdG. Qed.

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

Definition swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym.  Defined.

(* TODO *) 
Lemma swapI {i j : nat} (p : i != j): swap_neq (swap_neq p) = p. Admitted. 

Axiom X: forall {i j : nat}, (i != j) -> R -> ZZ.
Definition pow (h g : ZZ) := (g ^-1) .* h .* g.
Notation "h ^ g" := (pow h g).

Lemma pow_mul h g1 g2: h ^ (g1 .* g2) = (h ^ g1) ^ g2.
by rewrite /pow ?GIM ?GA. Qed.
Lemma mul_pow g h1 h2: (h1 .* h2) ^ g = h1 ^ g .* h2 ^ g.
by rewrite /pow ?GA -(GA g) GI IdG. Qed.
Lemma powId g: g ^ Id = g. by rewrite /pow IdI IdG GId. Qed.

Definition Z {i j : nat} (p : i != j) (r s : R) := (X p r) ^ (X (swap_neq p) s).

Lemma Zdef {i j} (p : i!= j) r s: (X p r) ^ (X (swap_neq p) s) = Z p r s. by rewrite /Z. Qed.

Lemma Zdef'{i j} (p : i!= j) r s: (X (swap_neq p) r) ^ (X p s) = Z (swap_neq p) r s.
by rewrite /Z swapI. Qed.

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

Lemma ST2': forall {i j k} (ik : i != k) (jk : j != k) (ij : i != j) a b, X ik a ^ X jk b = X ik a.
intros. rewrite pow_com -ST0' ST2. by rewrite IdG. exact (swap_neq ik). exact jk. Qed.

Lemma ST2'': forall {i j k} (ki : k != i) (kj : k != j) (ij : i != j) a b, X ki a ^ X kj b = X ki a.
intros. rewrite pow_com -ST0' ST2. by rewrite IdG. exact (swap_neq kj). exact ki. Qed.

Lemma R10 i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let RHS := 
 X jk (- (b * c * (a * b))) .* X ik (a * b)
.* (X (swap_neq ij) (- (b * (c * a * (b * c)))) .* X (swap_neq ik) (- (c * a * (b * c)))
.* Z (swap_neq jk) (- (c * a)) (- b)) .* Z ik (- a * b) (- c)
.* (X (swap_neq jk) (c * a) .* X ij a) in
 Z ij a (b * c) = RHS.
intros. rewrite /Z. set ji := swap_neq ij. set ki := swap_neq ik.  set kj := swap_neq jk.
rewrite -(ST1 jk ji ki) /Comm ?pow_mul (pow_com (X ij a)) -ST0' ST1' mul_pow inv_mul mul_inv invI
        (pow_com (X ij a)) -ST0' (ST1 ki kj ij) inv_mul.
rewrite 2!(mul_pow (X jk (-b))) Zdef' -(pow_mul). replace (swap_neq jk) with kj by done.
replace (X ki c .* X jk (-b)) with ([~ X ki c, X jk (-b)] .* X jk (-b) .* X ki c); 
 [|by rewrite /Comm ?GA -(GA (X jk (- b) ^-1)) IG IdG IG GId].
rewrite (ST1' jk ji ki) invI ?pow_mul (pow_com (X ik (a * b))) -ST0' ST1 inv_mul.
rewrite (mul_pow (X jk (- b))) {3}/pow -ST0' invI -2!ST0 (plus_comm b) plus_assoc inv_r plus_1_r. 
rewrite ST2'; [|exact ij]. rewrite (mul_pow (X ki c)) Zdef (pow_com _ (X ki c)) -ST0' ST1' invI mul_inv.
rewrite (pow_com (X ij a)) -ST0' invI ST1'.
remember (Z ik (a*b) c) as Z1. remember (Z kj (-(c*a)) (-b)) as Z2.
rewrite -?GA ?mul_pow HeqZ1 HeqZ2 {HeqZ1 HeqZ2 Z1 Z2}.
rewrite {1}/Z -pow_mul. replace (swap_neq ik) with ki; [|done]. rewrite -ST0 inv_r Xzero powId Zdef.
rewrite ST2'; [|exact jk]. rewrite (pow_com _ (X ki (- c))) -ST0' invI ST1' invI ST0' -GA IG IdG.
rewrite {1}/Z -pow_mul swapI. 
replace (X jk (- b) .* X ki (- c)) with ([~X jk (- b), X ki (- c)] .* X ki (- c) .* X jk (- b));
  [|by rewrite /Comm ?GA -(GA (X ki (- c) ^-1)) IG IdG IG GId].
rewrite ST1 inv_mul mul_inv invI (GA (X ji (b * c))) pow_mul (pow_com (X kj (- (c * a)))) -ST0' ST1' invI mul_inv mul_pow.
assert (A0: X ki (- c) .* X jk (- b) = [~ X ki (- c) , X jk (- b)] .* X jk (- b) .* X ki (- c)) by by
 rewrite /Comm ?GA -(GA (X jk (- b) ^-1)) IG IdG IG GId.
rewrite {1}A0 {A0} ST1' inv_mul mul_inv invI (pow_com (X ij a)) -ST0' invI ST1
        (GA (X ji (- b * c))) pow_mul ST2'; [|exact kj].
rewrite 2!pow_mul ST2''; [|exact ji].
rewrite Zdef' (pow_com (X ki (- (c * a * (b * c))))) -ST0' invI ST1 mul_inv
        mul_pow ST2' /pow;[|exact jk].
by rewrite -ST0' invI -?ST0 plus_comm -plus_assoc inv_l plus_1_l. Qed.

Corollary R1 i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = 
X jk (- (b * c * a * b)) .* X ik (a * b) .* (X ji (- (b * c * a * b * c))
    .* X ki (- (c * a * b * c)) .* Z kj (- (c * a)) (- b)) .* Z ik (- (a * b)) (- c) .* X kj (c * a) .* X ij a.
intros. move: (R10 i j k a b c ij ik jk). by rewrite -GA -?mul_assoc inv_mul. Qed.

Corollary R2 i j k a b: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
 Z ij a b = X jk (- (b * a * b)) .* X ik (a * b) .* (X ji (- (b * a * b)) .* X ki (- (a * b)) 
         .* Z kj (- a) (- b))    .* Z ik (- (a * b)) (- unit) .* X kj a .* X ij a.
 intros. by rewrite -{1} (mul_1_r b) (R1 i j k a b unit ij ik jk) ?mul_1_r ?mul_1_l. Qed.

Ltac expand := rewrite /Comm /pow ?GIM ?GII.
Ltac cancel := rewrite ?GI' ?IG' ?GI ?IG.
Ltac cancellate := expand; rewrite ?GA; cancel.

Lemma HallWitt x y z: 
 [~ y^-1, x, z] ^ (y^-1) .* 
 [~ z^-1, y, x] ^ (z^-1) .* 
 [~ x^-1, z, y] ^ (x^-1) = Id. by expand; rewrite ?GA; do 4 cancel. Qed.

Corollary HallWitt2 x y z: [~ y, x^-1, z^-1]^ y .* [~z, y^-1, x^-1]^ (z) .* [~x, z^-1, y^-1] ^ x = Id.
move: (HallWitt (x^-1) (y^-1) (z^-1)). by rewrite ?GII. Qed.

Lemma CL1 x y z: [~z, x, y]^ z = [~x, z^-1, y^z]. by cancellate. Qed.
Lemma CL2 x y z: [~ x .* y, z] = [~y, z] ^ (x^-1) .* [~x, z]. by cancellate. Qed.
Lemma CL3 x y z: [~ x, y .* z] = [~x, y] .* [~x, z] ^ (y^-1). by cancellate. Qed.
Lemma CL4 x y z: [~ x, y] ^ z = [~x ^ z, y ^ z]. by cancellate. Qed.
Lemma CL5 x y: [~ x, y] = y ^ (x^-1) .* y^-1. by cancellate. Qed.

Corollary HallWitt3 x y z: 
 [~ x^-1, y^-1, (z^-1)^y] .* 
 [~ y^-1, z^-1, (x^-1)^z] .* 
 [~ z^-1, x^-1, (y^-1)^x] = Id. by rewrite -?CL1 HallWitt2. Qed.

Definition HW x y z := [~x, y, z^(y^-1)] .*  [~y, z, x^(z^-1)] .*  [~z, x, y^(x^-1)].

Corollary HallWitt4 x y z: HW x y z = Id.
move: (HallWitt3 (x^-1) (y^-1) (z^-1)). by rewrite /HW ?GII. Qed.

Lemma R10' i j k (a b c : R): forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
let RHS := 
    Z ij a (- (b * c)) .* X ij (-a) .* X ki (- (c * a * b * c)) .* X kj (c * a * b * c * a)
 .* Z jk b (- (c * a)) .* X jk (-b) .* X ij (- (a * b * c * a)) .* X ik (a * b * c * a * b) 
 .* Z ki c (- (a * b)) .* X ki (-c) .* X jk (- (b * c * a * b)) .* X ji (b * c * a * b * c) in Id = RHS.
intros. assert (A0: HW (X jk b) (X ki c) (X ij a) = Id). apply HallWitt4.
rewrite /HW ?pow_com -?ST0' ?GII ?invI ?ST1 ?CL3 ST1' (ST1' ik) (ST1' ji) in A0.
rewrite ?CL4 -?ST0' ?ST2' in A0; [| exact kj| exact ji| exact ik].
rewrite ?pow_com -?ST0' ?invI ?ST1 ?CL2 in A0.
rewrite (ST1 ki) (ST1 ij) (ST1 jk) /pow ?inv_mul -?mul_assoc ?GII ?ST0' ?CL5 -?ST0' ?Zdef ?Zdef' in A0.
remember (Z ij a (- (b * c))) as Z1. remember (Z jk b (- (c * a))) as Z2. remember (Z (swap_neq ik) c (- (a * b))) as Z3.
rewrite ?GA ?ST0' ?IG' -?GA -?ST0' in A0. 
move: A0. unfold RHS. unfold ji. unfold ki. unfold kj. subst. done. Qed.