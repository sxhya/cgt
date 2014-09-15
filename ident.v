Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.

Module SteinbergGroup <: GroupCarrier.
Variable ZZ : Type.
End SteinbergGroup.

Module Import GF := Group.GroupFacts SteinbergGroup.
Module Import RF := Ring.RingFacts.
Import SteinbergGroup.

(* ********************************************** *)

Definition swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym.  Defined.

(* This statement is needed to get rid of proof-relevant nature of argument p of Z *) 
Axiom swapI : forall {i j : nat} (p : i != j), swap_neq (swap_neq p) = p.

Axiom X: forall {i j : nat}, (i != j) -> R -> ZZ.

Definition Z {i j : nat} (p : i != j) (r s : R) : ZZ := locked ((X p r) ^ (X (swap_neq p) s)).

Lemma Zdef {i j} (p : i!= j) r s: (X (p) r) ^ (X (swap_neq p) s) = Z p r s. by unlock Z. Qed.

Lemma Zdef'{i j} (p : i!= j) r s: (X (swap_neq p) r) ^ (X p s) = Z (swap_neq p) r s.
by unlock Z; rewrite swapI. Qed.

Axiom ST0: forall {i j : nat} (ij : (i != j)) r s, X ij (r + s) = X ij r .* X ij s.
Axiom ST1: forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X ij r , X jk s ] = X ik (r * s).
Axiom ST2: forall {i j k l : nat} (ij : (i != j)) (kl : (k != l)) r s, j != k -> i != l ->
 [~ X ij r, X kl s ] = Id.

Lemma Xzero: forall {i j : nat} (ij : (i != j)), X ij 0 = Id.
intros. apply (GCr (X ij 0)). by rewrite -{3}(plus_1_l 0) ST0 IdG. Qed.

Lemma ST0': forall {i j : nat} (ij : (i != j)) r, X ij (- r) = (X ij r) ^-1.
intros. apply (GCr (X ij r)). by rewrite -ST0 IG (inv_l) Xzero. Qed.

Lemma ST1': forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X jk r , X ij s ] = X ik (- s * r).
intros. by rewrite -comm_inv ST1 -ST0' inv_mul. Qed.

Lemma ST2': forall {i j k} {ik : i != k} {jk : j != k} (ij : i != j) a b, X ik a ^ X jk b = X ik a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq ik). exact jk. Qed.

Lemma ST2'': forall {i j k} {ki : k != i} {kj : k != j} (ij : i != j) a b, X ki a ^ X kj b = X ki a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq kj). exact ki. Qed.

Lemma Zinv {i j} (ij : i != j) (r s : R): Z ij (-r) s = (Z ij r s)^-1.
by unlock Z; rewrite /conj ST0' ?GIM ?GA GII. Qed.

(* Petrov's relation and its variations *)

Lemma R10 i j k a b c (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
let RHS := X jk (- (b * c * (a * b))) .* X ik (a * b)
.* (X ji (- (b * (c * a * (b * c)))) .* X ki (- (c * a * (b * c)))
.* Z kj (- (c * a)) (- b)) .* Z ik (- a * b) (- c)
.* (X kj (c * a) .* X ij a) in Z ij a (b * c) = RHS.
intros.
by rewrite 
 /Z -lock -(ST1 jk ji ki) /Comm ?conj_mul (conj_com (X ij a)) -ST0' ST1' mul_conj inv_mul mul_inv invI
 (conj_com (X ij a)) -ST0' (ST1 ki kj ij) inv_mul 2!(mul_conj (X jk (-b))) Zdef' -(conj_mul) -/kj
 (swap_comm (X ki c))(ST1' jk ji ki) invI ?conj_mul (conj_com (X ik (a * b))) -ST0' ST1 inv_mul
 (mul_conj (X jk (- b))) {3}/conj -ST0' invI -2!ST0 (plus_comm b) plus_assoc inv_r plus_1_r
 (ST2' ij) (mul_conj (X ki c)) Zdef (conj_com _ (X ki c)) -ST0' ST1' invI mul_inv
 (conj_com (X ij a)) -ST0' invI ST1' -?GA ?mul_conj {1}/Z -lock
 -conj_mul -/ki -ST0 inv_r Xzero conjId Zdef (ST2' jk)
 (conj_com _ (X ki (- c))) -ST0' invI ST1' invI ST0' -GA IG IdG
 {1}/Z -lock -conj_mul swapI (swap_comm (X jk (-b))) ST1 inv_mul mul_inv invI 
 (GA (X ji (b * c))) conj_mul (conj_com (X kj (- (c * a)))) -ST0' ST1' invI mul_inv mul_conj
 {1}(swap_comm (X ki (-c))) ST1' inv_mul mul_inv invI (conj_com (X ij a)) -ST0' invI ST1
 (GA (X ji (- b * c))) conj_mul (ST2' kj)
 2!conj_mul (ST2'' ji) Zdef' (conj_com (X ki (- (c * a * (b * c))))) -ST0' invI ST1 mul_inv
 mul_conj (ST2' jk) /conj -ST0' invI -?ST0 plus_comm -plus_assoc inv_l plus_1_l //. Qed.

Corollary R1' i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = 
   X jk (- (b * c * a * b)) .* X ik (a * b) .* (X ji (- (b * c * a * b * c))
.* X ki (- (c * a * b * c)) .* Z kj (- (c * a)) (- b)) .* Z ik (- (a * b)) (- c) 
.* X kj (c * a) .* X ij a.

intros. move: (R10 i j k a b c ij ik jk) => /=. by rewrite -GA -?mul_assoc inv_mul. Qed.

Corollary R1'' i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) .* X ij (- a) .* X kj (- (c * a)) .*  Z ik (a * b) (- c) .* Z kj (c * a) (- b) .* 
  X ki (c * a * b * c) .* X ji (b * c * a * b * c) .* X ik (- (a * b)) .* X jk (b * c * a * b) = Id.

intros. rewrite (R1' i j k) /Z -?lock /conj /ji /ki /kj ?ST0' ?GII ?GA. by do 4 cancel. Qed.

Corollary R1''' i j k (a b c : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ik (a * b) c =
  X kj (- (c * a)) .* X ij a .* Z ij (- a) (- (b * c)) .* X jk (b * c * a * b)
  .* X ik (a * b) .* X ji (- (b * c * a * b * c)) .* X ki (- (c * a * b * c))
  .* Z kj (c * a) (- b). 

intros. move: (R1'' i j k a b (-c) ij ik jk) => /=.
rewrite -/ji -/ki -/kj ?inv_mul ?mul_inv ?inv_mul ?invI => H.
apply eqIdP in H. rewrite -?ST0' ?invI in H. rewrite -{} H.
rewrite ?ST0' ?GA ?Zinv. do 2 cancel. by rewrite GId. Qed.

(* Another (botched!) attempt of deriving Petrov's relation *)

Definition HW x y z := [~x, y, z^(y^-1)] .*  [~y, z, x^(z^-1)] .*  [~z, x, y^(x^-1)].

Corollary HallWitt4 x y z: HW x y z = Id.
move: (HallWitt'' (x^-1) (y^-1) (z^-1)). by rewrite /HW ?GII. Qed.

Lemma R10' i j k (a b c : R): forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
let RHS := 
Z ij a (- (b * c)) .* X ij (- a) .* X ki (- (c * a * b * c))
.* X kj (c * a * b * c * a) .* X kj (c * a)
.* Z kj (- (c * a)) (- b) .* X ij (- (a * b * c * a))
.* X ik (a * b * c * a * b) .* X ik (a * b) .* Z ik (- (a * b)) (- c)
.* X jk (- (b * c * a * b)) .* X ji (b * c * a * b * c) in Id = RHS.

intros. assert (A0: HW (X jk b) (X ki c) (X ij a) = Id). apply HallWitt4.
move: A0. rewrite /HW ?ST1 ?conj_com -?ST0' ?GII ?invI ?ST1 ?cmul_r 
 ST1' (ST1' ik) (ST1' ji) ?comm_conj -?ST0' ?ST2' ?conj_com -?ST0' ?invI ?ST1 ?mul_inv ?inv_mul -?mul_assoc
 ?cmul_l // (ST1 ki) (ST1 ij) (ST1 jk) /conj -?ST0' ?invI.
remember ([ ~ X ji (b * c), X ij a]) as W1. rewrite comm_d1 -?ST0' Zdef in HeqW1.
remember ([ ~ X kj (c * a), X jk b]) as W2. rewrite comm_d2 -?ST0' Zdef' in HeqW2.
remember ([ ~ X ik (a * b), X ki c]) as W3. rewrite comm_d2 -?ST0' Zdef in HeqW3.
rewrite ?ST0'. cancellate. rewrite -?GA -?ST0' HeqW1 HeqW2 HeqW3.
remember (Z ij _ _) as Z1. remember (Z ik _ _) as Z2. remember (Z (swap_neq jk) _ _) as Z3.
by rewrite -?GA /RHS ?HeqZ1 ?HeqZ2 ?HeqZ3. Qed.

Corollary A0 i j k (a b c : R): forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in Id = Id.
intros. rewrite {1}(R10' i j k a b c ij ik jk) -inv_mul
(R10 i j k a (-b) c ij ik jk) -?inv_mul ?mul_inv ?invI -mul_assoc -?GA ?swapI -/ji -/ki -/kj.
rewrite ?ST0' ?GII ?GA. cancel. rewrite -?GA. rewrite (GA _ (X kj (c * a * b * c * a))) -ST0.
