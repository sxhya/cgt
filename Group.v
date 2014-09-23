Require Import ssreflect ssrnat ssrbool seq eqtype.

Module Type GroupCarrier.

Parameter ZZ : Type.

End GroupCarrier.

Module GroupFacts (carrier : GroupCarrier).
Import carrier.

(* Group Structure *)
Variable (group_mul : ZZ -> ZZ -> ZZ) (groupinv : ZZ -> ZZ) (Id : ZZ).

Notation "x .* y " := (group_mul x y) (at level 50, left associativity).
Notation "x ^-1" := (groupinv x) (at level 40).

(* Group axioms *)
Axiom GA : forall g1 g2 g3, g1 .* g2 .* g3 = g1 .* (g2 .* g3).
Axiom GId: forall g, g .* Id = g.
Axiom IdG: forall g, Id .* g = g.
Axiom GI : forall g, g .* (g ^-1) = Id.
Axiom IG: forall g, (g ^-1) .* g = Id.

(* Basic lemmata *)

Corollary GI' g A: g .* ((g ^-1) .* A) = A. by rewrite -GA GI IdG. Qed.

Corollary IG' g A: (g^-1) .* (g .* A) = A. by rewrite -GA IG IdG. Qed.

Corollary GI'l g A: A .* g .* (g ^-1) = A. by rewrite GA GI GId. Qed.

Corollary IG'l g A: A .* (g^-1) .* g = A. by rewrite GA IG GId. Qed.

Lemma GCr: forall g3 g1 g2, g1 .* g3 = g2 .* g3 -> g1 = g2.
intros. have: (g1 .* g3 .* g3 ^-1 = g2 .* g3 .* g3 ^-1) by rewrite H.
by rewrite ?GA ?GI ?GId. Qed.

Lemma GCl g3 g1 g2: g3 .* g1 = g3 .* g2 -> g1 = g2.
intros. have: (g3^-1 .* g3 .* g1 = g3 ^-1 .* g3 .* g2) by rewrite ?GA H.
by rewrite ?IG ?IdG. Qed.

Lemma GIM: forall g1 g2, (g1 .* g2) ^-1 = g2 ^-1 .* g1 ^-1.
intros. apply (GCr (g1 .* g2)). by rewrite IG GA -(GA (g1 ^-1)) IG IdG IG. Qed.

Lemma GII: forall g, g ^-1 ^-1 = g.
intros. apply (GCr (g^-1)). by rewrite IG GI. Qed.

Corollary GCl' g3 g1 g2: g1 = g2 -> g3 .* g1 = g3 .* g2.
by move => ->. Qed.

Corollary GCr' g3 g1 g2: g1 = g2 -> g1 .* g3 = g2 .* g3.
by move => ->. Qed.

Lemma IdI: Id ^-1 = Id. apply (GCr Id). by rewrite IG IdG. Qed.

Lemma eqIdP a b: a .* b = Id <-> a = b^-1.
split; intros; [apply (GCr b); by rewrite IG| apply (GCr (b^-1)); by rewrite GA IdG GI GId]. Qed.

Lemma eqIdP' a b: a .* (b^-1) = Id -> a = b.
move /(GCr' b). by rewrite GA IG GId IdG. Qed.

Lemma eqIdP'' a b: a = b -> a .* (b^-1) = Id.
move /(GCr' (b^-1)). by rewrite GI. Qed.

Lemma rotate a b: a .* b = Id -> b .* a = Id.
intros. apply eqIdP in H. by rewrite H GI. Qed.

(* Conjugate elements *)

Definition conj (h g : ZZ) := (g ^-1) .* h .* g.
Notation "h ^ g" := (conj h g).

Lemma conj_mul h g1 g2: h ^ (g1 .* g2) = (h ^ g1) ^ g2.
by rewrite /conj ?GIM ?GA. Qed.

Lemma mul_conj g h1 h2: (h1 .* h2) ^ g = h1 ^ g .* h2 ^ g.
by rewrite /conj ?GA -(GA g) GI IdG. Qed.

Lemma conjId g: g ^ Id = g.
by rewrite /conj IdI IdG GId. Qed.

(* Commutators *)

Definition Comm (x y : ZZ) : ZZ := (x .* y .* x^-1 .* y^-1).
Notation "[ ~ x1 , x2 , .. , xn ]" :=
  (Comm .. (Comm x1 x2) .. xn) (at level 29, left associativity).

Ltac expand := rewrite /Comm /conj ?GIM ?GII.
Ltac cancel := rewrite ?GI' ?GI'l ?IG' ?IG'l ?GI ?IG ?IdG ?GId.
Ltac cancellate := expand; rewrite ?GA; cancel; rewrite -?GA.
Ltac rotate := rewrite ?GA; apply rotate; rewrite ?GA.
Ltac conjugate_r M := rewrite -?GA; move /(GCl' (M ^-1)) /(GCr' M); cancellate.
Ltac conjugate_l M := rewrite -?GA; move /(GCl' M) /(GCr' (M^-1)); cancellate.

Lemma Gswap a b: a .* b = b .* a ^ b. by cancellate. Qed.

Lemma Gswap' a b g: g .* a .* b = g .* b .* a ^ b. by cancellate. Qed.

Lemma comm_inv: forall x y, [~ x, y] ^-1 = [~y, x].
intros. by rewrite /Comm ?GIM ?GII -?GA. Qed.

Lemma swap_comm a b: a .* b = [~ a, b] .* b .* a. by expand; cancel. Qed.

Lemma conj_com: forall a b, a ^ b = [~ b ^-1, a] .* a. 
intros. rewrite /conj. apply (GCr Id). by rewrite -{1}(IG a) -GA /Comm GII GId. Qed. 

Lemma comm3 x y z: [~z, x, y]^ z = [~x, z^-1, y^z]. by cancellate. Qed.

Lemma cmul_l x y z: [~ x .* y, z] = [~y, z] ^ (x^-1) .* [~x, z]. by cancellate. Qed.

Lemma cmul_r x y z: [~ x, y .* z] = [~x, y] .* [~x, z] ^ (y^-1). by cancellate. Qed.

Lemma comm_conj x y z: [~ x, y] ^ z = [~x ^ z, y ^ z]. by cancellate. Qed.

Lemma conj_comm' x y z : [ ~ y, z] ^ x = [ ~ x ^-1 .* y, z] .* [ ~ z, x ^-1]. by cancellate; cancel. Qed.

Lemma comm_d1 x y: [~ x, y] = y ^ (x^-1) .* y^-1. by expand. Qed.

Lemma comm_d2 x y: [~ x, y] = x .* (x^-1) ^ (y^-1). by cancellate. Qed.

Lemma comm_d1' x y g: g .* [ ~ x, y] = g .* y ^ (x ^-1) .* y ^-1. by cancellate. Qed.

Lemma comm_d2' x y g: g .* [~ x, y] = g .* x .* (x^-1) ^ (y^-1). by cancellate. Qed.

(* Variations of Hall-Witt identity*)

Lemma HallWitt x y z: 
 [~ y^-1, x, z] ^ (y^-1) .* [~ z^-1, y, x] ^ (z^-1) .* [~ x^-1, z, y] ^ (x^-1) = Id. 
 by expand; rewrite ?GA; do 4 cancel. Qed.

Corollary HallWitt' x y z: [~ y, x^-1, z^-1]^ y .* [~z, y^-1, x^-1]^ z .* [~x, z^-1, y^-1] ^ x = Id.
move: (HallWitt (x^-1) (y^-1) (z^-1)). by rewrite ?GII. Qed.

Corollary HallWitt'' x y z:
 [~ x^-1, y^-1, (z^-1)^y] .* [~ y^-1, z^-1, (x^-1)^z] .* [~ z^-1, x^-1, (y^-1)^x] = Id. 
by rewrite -?comm3 HallWitt'. Qed.

End GroupFacts.