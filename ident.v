Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.

Module SteinbergGroup <: GroupCarrier.
Variable ZZ : Type.
End SteinbergGroup.

Module Import GF := Group.GroupFacts SteinbergGroup.
Module Import RF := Ring.RingFacts.
Import SteinbergGroup.

(* Reflection principle for (in)equality *)

CoInductive eqneq (m n : nat) : bool -> bool -> Set :=
 | Equal     of m == n : eqneq m n true false
 | Different of m != n : eqneq m n false true.

Lemma eqneqP m n: eqneq m n (m == n) (m != n).
  by case A0: eq_op; rewrite /negb; constructor; rewrite A0. Qed.

(*************************************************)

Definition swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym.  Defined.

Axiom X: forall {i j : nat}, (i != j) -> R -> ZZ.

Axiom ST0: forall {i j : nat} (ij : (i != j)) r s, X ij (r + s) = X ij r .* X ij s.

Lemma Xzero: forall {i j : nat} (ij : (i != j)), X ij 0 = Id.
intros. apply (GCr (X ij 0)). by rewrite -{3}(plus_0_l 0) ST0 IdG. Qed.

Lemma ST0': forall {i j : nat} (ij : (i != j)) r, X ij (- r) = (X ij r) ^-1.
intros. apply (GCr (X ij r)). by rewrite -ST0 IG (inv_l) Xzero. Qed.

Lemma ST0'' {i j} a b (ij : i != j): X ij a ^ X ij b = X ij a.
expand. by rewrite -ST0' -?ST0 plus_comm -plus_assoc inv_r plus_0_l. Qed.

Axiom ST1: forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X ij r , X jk s ] = X ik (r * s).

Lemma ST1': forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X jk r , X ij s ] = X ik (- s * r).
intros. by rewrite -comm_inv ST1 -ST0' inv_mul. Qed.

Lemma ST1'' {i j k} a b (ik : i != k) (kj : k!= j) (ij : i!=j): 
 X ik a ^ X kj b = X ij (a * b) .* X ik a.
by rewrite conj_com -ST0' ST1' mul_inv inv_mul invI. Qed.

Lemma ST1''2 {i j k} a b {ij : i != j} {ki : k != i} (kj : k != j):
X ij a ^ X ki b = X kj (- (b * a)) .* X ij a.
by rewrite conj_com -ST0' ST1 inv_mul. Qed.

Axiom ST2: forall {i j k l : nat} (ij : (i != j)) (kl : (k != l)) r s, j != k -> i != l ->
 [~ X ij r, X kl s ] = Id.

Lemma ST2': forall {i j k} {ik : i != k} {jk : j != k} (ij : i != j) a b, X ik a ^ X jk b = X ik a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq ik). exact jk. Qed.

Corollary ST2'_swap: forall {i j k} {ik : i != k} {jk : j != k} (ij : i != j) a b, X ik a .* X jk b = X jk b .* X ik a.
intros. rewrite -{2}(ST2' ij a b). by cancellate. Qed.

Lemma ST2'': forall {i j k} {ki : k != i} {kj : k != j} (ij : i != j) a b, X ki a ^ X kj b = X ki a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq kj). exact ki. Qed.

Corollary ST2''_swap: forall {i j k} {ki : k != i} {kj : k != j} (ij : i != j) a b, X ki a .* X kj b = X kj b .* X ki a.
intros. rewrite -{2}(ST2'' ij a b). by cancellate. Qed.

Lemma ST2''' {i j k l : nat} (ij : i != j) (kl : k != l) (jk : j != k) (il : i != l) r s:
 X ij r ^ X kl s = X ij r. rewrite conj_com -ST0' ST2. by rewrite IdG. by exact (swap_neq il). by exact (swap_neq jk). Qed.

(* These 2 axioms are needed to get rid of proof-relevant nature of parameter "p" of Z *) 

Axiom swapI : forall {i j : nat} (p : i != j), swap_neq (swap_neq p) = p.

Axiom irrelev : forall {i j : nat} (p q : i != j), p = q.

(* Tits relative generators z_{ij}(a, r) *)

Definition Z {i j : nat} (p : i != j) (r s : R) : ZZ := locked ((X p r) ^ (X (swap_neq p) s)).

Lemma Zdef {i j} (p : i!= j) r s: (X (p) r) ^ (X (swap_neq p) s) = Z p r s. by unlock Z. Qed.

Lemma Zdef'{i j} (p : i!= j) r s: (X (swap_neq p) r) ^ (X p s) = Z (swap_neq p) r s.
by unlock Z; rewrite swapI. Qed.

Lemma Zadd {i j} (ij : i != j) (r s t : R): Z ij (r+s) t = Z ij r t .* Z ij s t.
unlock Z. by rewrite -mul_conj ST0. Qed. 

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
 (mul_conj (X jk (- b))) {3}/conj -ST0' invI -2!ST0 (plus_comm b) plus_assoc inv_r plus_0_r
 (ST2' ij) (mul_conj (X ki c)) Zdef (conj_com _ (X ki c)) -ST0' ST1' invI mul_inv
 (conj_com (X ij a)) -ST0' invI ST1' -?GA ?mul_conj {1}/Z -lock
 -conj_mul -/ki -ST0 inv_r Xzero conjId Zdef (ST2' jk)
 (conj_com _ (X ki (- c))) -ST0' invI ST1' invI ST0' -GA IG IdG
 {1}/Z -lock -conj_mul swapI (swap_comm (X jk (-b))) ST1 inv_mul mul_inv invI 
 (GA (X ji (b * c))) conj_mul (conj_com (X kj (- (c * a)))) -ST0' ST1' invI mul_inv mul_conj
 {1}(swap_comm (X ki (-c))) ST1' inv_mul mul_inv invI (conj_com (X ij a)) -ST0' invI ST1
 (GA (X ji (- b * c))) conj_mul (ST2' kj)
 2!conj_mul (ST2'' ji) Zdef' (conj_com (X ki (- (c * a * (b * c))))) -ST0' invI ST1 mul_inv
 mul_conj (ST2' jk) /conj -ST0' invI -?ST0 plus_comm -plus_assoc inv_l plus_0_l //. Qed.

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
rewrite ?ST0' ?GA ?Zinv. by do 2 cancel. Qed.

Corollary R12 i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ik a b =
  X kj (- (b * a)) .* X ij a .* Z ij (- a) (- (b)) .* X jk (b * a)
  .* X ik (a) .* X ji (- (b * a * b)) .* X ki (- (b * a * b))
  .* Z kj (b * a) (-(1)).
intros. move: (R1''' i j k a 1 b ij ik jk) => /=.
by rewrite ?mul_1_r ?mul_1_l -/ji -/ki -/kj. Qed.

Section S1.
Context (i j k l : nat) (a b c d : R) (ij : i != j) (ik : i != k) (jk : j != k)
                                      (kl : k != l) (il : i != l) (jl : j != l).
Let ji := (swap_neq ij). Let ki := (swap_neq ik). Let kj := (swap_neq jk).
Let lk := (swap_neq kl). Let li := (swap_neq il). Let lj := (swap_neq jl).

(* Shorter and slicker relation taken from Petrov's Russian thesis (Lemma 7)*)

Lemma C1': (Z ij a b) ^ (X ij c) = 
X ik ((c * b + 1) * a) .* X jk (- (b * a))
.* X ki (- ((b * c + 1) * b * a * b))       .* X ji (- (b * a * b))                 .* Z jk (b * a) (- (b * c + 1)) 
.* X kj (b * (c * b + 1) * a * (b * c + 1)) .* X ij ((c * b + 1) * a * (b * c + 1)) .* Z ik (- ((c * b + 1) * a)) (- b).

rewrite /Z -lock -conj_mul -/ji.
move: (ST1 ik ij kj a 1). rsimpl. move => <-.
rewrite conj_mul comm_conj ST1'' ST1''2
        comm_conj ?mul_conj ST2'' // ST2' // ST1'' ST1''2; rsimpl.
by rewrite ST2''_swap // ?GA -ST0 ST2'_swap // -GA -ST0 -{2}(mul_1_l a) -dist_r
           comm_d2 ?GIM -?ST0' invI mul_conj {1}ST2''_swap //
           ?conj_mul 2!ST1'' ?mul_conj ST1''2 ?Zdef ST1''2
           ?inv_mul ?mul_inv ?invI -?GA -?lock -?mul_assoc. Qed.

Lemma C2: (Z ij a b) ^ (X ji c) = (Z ij a (b + c)). by rewrite /Z -?lock -/ji -conj_mul ST0. Qed.

Lemma C3: (Z ij a b) ^ (X jk c) = X jk (- (b * a * c)) .* X ik (a * c) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 // 
           IdG conj_mul ST1'' mul_conj ST1''2 Zdef; rsimpl. Qed.

Lemma C3': (Z ij a b) ^ (X ki c) = X ki (- (c * a * b)) .* X kj (- (c * a)) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 //; cancel;
rewrite conj_mul ST1''2  mul_conj ST1'' Zdef; rsimpl. Qed.

Lemma C4: (Z ij a b) ^ (X kj c) = X ki (c * b * a * b) .* X kj (c * b * a) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST1' GA 
        conj_mul ST1''2 ?mul_conj ?conj_mul ST0'' ST1'' ST2' // Zdef; rsimpl. Qed.

Lemma C4': (Z ij a b) ^ (X ik c) = X jk (- (b * a * b * c)) .* X ik (a * b * c) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST1 GA
        conj_mul ST1'' ?mul_conj ?conj_mul ST0'' ST1''2 ST2'' // Zdef; rsimpl. Qed.

Lemma C5: (Z ij a b) ^ (X kl c) = Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 // IdG 
           conj_mul (conj_com (X ij a)) -ST0' ST2// IdG Zdef. Qed.

End S1.

(* Lemmata about conjugation with Weyl elements *)

Definition W {i j} (ij : i != j) := let ji := (swap_neq ij) in X ij (1) .* X ji (-(1)) .* X ij (1).

Lemma Wconj1 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ki a) ^ W ij = X kj a.
intros. rewrite /W -/ji 2!conj_mul ST1'' mul_conj ST1'' ST2' // ?mul_conj ?ST1'' ST2' // (ST2''_swap) //.
rsimpl. rewrite ?ST0'. cancel. rewrite (ST2''_swap) //. cancel. done. Qed. 

Lemma Wconj1' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X jk a) ^ W ij = X ik (-a).
intros. rewrite /W -/ji 2!conj_mul ST1''2 mul_conj ST1''2 ST2'' // ?mul_conj ?ST1''2 ST2'' // ST2'_swap //.
rsimpl. rewrite ?ST0'. cancel. rewrite -?ST0' (ST2'_swap) // ?ST0'. cancel. done. Qed.

Lemma Wconj2 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ik a) ^ W ij = X jk a.
intros. rewrite /W -/ji 2!conj_mul ST2'' // ST1''2 mul_conj ST2'' // ST1''2.
rsimpl. rewrite (ST2'_swap) // ST0'. cancel. done. Qed.

Lemma Wconj2' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X kj a) ^ W ij = X ki (-a).
intros. rewrite /W -/ji 2!conj_mul ST2' // ST1'' mul_conj ST2' // ST1''.
rsimpl. rewrite (ST2''_swap) // ?ST0'. cancel. done. Qed.

Lemma Wconj3 i j k l (ij : i != j) (ik : i != k) (jk : j != k) (il : i != l) (kl : k != l) (jl : j!=l) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 let li := swap_neq il in let lk := swap_neq kl in let lj := swap_neq jl in
 (X kl a) ^ W ij = X kl a.
intros. rewrite /W -/ji ?conj_mul. by do 3 rewrite ST2''' //. Qed.

Lemma Wconj4 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ji a) ^ W ij = X ij (-a).
intros. rewrite -{1}(mul_1_r a) -(ST1 jk ji ki) comm_conj Wconj1 Wconj1' -/kj ST1. by rsimpl. Qed.

Lemma Wconj4' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ij a) ^ W ij = X ji (-a).
intros. rewrite -{1}(mul_1_r a) -(ST1 ik ij kj) comm_conj Wconj2 Wconj2' -/ki ST1. by rsimpl. Qed.

(* =========================================================== *)
(*  Another Presentation for Relative Steinberg Group          *)
(* =========================================================== *)

Section RelSteinberg.

Axiom Z': forall {i j : nat} (p : i != j) (r s : R), ZZ. (* Formal Generator *)

Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

Axiom Z2: forall i j k l (ij : i!=j) (kl : k!=l) a b c, Z' ij a b ^ Z' kl c 0 = Z' ij a b ^ X kl c.

Context (i j k l : nat) {a b c d : R} {ij : i != j} {ik : i != k} {jk : j != k}
                                      {kl : k != l} {il : i != l} {jl : j != l}.

Context (ji : j != i) (ki : k != i) (kj : k != j)
        (lk : l != k) (li : l != i) (lj : j != l).

Axiom Z0: Z' ij (a + b) c = Z' ij a c .* Z' ij b c.
Axiom Z0': (Z' ij a b) ^ (X' ji c) = Z' ij a (b + c).

(* TODO: Use this relation to define morphism of Steinberg groups *)

Axiom Z1: Z' ik (a * b) c =
  X' kj (- (c * a)) .* X' ij a .* Z' ij (- a) (- (b * c)) .* X' jk (b * c * a * b)
  .* X' ik (a * b) .* X' ji (- (b * c * a * b * c)) .* X' ki (- (c * a * b * c))
  .* Z' kj (c * a) (- b). 

Axiom Z1': Z' ij a (b * c) = 
   X' jk (- (b * c * a * b)) .* X' ik (a * b) .* (X' ji (- (b * c * a * b * c))
.* X' ki (- (c * a * b * c)) .* Z' kj (- (c * a)) (- b)) .* Z' ik (- (a * b)) (- c) 
.* X' kj (c * a) .* X' ij a.

Axiom ZC1: (Z' ij a b) ^ (X ij c) = 
X' ik ((c * b + 1) * a) .* X' jk (- (b * a))
.* X' ki (- ((b * c + 1) * b * a * b)) .* X' ji (- (b * a * b)) .* Z' jk (b * a) (- (b * c + 1)) 
.* X' kj (b * (c * b + 1) * a * (b * c + 1)) .* X' ij ((c * b + 1) * a * (b * c + 1)) .* Z' ik (- ((c * b + 1) * a)) (- b).

Axiom ZC2: (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom ZC3: (Z' ij a b) ^ (X jk c) = X' jk (- (b * a * c)) .* X' ik (a * c) .* Z' ij a b.

Axiom ZC3': (Z' ij a b) ^ (X ki c) = X' ki (- (c * a * b)) .* X' kj (- (c * a)) .* Z' ij a b.

Axiom ZC4: (Z' ij a b) ^ (X kj c) = X' ki (c * b * a * b) .* X' kj (c * b * a) .* Z' ij a b.

Axiom ZC4': (Z' ij a b) ^ (X ik c) = X' jk (- (b * a * b * c)) .* X' ik (a * b * c) .* Z' ij a b.

Axiom ZC5: (Z' ij a b) ^ (X kl c) = Z' ij a b.

End RelSteinberg.

Lemma Zzero i j a (ij : i != j): Z' ij 0 a = Id.
apply (GCr (Z' ij 0 a)). by rewrite IdG -Z0 plus_0_r. Qed.

Corollary X'zero i j (ij : i != j): X' ij 0 = Id. by rewrite /X' Zzero. Qed.

Lemma Z'Inv i j a b (ij : i != j): Z' ij (-a) b = (Z' ij a b)^-1.
apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l IG Zzero. Qed.

Corollary X'Inv i j a (ij : i != j): X' ij (-a) = (X' ij a)^-1. by rewrite /X' Z'Inv. Qed.

Section XCorollaries.
Context (i j k l : nat) {a b c d : R} {ij : i != j} {ik : i != k} {jk : j != k}
                                      {kl : k != l} {il : i != l} {jl : j != l}.

Context (ji : j != i) (ki : k != i) (kj : k != j)
        (lk : l != k) (li : l != i) (lj : j != l).

Ltac ZX E := rewrite /X'; rewrite E; rewrite /X'; rsimpl; rewrite ?Zzero; cancel.

Lemma X0: X' ij (a + b) = X' ij a .* X' ij b. by ZX Z0. Qed.

Corollary X0': forall (g : ZZ), g .* X' ij a .* X' ij b = g .* X' ij (a+b).
intros. by rewrite GA -X0. Qed.

Corollary XC1 : (X' ij a) ^ (X ij c) = X' ik (a) .* X' ij (a) .* X' ik (-a). by ZX (@ZC1 i j k a (0) c). Qed.
Corollary XC2 : (X' ij a) ^ (X ji c) = Z' ij a c. by ZX ZC2. Qed.
Corollary XC3 : (X' ij a) ^ (X jk c) = X' ik (a * c) .* X' ij a. by ZX ZC3. Qed.
Corollary XC3': (X' ij a) ^ (X ki c) = X' kj (- (c * a)) .* X' ij a. by ZX ZC3'. Qed.
Corollary XC4 : (X' ij a) ^ (X kj c) = X' ij a. by ZX ZC4. Qed.
Corollary XC4': (X' ij a) ^ (X ik c) = X' ij a. by ZX ZC4'. Qed.
Corollary XC5 : (X' ij a) ^ (X kl c) = X' ij a. by ZX ZC5. Qed.

Corollary XC4_swap: (X' ij a) .* (X' kj c) = (X' kj c) .* (X' ij a).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4; rsimpl; rewrite /X' ?Zzero; cancel. Qed.

Corollary XC4'_swap: (X' ij a) .* (X' ik c) = (X' ik c) .* (X' ij a).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4'; rsimpl; rewrite /X' ?Zzero; cancel. Qed.

Corollary XC4_swap': forall (g : ZZ), g .* (X' ij a) .* (X' kj c) = g .* (X' kj c) .* (X' ij a).
intros. by rewrite GA XC4_swap ?GA. Qed.

Corollary XC4'_swap': forall (g : ZZ), g .* (X' ij a) .* (X' ik c) = g .* (X' ik c) .* (X' ij a).
intros. by rewrite GA XC4'_swap ?GA. Qed.

End XCorollaries.

Corollary ZC3_swap{i j k} {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} a b c:
 (Z' ij a b) .* (X' jk c) = (X' jk ((1 + -(b * a)) * c)) .* X' ik (a * c) .* Z' ij a b.
apply (GCl ((X' jk c)^-1)). rewrite -?GA. replace (X' jk c ^-1 .* Z' ij a b .* X' jk c) with (Z' ij a b ^ X' jk c); try by expand.
by rewrite {1}/X' Z2 ZC3 dist_r mul_1_l X0; cancellate; rsimpl. Qed.

Corollary Z11' {i j k} {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} a b:
Z' ij a b =  X' jk (- (b * a * b)) .* X' ik (a * b) .* (X' ji (- (b * a * b))
.* X' ki (- (a * b)) .* Z' kj (- (a)) (- b)) .* Z' ik (- (a * b)) (- (1)) 
.* X' kj (a) .* X' ij a.
by rewrite -{1}(mul_1_r b) (Z1' i j k ji ki kj); rsimpl. Qed.

Corollary Z12' {i j} k {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} a b:
 Z' ij a b = X' jk (- (b * a)) .* X' ik a .* Z' ik (- a) (- b) .* X' kj (b * a)
  .* X' ij (a) .* X' ki (- (b * a * b)) .* X' ji (- (b * a * b)) .* Z' jk (b * a) (- (1)).
by rewrite -{1}(mul_1_r a) (Z1 i k j ki ji jk); rsimpl. Qed.

(* Key identity to be proved *)
Lemma Q1 a b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
X' ik a .* X' jk (- (b * a)) .* X' kj ((b * c + 1) * b * a * b * c)
.* X' ki (- ((b * c + 1) * b * a * b)) .* Z' ji (- (b * a * b)) (- c)
.* X' ij (- (c * b * a * (b * c + 1))) .* X' ik (c * b * a)
.* Z' jk (b * a) (- (b * c + 1)) .* X' kj (b * (c * b + 1) * a)
.* X' ij ((c * b + 1) * a) .* Z' ik (- ((c * b + 1) * a)) (- b) = Z' ij a b. 
Admitted.

Corollary ActionCorr1 a b c i j k 
(ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 Z' ij a b ^ (X ij c .* X ij (-(c))) = Z' ij a b.
intros. rewrite ?conj_mul (@ZC1 i j k a b c) -/ji -/kj -/ki -?GA
?mul_conj XC3'// XC2 ZC3' ZC4' XC3 XC4// (XC1 i j k)// XC4'// -?GA.
rsimpl. rewrite (XC4'_swap' i k j) // -X0 ?X0' inv_r X'zero GId.
rewrite (XC4_swap' i j k) // ?X0' (plus_comm (c*b)) dist_r plus_assoc inv_r mul_1_l plus_0_r.
rewrite (plus_comm _ 1) ?(dist_l _ (1)) ?mul_1_r ?plus_assoc ?mul_assoc ?inv_r.
rewrite ?plus_0_r ?mul_assoc -{6}(mul_1_r a) -{16}(mul_1_r b) -?dist_l -{10 12}(mul_1_l a) -?mul_assoc -?dist_r ?(plus_comm (1)).
apply Q1. Qed.

Corollary AdditivityCheck1 a b c d i j k 
(ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 Z' ij a b ^ (X ij c .* X ij d .* X ij (-(c+d))) = Z' ij a b.
intros. rewrite ?conj_mul (@ZC1 i j k a b c) -/ji -/kj -/ki -?GA
        ?(mul_conj (X ij d)) XC4' // XC3' XC2 ZC3'
        ZC4' XC3 XC4 // (XC1 i j k) // ?mul_conj
        ?(XC4' i k j) // ?(XC3' j k i) ?(XC4 k j i) //
        ZC2 ZC4' ZC3' ?(XC3 k i j) ?(XC1 i j k) //; rsimpl.
rewrite -?GA -?X0 ?X0'.
rewrite ?X0' (@XC4_swap' k j i) // ?(XC4'_swap' i j k) // ?X0'.
rewrite (XC4'_swap' i k j) // (XC4_swap' i j k) // ?X0'.

replace ((c * b + 1) * a + d * b * a + - ((c + d) * b * a)) with a;
 [|by rewrite ?dist_l ?dist_r ?mul_1_l (plus_comm (c*b*a)) 2!(plus_assoc a) inv_r plus_0_r].
replace (- ((b * c + 1) * b * a * b * d) + (b * c + 1) * b * a * b * (c + d)) with ((b*c+1)*b*a*b*c);
 [|by rewrite (plus_comm c) (dist_l _ d) -plus_assoc inv_l plus_0_l].
replace (d + - (c + d)) with (- c);
 [|by rewrite (plus_comm c) inv_plus -plus_assoc inv_r plus_0_l].
replace (d * b * a * (b * c + 1) + - ((c + d) * b * a * (b * c + 1)))
   with (-(c * b * a * (b * c + 1)));
[|by rewrite (plus_comm c) ?dist_r inv_plus -plus_assoc inv_r plus_0_l].
rewrite inv_r X'zero GId.
replace ((c * b + 1) * a * (b * c + 1) + (c * b + 1) * a * (b * c + 1) +
      (- ((c * b + 1) * a * (b * c + 1)) + - ((c * b + 1) * a * (b * c + 1))))
with 0; [| by rewrite -inv_plus inv_r].
rewrite X'zero GId.
replace ((c * b + 1) * a * (b * c + 1) +
      ((c * b + 1) * a * b * d + - ((c * b + 1) * a * b * (c + d))))
with ((c * b + 1) * a);
[| by rewrite -mul_inv (plus_comm (b * c)) dist_l mul_1_r
        plus_assoc -?mul_assoc -dist_l (plus_comm c) inv_plus -(plus_assoc d) inv_r
        plus_0_l -dist_l inv_r mul_0_r plus_0_r].
rewrite X0' ?mul_assoc -?dist_l (plus_comm (b*c) (1)) (plus_assoc (1)) -dist_l.
rewrite (XC4_swap' i j k) // -?GA X0' -?mul_inv -?dist_l ?mul_inv (plus_assoc 1) inv_r plus_0_r.
rewrite -?mul_inv -plus_assoc -?dist_l ?mul_inv -plus_assoc inv_r plus_0_l.
rewrite (plus_comm c) (dist_r (b*a)) ?mul_inv -plus_assoc inv_l plus_0_l.
rsimpl. move: (@Q1 a b c i j k ij ik jk) => /=. rewrite -/ji -/kj -/ki. rewrite ?(plus_comm (1)) ?GA => <-.
do 5 apply GCl'. rewrite -?GA. do 4 apply GCr'. by rewrite XC4'_swap. Qed.