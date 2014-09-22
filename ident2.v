Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident.

Import Ring.RingFacts.
Import SteinbergGroup.
Import GF.
Open Scope ring_scope.

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

Lemma Z'zero i j a (ij : i != j): Z' ij 0 a = Id.
apply (GCr (Z' ij 0 a)). by rewrite IdG -Z0 plus_0_r. Qed.

Corollary X'zero i j (ij : i != j): X' ij 0 = Id. by rewrite /X' Z'zero. Qed.

Lemma Z'Inv i j a b (ij : i != j): Z' ij (-a) b = (Z' ij a b)^-1.
apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l IG Z'zero. Qed.

Corollary X'Inv i j a (ij : i != j): X' ij (-a) = (X' ij a)^-1. by rewrite /X' Z'Inv. Qed.

Section XCorollaries.
Context (i j k l : nat) {a b c d : R} {ij : i != j} {ik : i != k} {jk : j != k}
                                      {kl : k != l} {il : i != l} {jl : j != l}.

Context (ji : j != i) (ki : k != i) (kj : k != j)
        (lk : l != k) (li : l != i) (lj : j != l).

Ltac ZX E := rewrite /X'; rewrite E; rewrite /X'; rsimpl; rewrite ?Z'zero; cancel.

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
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4; rsimpl; rewrite /X' ?Z'zero; cancel. Qed.

Corollary XC4'_swap: (X' ij a) .* (X' ik c) = (X' ik c) .* (X' ij a).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4'; rsimpl; rewrite /X' ?Z'zero; cancel. Qed.

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