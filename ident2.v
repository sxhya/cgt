Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident.
Import Ring.RingFacts SteinbergGroup GF.

Section RelSteinbergAxioms.

Parameter Z': forall {i j : nat} (p : i != j), I -> R -> ZZ.
Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

Context (i j k l : nat) {a a1 a2 : I} (b c : R).

(* Definition of the action of the Steinberg group on relative generators *)

Axiom ZC1: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), 
let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
Z' ij a b ^ X ij c =
X' ji (- b *_ a _* b) ^ X ik (- c * b - 1) .* Z' ki (a _* b) (- c * b - 1)
.* X' ij ((c * b + 1) *_ a _* (b * c + 1)) ^ X jk b .* Z' kj (a _* (b * c + 1)) b
.* X' kj (-_ a) .* X' ki (-_ a _* b) ^ X ij c.

Axiom ZC2: forall (ij : i!=j), let ji := swap_neq ij in (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom ZC3: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
(Z' ij a b) ^ (X jk c) = X' jk (-_ (b *_ a _* c)) .* X' ik (a _* c) .* Z' ij a b.

Axiom ZC3': forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
 (Z' ij a b) ^ (X ki c) = X' ki (-_ (c *_ a _* b)) .* X' kj (-_(c *_ a)) .* Z' ij a b.

Axiom ZC4: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
 (Z' ij a b) ^ (X kj c) = X' ki (c * b *_ a _* b) .* X' kj (c * b *_ a) .* Z' ij a b.

Axiom ZC4': forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
 (Z' ij a b) ^ (X ik c) = X' jk (-_ (b *_ a _* b _* c)) .* X' ik (a _* b _* c) .* Z' ij a b.

Axiom ZC5: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (il : i!=l) (jl : j!=l) (kl : k!=l),
 let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
 let li := swap_neq il in let lj := swap_neq jl in let lk := swap_neq kl in 
 (Z' ij a b) ^ (X kl c) = Z' ij a b.

(* Definition of Relations between relative generators *)

Axiom Z0: forall (ij : i!=j), Z' ij (a1 _+_ a2) c = Z' ij a1 c .* Z' ij a2 c.

Axiom Z1: forall (ij : i!=j), let ji := (swap_neq ij) in (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom Z2: forall (ij : i!=j) (kl : k!=l), Z' ij a b ^ X' kl a1 = Z' ij a b ^ X kl a1.

(* Fix these 2 statements*)

Axiom Z3: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
Z' ij (a _* b) c =  X' jk (-_ (c *_ a)) .* X' ik a .* X' ij (a _* b) ^ X ki (- (b * c))
.* Z' ik (-_ a) (- (b * c)) .* X' ji (-_ (c *_ a _* b _* c)) ^ X kj (- b)
.* Z' jk (c *_ a) (- b).

(* Axiom Z3': forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
 Z ij (a * b) c =  Z jk (- (c * a)) b .* X ij (a * b) .* X ik a .* Z ik (- a) (- (b * c))
.* X ji (- (c * a * b * c)) .* X jk (c * a) .* X ki (- (b * c * a * b * c)) .* X kj (- (b * c * a * b)). *)

End RelSteinbergAxioms.

Lemma Z'zero i j a (ij : i != j): Z' ij 0 a = Id.
apply (GCr (Z' ij 0 a)). rewrite -Z0. by rewrite IdG; rsimpl. Qed.

Corollary X'def i j (ij : i != j) a: Z' ij a 0 = X' ij a. done. Qed.

Corollary X'zero i j (ij : i != j): X' ij 0 = Id. by rewrite /X' Z'zero. Qed.

Lemma Z'Inv i j a b (ij : i != j): Z' ij (-_a) b = (Z' ij a b)^-1.
apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l' IG Z'zero. Qed.

Corollary X'Inv i j a (ij : i != j): X' ij (-_a) = (X' ij a)^-1. by rewrite /X' Z'Inv. Qed.

Section XCorollaries.

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.

Ltac ZX E := rewrite /X'; rewrite E; rewrite /X'; rsimpl; rewrite ?Z'zero; cancel.

Lemma X0: X' ij a1 .* X' ij a2 = X' ij (a1 _+_ a2). by ZX Z0. Qed.

Corollary X0': forall (g : ZZ), g .* X' ij a1 .* X' ij a2 = g .* X' ij (a1 _+_ a2).
intros. by rewrite GA -X0. Qed.

(* For XC1 see below *)
Corollary XC2 : (X' ij a) ^ (X ji c) = Z' ij a c.
by move: (@ZC2 i j a (0) c ij) => /=; rewrite (irrelev (swap_neq ij) ji) plus_0_l /X'. Qed.
Corollary XC3 : (X' ij a) ^ (X jk c) = X' ik (a _* c) .* X' ij a. by ZX ZC3. Qed.
Corollary XC3': (X' ij a) ^ (X ki c) = X' kj (-_ (c *_ a)) .* X' ij a.
 by rewrite -(swapI ki); ZX ZC3'; rewrite (irrelev (swap_neq jk) kj). Qed.
Corollary XC4 : (X' ij a) ^ (X kj c) = X' ij a. by rewrite -(swapI kj); ZX ZC4. Qed. 
Corollary XC4': (X' ij a) ^ (X ik c) = X' ij a. by ZX ZC4'. Qed.
Corollary XC5 : (X' ij a) ^ (X kl c) = X' ij a. by ZX ZC5. Qed.

Corollary XC4_swap: (X' ij a1) .* (X' kj a2) = (X' kj a2) .* (X' ij a1).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 -(swapI ij) ZC4; rsimpl; rewrite /X' ?Z'zero; cancel. Qed. 

Corollary XC4'_swap: (X' ij a1) .* (X' ik a2) = (X' ik a2) .* (X' ij a1).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4'; rsimpl; rewrite /X' ?Z'zero; cancel. Qed.

Corollary XC4_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' kj a2) = g .* (X' kj a2) .* (X' ij a1).
intros. by rewrite GA XC4_swap ?GA. Qed.

Corollary XC4'_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' ik a2) = g .* (X' ik a2) .* (X' ij a1).
intros. by rewrite GA XC4'_swap ?GA. Qed.

End XCorollaries.

Section MainSection.

Corollary XC1 (a : I) (c : R) {i j k} {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}:
 (X' ij a) ^ (X ij c) = X' ik (a) .* X' ij (a) .* X' ik (-_a).
rewrite (@ZC1 i j k a (0) c); rsimpl;
rewrite (irrelev (swap_neq jk) kj) ?Z'zero ?X'zero ?X'def Xzero conjId; cancel.
by rewrite GA X0 XC4'_swap// GA ?X0 ?inv_r' ?X'zero ?GId. Qed.

Corollary ZC3_swap{i j k} {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}
 (a c : I) (b : R):
 (Z' ij a b) .* (X' jk c) = (X' jk ((1 - b * a) *_ c)) .* X' ik (a _* c) .* Z' ij a b.
apply (GCl ((X' jk c)^-1)). rewrite -?GA. replace (X' jk c ^-1 .* Z' ij a b .* X' jk c) with (Z' ij a b ^ X' jk c); try by expand.
by rewrite {1}/X' Z2 ZC3 dist_r' mul_1_l' -X0; cancellate; rsimpl. Qed.

Corollary ZC4'_swap{i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} 
 (a c: I) (b : R):
 (Z' ij a b) .* (X' ik c) = X' ik (c _+_ a * b *_ c) .* X' jk (-_ (b * a * b *_ c)) .* Z' ij a b.
apply (GCl ((X' ik c)^-1)). rewrite -X0; cancellate. replace (X' ik c ^-1 .* Z' ij a b .* X' ik c) with (Z' ij a b ^ X' ik c); [|try by expand].
by rewrite Z2 ZC4' XC4_swap; rsimpl. Qed.

Corollary ZC3'_swap{i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}
(a c : I) (b : R):
 (Z' ij a b) .* (X' ki c) = (X' ki c) .* X' ki (-_ (c _* a _* b)) .* X' kj (-_ (c _* a)) .* Z' ij a b.
apply (GCl ((X' ki c)^-1)). cancellate. replace (X' ki c ^-1 .* Z' ij a b .* X' ki c) with (Z' ij a b ^ X' ki c); [|by expand].
by rewrite -(swapI ki) Z2 ZC3' ?swapI (irrelev (swap_neq jk) kj); rsimpl. Qed.

Corollary ZC4_swap{i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} 
(a c : I) (b : R):
 (Z' ij a b) .* (X' kj c) = (X' kj c) .* X' ki (c _* b _* a _* b) .* X' kj (c _* b _* a) .* Z' ij a b.
apply (GCl ((X' kj c)^-1)). cancellate. replace (X' kj c ^-1 .* Z' ij a b .* X' kj c) with (Z' ij a b ^ X' kj c); [|by expand].
by rewrite -(swapI kj) Z2 ZC4 ?swapI (irrelev (swap_neq ik) ki); rsimpl. Qed.

Corollary ZC4'_swap'{i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} 
(a c : I) (b : R) g:
 g .* (Z' ij a b) .* (X' ik c) = g .* X' ik (c _+_ a * b *_ c) .* X' jk (-_ (b * a * b *_ c)) .* Z' ij a b.
by rewrite GA ZC4'_swap // -?GA. Qed.

Corollary XZ_swap {i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} 
(a c : I) (b : R): X' ji a ^ X ik b .* Z' ki c b = Z' ki c b .* X' ji a ^ X ik b.
rewrite /X' ZC3. rsimpl. rewrite ?X'zero. cancel. rewrite ?X'def -GA.
rewrite ZC3'_swap // ?GA ZC4_swap// -?GA. apply GCr'.
by rewrite X0' X0 XC4'_swap'// X0' XC4'_swap'// X0
   plus_assoc' inv_l' plus_0_r' plus_comm' -plus_assoc' inv_r' plus_0_l'. Qed.

Corollary XZ_swap' {i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}
(a c : I) (b : R):
X' kj a ^ X ik b .* Z' ki c b = Z' ki c b .* X' kj a ^ X ik b.
rewrite /X' -(swapI ik) ZC3'; rsimpl; rewrite ?X'zero (irrelev (swap_neq ji) ij). cancel; rewrite ?X'def -GA.
rewrite ZC3_swap // ?GA ZC4'_swap// -?GA. apply GCr'. symmetry.
rewrite X0' XC4_swap // X0'; rsimpl. rewrite plus_comm' plus_assoc' inv_r'. 
rewrite dist_r mul_1_l dist_r' inv_plus' plus_assoc' -inv_plus'; rsimpl. rewrite inv_l'; rsimpl.
rewrite XC4_swap //. Qed.

(* ============================== *)

(* Lemma freshN: forall (i j : nat), exists k, k!=i /\ k!=j. Admitted.

Lemma CorrZ0 i j k l (ij : i!=j) (kl : k!=l) a b c d:
Z' ij (a + b) c ^ X kl d = Z' ij a c ^ X kl d .* Z' ij b c ^ X kl d. *)


(* 
case: (eqneqP i k) => [/eqP|] ik; subst; [rename ij into kj|];
(case: (eqneqP j l) => [/eqP|] jl; subst; [try rename kj into kl'; try rename ij into il|]);
try rewrite (irrelev kl' kl) {kl'}.

+ move: (freshN k l) => [] s [] sk sl.
  set (ls := swap_neq sl). set (ks := swap_neq sk). set (lk := swap_neq kl).
  rewrite ?(ZC1 k l s) ?swapI -/ls -/ks -/lk -?GA.
  remember (c*d + 1) as cd1.
  remember (d*c + 1) as dc1.
  rewrite ?dist_l ?inv_plus -?X0 ?Z0 -?GA. apply GCr'.
  rewrite ?GA. apply GCl'. rewrite -?GA.

case: (eqneqP j k) => [/eqP|] jk; subst; [rename ij into ik|];
(case: (eqneqP i l) => [/eqP|] il; subst; [try rename ij into lj; try rename ik into lk|]).
 + (* by rewrite ?ZC2 Z0. *) admit.
 + rewrite ?ZC3; rsimpl. rewrite ?dist_l ?dist_r inv_plus ?X0 -?GA.
   set (ki := swap_neq ik). set (lk := swap_neq kl). set (li := swap_neq il).
   rewrite (XC4_swap' k l i)// ?GA. do 2 apply GCl'.
   rewrite Z0 -?GA. apply GCr'.
   rewrite ZC3_swap // ZC4'_swap' //. apply GCr'. 
   rewrite ?dist_l ?dist_r; rsimpl.
   rewrite (plus_comm (b*d)).
   rewrite ?X0 ?GA ?X'Inv. apply GCl'. cancellate.
   rewrite XC4_swap// ?X'Inv; by cancel.
 + set (lk := swap_neq kl). set (kj := swap_neq jk). set (jl := swap_neq lj).
   rewrite -(swapI kl) ?ZC3' ?swapI -/kj Z0 ?dist_r ?dist_l ?dist_r ?inv_plus ?X0 ?GA. 
   apply GCl'. rewrite -?GA XC4'_swap//. apply GCr'. rewrite ?GA. apply GCl'. rewrite -?GA.
   rewrite ZC3'_swap // ?GA ZC4_swap//. apply GCl'. rewrite -?GA. apply GCr'.
   rewrite XC4'_swap' //; rsimpl. rewrite ?X0'. rewrite plus_comm plus_assoc inv_l plus_0_r.
   rewrite XC4'_swap'// ?X'Inv. by cancel.
 + (* by rewrite ?ZC5 Z0. *) admit. Qed. *) 


(* Axiom Z1: (Z' ij a b) ^ (X' ji c) = Z' ij a (b + c).

Axiom Z2: Z' ij a b ^ X' kl c = Z' ij a b ^ X kl c.

Axiom Z3: Z ij (a * b) c =  X jk (- (c * a)) .* X ik a .* Z ik (- a) (- (b * c)) .* X kj (b * c * a * b)
               .* X ij (a * b) .* X ki (- (b * c * a * b * c)) .* X ji (- (c * a * b * c)) .* Z jk (c * a) (- b). 

Axiom Z3': Z ij (a * b) c =  Z jk (- (c * a)) b .* X ij (a * b) .* X ik a .* Z ik (- a) (- (b * c))
.* X ji (- (c * a * b * c)) .* X jk (c * a) .* X ki (- (b * c * a * b * c)) .* X kj (- (b * c * a * b)). *)




(* Key identity to be proved *)

(* Lemma Q1 a b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
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
do 5 apply GCl'. rewrite -?GA. do 4 apply GCr'. by rewrite XC4'_swap. Qed. *)