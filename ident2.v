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
   X' ji (- b *_ a _* b)                   ^ X ik (- c * b - 1) .* Z' ki (a _* b) (- c * b - 1)
.* X' ij ((c * b + 1) *_ a _* (b * c + 1)) ^ X jk b             .* Z' kj (a _* (b * c + 1)) b
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

Axiom Z1: forall (ij : i!=j) (ji : j!=i), (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom Z2: forall (ij : i!=j) (kl : k!=l), Z' ij a b ^ X' kl a1 = Z' ij a b ^ X kl a1.

Axiom Z3L: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
Z' ij (a _* b) c =             X' jk (-_ (c *_ a)) .* X' ik a .*
                 X' ij (a _* b) ^ X ki (- (b * c)) .* Z' ik (-_ a) (- (b * c)) .* 
  X' ji (-_ (c *_ a _* b _* c)) ^ X kj (- b)       .* Z' jk (c *_ a) (- b).

Axiom Z3R: forall (ij : i!=j) (jk : j!=k) (ik : i!=k), let ki := swap_neq ik in let kj := swap_neq jk in let ji := swap_neq ij in
Z' ij (b *_ a) c = (X' ji (-_ (c * b *_ a _* c)) .* X' ki (a _* c)) ^ X ik (- b) .*
                   (X' ij (b *_ a) .* X' kj a) ^ X jk (c * b) .*
                    X' kj (-_ a) .* X' ki (-_ (a _* c)).

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
 (X' ij a) ^ (X ij c) = X' ij (a).
rewrite (@ZC1 i j k a (0) c); rsimpl;
rewrite (irrelev (swap_neq jk) kj) ?Z'zero ?X'zero ?X'def Xzero conjId; cancel.
by rewrite X0' inv_r' X'zero GId. Qed.

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

(* ========================== *)
Lemma ACL01 a d b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(Z' ji a d ^ X ik (b)) ^ X ij (c) = (Z' ji a d ^ X ij (c)) ^ X ik (b).
intros. rewrite ZC3 mul_conj -(swapI ij) ZC2 ?swapI mul_conj XC4'// XC3'// ZC3 -?GA.
do 2 apply GCr'. by rewrite X0 -inv_plus' -dist_r'. Qed.

Lemma ACL02 a d b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(Z' jk a d ^ X ik (b)) ^ X ij (c) = (Z' jk a d ^ X ij (c)) ^ X ik (b).
intros. 
rewrite -(swapI ik) ZC4 ?swapI 2!mul_conj (@XC1 _ _ _ _ k)//
        XC4'// -(swapI ij) ZC3' ?swapI 2!mul_conj XC4'// 
        (@XC1 _ _ _ _ j)// -(swapI ik) ZC4 ?swapI -?GA
        XC4'_swap' // X0' XC4'_swap'// X0. symmetry.
by rewrite XC4'_swap'// X0' XC4'_swap' // X0 plus_comm' (plus_comm' (b*d*_a)). Qed.

Corollary ACL01' a b c i j k 
(ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(X' ji (a) ^ X ik (b)) ^ X ij (c) = (X' ji (a) ^ X ij (c)) ^ X ik (b).
by intros; rewrite ?/X' ACL01. Qed.

Corollary ACL02' a b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(X' jk a ^ X ik (b)) ^ X ij (c) = (X' jk a ^ X ij (c)) ^ X ik (b).
by intros; rewrite ?/X' ACL02. Qed.

(* ========================== *)

Corollary ACL1 a b i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(X' ki (a) ^ X ij b) ^ X ij (- b) = X' ki a.
intros.  rewrite XC3 mul_conj XC3 XC4 // -GA X0.
by rsimpl; rewrite inv_r' X'zero IdG. Qed.

Lemma ACL2 a1 a2 b c i j k 
(ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
((X' ji (a1) .* X' ki (a2)) ^ X ik b) ^ X ij c = 
((X' ji (a1) .* X' ki (a2)) ^ X ij c) ^ X ik b.
intros. by rewrite 2!mul_conj -ACL01' // -/ki ACL01' // -/ji 2!mul_conj. Qed.

Lemma ACL3 a1 a2 a3 b c d i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
((Z' ji (a1) b .* X' kj (a2) .* X' ki (a3)) ^ X ik d) ^ X ij c = 
((Z' ji (a1) b .* X' kj (a2) .* X' ki (a3)) ^ X ij c) ^ X ik d.
intros. by rewrite 4!mul_conj ACL01// -/ji -ACL02' -ACL01'// -/ki -?mul_conj. Qed.

Corollary ACL4 a1 a2 b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij (-c)) ^ (X ij c) =
  (X' ji a1 .* X' ki a2) ^ X ik b.
intros. rewrite ACL2 // -/ji -/ki mul_conj /X' Z1 ?X'def plus_0_l XC3 -GA.
rewrite ACL3 -/ji -/ki -/kj 3!mul_conj /X' Z1 inv_l ?X'def.
rewrite XC4 // XC3 -mul_conj -GA; rsimpl; rewrite X0' inv_l' X'zero GId //. Qed.

(* TODO: PROVE THIS LEMMA*)
Lemma ACL5 a1 a2 b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(((X' ij a1 .* X' kj a2) ^ X jk b) ^ X ij (- c)) ^ X ij (c) = 
 (X' ij a1 .* X' kj a2) ^ X jk b.
intros. rewrite (mul_conj (X jk b)) (mul_conj (X ij (- c))).
Admitted.

Corollary ACL4' a1 a2 b c i j k 
{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}:
(((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij (-c)) ^ (X ij c) =
  (X' ji a1 .* X' ki a2) ^ X ik b.
move: (ACL4 a1 a2 b c i j k ij ik jk) => /=.
by rewrite (irrelev (swap_neq ij) ji) (irrelev (swap_neq ik) ki). Qed.

Corollary ActionCorr1 a b c i j k 
(ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (Z' ij a b ^ X ij c) ^ X ij (-(c)) = Z' ij a b.
intros. rewrite -{1}(mul_1_l' a) (Z3R _ _ k)
        (irrelev (swap_neq ij) ji) (irrelev (swap_neq ik) ki) (irrelev (swap_neq jk) kj).
rsimpl. rewrite 3!(mul_conj (X ij c)) 3!(mul_conj (X ij (- c))).
rewrite XC4 // XC4 // ACL1 // -/ki. 
replace (c) with (--c); [|by rewrite invI].
replace (- - - c) with (- c); [|by rewrite invI].
rewrite ACL4' // ACL5 // -/kj.
rewrite -{7}(mul_1_l' a) (Z3R _ _ k)
 (irrelev (swap_neq ij) ji) (irrelev (swap_neq ik) ki) (irrelev (swap_neq jk) kj); rsimpl; done. Qed.

(* Lemma ACL03 a d b c i j k (ij : i != j) (ik : i != k) (jk : j != k):
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
(Z' ij a d ^ X ik (b)) ^ X ij (c) = (Z' ij a d ^ X ij (c)) ^ X ik (b).
intros.
rewrite -(swapI ik) ZC4' ?swapI (ZC1 _ _ k) -/ji -/kj -/ki.
rewrite 2!mul_conj XC3'// XC4'// (ZC1 _ _ k) -/ji -/kj -/ki.
rewrite XC3 XC3 XC3 7!mul_conj. rewrite XC4//.
rewrite (@XC1 _ _ _ _ j)// XC4'// ?XC3 ?XC3'//.
rewrite mul_conj XC3'// /X' ?Z1 ?X'def plus_0_l.
rewrite -(swapI ik) ZC3' ?swapI. *)


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