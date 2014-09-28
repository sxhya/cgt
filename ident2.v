Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident.
Import Ring.RingFacts SteinbergGroup GF.

Section RelSteinbergAxioms.

Parameter Z': forall {i j : nat} (p : i != j) (a : I) (r : R), ZZ.

Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

Context (i j k l : nat) {a a1 a2 : I} (b c : R).

(* Definition of the action of the Steinberg group on relative generators *)

Axiom ZC1: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ji : j!=i) (kj : k!=j) (ki : k!=i), 
      Z' ij a b ^ X ij c =
      X' ji (- b *_ a _* b) ^ X ik (- c * b - 1) .* Z' ki (a _* b) (- c * b - 1) .*
      X' ij ((c * b + 1) *_ a _* (b * c + 1)) ^ X jk b .* Z' kj (a _* (b * c + 1)) b .*
      X' kj (-_ a) .* X' ki (-_ a _* b) ^ X ij c.

Axiom ZC2: forall (ij : i != j) (ji : j != i),
      (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom ZC3: forall (ij : i != j) (jk : j != k) (ik : i != k) (ki : k != i) (ik : i != k),
      (Z' ij a b) ^ (X jk c) = X' jk (-_ (b *_ a _* c)) .* X' ik (a _* c) .* Z' ij a b.

Axiom ZC3': forall (ij : i != j) (ik : i != k) (ki : k != i) (kj: k != j),
      (Z' ij a b) ^ (X ki c) = X' ki (-_ (c *_ a _* b)) .* X' kj (-_(c *_ a)) .* Z' ij a b.

Axiom ZC4: forall (ij : i!=j) (kj : k!=j) (ki : k!=i),
      (Z' ij a b) ^ (X kj c) = X' ki (c * b *_ a _* b) .* X' kj (c * b *_ a) .* Z' ij a b.

Axiom ZC4': forall (ij : i!=j) (jk : j!=k) (ik : i!=k),
      (Z' ij a b) ^ (X ik c) = X' jk (-_ (b *_ a _* b _* c)) .* X' ik (a _* b _* c) .* Z' ij a b.

Axiom ZC5: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (il : i!=l) (jl : j!=l) (kl : k!=l),
      (Z' ij a b) ^ (X kl c) = Z' ij a b.

(* Definition of Relations between relative generators *)

Axiom Z0: forall (ij : i!=j), Z' ij (a1 _+_ a2) c = Z' ij a1 c .* Z' ij a2 c.

Axiom Z1: forall (ij : i!=j) (ji : j!=i), 
      (Z' ij a b) ^ (X ji c) = Z' ij a (b + c).

Axiom Z2: forall (ij : i!=j) (kl : k!=l), 
      Z' ij a b ^ X' kl a1 = Z' ij a b ^ X kl a1.

Axiom Z3L: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i), 
      Z' ij (a _* b) c = X' jk (-_ (c *_ a)) .* X' ik a .*
      X' ij (a _* b) ^ X ki (- (b * c)) .* Z' ik (-_ a) (- (b * c)) .* 
      X' ji (-_ (c *_ a _* b _* c)) ^ X kj (- b) .* Z' jk (c *_ a) (- b).

Axiom Z3R: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i),
      Z' ij (b *_ a) c = (X' ji (-_ (c * b *_ a _* c)) .* X' ki (a _* c)) ^ X ik (- b) .*
      (X' ij (b *_ a) .* X' kj a) ^ X jk (c * b) .*
      X' kj (-_ a) .* X' ki (-_ (a _* c)).

End RelSteinbergAxioms.

Lemma Z'zero i j b (ij : i != j):
      Z' ij 0 b = Id.
intros. apply (GCr (Z' ij 0 b)). rewrite -Z0. by rewrite IdG; rsimpl. Qed.

Lemma Z'Inv i j a b (ij : i != j):
      Z' ij (-_a) b = (Z' ij a b)^-1.
apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l' IG Z'zero. Qed.

Lemma X'def i j a (ij : i != j):
      Z' ij a 0 = X' ij a. 
done. Qed.

Lemma X'zero i j (ij : i != j):
      X' ij 0 = Id. 
by rewrite /X' Z'zero. Qed.

Lemma X'Inv i j (ij : i != j) a:
      X' ij (-_a) = (X' ij a)^-1. 
by rewrite /X' Z'Inv. Qed.

Section XCorollaries.

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.

Ltac ZX E := rewrite /X'; rewrite E; rewrite /X'; rsimpl; rewrite ?Z'zero; cancel.

Lemma X0: X' ij a1 .* X' ij a2 = X' ij (a1 _+_ a2). by ZX Z0. Qed.

Lemma X1: X' ij a ^ X ji b = Z' ij a b. by rewrite /X' Z1 ?X'def plus_0_l. Qed.

Corollary X0': forall (g : ZZ), g .* X' ij a1 .* X' ij a2 = g .* X' ij (a1 _+_ a2).
intros. by rewrite GA -X0. Qed.

(* For XC1 see below *)
Corollary XC2: (X' ij a) ^ (X ji c) = Z' ij a c.
by move: (@ZC2 i j a (0) c ij ji) => /=; rewrite /X' plus_0_l => ->. Qed.

Corollary XC3: (X' ij a) ^ (X jk c) = X' ik (a _* c) .* X' ij a.
by ZX ZC3. Qed.

Corollary XC3': (X' ij a) ^ (X ki c) = X' kj (-_ (c *_ a)) .* X' ij a.
by rewrite -(swapI ki); ZX ZC3'. Qed.

Corollary XC4: (X' ij a) ^ (X kj c) = X' ij a. 
by rewrite -(swapI kj); ZX ZC4. Qed. 

Corollary XC4': (X' ij a) ^ (X ik c) = X' ij a. 
by ZX ZC4'. Qed.

Corollary XC5: (X' ij a) ^ (X kl c) = X' ij a. 
by ZX ZC5. Qed.

Corollary XC4_swap: (X' ij a1) .* (X' kj a2) = (X' kj a2) .* (X' ij a1).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 -(swapI ij) ZC4; rsimpl; rewrite /X' ?Z'zero; cancel. Qed. 

Corollary XC4'_swap: (X' ij a1) .* (X' ik a2) = (X' ik a2) .* (X' ij a1).
by rewrite /X' {1}swap_comm comm_d1 -Z'Inv Z2 ZC4'; rsimpl; rewrite /X' ?Z'zero; cancel. Qed.

Corollary XC4_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' kj a2) = g .* (X' kj a2) .* (X' ij a1).
intros. by rewrite GA XC4_swap ?GA. Qed.

Corollary XC4'_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' ik a2) = g .* (X' ik a2) .* (X' ij a1).
intros. by rewrite GA XC4'_swap ?GA. Qed.

End XCorollaries.

Section SwapLemmata.

(* assume rank >= 2*)

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Corollary XC1: (X' ij a) ^ (X ij c) = X' ij (a).
rewrite (@ZC1 i j k a (0) c)//; rsimpl;
rewrite ?Z'zero ?X'zero ?X'def Xzero conjId //; cancel.
by rewrite X0' inv_r' X'zero GId. Qed.

Corollary ZC3_swap: (Z' ij a b) .* (X' jk a1) =
 (X' jk ((1 - b * a) *_ a1)) .* X' ik (a _* a1) .* Z' ij a b.
apply (GCl ((X' jk a1)^-1)). rewrite -?GA.
replace (X' jk a1 ^-1 .* Z' ij a b .* X' jk a1) with (Z' ij a b ^ X' jk a1); try by expand.
by rewrite {1}/X' Z2 ZC3// dist_r' mul_1_l' -X0; cancellate; rsimpl. Qed.

Corollary ZC4'_swap: (Z' ij a b) .* (X' ik a1) = 
 X' ik (a1 _+_ a * b *_ a1) .* X' jk (-_ (b * a * b *_ a1)) .* Z' ij a b.
apply (GCl ((X' ik a1)^-1)). rewrite -X0; cancellate.
replace (X' ik a1 ^-1 .* Z' ij a b .* X' ik a1) with (Z' ij a b ^ X' ik a1); [|try by expand].
by rewrite Z2 ZC4' XC4_swap; rsimpl. Qed.

Corollary ZC3'_swap: (Z' ij a b) .* (X' ki a1) = 
 (X' ki a1) .* X' ki (-_ (a1 _* a _* b)) .* X' kj (-_ (a1 _* a)) .* Z' ij a b.
apply (GCl ((X' ki a1)^-1)). cancellate.
replace (X' ki a1 ^-1 .* Z' ij a b .* X' ki a1) with (Z' ij a b ^ X' ki a1); [|by expand].
by rewrite Z2 ZC3'; rsimpl. Qed.

Corollary ZC4_swap:
 (Z' ij a b) .* (X' kj a1) =
 (X' kj a1) .* X' ki (a1 _* b _* a _* b) .* X' kj (a1 _* b _* a) .* Z' ij a b.
apply (GCl ((X' kj a1)^-1)). cancellate.
replace (X' kj a1 ^-1 .* Z' ij a b .* X' kj a1) with (Z' ij a b ^ X' kj a1); [|by expand].
by rewrite Z2 ZC4; rsimpl. Qed.

End SwapLemmata.

(* Corollary ZC4'_swap' g:
 g .* (Z' ij a b) .* (X' ik a1) = g .* X' ik (a1 _+_ a * b *_ a1) .* X' jk (-_ (b * a * b *_ a1)) .* Z' ij a b.
by rewrite GA ZC4'_swap // -?GA. Qed.

Corollary XZ_swap:
 X' ji a ^ X ik b .* Z' ki a1 b = Z' ki a1 b .* X' ji a ^ X ik b.
rewrite /X' ZC3 //. rsimpl. rewrite ?X'zero. cancel. rewrite ?X'def -GA.
rewrite ZC3'_swap //. ?GA ZC4_swap// -?GA. apply GCr'.
by rewrite X0' X0 XC4'_swap'// X0' XC4'_swap'// X0
   plus_assoc' inv_l' plus_0_r' plus_comm' -plus_assoc' inv_r' plus_0_l'. Qed.

Corollary XZ_swap' {i j k}{ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}
(a c : I) (b : R):
X' kj a ^ X ik b .* Z' ki c b = Z' ki c b .* X' kj a ^ X ik b.
rewrite /X' -(swapI ik) ZC3'; rsimpl; rewrite ?X'zero (irrelev (swap_neq ji) ij). cancel; rewrite ?X'def -GA.
rewrite ZC3_swap // ?GA ZC4'_swap// -?GA. apply GCr'. symmetry.
rewrite X0' XC4_swap // X0'; rsimpl. rewrite plus_comm' plus_assoc' inv_r'. 
rewrite dist_r mul_1_l dist_r' inv_plus' plus_assoc' -inv_plus'; rsimpl. rewrite inv_l'; rsimpl.
rewrite XC4_swap //. Qed. *)

(* ========================== *)

Section ActionCommutation1.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ACL01: (Z' ji a d ^ X ik (b)) ^ X ij (c) = (Z' ji a d ^ X ij (c)) ^ X ik (b).
intros. rewrite ZC3// mul_conj -(swapI ij) ZC2 ?swapI mul_conj XC4'// XC3'// ZC3 -?GA//.
do 2 apply GCr'. by rewrite X0 -inv_plus' -dist_r'. Qed.

Lemma ACL02: (Z' jk a d ^ X ik (b)) ^ X ij (c) = (Z' jk a d ^ X ij (c)) ^ X ik (b).
intros. 
rewrite -(swapI ik) ZC4// ?swapI 2!mul_conj (XC1 _ _ k)//
        XC4'// -(swapI ij) ZC3'// ?swapI 2!mul_conj XC4'// 
        (XC1 _ _ j)// -(swapI ik) ZC4 ?swapI -?GA
        XC4'_swap' // X0' XC4'_swap'// X0. symmetry.
by rewrite XC4'_swap'// X0' XC4'_swap' // X0 plus_comm' (plus_comm' (b*d*_a)). Qed.

End ActionCommutation1.

Section ActionCommutation2.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Corollary ACL01': (X' ji (a) ^ X ik (b)) ^ X ij (c) = (X' ji (a) ^ X ij (c)) ^ X ik (b).
by intros; rewrite ?/X' ACL01. Qed.

Corollary ACL02': (X' jk a ^ X ik (b)) ^ X ij (c) = (X' jk a ^ X ij (c)) ^ X ik (b).
by intros; rewrite ?/X' ACL02. Qed.

Lemma ACL03': (X' ij a ^ X jk b) ^ X ij c = (X' ij a ^ X ij c) ^ X jk b.
intros. by rewrite XC3// (XC1 _ _ k)// mul_conj XC3// XC4'// (XC1 _ _ k). Qed.

End ActionCommutation2.

(* ========================== *)

Section ActionCommutation3.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ACL1: ((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij c = 
            ((X' ji a1 .* X' ki a2) ^ X ij c) ^ X ik b.
intros. by rewrite 2!mul_conj -ACL01' // ACL01' // 2!mul_conj. Qed.

Lemma ACL2: ((Z' ji a1 b .* X' kj a2 .* X' ki a3) ^ X ik d) ^ X ij c = 
            ((Z' ji a1 b .* X' kj a2 .* X' ki a3) ^ X ij c) ^ X ik d.
intros. by rewrite 4!mul_conj ACL01// -ACL02'// -ACL01'// -?mul_conj. Qed.

End ActionCommutation3.

Section ActionCommutation4.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ACL3: (((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij c) ^ (X ij d) =
             ((X' ji a1 .* X' ki a2) ^ X ik b) ^ (X ij (c+d)).
intros.
by rewrite ACL1 // mul_conj X1 XC3// -GA ACL1 // ACL2//
 (mul_conj (X ij (c+d))) X1 XC3// ?(mul_conj (X ij d))
 ZC2 XC3// XC4// -2!GA X0' dist_l'. Qed.

Lemma ACL3': (((X' ij a1 .* X' kj a2) ^ X jk b) ^ X ij c) ^ X ij (d) = 
              ((X' ij a1 .* X' kj a2) ^ X jk b) ^ (X ij (c+d)).
intros. rewrite 4!mul_conj; do 3 rewrite ACL03'// (XC1 _ _ k)//.
apply GCl'. rewrite X1 2!ZC4 2!mul_conj ZC4' ZC4 (XC1 _ _ k)//; rsimpl.
rewrite ?X'zero ?IdG ?X'def -2!GA XC4'_swap'// X0' XC4'_swap// X0'.
by rewrite -dist_r' -dist_r'' -dist_r' -dist_r XC4'_swap. Qed.
End ActionCommutation4.

Section ActionCorrectness.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Corollary ActionCorr1:
 (Z' ij a b ^ X ij c) ^ X ij d = Z' ij a b ^ X ij (c+d). 

intros. rewrite -(mul_1_l' a) (Z3R _ _ k); rsimpl.
rewrite 3!(mul_conj (X ij c)) 3!(mul_conj (X ij d)) 3!(mul_conj (X ij (c+d))).
rewrite ACL3 // ACL3' //.
replace conj with (locked conj); [|by rewrite -lock].
rewrite ?GA. do 2 apply GCl'. rewrite -?lock.
do 3 rewrite ?XC3 // ?XC4 // ?mul_conj -GA ?X0'.
by rewrite -dist_l'. Qed.

End ActionCorrectness.

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