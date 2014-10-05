Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident.
Import Ring.RingFacts.

Section RelSteinbergAxioms.

Parameter Z': forall {i j : nat} (p : i != j) (a : I) (r : R), ZZ.

Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

(* We assume that rank is at least 3 *)

Axiom fresh2: forall (i j : nat), exists k, k!=i /\ k!=j.
Axiom fresh3: forall (i j k : nat), exists l, l!=i /\ l!=j /\ l!=k.

Context (i j k l : nat) {a a1 a2 : I} (b c : R).

(* Definition of the action of the Steinberg group on relative generators *)
(* Don't use it *)
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

Axiom Z2: forall (ij : i!=j) (kl : k!=l), 
      Z' ij a b ^ X' kl a1 = Z' ij a b ^ X kl a1.

Axiom Z3R': forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i),
       (X' kj a ^ X ik (- b)) ^ X ji c =
      ((X' kj a ^ X ji c) ^ X ik (- b)) ^ X jk (c * b).

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

Lemma X1: X' ij a ^ X ji b = Z' ij a b. by rewrite /X' ZC2 ?X'def plus_0_l. Qed.

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

Corollary XC5_swap: (X' ij a1) .* (X' kl a2) =  (X' kl a2) .* (X' ij a1).
by rewrite /X' {1}swap_comm comm_d1 -?Z'Inv ?X'def Z2 ZC5 // X'def X'Inv; cancellate. Qed.

Corollary XC5_swap' g: g .* (X' ij a1) .* (X' kl a2) = g .* (X' kl a2) .* (X' ij a1).
by rewrite ?GA XC5_swap. Qed.

End XCorollaries.

Section SwapLemmata.

(* assume rank >= 2*)

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.

Corollary XC1: (X' ij a) ^ (X ij c) = X' ij (a).
rewrite (@ZC1 i j k a (0) c)//; rsimpl;
rewrite ?Z'zero ?X'zero ?X'def Xzero conjId //; cancel.
by rewrite X0' inv_r' X'zero GId. Qed.

Corollary ZC3_swap: (Z' ij a b) .* (X' jk a1) =
 (X' jk ((1 - b * a) *_ a1)) .* X' ik (a _* a1) .* Z' ij a b.
apply (GCl ((X' jk a1)^-1)). 
rewrite -?GA. by rewrite conj_def {1}/X' Z2 ZC3// dist_r' mul_1_l' -X0;
     cancellate; rsimpl. Qed.

Corollary ZC4'_swap: (Z' ij a b) .* (X' ik a1) = 
 X' ik (a1 _+_ a * b *_ a1) .* X' jk (-_ (b * a * b *_ a1)) .* Z' ij a b.
apply (GCl ((X' ik a1)^-1)). rewrite -X0; cancellate. by rewrite conj_def Z2 ZC4' XC4_swap; rsimpl. Qed.

Corollary ZC3'_swap: (Z' ij a b) .* (X' ki a1) = 
 (X' ki a1) .* X' ki (-_ (a1 _* a _* b)) .* X' kj (-_ (a1 _* a)) .* Z' ij a b.
apply (GCl ((X' ki a1)^-1)). cancellate. by rewrite conj_def Z2 ZC3'; rsimpl. Qed.

Corollary ZC4_swap:
 (Z' ij a b) .* (X' kj a1) =
 (X' kj a1) .* X' ki (a1 _* b _* a _* b) .* X' kj (a1 _* b _* a) .* Z' ij a b.
apply (GCl ((X' kj a1)^-1)). cancellate. by rewrite conj_def Z2 ZC4; rsimpl. Qed.

Corollary ZC5_swap:
 (Z' ij a b) .* (X' kl a1) = (X' kl a1) .* (Z' ij a b).
apply (GCl ((X' kl a1) ^-1)). rewrite -?GA; cancellate; by rewrite ?conj_def Z2 ZC5. Qed.

Corollary ZC5_swap' g: 
 g .* (Z' ij a b) .* (X' kl a1) = g .* (X' kl a1) .* (Z' ij a b).
by rewrite ?GA ZC5_swap. Qed.

End SwapLemmata.

Section Z0_ZC.

Section Z2_ZC.

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.
Context (m n : nat)
        {mi : m != i} {mj : m != j} {mk : m != k} {ml : m != l}
        {im : i != m} {jm : j != m} {km : k != m} {lm : l != m}
        {ni : n != i} {nj : n != j} {nk : n != k} {nl : n != l} {nm : n != m}
        {in' : i != n} {jn : j != n} {kn : k != n} {ln : l != n} {mn : m != n}.

Lemma Z2_00: (Z' ij a1 b ^ X' kl a2) ^ (X ji c) = (Z' ij a1 b ^ X kl a2) ^ (X ji c).
rewrite {2}/conj -X'Inv 2!mul_conj ZC2 ?XC5 // ZC5 // ZC2 X'Inv conj_def Z2 ZC5 //. Qed.

Lemma Z2_01: (Z' ij a1 b ^ X' kl a2) ^ (X mn c) = (Z' ij a1 b ^ X kl a2) ^ (X mn c).
rewrite {2}/conj -X'Inv 2!mul_conj ?XC5 // ?ZC5 // X'Inv conj_def Z2 ZC5 //. Qed.

Lemma Z2_02: (Z' ij a1 b ^ X' kl a2) ^ (X jm c) = (Z' ij a1 b ^ X kl a2) ^ (X jm c).
by rewrite {2}/conj -X'Inv 2!mul_conj ?XC5 // ZC3 // ZC5 // ZC3 // -?GA (ZC5_swap' i j) //
          -?(XC5_swap' k l) // X'Inv; cancel. Qed.

Lemma Z2_03: (Z' ij a1 b ^ X' kl a2) ^ (X km c) = (Z' ij a1 b ^ X kl a2) ^ (X km c).
by rewrite {2}/conj -X'Inv 2!mul_conj
           ZC5 // ZC5 // XC4' // XC4' // ZC5 // -ZC5_swap // X'Inv; cancel. Qed.



End Z2_ZC.

Context (i j k : nat) (a a1 a2 : I) (b c : R)
(ij : i != j) (ik : i != k) (jk : j != k) (ji : j != i) (ki : k != i) (kj : k != j).

(* Boilerplate lemmata about preservation of Relation Z0 *)

Lemma Z0_ZC2: forall (ij : i != j) (ji : j != i),
      (Z' ij (a1 _+_ a2) b) ^ (X ji c) = (Z' ij (a1) b) ^ (X ji c) .* (Z' ij (a2) b) ^ (X ji c).
by intros; rewrite ?ZC2 Z0. Qed.

Lemma Z0_ZC3: (Z' ij (a1 _+_ a2) b) ^ (X jk c) = (Z' ij (a1) b) ^ (X jk c) .* (Z' ij (a2) b) ^ (X jk c).
rewrite ?ZC3 //. rewrite Z0 -?GA. apply GCr'. rexpand.
rewrite -X0 ?GA. apply GCl'. 
rewrite -3!GA -X0 -GA XC4_swap // ?GA. apply GCl'.
rewrite -?GA ZC3_swap //. rexpand. rsimpl. rewrite -X0 ?GA. apply GCl'.
rewrite ZC4'_swap // -?GA. apply GCr'. rewrite X0'.
rewrite XC4_swap' // X0. rsimpl. rewrite inv_r' X'zero IdG. rexpand.
rewrite plus_comm' plus_assoc' inv_r' plus_0_r'. done. Qed.

Lemma Z0_ZC3': (Z' ij (a1 _+_ a2) b) ^ (X ki c) = (Z' ij a1 b) ^ (X ki c) .* (Z' ij a2 b) ^ (X ki c).
rewrite ?ZC3' //. rexpand. rewrite -X0 Z0 -?GA. apply GCr'.
cancel_l. rewrite -X0 -GA -?GA XC4'_swap //. cancel_l.
rewrite ZC3'_swap //. cancel_l. rewrite ?GA. rewrite ZC4_swap // -?GA. apply GCr'.
rewrite XC4'_swap' // ?X0'. rewrite XC4'_swap // ?X0'. rsimpl.
by rewrite inv_r' X'zero GId plus_comm' plus_assoc' inv_l' plus_0_r'. Qed.

Lemma Z0_ZC4: (Z' ij (a1 _+_ a2) b) ^ (X kj c) = (Z' ij a1 b) ^ (X kj c) .* (Z' ij a2 b) ^ (X kj c).
rewrite ?ZC4 //. rexpand. rewrite -X0 Z0 -?GA. apply GCr'.
cancel_l. rewrite -X0 -GA -?GA XC4'_swap //. cancel_l.
rewrite ZC3'_swap //. cancel_l. rewrite ?GA ZC4_swap // -?GA. apply GCr'.
rewrite XC4'_swap' // ?X0' XC4'_swap // ?X0'. rsimpl.
by rewrite plus_comm' plus_assoc' inv_r' plus_0_r' inv_l' X'zero GId. Qed.

Lemma Z0_ZC4' : (Z' ij (a1 _+_ a2) b) ^ (X ik c) = (Z' ij a1 b) ^ (X ik c) .* (Z' ij a2 b) ^ (X ik c).
rewrite ?ZC4' //. rexpand. rewrite -X0 Z0 -?GA. apply GCr'.
cancel_l. rewrite -X0 -GA -?GA XC4_swap //. cancel_l.
rewrite ZC3_swap //. rexpand. rsimpl. rewrite -X0. cancel_l.
rewrite GA ZC4'_swap // -?GA. apply GCr'. rewrite ?X0'.
rewrite XC4_swap' // ?X0' ?X0. rsimpl. rewrite inv_r' X'zero IdG.
by rewrite -plus_assoc' plus_comm' -plus_assoc' inv_r' plus_0_l'. Qed.

Context (l : nat) (il : i != l) (li : l != i) (jl : j != l) (lj : l != j) (kl : k != l) (lk : l != k).

Lemma Z0_ZC5: (Z' ij (a1 _+_ a2) b) ^ (X kl c) = 
              (Z' ij (a1) b) ^ (X kl c) .* (Z' ij (a2) b) ^ (X kl c).
by rewrite ?ZC5 // Z0. Qed.

End Z0_ZC.

Lemma Z3R: forall i j k a b c(ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i),
      Z' ij (b *_ a) c = (X' ji (-_ (c * b *_ a _* c)) .* X' ki (a _* c)) ^ X ik (- b) .*
      (X' ij (b *_ a) .* X' kj a) ^ X jk (c * b) .*
      X' kj (-_ a) .* X' ki (-_ (a _* c)). Admitted.

(* ========================== *)

Section ActionCommutation1.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ACL01: (Z' ji a d ^ X ik (b)) ^ X ij (c) = (Z' ji a d ^ X ij (c)) ^ X ik (b).
intros. rewrite ZC3// mul_conj -(swapI ij) ZC2 ?swapI mul_conj XC4'// XC3'// ZC3 -?GA//.
do 2 apply GCr'. by rewrite X0; collect. Qed.

Lemma ACL02: (Z' jk a d ^ X ik (b)) ^ X ij (c) = (Z' jk a d ^ X ij (c)) ^ X ik (b).
intros. 
rewrite -(swapI ik) ZC4// ?swapI 2!mul_conj (XC1 _ _ k)//
        XC4'// -(swapI ij) ZC3'// ?swapI 2!mul_conj XC4'// 
        (XC1 _ _ j)// -(swapI ik) ZC4 ?swapI -?GA
        XC4'_swap' // X0' XC4'_swap'// X0. symmetry.
by rewrite XC4'_swap'// X0' XC4'_swap' // X0 plus_comm' (plus_comm' (b*d*_a)). Qed.

Lemma ACL04 : (Z' kj a b ^ X ik c) ^ X jk d = (Z' kj a b ^ X jk d) ^ X ik c.
by rewrite ZC3' // 2!mul_conj XC3// XC4 // ZC2 ZC3' // -GA X0; rsimpl; collect. Qed.

Lemma ACL05 : (Z' kj a b ^ X ji c) ^ X jk d = (Z' kj a b ^ X jk d) ^ X ji c.
by rewrite ZC3 // 2!mul_conj XC4' // XC3' // ZC2 ZC3 // -GA X0; rsimpl; collect. Qed.

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

Corollary ACL04' : (X' kj a ^ X ik b) ^ X jk c = (X' kj a ^ X jk c) ^ X ik b.
by rewrite ACL04 //. Qed.

Corollary ACL05' : (X' kj a ^ X ji b) ^ X jk c = (X' kj a ^ X jk c) ^ X ji b.
by rewrite ACL05 //. Qed.

End ActionCommutation2.

(* There are no problems with argument validity before this line *)

Section ActionCommutation3.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma Z3R'':
((X' kj a ^ X jk (-b * c)) ^ X ji b) ^ X ik (c) = (X' kj a ^ X ik c) ^ X ji b.
move: (@Z3R' i j k a (-c) b ij jk ik ki kj ji); rsimpl. move => ->. symmetry.
by rewrite {1}XC3 // 2!mul_conj -(ACL04' j i k) // 
           (ACL04' i j k)// -?mul_conj -(XC3 k j i) // ACL05. Qed.

Lemma Z3R''': Z' ij (b *_ a) c = ((X' kj a ^ X ji c) ^ X ik (- b)) ^ X jk (c * b) .* X' kj (-_ a) ^ X ji c.
move: (@Z3R' i j k a b c ij jk ik ki kj ji).
rewrite XC3' // XC3 // {1} mul_conj ; rsimpl.
rewrite X1. move /(GCr' ((X' kj a ^ (X ji c)) ^-1)). cancel.
move => ->. by rewrite -?conjI -?X'Inv -(XC3 k j i). Qed.

Lemma ACL1: ((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij c = 
            ((X' ji a1 .* X' ki a2) ^ X ij c) ^ X ik b.
intros. by rewrite 2!mul_conj -ACL01' // ACL01' // 2!mul_conj. Qed.

Lemma ACL2: ((Z' ji a1 b .* X' kj a2 .* X' ki a3) ^ X ik d) ^ X ij c = 
            ((Z' ji a1 b .* X' kj a2 .* X' ki a3) ^ X ij c) ^ X ik d.
intros. by rewrite 4!mul_conj ACL01// -ACL02'// -ACL01'// -?mul_conj. Qed.

Lemma ACL4': ((X' ki a1 .* X' kj a2) ^ X ik c) ^ X jk b = 
             ((X' ki a1 .* X' kj a2) ^ X jk b) ^ X ik c.
intros. rewrite 4!mul_conj -ACL04' // -ACL04' //. Qed.

End ActionCommutation3.

Section ActionCommutation4.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.


Lemma ACL3: (((X' ji a1 .* X' ki a2) ^ X ik b) ^ X ij c) ^ (X ij d) =
             ((X' ji a1 .* X' ki a2) ^ X ik b) ^ (X ij (c+d)).
intros.
by rewrite ACL1 // mul_conj X1 XC3// -GA ACL1 // ACL2//
 (mul_conj (X ij (c+d))) X1 XC3// ?(mul_conj (X ij d))
 ZC2 XC3// XC4// -2!GA X0'; collect. Qed.

Lemma ACL3': (((X' ij a1 .* X' kj a2) ^ X jk b) ^ X ij c) ^ X ij (d) = 
              ((X' ij a1 .* X' kj a2) ^ X jk b) ^ (X ij (c+d)).
intros. rewrite 4!mul_conj; do 3 rewrite ACL03'// (XC1 _ _ k)//.
apply GCl'. rewrite X1 2!ZC4 2!mul_conj ZC4' ZC4 (XC1 _ _ k)//; rsimpl.
by rewrite ?X'zero ?IdG ?X'def -2!GA XC4'_swap'// 
           X0' XC4'_swap// X0' XC4'_swap; collect. Qed.

End ActionCommutation4.

Section ActionCorrectness.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ActionLemma1:
 (Z' ij a b ^ X ij c) ^ X ij d = Z' ij a b ^ X ij (c+d). 

intros. rewrite -(mul_1_l' a) (Z3R _ _ k); rsimpl.
rewrite 3!(mul_conj (X ij c)) 3!(mul_conj (X ij d)) 3!(mul_conj (X ij (c+d))).
rewrite ACL3 // ACL3' //.
replace conj with (locked conj); [|by rewrite -lock].
rewrite ?GA. do 2 apply GCl'. rewrite -?lock.
by (do 3 rewrite ?XC3 // ?XC4 // ?mul_conj -GA ?X0'); collect. Qed.

End ActionCorrectness.

Theorem ActionProperty1 i j k l (ij : i != j) (kl : k != l) a b c d:
 (Z' ij a b ^ X kl c) ^ X kl d = Z' ij a b ^ X kl (c + d).

case: (eqneqP i k) => [/eqP|] ik; subst; [rename ij into kj|];
(case: (eqneqP j l) => [/eqP|] jl; subst; [try rename kj into kl'; try rename ij into il|]).
 + rewrite (irrelev kl' kl). move: (fresh2 k l) => [] s [] sk sl.
   set (ks := swap_neq sk); set (ls := swap_neq sl); set (lk := swap_neq kl).
   by rewrite (ActionLemma1 k l s).
 + set (lk := swap_neq kl); set (jk := swap_neq kj); set (lj := swap_neq jl).
   by rewrite ?ZC4' 2!mul_conj XC4// (XC1 _ _ j) // ZC4' -2!GA
             (XC4_swap' k l j) // X0 X0'; collect.
 + set (lk := swap_neq kl); set (ki := swap_neq ik); set (li := swap_neq il).
   by rewrite ?ZC4 2!mul_conj XC4'// (XC1 _ _ i) // ZC4 -2!GA
             (XC4'_swap' k l i) // X0 X0'; collect.
 + case: (eqneqP j k) => [/eqP|] jk; subst; [|]; 
   (case: (eqneqP i l) => [/eqP|] il; subst; [|]).
  * clear jl. rewrite (irrelev ij ik). clear ij. rename ik into lk. 
    by rewrite ?ZC2 plus_assoc.
  * rewrite (irrelev ij ik). clear ij. clear jl.
    set (lk := swap_neq kl); set (ki := swap_neq ik); set (li := swap_neq il).
    by rewrite ?ZC3 // 2!mul_conj (XC1 _ _ i)// XC4 // ZC3// 
            -2!GA (XC4_swap' i l k) // X0 X0'; collect.
  * rename ij into lj. rename ik into lk. set (kj := swap_neq jk).
    by rewrite ?ZC3' // 2!mul_conj (XC1 _ _ j)// XC4' // ZC3'// 
            -2!GA (XC4'_swap' k j l) // X0 X0'; collect.
  * by rewrite ?ZC5. Qed.

(* TODO: Fix this error *)
Lemma Z0Lemma k i j a1 a2 b (ij : i!=j) (jk : j!=k) (ki : k!=i) (ji : j!=i) (kj : k!=j) (ik :i!=k):
 Z' ij (a1 _+_ a2) b = Z' ij a1 b .* Z' ij a2 b. 

rewrite -(mul_1_l' (a1 _+_ a2)) -{2}(mul_1_l' a1) -{2}(mul_1_l' a2) ?(Z3R''' _ _ k)//. 
rsimpl. rewrite -{1}X0 3!mul_conj. cancel_l.
rewrite inv_plus' -X0 mul_conj -GA. apply GCr'.

move: (@Z3R' i j k (a2) (1) b ij jk ik ki kj ji); rsimpl; move => <-.
rewrite -?mul_conj. apply conj_eq. rewrite ?XC3' //; rsimpl.
by rewrite XC4_swap // XC4_swap' // -GA ?X0 plus_comm'. Qed.

Theorem CorrZ0 i j k l (ij : i!=j) (kl : k!=l) a b c d:
Z' ij (a _+_ b) c ^ X kl d = Z' ij a c ^ X kl d .* Z' ij b c ^ X kl d.

case: (eqneqP i k) => [/eqP|] ik; subst; [rename ij into kj|];
(case: (eqneqP j l) => [/eqP|] jl; subst; [try rename kj into kl'; try rename ij into il|]);
try rewrite (irrelev kl' kl) {kl'}.

+ move: (fresh2 k l) => [] s [] sk sl.
  set (ls := swap_neq sl); set (ks := swap_neq sk); set (lk := swap_neq kl).
  admit.
+ set (lk := swap_neq kl); set (jk := swap_neq kj); set (lj := swap_neq jl).
  by rewrite Z0_ZC4'.
+ set (lk := swap_neq kl); set (ki := swap_neq ik); set (li := swap_neq il).
  by rewrite Z0_ZC4.
+ case: (eqneqP j k) => [/eqP|] jk; subst; [|]; 
  (case: (eqneqP i l) => [/eqP|] il; subst; [|]).
 * clear ik; rename ij into lk; clear jl.
   by rewrite Z0_ZC2.
 * clear ik; clear jl. rename ij into ik.
   set (lk := swap_neq kl); set (ki := swap_neq ik); set (li := swap_neq il).
   by rewrite Z0_ZC3.
 * rename ij into lj. rename ik into lk. set (kj := swap_neq jk).
   by rewrite Z0_ZC3'.
 * rewrite Z0_ZC5 //. Qed.