Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.
Import Ring.RingFacts.

Lemma swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym. Qed.

Axiom fresh2: forall (i j : nat), exists k, k!=i /\ k!=j.
Axiom fresh3: forall (i j k : nat), exists l, l!=i /\ l!=j /\ l!=k.

Parameter ZZZ : Type.
Parameter X : forall {i j : nat} (ij : i!=j) (x : R), ZZZ.

(* Custom 'pseudo'-conjugation *)
Parameter conj1 : ZZ -> ZZZ -> ZZ.
Axiom forward_rule: forall h1 h2 g, conj1 (h1 .* h2) g = (conj1 h1 g) .* (conj1 h2 g). 
Axiom identity_rule: forall h, conj1 Id h = Id.

Notation "h ^^ g" := (conj1 h g) (at level 11, left associativity).
Parameter Z': forall {i j : nat} (p : i != j) (a r : R), ZZ.
Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

Section Main.
Context (i j k l : nat) (a a1 a2 b c : R).

Axiom ZC1: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ji : j!=i) (kj : k!=j) (ki : k!=i), 
     Z' ij a b ^^ X ij c = 
     X' ki (a * b) .*
     X' kj (a * (b * c + 1)) .*
     X' kj (- (a * (b * c + 1))) ^^ X jk (- b) ^^ X ik (c * b + 1) .*
     X' ki (- (a * b))           ^^ X jk (- b) ^^ X ik (c * b + 1).

Axiom ZC2: forall (ij : i != j) (ji : j != i),
      (Z' ij a b) ^^ (X ji c) = Z' ij a (b + c).

Axiom ZC3: forall (ij : i != j) (jk : j != k) (ik : i != k) (ki : k != i) (ik : i != k),
      (Z' ij a b) ^^ (X jk c) = X' jk (- (b * a * c)) .* X' ik (a * c) .* Z' ij a b.

(* Unsure about this one *)
Axiom ZC3': forall (ij : i != j) (ik : i != k) (ki : k != i) (kj: k != j),
      (Z' ij a b) ^^ (X ki c) = X' ki (- (c * a * b)) .* X' kj (-(c * a)) .* Z' ij a b.

Axiom ZC4: forall (ij : i!=j) (kj : k!=j) (ki : k!=i),
      (Z' ij a b) ^^ (X kj c) = X' ki (c * b * a * b) .* X' kj (c * b * a) .* Z' ij a b.

Axiom ZC4': forall (ij : i!=j) (jk : j!=k) (ik : i!=k),
      (Z' ij a b) ^^ (X ik c) = X' jk (- (b * a * b * c)) .* X' ik (a * b * c) .* Z' ij a b.

Axiom ZC5: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (il : i!=l) (jl : j!=l) (kl : k!=l),
      (Z' ij a b) ^^ (X kl c) = Z' ij a b.

(* Identites for Relative Steinberg group *)

Axiom Z0: forall (ij : i!=j), Z' ij (a1 + a2) b = Z' ij a1 b .* Z' ij a2 b. 

Axiom Z1: forall (ij : i!=j) (ji : j!=i), 
      X' ji (- a2) .* Z' ij a1 b ^^ X ij c .* X' ij a2 = Z' ij a1 b ^^ (X ij (c+a2)).

Axiom Z2: forall (ij : i!=j) (ji : j!=i),
      Z' ji (- a2) c .* Z' ij a1 b ^^ X ij c .* Z' ji a2 c = Z' ij a1 (b + a2) ^^ X ij c.

Axiom Z3: forall (ij : i!=j) (kj : k!=j) (jk : j!=k) (ik : i!=k),
      X' jk (- a2) .* Z' ij a1 b .* X' jk a2 = Z' ij a1 b ^^ X jk a2.

Axiom Z3': forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i),
      X' ki (- a2) .* Z' ij a1 b .* X' ki a2 = Z' ij a1 b ^^ X ki a2.

Axiom Z4: forall (ij : i!=j) (kj : k!=j) (ik : i!=k), 
      X' kj (- a2) .* Z' ij a1 b .* X' kj a2 = Z' ij a1 b ^^ X kj a2.

Axiom Z4': forall (ij : i!=j) (kj : k!=j) (ik : i!=k), 
      X' ik (- a2) .* Z' ij a1 b .* X' ik a2= Z' ij a1 b ^^ X ik a2.

Axiom Z5: forall (ij : i!=j) (kl : k!=l), i!=k -> i!=l -> j!=k -> j!=l ->
      Z' kl a1 b .* Z' ij a2 c = Z' ij a2 c .* Z' kl a1 b. 

Axiom PR: forall (ij : i!=j) (ji : j!=i) (kj : k!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i),
       (X' kj a ^^ X ik (- b)) ^^ X ji c =
      ((X' kj a ^^ X ji c) ^^ X ik (- b)) ^^ X jk (c * b).

End Main.

Section BasicCorollaries.

Context (i j : nat) (a : R) (ij : i!=j).

Lemma Z'zero: forall b, Z' ij 0 b = Id.
intros. apply (GCr (Z' ij 0 b)).
Proof. rewrite -Z0. by rewrite IdG; rsimpl. Qed.

Lemma Z'Inv: forall b, Z' ij (-a) b = (Z' ij a b)^-1.
Proof. intros. apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l IG Z'zero. Qed.

Lemma X'def: Z' ij a 0 = X' ij a.
Proof. done. Qed.

Lemma X'zero: X' ij 0 = Id. 
Proof. by rewrite /X' Z'zero. Qed.

Lemma X'Inv: X' ij (-a) = (X' ij a)^-1.
Proof. by rewrite /X' Z'Inv. Qed.

End BasicCorollaries.

Ltac simplify0 := rsimpl; rewrite ?X'zero ?X'def ?forward_rule ?identity_rule -?GA; cancel.

Section XC_Corollaries.
(* Computation rules for simpler generators X_ij *)
Ltac XC E := rewrite /X' E; simplify0.

Context (i j k l : nat)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

Lemma X0' a1 a2 g: g .* X' ij (a1 + a2) = g .* X' ij a1 .* X' ij a2 .
Lemma X0  a1 a2: X' ij (a1 + a2) = X' ij a1 .* X' ij a2 .

Lemma XC2 a b: X' ij a ^^ X ji b = Z' ij a b.
Lemma XC3 a c: (X' ij a) ^^ (X jk c) = X' ik (a * c) .* X' ij a.
Lemma XC3' a c: (X' ij a) ^^ (X ki c) = X' kj (-(c * a)) .* X' ij a.
Lemma XC4  a c: (X' ij a) ^^ (X kj c) = X' ij a. 
Lemma XC4' a c: (X' ij a) ^^ (X ik c) = X' ij a. 
Lemma XC5  a c: (X' ij a) ^^ (X kl c) = X' ij a. 

by XC ZC5. Qed. by XC ZC4'. Qed.
by XC ZC4. Qed. by XC ZC3'. Qed.
by XC ZC3. Qed. by XC (@ZC2 i j a 0 b ij ji). Qed.
by XC Z0. Qed. by rewrite GA X0. Qed.
End XC_Corollaries.

Lemma XC1 i j (ij : i!=j) a c: X' ij a ^^ X ij c  = X' ij a.
move: (fresh2 i j) => [] m [] mi mj.
move: (swap_neq mi) (swap_neq mj) (swap_neq ij) => im jm ji.
rewrite /X' (ZC1 i j m) //; simplify0.
rewrite ZC2 plus_0_r X'def ZC3' //; simplify0.
move: (@Z4 i j m a (-a) 0 ij mj im); simplify0.
by rewrite XC4. Qed.

Module ZC_tactic.
Ltac Z_guard :=
  match goal with
    | [ |- is_true (negb (eq_op ?X ?X)) ] => fail 1
    | [ |- is_true (negb (eq_op ?X ?Y)) ] => done
    | [ |- _ ] => idtac
  end.

Ltac safe_rw E := try (rewrite E; Z_guard).

 Tactic Notation "safe_rw4" 
  reference(F1) "," reference(F2) "," reference(F3) "," reference(F4) :=
  safe_rw F1; safe_rw F2; safe_rw F3; safe_rw F4.

 Ltac ZC := safe_rw4 XC2,  ZC2,  XC3, ZC3;
            safe_rw4 XC3', ZC3', XC4, ZC4;
            safe_rw4 XC4', ZC4', XC5, ZC5;
            safe_rw XC1; rewrite ?forward_rule ?identity_rule; rsimpl; cancel.

 Ltac ZCR := repeat ZC.
End ZC_tactic.

Section AxiomsExpanded. Import ZC_tactic.

Context (i j k l : nat) (a a1 a2 b c : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

Lemma PRFS: 
Z' ij (b * a) c .* X' ki (a * c) .* X' kj a =
X' jk (c * b * a * c * b) .* X' ji (- (c * b * a * c)) .* Z' ki (a * c) (- b)
.* X' ik (b * a * c * b) .* X' ij (b * a) .* Z' kj a (c * b).
(* move: (PR i j k a b c ij ji kj jk ik ki). by ZCR; simplify0. Qed. *) Admitted.

Lemma Z3FS: 
 X' jk (- a2) .* Z' ij a1 b .* X' jk a2 = 
 X' jk (- (b * a1 * a2)) .* X' ik (a1 * a2) .* Z' ij a1 b.
move: (Z3 i j k a1 a2 b ij kj jk ik). by ZCR; simplify0. Qed.

Lemma Z3'FS:
 X' ki (- a2) .* Z' ij a1 b .* X' ki a2 =
 X' ki (- (a2 * a1 * b)) .* X' kj (- (a2 * a1)) .* Z' ij a1 b.
move: (Z3' i j k a1 a2 b ij jk ik ki). by ZCR; simplify0. Qed.

Lemma Z4FS: 
 X' kj (- a2) .* Z' ij a1 b .* X' kj a2 = 
 X' ki (a2 * b * a1 * b) .* X' kj (a2 * b * a1) .* Z' ij a1 b.
move: (Z4 i j k a1 a2 b ij kj ik). by ZCR; simplify0. Qed.

Lemma Z4'FS:
 X' ik (- a2) .* Z' ij a1 b .* X' ik a2 =
 X' jk (- (b * a1 * b * a2)) .* X' ik (a1 * b * a2) .* Z' ij a1 b.
move: (Z4' i j k a1 a2 b ij kj ik). by ZCR; simplify0. Qed.

End AxiomsExpanded.

Section Swap. Import ZC_tactic.

Corollary Z4_swap a a1 b i j k {ij : i != j} {ji : j != i} {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j}:
Z' ij a b .* X' kj a1 = X' kj a1 .* X' ki (a1 * b * a * b) .* X' kj (a1 * b * a) .* Z' ij a b.
by move: (@Z4 i j k a a1 b ij kj ik); ZCR; simplify0; move /(GCl' (X' kj a1)); rewrite -?GA X'Inv GI IdG. Qed.

Corollary Z4'_swap a a1 b i j k {ij : i != j} {ji : j != i} {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j}:
Z' ij a b .* X' ik a1 = X' ik (a1 + a * b * a1) .* X' jk (-(b * a * b * a1)) .* Z' ij a b.
move: (@Z4' i j k a a1 b ij kj ik); ZCR; simplify0; move /(GCl' (X' ik a1)); rewrite -?GA X'Inv GI IdG X0 => ->.
by bite; rewrite Z4_swap //; simplify0. Qed.

Corollary Z3_swap a a1 b i j k {ij : i != j} {ji : j != i} {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j}:
Z' ij a b .* X' jk (a1) = X' jk ((1 - b * a) * a1) .* X' ik ((a * a1)) .* Z' ij a b.
move: (@Z3 i j k a (a1) b ij kj jk ik); ZCR; simplify0.
move /(GCl' (X' jk (a1))). rewrite X'Inv -?GA GI IdG -X0 dist_r. by rsimpl. Qed.

Corollary Z3_swap_l a a1 b i j k {ij : i != j} {ji : j != i} {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j}:
X' jk (a1) .* Z' ij a b = Z' ij a b .* X' ik (- (a * a1)) .* X' jk ((1 + b * a) * a1).
move: (@Z3_swap (-a) (-a1) b i j k ij ji ik jk ki kj).
rewrite ?inv_mul ?mul_inv ?Z'Inv ?X'Inv -?GIM => /eqI; rsimpl.
by rewrite -?X'Inv -?Z'Inv -?GA. Qed.

Corollary Z3'_swap a a1 b i j k {ij : i != j} {ji : j != i} {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j}:
Z' ij a b .* X' ki a1 = X' ki (a1 * (1 - a * b)) .* X' kj (- (a1 * a)) .* Z' ij a b.
move: (@Z3' i j k a a1 b ij jk ik ki). ZCR; simplify0. 
move /(GCl' (X' ki a1)). by rewrite X'Inv -?GA GI IdG -X0 dist_l; rsimpl. Qed.

Context (i j k l : nat) (a a1 a2 b c : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

Corollary X4_swap: (X' ij a1) .* (X' kj a) = (X' kj a) .* (X' ij a1).
by rewrite Z4_swap //; simplify0. Qed.

Corollary X4'_swap: (X' ij a1) .* (X' ik a2) = (X' ik a2) .* (X' ij a1).
by rewrite Z4'_swap //; simplify0. Qed.

Corollary X5_swap: (X' ij a1) .* (X' kl a2) =  (X' kl a2) .* (X' ij a1).
by rewrite Z5. Qed.

(* Prime corollaries *)

Corollary X4_swap' g: g.* X' ij a1 .* X' kj a = g .* X' kj a .* X' ij a1.
by rewrite GA X4_swap -?GA. Qed.

Corollary X4'_swap' g: g .* X' ij a1 .* X' ik a2 = g .* X' ik a2 .* X' ij a1.
by rewrite GA X4'_swap -?GA. Qed.

Corollary X5_swap' g: g .* X' ij a1 .* X' kl a2 = g .* X' kl a2 .* X' ij a1.
by rewrite GA X5_swap -?GA. Qed.

Corollary Z3_swap' g:
g .* Z' ij a b .* X' jk a1 = g .* X' jk ((1 - b * a) * a1) .* X' ik ((a * a1)) .* Z' ij a b.
by rewrite GA Z3_swap -?GA. Qed.

Corollary Z3_swap'_l g:
g .* X' jk (a1) .* Z' ij a b = g .* Z' ij a b .* X' ik (- (a * a1)) .* X' jk ((1 + b * a) * a1).
by rewrite GA Z3_swap_l -?GA. Qed.

Corollary Z3'_swap' g:
g .* Z' ij a b .* X' ki a1 = g .* X' ki (a1 * (1 - a * b)) .* X' kj (- (a1 * a)) .* Z' ij a b.
by rewrite GA Z3'_swap -?GA. Qed.

Corollary Z4_swap' g: 
 g .* Z' ij a b .* X' kj a1 = 
 g .* X' kj a1 .* X' ki (a1 * b * a * b) .* X' kj (a1 * b * a) .* Z' ij a b.
by rewrite GA Z4_swap -?GA. Qed.

Corollary Z4'_swap' g:
 g .* Z' ij a b .* X' ik a1 = 
 g .* X' ik (a1 + a * b * a1) .* X' jk (-(b * a * b * a1)) .* Z' ij a b.
by rewrite GA Z4'_swap -?GA. Qed.

Corollary Z5' g: g.* Z' kl a1 b .* Z' ij a2 c = g .* Z' ij a2 c .* Z' kl a1 b. 
by rewrite 2!GA Z5. Qed.

End Swap.

Section Z5_Untangle. Import ZC_tactic.

Context (i j k l m n : nat) (a1 a2 b c d : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}

        {mi : m != i}  {mj : m != j} {mk : m != k} {ml : m != l}
        {im : i != m}  {jm : j != m} {km : k != m} {lm : l != m}

        {ni : n != i}  {nj : n != j} {nk : n != k} {nl : n != l} {nm : n != m}
        {in' : i != n} {jn : j != n} {kn : k != n} {ln : l != n} {mn : m != n}.

(* No clash in indices *)

Lemma Z5_01: (Z' kl a1 b .* Z' ij a2 c) ^^ (X mn d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X mn d).
ZCR. by rewrite Z5. Qed.

(* 1 index (rank 4) *)

Lemma Z5_02: (Z' kl a1 b .* Z' ij a2 c) ^^ (X mi d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X mi d).
ZCR. simplify0. rewrite -(Z5' i j k l) //; bite.
rewrite Z5 //; simplify0. bite. by rewrite Z5 //; simplify0. Qed.

Lemma Z5_03: (Z' kl a1 b .* Z' ij a2 c) ^^ (X mj d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X mj d).
ZCR. do 2 (rewrite -?GA -(Z5 k l) //; simplify0; bite). by rewrite Z5. Qed.

Lemma Z5_04: (Z' kl a1 b .* Z' ij a2 c) ^^ (X im d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X im d).
ZCR. do 2 (rewrite -?GA -(Z5 k l) //; simplify0; bite). by rewrite Z5. Qed.

Lemma Z5_05: (Z' kl a1 b .* Z' ij a2 c) ^^ (X jm d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X jm d).
ZCR. do 2 (rewrite -?GA -(Z5 k l) //; simplify0; bite). by rewrite Z5. Qed.

(* Uses rank 3 assumption 4*)
Lemma Z5_06: (Z' kl a1 b .* Z' ij a2 c) ^^ (X ij d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X ij d).
ZCR. rewrite (ZC1 _ _ m) //. ZCR. rewrite -?GA.
rewrite Z5 //; simplify0; repeat (rewrite -(Z5' k l) //; simplify0). Qed.

Lemma Z5_07: (Z' kl a1 b .* Z' ij a2 c) ^^ (X ji d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X ji d).
ZCR. by rewrite Z5. Qed.

Lemma Z5_08: (Z' kl a1 b .* Z' ij a2 c) ^^ (X ik d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X ik d).
ZCR. rewrite -?GA. rewrite Z3'_swap' // Z3'_swap' // Z5' //; simplify0. bite.
do 2 rewrite (@Z4'_swap' i j) //; simplify0; bite.
rewrite -?X0' (X5_swap' j l i k) // (X4_swap' j l i) // (X5_swap' i l j k) //
X4_swap // (X4'_swap' i k l) // (X4_swap' i k j) // -?X0' (X4'_swap' i l k) // -?X0' -?X0.
rexpand. rsimpl. bite. by rewrite -?plus_assoc (plus_comm (- _)). Qed.

Lemma Z5_09: (Z' kl a1 b .* Z' ij a2 c) ^^ (X il d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X il d).
ZCR. rewrite -?GA. do 2 rewrite Z4'_swap' //. do 2 rewrite (Z4_swap' k l) //.
rewrite -(Z5' i j) //; bite.
rewrite (X4_swap' j l i) // (X5_swap' j l) // (X4_swap' j l) //; rsimpl; bite.
rewrite (X4'_swap' i l k) // -?X0' (X4_swap' i l j) // (X4'_swap' i l k) //.
do 2 rewrite (X5_swap' i l j k) //. 
rewrite (X4'_swap' i l k) // -?X0' -?plus_assoc (plus_comm (a2 * c * d)).
by rewrite (X4_swap' j k i) // X5_swap // -X0'. Qed.

Lemma Z5_10: (Z' kl a1 b .* Z' ij a2 c) ^^ (X jk d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X jk d).
ZCR. rewrite -?GA. do 2 rewrite Z3'_swap' //. do 2 rewrite Z3_swap' //.
rewrite (Z5' k l i j) //; bite.
rewrite (X4'_swap' j l k) // (X4_swap' i k j) // -?X0.
rexpand; rsimpl; rewrite -?plus_assoc (plus_comm (-(c * a2 * d))). bite.
by rewrite -2!X0 X5_swap. Qed.

(* Same as above*)
Lemma Z5_11: (Z' kl a1 b .* Z' ij a2 c) ^^ (X jl d)  = (Z' ij a2 c .* Z' kl a1 b) ^^ (X jl d).
Abort.

End Z5_Untangle.

Section ACL_Z. Import ZC_tactic.

Context (i j k l : nat) (a b c d : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

(* Z_{-alpha} ^^ X_{-beta} ^^ X_{alpha} == Z_{-alpha} ^^ X_{alpha} ^^ X_{-beta} *)

Lemma ACL01: (Z' ji a d ^^ X ik (b)) ^^ X ij (c) = (Z' ji a d ^^ X ij (c)) ^^ X ik (b).
ZCR. rewrite -?X'Inv. bite. rewrite -X0. by collect. Qed.

(* Z_{beta} ^^ X_{-gamma} ^^ X_{alpha} == Z_{beta} ^^ X_{alpha} ^^ X_{-gamma} *)

Lemma ACL02: (Z' jk a d ^^ X ik (b)) ^^ X ij (c) = (Z' jk a d ^^ X ij (c)) ^^ X ik (b).
ZCR.  simplify0.
rewrite -?X'Inv (X4'_swap' i k j) // -X0 -X0' (X4'_swap' i k j) // -X0 -X0'.
by do 2 (rewrite plus_comm; bite). Qed.

(* FALSE STATEMENT *)
Lemma ACL03': (Z' ij a d ^^ X jk b) ^^ X ij c = (Z' ij a d ^^ X ij c) ^^ X jk b.
ZCR. rewrite X4_swap // -X0' -(mul_1_l (a * b)) -?mul_assoc -?dist_r.
rewrite ?(ZC1 _ _ l) //. ZCR. simplify0. bite.
rewrite (Z3_swap' i j k) //; simplify0.
rewrite (X5_swap' i j l k) //; bite.
rewrite (X4_swap' i k j) // -X0'. Abort.

(* Z_{-beta} ^^ X_{-gamma} ^^ X_{beta} == Z_{-beta} ^^ X_{beta} ^^ X_{-gamma} *)

Lemma ACL04 : (Z' kj a b ^^ X ik c) ^^ X jk d = (Z' kj a b ^^ X jk d) ^^ X ik c.
ZCR. by rewrite -?GA -?X'Inv -X0; collect. Qed.

(* Z_{-beta} ^^ X_{-alpha} ^^ X_{beta} == Z_{-beta} ^^ X_{beta} ^^ X_{-alpha}*)

Lemma ACL05 : (Z' kj a b ^^ X ji c) ^^ X jk d = (Z' kj a b ^^ X jk d) ^^ X ji c.
ZCR. by rewrite -?GA -?X'Inv -X0; collect. Qed.

End ACL_Z.

Section ZC1_interaction. Import ZC_tactic.

Context (i j k l m n : nat) (a1 a2 b c d : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}

        {mi : m != i}  {mj : m != j} {mk : m != k} {ml : m != l}
        {im : i != m}  {jm : j != m} {km : k != m} {lm : l != m}.

Ltac cancm E := rewrite -?(plus_comm0 _ E) -?(plus_comm0 _ (-E)); progress (rewrite ?inv_r0 ?inv_l0).

Lemma ZC1_I_01:
Z' ij a1 b ^^ X ij c .* X' il d = 
  X' il ((1 + (c * b + 1) * a1 * b) * d) .*
  X' jl (- (b * a1 * b * d)) .*
  Z' ij a1 b ^^ X ij c.
(* Proof.
remember (Z' ij a1 b ^^ X ij c) as RHS.
rewrite {1}HeqRHS.
rewrite (ZC1 _ _ k) //. ZCR. rewrite -?GA.
rewrite (Z3_swap' k i l) //.
rewrite (Z3_swap' j i l) //; simplify0.
rewrite (X5_swap' j i k l) //. rexpand. rsimpl.
rewrite (X5_swap' j k i l) //.
rewrite (X4'_swap' j k l) //.
rewrite (Z3_swap' j k l) //; simplify0.
rewrite (X4_swap' k l j) // -X0'.
rewrite -(Z5' k j i l) // X'def.
rewrite (Z3_swap' k j l) //; simplify0.

rexpand. rsimpl. rewrite -?plus_assoc.

remember (b * a1 * b) as A0.
remember (A0 * c * b * a1 * b) as A1.
remember (A0 * a1 * b) as A2.
remember (A1 * c * b * a1 * b * d) as A3.
remember (A1 * a1 * b * d) as A4.
remember (A2 * c * b * a1 * b * d) as A5.
remember (A2 * a1 * b * d) as A6.

cancm (A1 * d). cancm (A2 * d). cancm A3. cancm A4. cancm A5. 

remember (a1 * b) as B0.
remember (B0 * c * b * a1 * b) as B1.
remember (B0 * a1 * b) as B2.
remember (B1 * c * b * a1 * b * d) as B3.
remember (B2 * c * b * a1 * b * d) as B4.
remember (B1 * a1 * b * d) as B5.
remember (B2 * a1 * b * d) as B6.

cancm B3. cancm B4. cancm B5.

rewrite (Z4'_swap' k j l) // -X0'. simplify0.
rewrite (X4_swap' k l j) // -X0'.
rewrite (X4'_swap' i j l) //.
rewrite (Z3_swap' i j l) //; simplify0.
rewrite (X4_swap' j l i) // -X0'.
rewrite (X5_swap' i j k l) //.
rewrite (X4'_swap' i k l) //.
rewrite (X5_swap' i k j l) //.
rewrite (Z3_swap' i k l) //; simplify0.
rewrite (X4_swap' k l i) //.
rewrite (X4_swap' j l i) // -X0'.
rewrite (X5_swap' k j i l) //.
rewrite (Z3_swap' k j l) //; simplify0.
rewrite (X4'_swap' k j l) // -X0'.
rewrite (Z3_swap _ _ _ k i l) //; simplify0.
rewrite (X5_swap' k i j l) //.
rewrite (X4'_swap' k i l) //.
rewrite (X4_swap' j l k) // -X0'.

subst. simplify0. rexpand. rsimpl. rewrite -?plus_assoc -?mul_assoc.

remember (c * b * a1 * b) as C0.
remember (a1 * b * a1 * b) as C1.
remember (a1 * b * c * b * a1 * b) as C2.
remember (C2 * a1 * b) as C3.
remember (C2 * c * b * a1 * b) as C4.
remember (C1 * a1 * b) as C5.
remember (C1 * c * b * a1 * b) as C6.
remember (C3 * a1 * b) as C7.
remember (C3 * c * b * a1 * b) as C8.
remember (C6 * a1 * b) as C9.
remember (C6 * c * b * a1 * b) as C10.
remember (C4 * a1 * b) as C11.
remember (C4 * c * b * a1 * b) as C12.
remember (C5 * a1 * b) as C13.
remember (C5 * c * b * a1 * b) as C14.

cancm (C1 * d). cancm (C2 * d). cancm (C3 * d). cancm (C4 * d).
cancm (C5 * d). cancm (C6 * d). cancm (C7 * d). cancm (C8 * d).
cancm (C9 * d). cancm (C10 * d). cancm (C11 * d). cancm (C12 * d).
cancm (C13 * d). rewrite inv_r X'zero GId. subst.

remember (c * b * a1 * b) as D1.
remember (D1 * c * b) as D2.
remember (D1 * a1 * b) as D3.
remember (D2 * a1 * b) as D4.
remember (D3 * a1 * b) as D5.
remember (D3 * c * b) as D6.
remember (D4 * a1 * b) as D7.
remember (D4 * c * b) as D8.
remember (D6 * a1 * b) as D9.
remember (D8 * a1 * b) as D10.

cancm (D4 * d). cancm (D3 * d). cancm (D10 * d). cancm (D9 * d).
cancm (D5 * d). subst.

remember (b * a1 * b) as E1.
remember (E1 * c * b) as E2.
remember (E1 * a1 * b) as E3.
remember (E2 * a1 * b) as E4.

cancm (E4 * d). subst.

rewrite (ZC1 _ _ k) //. ZCR. 
rewrite -?GA. rexpand. rsimpl. by rewrite -?plus_assoc. Qed. *) Admitted.

End ZC1_interaction.

Section Z4_Untangle. Import ZC_tactic.

Context (i j k l m n : nat) (a a1 a2 b c d : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}

        {mi : m != i}  {mj : m != j} {mk : m != k} {ml : m != l}
        {im : i != m}  {jm : j != m} {km : k != m} {lm : l != m}.

Lemma PR1:
 X' kj a ^^ X ik (- b) ^^ X ji c =
 X' kj a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b). by apply /PR. Qed.

Lemma PR2:
 X' jk a ^^ X ik (- b) ^^ X ji c =
 X' jk a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
by ZCR.  Qed.

Lemma PR3:
 X' ij a ^^ X ik (- b) ^^ X ji c =
 X' ij a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).

by ZCR; rewrite -?GA (X4_swap' i k j) // -X0 -X0' inv_r inv_l; simplify0. Qed.

Lemma PR4:
 X' ji a ^^ X ik (- b) ^^ X ji c =
 X' ji a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
by ZCR. Qed.

Lemma PR5:
 X' ki a ^^ X ik (- b) ^^ X ji c =
 X' ki a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
by ZCR. Qed.

Lemma PR6:
 X' ik a ^^ X ik (- b) ^^ X ji c =
 X' ik a ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
by ZCR. Qed.

(* ====== ====== *)

(* not that easy *)
Lemma ZPR2:
 Z' jk a d ^^ X ik (- b) ^^ X ji c =
 Z' jk a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
rewrite -?XC2.

ZCR. rewrite -?GA -?XC2.

Lemma ZPR3:
 Z' ij a d ^^ X ik (- b) ^^ X ji c =
 Z' ij a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
ZCR. bite. rewrite (X4_swap' i k j) // -?X0' -?X0. Admitted.

Lemma ZPR4:
 Z' ji a d ^^ X ik (- b) ^^ X ji c =
 Z' ji a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
Abort.

Lemma ZPR5:
 Z' ki a d ^^ X ik (- b) ^^ X ji c =
 Z' ki a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
ZCR. bite. Admitted.

Lemma ZPR6:
 Z' ik a d ^^ X ik (- b) ^^ X ji c =
 Z' ik a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
ZCR. Abort.

Lemma ZPR1:
 Z' kj a d ^^ X ik (- b) ^^ X ji c =
 Z' kj a d ^^ X ji c ^^ X ik (- b) ^^ X jk (c * b).
ZCR. Abort.



Lemma Z4_01: (X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ (X im d) = (Z' ij a2 b ^^ X kj a1) ^^ (X im d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel.
rewrite Z4_swap' //.
rewrite (X5_swap' i m k j) // (Z3'_swap' i m k) // X'def (X5_swap' i m k j) //
        (Z3'_swap' j m k) // X'def (X5_swap' j m k i) //
        (Z3_swap' k j m) // -X0. simplify0. rewrite inv_l. by simplify0. Qed.

Lemma Z4_02: (X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ (X jm d) = (Z' ij a2 b ^^ X kj a1) ^^ (X jm d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel.
rewrite -(Z5' i j k m) // (Z4_swap' i j k). simplify0. bite.
rewrite 

move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj). Admitted.

(* Should be similar to the one above*)
Lemma Z4_03: ((X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ X ik c) ^^ (X km d) = (Z' ij a2 b ^^ X kj a1 ^^ X ik c) ^^ (X km d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel.
move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj). Admitted.

Lemma Z4_04: ((X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ X ik c) ^^ (X mi d) = (Z' ij a2 b ^^ X kj a1 ^^ X ik c) ^^ (X mi d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel. 
move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj). Admitted.

Lemma Z4_05: ((X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ X ik c) ^^ (X mj d) = (Z' ij a2 b ^^ X kj a1 ^^ X ik c) ^^ (X mj d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel. 
move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj). Admitted.

Lemma Z4_06: ((X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ X ik c) ^^ (X mk d) = (Z' ij a2 b ^^ X kj a1 ^^ X ik c) ^^ (X mk d).
ZCR. rewrite ?X'def ?X'zero -?GA; cancel.
move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj). Admitted.

(* 2 index clash *)

Lemma Z4_07: ((X' kj (- a1) .* Z' ij a2 b .* X' kj a1) ^^ X ik c) ^^ (X ij d) = (Z' ij a2 b ^^ X kj a1 ^^ X ik c) ^^ (X ij d).
rewrite ?forward_rule. rewrite ZC4. rewrite ?forward_rule.

ZCR. remember (Z' ij a2 b ^^ X ij d) as E1. simplify0.
rewrite ?(XC1 _ _ k) //. ZCR. simplify0. rewrite HeqE1.
move: (@Z4FS i j k a2 a1 b c ij ik jk ki kj).


End Z4_Untangle.