Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.
Import Ring.RingFacts.

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
Context (i j k l : nat) {a a1 a2 b c : R}.

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

Axiom Z1: forall (ij : i!=j) (kj : k!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i),
     Z' ij a b ^^ X ij c = 
     X' ki (a * b) .* X' kj (a * (b * c + 1)) .*
     X' kj (- (a * (b * c + 1))) ^^ X jk (- b) ^^ X ik (c * b + 1) .*
     X' ki (- (a * b))           ^^ X jk (- b) ^^ X ik (c * b + 1).

Axiom Z2: forall (ij : i!=j) (ji : j!=i),
      Z' ji (- a2) c .* Z' ij a1 b ^^ X ij c .* Z' ji a2 c = Z' ij a1 (b + a2) ^^ X ij c.

Axiom Z3: forall (ij : i!=j) (kj : k!=j) (jk : j!=k) (ik : i!=k),
      (X' jk (- a2) .* Z' ij a1 b .* X' jk a2) ^^ X kj c = Z' ij a1 b ^^ X jk a2 ^^ X kj c.

Axiom Z4: forall (ij : i!=j) (kj : k!=j) (ik : i!=k), 
      (X' kj (- a1) .* Z' ij a b .* X' kj a1) ^^ X ik c = Z' ij a b ^^ X kj a1 ^^ X ik c.

Axiom Z5: forall (ij : i!=j) (kl : k!=l), i!=k -> i!=l -> j!=k -> j!=l ->
      Z' kl a1 b .* Z' ij a2 c = Z' ij a2 c .* Z' kl a1 b. 

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

Section XC_Corollaries.
(* Computation rules for simpler generators X_ij *)
Ltac XC E := rewrite /X' E; rsimpl; rewrite ?X'def ?X'zero; cancel.

Context (i j k l : nat) {a a1 a2 : R} (b c : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

Lemma XC1: X' ij a ^^ X ij c  = X' ij a.
 Proof. rewrite /X' (ZC1 i j k) //. rsimpl. rewrite ?X'zero ?X'def IdG.
        rewrite ZC2 plus_0_r X'def ?identity_rule GId ZC3' //; rsimpl.
        rewrite X'def X'zero IdG -?GA.
        move: (@Z4 i j k a (-a) 0 0 ij kj ik); rewrite ?forward_rule.
        rewrite /X' ZC3' // ZC4 // ZC3' // ZC4' //; rsimpl.
        rewrite ?X'zero ?X'def; cancel. rewrite ZC4' //. rsimpl.
        by rewrite ?X'zero ?X'def; cancel. Qed.
Lemma XC2: X' ij a ^^ X ji b = Z' ij a b.
Lemma XC3: (X' ij a) ^^ (X jk c) = X' ik (a * c) .* X' ij a.
Lemma XC3': (X' ij a) ^^ (X ki c) = X' kj (-(c * a)) .* X' ij a.
Lemma XC4: (X' ij a) ^^ (X kj c) = X' ij a. 
Lemma XC4': (X' ij a) ^^ (X ik c) = X' ij a. 
Lemma XC5: (X' ij a) ^^ (X kl c) = X' ij a. 

by XC ZC5. Qed. by XC ZC4'. Qed. by XC ZC4. Qed. by XC ZC3'. Qed. by XC ZC3. Qed. by XC (@ZC2 i j a 0 b ij ji). Qed.

Corollary XC4_swap: (X' ij a1) .* (X' kj a2) = (X' kj a2) .* (X' ij a1).
rewrite {1}swap_comm comm_d1 -X'Inv. cancel. rewrite /conj -X'Inv.
rewrite {2}/X' Z2 ZC4. rsimpl. rewrite ?X'zero X'def. by cancel. Qed.



Corollary XC4'_swap: (X' ij a1) .* (X' ik a2) = (X' ik a2) .* (X' ij a1).
rewrite {1}swap_comm comm_d1 -X'Inv. cancel. rewrite /conj -X'Inv.
rewrite {2}/X' Z2 ZC4'. rsimpl. rewrite ?X'zero X'def. by cancel. Qed.

Corollary XC4_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' kj a2) = g .* (X' kj a2) .* (X' ij a1).
intros. by rewrite GA XC4_swap ?GA. Qed.

Corollary XC4'_swap': forall (g : ZZ), g .* (X' ij a1) .* (X' ik a2) = g .* (X' ik a2) .* (X' ij a1).
intros. by rewrite GA XC4'_swap ?GA. Qed.

Corollary XC5_swap: (X' ij a1) .* (X' kl a2) =  (X' kl a2) .* (X' ij a1).
rewrite {1}swap_comm comm_d1 -X'Inv. cancel. by rewrite /conj -X'Inv {2}/X' Z2 ZC5. Qed.

Corollary XC5_swap' g: g .* (X' ij a1) .* (X' kl a2) = g .* (X' kl a2) .* (X' ij a1).
by rewrite ?GA XC5_swap. Qed.



End S1.

Section ZC_tactic.
Ltac Z_guard :=
  match goal with
    | [ |- is_true (negb (eq_op ?X ?X)) ] => fail 1
    | [ |- is_true (negb (eq_op ?X ?Y)) ] => done
    | [ |- _ ] => idtac
  end.

Ltac safe_rw E := try (rewrite E; Z_guard).

Tactic Notation "safe_rw4" reference(F1) "," reference(F2) "," 
                           reference(F3) "," reference(F4) :=
  safe_rw F1; safe_rw F2; safe_rw F3; safe_rw F4.

Ltac pure_ZC :=
           safe_rw4 XC2,  ZC2,  XC3, ZC3;
           safe_rw4 XC3', ZC3', XC4, ZC4;
           safe_rw4 XC4', ZC4', XC5, ZC5;
           rewrite ?forward_rule ?identity_rule; rsimpl; cancel.
Ltac ZCR0 := repeat pure_ZC.

Lemma X0: X' ij a1 .* X' ij a2 = X' ij (a1 + a2).
Proof. by rewrite /X' Z0. Qed.


End ZC_tactic.

