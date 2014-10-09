Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.
Import Ring.RingFacts.

Parameter ZZZ : Type.
Parameter X : forall {i j : nat} (ij : i!=j) (x : R), ZZZ.
Parameter conj1 : ZZ -> ZZZ -> ZZ.
Notation "h ^^ g" := (conj1 h g) (at level 11, left associativity).
Parameter Z': forall {i j : nat} (p : i != j) (a : I) (r : R), ZZ.
Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

Section Main.
Context (i j k l : nat) {a a1 a2 : I} (b c : R).

Axiom ZC1: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ji : j!=i) (kj : k!=j) (ki : k!=i), 
     Z' ij a b ^^ X ij c = 
     X' ki (a _* b) .*
     X' kj (a _* (b * c + 1)) .*
     X' kj (-_ (a _* (b * c + 1))) ^^ X jk (- b) ^^ X ik (c * b + 1) .*
     X' ki (-_ (a _* b))           ^^ X jk (- b) ^^ X ik (c * b + 1).

Axiom ZC2: forall (ij : i != j) (ji : j != i),
      (Z' ij a b) ^^ (X ji c) = Z' ij a (b + c).

Axiom ZC3: forall (ij : i != j) (jk : j != k) (ik : i != k) (ki : k != i) (ik : i != k),
      (Z' ij a b) ^^ (X jk c) = X' jk (-_ (b *_ a _* c)) .* X' ik (a _* c) .* Z' ij a b.

Axiom ZC3': forall (ij : i != j) (ik : i != k) (ki : k != i) (kj: k != j),
      (Z' ij a b) ^^ (X ki c) = X' ki (-_ (c *_ a _* b)) .* X' kj (-_(c *_ a)) .* Z' ij a b.

Axiom ZC4: forall (ij : i!=j) (kj : k!=j) (ki : k!=i),
      (Z' ij a b) ^^ (X kj c) = X' ki (c * b *_ a _* b) .* X' kj (c * b *_ a) .* Z' ij a b.

Axiom ZC4': forall (ij : i!=j) (jk : j!=k) (ik : i!=k),
      (Z' ij a b) ^^ (X ik c) = X' jk (-_ (b *_ a _* b _* c)) .* X' ik (a _* b _* c) .* Z' ij a b.

Axiom ZC5: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (il : i!=l) (jl : j!=l) (kl : k!=l),
      (Z' ij a b) ^^ (X kl c) = Z' ij a b.

(* Identites for Relative Steinberg group *)

Axiom Z0: forall (ij : i!=j), Z' ij (a1 _+_ a2) b = Z' ij a1 b .* Z' ij a2 b. 

Axiom Z2: forall (ij : i!=j) (ji : j!=i),
      Z' ji (-_ a2) c .* Z' ij a1 b ^^ X ij c .* Z' ji a2 c = Z' ij a1 (b + a2) ^^ X ij c.

Axiom Z4: forall (ij : i!=j) (kj : k!=j) (ik : i!=k), 
      (X' kj (-_ a1) .* Z' ij a b .* X' kj a1) ^^ X ik c = Z' ij a b ^^ X kj a1 ^^ X ik c.

Axiom Z5: forall (ij : i!=j) (kl : k!=l), i!=k -> i!=l -> j!=k -> j!=l ->
      Z' kl a1 b .* Z' ij a2 c = Z' ij a2 c .* Z' kl a1 b. 

End Main.