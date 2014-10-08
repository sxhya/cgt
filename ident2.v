Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident.
Import Ring.RingFacts.

Definition conj' := locked conj.
Notation "h ^^ g" := (conj' h g) (at level 11, left associativity).

Parameter Z': forall {i j : nat} (p : i != j) (a : I) (r : R), ZZ.

Definition X' {i j : nat} (p : i != j) r := Z' p r (0).

(* We assume that rank is at least 3 *)

Axiom fresh2: forall (i j : nat), exists k, k!=i /\ k!=j.
Axiom fresh3: forall (i j k : nat), exists l, l!=i /\ l!=j /\ l!=k.

Module ZC_Rules.
Section Axioms.
Context (i j k l : nat) {a a1 a2 : I} (b c : R).

(* Definition of the action of the Steinberg group on relative generators *)
(* Don't use it 
Axiom ZC1: forall (ij : i!=j) (jk : j!=k) (ik : i!=k) (ji : j!=i) (kj : k!=j) (ki : k!=i), 
      Z' ij a b ^^ X ij c =
      X' ji (- b *_ a _* b) ^^ X ik (- c * b - 1)       .*
                     Z' ki (a _* b) (- c * b - 1)       .*
      X' ij ((c * b + 1) *_ a _* (b * c + 1)) ^^ X jk b .* 
                             Z' kj (a _* (b * c + 1)) b .*
      X' kj (-_ a) .* X' ki (-_ a _* b) ^^ X ij c. *)

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
End Axioms.
End ZC_Rules.

(* Definition of Relations between relative generators *)

Module AxiomLevel0.
Axiom Z0: forall (i j : nat) a1 a2 b (ij : i!=j), Z' ij (a1 _+_ a2) b = Z' ij a1 b .* Z' ij a2 b. 
End AxiomLevel0.

Module AxiomLevel1. Export AxiomLevel0 ZC_Rules.
Axiom Z2: forall (i j k l : nat) a a1 b (ij : i!=j) (kl : k!=l), 
      (X' kl (-_a1) .* Z' ij a b .* X' kl a1) = Z' ij a b ^^ X kl a1. 
End AxiomLevel1.

Module AxiomLevel2. Export AxiomLevel1.
Axiom Z1: forall (i j k l : nat) a1 a2 b c {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
                 {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j},
          Z' ij a1 b .* Z' kl a2 c = Z' kl a2 c .* Z' ij a1 b.
End AxiomLevel2.

Module AxiomLevel3. Export AxiomLevel2.
Axiom Z3R': forall i j k a b c (ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i),
       (X' kj a ^^ X ik (- b)) ^^ X ji c =
      ((X' kj a ^^ X ji c) ^^ X ik (- b)) ^^ X jk (c * b).
End AxiomLevel3.

Section BasicLemmata. Import AxiomLevel0.

Context (i j : nat) (a : I) (ij : i!=j).

Lemma Z'zero: forall b, Z' ij 0 b = Id.
intros. apply (GCr (Z' ij 0 b)). rewrite -Z0. by rewrite IdG; rsimpl. Qed.

Lemma Z'Inv: forall b, Z' ij (-_a) b = (Z' ij a b)^-1.
intros. apply (GCr (Z' ij a b)). by rewrite -Z0 inv_l' IG Z'zero. Qed.

Lemma X'def: Z' ij a 0 = X' ij a.  done. Qed.

Lemma X'zero: X' ij 0 = Id. 
by rewrite /X' Z'zero. Qed.

Lemma X'Inv: X' ij (-_a) = (X' ij a)^-1. 
by rewrite /X' Z'Inv. Qed.

End BasicLemmata.

Section XCorollaries. Import AxiomLevel1.

Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.

Ltac ZX E := rewrite /X'; rewrite E; rewrite /X'; rsimpl; rewrite ?Z'zero; cancel.

Lemma X0: X' ij a1 .* X' ij a2 = X' ij (a1 _+_ a2). by ZX Z0. Qed.

Lemma X1: X' ij a ^^ X ji b = Z' ij a b. by rewrite /X' ZC2 ?X'def plus_0_l. Qed.

Corollary X0': forall (g : ZZ), g .* X' ij a1 .* X' ij a2 = g .* X' ij (a1 _+_ a2).
intros. by rewrite GA -X0. Qed.

(* For XC1 see below *)
Corollary XC2: (X' ij a) ^^ (X ji c) = Z' ij a c.
by move: (@ZC2 i j a (0) c ij ji) => /=; rewrite /X' plus_0_l => ->. Qed.

Corollary XC3: (X' ij a) ^^ (X jk c) = X' ik (a _* c) .* X' ij a.
by ZX ZC3. Qed.

Corollary XC3': (X' ij a) ^^ (X ki c) = X' kj (-_ (c *_ a)) .* X' ij a.
by ZX ZC3'. Qed.

Corollary XC4: (X' ij a) ^^ (X kj c) = X' ij a. 
by ZX ZC4. Qed. 

Corollary XC4': (X' ij a) ^^ (X ik c) = X' ij a. 
by ZX ZC4'. Qed.

Corollary XC5: (X' ij a) ^^ (X kl c) = X' ij a. 
by ZX ZC5. Qed.

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

End XCorollaries.

Section SwapLemmata. Export AxiomLevel1.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {kl : k != l} {il : i != l} {jl : j != l}
        {ji : j != i} {ki : k != i} {kj : k != j} {lk : l != k} {li : l != i} {lj : l != j}.
          
Corollary XC1: (X' ij a) ^^ (X ij c) = X' ij (a). Admitted.
(* Proof involves certain facts which are disallowed in current setting*)
(* rewrite (@ZC1 i j k a (0) c)//; rsimpl;
rewrite ?Z'zero ?X'zero ?X'def Xzero conjId //; cancel.
by rewrite X0' inv_r' X'zero GId. Qed. *)

Corollary ZC3_swap: (Z' ij a b) .* (X' jk a1) =
 (X' jk ((1 - b * a) *_ a1)) .* X' ik (a _* a1) .* Z' ij a b.
apply (GCl (X' jk (-_a1))). rewrite -?GA.
by rewrite Z2 X0 dist_r'; rsimpl; rewrite -plus_assoc' inv_l' ZC3; rsimpl. Qed.

Corollary ZC3_swap' g: g .* (Z' ij a b) .* (X' jk a1) =
 g .* (X' jk ((1 - b * a) *_ a1)) .* X' ik (a _* a1) .* Z' ij a b.
by rewrite GA ZC3_swap ?GA. Qed.

Corollary ZC4'_swap: (Z' ij a b) .* (X' ik a1) = 
 X' ik (a1 _+_ a * b *_ a1) .* X' jk (-_ (b * a * b *_ a1)) .* Z' ij a b.
apply (GCl (X' ik (-_a1))). rewrite -X0; cancellate.
by rewrite Z2 ZC4' X0 X0 XC4_swap // inv_l' plus_0_l'; rsimpl. Qed.

Corollary ZC4'_swap' g: g .* (Z' ij a b) .* (X' ik a1) = 
g .* X' ik (a1 _+_ a * b *_ a1) .* X' jk (-_ (b * a * b *_ a1)) .* Z' ij a b.
by rewrite GA ZC4'_swap ?GA. Qed.

Corollary ZC3'_swap: (Z' ij a b) .* (X' ki a1) = 
 (X' ki a1) .* X' ki (-_ (a1 _* a _* b)) .* X' kj (-_ (a1 _* a)) .* Z' ij a b.
apply (GCl (X' ki (-_a1))). cancellate.
by rewrite X0 inv_l' X'zero IdG Z2 ZC3'; rsimpl. Qed.

Corollary ZC3'_swap' g: g .* (Z' ij a b) .* (X' ki a1) = 
 g .* (X' ki a1) .* X' ki (-_ (a1 _* a _* b)) .* X' kj (-_ (a1 _* a)) .* Z' ij a b.
by rewrite GA ZC3'_swap ?GA. Qed.

Corollary ZC4_swap:
 (Z' ij a b) .* (X' kj a1) =
 (X' kj a1) .* X' ki (a1 _* b _* a _* b) .* X' kj (a1 _* b _* a) .* Z' ij a b.
apply (GCl ((X' kj (-_a1)))). cancellate.
by rewrite Z2 ZC4 X0 inv_l' X'zero IdG; rsimpl. Qed.

Corollary ZC4_swap' g:
 g .* (Z' ij a b) .* (X' kj a1) =
 g .* (X' kj a1) .* X' ki (a1 _* b _* a _* b) .* X' kj (a1 _* b _* a) .* Z' ij a b.
by rewrite GA ZC4_swap ?GA. Qed.

Corollary ZC5_swap:
 (Z' ij a b) .* (X' kl a1) = (X' kl a1) .* (Z' ij a b).
apply (GCl (X' kl (-_a1))). rewrite -?GA; cancellate.
by rewrite Z2 ZC5 // X0 inv_l' X'zero IdG. Qed.

Corollary ZC5_swap' g: 
 g .* (Z' ij a b) .* (X' kl a1) = g .* (X' kl a1) .* (Z' ij a b).
by rewrite ?GA ZC5_swap. Qed.

End SwapLemmata.

Module ZC_tactic. Export ZC_Rules.

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

Axiom forward_rule: forall h1 h2 g, conj' (h1 .* h2) g = (conj' h1 g) .* (conj' h2 g). 
Axiom identity_rule: forall h, conj' Id h = Id.

Ltac pure_ZC :=
           safe_rw4 XC2,  ZC2,  XC3, ZC3;
           safe_rw4 XC3', ZC3', XC4, ZC4;
           safe_rw4 XC4', ZC4', XC5, ZC5;
           rewrite ?forward_rule ?identity_rule; rsimpl; cancel.
Ltac ZCR0 := repeat pure_ZC.

End ZC_tactic.

Section Z0_ZC. Import ZC_tactic AxiomLevel1.
Context (i j k : nat) (a a1 a2 : I) (b c : R)
(ij : i != j) (ik : i != k) (jk : j != k) (ji : j != i) (ki : k != i) (kj : k != j).

(* Boilerplate lemmata about preservation of Relation Z0 *)

Lemma Z0_ZC2: (Z' ij (a1 _+_ a2) b) ^^ (X ji c) = (Z' ij (a1) b) ^^ (X ji c) .* (Z' ij (a2) b) ^^ (X ji c).
ZCR0. by rewrite Z0. Qed.

Lemma Z0_ZC3: (Z' ij (a1 _+_ a2) b) ^^ (X jk c) = (Z' ij (a1) b) ^^ (X jk c) .* (Z' ij (a2) b) ^^ (X jk c).
ZCR0. 
rewrite -?X'Inv; rexpand; rewrite -?X0 Z0; bite.
rewrite XC4_swap //; bite.
rewrite ZC3_swap //; rexpand; rsimpl; rewrite -X0; bite.
rewrite ZC4'_swap' // X0' XC4_swap // plus_comm' plus_assoc'.
rsimpl. rewrite inv_r' plus_0_r'. bite.
by rewrite X0 inv_r' X'zero IdG. Qed.

Lemma Z0_ZC3': (Z' ij (a1 _+_ a2) b) ^^ (X ki c) = (Z' ij a1 b) ^^ (X ki c) .* (Z' ij a2 b) ^^ (X ki c).
ZCR0. 
rewrite -?X'Inv; rexpand; rewrite -X0 Z0. bite.
rewrite XC4'_swap // -X0; bite.
rewrite ZC3'_swap // XC4'_swap //. bite. 
rewrite ZC4_swap' ?X0'. bite.
rewrite ?X0' XC4'_swap' ?X0' // XC4'_swap // plus_comm' -?plus_assoc'.
rsimpl. by rewrite inv_l' plus_0_l' ?X0' inv_r' X'zero GId. Qed.

Lemma Z0_ZC4: (Z' ij (a1 _+_ a2) b) ^^ (X kj c) = (Z' ij a1 b) ^^ (X kj c) .* (Z' ij a2 b) ^^ (X kj c).
ZCR0. 
rexpand. rewrite -X0 Z0. bite.
rewrite XC4'_swap // -X0. bite.
rewrite ZC3'_swap // X0.
rewrite ZC4_swap' // X0'. bite. rsimpl.
rewrite XC4'_swap // -X0. bite.
by rewrite XC4'_swap // X0' inv_l' X'zero GId X0 plus_comm'
        -?plus_assoc' inv_r' plus_0_l'. Qed.

Lemma Z0_ZC4' : (Z' ij (a1 _+_ a2) b) ^^ (X ik c) = (Z' ij a1 b) ^^ (X ik c) .* (Z' ij a2 b) ^^ (X ik c).
ZCR0. 
rewrite -?X'Inv. rexpand. rewrite -X0 Z0. bite.
rewrite XC4_swap // -X0. bite.
rewrite ZC3_swap // ZC4'_swap' // ?X0'. bite.
rewrite XC4_swap' // X0 XC4_swap //. rexpand. rsimpl.
rewrite plus_assoc' inv_r'  plus_0_r' (plus_comm' (a2 _* b _* c)) -plus_assoc'. rsimpl.
by rewrite inv_l' plus_0_l'. Qed.

Context (l : nat) (il : i != l) (li : l != i) (jl : j != l) (lj : l != j) (kl : k != l) (lk : l != k).

Lemma Z0_ZC5: (Z' ij (a1 _+_ a2) b) ^^ (X kl c) = 
              (Z' ij (a1) b) ^^ (X kl c) .* (Z' ij (a2) b) ^^ (X kl c).
by rewrite ?ZC5 // Z0. Qed.

Import AxiomLevel3.

(* This is not that simple *)
Lemma Z0_ZC1: (Z' ij (a1 _+_ a2) b) ^^ (X ij c) =  (Z' ij (a1) b) ^^ (X ij c) .* (Z' ij (a2) b) ^^ (X ij c).
rewrite ?(ZC1 _ _ k) //.
 + rewrite dist_r'' -X0. bite.
 + rewrite {1}dist_r'' -X0 -?GA XC4'_swap //. bite. 
Abort.

End Z0_ZC.

Section Z2_ZC. Import ZC_tactic AxiomLevel2.

(* Ltac ZC := rewrite -?X'Inv -?Z'Inv ?XC1; pure_ZC;
           rewrite ?X'def ?X'Inv ?Z'Inv; rsimpl;
           rewrite ?Z'zero ?X'zero -?GA; cancel.

Ltac ZCR := repeat ZC. *)

Context (i j k l m n : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}

        {mi : m != i}  {mj : m != j} {mk : m != k} {ml : m != l}
        {im : i != m}  {jm : j != m} {km : k != m} {lm : l != m}

        {ni : n != i}  {nj : n != j} {nk : n != k} {nl : n != l} {nm : n != m}
        {in' : i != n} {jn : j != n} {kn : k != n} {ln : l != n} {mn : m != n}.

(* Preservation of Z2 (ZC5 flavour) *)

Lemma Z2_00: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X ji c) = (Z' ij a1 b ^^ X kl a2) ^^ (X ji c).
ZCR0. by rewrite X'def ZC5_swap' // X0 inv_l' X'zero IdG. Qed.

Import AxiomLevel3.

Lemma Z2_00': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X lk c) = (Z' ij a1 b ^^ X kl a2) ^^ (X lk c).
Abort.

Lemma Z2_00'': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X kl c) = (Z' ij a1 b ^^ X kl a2) ^^ (X kl c).
ZCR0. by rewrite ?XC1 (ZC5_swap' i j) // ?X'Inv; cancel. Qed.

(* This proof assumes rk >= 4, which is likely to be superfluous; check this later*)
Lemma Z2_00''': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X ij c) = (Z' ij a1 b ^^ X kl a2) ^^ (X ij c).
ZCR0. rewrite ?(ZC1 _ _ m) //. ZCR0. rsimpl. rewrite -?GA.
do 2(repeat (rewrite ?(XC5_swap k l) ?(XC5_swap' k l)//); rewrite -(ZC5_swap' _ _ k l) //). 
by rewrite X0' inv_l' X'zero GId. Qed.

Lemma Z2_04: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X ik c) = (Z' ij a1 b ^^ X kl a2) ^^ (X ik c).
ZCR0. rewrite ?X'zero ?IdG -?GA ?X'def.
rewrite XC4_swap //.
rewrite (XC5_swap' i l j k) //.
rewrite (XC4'_swap' i l k) //.
rewrite ZC4'_swap' // X0'; rsimpl; rewrite -plus_assoc' inv_r' plus_0_l'.
rewrite ZC5_swap' //; bite.
rewrite (XC4_swap' j l k) //.
rewrite (XC4_swap' i l k) //.
rewrite (ZC3_swap' i k l) //; rsimpl.
rewrite X'def (ZC3_swap' j k l) //; rsimpl; rewrite X'def ?X'Inv; cancel.
rewrite -?X'Inv (XC4'_swap' i l k) // X0' inv_r' X'zero GId.
rewrite XC4'_swap //.
by rewrite (XC5_swap' j l i k) // X0' inv_l' X'zero GId. Qed.

Lemma Z2_04': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X il c) = (Z' ij a1 b ^^ X kl a2) ^^ (X il c).
ZCR0. by rewrite ?X'zero ?IdG -?GA ?X'def XC4_swap // ZC5_swap' //
         (XC4_swap' i l k) // X0' inv_l' X'zero GId; rsimpl. Qed.

Lemma Z2_04'': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X ki c) = (Z' ij a1 b ^^ X kl a2) ^^ (X ki c).
ZCR0. by rewrite ?X'zero ?IdG -?GA ?X'def XC4'_swap // ZC5_swap' //
              (XC4'_swap' k j l) // X0' inv_l' X'zero GId. Qed.

Lemma Z3_04''': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X li c) = (Z' ij a1 b ^^ X kl a2) ^^ (X li c).
ZCR0. rewrite ?X'zero ?IdG -?GA ?X'def.
rewrite XC4'_swap //.
rewrite (ZC3'_swap' i j k) //.
rewrite (XC4_swap' k i l) //.
rewrite (XC5_swap' k i l j) // ?X0' -plus_assoc' inv_l' plus_0_l'.
rewrite (ZC5_swap' i j k l) //.
rewrite (XC4'_swap' k j l) //.
rewrite (XC4'_swap' k i l) //.
rewrite (ZC3'_swap' l j k) //; rsimpl; rewrite X'zero X'def GId.
rewrite (XC4'_swap' k i j) // (XC4_swap' k j l) // X0' inv_r' X'zero GId.
rewrite ZC3_swap //; rsimpl; rewrite X'def X0' inv_l' X'zero GId.
by rewrite (XC5_swap' k i l j) // X0'; rsimpl; rewrite inv_r' X'zero GId. Qed. 

Lemma Z2_05: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X jk c) = (Z' ij a1 b ^^ X kl a2) ^^ (X jk c).
ZCR0. rewrite ?X'zero ?IdG -?GA ?X'def.
rewrite XC4_swap //.
rewrite (ZC3_swap' i j l) //. 
rewrite (XC4'_swap' j l k) //.
rewrite (XC5_swap' i k j l) // ?X0'; rexpand; rsimpl; rewrite -plus_assoc' inv_r' plus_0_l'.
rewrite (ZC5_swap' i j k l) //.
rewrite (XC4_swap' i l k) //; bite.
rewrite (ZC3_swap' i k l) //; rsimpl; rewrite X'def.
rewrite (XC4'_swap' i k l) // X0' inv_r' X'zero GId; bite.
rewrite (XC4_swap' j l k) // (ZC3_swap' j k l) //; rsimpl; rewrite X'def.
by rewrite (XC4'_swap' j k l) // X0 ?X0' ?inv_l' ?X'zero ?IdG. Qed.

Lemma Z2_05': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X jl c) = (Z' ij a1 b ^^ X kl a2) ^^ (X jl c).
ZCR0. by rewrite ?X'zero ?IdG -?GA ?X'def XC4_swap // ZC5_swap' //
         (XC4_swap' i l k) // X0' inv_l' X'zero GId; rsimpl. Qed.

Lemma Z2_05'': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X kj c) = (Z' ij a1 b ^^ X kl a2) ^^ (X kj c).
ZCR0. by rewrite ?X'zero ?IdG -?GA ?X'def XC4'_swap // ZC5_swap' //
              (XC4'_swap' k j l) // X0' inv_l' X'zero GId. Qed.

(* Proof should be the same as above *)
Lemma Z3_05''': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X lj c) = (Z' ij a1 b ^^ X kl a2) ^^ (X lj c).
ZCR0. rewrite ?X'zero ?IdG -?GA ?X'def.
rewrite XC4'_swap //.
rewrite (ZC4_swap' i j k) //.
rewrite (XC5_swap' k j l i) //.
rewrite (ZC3_swap k l i) //; rsimpl; rewrite X'def; bite.
rewrite (XC4_swap' k j l) // X0' inv_l' X'zero GId.
rewrite (ZC3_swap' k l j) //; rsimpl; rewrite X'def.
rewrite XC5_swap //; bite.
rewrite ZC5_swap' //.
rewrite (XC4'_swap' k l i) //.
rewrite (XC4'_swap' k j i) // X0 inv_l' X'zero IdG.
rewrite (XC4'_swap' k l j) //. by do 2 rewrite X0 inv_l' X'zero IdG. Qed.

Lemma Z2_01: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X mn c) = (Z' ij a1 b ^^ X kl a2) ^^ (X mn c).
ZCR0. by rewrite GA ZC5_swap // -GA X'Inv; cancel. Qed.

Lemma Z2_02: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X jm c) = (Z' ij a1 b ^^ X kl a2) ^^ (X jm c).
ZCR0. by rewrite -?GA -?X'Inv (ZC5_swap' i j) // -?(XC5_swap' k l) // ?X'Inv; cancel. Qed.

Lemma Z2_02': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X im c) = (Z' ij a1 b ^^ X kl a2) ^^ (X im c).
ZCR0. rewrite -?GA -?X'Inv. repeat (rewrite (XC5_swap k l) //; bite). rewrite ?X'def Z2. by ZCR0. Qed.

Lemma Z2_02'': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X mj c) = (Z' ij a1 b ^^ X kl a2) ^^ (X mj c).
ZCR0. by rewrite -?GA -?X'Inv ?X'def (ZC5_swap' i j) // -?(XC5_swap' k l) // ?X'Inv; cancel. Qed.

Lemma Z2_02''': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X mi c) = (Z' ij a1 b ^^ X kl a2) ^^ (X mi c).
ZCR0. by rewrite -?GA -?X'Inv ?X'def (ZC5_swap' i j) // -?(XC5_swap' k l) // ?X'Inv; cancel. Qed.
 
Lemma Z2_03: (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X km c) = (Z' ij a1 b ^^ X kl a2) ^^ (X km c).
ZCR0. rewrite ?X'zero X'def; cancel. rewrite Z2. by ZCR0. Qed.

Lemma Z2_03': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X lm c) = (Z' ij a1 b ^^ X kl a2) ^^ (X lm c).
ZCR0. rewrite ?X'zero X'def -?GA; cancel. do 2 rewrite ZC5_swap' //.
by rewrite (XC4'_swap' k l m) // ?X0 ?X0' ?inv_l' ?X'zero ?IdG. Qed.

Lemma Z2_03'': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X mk c) = (Z' ij a1 b ^^ X kl a2) ^^ (X mk c).
ZCR0. rewrite ?X'zero X'def -?GA; cancel. do 2 rewrite ZC5_swap' //.
by rewrite (XC4_swap' k l m) // ?X0 ?X0' inv_r' inv_l' ?X'zero ?IdG. Qed. 

Lemma Z2_03''': (X' kl (-_a2) .* Z' ij a1 b .* X' kl a2) ^^ (X ml c) = (Z' ij a1 b ^^ X kl a2) ^^ (X ml c).
ZCR0. rewrite ?X'zero X'def -?GA; cancel. by rewrite (ZC5_swap' i j) // X0 inv_l' X'zero IdG. Qed.

(* Preservation of Z2 (ZC4 flavour) *)

(* no interaction -- simplest case *)
Lemma Z2_ZC4_00: (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X lm c = Z' ij a b ^^ X kj a1 ^^ X lm c.
ZCR0. by rewrite ?X'zero X'def GA ZC4_swap -?GA X0 inv_l' X'zero IdG; rsimpl. Qed.

(* 1 -- k *)
Lemma Z2_ZC4_01: (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X kl c = Z' ij a b ^^ X kj a1 ^^ X kl c.
ZCR0. rewrite ?X'zero ?X'def; cancel. by rewrite GA ZC4_swap -?GA X0 inv_l' X'zero IdG; rsimpl. Qed.

Lemma Z2_ZC4_01': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X lk c = Z' ij a b ^^ X kj a1 ^^ X lk c.
ZCR0. rewrite ?X'zero ?X'def; cancel. rewrite -?GA ZC4_swap' ZC4_swap'; rsimpl; bite.
rewrite XC4_swap // X0' inv_r' X'zero GId. rewrite (XC4_swap' l j k) //.
by rewrite (XC5_swap' l i k j) // X0 inv_l' X'zero IdG XC5_swap'. Qed.

Lemma Z2_ZC4_01'': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X il c = Z' ij a b ^^ X kj a1 ^^ X il c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel.
rewrite ZC4_swap'; bite. rewrite (XC5_swap' i l k j) //. rewrite (ZC3'_swap' j l) //; rsimpl.
rewrite X0 inv_l' ?X'zero GId IdG X'def. rsimpl; bite.
rewrite ZC3'_swap' //; rsimpl; rewrite ?X'zero XC5_swap // X'def GId; bite.
rewrite XC5_swap' //; bite. rewrite XC4_swap // ZC3'_swap' // X'def; rsimpl. bite.
rewrite X'zero GId XC4'_swap // X0'; rsimpl.
by rewrite inv_l' X'zero GId. Qed.

Lemma Z2_ZC4_01''': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X li c = Z' ij a b ^^ X kj a1 ^^ X li c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel.
rewrite ZC4_swap'; bite. rewrite (XC4_swap' l j k) // (XC5_swap' l j) // (XC4_swap' l j k) //; bite.
rewrite (XC4'_swap' k i j) // X0' (XC5_swap' l i) // X0 -plus_assoc' inv_l' plus_0_l'.
by rewrite XC4_swap' // XC4'_swap //; rsimpl. Qed.

Lemma Z2_ZC4_01'''': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X jl c = Z' ij a b ^^ X kj a1 ^^ X jl c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel.
rewrite ZC5_swap' //. rewrite ZC4_swap'. bite. rewrite (XC4'_swap' k i j) // X0'.
rewrite (XC4_swap' i l k) // (XC5_swap' i l) // (ZC3'_swap' i l) // ?X'def; bite.
rewrite X0' (XC4'_swap' k l j) //. rewrite (ZC3'_swap' j l k) //. rsimpl. 
rewrite X'zero GId X'def X0' -plus_assoc' inv_l' plus_0_l'.
rewrite (XC4_swap' j l k) // X0'. rewrite (XC5_swap' j l k i) //.
rewrite (XC4_swap' j l k) //. bite. rewrite (XC4'_swap' k i l) // X0'.
rewrite (XC4'_swap' k j l) // X0. rewrite (XC4'_swap k i l) //.
rewrite (XC4'_swap' k i j) //. bite. rewrite -?plus_assoc'.
rewrite (plus_assoc' (-_(a1 _*c))) (plus_comm' _ (a1 _* c)) -plus_assoc' inv_l' plus_0_l'.
rsimpl. rewrite -inv_mul' -dist_r''. rewrite -inv_mul''. rewrite -dist_r'.
rsimpl. by rewrite -inv_mul' -dist_r'' plus_assoc' inv_r' plus_0_r'. Qed. 

Lemma Z2_ZC4_01''''': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X lj c = Z' ij a b ^^ X kj a1 ^^ X lj c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel.
rewrite ZC4_swap'. bite.
rewrite (XC4'_swap' k i j) // X0'.
rewrite (XC4_swap' l j k) //.
rewrite (XC5_swap' l i k j) // X0 -plus_assoc' inv_l' plus_0_l'.
rewrite (XC5_swap' l j k i) //. bite.
rewrite (XC4_swap' l i) //. bite.
by rewrite (XC4'_swap k j) //; rsimpl. Qed.

(* ijk *)

(* OBSTACLE *)
Lemma Z2_ZC4_02: (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X ij c = Z' ij a b ^^ X kj a1 ^^ X ij c.
Abort.

Lemma Z2_ZC4_02': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X ji c = Z' ij a b ^^ X kj a1 ^^ X ji c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel. rewrite ZC3'_swap' //. rewrite ZC4_swap' //. bite.
rewrite ?X0' ?X0. rewrite (XC4'_swap' k j i) // ?X0'. rewrite (XC4'_swap' k j i) // ?X0 ?X0'.
rsimpl. rewrite -?plus_assoc' inv_l' plus_0_l'. collect.
rewrite -?inv_mul'. rewrite -dist_r'' (plus_comm b) (dist_l' a1).
rewrite -?inv_mul''. rewrite -dist_r'. rsimpl. rewrite -plus_assoc'.
rewrite inv_l' plus_0_l'. bite. rewrite pIp dist_r'.
by rewrite -?plus_assoc' (plus_assoc' _ a1) inv_l' plus_0_l'. Qed.

(* OBSTACLE *)
Lemma Z2_ZC4_02'': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X jk c = Z' ij a b ^^ X kj a1 ^^ X jk c.
ZCR0. rewrite ?X'zero ?X'def -?GA; cancel. Abort.

Lemma Z2_ZC4_02'': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X kj c = Z' ij a b ^^ X kj a1 ^^ X kj c.
ZCR0. rewrite ?XC1 ?X'zero ?X'def -?GA. ZCR0.
rewrite ZC4_swap'. bite. rewrite ?X0' XC4'_swap // X0' (plus_comm' _ a1) -plus_assoc' inv_l' plus_0_l'.
rewrite ?(XC4'_swap' k j i) ?X0' ?X0 //. rewrite plus_comm'. rsimpl. bite. by rewrite plus_comm'. Qed.

Lemma Z2_ZC4_02''': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X ki c = Z' ij a b ^^ X kj a1 ^^ X ki c.
ZCR0. rewrite ?XC1 ?X'zero ?X'def -?GA. ZCR0.
rewrite ZC4_swap'. bite. rewrite ?X0' XC4'_swap // X0' (plus_comm' _ a1) -plus_assoc' inv_l' plus_0_l'.
rewrite ?(XC4'_swap' k j i) ?X0' ?X0 //. rewrite plus_comm'. rsimpl. bite. by rewrite plus_comm'. Qed.

(* OBSTACLE *)
Lemma Z2_ZC4_02'''': (X' kj (-_a1) .* Z' ij a b .* X' kj a1) ^^ X ik c = Z' ij a b ^^ X kj a1 ^^ X ik c.
ZCR0. rewrite ?XC1 ?X'zero ?X'def -?GA; cancel. ZCR0.

(* Preservation of Z2 (ZC2 flavour) *)

Lemma Z2_06: (X' ji (-_a2) .* Z' ij a1 b .* X' ji a2) ^^ (X ji c) = (Z' ij a1 b ^^ X ji a2) ^^ (X ji c).
ZCR0. by rewrite ?XC1 Z2 ZC2 {1}plus_assoc (plus_comm c) -plus_assoc. Qed.

(* OBSTACLE *)
Lemma Z2_06': (X' ji (-_a2) .* Z' ij a1 b .* X' ji a2) ^^ (X ij c) = (Z' ij a1 b ^^ X ji a2) ^^ (X ij c).
ZCR0. rewrite ?(ZC1 _ _ m). rsimpl. rewrite -?GA.
rewrite ?ZC2 ?plus_0_l. Abort.

End Z2_ZC.

Lemma Z3R: forall i j k a b c(ij : i!=j) (jk : j!=k) (ik : i!=k) (ki : k!=i) (kj : k!=j) (ji : j!=i),
      Z' ij (b *_ a) c = (X' ji (-_ (c * b *_ a _* c)) .* X' ki (a _* c)) ^ X ik (- b) .*
      (X' ij (b *_ a) .* X' kj a) ^ X jk (c * b) .*
      X' kj (-_ a) .* X' ki (-_ (a _* c)). Admitted.

Section ActionCommutation1.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ACL01: (Z' ji a d ^^ X ik (b)) ^^ X ij (c) = (Z' ji a d ^^ X ij (c)) ^^ X ik (b).
ZCR. rewrite -?X'Inv. bite. rewrite X0. by collect. Qed.

Lemma ACL02: (Z' jk a d ^^ X ik (b)) ^^ X ij (c) = (Z' jk a d ^^ X ij (c)) ^^ X ik (b).
ZCR. rewrite -?X'Inv (XC4'_swap' i k j) // X0 X0' (XC4'_swap' i k j) // X0 X0'.
by do 2 (rewrite plus_comm'; bite). Qed.

Lemma ACL04 : (Z' kj a b ^^ X ik c) ^^ X jk d = (Z' kj a b ^^ X jk d) ^^ X ik c.
ZCR. by rewrite -?X'Inv X0; collect. Qed.

Lemma ACL05 : (Z' kj a b ^^ X ji c) ^^ X jk d = (Z' kj a b ^^ X jk d) ^^ X ji c.
ZCR. by rewrite -?X'Inv X0; collect. Qed.

End ActionCommutation1.

Section ActionCommutation2.
Context (i j k l : nat) {a a1 a2 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Corollary ACL01': (X' ji (a) ^^ X ik (b)) ^^ X ij (c) = (X' ji (a) ^^ X ij (c)) ^^ X ik (b).
by rewrite ACL01. Qed.

Corollary ACL02': (X' jk a ^^ X ik (b)) ^^ X ij (c) = (X' jk a ^^ X ij (c)) ^^ X ik (b).
by rewrite ACL02. Qed.

Lemma ACL03': (X' ij a ^^ X jk b) ^^ X ij c = (X' ij a ^^ X ij c) ^^ X jk b.
by ZCR. Qed.

Corollary ACL04' : (X' kj a ^^ X ik b) ^^ X jk c = (X' kj a ^^ X jk c) ^^ X ik b.
by rewrite ACL04. Qed.

Corollary ACL05' : (X' kj a ^^ X ji b) ^^ X jk c = (X' kj a ^^ X jk c) ^^ X ji b.
by rewrite ACL05. Qed.

End ActionCommutation2.

(* TODO: REFACTOR CODE THAT FOLLOWS THIS LINE *)

Section ActionCommutation3.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

(* Lemma Z3R'':
((X' kj a ^ X jk (-b * c)) ^ X ji b) ^ X ik (c) = (X' kj a ^ X ik c) ^ X ji b.
move: (@Z3R' i j k a (-c) b ij jk ik ki kj ji); rsimpl. move => ->. symmetry.
by rewrite {1}XC3 // 2!mul_conj -(ACL04' j i k) // 
           (ACL04' i j k)// -?mul_conj -(XC3 k j i) // ACL05. Qed.

Lemma Z3R''': Z' ij (b *_ a) c = ((X' kj a ^ X ji c) ^ X ik (- b)) ^ X jk (c * b) .* X' kj (-_ a) ^ X ji c.
move: (@Z3R' i j k a b c ij jk ik ki kj ji).
rewrite XC3' // XC3 // {1} mul_conj ; rsimpl.
rewrite X1. move /(GCr' ((X' kj a ^ (X ji c)) ^-1)). cancel.
move => ->. by rewrite -?conjI -?X'Inv -(XC3 k j i). Qed. *)

(* Lemma ACL1: (X' ji a1 ^^ X ik b) ^^ X ij c .* (X' ki a2 ^^ X ik b) ^^ X ij c = 
            (X' ji a1 ^^ X ij c) ^^ X ik b .* (X' ki a2 ^^ X ij c) ^^ X ik b.
by rewrite -?ACL01'. Qed.

Lemma ACL2: ((Z' ji a1 b) ^ X ik d) ^ X ij c .* X' kj a2 .* X' ki a3 = 
            ((Z' ji a1 b) ^ X ij c) ^ X ik d.
intros. by rewrite 4!mul_conj ACL01// -ACL02'// -ACL01'// -?mul_conj. Qed.

Lemma ACL4': ((X' ki a1 .* X' kj a2) ^ X ik c) ^ X jk b = 
             ((X' ki a1 .* X' kj a2) ^ X jk b) ^ X ik c.
intros. rewrite 4!mul_conj -ACL04' // -ACL04' //. Qed. *)

End ActionCommutation3.

Section ActionCommutation4.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

(* Lemma ACL3: (((X' ji a1 .* X' ki a2) ^^ X ik b) ^ X ij c) ^ (X ij d) =
             ((X' ji a1 .* X' ki a2) ^^ X ik b) ^ (X ij (c+d)).
intros.
by rewrite ACL1 // mul_conj X1 XC3// -GA ACL1 // ACL2//
 (mul_conj (X ij (c+d))) X1 XC3// ?(mul_conj (X ij d))
 ZC2 XC3// XC4// -2!GA X0'; collect. Qed.

Lemma ACL3': (((X' ij a1 .* X' kj a2) ^ X jk b) ^ X ij c) ^ X ij (d) = 
              ((X' ij a1 .* X' kj a2) ^ X jk b) ^ (X ij (c+d)).
intros. rewrite 4!mul_conj; do 3 rewrite ACL03'// (XC1 _ _ k)//.
apply GCl'. rewrite X1 2!ZC4 2!mul_conj ZC4' ZC4 (XC1 _ _ k)//; rsimpl.
by rewrite ?X'zero ?IdG ?X'def -2!GA XC4'_swap'// 
           X0' XC4'_swap// X0' XC4'_swap; collect. Qed. *)

End ActionCommutation4.

Section ActionCorrectness.

Context (i j k l : nat) {a a1 a2 a3 : I} {b c d : R} 
        {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j}.

Lemma ActionLemma1:
 (Z' ij a b ^^ X ij c) ^^ X ij d = Z' ij a b ^^ X ij (c+d).

rewrite ?(ZC1 _ _ k) //. ZCR. rewrite -?X'Inv -?Z'Inv. rsimpl.
rewrite ?X0' ?X0. collect. bite.

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