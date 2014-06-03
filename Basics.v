Require Import ssreflect.
Require Import Arith List Setoid BinPos BinNat Ring Relations.

Definition word (X : Type) := list (X * bool).
Inductive eqg {X : Type} : relation (word X) :=
 | Eq_nil  : eqg nil nil
 | Eq_ins  : forall (x : X) f y z, eqg y z -> eqg ((x, f) :: (x, negb f) :: y) z
 | Eq_cons : forall e y z, eqg y z -> eqg (e :: y) (e :: z).

Inductive cl' {Z} (R : relation Z) : Z -> Z -> nat -> Prop:=
  | Cl_base0 : forall z1 z2, R z1 z2 -> cl' R z1 z2 0
  | Cl_step  : forall z1 z2 z3 n, cl' R z1 z2 n -> cl' R z2 z3 n -> cl' R z1 z3 (S n).

Lemma increase_n1: forall Z (R : relation Z), reflexive Z R -> 
forall n z1 z2, R z1 z2 -> cl' R z1 z2 n.
intros Z R Refl. induction n; intros. by apply Cl_base0. intros. apply (Cl_step R z1 z2).
apply IHn; apply H. rewrite /reflexive in Refl. by move: (IHn _ _ (Refl z2)). Qed.

Corollary increase_n: forall Z (R : relation Z), reflexive Z R -> 
forall z1 z2 n n', cl' R z1 z2 n -> cl' R z1 z2 (n+n').
intros Z R Refl. induction n'. rewrite plus_0_r //.
rewrite -plus_Snm_nSm /=. move => A. rewrite /reflexive in Refl. 
by move: (Cl_step R _ _ z2 _ (IHn' A) (increase_n1 Z R Refl (n+n') z2 z2 (Refl z2))). Qed.

Inductive cl {Z} (R : relation Z) : relation Z :=
  | Cl: forall z1 z2 n, cl' R z1 z2 n -> cl R z1 z2.

Lemma L1: forall Z R, reflexive Z R -> transitive Z (cl R).
intros Z R Refl. rewrite /equiv /reflexive /transitive. 
intros.
 + destruct H0. destruct H. 
   apply increase_n with (n':=n0) in H0. apply increase_n with (n':=n) in H.
   rewrite plus_comm in H. by move: (Cl _ _ _ _ (Cl_step _ _ _ _ _ H H0)). done. done. Qed.

Inductive term (X : Type) :=
 | Id : term X
 | Atom : X -> term X
 | Inv : term X -> term X
 | Exp : term X -> nat -> term X
 | Mul : term X -> term X -> term X
 | Conj : term X -> term X -> term X
 | Comm : term X -> term X -> term X.
Implicit Arguments Inv [[X]].

Notation "1" := Id : rel_presentation.
Arguments Scope Inv [rel_presentation].
Arguments Scope Exp [rel_presentation nat_scope].
Arguments Scope Mul [rel_presentation rel_presentation].
Arguments Scope Conj [rel_presentation rel_presentation].
Arguments Scope Comm [rel_presentation rel_presentation].

Notation "x * y" := (Mul x y) : rel_presentation.
Notation "x ^ y" := (Conj x y) : rel_presentation.
Notation "x ^-1" := (Inv x) (at level 29, left associativity) : rel_presentation.
Notation "x ^+ n" := (Exp x n) (at level 29, left associativity) : rel_presentation.
Notation "x ^- n" := (Inv (Exp x n)) (at level 29, left associativity) : rel_presentation.
Notation "[ ~ x1 , x2 , .. , xn ]" :=
  (Comm .. (Comm x1 x2) .. xn) : rel_presentation.