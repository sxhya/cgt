Require Import ssreflect.
Require Import Arith List Setoid BinPos BinNat Ring Relations.

(* Formalization of the notion of equivalence relation *)

Inductive eqv {Z} (R : relation Z) : Z -> Z -> nat -> Prop:=
  | Cl_base  : forall z1 z2, R z1 z2 -> eqv R z1 z2 0
  | Cl_swap  : forall z1 z2 n, eqv R z1 z2 n -> eqv R z2 z1 (S n)
  | Cl_step  : forall z1 z2 z3 n, eqv R z1 z2 n -> eqv R z2 z3 n -> eqv R z1 z3 (S n).

Implicit Arguments Cl_swap [[Z] [R] [z1] [z2] [n]].
Implicit Arguments Cl_base [[Z] [R] [z1] [z2]].
Implicit Arguments Cl_step [[Z] [R] [z1] [z2] [z3] [n]].

Lemma Reqv: forall {Z} {R : relation Z}, reflexive Z R -> 
forall n {z1 z2}, R z1 z2 -> eqv R z1 z2 n.
Proof. intros Z R Refl. induction n; intros. by apply Cl_base. intros. apply (@Cl_step Z R z1 z2).
apply IHn; apply H. rewrite /reflexive in Refl. by move: (IHn _ _ (Refl z2)). Qed.

Corollary eqv_plus: forall {Z} {R : relation Z}, reflexive Z R -> 
forall n' {z1 z2 n}, eqv R z1 z2 n -> eqv R z1 z2 (n+n').
Proof. intros Z R Refl. induction n'; intros. rewrite plus_0_r //.
rewrite -plus_Snm_nSm /=. rewrite /reflexive in Refl.
by move: (Cl_step (IHn' _ _ _ H) (Reqv Refl (n+n') (Refl z2))). Qed.

Inductive eq {Z} (R : relation Z) : relation Z :=
  | Cl: forall {n z1 z2}, eqv R z1 z2 n -> eq R z1 z2.

Implicit Arguments Cl [[Z] [R] [n] [z1] [z2]].

Lemma equiv_eq: forall Z R, reflexive Z R -> equiv Z (eq R).
intros Z R Refl. rewrite /equiv /reflexive /transitive /symmetric. 
intros; split; [| split]; intros. 
 + by move: (Cl ((Reqv Refl 0) (Refl x))).
 + inversion H. inversion H0. subst.
   apply (eqv_plus Refl) with (n':=n) in H4.
   rewrite plus_comm in H4. by move: (Cl (Cl_step (eqv_plus Refl n0 H1) H4)).
 + inversion H. subst. by move: (Cl (Cl_swap H0)). Qed.

(* Formalization of basic combinatorial group theory *)

Definition word (X : Type) := list (X * bool).

Notation "[ a ; .. ; b ]" := (a :: .. (b :: nil) ..).
Inductive eqg {X : Type} (P : word X -> Prop) : relation (word X) :=
 | Eq_nil  : eqg P nil nil
 | Eq_triv : forall x f, eqg P [(x, f); (x, negb f)] nil
 | Eq_rel  : forall w, P w -> eqg P w nil
 | Eq_cons : forall e y z, eqg P y z -> eqg P (e :: y) (e :: z).
Implicit Arguments Eq_rel [[X] [P] [w]].
Implicit Arguments Eq_cons [[X] [P] [y] [z]].

Definition eqgg {X} (P : word X -> Prop) := eq (@eqg X P).

Lemma app_left: forall X (P : word X -> Prop) z x y, eqgg P x y -> eqgg P (z++x) (z++y).
Proof. move => X P. elim => [|z zs H] x y //=.
rewrite /eqgg -?app_comm_cons => [[n z1 z2 A]]. apply Eq_cons.

(***************************)

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