Require Import ssreflect.
Require Import Arith List Setoid BinPos BinNat Ring Relations Bool.

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

Implicit Arguments Cl [[Z] [R] [z1] [z2]].

Lemma equiv_eq: forall Z R, reflexive Z R -> equiv Z (eq R).
intros Z R Refl. rewrite /equiv /reflexive /transitive /symmetric. 
intros; split; [| split]; intros. 
 + by move: (Cl 0 ((Reqv Refl 0) (Refl x))).
 + inversion H. inversion H0. subst.
   apply (eqv_plus Refl) with (n':=n) in H4.
   rewrite plus_comm in H4. by move: (Cl (S(n+n0)) (Cl_step (eqv_plus Refl n0 H1) H4)).
 + inversion H. subst. by move: (Cl (S n) (Cl_swap H0)). Qed.

(* Formalization of basic combinatorial group theory *)

Notation "[ a ; .. ; b ]" := (a :: .. (b :: nil) ..).

Definition word (X : Type) := list (X * bool).

Fixpoint invw {X: Type} (w : word X) :=
match w with
 nil => nil
 | (x, f) :: ws => (invw ws) ++ [(x, negb f)]
end.

Lemma invw_app: forall X (v w : word X), invw (v ++ w) = invw w ++ invw v.
Proof. intros X. elim => [|[x f] vs IH] w. by rewrite app_nil_l app_nil_r.
by rewrite -app_comm_cons /= app_assoc IH. Qed.

Lemma invw_involutive: forall X (w : word X), invw (invw w) = w.
Proof. intros X. elim => [|[x f] ws IH] //=. by rewrite invw_app /= negb_involutive IH. Qed.

Inductive eqg {X : Type} (P : word X -> Prop) : relation (word X) :=
 | Eq_nil  : eqg P nil nil
 | Eq_triv : forall x f w, eqg P ((x, f) :: (x, negb f) :: w) w
 | Eq_rel  : forall w, P w -> eqg P w nil
 | Eq_cons : forall e y z, eqg P y z -> eqg P (e :: y) (e :: z).

Implicit Arguments Eq_rel [[X] [P] [w]].
Implicit Arguments Eq_cons [[X] [P] [y] [z]].

Lemma eqg_plus: forall {X} {P : word X -> Prop} e {y z}, eqg P y z -> eqg P (e ++ y) (e ++ z).
Proof. move => X P. elim => [|e es IH] y z H //. rewrite -?app_comm_cons.
by move: (Eq_cons e (IH y z H)). Qed.

Corollary eqg_same: forall X (P : word X -> Prop) y, eqg P y y.
Proof. intros. rewrite -(app_nil_r y). by move: (eqg_plus y (Eq_nil P)). Qed.

Corollary eqg_reflexive: forall {X} (P : word X -> Prop), reflexive (word X) (eqg P).
Proof. rewrite /reflexive => X P x. apply eqg_same. Qed.

Definition eqgg {X} (P : word X -> Prop) := eq (@eqg X P).

Corollary eqgg_trans: forall {X} (P : word X -> Prop) {x} y {z}, 
  eqgg P x y -> eqgg P y z -> eqgg P x z.
Proof. rewrite /eqgg => X P x y z A B. 
move: (equiv_eq (word X) (eqg P) (eqg_reflexive P)) => [A1 [A2 A3]]. 
rewrite /transitive in A2. apply (A2 x y z). apply A. apply B. Qed.

Lemma eqv_cons: forall {X} {P : word X -> Prop} {n} e {y z},
 eqv (eqg P) y z n -> eqv (eqg P) (e :: y) (e :: z) n.
Proof. intros X P. induction n; intros; inversion_clear H; subst.
 + by move: (Cl_base (Eq_cons e H0)).
 + apply IHn with (e:=e) in H0. by move: (Cl_swap H0).
 + apply IHn with (e:=e) in H0. apply IHn with (e:=e) in H1.
   by move: (Cl_step H0 H1). Qed.

Corollary eqgg_plus: forall {X} {P : word X -> Prop} e {y z},
  eqgg P y z -> eqgg P (e ++ y) (e ++ z).
Proof. intros X P. induction e as [|e es]; intros.
 + by move: H.
 + rewrite -?app_comm_cons. apply IHes in H. inversion H. 
   subst. by move: (Cl n (eqv_cons e H0)). Qed.

Lemma eqg_inv: forall X (P : word X -> Prop) w, eqgg P (w ++ (invw w)) nil.
Proof. intros X P. apply (rev_ind (fun l => eqgg P (l ++ invw l) nil)).
 + by move: (Cl 0 (Cl_base (Eq_nil P))).
 + move => [x f] l. rewrite invw_app /=. apply (eqgg_trans P (l ++ invw l)).
   rewrite -app_assoc /=. by move: (Cl 0 (Cl_base (eqg_plus l (Eq_triv P x f (invw l))))). Qed.

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