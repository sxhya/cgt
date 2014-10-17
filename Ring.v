Require Import ssreflect ssrnat ssrbool seq eqtype.

Axiom I : Type.
Axiom R : Type.
Axiom embd : I -> R.
Coercion embd: I >-> R.


Module RingFacts.
Variable (plus mul : R -> R -> R) (inv : R -> R) (unit : R) (zero : I).

Notation "x + y" := (plus x y) : ring_scope.
Notation "x - y" := (plus x (inv y)) (at level 50, left associativity) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "0" := zero : ring_scope.
Notation "1" := unit : ring_scope.
Notation "- x" := (inv x) : ring_scope.

Open Scope ring_scope.

Axiom plus_assoc: forall a b c, (a + b) + c = a + (b + c).
Axiom mul_assoc: forall a b c, (a * b) * c = a * (b * c).

Axiom dist_l: forall a b c, a * (b + c) = (a * b) + (a * c).

Axiom dist_r: forall c a b, (a + b) * c = (a * c) + (b * c).

Axiom plus_comm: forall a b, a + b = b + a.

Lemma plus_comm0 a b g: g + a + b = g + b + a. 
by rewrite plus_assoc (plus_comm a) plus_assoc. Qed.

Lemma plus_comm1 a b g1: a + g1 + b = b + g1 + a.
by rewrite (plus_comm a) (plus_comm b) plus_comm0. Qed.

Lemma plus_comm1' a b g g1: g + a + g1 + b = g + b + g1 + a.
by rewrite ?plus_assoc -?(plus_assoc a) -?(plus_assoc b) plus_comm1. Qed.

Lemma plus_comm2 a b g1 g2: a + g1 + g2 + b = b + g1 + g2 + a.
by rewrite (plus_comm a) (plus_comm b) ?plus_assoc (plus_comm a) 
           (plus_comm b) ?plus_assoc (plus_comm a). Qed.

Lemma plus_comm2' a b g1 g2 g: g + a + g1 + g2 + b = g + b + g1 + g2 + a.
by rewrite ?(plus_assoc g) plus_comm2. Qed.

Axiom mul_1_r: forall a, a * 1 = a.
Axiom mul_1_l: forall a, 1 * a = a.

Axiom plus_0_r: forall a, a + 0 = a.
Axiom plus_0_l: forall a, 0 + a = a.

Axiom inv_r: forall a, a + (-a) = 0.
Axiom inv_l: forall a, (-a) + a = 0.

Lemma inv_l0 a g: g - a + a = g. 
by rewrite plus_assoc inv_l plus_0_r. Qed.
Lemma inv_r0 a g: g + a - a = g.
by rewrite plus_assoc inv_r plus_0_r. Qed.

Lemma canc_r a b c: a + b = a + c -> b = c.
intros. have: (-a+(a+b) = -a+(a+c)) by rewrite H.
by rewrite -?plus_assoc ?inv_l ?plus_0_l. Qed.

Lemma canc_l a b c: b + a = c + a -> b = c.
intros. have: ((b+a)+(-a)) = (c+a)+(-a) by rewrite H.
by rewrite ?plus_assoc ?inv_r ?plus_0_r. Qed.

Lemma mul_0_r a: a * 0 = 0.
apply (canc_r (a * 0)). by rewrite -dist_l ?plus_0_r. Qed.

Lemma mul_0_l a: 0 * a = 0.
apply (canc_l (0 * a)). by rewrite -dist_r ?plus_0_l. Qed.

Lemma inv_mul a b: -a * b = -(a * b).
apply (canc_r (a * b)). by rewrite -dist_r ?inv_r mul_0_l. Qed.

Lemma mul_inv a b: a * (-b) = -(a * b).
apply (canc_l (a * b)). by rewrite -dist_l ?inv_l mul_0_r. Qed.

Lemma invI a: -(-a) = a.
apply (canc_r (-a)). by rewrite inv_l inv_r. Qed.

Lemma inv_zero: -0 = 0.
apply (canc_l 0). by rewrite inv_l plus_0_r. Qed.

Lemma inv_plus a b: -(a + b) = -a + -b.
apply (canc_l (a + b)). 
 by rewrite inv_l (plus_comm a) ?plus_assoc -(plus_assoc (-b)) inv_l plus_0_l inv_l. Qed.

Ltac rsimpl := repeat rewrite                
               ?mul_0_r ?mul_0_l ?plus_0_l ?plus_0_r ?inv_zero
               ?mul_inv ?inv_mul ?mul_1_r ?mul_1_l -?mul_assoc ?invI.

Ltac collect := repeat rewrite -?inv_plus -?dist_l -?dist_r.

Ltac rexpand := repeat rewrite ?inv_plus ?dist_l ?dist_r.

Ltac cancm E := rewrite -?(plus_comm0 _ E) -?(plus_comm0 _ (-E)); progress (rewrite ?inv_r0 ?inv_l0).

End RingFacts.

Module CommRing. Export RingFacts.

Axiom mul_comm: forall a b, a * b = b * a.

End CommRing.

Module ideal.

Open Scope ring_scope. Export RingFacts.
Variable (plusI : I -> I -> I) (invsI : I -> I) (mulIR : I -> R -> I) (mulRI : R -> I -> I).

Notation "x _+_ y" := (plusI x y) (at level 50, left associativity)  : ring_scope.
Notation "x _-_ y" := (plusI x (invsI y)) (at level 50, left associativity): ring_scope.
Notation "x _* y" := (mulIR x y) (at level 40, left associativity) : ring_scope.
Notation "x *_ y" := (mulRI x y) (at level 41, right associativity) : ring_scope.
Notation "-_ x" := (invsI x) (at level 35, right associativity)  : ring_scope.

(* Ideal equalities *)

Axiom inI: forall x : I,  - embd x = (-_ x). 
Axiom pIp: forall x y : I, embd (x _+_ y) = x + y.
Axiom mIR: forall (x : I) (y : R), embd (x _* y) = x * y.
Axiom mRI: forall (x : I) (y : R), embd (y *_ x) = y * x.
Axiom mIR': forall (x : R) (y : I), embd (x *_ y) = x * y.
Axiom mRI': forall (x : R) (y : I), embd (y _* x) = y * x.

Axiom plus_assoc': forall a b c, (a _+_ b) _+_ c = a _+_ (b _+_ c).
Axiom mul_assoc': forall a b c, (a _* b) _* c = a _* (b * c).
Axiom mul_assoc'': forall a b c, (a * b) *_ c = a *_ (b *_ c).
Axiom mul_assoc''': forall a b c, (a *_ b) _* c = a *_ (b _* c).
Axiom mul_assoc'''': forall a b (c : I), a _* b _* c = a _* (b *_ c).
Axiom dist_l': forall a b c, a _* (b + c) = (a _* b) _+_ (a _* c).
Axiom dist_l'': forall c a b, a *_ (b _+_ c) = (a *_ b) _+_ (a *_ c).
Axiom dist_r': forall c a b, (a + b) *_ c = (a *_ c) _+_ (b *_ c).
Axiom dist_r'': forall c a b, (a _+_ b) _* c = a _* c _+_ b _* c.

Axiom plus_comm': forall a b, a _+_ b = b _+_ a.
Axiom mul_1_r': forall a, a _* 1 = a.
Axiom mul_1_l': forall a, 1 *_ a = a.
Axiom plus_0_r': forall a, a _+_ 0 = a.
Axiom plus_0_l': forall a, 0 _+_ a = a.
Axiom inv_r': forall a, a _+_ (-_a) = 0.
Axiom inv_l': forall a, (-_a) _+_ a = 0.

Axiom mul_0_r': forall a, a *_ 0 = 0.
Axiom mul_0_r'': forall a, a _* 0 = 0.
Axiom mul_0_l': forall a, 0 _* a = 0. 
Axiom mul_0_l'': forall a, 0 *_ a = 0. 
Axiom inv_mul': forall a b, -_a _* b = -_(a _* b).
Axiom inv_mul'': forall a b, (-a) *_ b = -_(a *_ b).
Axiom inv_mul''': forall a b, -_a *_ b = -_(a *_ b).
Axiom mul_inv': forall a b, a _* (-b) = -_(a _* b).
Axiom mul_inv'': forall a b, a _* (-_ b) = -_(a _* b).
Axiom mul_inv''': forall a b, a *_ (-_ b) = -_(a *_ b).

Axiom invI': forall a, -_(-_ a) = a.
Axiom inv_zero': -_0 = 0.
Axiom inv_plus': forall a b, -_(a _+_ b) = -_a _+_ -_b.
Axiom mIRRI: forall a b, (embd  a) *_ b = a _* (embd b).

Ltac rsimpl := (do 3 rewrite 
               ?inI -?pIp -?mIR -?mRI -?mIR' -?mRI'
               ?mul_0_r ?mul_0_l ?plus_0_l ?plus_0_r ?inv_zero
               ?mul_inv ?inv_mul ?mul_1_r ?mul_1_l -?mul_assoc ?invI
               ?mul_0_r' ?mul_0_l' ?mul_0_r'' ?mul_0_l'' ?plus_0_l' ?plus_0_r' ?inv_zero'
               ?mul_inv' ?inv_mul' ?mul_inv'' ?inv_mul'' ?mul_inv''' ?inv_mul''' 
               ?mul_1_r' ?mul_1_l' -?mul_assoc' -?mul_assoc'' -?mul_assoc''' -?mul_assoc'''' ?invI'); rewrite -?mIRRI.

Ltac collect := do 3 rewrite -?inv_plus' -?inv_plus -?dist_l -?dist_l' -?dist_l''
                -?dist_r -?dist_r' -?dist_r''.

Ltac rexpand := do 3 rewrite ?inv_plus' ?inv_plus ?dist_l ?dist_l' ?dist_l''
                 ?dist_r ?dist_r' ?dist_r''.

Axiom mul_comm': forall a (b : I), a _* b = b _* a.
Axiom mul_comm'': forall a b, a _* b = b *_ a.

End ideal.