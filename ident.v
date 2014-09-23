Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group.

Module SteinbergGroup <: GroupCarrier.
Variable ZZ : Type.
End SteinbergGroup.

Module Import GF := Group.GroupFacts SteinbergGroup.
Module Import RF := Ring.RingFacts.
Import SteinbergGroup.

(* Reflection principle for (in)equality *)

CoInductive eqneq (m n : nat) : bool -> bool -> Set :=
 | Equal     of m == n : eqneq m n true false
 | Different of m != n : eqneq m n false true.

Lemma eqneqP m n: eqneq m n (m == n) (m != n).
  by case A0: eq_op; rewrite /negb; constructor; rewrite A0. Qed.

(*************************************************)

Definition swap_neq {i j : nat}: i != j -> j != i. by rewrite eq_sym.  Defined.

Axiom X: forall {i j : nat}, (i != j) -> R -> ZZ.

Axiom ST0: forall {i j : nat} (ij : (i != j)) r s, X ij (r + s) = X ij r .* X ij s.

Lemma Xzero: forall {i j : nat} (ij : (i != j)), X ij 0 = Id.
intros. apply (GCr (X ij 0)). by rewrite -{3}(plus_0_l 0) ST0 IdG. Qed.

Lemma ST0': forall {i j : nat} (ij : (i != j)) r, X ij (- r) = (X ij r) ^-1.
intros. apply (GCr (X ij r)). by rewrite -ST0 IG (inv_l) Xzero. Qed.

Lemma ST0'' {i j} a b (ij : i != j): X ij a ^ X ij b = X ij a.
expand. by rewrite -ST0' -?ST0 plus_comm -plus_assoc inv_r plus_0_l. Qed.

Axiom ST1: forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X ij r , X jk s ] = X ik (r * s).

Lemma ST1': forall {i j k : nat} (ij : (i != j)) (ik : (i != k)) (jk : (j != k)) r s,
 [~ X jk r , X ij s ] = X ik (- s * r).
intros. by rewrite -comm_inv ST1 -ST0' inv_mul. Qed.

Lemma ST1'' {i j k} a b (ik : i != k) (kj : k!= j) (ij : i!=j): 
 X ik a ^ X kj b = X ij (a * b) .* X ik a.
by rewrite conj_com -ST0' ST1' mul_inv inv_mul invI. Qed.

Lemma ST1''2 {i j k} a b {ij : i != j} {ki : k != i} (kj : k != j):
X ij a ^ X ki b = X kj (- (b * a)) .* X ij a.
by rewrite conj_com -ST0' ST1 inv_mul. Qed.

Axiom ST2: forall {i j k l : nat} (ij : (i != j)) (kl : (k != l)) r s, j != k -> i != l ->
 [~ X ij r, X kl s ] = Id.

Lemma ST2': forall {i j k} {ik : i != k} {jk : j != k} (ij : i != j) a b, X ik a ^ X jk b = X ik a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq ik). exact jk. Qed.

Corollary ST2'_swap: forall {i j k} {ik : i != k} {jk : j != k} (ij : i != j) a b, X ik a .* X jk b = X jk b .* X ik a.
intros. rewrite -{2}(ST2' ij a b). by cancellate. Qed.

Lemma ST2'': forall {i j k} {ki : k != i} {kj : k != j} (ij : i != j) a b, X ki a ^ X kj b = X ki a.
intros. rewrite conj_com -ST0' ST2. by rewrite IdG. exact (swap_neq kj). exact ki. Qed.

Corollary ST2''_swap: forall {i j k} {ki : k != i} {kj : k != j} (ij : i != j) a b, X ki a .* X kj b = X kj b .* X ki a.
intros. rewrite -{2}(ST2'' ij a b). by cancellate. Qed.

Lemma ST2''' {i j k l : nat} (ij : i != j) (kl : k != l) (jk : j != k) (il : i != l) r s:
 X ij r ^ X kl s = X ij r. rewrite conj_com -ST0' ST2. by rewrite IdG. by exact (swap_neq il). by exact (swap_neq jk). Qed.

(* These 2 axioms are needed to get rid of proof-relevant nature of parameter "p" of Z *) 

Axiom swapI : forall {i j : nat} (p : i != j), swap_neq (swap_neq p) = p.

Axiom irrelev : forall {i j : nat} (p q : i != j), p = q.



(* Tits relative generators z_{ij}(a, r) *)

Definition Z {i j : nat} (p : i != j) (r s : R) : ZZ := locked ((X p r) ^ (X (swap_neq p) s)).

Lemma Zdef {i j} (p : i!= j) r s: (X (p) r) ^ (X (swap_neq p) s) = Z p r s. by unlock Z. Qed.

Lemma Zdef'{i j} (p : i!= j) r s: (X (swap_neq p) r) ^ (X p s) = Z (swap_neq p) r s.
by unlock Z; rewrite swapI. Qed.

Lemma Zdef''{i j} {p : i != j} {q  : j != i} r s: (X p r) ^ (X q s) = Z p r s.
by rewrite /Z -lock (irrelev (swap_neq p) q). Qed.

Lemma Zadd {i j} (ij : i != j) (r s t : R): Z ij (r+s) t = Z ij r t .* Z ij s t.
unlock Z. by rewrite -mul_conj ST0. Qed. 

Lemma Zinv {i j} (ij : i != j) (r s : R): Z ij (-r) s = (Z ij r s)^-1.
by unlock Z; rewrite /conj ST0' ?GIM ?GA GII. Qed.

Lemma Zzero {i j} (ij : i != j) (s : R): Z ij s 0 = X ij s.
by rewrite /Z -?lock Xzero /conj IdI IdG GId. Qed.

Lemma Zd i j (ij : i!=j) (ji : j!=i) a b:
 X ji (- a) .* X ij b .* X ji a = Z ij b a.
by rewrite /Z -lock (irrelev (swap_neq ij) ji) /conj ST0'. Qed.

Lemma Zd' i j (ij : i!=j) (ji : j!=i) a b:
 X ji (a) .* X ij b .* X ji (-a) = Z ij b (-a).
move: (Zd i j ij ji (-a) b). by rewrite ?invI. Qed.

Corollary Zd2 i j (ij : i!=j) (ji : j!=i) a b g:
  g .* X ji (- a) .* X ij b .* X ji a = g .* Z ij b a.
by rewrite (GA g) GA Zd. Qed.

Corollary Zd2' i j (ij : i!=j) (ji : j!=i) a b g:
  g .* X ji (a) .* X ij b .* X ji (-a) = g .* Z ij b (-a).
move: (Zd2 i j ij ji (-a) b g). by rewrite ?invI. Qed.

Ltac collectZ := rewrite -?GA -?ST0' ?invI ?Zdef'' ?Zd2 ?Zd2' ?Zd ?Zd'.

Lemma ZX {i j} (ij : i!=j) a b: let ji := swap_neq ij in
Z ij a b .* X ij (-a) = X ji (- b) .* X ji b ^ X ij (- a).
by intros; rewrite /Z -?lock -/ji ST0' comm_d1'' comm_d2 GII -?ST0'. Qed.

Lemma ZX' {i j} (ij : i!=j) a b g: let ji := swap_neq ij in
g .* Z ij a b .* X ij (-a) = g .* X ji (- b) .* X ji b ^ X ij (- a).
intros. by rewrite ?(GA g) ZX. Qed.

Section S0.

Context (i j k l : nat) (a b c d : R) (ij : i != j) (ik : i != k) (jk : j != k)
                                      (kl : k != l) (il : i != l) (jl : j != l).
Let ji := (swap_neq ij). Let ki := (swap_neq ik). Let kj := (swap_neq jk).
Let lk := (swap_neq kl). Let li := (swap_neq il). Let lj := (swap_neq jl).

Lemma C3': (Z ij a b) ^ (X ki c) = X ki (- (c * a * b)) .* X kj (- (c * a)) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 //; cancel;
rewrite conj_mul ST1''2  mul_conj ST1'' Zdef; rsimpl. Qed.

End S0.

Section S1.
Context (i j k l : nat) (a b c d : R) (ij : i != j) (ik : i != k) (jk : j != k)
                                      (kl : k != l) (il : i != l) (jl : j != l).
Let ji := (swap_neq ij). Let ki := (swap_neq ik). Let kj := (swap_neq jk).
Let lk := (swap_neq kl). Let li := (swap_neq il). Let lj := (swap_neq jl).

(* Shorter and slicker relation taken from Petrov's Russian thesis (Lemma 7)*)

Lemma C1: (Z ij a b) ^ (X ij c) = 
   X kj (a * (b * c + 1)) .* X ki (a * b) .*
   X ik (- ((c * b + 1) * a * (b * c + 1) * b)) .* X ij ((c * b + 1) * a * (b * c + 1)) .* Z kj (- (a * (b * c + 1))) (- b) .*
   X jk (- (b * a * b * (c * b + 1))) .* X ji (- (b * a * b)) .* Z ki (- (a * b)) (c * b + 1).

rewrite /Z -lock -conj_mul -/ji. 
move: (ST1' ik ij kj a (-(1))); rsimpl => <-.
rewrite conj_mul comm_conj ST1'' ST1''2
        comm_conj ?mul_conj ST2'' // ST2' // ST1'' ST1''2; rsimpl.
rewrite ST2''_swap // ?GA -ST0 ST2'_swap // -GA -ST0 -{3}(mul_1_r a) mul_assoc -dist_l.
rewrite comm_d2 ?GIM -?ST0' inv_plus ?invI mul_conj {1}ST2''_swap //.
rewrite ?conj_mul Zdef'' ST1''2 ?mul_conj.
by rewrite ST1'' ?Zdef'' -(swapI ik) C3' ?swapI -?GA -?lock; rsimpl. Qed.

Lemma C1': (Z ij a b) ^ (X ij c) = 
  X ik ((c * b + 1) * a) .* X jk (- (b * a)) .*
  X ki (- ((b * c + 1) * b * a * b)) .* X ji (- (b * a * b)) .* Z jk (b * a) (- (b * c + 1)) .*
  X kj (b * (c * b + 1) * a * (b * c + 1)) .* X ij ((c * b + 1) * a * (b * c + 1)) .* Z ik (- ((c * b + 1) * a)) (- b).

rewrite /Z -lock -conj_mul -/ji.
move: (ST1 ik ij kj a 1). rsimpl. move => <-.
rewrite conj_mul comm_conj ST1'' ST1''2 comm_conj ?mul_conj ST2'' // ST2' // ST1'' ST1''2; rsimpl.
rewrite ST2''_swap // ?GA -ST0 ST2'_swap // -GA -ST0 -{2}(mul_1_l a) -dist_r.
rewrite comm_d2 ?GIM -?ST0' invI mul_conj {1}ST2''_swap //.
rewrite ?conj_mul 2!ST1'' ?mul_conj ST1''2 ?Zdef ST1''2.
by rewrite ?inv_mul ?mul_inv ?invI -?GA -?lock -?mul_assoc. Qed.

Lemma C2: (Z ij a b) ^ (X ji c) = (Z ij a (b + c)). by rewrite /Z -?lock -/ji -conj_mul ST0. Qed.

Lemma C3: (Z ij a b) ^ (X jk c) = X jk (- (b * a * c)) .* X ik (a * c) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 // 
           IdG conj_mul ST1'' mul_conj ST1''2 Zdef; rsimpl. Qed.

Lemma C4: (Z ij a b) ^ (X kj c) = X ki (c * b * a * b) .* X kj (c * b * a) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST1' GA 
        conj_mul ST1''2 ?mul_conj ?conj_mul ST0'' ST1'' ST2' // Zdef; rsimpl. Qed.

Lemma C4': (Z ij a b) ^ (X ik c) = X jk (- (b * a * b * c)) .* X ik (a * b * c) .* Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST1 GA
        conj_mul ST1'' ?mul_conj ?conj_mul ST0'' ST1''2 ST2'' // Zdef; rsimpl. Qed.

Lemma C5: (Z ij a b) ^ (X kl c) = Z ij a b.
by rewrite /Z -lock -/ji -conj_mul swap_comm ST2 // IdG 
           conj_mul (conj_com (X ij a)) -ST0' ST2// IdG Zdef. Qed.

End S1.

Corollary C10 i j k a b (ij : i!=j) (ik : i!=k) (jk : j!=k): 
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in

Z ij a b = X kj a .* X ki (a * b) .* X ik (- (a * b)) .* X ij a .* Z kj (- a) (- b)
.* X jk (- (b * a * b)) .* X ji (- (b * a * b)) .* Z ki (- (a * b)) 1.

intros. move: (C1 i j k a b 0 ij ik jk) => /=. rewrite -/ji -/ki -/kj; rsimpl.
rewrite ?Xzero. by rewrite /conj IdI IdG GId. Qed.

Corollary C1'0 i j k a b (ij : i!=j) (ik : i!=k) (jk : j!=k): 
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in

Z ij a b = X ik a .* X jk (- (b * a)) .* X ki (- (b * a * b)) .* X ji (- (b * a * b))
.* Z jk (b * a) (- (1)) .* X kj (b * a) .* X ij a .* Z ik (- a) (- b).

intros. move: (C1' i j k a b 0 ij ik jk) => /=. rewrite -/ji -/ki -/kj; rsimpl.
rewrite ?Xzero. by rewrite /conj IdI IdG GId. Qed.

(* Petrov's relation and its variations *)

Ltac rotate1 := rewrite ?GA; move /rotate; rewrite ?GA.
Ltac simplify := expand; rewrite -?Zinv -?ST0' ?invI -?GA; rsimpl.

(* Petrov relations can be deduced from the following 6-relation (which is not inside relative Steinberg subgroup) *)

Lemma SixRelation i j k a b c (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
X ki (- (b * c)) .* Z jk (c * a) b .* X ij (- (a * b)) .* Z ki (b * c) a
.* X jk (- (c * a)) .* Z ij (a * b) c = Id.

intros. move: (HallWitt'' (X ik (a)) (X ji c) (X kj b)).
rewrite -?ST0' ?invI. do 3 rewrite ST1' ST1''; rsimpl.
expand. conjugate_r (X jk (-(c*a))). collectZ. rewrite ?ST0'; cancel.
by rewrite -?ST0'. Qed.

(* =========================== *)

Lemma RG1 i j k a b c (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
let RHS := X jk (- (b * c * a * b)) .* X ik (a * b) .* X ji (- (b * c * a * b * c))
.* X ki (- (c * a * b * c)) .* Z kj (- (c * a)) (- b)
.* Z ik (- (a * b)) (- c) .* X kj (c * a) .* X ij a in
Z ij a (b * c) = RHS.  intros.
rewrite /Z -lock -/ji -(ST1 jk ji ki) /Comm ?conj_mul.

rewrite ST1'' (mul_conj (X ki c)) Zdef ST1''2 (mul_conj (X jk b ^-1)) -?ST0'.
rewrite -(swapI jk) C4 -/ji ?swapI -?mul_assoc
         (mul_conj (X jk (- b))) Zdef' -/kj ST1''. 

rewrite ?mul_conj ST2'// ST1'' C2 inv_r C4' Zdef ST1''2; rsimpl.
by rewrite Zzero ?ST0'; cancel; rewrite -?ST0' -?GA. Qed.

Lemma RG2 i j k a b c (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
let RHS := X ki (- (c * a * b * c)) .* X kj (- (c * a)) .* X ji (- (b * c * a * b * c))
.* X jk (b * c * a * b) .* Z ik (- (a * b)) (- c) .* Z kj (c * a) b
.* X ik (a * b) .* X ij a in 
Z ij a (b * c) = RHS. intros.
rewrite /Z -lock -/ji. 
move: (@ST1' j k i jk ji ki c (-b)). rewrite ?invI => <-. rewrite /Comm ?conj_mul.

rewrite ST1''2 mul_conj Zdef' -/kj ST1'' -?ST0' ?invI.
rewrite ?(mul_conj (X ki (-c))) C4' Zdef ST1''2.
rewrite ?mul_conj ST2''// ST1''2 -(swapI jk) C2 C4 ?swapI Zdef' ST1''.
by rsimpl; rewrite ?ST0'; cancel; rewrite -?ST0' inv_l Zzero -/kj -?GA. Qed.

(* ====== *)

Corollary RG1' i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = X jk (- (b * c * a * b)) .* X ik (a * b) .* (X ji (- (b * c * a * b * c))
.* X ki (- (c * a * b * c)) .* Z kj (- (c * a)) (- b)) .* Z ik (- (a * b)) (- c) .* X kj (c * a) .* X ij a. 
intros. by rewrite (RG1 i j k a b c) -/ji -/ki -/kj ?GA. Qed.

Corollary RG2' i j k a b c (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = X ki (c * a * b * c) .* X kj (c * a) .* X ji (- (b * c * a * b * c))
.* X jk (- (b * c * a * b)) .* Z ik (a * b) c .* Z kj (- (c * a)) (- b)
.* X ik (- (a * b)) .* X ij a.
intros. replace (b * c) with (-b * -c); [| by rsimpl]. 
by rewrite (RG2 i j k a (-b) (-c)) -/ji -/ki -/kj; rsimpl. Qed.

(* ====== *)

Corollary RG1'' i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = X ij a .* X kj (c * a) .* Z ik (- (a * b)) (- c) .* Z kj (- (c * a)) (- b)
.* X ki (- (c * a * b * c)) .* X ji (- (b * c * a * b * c)) .* X ik (a * b) .* X jk (- (b * c * a * b)).

intros. by rewrite -{1}(invI a) Zinv (RG1' i j k (-a) b c) -/ji -/ki -/kj; 
 expand; rewrite -?ST0' -?Zinv -?GA; rsimpl. Qed.

Corollary RG2'' i j k a b c: forall (ij : i!=j) (ik : i!=k) (jk : j!=k),
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a (b * c) = X ij a .* X kj (c * a) .* Z ik (- (a * b)) (- c) .* Z kj (- (c * a)) (- b)
.* X ki (- (c * a * b * c)) .* X ji (- (b * c * a * b * c)) .* X ik (a * b) .* X jk (- (b * c * a * b)).
intros. by rewrite -{1}(invI a) Zinv (RG1' i j k (-a) b c) -/ji -/ki -/kj; 
 expand; rewrite -?ST0' -?Zinv -?GA; rsimpl. Qed.

(* ====== *)

Corollary RG1bis i j k (a b c : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij (a * b) c =  X jk (- (c * a)) .* X ik a .* Z ik (- a) (- (b * c)) .* X kj (b * c * a * b)
               .* X ij (a * b) .* X ki (- (b * c * a * b * c)) .* X ji (- (c * a * b * c)) .* Z jk (c * a) (- b). 

intros. apply eqIdP'. rewrite ?GIM -?Zinv -?ST0' ?invI -?GA -?mul_inv.
by rewrite (RG1' i k j a b (-c)) ?swapI -/ji -/ki -/kj; rsimpl; rewrite ?ST0' ?Zinv ?GA; do 2 cancel. Qed.

Corollary RG2bis i j k (a b c : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij (a * b) c =  Z jk (- (c * a)) b .* X ij (a * b) .* X ik a .* Z ik (- a) (- (b * c))
.* X ji (- (c * a * b * c)) .* X jk (c * a) .* X ki (- (b * c * a * b * c)) .* X kj (- (b * c * a * b)). 

intros. move: (RG2' i k j a (-b) c ik ij kj) => /=; rewrite ?swapI -/ji -/ki -/kj -?GA ?Zinv; rsimpl.
move /eqIdP''; rewrite ?GIM -?ST0' -?Zinv ?invI. do 4 (move /rotate; rewrite ?GA). move /eqIdP => ->.
by rewrite ?GIM -?Zinv -?ST0' ?invI ?GA. Qed.

(* ====== *)

Corollary R12 i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = X jk (- (b * a)) .* X ik a .* Z ik (- a) (- b) .* X kj (b * a) .* X ij a
.* X ki (- (b * a * b)) .* X ji (- (b * a * b)) .* Z jk (b * a) (- (1)).

intros. move: (RG1bis i j k a 1 b ij ik jk) => /=.
by rewrite ?swapI -/ji -/ki -/kj; rsimpl. Qed.

Corollary R22 i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = Z jk (- (b * a)) 1 .* X ij a .* X ik a .* Z ik (- a) (- b)
.* X ji (- (b * a * b)) .* X jk (b * a) .* X ki (- (b * a * b))
.* X kj (- (b * a)).

intros. move: (RG2bis i j k a 1 b ij ik jk) => /=.
by rewrite ?swapI -/ji -/ki -/kj; rsimpl. Qed.

(* ====== *)

Corollary R12' i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = Z jk (b * a) (- (1)) .* X ji (- (b * a * b)) .* X ki (- (b * a * b))
.* X ij a .* X kj (b * a) .* Z ik (- a) (- b) .* X ik a .* X jk (- (b * a)).

intros. move: (RG1bis i j k (-a) 1 b ij ik jk) => /=.
rewrite ?swapI -/ji -/ki -/kj; rsimpl.
rewrite Zinv. rewrite -{2}(GII (Z ij a b)) => ->.
by rewrite ?GIM -?Zinv -?ST0' ?invI -?GA //. Qed.

Corollary R12'' i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = X jk (b * a) .* X ik (- a) .* Z ik a b .* X kj (- (b * a)) .* X ij a
.* X ki (b * a * b) .* X ji (- (b * a * b)) .* Z jk (- (b * a)) 1.

intros. move: (RG1bis i j k (-a) (-(1)) b ij ik jk) => /=.
rewrite ?swapI -/ji -/ki -/kj; rsimpl.
rewrite Zinv. rewrite -{2}(GII (Z ij a b)) => ->.
by rewrite ?GIM -?Zinv -?ST0' ?invI -?GA //. Qed.

Corollary R22'  i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = X kj (- (b * a)) .* X ki (- (b * a * b)) .* X jk (b * a)
.* X ji (- (b * a * b)) .* Z ik (- a) (- b) .* X ik a .* X ij a
.* Z jk (- (b * a)) 1.

intros. move: (RG2bis i j k (-a) 1 b ij ik jk) => /=.
rewrite ?swapI -/ji -/ki -/kj; rsimpl.
rewrite Zinv. rewrite -{2}(GII (Z ij a b)) => ->.
by rewrite ?GIM -?Zinv -?ST0' ?invI -?GA //. Qed.

Corollary R22'' i j k (a b : R) (ij : i!=j) (ik : i!=k) (jk : j!=k):
let ji := swap_neq ij in let ki := swap_neq ik in let kj := swap_neq jk in
Z ij a b = Z jk (b * a) (- (1)) .* X ij a .* X ik (- a) .* Z ik a b
.* X ji (- (b * a * b)) .* X jk (- (b * a)) .* X ki (b * a * b)
.* X kj (b * a).

intros. move: (RG2bis i j k (-a) (-(1)) b ij ik jk) => /=.
rewrite ?swapI -/ji -/ki -/kj; rsimpl.
rewrite -{2}(GII (Z ij a b)) => ->.
by rewrite ?GIM -?Zinv -?ST0' ?invI -?GA //. Qed.

(* ====== *)

Lemma StrangeL {i j k} {ij : i != j} {ik : i != k} {jk : j != k} {ji : j != i} {ki : k != i} {kj : k != j} a b c:
[ ~ X ik ((c * b + 1) * a) .* X jk (- (b * a)), X ki b .* X kj (b * c + 1)] ^ (X ij (-c)) = Z ij a b.
rewrite comm_conj ?mul_conj ?ST1'' ?ST1''2 ST2'' // ST2' //; rsimpl. 
rewrite -GA -ST0 (ST2''_swap ji) GA -ST0 (plus_comm _ (1))
        dist_r plus_assoc inv_r plus_0_r -plus_assoc inv_l plus_0_l mul_1_l
        comm_d2 ?GIM -?ST0' ?invI ?conj_mul mul_conj Zdef'' ST1''
        ?mul_conj C3 ST1''2 Zdef''; rsimpl.

move: (R12' i j k a b ij ik jk) => /=.
 
rewrite (irrelev (swap_neq jk) kj) (irrelev (swap_neq ij) ji) (irrelev (swap_neq ik) ki).
Admitted.


(* Lemmata about conjugation with Weyl elements *)

Definition W {i j} (ij : i != j) := let ji := (swap_neq ij) in X ij (1) .* X ji (-(1)) .* X ij (1).

Lemma Wconj1 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ki a) ^ W ij = X kj a.
intros. rewrite /W -/ji 2!conj_mul ST1'' mul_conj ST1'' ST2' // ?mul_conj ?ST1'' ST2' // (ST2''_swap) //.
rsimpl. rewrite ?ST0'. cancel. rewrite (ST2''_swap) //. cancel. done. Qed. 

Lemma Wconj1' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X jk a) ^ W ij = X ik (-a).
intros. rewrite /W -/ji 2!conj_mul ST1''2 mul_conj ST1''2 ST2'' // ?mul_conj ?ST1''2 ST2'' // ST2'_swap //.
rsimpl. rewrite ?ST0'. cancel. rewrite -?ST0' (ST2'_swap) // ?ST0'. cancel. done. Qed.

Lemma Wconj2 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ik a) ^ W ij = X jk a.
intros. rewrite /W -/ji 2!conj_mul ST2'' // ST1''2 mul_conj ST2'' // ST1''2.
rsimpl. rewrite (ST2'_swap) // ST0'. cancel. done. Qed.

Lemma Wconj2' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X kj a) ^ W ij = X ki (-a).
intros. rewrite /W -/ji 2!conj_mul ST2' // ST1'' mul_conj ST2' // ST1''.
rsimpl. rewrite (ST2''_swap) // ?ST0'. cancel. done. Qed.

Lemma Wconj3 i j k l (ij : i != j) (ik : i != k) (jk : j != k) (il : i != l) (kl : k != l) (jl : j!=l) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 let li := swap_neq il in let lk := swap_neq kl in let lj := swap_neq jl in
 (X kl a) ^ W ij = X kl a.
intros. rewrite /W -/ji ?conj_mul. by do 3 rewrite ST2''' //. Qed.

Lemma Wconj4 i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ji a) ^ W ij = X ij (-a).
intros. rewrite -{1}(mul_1_r a) -(ST1 jk ji ki) comm_conj Wconj1 Wconj1' -/kj ST1. by rsimpl. Qed.

Lemma Wconj4' i j k (ij : i != j) (jk : j != k) (ik : i != k) a:
let ji := swap_neq ij in let kj := swap_neq jk in let ki := swap_neq ik in
 (X ij a) ^ W ij = X ji (-a).
intros. rewrite -{1}(mul_1_r a) -(ST1 ik ij kj) comm_conj Wconj2 Wconj2' -/ki ST1. by rsimpl. Qed.