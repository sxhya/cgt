Require Import ssreflect ssrnat ssrbool seq eqtype Group Ssromega.

Definition coo (n i j : nat) := (i < j) && (j - i < n).
Definition s {n : nat} {i j : nat} (ij : coo n i j) (g : ZZ) : ZZ. Admitted.
Definition between (i j k : nat) := (i < j) && (j < k).
Definition coosuc {n i j : nat} (p : coo n i j) : coo (n.+1) i j.
 move: p => /andP [] A0 A1. apply /andP. split. done. ssromega. Defined.

Require Import Coq.Logic.ProofIrrelevance.

Lemma coo_irrel: forall (n i j : nat) (p q : coo n i j), p = q.
intros. by apply proof_irrelevance. Qed.
Lemma coo_ne {n i j : nat} (p : coo n i j): i <> j.
apply /eqP. rewrite neq_ltn. move: p => /andP []. by case: (ltngtP i j). Qed.
Lemma coo_ne' {n i j : nat} (p : coo n i j): j <> i.
apply /eqP. rewrite neq_ltn. move: p => /andP []. by case: (ltngtP i j). Qed.

Parameter (n : nat).

Axiom R1: forall {i j : nat} (ij : coo n i j) (g : ZZ), (s ij g) .* (s ij g) = Id.
Lemma R1a: forall {i j : nat} (ij : coo n i j) (g h : ZZ), h .* (s ij g) = (s ij g) .* h ^ (s ij g).
 intros. expand. rewrite -?GA. by cancel. Qed.

Axiom R2: forall (i j k : nat) (a b a' b': ZZ) (ij : coo n i j) (jk : coo n j k), a .* b = a' .* b' ->
   (s ij a) ^ (s jk b) = (s jk b') ^ (s ij a').

Lemma R2a: forall (i j k : nat) (a b a' b': ZZ) (ij : coo n i j) (jk : coo n j k), a .* b = a' .* b' ->
   (s ij a) ^ (s jk b) = (s ij a') ^ (s jk b').
 intros. rewrite (R2 i j k a b a' b') //. rewrite -(R2 i j k a' b' a' b') //. Qed.

Axiom R3: forall (i j k l : nat) (a b : ZZ) (ij : coo n i j) (kl : coo n k l), 
 i <> k -> i <> l -> j <> k -> j <> l ->
   (s ij a) .* (s kl b) = (s kl b) .* (s ij a).
Axiom R4: forall (i j k : nat) (a b : ZZ) (ij : coo n i j) (jk : coo n j k) (ik : coo n i k),
   (s ij a) ^ (s jk b) = (s ik (a .* b)).

Definition split1 (n i k j : nat) (ij : coo (n.+1) i j) (p : between i k j) : (coo n i k).
 move: ij p. move => /andP [] A0 A1 [] /andP [] A2 A3. apply /andP. split => //. ssromega. Defined.
Definition split2 (n i k j : nat) (ij : coo (n.+1) i j) (p : between i k j) : (coo n k j).
 move: ij p. move => /andP [] A0 A1 [] /andP [] A2 A3. apply /andP. split => //. ssromega. Defined.

Definition s' {i j : nat} (k : nat) (p : between i k j) (ij : coo (n.+1) i j) (g : ZZ) :=
  let ik := split1 n i k j ij p in
    let kj := split2 n i k j ij p in
      (s ik g) ^ (s kj Id).

Lemma wd: forall (i j : nat) (g : ZZ) (ij : coo (n.+1) i j) (k k' : nat) (p : between i k j) (p' : between i k' j), 
   s' k p ij g = s' k' p' ij g. intros. rewrite /s'. 
   move: (ltngtP k k') => []; [ |rename k' into k''; rename k into k'; rename k'' into k; rename p' into p''; rename p into p'; rename p'' into p |
       move => A0; subst; assert (B0: p = p') by apply proof_irrelevance; by rewrite B0 ];
     move => B0; move: (split1 n i k j ij p) => ik; move: (split2 n i k j ij p) => kj;
                 move: (split1 n i k' j ij p') => ik'; move: (split2 n i k' j ij p') => k'j;
     assert (B1: between i k k') by (move: ik B0; rewrite /coo /between; by case: (i < k) (k < k'));
     move: (split2 n i k k' (coosuc ik') B1) => kk';
     move: (R4 i k k' g Id ik kk' ik') => B2; rewrite GId in B2; rewrite -B2;
     move: (R4 k k' j Id Id kk' k'j kj) => B3; rewrite GId in B3; rewrite -B3; expand; bite;
     rewrite (R3 k' j i k Id g k'j ik (coo_ne' ik') (coo_ne' kk') (coo_ne' ij) (coo_ne' kj)); by cancel. Qed.

Lemma wd2: forall (i j : nat) (g : ZZ) (ij : coo n i j) (k : nat) (p : between i k j),
   s' k p (coosuc ij) g = s ij g. intros. rewrite /s'.
   move: (split1 n i k j (coosuc ij) p) => ik; move: (split2 n i k j (coosuc ij) p) => kj.
   move: (R4 i k j g Id ik kj ij). by rewrite GId. Qed.
 
Lemma R1': forall (i j : nat) (g : ZZ) (ij : coo (n.+1) i j) (k k' : nat) (p : between i k j) (p' : between i k' j),
  (s' k p ij g) .* (s' k p ij g) = Id. intros. by rewrite /s' -mul_conj R1 Idconj. Qed.

Lemma R4': forall (i j k : nat) (a b : ZZ) (ij : coo (n.+1) i j) (j' : nat) (p : between i j' j)
                                           (jk : coo n j k) (ik : coo (n.+1) i k),
   exists p',
   (s' j' p ij a) ^ (s jk b) = (s' j' p' ik (a .* b)). intros.
   assert (p': between i j' k). move: p jk. rewrite /between /coo => A0 /andP [] A1 A2. ssromega.
   exists p'. rewrite /s'.
   move: (split1 n i j' j ij p) => ij'.
   move: (split2 n i j' j ij p) => j'j.
   move: (split1 n i j' k ik p') => ij'2.
   move: (split2 n i j' k ik p') => j'k.
   rewrite -(coo_irrel n i j' ij' ij'2).
   rewrite -conj_mul. rewrite (R1a jk b) R4 IdG.
   rewrite (R2a i j' k (a .* b) Id a b ij' j'k); [| by cancel].
   expand. bite.
   rewrite GA -(R3 j k i j' b a jk ij' (coo_ne' ij) (coo_ne' j'j) (coo_ne' ik) (coo_ne' j'k)).
   by cancel. Qed.

