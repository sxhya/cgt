Require Import ssreflect ssrnat ssrbool seq eqtype Group Ssromega.

Definition coo (n i j : nat) := (i < j) && (j - i < n).
Definition s {n : nat} {i j : nat} (ij : coo n i j) (g : ZZ) : ZZ. Admitted.
Definition between (i j k : nat) := (i < j) && (j < k).
Definition coosuc {n i j : nat} (p : coo n i j) : coo (n.+1) i j.
 move: p => /andP [] A0 A1. apply /andP. split. done. ssromega. Defined.

Require Import Coq.Logic.ProofIrrelevance.

Lemma coo_irrel: forall {n i j : nat} (p q : coo n i j), p = q.
intros. by apply proof_irrelevance. Qed.
Lemma coo_ne {n i j : nat} (p : coo n i j): i <> j.
apply /eqP. rewrite neq_ltn. move: p => /andP []. by case: (ltngtP i j). Qed.
Lemma coo_ne' {n i j : nat} (p : coo n i j): j <> i.
apply /eqP. rewrite neq_ltn. move: p => /andP []. by case: (ltngtP i j). Qed.

Parameter (n : nat).

Axiom R1: forall {i j : nat} (ij : coo n i j) (g : ZZ), (s ij g) .* (s ij g) = Id.
Lemma R1a: forall {i j : nat} (ij : coo n i j) (g h : ZZ), h .* (s ij g) = (s ij g) .* h ^ (s ij g).
 intros. expand. rewrite -?GA. by cancel. Qed.
Lemma R1b: forall {i j : nat} (ij : coo n i j) (g : ZZ), (s ij g) = (s ij g) ^-1.
 intros. apply (GCl (s ij g)). rewrite R1. by cancel. Qed.

Axiom R2: forall {i j k : nat} (a b a' b': ZZ) (ij : coo n i j) (jk : coo n j k), a .* b = a' .* b' ->
   (s ij a) ^ (s jk b) = (s jk b') ^ (s ij a').

Lemma R2a: forall {i j k : nat} (a b a' b': ZZ) (ij : coo n i j) (jk : coo n j k), a .* b = a' .* b' ->
   (s ij a) ^ (s jk b) = (s ij a') ^ (s jk b').
 intros. rewrite (R2 a b a' b') //. rewrite -(R2 a' b' a' b') //. Qed.

Axiom R3: forall {i j k l : nat} (a b : ZZ) (ij : coo n i j) (kl : coo n k l), 
 i <> k -> i <> l -> j <> k -> j <> l ->
   (s ij a) .* (s kl b) = (s kl b) .* (s ij a).
Lemma R3a: forall {i j k l : nat} (a b : ZZ) (ij : coo n i j) (kl : coo n k l), 
 i <> k -> i <> l -> j <> k -> j <> l ->
   (s ij a) ^ (s kl b) = (s ij a).
intros. rewrite /conj -R1b. by rewrite GA (R3 a b ij kl) // -GA R1 IdG. Qed.

Axiom R4: forall {i j k : nat} (a b : ZZ) (ij : coo n i j) (jk : coo n j k) (ik : coo n i k),
   (s ij a) ^ (s jk b) = (s ik (a .* b)).

Definition split1 (n i k j : nat) (ij : coo (n.+1) i j) (p : between i k j) : (coo n i k).
 move: ij p. move => /andP [] A0 A1 [] /andP [] A2 A3. apply /andP. split => //. ssromega. Defined.
Definition split2 (n i k j : nat) (ij : coo (n.+1) i j) (p : between i k j) : (coo n k j).
 move: ij p. move => /andP [] A0 A1 [] /andP [] A2 A3. apply /andP. split => //. ssromega. Defined.

Definition s' {i j : nat} (k : nat) (p : between i k j) (ij : coo (n.+1) i j) (g : ZZ) :=
  let ik := split1 n i k j ij p in
    let kj := split2 n i k j ij p in
      (s ik g) ^ (s kj Id).

Lemma wd: forall {i j : nat} (g : ZZ) (ij : coo (n.+1) i j) (k k' : nat) (p : between i k j) (p' : between i k' j), 
   s' k p ij g = s' k' p' ij g. intros. rewrite /s'. 
   move: (ltngtP k k') => []; [ |rename k' into k''; rename k into k'; rename k'' into k; rename p' into p''; rename p into p'; rename p'' into p |
       move => A0; subst; assert (B0: p = p') by apply proof_irrelevance; by rewrite B0 ];
     move => B0; move: (split1 n i k j ij p) => ik; move: (split2 n i k j ij p) => kj;
                 move: (split1 n i k' j ij p') => ik'; move: (split2 n i k' j ij p') => k'j;
     assert (B1: between i k k') by (move: ik B0; rewrite /coo /between; by case: (i < k) (k < k'));
     move: (split2 n i k k' (coosuc ik') B1) => kk';
     move: (R4 g Id ik kk' ik') => B2; rewrite GId in B2; rewrite -B2;
     move: (R4 Id Id kk' k'j kj) => B3; rewrite GId in B3; rewrite -B3; expand; bite;
     rewrite (R3 Id g k'j ik (coo_ne' ik') (coo_ne' kk') (coo_ne' ij) (coo_ne' kj)); by cancel. Qed.

Lemma wd2: forall {i j : nat} (g : ZZ) (ij : coo n i j) (k : nat) (p : between i k j),
   s' k p (coosuc ij) g = s ij g. intros. rewrite /s'.
   move: (split1 n i k j (coosuc ij) p) => ik; move: (split2 n i k j (coosuc ij) p) => kj.
   move: (R4 g Id ik kj ij). by rewrite GId. Qed.
 
Lemma R1A: forall (i j : nat) (g : ZZ) (ij : coo (n.+1) i j) (k k' : nat) (p : between i k j) (p' : between i k' j),
  (s' k p ij g) .* (s' k p ij g) = Id. intros. by rewrite /s' -mul_conj R1 Idconj. Qed.

Lemma R4A: forall {i j k : nat} (a b : ZZ) (ij : coo (n.+1) i j) (j' : nat) (p : between i j' j)
                                           (jk : coo n j k) (ik : coo (n.+1) i k),
   exists p',
   (s' j' p ij a) ^ (s jk b) = (s' j' p' ik (a .* b)).

   intros. assert (p': between i j' k). move: p jk. rewrite /between /coo => A0 /andP [] A1 A2. ssromega. exists p'. rewrite /s'.
   move: (split1 n i j' j ij p) (split2 n i j' j ij p) (split1 n i j' k ik p') (split2 n i j' k ik p') => ij' j'j ij'2 j'k.
   rewrite -(coo_irrel ij' ij'2) -conj_mul (R1a jk b) R4 IdG (R2a (a .* b) Id a b ij' j'k); [| by cancel]. expand. bite.
   rewrite GA -(R3 b a jk ij' (coo_ne' ij) (coo_ne' j'j) (coo_ne' ik) (coo_ne' j'k)). by cancel. Qed.

Lemma R4B: forall (i j k : nat) (a b : ZZ) (ij : coo n i j) (j' : nat) (p : between j j' k)
                                            (jk : coo (n.+1) j k) (ik : coo (n.+1) i k),
   exists p',
   (s ij a) ^ (s' j' p jk b) = (s' j' p' ik (a .* b)).
  
   intros. assert (p': between i j' k). move: p ij. rewrite /between /coo => A0 /andP [] A1 A2. ssromega. exists p'. rewrite /s'.
   move: (split1 n j j' k jk p) (split2 n j j' k jk p) (split1 n i j' k ik p') (split2 n i j' k ik p') => jj' j'k ij' j'k2.
   rewrite -(coo_irrel j'k j'k2) -(R4 a b ij jj' ij'). expand. bite.
   rewrite (R3 Id a j'k ij (coo_ne' ij') (coo_ne' jj') (coo_ne' ik)  (coo_ne' jk)). by cancel. Qed.

Lemma R4C: forall (i j k : nat) (a b : ZZ) (ij : coo (n.+1) i j) (j' : nat) (p' : between i j' j)
                                           (jk : coo (n.+1) j k) (j'' : nat) (p'' : between j j'' k)
                                           (ik : coo (n.+1) i k),
   exists p, (s' j' p' ij a) ^ (s' j'' p'' jk b) = (s' j' p ik (a .* b)). 

   intros.
   assert (p: between i j' k). move: p' jk. rewrite /between /coo => A0 /andP [] A1 A2. ssromega. exists p.
   assert (coo n i j /\ coo n j k).
    + move: ij => /andP []. intros. move: ik => /andP []. intros. move: jk => /andP []. intros.
      split; apply /andP; split; ssromega. 
   move: H => [ij_ jk_].
   move: (wd2 a ij_ j' p').
   rewrite -(coo_irrel ij (coosuc ij_)) => ->.
   move: (R4B i j k a b ij_ j'' p'' jk ik) => [p3].
   move: (wd (a .* b) ik j' j'' p p3) => -> //. Qed.

Lemma neqs {i j : nat} (p : i <> j) : j <> i.
 Proof. ssromega. Qed.

Lemma R3A: forall {i j k l : nat} (a b : ZZ) (ij : coo (n.+1) i j) (kl : coo n k l) (j' : nat) (p : between i j' j), 
 i <> k -> i <> l -> j <> k -> j <> l -> (s' j' p ij a) .* (s kl b) = (s kl b) .* (s' j' p ij a).

 intros. rewrite /s'.
 move: (split1 n i j' j ij p) (split2 n i j' j ij p) => ij' j'j.
 assert (A0: j' = k \/ j' <> k). ssromega.
 assert (A1: j' = l \/ j' <> l). ssromega.
 move: A0 A1 => [] A0 [] A1.
  + assert false. move: (coo_ne' kl). by rewrite -A0 -A1. by move: H3.
  + subst. rename ij' into ik. rename j'j into kj. 

    move: (ltngtP j l) => [] C0 //.
    + assert (p': between k j l). apply /andP. split => //. by move: kj => /andP [].
      set jl := split2 n k j l (coosuc kl) p'.
      move: (R4 Id b kj jl kl) => A2. rewrite IdG in A2. rewrite -A2.
      move: (R2 Id b Id b kj jl) => A3. rewrite A3 //. rewrite -2!mul_conj.
      by rewrite (R3 a b ik jl (coo_ne ij) H0 (coo_ne kj) A1).
    + assert (p': between k l j). apply /andP. split => //. move: kl => /andP [] * //.
      assert (p'': between i l j). apply /andP. split => //. move: ik kl => /andP [] B0 B1 /andP [] B2 B3. ssromega.
      set lj := split2 n k l j (coosuc kj) p'.
      set il := split1 n i l j ij p''.
      move: (R4 Id Id kl lj kj) => A2. rewrite IdG /conj GA in A2. rewrite -A2 -R1b conj_mul.
      rewrite (R3a a Id ik lj H0 (coo_ne ij) A1 (coo_ne kj)). rewrite conj_mul.
      move: (R4 a Id ik kl il). rewrite GId => ->.
      assert (A3: s kl b = (s kl b) ^ ((s lj Id) .* (s lj Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A3 conj_mul -2!mul_conj. move: (R4 b Id kl lj kj). rewrite GId => ->.
      rewrite (R3 a b il kj H (coo_ne ij)) => //; ssromega.

  + subst. rename ij' into il. rename j'j into lj. 

    move: (ltngtP i k) => [] C0 //.
    + assert (p': between i k l). apply /andP. split => //. by move: kl => /andP [].
      assert (p'': between i k j). apply /andP. split => //. move: kl lj => /andP [] B0 B1 /andP [] B2 B3. ssromega.
      set ik := split1 n i k l (coosuc il) p'.
      set kj := split2 n i k j ij p''.
      move: (R4 a Id ik kl il). rewrite GId => <-. 
      assert (A1: s kl b = (s kl b) ^ ((s lj Id) .* (s lj Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A1. rewrite conj_mul -2!mul_conj.
      move: (R4 a Id ik kl il). rewrite GId => ->.
      move: (R4 b Id kl lj kj). rewrite GId => ->.
      by move: (R3 a b il kj H (coo_ne ij) A0 (coo_ne lj)) => ->. 
    + assert (p': between k i l). apply /andP. split => //. by move: il => /andP [].
      set ki := split1 n k i l (coosuc kl) p'.
      move: (R4 b Id ki il kl). rewrite GId => <-.
      move: (R2 a Id Id a il lj). rewrite GId IdG => -> //. rewrite -2!mul_conj. 
      by rewrite (R3 a b lj ki (A0) (neqs H0) H1 (coo_ne' ij)).
  + (* rank 5 case *)
      assert (A2: s kl b = (s kl b) ^ ((s j'j Id) .* (s j'j Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A2 conj_mul -2!mul_conj.
      move: (R3a b Id kl j'j (neqs A0) (neqs H1) (neqs A1) (neqs H2)) => ->.
      by move: (R3 a b ij' kl H H0 A0 A1) => ->. Qed.

Lemma R3Aa: forall {i j k l : nat} (a b : ZZ) (ij : coo (n.+1) i j) (kl : coo n k l) (j' : nat) (p : between i j' j), 
 i <> k -> i <> l -> j <> k -> j <> l -> 
   (s' j' p ij a) ^ (s kl b) = (s' j' p ij a).
intros. rewrite /conj -R1b. by rewrite GA (R3A a b ij kl) // -GA R1 IdG. Qed.

Lemma R2A: forall {i j k : nat} (a b a' b': ZZ) (ij : coo (n.+1) i j) (jk : coo n j k) (j' : nat) (p : between i j' j), a .* b = a' .* b' ->
   (s' j' p ij a) ^ (s jk b) = (s jk b') ^ (s' j' p ij a').

 intros. rewrite /s'.
 move: (split1 n i j' j ij p) (split2 n i j' j ij p) => ij' j'j.
 rewrite {4}/conj -R1b GA conj_mul.
 rewrite -(R2 Id b' Id b' j'j jk) //.
 rewrite -2!conj_mul -GA.
 assert (A0: k <> i). move: ij jk => /andP [] B0 _ /andP [] B1 _. ssromega.
 assert (A1: k <> j'). move: j'j jk => /andP [] B0 _ /andP [] B1 _. ssromega.

 rewrite (R3 b' a' jk ij' (coo_ne' ij) (coo_ne' j'j) A0 A1) GA (R1a j'j Id).
 rewrite 2!conj_mul.
 rewrite -(R2 a' Id a' Id ij' j'j) //.
 rewrite -2!conj_mul -GA R1 IdG conj_mul.
 rewrite -(R2 b' Id  Id b' j'j jk) ?GId ?IdG //.
 rewrite {4}/conj -R1b GA conj_mul.
 rewrite (R3a a' Id ij' jk (coo_ne ij) (neqs A0) (coo_ne j'j) (neqs A1)).
 rewrite conj_mul.
 rewrite -(R2a a b a' b' ij' j'j H).
 rewrite -?conj_mul (R1a jk Id).
 rewrite (R2a b Id Id b j'j jk) ?GId ?IdG //.
 rewrite {3}/conj GA ?conj_mul -R1b.
 rewrite (R3a a Id ij' jk (coo_ne ij) (neqs A0) (coo_ne j'j) (neqs A1)).
 rewrite (R3a a b ij' jk (coo_ne ij) (neqs A0) (coo_ne j'j) (neqs A1)). 
 done. Qed.

Lemma R2B: forall {i j k : nat} (a b a' b': ZZ) (ij : coo n i j) (jk : coo (n.+1) j k) (j' : nat) (p : between j j' k), a .* b = a' .* b' ->
   (s ij a) ^ (s' j' p jk b) = (s' j' p jk b') ^ (s ij a').

  intros. rewrite /s'.
  move: (split1 n j j' k jk p) (split2 n j j' k jk p) => jj' j'k. symmetry.
  rewrite {4}/conj -R1b GA conj_mul.

  assert (A0: i <> j'). move: ij jj' => /andP [] B0 _ /andP [] B1 _. ssromega.
  assert (A1: i <> k). move: ij jk => /andP [] B0 _ /andP [] B1 _. ssromega.

  rewrite (R3a a Id ij j'k A0 A1 (coo_ne jj') (coo_ne jk)).
  rewrite conj_mul.
  rewrite (R2 a b a' b' ij jj') //.
  rewrite -?conj_mul.
  rewrite (R1a j'k Id).
  by move: (R3a a' Id ij j'k A0 A1 (coo_ne jj') (coo_ne jk)) => ->. Qed.

Lemma R2C: forall {i j k : nat} (a b a' b': ZZ) (ij : coo (n.+1) i j) (jk : coo (n.+1) j k) (j' : nat) (p : between i j' j) (k' : nat) (pk : between j k' k), a .* b = a' .* b' ->
   (s' j' p ij a) ^ (s' k' pk jk b) = (s' k' pk jk b') ^ (s' j' p ij a').

  intros. remember (s' k' pk jk b) as z.   rewrite /s' in Heqz.
          remember (s' k' pk jk b') as z'. rewrite /s' in Heqz'.
  move: (split1 n j k' k jk pk) (split2 n j k' k jk pk) Heqz Heqz' => jk' k'k -> ->. symmetry.
  rewrite {4}/conj -R1b GA conj_mul.
  assert (A0: i <> k'). move: ij jk' => /andP [] B0 _ /andP [] B1 _. ssromega.
  assert (A1: i <> k). move: ij jk => /andP [] B0 _ /andP [] B1 _. ssromega.

  rewrite (R3Aa a Id ij k'k j' p A0 A1 (coo_ne jk') (coo_ne jk)). 
  rewrite conj_mul.
  rewrite (R2A a b a' b' ij jk') //.
  rewrite -?conj_mul.
  rewrite (R1a k'k Id).
  by move: (R3Aa a' Id ij k'k j' p A0 A1 (coo_ne jk') (coo_ne jk)) => ->. Qed.
  
Lemma R3B: forall (i j k l : nat) (a b : ZZ) (ij : coo (n.+1) i j) (kl : coo (n.+1) k l) (j' k' : nat) (p : between i j' j) (pk : between k k' l),
 i <> k -> i <> l -> j <> k -> j <> l -> (s' j' p ij a) .* (s' k' pk kl b) = (s' k' pk kl b) .* (s' j' p ij a).

 intros. remember (s' j' p ij a). rewrite /s' in Heqz.
 move: Heqz.
 move: (split1 n i j' j ij p) (split2 n i j' j ij p) => ij' j'j ->.
 assert (A0: j' = k \/ j' <> k). ssromega.
 assert (A1: j' = l \/ j' <> l). ssromega.
 move: A0 A1 => [] A0 [] A1.
  + assert false. move: (coo_ne' kl). by rewrite -A0 -A1. by move: H3.
  + subst. rename ij' into ik. rename j'j into kj. 

    move: (ltngtP j l) => [] C0 //.
    + assert (p': between k j l). apply /andP. split => //. by move: kj => /andP [].
      move:(wd b kl k' j pk p') => ->. rewrite /s'. set jl := split2 n k j l kl p'.
      set kj_ := split1 n k j l kl p'. rewrite -(proof_irrelevance _ kj kj_). clear kj_.      
      move: (R2 b Id Id b kj jl) => A3. rewrite A3 ?GId ?IdG //. rewrite -2!mul_conj.
      by rewrite (R3 a b ik jl (coo_ne ij) H0 (coo_ne kj) A1).
    + assert (p': between k l j). apply /andP. split => //. move: kl => /andP [] * //.
      assert (p'': between i l j). apply /andP. split => //. move: ik kl => /andP [] B0 B1 /andP [] B2 B3. ssromega.
      set lj := split2 n k l j (coosuc kj) p'.
      set il := split1 n i l j ij p''.
      set kl_ := split1 n k l j (coosuc kj) p'.
      rewrite (coo_irrel kl (coosuc kl_)) (wd2 b kl_ k' pk).
      move: (R4 Id Id kl_ lj kj) => A2. rewrite IdG /conj GA in A2. rewrite -A2 -R1b conj_mul.
      rewrite (R3a a Id ik lj H0 (coo_ne ij) A1 (coo_ne kj)). rewrite conj_mul.
      move: (R4 a Id ik kl_ il). rewrite GId => ->.
      assert (A3: s kl_ b = (s kl_ b) ^ ((s lj Id) .* (s lj Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A3 conj_mul -2!mul_conj. move: (R4 b Id kl_ lj kj). rewrite GId => ->.
      rewrite (R3 a b il kj H (coo_ne ij)) => //; ssromega.

  + subst. rename ij' into il. rename j'j into lj. 

    move: (ltngtP i k) => [] C0 //.
    + assert (p': between i k l). apply /andP. split => //. by move: kl => /andP [].
      assert (p'': between i k j). apply /andP. split => //. move: kl lj => /andP [] B0 B1 /andP [] B2 B3. ssromega.
      set ik := split1 n i k l (coosuc il) p'.
      set kj := split2 n i k j ij p''.
      set kl_ := split2 n i k l (coosuc il) p'.
      rewrite (coo_irrel kl (coosuc kl_)) (wd2 b kl_ k' pk).
      move: (R4 a Id ik kl_ il). rewrite GId => <-. 
      assert (A1: s kl_ b = (s kl_ b) ^ ((s lj Id) .* (s lj Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A1. rewrite conj_mul -2!mul_conj.
      move: (R4 a Id ik kl_ il). rewrite GId => ->.
      move: (R4 b Id kl_ lj kj). rewrite GId => ->.
      by move: (R3 a b il kj H (coo_ne ij) A0 (coo_ne lj)) => ->. 
    + assert (p': between k i l). apply /andP. split => //. by move: il => /andP [].
      move:(wd b kl k' i pk p') => ->. rewrite /s'. 
      set ki := split1 n k i l kl p'.
      set il_ := (split2 n k i l kl p').
      rewrite (coo_irrel il_ il). clear il_.
      move: (R2 a Id Id a il lj). rewrite GId IdG => -> //. rewrite -2!mul_conj. 
      by rewrite (R3 a b lj ki (A0) (neqs H0) H1 (coo_ne' ij)).
  + (* rank 5 case *)
      assert (A2: s' k' pk kl b = (s' k' pk kl b) ^ ((s j'j Id) .* (s j'j Id))). by rewrite R1 /conj GId IdI IdG.
      rewrite A2 conj_mul -2!mul_conj.
      move: (R3Aa b Id kl j'j k' pk (neqs A0) (neqs H1) (neqs A1) (neqs H2)) => ->.
      by move: (@R3A k l i j' b a kl ij' k' pk (neqs H) (neqs A0) (neqs H0) (neqs A1)) => ->. Qed.