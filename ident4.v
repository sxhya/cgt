Require Import ssreflect ssrnat ssrbool seq eqtype Ring Group ident3.
Import Ring.ideal.

Section Aux1. Import ZC_tactic.

Context (i j k l m n : nat) (a1 a2 b c d : R)
        {ij : i != j} {ji : j != i} 
        {ik : i != k} {jk : j != k} {ki : k != i} {kj : k != j} 
        {kl : k != l} {il : i != l} {jl : j != l} {lk : l != k} {li : l != i} {lj : l != j}.

Lemma ZC1_I_01:
Z' ij a1 b ^^ X ij c .* X' il d = 
  X' il ((1 + (c * b + 1) * a1 * b) * d) .*
  X' jl (- (b * a1 * b * d)) .*
  Z' ij a1 b ^^ X ij c.
Proof.
remember (Z' ij a1 b ^^ X ij c) as RHS.
rewrite {1}HeqRHS.
rewrite (ZC1 _ _ k) //. ZCR. rewrite -?GA.
rewrite (Z3_swap' k i l) //.
rewrite (Z3_swap' j i l) //; simplify0.
rewrite (X5_swap' j i k l) //. rexpand. rsimpl.
rewrite (X5_swap' j k i l) //.
rewrite (X4'_swap' j k l) //.
rewrite (Z3_swap' j k l) //; simplify0.
rewrite (X4_swap' k l j) // -X0'.
rewrite -(Z5' k j i l) // X'def.
rewrite (Z3_swap' k j l) //; simplify0.

rexpand. rsimpl. rewrite -?plus_assoc.

remember (b * a1 * b) as A0.
remember (A0 * c * b * a1 * b) as A1.
remember (A0 * a1 * b) as A2.
remember (A1 * c * b * a1 * b * d) as A3.
remember (A1 * a1 * b * d) as A4.
remember (A2 * c * b * a1 * b * d) as A5.
remember (A2 * a1 * b * d) as A6.

cancm (A1 * d). cancm (A2 * d). cancm A3. cancm A4. cancm A5. 

remember (a1 * b) as B0.
remember (B0 * c * b * a1 * b) as B1.
remember (B0 * a1 * b) as B2.
remember (B1 * c * b * a1 * b * d) as B3.
remember (B2 * c * b * a1 * b * d) as B4.
remember (B1 * a1 * b * d) as B5.
remember (B2 * a1 * b * d) as B6.

cancm B3. cancm B4. cancm B5.

rewrite (Z4'_swap' k j l) // -X0'. simplify0.
rewrite (X4_swap' k l j) // -X0'.
rewrite (X4'_swap' i j l) //.
rewrite (Z3_swap' i j l) //; simplify0.
rewrite (X4_swap' j l i) // -X0'.
rewrite (X5_swap' i j k l) //.
rewrite (X4'_swap' i k l) //.
rewrite (X5_swap' i k j l) //.
rewrite (Z3_swap' i k l) //; simplify0.
rewrite (X4_swap' k l i) //.
rewrite (X4_swap' j l i) // -X0'.
rewrite (X5_swap' k j i l) //.
rewrite (Z3_swap' k j l) //; simplify0.
rewrite (X4'_swap' k j l) // -X0'.
rewrite (Z3_swap _ _ _ k i l) //; simplify0.
rewrite (X5_swap' k i j l) //.
rewrite (X4'_swap' k i l) //.
rewrite (X4_swap' j l k) // -X0'.

subst. simplify0. rexpand. rsimpl. rewrite -?plus_assoc -?mul_assoc.

remember (c * b * a1 * b) as C0.
remember (a1 * b * a1 * b) as C1.
remember (a1 * b * c * b * a1 * b) as C2.
remember (C2 * a1 * b) as C3.
remember (C2 * c * b * a1 * b) as C4.
remember (C1 * a1 * b) as C5.
remember (C1 * c * b * a1 * b) as C6.
remember (C3 * a1 * b) as C7.
remember (C3 * c * b * a1 * b) as C8.
remember (C6 * a1 * b) as C9.
remember (C6 * c * b * a1 * b) as C10.
remember (C4 * a1 * b) as C11.
remember (C4 * c * b * a1 * b) as C12.
remember (C5 * a1 * b) as C13.
remember (C5 * c * b * a1 * b) as C14.

cancm (C1 * d). cancm (C2 * d). cancm (C3 * d). cancm (C4 * d).
cancm (C5 * d). cancm (C6 * d). cancm (C7 * d). cancm (C8 * d).
cancm (C9 * d). cancm (C10 * d). cancm (C11 * d). cancm (C12 * d).
cancm (C13 * d). rewrite inv_r X'zero GId. subst.

remember (c * b * a1 * b) as D1.
remember (D1 * c * b) as D2.
remember (D1 * a1 * b) as D3.
remember (D2 * a1 * b) as D4.
remember (D3 * a1 * b) as D5.
remember (D3 * c * b) as D6.
remember (D4 * a1 * b) as D7.
remember (D4 * c * b) as D8.
remember (D6 * a1 * b) as D9.
remember (D8 * a1 * b) as D10.

cancm (D4 * d). cancm (D3 * d). cancm (D10 * d). cancm (D9 * d).
cancm (D5 * d). subst.

remember (b * a1 * b) as E1.
remember (E1 * c * b) as E2.
remember (E1 * a1 * b) as E3.
remember (E2 * a1 * b) as E4.

cancm (E4 * d). subst.

rewrite (ZC1 _ _ k) //. ZCR. 
rewrite -?GA. rexpand. rsimpl. by rewrite -?plus_assoc. Qed.


End Aux1.