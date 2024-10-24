Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section Test.

(* 
prop_doublesum :: [Integer] -> Bool
prop_doublesum xs = 
    sum (map (\x -> 2*x) xs) = 2*(sum xs)
 *)

Definition sum_list := fold_right (fun x y=>x+y) 0. 

(* training prove mul_asso*)

Lemma inv_add:
    forall x:nat, forall y:nat,
        S (x+y) = S x +y.
        intros.
        simpl.
        reflexivity.
Qed.

Lemma add_reflx1:
    forall x:nat, 
        x + 1 = 1 + x. 
        intros.
        induction x.
        trivial. 
        simpl.
        rewrite -> IHx.
        reflexivity.       
Qed.

Lemma add_right: 
    forall x: nat, forall y:nat, 
        S (x+y) = x + S y.
    intros. 
    induction x. 
    reflexivity.
    assert (S x+y = S (x+y)).
    reflexivity.
    rewrite -> H.
    rewrite -> IHx.  
    trivial.

Qed.

Theorem add_reflx: 
    forall x:nat, forall y:nat,
        x+y = y+x.
        intros.
        induction x.
        1:induction y.
        reflexivity.
        simpl.
        assert (y+0=0+y).
        rewrite IHy.
        reflexivity.
        rewrite -> H.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHx. 
        rewrite add_right.
        reflexivity.
Qed.



Theorem add_asso:
    forall x:nat, forall y:nat, forall z:nat, 
        x+(y+z) = x+y+z.
        intros.
        induction x.
        trivial. (* x=0 done *)
        1:induction y.
        assert (S x+0 = S x).
        rewrite -> add_reflx.
        reflexivity.
        rewrite -> H.
        simpl.
        reflexivity. (* y = 0 done*)
        simpl.
        assert (x + S (y + z) = x+S y +z).
        simpl.
        rewrite inv_add.
        trivial.
        rewrite H.
        reflexivity.
Qed.

Theorem add_switch1:
    forall x:nat, forall y:nat, forall z:nat, 
        x + y + z = x + z + y .
    intros.
    split.
    rewrite add_reflx.
    rewrite add_asso.
    rewrite add_reflx.
    assert ((z+x) =(x+z)).
    rewrite add_reflx.
    trivial.
    rewrite H.
    rewrite add_reflx.
    trivial.
    rewrite add_reflx.
    rewrite add_asso.
    reflexivity.
    
Qed.

Theorem 


Lemma mul_reflx1:
    forall x:nat, forall y:nat, 
        x + x * y = x * S y.
        intros.
        induction x.
        trivial. (* x = 0 solved *)
        simpl.
        assert (x * S y = x+x*y).
        trivial. 
        rewrite -> IHx.
        reflexivity.
        assert ((y + x * S y) = y + x + x * y).
        rewrite -> H.
        rewrite add_asso.
        reflexivity.
        rewrite -> H0.
        assert (x + (y+x*y) = y+x+x*y).
        assert (x + (y+x*y) = x+y + x*y).
        rewrite add_asso.
        reflexivity.
        rewrite -> H1.
        assert (x+y = y+x).
        rewrite add_reflx.
        reflexivity.
        rewrite H2.
        reflexivity.
        rewrite H1.
        reflexivity.
Qed.

Theorem mul_reflx:
    forall x:nat, forall y:nat,
        x*y = y*x.
        intros.
        induction x. 
        trivial. (* x = 0 branch complete*)
        simpl.
        rewrite -> IHx. 
        rewrite mul_reflx1.
        reflexivity.
Qed.

Theorem mul_dist:
    forall x:nat, forall y:nat, forall z:nat, 
        x*(y+z) = x*y + x*z. 
        intros.
        induction x.
        simpl.
        reflexivity. (* x=0 done*)
        induction y.
        simpl.
        assert (x*0 =0).
        rewrite mul_reflx.
        reflexivity.
        rewrite H.
        reflexivity. (* y=0 done*)
        simpl.
        assert (x*S(y+z) = x*S y +x * z).
        assert (x*S(y+z) = x*(S y+z)).
        assert (S(y+z) = S y+z).
        trivial.
        rewrite H.
        trivial.
        rewrite H.
        rewrite IHx.
        trivial.
        rewrite H.
        rewrite add_asso.
        assert (y+x*S y + (z+x*z) = y+z + x*S y + x*z).
        



Qed.


Theorem mul_asso:
    forall x:nat, forall y:nat, forall z:nat, 
        (x*y)*z = x*(y*z).
        intros. 
        induction x.
        trivial. (* x = 0 complete *)
        induction y.
        assert (S x * 0 =0).
        rewrite mul_reflx.
        reflexivity.
        rewrite H.
        simpl.
        rewrite mul_reflx.
        reflexivity. (* y = 0 complete *)
        assert (S x * (S y * z) = (S y*z) + x * (S y *z)).
        reflexivity.
        rewrite H.
        assert (S y *z + x * (S y * z) = S y *z + (x * S y) * z).
        rewrite IHx.
        reflexivity.
        rewrite H0.
        simpl.



Qed.



Hypothesis mul_dist_hypo:
    forall x:nat, forall y:nat, forall z:nat, 
        x*(y+z) =x*y + x*z.

Theorem prop_doublesum :
    forall xs: list nat, 
        sum_list (map double xs) = double (sum_list xs).
        intros.
        induction xs.
        constructor.
        simpl.
        unfold double.
        unfold double in IHxs.
        rewrite -> IHxs.
        rewrite -> mul_dist_hypo.
        reflexivity. 
         
Qed. 


End Test.