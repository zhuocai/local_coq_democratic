Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Section AMod.



(* a real challenge in induction *)


Variable steps: nat->nat. 

Hypothesis step_0:
    steps 0 = 0.
Hypothesis step_increment:
    forall n:nat, steps n < 10 -> steps (S n) = steps n + 1.

Hypothesis step_increment2:
    forall n:nat, (steps n)>=10 -> steps (S n) = steps n. 

Theorem bound: forall n:nat, steps n <= 10.

    intros.
    induction n.
    rewrite -> step_0.
    lia.
    remember (10 -(steps n)) as x.
    destruct_with_eqn x.
    assert (steps n = 10) by lia.
    rewrite -> step_increment2.
    lia.
    lia.
    assert (steps n < 10) by lia.
    rewrite -> step_increment.
    lia.
    trivial.

Qed.

Theorem check: 
    (exists n:nat, 
        n = n+1) -> False.
    intros.
    destruct H.
    induction x.
    lia.
    lia.
Qed.
(* extract hint *)



Theorem leb_false: forall a b: nat, (a<=?b) = false -> a>b.
intros.
assert ({a<=b} + {a>b}).
apply le_gt_dec with (n:=a) (m:=b).
destruct H0.
assert (a<=?b = true).
apply Nat.leb_le. auto.
congruence.
auto.
Qed.


End AMod.