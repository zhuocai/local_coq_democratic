Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section AMod.

(* how to build a unique chain *)
Variable prev_nat: nat -> option nat. 

Hypothesis prev_0_is_none: prev_nat 0 = None.

Hypothesis prev_is_injective:
    forall a b, prev_nat a = prev_nat b -> a = b.

Theorem prev_is_injective_alt:
    forall a b, a <> b -> prev_nat a <> prev_nat b.
    intros. 
    intro.
    apply prev_is_injective in H0.
    contradiction.



End AMod.