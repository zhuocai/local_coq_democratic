Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section AMod.

Theorem simple:
    forall x:nat, forall y:nat, 
        x+ y = x+y.

        intros.
        reflexivity.

End AMod.