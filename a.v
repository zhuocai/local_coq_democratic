Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section AMod.



Inductive Opt: Set :=
| fail : Opt
| ok : bool -> Opt.


Theorem get: forall x: Opt, x<>fail -> bool.
    refine (fun x:Opt => 
    match x return x <> fail ->bool with
    | fail => _ 
    | ok b => fun _ =>b
    end ).
    intros; absurd(fail = fail).
    

Qed.


End AMod.