Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.


Section sync_hotstuff_sluggish_1block.

Variable delta : nat. 

Definition blockType := nat. (* 0 is a special empty block*)
Definition person := nat. 

Inductive certType : Type :=
    | empty
    | cert (block:blockType) (round: nat).

Inductive msgContentType : Type :=
    | propose (Bk: blockType) (round: nat) (cert: certType)
    | vote (Bk: blockType) (round:nat) (voter:person)
    | precommit (Bk: blockType) (round: nat) (voter:person).


Definition msgType := (person * person * msgContentType * nat) % type.

Variable isHonest : person -> bool.

Variable n_replicas : nat.

Fixpoint range (n:nat) : list nat :=
    match n with
    | O => []
    | S n' => n' :: range n'
    end.
Definition replicas := range n_replicas.


(* leader of round i is replica i%n. Where n is length replicas. And f+1 of them are honest *)

Hypothesis honestMajority: 
    length (filter isHonest replicas) * 2 > n_replicas.

Definition leaderOfRound (round:nat) : person :=
    nth (round mod n_replicas) replicas 0.

(* note that round starts from 0, replicas start from 0~n-1*)

Definition isLeader (round:nat) (replica:person) : bool :=
    Nat.eqb (leaderOfRound round) replica.

(*every one maintains a list of certified blocks (have f+1 ack)*)
(* for each round*)
Variable certifiedBlocks : person -> nat -> list blockType.

Variable viewOfHighestCertifiedBlock : person -> nat -> nat. (* problem with view 0. If there is no certified block, I want it to return -1? Let round starts with 1. *)

Hypothesis highestCertifiedBlock_def:
    forall p: person, forall r1: nat,
    ( forall r2:nat,
    r1 <= r2 ->
        length (certifiedBlocks p r1) > 0 ->
        (viewOfHighestCertifiedBlock p r2) >= r1) /\
        ((viewOfHighestCertifiedBlock p r1)>=0).


(* the list is sorted in descending order of block number *)

(* the list is sorted in descending order of round number *)

(* the list is sorted in descending order of block number *)

(* the list is sorted in descending order of round number *)

Variable incomingMessages : person -> list msgType.
Variable outgoingMessages : person -> list msgType.

(* communication assumptions. *)
Hypothesis synchrony:
    forall p1 p2: person, forall m: msgContentType, forall t1 t2: nat, 
        isHonest p1 = true -> isHonest p2 = true ->
        In (p1, p2, m, t1) (outgoingMessages p1) ->
        In (p1, p2, m, t2) (incomingMessages p2) /\
        t1<=t2 <= t1 + delta.

Hypothesis synchrony_incoming_implies_outgoing:
    forall p1 p2: person, forall m: msgContentType, forall t1 t2: nat, 
        isHonest p1 = true -> isHonest p2 = true ->
        In (p1, p2, m, t2) (incomingMessages p2) ->
        In (p1, p2, m, t1) (outgoingMessages p1) /\
        t1<=t2 <= t1 + delta.



(* the above two assumptions are not necessary. *)

(* the following two assumptions are necessary. *)
    

(* the list is sorted in ascending order of round number *)

Variable roundStartTime : person -> nat -> nat.

(* the time when the round starts *)
Variable roundEndTime : person -> nat -> nat.

Variable currentRound : person -> nat -> nat. 

Hypothesis currentRound_def: 
    forall p: person, forall t: nat, 
        let r := currentRound p t in 
        roundStartTime p r <= t < roundStartTime p (r+1). 

(* the time when the round ends *)

(* proposal of leader in slot s. If person is not leader in the slot, return arbitrary things. *)
Variable proposalsOfLeaders: person->nat-> (prod blockType certType).
(* the proposal of a leader is the block and the certificate. *)

(* the following two assumptions are necessary. *)

Hypothesis startAtZero: 
    forall p:person, forall r:nat, roundStartTime p r = 0.

Hypothesis roundStartAfterEnd:
    forall p:person, forall r:nat, roundStartTime p (r+1) = roundEndTime p r.
(* seems like in the sluggish protocol, there is no waiting. To be adjusted later. *)


Hypothesis leaderProposaR0_empty_cert:
    exists Bk: blockType,
        let l0:= leaderOfRound 0 in
            isHonest l0 = true -> proposalsOfLeaders l0 0 = (Bk, empty).

Hypothesis leaderProposeR0:
    forall p:person, 
        let l0 := leaderOfRound 0 in
        isHonest l0 = true -> In (p, l0, (propose (fst (proposalsOfLeaders l0 0)) 0 (snd (proposalsOfLeaders l0 0))), roundStartTime l0 0) (outgoingMessages l0).


(* new leaders should wait for 2*delta time after entering its view. One delta for others to enter view, another delta to let others send their locked cert. *)
Hypothesis leaderProposeRn:
    forall p:person, forall r:nat, 
        r>=1 ->
        let lr := leaderOfRound r in
        isHonest lr = true -> In (p, lr, (propose (fst (proposalsOfLeaders lr r)) r (snd (proposalsOfLeaders lr r))), (roundStartTime lr r) + 2*delta) (outgoingMessages lr).


(* the above only says that the leader of round 0 should propose. It does not say that an honest leader only send 1 and only send at time 0. *)
Hypothesis leaderPropose_proposal_in_time_AND_unique:
    forall l p:person, forall msg:msgContentType, forall t:nat,
        isHonest l = true -> 
        In (l, p, msg, t) (outgoingMessages l) ->
        exists (Bk:blockType) (r:nat) (cert:certType),
            msg = (propose Bk r cert) ->
        (
        let r' := currentRound p t in 
        let (Bk', cert') := proposalsOfLeaders l r' in
            r' = r /\ Bk' = Bk /\ cert' = cert
            /\ ((r=0 /\ t = roundStartTime l 0) \/ (r>=1 /\ t = (roundStartTime l r) + 2*delta))
        ).


(* vote | new-view is also a propose. *)

Definition isProposalValid (p:person) (Bk:blockType) (r:nat) (cert:certType) : bool :=
    if r =? 0 then
        match cert with
        | empty => true
        | _ => false
        end
    else
        match cert with
        | empty => 
        | cert Bk' r' => 
            if Bk =? Bk' then
                if r =? r' + 1 then
                    true
                else
                    false
            else
                false
        end.







End sync_hotstuff_sluggish_1block.