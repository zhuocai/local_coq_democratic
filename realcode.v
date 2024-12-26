Require Import List.
Require Import PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.ListDec.
Require Import Coq.Lists.ListSet. (* data structure of finite sets*)
Scheme Equality for list. 
Import ListNotations.

Section RealDemocratic. 

(* ##### Part 1: Useful Lemmas *)

(* ##### Part 1 ends *)

(* ##### Part 2: Basic Definition and Data Structures *)

Definition node:=nat.
Definition slot:=nat.
Variable committees: slot->set node. 


Variable delta: nat. (* the communication delay *)
Variable interact_duration: nat. (* the time for proposal-voting-aggregation step *)

Record PlainProposalType: Type := mkPlainProposal {
    pr_slot: slot;
    pr_proposer: node;
    pr_value: nat;
    pr_prevhash: nat;     
}.


Record AggregatedProposalType: Type := mkAggregatedProposal {
    ap_proposal: PlainProposalType;
    ap_weight: nat;
}.

Record AckType: Type := mkAck {
    ak_ap: AggregatedProposalType;
    ak_voter: node; 
    ak_round: nat;
}.

Record AckProofType: Type := mkAckProof {
    ap_ap: AggregatedProposalType;
    ap_acks: set AckType;
}.

Record LeaderProposalType: Type:=
    mkLeaderProposal {
        lp_ap: AggregatedProposalType;
        lp_proposal: node; 
        lp_round: nat; 
        lp_cert: option AckProofType; 
    }.

Record BlameType: Type := mkBlame {
    bl_slot: slot;
    bl_round: nat;
    bl_blamer: node;
}.

Record QuitBlameType: Type := mkQuitBlameType {
    qb_slot: slot;
    qb_round: nat;
    qb_blames: set BlameType;  
}. 

Record QuitConflictType: Type := mkQuitConflictType {
    qc_slot: slot;
    qc_round: nat;
    qc_proposal1: LeaderProposalType;
    qc_proposal2: LeaderProposalType;
}.

Inductive QuitType: Type :=
    | qt_conflict (qc: QuitConflictType)
    | qt_blame (qb: QuitBlameType).

Inductive MsgContentType: Type :=
    | winnerMsg (winnerProposal)
    | leaderProposalMsg (leaderProposal)
    | ackMsg (ack: AckType)
    | quitMsg (qt: QuitType)

Record BlockType:Type := mkBlock {
    bk_proposal: ProposalType;
    bk_proof: set CertType; 
}.


Variable block2hash: BlockType->nat. (* *)

Variable confirmed_blocks: node->slot->block. 
(* ##### Part 2 ends *)

(* ##### Part 3: States and state transition rules *)

(* ##### Part 3 ends *)

(* ##### Part 4: Events and ordering *)

(* ##### Part 4 ends *)

(* ##### Part 5: Triggers *)
(* ##### Part 5 ends *)

(* ##### Part 6: Intermediate Lemmas *)
(* ##### Part 6 ends *)



(* ##### Part 7: Big Lemmas *)

(* safety theorem: *)
Theorem safety: 
    forall s:slot, forall n1 n2:node, forall i1 i2:nat, 
    let state1:= state_after_node_id n1 i1 in 
    let state2:= state_after_node_id n2 i2 in
    state1.(st_slot) = s -> state2.(st_slot) = s ->
    state1.(st_committed) = true -> state2.(st_committed) = true ->
    state1.(st_confirmed_block) = state2.(st_value).
Qed. 
(* ##### Part 7 ends*)

End RealDemocratic.