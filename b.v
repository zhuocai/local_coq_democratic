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

Record CertType: Type := mkCert {
    ct_proposal: LeaderProposalType;
    ct_voter: node; 
    ct_round: nat;
}.

Record CertProofType: Type := mkCertProof {
    cp_proposal: LeaderProposalType; 
    cp_certs: set CertType;
}.

Inductive MsgContentType: Type :=
    | leaderProposalMsg (leaderProposal:LeaderProposalType)
    | ackMsg (ack: AckType)
    | quitMsg (qt: QuitType).

Record FullBlockType:Type := mkBlock {
    bk_proposal: LeaderProposalType;
    bk_proof: CertProofType; 
}.

Inductive TimeoutType: Type :=
    | timeout_leader (leader: node)
    | timeout_voter (voter: node).

Inductive TriggerType: Type :=
    | trigger_timeout (timeout: TimeoutType)
    | trigger_msg (msg: MsgContentType). 

Variable block2hash: AggregatedProposalType->nat. (* *)

Variable confirmed_blocks: node->slot->FullBlockType. 

Definition block_equal (b1 b2: FullBlockType): Prop:=
    True. (* left as TODO *) 

(* ##### Part 2 ends *)

(* ##### Part 3: States, events and state transition rules *)
(* ##### Part 2 ends *)

(* ##### Part 3: States, events and state transition rules *)
Record State: Type:= mkState {
    st_slot: slot;
    st_committed_block: option FullBlockType;
}.

Record Event: Type:= mkEvent {
    ev_time: nat; 
    ev_node: node; 
    ev_trigger: TriggerType; 
}.

Definition state_transition (curr_state: State) (ev: Event): State :=
    curr_state.

Definition state_transition_op (curr_state: State) (ev: option Event): State :=
    match ev with
    | None => curr_state
    | Some ev' => state_transition curr_state ev'
    end.


Definition initial_states (n: node) :State:=
    mkState 0 None.

(* ##### Part 3 ends *)

(* ##### Part 4: Events ordering *)
(* ##### Part 3 ends *)

(* ##### Part 4: Events ordering *)


Variable node_id_to_event: node->nat->option Event. 

Fixpoint state_after_node_id (n:node) (i:nat): State:=
    match i with
    | 0 => initial_states n
    | S i' => let prev_state := state_after_node_id n i' in
        match node_id_to_event n i' with
            | None => prev_state
            | Some ev => state_transition prev_state ev
            end
    end.


(* ##### Part 4 ends *)

(* ##### Part 5: Triggers | many assumptions are here *)

(* assumption - honest committee members receive the largest honest winner block on time. *)
(* ##### Part 4 ends *)

(* ##### Part 5: Triggers | many assumptions are here *)

(* assumption - honest committee members receive the largest honest winner block on time. *)


(* ##### Part 5 ends *)

(* ##### Part 6: Intermediate Lemmas *)
(* ##### Part 6 ends *)


(* buffer: to move earlier *)
Variable is_committee: node->nat->Prop. (* actually based on its state *)

(* buffer: to move earlier *)

(* ##### Part 7: Big Lemmas *)



Lemma safety_slot_committee:
    forall s:slot, forall n1 n2: node, forall i1 i2:nat, forall b1 b2:FullBlockType, 
    let state1:=state_after_node_id n1 i1 in
    let state2:=state_after_node_id n2 i2 in
    state1.(st_slot) = s -> state2.(st_slot) = s ->
    is_committee n1 i1 -> is_committee n2 i2 ->



(* safety theorem: *)
Theorem safety: 
    forall s:slot, forall n1 n2:node, forall i1 i2:nat, forall b1 b2:FullBlockType, 
    let state1:=state_after_node_id n1 i1 in 
    let state2:=state_after_node_id n2 i2 in
    state1.(st_slot) = s -> state2.(st_slot) = s ->
    state1.(st_committed_block) = Some b1 -> state2.(st_committed_block) = Some b2 ->
    block_equal b1 b2.
Admitted.


(* liveness theorem: *)
Theorem liveness:
    forall n:node, forall s:slot, exists i:nat, 
    let state:=state_after_node_id n i in
    state.(st_slot) = s /\ state.(st_committed_block) <> None.
Admitted. 
(* ##### Part 7 ends*)

End RealDemocratic.