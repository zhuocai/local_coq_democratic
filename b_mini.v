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

Section BugMini. 

(* ##### Part 1: Useful Lemmas *)

(* ##### Part 1 ends *)

(* ##### Part 2: Basic Definition and Data Structures *)

Definition node:=nat.
Definition slot:=nat.
Variable n_faulty:nat.
Definition n_committee: nat:= 2*n_faulty + 1.
Variable local_committees: node->slot->set node. 
Variable is_honest_bool: node->bool.
Definition is_honest (n:node):Prop
    := is_honest_bool n = true.
Hypothesis committee_size: forall s:slot, forall n:node, 
    length (local_committees n s) = n_committee.
Definition is_committee_maj_honest (nodes: set node): Prop:=
    let honest_nodes:= filter is_honest_bool nodes in
    2*(length honest_nodes) > length nodes.


Definition node_eq_dec := Nat.eq_dec.

Definition in_committee_for (n:node) (s:slot) (view: node): bool:=
    set_mem node_eq_dec n (local_committees view s).

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

Variable aggblock2hash: AggregatedProposalType->nat. (* *)
(* Variable fullblock2hash: FullBlockType->nat. when pointing to a previous block, the previous block must be confirmed. However the confirmation quorum might be different for different nodes. Therefore, only define hash for aggregatedProposaltype *)

Definition fullblock2hash (block: FullBlockType): nat:=
    aggblock2hash block.(bk_proposal).(lp_ap).
Definition fullblock_prevhash (block: FullBlockType): nat:=
    block.(bk_proposal).(lp_ap).(ap_proposal).(pr_prevhash).

Variable agg_prevblock: AggregatedProposalType->FullBlockType. 
Definition full_prevblock (block: FullBlockType): FullBlockType:=
    agg_prevblock block.(bk_proposal).(lp_ap).

(* ##### Part 2 ends *)

(* ##### Part 3: States, events and state transition rules *)
(* ##### Part 2 ends *)

(* ##### Part 3: States, events and state transition rules *)

(* prev_block modeling the effect of hash chaining *)
Hypothesis aggprev_hash: 
    forall ap: AggregatedProposalType, 
    fullblock2hash (agg_prevblock ap) = ap.(ap_proposal).(pr_prevhash).
    

Variable confirmed_blocks: node->slot->option FullBlockType. 

Variable is_fullblock_valid: FullBlockType->Prop.

(* Definition is_fullblock_valid (block: FullBlockType): Prop:=
    True.  *)

Variable block_equal: FullBlockType->FullBlockType->Prop.

(* Definition block_equal (b1 b2: FullBlockType): Prop:=
    True. *)

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

Hypothesis honest_majority: forall s:slot, forall n:node, 
    is_honest n -> is_committee_maj_honest (local_committees n s).

Hypothesis confirmed_block_none_keeps_none: forall s:slot, forall n:node, 
    confirmed_blocks n s = None -> confirmed_blocks n (S s) = None.

Lemma confirmed_block_some_implies_some: forall s:slot, forall n:node, forall block: FullBlockType,
    confirmed_blocks n (S s) = Some block -> exists b, confirmed_blocks n s = Some b.
    intros.
    destruct_with_eqn (confirmed_blocks n s).
    exists f. auto.
    apply confirmed_block_none_keeps_none in Heqo. congruence.
Qed.
(* ##### Part 5 ends *)




Lemma safety_slot_induction_s0:
    forall n1 n2: node, forall block1 block2: FullBlockType,
    is_honest n1 -> is_honest n2 ->
    confirmed_blocks n1 0 = Some block1 ->
    confirmed_blocks n2 0 = Some block2 ->
    block_equal block1 block2.
Admitted.

(* safety theorem: *)
Theorem safety: 
    forall s:slot, forall n1 n2:node, forall block1 block2: FullBlockType,
    is_honest n1 -> is_honest n2 ->
    confirmed_blocks n1 s = Some block1 ->
    confirmed_blocks n2 s = Some block2 ->
    block_equal block1 block2.
    intros.
    generalize H1 H2.
    generalize block1 block2. clear H1 H2. clear block1 block2.
    induction s.
    intros.
    apply safety_slot_induction_s0 with (n1:=n1) (n2:=n2) (block1:=block1) (block2:=block2). auto. auto. auto. auto. 

    intro block3. intro block4. intros.
    inversion H1. inversion H2. (*duplicate*)
    apply confirmed_block_some_implies_some in H4.
    apply confirmed_block_some_implies_some in H5.
    destruct H4. destruct H5.
    assert (block_equal x x0).
    apply IHs with (block1:=x) (block2:=x0). auto. auto. 
    apply 


Qed.

End BugMini.