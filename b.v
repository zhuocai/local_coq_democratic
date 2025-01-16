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
Variable nodes: set node. 
Definition n_nodes: nat:= length nodes.
Variable n_faulty:nat.
Definition n_committee: nat:= 2*n_faulty + 1.
Variable local_committees: node->slot->set node. 
Variable is_honest_bool: node->bool.
Definition is_honest (n:node):Prop
    := is_honest_bool n = true.


Definition node_eq_dec := Nat.eq_dec.

Lemma set_mem_iff_list_in: 
    forall n:node, forall setx: set node,
    set_mem node_eq_dec n setx = true <-> In n setx.
    intros.
    split.
    - apply set_mem_correct1.
    - apply set_mem_correct2.
Qed.

Hypothesis committee_size: forall s:slot, forall n:node, 
    length (local_committees n s) = n_committee.

Hypothesis committee_in_nodes: forall s:slot, forall n:node, 
    incl (local_committees n s) nodes.

Lemma com_in_nodes: forall s:slot, forall n_v: node, 
    forall n_com:node,
    set_mem node_eq_dec n_com (local_committees n_v s) = true -> set_mem node_eq_dec n_com nodes = true.
    intros.
    apply set_mem_iff_list_in in H.
    rewrite set_mem_iff_list_in.
    apply committee_in_nodes with (s:=s)(n:=n_v). auto.
Qed.

Definition is_committee_maj_honest (nodes: set node): Prop:=
    let honest_nodes:= filter is_honest_bool nodes in
    2*(length honest_nodes) > length nodes.



Definition in_committee_for_bool (n:node) (s:slot) (view: node): bool:=
    set_mem node_eq_dec n (local_committees view s).

Definition in_committee_for (n:node) (s:slot) (view: node): Prop:=
    set_mem node_eq_dec n (local_committees view s) = true.

Definition is_honest_node (n:node):Prop:=
    is_honest n /\ set_mem node_eq_dec n nodes = true.
Definition is_honest_node_bool (n:node):bool:=
    is_honest_bool n && set_mem node_eq_dec n nodes. 

Variable delta: nat. (* the communication delay *)
Variable interact_duration: nat. (* the time for proposal-voting-aggregation step *)
Variable slot_duration: nat. (* the upper limit of time from entering slot to confirming a block *)

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
    | aggProposalMsg (aggProposal: AggregatedProposalType)
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
Definition fullblock2aggblock (block: FullBlockType): AggregatedProposalType:=
    block.(bk_proposal).(lp_ap).

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
    


Definition is_fullblock_valid (block: FullBlockType): Prop:=
    True. (* left as TODO *)

Definition block_equal (b1 b2: FullBlockType): Prop:=
    fullblock2aggblock b1 = fullblock2aggblock b2. (* left as TODO *) 

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



Variable confirmed_blocks: node->slot->option FullBlockType. 

Variable enter_slot_seqid: node->slot->nat. 
Definition enter_slot_time (n:node) (s:slot):=
    match node_id_to_event n (enter_slot_seqid n s) with 
    | None => 0
    | Some ev => ev.(ev_time)
    end. 
Variable confirm_slot_seqid: node->slot->nat. 
Definition confirm_slot_time (n:node) (s:slot):=
    match node_id_to_event n (enter_slot_seqid n s) with
    | None => 0
    | Some ev => ev.(ev_time)
    end. 

Variable honest_winner_block: slot->AggregatedProposalType.

Variable certified_blocks: node->slot->nat->option LeaderProposalType. (* round *)

Variable acknowledged_blocks: node->slot->nat->option LeaderProposalType.

(* ##### Part 4 ends *)

(* ##### Part 5: Triggers | many assumptions are here *)

(* assumption - honest committee members receive the largest honest winner block on time. *)

Lemma nonemptyset_exists: 
    forall setx: set node,
    length setx > 0 -> exists n:node, set_mem node_eq_dec n setx = true.
    intros.
    destruct_with_eqn setx.
    inversion H.
    exists n. simpl. unfold node_eq_dec.
    destruct (Nat.eq_dec n n); auto. 
Qed.



Lemma setfilter_cond:
    forall setx: set node, forall f: node->bool,
    let subset:= filter f setx in
    forall n:node, set_mem node_eq_dec n subset = true -> set_mem node_eq_dec n setx = true /\ f n = true.
    intros.
    apply set_mem_iff_list_in in H.
    rewrite set_mem_iff_list_in.
    apply filter_In.
    auto.
Qed.


Hypothesis honest_majority: forall s:slot, forall n:node, 
    is_honest_node n -> is_committee_maj_honest (local_committees n s).

Hypothesis exists_honest_node:
    exists h_n:node, is_honest_node h_n.


Lemma exists_honest_com_node:
    forall s:slot, forall n_v:node,
    is_honest_node n_v ->
    exists n_hc:node,  in_committee_for n_hc s n_v /\ is_honest_node n_hc.
    intros.
    pose proof H as G.
    apply honest_majority with (s:=s)(n:=n_v) in G .
    unfold is_committee_maj_honest in G.
    remember (local_committees n_v s) as coms.
    remember (filter is_honest_bool coms) as honest_coms.
    assert (length honest_coms >0).
    lia.
    assert (exists n:node, set_mem node_eq_dec n honest_coms = true).
    apply nonemptyset_exists. auto.
    destruct H1.
    exists x. 
    unfold in_committee_for.
    rewrite <- Heqcoms. 

    (* a node from honest_coms is both honest and in_com *)
    rewrite Heqhonest_coms in H1.
    unfold is_honest_node.
    apply setfilter_cond in H1.
    destruct H1. split. auto. split. auto.
    
    apply com_in_nodes with (s:=s)(n_v:=n_v). rewrite <- Heqcoms. auto.
Qed.

Hypothesis confirmed_block_none_keeps_none: forall s:slot, forall n:node, 
    confirmed_blocks n s = None -> confirmed_blocks n (S s) = None.

Lemma confirmed_block_some_implies_some: forall s:slot, forall n:node, forall block: FullBlockType,
    confirmed_blocks n (S s) = Some block -> exists b, confirmed_blocks n s = Some b.
    intros.
    destruct_with_eqn (confirmed_blocks n s).
    exists f. auto.
    apply confirmed_block_none_keeps_none in Heqo. congruence.
Qed.

Hypothesis confirm_slot_sync: (* enter slot is defined as 1 unit of time after confirmation. Using a timeout. Just define a variable similar to the local chain.  *)
    forall s:slot, forall n1 n2:node, 
        confirm_slot_time n1 s <= (confirm_slot_time n2 s) + delta. 
(* Don't need enter slot time anymore. *)



Hypothesis receive_honest_winner_block:
    forall s:slot, forall n:node, forall b: FullBlockType, 
    is_honest_node n ->
    confirmed_blocks n s = Some b ->
    exists i:nat, exists ev: Event,
    node_id_to_event n i = Some ev /\
    ev.(ev_trigger) = trigger_msg (aggProposalMsg (honest_winner_block (s+1))) /\ (ev.(ev_time) > ((confirm_slot_time n s) + delta)) /\ (ev.(ev_time) < ((confirm_slot_time n s) + interact_duration)).


(* ##### Part 5 ends *)

(* ##### Part 6: Intermediate Lemmas *)
Lemma one_commit_other_committed:
    forall s:slot, forall n1 n2:node, forall block1: FullBlockType, 
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_blocks n1 s = Some block1 ->
    exists block2: FullBlockType,
    confirmed_blocks n2 s = Some block2.
Admitted. 

Definition confirm_same_block_pred (s:slot): Prop:=
    exists aggProposal: AggregatedProposalType, forall n:node,
    is_honest_node n ->
    exists block: FullBlockType,
    confirmed_blocks n s = Some block /\ fullblock2aggblock block = aggProposal.

(* here not mentioning the time *)


Lemma commit_implies_honest_certify:
    forall s:slot, forall n:node, forall fb:FullBlockType,
    is_honest_node n ->
    confirmed_blocks n s = Some fb ->
    exists com:node, is_honest_node com /\ in_committee_for com s n /\ let lp:= fb.(bk_proposal) in
    certified_blocks com s lp.(lp_round) = Some lp.
Admitted. 

(* ##### Part 6 ends *)


(* buffer: to move earlier *)

(* ##### Part 7: Big Lemmas *)


Hypothesis committee_determined_by_prevblocks:
    forall s:slot, forall n1 n2:node, forall block1 block2: FullBlockType,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_blocks n1 s = Some block1 -> 
    confirmed_blocks n2 s = Some block2 ->
    block_equal block1 block2 ->
    local_committees n1 (S s) = local_committees n2 (S s).

Hypothesis committee_same_s0:
    forall n1 n2:node, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committees n1 0 = local_committees n2 0.

(* a leader proposal's witness (f+1 ack) is known by node for slot and round *)
Variable lp_in_ackproof_node_slot_round: LeaderProposalType->node->slot->nat->Prop.


Lemma block_implies_committee_same_s1:
    forall s:slot, 
    confirm_same_block_pred s ->
    exists coms: set node, forall n:node, is_honest_node n ->
    local_committees n (S s) = coms. 

    intros.
    (* strategy choice: assume that there exist an honest node. use its coms.  *)
    destruct exists_honest_node as [n_h].
    remember (local_committees n_h (S s)) as coms.
    exists coms.
    intros.
    unfold confirm_same_block_pred in H.
    destruct H as [aggProposal].

    pose proof H0 as H0'.
    apply H in H0'.
    destruct H0' as [block1].
    destruct H2.

    pose proof H1 as H1'.
    apply H in H1'.
    destruct H1' as [block2].
    destruct H4.

    assert (block_equal block2 block1).
    unfold block_equal. rewrite H3. rewrite H5. auto.
    
    rewrite Heqcoms.
    apply committee_determined_by_prevblocks with (s:=s)(n1:=n)(n2:=n_h) (block1:=block2)(block2:=block1). auto. auto. auto. auto. auto. 
Qed.


Lemma block_implies_committee_pair_equal:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall n1 n2:node,
    is_honest_node n1 -> is_honest_node n2 ->
    local_committees n1 s = local_committees n2 s.

Admitted.

Lemma block_implies_committee_view_pair_equal:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall com n1 n2:node,
    is_honest_node n1 -> is_honest_node n2 ->
    in_committee_for com s n1 -> in_committee_for com s n2.
Admitted.


(* same slot, same round implication. *)
Lemma honest_cert_implies_honest_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall r:nat, forall lp:LeaderProposalType,
    forall n:node, is_honest_node n ->
    in_committee_for n s n ->
    certified_blocks n s r = Some lp ->
   acknowledged_blocks n s r = Some lp.

Admitted. 

(* assuming honest majority implicitly *)
Lemma important_lemma: 
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall n:node, forall lp: LeaderProposalType,
    is_honest_node n ->
    certified_blocks n s lp.(lp_round) = Some lp ->
    (forall n': node, is_honest_node n' -> (* saved the ack-witness in round lp_round *)
    in_committee_for n' s n' ->
    lp_in_ackproof_node_slot_round lp n' s lp.(lp_round)) /\ (* part 1: every other has ackproof *)
    (forall n'':node, is_honest_node n''->
    in_committee_for n'' s n'' ->
    exists lp':LeaderProposalType, acknowledged_blocks n'' s lp.(lp_round) = Some lp'-> lp' = lp).
Admitted.

Lemma comH_ackproofed_implies_no_conflict_honest_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall r:nat, forall lp:LeaderProposalType,
    (forall n:node, is_honest_node n ->
    in_committee_for n s n ->
    lp_in_ackproof_node_slot_round lp n s r) ->
    (forall r':nat, forall n':node, forall lp':LeaderProposalType, is_honest_node n' -> r<=r'  -> acknowledged_blocks n' s r' = Some lp'-> lp'.(lp_ap) = lp.(lp_ap)).
Admitted.

(* proof-chain: enter slot sync -> receive honest winner sync -> ! not required in safety, only required in liveness. *)

(* as long as every committee member of slot s, enters slot s with at most delta delay among each other, confirming on the same block in slot s-1 -> every node, will confirm the same block in slot s. With delta delay. *)
Lemma safety_per_slot_helper:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall n1 n2:node, forall block1 block2: FullBlockType,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_blocks n1 s = Some block1 ->
    confirmed_blocks n2 s = Some block2 ->
    let lp1:= block1.(bk_proposal) in
    let lp2:= block2.(bk_proposal) in
    lp1.(lp_round) <= lp2.(lp_round) ->
    block_equal block1 block2.

    intros. 
    (* confirm means receiving f+1 certify => at least one certify *)

    (* confirm block -> lp -> 
        early lp -> later honest nodes will not contribute to conflicting lps. 
    *)
    inversion H2. 
    assert (exists com:node, is_honest_node com /\ in_committee_for com s n1 /\ let lp1:= block1.(bk_proposal) in certified_blocks com s lp1.(lp_round) = Some lp1).
    apply commit_implies_honest_certify with (s:=s) (n:=n1). auto. auto.
    destruct H5 as [com_node].
    destruct H5 as [H5_1 [H5_2 H5_3]].

    simpl in H5_3.

    inversion H5_3.
    apply important_lemma with (s:=s) (n:=com_node) (lp:=lp1) in H7. 2:auto. 2:auto.

    destruct H7 as [H7_1 H7_2].

    inversion H3.
    assert (exists com:node, is_honest_node com /\ in_committee_for com s n2 /\ let lp:= block2.(bk_proposal) in certified_blocks com s lp.(lp_round) = Some lp).
    apply commit_implies_honest_certify with (s:=s) (n:=n2). auto. auto.
    destruct H5 as [com_node2].
    destruct H5 as [H8_1 [H8_2 H8_3]].
    simpl in H8_3.

    remember (lp2.(lp_round)-lp1.(lp_round)) as r_gap.
    assert (lp2.(lp_round) = lp1.(lp_round) + r_gap) by lia.


    assert (in_committee_for com_node s com_node).
    apply block_implies_committee_view_pair_equal with (s:=s) (com:=com_node) (n1:=n1)(n2:=com_node). auto. auto. auto. auto. 

    assert (in_committee_for com_node2 s com_node2).
    apply block_implies_committee_view_pair_equal with (s:=s) (com:=com_node2) (n1:=n2)(n2:=com_node2). auto. auto. auto. auto.

    (* com_node1/2 certs => also acked. *)

    assert(acknowledged_blocks com_node s lp1.(lp_round) = Some lp1).
    apply honest_cert_implies_honest_ack with (s:=s) (r:=lp1.(lp_round)) (lp:=lp1). auto. auto. auto. auto.

    assert(acknowledged_blocks com_node2 s lp2.(lp_round) = Some lp2).
    apply honest_cert_implies_honest_ack with (s:=s) (r:=lp2.(lp_round)) (lp:=lp2). auto. auto. auto. auto.


    specialize (H7_1 com_node H5_1 H8).
    specialize (H7_2 com_node H8_1 H9).

    pose proof H as H'.
    induction r_gap.
    (* in the same slot, no-one certifies a different block *)
    
    











Qed.

Lemma safety_per_slot:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall n1 n2:node, forall block1 block2: FullBlockType,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_blocks n1 s = Some block1 ->
    confirmed_blocks n2 s = Some block2 ->
    block_equal block1 block2.
    intros.
    remember (block1.(bk_proposal)) as lp1.
    remember (block2.(bk_proposal)) as lp2.

    assert ({lp1.(lp_round) <= lp2.(lp_round)} + {lp2.(lp_round)<lp1.(lp_round)}).
    apply le_lt_dec.

    destruct H4.
    apply safety_per_slot_helper with (s:=s)(n1:=n1)(n2:=n2)(block1:=block1)(block2:=block2). auto. auto. auto. auto. auto. rewrite <- Heqlp1. rewrite <-Heqlp2. auto.


    assert (block_equal block2 block1).
    apply safety_per_slot_helper with (s:=s)(n1:=n2)(n2:=n1)(block1:=block2)(block2:=block1). auto. auto. auto. auto. auto. rewrite <- Heqlp2. rewrite <-Heqlp1. lia.
    unfold block_equal. unfold block_equal in H4. auto.

Qed.

Lemma liveness_per_slot:
    forall s:slot, 
    (s = 0 \/ confirm_same_block_pred (s-1)) ->
    forall n:node, is_honest_node n -> 
    exists block: FullBlockType,
    confirmed_blocks n s = Some block /\ confirm_slot_time n s <= enter_slot_time n s + slot_duration.
Admitted.


(* safety theorem: *)
Theorem safety: 
    forall s:slot, forall n1 n2:node, forall block1 block2: FullBlockType,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_blocks n1 s = Some block1 ->
    confirmed_blocks n2 s = Some block2 ->
    block_equal block1 block2.
    intros.
    generalize H H0 H1 H2.
    generalize n1 n2 block1 block2. clear H H0 H1 H2. clear n1 n2 block1 block2.
    induction s. 
    intros.
    apply safety_per_slot with (s:=0)(n1:=n1)(n2:=n2)(block1:=block1)(block2:=block2). left. auto. auto. auto. auto. auto.

    intro n3. intro n4.
    intro block3. intro block4.
    intros.
    inversion H1. (* duplicate one. show that there is a confirmed block in slot s *)
    
    apply confirmed_block_some_implies_some in H4.

    assert (confirm_same_block_pred s). 
    unfold confirm_same_block_pred.
    destruct H4 as [b]. exists (fullblock2aggblock b). intros.


    inversion H3. 
    apply one_commit_other_committed with (s:=s) (n1:=n3) (n2:=n) (block1:=b) in H6.
    destruct H6 as [b'].
    exists b'. split. auto.
    apply IHs with (n1:=n)(n2:=n3) (block1:=b') (block2:=b). auto. auto. auto. auto. auto. auto. 

    apply safety_per_slot with (s:=S s)(n1:=n3)(n2:=n4)(block1:=block3)(block2:=block4).
    right. replace (S s - 1) with s by lia. auto.  auto. auto. auto. auto. 
Qed.


(* liveness theorem: *)
Theorem liveness:
    forall s:slot, forall n:node, 
    is_honest_node n -> 
        exists block: FullBlockType, 
        confirmed_blocks n s = Some block /\ confirm_slot_time n s <= enter_slot_time n s + slot_duration.
    intros.
    induction s. 
    apply liveness_per_slot with (s:=0)(n:=n). left. auto. auto. 

    assert (confirm_same_block_pred s).
    2:{apply liveness_per_slot with (s:=S s)(n:=n). right. replace (S s - 1) with s by lia. auto. auto. }
    
    unfold confirm_same_block_pred.
    destruct IHs as [b]. destruct H0. exists (fullblock2aggblock b).
    intros.

    inversion H0.
    apply one_commit_other_committed with (s:=s) (n1:=n) (n2:=n0) (block1:=b) in H4. 2:auto. 2:auto.
    destruct H4 as [b'].
    exists b'. split. auto.
    apply safety with (s:=s)(n1:=n0)(n2:=n)(block1:=b')(block2:=b). auto. auto. auto. auto. 
Qed. 
(* ##### Part 7 ends*)

End RealDemocratic.