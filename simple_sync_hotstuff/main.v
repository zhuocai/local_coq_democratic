Require Import List.
Require Import PeanoNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool.
Scheme Equality for list. 
Import ListNotations.


Section SyncHotStuff.

Variable delta : nat. 

Definition Node: Type := nat. 
Definition BlockType : Type := nat.

Definition is_element (a : nat) (b : list nat) : bool :=
  existsb (fun x => Nat.eqb x a) b.

Record Certificate: Type := mkCertificate {
  c_block : BlockType;
  c_round : nat;
  c_voters : list Node;
}.

Definition certificate_beq (c1 c2: Certificate): bool :=
    Nat.eqb c1.(c_block) c2.(c_block) && Nat.eqb c1.(c_round) c2.(c_round) && list_beq Node Nat.eqb c1.(c_voters) c2.(c_voters).

Record ProposalType: Type := mkProposalType {
  p_block: BlockType;
  p_round: nat;
  p_cert: option Certificate;
  p_proposer: Node;
}.

Definition proposal_beq (p1 p2: ProposalType): bool :=
    match p1.(p_cert), p2.(p_cert) with
    | None, None => Nat.eqb p1.(p_block) p2.(p_block) && Nat.eqb p1.(p_round) p2.(p_round) && Nat.eqb p1.(p_proposer) p2.(p_proposer)
    | Some c1, Some c2 => Nat.eqb p1.(p_block) p2.(p_block) && Nat.eqb p1.(p_round) p2.(p_round) && certificate_beq c1 c2 && Nat.eqb p1.(p_proposer) p2.(p_proposer)
    | _, _ => false
    end.

Record VoteType: Type := mkVoteType {
  v_block: BlockType;
  v_round: nat;
  v_voter: Node;
}.

Definition vote_beq (v1 v2: VoteType): bool :=
    Nat.eqb v1.(v_block) v2.(v_block) && Nat.eqb v1.(v_round) v2.(v_round) && Nat.eqb v1.(v_voter) v2.(v_voter).

Record PrecommitType: Type := mkPrecommitType {
  pc_block: BlockType;
  pc_round: nat;
  pc_voter: Node;
}.

Definition precommit_beq (pc1 pc2: PrecommitType): bool :=
    Nat.eqb pc1.(pc_block) pc2.(pc_block) && Nat.eqb pc1.(pc_round) pc2.(pc_round) && Nat.eqb pc1.(pc_voter) pc2.(pc_voter).


Record BlameType: Type := mkBlameType {
  b_round: nat;
  b_blamer: Node;
}.

Definition blame_beq (b1 b2: BlameType): bool :=
    Nat.eqb b1.(b_round) b2.(b_round) && Nat.eqb b1.(b_blamer) b2.(b_blamer).

Record QuitConflictType: Type := mkQuitConflictType {
  qc_round: nat;
  qc_proposal1: ProposalType;
    qc_proposal2: ProposalType;
}.

Definition quitconflict_beq (qc1 qc2: QuitConflictType): bool :=
    Nat.eqb qc1.(qc_round) qc2.(qc_round) && proposal_beq qc1.(qc_proposal1) qc2.(qc_proposal1) && proposal_beq qc1.(qc_proposal2) qc2.(qc_proposal2).

Record QuitBlameType: Type := mkQuitBlameType {
  qb_round: nat;
  qb_blames: list BlameType;
}.

Definition quitblame_beq (qb1 qb2: QuitBlameType): bool :=
    Nat.eqb qb1.(qb_round) qb2.(qb_round) && list_beq BlameType blame_beq qb1.(qb_blames) qb2.(qb_blames).

Inductive QuitType : Type :=
    | quit_conflict (qc: QuitConflictType)
    | quit_blame (qb: QuitBlameType).

Definition quittype_beq (qt1 qt2: QuitType): bool :=
    match qt1, qt2 with
    | quit_conflict qc1, quit_conflict qc2 => quitconflict_beq qc1 qc2
    | quit_blame qb1, quit_blame qb2 => quitblame_beq qb1 qb2
    | _, _ => false
    end.

Inductive MsgContentType : Type :=
    | msg_propose (proposal: ProposalType)
    | msg_vote (vote: VoteType)
    | msg_precommit (precommit: PrecommitType)
    | msg_blame (blame:BlameType)
    | msg_quit (qt: QuitType)
    | msg_highest_cert (cert:Certificate). 

Definition msgcontent_type_beq (msgc1 msgc2:MsgContentType):bool:=
    match msgc1, msgc2 with
    | msg_propose p1, msg_propose p2 => proposal_beq p1 p2
    | msg_vote v1, msg_vote v2 => vote_beq v1 v2
    | msg_precommit pc1, msg_precommit pc2 => precommit_beq pc1 pc2
    | msg_blame b1, msg_blame b2 => blame_beq b1 b2
    | msg_quit qt1, msg_quit qt2 => quittype_beq qt1 qt2
    | msg_highest_cert c1, msg_highest_cert c2 => certificate_beq c1 c2
    | _, _ => false
    end.



Record MsgType : Type := mkMsgType {
  msg_sender : Node;
  msg_recipient : Node; (* esop uses a list of recipients. we use a single node *)
  msg_content : MsgContentType;
  msg_send_time : nat; 
}.

Definition msg_beq (m1 m2:MsgType):bool :=
    (m1.(msg_sender) =? m2.(msg_sender)) && (m1.(msg_recipient) =? m2.(msg_recipient)) && msgcontent_type_beq m1.(msg_content) m2.(msg_content) && (m1.(msg_send_time) =? m2.(msg_send_time)).

Variable msg_receive_time: MsgType -> nat.

Variable isHonest: Node -> bool. 

Variable n_faulty: nat. 

(* #total nodes = 2*n_faulty+1. Actual faulty nodes: <= n_faulty *)

Definition replicas: list Node := List.seq 0 (2*n_faulty+1).

Hypothesis honest_majority: 
    length (filter isHonest replicas) >= 1+n_faulty.


Definition leaderOfRound (r: nat): Node := (r mod (2*n_faulty+1)).

(* First define events, then define states*)

Inductive TimeoutType: Type := 
    | timeout_proposal 
    | timeout_precommit 
    | timeout_quit_status 
    | timeout_new_view_wait.

Definition timeouttype_beq (t1 t2: TimeoutType): bool :=
    match t1, t2 with
    | timeout_proposal, timeout_proposal => true
    | timeout_precommit, timeout_precommit => true
    | timeout_quit_status, timeout_quit_status => true
    | timeout_new_view_wait, timeout_new_view_wait => true
    | _, _ => false
    end.

Inductive TriggerType: Type:= 
    | trigger_msg_receive (msg: MsgType)
    | trigger_timeout (timeout: TimeoutType) (node:Node) (round: nat) (expire_time: nat). 



Definition triggertype_beq (t1 t2: TriggerType): bool :=
    match t1, t2 with
    | trigger_msg_receive msg1, trigger_msg_receive msg2 => msg_beq msg1 msg2
    | trigger_timeout timeout1 node1 r1 t1, trigger_timeout timeout2 node2 r2 t2 => Nat.eqb r1 r2 && Nat.eqb t1 t2 && timeouttype_beq timeout1 timeout2 && Nat.eqb node1 node2
    | _, _ => false
    end.

Record Event: Type := mkEvent {
    ev_node: Node;
    ev_trigger: option TriggerType; (* None <=> node is arbitrary *)
    ev_time: nat;
}.


Variable event_happen_before: Event -> Event -> Prop.
Variable direct_pred: Event -> option Event. 

Variable event_to_history: Event-> list Event. 

Hypothesis event_history_def:
    forall e:Event, 
    (direct_pred e = None -> event_to_history e = [e]) /\
    (exists e_pred:Event, direct_pred e = Some e_pred -> event_to_history e = (e::(event_to_history e_pred))).

(* note that two events might trigger the same event. for example, two different events can generate the same message sending. Therefore, the event_his_beq further requires that the history of the two events are exactly the same. *)
Definition event_beq (e1 e2: Event): bool :=
    Nat.eqb e1.(ev_node) e2.(ev_node) && Nat.eqb e1.(ev_time) e2.(ev_time) && 
    match e1.(ev_trigger), e2.(ev_trigger) with
    | None, None => true
    | Some t1, Some t2 => 
        triggertype_beq t1 t2
    | _, _ => false
    end.

Definition event_his_beq (e1 e2:Event): bool:=
    list_beq Event event_beq (event_to_history e1) (event_to_history e2).

(* properties of events: 1. ordering *)

Hypothesis event_ordering_by_time: forall e1 e2:Event, 
    e1.(ev_time) < e2.(ev_time) -> event_happen_before e1 e2.
Hypothesis event_ordering_by_node: forall e1 e2:Event, 
    e1.(ev_time) = e2.(ev_time) -> e1.(ev_node) < e2.(ev_node) -> event_happen_before e1 e2.

Hypothesis event_ordering_msg_before_timeout: forall e1 e2: Event, 
    e1.(ev_time) = e2.(ev_time) -> e1.(ev_node) = e2.(ev_node) -> exists msg, e1.(ev_trigger) = Some (trigger_msg_receive msg) -> exists timeout t_node t_round t_expire_time, e2.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> event_happen_before e1 e2.

Hypothesis event_ordering_reflexive: forall e:Event, event_happen_before e e.

Hypothesis event_ordering_decisive: forall e1 e2:Event, (e1 = e2) \/ ((event_happen_before e1 e2 -> not (event_happen_before e2 e1)) /\ (not (event_happen_before e1 e2) -> event_happen_before e2 e1)). 

Hypothesis event_ordering_transitive: forall e1 e2 e3:Event, 
    event_happen_before e1 e2 -> event_happen_before e2 e3 -> event_happen_before e1 e3.

Hypothesis direct_pred_ordering: forall e1 e2:Event, 
    direct_pred e1 = Some e2 -> e1.(ev_node) = e2.(ev_node) /\ event_happen_before e2 e1.

Record StateType: Type := mkState {
    st_round: nat;
    st_committed: bool;
    st_locked_highest_cert: option Certificate; (* the highest block is included in the highest cert*)
    (* the locked certificate only gets updated during the quit round break *)
    st_dynamic_highest_cert: option Certificate; 
    st_all_certs: nat -> BlockType -> list Node; (* round -> block -> list of voters *)
    st_round_start_time: nat; 
    st_first_valid_proposal: option ProposalType;
    st_first_received_proposals: option ProposalType; (* for forwarding them. Always forward the first two different proposals. Here the proposals can fail the certificate check. *)
    st_receive_valid_proposals_from: list Node; (* should be made non-repetitive *)
    st_quit_round_time: option nat;
    st_received_blames: list BlameType;
    (* st_has_voted: bool; same as received proposal *)
    st_vote: option VoteType;
    st_precommit_time: option nat; (* start precommit timer*)
    st_received_precommits_from: list Node;
    st_new_view_timeouted: bool;

}.

(* use the following interfaces to modify some fields of the state *)

Definition state_set_first_received_proposal (curr_state:StateType) (proposal:ProposalType): StateType:=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    (Some proposal) (*curr_state.(st_first_received_proposals) *)
    curr_state.(st_receive_valid_proposals_from)
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_first_valid_proposal (curr_state:StateType) (proposal:ProposalType) (msg_sender: Node) (node:Node): StateType :=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    (*set curr_state.(st_first_valid_proposal)*)
    (Some proposal)
    (* curr_state.(st_first_received_proposals)  *)
    (Some proposal)
    (* curr_state.(st_receive_valid_proposals_from) *)
    [msg_sender]
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    (* curr_state.(st_vote)  *)
    (Some (mkVoteType proposal.(p_block) proposal.(p_round) node))
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

(* handle repetition. *)
(* *)
Definition state_set_more_proposals (curr_state:StateType) (proposal: ProposalType)  (msg_sender: Node): StateType:=
    if is_element msg_sender curr_state.(st_receive_valid_proposals_from) then curr_state
    else 
        mkState curr_state.(st_round) 
        curr_state.(st_committed) 
        curr_state.(st_locked_highest_cert)
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs) 
        curr_state.(st_round_start_time)
        curr_state.(st_first_valid_proposal)
        curr_state.(st_first_received_proposals) 
        (* curr_state.(st_receive_valid_proposals_from) *)
        (msg_sender::curr_state.(st_receive_valid_proposals_from))
        curr_state.(st_quit_round_time)
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition blames_to_blamers: list BlameType -> list Node := 
    map (fun b => b.(b_blamer)).

Definition state_set_receive_blame (curr_state:StateType) (blame:BlameType) : StateType :=
    if is_element blame.(b_blamer) (blames_to_blamers curr_state.(st_received_blames)) then curr_state
    else 
        mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposals) 
    curr_state.(st_receive_valid_proposals_from)
    curr_state.(st_quit_round_time) 
    (blame::curr_state.(st_received_blames)) (*set*)
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_receive_qt (curr_state:StateType) (qt:QuitType) (time: nat): StateType :=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposals) 
    curr_state.(st_receive_valid_proposals_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_quit_blame (curr_state:StateType) (time: nat): StateType :=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposals) 
    curr_state.(st_receive_valid_proposals_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_quit_conflict (curr_state:StateType) (time: nat): StateType :=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposals) 
    curr_state.(st_receive_valid_proposals_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_precommit_start (curr_state:StateType) (time:nat):StateType:=
    mkState curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposals) 
    curr_state.(st_receive_valid_proposals_from)
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    (* curr_state.(st_precommit_time)  *)
    (Some time)
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

Definition update_all_certs (all_certs: nat -> BlockType -> list Node) (new_vote: VoteType): nat -> BlockType -> list Node :=
    fun r b => 
    if (r =? new_vote.(v_round)) && (b =? new_vote.(v_block)) then
     if is_element new_vote.(v_voter) (all_certs r b) then all_certs r b 
     else new_vote.(v_voter)::(all_certs r b)
    else all_certs r b.

Definition update_highest_cert (highest_cert: option Certificate) (all_certs: nat -> BlockType -> list Node) (new_vote: VoteType): option Certificate :=
    let new_all_certs := update_all_certs all_certs new_vote in
    if (length (new_all_certs new_vote.(v_round) new_vote.(v_block)) =? n_faulty+1) then
        match highest_cert with
        | None => Some (mkCertificate new_vote.(v_block) new_vote.(v_round) (new_all_certs new_vote.(v_round) new_vote.(v_block)))
        | Some cert =>
            if cert.(c_round) <? new_vote.(v_round) then Some (mkCertificate new_vote.(v_block) new_vote.(v_round) (new_all_certs new_vote.(v_round) new_vote.(v_block)))
            else Some cert
        end
    else highest_cert.

(* update highest cert, all certs, vote *)
(* TODO fix bug: fix highest_cert during slot, updating during the quit_round break.   *)
Definition state_set_receive_vote (curr_state:StateType) (vote:VoteType):StateType:=
    mkState 
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert) 
    (* curr_state.(st_dynamic_highest_cert) *)
    (update_highest_cert curr_state.(st_dynamic_highest_cert) curr_state.(st_all_certs) vote) 
    (* curr_state.(st_all_certs) *)
    (update_all_certs curr_state.(st_all_certs) vote) 
    curr_state.(st_round_start_time) 
    curr_state.(st_first_valid_proposal) 
    curr_state.(st_first_received_proposals)
    curr_state.(st_receive_valid_proposals_from) 
    curr_state.(st_quit_round_time) 
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommits_from)
    curr_state.(st_new_view_timeouted).

(* also set the locked highest cert *)
Definition state_set_enter_new_round (curr_state:StateType) (time: nat): StateType :=
    mkState (curr_state.(st_round)+1) false 
    curr_state.(st_dynamic_highest_cert) (*set locked highest cert*) 
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    time None None [] None [] None None [] false.

(* collect and count |
Question: is it possible to receive precommit before receiving a proposal? 
If no valid proposal is received at t => no valid proposal is received at any honest node at t-delta => will not send precommit by t+delta. 
*)
Definition state_set_receive_precommit (curr_state:StateType) (precommit: PrecommitType) : StateType :=
    if is_element precommit.(pc_voter) curr_state.(st_received_precommits_from) then curr_state
    else 
        mkState
        curr_state.(st_round) 
        curr_state.(st_committed) 
        curr_state.(st_locked_highest_cert) 
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposals)
        curr_state.(st_receive_valid_proposals_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        (* curr_state.(st_received_precommits_from) *)
        (precommit.(pc_voter)::curr_state.(st_received_precommits_from))
        curr_state.(st_new_view_timeouted).

(* commit the current proposal. *)


(* once committed, the state of the node will not change any more. The committed proposal is exactly curr_state.(st_current_proposal)*)
Definition state_set_commit (curr_state:StateType) (time:nat) : StateType :=
    mkState
        curr_state.(st_round) 
        (* curr_state.(st_committed)  *)
        true
        curr_state.(st_locked_highest_cert) 
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposals)
        curr_state.(st_receive_valid_proposals_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommits_from)
        curr_state.(st_new_view_timeouted).

Definition state_set_dynamic_highest_cert (curr_state:StateType) (cert:Certificate): StateType :=
    mkState
        curr_state.(st_round) 
        curr_state.(st_committed)
        curr_state.(st_locked_highest_cert) 
        (Some cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposals)
        curr_state.(st_receive_valid_proposals_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommits_from)
        curr_state.(st_new_view_timeouted).

Definition state_set_recv_cert (curr_state:StateType) (cert:Certificate): StateType:=
    match curr_state.(st_dynamic_highest_cert) with 
    | None =>  state_set_dynamic_highest_cert curr_state cert
    | Some old_cert => 
        if old_cert.(c_round) <? cert.(c_round) then state_set_dynamic_highest_cert curr_state cert
        else curr_state
    end.

Definition state_set_new_view_timeout (curr_state:StateType): StateType:=
    mkState
        curr_state.(st_round) 
        curr_state.(st_committed)
        curr_state.(st_locked_highest_cert)
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposals)
        curr_state.(st_receive_valid_proposals_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommits_from)
        (* curr_state.(st_new_view_timeouted). *)
        true.


(* checks proposal round, leader-proposer, cert*)
Definition is_proposal_valid_round_proposer (proposal: ProposalType) (curr_state: StateType): bool := 
    Nat.eqb proposal.(p_round) curr_state.(st_round) && Nat.eqb proposal.(p_proposer)  (leaderOfRound curr_state.(st_round)).

Definition is_proposal_valid_cert (proposal: ProposalType) (curr_state: StateType): bool := 
    is_proposal_valid_round_proposer proposal curr_state 
    && (
        match curr_state.(st_locked_highest_cert) with
        | None => true
        | Some cert => cert.(c_round) <=? proposal.(p_round)
        end
    ). 

(* state transition rule applies to any node. *)
(* Byzantine nodes can arbitrarily send messages. (for honest nodes, every trigger must be generated fairly, except messages sent by Byzantine nodes.) *)

(* priority order:
    1. committed: if committed, do not change anymore. 
    2. has quited current round (means not entering a new round) - only waiting and forming certificates using votes. update locked highest cert. 
    3. case by trigger
        case by msgs
            proposal => 
                first_proposal => valid (vote) | invalid
                second_different_proposal => quit conflict
                first_proposal from more senders => <= f | = f+1 -> (precommit start)
            vote => 
                collect votes - form certificates - update dynamic    highest cert. 
            blame => collect blames - form quit - quit and broadcast. 
            precommit => collect precommits - commit. 
            quit => quit
        case by trigger
            proposal timeout => blame
            precommit timeout => broadcast precommit
            quit_status timeout => enter new round
            new_view_wait timeout => leader send proposal. 

 *)

 Definition state_transition_receive_proposal (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
    | Some(trigger_msg_receive msg) =>
    match msg.(msg_content) with
    | msg_propose proposal =>
        match curr_state.(st_first_received_proposals) with
        | None  =>
            if is_proposal_valid_cert proposal curr_state then
                state_set_first_valid_proposal curr_state proposal  msg.(msg_sender) e.(ev_node)
            else if is_proposal_valid_round_proposer proposal curr_state then
                state_set_first_received_proposal curr_state proposal
            else curr_state
        | Some first_proposal =>
            if proposal_beq proposal first_proposal then (*receiving the same first proposal again*)
                match curr_state.(st_first_valid_proposal) with 
                | None => curr_state (*receiving the same cert-invalid proposal, ignore*)
                | Some valid_proposal => (* the first proposal is valid, now receiving one more proposal that is the same. *)
                    if proposal_beq proposal valid_proposal then 
                        if 1+n_faulty <=? (length curr_state.(st_receive_valid_proposals_from)) then (*already pre-committed. ignore the msg*)
                            curr_state
                        else (*need more proposals*)
                            let temp_state := state_set_more_proposals curr_state proposal msg.(msg_sender) in
                            if (1+n_faulty) <=? (length (temp_state.(st_receive_valid_proposals_from))) then (*trigger precommit start*) 
                                state_set_precommit_start temp_state e.(ev_time)
                        else temp_state
                    else (* should not happen in our logic *)
                        curr_state
                end
            else (* receiving a different proposal | totally-invalid or cert-invalid or valid | total_invalid => ignore / otherwise => duplicate report quit *)
                if is_proposal_valid_round_proposer proposal curr_state then
                    state_set_quit_conflict curr_state e.(ev_time)
                else curr_state
        end
    | _ => curr_state (*other msg type*)
    end
    | _ => curr_state (*other trigger type*)
    end.
    

Definition state_transition (e: Event) (curr_state: StateType) : StateType := 
    if curr_state.(st_committed) then curr_state 
    else match curr_state.(st_quit_round_time) with 
    | Some quit_time =>  (* receiving votes | waiting for delta timeout to enter next round*)
        match e.(ev_trigger) with
        | None => curr_state
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_vote vote => 
                if vote.(v_round) =? curr_state.(st_round) then 
                    state_set_receive_vote curr_state vote
                else curr_state
            | _ => curr_state
            end
        | Some (trigger_timeout timeout t_node t_round t_expire_time) =>
            match timeout with
            | timeout_quit_status => 
                if t_round =? curr_state.(st_round) then 
                    state_set_enter_new_round curr_state e.(ev_time)
                else curr_state
            | _ => curr_state
            end
        end
    | None => (* has not quitted or committed *)
        match e.(ev_trigger) with
        | None => curr_state
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_quit qt => 
                match qt with
                | quit_conflict qc => 
                    if qc.(qc_round) =? curr_state.(st_round) then 
                        state_set_receive_qt curr_state qt e.(ev_time)
                    else curr_state
                | quit_blame qb => 
                    if qb.(qb_round) =? curr_state.(st_round) then 
                        state_set_receive_qt curr_state qt e.(ev_time)
                    else curr_state
                end
            | msg_blame blame => (* check if blame reaches f+1*)
                if blame.(b_round) =? curr_state.(st_round) then
                    let temp_state := state_set_receive_blame curr_state blame in
                    if (1+n_faulty) <=? (length temp_state.(st_received_blames)) then 
                        state_set_quit_blame temp_state e.(ev_time)
                    else temp_state
                else curr_state
            | msg_propose proposal =>
                state_transition_receive_proposal e curr_state
            | msg_vote vote => (* vote is used to form certificates  *)
                state_set_receive_vote curr_state vote
            | msg_precommit precommit => (*require at least received proposal*)
                if (precommit.(pc_round) =? curr_state.(st_round)) then 
                    match curr_state.(st_first_valid_proposal) with 
                        | None => curr_state 
                        | Some valid_proposal =>
                        if (valid_proposal.(p_block) =? precommit.(pc_block)) then 
                            let temp_state:= state_set_receive_precommit curr_state precommit in (* if curr_state has received f+1 precommits already, would have committed. will not enter this function*)
                            if (1+n_faulty) <=? (length temp_state.(st_received_precommits_from)) then
                                state_set_commit temp_state e.(ev_time)
                            else temp_state
                        else curr_state (* ignore precommit for other proposals*)
                    end
                else curr_state (*ignore precommit for other rounds*)
            | msg_highest_cert cert => 
                if e.(ev_node) =? (leaderOfRound curr_state.(st_round)) then 
                    if curr_state.(st_new_view_timeouted) then curr_state (*too late*)
                        else state_set_recv_cert curr_state cert
                else curr_state
            end     
        | Some(trigger_timeout timeout t_node t_round t_expire_time) =>
            match timeout with
                | timeout_proposal => 
                    curr_state (* might send blame out | but handled in generating trigger*)
                | timeout_precommit =>
                    curr_state (* might send precommit message | but handled in generating trigger *)
                | timeout_quit_status =>
                    curr_state (* should not happen | already handled in the beginning of the function *)
                | timeout_new_view_wait =>
                    (* should broadcast new proposals | to handle in generating trigger *)
                    state_set_new_view_timeout curr_state
            end
        end
    end.

Variable init_state: StateType.

Variable state_before_event: Event -> StateType. 
Variable state_after_event: Event -> StateType. 

(* Variable messages_after_event: Event -> option (list MsgType).
Variable timeouts_after_event: Event -> option (list TimeoutType). *)

Hypothesis init_state_def: 
    init_state.(st_round) = 0 /\ 
    init_state.(st_committed) = false /\ 
    init_state.(st_locked_highest_cert) = None /\ 
    init_state.(st_dynamic_highest_cert) = None /\ 
    init_state.(st_all_certs) = (fun r b => []) /\ 
    init_state.(st_round_start_time) = 0 /\ 
    init_state.(st_first_valid_proposal) = None /\
    init_state.(st_first_received_proposals) = None /\
    init_state.(st_receive_valid_proposals_from) = [] /\
    init_state.(st_quit_round_time) = None /\
    init_state.(st_received_blames) = [] /\
    init_state.(st_vote) = None /\
    init_state.(st_precommit_time) = None /\
    init_state.(st_received_precommits_from) = [].

Hypothesis state_before_first_event:
    forall e:Event, direct_pred e = None -> state_before_event e = init_state.

Hypothesis state_recursive_def: 
    forall e:Event, 
    state_after_event e = state_transition e (state_before_event e).

Hypothesis state_direct_pred_def:
    forall e1 e2:Event, 
    direct_pred e2 = Some e1 -> state_after_event e1 = state_before_event e2.


(* a trigger -> event -> state update && new triggers. All new triggers should be attributed to the event. *)

Variable generators_of_triggers: TriggerType -> Event. 
Variable triggers_generated_by_event: Event -> list TriggerType. 

(* the first event is the special event, which generates the first timeout && first proposal. *)

Variable first_events: Node->Event. 

Variable first_event_def: 
    forall n:Node,  n<1+2*n_faulty ->
    let e := first_events n in
    e.(ev_node) = n /\ e.(ev_time) = 0 /\ e.(ev_trigger) = None /\ direct_pred e = None.

(* every event has a trigger. except the special first_event *)

Hypothesis honest_event_triggered_by_something: forall e:Event, 
    isHonest e.(ev_node) = true -> not (direct_pred e = None) -> exists trigger,  e.(ev_trigger) = Some trigger.

Hypothesis synchrony: 
    forall msg:MsgType, msg_receive_time msg >= msg.(msg_send_time) /\ msg_receive_time msg <= msg.(msg_send_time) + delta.

Hypothesis honest_event_triggered_by_msg_at_recv_time: 
    forall e:Event, 
        isHonest e.(ev_node) = true -> (exists msg:MsgType, e.(ev_trigger) = Some (trigger_msg_receive msg) -> (msg_receive_time msg) = e.(ev_time)).

Hypothesis honest_event_triggered_by_msg_at_receiver:
    forall e:Event, 
        isHonest e.(ev_node) = true -> (exists msg:MsgType, e.(ev_trigger) = Some (trigger_msg_receive msg) -> msg.(msg_recipient) = e.(ev_node)).

Hypothesis honest_event_triggered_by_timeout_at_expire_time:
    forall e:Event, 
        isHonest e.(ev_node) = true -> (exists timeout t_node t_round t_expire_time, e.(ev_trigger) = Some (trigger_timeout t_node timeout t_round t_expire_time) -> e.(ev_time) = t_expire_time).
Hypothesis honest_event_triggered_by_timeout_of_itself:
    forall e:Event, 
        isHonest e.(ev_node) = true -> (exists timeout t_node t_round t_expire_time, e.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> (t_node = e.(ev_node))).

(* An event generate some events in the future. If it is timeout type, the trigger is exactly generated. If it is sending a message, the message receive time might be delayed by at most delta after the sending time. *)

(* default first block is 1 *)




Variable event_ancestor: Event -> Event. 

(* the first event is the ancestor of all events. *)
Hypothesis event_ancestor_def:
    forall e:Event, (direct_pred e = None -> event_ancestor e = e) /\
    (exists e_pred:Event, direct_pred e = Some e_pred -> ((event_ancestor e) = (event_ancestor e_pred))).

(* every event has a unique ancestor. *)
Hypothesis events_of_node_form_a_path:
    forall e: Event, 
        e.(ev_node) < 1+2*n_faulty ->
        isHonest e.(ev_node) = true ->
        event_his_beq (event_ancestor e) (first_events e.(ev_node)) = true.



Hypothesis all_events_are_triggered_by_previous_events:
    forall e2:Event,
        isHonest e2.(ev_node) = true -> 
        not (direct_pred e2 = None) -> (*e2 is not the special previous events*)
        match e2.(ev_trigger) with
        | None => False (* should not happen for honest nodes *)
        | Some trigger => 
            exists e1:Event, (e1 = generators_of_triggers trigger) /\ In trigger (triggers_generated_by_event e1)
        end.

(* A list of all triggers to consider.
1. proposal-receiving timeout of the first round (handled by first_event)
2. leader of first round sending proposal to all replicas (handled by first event)
3. upon receiving the first proposal => (broadcast) forward the proposal & vote (broadcast) 
*)

Definition node_to_msg (sender:Node) (content:MsgContentType) (send_time:nat) (node:nat) : MsgType :=
    mkMsgType sender node content send_time.

Definition broadcast_msgs (sender:Node) (content:MsgContentType) (send_time: nat): list MsgType :=
    map (node_to_msg sender content send_time) replicas. 

Definition broadcast_msgs_to_trigger_list (sender:Node) (content:MsgContentType) (send_time: nat): list TriggerType :=
    map (fun msg => trigger_msg_receive msg) (broadcast_msgs sender content send_time).

Definition triggers_generated_by_receiving_a_proposal_def (e:Event) (proposal:ProposalType) (prev_state:StateType) (new_state:StateType): list TriggerType :=
    []

.


(* no worries about forwarding quit messages multiple times: once quit (recv f+1 blame or recv quit), forward it, then never handle the following*)
Definition triggers_generated_by_receiving_def (e: Event) (msg:MsgType) (prev_state:StateType) (new_state:StateType): list TriggerType :=
    match msg.(msg_content) with
    | msg_propose proposal =>
        triggers_generated_by_receiving_a_proposal_def e proposal prev_state new_state
    | msg_vote vote =>
        [] (*just form certificates locally*)
    | msg_blame blame => (* if forming f+1 blames, broadcast quit blame*)
        if (length (prev_state.(st_received_blames)) <=? n_faulty) && (1+n_faulty <=? (length (new_state.(st_received_blames)))) then 
            broadcast_msgs_to_trigger_list e.(ev_node) (msg_quit (quit_blame (mkQuitBlameType prev_state.(st_round) new_state.(st_received_blames)))) e.(ev_time)
        else []
    | msg_quit qt =>
        (broadcast_msgs_to_trigger_list e.(ev_node) (msg_quit qt) e.(ev_time)) ++ 
        [trigger_timeout timeout_quit_status e.(ev_node) (prev_state.(st_round)) (e.(ev_time) + delta)] (*forward & timer*)
    | msg_highest_cert cert =>
        [] (*just update the dynamic highest cert*)
    | msg_precommit precommit =>
        [] (*just collect precommits | will commit locally if reach f+1*)
    end
    .

Variable honest_default_proposal_of_round: nat -> BlockType.

Definition triggers_generated_by_timout_def (e:Event) (timeout:TimeoutType) (node:Node) (round:nat) (expire_time:nat) (prev_state:StateType) (new_state:StateType): list TriggerType :=
    match timeout with
    | timeout_proposal => 
        match prev_state.(st_first_valid_proposal) with 
        | None =>  
            broadcast_msgs_to_trigger_list e.(ev_node) (msg_blame (mkBlameType round e.(ev_node))) e.(ev_time)
        | Some valid_proposal => [] (*already received a valid proposal*)
        end
    | timeout_precommit => (* broadcast precommit message if condition matches*)
        match prev_state.(st_quit_round_time) with
        | None => 
            match prev_state.(st_first_valid_proposal) with
            | None => [] (*shuold not happen. If h precommits, it must have received a valid proposal *)
            | Some valid_proposal => broadcast_msgs_to_trigger_list e.(ev_node) (msg_precommit (mkPrecommitType valid_proposal.(p_block) round e.(ev_node))) e.(ev_time)
            end
        | Some quit_time => [] (*do nothing because have quitted. | Shouldn't be called*)
        end
    | timeout_quit_status => [] (* handled elsewhere during quit *)
    | timeout_new_view_wait => (* check if the trigger is successful. Should be successful. *)
        if (e.(ev_node) =? (leaderOfRound new_state.(st_round))) && (negb prev_state.(st_new_view_timeouted)) && (new_state.(st_new_view_timeouted)) then 
            let new_proposal := 
            match new_state.(st_dynamic_highest_cert) with 
            | None => mkProposalType (honest_default_proposal_of_round (prev_state.(st_round))) (prev_state.(st_round)+1) None e.(ev_time)
            | Some cert => mkProposalType cert.(c_block) (prev_state.(st_round)) (Some cert) e.(ev_time)
            end in
            broadcast_msgs_to_trigger_list e.(ev_node) (msg_propose new_proposal) e.(ev_time)
        else [] (*only leader sends proposal*)
    end.
    

(* the first event is the ancestor of all events. *)
    
Definition triggers_of_first_event (n: Node) : list TriggerType :=
    if  1<=?n then 
    [(trigger_timeout timeout_proposal n 0 (2*delta))]
    else [(trigger_timeout timeout_proposal n 0 (2*delta))] ++ (broadcast_msgs_to_trigger_list 0 (msg_propose (mkProposalType 1 0 None 0)) 0).

(* applies to only honest replicas *)
Definition triggers_generation_def (e:Event): list TriggerType :=
    (* first event is define else where *)
    match direct_pred e with 
    | None => triggers_of_first_event e.(ev_node) 
    | Some e_pred =>
        let prev_state := state_before_event e in
        let new_state := state_after_event e in
        if prev_state.(st_committed) then []
        else match prev_state.(st_quit_round_time) with
        | Some quit_time => 
            match e.(ev_trigger) with
            | Some  (trigger_timeout timeout_type node round expire_time) =>
                match timeout_type with
                | timeout_quit_status =>
                    if prev_state.(st_round) <? new_state.(st_round) then (*enter new round, will send locked highest cert to new leader*) 
                    match (new_state.(st_locked_highest_cert)) with
                    | None => [] (*no cert . don't need send*)
                    | Some cert =>
                        [(trigger_msg_receive (mkMsgType e.(ev_node) (leaderOfRound (prev_state.(st_round)+1)) (msg_highest_cert cert) e.(ev_time)))]
                    end
                    else []
                | _ => [] (*ignore other triggers*)
                end
            | _ => [] (* no generated trigger in other events *)
            end
        | None =>  (*not quitted*)
            match e.(ev_trigger) with
            | Some trigger => 
                    match trigger with
                    | trigger_msg_receive msg => triggers_generated_by_receiving_def e msg prev_state new_state
                    | trigger_timeout timeout node round expire_time => 
                        if round=? prev_state.(st_round) then triggers_generated_by_timout_def e timeout node round expire_time prev_state new_state
                        else [] (*ignore timeout for other rounds*)
                    end
            | None => [] (* should not happen for honest nodes*)
            end
        end
    end.

Hypothesis actual_cert_require_majority:
    forall cert: Certificate, length cert.(c_voters) >= 1+n_faulty.


Theorem safety: 
    forall e1 e2: Event, 
        isHonest (e1.(ev_node)) = true -> isHonest (e2.(ev_node)) = true ->
        e1.(ev_time) <= e2.(ev_time) ->
        (let state1 := state_after_event e1 in 
        let state2 := state_after_event e2 in
        state1.(st_committed) = true -> state2.(st_committed) = true) /\
        match state1.(st_first_valid_proposal), state2.(st_first_valid_proposal) with
        | Some p1, Some p2 => p1.(p_block) = p2.(p_block)
        | Some p1, None => False
        | None, _ => True
        end.


(* for liveness, require extending events. *)
Theorem liveness: 
    forall n:Node, 
    n<1+2*n_faulty ->
    isHonest n = true ->
    exists e:Event, e.(ev_node) = n /\ (let state:= state_after_event e in state.(st_committed)=true).


End SyncHotStuff.

