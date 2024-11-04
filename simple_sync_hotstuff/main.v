Require Import List.
Require Import PeanoNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 

Import ListNotations.


Section SyncHotStuff.

Variable delta : nat. 

Definition Node: Type := nat. 
Definition BlockType : Type := nat.

Record Certificate: Type := mkCertificate {
  c_block : BlockType;
  c_node : Node;
  c_round : nat;
  c_justification : list BlockType;
}.

Record ProposalType: Type := mkProposalType {
  p_block: BlockType;
  p_round: nat;
  p_cert: Certificate;
  p_proposer: Node;
}.

Record VoteType: Type := mkVoteType {
  v_block: BlockType;
  v_round: nat;
  v_voter: Node;
}.

Record PrecommitType: Type := mkPrecommitType {
  pc_block: BlockType;
  pc_round: nat;
  pc_voter: Node;
}.

Record BlameType: Type := mkBlameType {
  b_round: nat;
  b_blamer: Node;
}.

Record QuitConflictType: Type := mkQuitConflictType {
  qc_round: nat;
  qc_proposal1: ProposalType;
    qc_proposal2: ProposalType;
}.

Record QuitBlameType: Type := mkQuitBlameType {
  qb_round: nat;
  qb_blames: list BlameType;
}.

Inductive QuitType : Type :=
    | quit_conflict (qc: QuitConflictType)
    | quit_blame (qb: QuitBlameType).

Inductive MsgContentType : Type :=
    | msg_propose (proposal: ProposalType)
    | msg_vote (vote: VoteType)
    | msg_precommit (precommit: PrecommitType)
    | msg_blame (blame:BlameType)
    | msg_quit (qt: QuitType). 

Record MsgType : Type := mkMsgType {
  msg_sender : Node;
  msg_recipient : Node; (* esop uses a list of recipients. we use a single node *)
  msg_content : MsgContentType;
  msg_send_time : nat; 
  msg_receive_time : nat; 
}.

Variable isHonest: Node -> bool. 

Variable n_faulty: nat. 

(* #total nodes = 2*n_faulty+1. Actual faulty nodes: <= n_faulty *)

Definition replicas: list Node := List.seq 1 (2*n_faulty+1).

Hypothesis honest_majority: 
    length (filter isHonest replicas) >= 1+n_faulty.


Definition leaderOfRound (r: nat): Node := (r mod (2*n_faulty+1)) + 1.

(* First define events, then define states*)

Inductive TimeoutType: Type := 
    | timeout_proposal (round: nat)
    | timeout_precommit (round: nat).

Inductive TriggerType: Type:= 
    | trigger_msg_receive (msg: MsgType)
    | trigger_timeout (timeout: TimeoutType). 

Record Event: Type := mkEvent {
    ev_node: Node;
    ev_trigger: option TriggerType; (* None <=> node is arbitrary *)
    ev_time: nat;
}.

Variable event_happen_before: Event -> Event -> Prop.
Variable direct_pred: Event -> option Event. 


(* properties of events: 1. ordering *)

Hypothesis event_ordering_by_time: forall e1 e2:Event, 
    e1.(ev_time) < e2.(ev_time) -> event_happen_before e1 e2.
Hypothesis event_ordering_by_node: forall e1 e2:Event, 
    e1.(ev_time) = e2.(ev_time) -> e1.(ev_node) < e2.(ev_node) -> event_happen_before e1 e2.

Hypothesis event_ordering_msg_before_timeout: forall e1 e2: Event, 
    e1.(ev_time) = e2.(ev_time) -> e1.(ev_node) = e2.(ev_node) -> exists msg, e1.(ev_trigger) = Some (trigger_msg_receive msg) -> exists timeout, e2.(ev_trigger) = Some (trigger_timeout timeout) -> event_happen_before e1 e2.

Hypothesis event_ordering_reflexive: forall e:Event, event_happen_before e e.

Hypothesis event_ordering_decisive: forall e1 e2:Event, (e1 = e2) \/ ((event_happen_before e1 e2 -> not (event_happen_before e2 e1)) /\ (not (event_happen_before e1 e2) -> event_happen_before e2 e1)). 

Hypothesis event_ordering_transitive: forall e1 e2 e3:Event, 
    event_happen_before e1 e2 -> event_happen_before e2 e3 -> event_happen_before e1 e3.

Hypothesis direct_pred_ordering: forall e1 e2:Event, 
    direct_pred e1 = Some e2 -> e1.(ev_node) = e2.(ev_node) /\ event_happen_before e2 e1.

Hypothesis honest_event_triggered_by_something: forall e:Event, 
    isHonest e.(ev_node) = true -> exists trigger,  e.(ev_trigger) = Some trigger.

(* rules on how events can be triggered*)

Record StateType: Type := mkState {
    st_round: nat;
    st_committed: bool;
    st_highest_cert: option Certificate; (* the highest block is included in the highest cert*)
    st_round_start_time: nat; 
    st_has_received_proposal: bool; 
    st_proposal_receive_time: option nat;
    st_current_proposal: option ProposalType;
    st_receive_proposals_from: list Node; (* should be made non-repetitive *)
    st_has_quited_round: bool; 
    st_quit_round_time: option nat;
    st_received_blames: list BlameType;
    (* st_has_voted: bool; same as received proposal *)
    st_vote: option VoteType;
    st_has_precommitted: bool;
    st_precommit_time: option nat;
    st_precommit: option PrecommitType;

}.

(* use the following interfaces to modify some fields of the state *)
Definition state_set_first_proposal (curr_state:StateType) (proposal:ProposalType) : StateType :=
.



Variable init_state: StateType.

Variable state_before_event: Event -> StateType. 
Variable state_after_event: Event -> StateType. 

Variable messages_after_event: Event -> option (list MsgType).
Variable timeouts_after_event: Event -> option (list TimeoutType).

(* state transition rule only applies to honest node *)
(* This is the protocol. *)

Definition is_proposal_valid (proposal: ProposalType) (curr_state: StateType): bool := 
    proposal.(p_round) = curr_state.(st_round) && proposal.(p_proposer) = leaderOfRound curr_state.(st_round) 
    && (
        match curr_state.(st_highest_cert) with
        | None => true
        | Some cert => cert.(c_round) <= proposal.(p_round)
        end
    ). 

Definition state_transition_waiting_first_proposal (e:Event) (curr_state: StateType) : StateType:=
(* only care about receiving the first proposal message or timeout*)
match e.(ev_trigger) with
| None => curr_state (* note that dishonest nodes are not constrained by state_transition rules. Honest nodes should only process events triggered by something *)
| trigger_msg_receive msg => 
    match msg.(msg_content) with
    | msg_propose proposal => (* if receiving late, then timeout event should come first. *)
        if is_proposal_valid proposal curr_state then
            let new_state := 
                mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_round_start_time) true (Some msg.(msg_receive_time)) (Some proposal) ([msg.(msg_sender)]) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_precommit) in
                    new_state
        else curr_state
    | _ => curr_state
    end
| trigger_timeout timeout =>
    match timeout with
    | timeout_proposal round => 
        if round = curr_state.(st_round) then (*send blame*)
            curr_state (* not sure if there is anything to do*)
        else curr_state
    | _ => curr_state
    end
end
.

Definition state_transition_quited_round(e:Event) (curr_state: StateType) : StateType := 
    match e.(ev_trigger) with
    | None => curr_state
    | trigger_timeout timeout => 
        match timeout with
        | timeout_proposal round => 
            if round = curr_state.(st_round) then 
                let new_state := 
                    mkState (curr_state.(st_round)+1) false None e.(ev_time) false None None [] false None false None None None in
                    new_state
            else curr_state
        | _ => curr_state
        end
    | _ => curr_state
    end.

Definition state_transition_waiting_maj_proposals (e:Event) (curr_state: StateType): StateType :=

.

Definition state_transition (e: Event) (curr_state: StateType) : StateType := 
if curr_state.(st_committed) then curr_state 
else if curr_state.(st_has_quited_round) then 
    state_transition_quited_round e curr_state
else (* handle quit first*)
match e.(ev_trigger) with
| None => curr_state
| trigger_msg_receive msg =>
    match msg.(msg_content) with
    | msg_quit qt => 
        match qt with
        | quit_conflict qc => 
            if qc.(qc_round) = curr_state.(st_round) then 
                let new_state := 
                    mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some e.(ev_time)) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_precommit) in
                    new_state
            else curr_state
        | quit_blame qb => 
            if qb.(qb_round) = curr_state.(st_round) then 
                let new_state := 
                    mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some e.(ev_time)) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_precommit) in
                    new_state
            else curr_state
        end
    | msg_blame blame => (* check if blame reaches f+1*)
        if blame.(b_round) = curr_state.(st_round) then
            if In  
            let new_state := 
                mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some e.(ev_time)) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_precommit) in
                new_state
        else curr_state
    if isHonest msg.(msg_sender) then 
        if ~curr_state.(st_has_received_proposal) then 
            state_transition_waiting_first_proposal e curr_state
        else if ~curr_state.(st_has_precommitted) then
            state_transition_waiting_maj_proposals e curr_state
        else curr_state
    else curr_state
 if ~curr_state.(st_has_received_proposal) then 
        state_transition_waiting_first_proposal e curr_state
    else if ~curr_state.(st_has_precommitted) then
        state_transition_waiting_maj_proposals e curr_state
    else curr_state.   

    end
. 




Definition is_msg_receive_valid (msg: MsgType): Prop := 
    match msg.(msg_content) with
    | msg_propose proposal => True
    | msg_vote vote => True
    | msg_precommit precommit => True
    | msg_blame blame => True
    end.

Hypothesis honest_event_triggered_by_msg_or_timer:
    forall e:Event, 
    isHonest e.(ev_node) = true ->
    (exists msg:MsgType, e.(ev_trigger) = Some (trigger_msg_receive msg) /\ is_msg_receive_valid msg)  \/ 
    (exists timeout: TimeoutType, e.(ev_trigger) = Some (trigger_timeout timeout) /\ is_timeout_valid timeout).

(* a list of hypotheses to specify how events change states *)

End SyncHotStuff.