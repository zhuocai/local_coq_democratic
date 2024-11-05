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
  p_cert: Certificate;
  p_proposer: Node;
}.

Definition proposal_beq (p1 p2: ProposalType): bool :=
    Nat.eqb p1.(p_block) p2.(p_block) && Nat.eqb p1.(p_round) p2.(p_round) && certificate_beq p1.(p_cert) p2.(p_cert) && Nat.eqb p1.(p_proposer) p2.(p_proposer).

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
    | timeout_precommit (round: nat)
    | timeout_quit_status (round: nat) (* for the old round *)
    | timeout_new_view_wait (round: nat).

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



Record StateType: Type := mkState {
    st_round: nat;
    st_committed: bool;
    st_highest_cert: option Certificate; (* the highest block is included in the highest cert*)
    st_all_certs: nat -> BlockType -> list Node; (* round -> block -> list of voters *)
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
    st_precommit_time: option nat; (* start precommit timer*)
    st_received_precommits_from: list Node;

}.

(* use the following interfaces to modify some fields of the state *)

Definition state_set_first_proposal (curr_state:StateType) (proposal:ProposalType) (time: nat) (msg_sender: Node): StateType :=
    mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) true (Some time) (Some proposal) [msg_sender] curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

(* handle repetition. *)
(* when it reaches f+1. will set precommitted. If set precommitted, will not call this function again. *)
Definition state_set_more_proposals (curr_state:StateType) (proposal: ProposalType)  (msg_sender: Node): StateType:=
    if is_element msg_sender curr_state.(st_receive_proposals_from) then curr_state
    else 
        mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) (msg_sender::curr_state.(st_receive_proposals_from)) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

Definition blames_to_blamers: list BlameType -> list Node := 
    map (fun b => b.(b_blamer)).

Definition state_set_receive_blame (curr_state:StateType) (blame:BlameType) : StateType :=
    if is_element blame.(b_blamer) (blames_to_blamers curr_state.(st_received_blames)) then curr_state
    else 
        mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) (blame::curr_state.(st_received_blames)) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

Definition state_set_receive_qt (curr_state:StateType) (qt:QuitType) (time: nat): StateType :=
    match qt with
    | quit_conflict qc => 
        mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from)
    | quit_blame qb => 
        mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from)
    end.

Definition state_set_quit_blame (curr_state:StateType) (time: nat): StateType :=
    mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) true (Some time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

Definition state_set_precommit_start (curr_state:StateType) (time:nat):StateType:=
    mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) true (Some time) curr_state.(st_received_precommits_from).

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

Definition state_set_receive_vote (curr_state:StateType) (vote:VoteType):StateType:=
    mkState curr_state.(st_round) curr_state.(st_committed) (update_highest_cert curr_state.(st_highest_cert) curr_state.(st_all_certs) vote) (update_all_certs curr_state.(st_all_certs) vote) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

Definition state_set_enter_new_round (curr_state:StateType) (time: nat): StateType :=
    mkState (curr_state.(st_round)+1) false curr_state.(st_highest_cert) curr_state.(st_all_certs) time false None None [] false None [] None false None [].

Definition state_set_receive_precommit (curr_state:StateType) (precommit: PrecommitType) : StateType :=
    if is_element precommit.(pc_voter) curr_state.(st_received_precommits_from) then curr_state
    else 
        mkState curr_state.(st_round) curr_state.(st_committed) curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time)  (precommit.(pc_voter)::curr_state.(st_received_precommits_from)).

(* commit the current proposal. *)


(* once committed, the state of the node will not change any more. The committed proposal is exactly curr_state.(st_current_proposal)*)
Definition state_set_commit (curr_state:StateType) (time:nat) : StateType :=
    mkState curr_state.(st_round) true curr_state.(st_highest_cert) curr_state.(st_all_certs) curr_state.(st_round_start_time) curr_state.(st_has_received_proposal) curr_state.(st_proposal_receive_time) curr_state.(st_current_proposal) curr_state.(st_receive_proposals_from) curr_state.(st_has_quited_round) curr_state.(st_quit_round_time) curr_state.(st_received_blames) curr_state.(st_vote) curr_state.(st_has_precommitted) curr_state.(st_precommit_time) curr_state.(st_received_precommits_from).

(* state transition rule applies to any node. *)
(* Byzantine nodes can arbitrarily send messages. (for honest nodes, every trigger must be generated fairly, except messages sent by Byzantine nodes.) *)

(* state transition rule applies to any node. *)
(* Byzantine nodes can arbitrarily send messages. (for honest nodes, every trigger must be generated fairly, except messages sent by Byzantine nodes.) *)




(* checks proposal round, leader-proposer, cert*)
Definition is_proposal_valid (proposal: ProposalType) (curr_state: StateType): bool := 
    Nat.eqb proposal.(p_round) curr_state.(st_round) && Nat.eqb proposal.(p_proposer)  (leaderOfRound curr_state.(st_round)) 
    && (
        match curr_state.(st_highest_cert) with
        | None => true
        | Some cert => cert.(c_round) <=? proposal.(p_round)
        end
    ). 

(* state transition rule applies to any node. *)
(* Byzantine nodes can arbitrarily send messages. (for honest nodes, every trigger must be generated fairly, except messages sent by Byzantine nodes.) *)
Definition state_transition (e: Event) (curr_state: StateType) : StateType := 
    if curr_state.(st_committed) then curr_state 
    else if curr_state.(st_has_quited_round) then (* receiving votes | waiting for delta timeout to enter next round*)
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
        | Some (trigger_timeout timeout) =>
            match timeout with
            | timeout_quit_status round => 
                if round =? curr_state.(st_round) then 
                    state_set_enter_new_round curr_state e.(ev_time)
                else curr_state
            | _ => curr_state
            end
        end
    else (* handle receiving quit first*)
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
                if negb curr_state.(st_has_received_proposal) then 
                    if is_proposal_valid proposal curr_state then
                        state_set_first_proposal curr_state proposal e.(ev_time) msg.(msg_sender)
                    else curr_state
                else if negb curr_state.(st_has_precommitted) then
                    match curr_state.(st_current_proposal) with
                        | None => curr_state (*should not happen*)
                        | Some curr_proposal =>
                        if proposal_beq proposal curr_proposal then 
                            let temp_state := state_set_more_proposals curr_state proposal msg.(msg_sender) in
                            if (1+n_faulty) <=? (length (temp_state.(st_receive_proposals_from))) then 
                                state_set_precommit_start temp_state e.(ev_time)
                            else temp_state
                        else curr_state (* should qc conflict*)
                    end
                else (* has precommitted _started the timer | TODO check conflict qc. *)
                    curr_state
            | msg_vote vote => (* vote is used to form certificates  *)
                state_set_receive_vote curr_state vote
            | msg_precommit precommit => (*require at least received proposal*)
                if (precommit.(pc_round) =? curr_state.(st_round)) && curr_state.(st_has_received_proposal) then
                    let temp_state:= state_set_receive_precommit curr_state precommit in
                        (* if receiving f+1 precommit msg, really commit*)
                        if (1+n_faulty) <=? (length temp_state.(st_received_precommits_from)) then
                            state_set_commit temp_state e.(ev_time)
                        else temp_state
                    
                else curr_state
            end     
        | Some(trigger_timeout timeout) =>
            match timeout with
                | timeout_proposal round => 
                    if (round =? curr_state.(st_round)) && curr_state.(st_has_received_proposal) then 
                        curr_state
                    else (* send blame out *)
                        curr_state
                | timeout_precommit round =>
                    if (round =? curr_state.(st_round)) && negb curr_state.(st_has_quited_round) then (*sending precommit msg*)
                        curr_state
                    else curr_state
                | timeout_quit_status round =>
                    curr_state (* should not be in quit*)
                | timeout_new_view_wait round =>
                    (* broadcast new proposal*)
                    curr_state
            end
    end.

Variable init_state: StateType.

Variable state_before_event: Event -> StateType. 
Variable state_after_event: Event -> StateType. 

Variable messages_after_event: Event -> option (list MsgType).
Variable timeouts_after_event: Event -> option (list TimeoutType).

Hypothesis init_state_def: 
    init_state.(st_round) = 0 /\ init_state.(st_committed) = false /\ init_state.(st_highest_cert) = None /\ init_state.(st_all_certs) = (fun r b => []) /\ init_state.(st_round_start_time) = 0 /\ init_state.(st_has_received_proposal) = false /\ init_state.(st_proposal_receive_time) = None /\ init_state.(st_current_proposal) = None /\ init_state.(st_receive_proposals_from) = [] /\ init_state.(st_has_quited_round) = false /\ init_state.(st_quit_round_time) = None /\ init_state.(st_received_blames) = [] /\ init_state.(st_vote) = None /\ init_state.(st_has_precommitted) = false /\ init_state.(st_precommit_time) = None /\ init_state.(st_received_precommits_from) = [].

Hypothesis state_before_first_event:
    forall e:Event, direct_pred e = None -> state_before_event e = init_state.

Hypothesis state_recursive_def: 
    forall e:Event, 
    state_after_event e = state_transition e (state_before_event e).

(* a trigger -> event -> state update && new triggers. All new triggers should be attributed to the event. *)

Variable generators_of_triggers: TriggerType -> Event. 
Variable triggers_generated_by_event: Event -> list TriggerType. 



End SyncHotStuff.

