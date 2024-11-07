Require Import List.
Require Import PeanoNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool.
Require Import Lia.
Scheme Equality for list. 
Import ListNotations.


Section SyncHotStuff.

(* ############### PART 1: Basic data types ##################*)

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



(* note that two events might trigger the same event. for example, two different events can generate the same message sending.  
However, if two events are exactly the same, the state transition can ignore the second event. 

*)
Definition event_beq (e1 e2: Event): bool :=
    Nat.eqb e1.(ev_node) e2.(ev_node) && Nat.eqb e1.(ev_time) e2.(ev_time) && 
    match e1.(ev_trigger), e2.(ev_trigger) with
    | None, None => true
    | Some t1, Some t2 => 
        triggertype_beq t1 t2
    | _, _ => false
    end.

(* ============================ PART 1 END ==========================*)

(* ############################ PART 2 replicas, n, f ########################*)

Variable isHonest: Node -> bool. 

Variable n_faulty: nat. 

(* #total nodes = 2*n_faulty+1. Actual faulty nodes: <= n_faulty *)

Definition replicas: list Node := List.seq 0 (2*n_faulty+1).

Hypothesis honest_majority: 
    length (filter isHonest replicas) >= 1+n_faulty.


Definition leaderOfRound (r: nat): Node := (r mod (2*n_faulty+1)).

Hypothesis actual_cert_require_majority:
    forall cert: Certificate, length cert.(c_voters) >= 1+n_faulty.

(* =========================== PART 2 END ========================== *)

(* ########################### PART 3 states and state transition ############*)

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

Variable state_before_event: Event -> StateType. 
Variable state_after_event: Event -> StateType. 

(* Variable messages_after_event: Event -> option (list MsgType).
Variable timeouts_after_event: Event -> option (list TimeoutType). *)

Definition init_state: StateType := mkState 0 false None None (fun r b => []) 0 None None [] None [] None None [] false.


(* ======================= PART 3 END ================ *)

(* ======================= PART 4 Events - Sequence Ordering ============= *)

(* For proof, must make event history inductive. *)
(* for proof of liveness, also need to make events inductive forward*)

(* try: associate a number with a event. List of events*)
(* and list of events towards the end. *)

(* a trigger -> event -> state update && new triggers. All new triggers should be attributed to the event. *)



(* the first event is the special event, which generates the first timeout && first proposal. *)

Definition first_event (n:Node):Event:= 
    mkEvent n None 0.

(* Make events bi-directional inductive *)
Variable event_to_seq_id: Event -> nat. (* for each node, this is a bijection*)
(* Variable event_to_inv_seq_id: Event -> nat. *) 
(* inv_seq_id assumes termination | not define for now*)

Hypothesis event_id_bijection: (*a real hypothesis: events happen in some order. *)
    forall e1 e2:Event, event_to_seq_id e1 = event_to_seq_id e2 -> e1.(ev_node) = e2.(ev_node) -> e1 = e2.

Hypothesis event_id_init_first:
    forall n:Node, event_to_seq_id (first_event n) = 1.

Hypothesis event_id_none_zero:
    forall e: Event, event_to_seq_id e >= 1.
(* id 0 leave for None? *)

(* this is already assuming the protocol will terminate | don't use it for now*)
(* Hypothesis event_id_init_last:
    forall e: Event, direct_next e = None -> event_to_inv_seq_id e = 0. *)

Variable node_id_to_event: Node -> nat -> option Event. (* for each node, this is a bijection*)
Hypothesis node_id_to_event_def:
    forall n:Node, forall i:nat, forall e:Event,
        node_id_to_event n i = Some e <-> (e.(ev_node) = n /\ event_to_seq_id e = i).

Hypothesis node_id_to_even_def_id0:
    forall n:Node, node_id_to_event n 0 = None.

Hypothesis node_id_to_event_def_none:
    forall n:Node, forall i:nat, i>=1 ->
        node_id_to_event n i = None <-> forall e:Event, e.(ev_node) = n -> event_to_seq_id e < i. 



Lemma event_node_id_of_event_eq:
    forall e: Event, 
        node_id_to_event e.(ev_node) (event_to_seq_id e) = Some e.
    
    intros.
    remember (event_to_seq_id e) as i. 
    remember (e.(ev_node)) as n.
    rewrite node_id_to_event_def with (n:=n) (i:=i) (e:=e).
    split.
    auto.
    auto.
Qed.


Definition direct_pred (e: Event): option Event:=
    match event_to_seq_id e with
    | 0 => None 
    | S i => node_id_to_event e.(ev_node) i
    end.

Definition direct_next (e: Event): option Event:=
    node_id_to_event e.(ev_node) (S (event_to_seq_id e)).
    
Lemma pred_is_injective:
    forall e1 e2: Event, direct_pred e1 = direct_pred e2 -> 
        ~direct_pred e1 = None -> e1 = e2. (* note that the special first events can point to the same None *)
Admitted.

Lemma pred_is_for_same_node:
    forall e1 e2: Event, direct_pred e1 = Some e2 -> e1.(ev_node) = e2.(ev_node).
Admitted.

Lemma direct_next_is_injective:
    forall e1 e2: Event, direct_next e1 = direct_next e2 -> ~direct_next e1 = None -> e1 = e2. (* the last events all point to None | have to prove there exist last event for every node ; *)
Admitted.

Lemma direct_next_is_for_same_node:
    forall e1 e2: Event, direct_next e1 = Some e2 -> e1.(ev_node) = e2.(ev_node).

Fixpoint node_id_to_ev_history (n:Node) (i:nat): list Event :=
    match i with
    | 0 => []
    | S i' => 
        match node_id_to_event n i with
        | None => []
        | Some e => e::(node_id_to_ev_history n i')
        end
    end.

Definition event_to_history (e: Event) : list Event :=
    node_id_to_ev_history e.(ev_node) (event_to_seq_id e). 

(* properties of events: 1. time ordering *)

Hypothesis event_ordering_by_time: 
    forall e1 e2: Event, 
        e1.(ev_node) = e2.(ev_node) -> e1.(ev_time) < e2.(ev_time) -> (event_to_seq_id e1) < (event_to_seq_id e2).

(*if receive message in the last second, it is still valid. *)
Hypothesis event_ordering_msg_before_timeout: forall e1 e2: Event, 
    e1.(ev_node) = e2.(ev_node) -> e1.(ev_time) = e2.(ev_time) -> 
    exists msg, e1.(ev_trigger) = Some (trigger_msg_receive msg) -> 
    exists timeout t_node t_round t_expire_time, e2.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> 
    (event_to_seq_id e1) < (event_to_seq_id e2).
    


Hypothesis state_before_first_event:
    forall n:Node, state_before_event (first_event n) = init_state.

Hypothesis state_after_transition_def: 
    forall e:Event, 
    state_after_event e = state_transition e (state_before_event e).

Hypothesis state_direct_pred_def:
    forall e1 e2:Event, 
    direct_pred e2 = Some e1 -> state_after_event e1 = state_before_event e2.

Lemma state_direct_next: (* can be proved with the above, but assumed for simplicity *)
    forall e1 e2:Event, 
    direct_next e1 = Some e2 -> state_after_event e1 = state_before_event e2.
Admitted.




(* =================== PART 4 END ===================== *)

(* ################### PART 5 Trigger & its Generation by events ########*)
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
    let vote_triggers:= broadcast_msgs_to_trigger_list e.(ev_node) (msg_vote (mkVoteType proposal.(p_block) proposal.(p_round) e.(ev_node))) e.(ev_time) in
    let forward_triggers:= broadcast_msgs_to_trigger_list e.(ev_node) (msg_propose proposal) e.(ev_time) in
    match prev_state.(st_first_received_proposals) with 
    | None =>
        if is_proposal_valid_cert proposal prev_state then (*vote + forward*)
            vote_triggers ++ forward_triggers
        else if is_proposal_valid_round_proposer proposal prev_state then (*only forward*)
            forward_triggers
        else []
    | Some first_proposal =>
        if proposal_beq proposal first_proposal then (*receiving the same first proposal again*)
            []
        else (* receiving a different proposal | totally-invalid or cert-invalid or valid | total_invalid => ignore / otherwise => duplicate report quit *)
            if is_proposal_valid_round_proposer proposal prev_state then (*broadcast quit conflict*)
                broadcast_msgs_to_trigger_list e.(ev_node) (msg_quit (quit_conflict (mkQuitConflictType prev_state.(st_round) first_proposal proposal))) e.(ev_time)
            else []
    end.


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
    if  (1<=?n) && (n <=?2*n_faulty) then 
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



(* event -> next triggers: defined as function *)
(* event -> current trigger: e.(ev_trigger) *)
(* event -> next events. Not defined *)
(*  instead, trigger -> next_event is a variable. | one_trigger only generates one event *)
(* trigger -> from_event: generated by from_event. *)

(* maybe e1 e2 -> both generate trigger tri. *)

(* trigger -> next_event, triggered by trigger | this acts as a hypothesis, saying that any trigger will generate an event *)
Variable event_of_trigger: TriggerType -> Event.

(* as a hypothesis, that every trigger is generated by some event. *)
(* trigger -> from_event *)
Variable generators_of_triggers: TriggerType -> Event. 

(* event_ancestor is naturally defined as first_event of event_node *)

(* ================= PART 5 END ================== *)

(* ################# PART 6 Properties - prepare for proof ################ *)

Fixpoint is_nonrepeat (nodes: list Node): bool:=
    match nodes with
    | [] => true
    | n::nodes' => if is_element n nodes' then false else is_nonrepeat nodes'
    end.

Fixpoint is_subset_replicas (nodes: list Node):bool:=
    match nodes with
    | [] => true
    | n::nodes' => if is_element n replicas then is_subset_replicas nodes' else false
    end.

Definition is_nonrepeat_subset_replicas (nodes: list Node):bool:=
    is_nonrepeat nodes && is_subset_replicas nodes.

(* a quorum is a nonrepeat subset of replicas *)

Definition is_quorum (nodes: list Node):bool:=
    is_nonrepeat_subset_replicas nodes && ((1+n_faulty) <=? length nodes).

(* a quorum is a nonrepeat subset of replicas *)

Lemma state_transition_remain_committed_once_committed:
    forall e: Event, forall curr_state: StateType, 
        curr_state.(st_committed) = true ->
        state_transition e curr_state = curr_state.
        intros.
        unfold state_transition.
        rewrite H.
        trivial.
Qed.

Lemma once_committed_commit_in_next_state:
    forall e e_next:Event, 
    isHonest e.(ev_node) = true ->
    (state_after_event e).(st_committed) = true ->
    direct_next e = Some e_next -> 
    (state_after_event e_next).(st_committed) = true.
    
    intros.
    replace (state_after_event e_next) with (state_transition e_next (state_before_event e_next)).
    2:rewrite state_after_transition_def. 2:auto.
    replace (state_before_event e_next) with (state_after_event e).
    2:rewrite state_direct_next with (e1:= e) (e2:=e_next). 3:trivial. 2:trivial.
    replace (state_transition e_next (state_after_event e)) with (state_after_event e). trivial.
    rewrite state_transition_remain_committed_once_committed. 
    trivial. trivial.
Qed.

(* induction is required on the future events *)
Lemma once_committed_remain_committed: 
    forall e1:Event, forall id_gap:nat, 
    isHonest e1.(ev_node) = true -> 
    (state_after_event e1).(st_committed) = true ->
    let e1_id := event_to_seq_id e1 in
    let next_event := (node_id_to_event e1.(ev_node) (e1_id + id_gap)) in
    match next_event with
    | None => True
    | Some e2 => 
        (state_after_event e2).(st_committed) = true
    end.

    intros.
    induction id_gap.
    replace (e1_id + 0) with e1_id. 
    2:lia.
    
    (* TODO pick up proof here | may need to change the above notion *)
    replace (node_id_to_event e1.(ev_node) e1_id) with e1.
    
Qed.


Lemma lemma_1_commit_implies_maj_precommits_in_same_round:
    forall e1:Event, 
        isHonest (e1.(ev_node)) = true ->
        let state1 := state_after_event e1 in 
        (state1.(st_committed) = true -> is_quorum state1.(st_received_precommits_from) = true).

    .

Theorem safety: 
    forall e1 e2: Event, 
        isHonest (e1.(ev_node)) = true -> isHonest (e2.(ev_node)) = true ->
        e1.(ev_time) <= e2.(ev_time) ->
        (let state1 := state_after_event e1 in 
        let state2 := state_after_event e2 in
        (state1.(st_committed) = true -> state2.(st_committed) = true) /\
        (match state1.(st_first_valid_proposal), state2.(st_first_valid_proposal) with
        | Some p1, Some p2 => p1.(p_block) = p2.(p_block)
        | Some p1, None => False
        | None, _ => True
        end)).
Admitted.

(* for liveness, require extending events. *)
Theorem liveness: 
    forall n:Node, 
    n<1+2*n_faulty ->
    isHonest n = true ->
    exists e:Event, e.(ev_node) = n /\ (let state:= state_after_event e in state.(st_committed)=true).
Admitted.


End SyncHotStuff.

