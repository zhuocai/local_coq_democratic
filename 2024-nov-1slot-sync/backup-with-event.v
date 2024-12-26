Require Import List.
Require Import PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Lia.
Require Import Coq.Program.Equality.
Scheme Equality for list. 
Import ListNotations.


Section SyncHotStuff.

(* ############### PART 1: Basic data types ##################*)


(* Nat.eqb_refl *)

(* Use Nat.eqb_eq*)

Variable delta : nat. 

Hypothesis delta_is_positive: delta >= 1.

(* ============================ PART 1 ==========================*)

(* #def 1A *)

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

(* =========================== PART 2 END ========================== *)

(* ########################### PART 3 states and state transition ############*)

(* edit add a node *)
Record StateType: Type := mkState {
    st_node: Node;
    st_round: nat;
    st_committed: bool;
    st_locked_highest_cert: option Certificate; (* the highest block is included in the highest cert*)
    (* the locked certificate only gets updated during the quit round break *)
    st_dynamic_highest_cert: option Certificate; 
    st_all_certs: nat -> BlockType -> list Node; (* round -> block -> list of voters *)
    st_round_start_time: nat; 
    st_first_valid_proposal: option ProposalType;
    st_first_received_proposal: option ProposalType; (* for forwarding them. Always forward the first two different proposals. Here the proposals can fail the certificate check. *)
    st_received_valid_proposal_from: list Node; (* should be made non-repetitive *)
    st_quit_round_time: option nat;
    st_received_blames: list BlameType;
    (* st_has_voted: bool; same as received proposal *)
    st_vote: option VoteType;
    st_precommit_time: option nat; (* start precommit timer*)
    st_received_precommit_from: list Node;
    st_new_view_timeouted: bool;

}.

(* use the following interfaces to modify some fields of the state *)

Definition state_set_first_received_proposal (curr_state:StateType) (proposal:ProposalType): StateType:=
    mkState 
    curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    (Some proposal) (*curr_state.(st_first_received_proposal) *)
    curr_state.(st_received_valid_proposal_from)
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_first_valid_proposal (curr_state:StateType) (proposal:ProposalType) (msg_sender: Node) (node:Node): StateType :=
    mkState 
    curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    (*set curr_state.(st_first_valid_proposal)*)
    (Some proposal)
    (* curr_state.(st_first_received_proposal)  *)
    (Some proposal)
    (* curr_state.(st_received_valid_proposal_from) *)
    [msg_sender]
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    (* curr_state.(st_vote)  *)
    (Some (mkVoteType proposal.(p_block) proposal.(p_round) node))
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

(* handle repetition. *)
(* *)
Definition state_set_more_proposals (curr_state:StateType) (proposal: ProposalType)  (msg_sender: Node): StateType:=
    if is_element msg_sender curr_state.(st_received_valid_proposal_from) then curr_state
    else 
        mkState curr_state.(st_node)
        curr_state.(st_round) 
        curr_state.(st_committed) 
        curr_state.(st_locked_highest_cert)
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs) 
        curr_state.(st_round_start_time)
        curr_state.(st_first_valid_proposal)
        curr_state.(st_first_received_proposal) 
        (* curr_state.(st_received_valid_proposal_from) *)
        (msg_sender::curr_state.(st_received_valid_proposal_from))
        curr_state.(st_quit_round_time)
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition blames_to_blamers: list BlameType -> list Node := 
    map (fun b => b.(b_blamer)).

Definition state_set_receive_blame (curr_state:StateType) (blame:BlameType) : StateType :=
    if is_element blame.(b_blamer) (blames_to_blamers curr_state.(st_received_blames)) then curr_state
    else 
        mkState curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposal) 
    curr_state.(st_received_valid_proposal_from)
    curr_state.(st_quit_round_time) 
    (blame::curr_state.(st_received_blames)) (*set*)
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_receive_qt (curr_state:StateType) (qt:QuitType) (time: nat): StateType :=
    mkState curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposal) 
    curr_state.(st_received_valid_proposal_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_quit_blame (curr_state:StateType) (time: nat): StateType :=
    mkState curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposal) 
    curr_state.(st_received_valid_proposal_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_quit_conflict (curr_state:StateType) (time: nat): StateType :=
    mkState curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposal) 
    curr_state.(st_received_valid_proposal_from)
    (Some time) (*set*)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

Definition state_set_precommit_start (curr_state:StateType) (time:nat):StateType:=
    mkState curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert)
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    curr_state.(st_round_start_time)
    curr_state.(st_first_valid_proposal)
    curr_state.(st_first_received_proposal) 
    curr_state.(st_received_valid_proposal_from)
    curr_state.(st_quit_round_time)
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    (* curr_state.(st_precommit_time)  *)
    (Some time)
    curr_state.(st_received_precommit_from)
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
    curr_state.(st_node)
    curr_state.(st_round) 
    curr_state.(st_committed) 
    curr_state.(st_locked_highest_cert) 
    (* curr_state.(st_dynamic_highest_cert) *)
    (update_highest_cert curr_state.(st_dynamic_highest_cert) curr_state.(st_all_certs) vote) 
    (* curr_state.(st_all_certs) *)
    (update_all_certs curr_state.(st_all_certs) vote) 
    curr_state.(st_round_start_time) 
    curr_state.(st_first_valid_proposal) 
    curr_state.(st_first_received_proposal)
    curr_state.(st_received_valid_proposal_from) 
    curr_state.(st_quit_round_time) 
    curr_state.(st_received_blames) 
    curr_state.(st_vote) 
    curr_state.(st_precommit_time) 
    curr_state.(st_received_precommit_from)
    curr_state.(st_new_view_timeouted).

(* also set the locked highest cert *)
Definition state_set_enter_new_round (curr_state:StateType) (time: nat): StateType :=
    mkState (curr_state).(st_node) (curr_state.(st_round)+1) (curr_state.(st_committed)) 
    curr_state.(st_dynamic_highest_cert) (*set locked highest cert*) 
    curr_state.(st_dynamic_highest_cert)
    curr_state.(st_all_certs) 
    time None None [] None [] None None [] false.

(* collect and count |
Question: is it possible to receive precommit before receiving a proposal? 
If no valid proposal is received at t => no valid proposal is received at any honest node at t-delta => will not send precommit by t+delta. 
*)
Definition state_set_receive_precommit (curr_state:StateType) (precommit: PrecommitType) : StateType :=
    if is_element precommit.(pc_voter) curr_state.(st_received_precommit_from) then curr_state
    else 
        mkState
        curr_state.(st_node)
        curr_state.(st_round) 
        curr_state.(st_committed) 
        curr_state.(st_locked_highest_cert) 
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposal)
        curr_state.(st_received_valid_proposal_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        (* curr_state.(st_received_precommit_from) *)
        (precommit.(pc_voter)::curr_state.(st_received_precommit_from))
        curr_state.(st_new_view_timeouted).

(* commit the current proposal. *)


(* once committed, the state of the node will not change any more. The committed proposal is exactly curr_state.(st_current_proposal)*)
Definition state_set_commit (curr_state:StateType) (time:nat) : StateType :=
    mkState
        curr_state.(st_node)
        curr_state.(st_round) 
        (* curr_state.(st_committed)  *)
        true
        curr_state.(st_locked_highest_cert) 
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposal)
        curr_state.(st_received_valid_proposal_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommit_from)
        curr_state.(st_new_view_timeouted).

Definition state_set_dynamic_highest_cert (curr_state:StateType) (cert:Certificate): StateType :=
    mkState
        curr_state.(st_node)
        curr_state.(st_round) 
        curr_state.(st_committed)
        curr_state.(st_locked_highest_cert) 
        (Some cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposal)
        curr_state.(st_received_valid_proposal_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommit_from)
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
        curr_state.(st_node)
        curr_state.(st_round) 
        curr_state.(st_committed)
        curr_state.(st_locked_highest_cert)
        curr_state.(st_dynamic_highest_cert)
        curr_state.(st_all_certs)
        curr_state.(st_round_start_time) 
        curr_state.(st_first_valid_proposal) 
        curr_state.(st_first_received_proposal)
        curr_state.(st_received_valid_proposal_from) 
        curr_state.(st_quit_round_time) 
        curr_state.(st_received_blames) 
        curr_state.(st_vote) 
        curr_state.(st_precommit_time) 
        curr_state.(st_received_precommit_from)
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

Definition state_transition_2_msg_A_quit (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
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
            | _ => curr_state
            end
        | _ => curr_state
    end.

Definition state_transition_2_msg_B_blame (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_blame blame => (* check if blame reaches f+1*)
                if blame.(b_round) =? curr_state.(st_round) then
                    let temp_state := state_set_receive_blame curr_state blame in
                    if (1+n_faulty) <=? (length temp_state.(st_received_blames)) then 
                        state_set_quit_blame temp_state e.(ev_time)
                    else temp_state
                else curr_state
            | _ => curr_state
            end
        | _ => curr_state
    end.

Definition state_transition_2_msg_C_precommit (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_precommit precommit => (*require at least received proposal*)
                if (precommit.(pc_round) =? curr_state.(st_round)) then 
                    match curr_state.(st_first_valid_proposal) with 
                        | None => curr_state 
                        | Some valid_proposal =>
                        if (valid_proposal.(p_block) =? precommit.(pc_block)) then 
                            let temp_state:= state_set_receive_precommit curr_state precommit in (* if curr_state has received f+1 precommits already, would have committed. will not enter this function*)
                            if (1+n_faulty) <=? (length temp_state.(st_received_precommit_from)) then
                                state_set_commit temp_state e.(ev_time)
                            else temp_state
                        else curr_state (* ignore precommit for other proposals*)
                    end
                else curr_state (*ignore precommit for other rounds*)
            | _ => curr_state
            end
        | _ => curr_state
    end.

Definition state_transition_2_msg_D_highest_cert (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_highest_cert cert => 
                if e.(ev_node) =? (leaderOfRound curr_state.(st_round)) then 
                    if curr_state.(st_new_view_timeouted) then curr_state (*too late*)
                        else state_set_recv_cert curr_state cert
                else curr_state
            | _ => curr_state
            end
        | _ => curr_state
    end.

(* #def 2E state *)
Definition state_transition_2_msg_E_vote (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_vote vote => 
                if vote.(v_round) =? curr_state.(st_round) then 
                    state_set_receive_vote curr_state vote
                else curr_state
            | _ => curr_state
            end
        | _ => curr_state
    end.

(* #def 2F state*)

Definition state_transition_2_msg_F_proposal (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
    | Some(trigger_msg_receive msg) =>
    match msg.(msg_content) with
    | msg_propose proposal =>
        match curr_state.(st_first_received_proposal) with
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
                        if 1+n_faulty <=? (length curr_state.(st_received_valid_proposal_from)) then (*already pre-committed. ignore the msg*)
                            curr_state
                        else (*need more proposals*)
                            let temp_state := state_set_more_proposals curr_state proposal msg.(msg_sender) in
                            if (1+n_faulty) <=? (length (temp_state.(st_received_valid_proposal_from))) then (*trigger precommit start*) 
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

(* #def state transition*)

Definition state_transition_2_trigger_msg (e:Event) (curr_state:StateType):StateType:=
    match e.(ev_trigger) with
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_quit qt => 
                state_transition_2_msg_A_quit e curr_state
            | msg_blame blame => (* check if blame reaches f+1*)
                    state_transition_2_msg_B_blame e curr_state
            | msg_precommit precommit => (*require at least received proposal*)
                state_transition_2_msg_C_precommit e curr_state
            | msg_highest_cert cert => 
                state_transition_2_msg_D_highest_cert e curr_state
            | msg_vote vote => (* vote is used to form certificates  *)
                state_transition_2_msg_E_vote e curr_state
            | msg_propose proposal =>
                state_transition_2_msg_F_proposal e curr_state
        end     
    | _ => curr_state    
    end.

Definition state_transition_3_trigger_timeout (e:Event) (curr_state:StateType):=
    if negb (curr_state.(st_node) =? e.(ev_node)) then curr_state
    else if curr_state.(st_committed) then curr_state 
    else match curr_state.(st_quit_round_time) with 
    | None =>
        match e.(ev_trigger) with
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
        | _ => curr_state
        end
    | _ => curr_state
    end.

Definition state_transition_1_quit_round (e:Event) (curr_state:StateType): StateType:=
    match curr_state.(st_quit_round_time) with 
    | Some quit_time =>  (* receiving votes | waiting for delta timeout to enter next round*)
        match e.(ev_trigger) with
        | None => curr_state
        | Some(trigger_msg_receive msg) =>
            match msg.(msg_content) with
            | msg_vote vote => 
                state_transition_2_msg_E_vote e curr_state
            | msg_highest_cert cert =>
                state_transition_2_msg_D_highest_cert e curr_state
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
    | _ => curr_state
    end.

(* #def state transition*)
Definition state_transition (e: Event) (curr_state: StateType) : StateType := 
    if negb (curr_state.(st_node) =? e.(ev_node)) then curr_state
    else if curr_state.(st_committed) then curr_state 
    else match curr_state.(st_quit_round_time) with 
    | Some quit_time =>  (* receiving votes | waiting for delta timeout to enter next round*)
        state_transition_1_quit_round e curr_state
    | None => (* has not quitted or committed *)
        match e.(ev_trigger) with
        | None => curr_state
        | Some(trigger_msg_receive msg) =>
            state_transition_2_trigger_msg e curr_state
        | Some(trigger_timeout timeout t_node t_round t_expire_time) =>
           state_transition_3_trigger_timeout e curr_state
        end
    end.

Definition state_transition_op (event: option Event) (state:StateType): StateType:=
    match event with
    | None => state
    | Some e => state_transition e state
    end. 

(* 
Variable state_before_event: Event -> StateType. 
Variable state_after_event: Event -> StateType.  *)

Definition init_state (n:Node): StateType := mkState n 0 false None None (fun r b => []) 0 None None [] None [] None None [] false.



(* #properties state transition | from specific rules to general rules *)

Lemma st_2A_only_change_quit_time:
    forall e:Event, forall prev_state:StateType,
        let new_state:= (state_transition_2_msg_A_quit e prev_state) in 
        new_state.(st_node) = prev_state.(st_node) /\
        new_state.(st_round) = prev_state.(st_round) /\
        new_state.(st_committed) = prev_state.(st_committed) /\
        new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
        new_state.(st_dynamic_highest_cert) = prev_state.(st_dynamic_highest_cert) /\
        new_state.(st_all_certs) = prev_state.(st_all_certs) /\
        new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
        new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
        new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
        new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
        new_state.(st_received_blames) = prev_state.(st_received_blames) /\
        new_state.(st_vote) = prev_state.(st_vote) /\
        new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
        new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
        new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).
        intros.
        unfold new_state.
        unfold state_transition_2_msg_A_quit.
        destruct_with_eqn (ev_trigger e).
        destruct_with_eqn t.
        destruct_with_eqn (msg_content msg).
        repeat split.
        repeat split.
        repeat split.
        repeat split.
        destruct_with_eqn qt.
        destruct_with_eqn (qc_round qc =? st_round prev_state).
        unfold state_set_receive_qt.
        repeat split.
        repeat split.
        destruct_with_eqn (qb_round qb =? st_round prev_state).
        repeat split. repeat split. repeat split. repeat split. repeat split.

Qed.

Lemma st_2B_only_change_recvblames_and_quit_time:
    forall e:Event, forall prev_state:StateType, 
    let new_state:= (state_transition_2_msg_B_blame e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
        new_state.(st_round) = prev_state.(st_round) /\
        new_state.(st_committed) = prev_state.(st_committed) /\
        new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
        new_state.(st_dynamic_highest_cert) = prev_state.(st_dynamic_highest_cert) /\
        new_state.(st_all_certs) = prev_state.(st_all_certs) /\
        new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
        new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
        new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
        new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
        new_state.(st_vote) = prev_state.(st_vote) /\
        new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
        new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
        new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_msg_B_blame.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    repeat split. repeat split. repeat split. 
    destruct_with_eqn (b_round blame =? st_round prev_state).
    destruct_with_eqn (1+n_faulty<=?length (st_received_blames (state_set_receive_blame prev_state blame))).
    unfold state_set_quit_blame.
    unfold state_set_receive_blame.
    destruct_with_eqn (is_element (b_blamer blame) (blames_to_blamers (st_received_blames prev_state))).
    simpl. repeat split. repeat split.
    unfold state_set_receive_blame.
    destruct_with_eqn (is_element (b_blamer blame) (blames_to_blamers (st_received_blames prev_state))).
    repeat split.
    simpl.
    repeat split.
    repeat split.
    repeat split.
    repeat split.
    repeat split.
    repeat split.
Qed.

Lemma st_2C_only_change_recvprecommits_and_commit:
    forall e:Event, forall prev_state:StateType, 
    let new_state:= (state_transition_2_msg_C_precommit e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
        new_state.(st_round) = prev_state.(st_round) /\
        new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
        new_state.(st_dynamic_highest_cert) = prev_state.(st_dynamic_highest_cert) /\
        new_state.(st_all_certs) = prev_state.(st_all_certs) /\
        new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
        new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
        new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
        new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
        new_state.(st_quit_round_time) = prev_state.(st_quit_round_time) /\
        new_state.(st_received_blames) = prev_state.(st_received_blames) /\
        new_state.(st_vote) = prev_state.(st_vote) /\
        new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
        new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).
    intros.
    unfold new_state.
    unfold state_transition_2_msg_C_precommit.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    repeat split. repeat split. 
    destruct_with_eqn (pc_round precommit =? st_round prev_state).
    destruct_with_eqn (st_first_valid_proposal prev_state).
    destruct_with_eqn (p_block p =? pc_block precommit).
    destruct_with_eqn (1+n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit prev_state precommit))).
    unfold state_set_receive_precommit.
    destruct_with_eqn (is_element (pc_voter precommit) (st_received_precommit_from prev_state)).
    unfold state_set_commit.
    simpl. repeat split. auto.
    unfold state_set_commit.
    simpl. repeat split. auto.
    unfold state_set_receive_precommit.
    destruct_with_eqn (is_element (pc_voter precommit) (st_received_precommit_from prev_state)).
    repeat split.
    auto.
    simpl.
    repeat split.
    auto.
    repeat split.
    auto.
    repeat split.
    auto.
    all:repeat split.
Qed.

Lemma st_2D_only_change_all_cert_AND_dynamic_cert:
    forall e:Event, forall prev_state:StateType,
    let new_state:= (state_transition_2_msg_D_highest_cert e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
    new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
    new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
    new_state.(st_received_blames) = prev_state.(st_received_blames) /\
    new_state.(st_vote) = prev_state.(st_vote) /\
    new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
    new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_msg_D_highest_cert.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    repeat split. repeat split. repeat split. repeat split. repeat split.
    destruct_with_eqn (ev_node e =? leaderOfRound (st_round prev_state)).
    destruct_with_eqn (st_new_view_timeouted prev_state).
    repeat split. auto.
    unfold state_set_recv_cert.
    destruct_with_eqn (st_dynamic_highest_cert prev_state).
    destruct_with_eqn (c_round c <? c_round cert).
    unfold state_set_dynamic_highest_cert.
    simpl. repeat split. auto.
    repeat split. auto. 
    unfold state_set_dynamic_highest_cert.
    simpl. all:repeat split. auto.
Qed.

Lemma st_2E_only_change_all_certs_AND_dynamic_certs:
    forall e:Event, forall prev_state:StateType,
    let new_state:= (state_transition_2_msg_E_vote e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
    new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
    new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
    new_state.(st_received_blames) = prev_state.(st_received_blames) /\
    new_state.(st_vote) = prev_state.(st_vote) /\
    new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
    new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_msg_E_vote.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    repeat split. 
    destruct_with_eqn (v_round vote =? st_round prev_state).
    unfold state_set_receive_vote.
    simpl. all:repeat split.
Qed.

Lemma st_2F_only_change_proposal_related:
    forall e:Event, forall prev_state:StateType,
    let new_state:= (state_transition_2_msg_F_proposal e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_dynamic_highest_cert) = prev_state.(st_dynamic_highest_cert) /\
    new_state.(st_all_certs) = prev_state.(st_all_certs) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_received_blames) = prev_state.(st_received_blames) /\
    new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_msg_F_proposal.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    destruct_with_eqn (st_first_received_proposal prev_state).
    destruct_with_eqn (proposal_beq proposal p).
    destruct_with_eqn (st_first_valid_proposal prev_state).
    destruct_with_eqn (proposal_beq proposal p0).
    destruct_with_eqn (1 + n_faulty <=? length (st_received_valid_proposal_from prev_state)).
    repeat split. 
    destruct_with_eqn (1 + n_faulty <=? length (st_received_valid_proposal_from (state_set_more_proposals prev_state proposal (msg_sender msg)))).
    unfold state_set_more_proposals.
    destruct_with_eqn (is_element (msg_sender msg) (st_received_valid_proposal_from prev_state)).
    unfold state_set_precommit_start.
    simpl. repeat split.
    unfold state_set_precommit_start.
    simpl. repeat split. 
    unfold state_set_more_proposals.
    destruct_with_eqn (is_element (msg_sender msg) (st_received_valid_proposal_from prev_state)).
    repeat split.
    simpl. repeat split.
    repeat split. repeat split.
    destruct_with_eqn (is_proposal_valid_round_proposer proposal prev_state).
    unfold state_set_quit_conflict. simpl. repeat split.
    repeat split.
    destruct_with_eqn (is_proposal_valid_cert proposal prev_state).
    destruct_with_eqn (is_proposal_valid_round_proposer proposal prev_state).
    unfold state_set_first_valid_proposal. simpl. repeat split.
    unfold state_set_first_valid_proposal. simpl. repeat split.
    unfold is_proposal_valid_round_proposer. 
    destruct_with_eqn (p_round proposal =? st_round prev_state).
    simpl.
    destruct_with_eqn (p_proposer proposal =? leaderOfRound (st_round prev_state)).
    unfold state_set_first_received_proposal. simpl. repeat split. repeat split.
    simpl. all:repeat split. 
Qed.

Lemma st_2_trigger_msg_only_change_msg_related:
    forall e:Event, forall prev_state:StateType,
    let new_state:= (state_transition_2_trigger_msg e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_trigger_msg.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    repeat split.
    all:(try apply st_2F_only_change_proposal_related).
    repeat split.
    all:(try apply st_2E_only_change_all_certs_AND_dynamic_certs).
    repeat split.
    all:(try apply st_2C_only_change_recvprecommits_and_commit).
    repeat split.
    all:(try apply st_2B_only_change_recvblames_and_quit_time).
    repeat split.
    all:(try apply st_2A_only_change_quit_time).
    repeat split.
    all:(try apply st_2D_only_change_all_cert_AND_dynamic_cert).
    repeat split.
    repeat split.
Qed.

Lemma st_1_only_keep_node_committed:
    forall e:Event, forall prev_state:StateType, 
    let new_state:= (state_transition_1_quit_round e prev_state) in 
    new_state.(st_node) = prev_state.(st_node) /\ new_state.(st_committed) = prev_state.(st_committed).
    intros.
    unfold new_state.
    unfold state_transition_1_quit_round.
    destruct_with_eqn (st_quit_round_time prev_state).
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    split. all:trivial.
    repeat split.
    all:(try apply st_2E_only_change_all_certs_AND_dynamic_certs).
    repeat split. repeat split. repeat split.
    repeat split.
    all:(try apply st_2D_only_change_all_cert_AND_dynamic_cert).
    destruct_with_eqn timeout.
    repeat split.
    repeat split.
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round.
    simpl.
    all:repeat split.
Qed.

Lemma st_3_only_change_new_view_timeouted:
    forall e:Event, forall prev_state:StateType, 
    let new_state:= (state_transition_3_trigger_timeout e prev_state) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_dynamic_highest_cert) = prev_state.(st_dynamic_highest_cert) /\
    new_state.(st_all_certs) = prev_state.(st_all_certs) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_first_valid_proposal) = prev_state.(st_first_valid_proposal) /\
    new_state.(st_first_received_proposal) = prev_state.(st_first_received_proposal) /\
    new_state.(st_received_valid_proposal_from) = prev_state.(st_received_valid_proposal_from) /\
    new_state.(st_received_blames) = prev_state.(st_received_blames) /\
    new_state.(st_vote) = prev_state.(st_vote) /\
    new_state.(st_precommit_time) = prev_state.(st_precommit_time) /\
    new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from).
    intros.
    unfold new_state.
    unfold state_transition_3_trigger_timeout.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    repeat split.
    destruct_with_eqn (st_committed prev_state).
    repeat split. auto.
    destruct_with_eqn (st_quit_round_time prev_state).
    repeat split. auto.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    repeat split. auto.
    destruct_with_eqn timeout.
    repeat split. auto.
    repeat split. auto.
    repeat split. auto.
    unfold state_set_new_view_timeout.
    simpl.
    repeat split. auto. repeat split. auto.
Qed.



Lemma st_only_keeps_node:
    forall e:Event, forall prev_state:StateType, 
    let new_state:=state_transition e prev_state in 
    new_state.(st_node) = prev_state.(st_node).
    intros.
    unfold new_state.
    unfold state_transition.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    auto.
    destruct_with_eqn (st_committed prev_state).
    auto.
    destruct_with_eqn (st_quit_round_time prev_state).
    apply st_1_only_keep_node_committed.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    apply st_2_trigger_msg_only_change_msg_related.
    apply st_3_only_change_new_view_timeouted.
    auto.
Qed.

(* inverse infer | if some states change, event must satisfy some condition *)

Lemma st_change_round_only_if_quit_status_timer:
    forall e:Event, forall prev_state:StateType, 
    let new_state:=state_transition e prev_state in
    new_state.(st_round) <> prev_state.(st_round) ->
    exists timeout t_node t_round t_expire_time, 
        ev_trigger e = Some (trigger_timeout timeout t_node t_round t_expire_time) /\
        timeout = timeout_quit_status /\
        t_round = prev_state.(st_round).
    intros.
    unfold new_state in H.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    destruct_with_eqn (st_committed prev_state).
    contradiction.
    destruct_with_eqn (st_quit_round_time prev_state).
    unfold state_transition_1_quit_round in H.
    rewrite Heqo in H.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    assert ((state_transition_2_msg_E_vote e prev_state).(st_round) = prev_state.(st_round)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    all:(try contradiction). 
    assert ((state_transition_2_msg_D_highest_cert e prev_state).(st_round) = prev_state.(st_round)).
    apply st_2D_only_change_all_cert_AND_dynamic_cert.
    all:(try contradiction).
    destruct_with_eqn timeout.
    all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    repeat eexists.
    apply Nat.eqb_eq in Heqb1. auto.
    contradiction.
    destruct_with_eqn (ev_trigger e). 
    destruct_with_eqn t.
    assert ((state_transition_2_trigger_msg e prev_state).(st_round) = prev_state.(st_round)).
    apply st_2_trigger_msg_only_change_msg_related.
    all:(try contradiction).
    assert ((state_transition_3_trigger_timeout e prev_state).(st_round) = prev_state.(st_round)).
    apply st_3_only_change_new_view_timeouted.
    all:(try contradiction).

Qed.



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



(* not necessary: (* for construction, use destruct_with_eqn *)
Lemma option_event_not_one_is_some_event: 
    forall e: option Event, ~e=None -> exists se, e = Some se. 
    intros.
    destruct_with_eqn e. 
    exists e0.
    trivial.
    contradiction.
Qed. *)

(* not necessary: rewrite one using the other, then discriminate  *)
(* Lemma option_event_cannot_be_done_and_event: 
    forall e: option Event, forall e':Event, e = Some e' -> e = None -> False.
    intros.
    rewrite H in H0. discriminate.
Qed. *)


(* Make events bi-directional inductive *)
Variable event_to_seq_id: Event -> nat. (* for each node, | for id>=1, this is a partial bijection*)
(* Variable event_to_inv_seq_id: Event -> nat. *) 
(* inv_seq_id assumes termination | not define for now*)

Hypothesis event_id_partial_injection: (*a real hypothesis: events happen in some order. *)
    forall e1 e2:Event, event_to_seq_id e1 = event_to_seq_id e2 -> event_to_seq_id e1 >=1 -> e1.(ev_node) = e2.(ev_node) -> e1 = e2.

Hypothesis event_id_init_first:
    forall n:Node, event_to_seq_id (first_event n) = 1.

(* if e1 -> i, e2->i+2, then exists e3 -> i+1 *)
Hypothesis event_id_continuous:
    forall e1 e2:Event, forall i:nat, 
        event_to_seq_id e1 = i -> event_to_seq_id e2 = S (S i) -> 
        exists e3, event_to_seq_id e3 = S i.

(* id = 0: for irrelevant events *)

(* this is already assuming the protocol will terminate | don't use it for now*)
(* Hypothesis event_id_init_last:
    forall e: Event, direct_next e = None -> event_to_inv_seq_id e = 0. *)

Variable node_id_to_event: Node -> nat -> option Event. (* for each node, this is a partial bijection*)
Hypothesis node_id_to_event_def_id0:
    forall n:Node, node_id_to_event n 0 = None.

Hypothesis node_id_to_event_def:
    forall n:Node, forall i:nat, forall e:Event,
        i>=1 -> 
        node_id_to_event n i = Some e <-> (e.(ev_node) = n /\ event_to_seq_id e = i).

Hypothesis node_id_to_event_def_none:
    forall n:Node, forall i:nat, i>=1 ->
        node_id_to_event n i = None <-> forall e:Event, e.(ev_node) = n -> (event_to_seq_id e < i). 

Lemma node_id_to_event_infer_id: 
    forall n:Node, forall i:nat, forall e:Event,
        node_id_to_event n i = Some e -> event_to_seq_id e = i.
    intros.
    destruct_with_eqn i.
    rewrite node_id_to_event_def_id0 in H. discriminate.
    apply node_id_to_event_def in H.
    destruct H.
    auto.
    lia.
Qed.

Lemma node_id_to_event_infer_node: 
    forall n:Node, forall i:nat, forall e:Event,
        node_id_to_event n i = Some e -> e.(ev_node) = n.
    intros.
    destruct_with_eqn i.
    rewrite node_id_to_event_def_id0 in H. discriminate.
    apply node_id_to_event_def in H.
    destruct H. auto. lia.
Qed.

(* i -> Some e1, i+2 -> Some e2 => i+1 -> Some e3 *)
Lemma node_id_to_event_continuous:
    forall n:Node, forall i:nat, forall e1 e2: Event,
        node_id_to_event n i = Some e1 -> node_id_to_event n (S (S i)) = Some e2 -> 
        exists e3, node_id_to_event n (S i) = Some e3.
    intros.
    destruct_with_eqn (node_id_to_event n (S i)).
    exists e. trivial.
    assert (forall e':Event, e'.(ev_node) = n -> (event_to_seq_id e' < S i)).
    apply node_id_to_event_def_none with (i:=S i). lia. auto. 
    assert (forall e':Event, e'.(ev_node) = n -> (event_to_seq_id e' < S (S i))).
    intros.
    assert (event_to_seq_id e' < S i).
    apply H1. auto. lia.
    assert (node_id_to_event n (S (S i)) = None).
    apply node_id_to_event_def_none with (i:=S (S i)). lia. auto. rewrite H0 in H3. discriminate.
Qed.

Lemma node_id_event_nonempty_i1_implies_nonempty_i:
    forall n:Node, forall i: nat, forall se: Event,
        i>=1 ->
        Some se = node_id_to_event n (S i) ->
        ~node_id_to_event n i=None. 
    intros.
    destruct_with_eqn (node_id_to_event n i).
    discriminate.
    assert (forall e':Event, e'.(ev_node) = n -> (event_to_seq_id e' < i)).
    apply node_id_to_event_def_none with (i:=i). lia. auto.
    assert (forall e':Event, e'.(ev_node) = n -> (event_to_seq_id e' < S i)).
    intros. assert (event_to_seq_id e' < i). apply H1. auto. lia.
    assert (node_id_to_event n (S i) = None).
    apply node_id_to_event_def_none with (i:=S i). lia. auto.
    rewrite H3 in H0. discriminate.
Qed.

Lemma node_id_event_empty_i_implies_empty_i1:
    forall n:Node, forall i: nat, 
        i>=1 ->
        node_id_to_event n i = None ->
        node_id_to_event n (S i) = None.
    intros.
    destruct_with_eqn (node_id_to_event n (S i)).
    assert (~node_id_to_event n i = None).
    apply node_id_event_nonempty_i1_implies_nonempty_i with (se:=e). lia. auto. rewrite H0 in H1. contradiction. auto.
Qed.




Lemma node_id_to_event_id1:
    forall n:Node, node_id_to_event n 1 = Some (first_event n).
    intros.
    assert ((first_event n).(ev_node) = n).
    unfold first_event. trivial.
    assert (event_to_seq_id (first_event n) = 1).
    apply event_id_init_first. 
    apply <- node_id_to_event_def.
    auto. auto.
Qed.

(* #def state_after/before node-id *)
Fixpoint state_after_node_id (n:Node) (i:nat):StateType:=
    match i with 
    | 0 => init_state n
    | (S i') => state_transition_op (node_id_to_event n (i)) (state_after_node_id n (i'))
    end.

Definition state_before_node_id (n:Node) (i:nat):StateType:=
    match i with 
    | 0 => init_state n
    | S i' => state_after_node_id n i'
    end.




Lemma event_node_id_of_event_eq:
    forall e: Event, 
        (event_to_seq_id e)>=1 ->
        node_id_to_event e.(ev_node) (event_to_seq_id e) = Some e.
    
    intros.
    remember (event_to_seq_id e) as i. 
    remember (e.(ev_node)) as n.
    rewrite node_id_to_event_def with (n:=n) (i:=i) (e:=e).
    split.
    all:(try auto).
Qed.

(* unfolding the fixpoint definition will reveal the fix formula. Sometimes I just want the following *)
Lemma state_after_node_id_one_level:
    forall n:Node, forall i:nat,
        state_after_node_id n (S i) = state_transition_op (node_id_to_event n (S i)) (state_after_node_id n i).
    intros.
    remember (state_after_node_id n i) as s.
    unfold state_after_node_id.
    rewrite Heqs.
    trivial.
Qed.

(* #define direct_pred: now determined by node-id system *)
(* direct_pred n 1 = None *)
Definition direct_pred (e: Event): option Event:=
    match event_to_seq_id e with
    | 0 => None 
    | S i => node_id_to_event e.(ev_node) i
    end.

Definition direct_next (e: Event): option Event:=
    node_id_to_event e.(ev_node) (S (event_to_seq_id e)).

(* seems unnecessary now. *)  
(* Lemma pred_is_injective:
    forall e1 e2: Event, direct_pred e1 = direct_pred e2 -> 
        ~direct_pred e1 = None -> e1 = e2. (* note that the special first events can point to the same None *)
Admitted. *)

(*seems unnecessary*)
(* Lemma pred_is_for_same_node:
    forall e1 e2: Event, direct_pred e1 = Some e2 -> e1.(ev_node) = e2.(ev_node).
    intros.
    unfold direct_pred in H.
    destruct_with_eqn (event_to_seq_id e1).
    discriminate.
    rewrite node_id_to_event_infer_node with (n:=(ev_node e1)) (i:=n) (e:=e2). all:(try auto).
Qed. *)

(*seems unncessary*)
(* Lemma direct_next_is_injective:
    forall e1 e2: Event, direct_next e1 = direct_next e2 -> ~direct_next e1 = None -> e1 = e2. (* the last events all point to None | have to prove there exist last event for every node ; *)
Admitted. *)

(* (seems unnecessary) *)
(* Lemma direct_next_is_for_same_node:
    forall e1 e2: Event, direct_next e1 = Some e2 -> e1.(ev_node) = e2.(ev_node).
Admitted. *)

(* some relation between direct_pred/next and event_id*)

(* Lemma next_id_is_direct_next_if_non_none:
    forall e1 e2:Event,
        node_id_to_event (ev_node e1) (S (event_to_seq_id e1)) = Some e2 ->
           Some e2 = direct_next e1.
        intros.
        unfold direct_next.
        auto.
Qed. *)
(* 
Lemma direct_next_of_none_id_is_none:
    forall n:Node, forall i:nat, 
        node_id_to_event n i = None -> node_id_to_event n (S i) = None.
    Admitted.
     *)


    
(* 
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
    node_id_to_ev_history e.(ev_node) (event_to_seq_id e).  *)

(* properties of events: 1. time ordering *)

Hypothesis event_ordering_1_by_time: 
    forall n:Node, forall i1 i2:nat, forall e1 e2:Event,
        node_id_to_event n i1 = Some e1 -> node_id_to_event n i2 = Some e2 -> 
        e1.(ev_time) < e2.(ev_time) -> (event_to_seq_id e1) < (event_to_seq_id e2).

(*if receive message in the last second, it is still valid. *)
Hypothesis event_ordering_2_msg_before_timeout: 
    forall n:Node, forall i1 i2:nat, forall e1 e2: Event, forall msg timeout t_node t_round t_expire_time,
        node_id_to_event n i1 = Some e1 -> node_id_to_event n i2 = Some e2 ->  
        e1.(ev_time) = e2.(ev_time) -> 
        e1.(ev_trigger) = Some (trigger_msg_receive msg) -> 
        e2.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> 
        (event_to_seq_id e1) < (event_to_seq_id e2).

(* 
6 types of messages: proposal/vote/precommit/quit/blame/highest-cert
Problem: if receive the first proposal and quit-conflict at the same time. Leave it until the proof need it.
*)
(* Hypothesis event_ordering_3_msg_by_type:
    forall  *)


(* Lemma state_before_first_event:
    forall n:Node, state_before_event (first_event n) = init_state n.
    intros.
    assert (node_id_to_event n 1 = Some (first_event n)).
    apply node_id_to_event_id1.  
    unfold state_before_event.
Qed. *)
(* Hypothesis state_after_transition_def: 
    forall e:Event, 
    state_after_event e = state_transition e (state_before_event e). *)
(* 
Hypothesis state_direct_pred_def:
    forall e1 e2:Event, 
    direct_pred e2 = Some e1 -> state_after_event e1 = state_before_event e2. *)

(* Lemma state_direct_next: (* can be proved with the above, but assumed for simplicity *)
    forall e1 e2:Event, 
    direct_next e1 = Some e2 -> state_after_event e1 = state_before_event e2.
Admitted. *)

Lemma id_none_before_event_implies_id0:
    forall n:Node, forall i:nat, 
        node_id_to_event n i = None -> 
        ~node_id_to_event n (S i) = None -> i=0.
    intros.
    destruct_with_eqn i.
    auto.
    assert (i>=1).
    lia.
    assert (node_id_to_event n (S i) = None).
    apply node_id_event_empty_i_implies_empty_i1 with (n:=n) . auto. rewrite <-Heqn0 in H. auto.
    rewrite <-Heqn0 in H0. contradiction. 
Qed.

Lemma state_after_equiv:
    forall n:Node, forall i:nat, forall e: Event,
        node_id_to_event n i = Some e ->
        state_after_node_id n i = state_after_event e.
        intros.
        dependent induction i. (* event_i = Some e. In induction hypothesis, want event_i = Some e', not Some e *)
        - rewrite node_id_to_event_def_id0 in H. apply  option_event_cannot_be_done_and_event in H. contradiction. auto. 
        - destruct_with_eqn (node_id_to_event n i).
                assert (state_after_node_id n i = state_after_event e0).
                apply IHi with (e:=e0). auto.
                destruct_with_eqn i. (* i should >=1*)
                rewrite node_id_to_event_def_id0 in Heqo. 
                    discriminate.
                rewrite state_after_transition_def with (e:=e).
                rewrite <- state_direct_pred_def with (e1:=e0) (e2:=e).
                rewrite <- H0.
                remember (S n0) as n1.
                remember (state_after_node_id n n1) as state_n1.
                simpl.
                rewrite -> H.
                unfold state_transition_op.
                rewrite <- Heqstate_n1. 
                trivial.

                unfold direct_pred.
                replace (event_to_seq_id e) with (S (S n0)).
                assert (ev_node e = n).
                apply node_id_to_event_def_node with (i:=(S( S(n0)))). auto.
                rewrite -> H1.
                auto.
                rewrite -> node_id_to_event_def_id with (n:=n)(i:=S(S n0)). auto.
                auto.
                assert (i=0).
                apply id_none_before_event_implies_id0 with (n:=n). auto. 
                rewrite -> H.
                discriminate.
                rewrite H0.
                unfold state_after_node_id.
                rewrite H0 in H.
                rewrite -> H.
                unfold state_transition_op.
                rewrite state_after_transition_def.
                assert (state_before_event e = init_state n).
                assert ( e = first_event n).
                apply event_id_bijection with (e1:=e) (e2:=first_event n). 
                rewrite -> event_id_init_first.
                apply node_id_to_event_def_id with (n:=n)(i:=1). auto.
                unfold first_event.
                simpl.
                apply node_id_to_event_def_node with (i:=1). auto.
                rewrite -> H1.
                apply state_before_first_event.
                rewrite -> H1.
                auto.
Qed.

Lemma state_before_equiv:
    forall n:Node, forall i:nat, forall e: Event,
        node_id_to_event n i = Some e ->
        state_before_node_id n i = state_before_event e.


Lemma state_node_id_transition:
    forall n:Node, forall i:nat, 
        state_after_node_id n i = state_transition_op (node_id_to_event n i) (state_before_node_id n i).
    intros.
    destruct_with_eqn i.
    unfold state_after_node_id.
    unfold state_before_node_id.
    rewrite node_id_to_event_def_id0.
    simpl.
    auto.
    unfold state_after_node_id.
    unfold state_before_node_id.
    unfold state_after_node_id.
    auto.
Qed.

Lemma node_of_state_after_node_id_is_n:
    forall n:Node, forall i:nat, 
        (state_after_node_id n i).(st_node) = n.
    intros.
    dependent induction i.
    - simpl. auto.
    - simpl.
    remember (state_after_node_id n i) as state_i.
    remember (state_after_node_id n (S i)) as state_i1.
    destruct_with_eqn (node_id_to_event n (S i)).
    simpl.
    rewrite <- IHi.
    apply st_only_keeps_node with (e:=e)(prev_state:=state_i).
    simpl. auto.
Qed.
(* =================== PART 4 END ===================== *)

(* ################### PART 5 Trigger & its Generation by events ########*)
(* every event has a trigger. except the special first_event *)

(* the only difference between honest node and dishonest node is: 
For honest node, every trigger of new event is generated by some old event (possibly old events of others). 

Dishonest node can have any arbitrary event. Most importantly, the trigger generation model only works for honest nodes. *)

(*
Another constraint: dishonest nodes cannot fake messages. they cannot generate timeout for others. If can not fake messages senders/voters. 
*)

Hypothesis honest_event_triggered_by_something: forall n:Node, forall i:nat, forall e:Event, 
    isHonest n = true -> node_id_to_event n i = Some e -> ~ e.(ev_trigger) = None.


Hypothesis synchrony: 
    forall msg:MsgType, msg_receive_time msg >= msg.(msg_send_time) /\ msg_receive_time msg <= msg.(msg_send_time) + delta.

Lemma synchrony_1:
    forall msg:MsgType, msg_receive_time msg >= msg.(msg_send_time).
    intros.
    apply synchrony.
Qed.

Lemma synchrony_2:
    forall msg:MsgType, msg_receive_time msg <= msg.(msg_send_time) + delta.
    intros.
    apply synchrony.
Qed.

(* Hypothesis event_triggered_by_msg_at_recv_time: 
    forall e:Event, forall msg:MsgType,e.(ev_trigger) = Some (trigger_msg_receive msg) -> (msg_receive_time msg) = e.(ev_time).

Lemma the_above_is_wrong: False.
    remember (mkMsgType 0 0 (msg_blame (mkBlameType 0 0)) 0) as msg0.
    remember (mkEvent 0 (Some (trigger_msg_receive msg0)) (2*delta+1)) as e0.
    assert (msg_receive_time msg0 = 2*delta+1).
    rewrite event_triggered_by_msg_at_recv_time with (e:=e0) (msg:=msg0).
    rewrite Heqe0. auto. 
    rewrite Heqe0. auto.
    assert (msg_receive_time msg0 <= delta).
    assert (msg_send_time msg0 = 0).
    rewrite Heqmsg0. auto.
    rewrite synchrony_2 with (msg:=msg0).
    rewrite H0. lia.
    rewrite H in H0.
    lia.
Qed. *)

Hypothesis event_triggered_by_msg_at_recv_time:
    forall n:Node, forall i:nat, forall e:Event, forall msg:MsgType,
        node_id_to_event n i = Some e ->
        e.(ev_trigger) = Some (trigger_msg_receive msg) -> 
        msg.(msg_receive_time) = e.(ev_time).

Hypothesis event_triggered_by_msg_at_receiver:
    forall n:Node, forall i:nat, forall e:Event, forall msg:MsgType,
        node_id_to_event n i = Some e ->
        e.(ev_trigger) = Some (trigger_msg_receive msg) -> 
        msg.(msg_recipient) = e.(ev_node).

Hypothesis event_triggered_by_timeout_at_expire_time:
    forall n:Node, forall i:nat, forall e:Event, forall timeout t_node t_round t_expire_time,
        node_id_to_event n i = Some e ->
       e.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> 
       e.(ev_time) = t_expire_time.

Hypothesis event_triggered_by_timeout_of_itself:
    forall n:Node, forall i:nat, forall e:Event, forall  timeout t_node t_round t_expire_time,
        node_id_to_event n i = Some e ->
       e.(ev_trigger) = Some (trigger_timeout timeout t_node t_round t_expire_time) -> t_node = e.(ev_node).

(* An event generate some events in the future. If it is timeout type, the trigger is exactly generated. If it is sending a message, the message receive time might be delayed by at most delta after the sending time. *)

(* default first block is 1 *)


(* A list of all triggers to consider.
1. proposal-receiving timeout of the first round (handled by first_event)
2. leader of first round sending proposal to all replicas (handled by first event)
3. upon receiving the first proposal => (broadcast) forward the proposal & vote (broadcast) 
*)

(* since only replicas are broadcasted to. The safety/liveness only works for replicas. *)

Definition node_to_msg (sender:Node) (content:MsgContentType) (send_time:nat) (node:nat) : MsgType :=
    mkMsgType sender node content send_time.

Definition broadcast_msgs (sender:Node) (content:MsgContentType) (send_time: nat): list MsgType :=
    map (node_to_msg sender content send_time) replicas. 

Definition broadcast_msgs_to_trigger_list (sender:Node) (content:MsgContentType) (send_time: nat): list TriggerType :=
    map (fun msg => trigger_msg_receive msg) (broadcast_msgs sender content send_time).

Definition triggers_generated_by_receiving_a_proposal_def (e:Event) (proposal:ProposalType) (prev_state:StateType) (new_state:StateType): list TriggerType :=
    let vote_triggers:= broadcast_msgs_to_trigger_list e.(ev_node) (msg_vote (mkVoteType proposal.(p_block) proposal.(p_round) e.(ev_node))) e.(ev_time) in
    let forward_triggers:= broadcast_msgs_to_trigger_list e.(ev_node) (msg_propose proposal) e.(ev_time) in
    match prev_state.(st_first_received_proposal) with 
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

Lemma st_change_committed_only_if_false_to_true:
    forall e:Event, forall prev_state:StateType,
    let new_state:=state_transition e prev_state in
    new_state.(st_committed) <> prev_state.(st_committed) ->
    prev_state.(st_committed) = false /\ new_state.(st_committed) = true.
    intros.
    destruct_with_eqn (st_committed prev_state).
    (* new state must be committed*)
    unfold new_state in H.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    rewrite Heqb in H.
    contradiction.
    split. auto.
    destruct_with_eqn (st_committed new_state).
    auto. contradiction.

Qed.

Lemma st_change_locked_highest_cert_only_if_status_timer:
    forall e:Event, forall prev_state:StateType,
    let new_state:=state_transition e prev_state in
    new_state.(st_locked_highest_cert) <> prev_state.(st_locked_highest_cert) ->
    exists timeout t_node t_round t_expire_time, 
        ev_trigger e = Some (trigger_timeout timeout t_node t_round t_expire_time) /\
        timeout = timeout_quit_status /\
        t_round = prev_state.(st_round) /\
        t_expire_time = e.(ev_time).
    intros.
    unfold new_state in H.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    destruct_with_eqn (st_committed prev_state).
    contradiction.
    destruct_with_eqn (st_quit_round_time prev_state).
    unfold state_transition_1_quit_round in H.
    rewrite Heqo in H.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    assert ((state_transition_2_msg_E_vote e prev_state).(st_locked_highest_cert) = prev_state.(st_locked_highest_cert)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    rewrite H0 in H. all:(try contradiction).
    assert ((state_transition_2_msg_D_highest_cert e prev_state).(st_locked_highest_cert) = prev_state.(st_locked_highest_cert)).
    apply st_2D_only_change_all_cert_AND_dynamic_cert.
    rewrite H0 in H. all:(try contradiction).
    destruct_with_eqn timeout. all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H.
    simpl in H. all:(try contradiction).
    repeat eexists. apply Nat.eqb_eq. repeat auto.   
    apply triggered_by_timeout_at_expire_time.

    
Qed.



(* delayed because must prove that commit-false implies <=f precommits*)
Lemma st_change_commited_only_if_recv_precommit:
    forall e:Event, forall prev_state:StateType, 
    let new_state:=state_transition e prev_state in
    new_state.(st_committed) <> prev_state.(st_committed) ->
    exists msg precommit, 
        ev_trigger e = Some (trigger_msg_receive msg) /\
        msg.(msg_content) = msg_precommit precommit /\
        precommit.(pc_round) = prev_state.(st_round) /\ 
        (exists valid_proposal, prev_state.(st_first_valid_proposal) = Some valid_proposal) /\
        (length (prev_state.(st_received_precommit_from)) = n_faulty) /\
        (length (new_state.(st_received_precommit_from)) = 1+n_faulty) /\
        ~ In precommit.(pc_voter) prev_state.(st_received_precommit_from).
    intros.
    assert (prev_state.(st_committed) = false /\ new_state.(st_committed) = true).
    apply st_change_committed_only_if_false_to_true.
    unfold new_state in H. auto.
    destruct H0.
    clear H.
    unfold new_state in H1.
    unfold state_transition in H1.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    rewrite H1 in H0. discriminate.
    rewrite -> H0 in H1.
    destruct_with_eqn (st_quit_round_time prev_state).
    unfold state_transition_1_quit_round in H1.
    rewrite Heqo in H1.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).

    rewrite H0 in H1. discriminate.
    assert ((state_transition_2_msg_E_vote e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)).
    assert ((state_transition_2_msg_D_highest_cert e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2D_only_change_all_cert_AND_dynamic_cert.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)).
    destruct_with_eqn timeout.
    all: (try (rewrite H0 in H1; discriminate)).
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H1.
    simpl in H1. all: (try (rewrite H0 in H1; discriminate)).
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    
    unfold state_transition_2_trigger_msg in H1.
    rewrite Heqo0 in H1.



    destruct_with_eqn (msg_content msg).
    assert ((state_transition_2_msg_F_proposal e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2F_only_change_proposal_related.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)).
    assert ((state_transition_2_msg_E_vote e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)).
    4:{assert ((state_transition_2_msg_D_highest_cert e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2D_only_change_all_cert_AND_dynamic_cert.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)). }
    2:{assert ((state_transition_2_msg_B_blame e prev_state).(st_committed) = prev_state.(st_committed)). 
    apply st_2B_only_change_recvblames_and_quit_time.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)). 
    }
    2:{assert ((state_transition_2_msg_A_quit e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_2A_only_change_quit_time.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)). }
    2:{assert ((state_transition_3_trigger_timeout e prev_state).(st_committed) = prev_state.(st_committed)).
    apply st_3_only_change_new_view_timeouted.
    rewrite H in H1. all: (try (rewrite H0 in H1; discriminate)). }
    unfold state_transition_2_msg_C_precommit in H1.
    rewrite Heqo0 in H1.
    rewrite Heqm in H1.
    destruct_with_eqn (pc_round precommit =? st_round prev_state).
    destruct_with_eqn (st_first_valid_proposal prev_state).
    destruct_with_eqn (p_block p =? pc_block precommit).
    destruct_with_eqn (1 + n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit prev_state precommit))).
    unfold state_set_receive_precommit in H1.
    destruct_with_eqn (is_element (pc_voter precommit) (st_received_precommit_from prev_state)).
    simpl in H1.


Qed.

Lemma state_transition_remain_committed_once_committed:
    forall e: Event, forall prev_state: StateType,
        prev_state.(st_committed) = true ->
        state_transition e prev = prev_state.
        intros.
        unfold state_transition.
        case_eq (prev_state.(st_node) =? e.(ev_node)).
        simpl.
        intros. 
        rewrite H.
        trivial.
        intro.
        simpl.
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

    (* case next_event as [e2|].
    2:trivial. *)
    induction id_gap.
    replace (e1_id + 0) with e1_id. 
    2:lia.
    
    (* TODO pick up proof here | may need to change the above notion *)
    unfold next_event.
    replace (e1_id+0) with e1_id. 2:lia.
    replace (node_id_to_event e1.(ev_node) e1_id) with (Some e1). 
    trivial.
    replace e1_id with (event_to_seq_id e1).
    rewrite event_node_id_of_event_eq with (e:=e1). trivial.
    trivial.

    destruct_with_eqn next_event.
    2:trivial.

    remember (node_id_to_event e1.(ev_node) (e1_id + id_gap)) as gap_event.
    (* if gap_event is None, then next_event is also None. *)
    (* if gap_event is not None, the next_event might be None or not. If next_event is None, ok. Otherwise Some next_event = direct_next *) 
    destruct_with_eqn gap_event.
    assert (e1_id+id_gap = event_to_seq_id e0).
    rewrite node_id_to_event_def_id with (n:=e1.(ev_node)) (i:=e1_id+id_gap) (e:=e0). auto.
    rewrite Heqgap_event. trivial.
    assert (e0.(ev_node) = e1.(ev_node)).
    rewrite node_id_to_event_def_node with (n:=e1.(ev_node)) (i:=e1_id+id_gap) (e:=e0). auto.
    rewrite Heqgap_event. trivial.
    assert (next_event=direct_next e0).
    unfold next_event.
    unfold direct_next.
    rewrite H2.
    replace (e1_id+ S id_gap) with (S (e1_id + id_gap)).
    rewrite H1. auto.
    lia.
    apply once_committed_commit_in_next_state with (e:=e0) (e_next:=e).
    rewrite H2.
    trivial.
    simpl in IHid_gap.
    trivial.
    replace (Some e) with next_event.
    rewrite H3.
    trivial.
    (* conflict. *)
    assert (next_event=None).
    unfold next_event.
    replace (e1_id+ S id_gap) with (S (e1_id + id_gap)).
    rewrite direct_next_of_none_id_is_none with (n:=e1.(ev_node)) (i:=e1_id+id_gap). trivial.
    rewrite Heqgap_event in Heqo0.
    auto.
    lia.
    assert False.
    apply option_event_cannot_be_done_and_event with (e:=next_event) (e':=e).
    auto. auto. auto. 
Qed.


Lemma once_committed_remain_committed_by_node_id:
    forall n:Node, forall i:nat, 
        st_committed (state_after_node_id n i) = true ->
        forall gap:nat, 
            st_committed (state_after_node_id n (gap+i)) = true.
        intros.
        induction gap.
        - simpl. auto.
        - simpl.
            destruct_with_eqn (node_id_to_event n ( S (gap+i))).
            simpl.
            unfold state_transition.
            assert (st_node (state_after_node_id n (gap+i)) = n). 
            apply node_of_state_after_node_id_is_n.
            rewrite -> H0.
            assert (ev_node e = n).
            apply node_id_to_event_def_node with (i:=S(gap+i)). auto.
            rewrite -> H1.
            assert (n=?n = true). apply Nat.eqb_refl with (n:=n).
            rewrite -> H2.
            simpl.
            rewrite -> IHgap.
            auto.
            simpl.
            auto.
Qed.

(* lemma to prove: 
    forall n, i, if the state is non-committed, then precommits is not a quorum. 
    induction step: 
    i = 0 ok. 
    if at i, non-committed -> not quorum. => at i+1, remain non-committed -> not quorum. otherwise has committed. 

    corner case, event_i is None => i = 0. then event_{i+1} is init state. 
    event_{i+1} is None => not interested. 
    so, the main case is when event_i is not None, event_{i+1} is not None. 
    know that state_{i+1} says non-committed. 
    First rule out the case that state_{i} is committed. For otherwise, state_{i+1} is committed. 
*)

Lemma once_comitted_state_not_change_node_id:
    forall n:Node, forall i:nat, forall gap:nat,
        st_committed (state_after_node_id n i) = true ->
        state_after_node_id n (gap+i) = state_after_node_id n i.
    intros.
    induction gap.
    repeat simpl. auto.
    remember (state_after_node_id n i) as state_i.
    remember (state_after_node_id n (gap+i)) as state_gap_i.
    simpl.
    assert (st_committed state_gap_i = true). rewrite IHgap. auto.
    rewrite <- Heqstate_gap_i.
    destruct_with_eqn (node_id_to_event n (S(gap+i))).
    unfold state_transition_op.
    unfold state_transition.
    destruct (negb (st_node state_gap_i =? ev_node e)).
    auto.
    rewrite H0. auto.
    repeat simpl. auto.
Qed.

Lemma state_transition_receive_proposal_keeps_commit:
    forall e: Event, forall curr_state: StateType,
        curr_state.(st_committed) = true ->
        state_transition_receive_proposal e curr_state = curr_state.
        intros.
        unfold state_transition_receive_proposal.   
        destruct_with_eqn (ev_trigger e).
        destruct_with_eqn t.
        destruct_with_eqn (msg_content msg).
        destruct_with_eqn (st_first_received_proposal curr_state).
        destruct_with_eqn (proposal_beq proposal p).
        destruct_with_eqn (st_first_valid_proposal curr_state).
        destruct_with_eqn (proposal_beq proposal p0).
        destruct_with_eqn (1+n_faulty<=?length (st_received_valid_proposal_from curr_state)).
        all:trivial.
        destruct_with_eqn (1+n_faulty<=? length (st_received_valid_proposal_from (state_set_more_proposals curr_state proposal (msg_sender msg)))).
Qed.

(* this lemma relies on (not_committed -> not enough precommits)*)
Lemma turn_committed_implies_enough_precommits:
    forall n:Node, forall i:nat,
        st_committed (state_after_node_id n i) = false ->
        is_quorum (state_after_node_id n i).(st_received_precommit_from) = false ->
        st_committed (state_after_node_id n (S i)) = true ->
        is_quorum (state_after_node_id n (S i)).(st_received_precommit_from) = true.

    intros.
    (* destruct on the branches of state_transition. In most branches, quorum not change. In some, quorum change but not trigger commit, violating the hypothesis. In one branch, trigger commit, yes. *)
    remember (state_after_node_id n i) as state_i.
    rewrite state_after_node_id_one_level with (n:=n) (i:=i).
    destruct_with_eqn (node_id_to_event n (S i)).
    2:{
        (* contradiction in hyp:  *)
        assert (state_after_node_id n (S i) = state_i).
        rewrite state_after_node_id_one_level with (n:=n) (i:=i).
        rewrite Heqo.
        simpl.
        auto.
        simpl.
        rewrite <- Heqstate_i.
        rewrite H2 in H1.
        rewrite H in H1. discriminate.
    }
    1:{
        simpl.
        remember (state_after_node_id n (S i)) as state_i1.
        assert (state_i1 = state_i -> False).
        intros.
        rewrite H2 in H1.
        rewrite H1 in H.
        discriminate.
        assert (state_i1 = state_transition e (state_after_node_id n i)).
        rewrite Heqstate_i1.
        rewrite state_after_node_id_one_level.
        rewrite Heqo.
        simpl. trivial.

        unfold state_transition.
        rewrite <- Heqstate_i.
        destruct_with_eqn (negb (st_node state_i =? ev_node e)).
        replace (ev_node e) with n in Heqb.
        (* st_node state_i = n*)
        assert (st_node state_i = n).
        rewrite Heqstate_i.
        apply node_of_state_after_node_id_is_n with (n:=n) (i:=i).

        rewrite H4 in Heqb.
        rewrite -> Nat.eqb_refl with (n:=n) in Heqb.
        discriminate.
        rewrite node_id_to_event_def_node with (n:=n) (i:=S i) (e:=e). auto.
        auto.
        rewrite -> H.

        (* note that precommits also change by enter new round, triggered by timeout, quit status round match*)

        destruct_with_eqn (st_quit_round_time state_i).
        (* assert (st_received_precommit_from state_i1 = st_received_precommit_from state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0.  *)
        destruct_with_eqn (ev_trigger e).
        destruct_with_eqn t.

        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1.

        destruct_with_eqn (msg_content msg). all:trivial.
        destruct_with_eqn (v_round vote =? st_round state_i). 
        unfold state_set_receive_vote.
        simpl. all:trivial.

        rewrite H4 in H1. rewrite H1 in H. discriminate. 
        destruct_with_eqn timeout.
        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. 
        all:trivial. rewrite H4 in H1. rewrite H1 in H. discriminate. 

        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. 
        all:trivial. rewrite H4 in H1. rewrite H1 in H. discriminate. 

        (*now timeout quit status*)
        destruct_with_eqn (round=? st_round state_i).
        unfold state_set_enter_new_round. 
        assert (st_committed state_i1 = false).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. rewrite Heqb0. 
        unfold state_set_enter_new_round. simpl. all:trivial. 
        rewrite H4 in H1. discriminate.
        assert (st_committed state_i1 = st_committed state_i). 
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. rewrite Heqb0. 
        all:trivial.
        rewrite H4 in H1. rewrite H1 in H. discriminate.


        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. 
        all:trivial.
        rewrite H4 in H1. rewrite H1 in H. discriminate.

        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. 
        all:trivial.
        rewrite H4 in H1. rewrite H1 in H. discriminate.

        destruct_with_eqn (ev_trigger e).
        destruct_with_eqn t.
        destruct_with_eqn (msg_content msg).

        assert (st_committed state_i1 = st_committed state_i).
        rewrite -> Heqstate_i1. rewrite state_after_node_id_one_level. rewrite -> Heqo. unfold state_transition_op. unfold state_transition. rewrite <- Heqstate_i. rewrite -> Heqb. rewrite H. rewrite Heqo0. rewrite Heqo1. rewrite Heqm. 
        all:trivial.
        rewrite H4 in H1. rewrite H1 in H. discriminate.










        

    }

    Abort.


Qed.

Lemma not_committed_implies_not_enough_precommits:
    forall n: Node, forall i: nat,
        ~node_id_to_event n i = None ->
        let state := state_after_node_id n i in
        state.(st_committed) = false -> 
        is_quorum state.(st_received_precommit_from) = false.
        intros.
        unfold state.
        unfold state in H0. 
        dependent induction i.
        rewrite node_id_to_event_def_id0 in H.
        contradiction.

        destruct_with_eqn (node_id_to_event n i).
        (* the first case, last_event = Some e *) (* will use the IH*)
        (*simple goal first*)
        (* none - some -> i=0*)
        Focus 2.
        assert (i=0).
        apply id_none_before_event_implies_id0 with (n:=n) (i:=i). auto. auto.
        rewrite H1.
        unfold state_after_node_id.
        rewrite node_id_to_event_id1.
        unfold state_transition_op.
        unfold first_event.
        unfold init_state.
        unfold state_transition.
        simpl.
        replace (n=?n) with true.
        simpl.
        unfold is_quorum.
        simpl.
        auto.
        rewrite -> Nat.eqb_refl with (n:=n). auto.
        (* the main case *)
        (* if the event is*)

        destruct_with_eqn (st_committed (state_after_node_id n i)).
        (* if committed -> will be committed -> contradiction*)
        assert (state_after_node_id n (S i) = state_after_node_id n i).
        replace (S i) with (1+i) by lia.
        
        apply once_comitted_state_not_change_node_id with (n:=n) (i:=i) (gap:=1). auto.
        assert (st_committed (state_after_node_id n (S i)) = true). 
        apply once_committed_remain_committed_by_node_id with (n:=n) (i:=i) (gap:=1). auto.
        rewrite H0 in H2. discriminate.
        (* the most important case, not-commit -> not-commit. Require a case work *)
        rewrite state_after_node_id_one_level with (n:=n) (i:=i).
        assert (Some e<>None -> false = false).
        auto.
        apply IHi in H1.
        2:(apply some_e_not_none with (e:=e)). (*Some e<> None*)
        2:(apply some_e_not_none with (e:=e)). 
        destruct_with_eqn (node_id_to_event n (S i)).
        (* if event_i+1 is None, then state_i+1 is init_state. *)
        2:simpl. 2:apply H1.
        unfold state_transition_op.
        (* do branching over state_transition. In most branches, the st_received_precommit_from are not changed | In some branches, they change. but use the condition that commmit is not triggered to say that is not quorum | Painful branching *)
        remember (state_after_node_id n i) as state_i.
        unfold state_transition.
        destruct (negb (st_node state_i =? ev_node e0)). (*not important*) 
        auto.
        rewrite Heqb.
        destruct (st_quit_round_time state_i).
        destruct (ev_trigger e0).


        



        

        
        





Qed.

Lemma is_committed_if_enough_precommits:
    forall n: Node, forall i: nat, forall e:Event,
        Some e = node_id_to_event n i ->
        let state := state_after_event e in
        state.(st_committed) = true -> 
        is_quorum state.(st_received_precommit_from) = true.

        
Admitted.


Lemma if_committed_exists_block: 
    forall e: Event, 
    isHonest e.(ev_node) = true ->
    (state_after_event e).(st_committed) = true ->
    exists proposal, (state_after_event e).(st_first_valid_proposal) = Some proposal.

Admitted. 

Theorem lemma_61_part1:
    forall e: Event, forall block: BlockType,
    isHonest e.(ev_node) = true ->
    (state_before_event e).(st_committed) = false ->
    (state_after_event e).(st_committed) = true ->
    let commit_proposal:= (state_after_event e).(st_first_valid_proposal) in
    let round := (state_after_event e).(st_round) in
    (forall e2: Event,
        let state2after:= state_after_event e2 in 
        state2after.(st_round) = round -> 
        is_quorum (state2after.(st_all_certs) round block) = true -> (* if there is a certified block in the same round, must be the committed one*)
        (match commit_proposal with 
        | None => False
        | Some proposal => block = proposal.(p_block)
        end 
        )).

    Admitted. 

Theorem lemma_61_part2:
    forall e: Event, 
    isHonest e.(ev_node) = true ->
    (state_before_event e).(st_committed) = false ->
    (state_after_event e).(st_committed) = true ->
    let commit_proposal:= (state_after_event e).(st_first_valid_proposal) in
    let round := (state_after_event e).(st_round) in
    (forall e2: Event,
        let state2before:= state_before_event e2 in
        let state2after:= state_after_event e2 in
        isHonest e2.(ev_node) = true -> 
        state2before.(st_round) = round ->
        state2after.(st_round) = (round+1) -> 
        exists cert:Certificate, 
        state2after.(st_locked_highest_cert) = Some cert /\
        (match commit_proposal with 
        | None => False
        | Some proposal => cert.(c_block) = proposal.(p_block)
        end 
        )).

Admitted.



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

