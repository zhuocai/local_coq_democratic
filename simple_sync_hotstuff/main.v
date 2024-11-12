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
Scheme Equality for list. 
Import ListNotations.


Section SyncHotStuff.

(* ############### PART 1: Basic data types ##################*)


(* Nat.eqb_refl *)

(* Use Nat.eqb_eq*)

Lemma nat_eqb_eq_single:
    forall x y : nat, Nat.eqb x y = true -> x = y.
    intros.
    apply Nat.eqb_eq. auto.
Qed.

Lemma nat_eqb_eq_single_reverse:
    forall x y : nat, x = y -> Nat.eqb x y = true.
    intros.
    apply Nat.eqb_eq. auto.
Qed.
(* Lemma list_eq_or_neq: forall A:Set, forall a b: list A, a=b \/~a=b.
    intros. destruct (list_eq_dec A a b). left. apply e. right. apply n.
Qed. *)

(* replace with leb_iff_conv in Arith.Compare_dec*)
(* Theorem leb_iff_conv: forall a b: nat, (a<=?b) = false <-> a>b.
intros.
split.
apply leb_iff_conv. auto.

Qed. *)

Definition is_element (a : nat) (b : list nat) : bool :=
  existsb (fun x => Nat.eqb x a) b.


Theorem neqb_neq:
    forall a b:nat, (a=?b) = false <-> a<>b.
    intros.
    split.
    assert ({a=b} + {a<>b}).
    apply eq_dec with (x:=a)(y:=b) (beq:=Nat.eqb).
    intros. rewrite <- Nat.eqb_refl with (x:=x). auto.
    intros. rewrite <- Nat.eqb_eq with (n:=x) (m:=y). auto.
    destruct H. 
    rewrite e. rewrite Nat.eqb_refl.  congruence. auto.
    intros.
    destruct_with_eqn (a=?b).
    rewrite Nat.eqb_eq in Heqb0. congruence.
    auto.
Qed.

Theorem is_element_true_prop: forall A b, is_element b A = true <->In b A.
    intros.
    split.
    intros.
    induction A.
    simpl in H. congruence.
    simpl in H. simpl.
    destruct_with_eqn (a=?b).
    left. apply Nat.eqb_eq. auto. 
    simpl in H. right. apply IHA. auto.

    intros.
    induction A.
    simpl in H. contradiction.
    simpl in H. destruct H.
    simpl. rewrite H. rewrite Nat.eqb_refl. simpl. auto.
    apply IHA in H. simpl. rewrite H. simpl. destruct_with_eqn (a=?b). simpl. auto. simpl. auto. 
Qed.



Theorem is_element_false_prop: forall A:list nat,forall b:nat,
    is_element b A = false <-> ~ In b A.
    intros.
    split.
    intros.
    induction A.
    simpl. auto.
    simpl in H.
    simpl.
    destruct_with_eqn (a=?b).
    simpl in H. congruence.
    assert (a<>b) by (apply neqb_neq; auto).
    simpl in H. apply IHA in H.
    assert (a<>b /\(~In b A)). split. auto. auto. 
    apply Classical_Prop.and_not_or with (P:= (a=b)) (Q:=(In b A)). auto.
    intros. 
    induction A.
    simpl. auto.
    simpl in H.
    apply (Classical_Prop.not_or_and (a=b) (In b A)) in H.
    destruct H.
    apply IHA in H0.
    simpl. assert (a=?b=false) by (rewrite neqb_neq with (a:=a)(b:=b); auto).
    rewrite H1. auto.
Qed.



Variable delta : nat. 

Hypothesis delta_is_positive: delta >= 1.

(* ============================ PART 1 ==========================*)

(* #def 1A *)

Definition Node: Type := nat. 
Definition BlockType : Type := nat.

Variable isHonest: Node -> bool. 

Variable n_faulty: nat. 
Hypothesis n_positive: n_faulty >= 1.
Definition n_replicas: nat := 2*n_faulty+1.

(* #total nodes = 2*n_faulty+1. Actual faulty nodes: <= n_faulty *)

Definition replicas: list Node := List.seq 0 n_replicas.

Hypothesis honest_majority: 
    length (filter isHonest replicas) >= 1+n_faulty.

Lemma in_replicas_cond: forall n: Node, 
    n < n_replicas <-> In n replicas.
    intros.
    split.
    intros.
    apply in_seq. lia.
    intros.
    apply in_seq with (start:=0) (len:=n_replicas).
    unfold replicas in H. auto.
Qed.

Lemma is_replicas_element_cond: forall n:Node, 
    n< n_replicas -> is_element n replicas = true.
    intros.
    assert (In n replicas).
    apply in_replicas_cond. auto.
    apply is_element_true_prop. auto.
Qed.  

Definition leaderOfRound (r: nat): Node := (r mod (n_replicas)).

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

Fixpoint is_subset (list1: list Node) (list2: list Node): bool:=
    match list1 with
    | [] => true
    | n::list1' => if is_element n list2 then is_subset list1' list2 else false
    end.

(* a nonrepeat subset of replicas *)

Definition is_nonrepeat_subset_replicas (nodes: list Node):bool:=
    is_nonrepeat nodes && is_subset_replicas nodes.

(* a quorum is a nonrepeat subset of replicas *)

Definition is_quorum (nodes: list Node):bool:=
    is_nonrepeat_subset_replicas nodes && ((1+n_faulty) <=? length nodes).

Definition honest_replicas : list Node := filter isHonest replicas.
Definition dishonest_replicas : list Node := filter (fun n => negb (isHonest n)) replicas.

Lemma honest_replicas_length: length honest_replicas >= 1+n_faulty.
    unfold honest_replicas.
    auto.
Qed.

(* induction on both length and start *)
(* Lemma filter_length_my: 
    forall n start len:nat, forall filter_cond: Node -> bool, 
    let l := List.seq start len in
    let neg_filter_cond:= fun n => negb (filter_cond n) in
    n <= len ->
    length (filter filter_cond l) >= n -> 
    length (filter neg_filter_cond l) <= len-n. 
    intros.
    generalize dependent len.
Qed.  *)


Lemma dishonest_replicas_length: length dishonest_replicas <= n_faulty.
    assert (length (honest_replicas) + length (dishonest_replicas) = length replicas).
    unfold honest_replicas. unfold dishonest_replicas.
    apply filter_length.
    unfold replicas in H. rewrite length_seq in H.
    unfold n_replicas in H. 
    fold honest_replicas in honest_majority. 
    remember (length honest_replicas) as l1.
    remember (length dishonest_replicas) as l2.
    lia.
Qed.

Lemam

Lemma filter_sublist:
    forall list1 list2: list Node, 
        is_nonrepeat list1 = true ->
        is_nonrepeat list2 = true ->
        is_subset list1 list2 = true ->
        list1 = filter (fun n => is_element n list1) list2.
Qed.

(* idea of induction: 
the list is non-repeat subset. 
if induction on list. 
if the first element is honest, ok. 
otherwise, the remaining is a non-repeat subset of length - 1.
*)

Lemma list_is_quorum_then_exists_honest_node:
    forall l: list Node, is_quorum l = true -> length (filter isHonest l) >=1.
    intros.
    unfold is_quorum in H.
    destruct_with_eqn (is_nonrepeat_subset_replicas l).
    destruct_with_eqn ((1+n_faulty) <=? length l).
    (* this is the case *)
    2:{simpl in H. congruence. }
    2:{simpl in H. congruence. }
    clear H.
    unfold is_nonrepeat_subset_replicas in Heqb.
    rewrite Nat.leb_le in Heqb0. 
    
    (*step 1: *)
    assert (l = filter (fun n => is_element n l) replicas).


    assert (length(filter (fun n => negb (isHonest n)) l) <= length (filter (fun n => negb (isHonest n)) replicas)).

    generalize Heqb. generalize Heqb0. 
    remember (length l) as len_l. 
    dependent induction len_l.


Qed. 


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

Definition state_set_recv_opt_cert (curr_state:StateType) (o_cert:option Certificate) :StateType:=
    match o_cert with
    | None => curr_state
    | Some cert => state_set_recv_cert curr_state cert
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
        | Some cert => (cert.(c_round) <=? proposal.(p_round)) && is_quorum cert.(c_voters)
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

Definition state_transition_2_msg_A_quit (e:Event) (curr_state:StateType) (msg:MsgType) (qt:QuitType):StateType:=
    match qt with
    | quit_conflict qc => 
        if qc.(qc_round) =? curr_state.(st_round) then 
            state_set_receive_qt curr_state qt e.(ev_time)
        else curr_state
    | quit_blame qb => 
        if qb.(qb_round) =? curr_state.(st_round) then 
            state_set_receive_qt curr_state qt e.(ev_time)
        else curr_state
    end.

Definition state_transition_2_msg_B_blame (e:Event) (curr_state:StateType) (msg:MsgType) (blame:BlameType):StateType:=
    if n_replicas <=? blame.(b_blamer) then curr_state else
    if blame.(b_round) =? curr_state.(st_round) then
    let temp_state := state_set_receive_blame curr_state blame in
    if (1+n_faulty) <=? (length temp_state.(st_received_blames)) then 
        state_set_quit_blame temp_state e.(ev_time)
    else temp_state
    else curr_state.

Definition state_transition_2_msg_C_precommit (e:Event) (curr_state:StateType) (msg:MsgType) (precommit:PrecommitType):StateType:=
    if n_replicas<=? precommit.(pc_voter) then curr_state else
    if (precommit.(pc_round) =? curr_state.(st_round)) then 
    match curr_state.(st_first_valid_proposal) with 
        | None => curr_state 
        | Some valid_proposal =>
        if (valid_proposal.(p_block) =? precommit.(pc_block)) then 
            if (is_element precommit.(pc_voter) curr_state.(st_received_precommit_from)) then curr_state
            else let temp_state:= state_set_receive_precommit curr_state precommit in (* if curr_state has received f+1 precommits already, would have committed. will not enter this function*)
            if (1+n_faulty) <=? (length temp_state.(st_received_precommit_from)) then
                state_set_commit temp_state e.(ev_time)
            else temp_state
        else curr_state (* ignore precommit for other proposals*)
    end
else curr_state (*ignore precommit for other rounds*).

Definition state_transition_2_msg_D_highest_cert (e:Event) (curr_state:StateType) (msg:MsgType) (cert:Certificate) :StateType:=
    if (e.(ev_node) =? (leaderOfRound curr_state.(st_round))) && (negb curr_state.(st_new_view_timeouted)) 
    then state_set_recv_cert curr_state cert else curr_state.

(* #def 2E state *)
Definition state_transition_2_msg_E_vote (e:Event) (curr_state:StateType) (msg:MsgType) (vote:VoteType):StateType:=
    if n_replicas<=? vote.(v_voter) then curr_state else
    if vote.(v_round) =? curr_state.(st_round) then state_set_receive_vote curr_state vote else curr_state.

(* #def 2F state*)
(* update also update cert *)
(* require voter in replicas *)
Definition state_transition_2_msg_F_proposal (e:Event) (curr_state:StateType) (msg:MsgType) (proposal:ProposalType):StateType:=
    if n_replicas <=? proposal.(p_proposer)  then curr_state
    else
    match curr_state.(st_first_received_proposal) with
    | None  =>
        if is_proposal_valid_cert proposal curr_state then
            state_set_recv_opt_cert (state_set_first_valid_proposal curr_state proposal  msg.(msg_sender) e.(ev_node)) proposal.(p_cert)
        else if is_proposal_valid_round_proposer proposal curr_state then
            state_set_recv_opt_cert (state_set_first_received_proposal curr_state proposal) proposal.(p_cert)
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
    end.

(* #def state transition*)
(* already excluded msg_sender not in range issue *)
Definition state_transition_2_trigger_msg (e:Event) (curr_state:StateType) (msg:MsgType):StateType:=
    match msg.(msg_content) with
    | msg_quit qt => 
        state_transition_2_msg_A_quit e curr_state msg qt
    | msg_blame blame => (* check if blame reaches f+1*)
        state_transition_2_msg_B_blame e curr_state msg blame
    | msg_precommit precommit => (*require at least received proposal*)
        state_transition_2_msg_C_precommit e curr_state msg precommit
    | msg_highest_cert cert => 
        state_transition_2_msg_D_highest_cert e curr_state msg cert
    | msg_vote vote => (* vote is used to form certificates  *)
        state_transition_2_msg_E_vote e curr_state msg vote
    | msg_propose proposal =>
        state_transition_2_msg_F_proposal e curr_state msg proposal
    end.

Definition state_transition_3_trigger_timeout (e:Event) (curr_state:StateType) (timeout:TimeoutType) (t_node:Node) (t_round:nat) (t_expire_time:nat):=
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
    end.

Definition state_transition_1_quit_round (e:Event) (curr_state:StateType): StateType:=
    match e.(ev_trigger) with
    | None => curr_state
    | Some(trigger_msg_receive msg) =>
        match msg.(msg_content) with
        | msg_vote vote => 
            state_transition_2_msg_E_vote e curr_state msg vote
        | msg_highest_cert cert =>
            state_transition_2_msg_D_highest_cert e curr_state msg cert
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
    end.

(* #def state transition*)
(* update if msg_sender not in replicas, or voter/proposer not in replicas. Ignore *)
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
            if (n_replicas <=?msg.(msg_sender)) then curr_state
            else state_transition_2_trigger_msg e curr_state msg
        | Some(trigger_timeout timeout t_node t_round t_expire_time) => 
            if (negb (t_node =? curr_state.(st_node))) then curr_state
            else
            state_transition_3_trigger_timeout e curr_state timeout t_node t_round t_expire_time
        end
    end.

Definition state_transition_op (event: option Event) (state:StateType): StateType:=
    match event with
    | None => state
    | Some e => state_transition e state
    end. 


Definition init_state (n:Node): StateType := mkState n 0 false None None (fun r b => []) 0 None None [] None [] None None [] false.



(* #properties state transition | from specific rules to general rules *)

Lemma st_2A_only_change_quit_time:
    forall e:Event, forall prev_state msg qt, 
        let new_state:= (state_transition_2_msg_A_quit e prev_state msg qt) in 
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
        destruct_with_eqn qt.
        destruct_with_eqn (qc_round qc =? st_round prev_state).
        unfold state_set_receive_qt.
        repeat split.
        repeat split.
        destruct_with_eqn (qb_round qb =? st_round prev_state).
        repeat split. repeat split. 

Qed.

Lemma st_2B_only_change_recvblames_and_quit_time:
    forall e:Event, forall prev_state msg blame, 
    let new_state:= (state_transition_2_msg_B_blame e prev_state msg blame) in
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
    destruct_with_eqn (n_replicas <=? b_blamer blame). repeat split.
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
Qed.

Lemma st_2C_only_change_recvprecommits_and_commit:
    forall e:Event, forall prev_state msg precommit, 
    let new_state:= (state_transition_2_msg_C_precommit e prev_state msg precommit) in
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
    destruct_with_eqn (n_replicas<=?pc_voter precommit). repeat split.
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

Lemma st_2D_only_change_dynamic_cert:
    forall e:Event, forall prev_state msg cert,
    let new_state:= (state_transition_2_msg_D_highest_cert e prev_state msg cert) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
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
    unfold state_transition_2_msg_D_highest_cert.
    destruct_with_eqn (ev_node e =? leaderOfRound (st_round prev_state)).
    destruct_with_eqn (st_new_view_timeouted prev_state).
    repeat split. auto.
    unfold state_set_recv_cert. simpl.
    destruct_with_eqn (st_dynamic_highest_cert prev_state).
    destruct_with_eqn (c_round c <? c_round cert).
    unfold state_set_dynamic_highest_cert.
    simpl. repeat split. auto.
    repeat split. auto. 
    unfold state_set_dynamic_highest_cert.
    simpl. all:repeat split. auto.
Qed.

Lemma st_2E_only_change_all_certs_AND_dynamic_certs:
    forall e:Event, forall prev_state msg vote,
    let new_state:= (state_transition_2_msg_E_vote e prev_state msg vote) in
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
    destruct_with_eqn (n_replicas<=?v_voter vote). repeat split.
    destruct_with_eqn (v_round vote =? st_round prev_state).
    unfold state_set_receive_vote.
    simpl. all:repeat split.
Qed.

Lemma st_2F_only_change_proposal_related:
    forall e:Event, forall prev_state msg proposal,
    let new_state:= (state_transition_2_msg_F_proposal e prev_state msg proposal) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_committed) = prev_state.(st_committed) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_received_blames) = prev_state.(st_received_blames) /\
    new_state.(st_received_precommit_from) = prev_state.(st_received_precommit_from) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    (* rewrite -> H. *)
    unfold new_state.
    unfold state_transition_2_msg_F_proposal.
    destruct_with_eqn (n_replicas <=? p_proposer proposal). repeat split.
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
    unfold state_set_first_valid_proposal.
    unfold state_set_recv_opt_cert.
    destruct_with_eqn (p_cert proposal).
    unfold state_set_recv_cert.
    simpl.
    destruct_with_eqn (st_dynamic_highest_cert prev_state).
    destruct_with_eqn (c_round c0 <? c_round c).
    unfold state_set_dynamic_highest_cert.
    all:simpl. 
    repeat split. repeat split. repeat split. repeat split.
    unfold state_set_recv_opt_cert.
    destruct_with_eqn (p_cert proposal).
    unfold state_set_recv_cert.
    destruct_with_eqn (st_dynamic_highest_cert (state_set_first_valid_proposal prev_state proposal (msg_sender msg) (ev_node e))).
    destruct_with_eqn (c_round c0<? c_round c).
    unfold state_set_dynamic_highest_cert. all:simpl. 
    repeat split. repeat split. repeat split. repeat split.
    unfold is_proposal_valid_round_proposer. 
    destruct_with_eqn (p_round proposal =? st_round prev_state).
    simpl.
    destruct_with_eqn (p_proposer proposal =? leaderOfRound (st_round prev_state)).
    unfold state_set_recv_opt_cert.
    destruct_with_eqn (p_cert proposal).
    unfold state_set_recv_cert.
    destruct_with_eqn (st_dynamic_highest_cert (state_set_first_received_proposal prev_state proposal )).
    destruct_with_eqn (c_round c0<? c_round c).
    unfold state_set_dynamic_highest_cert. all:simpl. 
    all:repeat split. 
Qed.

Lemma st_2_trigger_msg_only_change_msg_related:
    forall e:Event, forall prev_state msg,
    let new_state := (state_transition_2_trigger_msg e prev_state msg) in
    new_state.(st_node) = prev_state.(st_node) /\
    new_state.(st_round) = prev_state.(st_round) /\
    new_state.(st_locked_highest_cert) = prev_state.(st_locked_highest_cert) /\
    new_state.(st_round_start_time) = prev_state.(st_round_start_time) /\
    new_state.(st_new_view_timeouted) = prev_state.(st_new_view_timeouted).

    intros.
    unfold new_state.
    unfold state_transition_2_trigger_msg.
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
    all:(try apply st_2D_only_change_dynamic_cert).
Qed.

Lemma st_1_only_keep_node_committed:
    forall e:Event, forall prev_state:StateType, 
    let new_state:= (state_transition_1_quit_round e prev_state) in 
    new_state.(st_node) = prev_state.(st_node) /\ new_state.(st_committed) = prev_state.(st_committed).
    intros.
    unfold new_state.
    unfold state_transition_1_quit_round.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    split. all:trivial.
    repeat split.
    all:(try apply st_2E_only_change_all_certs_AND_dynamic_certs).
    repeat split. repeat split. repeat split. 
    repeat split.
    all:(try apply st_2D_only_change_dynamic_cert).
    destruct_with_eqn timeout.
    repeat split.
    repeat split.
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round.
    simpl.
    all:repeat split.
Qed.

Lemma st_3_only_change_new_view_timeouted:
    forall e:Event, forall prev_state timeout t_node t_round t_expire_time, 
    let new_state:= (state_transition_3_trigger_timeout e prev_state timeout t_node t_round t_expire_time) in
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
    destruct_with_eqn timeout.
    repeat split. auto.
    repeat split. auto.
    repeat split. auto.
    unfold state_set_new_view_timeout.
    simpl.
    repeat split. 
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
    destruct_with_eqn (n_replicas<=?msg_sender msg). auto.
    apply st_2_trigger_msg_only_change_msg_related.
    destruct_with_eqn (negb (node=?st_node prev_state)). auto.
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
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    assert ((state_transition_2_msg_E_vote e prev_state msg vote).(st_round) = prev_state.(st_round)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    all:(try contradiction). 
    assert ((state_transition_2_msg_D_highest_cert e prev_state msg cert).(st_round) = prev_state.(st_round)).
    apply st_2D_only_change_dynamic_cert.
    all:(try contradiction).
    destruct_with_eqn timeout.
    all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    repeat eexists.
    apply Nat.eqb_eq in Heqb1. auto.
    contradiction.
    destruct_with_eqn (ev_trigger e). 
    destruct_with_eqn t.
    destruct_with_eqn (n_replicas<=? msg_sender msg). contradiction.
    assert ((state_transition_2_trigger_msg e prev_state msg).(st_round) = prev_state.(st_round)).
    apply st_2_trigger_msg_only_change_msg_related.
    all:(try contradiction).
    assert ((state_transition_3_trigger_timeout e prev_state timeout node round expire_time).(st_round) = prev_state.(st_round)).
    apply st_3_only_change_new_view_timeouted.
    destruct_with_eqn (negb (node=? st_node prev_state)).
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

(* will add some hypothesis, saying that dishonest nodes cannot trigger something. *)

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
Definition triggers_generation_def (n:Node) (i:nat): list TriggerType :=
    (* first event is define else where *)
    if i =? 0  then []
    else if i =? 1 then triggers_of_first_event n
    else match node_id_to_event n i with
    | None => []
    | Some e =>
        let prev_state := state_after_node_id n (i-1) in
        let new_state := state_after_node_id n i in
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
(* Variable event_of_trigger: TriggerType -> . *)

(* as a hypothesis, that every trigger is generated by some event. *)
(* trigger -> from_event *)
(* Variable generators_of_triggers: TriggerType -> Event.  *)

Variable gen_id_of_event_at_node_id: Node -> nat -> nat. (* If there is no event -> map to 0*)
Hypothesis gen_id_def_id0: 
    forall n:Node, gen_id_of_event_at_node_id n 0 = 0.
Hypothesis gen_id_def_none_to_0:
    forall n:Node, forall i:nat, node_id_to_event n i = None -> gen_id_of_event_at_node_id n i = 0.
Hypothesis gene_id_def_1_to_0:
    forall n:Node, gen_id_of_event_at_node_id n 1 = 0. (* the first event does not have previous generator. *)
Hypothesis gen_id_def_some_to_id:
    forall n:Node, forall i:nat, 
        i>=2 ->
        gen_id_of_event_at_node_id n i < i /\ gen_id_of_event_at_node_id n i >= 1.

(* when i = 0, node_id_event n i = None. 
When i = 1, first_event.ev_trigger = None. *)
Hypothesis gen_id_trigger_map:
    forall n:Node, forall i:nat, forall e:Event, forall trigger:TriggerType, 
        (*i>=2 ->*) node_id_to_event n i = Some e ->
        e.(ev_trigger) = Some trigger -> In trigger (triggers_generation_def n (gen_id_of_event_at_node_id n i)).
    

    

(* ================= PART 5 END ================== *)

(* ################# PART 6 Properties - prepare for proof ################ *)


(* a quorum is a nonrepeat subset of replicas *)

Lemma st_change_only_if_event_nonempty:
    forall n:Node, forall i:nat, 
        ~(state_after_node_id n (S i)) = (state_after_node_id n i) -> node_id_to_event n (S i) <> None.
    intros.
    destruct_with_eqn (node_id_to_event n (S i)).
    discriminate.
    rewrite state_after_node_id_one_level in H.
    rewrite Heqo in H.
    simpl in H.
    contradiction.
Qed.

Lemma st_change_committed_only_if_false_to_true:
    forall n:Node, forall i:nat, 
    let prev_state:=state_after_node_id n i in
    let new_state:= state_after_node_id n (S i) in
    new_state.(st_committed) <> prev_state.(st_committed) ->
    prev_state.(st_committed) = false /\ new_state.(st_committed) = true.
    intros.
    destruct_with_eqn (st_committed prev_state).
    (* new state must be committed*)
    unfold new_state in H.
    rewrite state_after_node_id_one_level in H.
    destruct_with_eqn (node_id_to_event n (S i)).
    unfold state_transition_op in H.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)).
    unfold prev_state in Heqb. 
    contradiction.
    unfold prev_state in Heqb.
    rewrite Heqb in H.
    contradiction.
    simpl in H.
    unfold prev_state in Heqb.
    contradiction.
    split. auto.
    destruct_with_eqn (st_committed new_state).
    auto. contradiction.

Qed.

Lemma st_change_locked_highest_cert_only_if_status_timer:
    forall n:Node, forall i:nat, forall e:Event,
    let prev_state:= state_after_node_id n i in
    let new_state:=state_after_node_id n (S i) in
    new_state.(st_locked_highest_cert) <> prev_state.(st_locked_highest_cert) ->
    node_id_to_event n (S i) = Some e ->
    exists timeout t_node t_round t_expire_time, 
        ev_trigger e = Some (trigger_timeout timeout t_node t_round t_expire_time) /\
        timeout = timeout_quit_status /\
        t_round = prev_state.(st_round) /\
        t_expire_time = e.(ev_time).
    intros.
    unfold new_state in H. 
    rewrite state_after_node_id_one_level in H. rewrite H0 in H. simpl in H.
    replace (state_after_node_id n i) with prev_state in H.

    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    destruct_with_eqn (st_committed prev_state).
    contradiction.
    destruct_with_eqn (st_quit_round_time prev_state).
    unfold state_transition_1_quit_round in H.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    assert ((state_transition_2_msg_E_vote e prev_state msg vote).(st_locked_highest_cert) = prev_state.(st_locked_highest_cert)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    rewrite H1 in H. all:(try contradiction).
    assert ((state_transition_2_msg_D_highest_cert e prev_state msg cert).(st_locked_highest_cert) = prev_state.(st_locked_highest_cert)).
    apply st_2D_only_change_dynamic_cert.
    rewrite H1 in H. all:(try contradiction).
    destruct_with_eqn timeout. all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H.
    simpl in H. all:(try contradiction).
    repeat eexists. apply Nat.eqb_eq. repeat auto.   
    assert (e.(ev_time) = expire_time).
    apply event_triggered_by_timeout_at_expire_time with (n:=n) (i:=(S i)) (e:=e) (timeout:=timeout_quit_status) (t_node:=node) (t_round:=round) (t_expire_time:=expire_time). auto. auto. auto.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    assert ((state_transition_2_trigger_msg e prev_state msg).(st_locked_highest_cert) = prev_state.(st_locked_highest_cert)).
    apply st_2_trigger_msg_only_change_msg_related. 
    destruct_with_eqn (n_replicas<=?msg_sender msg).
    all:(try contradiction).
    destruct_with_eqn (negb (node =? st_node prev_state)).
    unfold state_transition_3_trigger_timeout in H. contradiction.
    unfold state_transition_3_trigger_timeout in H.
    destruct_with_eqn timeout. all:(try contradiction). auto.
    
Qed.


(* use a simple version for all_certs and dynamic certs first | see what is required later. *)
Lemma st_change_all_certs_only_if_recv_vote_or_proposal:
    forall n:Node, forall i:nat, forall e:Event, 
    let prev_state:= state_after_node_id n i in
    let new_state:=state_after_node_id n (S i) in
    new_state.(st_all_certs) <> prev_state.(st_all_certs) -> 
    node_id_to_event n (S i) = Some e ->
    exists msg, 
        ev_trigger e = Some (trigger_msg_receive msg) /\

        ((exists vote, msg.(msg_content) = msg_vote vote) \/
        (exists proposal, msg.(msg_content) = msg_propose proposal)). (* /\
        vote.(v_round) = prev_state.(st_round) /\
        ~ In vote.(v_voter) (prev_state.(st_all_certs) vote.(v_round) vote.(v_block)).*)
    intros.
    unfold new_state in H.
    assert (state_after_node_id n (S i) = state_transition e (state_after_node_id n i)). 
    remember (state_after_node_id n i) as state1.
    rewrite state_after_node_id_one_level.
    rewrite H0.
    simpl.
    rewrite Heqstate1. auto.
    rewrite H1 in H.
    replace (state_after_node_id n i) with prev_state in H.
    2:auto.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    destruct_with_eqn (st_committed prev_state). contradiction.
    destruct_with_eqn (st_quit_round_time prev_state). 
    unfold state_transition_1_quit_round in H. 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    (* unfold state_transition_2_msg_E_vote in H. 
    rewrite Heqo0 in H. rewrite Heqm in H. 
    destruct_with_eqn (v_round vote =? st_round prev_state).
    unfold state_set_receive_vote in H.
    simpl in H. unfold update_all_certs in H. *)
    exists msg. split. auto. left. exists vote. auto.
    all:(try contradiction).
    assert (st_all_certs (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_all_certs)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. contradiction.
    destruct_with_eqn timeout.
    all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H. simpl in H. all:(try contradiction). 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (n_replicas<=?msg_sender msg).
    all:(try contradiction).
    unfold state_transition_2_trigger_msg in H.
    destruct_with_eqn (msg_content msg).
    exists msg. split. auto. right. exists proposal. auto. 
    exists msg. split. auto. left. exists vote. auto. 
    assert (st_all_certs (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_all_certs prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. contradiction.
    assert (st_all_certs (state_transition_2_msg_B_blame e prev_state msg blame) = st_all_certs prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. contradiction.
    assert (st_all_certs (state_transition_2_msg_A_quit e prev_state msg qt) = st_all_certs prev_state).
    apply st_2A_only_change_quit_time. rewrite H2 in H. contradiction.
    assert (st_all_certs (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_all_certs prev_state).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. contradiction.
    destruct_with_eqn (node =? st_node prev_state).
    simpl in H. 
    assert (st_all_certs (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_all_certs prev_state).
    apply st_3_only_change_new_view_timeouted. rewrite H2 in H. contradiction.
    simpl in H. contradiction.
Qed.

Lemma st_change_dynamic_highest_cert_only_if_recv_vote_or_proposal_or_cert:
    forall n:Node, forall i:nat, forall e:Event, 
    let prev_state:= state_after_node_id n i in
    let new_state:=state_after_node_id n (S i) in
    new_state.(st_all_certs) <> prev_state.(st_all_certs) -> 
    node_id_to_event n (S i) = Some e ->
    exists msg, 
        ev_trigger e = Some (trigger_msg_receive msg) /\

        ((exists vote, msg.(msg_content) = msg_vote vote) \/
        (exists proposal, msg.(msg_content) = msg_propose proposal) \/
        (exists cert, msg.(msg_content) = msg_highest_cert cert)).

    intros.
    unfold new_state in H.
    assert (state_after_node_id n (S i) = state_transition e (state_after_node_id n i)). 
    remember (state_after_node_id n i) as state1.
    rewrite state_after_node_id_one_level.
    rewrite H0.
    simpl.
    rewrite Heqstate1. auto.
    rewrite H1 in H.
    replace (state_after_node_id n i) with prev_state in H.
    2:auto.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    contradiction.
    destruct_with_eqn (st_committed prev_state). contradiction.
    destruct_with_eqn (st_quit_round_time prev_state). 
    unfold state_transition_1_quit_round in H. 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    contradiction.
    exists msg. split. auto. left. exists vote. auto.
    all:(try contradiction).
    assert (st_all_certs (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_all_certs)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. contradiction.
    destruct_with_eqn timeout.
    all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H. simpl in H. all:(try contradiction). 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (n_replicas<=?msg_sender msg).
    all:(try contradiction).
    unfold state_transition_2_trigger_msg in H.
    destruct_with_eqn (msg_content msg).
    exists msg. split. auto. right. left. exists proposal. auto. 
    exists msg. split. auto. left. exists vote. auto. 
    assert (st_all_certs (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_all_certs prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. contradiction.
    assert (st_all_certs (state_transition_2_msg_B_blame e prev_state msg blame) = st_all_certs prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. contradiction.
    assert (st_all_certs (state_transition_2_msg_A_quit e prev_state msg qt) = st_all_certs prev_state).
    apply st_2A_only_change_quit_time. rewrite H2 in H. contradiction.
    exists msg. split. auto. right. right. exists cert. auto. 
    destruct_with_eqn (node =? st_node prev_state).
    simpl in H. 
    assert (st_all_certs (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_all_certs prev_state).
    apply st_3_only_change_new_view_timeouted. rewrite H2 in H. contradiction.
    simpl in H. contradiction.

Qed.

(* round start time seems not important *)

Ltac contradiction_4 H:=(destruct H; contradiction; destruct H; contradiction; destruct H; contradiction; contradiction).

Lemma st_change_proposal_related_only_if_recv_proposal_or_vote_or_timeout_status:
    forall n:Node, forall i:nat, forall e:Event, 
    let prev_state:= state_after_node_id n i in
    let new_state:=state_after_node_id n (S i) in
    ((new_state.(st_first_received_proposal) <> prev_state.(st_first_received_proposal)) \/ 
    (new_state.(st_first_valid_proposal) <> prev_state.(st_first_valid_proposal)) \/ 
    (new_state.(st_received_valid_proposal_from) <> prev_state.(st_received_valid_proposal_from)) \/ 
    (new_state.(st_vote) <> prev_state.(st_vote))) -> 
    node_id_to_event n (S i) = Some e ->
    (exists t_node t_round t_expire_time, 
        ev_trigger e = Some (trigger_timeout timeout_quit_status t_node t_round t_expire_time) /\
        t_round = prev_state.(st_round) /\
        t_expire_time = e.(ev_time)) \/
    (exists msg, 
        ev_trigger e = Some (trigger_msg_receive msg) /\
        ((exists vote, msg.(msg_content) = msg_vote vote) \/
        (exists proposal, msg.(msg_content) = msg_propose proposal))).
    intros.
    unfold new_state in H.
    assert (state_after_node_id n (S i) = state_transition e (state_after_node_id n i)). 
    remember (state_after_node_id n i) as state1.
    rewrite state_after_node_id_one_level.
    rewrite H0.
    simpl.
    rewrite Heqstate1. auto.
    rewrite H1 in H.
    replace (state_after_node_id n i) with prev_state in H.
    2:auto.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct_with_eqn (st_committed prev_state). destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct_with_eqn (st_quit_round_time prev_state). 
    unfold state_transition_1_quit_round in H. 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg).
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    right. exists msg. split. auto. left. exists vote. auto.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    assert (st_first_received_proposal (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_first_received_proposal)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_first_valid_proposal)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_received_valid_proposal_from)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_vote)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct_with_eqn timeout.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct_with_eqn (round =? st_round prev_state).
    unfold state_set_enter_new_round in H. simpl in H. 
    left. exists node, round, (e.(ev_time)). split. 
    assert (e.(ev_time) = expire_time).
    apply event_triggered_by_timeout_at_expire_time with (n:=n) (i:=(S i)) (e:=e) (timeout:=timeout_quit_status) (t_node:=node) (t_round:=round) (t_expire_time:=expire_time). auto. auto. rewrite H2.
    auto. split. 
    apply Nat.eqb_eq. auto. auto.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (n_replicas<=?msg_sender msg).
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    unfold state_transition_2_trigger_msg in H.
    destruct_with_eqn (msg_content msg).
    right. exists msg. split. auto. right. exists proposal. auto. 
    right. exists msg. split. auto. left. exists vote. auto. 
    assert (st_first_received_proposal (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_first_received_proposal prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_first_valid_proposal prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_received_valid_proposal_from prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_2_msg_C_precommit e prev_state msg precommit) = st_vote prev_state).
    apply st_2C_only_change_recvprecommits_and_commit. rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    
    assert (st_first_received_proposal (state_transition_2_msg_B_blame e prev_state msg blame) = st_first_received_proposal prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_2_msg_B_blame e prev_state msg blame) = st_first_valid_proposal prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_2_msg_B_blame e prev_state msg blame) = st_received_valid_proposal_from prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_2_msg_B_blame e prev_state msg blame) = st_vote prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.

    assert (st_first_received_proposal (state_transition_2_msg_A_quit e prev_state msg qt) = st_first_received_proposal prev_state).
    apply st_2A_only_change_quit_time. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_2_msg_A_quit e prev_state msg qt) = st_first_valid_proposal prev_state).
    apply st_2A_only_change_quit_time.   rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_2_msg_A_quit e prev_state msg qt) = st_received_valid_proposal_from prev_state).
    apply st_2A_only_change_quit_time.  rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_2_msg_A_quit e prev_state msg qt) = st_vote prev_state).
    apply st_2A_only_change_quit_time.  rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.

    assert (st_first_received_proposal (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_first_received_proposal prev_state).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_first_valid_proposal prev_state).
    apply st_2D_only_change_dynamic_cert.   rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_received_valid_proposal_from prev_state).
    apply st_2D_only_change_dynamic_cert.  rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_vote prev_state).
    apply st_2D_only_change_dynamic_cert.  rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.

    destruct_with_eqn (node =? st_node prev_state).
    simpl in H. 

    assert (st_first_received_proposal (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_first_received_proposal prev_state).
    apply st_3_only_change_new_view_timeouted. rewrite H2 in H. clear H2.
    assert (st_first_valid_proposal (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_first_valid_proposal prev_state).
    apply st_3_only_change_new_view_timeouted.  rewrite H2 in H. clear H2.
    assert (st_received_valid_proposal_from (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_received_valid_proposal_from prev_state).
    apply st_3_only_change_new_view_timeouted.  rewrite H2 in H. clear H2.
    assert (st_vote (state_transition_3_trigger_timeout e prev_state timeout node round expire_time) = st_vote prev_state).
    apply st_3_only_change_new_view_timeouted. rewrite H2 in H. clear H2.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.

    simpl in H. 
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
    destruct H. contradiction. destruct H. contradiction. destruct H. contradiction. contradiction.
Qed.

(* do not do others right now. *)
(* need much more information. If receive precommit, then the voter must be in replicas, not in previous recv_pre_commit_from, but in the new one. *)
Lemma st_change_recv_pc_from_only_if_recv_precommit_or_timeout_status:
    forall n:Node, forall i:nat, forall e:Event, 
    let prev_state:= state_after_node_id n i in
    let new_state:=state_after_node_id n (S i) in
    ((new_state.(st_received_precommit_from) <> prev_state.(st_received_precommit_from))) -> 
    node_id_to_event n (S i) = Some e ->
    ((exists t_node t_round t_expire_time quit_time,
        prev_state.(st_quit_round_time) = Some quit_time /\
        ev_trigger e = Some (trigger_timeout timeout_quit_status t_node t_round t_expire_time) /\
        t_round = prev_state.(st_round) /\
        t_expire_time = e.(ev_time)) \/
    (exists msg, 
        prev_state.(st_quit_round_time) = None /\
        ev_trigger e = Some (trigger_msg_receive msg) /\
        ((exists precommit, msg.(msg_content) = msg_precommit precommit /\ 
        precommit.(pc_voter)<n_replicas /\
        ~In precommit.(pc_voter) prev_state.(st_received_precommit_from) /\
        (* In precommit.(pc_voter) new_state.(st_received_precommit_from) /\  *)
        precommit.(pc_round) = prev_state.(st_round) /\
        (exists valid_proposal, prev_state.(st_first_valid_proposal)=Some valid_proposal /\
            precommit.(pc_block) = valid_proposal.(p_block)) )))).
    intros.
    unfold new_state in H.
    assert (state_after_node_id n (S i) = state_transition e (state_after_node_id n i)). 
    remember (state_after_node_id n i) as state1.
    rewrite state_after_node_id_one_level.
    rewrite H0.
    simpl.
    rewrite Heqstate1. auto.
    rewrite H1 in H.
    replace (state_after_node_id n i) with prev_state in H.
    2:auto.
    unfold state_transition in H.
    destruct_with_eqn (negb (st_node prev_state =? ev_node e)).
     contradiction.
    destruct_with_eqn (st_committed prev_state). contradiction.
    destruct_with_eqn (st_quit_round_time prev_state). 
    unfold state_transition_1_quit_round in H. 
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg). contradiction. 
    assert (st_received_precommit_from (state_transition_2_msg_E_vote e prev_state msg vote) = prev_state.(st_received_precommit_from)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs. rewrite H2 in H. clear H2. 
    all:(try contradiction).
    assert (st_received_precommit_from (state_transition_2_msg_D_highest_cert e prev_state msg cert) = prev_state.(st_received_precommit_from)).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2.
    all:(try contradiction).

    destruct_with_eqn timeout.
    all:(try contradiction).
    destruct_with_eqn (round =? st_round prev_state).
    left. exists node, round, (e.(ev_time)). exists n0. split. auto. split. 

    assert (e.(ev_time) = expire_time).
    apply event_triggered_by_timeout_at_expire_time with (n:=n) (i:=(S i)) (e:=e) (timeout:=timeout_quit_status) (t_node:=node) (t_round:=round) (t_expire_time:=expire_time). auto. auto. rewrite H2.
    auto. split. 
    apply Nat.eqb_eq. auto. auto. contradiction.

    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (n_replicas<=?msg_sender msg).
    contradiction.
    unfold state_transition_2_trigger_msg in H.
    destruct_with_eqn (msg_content msg).
    
    assert (st_received_precommit_from (state_transition_2_msg_F_proposal e prev_state msg proposal) = st_received_precommit_from prev_state).
    apply st_2F_only_change_proposal_related. rewrite H2 in H. clear H2. contradiction.
    assert (st_received_precommit_from (state_transition_2_msg_E_vote e prev_state msg vote) = st_received_precommit_from prev_state).
    apply st_2E_only_change_all_certs_AND_dynamic_certs. rewrite H2 in H. clear H2. contradiction.

    (* the important type: precommit - unfold precommit to get more information*)
    unfold state_transition_2_msg_C_precommit in H.
    destruct_with_eqn (n_replicas <=? pc_voter precommit). congruence.
    destruct_with_eqn (pc_round precommit =? st_round prev_state).
    destruct_with_eqn (st_first_valid_proposal prev_state).
    destruct_with_eqn (p_block p =? pc_block precommit).
    destruct_with_eqn (is_element (pc_voter precommit) (st_received_precommit_from prev_state)). congruence.
    destruct_with_eqn (1+n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit prev_state precommit))).
    unfold state_set_receive_precommit in H.
    rewrite Heqb5 in H.
    unfold state_set_commit in H. simpl in H. 

 
    right. exists msg. split. auto. split. auto. exists precommit. split. auto. split. 
    apply leb_iff_conv. auto.
    split. 
    apply is_element_false_prop. auto.
    split.  apply Nat.eqb_eq. auto.
    exists p. split. auto.
    assert (p_block p = pc_block precommit) by (apply Nat.eqb_eq; auto). auto.

    right. exists msg. split. auto. split. auto. exists precommit. split. auto. split. 
    apply leb_iff_conv. auto.
    split. apply is_element_false_prop. auto.
    split. apply Nat.eqb_eq. auto.
    exists p. split. auto.
    assert (p_block p = pc_block precommit) by (apply Nat.eqb_eq; auto). auto.

    all:(try contradiction).

    assert (st_received_precommit_from (state_transition_2_msg_B_blame e prev_state msg blame) = st_received_precommit_from prev_state).
    apply st_2B_only_change_recvblames_and_quit_time. rewrite H2 in H. clear H2. contradiction.

    assert (st_received_precommit_from (state_transition_2_msg_A_quit e prev_state msg qt) = st_received_precommit_from prev_state).
    apply st_2A_only_change_quit_time. rewrite H2 in H. clear H2. contradiction.

    assert (st_received_precommit_from (state_transition_2_msg_D_highest_cert e prev_state msg cert) = st_received_precommit_from prev_state).
    apply st_2D_only_change_dynamic_cert. rewrite H2 in H. clear H2. contradiction.

    destruct_with_eqn (negb (node =? st_node prev_state)).
    all:(try contradiction).
    unfold state_transition_3_trigger_timeout in H.
    destruct_with_eqn timeout. all:(try contradiction).
Qed.

Lemma st_precommits_always_non_repeat_subset:
    forall n i, 
    let state:=state_after_node_id n i in
    is_nonrepeat_subset_replicas state.(st_received_precommit_from) = true.
    intros.
    unfold state.
    clear state.
    induction i.
    simpl. auto.
    assert (st_received_precommit_from (state_after_node_id n (S i))= st_received_precommit_from (state_after_node_id n i) \/ ~st_received_precommit_from (state_after_node_id n (S i))= st_received_precommit_from (state_after_node_id n i)).
    destruct (list_eq_dec Node Nat.eqb nat_eqb_eq_single nat_eqb_eq_single_reverse (st_received_precommit_from (state_after_node_id n i)) (st_received_precommit_from (state_after_node_id n (S i)))). left. auto. right. auto.
    destruct H.
    rewrite H. auto.
    destruct_with_eqn (node_id_to_event n (S i)).
    (* remember (state_after_node_id n i) as prev_state. *)
    assert ((exists t_node t_round t_expire_time quit_time,
        (state_after_node_id n i).(st_quit_round_time) = Some quit_time /\ 
        ev_trigger e = Some (trigger_timeout timeout_quit_status t_node t_round t_expire_time) /\
        t_round = (state_after_node_id n i).(st_round) /\
        t_expire_time = e.(ev_time)) \/
    (exists msg, 
        (state_after_node_id n i).(st_quit_round_time) = None /\
        ev_trigger e = Some (trigger_msg_receive msg) /\
        ((exists precommit, msg.(msg_content) = msg_precommit precommit /\ 
        precommit.(pc_voter)<n_replicas /\
        ~In precommit.(pc_voter) (state_after_node_id n i).(st_received_precommit_from) /\
        (* In precommit.(pc_voter) new_state.(st_received_precommit_from) /\  *)
        precommit.(pc_round) = (state_after_node_id n i).(st_round) /\
        (exists valid_proposal, (state_after_node_id n i).(st_first_valid_proposal)=Some valid_proposal /\
            precommit.(pc_block) = valid_proposal.(p_block)) )))).
    apply st_change_recv_pc_from_only_if_recv_precommit_or_timeout_status with (n:=n) (i:=i) (e:=e). auto. auto. 
    2:{
        remember (state_after_node_id n i) as prev_state.
        rewrite state_after_node_id_one_level in H.
        rewrite Heqo in H. simpl in H. rewrite Heqprev_state in H. auto.
    }
    (* the event filters seem to not help? *)
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    destruct H2.
    rewrite state_after_node_id_one_level.
    rewrite Heqo.
    simpl.
    unfold state_transition.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)). auto.
    destruct_with_eqn (st_committed (state_after_node_id n i)). auto.
    rewrite H0.
    unfold state_transition_1_quit_round.
    rewrite H1.
    rewrite H2.
    rewrite Nat.eqb_refl with (x:=(st_round (state_after_node_id n i))).
    simpl. auto.
    destruct H0.
    destruct H0.
    destruct H1.
    destruct H2. destruct H2.
    destruct H3.
    destruct H4.
    destruct H5.
    destruct H6. destruct H6.
    rewrite state_after_node_id_one_level.
    rewrite Heqo.
    simpl.
    unfold state_transition.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)). auto.
    destruct_with_eqn (st_committed (state_after_node_id n i)). auto.
    rewrite H0. 
    unfold state_transition_1_quit_round.
    rewrite H1.
    destruct_with_eqn (n_replicas <=? msg_sender x).
    auto.
    unfold state_transition_2_trigger_msg.
    rewrite H2.
    unfold state_transition_2_msg_C_precommit.
    assert (n_replicas <=? pc_voter x0 = false).
    apply leb_iff_conv.
    destruct_with_eqn (n_replicas <=? pc_voter x0).
    auto.
    destruct_with_eqn (pc_round x0 =? st_round (state_after_node_id n i)).
    destruct_with_eqn (st_first_valid_proposal (state_after_node_id n i)).
    destruct_with_eqn (p_block p =? pc_block x0).
    destruct_with_eqn (1+n_faulty<=?length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0))).
    unfold state_set_receive_precommit.
    simpl.
    destruct_with_eqn (is_element (pc_voter x0) (st_received_precommit_from (state_after_node_id n i))).
    auto.
    simpl. 
    unfold is_nonrepeat_subset_replicas.
    simpl. auto. auto. auto. auto. auto.
    destruct_with_eqn (is_element (pc_voter x0) replicas).
    unfold is_nonrepeat_subset_replicas in IHi.
    auto.
    rewrite H7.
    rewrite H5.
    rewrite Nat.eqb_refl.
    rewrite H6.
    rewrite H8.
    rewrite Nat.eqb_refl.
    assert (is_element (pc_voter x0) (st_received_precommit_from (state_after_node_id n i))=false). rewrite-> is_element_false_prop with (b:=pc_voter x0) (A:=(st_received_precommit_from (state_after_node_id n i))). auto. 
    rewrite H9.
    destruct_with_eqn (1+n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0))).
    unfold state_set_receive_precommit.
    rewrite H9.
    simpl.
    
    unfold is_nonrepeat_subset_replicas.
    unfold is_nonrepeat.
    rewrite H9.
    fold is_nonrepeat.
    unfold is_subset_replicas.
    rewrite Heqb2.
    fold is_subset_replicas.
    auto.
    
    unfold state_set_receive_precommit. rewrite H9. simpl. 
    
    unfold is_nonrepeat_subset_replicas.
    unfold is_nonrepeat.
    rewrite H9.
    fold is_nonrepeat.
    unfold is_subset_replicas.
    rewrite Heqb2.
    fold is_subset_replicas.
    auto.

    assert (is_element (pc_voter x0) replicas = true).
    apply is_element_true_prop. apply in_replicas_cond. auto. congruence. 
Qed.

Lemma st_commit_false_implies_not_enough_precommits:
    forall n:Node, forall i:nat, 
        let state:=state_after_node_id n i in
        state.(st_committed) = false ->
        is_quorum (state.(st_received_precommit_from)) = false /\ length (state.(st_received_precommit_from)) <= n_faulty.
    intros.
    dependent induction i.
    simpl. split. auto. lia.
    assert (state_after_node_id n (S i) = state_transition_op (node_id_to_event n (S i)) (state_after_node_id n i)).
    rewrite state_after_node_id_one_level. auto. 

    unfold state in H.
    destruct_with_eqn ((state_after_node_id n i).(st_committed)).
    destruct_with_eqn (node_id_to_event n (S i)).
    unfold state_transition_op in H0.
    unfold state_transition in H0.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)).
    rewrite H0 in H.
    congruence.
    rewrite Heqb in H0. rewrite H0 in H. congruence.
    unfold state_transition_op in H0. rewrite H0 in H. congruence.
    (* hard part. after the transition, the state remains un-committed. therefore, cannot reach the condition of set. *)
    (* can use the above lemma, change recv_precommit_from only if ..*)

    assert (false=false). auto.
    apply IHi in H1. clear IHi.
    destruct H1 as [IH1 IH2].
    
    assert (is_quorum (st_received_precommit_from (state_after_node_id n i)) = false).
    apply IH1.
    unfold state.
    assert (st_received_precommit_from (state_after_node_id n (S i)) = st_received_precommit_from (state_after_node_id n i) \/ ~st_received_precommit_from (state_after_node_id n (S i)) = st_received_precommit_from (state_after_node_id n i)).
    destruct (list_eq_dec Node Nat.eqb nat_eqb_eq_single nat_eqb_eq_single_reverse (st_received_precommit_from (state_after_node_id n i)) (st_received_precommit_from (state_after_node_id n (S i)))). left. auto. right. auto.
    destruct H2.
    rewrite H2. auto.
    destruct_with_eqn (node_id_to_event n (S i)).
    2:{remember (state_after_node_id n i) as prev_state. rewrite state_after_node_id_one_level in H2. rewrite Heqo in H2. simpl in H2. rewrite Heqprev_state in H2. congruence. }
    apply st_change_recv_pc_from_only_if_recv_precommit_or_timeout_status with (n:=n) (i:=i) (e:=e) in H2. 2:auto. 
    destruct H2.

    (* case 1: quitstatus. new list might be []*)
    destruct H2.
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4.
    rewrite state_after_node_id_one_level. rewrite Heqo. simpl.
    unfold state_transition.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)). auto.
    rewrite Heqb. rewrite H2. unfold state_transition_1_quit_round. rewrite H3. rewrite H4. rewrite Nat.eqb_refl. simpl. split. auto. lia.
    (* case 2: precommit. *)
    destruct H2. destruct H2. destruct H3. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. destruct H8. destruct H8.
    rewrite state_after_node_id_one_level. rewrite Heqo. simpl.
    unfold state_transition.
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)). split. auto. auto.
    rewrite Heqb. rewrite H2.  rewrite H3. 
    destruct_with_eqn (n_replicas <=? msg_sender x). split. auto. auto. 
    unfold state_transition_2_trigger_msg.
    destruct_with_eqn (n_replicas <=? pc_voter x0). rewrite H4. 
    
    unfold state_transition_2_msg_C_precommit. rewrite Heqb2. split. auto. auto.
    rewrite H4. 
    
    unfold state_transition_2_msg_C_precommit. rewrite Heqb2. rewrite H7. rewrite Nat.eqb_refl. rewrite H8. rewrite H9. rewrite Nat.eqb_refl.
    destruct_with_eqn (is_element (pc_voter x0) (st_received_precommit_from (state_after_node_id n i))). split. auto. auto.
    destruct_with_eqn (1 + n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0))). (* remember, if is_quorum = true, then can infer that set commit true *)

    assert (st_committed state = true). 
    unfold state. rewrite H0. simpl.
    unfold state_transition.
    rewrite Heqb0. rewrite Heqb. rewrite H2. rewrite H3. rewrite Heqb1. unfold state_transition_2_trigger_msg. rewrite H4. unfold state_transition_2_msg_C_precommit. rewrite H7. rewrite Heqb2. rewrite Nat.eqb_refl. rewrite H8. rewrite H9. rewrite Nat.eqb_refl. rewrite Heqb3. rewrite Heqb4. 
    (* directly open state_set_commit *)
    unfold state_set_commit. simpl. auto. unfold state in H10.

    congruence.

    unfold is_quorum.
    rewrite Heqb4.
    assert (is_nonrepeat_subset_replicas (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0)) = true).
    unfold state_set_receive_precommit.
    rewrite Heqb3.
    simpl.

    unfold is_nonrepeat_subset_replicas.
    unfold is_nonrepeat. rewrite Heqb3. fold is_nonrepeat.
    unfold is_subset_replicas. assert (is_element (pc_voter x0) replicas=true). apply is_replicas_element_cond. auto. rewrite H10. fold is_subset_replicas. 
    apply st_precommits_always_non_repeat_subset. rewrite H10. simpl. split. auto. 
    assert (length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0)) < 1+ n_faulty).
     apply leb_iff_conv with (n:=1+n_faulty) (m:= length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) x0))). auto. lia.
Qed.

(* delayed because must prove that commit-false implies <=f precommits*)
Lemma st_change_committed_only_if_recv_precommit:
    forall n:Node, forall i:nat,
    let prev_state:=state_after_node_id n i in 
    let new_state:=state_after_node_id n (S i) in
    new_state.(st_committed) <> prev_state.(st_committed) ->
    (length (prev_state.(st_received_precommit_from)) = n_faulty) /\
        (length (new_state.(st_received_precommit_from)) = 1+n_faulty) /\
        (exists valid_proposal, prev_state.(st_first_valid_proposal) = Some valid_proposal) /\
    (exists e msg precommit,
        node_id_to_event n (S i) = Some e /\
        prev_state.(st_quit_round_time) = None /\ 
        ev_trigger e = Some (trigger_msg_receive msg) /\
        msg.(msg_content) = msg_precommit precommit /\
        ~ In precommit.(pc_voter) prev_state.(st_received_precommit_from) /\
        precommit.(pc_round) = prev_state.(st_round)).
    intros.
    assert (prev_state.(st_committed) = false /\ new_state.(st_committed) = true).

    apply st_change_committed_only_if_false_to_true.
    unfold new_state in H. auto.
    destruct H0.
    clear H.
    unfold new_state in H1.
    unfold prev_state in H0.
    unfold state_transition in H1.
    rewrite state_after_node_id_one_level in H1. 
    destruct_with_eqn (node_id_to_event n (S i)).
    2: {simpl in H1.  congruence. }
    simpl in H1. unfold state_transition in H1. 
    destruct_with_eqn (negb (st_node (state_after_node_id n i) =? ev_node e)).
    congruence.
    rewrite -> H0 in H1.
    destruct_with_eqn (st_quit_round_time (state_after_node_id n i)).
    unfold state_transition_1_quit_round in H1.
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    destruct_with_eqn (msg_content msg). congruence.

    assert ((state_transition_2_msg_E_vote e (state_after_node_id n i) msg vote).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    all: (try (congruence)).
    assert ((state_transition_2_msg_D_highest_cert e (state_after_node_id n i) msg cert).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2D_only_change_dynamic_cert.
    all: (try (congruence)).
    destruct_with_eqn timeout.
    all: (try (congruence)).
    destruct_with_eqn (round =? st_round (state_after_node_id n i)).
    unfold state_set_enter_new_round in H1.
    simpl in H1. all: (try (congruence)).
    destruct_with_eqn (ev_trigger e).
    destruct_with_eqn t.
    
    unfold state_transition_2_trigger_msg in H1.
    destruct_with_eqn (n_replicas<=?msg_sender msg). congruence.

    destruct_with_eqn (msg_content msg).
    assert ((state_transition_2_msg_F_proposal e (state_after_node_id n i) msg proposal).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2F_only_change_proposal_related.
    all: (try (congruence)).
    assert ((state_transition_2_msg_E_vote e (state_after_node_id n i) msg vote).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2E_only_change_all_certs_AND_dynamic_certs.
    all: (try (congruence)).
    4:{assert ((state_transition_2_msg_D_highest_cert e (state_after_node_id n i) msg cert).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2D_only_change_dynamic_cert.
    all: (try (congruence)). }
    2:{assert ((state_transition_2_msg_B_blame e (state_after_node_id n i) msg blame).(st_committed) = (state_after_node_id n i).(st_committed)). 
    apply st_2B_only_change_recvblames_and_quit_time.
    all: (try (congruence)). 
    }
    2:{assert ((state_transition_2_msg_A_quit e (state_after_node_id n i) msg qt).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_2A_only_change_quit_time.
    all: (try (congruence)). }
    2:{ destruct_with_eqn (negb (node =? st_node (state_after_node_id n i))). congruence.
        assert ((state_transition_3_trigger_timeout e (state_after_node_id n i) timeout node round expire_time).(st_committed) = (state_after_node_id n i).(st_committed)).
    apply st_3_only_change_new_view_timeouted. rewrite H1 in H.
    all: (try (congruence)). }
    unfold state_transition_2_msg_C_precommit in H1.
    destruct_with_eqn (n_replicas <=? pc_voter precommit). congruence.
    destruct_with_eqn (pc_round precommit =? st_round (state_after_node_id n i)). 2:congruence.
    destruct_with_eqn (st_first_valid_proposal (state_after_node_id n i)). 2:congruence.
    destruct_with_eqn (p_block p =? pc_block precommit). 2:congruence.
    destruct_with_eqn (is_element (pc_voter precommit) (st_received_precommit_from (state_after_node_id n i))). congruence.
    destruct_with_eqn (1 + n_faulty <=? length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) precommit))). 2:{ unfold state_set_receive_precommit in H1. rewrite Heqb4 in H1. simpl in H1. congruence. }
    unfold state_set_receive_precommit in H1.
    rewrite Heqb4 in H1.
    simpl in H1. 
    
    
    assert (length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) precommit)) <= 1+ length (st_received_precommit_from (state_after_node_id n i))).
    unfold state_set_receive_precommit. rewrite Heqb4. simpl. auto.

    assert (length (st_received_precommit_from (state_after_node_id n i)) <= n_faulty).
    apply st_commit_false_implies_not_enough_precommits. auto. 
    assert (is_quorum (st_received_precommit_from (state_after_node_id n i)) = false).
    apply st_commit_false_implies_not_enough_precommits. auto.
    assert (1+n_faulty <= length (st_received_precommit_from (state_set_receive_precommit (state_after_node_id n i) precommit))).
    apply Nat.leb_le. auto.
    
    
    assert (1+n_faulty <= 1+length (st_received_precommit_from (state_after_node_id n i))).
    lia. unfold prev_state.
    assert (length (st_received_precommit_from (state_after_node_id n i))=n_faulty).
    lia. 
    split. lia.
    split. unfold new_state. 
    
    (* in order to prove something about state_after_node_id n (S i) expand it*)
    rewrite state_after_node_id_one_level. rewrite Heqo. unfold state_transition_op. unfold state_transition. 
    rewrite Heqb. rewrite H0. rewrite Heqo0. rewrite Heqo1. rewrite Heqb0. unfold state_transition_2_trigger_msg. 
    rewrite Heqm. unfold state_transition_2_msg_C_precommit. rewrite Heqb1. rewrite Heqb2. rewrite Heqo2. rewrite Heqb3. rewrite Heqb4. rewrite Heqb5. unfold state_set_receive_precommit. rewrite Heqb4. simpl. lia.

    split. exists p. auto. 
    exists e, msg, precommit. split. auto. split. auto. split. auto. split. auto. split. apply is_element_false_prop. auto.  apply Nat.eqb_eq. auto. 
    
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
            destruct_with_eqn (negb (st_node (state_after_node_id n (gap+i)) =? ev_node e)). auto.
            rewrite IHgap. auto.
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

Lemma once_committed_state_not_change_node_id:
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


(* this lemma relies on (not_committed -> not enough precommits)*)
Lemma turn_committed_implies_enough_precommits_and_a_valid_proposal:
    forall n:Node, forall i:nat,
        st_committed (state_after_node_id n i) = false ->
        st_committed (state_after_node_id n (S i)) = true ->
        is_quorum (state_after_node_id n (S i)).(st_received_precommit_from) = true /\ 
        (exists valid_proposal, st_first_valid_proposal  (state_after_node_id n i) = Some valid_proposal).

    intros.
    assert (is_quorum (state_after_node_id n i).(st_received_precommit_from) = false).
    apply st_commit_false_implies_not_enough_precommits. auto.
    assert (length (state_after_node_id n (S i)).(st_received_precommit_from) = 1+n_faulty).
    apply st_change_committed_only_if_recv_precommit with (n:=n)(i:=i). 
    rewrite H. rewrite H0. congruence.

    unfold is_quorum.
    assert (is_nonrepeat_subset_replicas (state_after_node_id n (S i)).(st_received_precommit_from) = true).
    apply st_precommits_always_non_repeat_subset.
    rewrite H3. rewrite H2. assert ((1+n_faulty<=?1+n_faulty) = true). apply Nat.leb_le. auto. rewrite H4. 
    
    assert (exists valid_proposal, st_first_valid_proposal  (state_after_node_id n (i)) = Some valid_proposal).
    apply st_change_committed_only_if_recv_precommit with (n:=n) (i:=i). rewrite H. rewrite H0. congruence.
    destruct H5. split. auto. exists x. auto.
Qed.

Lemma is_committed_then_enough_precommits_and_a_valid_proposal:
    forall n: Node, forall i: nat, 
        st_committed (state_after_node_id n i) = true ->
        is_quorum (state_after_node_id n i).(st_received_precommit_from) = true /\ 
        (exists valid_proposal, st_first_valid_proposal  (state_after_node_id n i) = Some valid_proposal).

    intros.
    induction i.
    simpl in H. congruence.

    destruct_with_eqn (st_committed (state_after_node_id n i)).
    assert (true=true). auto. apply  IHi in H0. destruct H0. destruct H1. 
    assert (state_after_node_id n (S i) = state_after_node_id n i).
    apply once_committed_state_not_change_node_id with (n:=n) (i:=i) (gap:=1). auto.  rewrite H2. split. auto. exists x. auto.

    split.
    apply turn_committed_implies_enough_precommits_and_a_valid_proposal with (n:=n) (i:=i). auto. auto. 
    
    assert (exists valid_p, st_first_valid_proposal  (state_after_node_id n i) = Some valid_p).
    apply turn_committed_implies_enough_precommits_and_a_valid_proposal with (n:=n) (i:=i). auto. auto.
    destruct H0.
    (*must prove that in this step, the valid proposal field is not changed*)

    destruct_with_eqn (st_first_valid_proposal (state_after_node_id n (S i))).
    exists p. auto.
    assert (st_first_valid_proposal (state_after_node_id n (S i)) <> st_first_valid_proposal (state_after_node_id n i)).
    rewrite H0. rewrite Heqo. congruence.

    destruct_with_eqn (node_id_to_event n (S i)).

    assert ( (exists e msg precommit,
        node_id_to_event n (S i) = Some e /\
        (state_after_node_id n i).(st_quit_round_time) = None /\ 
        ev_trigger e = Some (trigger_msg_receive msg) /\
        msg.(msg_content) = msg_precommit precommit /\
        ~ In precommit.(pc_voter) (state_after_node_id n i).(st_received_precommit_from) /\
        precommit.(pc_round) = (state_after_node_id n i).(st_round))).
    apply st_change_committed_only_if_recv_precommit with (n:=n) (i:=i). auto. auto. rewrite H. rewrite Heqb. congruence.
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5. clear H6.

    assert ((exists t_node t_round t_expire_time, 
        ev_trigger e = Some (trigger_timeout timeout_quit_status t_node t_round t_expire_time) /\
        t_round = (state_after_node_id n i).(st_round) /\
        t_expire_time = e.(ev_time)) \/
    (exists msg, 
        ev_trigger e = Some (trigger_msg_receive msg) /\
        ((exists vote, msg.(msg_content) = msg_vote vote) \/
        (exists proposal, msg.(msg_content) = msg_propose proposal)))).

    apply st_change_proposal_related_only_if_recv_proposal_or_vote_or_timeout_status with (n:=n) (i:=i). auto. auto.
    destruct H6. destruct H6. destruct H6. destruct H6. destruct H6.
    rewrite H2 in Heqo0. inversion Heqo0. 
    rewrite  H9 in H4. congruence.
    
    destruct H6. destruct H6. destruct H7. destruct H7. 
    rewrite H2 in Heqo0. inversion Heqo0. rewrite H9 in H4. rewrite H6 in H4. inversion H4. rewrite H10 in H7. congruence. 
    
    destruct H7.  rewrite H2 in Heqo0. inversion Heqo0. rewrite H9 in H4. rewrite H6 in H4. inversion H4. rewrite H10 in H7. congruence.

    rewrite state_after_node_id_one_level in H1. 
    rewrite Heqo0 in H1. simpl in H1. congruence.
Qed.

(* update cert: 1 - receive vote. this changes all_certs, and further dynamic cert. 
2 - receive highest cert, only applies to leader, at the beginning of new round. *)

(* at the current round, only vote is affecting all_certs *)
(* if anyone commit, it means receiving f+1 precommit. At least 1 precommits from honest. *)
Theorem lemma_61_part1:
    forall n:Node, forall i:nat, 
    let prev_state:= state_before_node_id n i in 
    let new_state:= state_after_node_id n i in 
    prev_state.(st_committed) = false ->
    new_state.(st_committed) = true ->
    (exists valid_proposal, new_state.(st_first_valid_proposal) = Some valid_proposal /\
    (let round:= (new_state).(st_round) in
    (forall n2: Node, forall i2: nat, forall block:BlockType,
        let state2:= state_after_node_id n2 i2 in 
        n2 < n_replicas -> 
        state2.(st_round) = round -> 
        is_quorum (state2.(st_all_certs) round block) = true -> block = valid_proposal.(p_block)
        ))).

    intros.

    (*existence of valid_proposal by *)
    assert (is_quorum (state_after_node_id n i).(st_received_precommit_from) = true /\ 
        (exists valid_proposal, st_first_valid_proposal  (state_after_node_id n i) = Some valid_proposal)).
    apply is_committed_then_enough_precommits_and_a_valid_proposal with (n:=n) (i:=i). auto.

    destruct H1. destruct H2. 
    exists x. split. auto.  (* if there is ever a cert in round -> receive the cert in *)

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

