(* Require Import Nat. *)
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
(* Require Import Coq.Init.Peano. 
Require Coq.Init.Nat. *)
Require Import Lia.
Import ListNotations.

(* Replicas: [1,2,..., n] starting from 1 *)
(* Round: starting from 1! *)

Section sync_hotstuff_sluggish_1block.

Variable delta : nat. 

Definition blockType := nat. (* 0 is a special empty block*)
Definition person := nat. 

Inductive certType : Type :=
    | empty
    | certificates (block:blockType) (round: nat).

Inductive msgContentType : Type :=
    | propose (Bk: blockType) (round: nat) (cert: certType) (proposer: person)
    | vote (Bk: blockType) (round:nat) (voter:person)
    | precommit (Bk: blockType) (round: nat) (voter:person)
    | blame (round: nat) (blamer:person).

Inductive precommitOrEmptyType : Type :=
    | precommitEmpty
    | precommitConstructor (Bk: blockType).

Inductive blockOrEmptyType : Type :=
    | blockEmpty
    | blockConstructor (Bk: blockType).

Definition msgType := (person * person * msgContentType * nat) % type.

Definition is_element (a : nat) (b : list nat) : bool :=
  existsb (fun x => Nat.eqb x a) b.

Variable isHonest : person -> bool.

Variable n_maj : nat. 

Variable n_replicas : nat.

Hypothesis n_2f_1:
    n_replicas = 2 * n_maj + 1.


Hypothesis non_empty_replicas:
    n_replicas > 0.

Fixpoint range (n:nat) : list nat :=
    match n with
    | 0 => []
    | S n' => range n' ++ [n]
    end.
   
Definition replicas := range n_replicas.

Lemma rev_dist:
    forall l1 l2: list nat, rev (l1 ++ l2) = rev l2 ++ rev l1.
    intros.
    induction l1.
    simpl. rewrite app_nil_r. reflexivity.
    simpl. rewrite IHl1. rewrite app_assoc. reflexivity.

Qed.

Lemma rev_rev:
    forall l: list nat, rev (rev l) = l.
    intros. 
    induction l.
    simpl. reflexivity. 
    simpl. rewrite rev_dist. rewrite IHl. simpl. reflexivity.
    
Qed.

Lemma length_range:
    forall n:nat, length (range n) = n.
    intros. 
    induction n.
    simpl. reflexivity.
    simpl. rewrite length_app. rewrite IHn. simpl. ring.
Qed.

Lemma nmn0:
    forall n:nat, n - n = 0.
    intros.
    induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma zmSn:
    forall n:nat, 0 < S n.
    intros.
    apply le_n_S. apply le_0_n.
    Qed.

(* for the replicas list *)
Theorem replica_i_is_i:
    forall i:nat, i < n_replicas -> nth i replicas 0 = 1+i.
    intros.
    unfold replicas.
    clear n_2f_1.
    induction n_replicas.
    inversion H.
    assert (i<n \/ i=n).
    apply Nat.lt_eq_cases.
    unfold lt in H.
    apply le_S_n.
    trivial.
    destruct H0.
    assert (length (range n) = n).
    rewrite length_range. trivial.
    replace (range (S n)) with (range n ++ [S n]).  
    rewrite app_nth1 with (l:=range n) (l':=[S n]).
    assert (n>0).
    destruct n.
    inversion H0.
    apply zmSn.
    apply IHn.
    assumption.
    assumption.
    rewrite H1.
    assumption.
    trivial.
    induction n.
    rewrite H0.
    simpl.
    trivial.
    replace (range (S (S n))) with (range (S n) ++ [S (S n)]).
    rewrite app_nth2 with (l:=range (S n)) (l':=[S (S n)]).
    rewrite length_range. 
    rewrite H0.
    replace (S n - S n) with 0.
    simpl. trivial.
    rewrite nmn0. trivial.
    rewrite length_range. 
    unfold ge. 
    rewrite H0.
    apply le_n. 
    simpl. trivial.
Qed. 
(* leader of round i is replica i%n. Where n is length replicas. And f+1 of them are honest *)

Hypothesis honestMajority: 
    length (filter isHonest replicas) * 2 > n_replicas.

Lemma le_trans:
    forall x1 x2 x3:nat, x1 <= x2 -> x2 <= x3 -> x1 <= x3.
    intros.
    induction H as [ | x2 IH].
    assumption.
    assert (S x2<= S x3).
    apply le_S.
    assumption.
    assert (x2<=x3).
    apply le_S_n.  
    trivial.
    apply IHIH.
    trivial.
Qed.

Lemma ele_subset_in_set_simp: (* directly use filter_In in the stdlib *)
    forall (A:Type) (l: list A) (cond: A->bool),
        forall x:A, In x (filter cond l) -> In x l.
        induction l. 
        simpl.
        intros.
        destruct H.
        intros.
        case_eq(cond a).
        intros.
        replace (filter cond (a::l)) with (a::(filter cond l)) in H.
        induction H.
        simpl. left. trivial.
        simpl. right. apply (IHl cond x). assumption.
        simpl. rewrite H0. reflexivity.
        intros.
        replace (filter cond (a::l)) with (filter cond l) in H.
        right. apply (IHl cond x). simpl. assumption.
        simpl. rewrite H0. reflexivity.
Qed.

Lemma le_n_S_n:
    forall x:nat, forall y:nat, x<=y -> x <= S y.
    intros.
    assert (y <= S y).
    apply le_S.
    trivial.
    apply le_trans with (x1:=x) (x2:=y) (x3:=S y).
    trivial.
    trivial.
Qed. 

Lemma all_replicas_lt_n:
    forall i:nat, (In i replicas) -> 1<=i /\ i<=n_replicas.
    intros.
    clear honestMajority.
    clear non_empty_replicas.
    clear delta.
    clear n_2f_1.
    unfold replicas in H.
    induction n_replicas.
    simpl in H. destruct H.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    assert (1<=i<=n).
    apply IHn.
    assumption.
    split.
    destruct H0.
    assumption.
    destruct H0.
    apply le_n_S_n with (y:=n). assumption.
    simpl in H.
    destruct H.
    rewrite H.
    split.
    replace i with  (S n).
    apply zmSn.
    apply le_n.
    destruct H. 



Qed.

Theorem existHonest:
    exists i:nat, In i replicas /\ isHonest i = true.
    remember (length (filter isHonest replicas)) as len.
    unfold gt in non_empty_replicas, honestMajority.
    unfold lt in honestMajority, non_empty_replicas.
    assert (2<=len*2). 
    assert (2<=S n_replicas).
    apply le_n_S.
    trivial.
    pose proof (le_trans 2 (S n_replicas) (len*2)) as trans.
    apply trans.
    trivial.
    trivial.
    assert (1<=len).
    destruct len.
    simpl in H.
    inversion H.
    apply zmSn.
    remember (filter isHonest replicas) as honests.
    assert (len = length honests).
    rewrite Heqlen.
    trivial.
    remember (nth 0 honests 0) as fist.
    exists fist. 
    split.
    assert (In fist honests).
    rewrite Heqfist.
    assert (0 < length honests).
    unfold lt.
    replace (length honests) with len.
    assumption.

    pose proof (nth_In honests 0 H2) as nthIn.
    trivial.
    apply (filter_In isHonest fist replicas).
    rewrite Heqhonests in H2. 
    assumption.
    apply (filter_In isHonest fist replicas).
    rewrite Heqfist.
    replace (filter isHonest replicas) with honests.
    apply nth_In.
    replace (length honests) with len.
    assumption.
Qed.

Definition leaderOfRound (round:nat) : person :=
    nth (((round-1) mod n_replicas)) replicas 0.

Lemma le_Sn_le:
    forall n m, S n <= m -> n <= m.
    intros.
    assert (n<= S n ).
    apply le_S.
    trivial.
    apply le_trans with (x1:= n) (x2:=S n).
    trivial.
    trivial.

Qed.

Lemma divmod_small_range:
    forall x:nat, forall y:nat, forall r:nat,
        x<=y -> x+r<=y ->
        Nat.divmod x y 0 (x+r) = (0, r).
    intros.
    induction x.
    simpl.
    trivial.
    simpl.
    apply IHx.
    apply le_Sn_le with (n:=x) (m:=y).
    trivial.
    apply le_Sn_le with (n:=x+r) (m:=y).
    trivial.
Qed.



Lemma mod_smaller_range:
    forall i:nat, forall n:nat, 
        1<=n /\ i<= n-1
            -> i mod n = i.
    intros.
    destruct H.
    unfold "mod".
    induction n.
    inversion H.
    replace (Nat.divmod i n 0 n) with (0, n-i).
    simpl.
    lia.
    replace (Nat.divmod i n 0 n) with (Nat.divmod i n 0 (i+(n-i))).
    rewrite divmod_small_range with (x:=i) (y:=n) (r:=n-i).
    trivial.
    nia.
    nia.
    replace (i+(n-i)) with n.
    trivial.
    nia.
Qed.

(*actually we will prove that the protocol finishes within the first N rounds. *)

Theorem leaderOfFirstNRounds:
    forall r:nat, 1<=r -> r <= n_replicas -> leaderOfRound r = r.
    intros.
    unfold leaderOfRound.
    replace ((r-1) mod n_replicas) with (r-1).
    rewrite replica_i_is_i.
    lia.
    lia.
    rewrite mod_smaller_range with (n:=n_replicas).
    trivial.
    lia.
Qed.

(* note that round starts from 1, replicas 1~n*)

Definition isLeader (round:nat) (replica:person) : bool :=
    Nat.eqb (leaderOfRound round) replica.

(*every one maintains a list of certified blocks (have f+1 ack)*)
(* for each round*)
Variable certifiedBlocks : person -> nat -> list blockType.

Variable committedBlock : person -> nat -> blockOrEmptyType.

Variable is_committedTime: person  -> nat -> bool.

(* committed block is the last certified block. *)
Variable roundOfCommit : person -> nat.

(* committed block is the last certified block. *)

Variable viewOfHighestCertifiedBlock : person -> nat -> nat. (* Let round starts with 1. If there is no previous certified block. return 0. *)

Hypothesis highestCertifiedBlock_def:
    forall p: person, forall r1: nat,
    ( forall r2:nat,
    1<=r1 -> 1<=r2 ->
    r1 <= r2 ->
    isHonest p = true ->
        length (certifiedBlocks p r1) > 0 ->
        (viewOfHighestCertifiedBlock p r2) >= r1). (* if p has a certified block in view r1, future highest certified blocks in view at least r1. *)

Variable incomingMessages : person -> list msgType.
Variable outgoingMessages : person -> list msgType.

(* communication assumptions. *)
Hypothesis synchrony:
    forall p1 p2: person, forall m: msgContentType, forall t1 t2: nat, 
        isHonest p1 = true -> isHonest p2 = true ->
        In (p1, p2, m, t1) (outgoingMessages p1) ->
        In (p1, p2, m, t2) (incomingMessages p2) /\
        t1<=t2 <= t1 + delta.

Hypothesis synchrony_incoming_implies_outgoing:
    forall p1 p2: person, forall m: msgContentType, forall t1 t2: nat, 
        isHonest p1 = true -> isHonest p2 = true ->
        In (p1, p2, m, t2) (incomingMessages p2) ->
        In (p1, p2, m, t1) (outgoingMessages p1) /\
        t1<=t2 <= t1 + delta.



(* the above two assumptions are not necessary. *)

(* the following two assumptions are necessary. *)
    

(* the list is sorted in ascending order of round number *)

Variable roundStartTime : person -> nat -> nat.
Variable precommitTime : person -> nat -> nat. 
(* the time when the round starts *)
Variable roundEndTime : person -> nat -> nat.

Variable currentRound : person -> nat -> nat. 

Variable hasQuit : person -> nat -> bool.

Inductive RoundResultType : Type :=
    | RoundCommitted (Bk: blockType)
    | RoundQuitConflict (Bk1: blockType) (cert1: certType) (Bk2: blockType) (cert2: certType)
    | RoundQuitBlame. 

Variable resultRound: person -> nat -> RoundResultType. 


(* the following two assumptions are necessary. *)

Hypothesis currentRound_def: 
    forall p: person, forall t: nat, 
        let r := currentRound p t in 
        roundStartTime p r <= t < roundStartTime p (r+1). 

(* the time when the round ends *)

(* proposal of leader in slot s. If person is not leader in the slot, return arbitrary things. *)
Variable proposalsOfLeaders: person->nat-> (prod blockType certType).
(* the proposal of a leader is the block and the certificate. *)
Variable precommitOfMembers: person->nat->precommitOrEmptyType. 


(* the following two assumptions are necessary. *)

Hypothesis startR1AtZero: 
    forall p:person, roundStartTime p 1 = 0.

Hypothesis roundStartAfterEnd:
    forall p:person, forall r:nat, 1<=r -> roundStartTime p (r+1) = roundEndTime p r.
(* seems like in the sluggish protocol, there is no waiting. To be adjusted later. *)


Hypothesis leaderProposaR1_empty_cert:
    exists Bk: blockType,
        let l1:= leaderOfRound 1 in
            isHonest l1 = true -> proposalsOfLeaders l1 1 = (Bk, empty).

Hypothesis leaderProposeR1:
    forall p:person, 
        In p replicas ->
        let l1 := leaderOfRound 1 in
        isHonest l1 = true -> In (p, l1, (propose (fst (proposalsOfLeaders l1 1)) 1 (snd (proposalsOfLeaders l1 1)) l1), roundStartTime l1 1) (outgoingMessages l1).


(* new leaders should wait for 2*delta time after entering its view. One delta for others to enter view, another delta to let others send their locked cert. *)
Hypothesis leaderProposeRn:
    forall p:person, forall r:nat, 
        r>=2 -> In p replicas ->
        let lr := leaderOfRound r in
        isHonest lr = true -> In (p, lr, (propose (fst (proposalsOfLeaders lr r)) r (snd (proposalsOfLeaders lr r)) lr), (roundStartTime lr r) + 2*delta) (outgoingMessages lr).


(* the above only says that the leader of round 0 should propose. It does not say that an honest leader only send 1 and only send at time 0. *)
Hypothesis leaderPropose_proposal_in_time_AND_unique:
    forall l p:person, forall msg:msgContentType, forall t:nat,
        In l replicas -> In p replicas ->
        isHonest l = true -> 
        exists (Bk:blockType) (r:nat) (cert:certType),
        In (l, p, (propose Bk r cert l), t) (outgoingMessages l) ->
        (
        let r' := currentRound p t in 
        let (Bk', cert') := proposalsOfLeaders l r' in
            r' = r /\ Bk' = Bk /\ cert' = cert
            /\ ((r=1 /\ t = roundStartTime l 1) \/ (r>=2 /\ t = (roundStartTime l r) + 2*delta))
        ).


(* vote | new-view is also a propose. *)
(* the following proposalValid checks if it has certificates. *)

Definition isProposalValid (p:person) (Bk:blockType) (r:nat) (cert:certType) : bool :=
    if is_element p replicas then
        if r =? 0 then false else
        if r =? 1 then
            match cert with
            | empty => true
            | _ => false
            end
        else
            match cert with
            | empty => if viewOfHighestCertifiedBlock p (r-1) =? 0 then true else false 
            | certificates Bk' r' => 
                if viewOfHighestCertifiedBlock p (r-1) <=? r' then true else false
            end
    else false.


Definition eq_cert (c1:certType) (c2:certType) : bool :=
    match c1, c2 with
    | empty, empty => true
    | certificates Bk1 r1, certificates Bk2 r2 => (Bk1 =? Bk2) && (r1 =? r2)
    | _, _ => false
    end.

(* the following isProposalDuplicate checks if the proposal is a duplicate. *)

Definition conflict  (p:person) (leader:person) (Bk:blockType) (r:nat) (cert:certType) (t:nat) (msg:msgType): bool :=
    match msg with
    | (_, p, msgcontent', t') =>
        match msgcontent' with
        | propose Bk' r' cert' proposer' =>
            if (r=?r') then
                if (proposer' =? leader) then 
                    if (t<?t') then negb (Bk =? Bk') || negb (eq_cert cert cert') else 
                    if (t=?t') then negb (Bk' <? Bk) || ((Bk' =? Bk) && negb (eq_cert cert cert')) else false
                else false 
            else false 
        | _ => false
        end
    end.

Definition isProposalDuplicate (p:person) (sender:person) (leader:person) (Bk:blockType) (r:nat) (cert:certType) (t:nat):bool :=
    if 0<?(length (filter (conflict p leader Bk r cert t) (incomingMessages p))) then true else false.

(* vote is valid if the voter has seen the proposal and the proposal is valid. *)

Hypothesis voteValid:
    forall p:person, forall sender:person, forall leader:person, forall Bk:blockType, forall r:nat, forall cert:certType, forall t:nat, forall anyone:person, 
    In p replicas ->
    In sender replicas ->
    In leader replicas ->  
    In anyone replicas ->
    isHonest p = true ->
    isLeader r leader = true ->
    currentRound p t = r -> (* also need a round not quit check. *)
        In (sender, p, (propose Bk r cert leader), t) (incomingMessages p) ->
        isProposalValid p Bk r cert = true -> (* check certificate*)
        isProposalDuplicate p sender leader Bk r cert t = false -> (* check duplicate *)
        In (p, anyone, (vote Bk r p), t) (outgoingMessages p).

Hypothesis forwardProposal:
    forall p:person, forall sender:person, forall anyone: person, forall leader:person, forall Bk:blockType, forall r:nat, forall cert:certType, forall t:nat,
    In p replicas ->
    In anyone replicas ->
    isHonest p = true ->
    r >= 1 ->
    currentRound p t = r ->
    isLeader r leader = true ->
    In (sender, p, (propose Bk r cert leader), t) (incomingMessages p) ->
    In (p, anyone, (propose Bk r cert leader), t) (outgoingMessages p).
    
Hypothesis blameLeader: (*not receiving a proposal in time*)
    forall p:person, forall leader:person, forall anyone:person, forall round:nat, 
    In p replicas ->
    In leader replicas ->
    In anyone replicas ->
    isHonest p = true ->
    isLeader round leader = true ->
    round >=1 ->
    let blameTime := if round =? 1 then (roundStartTime leader 1) + delta else if 2<=?round then  (roundStartTime leader round) + 4*delta else 0 in
    (
    (forall Bk: blockType, forall cert:certType, forall t:nat, 
        In (leader, p, (propose Bk round cert leader), t) (incomingMessages p) -> t>blameTime) -> (* TODO set the time correct *)
    In (p, anyone, (blame round p), blameTime) (outgoingMessages p)).

(* precommit is valid if the voter has seen the proposal and the proposal is valid. *)

Fixpoint countNonRep (l: list nat) : nat :=
    match l with
    | [] => 0
    | h::t => if is_element h replicas then countNonRep t else 1 + countNonRep t
    end.

Definition CountMsgs (cond:msgType->bool) (extractPerson: msgType->person) (msgs: list msgType) : nat :=
    countNonRep (map extractPerson (filter cond msgs)).

Definition cond_proposal (p:person) (Bk:blockType) (round:nat) (cert: certType) (proposer:person) (tleft:nat) (tright:nat) (msg:msgType): bool :=
    match msg with
    | (_, p, propose Bk round cert proposer, t) => 
        (tleft<=?t) && (t<=?tright)
    | _ => false
    end.


Definition cond_precommit(p:person) (Bk:blockType) (round:nat) (tleft:nat) (tright:nat) (msg:msgType):bool:=
    match msg with 
    | (_, p, precommit Bk round _, t) =>
        (tleft<=?t) && (t<=?tright)
    | _ => false
    end.

Definition extract_sender (msg:msgType) : person :=
    match msg with
    | (p, _, _, _) => p
    end.    

Hypothesis precommitPrepare:
    forall p:person, forall leader:person, forall anyone:person, forall Bk:blockType, forall r:nat, forall cert:certType, forall t:nat,
    In p replicas ->
    In anyone replicas ->
    In leader replicas ->
    isHonest p = true ->
    r >= 1 ->
    isLeader r leader = true ->
    currentRound p t = r -> (*might need quit view fix*)
    CountMsgs (cond_proposal p Bk r cert leader (roundStartTime p r) t) (extract_sender) (incomingMessages p) >= n_maj ->
    (t>=1 ->
    CountMsgs (cond_proposal p Bk r cert leader (roundStartTime p r) (t-1)) (extract_sender) (incomingMessages p) < n_maj) ->
    precommitTime p r = t /\ precommitOfMembers p r = precommitConstructor Bk. 

Hypothesis precommitTrigger:
    forall p:person, forall round: nat, forall anyone:person, forall t:nat, forall Bk:blockType, 
    In p replicas ->
    In anyone replicas ->
    isHonest p = true ->
    round >= 1 ->
    currentRound p t = round ->
    t = precommitTime p round + 2*delta ->
    In (p, anyone, (precommit Bk round p), t) (outgoingMessages p).

Hypothesis commitMember: 
    forall p:person, forall anyone:person, forall round: nat, forall t:nat, forall Bk:blockType, 
    In p replicas ->
    In anyone replicas ->
    isHonest p = true ->
    round >= 1 ->
    currentRound p t = round ->
    CountMsgs (cond_precommit p Bk round (roundStartTime p round) t) (extract_sender) (incomingMessages p) >= n_maj ->
    (forall t':nat, t'<t -> is_committedTime p t' = false) ->
    is_committedTime p t = true.

Hypothesis commitAtMostOnce: 
    forall p:person, forall t:nat, forall t':nat,
    In p replicas ->
    isHonest p = true ->
    is_committedTime p t = true ->
    t<=t' ->
    is_committedTime p t' = false.

(* the following two assumptions are necessary. *)

Hypothesis commitOnlyIfReceiving:
    forall p: person, forall t: nat,
        In p replicas ->
        isHonest p = true ->
        is_committedTime p t = true ->
        (exists Bk:blockType, exists round:nat, 
        (round >= 1) /\ (currentRound p t = round) /\ (CountMsgs (cond_precommit p Bk round (roundStartTime p round) t) (extract_sender) (incomingMessages p) >= n_maj)).


Hypothesis quitAfterConflict:
    forall p:person, forall t1 t2: nat, forall r:nat, 
    forall Bk Bk':blockType, forall cert cert':certType, forall sender sender':person,
    In p replicas ->
    isHonest p = true ->
    r >= 1 ->
    currentRound p t1 <= r ->
    currentRound p t2 <= r ->
    t1 <= t2 ->
    In (sender, p, (propose Bk r cert (leaderOfRound r)), t1) (incomingMessages p) -> 
    In (sender', p, (propose Bk' r cert' (leaderOfRound r)) t2) (incomingMessages p) ->  
    conflict p (leaderOfRound r) Bk r cert t1 (sender', p, (propose Bk' r cert' (leaderOfRound r)), t2) = true ->
    hasQuit p t2 = true.

(* the following two assumptions are necessary. *)

Theorem precommit_only_once: 
    forall p: person, forall anyone:person, forall round: nat, forall t: nat, forall Bk: blockType,
        In p replicas ->
        In anyone replicas ->
        round >= 1 ->
        isHonest p = true ->
        In (p, anyone, (precommit Bk round p), t) (outgoingMessages p) ->
        (currentRound p t = round) /\
        (precommitOfMembers p round = precommitConstructor Bk).
accept.
Qed.





End sync_hotstuff_sluggish_1block.