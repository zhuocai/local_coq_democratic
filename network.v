Require Import Nat.
Require Import Lists.List.
Require Import Structures.Orders.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.


Section democraticBlockchain.



(*whether a is an element of b*)
Definition is_element (a : nat) (b : list nat) : bool :=
  existsb (fun x => Nat.eqb x a) b.


Variable delta : nat.
Variable web_time : nat. 
(* the allowed duration for miners proposing blocks, aggregating votes and publishing aggregated votes *)

Definition person := nat.
Definition weight :=nat. 

Variable isHonest : person -> bool.

Inductive block : Type :=
  | genesis
  | blk (prevBlock: block)(miner: person)(hash: nat)(time: nat).


Inductive msgcontent : Type :=
  | certify (slot: nat)(b: block)
  | proposal
  | aggregate
  | acknowledge
  | block_with_votes (slot: nat)(b:block)(w:weight) (*block proposer publishes it*)
  | local_winner (slot: nat) (b:block)(w:weight)
  | winner_proposal (slot: nat) (round: nat) (b:block) (w:weight) .

Inductive message : Type := 
  | msg (sender: person) (recipient: person)(content: msgcontent)(time: nat).

Inductive Stage : Type :=
  | receiving_proposals (* waiting to receive aggregate block from block proposers, lasts for web_time+delta. ends at t0 *)
  | sending_local_winner (* t0~t0+delta *)
  | receiving_local_winner  (* t0+delta ~ t0+2*delta*)
  | leader_propose (* committee leader starts proposing a winner, t0+2*delta ~ t0+3*delta *) 
  | receive_from_leader (* t0+3*delta ~ t0+4*delta *)
  | blame (* 2*delta after receiving_from_leader. This might overlap with the above stages *)
  | new_leader. 

(* List of signed incomingMessages and outgoingMessages of each person *)
Variable incomingMessages : person -> list message.
Variable outgoingMessages : person -> list message.

(*The blockchain from the point of view of each person at each slot*)
Variable blockchain : person -> nat -> block.

(*The current active slot from the point of view of each person
currentSlot p t is the slot from the point-of-view of person p at time t
 *)
Variable currentSlot : person -> nat -> nat.

Variable currentStage : person -> nat -> Stage. 
(* the current HotStuff round *)
Variable currentRound : person -> nat -> nat. 

(* don't use stages explicitly. Use timers instead *)
(* enterSlotTimers person slot = time to enter the slot. 
Define t0 = enterSlotTimers+delta. t0 is the time that committee members stop receiving proposals from block proposers. 
 *)
Variable enterSlotTimers: person->nat->nat.  

(* time in slot t and round r that a committee member receives the leader proposal *)
Variable leaderProposalTimers: person->nat->nat->nat. 

(* time in slot t and round r, that a committee member sends its acknowledge message *)
Variable precommitTimers: person->nat->nat->nat. 

(* time in slot t and round r, that a committee member quits the previous round r-1 *)
Variable newRoundTimers: person->nat->nat->nat. 


(* *)
Variable maxLocalWinner: person->nat->(prod block nat). 

(*Current slot can only increase by 1 if you are honest*)
Hypothesis incrementalSlot : forall a: person, isHonest a = true ->
  forall t: nat, currentSlot a t = currentSlot a (t+1) \/ currentSlot a t = currentSlot a (t+1) - 1.
 

(*The current committee from the point of view of each person at any given slot *)
Variable currentCommittee : person -> nat -> list person.

(* the HotStuff round leader in slot and round. *)
Variable currentLeader: person->nat->nat->person. 

(* Everyone starts at time zero in slot zero *)
Hypothesis startAtZero: forall p: person, currentSlot p 0 = 0.

(*Everyone starts with the genesis block*)
Hypothesis startAtGenesis: forall p:person, blockchain p 0 = genesis.

(* The property that a list of messages is sorted by time *)
Fixpoint isSorted (A:list message) : bool :=
  match A with
  | nil => true
  | cons (msg xs xr xc xt) Y => match Y with
                | nil => true
                | cons y Z => match y with
                              | msg ys yr yc yt => andb (xt<=?yt) (isSorted Y)
                              end
                end
  end.

(* The incoming and outgoing message lists are sorted *)
Hypothesis sortedIncoming: forall a: person, isSorted (incomingMessages a) = true.
Hypothesis sortedOutgoing: forall a: person, isSorted (outgoingMessages a) = true.

(* Synchrony: if a sends a message, b will receive it with delay at most delta *)
Hypothesis synchrony: forall a: person, forall b: person,
  forall msg a b (content: msgcontent) (time:nat),
  (In (msg a b content time) (outgoingMessages a)) ->
  exists m: message, exists time': nat,
  (In m (incomingMessages b)) /\ time' >= time /\ time' <= time + delta
  /\ m = msg a b content time'.

(* A function that returns all committee members in C from whom there is a 
certificate in list A on block b, for slot s, received on or before 
time t -- does not include duplicate elements*)

Fixpoint certificates(A: list message)(C: list person)(s: nat)(t: nat)(b: block) : list person :=
  match A with
  | nil => nil
  | m::B => match m with
                | msg sender recipient (certify s b) time =>
                    if andb (time<=?t) (is_element sender C) then
                      if is_element sender (certificates B C s t b) then (* remove duplicates *)
                        certificates B C s t b
                      else
                        sender::(certificates B C s t b)
                    else
                      certificates B C s t b
                | _ => certificates B C s t b
                end
  end.


(*A block is certified from your point of view, if you receive certify messages from half of the committee *)
Definition hasCertificateFromMajority (a: person)(t: nat)(b: block) := 
let s := currentSlot a t in
let committee := currentCommittee a s in
let certs b := certificates (incomingMessages a) committee s t b in
  2 * (length (certs b)) > length (committee).

(* If you are honest, you should constantly check if the block is certified,
and if so, go to the next slot *)
Hypothesis moveForward:
  forall a: person, forall t: nat, exists b: block, isHonest a = true -> hasCertificateFromMajority a t b -> 
      currentSlot a (t+1) = (currentSlot a t)+1.


(* If you are honest and you receive a certify message from a 
committee member, you will broadcast it *)
Hypothesis broadcastCertify:
  forall a b c: person, forall t: nat, forall m: message,  isHonest a = true ->
  In m (incomingMessages a) ->
  In c (currentCommittee a (currentSlot a t)) ->
  exists bl: block, exists s: nat, m = msg c a (certify s bl) t ->
  exists m': message,
  exists t': nat,
  t' <= t+delta /\
  In m' (incomingMessages b) /\
  m' = msg c b (certify s bl) t'.

(* If you are honest, you will add a block b at slot s only if you receive a majority certificate*)
(* Here, t is the last time of slot s *)
Hypothesis blockAddition:
  forall a: person, forall s: nat, forall b: block, forall t: nat, isHonest a = true ->
  currentSlot a t = s ->
  currentSlot a (t+1) = s+1 ->
  blockchain a s = b ->
  hasCertificateFromMajority a t b.
  



(* Real hypothesis: in every slot, the majority of committee members are honest *)
Hypothesis honestMajorityCommittee:
  forall slot:nat, forall a:person, 
    2 * length (filter isHonest (currentCommittee a slot)) > length (currentCommittee a slot).

(* Sync HotStuff, require stages in slot*) 

Hypothesis hotstuffStages_init:
  forall a:person, forall t: nat, forall t1:nat, 
  In a (currentCommittee a (currentSlot a t)) -> 
  currentSlot a t = (currentSlot a t-1) + 1 ->
  (t1>=t /\ t1<t+web_time+delta -> currentStage a t1 = receiving_proposals) /\ 
(*It enters current slot at time t, another person might enter at time t+delta, and finish by t+delta+web_time*)
  (t1>=t+web_time+delta /\ t1<t+web_time+2*delta -> currentStage a t1 = sending_local_winner) /\ 
(* actually sending at time t+web_time+delta*)
  (t1>=t+web_time+2*delta /\ t1<t+web_time+3*delta -> currentStage a t1 = receiving_local_winner) /\
  (*let t0 = t+web_time+delta. This is the time that local person sends its local winner.
   by t0+delta, all others have sent their local winners. by t0+2*delta, it (leader) receives all local winners.
  Therefore, leader proposes winner at time t0+2*delta*)
  (t1>=t+web_time+3*delta /\ t1<t+web_time+4*delta -> currentStage a t1 = leader_propose) /\
(* as a non-leader member, it sends its local winner at t0, the leader might be delta after him. 
In his local time, leader proposes winner by t0+3*delta. 
Therefore he expect to receive the proposal by t0+4*delta. 
On the other hand, he receives the proposal after t0+delta. 
*)
  (t1>=t+web_time+4*delta /\ t1<t+web_time+5*delta -> currentStage a t1 = receive_from_leader). 
  

(* Hotstuff stages after receiving the leader's proposal, we need a new timer*)
(*Hypothesis after_receiving_proposal: 
  forall a*)

(* Real hypothesis: at least one block proposer is honest 
-> all committee members at least receive one block proposal with aggregated votes. *) 
Hypothesis committeeReceiveAggregatedProposal:
  forall a:person, forall slot:nat, 
    In a (currentCommittee a slot) -> 
    exists m: message, exists b:person, exists bl:block, exists w:weight, exists t':nat, 
    (In m (incomingMessages a)) /\ 
    (m = msg b a (block_with_votes slot bl w) t') /\
    (currentSlot a t' = slot) /\
    (currentStage a t' = receiving_proposals). 
    

Fixpoint allAggregatedProposals (a:person) (slot:nat) (messages: list message) : list msgcontent :=
 match messages with
  | nil => []
  | cons (msg xs xr xc xt) Y => 
    match xc with 
      | (block_with_votes slot bl w) =>
           if ((currentSlot a xt) =? slot) then
            match (currentStage a xt) with 
              | receiving_proposals => xc::(allAggregatedProposals a slot Y)
              | _ => allAggregatedProposals a slot Y
            end
           else allAggregatedProposals a slot Y
      | _ => allAggregatedProposals a slot Y
  end
end.

Definition extractContentFromMessage (m: message): msgcontent :=
  match m with
    | msg x y c t => c
  end.

Definition larger_block_votes (msgc1: msgcontent) (msgc2: msgcontent) :=
  match msgc1 with
    | (block_with_votes slot bl w) =>
      match msgc2 with
        | (block_with_votes slot2 bl2 w2) =>
          if (w<?w2) then msgc2 else msgc1
        | _ => msgc1
      end
    | _ => msgc1
  end.


Fixpoint maxAggregatedProposal (proposals: list msgcontent): msgcontent :=
  match proposals with
    | nil => (block_with_votes 0 genesis 0) (* should not occur*)
    | cons x Y => 
      larger_block_votes x (maxAggregatedProposal Y)
  end.

      
Definition localWinner (member:person) (slot:nat) : msgcontent:=  
  maxAggregatedProposal (allAggregatedProposals member slot (incomingMessages member)).



(* Protocol Hypothesis: honest member sends a block_with_votes to all members at time t0 *)
Hypothesis memberSendLocalWinner:
  forall a:person, forall slot:nat, forall t:nat, forall b:person,
    In a (currentCommittee a slot) -> 
    In b (currentCommittee a slot) ->
    currentSlot a (t-1) = slot ->
    currentStage a (t-1) = receiving_proposals ->
    currentStage a t = sending_local_winner ->
    match (localWinner a slot) with 
      | (block_with_votes slot bl w) => 
         In (msg a b (local_winner slot bl w) t) (outgoingMessages a)
      | _ => False (*must take the above branch*)
    end
.

(* require a function to extract the local_winner block with the largest weight among the current committee members. *)
Definition filter_cond_is_local_winner (a:person) (slot:nat) (round:nat) (m:message):bool :=
  match m with 
    | msg x y c t =>
      match c with 
        | local_winner slot b w =>  andb (currentSlot a t =? slot) 
      (andb (currentRound a t =? round) 
      (andb  (
          match currentStage a (t-1) with 
            | receiving_proposals => true
            | sending_local_winner => true
            | receiving_local_winner => true
            | _ => false
            end
            )
    (andb (is_element x (currentCommittee a slot)) (y=?a))))
        | _ => false
      end
    end
  .
      

Fixpoint largest_winner (local_winners : list msgcontent) : msgcontent :=
  match local_winners with
    | [] => local_winner 0 genesis 0 (* error*)
    | [w] => w
    | w::ws => 
        match w with 
          | local_winner slot bl w =>
             match largest_winner ws with
               | local_winner slot2 bl2 weight2 => 
                  if (weight <? weight2) then  local_winner slot2 bl2 weight2 else w
               | _ => w
             end
          | _ => w
        end
  end.

                 

(* Protocol Hypothesis: honest leader proposes the largest winner to all members at time t0+2*delta *)
Hypothesis leaderProposeR0: 
  forall a: person, forall slot:nat, forall t: nat, forall b:person, 
    (currentLeader a slot 0 = a) ->
    (* at what time should the leader send *)
    (* which winner should the leader send *)
    currentSlot a t = slot -> 
    currentRound a t = 0 ->
    currentStage a t = leader_propose /\ currentStage a (t-1) = receiving_local_winner ->
    In b (currentCommittee a slot) ->
    In (msg a b (largest_winner (map extractContentFromMessage (filter (filter_cond_is_local_winner a slot 0) (incomingMessages a)))) t) (outgoingMessages a).

(* in later rounds, select largest local winner only if there is no existing ack block? *)
Hypothesis leaderProposeRn: True. (*figure out later*)

(* a lot of remaining check to ensure that honest people don't send extra messages. *)

(* a member should receive leader proposal during [t0+delta, t0+4*delta]*)
Hypothesis memberForwardProposal:
  forall a:person, forall slot:nat, forall t:nat, forall round:nat, forall b:person, forall c:person, 
    (In a (currentCommittee a slot)) ->
    (currentLeader a slot = b) ->
    (In c (currentCommittee a slot))->
    currentSlot a t = slot ->
    currentRound a t = round ->
    (round = 0 /\ 
        (t>= ((enterSlotTimers a slot) + web_time + 2*delta)) /\
        (t<= ((enterSlotTimers a slot) + web_time + 5*delta))
        ) /\
    (round >= 1 /\ True) (* fillin the detail later *) ->
    exists bl:block, exists w:weight,
    (In (msg b a (winner_proposal slot round bl w) t) (incomingMessages a)) /\ 
    (w>= snd (maxLocalWinner a slot)) /\
    True (*non conflict*) ->
    In (msg a c (winner_proposal slot round bl w) t) (outgoingMessages a).


    
    




End democraticBlockchain.
