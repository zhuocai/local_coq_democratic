# Working note

On Dec 25, I restarted working on the coq proof of democratic blockchain protocol. 

This time, I am confident that it can be finished. In order to prevent repetitive workload, I want to directly describe the complete protocol and prove the protocol. Start with the final lemmas we claim in the paper about multiple slots. 

Organization of this note: 
* section1: high level design choice. 
* section2: low-level details. 
- 2.1 message data structures
- 2.2 states and related data structures. 
- 2.2 assumptions and inference
* section3: project progress. 

## 1: High-Level Design choice

Previously, I worked on coq proofs of single-slot sync hotstuff protocol. New changes are the following:
* fix the protocol change of single-slot protocol in the democratic blockchain, as formalized in the s&p submission. Note that it is different from both standard-sync hotstuff and sluggish-sync hotstuff. 
* add the assumption-hypotheses required for liveness. In every round, every honest node receives only bounded messages from anyone. This allows the honest node to process all honest messages. 
* maybe use c++/python to generate the proof for me. 
* extend the set of committee members from sequence to more general finite sets (of equal length as simplification) 
* think about multiple slots. 
* authentication. Every block proposal should be signed, every vote and other messages should be signed. Trigger by something! 

#### Problem
1. If blockchain, a new block points to a previous block by hash. 
However, in coq, it's difficult to actually model the hash functions. Then it might cause problem, when different blocks have the same hash. 

Example: suppose the confirmed block for slot $s$ is $B_s$, with hash $hash(B_s)$, and there is another block $B'_s$ for the same slot $s$ that has the same hash $hash(B'_s) = hash(B_s)$. Once the confirmed block for slot $s+1$ is known, the new block might point to $B_s$ or $B'_s$. 

However, our protocol reaches consensus for each slot within the slot. Therefore, honest users still form the same chain of blocks. 

2. authentication

Every message received by an honest node must be authenticated: sent by the sender before. 

3. Backward engineering. 
Firstly write the big results, define necessary objects. However, for these types, don't have to be complete right now. For example, message types might not contain all types that are finally required. 

4. liveness
Argue that the chain is infinite. Also set state_after_node_id return type to be State instead of option State. 


## 2: Low-Level Details
### 2.1 Message and State - Data structures. 
#### 2.1.1 blockhash

The blockhash depends on the following fields: 
* prevhash: defined recursively. 
* block proposer: node. 
* block value: nat. 
* block slot: nat. 
* vote weight (actually with its proof). 
Note that the proof of consensus (CertProof, a list of certify messages by committee) is not included in the computation of hash. Reason: different nodes might receive different set of certify messages and proceed. If they include the set of certify messages in the computation of hash, then they the same block content might have multiple different hash values, making it hard to refer by hash values in the future. 

### 2.2 State
States: the blockchain system is a state machine system. Every node maintains its local states, and reaches consensus on the block contents. 

Committee members are determined by previous blocks, are part of the blockchain state, might be different for different nodes. Proving that they are the same for every node is a result of proving that they confirm the same block in every slot. 

State machine rules:

keep record of the following: 
- current slot. 
- confirmed blocks. (once confirmed, never reverted. )
  
#### 2.2.1 Remark of confirmed\_blocks
From the above framework, we can define a variable, that is the committee of each slot, in the eye of a node. 

Define a full mapping: node->slot->FullBlockType? (does not assume that every block derived from the mapping, is a valid block. )

Or use a optional mapping: node->slot->optional FullBlockType. 

comparison: disadvantages of full mapping: (1) already assuming that there is a confirmed block in every slot for every node, OR FullBlockType might be valid or not. 

My decision: use optional. Otherwise, I might forgot to apply the condition that the block should be valid. 



#### 2.2.2 confirm a block and enter a new slot

When receiving enough votes to confirm, the state does not go to the next slot immediately. Instead, it waits until receiving the aggregated proposal. This is to ensure that there exists a time, that the state confirms a block in a given slot. 


when confirmed, stay in slot, set a timer of 1 unit, enter new slot. Using this to manually make sure that, after the event that makes the node confirm, the state remains in the current slot and committed. 
So enter\_slot\_time = delta + previous-commit-time. 

#### 2.2.3 Event ordering
Event is ordered by time. If the time is the same, also define a rule. For example, if proposal arrives at the same time as proposal-timeout, do not blame, handle proposal arrival first. 

### 2.3 Blockchain Assumptions
#### 2.3.1 bound on number of nodes

note that, the set of nodes must be bounded. Otherwise, a node might receive infinite incoming messages in one slot, thus not able to prove liveness. Will add a hypothesis, saying that each node at most receives a bounded amount of messsages from boundedly many nodes in every slot. Thus can show liveness with concrete time bounds. 




## 3: work record
There are two ultimate goals: proving safety and proving liveness. If I only consider proving safety first, I might end up with writing a lot of code, but missing the necessary details for proving livess. 



#### how to prove safety

turns out that the safety proof is a bit more complicated. 

Forwaring confirmation quorom, only implies that if h1 commits block B1, then delta later, any other honest node must commit. However, other honest nodes might commit other blocks. 

Stating that other honest nodes also commit the same block, is the safety theorem itself. Therefore, introducing extra lemmas do not help. 

Therefore, must develop the state transition and triggers now. BUT don't forget backward engineering. How does the safety lemma breaks apart? 

#### Break safety:
- safety\_per\_slot: if every honest node confirms the same block in the previous slot, then if any two honest nodes confirm blocks in the current slot, they must confirm the same block. 
- one\_commit\_other\_committed: this is a lemma that can be easily proved, when the message forwarding is described. Others might not commit the same block. 
- Hypothesis: none-keeps-none -> implies some-prev-is-some. Part of the state machine definition, must confirm a block before proceeding to confirm the next slot. 

#### Break liveness:
- liveness\_per\_slot: condition is, every honest node confirms the same block in the previous slot. 
- one\_commit\_other\_committed: to show that in the previous slot, everyone committed. 
- safety: since everyone committed in the previous slot, they committed the same block in previous slot. 

Therefore, in the next stage, I should prove the following lemmas:
* safety per slot: 
* liveness per slot:
* one commit other committed: this is much more detailed results. 

## 4: coq notes

How to use a lemma that states exists something.  How to make it explicit. 

example: exists e, var = some e. 

How to replace var with some e. 

directly use destruct. 
