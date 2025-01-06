# Working note

On Dec 25, I restarted working on the coq proof of democratic blockchain protocol. 

This time, I am confident that it can be finished. In order to prevent repetitive workload, I want to directly describe the complete protocol and prove the protocol. Start with the final lemmas we claim in the paper about multiple slots. 

## Design choice

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


## Details

### outside sync hotstuff
#### message types
directly add an hypothesis 


#### blockhash

The blockhash depends on the following fields: 
* prevhash: defined recursively. 
* block proposer: node. 
* block value: nat. 
* block slot: nat. 
* vote weight (actually with its proof). 
Note that the proof of consensus (CertProof, a list of certify messages by committee) is not included in the computation of hash. Reason: different nodes might receive different set of certify messages and proceed. If they include the set of certify messages in the computation of hash, then they the same block content might have multiple different hash values, making it hard to refer by hash values in the future. 

#### State
State machine rules:

keep record of the following: 
- current slot. 
- confirmed blocks. (once confirmed, never reverted. )
  
From the above framework, we can define a variable, that is the committee of each slot, in the eye of a node. 

Define a full mapping: node->slot->FullBlockType? (does not assume that every block derived from teh mapping, is a valid block. )

Or use a optional mapping: node->slot->optional FullBlockType. 

comparison: disadvantages of full mapping: (1) already assuming that there is a confirmed block in every slot for every node, OR FullBlockType might be valid or not. 

#### definition of state

## work record
There are two ultimate goals: proving safety and proving liveness. If I only consider proving safety first, I might end up with writing a lot of code, but missing the necessary details for proving livess. 
