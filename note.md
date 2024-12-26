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
