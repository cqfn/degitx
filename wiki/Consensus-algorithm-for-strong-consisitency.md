When a client pushes new changes to DeGitX system, the request is handled by the front-end (a node which processes git request). This node will take the role of transaction-manager (TM). The front-end node finds all back-end nodes ( The back-end node _stores_ git repository replicas), where the back-end node has a resource-manager role (RM). 
Identifying the leader
1. TM node starts uploading blob objects to all RM nodes asynchronously. 
2. When all RMs accept blob objects, TM initiates the reference update by choosing one random RM node and sending reference update requests. Let’s call this random node a “leader” of the transaction. 
3. The leader is trying to prepare for commit by locking a reference and writing references on disk. 

### In the picture below from the left to the right:
* The first column is TM aka the Frontend
* The second column is the leader of RMs (aka the Backend nodes) randomly selected above
* The third column is the rest of RMs, non-leader 
![Paxos Commit](https://user-images.githubusercontent.com/3345425/104873404-47d85300-5905-11eb-800a-6879c5e7acc5.png)

On success, the leader of RM nodes calls reference-transaction hook with “prepared” argument. Each back-end node in this commit scope `has an instance of Paxos` to agree on a transaction decision: prepared or aborted. `This string value will be called a decision`; each back-end and front-end exposes “acceptor” API for other back-end nodes and uses “proposer” client to send the decision to other nodes. 

When the leader is prepared, it performs `two actions`: 
1) it sends 2A Paxos message with value “prepared” and ballot number 0 to all Paxos acceptors; **Assume all frontend and backend nodes are Paxos acceptors?** 
2) it sends "prepare" message to all other RMs. 


Each RM who received prepare messages it trying to prepare for the transaction `in the same way as it was performed by the leader`, except it doesn’t send prepare messages to other RMs on success. `Each RM is listening for decisions accepted from Paxos instances`, if it sees any “abort” decision, then it also aborts the transaction, if it sees that all RMs decided to commit, then it commits the transaction too. 

The TM (it also Paxos acceptor in the context of this transaction), is doing the same: `if it receives any “abort” message`, then it sends abort to all RM, if all Paxos instances have “prepare” messages, it sends commit request to all RMs. 
`Each RM periodically checks the state of Paxos instances of current commit`, and if it sees that the quorum (N/2 + 1) of each Paxos instance has “prepare” value, then it sends commit message too. In case if RM node crashed, it send 1A Paxos message with larger ballot number for “abort” decision, `it guarantees` that if the same node already committed the transaction but didn’t remember the Paxos instance will respond with “prepared” decision. In case if TM fails, all of the nodes can complete the transaction because they check the status of Paxos instance and can commit or abort based on this decision.

### Questions: 
* Wha is an instance of Paxos?  Is it running inside the node of RM? (Paxos-instance is an abstraction of acceptors and proposers roles serving distributed decision storage for each RM; theoretically, it could be hosted as dedicated servers but it'd not really optimal, so each RM can implement "acceptor" interface and process messages for all `N` Paxos-instances, where `N` is an amount of RMs, and behave like a proposer of self instance; another optimization described in "Consensus on transaction commit" paper is to merge acceptor's messages for different Paxos-instances and send bulk requests for all instances)
* How is API of "Acceptor" running in RM, or TM node? (it's described in first reference of this report, please check: Gray and L. Lamport, “Consensus on transaction commit,” ACM Trans. Database Syst., vol. 31, p. 133–160,Mar. 2006") 
* How does each RM is listening for decisions accepted from Paxos instances? (since each RM implements Paxos acceptor, it receives all messages related to decision value)
* How does TM knows all Paxos instances have "prepared" message?  (TM also implements Paxos acceptor, so it knows when all RMs are in prepared state)

### Benefits of using Paxos
Paxos-commit guarantees the presence of only one leader that proposes updates. the decision is made only if the quorum is reached. The use of quorums provides partition tolerance by fencing minority partitions while the majority (N/2 + 1) continues to operate. This is the pessimistic approach to solving split-brain, so it comes with an inherent availability trade-off. This problem is mitigated by the fact that each node hosts a replicated state machine which can be rebuilt or reconciled once the partition is healed. this guarantees progress by partitioning if at least one part of the network has N/2 + 1 nodes. In other cases quorum is unreachable.