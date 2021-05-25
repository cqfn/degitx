## Paxos - Consensus on Transaction Commit
1. In the real system, a transaction is first created and then RMs join it. How to handle a dynamically varying set of RMs. 
2. Registrar process is needed to accommodate a dynamic set of RMs.  What is RM in Kirill design? 
3. How to select the RM1 = BES (Hooks), which also acts as the lead? 
4. RM1 is BES (hooks) and Other RMs are BES (replicas). Where are the initial leader and acceptors? the registrar is generally on the same node as the initial leader, which is typically on the same node as the RM that creates the transaction.  So BES (hooks) also runs the initial leader, and registrar. 

## Others
1. Can we use bitcoin architecture to develop p2p system?  https://filecoin.io/. 
2. Can we use Kubernetes to manage nodes? 

