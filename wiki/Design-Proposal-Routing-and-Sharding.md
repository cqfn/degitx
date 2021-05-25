### Eventual consistency
* Each repository is saved in one node and replicated to two other nodes in the same sharding.  
* Eventual consistency of the secondary replicas. (Not a strong consistency solution)
* Automatic failover from the primary to the secondary
* Reporting of possible data loss if the replication queue is non empty.
* Marking the newly promoted primary read only if possible data loss is detected.
* Distributed read can route the read request to an up to date node that has completed last replication and no scheduled replication.   The primary node is always a fallback option.  

### Strong Consistency
* In order to achieve strong consistency, the proxy node can issue write to multiple git nodes.  After the proxy node receives all success from the git nodes, it will then issue the commit to all git nodes.  
* The second replication cluster established in the different geo region, it may only support read. All writes will be redirected to the primary cluster. 

[[/images/DeGitX_Sharding.jpg|Sharding]]
[[/images/strong_consistency.png|Sequential Diagram]]
* Praefect will proxy an incoming ReceivePack request to multiple Gitaly nodes.
* Gitaly executes git receive-pack and passes incoming data to it.
* After git receive-pack has received all references that are to be updated, it executes the reference-transaction hook for each reference which is to be updated.
* The reference-transaction hook reaches out to Praefect and notifies it about all reference update it wants to perform.
* Praefect waits until all Gitaly nodes have notified it about the reference update. After it has received all notifications, it verifies that all nodes want to perform the same update. If so, it notifies them that they may go ahead by sending a "commit" message. Otherwise, it will send an "abort" message.
* When receiving the response, the hook will either return an error in case it got an "abort" message, which will instruct Git to not update the references.
* Otherwise, the hook will exit successfully and Git will proceed.
* Gitaly returns success to Praefect and the transaction is done.

[[/images/transaction_voting.png|Transaction Sequential Diagram]]

### References
https://gitlab.com/gitlab-org/gitaly/-/blob/master/doc/design_ha.md