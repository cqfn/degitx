## Consensus
### Paxos (Basic)

Paxos is a well known consensus algorithm to agree on a single value as chosen.

![basic-paxos-phases](https://img.draveness.me/2017-12-18-basic-paxos-phases.png)


The above screenshot is taken from page 12 of [Paxos lecture (Raft user study)](https://www.youtube.com/watch?v=YbZ3zDzDnrw).
If you want to know more about the Paxos protocol, you can take a look at that lecture.

Paxos isn't optimized for agreeing on a series of values in strict order.
If Basic Paxos is used to process the data stream, it will cause a very obvious performance loss.
Preparation phase for each value and resolving proposer conflicts for example.

### Multi-Paxos

Multi-Paxos combines several instances of Basic Paxos to agree on a series of values forming the log.
Multi-Paxos includes performance optimizations:
 - Use leader to reduce proposer conflicts.
 - Eliminate most Prepare requests.

If the leader in the cluster is very stable,
we need the preparation phase only for first Accept from this leader,
so that we can reduce the number of RPCs by half.

Basic Paxos: the leader isn't elected and everyone could propose.

![paxos-example](https://img.draveness.me/2017-12-18-paxos-example.png)

Multi-Paxos: the only one leader is elected and everyone could trust him -> prepare request is redundant.

![multi-paxos-example](https://img.draveness.me/2017-12-18-multi-paxos-example.png)

The above picture describes the process of Multi-Paxos in the stable phase.
S1 is the leader of the entire cluster.
When other servers receive requests from the client,
they will forward requests to the leader.

Of course, the emergence of the Leader role will naturally bring another problem - how the Leader should be elected.

Multi-Paxos is not specified precisely in literature.
There are significant gaps between the description of the Multi-Paxos algorithm and the needs of a real-world system.
In order to build a real-world system, an expert needs to use numerous ideas scattered in
the literature and make several relatively small protocol extensions.
The cumulative effort will be substantial and the final system will be based on an unproven protocol.


So it's up to you how to elect the Leader. As well as for other optimizations on the basis of Basic Paxos.

One simple approach as an example how to elect the leader.

- Let the server with highest ID act as leader.

- Each server sends a heartbeat message to every other servers every T ms.

- If a server hasn't received heartbeat from a server with higher ID in last 2T ms, it acts as leader:
    - Accepts requests from clients
    - Acts as proposer and acceptor
- If server not leader:
    - Rejects client requests(redirect to leader)
    - Acts only as acceptor

The operation of appending logs in Multi-Paxos is concurrent.
Such Election approach doesn't guarantee that new leader has same log as Quorum,
because Quorum doesn't even vote for a new leader.
A server that was unavailable all the time could reborn and became a new leader with an empty log.
So the new leader's log needs to be completed.

### Raft

Raft is actually a variant of Multi-Paxos, that IS SPECIFIED in literature.
By simplifying the Multi-Paxos model,
Raft implements a consensus algorithm that is easier for people to understand.

Raft has two restrictions on the basis of Multi-Paxos.
First, the operation of appending logs in Raft must be continuous,
while the operation of appending logs in Multi-Paxos is concurrent,
but for the state machine inside the node Both are in order.
The second is that Raft restricts the conditions of Leader election.
Only nodes with the latest and most complete logs can be elected as Leaders.

![multipaxos-vs-raft](https://img.draveness.me/2017-12-18-multi-paxos-and-raft-log.png)

In Raft, all follower logs are a subset of Leader,
while logs in Multi-Paxos do not guarantee this.
Because Raft restricts the way in which logs are appended, and the election process,
it will be easier to implement.

In theory, Paxos that supports concurrent log appending will have better performance than Raft,
but its understanding and implementation are still more complicated.
[Paxos made live article]((http://www.read.seas.harvard.edu/~kohler/class/08w-dsi/chandra07paxos.pdf)) as a proof.

As I see, almost any optimization of Multi-Paxos makes it more similar to Raft.
Except of concurrent log appending feature.

Reference:

https://draveness.me/consensus
https://youtu.be/JEpsBg0AO6o
https://youtu.be/YbZ3zDzDnrw
http://www.read.seas.harvard.edu/~kohler/class/08w-dsi/chandra07paxos.pdf
