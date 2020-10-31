**Source:**

[`M. Castro, P. Druschel, A. Ganesh, A. Rowstron, and D. S.Wallach. Secure routing for structured peer-to-peer overlay networks. SIGOPS Oper. Syst. Rev., 36(SI):299–314, 2002.`](https://www.cs.cornell.edu/people/egs/cornellonly/syslunch/spring03/securep2p.pdf)

**Problem**: Presence of malicious node.

**Damage**: A small fraction of malicious nodes can prevent correct message delivery throughout the overlay.
> Such nodes may mis-route, corrupt, or drop messages and routing information.
> Additionally, they may attempt to assume the identity of other nodes and corrupt or delete objects
> they are supposed to store on behalf of the system.

**Analysis**:
> This problem is particularly serious in open peer-to-peer systems,
> where many diverse, autonomous parties without preexisting trust relationships
> wish to pool their resource.
>
> Even in a closed system of sufficiently large scale,
> it may be unrealistic to assume that none of the participating nodes
> have been compromised by attacker.

DeGitX is a system where resource pooling without preexisting trust relationships
should never happens or at least isn't planned by design.
It's assumed that all the nodes of one system are deployed at the capacities of one owner
and do not interact with other systems. 
<!-- link to white paper? -->

> Key building block to construct secure,
> decentralized applications upon structured overlay:
> - Secure assignment of node identifiers (1)
> - Secure routing table maintenance (2)
> - Secure message forwarding (3)

##### Secure nodeId assignment

> Secure nodeId assignment ensures that an attacker cannot choose
> the value of nodeIds assigned to the nodes that the attacker controls.
> Without it, the attacker could arrange to control all replicas of a given object,
> or to mediate all traffic to and from a victim node.

**Solution**: Introduce certificates, which bind a nodeId to public key.

> These certificates give the overlay a public key infrastructure, 
> suitable for establishing encrypted and authenticated channels between nodes.
> Nodes with valid nodeId certificates can join the overlay, route messages,
> and leave repeatedly without involvement of the CAs.

> Certified nodeIds work well when nodes have fixed nodeIds.

Degitx nodeId is a hash from its public key, so this condition is met.

> While nodeId assignment by a CA ensures that nodeIds are chosen randomly.

It's needed to prevent attackers from easy chose of nodeId, when untrusted nodes are allowed to join. 

> it is also important to prevent an attacker from easily obtaining a large number of nodeId certificates.

Condition is met: Untrusted nodes aren't allowed to join. Attackers can only compromise a node.

> None of the known solutions to nodeId assignment are effective when the overlay network is very small.
> For small overlay networks, we must require that all members of the network are trusted not to cheat.
> Only when a network reaches a critical mass, 
> where it becomes sufficiently hard for an attacker 
> to muster enough resources to control a significant fraction of the overlay,
> should untrusted nodes be allowed to join.

This condition is also met.

> The CAs represent points of failure, vulnerable to both technical and legal attacks.

##### Secure routing table maintenance

> Systems without strong constraints on the set of nodeIds
> that can fill each routing table slot are more vulnerable to this attack.
> Pastry and Tapestry impose very weak constraints at the top levels of routing tables.
> This flexibility makes it hard to determine if routing updates are unbiased,
> but it allows these systems to effectively exploit network proximity
> to improve routing performance.

If attackers can't obtain signed nodeId, attacks on routing table are excluded, 
because node updates its routing table only from trusted nodes.

##### Secure message forwarding

If we own 100% of nodes, routing isn't under attack, we only need to
establish encrypted and authenticated channels between nodes via public key infrastructure.

### Conclusion
When the membership of a peer-to-peer system is constraint and all nodes are trusted,
CAs could solve all security issues because all attacks are based on malicious nodes presence.
