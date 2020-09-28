When user call some Remote Procedure,
before perform operation we should:
- Balance load.
- Resolve repo location.
- Discover complementary nodes.
 
 Praefect cares about last lo steps.
  
 ### Praefect
 
 Praefect is a router and transaction manager for Gitaly, and a required component for running a Gitaly Cluster.
 
 > The high level design takes a reverse proxy approach to fanning out write requests to the appropriate nodes:
>
 ![praefect](https://user-content.gitlab-static.net/42d614c076d253d6497e96b4f5b5c51571f7d263/68747470733a2f2f646f63732e676f6f676c652e636f6d2f64726177696e67732f642f652f32504143582d3176526c3757532d3652424f5778794c5342624242416f56394d75706d5468357654714d4f775f41583961786c626f716b796254624671477145784c7979594f696c7145573753396575586442487a582f7075623f773d39363026683d373230)
 
 Datastore contains:
 - Primary location for a project.
 - Redundant locations for a project.
 - Available storage locations.
 
 Storage Coordinator serves for:
 - Resolving repo location to modify primary node.
 - Discovering complementary nodes to replicate.
 
 See entire workflow [here](https://gitlab.com/gitlab-org/gitaly/-/blob/master/doc/design_ha.md).
 
 ### Load Balancer
 
 ![load balancer](https://docs.gitlab.com/13.3/ee/administration/gitaly/img/praefect_architecture_v12_10.png)
 
 The minimum recommended configuration for a Gitaly Cluster requires:
 
- 1 load balancer
- 1 PostgreSQL server (PostgreSQL 11 or newer)
- 3 Praefect nodes
- 3 Gitaly nodes (1 primary, 2 secondary)

Gitaly Cluster docs is [here](https://docs.gitlab.com/13.3/ee/administration/gitaly/praefect.html).

**Load Balancers for RPC:**
- [grpclb](https://github.com/bsm/grpclb) - External Load Balancing Service solution for gRPC written in Go.
- [nRPC](https://github.com/nats-rpc/nrpc) - Load balancing without load balancers: Stateless microservices can be hosted redundantly and connected to the same NATS cluster. The incoming requests can then be random-routed among these using NATS queueing. There is no need to setup a (high availability) load balancer per microservice.


 
                           