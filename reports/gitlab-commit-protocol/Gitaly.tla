(* 
    MIT License Copyright (c) 2020 CQFN
    https://github.com/cqfn/degitx/blob/master/LICENSE
    
    DeGit Tech Report. Appendix 1. Gitaly implementation of the Consensus algorithm.
    
    During the research, it was found out Gitaly implements Two-Phase commit protocol.
    Moddeling of its behavior show the protocol is correct and inconcistance was not reached.
    It means that is is not possible to get one node in committed state and another node 
    in aborted state in the same transaction. 
    The biggest issue of such implementation is block of Git branch in case of network fail
    with unreacheble consensus (based on majority rule).
    At the same time, recovery procedure is not supported at the protocol level. 
    There are a set of external modules supply turning back repositories to the same version.
        
 *)
---- MODULE Gitaly ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

(*--algorithm GitalyCommit

variables 

    \* Resource managers - complete list of nodes.
    RM = << "r0", "r1", "r2", "r3", "r4", "r5" >>;

    Nodes = Tail(RM); \* Assumed r0 is the master node.
 
    (*
       Set os states of Resourse Managers. Transaction we interesting in start
       at Master Node and switch it to "prepared" state. 
       If it is no possible - it will not go further and out of the scope of this task.
       Possible RM states: "working", "prepared", "committed", "aborted".    
     *)
    rmState = <<"prepared">> \o [n \in DOMAIN Nodes |-> "working"];

    \* Sets of nodes what answered to request from MasterNode. 
    \* Used to calculate consensus votes.
    preparedNodes = {};
    committedNodes = {};
    abortedNodes = {};

process atomicCommit = 1
begin 
    (*
      Loop till consensus is reached. The condition to exit is majority of votes
      for commit or abort transaction.
      Here modulated the case, when Master Node is already prepared 
      (ready to write commit) and waiting for acknoledge from follower nodes.
      In reality there can be more votes than Nodes/2, but it does not metter
      to make a decision. 
    *)
    mainLoop:
    while Cardinality(committedNodes) * 2 < Len(RM) 
       /\ Cardinality(abortedNodes)   * 2 < Len(RM) do
        prepareNodes:
            \* Every node can eiter process the Trx or fail.
            with node \in 2..Len(RM) do
                either
                    rmState[node] := "prepared";
                    preparedNodes := preparedNodes \union {RM[node]};
                or
                    rmState[node] := "aborted";
                    abortedNodes := abortedNodes \union {RM[node]};
                end either;
            end with;
        (*
            Technical step:
            All nodes are able to vote and move from working stage to 
            prepared or aborted. Whel all voted, MasterNode has to decide. 
        *)    
        nextStep:
            \* Nodes iterator
            if \E n \in DOMAIN RM : rmState[n] = "working" then
                goto prepareNodes;
            else
                goto masterDecide;
            end if;
        (*
            All nodes are voted, MasterNode calculates the magority.
        *)                            
        masterDecide:          
            either
                await Cardinality(preparedNodes) * 2 >= Len(Nodes) 
                   /\ rmState[1] = "prepared";
                rmState[1] := "committed";            
            or
                await Cardinality(abortedNodes) * 2 > Len(Nodes);
                rmState[1] := "aborted";
            end either;
        (*
            The final step: every Node executes the order came from MAsterNode. 
        *)    
        nodesWrite:
            with node \in 2..Len(RM) do
                await rmState[1] \in {"committed", "aborted"} 
                   /\ rmState[node] \notin {"committed", "aborted"};
                rmState[node] := rmState[1];
            end with;        
    end while;    
end process;

end algorithm;*)

VARIABLES RM, Nodes, rmState, preparedNodes, committedNodes, abortedNodes, pc

vars == << RM, Nodes, rmState, preparedNodes, committedNodes, abortedNodes, 
           pc >>

ProcSet == {1}

Init == (* Global variables *)
        /\ RM = << "r0", "r1", "r2", "r3", "r4", "r5" >>
        /\ Nodes = Tail(RM)
        /\ rmState = <<"prepared">> \o [n \in DOMAIN Nodes |-> "working"]
        /\ preparedNodes = {}
        /\ committedNodes = {}
        /\ abortedNodes = {}
        /\ pc = [self \in ProcSet |-> "mainLoop"]

mainLoop == /\ pc[1] = "mainLoop"
            /\ IF    Cardinality(committedNodes) * 2 < Len(RM)
                  /\ Cardinality(abortedNodes)   * 2 < Len(RM)
                  THEN /\ pc' = [pc EXCEPT ![1] = "prepareNodes"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
            /\ UNCHANGED << RM, Nodes, rmState, preparedNodes, committedNodes, 
                            abortedNodes >>

prepareNodes == /\ pc[1] = "prepareNodes"
                /\ \E node \in 2..Len(RM):
                     \/ /\ rmState' = [rmState EXCEPT ![node] = "prepared"]
                        /\ preparedNodes' = (preparedNodes \union {RM[node]})
                        /\ UNCHANGED abortedNodes
                     \/ /\ rmState' = [rmState EXCEPT ![node] = "aborted"]
                        /\ abortedNodes' = (abortedNodes \union {RM[node]})
                        /\ UNCHANGED preparedNodes
                /\ pc' = [pc EXCEPT ![1] = "nextStep"]
                /\ UNCHANGED << RM, Nodes, committedNodes >>

nextStep == /\ pc[1] = "nextStep"
            /\ IF \E n \in DOMAIN RM : rmState[n] = "working"
                  THEN /\ pc' = [pc EXCEPT ![1] = "prepareNodes"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "masterDecide"]
            /\ UNCHANGED << RM, Nodes, rmState, preparedNodes, committedNodes, 
                            abortedNodes >>

masterDecide == /\ pc[1] = "masterDecide"
                /\ \/ /\    Cardinality(preparedNodes) * 2 >= Len(Nodes)
                         /\ rmState[1] = "prepared"
                      /\ rmState' = [rmState EXCEPT ![1] = "committed"]
                   \/ /\ Cardinality(abortedNodes) * 2 > Len(Nodes)
                      /\ rmState' = [rmState EXCEPT ![1] = "aborted"]
                /\ pc' = [pc EXCEPT ![1] = "nodesWrite"]
                /\ UNCHANGED << RM, Nodes, preparedNodes, committedNodes, 
                                abortedNodes >>

nodesWrite == /\ pc[1] = "nodesWrite"
              /\ \E node \in 2..Len(RM):
                   /\    rmState[1] \in {"committed", "aborted"}
                      /\ rmState[node] \notin {"committed", "aborted"}
                   /\ rmState' = [rmState EXCEPT ![node] = rmState[1]]
              /\ pc' = [pc EXCEPT ![1] = "mainLoop"]
              /\ UNCHANGED << RM, Nodes, preparedNodes, committedNodes, 
                              abortedNodes >>

atomicCommit == mainLoop \/ prepareNodes \/ nextStep \/ masterDecide
                   \/ nodesWrite

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == atomicCommit
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

====
