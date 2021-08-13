(* 
    MIT License Copyright (c) 2021 CQFN
    https://github.com/cqfn/degitx/blob/master/LICENSE
    
    DeGit Tech Report. 
    Appendix 1. Gitaly fails explore.
    
    Situation:
    -> 1.1 Preafect calls Gitally with data to commit.
    |    2.1 Node process those data and call preafect with "prepared" state.
    |    2.2 Preafect responses with "commit" or "abort" command, depends on quorum.
    -- 1.2 Node writes data and response "acknowlege committed"
    3.1 Preafect calls DB and increase generations.

    Problem statement:
    Node can write down data (make commit done) (step 1.2) 
    and not response to Preafect, or Preafect can die on step 3.1.

    Result:
    At least ANY node where
        Data ARE saved.
        Generation is NOT incremented.
    
 *)
------------------------------ MODULE GitalyFail ------------------------------
EXTENDS TLC, Naturals, FiniteSets, Sequences

\* CONSTANT RM

VARIABLES rmState, rmVotedYes, rmVotedNo, rmAck, rmPrepared, rmCommitted, rmAborted, 
    rmGenerations, targetGeneration, MasterNode

\* MasterNode == "r0"
RM == { "r0", "r1", "r2", "r3", "r4", "r5" }

            
GFInit ==   /\ rmState = [r \in RM |-> "init"]            
            /\ rmGenerations = [r \in RM |-> 0]
            /\ targetGeneration = 0
            /\ rmVotedYes = {}
            /\ rmVotedNo = {}
            /\ rmAck = {}
            /\ rmPrepared = {}
            /\ rmCommitted = {}
            /\ rmAborted = {}
            /\ MasterNode = CHOOSE r \in RM: TRUE \* Always the same item.

\* Step 1.1 Preafect call RM and swith it to working state
RMRcvPack(r) == /\ rmState[r] = "init"
                /\ rmState' = [rmState EXCEPT ![r] = "working"] \* All the Nodes are answered
                /\ UNCHANGED << rmAborted, rmAck, rmCommitted, rmGenerations, rmPrepared, rmVotedNo, rmVotedYes, targetGeneration, MasterNode >>
                
\* Step 2.1 Node calls Preafect and send Vote
NodeVote(r) == /\ rmState[r] = "working"
               /\ (\/ (/\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                       /\ rmVotedYes' = rmVotedYes \cup {r}
                       /\ rmPrepared' = rmPrepared \cup {r}
                       /\ UNCHANGED << rmVotedNo, rmAborted >>) \* Prepared
                   \/ (/\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                       /\ rmVotedNo' = rmVotedNo \cup {r}
                       /\ rmAborted' = rmAborted \cup {r}
                       /\ UNCHANGED << rmVotedYes, rmPrepared >>)  \* Aborted
                   )  
               /\ UNCHANGED << rmAck, rmCommitted, rmGenerations,  targetGeneration, MasterNode >>              

\* Step 2.2 Preafect await for Quorum and send its decision
isQuorumYes == /\ MasterNode \in rmVotedYes
               /\ rmState[MasterNode] \in {"prepared", "committed"} \* Doublecheck
               /\ Cardinality(rmVotedYes) * 2 >= Cardinality(RM)

isQuorumNo  == \/ (/\ MasterNode \in rmVotedNo
                   /\ rmState[MasterNode] = "aborted") \* Doublecheck
               \/ Cardinality(rmVotedNo) * 2 > Cardinality(RM)              

RMRcvCommit(r) == /\ isQuorumYes
                  \* /\ rmState[r] /= "aborted"
                  /\ r \in rmPrepared  
                  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                  \* Send Ack or not send
                  /\ (\/ rmAck' = rmAck \cap {r} \* Answered to Preafect and counted by it
                      \/ UNCHANGED << rmAck >>) \* Preafect didn't receive acknowlege
                  /\ UNCHANGED << rmAborted, rmCommitted, rmGenerations, rmPrepared, rmVotedNo, rmVotedYes, targetGeneration, MasterNode >>
     
RMRcvAbort(r) == /\ isQuorumNo
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                 /\ (\/ rmAck' = rmAck \cap {r} \* Answered to Preafect and counted by it
                     \/ UNCHANGED << rmAck >>) \* Preafect didn't receive acknowlege
                 /\ UNCHANGED << rmAborted, rmCommitted, rmGenerations, rmPrepared, rmVotedNo, rmVotedYes, targetGeneration, MasterNode >>

\* Step 3.1 Preafect await all acks and calls DB and increase generations.

\* A trick to wait for all nodes are done their work
isTimeOut == \A r \in RM: rmState[r] \in {"committed", "aborted"}

ProcessGeneration == /\ isTimeOut \* All nodes voted
                     /\ targetGeneration' = 1
                     /\ rmGenerations = [r \in rmAck |-> 1]


GFNext == \/ ProcessGeneration
          \/  \E r \in RM:  \/ RMRcvPack(r) 
                            \/ NodeVote(r) 
                            \/ RMRcvCommit(r) 
                            \/ RMRcvAbort(r) 


\* Invariants
TypeOK == \A r \in RM: rmState[r] \in {"init", "working", "prepared", "committed", "aborted"}

SavedNoAck == ~\E r \in RM: /\ r \notin rmAck
                            /\ rmGenerations[r] = 1                            

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 15:25:42 MSK 2021 by i00544730
\* Created Wed Jan 20 15:30:37 MSK 2021 by i00544730

