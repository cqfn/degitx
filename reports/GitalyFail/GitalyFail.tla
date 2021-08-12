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

CONSTANT RM

VARIABLES rmState, rmVotedYes, rmVotedNo, rmAck, rmPrepared, rmCommitted, rmAborted, 
    rmGenerations, targetGeneration

\* Invariants
TypeOK == \A r \in RM: rmState[r] \in [RM -> {"init", "working", "prepared", "committed", "aborted"}]

Consistent == \A r \in RM : ~( \/ (/\ rmState[r] = "aborted"
                                   /\ rmGenerations[r] = 1)
                               \/ (/\ rmState[r] = "committed"
                                   /\ rmGenerations[r] = 0)
                              )

-------------------------------------------------------------------------------
========

MasterNode = Head(RM)
            
GFInit ==   /\ rmState = [r \in RM |-> "init"]            
            /\ rmGenerations = [r \in RM |-> 0]
            /\ targetGeneration = 0
            /\ rmVotedYes = {}
            /\ rmVotedNo = {}
            /\ rmAck = {}
            /\ rmPrepared = {}
            /\ rmCommitted = {}
            /\ rmAborted = {}

\* Step 1.1 Preafect call RM and swith it to working state
RMRcvPack(r) == /\ rmState[r] = "init"
                /\ rmState' = [rmState EXCEPT ![r] = "working"] \* All the Nodes are answered
                
\* Step 2.1 Node calls Preafect and send Vote
NodeVote(r) == /\ r \notin rmVotedYes
               /\ r \notin rmVotedNo
               /\ rmState[r] = "working"
               /\ (\/ (/\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                       /\ rmVotedYes' = rmVotedYes \union r
                       /\ rmPrepared' = rmPrepared \union r) \* Prepared
                   \/ (/\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                       /\ rmVotedNo' = rmVotedNo \union r
                       /\ rmAborted' = rmAborted \union r)  \* Aborted
                   )            

\* Step 2.2 Preafect await for Quorum and send its decision
isQuorumYes == /\ MasterNode \in rmVotedYes
               /\ rmState[MasterNode] = "prepared" \* Doublecheck
               /\ Len(rmVotedYes) * 2 > Len(RM)

isQuorumNo  == \/ (/\ MasterNode \in rmVotedNo
                   /\ rmState[MasterNode] = "aborted" \* Doublecheck
               \/ Len(rmVotedNo) * 2 > Len(RM)              

RMRcvCommit(r) == /\ isQuorumYes
                  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                  \* Send Ack or not send
                  /\ (\/ rmAck' = rmAck \union r \* Answered to Preafect and counted by it
                      \/ UNCHANGED << rmAck >>) \* Preafect didn't receive acknowlege

RMRcvAbort(r) == /\ isQuorumNo
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                 /\ (\/ rmAck' = rmAck \union r \* Answered to Preafect and counted by it
                      \/ UNCHANGED << rmAck >>) \* Preafect didn't receive acknowlege

\* Step 3.1 Preafect await all acks and calls DB and increase generations.

\* A trick to wait for all nodes are done their work
isTimeOut == \A r \in RM:
            \/ rmState[r] = "committed"
            \/ rmState[r] = "aborted"

ProcessGeneration == /\ isTimeOut \* All nodes voted
                     /\ targetGeneration' = 1
                     /\ \E r \in rmAck: /\ rmState[r] = "committed"
                                        /\ rmGenerations(r) = 0
                                        /\ rmGenerations' = 1

------------------------------------------------------------------------

GFNext == \E r \in RM:
            RMRcvPack(r) \/ NodeVote(r) \/ RMRcvCommit(r) \/ RMRcvAbort(r) \/ ProcessGeneration

GFSpec == GFInit /\ [][GFNext]_rmState

THEOREM == GFSpec => [](TypeOK /\ Consistent)
=============================================================================
\* Modification History
\* Last modified Mon Aug 09 10:43:09 MSK 2021 by i00544730
\* Created Wed Jan 20 15:30:37 MSK 2021 by i00544730