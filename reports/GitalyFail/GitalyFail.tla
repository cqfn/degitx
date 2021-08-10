------------------------------ MODULE GitalyFail ------------------------------
(* 
    MIT License Copyright (c) 2020 CQFN
    https://github.com/cqfn/degitx/blob/master/LICENSE
    
    DeGit Tech Report. 
    Appendix 1. Gitaly fails explore.
           
 *)
===============================================================================
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, 
    msgs, rmGenerations, tmGeneration, 

Messages == [type: {"Prepared"}, rm: RM] \union [type:{"Commit", "Abort"}]


TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "pre-committed", "committed", "aborted"}]
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages
            
TPInit ==   /\ rmState = [r \in RM |-> "working"]
            /\ tmState = "init"
            /\ tmPrepared = {}
            /\ msgs = {}            
            /\ rmGenerations = [r \in RM |-> 0]
            /\ tmGeneration = 0
            /\ rmPrepared = {},
            /\ rmCommitted = {}
            /\ rmAborted = {}

\* Don't call - endless loop
TMSend(r) == /\ \E r \in RM
             /\ rmState[r] = "working"
             /\ RMRcvPrep(r)
             /\ UNCHANGED << rmState, tmState, msgs >> 

(*
    Expected stages 
    
    TMInit + RMInit (all)
    TMsendPrepare
    RMRcvPrep -
        RMIgnorePrep
        RMDoPrepare
            RMConfirmPrepare - TMRcvConfirmation
    TMCalculateQuorum - add rms to voted
    TMSendCommit - to voted rms
    TMSendAbort - to voted rms
    RMRvcAbort
    RMRcvCommit -
        RMIgnoreCommit
        RMDoCommit
            RMConfirmCommit - add rms to confirmed commits
    TMIncreaseGen for confirmed
    
*)

DoNothing == /\ UNCHANGED << tmState, rmState >>

RMRcvPrep(r) == /\ \E r \in RM 
                /\ rmState[r] == "worknig"
                /\ (\/ DoNothing
                    \/ RMDoPrepare(r) )
                                      
RMDoPrepare(r) ==  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
\*                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                   /\ RMConfirmPrepare(r)
                   /\ UNCHANGED << tmState, tmPrepared >>

RMConfirmPrepare(r) == \/ DoNothing
                       \/ TMConfirmPrepare(r) 

TMConfirmPrepare(r) == /\ rmPrepared' = rmPrepared \union r
                       /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
        
IsQuorumPrepared == /\ [type |-> "Abort"] \notin msgs
                    /\ Cardinality(msgs) * 2 > Cardinality(Nodes)
                    \* AND MasterNode voted for Commit                     

TMSendCommit == /\ IsQuorumPrepared
                /\ tmState = "init"
                /\ tmState' = "done"
                \* /\ tmPrepared = RM
                /\ msgs' =  msgs \union {[type |-> "Commit"]}
                /\ tmGeneration' = tmGeneration + 1
                /\ UNCHANGED << rmState, tmPrepared >>  

TMSendAbort ==  /\ tmState = "init"
                /\ tmState' = "done"
                /\ msgs' =  msgs \union {[type |-> "Abort"]}
                /\ UNCHANGED << rmState, tmPrepared >>  

\* Here it is possible to devide to DoNothing and DoAbort, but it does not matter for the inconsistency issue. - ???
RMRcvAbort(r) == /\ rmState[r] \= "committed"
                 /\ [type |-> "Abort"] \in msgs
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                 /\ UNCHANGED << tmState, tmPrepared, msgs >>
                
RMRcvCommit(r) == /\ [type |-> "Commit"] \in msgs  
                  /\ (\/ DoNothing                
                      \/ RMDoCommit(r))
                  /\ UNCHANGED << tmState, tmPrepared, msgs >> 
                
RMDoCommit(r) == /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                 /\ (\/ DoNothing
                     \/ RMConfirmCommit(r) )

\* In fact  - TM got message rm[i] committed
RMConfirmCommit(r) == /\ msgs' = msgs \union {[type |-> "Commit", rm |-> r]}

\* Increase generation WHEN all answered AND difference is 1
TMRcvCommitConfirmation(r) == /\ tmGeneration = rmGenerations[r] + 1
                              /\ rmGenerations[r]' = tmGeneration 

\*-=-=-=-=-=-=-=-=-=-=-

TPNext == \/ TMSendCommit \/ TMSendAbort
          \/ \E r \in RM :
            RMRcvPrep(r) \/ RMConfirmPrepare(r) \/ RMRcvAbort(r) 
            \/ RMRcvCommit(r) \/ RMDoCommit(r) \/ TMRcvCommitConfirmation(r)         


\* ---------------
\* INSTANCE TCommit

\* Invariants
TCTypeOK == rmState \in [RM -> {"working", "prepared", "pre-committed", "committed", "aborted"}]

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"
=============================================================================
\* Modification History
\* Last modified Mon Aug 09 10:43:09 MSK 2021 by i00544730
\* Created Wed Jan 20 15:30:37 MSK 2021 by i00544730
