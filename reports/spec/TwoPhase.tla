------------------------------ MODULE TwoPhase ------------------------------
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \union [type:{"Commit", "Abort"}]

TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages
            

TPInit ==   /\ rmState = [r \in RM |-> "working"]
            /\ tmState = "init"
            /\ tmPrepared = {}
            /\ msgs = {}            

TMRcvPrepared(r) == /\ tmState = "init"
                    /\ [type |-> "Prepared", rm |-> r] \in msgs
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>                                  

TMCommit == /\ tmState = "init"
            /\ tmState' = "done"
            /\ tmPrepared = RM
            /\ msgs' =  msgs \union {[type |-> "Commit"]}
            /\ UNCHANGED << rmState, tmPrepared >>  

TMAbort ==  /\ tmState = "init"
            /\ tmState' = "done"
            /\ msgs' =  msgs \union {[type |-> "Abort"]}
            /\ UNCHANGED << rmState, tmPrepared >>  
           
RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED << tmState, tmPrepared >>

RMChooseToAbort(r) == /\ rmState[r] = "working"
                   /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                   /\ UNCHANGED << tmState, tmPrepared, msgs >>  

RMRcvCommitMsg(r) == /\ [type |-> "Commit"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >> 
 
RMRcvAbortMsg(r) == /\ [type |-> "Abort"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >>

TPNext == \/ TMCommit \/ TMAbort
          \/ \E r \in RM :
            TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r) 
            \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)           


\* ---------------
INSTANCE TCommit

            
=============================================================================
\* Modification History
\* Last modified Mon Jan 25 11:12:56 MSK 2021 by i00544730
\* Created Wed Jan 20 15:30:37 MSK 2021 by i00544730
