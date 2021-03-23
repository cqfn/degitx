(* MIT License Copyright (c) 2020 CQFN
 *    https://github.com/cqfn/degitx/blob/master/LICENSE
 *)
------------------------------ MODULE ThreePhase ------------------------------
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \union [type:{"PreCommit", "Commit", "Abort"}]

\* All possible states of Resource Managers and Transaction Managers
TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "pre-committed", "committed", "aborted"}]
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

TMPreCommit == /\ tmState = "init"
            /\ tmState' = "done"
            /\ tmPrepared = RM
            /\ msgs' =  msgs \union {[type |-> "PreCommit"]}
            /\ UNCHANGED << rmState, tmPrepared >>  

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

RMChooseToAbort(r) == /\ rmState[r] \in {"working", "prepared"}
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED << tmState, tmPrepared, msgs >>  

RMRcvPreCommitMsg(r) == /\ [type |-> "PreCommit"] \in msgs
                        /\ rmState' = [rmState EXCEPT ![r] = "pre-committed"]
                        /\ UNCHANGED << tmState, tmPrepared, msgs >> 

RMRcvCommitMsg(r) == /\ [type |-> "Commit"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >> 
 
RMRcvAbortMsg(r) == /\ [type |-> "Abort"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >>

TPNext == \/ TMCommit \/ TMPreCommit \/ TMAbort
          \/ \E r \in RM :
            TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r) 
            \/ RMRcvPreCommitMsg(r) \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)           


\* ---------------
INSTANCE TCommit

            
=============================================================================

