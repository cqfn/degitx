(* MIT License Copyright (c) 2020 CQFN
 *    https://github.com/cqfn/degitx/blob/master/LICENSE
 *)
------------------------------ MODULE ThreePhase ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Key, Val, mngrs, tms

VARIABLES rmState, tmState, tmPrepared, msgs, store

\* Special workaround to make a Symmetry set cuz it's bug in TLA+
\* https://github.com/tlaplus/tlaplus/issues/404
RM == Permutations(mngrs)
TM == Permutations(tms)

Messages == [type: {"Prepared"}, rm: RM] \union [type:{"PreCommit", "Commit", "Abort"}]

\* The set of all combinations
\* Store == <<t \in TM, r \in RM>>

NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Val

(* Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]
*)

\* All possible states of Resource Managers and Transaction Managers
TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "pre-committed", "committed", "aborted"}]
            \* Old RM State here to remember the state was before Node gone down.            
            \* /\ tmState \in [TM -> {"init", "prepared", "done", "aborted"}]
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages
            
(*
 * Start conditions: all RMs work and ready to receive commands - "prepared"
                     all TMs work and primary for their own RMs, all in "init" state
                     store contains map of all cross-available pairs TM-RM
 *)
TPInit ==   /\ rmState = [r \in RM |-> "working"]
            /\ tmState = [t \in TM |-> "init"]
            /\ tmPrepared = {}
            /\ msgs = {}
            \* /\ store = [k \in Key |-> TM] 
            /\ store = Store

TPConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "pre-committed"

TMRcvPrepared(t, r) == /\ tmState[t] = "init"
                    /\ [type |-> "Prepared", rm |-> r] \in msgs
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>                                  

TMPreCommit(t) == /\ tmState[t] = "init"
            /\ tmState' = "prepared"
            /\ tmPrepared = RM
            /\ msgs' =  msgs \union {[type |-> "PreCommit"]}
            /\ UNCHANGED << rmState, tmPrepared, store >>  

TMCommit(t) == /\ tmState[t] = "prepared"
            /\ tmState' = "done"
            /\ tmPrepared = RM
            /\ msgs' =  msgs \union {[type |-> "Commit"]}
            /\ UNCHANGED << rmState, tmPrepared, store >>

TMAbort(t) ==  /\ tmState[t] = "init"
            /\ tmState' = "aborted"
            /\ msgs' =  msgs \union {[type |-> "Abort"]}
            /\ UNCHANGED << rmState, tmPrepared, store >>
           
RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED << tmState, tmPrepared, store >>

RMChooseToAbort(r) == \* /\ \E t \in TM: store[t][r] \notin {NoVal, r}                  
                      /\ rmState[r] \in {"working", "prepared"}
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED << tmState, tmPrepared, msgs, store >>  

RMRcvPreCommitMsg(r) == \* /\ \E t \in TM : store[t][r] \* Connected
                        /\ [type |-> "PreCommit"] \in msgs
                        /\ rmState' = [rmState EXCEPT ![r] = "pre-committed"]
                        /\ UNCHANGED << tmState, tmPrepared, msgs, store >> 

RMRcvCommitMsg(r) == \* /\ \E t \in TM : store[t][r] \* Connected
                     /\ [type |-> "Commit"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >> 
 
RMRcvAbortMsg(r) == \* /\ \E t \in TM : store[t][r] \* Connected
                    /\ [type |-> "Abort"] \in msgs
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                    /\ UNCHANGED << tmState, tmPrepared, msgs >>

RMunavailable(t,r) == /\ rmState[r] = "prepared"
                      /\ store[t][r] /= {}
                      /\ store' = [store EXCEPT ![t][r] = {}]
                      /\ UNCHANGED << tmState, tmPrepared, msgs >>

TPNext == \/ \E t \in TM : \E r \in RM :
            \/ TMCommit(t) \/ TMPreCommit(t) \/ TMAbort(t)
            \/ TMRcvPrepared(t, r) \/ RMPrepare(r) \/ RMChooseToAbort(r) 
            \/ RMRcvPreCommitMsg(r) \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

\* ---------------
INSTANCE TCommit
            
=============================================================================

