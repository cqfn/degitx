(* MIT License Copyright (c) 2020 CQFN
 *    https://github.com/cqfn/degitx/blob/master/LICENSE
 *)
------------------------------ MODULE TCommit ------------------------------
CONSTANT RM

VARIABLES rmState

\* Invariants
TCTypeOK == rmState \in [RM -> {"working", "prepared", "pre-committed", "committed", "aborted"}]

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"

----------------------------------------------------

TCInit == rmState = [r \in RM |-> "working"]

\* Noone is broken at the moment
canPreCommit == \A r \in RM : rmState[r] \in {"prepared", "pre-committed"}

canCommit == \A r \in RM : rmState[r] \in {"pre-committed", "committed"}

canAbort == \A r \in RM : rmState[r] \notin {"pre-committed", "committed"}

Decide(r) == \/ /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
             \/ /\ rmState[r] = "prepared"
                /\ canPreCommit
                /\ rmState' = [rmState EXCEPT ![r] = "pre-committed"]
             \/ /\ rmState[r] = "pre-committed"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             \/ /\ rmState[r] \in {"working", "prepared"}
                /\ canAbort
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \A r \in RM : Decide(r)
\* -------------------------

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)

=============================================================================
