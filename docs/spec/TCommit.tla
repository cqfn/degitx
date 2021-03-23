------------------------------ MODULE TCommit ------------------------------
CONSTANT RM

VARIABLES rmState

\* Invariants
TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"

----------------------------------------------------

TCInit == rmState = [r \in RM |-> "working"]


canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] \notin {"committed"}

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) == \/ /\ rmState[r] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             \/ /\ rmState[r] \in {"working", "prepared"}
                /\ notCommitted
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \A r \in RM : Prepare(r) \/ Decide(r)
\* -------------------------

(***************************************************************************)
(* The following part of the spec is not discussed in Video Lecture 5.  It *)
(* will be explained in Video Lecture 8.                                   *)
(***************************************************************************)
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol written as a temporal      *)
  (* formula.                                                              *)
  (*************************************************************************)

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate TCTypeOK /\ TCInvariant is an invariant   *)
  (* of the specification TCSpec.  Invariance of this conjunction is       *)
  (* equivalent to invariance of both of the formulas TCTypeOK and         *)
  (* TCConsistent.                                                         *)
  (*************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Jan 19 14:29:17 MSK 2021 by i00544730
\* Created Tue Jan 19 13:45:58 MSK 2021 by i00544730
