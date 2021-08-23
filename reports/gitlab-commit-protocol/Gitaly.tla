------------------------------- MODULE Gitaly -------------------------------
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT    RM,                 \* resource managers set
            TimeoutEnabled,     \* TRUE if RM timeout enabled
            TMFailEnabled,      \* TRUE if TM can crash
            MasterRM            \* Master RM node


VARIABLES
    rmState,
    tmState,
    messages,
    dbState,
    tmPrepared,
    tmCommitted

Messages == [type: {"receive-pack", "vote", "commited", "commit"}, rm: RM]

TypeOK ==   /\ rmState \in [RM -> {"working", "prepared", "commited", "aborted"}]
            /\ tmState \in {"up", "crash", "done"}
            /\ tmPrepared \subseteq RM
            /\ tmCommitted \subseteq RM
            /\ messages \subseteq Messages
            /\ dbState \in [RM -> {0, 1, 2}]

Init ==     /\ rmState = [r \in RM |-> "working"]
            /\ tmState = "up"
            /\ messages = {}
            /\ dbState = [r \in RM |-> 0]
            /\ tmPrepared = {}
            /\ tmCommitted = {}

(***********************************************************************)
(*                              HELPER                                 *)
(***********************************************************************)

Quorum(rms) ==
    \* Gitaly reaches the quorum if primary (first) RM voted for commit and at least a half of other RMs too
    (MasterRM \in rms) /\ (Cardinality(rms \intersect RM) * 2 > Cardinality(RM))

(***********************************************************************)
(*                              STEPS                                  *)
(***********************************************************************)

(* TM sends a message with receive pack command to one RM *)
TMSendInit ==   /\ tmState = "up"
                /\ \E rm \in RM: LET msg == [type |-> "receive-pack", rm |-> rm] IN
                    /\ msg \notin messages
                    /\ messages' = messages \cup {msg}
                /\ UNCHANGED <<rmState, tmState, dbState, tmPrepared, tmCommitted>>

RMPrepare(rm) == /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
                 /\ messages' = messages \cup {[type |-> "vote", rm |-> rm]}

RMAbort(rm) == /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
               /\ UNCHANGED <<messages>>

(****************************************************************)
(* One particular RM receives a message with receive-pack       *)
(* command. It either prepare or abort, if prepare, then vote   *)
(* by sending vote message to RM                                *)
(****************************************************************)
RMRcvInit == \E r \in {rm \in RM: rmState[rm] = "working"}:
            /\ [type |-> "receive-pack", rm |-> r] \in messages
            /\ (RMAbort(r) \/ RMPrepare(r))
            /\ UNCHANGED <<tmState, dbState, tmPrepared, tmCommitted>>

(* TM received vote message *)
TMRcvVote ==    /\ tmState = "up"
                /\ \E r \in {rm \in RM: rm \notin tmPrepared}: 
                    /\ [type |-> "vote", rm |-> r] \in messages
                    /\ tmPrepared' = tmPrepared \cup {r}
                /\ UNCHANGED <<rmState, tmState, messages, dbState, tmCommitted>>

(*************************************************************************)
(* The TM commits the transaction; enabled iff the TM is in its initial  *)
(* state and quorum of RM has sent a "Prepared" message.                 *)
(*************************************************************************)
TMSendCommit == /\ tmState = "up"
                /\ Quorum(tmPrepared)
                /\ \E rm \in RM: LET msg == [type |-> "commit", rm |-> rm] IN
                    /\ msg \notin messages
                    /\ messages' = messages \cup {msg}
                /\ UNCHANGED <<rmState, dbState, tmPrepared, tmCommitted, tmState>>

(* RM received commit comand and responds with committed message *)
RMRcvCommit == \E r \in {rm \in RM: rmState[rm] = "prepared"}:
            /\ [type |-> "commit", rm |-> r] \in messages
            /\ rmState' = [rmState EXCEPT ![r] = "commited"]
            /\ messages' = messages \cup {[type |-> "commited", rm |-> r]}
            /\ UNCHANGED <<tmState, dbState, tmPrepared, tmCommitted>>

(*******************************************************************)
(* If TM doesn't respond for Gitaly vote (prepared) message in     *)
(* some period of time, then Gitaly (RM) decide to abort           *)
(* the transaction.                                                *)
(*******************************************************************)
RMTimeoutAbort ==
            /\ TimeoutEnabled
            /\ \E r \in {rm \in RM: rmState[rm] = "prepared"}:
                rmState' = [rmState EXCEPT ![r] = "aborted"]
                \* TODO: check if Praefect handle timeout abort messages somehow or just ignore it
            /\ UNCHANGED <<tmState, messages, dbState, tmPrepared, tmCommitted>>

(* TM receives commit command and update db state *)
TMRcvCommitted ==   /\ tmState = "up"
                    /\ \E rm \in {r \in RM: r \notin tmCommitted}:
                        /\ [type |-> "commited", rm |-> rm] \in messages
                        /\ tmCommitted' = tmCommitted \cup {rm}
                        /\ LET state == dbState[rm] IN dbState' = [dbState EXCEPT ![rm] = state + 1]
                        /\ UNCHANGED <<rmState, tmState, messages, tmPrepared>>

TMDone ==   /\ tmState = "up"
            /\ \A rm \in RM: rm \in tmPrepared => rm \in tmCommitted
            /\ tmState' = "done"
            /\ UNCHANGED <<rmState, messages, dbState, tmPrepared, tmCommitted>>

TMFail == /\ TMFailEnabled
          /\ tmState = "up"
          /\ tmState' = "crash"
          /\ UNCHANGED <<rmState, messages, dbState, tmPrepared, tmCommitted>>

Next ==     \/ TMSendInit
            \/ RMRcvInit
            \/ TMRcvVote
            \/ TMSendCommit
            \/ RMRcvCommit
            \/ RMTimeoutAbort
            \/ TMRcvCommitted
            \/ TMFail
            \/ TMDone

(*
    invariant: consistency in Gitaly model is:
    all resource managers with highest generation
    has the same state.
*)

MaxGeneration == LET g == {dbState[rm]: rm \in RM} IN
            CHOOSE max \in g: \A x \in g: x <= max

RMConsistency(gen) ==  LET rms == {rm \in RM: dbState[rm] = gen} IN
                       \A rm1 \in rms: \A rm2 \in rms:
                           rmState[rm1] = "commited" => rmState[rm2] /= "aborted"

Consistency ==  \/ tmState = "up"
                \/ (tmState \in {"done", "crash"} /\ RMConsistency(MaxGeneration))

=============================================================================
