(* MIT License Copyright (c) 2020 CQFN
 *    https://github.com/cqfn/degitx/blob/master/LICENSE
 *
 * Gitaly 2PC implementation, as it was digged out form the source code
 *)
---- MODULE Gitaly ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

(*--algorithm GitalyCommit

variables 

    Master;
    RM = <<"r0", "r1", "r2">>; \* , "r3", "r4", "r5">>;

    masterNode = Head(RM);
    Nodes = Tail(RM);
 
    \* Possible values: "working", "prepared", "committed", "aborted".
    rmState =  {} \union [n \in DOMAIN RM |-> "working"];

    preparedNodes = {};
    committedNodes = {};
    abortedNodes = {};

     
    \* LET TypeInvariant = ~\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted";

process node \in 2..Len(RM)
begin
RunMe:
    while (rmState[1] \notin {"aborted", "committed"}) do   
        Suggest:
            \* The first step is Main Node suggest to prepare for writing Trx.
            rmState[1] := "prepared";
        Prep:
            await rmState[1] = "prepared";
            either
                rmState[self] := "prepared";
                preparedNodes := preparedNodes \union {RM[self]};
            or
                rmState[self] := "aborted";
                abortedNodes := abortedNodes \union {RM[self]};
            end either;
        Decide:
            either
                await Len(preparedNodes) * 2 > Len(RM) /\ rmState[1] = "prepared"
                rmState[1] := "committed";
            or
                await Len(abortedNodes) * 2 > Len(RM)
                rmState[1] := "aborted";
            end either;
        Write:
            await rmState[1] \in {"committed", "aborted"} /\ rmState[self] \notin {"committed", "aborted"};
            rmState[self] := rmState[1];
    end while;
    print << "FINAL STATE:", rmState >>;
end process;

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "44e2d299" /\ chksum(tla) = "ac2fab31")
CONSTANT defaultInitValue
VARIABLES Master, RM, masterNode, Nodes, rmState, preparedNodes, 
          committedNodes, abortedNodes, pc

vars == << Master, RM, masterNode, Nodes, rmState, preparedNodes, 
           committedNodes, abortedNodes, pc >>

ProcSet == (2..Len(RM))

Init == (* Global variables *)
        /\ Master = defaultInitValue
        /\ RM = <<"r0", "r1", "r2" , "r3", "r4", "r5">>
        /\ masterNode = Head(RM)
        /\ Nodes = Tail(RM)
        /\ rmState = ({} \union [n \in DOMAIN RM |-> "working"])
        /\ preparedNodes = {}
        /\ committedNodes = {}
        /\ abortedNodes = {}
        /\ pc = [self \in ProcSet |-> "RunMe"]

RunMe(self) == /\ pc[self] = "RunMe"
               /\ IF (rmState[1] \notin {"aborted", "committed"})
                     THEN /\ pc' = [pc EXCEPT ![self] = "Suggest"]
                     ELSE /\ PrintT(<< "FINAL STATE:", rmState >>)
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << Master, RM, masterNode, Nodes, rmState, 
                               preparedNodes, committedNodes, abortedNodes >>

Suggest(self) == /\ pc[self] = "Suggest"
                 /\ rmState' = [rmState EXCEPT ![1] = "prepared"]
                 /\ pc' = [pc EXCEPT ![self] = "Prep"]
                 /\ UNCHANGED << Master, RM, masterNode, Nodes, preparedNodes, 
                                 committedNodes, abortedNodes >>

Prep(self) == /\ pc[self] = "Prep"
              /\ rmState[1] /= "working"
              /\ \/ /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                    /\ preparedNodes' = (preparedNodes \union {RM[self]})
                    /\ UNCHANGED abortedNodes
                 \/ /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                    /\ abortedNodes' = (abortedNodes \union {RM[self]})
                    /\ UNCHANGED preparedNodes
              /\ pc' = [pc EXCEPT ![self] = "Decide"]
              /\ UNCHANGED << Master, RM, masterNode, Nodes, committedNodes >>

Decide(self) == /\ pc[self] = "Decide"
                /\ \A r \in 1..Len(RM) : rmState[r] \notin {"working"}
                /\ IF abortedNodes /= {}
                      THEN /\ rmState' = [rmState EXCEPT ![1] = "aborted"]
                      ELSE /\ rmState' = [rmState EXCEPT ![1] = "committed"]
                /\ pc' = [pc EXCEPT ![self] = "Write"]
                /\ UNCHANGED << Master, RM, masterNode, Nodes, preparedNodes, 
                                committedNodes, abortedNodes >>

Write(self) == /\ pc[self] = "Write"
               /\ rmState[1] \in {"committed", "aborted"}
               /\ rmState' = [rmState EXCEPT ![self+1] = rmState[1]]
               /\ pc' = [pc EXCEPT ![self] = "RunMe"]
               /\ UNCHANGED << Master, RM, masterNode, Nodes, preparedNodes, 
                               committedNodes, abortedNodes >>

node(self) == RunMe(self) \/ Suggest(self) \/ Prep(self) \/ Decide(self)
                 \/ Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 2..Len(RM): node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
