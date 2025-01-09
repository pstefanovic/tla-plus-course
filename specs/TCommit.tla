------------------------------ MODULE TCommit ------------------------------

(***************************************************************************)
(*RM is an array(set) of resource managers                                 *)
(***************************************************************************)
CONSTANT RM


(***************************************************************************)
(* rmState is a function yielding resource manager state for a given       *)
(* index. Permitted resource states are working, prepared, committed and   *)
(* aborted.                                                                *)
(***************************************************************************)
VARIABLE rmState
TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Initialy all resource managers must be in working state                 *)
(***************************************************************************)
TCInit == rmState = [r \in RM |-> "working"]

(***************************************************************************)
(* A resource manager may transition to a prepared state only from working *)
(* state                                                                   *)
(***************************************************************************)
TCPrepare(r) == rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"] 

(***************************************************************************)
(* A resource manager may transition to commited state only from prepared  *)
(* state, and only if all resource managers are either prepared or         *)
(* committed.                                                              *)
(***************************************************************************)
TCAllEitherPreparedOrCommitted == 
            \A r \in RM : rmState[r] \in {"committed", "prepared"}
TCCommit(r) == /\ rmState[r] = "prepared"
             /\ TCAllEitherPreparedOrCommitted
             /\ rmState' = [rmState EXCEPT ![r] = "committed"]

(***************************************************************************)
(* A resource manager may transition to aborted state from either working  *)
(* or prepared states, and only until no resource manager's state is       *)
(* committed                                                               *)
(***************************************************************************)
TCNoCommits == \A r \in RM : rmState[r] # "committed"
TCAbort(r) == /\ rmState[r] \in {"working", "prepared"}
            /\ TCNoCommits
            /\ rmState' = [rmState EXCEPT ![r] = "aborted"]             

(***************************************************************************)
(* Next step implies changing a state of at least one resource manager     *)
(***************************************************************************)
TCNext == \E r \in RM : TCPrepare(r) \/ TCCommit(r) \/ TCAbort(r)

(***************************************************************************)
(* If at any time we have two resource managers, either, one in commited   *)
(* and another in aborted, or one in committed and another in working      *)
(* state, then the combined resource managers state is not consistent      *)
(***************************************************************************)
TCNotConsistent == \A r \in RM : \A s \in RM : 
                                   \/ /\ rmState[r] = "committed" 
                                      /\ rmState[s] = "aborted"
                                   \/ /\ rmState[r] = "commited"
                                      /\ rmState[s] = "working"
TCConsistent == ~TCNotConsistent

=============================================================================
\* Modification History
\* Last modified Thu Jan 09 16:45:53 CET 2025 by temporaryadmin
\* Created Mon Dec 23 13:53:37 CET 2024 by temporaryadmin
