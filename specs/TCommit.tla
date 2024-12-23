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
TypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Initialy all resource managers must be in working state                 *)
(***************************************************************************)
Init == rmState = [r \in RM |-> "working"]

(***************************************************************************)
(* A resource manager may transition to a prepared state only from working *)
(* state                                                                   *)
(***************************************************************************)
Prepare(r) == rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"] 

(***************************************************************************)
(* A resource manager may transition to commited state only from prepared  *)
(* state, and only if all resource managers are either prepared or         *)
(* committed.                                                              *)
(***************************************************************************)
AllEitherPreparedOrCommitted == 
            \A r \in RM : rmState[r] \in {"committed", "prepared"}
Commit(r) == /\ rmState[r] = "prepared"
             /\ AllEitherPreparedOrCommitted
             /\ rmState' = [rmState EXCEPT ![r] = "committed"]

(***************************************************************************)
(* A resource manager may transition to aborted state from either working  *)
(* or prepared states, and only until no resource manager's state is       *)
(* committed                                                               *)
(***************************************************************************)
NoCommits == \A r \in RM : rmState[r] # "committed"
Abort(r) == /\ rmState[r] \in {"working", "prepared"}
            /\ NoCommits
            /\ rmState' = [rmState EXCEPT ![r] = "aborted"]             

(***************************************************************************)
(* Next step implies changing a state of at least one resource manager     *)
(***************************************************************************)
Next == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)

(***************************************************************************)
(* If at any time we have two resource managers, either, one in commiter   *)
(* and other in aborted or one in committed and other in working state,    *)
(* combined resource managers state is not consistent                      *)
(***************************************************************************)
NotConsistent == \A r \in RM : \A s \in RM : 
                                   \/ /\ rmState[r] = "committed" 
                                      /\ rmState[s] = "aborted"
                                   \/ /\ rmState[r] = "commited"
                                      /\ rmState[s] = "working"
Consistent == ~NotConsistent

=============================================================================
\* Modification History
\* Last modified Mon Dec 23 15:31:36 CET 2024 by temporaryadmin
\* Created Mon Dec 23 13:53:37 CET 2024 by temporaryadmin
