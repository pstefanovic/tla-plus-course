------------------------------ MODULE TwoPhase ------------------------------

CONSTANT RM

VARIABLES
  rmState,
  tmState,
  tmPrepared,
  msgs

Messages == [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]
   
TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "done"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

TPInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}
  

(***************************************************************************)
(* TM may receive a "prepared" message causing its state to change.  It    *)
(* may also receive the same message multiple times.  For the message we   *)
(* know its type and which RM is sending it.                               *)
(***************************************************************************)
TMRcvPrepared(r) == 
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>


(***************************************************************************)
(* TM may initiate a commit process by sending a commit message.           *)
(* TM send an commit message only if all RMs sent a prepare message.       *)
(***************************************************************************)
TMCommit == 
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>
  

(***************************************************************************)
(* TM may initiate an abort process by sending an abort message.  TM may   *)
(* spontenously send an abort message                                      *)
(***************************************************************************)
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>


(***************************************************************************)
(* RM may send a prepare message spontenously while in working state       *)
(***************************************************************************)
RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  

(***************************************************************************)
(* RM may decide to abort spontenously while in working state.             *)
(* It will not send an abort message though. It is not necessary           *)
(***************************************************************************)
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>



(***************************************************************************)
(* RM receives an abort message                                            *)
(***************************************************************************)
RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

(***************************************************************************)
(* RM receives a commit message                                            *)
(***************************************************************************)
RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


(***************************************************************************)
(* The spec evolves by either TM initiating an action, or TM receiving a   *)
(* message, or one of the RMs initiates an action or one of RMs receives a *)
(* message.                                                                *)
(***************************************************************************)
TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E r \in RM : 
    TMRcvPrepared(r)
    \/ RMPrepare(r) \/ RMChooseToAbort(r)
    \/ RMRcvAbortMsg(r) \/ RMRcvCommitMsg(r)


-----------------------------------------------------------------------------

INSTANCE TCommit 

\*(***************************************************************************)
\*(* The material below this point is not discussed in Video Lecture 6.  It  *)
\*(* will be explained in Video Lecture 8.                                   *)
\*(***************************************************************************)
\*
\*TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>
\*  (*************************************************************************)
\*  (* The complete spec of the Two-Phase Commit protocol.                   *)
\*  (*************************************************************************)
\*
\*THEOREM TPSpec => []TPTypeOK
\*  (*************************************************************************)
\*  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
\*  (* an invariant of the specification.                                    *)
\*  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*(***************************************************************************)
\*(* We now assert that the Two-Phase Commit protocol implements the         *)
\*(* Transaction Commit protocol of module TCommit.  The following statement *)
\*(* imports all the definitions from module TCommit into the current        *)
\*(* module.                                                                 *)
\*(***************************************************************************)
\*INSTANCE TCommit 
\*
\*THEOREM TPSpec => TCSpec
\*  (*************************************************************************)
\*  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
\*  (* Commit protocol implements the specification TCSpec of the            *)
\*  (* Transaction Commit protocol.                                          *)
\*  (*************************************************************************)
\*(***************************************************************************)
\*(* The two theorems in this module have been checked with TLC for six      *)
\*(* RMs, a configuration with 50816 reachable states, in a little over a    *)
\*(* minute on a 1 GHz PC.                                                   *)
\*(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Thu Jan 09 16:48:24 CET 2025 by temporaryadmin
\* Created Thu Jan 09 09:49:14 CET 2025 by temporaryadmin
