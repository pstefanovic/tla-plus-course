--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"  
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle" 
        /\ i' = i + 1
        /\ pc' = "done"  

Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Mon Dec 23 12:19:31 CET 2024 by temporaryadmin
\* Created Mon Dec 23 12:17:55 CET 2024 by temporaryadmin
