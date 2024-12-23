------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers
VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ small' = small
           /\ big' = 5

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ small' = small
            /\ big' = 0
            
SmallToBig == IF small + big <= 5 
                THEN big' = big + small
                    /\ small' = 0
                ELSE big' = 5
                    /\ small' = small - (5 - big)
                
BigToSmall == IF small + big <= 3 
                THEN big' = 0
                    /\ small' = small + big
                ELSE small' = 3
                    /\ big' = big - (3 - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall


=============================================================================
\* Modification History
\* Last modified Mon Dec 23 13:42:11 CET 2024 by temporaryadmin
\* Created Mon Dec 23 13:04:38 CET 2024 by temporaryadmin
