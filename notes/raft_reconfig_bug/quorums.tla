---- MODULE quorums ----
EXTENDS TLC

CONSTANT Server
VARIABLE Q

Init == Q \in SUBSET (SUBSET Server)

AddOne(s) == 
    /\ s \notin Q
    /\ Q' = Q \cup {s}

RemoveOne(s) == 
    /\ s \in Q
    /\ Q' = Q \ {s}

Next == 
    /\ Q' \in SUBSET (SUBSET Server)
    /\ \A q \in Q, q2 \in Q' : q \cap q2 # {} 
    
    \* \/ \E s \in Server : AddOne(s)
    \* \/ \E s \in Server : RemoveOne(s)

Symmetry == Permutations(Server)

====