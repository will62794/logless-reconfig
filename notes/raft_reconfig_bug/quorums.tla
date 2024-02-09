---- MODULE quorums ----
EXTENDS TLC

CONSTANT Server
VARIABLE Q

Init == Q = {}

AddOne(s) == 
    /\ s \notin Q
    /\ Q' = Q \cup {s}

RemoveOne(s) == 
    /\ s \in Q
    /\ Q' = Q \ {s}

Next == 
    \/ \E s \in Server : AddOne(s)
    \/ \E s \in Server : RemoveOne(s)

Symmetry == Permutations(Server)

====