---- MODULE quorums ----
EXTENDS TLC, FiniteSets, Naturals

CONSTANT Server
VARIABLE Q


\* The set of all majority quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

Add(s) == 
    /\ s \notin Q
    /\ Q' = Q \cup {s}

Rem(s) == 
    /\ s \in Q
    /\ Q' = Q \ {s}

Mov(s, Qnew) == 
    /\ s \in Qnew
    /\ QuorumsOverlap(Qnew, Q)
    /\ Q' = Qnew

Init == Q \in (SUBSET Server)

Next == 
    \/ \E s \in Server : Add(s)
    \/ \E s \in Server : Rem(s)
    \/ \E s \in Server, S \in SUBSET Server : Mov(s, S)

Symmetry == Permutations(Server)

====