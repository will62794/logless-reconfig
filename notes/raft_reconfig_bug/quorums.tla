---- MODULE quorums ----
EXTENDS TLC, FiniteSets, Naturals

CONSTANT Server
VARIABLE C


\* The set of all majority quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

Add(s) == 
    /\ s \notin C
    /\ C' = C \cup {s}

Rem(s) == 
    /\ s \in C
    /\ C # {s}
    /\ C' = C \ {s}

SingleNodeChange(s) == 
    \* Add
    \/ /\ s \notin C
       /\ C' = C \cup {s}
    \* Remove
    \/ /\ s \in C
       /\ C # {s}
       /\ C' = C \ {s}

ToQuorumOverlap(Qnew) == 
    /\ Qnew # C
    /\ Qnew # {}
    /\ QuorumsOverlap(Qnew, C)
    \* Take only reconfigs in this action that wouldn't be single node changes.
    /\ ~\E t \in Server : Qnew = C \cup {t}
    /\ ~\E t \in Server : Qnew = C \ {t}
    /\ C' = Qnew

Init == 
    /\ C \in (SUBSET Server)
    /\ C # {}

Next == 
    \/ \E s \in Server : SingleNodeChange(s)
    \/ \E S \in SUBSET Server : ToQuorumOverlap(S)

\* NextOverlap == 
    \* \/ \E S \in SUBSET Server : Overlap(S)


Symmetry == Permutations(Server)

====