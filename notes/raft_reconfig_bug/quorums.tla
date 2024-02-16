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
    /\ Q # {s}
    /\ Q' = Q \ {s}

SingleNodeChange(s) == 
    \* Add
    \/ /\ s \notin Q
       /\ Q' = Q \cup {s}
    \* Remove
    \/ /\ s \in Q
       /\ Q # {s}
       /\ Q' = Q \ {s}

ToQuorumOverlap(Qnew) == 
    /\ Qnew # Q
    /\ Qnew # {}
    /\ QuorumsOverlap(Qnew, Q)
    \* Take only reconfigs in this action that wouldn't be single node changes.
    /\ ~\E t \in Server : Qnew = Q \cup {t}
    /\ ~\E t \in Server : Qnew = Q \ {t}
    /\ Q' = Qnew

Init == 
    /\ Q \in (SUBSET Server)
    /\ Q # {}

Next == 
    \/ \E s \in Server : SingleNodeChange(s)
    \/ \E S \in SUBSET Server : ToQuorumOverlap(S)

\* NextOverlap == 
    \* \/ \E S \in SUBSET Server : Overlap(S)


Symmetry == Permutations(Server)

====