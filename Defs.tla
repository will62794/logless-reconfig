---- MODULE Defs ----
EXTENDS TLC, FiniteSets, Sequences, Naturals

\*
\* Various helper definitions.
\*

\* The set of all majority quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* The min/max of a set of numbers.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Is a sequence empty.
Empty(s) == Len(s) = 0

====