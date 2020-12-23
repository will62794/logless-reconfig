---- MODULE MongoSafeWeakLockstepRaft ----
\*
\* Restricted version of MongoSafeWeakRaft that requires entries to be committed before writing new ones.
\* 
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE config

VARIABLE elections
VARIABLE committed

vars == <<currentTerm, state, log, elections, committed, config>>

\* Constants for model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

MWR == INSTANCE MongoWeakRaft 
    WITH MaxTerm <- MaxTerm,
         MaxLogLen <- MaxLogLen,
         MaxConfigVersion <- MaxConfigVersion,
         Server <- Server,
         Secondary <- Secondary,
         Primary <- Primary,
         Nil <- Nil,
         currentTerm <- currentTerm,
         state <- state,
         config <- config,
         elections <- elections,
         committed <- committed

MSWR == INSTANCE MongoSafeWeakRaft 
    WITH MaxTerm <- MaxTerm,
         MaxLogLen <- MaxLogLen,
         MaxConfigVersion <- MaxConfigVersion,
         Server <- Server,
         Secondary <- Secondary,
         Primary <- Primary,
         Nil <- Nil,
         currentTerm <- currentTerm,
         state <- state,
         config <- config,
         elections <- elections,
         committed <- committed


\* Re-defined locally for convenience.
ElectionSafety == MSWR!MWR!ElectionSafety
LeaderCompleteness == MSWR!MWR!LeaderCompleteness
StateMachineSafety == MSWR!MWR!StateMachineSafety

\* Is log entry e=<<i,t>> committed.
EntryCommitted(e) == \E c \in committed : c.entry = e

\* Is log entry e=<<i,t>> committed. (shorter definition)
Committed(e) == EntryCommitted(e)

\* Is an edge 'e' an update edge i.e. both nodes have the same term.
IsUpdateEdge(e) == e[1][2] = e[2][2]

\* Is an edge 'e' an election edge i.e. the nodes have different terms.
IsElectionEdge(e) == e[1][2] # e[2][2]

Range(f) == MWR!Range(f)

\* Before executing a client write, the newest entry on a primary must be committed.
LockstepCommit ==
    \A s \in Server : \A i \in 2..Len(log[s]) : 
        LET edge == << <<i-1,log[s][i-1]>>, <<i,log[s][i]>> >> IN
        IsUpdateEdge(edge) => Committed(edge[1])

\* When a leader is elected, it must have atomically written a log entry in its new term.
LockstepElectionBarrier == 
    \A s \in Server : (state[s] = Primary) => \E t \in Range(log[s]) : t=currentTerm[s]

LockstepCondition == 
    /\ LockstepCommit
    /\ LockstepElectionBarrier

\* Is the last log entry of node 'i' currently committed.
LastIsCommitted(i) == 
    \/ Len(log[i]) = 0 \* consider an empty log as being committed.
    \/ /\ Len(log[i]) > 0
       /\ \E c \in committed : 
            c.entry = <<Len(log[i]), log[i][Len(log[i])]>>

\*
\* This protocol behaves the same as the "safe" weak protocol, except that it adds a few
\* extra pre/post conditions to ensure the lockstep behavior.
\*
Init == MSWR!Init /\ LockstepCondition
Next == MSWR!Next /\ LockstepCondition'
Spec == Init /\ [][Next]_vars


THEOREM MongoSafeWeakRaftSafety == Spec => []StateMachineSafety

--------------------------------------------------------

\*
\* Safety property definitions.
\*


\* Determines if it1=<<index1,term1>> is newer than it2=<<index2,term2>>
IndTermGT(it1,it2) == 
    \/ (it1[2] = it2[2] /\ it1[1] > it2[1])
    \/ it1[2] > it2[2]

IndTermGTE(it1,it2) ==
    IndTermGT(it1,it2) \/ it1=it2 

\* The log entry <<i, t>> at position 'i' in the log of node 's'. 
EntryAt(i,s) == <<i,log[s][i]>>

\* History edges in the log of node 's'.
LogEdges(s) == {<<EntryAt(i,s), EntryAt(i+1,s)>>: i \in 1..Len(log[s])-1}

\* The configuration history structure. It is a set of edges.
HistoryEdges == UNION {LogEdges(s) : s \in Server} 
HistoryNodes == UNION {{e[1], e[2]} : e \in HistoryEdges}

\* Set of all paths in the history graph.
Paths == {p \in Seq(HistoryNodes) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in HistoryEdges}

\* Is there a path from config ci to cj in the history.
AreConnected(ci, cj) == \E p \in Paths : p[1] = ci /\ p[Len(p)] = cj

\* Gives a path from ci to cj. Assumes one exists.
Path(ci, cj) == CHOOSE p \in Paths : (p[1] = ci /\ p[Len(p)] = cj)

\* Takes a path and returns the set of edges in that path.
EdgesInPath(p) == {<<p[i],p[i+1]>> : i \in 1..(Len(p)-1)}

\* Is config ci an ancestor of cj.
Ancestor(ci, cj) == AreConnected(ci, cj)

\* Is config ci a descendant of cj.
Descendant(ci, cj) == AreConnected(cj, ci)

\* The parent node of 'c' in the log history. Assumes 'c' exists.
Parent(c) == CHOOSE par \in HistoryNodes : \E e \in HistoryEdges : e[1]=par /\ e[2]=c

\* Are nodes ci and cj siblings.
Siblings(ci, cj) == 
    /\ \E ca \in HistoryNodes : Ancestor(ca, ci) /\ Ancestor(ca, cj)
    /\ ~Ancestor(ci, cj)
    /\ ~Ancestor(cj, ci)

\* The set of all nodes that are ancestors of both 'ci' and 'cj'.
CommonAncestors(ci, cj) ==
    {c \in HistoryNodes : 
        /\ Ancestor(c, ci) 
        /\ Ancestor(c, cj)}

\* The newest common ancestor between two nodes, assumed to be siblings.
NewestCommonAncestor(ci, cj) ==
    LET cancestors == CommonAncestors(ci, cj) IN
    CHOOSE cai \in cancestors : \A caj \in cancestors : IndTermGTE(cai, caj)

\* Returns the set of update edges in the given path 'p'.
UpdateEdges(p) == {e \in EdgesInPath(p) : IsUpdateEdge(e)}

\* Returns the number of update edges in the given path 'p'.
NUpdateEdges(p) == Cardinality(UpdateEdges(p))

\* The number of update edges between two sibling nodes, which is defined as the sum of the 
\* distance from their common ancestor to each node.
SiblingUpdateDist(c1, c2) == 
    LET nca == NewestCommonAncestor(c1, c2) IN 
    NUpdateEdges(Path(nca, c1)) + NUpdateEdges(Path(nca, c2))

\* For two sibling nodes separated by >= 2 reconfig edges, one of them must be committed.
SiblingBranchSafety == 
    \A c1,c2 \in HistoryNodes :
    Siblings(c1,c2) => 
    ((SiblingUpdateDist(c1,c2) >= 2) => 
        (EntryCommitted(c1) \/ EntryCommitted(c2)))

\* If a log entry e exists and was created via an update edge, 
\* then its parent in the log history must be committed.
UpdateEdgeMustBeCommitted == 
    \A e \in HistoryEdges : IsUpdateEdge(e) => EntryCommitted(e[1])

\*
\* Refinement definitions.
\*

THEOREM Spec => MWR!Spec
THEOREM Spec => MSWR!Spec

RefinesMongoWeakRaft == MWR!Spec
RefinesMongoSafeWeakRaft == MSWR!Spec

====