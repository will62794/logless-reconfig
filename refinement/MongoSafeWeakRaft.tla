---- MODULE MongoSafeWeakRaft ----
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


\* Electable node 's' in quorum 'q' overlaps with some node that contains term of election, for all previous elections.
QC_1(s, Q) == MWR!Electable(s, Q) => \A e \in elections : \E t \in Q : currentTerm[t] >= e.term 

\* Electable node 's' i quorum 'q' overlaps with some node containing entry E, for all committed entries E.
QC_2(s, Q) == MWR!Electable(s, Q) => \A c \in committed : \E t \in Q : MWR!InLog(c.entry, t)

\* Commitable write by node 's' in quorum 'q' overlaps with some node that contains term of election, for all previous elections. 
QC_3(s, Q) == ENABLED MWR!CommitEntry(s, Q) => (\A e \in elections : \E t \in Q : currentTerm[t] >= e.term)

\*
\* This is the abstract condition necessary for a Raft protocol to operate "safely" without
\* reliance on quorum overlaps.
\*
WeakQuorumCondition ==
    \A s \in Server :
    \A Q \in MWR!QuorumsAt(s) : 
        /\ QC_1(s, Q)
        /\ QC_2(s, Q)
        /\ QC_3(s, Q)

\* We define the state machine predicates for this protocol, though we specify the protocol more abstractly
\* below. This state machine characterization should be equivalent to the temporal logic characterization,
\* but the temporal logic version is slightly clearer to specify and understand.
Init == MWR!Init /\ WeakQuorumCondition
Next == MWR!Next /\ WeakQuorumCondition'

\*
\* This protocol behaves the same as the "weak" protocol, except that it satisfies the weak quorum
\* condition at every step.
\*
Spec == MWR!Spec /\ []WeakQuorumCondition

THEOREM MongoSafeWeakRaftSafety == Spec => []MWR!StateMachineSafety

\*
\* Refinement definitions.
\*

THEOREM Spec => MWR!Spec

RefinesMongoWeakRaft == MWR!Spec

\*
\* Correctness property definitions.
\*

\* Is log entry e=<<i,t>> committed.
EntryCommitted(e) == \E c \in committed : c.entry = e

\* Is log entry e=<<i,t>> committed. (shorter definition)
Committed(e) == EntryCommitted(e)

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

\* Is an edge 'e' an update edge i.e. both nodes have the same term.
IsUpdateEdge(e) == e[1][2] = e[2][2]

\* Is an edge 'e' an election edge i.e. the nodes have different terms.
IsElectionEdge(e) == e[1][2] # e[2][2]

\* Returns the set of update edges in the given path 'p'.
UpdateEdges(p) == {e \in EdgesInPath(p) : IsUpdateEdge(e)}

\* Returns the number of update edges in the given path 'p'.
NUpdateEdges(p) == Cardinality(UpdateEdges(p))

\* If an entry C1 is committed on one branch, then no other entry on the other branch can be committed,
\* and all entries on the other branch must be in a lower term.
CommittedEntryImpliesLesserSiblingTerms == 
    \A c1,c2 \in HistoryNodes :
    (Committed(c1) /\ Siblings(c1, c2)) => c2[2] < c1[2]

--------------

====