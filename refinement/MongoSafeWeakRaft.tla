---- MODULE MongoSafeWeakRaft ----
EXTENDS Naturals, Sequences, TLC

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

--------------

====