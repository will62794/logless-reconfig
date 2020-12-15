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

\* Re-defined locally for convenience.
ElectionSafety == MWR!ElectionSafety
LeaderCompleteness == MWR!LeaderCompleteness
StateMachineSafety == MWR!StateMachineSafety

\*
\* This is the abstract condition necessary for a Raft protocol to operate "safely" without
\* reliance on quorum overlaps.
\*
\*  (1) An electable node overlap with some node with term >=T for all elections that occurred in term T.
\*  (2) An electable must overlap with some node containing an entry E for all previously committed entries E.
\*  (3) A committable write must overlap with some node with term >=T for all elections that occurred in term T.
\*
WeakQuorumCondition ==
    \A s \in Server :
    \A quorum \in MWR!QuorumsAt(s) : 
        \* 1. Electable node overlaps with some node that contains term of election, for all previous elections.
        /\ MWR!Electable(s, quorum) => \A e \in elections : \E t \in quorum : currentTerm[t] >= e.term 
        \* 2. Electable node overlaps with some node containing entry E, for all committed entries E.
        /\ MWR!Electable(s, quorum) => \A c \in committed : \E t \in quorum : MWR!InLog(c.entry, t)
        \* 3. Commitable write overlaps with some node that contains term of election, for all previous elections. 
        /\ ENABLED MWR!CommitEntry(s, quorum) => (\A e \in elections : \E t \in quorum : currentTerm[t] >= e.term)

\*
\* This protocol behaves the same as the "weak" protocol, except that it satisfies the weak quorum
\* condition at every step. Note that it is valid in TLA+ to write the following formula:
\*      
\*  Init /\ [][MWR!Next]_vars /\ []WeakQuorumCondition
\* 
\* but the TLC  model checker will not interpret it correctly, so we insert the condition into
\* the initial and transition predicate directly to maintain the condition at every step.
\*

Init == MWR!Init /\ WeakQuorumCondition
Next == MWR!Next /\ WeakQuorumCondition'

Spec == Init /\ [][Next]_vars

THEOREM MongoSafeWeakRaftSafety == Spec => []StateMachineSafety

\*
\* Refinement definitions.
\*

THEOREM Spec => MWR!Spec

RefinesMongoWeakRaft == MWR!Spec

--------------

\* Used for model checking only.

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

====