---- MODULE MongoStaticRaft ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE config

VARIABLE elections
VARIABLE committed

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

\* \* The set of all quorums of a given set.
\* Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
\* QuorumsAt(i) == Quorums(config[i])

\* \* Can node 'i' currently cast a vote for node 'j' in term 'term'.
\* CanVoteForOplog(i, j, term) ==
\*     LET logOk ==
\*         \/ LastTerm(log[j]) > LastTerm(log[i])
\*         \/ /\ LastTerm(log[j]) = LastTerm(log[i])
\*            /\ Len(log[j]) >= Len(log[i]) IN
\*     /\ currentTerm[i] < term
\*     /\ logOk

    
\* \* Do all quorums of set x and set y share at least one overlapping node.
\* QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* -------------------------------------------------------------------------------------------

\* BecomeLeaderOplog(i, voteQuorum) == 
\*     \* Primaries make decisions based on their current configuration.
\*     LET newTerm == currentTerm[i] + 1 IN
\*     /\ i \in voteQuorum \* The new leader should vote for itself.
\*     /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
\*     \* Update the terms of each voter.
\*     /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
\*     /\ state' = [s \in Server |->
\*                     IF s = i THEN Primary
\*                     ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
\*                     ELSE state[s]]
\*     \* Update config's term on step-up.
\*     /\ UNCHANGED <<log>>    

\* For model checking.
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

Init ==
    /\ MWR!Init 
    \* All nodes have a fixed config, which is the set of all nodes.
    /\ \A s \in Server : config[s] = Server 

Next == 
    /\ MWR!Next
    \* We do not allow configs to be changed in the static protocol.
    /\ \A s \in Server : config'[s] = config[s]

Spec == Init /\ [][Next]_MWR!vars

ElectionSafety == MWR!ElectionSafety
StateMachineSafety == MWR!StateMachineSafety

THEOREM MongoStaticRaftSafety == Spec => StateMachineSafety

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.                                                *)
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

=============================================================================