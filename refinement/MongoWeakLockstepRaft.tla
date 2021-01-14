---- MODULE MongoWeakLockstepRaft ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE config

VARIABLE elections
VARIABLE committed

MWR == INSTANCE MongoWeakRaft 
    WITH Server <- Server,
         Secondary <- Secondary,
         Primary <- Primary,
         Nil <- Nil,
         currentTerm <- currentTerm,
         state <- state,
         config <- config,
         elections <- elections,
         committed <- committed

\* Is the last log entry of node 'i' currently committed.
LastIsCommitted(i) == 
    \/ Len(log[i]) = 0 \* consider an empty log as being committed.
    \/ /\ Len(log[i]) > 0
       /\ \E c \in committed : 
            c.entry = <<Len(log[i]), log[i][Len(log[i])].term>>

Init == MWR!Init
Next == 
    \* Strengthen the client request precondition so that the current entry must be committed.
    \/ \E s \in Server : LastIsCommitted(s) /\ MWR!ClientRequest(s)
    \/ \E s, t \in Server : MWR!GetEntries(s, t)
    \/ \E s, t \in Server : MWR!RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in MWR!QuorumsAt(s) : MWR!BecomeLeader(s, Q)
    \/ \E s \in Server : MWR!CommitEntry(s)
    \* TODO: Might want to allow this to change synchronously with any other action.
    \/ \E s \in Server : MWR!ChangeConfig(s)

Spec == Init /\ [][Next]_(MWR!vars)

ElectionSafety == MWR!ElectionSafety
QuorumInvariant == MWR!QuorumInvariant

RefinementProperty == MWR!Spec

THEOREM Spec => MWR!Spec

StateConstraint == MWR!StateConstraint

====