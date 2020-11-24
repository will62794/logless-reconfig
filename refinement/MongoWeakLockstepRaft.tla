---- MODULE MongoWeakLockstepRaft ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

VARIABLE currentTerm
VARIABLE state
VARIABLE log

vars == <<currentTerm, state, log>>

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
         log <- log

\* Is the last log entry of node i currently committed.
LastIsCommitted(i) == 
    \/ Len(log[i]) = 0 \* consider an empty log as being committed.
    \/ \E quorum \in MWR!Quorums :
        /\ Len(log[i]) > 0
        \* This node is leader and its last entry was written by it.
        /\ state[i] = Primary
        /\ log[i][Len(log[i])].term = currentTerm[i]
        \* All nodes in quorum this log entry and are in the term of the leader.
        /\ \A j \in quorum :
           \E k \in DOMAIN log[j] : 
                /\ k = Len(log[i])
                /\ log[j][k] = log[i][Len(log[i])]        \* they have the entry.
                /\ currentTerm[j] = currentTerm[i]  \* they are in the same term.

Init == MWR!Init
Next == 
    \* Strengthen the client request precondition so that the current entry must be committed.
    \/ \E s \in Server : 
        /\ LastIsCommitted(s)
        /\ MWR!ClientRequest(s)
    \/ \E s, t \in Server : MWR!GetEntries(s, t)
    \/ \E s, t \in Server : MWR!RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in MWR!Quorums : MWR!BecomeLeader(s, Q)

Spec == Init /\ [][Next]_vars

RefinementProperty == MWR!Spec

THEOREM Spec => MWR!Spec

StateConstraint == MWR!StateConstraint

====