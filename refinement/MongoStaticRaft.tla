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

\* The core protocol actions of StaticRaft are the same as in WeakRaft. However,
\* we do not allow the config to be changed. The config for each node starts out as 
\* the set of all servers and is never modified.
ClientRequest(s) == MWR!ClientRequest(s)
GetEntries(s,t) == MWR!GetEntries(s,t)
RollbackEntries(s, t) == MWR!RollbackEntries(s, t)
BecomeLeader(s, Q) == MWR!BecomeLeader(s, Q)
CommitEntry(s, Q) == MWR!CommitEntry(s, Q)
UpdateTerms(s, t) == MWR!UpdateTerms(s, t)

Init == MWR!Init 

NextStatic == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in MWR!QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in MWR!QuorumsAt(s) : CommitEntry(s, Q)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Next == NextStatic /\ UNCHANGED config

Spec == Init /\ [][Next]_MWR!vars

ElectionSafety == MWR!ElectionSafety
StateMachineSafety == MWR!StateMachineSafety

FutureCommittedImpliesImmediatelyCommitted == MWR!FutureCommittedImpliesImmediatelyCommitted
ImmediatelyCommittedImpliesFutureCommitted == MWR!ImmediatelyCommittedImpliesFutureCommitted

THEOREM MongoStaticRaftSafety == Spec => StateMachineSafety

=============================================================================