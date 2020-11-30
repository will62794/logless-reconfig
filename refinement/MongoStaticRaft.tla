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

\* The core protocol actions of StaticRaft are the same as in WeakRaft. However,
\* we do not allow the config to be changed. The config for each node starts out as 
\* the set of all servers and is never modified.
ClientRequest(s) == MWR!ClientRequest(s)
GetEntries(s,t) == MWR!GetEntries(s,t)
RollbackEntries(s, t) == MWR!RollbackEntries(s, t)
BecomeLeader(s, Q) == MWR!BecomeLeader(s, Q)
CommitEntry(s, Q) == MWR!CommitEntry(s, Q)

Init ==
    /\ MWR!Init 
    \* All nodes have a fixed config, which is the set of all nodes.
    /\ \A s \in Server : config[s] = Server 

Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in MWR!QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in MWR!QuorumsAt(s) : CommitEntry(s, Q)

Spec == Init /\ [][Next]_MWR!vars

ElectionSafety == MWR!ElectionSafety
StateMachineSafety == MWR!StateMachineSafety

FutureCommittedImpliesImmediatelyCommitted == MWR!FutureCommittedImpliesImmediatelyCommitted
ImmediatelyCommittedImpliesFutureCommitted == MWR!ImmediatelyCommittedImpliesFutureCommitted

THEOREM MongoStaticRaftSafety == Spec => StateMachineSafety

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.                                                *)
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen


\* For easier error diagnosis
Alias == 
    [
        currentTerm |-> currentTerm,
        state |-> state,
        log |-> log,
        config |-> config,
        elections |-> elections,
        committed |-> committed,
        futureCommitted |-> {e \in MWR!LogEntriesAll : MWR!IsFutureCommitted(e)}
    ]

=============================================================================