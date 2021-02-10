---- MODULE MongoLoglessDynamicRaftAux ----
EXTENDS TLC, MongoLoglessDynamicRaft

\*
\* Auxiliary specification for defining the refinement mapping between MongoLoglessDynamicRaft
\* and MongoSafeWeakRaft. Defines the conceptual mapping between the "logless" protocol
\* and the "log-based" versions of the protocol e.g. MongoSafeWeakRaft.
\*

\* Auxiliary variables needed for the refinement mapping.
VARIABLE log
VARIABLE elections
VARIABLE committed

InitAux == 
    /\ Init
    /\ log = [s \in Server |-> <<>>] 
    /\ elections = {}
    /\ committed = {}

ReconfigAux == 
    \E s \in Server, newConfig \in SUBSET Server : 
        /\ Reconfig(s, newConfig) 
        /\ log' = [log EXCEPT ![s] = Append(log[s], currentTerm[s])]
        /\ UNCHANGED <<elections, committed>>

SendConfigAux == 
    \E s,t \in Server : 
        /\ SendConfig(s, t)
        /\ log' = [log EXCEPT ![t] = log[s]]
        /\ UNCHANGED <<elections, committed>>

BecomeLeaderAux == 
    \E i \in Server : \E Q \in Quorums(config[i]) :  
        /\ BecomeLeader(i, Q)
        /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i] + 1)]
        /\ elections' = elections \cup 
            {[ leader  |-> i, 
                term   |-> currentTerm[i] + 1 ]}
        /\ UNCHANGED <<committed>>  

CommitConfigAux == 
    \E s \in Server :
        /\ ConfigIsCommitted(s)
        /\ committed' = committed \cup 
            {[ entry  |-> <<Len(log[s]), configTerm[s]>>,
                term  |-> currentTerm[s]]}
        /\ UNCHANGED <<currentTerm, log, state, elections, config, configVersion, configTerm>>

\* Next state relation with auxiliary variables.
NextAux ==
    \/ ReconfigAux
    \/ SendConfigAux
    \/ BecomeLeaderAux
    \* Record commits explicitly to simulate the behavior of MongoSafeWeakRaft.
    \/ CommitConfigAux

MWR == INSTANCE MongoWeakRaft WITH 
        currentTerm <- currentTerm,
        state <- state,
        log <- log,
        config <- config,
        elections <- elections,
        committed <- committed

StateMachineSafety == MWR!StateMachineSafety
====