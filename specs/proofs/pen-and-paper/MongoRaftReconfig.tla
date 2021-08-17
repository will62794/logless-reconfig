----------------------------- MODULE MongoRaftReconfig -----------------------------

\*
\* MongoDB replication protocol that allows for logless, dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Json

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE log
VARIABLE committed
VARIABLE currentTerm
VARIABLE state
VARIABLE config
VARIABLE configVersion
VARIABLE configTerm

VARIABLE elections

VARIABLE configHistory

vars == <<currentTerm, state, log, configVersion, configTerm, config, log, elections, committed, configHistory>>

\*
\* Helper operators.
\*

\* The set of all quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

QuorumsAt(i) == Quorums(config[i])

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

-------------------------------------------------------------------------------------------

CONSTANT MaxTerm,MaxConfigVersion,MaxLogLen

osmVars == <<log, elections, committed>>
csmVars == <<configVersion, configTerm, config, configHistory>>

\* The config state machine.
CSM == INSTANCE MongoLoglessDynamicRaft 
        WITH currentTerm <- currentTerm,
             state <- state,
             configVersion <- configVersion,
             configTerm <- configTerm,
             config <- config,
             CheckConfigCycles <- FALSE,
             MaxTerm <- MaxTerm,
             MaxConfigVersion <- MaxConfigVersion,
             configHistory <- configHistory

\* The oplog state machine.
OSM == INSTANCE MongoStaticRaft 
        WITH currentTerm <- currentTerm,
             state <- state,
             log <- log,
             config <- config,
             elections <- elections,
             committed <- committed
             
\*
\* This protocol is specified as a composition of a Config State Machine (which
\* runs MongoLoglessDynamicRaft) and an Oplog State Machine (which runs
\* MongoStaticRaft). The composition is asynchronous except for the election
\* action i.e. both protocols need to execute their election action
\* simultaneously.
\*
Init == 
    /\ CSM!Init 
    /\ OSM!Init

\* Oplog State Machine actions.
OSMNext == 
    \/ \E s \in Server : OSM!ClientRequest(s)
    \/ \E s, t \in Server : OSM!GetEntries(s, t)
    \/ \E s, t \in Server : OSM!RollbackEntries(s, t)
    \/ \E s \in Server :  \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)

\* Check whether the entry at "index" on "primary" is committed in the primary's current config.
IsCommitted(index, primary) ==
    \* The primary must contain such an entry.
    /\ Len(log[primary]) >= index
    \* The entry was written by this leader.
    /\ LogTerm(primary, index) = currentTerm[primary]
    /\ \E quorum \in Quorums(config[primary]):
        \* all nodes have this log entry and are in the term of the leader.
        \A s \in quorum : \E k \in DOMAIN log[s] :
            /\ k = index
            /\ log[s][k] = log[primary][k]    \* they have the entry.
            /\ currentTerm[s] = currentTerm[primary]  \* they are in the same term.

\*
\* This is the precondition about committed oplog entries that must be satisfied
\* on a primary server s in order for it to execute a reconfiguration.
\*
\* When a primary is first elected in term T, we can be sure that it contains
\* all committed entries from terms < T. During its reign as primary in term T
\* though, it needs to make sure that any entries it commits in its own term are
\* correctly transferred to new configurations. That is, before leaving a
\* configuration C, it must make sure that any entry it committed in T is now
\* committed by the rules of configuration C i.e. it is "immediately committed"
\* in C. That is, present on some quorum of servers in C that are in term T. 
OplogCommitment(s) == 
    \* The primary has at least committed one entry in its term if there are any
    \* entries committed in earlier terms.
    /\ committed = {} \/ \E c \in committed : IsCommitted(c.entry[1], s)
    \* All entries committed in the primary's term have been committed in the
    \* current config.
    /\ \A c \in committed : (c.term = currentTerm[s]) => IsCommitted(c.entry[1], s)

\* Config State Machine actions.
CSMNext == 
    \/ \E s \in Server, newConfig \in SUBSET Server : 
        \* Before reconfiguration, ensure that previously committed ops are safe.
        \* /\ OplogCommitment(s)
        /\ CSM!Reconfig(s, newConfig)
    \/ \E s,t \in Server : CSM!SendConfig(s, t)

JointBecomeLeader(i, Q) == 
    /\ OSM!BecomeLeader(i, Q)
    /\ CSM!BecomeLeader(i, Q)
        
\* Actions shared by the CSM and OSM i.e. that must be executed jointly by both protocols.
JointNext == 
    \/ \E i \in Server : \E Q \in Quorums(config[i]) : 
        /\ OSM!BecomeLeader(i, Q)
        /\ CSM!BecomeLeader(i, Q)
    \/ \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)

\* We define the transition relation as an interleaving composition of the OSM and CSM.
\* From the current state, we permit either the OSM or CSM to take a single,
\* non election step. Election steps (i.e. BecomeLeader) actions in either
\* state machine must synchronize i.e. they must be executed simultaneously
\* in both sub protocols.
Next == 
    \/ OSMNext /\ UNCHANGED csmVars
    \/ CSMNext /\ UNCHANGED osmVars
    \/ JointNext

ReconfigAction == 
    /\ \E s \in Server, newConfig \in SUBSET Server : 
        \* Before reconfiguration, ensure that previously committed ops are safe.
        /\ OplogCommitment(s)
        /\ CSM!Reconfig(s, newConfig)
    /\ UNCHANGED osmVars

SendConfigAction == 
    /\ \E s,t \in Server : CSM!SendConfig(s, t)
    /\ UNCHANGED osmVars
    
BecomeLeaderAction ==
    \/ \E i \in Server : \E Q \in Quorums(config[i]) : 
        /\ OSM!BecomeLeader(i, Q)
        /\ CSM!BecomeLeader(i, Q)

UpdateTermsAction == \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)

ClientRequestAction == 
    /\ \E s \in Server : OSM!ClientRequest(s)
    /\ UNCHANGED csmVars

GetEntriesAction == 
    /\ \E s, t \in Server : OSM!GetEntries(s, t)
    /\ UNCHANGED csmVars

RollbackEntries == 
    /\ \E s, t \in Server : OSM!RollbackEntries(s, t)
    /\ UNCHANGED csmVars

CommitEntryAction == 
    /\ \E s \in Server :  \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
    /\ UNCHANGED csmVars

\* Gives more informative error traces, with action names.
NextVerbose == 
    \* OSM
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntries
    \/ CommitEntryAction
    \* CSM
    \/ ReconfigAction
    \/ SendConfigAction
    \/ BecomeLeaderAction
    \/ UpdateTermsAction

Spec == Init /\ [][Next]_vars

\*
\* Correctness properties.
\*

ConfigTermsMonotonic == 
    [][\A s \in Server : configTerm'[s] >= configTerm[s]]_vars

CurrentTermGreaterOrEqualToConfigTerm ==
    \A s \in Server : currentTerm[s] >= configTerm[s]

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

StateMachineSafety == OSM!StateMachineSafety

OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c.term < currentTerm[s] => InLog(c.entry, s))

\*
\* Model checking stuff.
\*

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
                    /\ configVersion[s] <= MaxConfigVersion

ViewNoElections == <<currentTerm, state, log, configVersion, configTerm, config, log, committed>>

Symmetry == Permutations(Server)


-----------------------------------------------------------------------------

\*
\* DEBUGGING
\*

StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(log[s]) \o " " \o
    ToString(config[s]) \o " (" \o ToString(configVersion[s]) \o "," \o ToString(configTerm[s]) \o ")"

stateRecord == [
    log |-> log,
    currentTerm |-> currentTerm,
    state |-> state,
    committed |-> committed,
    config |-> config,
    configVersion |-> configVersion,
    configTerm |-> configTerm
]

ServerPair == Server \X Server
Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        \* elections |-> elections,
        \* config |-> config,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)],
        committed |-> committed,
        jsonstr |-> ToJson(stateRecord)
        \* activeConfigs |-> ActiveConfigSet,
        \* activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])],
        \* newestConfig |-> {<<config[s],CV(s)>> : s \in ServersInNewestConfig}
        \* configChains |-> [<<s,t>> \in ServerPair |-> ConfigChains(s,t)]
    ]


=============================================================================