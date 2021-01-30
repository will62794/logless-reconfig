----------------------------- MODULE MongoRaftReconfig -----------------------------

\*
\* MongoDB replication protocol that allows for logless, dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

(***************************************************************************)
(* Replication related variables.                                          *)
(***************************************************************************)

VARIABLE currentTerm
VARIABLE state
\* Oplog state machine.
VARIABLE log
\* Config state machine.
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config

VARIABLE elections
VARIABLE committed

serverVars == <<currentTerm, state, log>>
configVars == <<configVersion, configTerm, config>>
vars == <<serverVars, configVersion, configTerm, config, log, elections, committed>>

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

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


osmVars == <<log, elections, committed>>
csmVars == <<configVersion, configTerm, config>>

\* The config state machine.
CSM == INSTANCE MongoLoglessDynamicRaft 
        WITH currentTerm <- currentTerm,
             state <- state,
             configVersion <- configVersion,
             configTerm <- configTerm,
             config <- config

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
    \/ \E s \in Server :  \E Q \in OSM!MWR!QuorumsAt(s) : OSM!CommitEntry(s, Q)

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
        /\ OplogCommitment(s)
        /\ CSM!Reconfig(s, newConfig)
    \/ \E s,t \in Server : CSM!SendConfig(s, t)

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

Spec == Init /\ [][Next]_vars

ElectionSafety == OSM!ElectionSafety

StateMachineSafety == OSM!StateMachineSafety

LeaderCompleteness == OSM!MWR!LeaderCompleteness

\* If an election has occurred in term T, then no leader should be able to
\* commit writes in terms U < T. A sufficient condition to check this is to
\* ensure that, for all past elections E, any current primary P in a term <
\* E.term is deactivated from committing. 
\*
\* We can check for deactivation of a primary P in term U by checking that all
\* of its quorums contain some node V whose term is > U . This ensures that such
\* a primary could no longer commit writes now, or ever again in the future.
ElectionDisablesOldTerms == 
    \A e \in elections : 
    \A s \in Server : 
    (state[s] = Primary /\ currentTerm[s] < e.term) => 
        \A Q \in QuorumsAt(s) : 
        \E v \in Q : currentTerm[v] > currentTerm[s]
    

THEOREM MongoRaftReconfigSafety == Spec => StateMachineSafety

=============================================================================
