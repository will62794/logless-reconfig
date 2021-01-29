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

\* This is the precondition on committed oplog entries that must be satisfied on
\* server s before it can execute a reconfiguration. All previously committed
\* oplog entries must be committed by the rules of the server's current
\* configuration. Since a primary can only commit entries in its own term, we
\* check whether all entries committed in this primary's term are now committed
\* on a quorum of its configuration. This should be sufficient to ensure all
\* previously committed entries are committed, since every primary contains all
\* committed ops in its log on becoming primary.
OplogCommitmentCond(s) == 
    \A c \in {n \in committed : n.term = currentTerm[s]} : 
        \E Q \in QuorumsAt(s) : 
        \A v \in Q : (OSM!MWR!InLog(c.entry, v) /\ currentTerm[v] = currentTerm[s])

\* Config State Machine actions.
CSMNext == 
    \/ \E s \in Server, newConfig \in SUBSET Server : 
        \* Before reconfiguration, ensure that previously committed ops are safe.
        /\ OplogCommitmentCond(s)
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
