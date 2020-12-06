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

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

osmVars == <<log, elections, committed>>
csmVars == <<configVersion, configTerm, config>>

\* The config state machine.
CSM == INSTANCE MongoLoglessDynamicRaft 
        WITH currentTerm <- currentTerm,
             state <- state,
             configVersion <- configVersion,
             configTerm <- configTerm,
             config <- config,
             MaxLogLen <- MaxLogLen,
             MaxTerm <- MaxTerm,
             MaxConfigVersion <- MaxConfigVersion

\* The oplog state machine.
OSM == INSTANCE MongoStaticRaft 
        WITH currentTerm <- currentTerm,
             state <- state,
             log <- log,
             config <- config,
             elections <- elections,
             committed <- committed,
             MaxLogLen <- MaxLogLen,
             MaxTerm <- MaxTerm,
             MaxConfigVersion <- MaxConfigVersion
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

\* Config State Machine actions.
CSMNext == 
    \/ \E s \in Server, newConfig \in SUBSET Server : 
        \* Before allowing a Reconfig, we must also ensure that any previously committed ops
        \* are now committed by a quorum of the current configuration.
        /\ \A c \in committed : \E Q \in QuorumsAt(s) : OSM!MWR!ImmediatelyCommitted(c.entry, Q)
        /\ CSM!Reconfig(s, newConfig)
    \/ \E s,t \in Server : CSM!SendConfig(s, t)

\* Actions shared by the CSM and OSM i.e. that must be executed jointly by both protocols.
JointNext == 
     \E i \in Server : \E Q \in Quorums(config[i]) : 
        /\ OSM!BecomeLeader(i, Q)
        /\ CSM!BecomeLeader(i, Q)

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

ElectionSafety == \A x,y \in Server : 
    (/\ (state[x] = Primary) /\ (state[y] = Primary) 
     /\  currentTerm[x] = currentTerm[y]) => (x = y)

StateMachineSafety == OSM!StateMachineSafety

THEOREM MongoRaftReconfigSafety == Spec => StateMachineSafety

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

ServerSymmetry == Permutations(Server)

=============================================================================
