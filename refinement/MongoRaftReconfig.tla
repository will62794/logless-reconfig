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

serverVars == <<currentTerm, state, log>>
configVars == <<configVersion, configTerm, config>>
vars == <<serverVars, configVersion, configTerm, config, log>>

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

osmVars == <<log>>
csmVars == <<configVersion, configTerm, config>>

\* The config state machine.
CSM == INSTANCE MongoDynamicRaft 
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
             MaxLogLen <- MaxLogLen,
             MaxTerm <- MaxTerm,
             MaxConfigVersion <- MaxConfigVersion
\*
\* This protocol is specified as a composition of a Config State Machine (which
\* runs MongoDynamicRaft) and an Oplog State Machine (which runs
\* MongoStaticRaft). The composition is asynchronous except for the election
\* action i.e. both protocols need to execute their election action
\* simultaneously.
\*
Init == 
    /\ CSM!Init 
    /\ OSM!Init

Next == 
    \/ (OSM!Next /\ UNCHANGED csmVars)
    \/ (CSM!Next /\ UNCHANGED osmVars)
    \* Synchronized election action that must be executed by both state machines jointly.
    \/ \E s \in Server : \E Q \in Quorums(config[s]) : 
        /\ CSM!BecomeLeaderConfig(s, Q)
        /\ OSM!BecomeLeaderOplog(s, Q)

Spec == Init /\ [][Next]_vars

ElectionSafety == \A x,y \in Server : 
    (/\ (state[x] = Primary) /\ (state[y] = Primary) 
     /\  currentTerm[x] = currentTerm[y]) => (x = y)

\* TODO: Fill in.
StateMachineSafety == TRUE

THEOREM MongoRaftReconfigSafety == Spec => StateMachineSafety

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

=============================================================================
