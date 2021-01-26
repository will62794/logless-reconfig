---- MODULE MongoLoglessDynamicRaft ----
\* The logless, dynamic Raft protocol for reconfiguration.

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config

serverVars == <<currentTerm, state>>
configVars == <<configVersion, configTerm, config>>
vars == <<serverVars, configVersion, configTerm, config>>

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

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] > configVersion[j]

IsNewerOrEqualConfig(i, j) ==
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] = configVersion[j]
    \/ IsNewerConfig(i, j)

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerConfig(ci, cj) ==
    \* Compare configTerm first.
    \/ ci[2] > cj[2] 
    \* Compare configVersion if terms are equal.
    \/ /\ ci[2] = cj[2]
       /\ ci[1] > cj[1]  

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerOrEqualConfig(ci, cj) == NewerConfig(ci, cj) \/ ci = cj

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForConfig(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerOrEqualConfig(j, i)
    
\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* Is the current config on primary s committed. A config C=(v, t) can be committed on 
\* a primary in term T iff t=T and there are a quorum of nodes in term T that currently
\* have config C.
ConfigIsCommitted(s) == 
    /\ state[s] = Primary
    \* Config must be in the term of this primary.
    /\ configTerm[s] = currentTerm[s]
    /\ \E Q \in QuorumsAt(s) : 
        \A t \in Q : 
            \* Node must have the same config as the primary.
            /\ configVersion[s] = configVersion[t]
            /\ configTerm[s] = configTerm[t]
            \* Node must be in the same term as the primary (and the config).
            /\ currentTerm[t] = currentTerm[s]

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Next state actions.                                                     *)
(***************************************************************************)

\* Exchange terms between two nodes and step down the primary if needed.
UpdateTerms(i, j) ==
    \* Update terms of sender and receiver i.e. to simulate an RPC request and response (heartbeat).
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* May update state of sender or receiver.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j],
                              ![i] = IF currentTerm[i] < currentTerm[j] THEN Secondary ELSE state[i] ]

UpdateTermsOnNodes(i, j) == /\ UpdateTerms(i, j)
                            /\ UNCHANGED <<configVars>>

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in config[i] \* only become a leader if you are a part of your config.
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForConfig(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    \* Update config's term on step-up.
    /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<config, configVersion>>    

\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    (* PRE *)
    /\ state[i] = Primary
    /\ ConfigIsCommitted(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig
    (* POST *)
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state>>

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    (* PRE *)
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    (* POST *)
    \* TODO: Is this required for safety, and why or why not? Perhaps separate it into a separate
    \* communication channel.
    /\ UpdateTerms(i, j) 
    \* /\ UNCHANGED <<currentTerm, state>>
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]


csmVars == <<configVersion, configTerm, config>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ configVersion =  [i \in Server |-> 0]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ \E initConfig \in SUBSET Server :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]

Next ==
    \/ \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
    \/ \E s,t \in Server : SendConfig(s, t)
    \/ \E i \in Server : \E Q \in Quorums(config[i]) :  BecomeLeader(i, Q)

Spec == Init /\ [][Next]_vars

ElectionSafety == \A x,y \in Server : 
    (/\ (state[x] = Primary) /\ (state[y] = Primary) 
     /\  currentTerm[x] = currentTerm[y]) => (x = y)


\* TODO: Refinement mapping here needs auxiliary variables in this spec.
\*
\* Auxiliary variables.
\* VARIABLE log
\* VARIABLE configLog
\*
\* MDR == INSTANCE MongoDynamicRaft 
\*     WITH MaxTerm <- MaxTerm,
\*          MaxLogLen <- MaxLogLen,
\*          MaxConfigVersion <- MaxConfigVersion,
\*          Server <- Server,
\*          Secondary <- Secondary,
\*          Primary <- Primary,
\*          Nil <- Nil,
\*          currentTerm <- currentTerm,
\*          state <- state,
\*          config <- config,
\*          configLog <- \* ? need auxiliary variable.
\*          elections <- elections,
\*          committed <- committed

=============================================================================