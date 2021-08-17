---- MODULE MongoLoglessDynamicRaft ----
\*
\* Logless protocol for managing configuration state for dynamic reconfiguration
\* in MongoDB replication.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Json

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config

\* history variables for proof.
VARIABLE configHistory

vars == <<currentTerm, state, configVersion, configTerm, config, configHistory>>

\* Whether to check for config cycles during model checking via assert statements.
CONSTANT CheckConfigCycles

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


\* The current config of server 'i' is present on some quorum of nodes in that
\* config. This DISABLES any older configs that overlap with it.
ConfigQuorumCheck(i) == 
    \E Q \in Quorums(config[i]) : \A t \in Q : 
        /\ configVersion[t] = configVersion[i]
        /\ configTerm[t] = configTerm[i]

\* The current term of server 'i' is present on a quorum of servers in that
\* config. This protects the config and any that overlap with it from future
\* elections or commits in that term.
TermQuorumCheck(i) == \E Q \in Quorums(config[i]) : \A t \in Q : currentTerm[t] = currentTerm[i]      

ConfigIsCommittedAlt(i) ==

    /\ ConfigQuorumCheck(i)
    /\ TermQuorumCheck(i)
    /\ TRUE

    \* Goal 1: Disable older configs that overlap with you.
    \* The current config is present on some quorum of nodes in that config.
    \* This DISABLES any older configs that overlap with it
    \* /\ \E Q \in Quorums(config[i]) : \A t \in Q : 
    \*     /\ configVersion[t] = configVersion[i]
    \*     /\ configTerm[t] = configTerm[i]
        \* /\ currentTerm[t] = currentTerm[i]

    \* As written, this specification allows config propagation and term updates to 
    \* occur separately, so in addition to checking that the config has propagated to
    \* a quorum, we must also check an appropriate term condition. Specifically,
    \* we must define this in such a way that prevents older configs from satisfying this
    \* condition. 

    \* The terms from previous configs must have propagated to a quorum of this config.
    \* This DISABLES older configs that overlap with the config.
    \* /\ \E Q \in Quorums(config[i]) : \A t \in Q : 
        \* /\ currentTerm[t] = currentTerm[i]    
    

\* Set of all config nodes in the config history graph.
configHistoryNodes == UNION {{c[1], c[2]} : c \in configHistory}

-------------------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Update terms if node 'i' has a newer term than node 'j' and ensure 'j' reverts to Secondary state.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]

UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<configVersion, configTerm, config>>
    /\ UNCHANGED configHistory

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
    /\ LET oldCfg == [m |-> config[i], v |-> configVersion[i], t |-> configTerm[i]] 
           newCfg == [m |-> config[i], v |-> configVersion'[i], t |-> configTerm'[i]] IN
           /\ configHistory' = configHistory \cup {<< oldCfg, newCfg>>}
           \* Efficiently check for a cycle here i.e. are you adding an edge to a config that already exists?
           /\ Assert(~CheckConfigCycles \/ newCfg \notin configHistoryNodes, "cycle in config history detected")
    
\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    /\ state[i] = Primary
    \* /\ ConfigIsCommitted(i)
    /\ ConfigIsCommittedAlt(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state>>
    /\ LET  oldCfg == [m |-> config[i], v |-> configVersion[i], t |-> configTerm[i]] 
            newCfg == [m |-> newConfig, v |-> configVersion'[i], t |-> configTerm'[i]] IN
            /\ configHistory' = configHistory \cup {<< oldCfg, newCfg>>}
            \* Efficiently check for a cycle here i.e. are you adding an edge to a config that already exists?
            /\ Assert(~CheckConfigCycles \/ newCfg \notin configHistoryNodes, "cycle in config history detected")

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<currentTerm, state>>
    /\ UNCHANGED configHistory

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ \E initConfig \in SUBSET Server :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]
    /\ configHistory = {}

Next ==
    \/ \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
    \/ \E s,t \in Server : SendConfig(s, t)
    \/ \E i \in Server : \E Q \in Quorums(config[i]) :  BecomeLeader(i, Q)
    \/ \E s,t \in Server : UpdateTerms(s,t)

Spec == Init /\ [][Next]_vars

------------------------------------------

\*
\* Model checking stuff.
\*

CONSTANT MaxTerm,MaxConfigVersion
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

ServerSymmetry == Permutations(Server)

------------------------------------------

\*
\* Checking Proof Lemmas
\*

OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

ConfigHistoryUniqueParents == 
    /\ ~\E ei,ej \in configHistory : 
        /\ ei[1] # ej[1]
        /\ ei[2] = ej[2]

\* Sanity trace checking.
PrimaryExists == ~\E s,t \in Server : state[s] = Primary /\ state[t] = Primary /\ s#t

NotTwoReconfigEdgesLeavingSameConfig ==
    ~\E ei,ej \in configHistory :
        \* Leaving the same node.
        /\ ei[1] = ej[1]
        \* Going to different nodes.
        /\ ei[2] # ej[2]
        \* Both reconfig edges.
        /\ ei[1].t = ei[2].t
        /\ ej[1].t = ej[2].t

\*
\* DEBUGGING
\*

StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(config[s]) \o " (" \o ToString(configVersion[s]) \o "," \o ToString(configTerm[s]) \o ")"

\* TikZ drawings.

stateRecord == [
    currentTerm |-> currentTerm,
    state |-> state,
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
        jsonstr |-> ToJson(stateRecord)
        \* activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])],
        \* newestConfig |-> {<<config[s],CV(s)>> : s \in ServersInNewestConfig}
        \* configChains |-> [<<s,t>> \in ServerPair |-> ConfigChains(s,t)]
    ]

=============================================================================