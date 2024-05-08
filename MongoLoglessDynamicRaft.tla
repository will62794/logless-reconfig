---- MODULE MongoLoglessDynamicRaft ----
\*
\* Logless protocol for managing configuration state for dynamic reconfiguration
\* in MongoDB replication.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Defs

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE configVersion
VARIABLE configTerm
VARIABLE config

vars == <<currentTerm, state, configVersion, configTerm, config>>

\*
\* Helper operators.
\*

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
    
\* A quorum of servers in the config of server i have i's config.
ConfigQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : 
        /\ configVersion[t] = configVersion[i]
        /\ configTerm[t] = configTerm[i]

\* A quorum of servers in the config of server i have the term of i.
TermQuorumCheck(i) ==
    \E Q \in Quorums(config[i]) : \A t \in Q : currentTerm[t] = currentTerm[i]    

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

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in config[i]
    /\ i \in voteQuorum
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
\* Ported over directly from mldr3.tla:
\* https://github.com/egolf-cs/tla-synthesis/blob/3aa5a99182112187129a947aaa0434f007d48263/tool_and_experimentation/run_tool/proofs/mldr3.tla#L267-L282
Reconfig(i, newConfig) ==
    /\ state[i] = Primary \* gt: state[i] = Primary
    /\ ConfigQuorumCheck(i) \* gt: ConfigQuorumCheck(i)
    /\ TermQuorumCheck(i) \* gt: TermQuorumCheck(i)
    /\ QuorumsOverlap(config[i], newConfig) \* gt: QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig \* gt: i \in newConfig
    /\ newConfig # config[i] \* gt: newConfig # config[i]
    \* /\ (configVersion[i] < newVersion) \* gt: newVersion = configVersion[i] + 1
    /\ configTerm' = configTerm \* gt: [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ \E newVersion \in Nat : (configVersion[i] < newVersion) /\ configVersion' = [configVersion EXCEPT ![i] = newVersion] \* gt: [configVersion EXCEPT ![i] = newVersion]
    /\ config' = [config EXCEPT ![i] = newConfig] \* gt: [config EXCEPT ![i] = newConfig]
    /\ currentTerm' = currentTerm \* gt: currentTerm
    /\ state' = state \* gt: state

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<currentTerm, state>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ \E initConfig \in SUBSET Server :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]

Next ==
    \/ \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
    \/ \E s,t \in Server : SendConfig(s, t)
    \/ \E i \in Server : \E Q \in Quorums(config[i]) :  BecomeLeader(i, Q)
    \/ \E s,t \in Server : UpdateTerms(s,t)

Spec == Init /\ [][Next]_vars

=============================================================================