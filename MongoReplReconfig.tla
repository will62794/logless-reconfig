----------------------------- MODULE MongoReplReconfig -----------------------------
(**************************************************************************************************)
(* A high level specification of the MongoDB replication protocol, which is based on the Raft     *)
(* consensus protocol.                                                                            *)
(*                                                                                                *)
(* This spec models the system at a high level of abstraction.  For example, we do not explicitly *)
(* model the network or the exchange of messages between nodes.  Instead, we model the system so  *)
(* as to make it clear what the essential invariants to be upheld are.                            *)
(**************************************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Secondary, Candidate, Primary

\* A reserved value.
CONSTANTS Nil

(**************************************************************************************************)
(* Global variables                                                                               *)
(**************************************************************************************************)

\* Set of all immediately committed <<index, term, configVersion>> log entry pairs.
VARIABLE immediatelyCommitted

(**************************************************************************************************)
(* Per server variables.                                                                          *)
(*                                                                                                *)
(* These are all functions with domain Server.                                                    *)
(**************************************************************************************************)

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

serverVars == <<currentTerm, state>>

\* A sequence of log entries. The index into this sequence is the index of the
\* log entry
VARIABLE log

\*
\* Reconfig related variables.
\*

\* A server's current config. A config is just a set of servers 
\* i.e. an element of SUBSET Server
VARIABLE config

\* The config version of a node's current config.
VARIABLE configVersion

\* The term in which the current config on a node was written in i.e. the term of the primary
\* that moved to that config.
VARIABLE configTerm

vars == <<serverVars, log, immediatelyCommitted, config, configVersion, configTerm>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Generic helper operators                                                                       *)
(**************************************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
MajorityOnlyQuorums(S) == {i \in SUBSET(S) :
    /\ Cardinality(i) * 2 > Cardinality(S)
    /\ Cardinality(i) * 2 <= Cardinality(S) + 2}
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
    
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

-------------------------------------------------------------------------------------------

(******************************************************************************)
(* Next state actions.                                                        *)
(*                                                                            *)
(* This section defines the core steps of the algorithm, along with some      *)
(* related helper definitions/operators.  We annotate the main actions with   *)
(* an [ACTION] specifier to disinguish them from auxiliary, helper operators. *)
(******************************************************************************)    

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteFor(i, j, term) == 
    LET logOk == 
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    \* Nodes can only vote once per term, and they will never 
    \* vote for someone with a lesser term than their own.
    /\ currentTerm[i] < term
    \* you can only vote for someone with the same config version as you.
    \* TODO: Only vote for someone if their config version is >= your own.
    /\ configVersion[i] = configVersion[j]
    /\ logOk

\* Is it possible for log 'lj' to roll back based on the log 'li'. If this is true, it implies that
\* log 'lj' should remove entries to become a prefix of 'li'.
CanRollback(li, lj) == 
    /\ Len(li) > 0 
    /\ Len(lj) > 0
    \* The terms of the last entries of each log do not match. The term of node i's last 
    \* log entry is greater than that of node j's.
    /\ li[Len(li)].term > lj[Len(lj)].term

\* Returns the highest common index between two divergent logs, 'li' and 'lj'. 
\* If there is no common index between the logs, returns 0.
RollbackCommonPoint(li, lj) == 
    LET commonIndices == {k \in DOMAIN li : 
                            /\ k <= Len(lj)
                            /\ li[k] = lj[k]} IN
        IF commonIndices = {} THEN 0 ELSE Max(commonIndices)  
                                                       
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'j' removes entries based against the log of node 'i'.                *)
(******************************************************************************)
RollbackEntries(i, j) == 
    /\ CanRollback(log[i], log[j])
    /\ i \in config[j]
    /\ configVersion[i] = configVersion[j]    
    /\ LET commonPoint == RollbackCommonPoint(log[i], log[j]) IN
           \* If there is no common entry between log 'i' and
           \* log 'j', then it means that the all entries of log 'j'
           \* are divergent, and so we erase its entire log. Otherwise
           \* we erase all log entries after the newest common entry. Note that 
           \* if the commonPoint is '0' then SubSeq(log[i], 1, 0) will evaluate
           \* to <<>>, the empty sequence.
           log' = [log EXCEPT ![j] = SubSeq(log[i], 1, commonPoint)] 
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* Step down remote node if it's term is smaller than yours.                                      
    /\ state' = [state EXCEPT ![i] = IF currentTerm[i] < currentTerm[j] THEN Secondary ELSE state[i],
                              ![j] = Secondary] 
    /\ UNCHANGED <<config, configVersion, immediatelyCommitted, configTerm>>
       
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' gets a new log entry from node 'j'.                               *)
(******************************************************************************)
GetEntries(i, j) == 
    /\ j \in config[i]
    /\ state[i] = Secondary
    \* TODO: Remove this restriction on checking config version when fetching log entries.
    /\ configVersion[i] = configVersion[j]
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at 
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i]) 
                        THEN TRUE  
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1 
              newEntry      == log[j][newEntryIndex] 
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* Step down remote node if it's term is smaller than yours.                                      
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j]]          
    /\ UNCHANGED <<config, configVersion, immediatelyCommitted, configTerm>>   
    
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' automatically becomes a leader, if eligible.                      *)
(******************************************************************************)
BecomeLeader(i) ==
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    \E voteQuorum \in Quorums(config[i]) :
        /\ i \in config[i] \* only become a leader if you are a part of your config.
        /\ i \in voteQuorum \* The new leader should vote for itself.
        /\ \A v \in voteQuorum : CanVoteFor(v, i, newTerm)
        \* Update the terms of each voter.
        /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
        /\ state' = [s \in Server |-> 
                        IF s = i THEN Primary
                        ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                        ELSE state[s]]
        /\ UNCHANGED <<log, config, configVersion, immediatelyCommitted, configTerm>>         



\* A quorum of nodes have received this config or a newer one.
ConfigQuorumCheck(self, s) == configVersion[self] <= configVersion[s]

\* Was an op was committed in the config of node i.
OpCommittedInConfig(i) ==
    /\ \E e \in immediatelyCommitted : e[3] = configVersion[i]

\* Did a node talked to a quorum as primary.
TermQuorumCheck(self, s) == currentTerm[self] >= currentTerm[s]

\* Is the config on node i currently "safe".
ConfigIsSafe(i) ==
    /\ \E q \in Quorums(config[i]):
       \A s \in q : /\ TermQuorumCheck(i, s)
                    /\ ConfigQuorumCheck(i, s)
    /\ OpCommittedInConfig(i)

\*
\* A reconfig occurs on node i. The node must currently be a leader.
\*
Reconfig(i) == 
    \* Pick some arbitrary subset of servers to reconfig to. 
    \* Make sure to include this node in the new config, though.
    \E newConfig \in SUBSET Server : 
        /\ state[i] = Primary
        \* Only allow a new config to be installed if the current config is "safe".
        /\ ConfigIsSafe(i)
        \* Add or remove a single node. (OPTIONALLY ENABLE)
        /\ \/ \E n \in newConfig : newConfig \ {n} = config[i]  \* add 1.
           \/ \E n \in config[i] : config[i] \ {n} = newConfig  \* remove 1.
        /\ i \in newConfig
        \* The config on this node takes effect immediately
        /\ config' = [config EXCEPT ![i] = newConfig]
        \* Record the term of the primary that wrote this config.
        /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
        /\ \* Pick a config version higher than all existing config versions.
            LET newConfigVersion == configVersion[i] + 1 IN
            configVersion' = [configVersion EXCEPT ![i] = newConfigVersion]
        /\ UNCHANGED <<serverVars, log, immediatelyCommitted>>

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) == 
    /\ configVersion[i] > configVersion[j]
    \* /\ currentTerm[i] >= currentTerm[j] \* shouldn't be necessary anymore with 'configTerm'.
    /\ configTerm[i] >= currentTerm[j]

\* Node i sends its current config to node j. It is only accepted if the config version is newer.
SendConfig(i, j) == 
    \* TODO: Only allow configs to propagate from a primary to a secondary.
    \* Only update config if the received config version is newer. We still allow this
    \* action to propagate terms, though, even if the config is not updated.
    /\ IsNewerConfig(i, j)
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    \* Update terms of sender and receiver i.e. to simulate an RPC request and response (heartbeat).
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* May update state of sender or receiver.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j],
                              ![i] = IF currentTerm[i] < currentTerm[j] THEN Secondary ELSE state[i] ]
    /\ UNCHANGED <<log, immediatelyCommitted>>

\* TODO: Re-propose your current config in term T in a higher term U if you have been elected in term U.
ReproposeConfig(i) == TRUE

\* A leader i commits its newest log entry. It commits it according to its own config's notion of a quorum.
CommitEntry(i) ==
    LET ind == Len(log[i]) IN
    \E quorum \in Quorums(config[i]) :
        \* Must have some entries to commit. 
        /\ ind > 0 
        \* This node is leader.
        /\ state[i] = Primary
        \* The entry was written by this leader.
        /\ log[i][ind].term = currentTerm[i]
        \* all nodes have this log entry and are in the term of the leader.
        /\ \A s \in quorum : 
            /\ Len(log[s]) >= ind
            /\ log[s][ind] = log[i][ind]        \* they have the entry.
            /\ currentTerm[s] = currentTerm[i]  \* they are in the same term.
        /\ immediatelyCommitted' = immediatelyCommitted \cup {<<ind, currentTerm[i], configVersion[i]>>}
        /\ UNCHANGED <<serverVars, log, config, configVersion, configTerm>>
        
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i', a primary, handles a new client request and places the entry in  *)
(* its log.                                                                   *)
(******************************************************************************)        
ClientRequest(i) == 
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i]]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, config, configVersion, immediatelyCommitted, configTerm>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)

\* Are there two primaries in the current state.
TwoPrimaries == \E s, t \in Server : s # t /\ state[s] = Primary /\ state[s] = state[t]

NPrimaries(n) == 
    \E prims \in SUBSET Server : 
        /\ \A s \in prims : state[s] = Primary 
        /\ Cardinality(prims) = n

\* Are there 'n' concurrent, differing configs active on some set of nodes in 
\* the current state.
NConcurrentConfigs(n) == 
    \E S \in SUBSET Server :  
        /\ Cardinality(S) = n
        /\ \A x, y \in S : x # y => config[x] # config[y]

2ConcurrentConfigs == ~NConcurrentConfigs(2)
3ConcurrentConfigs == ~NConcurrentConfigs(3)
4ConcurrentConfigs == ~NConcurrentConfigs(4)
5ConcurrentConfigs == ~NConcurrentConfigs(5)

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* The set of all log entries (<<index, term>>) that appear in any log in the given log set.
AllLogEntries(logSet) == UNION {LogEntries(l) : l \in logSet}      

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) == 
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

(**************************************************************************************************)
(* There should be at most one leader per term.                                                   *)
(**************************************************************************************************)
TwoPrimariesInSameTerm ==
    \E i, j \in Server :
        /\ i # j
        /\ currentTerm[i] = currentTerm[j]
        /\ state[i] = Primary
        /\ state[j] = Primary

NoTwoPrimariesInSameTerm == ~TwoPrimariesInSameTerm
ElectionSafety == NoTwoPrimariesInSameTerm

(**************************************************************************************************)
(* Only uncommitted entries are allowed to be deleted from logs.                                  *)
(**************************************************************************************************)

RollbackCommitted == \E s \in Server : 
                     \E e \in immediatelyCommitted :
                        LET index == e[1]
                            term  == e[2] IN
                        /\ EntryInLog(log[s], index, term)
                        \* And the entry got rolled back.
                        /\ Len(log'[s]) < index
                        
NeverRollbackCommitted == [][~RollbackCommitted]_vars

\* At any time, some node can always become a leader.
ElectableNodeExists == \E s \in Server : ENABLED BecomeLeader(s)

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Spec definition                                                                                *)
(**************************************************************************************************)
InitConfigConstriant(c) == TRUE
InitConfigMaxSizeOnly(c) == c = Server
Init == 
    \* Server variables.
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    \* The set of terms that each node has voted in, if any. Every node can only vote 'yes' once in a given term.
    \* Log variables.
    /\ log          = [i \in Server |-> << >>]
    \* Reconfig variables.
    \* Initially, all nodes start out with the same view of the config. 
    \* We allow an initial config to be any non-empty subset of the current servers.
    /\ \E initConfig \in (SUBSET Server) : 
        /\ initConfig # {}
        /\ InitConfigConstriant(initConfig)
        /\ config = [i \in Server |-> initConfig]
    /\ configVersion =  [i \in Server |-> 0]
    /\ configTerm    =  [i \in Server |-> 0]
    \* History variables
    /\ immediatelyCommitted = {}

BecomeLeaderAction      ==  \E s \in Server : BecomeLeader(s)         
ClientRequestAction     ==  \E s \in Server : ClientRequest(s)        
GetEntriesAction        ==  \E s, t \in Server : GetEntries(s, t)     
RollbackEntriesAction   ==  \E s, t \in Server : RollbackEntries(s, t)
ReconfigAction          ==  \E s \in Server : Reconfig(s)             
SendConfigAction        ==  \E s,t \in Server : SendConfig(s, t)      
CommitEntryAction       ==  \E s \in Server : CommitEntry(s)          
  
Next == 
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ ReconfigAction
    \/ SendConfigAction
    \/ CommitEntryAction

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* State Constraint. Used for model checking only.                                                *)
(**************************************************************************************************)

CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

StateConstraint == \A s \in Server : 
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
                    /\ configVersion[s] <= MaxConfigVersion
        
ServerSymmetry == Permutations(Server)

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm    
LogLenInvariant ==  \A s \in Server  : Len(log[s]) <= MaxLogLen    

=============================================================================
\* Modification History
\* Last modified Tue Nov 12 15:11:06 EST 2019 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
