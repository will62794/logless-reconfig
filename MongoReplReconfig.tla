----------------------------- MODULE MongoReplReconfig -----------------------------
(***************************************************************************)
(*                                                                         *)
(* A specification of the logless, dynamic reconfiguration protocol in     *)
(* MongoDB replication.                                                    *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Randomization

\* The set of server IDs.
CONSTANTS Server

\* Server states.
CONSTANTS Secondary, Primary

\* An empty value.
CONSTANTS Nil

(***************************************************************************)
(* Replication related variables.                                          *)
(***************************************************************************)

\* The server's term number.
VARIABLE currentTerm

\* The server's current state.
VARIABLE state

serverVars == <<currentTerm, state>>

\* A node's sequence of log entries. 
\* The index into the sequence is the index of the log entry.
VARIABLE log

(***************************************************************************)
(* Reconfiguration related variables.                                      *)
(***************************************************************************)

\* A server's current config. 
\* A config is just a set of servers i.e. an element of SUBSET Server
VARIABLE config

\* The config version of a node's current config.
VARIABLE configVersion

\* The term in which the current config on a node was written in i.e. the term of the primary
\* that moved to that config.
VARIABLE configTerm

configVars == <<config, configVersion, configTerm>>

(***************************************************************************)
(* Auxiliary variables.                                                    *)
(***************************************************************************)

\* Set of all immediately committed entries. 
\* Each element of the set is a record e.g. [index |-> ..., term |-> ..., configVersion |-> ...]
\* This set does not include "prefix committed" entries.
VARIABLE immediatelyCommitted

vars == <<serverVars, log, immediatelyCommitted, config, configVersion, configTerm>>

-------------------------------------------------------------------------------------------

SeqOf(set, n) == 
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

BoundedSeq(S, n) ==
  (***************************************************************************)
  (* An alias for SeqOf to make the connection to Sequences!Seq, which is    *)
  (* the unbounded version of BoundedSeq.                                    *)
  (***************************************************************************)
  SeqOf(S, n)

\* TODO: Add TypeOK invariant.
TypeOK == 
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq([term  : Nat])]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    /\ immediatelyCommitted \in (SUBSET [index : Nat, term : Nat, configVersion: Nat])

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

MajorityOnlyQuorums(S) == {i \in SUBSET(S) :
    /\ Cardinality(i) * 2 > Cardinality(S)
    /\ Cardinality(i) * 2 <= Cardinality(S) + 2}

\* The set of all quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] >= configVersion[j]
       
\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteFor(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    \* Nodes can only vote once per term, and they will never
    \* vote for someone with a lesser term than their own.
    /\ currentTerm[i] < term
    \* Only vote for someone if their config version is >= your own.
    /\ IsNewerConfig(j, i)
    /\ logOk
    
\* A quorum of nodes have received this config.
ConfigQuorumCheck(self, s) == /\ configVersion[self] = configVersion[s]
                              /\ configTerm[self] = configTerm[s]

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Next state actions.                                                     *)
(*                                                                         *)
(* This section defines the core steps of the algorithm, along with some   *)
(* related helper definitions/operators.  We annotate the main actions     *)
(* with an [ACTION] specifier to disinguish them from auxiliary, helper    *)
(* operators.                                                              *)
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
                            /\ UNCHANGED <<log, immediatelyCommitted, configVars>>
(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* Node 'i' rolls back against the log of node 'j'.                        *)
(***************************************************************************)
RollbackEntries(i, j) ==
    /\ CanRollback(i, j)
    /\ j \in config[i]
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<immediatelyCommitted, configVars>>

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* Node 'i' gets a new log entry from node 'j'.                            *)
(***************************************************************************)
GetEntries(i, j) ==
    /\ j \in config[i]
    /\ state[i] = Secondary
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
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<immediatelyCommitted, configVars>>

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* A leader i commits its newest log entry.  It commits it according to    *)
(* its own config's notion of a quorum.                                    *)
(***************************************************************************)
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
        /\ immediatelyCommitted' = immediatelyCommitted \cup
             {[index |->ind, term |-> currentTerm[i], configVersion |-> configVersion[i]]}
        /\ UNCHANGED <<serverVars, log, configVars>>

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* Node 'i' automatically becomes a leader, if eligible.                   *)
(***************************************************************************)
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
        \* Update config's term on step-up.
        /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
        /\ UNCHANGED <<log, config, configVersion, immediatelyCommitted>>

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* Node 'i', a primary, handles a new client request and places the entry  *)
(* in its log.                                                             *)
(***************************************************************************)
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i]]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, immediatelyCommitted, configVars>>

\* Was an op was committed in the current config of node i.
\* OpCommittedInConfig(i) == ENABLED CommitEntry(i)

\* TODO: Fill in this definition correctly.
OpCommittedInConfig(i) == TRUE

\* Did a node talked to a quorum as primary.
TermQuorumCheck(self, s) == currentTerm[self] >= currentTerm[s]

\* Is the config on node i currently "safe".
ConfigIsSafe(i) ==
    /\ \E q \in Quorums(config[i]):
       \A s \in q : /\ TermQuorumCheck(i, s)
                    /\ ConfigQuorumCheck(i, s)
    /\ OpCommittedInConfig(i)

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* A reconfig occurs on node i. The node must currently be a leader.       *)
(***************************************************************************)
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
        /\ \* Increment the local config version. Here we do not assume that config versions
           \* are globally unique.
            LET newConfigVersion == configVersion[i] + 1 IN
            configVersion' = [configVersion EXCEPT ![i] = newConfigVersion]
        /\ UNCHANGED <<serverVars, log, immediatelyCommitted>>

(***************************************************************************)
(* [ACTION]                                                                *)
(*                                                                         *)
(* Node i sends its current config to node j.  It is only accepted if the  *)
(* config is newer.                                                        *)
(***************************************************************************)
SendConfig(i, j) ==
    /\ state[j] = Secondary
    \* Only update config if the received config is newer and its term is >= than your current term.
    /\ IsNewerConfig(i, j)
    \* Commenting out the line below allows receipt of configs with terms lower than your current term.
    \* /\ configTerm[i] >= currentTerm[j]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<log, immediatelyCommitted>>

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Miscellaneous properties for exploring/understanding the spec.          *)
(***************************************************************************)

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

(***************************************************************************)
(* Correctness Properties                                                  *)
(***************************************************************************)

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) ==
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

\* There should be at most one leader per term.
TwoPrimariesInSameTerm ==
    \E i, j \in Server :
        /\ i # j
        /\ currentTerm[i] = currentTerm[j]
        /\ state[i] = Primary
        /\ state[j] = Primary

NoTwoPrimariesInSameTerm == ~TwoPrimariesInSameTerm
ElectionSafety == NoTwoPrimariesInSameTerm

ConfigVersionIncreasesWithTerm ==
    ~(\E i, j \in Server :
        /\ i # j
        /\ configVersion[i] > configVersion[j]
        /\ configTerm[i] < configTerm[j]
    )

\* Only uncommitted entries are allowed to be deleted from logs.
RollbackCommitted == \E s \in Server :
                     \E e \in immediatelyCommitted :
                        /\ EntryInLog(log[s], e.index, e.term)
                        \* And the entry got rolled back.
                        /\ Len(log'[s]) < e.index

NeverRollbackCommitted == [][~RollbackCommitted]_vars

\* At any time, some node can always become a leader.
ElectableNodeExists == \E s \in Server : ENABLED BecomeLeader(s)

\* The set of all currently installed configs in the system.
InstalledConfigs == Range(config)

\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* Is a given config "active" i.e. can it form a quorum.
ActiveConfig(cfg) == \E Q \in Quorums(cfg) : \A s \in Q : config[s] = cfg

\* The set of all active configs.
ActiveConfigs == {c \in InstalledConfigs : ActiveConfig(c)}

\* For all installed configs, do their quorums overlap.
InstalledConfigsOverlap == \A x,y \in InstalledConfigs : QuorumsOverlap(x, y)

\* For all active configs, do their quorums overlap.
ActiveConfigsOverlap == \A x,y \in ActiveConfigs : QuorumsOverlap(x, y)

\* Property asserting that there is never more than 1 active config at a time.
AtMostOneActiveConfig == Cardinality(ActiveConfigs) <= 1

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
ConfigEventuallyPropagates ==
    \A i, j \in Server:
        i \in config[j] ~> \/ i \notin config[j]
                           \/ configVersion[i] = configVersion[j]

ElectableNodeEventuallyExists == <>(\E s \in Server : state[s] = Primary)

(***************************************************************************)
(* Spec definition                                                         *)
(***************************************************************************)
InitConfigConstraint(c) == TRUE
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
        /\ InitConfigConstraint(initConfig)
        /\ config = [i \in Server |-> initConfig]
    /\ configVersion =  [i \in Server |-> 0]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ immediatelyCommitted = {}

BecomeLeaderAction      ==  \E s \in Server : BecomeLeader(s)
ClientRequestAction     ==  \E s \in Server : ClientRequest(s)
GetEntriesAction        ==  \E s, t \in Server : GetEntries(s, t)
RollbackEntriesAction   ==  \E s, t \in Server : RollbackEntries(s, t)
ReconfigAction          ==  \E s \in Server : Reconfig(s)
SendConfigAction        ==  \E s,t \in Server : SendConfig(s, t)
CommitEntryAction       ==  \E s \in Server : CommitEntry(s)
UpdateTermsAction       ==  \E s, t \in Server : UpdateTermsOnNodes(s, t)

Next ==
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ ReconfigAction
    \/ SendConfigAction
\*    \/ CommitEntryAction
    \/ UpdateTermsAction

Liveness ==
    /\ WF_vars(BecomeLeaderAction)
    /\ WF_vars(SendConfigAction)
    /\ WF_vars(UpdateTermsAction)
    /\ WF_vars(GetEntriesAction)
    /\ WF_vars(RollbackEntriesAction)
    /\ WF_vars(CommitEntryAction)

Spec == Init /\ [][Next]_vars /\ Liveness

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

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(4, [Server -> Nat])
    /\ state \in RandomSubset(4, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(4, [Server -> Seq([term  : Nat])])
\*    /\ config \in [Server -> {Server}] \* used this for checking election safety without reconfiguration
    /\ config \in RandomSubset(4, [Server -> SUBSET Server])
    /\ configVersion \in RandomSubset(4, [Server -> Nat])
    /\ configTerm \in RandomSubset(4, [Server -> Nat])
    /\ immediatelyCommitted = {}

\* Inductive invariant for proving election safety.
\* TODO: More work to expand this to handle safety under reconfigurations.
ElectionSafetyInd == 
    /\ ElectionSafety
    /\ \A s \in Server : 
        ((state[s] = Primary) => 
        \* A quorum should have voted for you, so are in your term or greater.
        /\ (\E voters \in Quorums(config[s]) : 
            (\A v \in voters : currentTerm[v] >= currentTerm[s]))
        \* Primary's current config term must be equal to its current term.
        /\ configTerm[s] = currentTerm[s])
    
    
IndInv == ElectionSafetyInd
IInit == TypeOKRandom /\ IndInv
INext == Next


=============================================================================
