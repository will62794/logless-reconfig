----------------------------- MODULE LoglessReconfig -----------------------------
(***************************************************************************)
(*                                                                         *)
(* Specification of a logless, dynamic reconfiguration protocol for Raft   *)
(* based replication systems.                                              *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

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

VARIABLE elections

\* Records every reconfig state transition and the current and new config.
VARIABLE reconfigs

vars == <<serverVars, log, immediatelyCommitted, config, configVersion, configTerm, elections, reconfigs>>

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Define type correctness.                                                *)
(***************************************************************************)

ElectionType == [ leader : Server, 
                  term   : Nat, 
                  voters : SUBSET Server,
                  config : SUBSET Server,
                  configVersion : Nat,
                  configTerm    : Nat]

ElectionsType == SUBSET ElectionType

\* Store a pair of configs as (members,version term) records.
ReconfigType == [ old : [m : SUBSET Server, v : Nat, t : Nat],
                  new : [m : SUBSET Server, v : Nat, t : Nat]]

ReconfigsType == SUBSET ReconfigType

TypeOK == 
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq([term : Nat])]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    /\ immediatelyCommitted \in (SUBSET [index : Nat, term : Nat, configVersion: Nat])
    /\ elections \in ElectionsType
    /\ reconfigs \in ReconfigsType

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

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
\*ConfigQuorumCheck(self, s) == /\ configVersion[self] = configVersion[s]
\*                              /\ configTerm[self] = configTerm[s]

ConfigQuorumCheck(self, s) == 
    \* Equal configs.
    \/ (/\ configVersion[self] = configVersion[s]
        /\ configTerm[self] = configTerm[s])
    \/ IsNewerConfig(s, self)

\* Helper for saving reconfigs into a history variable.
RecordReconfig(rc) == reconfigs \cup {rc} 

\* Helper for saving elections into a history variable.
RecordElection(e) == elections \cup {e} 

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
                            /\ UNCHANGED <<log, immediatelyCommitted, configVars, elections, reconfigs>>

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
    /\ UNCHANGED <<immediatelyCommitted, configVars, elections, reconfigs>>

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
    /\ UNCHANGED <<immediatelyCommitted, configVars, elections, reconfigs>>

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
        /\ UNCHANGED <<serverVars, log, configVars, elections, reconfigs>>

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
        \* Record the election.
        /\ LET electionRec == [ leader |-> i, 
                                term   |-> newTerm, 
                                voters |-> voteQuorum,
                                config |-> [m |-> config[i], v |-> configVersion[i], t |-> configTerm[i]]] IN
           elections' = RecordElection(electionRec)
        /\ LET reconfigRec == [ old |-> [m |-> config[i], v |-> configVersion[i], t |-> configTerm[i]],
                                new |-> [m |-> config[i], v |-> configVersion[i], t |-> newTerm]] IN
               reconfigs' = RecordReconfig(reconfigRec) 
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
    /\ UNCHANGED <<serverVars, immediatelyCommitted, configVars, elections, reconfigs>>

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
        /\ LET reconfigRec == [ old |-> [m |-> config[i], v |-> configVersion[i], t |-> configTerm[i]],
                                new |-> [m |-> newConfig, v |-> configVersion[i]+1, t |-> currentTerm[i]]] IN
               reconfigs' = RecordReconfig(reconfigRec)
        /\ UNCHANGED <<serverVars, log, immediatelyCommitted, elections>>

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
    /\ UNCHANGED <<log, immediatelyCommitted, elections, reconfigs>>

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Auxiliary definitions and properties for analyzing correctness.         *)
(***************************************************************************)

\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* Can one config ever have more than one parent?
UniqueParentConfig == 
    ~\E rc1, rc2 \in reconfigs:
        \* New configs are both the same.
        /\ <<rc1.new.v, rc1.new.t>> = <<rc2.new.v, rc2.new.t>>
        \* Different old configs.
        /\ <<rc1.old.v, rc1.old.t>> # <<rc2.old.v, rc2.old.t>>

\* Set of all configs that have ever existed in the history.
AllHistoryConfigs == UNION { {rc.old, rc.new} : rc \in reconfigs}
        
ChildConfig(c1, c2) == 
    \E rc \in reconfigs : rc = [old |-> c1, new |-> c2]   

ChildrenConfigs(c) == {child \in AllHistoryConfigs : ChildConfig(c, child)}

\* The set of all configs in the history that have more than one child.
BranchPointConfigs == 
    {c \in AllHistoryConfigs : Cardinality(ChildrenConfigs(c)) > 1}

\* Set of all paths in the history graph.
Paths == {p \in Seq(AllHistoryConfigs) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : [old |-> p[i], new |-> p[i+1]] \in reconfigs}

\* Is there a path from config ci to cj in the history.
Path(ci, cj) == \E p \in Paths : p[1] = ci /\ p[Len(p)] = cj

\* Is config ci an ancestor of cj.
Ancestor(ci, cj) == Path(ci, cj)

\* Is config ci a descendant of cj.
Descendant(ci, cj) == Path(cj, ci)

\* Is config ci a sibling of cj i.e. are they on different branches with a common
\* ancestor.
Sibling(ci, cj) == 
    /\ \E a \in AllHistoryConfigs : Ancestor(a, ci) /\ Ancestor(a, cj)
    /\ ~Ancestor(ci, cj)
    /\ ~Ancestor(cj, ci)

Siblings(c) == {cfg \in AllHistoryConfigs : Sibling(cfg, c)}

\* A config C with term T is committed if a quorum of nodes in C have installed 
\* C or a newer config and every node in the quorum has current term equal to T. 
Committed(c) == 
    \E quorum \in Quorums(c.m) : 
    \A s \in quorum : 
        /\ NewerOrEqualConfig(<<configVersion[s], configTerm[s]>>,<<c.v,c.t>>)
        \* The current term of the node's is equal to the term of the primary that
        \* created the config.
        /\ currentTerm[s] = c.t
 
\* A config is deactivated if it is prevented from holding elections now or in the future.
\* That is, no quorum in the config could hold a successful election.
Deactivated(c) == 
    \A Q \in Quorums(c.m) : 
    \E s \in Q : 
        NewerConfig(<<configVersion[s],configTerm[s]>>, <<c.v,c.t>>)

\* Two primaries cannot be elected in the same term if one of their configs
\* is an ancestor of the other.
SinglePathElectionSafety == 
    \A e1, e2 \in elections :
        (/\ e1.term = e2.term
         /\ Ancestor(e1.config, e2.config)) => e1.leader # e2.leader
        
\* Once a config on a branch has committed, all sibling branhes are deactivated
\* and new sibling branches cannot be created.
CommittedBranchDeactivatesSiblings == 
    \A c \in AllHistoryConfigs : 
        Committed(c) => (\A s \in Siblings(c) : Deactivated(s))
   
\* At any branch point, at most one branch can contain a committed config.
AtMostOneCommittedConfigPerBranch == 
    \A b, ci, cj \in AllHistoryConfigs :
        \* If a config 'b' has two descendants that are both committed, then they 
        \* must be on the same branch.
        (/\ Descendant(b, ci) 
         /\ Descendant(b, cj)
         /\ Committed(ci) 
         /\ Committed(cj)) => ~Sibling(ci, cj)

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) ==
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

\* At any time, some node can always become a leader.
ElectableNodeExists == \E s \in Server : ENABLED BecomeLeader(s)

-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

ElectionSafety == 
    \A e1, e2 \in elections : 
        (e1.term = e2.term) => (e1.leader = e2.leader)

\* Only uncommitted entries are allowed to be deleted from logs.
RollbackCommitted == \E s \in Server :
                     \E e \in immediatelyCommitted :
                        /\ EntryInLog(log[s], e.index, e.term)
                        \* And the entry got rolled back.
                        /\ Len(log'[s]) < e.index

NeverRollbackCommitted == [][~RollbackCommitted]_vars


(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
ConfigEventuallyPropagates ==
    \A i, j \in Server:
        i \in config[j] ~> \/ i \notin config[j]
                           \/ configVersion[i] = configVersion[j]

ElectableNodeEventuallyExists == <>(\E s \in Server : state[s] = Primary)

-------------------------------------------------------------------------------------------

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
    /\ elections = {}
    /\ reconfigs = {}

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

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm
LogLenInvariant ==  \A s \in Server  : Len(log[s]) <= MaxLogLen

=============================================================================
