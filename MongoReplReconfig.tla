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

\* A history variable. This would not be present in an
\* implementation. Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable. This would not be present in an implementation. Keeps track of every log ever 
\* in the system (set of logs).
VARIABLE allLogs

\* Set of all immediately committed <<index, term>> log entry pairs.
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

\* The set of terms each server has voted in, if any.
VARIABLE votedFor

serverVars == <<currentTerm, state, votedFor>>

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

leaderVars == <<elections>>

vars == <<allLogs, serverVars, leaderVars, log, immediatelyCommitted, config, configVersion>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Generic helper operators                                                                       *)
(**************************************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
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
    /\ currentTerm[i] <= term
    /\ term \notin votedFor[i]
    \* you can only vote for someone with the same config version as you.
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
    /\ UNCHANGED <<votedFor, leaderVars, config, configVersion, immediatelyCommitted>>
       
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' gets a new log entry from node 'j'.                               *)
(******************************************************************************)
GetEntries(i, j) == 
    /\ j \in config[i]
    /\ state[i] = Secondary
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
    /\ UNCHANGED <<votedFor, leaderVars, config, configVersion, immediatelyCommitted>>   
    
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
        /\ votedFor' = [s \in Server |-> IF s \in voteQuorum THEN votedFor[s] \cup {newTerm} ELSE votedFor[s]]
        /\ state' = [s \in Server |-> 
                        IF s = i THEN Primary
                        ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                        ELSE state[s]] 
        /\ LET election == [eterm     |-> newTerm,
                            eleader   |-> i,
                            elog      |-> log[i],
                            evotes    |-> voteQuorum] IN
           elections'  = elections \cup {election}        
        /\ UNCHANGED <<log, config, configVersion, immediatelyCommitted>>         



\* A quorum of nodes have received this config or a newer one.
ConfigQuorumCheck(i) == 
    \E quorum \in Quorums(config[i]) : \A s \in quorum : configVersion[s] >= configVersion[i]

\* Was an op was committed in the config of node i.
OpCommittedInConfig(i) ==
    /\ \E e \in immediatelyCommitted : e[3] = configVersion[i]

\* Did a node talked to a quorum as primary.
TermQuorumCheck(i) ==
    /\ \A q \in Quorums(config[i]) :
       \A s \in q : currentTerm[i] >= currentTerm[s]

\* Is the config on node i currently "safe".
ConfigIsSafe(i) ==
    /\ TRUE \* a 'null' check i.e. always passes.
    /\ ConfigQuorumCheck(i)
    /\ OpCommittedInConfig(i)
    /\ TermQuorumCheck(i)

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
        /\ \* Pick a config version higher than all existing config versions.
            LET newConfigVersion == Max(Range(configVersion)) + 1 IN
            configVersion' = [configVersion EXCEPT ![i] = newConfigVersion]
        /\ UNCHANGED <<serverVars, leaderVars, log, immediatelyCommitted>>         

\* Node i sends its current config to node j. It is only accepted if the config version is newer.
SendConfig(i, j) == 
    /\ configVersion[j] < configVersion[i]
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    \* Update terms of sender and receiver i.e. to simulate an RPC request and response (heartbeat).
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* May update state of sender or receiver.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j],
                              ![i] = IF currentTerm[i] < currentTerm[j] THEN Secondary ELSE state[i] ]
    /\ UNCHANGED <<votedFor, leaderVars, log, immediatelyCommitted>>         

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
        /\ UNCHANGED <<serverVars, leaderVars, log, config, configVersion>>              
        
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
    /\ UNCHANGED <<serverVars, leaderVars, config, configVersion, immediatelyCommitted>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)

\* If a node is currently primary and learns about a higher term, and it is not the leader
\* of this newer term, then it must step down.
NodesStepDown == \A s \in Server : 
    /\ state[s] = Primary
    /\ currentTerm'[s] > currentTerm[s]
    /\ ~(\E elec \in elections' : elec.eterm = currentTerm'[s] /\ elec.eleader = s) =>
        state'[s] = Secondary \* make sure the node stepped down.

NodesStepDownProperty == [][NodesStepDown]_vars

\* Are there two primaries in the current state.
TwoPrimaries == \E s, t \in Server : s # t /\ state[s] = Primary /\ state[s] = state[t]

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* The set of all log entries (<<index, term>>) that appear in any log in the given log set.
AllLogEntries(logSet) == UNION {LogEntries(l) : l \in logSet}      

\* Determines whether an <<index, term>> entry is immediately committed, based on the
\* current state. Be careful to note that the value of this expression only depends on the current state, not the 
\* history of states. A particular entry may be immediately committed in the current state,
\* but not immediately committed in the next state.
ImmediatelyCommitted(index, term) == 
    \E Q \in Quorum :
        \A q \in Q : 
            /\ currentTerm[q] = term 
            /\ EntryInLog(log[q], index, term)

\* The set of all immediately committed log entries in the current state. An entry is committed
\* at a particular term t, so we store the entry itself along with the term at which it was committed. 
\* In general, the "commitment term" doesn't need to match the term of the entry itself, although for 
\* immediately committed entries, it will. It may not for prefix committed entries, though.
AllImmediatelyCommitted == 
    LET entries == {e \in AllLogEntries(Range(log)) : ImmediatelyCommitted(e[1], e[2])} IN
    {[entry |-> e, term |-> e[2]] : e \in entries}

\* The set of prefix committed entries.
PrefixCommittedEntries == 
    {e \in AllLogEntries(Range(log)) :
        \E l \in Range(log) : 
            /\ EntryInLog(l, e[1], e[2])
            /\ \E c \in LogEntries(l) :
                /\ c[1] > e[1]
                /\ \E x \in immediatelyCommitted : c = x.entry}

\* The set of prefix committed entries along with the term they were committed in.
PrefixCommittedEntriesWithTerm == 
    {   LET commitmentTerm == CHOOSE t \in 1..10 : 
            \E l \in Range(log) :
                /\ EntryInLog(l, e[1], e[2])
                /\ \E c \in LogEntries(l) :
                    /\ c[1] > e[1]
                    /\ [entry |-> c, term |-> t] \in immediatelyCommitted IN
         [entry |-> e, term |-> commitmentTerm]
        : e \in PrefixCommittedEntries}

\* The set of all committed log entries up to the current state. Note that this definition depends
\* on a history variable, 'immediatelyCommitted'. That history variable is constructed by appending the
\* immediately committed entries at every state to a set. So, at any one state, it should store the complete
\* set of entries that were ever immediately committed. Some entries may never be immediately committed and will
\* only get "prefix committed". 
CommittedEntries == immediatelyCommitted \cup PrefixCommittedEntriesWithTerm

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) == 
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

(**************************************************************************************************)
(* There should be at most one leader per term.                                                   *)
(**************************************************************************************************)
ElectionSafety == \A e1, e2 \in elections: 
                    e1.eterm = e2.eterm => e1.eleader = e2.eleader

(**************************************************************************************************)
(* An <<index, term>> pair should uniquely identify a log prefix.                                 *)
(**************************************************************************************************)
LogMatching == 
    \A xlog, ylog \in allLogs : 
    Len(xlog) <= Len(ylog) =>
    \A i \in DOMAIN xlog : 
        xlog[i].term = ylog[i].term => 
        SubSeq(xlog, 1, i) = SubSeq(ylog, 1, i)
       
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


(**************************************************************************************************)
(* If an entry was committed, then it must appear in the logs of all leaders of higher terms.     *)
(**************************************************************************************************)
LeaderCompleteness == 
 \A e \in CommittedEntries :
 \A election \in elections:
    LET index == e.entry[1] 
        term == e.entry[2] IN
    election.eterm > e.term => EntryInLog(election.elog, index, term)

\*
\* Liveness Properties (Experimental)
\*

\* Eventually all servers store the same logs forever. This should only be true 
\* in the absence of new client requests, but if the maximum log length of 
\* servers is limited in a model, then logs should eventually converge, since new client
\* requests will eventually be disallowed.
EventuallyLogsConverge == <>[][\A s, t \in Server : s # t => log[s] = log[t]]_vars

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Spec definition                                                                                *)
(**************************************************************************************************)
 
Init == 
    \* Server variables.
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    \*/\ votedFor    = [i \in Server |-> Nil]
    \* The set of terms that each node has voted in, if any. Every node can only vote 'yes' once in a given term.
    /\ votedFor    = [i \in Server |-> {}]
    \* Log variables.
    /\ log          = [i \in Server |-> << >>]
    \* Reconfig variables.
    \* Initially, all nodes start out with the same view of the config, which includes
    \* all nodes.
    /\ config =         [i \in Server |-> Server]
    /\ configVersion =  [i \in Server |-> 0]
    \* History variables
    /\ elections = {}
    /\ allLogs   = {log[i] : i \in Server}
    /\ immediatelyCommitted = {}
    
\* Next state predicate for history variables. We (unfortunately) add it to every next-state disjunct
\* instead of adding it as a conjunct with the entire next-state relation because it makes for clearer TLC 
\* Toolbox error traces i.e. we can see what specific action was executed at each step of the trace. 
HistNext == 
    /\ allLogs' = allLogs \cup {log[i] : i \in Server}
\*    /\ immediatelyCommitted' = immediatelyCommitted \cup AllImmediatelyCommitted'
\*    /\ immediatelyCommitted' = immediatelyCommitted 


BecomeLeaderAction      ==  \E s \in Server : BecomeLeader(s)                           /\ HistNext
ClientRequestAction     ==  \E s \in Server : ClientRequest(s)                          /\ HistNext
GetEntriesAction        ==  \E s, t \in Server : GetEntries(s, t)                       /\ HistNext
RollbackEntriesAction   ==  \E s, t \in Server : RollbackEntries(s, t)                  /\ HistNext
ReconfigAction          ==  \E s \in Server : Reconfig(s)                               /\ HistNext
SendConfigAction        ==  \E s,t \in Server : SendConfig(s, t)                        /\ HistNext
CommitEntryAction       ==  \E s \in Server : CommitEntry(s)                            /\ HistNext
  
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
\* Last modified Fri Nov 08 18:39:34 EST 2019 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
