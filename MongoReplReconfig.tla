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

\* The set of requests that can go into the log
CONSTANTS Value

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

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
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

(**************************************************************************************************)
(* Next state actions.                                                                            *)
(*                                                                                                *)
(* This section defines the core steps of the algorithm, along with some related helper           *)
(* definitions/operators.  We annotate the main actions with an [ACTION] specifier to disinguish  *)
(* them from auxiliary, helper operators.                                                         *)
(**************************************************************************************************)    

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteFor(i, j) == 
    LET logOk == 
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
\*    /\ currentTerm[i] <= currentTerm[j]
\*    /\ j # votedFor[i] 
    \* you can only vote for someone with the same config version as you.
    /\ configVersion[i] = configVersion[j]
    /\ logOk


\* Could server 'i' win an election in the current state.
IsElectable(i) == 
    LET voters == {s \in Server : CanVoteFor(s, i)} IN
        voters \in Quorum

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
                                                          
(**************************************************************************************************)
(* [ACTION]                                                                                       *)
(*                                                                                                *)
(* Node 'j' removes entries based against the log of node 'i'.                                    *)
(*                                                                                                *)
(* The rollback procedure used in this protocol is always executed by comparing the logs of two   *)
(* separate nodes.  By doing so, it is possible to determine if one node has a "divergent" log    *)
(* suffix, and thus has entries in its log that are uncommitted.  The essential idea is to see if *)
(* the last term of the entry of one log is less than the last term of the last entry of another  *)
(* log.  In this case, the log with the lesser last term should be considered eligible for        *)
(* rollback.  Note that the goal of this rollback procedure should be to truncate entries from a  *)
(* log that are both uncommitted, and also only truncate entries that it knows will NEVER become  *)
(* committed.  Of course, log entries that are written down by a primary before being replicated  *)
(* are clearly uncommitted, but deleting them wouldn't be sensible, since it is very possible     *)
(* those entries WILL become committed in the future.                                             *)
(**************************************************************************************************)
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
       
(**************************************************************************************************)
(* [ACTION]                                                                                       *)
(*                                                                                                *)
(* Node 'i' gets a new log entry from node 'j'.                                                   *)
(*                                                                                                *)
(* Note that there are only a few restrictions made about the sender and receiver of this log     *)
(* transferral.  Only secondaries fetch new logs by this means, but we allow them to get entries  *)
(* from any other node, regardless of whether they are a secondary or a primary.  We only         *)
(* stipulate that the sending node actually has a longer log than the receiver and that the log   *)
(* consistency check passes.  In other words, the receiver's log must be a prefix of the sender's *)
(* log, at the time entries are sent.                                                             *)
(**************************************************************************************************)
GetEntries(i, j) == 
\*  /\ currentTerm[j] >= currentTerm[i] \* (OPTIONAL, doesn't affect safety?)
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
    
(**************************************************************************************************)
(* [ACTION]                                                                                       *)
(*                                                                                                *)
(* Node 'i' automatically becomes a leader, if eligible.                                          *)
(*                                                                                                *)
(* We model an election as one atomic step.  Normally this would occur in multiple steps i.e.     *)
(* sending out vote requests to nodes and waiting for responses.  We simplify this process by     *)
(* simply checking if a node can become leader and then updating its state and the state of a     *)
(* quorum of nodes who voted for it appropriately, as if a full election has occurred.            *)
(**************************************************************************************************)
BecomeLeader(i) ==
    \* Primaries make decisions based on their current configuration.
    \E voteQuorum \in Quorums(config[i]) :
        /\ i \in config[i] \* only become a leader if you are a part of your config.
        /\ i \in voteQuorum \* The new leader should vote for itself.
        /\ \A v \in voteQuorum : 
            /\ CanVoteFor(v, i)
            \* Updating your term and casting your vote in that term are atomic in this spec,
            \* so there's no possible way you could be in term T but not have voted yet in term T.
            /\ currentTerm[i] + 1 > currentTerm[v]
        \* Update the terms of each voter.
        /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN currentTerm[i]+1 ELSE currentTerm[s]]
        /\ votedFor' = votedFor
        /\ state' = [s \in Server |-> 
                        IF s = i THEN Primary
                        ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                        ELSE state[s]] 
        /\ LET election == [eterm     |-> currentTerm[i]+1,
                            eleader   |-> i,
                            elog      |-> log[i],
                            evotes    |-> voteQuorum] IN
           elections'  = elections \cup {election}        
        /\ UNCHANGED <<log, config, configVersion, immediatelyCommitted>>         

\* Is the config on node i currently "safe".
ConfigIsSafe(i) ==
    \* a quorum of nodes have received this config or a newer one.
    /\ \E quorum \in Quorums(config[i]) : \A s \in quorum : configVersion[s] >= configVersion[i]
    \* require this node to have communicated with a quorum of the config i.e. to propagate term.
    \* if this node communicated with a quorum, then there must be some quorum such that
    \* all nodes have the same terms as i. 
    /\ \E q \in Quorums(config[i]) : 
       \A s \in q : 
        /\ currentTerm[i] = currentTerm[s] 
        /\ i \in q
    

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
        /\ \/ Cardinality(config[i]) + 1 = Cardinality(newConfig) 
           \/ Cardinality(config[i]) - 1 = Cardinality(newConfig) 
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
    \* Update the term of the receiver.
    /\ currentTerm' = [currentTerm EXCEPT ![j] = Max({currentTerm[i], currentTerm[j]})]
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j]]
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
        /\ immediatelyCommitted' = immediatelyCommitted \cup {<<ind, currentTerm[i]>>}
        /\ UNCHANGED <<serverVars, leaderVars, log, config, configVersion>>              
        
(**************************************************************************************************)
(* [ACTION]                                                                                       *)
(*                                                                                                *)
(* Node 'i', a primary, handles a new client request and places the entry in its log.             *)
(**************************************************************************************************)        
ClientRequest(i, v) == 
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, leaderVars, config, configVersion, immediatelyCommitted>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)

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

\* If two logs have the same last log entry term, then one is a prefix of the other. (Will is trying to see if 
\* this is actually true).
LastTermsEquivalentImplyPrefixes == 
    \A xlog, ylog \in allLogs :
        LastTerm(xlog) = LastTerm(ylog) =>
        IsPrefix(xlog, ylog) \/ IsPrefix(ylog, xlog)


(**************************************************************************************************)
(* The terms of every server increase monotonically.                                              *)
(*                                                                                                *)
(* We express this as an 'action' property.  That is, it depends on the both primed and unprimed  *)
(* variables.                                                                                     *)
(**************************************************************************************************)
TermsMonotonic == 
    [][\A s \in Server : currentTerm'[s] >= currentTerm[s]]_vars        

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
                     \E ind \in DOMAIN log[s] : 
                        \* An entry is committed.
                        /\ <<ind, log[s][ind].term>> \in immediatelyCommitted
                        \* And the entry got rolled back.
                        /\ Len(log'[s]) < ind
                        
NeverRollbackCommitted == [][~RollbackCommitted]_vars
    
RollbackSafety == 
    \E i,j \in Server : CanRollback(log[i], log[j]) =>
        LET commonPoint == RollbackCommonPoint(log[i], log[j])
            entriesToRollback == SubSeq(log[j], commonPoint + 1, Len(log[j])) IN
            \* The entries being rolled back should NOT be committed.
\*            entriesToRollback \cap CommittedEntries = {}     
            entriesToRollback \cap immediatelyCommitted = {}     


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
(* "Sanity Check" Properties                                                                      *)
(*                                                                                                *)
(* These are not high level correctness properties of the algorithm, but important properties     *)
(* that should hold true if we wrote the spec and the correctness properties correctly.           *)
(**************************************************************************************************)

\* The set of prefix committed entries should only ever grow. Entries should never be deleted
\* from it.
PrefixCommittedEntriesMonotonic == 
    [][(PrefixCommittedEntriesWithTerm \subseteq PrefixCommittedEntriesWithTerm')]_<<vars>>

\* The set of committed entries should only ever grow. Entries should never be deleted
\* from it.
CommittedEntriesMonotonic == 
    [][(CommittedEntries \subseteq CommittedEntries')]_<<vars>>
    
\* Immediately committed entries <<index, T>> are always committed at term T.
ImmediatelyCommittedTermMatchesLogEntryTerm == 
    \A e \in immediatelyCommitted : e.entry[2] = e.term
   

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Spec definition                                                                                *)
(**************************************************************************************************)
 
Init == 
    \* Server variables.
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ votedFor    = [i \in Server |-> Nil]
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


BecomeLeaderAction ==   \E s \in Server : BecomeLeader(s) /\ HistNext
ClientRequestAction ==  \E s \in Server : \E v \in Value : ClientRequest(s, v)    /\ HistNext
GetEntriesAction ==     \E s, t \in Server : GetEntries(s, t)                       /\ HistNext
RollbackEntriesAction ==  \E s, t \in Server : RollbackEntries(s, t)                /\ HistNext
ReconfigAction ==       \E s \in Server : Reconfig(s)                             /\ HistNext
SendConfigAction ==     \E s,t \in Server : SendConfig(s, t)                      /\ HistNext
CommitEntryAction ==     \E s \in Server : CommitEntry(s)                      /\ HistNext
  
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

CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server : 
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
        
MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm    
LogLenInvariant ==  \A s \in Server  : Len(log[s]) <= MaxLogLen    

=============================================================================
\* Modification History
\* Last modified Thu Nov 07 18:47:07 EST 2019 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
