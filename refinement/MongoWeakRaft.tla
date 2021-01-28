---- MODULE MongoWeakRaft ----
\* Weak Raft protocol that allows quorums to change arbitrarily.

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

(***************************************************************************)
(* Replication related variables.                                          *)
(***************************************************************************)

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE config

VARIABLE elections
VARIABLE committed

serverVars == <<currentTerm, state, log>>
vars == <<currentTerm, state, log, elections, committed, config>>

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

\* The set of all quorums. This satisfies no property of overlap between two quorums.
\* Quorums == SUBSET Server

Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
QuorumsAt(i) == Quorums(config[i])

\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
\* QuorumsAt(i) == Quorums(config[i])

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

NewerIndTerm(it1,it2) == 
    \/ (it1[2] = it2[2] /\ it1[1] > it2[1])
    \/ it1[2] > it2[2]

\* Does node 'i' have a newer log than node 'j', based on its last entry.
NewerLog(i, j) == 
    \/ log[j] = <<>> /\ log[i] # <<>>
    \/ log[j] # <<>> /\ log[i] # <<>> /\ NewerIndTerm(LastEntry(log[i]), LastEntry(log[j]))

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]
   
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

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry.  
    
-------------------------------------------------------------------------------------------

\*
\* Next state actions.                                                     
\*
\* The core actions do not specify how the 'config' variable changes, since in the final specification we allow
\* it to potentially change synchronously with any protocol transition.
\*

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]

\* Action that exchanges terms between two nodes and step down the primary if needed. This can be safely
\* specified as a separate action, rather than occurring atomically on other replication actions that
\* involve communication between two nodes. This makes it clearer to see where term propagation is strictly
\* necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, config, elections, committed>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<elections, committed, currentTerm, state>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
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
    /\ UNCHANGED <<elections, committed, currentTerm, state>>

\* This is a coarse grained atomic action that combines both log replication and rollback.
\* It atomically transfers the entire log from node 'i' to node 'j', if the log of node 'i'
\* is "newer", by log comparison rules, than the log of node 'j'. Implementations should be
\* allowed to do replication and rollback separately (fine-grained) or do it in one shot (coarse-grained).
MergeEntries(i, j) ==
    /\ NewerLog(i, j)
    /\ log' = [log EXCEPT ![j] = log[i]]
    /\ UNCHANGED <<elections, committed, currentTerm, state>>

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.                                                            
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, elections, committed>>

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ elections' = elections \cup 
        {[ leader  |-> i, 
            term   |-> newTerm ]}
    \* Allow new leaders to write a no-op on step up if they want to. It is optional, but permissible.
    /\ \/ log' = [log EXCEPT ![i] = Append(log[i], newTerm)]
       \/ UNCHANGED log
    /\ UNCHANGED <<committed>>   

CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c.entry = <<ind, currentTerm[i]>>
    /\ committed' = committed \cup
            {[ entry  |-> <<ind, currentTerm[i]>>,
               term  |-> currentTerm[i]]}
    /\ UNCHANGED <<currentTerm, state, log, elections>>

\* Arbitrarily change the config of some node.
ChangeConfig(i) == 
    /\ \E newConfig \in SUBSET Server : 
        /\ newConfig # {} \* configs should be non-empty.
        /\ config' = [config EXCEPT ![i] = newConfig]
    \* /\ UNCHANGED <<currentTerm, state, log, committed, elections>>

\* Is node 'i' currently electable with quorum 'q'.
Electable(i, q) == ENABLED BecomeLeader(i, q)

\* Is a log entry 'e'=<<index, term>> currently committed. This definition of
\* commitment is defined by checking if a log entry would be present in the log
\* of any future elected leader. If so, then the entry is committed. Otherwise,
\* it is not. This may requiring contacting every node, so it could, in
\* practice, be an expensive operation, but it should work fine for an abstract
\* definition, since we can reason about the global state directly.
\* TODO: Might also need to incorporate rollbacks into this definition?
IsFutureCommitted(e) == 
    LET electableNodes == {s \in Server : \E Q \in QuorumsAt(s) : Electable(s, Q)} IN 
    \A s \in electableNodes : InLog(e, s)

\* The set of all log entries (<<index, term>>) in the log of node 's'.
LogEntriesAt(s) == {<<i,log[s][i]>> : i \in DOMAIN log[s]} 

\* The set of log entries (<<index, term>>) in all node logs.
LogEntriesAll == UNION {LogEntriesAt(s) : s \in Server}

FutureCommittedImpliesImmediatelyCommitted == 
    \A e \in LogEntriesAll : IsFutureCommitted(e) => (\E c \in committed : c.entry = e)

ImmediatelyCommittedImpliesFutureCommitted ==
    \A e \in LogEntriesAll : (\E c \in committed : c.entry = e) => IsFutureCommitted(e) 

\* All quorums of all nodes always overlap. A sufficient condition for this is if
\* quorums of all configs overlap, and configs never change.
StrictQuorumCondition == 
    [][\A s,t \in Server : 
        /\ QuorumsOverlap(config[s], config[t])
        /\ config[s] = config'[s]]_vars

Init ==
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ \E initConfig \in SUBSET Server : 
        /\ initConfig # {} \* configs should be non-empty.
        /\ config = [i \in Server |-> initConfig]
    /\ elections = {}
    /\ committed = {}

\* The next state actions that do not affect the 'config' variable.
NextStatic == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
    \/ \E s, t \in Server : MergeEntries(s, t)
    \/ \E s, t \in Server : UpdateTerms(s, t)

\* We allow the protocol to take any 'core' protocol step and, if it wants to, change the config
\* on some node arbitrarily when that transition is taken.
Next == 
    /\ NextStatic 
    \* Allows the config to be changed or remain the same on any protocol step.
    /\ \E s \in Server : ChangeConfig(s)

Spec == Init /\ [][Next]_vars

\* Variants of the spec that satisfy different quorum conditions.
\* SpecStrictQuorums ==   Init /\ StrictQuorumCondition /\ [][Next /\ StrictQuorumCondition']_vars

ElectionSafety == 
    \A e1, e2 \in elections : 
        (e1.term = e2.term) => (e1.leader = e2.leader)

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c.term < currentTerm[s] => InLog(c.entry, s))

\* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)

\* This weak protocol should not be safe.
THEOREM ~(Spec => []StateMachineSafety)

\* THEOREM StrictQuorumSafety == SpecStrictQuorums => []StateMachineSafety

=============================================================================
