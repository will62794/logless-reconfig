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
\* QuorumsAt(i) == SUBSET config[i]
\* QuorumsAt(i) == Quorums(Server)
    
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
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x].term = e[2]
   
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

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<elections, committed, config>>

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
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<elections, committed, config>>

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.                                                            
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i]]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<currentTerm, state, elections, committed, config>>

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
            term   |-> newTerm, 
            quorum |-> voteQuorum]}
    /\ UNCHANGED <<log, committed, config>>   

CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind].term = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ \A s \in commitQuorum :
        /\ Len(log[s]) >= ind
        /\ log[s][ind] = log[i][ind]        \* they have the entry.
        /\ currentTerm[s] = currentTerm[i]  \* they are in the same term.
    /\ committed' = committed \cup
            {[ entry  |-> <<ind, currentTerm[i]>>,
               quorum |-> commitQuorum]}
    /\ UNCHANGED <<currentTerm, state, log, elections, config>>

\* Arbitrarily change the config of some node.
ChangeConfig(i) == 
    /\ \E newConfig \in SUBSET Server : config' = [config EXCEPT ![i] = newConfig]
    /\ UNCHANGED <<currentTerm, state, log, committed, elections>>

\* Is node 'i' currently electable with quorum 'q'.
Electable(i, q) == ENABLED BecomeLeader(i, q)

\* If a node is electable, its quorum must overlap with at least one node from
\* all previous vote quorums and all previous commit quorums.
StrictQuorumCondition == 
    \A s \in Server : 
    \A quorum \in SUBSET Server : 
        Electable(s, quorum) => 
            /\ \A e \in elections : (quorum \cap e.quorum) # {}
            /\ \A c \in committed : (quorum \cap c.quorum) # {}

\*
\* For any node that could be elected or could commit a write, all of its quorums must:
\*      1. Overlap with some node with term >=T for all elections that occurred in term T.
\*      2. Overlap with some node containing an entry E for all previously committed entries E.
\*
WeakQuorumCondition == 
    \A s \in Server :
    \A quorum \in QuorumsAt(s) :
        \* Overlaps with some node that contains term of election, for all previous elections.
        /\ \A e \in elections : \E t \in quorum : currentTerm[t] >= e.term 
        \* Overlaps with some node containing entry E, for all committed entries E.
        /\ \A w \in committed : \E t \in quorum : InLog(w.entry, t)

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

Init ==
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ \E initConfig \in SUBSET Server : config = [i \in Server |-> initConfig]
    /\ elections = {}
    /\ committed = {}

Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
    \* TODO: Might want to allow this to change synchronously with any other action.
    \/ \E s \in Server : ChangeConfig(s)

Spec == Init /\ [][Next]_vars

\* Variants of the spec that satisfy different quorum conditions.
SpecStrictQuorums ==   Init /\ [][Next /\ StrictQuorumCondition']_vars
SpecWeakQuorums ==     Init /\ [][Next /\ WeakQuorumCondition']_vars

ElectionSafety == 
    \A e1, e2 \in elections : 
        (e1.term = e2.term) => (e1.leader = e2.leader)

StateMachineSafety == TRUE


\* This weak protocol should not be safe.
THEOREM ~(Spec => []StateMachineSafety)

\* Using the strict or weak quorum condition should ensure safety.
THEOREM StrictQuorumSafety == SpecStrictQuorums => []StateMachineSafety
THEOREM WeakQuorumSafety == SpecWeakQuorums => []StateMachineSafety

\* The strict quorum condition should imply the weak quorum condition.
THEOREM StrictQuorumImpliesWeakQuorum == SpecStrictQuorums => []WeakQuorumCondition

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

=============================================================================
