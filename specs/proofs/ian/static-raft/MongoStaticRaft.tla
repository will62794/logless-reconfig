---- MODULE MongoStaticRaft ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE log
VARIABLE config

\* History variables for stating correctness properties.
VARIABLE elections
VARIABLE commitIndex

vars == <<currentTerm, state, log, elections, commitIndex, config>>

\*
\* Helper operators.
\*

Max(S) == CHOOSE m \in S : \A e \in S : m >= e
Min(S) == CHOOSE m \in S : \A e \in S : m <= e

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
QuorumsAt(i) == Quorums(config[i])

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
ImmediatelyCommitted(eind, eterm, Q) == 
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(<<eind,eterm>>, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, elections, commitIndex, config>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \*/\ currentTerm[i] <= currentTerm[j] \* idardik
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
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({commitIndex[j], Len(log[i])})]
    /\ UNCHANGED <<elections, currentTerm, state, config>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ state[i] = Secondary \* idardik
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<elections, commitIndex, currentTerm, state, config>>

\* Node 'i' gets elected as a primary.
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
    /\ UNCHANGED <<config, commitIndex>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET allIndices == {k \in DOMAIN log[i] : ImmediatelyCommitted(k, currentTerm[i], commitQuorum)}
                        \cup {0}
        maxIdx == Max(allIndices)
    IN
    /\ state[i] = Primary
    /\ maxIdx > commitIndex[i]
    /\ log[i][maxIdx] = currentTerm[i]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = maxIdx]
    /\ UNCHANGED <<currentTerm, state, log, config, elections>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, config, elections, commitIndex>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    (*
    /\ \E initConfig \in SUBSET Server : 
        \*/\ initConfig # {} \* configs should be non-empty.
        \*/\ config = [i \in Server |-> initConfig]
        /\ \A i \in Server : config[i] = Server
        *)
    /\ config = [i \in Server |-> Server]
    /\ elections = {}
    /\ commitIndex = [i \in Server |-> 0]

Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

ElectionSafety == 
    \A e1, e2 \in elections : 
        (e1.term = e2.term) => (e1.leader = e2.leader)

\* When a node gets elected as primary it contains all entries committed in previous terms.
\* idardik
LeaderCompleteness == 
    LET allIndices == {commitIndex[s] : s \in Server}
        maxIdx == Max(allIndices)
    IN
    \A s \in Server :
        (state[s] = Primary /\ \A t \in Server : currentTerm[s] >= currentTerm[t]) =>
            /\ Len(log[s]) >= maxIdx
            /\ \A t \in Server :
                  \A i \in 1..commitIndex[t] : log[s][i] = log[t][i]

\* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A s,t \in Server :
        \A i \in 1..Min({commitIndex[s],commitIndex[t]}) :
            log[s][i] = log[t][i]

\* a second form
StateMachineSafety2 == 
    \A s \in Server :
        \E Q \in QuorumsAt(s) :
            \A t \in Q :
                /\ Len(log[t]) >= commitIndex[s]
                /\ \A i \in 1..commitIndex[s] : log[s][i] = log[t][i]


(* Log Matching *)

EqualUpTo(log1, log2, i) ==
    \A j \in 1..i : log1[j] = log2[j]

\* This is a core property of Raft, but MongoStaticRaft does not satisfy this
LogMatching ==
    \A s,t \in Server :
        \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
            log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)


--------------------------------------------------------------------------------

\* idardik
(*
CommitsAreUnique ==
    \A c,d \in committed :
        (c.entry[1] = d.entry[1]) => (c = d)

AllPreviousCommitsAreCommitted ==
    \A c \in committed :
        LET idx == c.entry[1] IN
          (idx > 1) => \E d \in committed : d.entry[1] = idx-1
*)
=============================================================================
