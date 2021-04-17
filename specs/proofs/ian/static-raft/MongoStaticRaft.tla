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
VARIABLE committed

vars == <<currentTerm, state, log, elections, committed, config>>

\*
\* Helper operators.
\*

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
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
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
    /\ UNCHANGED <<currentTerm, state, elections, committed, config>>

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
    /\ UNCHANGED <<elections, committed, currentTerm, state, config>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    \*/\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<elections, committed, currentTerm, state, config>>

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
    /\ UNCHANGED <<config, committed>>   
            
\* Primary 'i' commits its latest log entry.
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
    /\ UNCHANGED <<currentTerm, state, log, config, elections>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, config, elections, committed>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    (*
    /\ \E initConfig \in SUBSET Server : 
        \*/\ initConfig # {} \* configs should be non-empty.
        \*/\ config = [i \in Server |-> initConfig]
        \*idardik
        /\ \A i \in Server : config[i] = Server
        *)
    /\ config = [i \in Server |-> Server]
    /\ elections = {}
    /\ committed = {}

Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

(* Not needed for the II *)

(*
HighestPrimaryCanRollbackNonconformingEntries ==
    \A p \in Server :
        (/\ state[p] = Primary
         /\ LastTerm(log[p]) = currentTerm[p]
         /\ \A s \in config[p] : currentTerm[p] >= currentTerm[s]) =>
             \A s \in config[p] :
                  \/ ExistsLogSubset(log[s],log[p]) \*LogSubset(log[s],log[p])
                  \/ CanRollback(s,p)

MissingACommitImpliesCanBeRolledBack ==
    \A s \in Server :
        (\E c \in committed : ~InLog(c.entry,s) /\ c.entry[1] <= Len(log[s])) =>
           /\ \/ log[s] = <<>>
              \/ \E t \in config[s] : CanRollback(s,t)
           \* it can't be possible for s to be elected
           /\ \A Q \in QuorumsAt(s) :
                \E q \in Q :
                    ~CanVoteForOplogOnlyBasedOnLog(q, s, currentTerm[s]+1)

           \*/\ \A t \in config[s] :
                  \*CanVoteForOplogOnlyBasedOnLog(t, s, currentTerm[s]+1) => t = s
                  \*CanVoteForOplog(t, s, currentTerm[s]+1) => t = s


AllSecondariesMustNotBeLatest ==
    \A s \in Server : state[s] = Secondary =>
        \E t \in config[s] :
            /\ t # s
            /\ currentTerm[t] >= currentTerm[s]
*)
--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

ElectionSafety == 
    \A e1, e2 \in elections : 
        (e1.term = e2.term) => (e1.leader = e2.leader)

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c.term < currentTerm[s] => InLog(c.entry, s))

\* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)


(* Log Matching *)

EqualUpTo(log1, log2, i) ==
    \A j \in 1..i : log1[j] = log2[j]

\* This is a core property of Raft, but MongoStaticRaft does not satisfy this
LogMatching ==
    \A s,t \in Server :
        \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
            log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)


(* StateMachineSafetyIndNew Helpers *)

Max(S) == CHOOSE m \in S : \A other \in S : m >= other

ExistsLogSubset(sub, super) ==
    \/ sub = <<>>
    \/ \E superStart,superEnd \in DOMAIN super : \E subStart,subEnd \in DOMAIN sub :
          /\ superStart <= superEnd
          /\ subStart <= subEnd
          /\ superEnd-superStart = subEnd-subStart
          /\ \A i \in 0..(superEnd-superStart) :
                super[superStart+i] = sub[subStart+i]

CanVoteForOplogOnlyBasedOnLog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ logOk


(* LemmaBasic Properties *)

AllConfigsAreServer ==
    \A s \in Server : config[s] = Server

\* A server's current term is always at least as large as the terms in its log.
\* This is LEMMA 6 from the Raft dissertation.
CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
    \A s \in Server : state[s] = Primary => (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* The terms of entries grow monotonically in each log.
\* This is LEMMA 7 from the Raft dissertation.
TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : i <= j => log[s][i] <= log[s][j]

OnePrimaryPerTerm ==
    \A s \in Server : state[s] = Primary =>
        \A t \in Server :
            (state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t

NonZeroLogsImplyExistsPrimary ==
    (\E s \in Server : Len(log[s]) > 0) => (\E s \in Server : state[s] = Primary)

AllSecondariesImplyInitialState ==
  (\A s \in Server : state[s] = Secondary) =>
   \A s \in Server :
        /\ currentTerm[s] = 0
        /\ log[s] = <<>>
        /\ committed = {}

LargestPrimaryMustHaveAQuorumInTerm ==
    (\E s \in Server : state[s] = Primary) =>
     \E p \in Server :
         /\ state[p] = Primary
         /\ \A u \in Server : currentTerm[p] >= currentTerm[u]
         /\ \E Q \in QuorumsAt(p) :
               \A q \in Q : currentTerm[q] = currentTerm[p]

LogsMustBeSmallerThanOrEqualToLargestTerm ==
    \A s \in Server : \E t \in Server : LastTerm(log[s]) <= currentTerm[t]


(* LemmaSecondariesLogFollowsPrimary *)

\* Belongs in TypeOK
CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm ==
    \A s \in Server :
        (state[s] = Secondary /\ LastTerm(log[s]) = currentTerm[s]) =>
           \/ \E p \in config[s] :
                  /\ state[p] = Primary
                  /\ currentTerm[p] = currentTerm[s]
                  /\ LastTerm(log[p]) >= LastTerm(log[s])
                  /\ Len(log[p]) >= Len(log[s])
                  \*/\ ExistsLogSubset(log[s],log[p])
           \/ \E p \in config[s] :
                  /\ state[p] = Primary
                  /\ currentTerm[p] > currentTerm[s] \* different from exceeds
           \/ \A t \in config[s]: state[t] = Secondary

SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm ==
    \A s \in Server :
        (state[s] = Secondary /\ LastTerm(log[s]) > currentTerm[s]) =>
           \/ \E p \in config[s] :
                  /\ state[p] = Primary
                  /\ currentTerm[p] = LastTerm(log[s])
                  /\ LastTerm(log[p]) >= LastTerm(log[s])
                  /\ Len(log[p]) >= Len(log[s])
                  \*/\ ExistsLogSubset(log[s],log[p])
           \/ \E p \in config[s] :
                  /\ state[p] = Primary
                  /\ currentTerm[p] > LastTerm(log[s]) \* different from matches


(* SMS_LC_II *)

\* when a server's latest log term EXCEEDS a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log
LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
            \A d \in committed :
                d.term <= c.term => /\ Len(log[s]) >= d.entry[1]
                                    /\ log[s][d.entry[1]] = d.term

\* when a server's latest log term is EQUAL to a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log (if the entry fits)
LogsEqualToCommittedMustHaveCommittedIfItFits ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] = c.term) =>
            \A d \in committed :
                (d.term <= c.term /\ Len(log[s]) >= d.entry[1]) =>
                      log[s][d.entry[1]] = d.term


CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens ==
    \A s \in Server :
        LET MaxLogLen == Max({ Len(log[t]) : t \in config[s] })
        IN \A c \in committed : c.entry[1] <= MaxLogLen

CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms ==
    \A s \in Server :
        LET MaxLogTerm == Max({ LastTerm(log[t]) : t \in config[s] })
        IN \A c \in committed : c.term <= MaxLogTerm

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderCompletenessGeneralized ==
    \A s \in Server : 
        (state[s] = Primary) =>
        (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

\* Basically the definition of committed--committed entries must appear on a quorum of
\* servers in a server's config
CommittedEntriesMustHaveQuorums ==
    \A c \in committed :
        \A s \in Server :
            \E Q \in Quorums(config[s]) : \A q \in Q :
                \E i \in DOMAIN log[q] :
                    /\ log[q][i] = c.term
                    /\ i = c.entry[1]

=============================================================================
