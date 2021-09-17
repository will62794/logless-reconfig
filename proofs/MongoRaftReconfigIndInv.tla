----------------------------- MODULE MongoRaftReconfigIndInv -----------------------------
\*
\* This module contains the definition of the inductive invariant used for 
\* establishing safety of MongoRaftReconfig.
\*

EXTENDS MongoRaftReconfig

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is node i disabled due to a quorum of its config having moved to a newer config.
ConfigDisabled(i) == 
    \A Q \in Quorums(config[i]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(i))

\* Does server s have the newest config.
NewestConfig(s) == \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))

\* Servers in the newest config.
ServersInNewestConfig == {s \in Server : NewestConfig(s)}

OlderConfig(ci, cj) == ~CSM!NewerOrEqualConfig(ci, cj) 

--------------------------------------------------------------------------------

PrimaryConfigTermEqualToCurrentTerm == 
    \A s \in Server : (state[s] = Primary) => (configTerm[s] = currentTerm[s])

ConfigVersionAndTermUnique ==
    \A i,j \in Server :
        (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>> )=>
        config[i] = config[j]

PrimaryInTermContainsNewestConfigOfTerm == 
    \A p,s \in Server : 
        (state[p] = Primary /\ configTerm[s] = configTerm[p]) =>
            (configVersion[p] >= configVersion[s]) 

\* If config t has an older config than s, and their configs don't overlap, then
\* config t must be disabled based on config ordering.
NewerConfigDisablesOlderNonoverlappingConfigs == 
    \A s,t \in Server :
        (/\ OlderConfig(CV(t), CV(s)) 
         /\ ~QuorumsOverlap(config[t], config[s])) => ConfigDisabled(t)

\* If t has an older or equal config than s and it is not disabled by a newer
\* config, then its quorum must overlap with some node in the term of config s.
NewerConfigDisablesTermsOfOlderNonDisabledConfigs ==
    \A s,t \in Server :
        (/\ OlderConfig(CV(t), CV(s)) \/ (CV(t) = CV(s))
         /\ ~ConfigDisabled(t)) => 
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]

EqualUpTo(log1, log2, i) ==
    \A j \in Nat : (j > 0 /\ j <= i) => log1[j] = log2[j]

LogMatching ==
    \A s,t \in Server :
        \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
            log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)

TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : i <= j => log[s][i] <= log[s][j]

\* If a log entry exists in term T and there is a primary in term T, then this
\* log entry should be present in that primary's log.
PrimaryHasEntriesItCreated == 
    \A i,j \in Server :
    (state[i] = Primary) => 
    \* Can't be that another node has an entry in this primary's term
    \* but the primary doesn't have it.
        ~(\E k \in DOMAIN log[j] :
            /\ log[j][k] = currentTerm[i]
            /\ ~InLog(<<k,log[j][k]>>, i))
    
\* A server's current term is always at least as large as the terms in its log.
\* This is LEMMA 6 from the Raft dissertation.
CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
    \A s \in Server : state[s] = Primary => (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* If a log entry in term T exists, there must have been an election in 
\* term T to create it, implying the existence of a config in term T or newer.
LogEntryInTermImpliesConfigInTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] :
    \E t \in Server : 
        configTerm[t] >= log[s][i]

\* If a log contains an entry in term T at index I such that
\* the entries at J < I are in a different term, then there must be
\* no other logs that contains entries in term T at indices J < I
UniformLogEntriesInTerm ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] : 
        (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => 
            (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)

\* \*
\* \* If a log entry in term T exists, then some primary in term T must have
\* \* created that log entry, and the corresponding log prefix must have only
\* \* propagated to other servers via this primary. So, there cannot exist an
\* \* entry in some other log in the same term that is in a conflicting position
\* \* with entries in this term. For example, the following log state is not
\* \* possible:
\* \*
\* \* n1: [1,2]
\* \* n2: [2]
\* \* 
\* UniformLogEntriesInTerm ==
\*     \A s,t \in Server :
\*     \A is \in DOMAIN log[s] : 
\*     \A it \in DOMAIN log[t] : 
\*         \* If the log entry on server t at index 'it' has the same term,
\*         \* as the entry on server s at 'is' and is at a lesser log index, 
\*         \* then the log on s at position 'it' must also be in term T.
\*         (log[s][is] = log[t][it] /\ it < is) => (log[s][it] = log[s][is])
    
CommittedEntryIndexesAreNonZero == \A c \in committed : c.entry[1] # 0

\* Belongs in TypeOK, or considered a completely separate II
CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

\* If a config has been created in term T', then this must prevent any commits
\* in configs in terms < T. Note that only primary nodes can commit writes in a 
\* config.
CommitOfNewConfigPreventsCommitsInOldTerms == 
    \A s,t \in Server : 
        (/\ configTerm[t] < configTerm[s]
         /\ state[t] = Primary) =>
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]

CommittedEntryIntersectsWithNewestConfig ==
    \A c \in committed :
    \A s \in ServersInNewestConfig :
        \A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n)

\* \* If a log entry is committed, then the quorums of every 
\* active config must overlap with some node that contains this log entry.
CommittedEntryIntersectsWithEveryActiveConfig ==
    \A c \in committed :
    \A s \in Server :
        ~ConfigDisabled(s) => (\A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n))

\* when a server's latest log term EXCEEDS a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log
LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
            \A d \in committed :
                d.term <= c.term => /\ Len(log[s]) >= d.entry[1]
                                    /\ log[s][d.entry[1]] = d.term

\* \* If a log contains an entry in term T, then it must also contain all entries
\* \* committed in terms < T.
\* LogsLaterThanCommittedMustHaveCommitted == 
\*     \A s \in Server :
\*     \A c \in committed :
\*     \A i \in DOMAIN log[s] :
\*         (c.term < log[s][i]) => InLog(c.entry, s)
                                    
ActiveConfigSet == {s \in Server : ~ConfigDisabled(s)}

\* The quorums of all active configs overlap with each other. 
ActiveConfigsOverlap == 
    \A s,t \in ActiveConfigSet : QuorumsOverlap(config[s], config[t])

\* Every active config overlaps with some node in a term >=T for all elections
\* that occurred in term T (and exist in some config that is still around).
ActiveConfigsSafeAtTerms == 
    \A s \in Server : 
    \A t \in ActiveConfigSet :
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]

ActiveConfigsOverlapWithCommittedEntry == 
    \A c \in committed :
    \A s \in ActiveConfigSet :
        \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c.entry, n)   

NewerConfigsDisablePrimaryCommitsInOlderTerms ==
    \A s,t \in Server : 
    (state[t] = Primary /\ currentTerm[t] < configTerm[s]) =>
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > currentTerm[t]

ConfigsNonempty ==
    \A s \in Server : config[s] # {}

--------------------------------------------------------------------------------

\*
\* The inductive invariant.
\*
Ind ==
    \*
    \* Establishing election safety under reconfiguration.
    \*
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigVersionAndTermUnique
    /\ PrimaryInTermContainsNewestConfigOfTerm
    /\ ActiveConfigsOverlap
    /\ ActiveConfigsSafeAtTerms

    \*
    \* Establishing log invariants.
    \*
    /\ LogMatching
    /\ TermsOfEntriesGrowMonotonically
    /\ PrimaryHasEntriesItCreated
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ LogEntryInTermImpliesConfigInTerm
    /\ UniformLogEntriesInTerm

    \*
    \* Basic type requirements of 'committed' variable.
    \*
    /\ CommittedEntryIndexesAreNonZero
    /\ CommittedTermMatchesEntry

    \*
    \* Establishing leader completeness.
    \*
    /\ LeaderCompleteness
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ ActiveConfigsOverlapWithCommittedEntry
    /\ NewerConfigsDisablePrimaryCommitsInOlderTerms
    
    /\ ConfigsNonempty

TypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq(Nat)]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    /\ committed \in SUBSET [ entry : Nat \X Nat, term : Nat ]

=============================================================================
