----------------------------- MODULE MongoRaftReconfigIndInv -----------------------------
\*
\* This module contains the definition of the inductive invariant used for 
\* establishing safety of MongoRaftReconfig.
\*

EXTENDS MongoRaftReconfig

\*
\* Some helper operators.
\*

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is node i disabled due to a quorum of its config having moved to a newer config.
ConfigDisabled(i) == 
    \A Q \in Quorums(config[i]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(i))

OlderConfig(ci, cj) == ~CSM!NewerOrEqualConfig(ci, cj) 

EqualUpTo(log1, log2, i) ==
    \A j \in Nat : (j > 0 /\ j <= i) => log1[j] = log2[j]

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

LogMatching ==
    \A s,t \in Server :
    \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
        log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)

TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

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
\* This is Lemma 6 from the Raft dissertation.
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

CommittedEntryIndexesAreNonZero == \A c \in committed : c.entry[1] # 0

CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

\* If a server's latest log term exceeds a committed entry c's term, all commits
\* with terms <= c's must be in the server's log.
LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : 
    \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
            \A d \in committed :
                d.term <= c.term => /\ Len(log[s]) >= d.entry[1]
                                    /\ log[s][d.entry[1]] = d.term

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
    \* Must establish type correctness.
    /\ TypeOK

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

=============================================================================
