----------------------------- MODULE TmpCheck -----------------------------

EXTENDS MongoRaftReconfig, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS


InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

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

\*
\* Establishing election safety under reconfiguration.
\*

OnePrimaryPerTerm ==
    \A s \in Server : state[s] = Primary =>
        \A t \in Server :
            (state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t

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


\*
\* Establishing log invariants.
\*

EqualUpTo(log1, log2, i) ==
    \*\A j \in 1..i : log1[j] = log2[j]
    \A j \in Nat : (j > 0 /\ j <= i) => log1[j] = log2[j]

\* This is a core property of Raft, but MongoStaticRaft does not satisfy this
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
    
\*
\* Basic type requirements of 'committed' variable.
\*

CommittedEntryIndexesAreNonZero == \A c \in committed : c.entry[1] # 0

\* Belongs in TypeOK, or considered a completely separate II
CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

\*
\* Establishing additional config related invariants that
\* help with leader completeness.
\*

\* For configs C=(v,t) and C'=(v+1,t), we know their quorums overlap, by explicit preconditions
\* of reconfiguration.
ConfigOverlapsWithDirectAncestor ==
    \A s,t \in Server :
        (/\ configVersion[s] = (configVersion[t] + 1)
         /\ configTerm[s] = configTerm[t]) => QuorumsOverlap(config[s], config[t])

NewestConfigHasLargestTerm == 
    \A s \in ServersInNewestConfig :
    \A t \in Server :
        currentTerm[t] <= configTerm[s]

\* The newest config should have some node that is currently primary or was
\* the newest primary (after stepping down). This node should be in its own config.
NewestConfigHasSomeNodeInConfig == 
    \A s \in ServersInNewestConfig : 
        (\E n \in config[s] :
            /\ n \in config[n]
            \* If this is node is or was primary in newest config,
            \* it's term should be the same as the term of the newest config.
            /\ currentTerm[n] = configTerm[s]
            /\ CV(n) = CV(s))

\* If two configs have the same version but different terms, one has a newer term,
\* then they either have the same member set or the older config is disabled. The 
\* latter is to address the case where these configs on divergent branches but have the
\* same version.
ConfigsWithSameVersionHaveSameMemberSet == 
    \A s,t \in Server : 
        (/\ configVersion[s] = configVersion[t]
         /\ configTerm[s] > configTerm[t]) => 
            \/ (config[s] = config[t])
            \/ ConfigDisabled(t)

\* If a config has been created in term T', then this must prevent any commits
\* in configs in terms < T. Note that only primary nodes can commit writes in a 
\* config.
CommitOfNewConfigPreventsCommitsInOldTerms == 
    \A s,t \in Server : 
        (/\ configTerm[t] < configTerm[s]
         /\ state[t] = Primary) =>
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]

\* 
\* Establishing leader completeness invariant.
\*

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderCompletenessGeneralized ==
    \A s \in Server : 
        (state[s] = Primary) =>
        (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

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

--------------------------------------------------------------------------------

\*IndAlt == 
Ind == 
    \*
    \* Establishing election safety under reconfiguration.
    \*
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigVersionAndTermUnique
    /\ PrimaryInTermContainsNewestConfigOfTerm
    \* (alternate)
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

    \* (alternate)
    /\ LeaderCompletenessGeneralized
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ ActiveConfigsOverlapWithCommittedEntry
    /\ NewerConfigsDisablePrimaryCommitsInOlderTerms 

TypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq(Nat)]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    \* For checking MongoRaftReconfig with logs.
    /\ committed \in SUBSET [ entry : Nat \X Nat, term : Nat ]
    /\ elections \in SUBSET [ leader : Server, term : Nat ]

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}

CVT(s) == <<configTerm[s], configVersion[s], currentTerm[s]>>

--------------------------------------------------------------------------------

LEMMA SeqDownwardInduction ==
ASSUME NEW P(_),
       NEW len \in Nat,
       len > 0,
       P(len),
       \A n \in 2..len : (P(n) => P(n-1))
PROVE P(1)
PROOF
    <1>. DEFINE Q(i) == (i <= len-1) => P(len-i)
    <1>. HIDE DEF Q
    <1>1. Q(0) BY DEF Q
    <1>2. ASSUME NEW n \in Nat, Q(n)
          PROVE Q(n+1)
        BY <1>2 DEF Q
    <1>3. \A n \in Nat : Q(n) BY <1>1, <1>2, NatInduction, Isa
    <1>. QED BY <1>3 DEF Q

LEMMA DifferentLogEntriesImplyUpperBoundary ==
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW upper \in DOMAIN log[s],
       NEW lower \in DOMAIN log[s],
       upper > lower,
       log[s][upper] # log[s][lower]
PROVE \E i \in DOMAIN log[s] :
            /\ i > 1
            /\ log[s][i] = log[s][upper]
            /\ log[s][i-1] < log[s][i]
PROOF
    <1>1. SUFFICES ASSUME \A i \in DOMAIN log[s] : i > 1 =>
                            \/ i <= 1
                            \/ log[s][i] # log[s][upper]
                            \/ log[s][i-1] >= log[s][upper]
          PROVE FALSE BY DEF TypeOK
    <1>2. log[s][upper] > log[s][lower] BY DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
    <1>3. upper > 1 BY DEF TypeOK
    <1>.  DEFINE P(idx) == log[s][idx] = log[s][upper]
    <1>.  HIDE DEF P
    <1>4. \A i \in DOMAIN log[s] : P(i) => P(i-1)
        <2>1. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => i > 1 BY <1>2 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
        <2>2. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => log[s][i-1] >= log[s][upper] BY <1>1, <2>1 DEF TypeOK
        <2>3. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => log[s][i-1] = log[s][upper]
            BY <2>1, <2>2 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
        <2>. QED BY <2>3 DEF P
    <1>5. \A i \in 1..Len(log[s]) : P(i) => P(i-1) BY <1>4 DEF P
    <1>6. P(upper) BY DEF P
    <1>7. P(1)
        <2>1. /\ upper \in Nat
              /\ upper > 0
              /\ P(upper)
              /\ \A n \in 2..upper : (P(n) => P(n-1))
            BY <1>3, <1>5, <1>6 DEF TypeOK
        <2>. QED BY <2>1, SeqDownwardInduction, Isa DEF TypeOK
    <1>8. log[s][1] = log[s][upper] BY <1>7 DEF P
    <1>. QED BY <1>2, <1>3, <1>8 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK

LEMMA EqualLastTermImpliesEqualAtIdx ==
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW t \in Server,
       LastTerm(log[s]) = LastTerm(log[t]),
       Len(log[s]) >= Len(log[t]),
       Len(log[t]) > 0
PROVE LET tLastIdx == Len(log[t])
      IN  log[s][tLastIdx] = log[t][tLastIdx]
PROOF
    <1>.  DEFINE tLastIdx == Len(log[t])
    <1>.  DEFINE sLastIdx == Len(log[s])
    <1>1. SUFFICES ASSUME sLastIdx > tLastIdx,
                          log[s][tLastIdx] # log[t][tLastIdx]
          PROVE FALSE BY DEF LastTerm, TypeOK
    <1>2. log[s][tLastIdx] < log[s][sLastIdx] BY <1>1 DEF Ind, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
    <1>3. PICK i \in DOMAIN log[s] :
                    /\ i > 1
                    /\ log[s][i] = log[s][sLastIdx]
                    /\ log[s][i-1] < log[s][sLastIdx]
        BY <1>1, DifferentLogEntriesImplyUpperBoundary DEF LastTerm
    <1>4. i > tLastIdx BY <1>1, <1>3 DEF Ind, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
    <1>5. \A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]
        <2>1. \A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i] BY <1>3 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
        <2>. QED BY <2>1 DEF Ind, UniformLogEntriesInTerm, TypeOK
    <1>. QED BY <1>3, <1>4, <1>5 DEF LastTerm, TypeOK

=============================================================================


















