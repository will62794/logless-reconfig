----------------------------- MODULE LeaderCompletenessLib -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib

LEMMA CommitEntryImpliesInActiveConfigSet ==
ASSUME Ind,
       NEW p \in Server,
       NEW Q \in Quorums(config[p]),
       OSM!CommitEntry(p, Q)
PROVE p \in ActiveConfigSet
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. SUFFICES ASSUME \A pQ \in Quorums(config[p]) : \E n \in pQ : CSM!NewerConfig(CV(n), CV(p))
          PROVE FALSE BY DEF ActiveConfigSet, ConfigDisabled
    <1>2. PICK n \in Q : CSM!NewerConfig(CV(n), CV(p)) BY <1>1
    <1>3. configTerm[p] < configTerm[n]
        BY <1>2 DEF OSM!CommitEntry, Ind, OnePrimaryPerTerm, PrimaryInTermContainsNewestConfigOfTerm,
                    CSM!NewerConfig, CV, Quorums, TypeOK
    <1>4. state[p] = Primary /\ currentTerm[p] < configTerm[n]
        BY <1>3 DEF OSM!CommitEntry, Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK
    <1>5. \E s \in Q : currentTerm[s] > currentTerm[p]
        BY <1>2, <1>4 DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, Quorums, TypeOK
    <1>. QED BY <1>ok, <1>5 DEF OSM!CommitEntry, OSM!ImmediatelyCommitted, TypeOK

LEMMA CommitEntryImpliesCurrentTermGreaterThanConfigTerms ==
ASSUME Ind,
       NEW p \in Server,
       NEW Q \in Quorums(config[p]),
       OSM!CommitEntry(p, Q)
PROVE \A s \in Server : currentTerm[p] >= configTerm[s]
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. SUFFICES ASSUME NEW s \in Server, currentTerm[p] < configTerm[s]
          PROVE FALSE BY DEF Ind, TypeOK
    <1>2. \E n \in Q : currentTerm[n] > currentTerm[p] BY <1>1 DEF OSM!CommitEntry, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms
    <1>. QED BY <1>ok, <1>2 DEF OSM!CommitEntry, OSM!ImmediatelyCommitted, TypeOK

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
ASSUME Ind,
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
    <1>ok. TypeOK BY DEF Ind
    <1>1. SUFFICES ASSUME \A i \in DOMAIN log[s] : i > 1 =>
                            \/ i <= 1
                            \/ log[s][i] # log[s][upper]
                            \/ log[s][i-1] >= log[s][upper]
          PROVE FALSE BY DEF Ind, TypeOK
    <1>2. log[s][upper] > log[s][lower] BY <1>ok DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
    <1>3. upper > 1 BY DEF Ind, TypeOK
    <1>.  DEFINE P(idx) == log[s][idx] = log[s][upper]
    <1>.  HIDE DEF P
    <1>4. \A i \in DOMAIN log[s] : P(i) => P(i-1)
        <2>1. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => i > 1 BY <1>ok, <1>2 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
        <2>2. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => log[s][i-1] >= log[s][upper] BY <1>ok, <1>1, <2>1 DEF TypeOK
        <2>3. \A i \in DOMAIN log[s] : (log[s][i] = log[s][upper]) => log[s][i-1] = log[s][upper]
            BY <1>ok, <2>1, <2>2 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
        <2>. QED BY <2>3 DEF P
    <1>5. \A i \in 1..Len(log[s]) : P(i) => P(i-1) BY <1>4 DEF P
    <1>6. P(upper) BY DEF P
    <1>7. P(1)
        <2>1. /\ upper \in Nat
              /\ upper > 0
              /\ P(upper)
              /\ \A n \in 2..upper : (P(n) => P(n-1))
            BY <1>ok, <1>3, <1>5, <1>6 DEF TypeOK
        <2>. QED BY <2>1, SeqDownwardInduction, Isa DEF TypeOK
    <1>8. log[s][1] = log[s][upper] BY <1>7 DEF P
    <1>9. 1 \in DOMAIN log[s] /\ upper \in DOMAIN log[s] BY <1>ok DEF TypeOK
    <1>. QED BY <1>2, <1>3, <1>8, <1>9, Z3 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK

LEMMA EqualLastTermImpliesEqualAtIdx ==
ASSUME Ind,
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

LEMMA ElectedLeadersHaveAllCommits ==
ASSUME Ind,
       NEW p \in Server,
       NEW Q \in Quorums(config[p]),
       OSM!BecomeLeader(p, Q),
       CSM!BecomeLeader(p, Q)
PROVE \A c \in committed : InLog(c.entry, p)
    <1>1. TAKE c \in committed
    <1>2. PICK n \in Q : InLog(c.entry, n) BY ElectedLeadersInActiveConfigSet DEF Ind, ActiveConfigsOverlapWithCommittedEntry
    <1>n. n \in Server BY <1>2 DEF Quorums, Ind, TypeOK
    <1>3. CASE LastTerm(log[p]) > LastTerm(log[n])
        <2>1. \E i \in DOMAIN log[n] : log[n][i] = c.term BY <1>2 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. LastTerm(log[n]) >= c.term BY <1>n, <1>1, <1>3, <2>1 DEF Ind, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
        <2>3. LastTerm(log[p]) > c.term BY <1>n, <1>1, <1>3, <2>2 DEF LastTerm, Ind, TypeOK
        <2>4. Len(log[p]) >= c.entry[1] /\ log[p][c.entry[1]] = c.term
            <3>1. p \in Server /\ c \in committed BY <1>1
            <3>2. \E i \in DOMAIN log[p] : log[p][i] > c.term BY <2>3 DEF LastTerm, Ind, TypeOK
            <3>. QED BY <3>1, <3>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>. QED BY <1>1, <2>4 DEF Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero, InLog, TypeOK
    <1>4. CASE LastTerm(log[p]) = LastTerm(log[n]) /\ Len(log[p]) >= Len(log[n])
        <2>.  DEFINE nLen == Len(log[n])
        <2>1. nLen > 0 BY <1>2 DEF InLog, TypeOK
        <2>2. log[p][nLen] = log[n][nLen] BY <1>n, <1>4, <2>1, EqualLastTermImpliesEqualAtIdx DEF TypeOK
        <2>3. \A i \in DOMAIN log[n] : log[n][i] = log[p][i]
            <3>1. \A i \in DOMAIN log[n] : \A j \in Nat : (j > 0 /\ j < nLen) => log[p][j] = log[n][j]
                BY <1>n, <1>4, <2>1, <2>2 DEF Ind, LogMatching, EqualUpTo, TypeOK
            <3>. QED BY <1>n, <1>4, <2>1, <2>2, <3>1, Zenon, Z3 DEF TypeOK
        <2>. QED BY <1>1, <1>n, <1>2, <1>4, <2>3 DEF InLog, TypeOK
    <1>. QED BY <1>3, <1>4 DEF OSM!BecomeLeader, OSM!CanVoteForOplog, OSM!LastTerm, LastTerm

LEMMA CommitImpliesInActiveConfigSet ==
ASSUME Ind,
       NEW p \in Server,
       NEW pQ \in Quorums(config[p]),
       OSM!CommitEntry(p, pQ)
PROVE p \in ActiveConfigSet
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. SUFFICES ASSUME \A Q \in Quorums(config[p]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(p))
          PROVE FALSE BY DEF ActiveConfigSet, ConfigDisabled
    <1>2. PICK n \in pQ : CSM!NewerConfig(CV(n), CV(p)) BY <1>1
    <1>n. n \in Server BY <1>ok, <1>2 DEF Quorums, TypeOK
    <1>3. state[p] = Primary BY DEF OSM!CommitEntry
    <1>4. n # p BY <1>ok, <1>2 DEF CSM!NewerConfig, CV, TypeOK
    <1>5. currentTerm[n] = currentTerm[p]
        <2>1. OSM!ImmediatelyCommitted(<<Len(log[p]),currentTerm[p]>>, pQ) BY DEF OSM!CommitEntry, TypeOK
        <2>. QED BY <2>1 DEF OSM!ImmediatelyCommitted, OSM!InLog, TypeOK
    <1>6. configTerm[n] > currentTerm[p]
        <2>1. state[n] # Primary BY <1>n, <1>3, <1>4, <1>5 DEF Ind, OnePrimaryPerTerm
        <2>2. configTerm[n] >= configTerm[p] BY <1>ok, <1>2 DEF CSM!NewerConfig, CV, TypeOK
        <2>3. (configTerm[n] = configTerm[p]) => (configVersion[n] <= configVersion[p])
            BY <1>n, <1>3, <2>1, <2>2 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm, TypeOK
        <2>4. configTerm[n] > configTerm[p] BY <1>ok, <1>n, <1>2, <2>2, <2>3 DEF CSM!NewerConfig, CV, TypeOK
        <2>. QED BY <1>3, <2>4 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
    <1>7. \E t \in pQ : currentTerm[t] > currentTerm[p]
        BY <1>ok, <1>3, <1>6 DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, Quorums, TypeOK
    <1>. QED BY <1>ok, <1>7 DEF OSM!CommitEntry, OSM!ImmediatelyCommitted, TypeOK

LEMMA ReconfigImpliesCommitTermsSmallerOrEqual ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       OplogCommitment(p),
       CSM!Reconfig(p, newConfig)
PROVE \A c \in committed : currentTerm[p] >= c.term
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. TAKE c \in committed
    <1>2. SUFFICES ASSUME c.term > currentTerm[p]
          PROVE FALSE BY DEF Ind, TypeOK
    <1>3. PICK d \in committed : d.term = currentTerm[p] BY DEF OplogCommitment
    <1>.  DEFINE k == d.entry[1]
    <1>4. PICK Q \in Quorums(config[p]) : \A s \in Q : (log[s][k] = log[p][k] /\ currentTerm[s] = currentTerm[p])
        <2>1. \E Q \in Quorums(config[p]) : \A s \in Q :
                    \E i \in DOMAIN log[s] : (i = k /\ log[s][k] = log[p][k] /\ currentTerm[s] = currentTerm[p])
            BY <1>ok, <1>3 DEF OplogCommitment, IsCommitted, TypeOK
        <2>. QED BY <2>1
    <1>5. \E n \in Q : InLog(c.entry, n) BY <1>4, ReconfigImpliesInActiveConfigSet DEF Ind, ActiveConfigsOverlapWithCommittedEntry
    <1>6. PICK s \in Server : configTerm[s] >= c.term
        BY <1>4, <1>5 DEF Ind, LogEntryInTermImpliesConfigInTerm, CommittedTermMatchesEntry, Quorums, InLog, TypeOK
    <1>7. currentTerm[p] < configTerm[s] BY <1>2, <1>6 DEF Ind, TypeOK
    <1>8. \E n \in Q : currentTerm[n] > currentTerm[p] BY <1>7 DEF CSM!Reconfig, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms
    <1>. QED BY <1>4, <1>8 DEF TypeOK

COROLLARY ReconfigImpliesHasAllCommits ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       OplogCommitment(p),
       CSM!Reconfig(p, newConfig)
PROVE \A c \in committed : InLog(c.entry, p)
BY ReconfigImpliesCommitTermsSmallerOrEqual DEF CSM!Reconfig,
    Ind, LeaderCompleteness, CommittedTermMatchesEntry, InLog, TypeOK

LEMMA ReconfigImpliesHasQuorumWithAllCommits ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       OplogCommitment(p),
       CSM!Reconfig(p, newConfig)
PROVE \A c \in committed : \A Q \in Quorums(newConfig) : \E n \in Q : InLog(c.entry, n)
    <1>1. TAKE c \in committed
    <1>2. CASE c.term = currentTerm[p]
        <2>.  DEFINE k == c.entry[1]
        <2>1. PICK Q \in Quorums(config[p]) : \A s \in Q : (k \in DOMAIN log[s] /\ log[s][k] = currentTerm[p] /\ currentTerm[s] = currentTerm[p])
            <3>1. \E Q \in Quorums(config[p]) : \A s \in Q : (k \in DOMAIN log[s] /\ log[s][k] = log[p][k] /\ currentTerm[s] = currentTerm[p])
                BY <1>2 DEF OplogCommitment, IsCommitted, LogTerm, TypeOK, Ind, CommittedEntryIndexesAreNonZero
            <3>2. LogTerm(p, k) = currentTerm[p] BY <1>2 DEF OplogCommitment, IsCommitted
            <3>3. k > 0 BY DEF Ind, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF LogTerm, GetTerm, TypeOK
        <2>2. \A pQ \in Quorums(newConfig) : \E s \in pQ : InLog(c.entry, s)
            <3>1. \A pQ \in Quorums(newConfig) : pQ \cap Q # {}
                <4>1. QuorumsOverlap(config[p], newConfig) BY QuorumsOverlapIdentical DEF CSM!Reconfig, Ind, TypeOK
                <4>. QED BY <2>1, <4>1, QuorumsOverlapIsCommutative DEF QuorumsOverlap, Quorums, TypeOK
            <3>2. \A pQ \in Quorums(newConfig) : \E s \in pQ : (k \in DOMAIN log[s] /\ log[s][k] = c.term)
                BY <1>1, <1>2, <2>1, <3>1 DEF InLog, TypeOK, Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero
            <3>3. \A pQ \in Quorums(newConfig) : \E s \in pQ : (k \in DOMAIN log[s] /\ log[s][k] = c.entry[2])
                BY <1>1, <3>2 DEF TypeOK, Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero
            <3>. QED BY <1>1, <3>3 DEF InLog, TypeOK
        <2>. QED BY <2>2
    <1>3. CASE c.term < currentTerm[p]
        <2>1. PICK d \in committed : d.term = currentTerm[p] BY DEF OplogCommitment
        <2>.  DEFINE k == d.entry[1]
        <2>.  DEFINE l == c.entry[1]
        <2>2. log[p][k] = d.term /\ k \in DOMAIN log[p]
            <3>1. LogTerm(p, k) = d.term BY <2>1 DEF OplogCommitment, IsCommitted, LogTerm, Ind, TypeOK
            <3>2. k \in DOMAIN log[p] BY <2>1 DEF OplogCommitment, IsCommitted, LogTerm, TypeOK, Ind, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry
            <3>. QED BY <3>1, <3>2 DEF LogTerm, GetTerm, Ind, TypeOK
        <2>3. InLog(c.entry, p)
            <3>1. \E i \in DOMAIN log[p] : log[p][i] > c.term BY <1>3, <2>1, <2>2 DEF TypeOK
            <3>2. Len(log[p]) >= c.entry[1] /\ log[p][c.entry[1]] = c.term
                <4>1. c.term <= c.term BY DEF Ind, TypeOK
                <4>. QED BY <1>1, <2>1, <3>1, <4>1, Zenon, Z3 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
            <3>. QED BY <1>1, <3>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry, InLog, TypeOK
        <2>4. PICK pQ \in Quorums(config[p]) : \A s \in pQ : InLog(c.entry, s)
            <3>1. PICK pQ \in Quorums(config[p]) : \A s \in pQ : (log[s][k] = log[p][k] /\ k \in DOMAIN log[s])
                BY <1>1, <2>1, <2>2, <2>3 DEF OplogCommitment, IsCommitted, InLog, TypeOK
            <3>2. c.term < d.term BY <1>1, <1>3, <2>1 DEF TypeOK
            <3>3. log[p][l] = c.term /\ l \in DOMAIN log[p] BY <1>1, <2>3 DEF InLog, Ind, CommittedTermMatchesEntry, TypeOK
            <3>4. l < k
                <4>1. SUFFICES ASSUME l >= k
                      PROVE FALSE BY DEF Ind, TypeOK
                <4>2. log[p][l] >= log[p][k] BY <2>2, <3>3, <4>1 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
                <4>. QED BY <1>1, <2>1, <2>2, <3>2, <3>3, <4>2 DEF Ind, CommittedTermMatchesEntry, TypeOK
            <3>5. \A s \in pQ : \A i \in DOMAIN log[s] :
                    (i <= k) => (log[s][i] = log[p][i] /\ i \in (DOMAIN log[s] \cap DOMAIN log[p]))
                BY <1>1, <2>1, <2>2, <3>1 DEF Ind, LogMatching, EqualUpTo, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry, Quorums, TypeOK
            <3>6. \A s \in pQ : (l \in DOMAIN log[s] /\ l <= k)
                BY <1>1, <2>1, <2>2, <3>1, <3>3, <3>4, <3>5 DEF Ind, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry, Quorums, TypeOK
            <3>7. \A s \in pQ : (l \in DOMAIN log[s] /\ l <= k => log[s][l] = log[p][l])
                BY <1>1, <2>1, <3>5, <3>6 DEF TypeOK
            <3>8. \A s \in pQ : (log[s][l] = log[p][l]) BY <3>6, <3>7
            <3>. QED BY <1>1, <3>3, <3>6, <3>8 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>5. \A Q \in Quorums(newConfig) : Q \cap pQ # {}
            BY <2>4, QuorumsOverlapIdentical, QuorumsOverlapIsCommutative DEF CSM!Reconfig, QuorumsOverlap, Ind, TypeOK
        <2>. QED BY <1>1, <2>3, <2>4, <2>5 DEF InLog, TypeOK
    <1>. QED BY <1>2, <1>3, ReconfigImpliesCommitTermsSmallerOrEqual DEF Ind, TypeOK

=============================================================================

