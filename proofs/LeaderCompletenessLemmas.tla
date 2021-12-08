----------------------------- MODULE LeaderCompletenessLemmas -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib, LeaderCompletenessLib

\* began: 8/29
\* finished 8/29
\* approx 3 min
LEMMA CommittedEntryIndexesAreNonZeroAndNext ==
ASSUME Ind, Next
PROVE CommittedEntryIndexesAreNonZero'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF OSM!RollbackEntries, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, CommittedEntryIndexesAreNonZero
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            BY <2>1 DEF OSM!BecomeLeader, Ind, CommittedEntryIndexesAreNonZero
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, Ind, CommittedEntryIndexesAreNonZero
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/29
\* finished 8/29
\* approx 3 min
LEMMA CommittedTermMatchesEntryAndNext ==
ASSUME Ind, Next
PROVE CommittedTermMatchesEntry'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, CommittedTermMatchesEntry, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, CommittedTermMatchesEntry, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF OSM!RollbackEntries, Ind, CommittedTermMatchesEntry, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, Ind, CommittedTermMatchesEntry, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, CommittedTermMatchesEntry
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            BY <2>1 DEF OSM!BecomeLeader, Ind, CommittedTermMatchesEntry
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, Ind, CommittedTermMatchesEntry
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


\* began: 8/29
\* finished: 9/1
LEMMA LeaderCompletenessAndNext ==
ASSUME Ind, Next
PROVE LeaderCompleteness'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, LeaderCompleteness, InLog, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, LeaderCompleteness, InLog, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3, PrimaryAndSecondaryAreDifferent, Z3 DEF OSM!RollbackEntries, Ind, LeaderCompleteness, InLog, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <2>4
            <3>2. \A s \in Server : currentTerm[p] >= configTerm[s]
                BY <3>1, QuorumsIdentical, CommitEntryImpliesCurrentTermGreaterThanConfigTerms DEF Ind
            <3>3. \A s \in Server : (state[s] = Primary /\ s # p) => currentTerm[s] < currentTerm[p]
                BY <3>1, <3>2 DEF OSM!CommitEntry, Ind, OnePrimaryPerTerm, PrimaryConfigTermEqualToCurrentTerm, TypeOK
            <3>. QED BY <3>1, <3>3 DEF OSM!CommitEntry, Ind, LeaderCompleteness, InLog, OnePrimaryPerTerm, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, Ind, LeaderCompleteness, InLog, TypeOK
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, Ind, LeaderCompleteness, InLog, TypeOK
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A c \in committed : InLog(c.entry, p) BY <3>1, ElectedLeadersHaveAllCommits
            <3>3. \A c \in committed : InLog(c.entry, p)' BY <3>1, <3>2 DEF OSM!BecomeLeader, InLog, TypeOK
            <3>4. \A s \in Server : (state[s] = Primary /\ s # p) => (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))
                BY <3>1 DEF OSM!BecomeLeader, Ind, LeaderCompleteness
            <3>5. \A s \in Server : (state'[s] = Primary /\ s # p) => (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))'
                BY <3>1, <3>4, PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader, InLog, TypeOK
            <3>. QED BY <3>1, <3>3, <3>5 DEF LeaderCompleteness, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, Ind, LeaderCompleteness, InLog, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 9/11
\* finished 9/12
LEMMA LogsLaterThanCommittedMustHaveCommittedAndNext ==
ASSUME Ind, Next
PROVE LogsLaterThanCommittedMustHaveCommitted'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE (\A s \in Server : \A c \in committed :
                            (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
                                \A d \in committed : (d.term <= c.term) => (Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term))'
                  BY DEF LogsLaterThanCommittedMustHaveCommitted
            <3>2. TAKE s \in Server
            <3>3. TAKE c \in committed'
            <3>4. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
                  PROVE \A d \in committed' : (d.term <= c.term) => (Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term) OBVIOUS
            <3>5. TAKE d \in committed'
            <3>6. SUFFICES ASSUME d.term <= c.term
                  PROVE Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term OBVIOUS
            <3>7. PICK p \in Server : OSM!ClientRequest(p) BY <2>1
            <3>8. CASE s # p BY <3>4, <3>6, <3>7, <3>8, Zenon DEF OSM!ClientRequest, Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
            <3>9. CASE s = p \* <3>9 isn't used, clearly the CASE split isn't necessary
                BY Z3,<3>4, <3>6, <3>7, <3>8 DEF OSM!ClientRequest, InLog, TypeOK,
                    Ind, LogsLaterThanCommittedMustHaveCommitted, LeaderCompleteness, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry
            <3>. QED BY <3>8, <3>9
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE (\A s \in Server : \A c \in committed :
                            (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
                                \A d \in committed : (d.term <= c.term) => (Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term))'
                  BY DEF LogsLaterThanCommittedMustHaveCommitted
            <3>2. TAKE s \in Server
            <3>3. TAKE c \in committed'
            <3>4. SUFFICES ASSUME NEW i \in DOMAIN log'[s], log'[s][i] > c.term
                  PROVE \A d \in committed' : (d.term <= c.term) => (Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term) OBVIOUS
            <3>5. TAKE d \in committed'
            <3>6. SUFFICES ASSUME d.term <= c.term
                  PROVE Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term OBVIOUS
            <3>7. PICK u,v \in Server : OSM!GetEntries(u, v) BY <2>2
            <3>8. CASE s # u BY <3>4, <3>6, <3>7, <3>8, Zenon DEF OSM!GetEntries, OSM!Empty, Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
            <3>9. CASE s = u
                <4>1. CASE i < Len(log'[s])
                    <5>1. c \in committed /\ d \in committed BY <3>4, <3>7, <3>9 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>2. i \in DOMAIN log[s] BY <3>4, <3>7, <3>9, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>3. log[s][i] > c.term BY <3>4, <3>6, <3>7, <5>1, <5>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>4. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term BY <3>6, <5>1, <5>2, <5>3 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                    <5>. QED BY <3>7, <3>9, <5>4 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry
                <4>2. CASE i = Len(log'[s])
                    <5>1. c \in committed /\ d \in committed BY <3>4, <3>7, <3>9 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>2. i \in DOMAIN log[v] BY <3>4, <3>7, <3>9, <4>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>3. log[v][i] > c.term BY <3>4, <3>7, <3>9, <4>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>4. Len(log[v]) >= d.entry[1] /\ log[v][d.entry[1]] = d.term
                        BY <3>6, <3>7, <3>9, <5>1, <5>2, <5>3, Zenon DEF Ind, LogsLaterThanCommittedMustHaveCommitted, OSM!GetEntries, OSM!Empty, TypeOK
                    <5>5. PICK j \in DOMAIN log[v] : (log[v][j] = d.term /\ j = d.entry[1])
                        BY <5>1, <5>4 DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK
                    <5>6. j \in DOMAIN log'[s]
                        <6>1. log[v][j] < log[v][i] BY <1>ok, <3>6, <3>7, <3>9, <5>1, <5>3, <5>5 DEF OSM!GetEntries, OSM!Empty, TypeOK
                        <6>2. j < i
                            <7>1. SUFFICES ASSUME j >= i
                                  PROVE FALSE BY <1>ok, <5>2, <5>5 DEF TypeOK
                            <7>2. log[v][j] >= log[v][i] BY <5>2, <5>5, <7>1 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
                            <7>. QED BY <1>ok, <3>7, <5>2, <5>5, <6>1, <7>2 DEF TypeOK
                        <6>. QED BY <3>7, <3>9, <4>2, <5>1, <5>2, <5>4, <5>5, <6>2 DEF Ind, CommittedEntryIndexesAreNonZero, OSM!GetEntries, OSM!Empty, TypeOK
                    <5>7. log'[s][j] = log[v][j] BY <3>7, <3>9, <5>4, <5>5, <5>6 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, OSM!Empty, TypeOK
                    <5>. QED BY <3>7, <3>9, <5>1, <5>5, <5>6, <5>7 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>. QED BY <3>4, <3>7, <3>9, <4>1, <4>2 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry
            <3>. QED BY <3>8, <3>9
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE (\A s \in Server : \A c \in committed :
                            (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
                                \A d \in committed : (d.term <= c.term) => (Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term))'
                  BY DEF LogsLaterThanCommittedMustHaveCommitted
            <3>2. TAKE s \in Server
            <3>3. TAKE c \in committed'
            <3>4. SUFFICES ASSUME NEW i \in DOMAIN log'[s], log'[s][i] > c.term
                  PROVE \A d \in committed' : (d.term <= c.term) => (Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term) OBVIOUS
            <3>5. TAKE d \in committed'
            <3>6. SUFFICES ASSUME d.term <= c.term
                  PROVE Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term OBVIOUS
            <3>7. PICK u,v \in Server : OSM!RollbackEntries(u, v) BY <2>3
            <3>8. CASE s # u BY <3>4, <3>6, <3>7, <3>8, Zenon DEF OSM!RollbackEntries, Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
            <3>9. CASE s = u
                <4>1. i \in DOMAIN log[s] /\ log[s][i] > c.term BY <3>4, <3>7, <3>9 DEF OSM!RollbackEntries, TypeOK
                <4>2. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term
                    BY <3>6, <3>7, <3>9, <4>1, Zenon DEF Ind, LogsLaterThanCommittedMustHaveCommitted, OSM!RollbackEntries, TypeOK
                <4>3. PICK j \in DOMAIN log[s] : (log[s][j] = d.term /\ j = d.entry[1])
                    BY <3>7, <3>9, <4>2 DEF Ind, CommittedEntryIndexesAreNonZero, OSM!RollbackEntries, TypeOK
                <4>4. j \in DOMAIN log'[s]
                    <5>1. log[s][j] < log[s][i] BY <1>ok, <3>6, <3>7, <3>9, <4>1, <4>2, <4>3 DEF OSM!RollbackEntries, TypeOK
                    <5>2. j < i
                        <6>1. SUFFICES ASSUME j >= i
                              PROVE FALSE BY <1>ok, <4>1, <4>3 DEF TypeOK
                        <6>2. log[s][j] >= log[s][i] BY <4>1, <4>3, <6>1 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
                        <6>. QED BY <1>ok, <3>7, <4>1, <4>3, <5>1, <6>2 DEF OSM!RollbackEntries, TypeOK
                    <5>. QED BY <3>7, <3>9, <4>1, <4>3, <5>1, <5>2 DEF Ind, CommittedEntryIndexesAreNonZero, OSM!RollbackEntries, TypeOK
                <4>. QED BY <3>4, <3>7, <3>9, <4>2, <4>3, <4>4 DEF OSM!RollbackEntries, TypeOK
            <3>. QED BY <3>8, <3>9
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE (\A s \in Server : \A c \in committed :
                            (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
                                \A d \in committed : (d.term <= c.term) => (Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term))'
                  BY DEF LogsLaterThanCommittedMustHaveCommitted
            <3>2. TAKE s \in Server
            <3>3. TAKE c \in committed'
            <3>4. SUFFICES ASSUME NEW i \in DOMAIN log'[s], log'[s][i] > c.term
                  PROVE \A d \in committed' : (d.term <= c.term) => (Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term) OBVIOUS
            <3>5. TAKE d \in committed'
            <3>6. SUFFICES ASSUME d.term <= c.term
                  PROVE Len(log'[s]) >= d.entry[1] /\ log'[s][d.entry[1]] = d.term OBVIOUS
            <3>7. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <2>4, QuorumsIdentical DEF Ind
            <3>8. CASE d \in committed
                <4>1. i \in DOMAIN log[s] BY <3>4, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>2. log[s][i] > d.term BY <1>ok, <3>4, <3>6, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>3. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term
                    BY <3>8, <4>1, <4>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                <4>. QED BY <3>7, <4>3 DEF OSM!CommitEntry, TypeOK
            <3>9. CASE d \notin committed
                \* this case is not possible.  proof by contradiction
                <4>.  DEFINE pLen == Len(log[p])
                <4>q. PICK Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <3>7
                <4>1. d = [entry |-> <<pLen, currentTerm[p]>>, term |-> currentTerm[p]] BY <3>7, <3>9 DEF OSM!CommitEntry, TypeOK
                <4>2. log[p][pLen] = d.term BY <3>7, <4>1 DEF OSM!CommitEntry, TypeOK
                <4>3. log[s][i] > d.term BY <1>ok, <3>4, <3>6, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>4. PICK t \in Server : configTerm[t] > log[p][pLen]
                    <5>1. \E t \in Server : configTerm[t] >= log[s][i] BY <3>4, <3>7 DEF Ind, LogEntryInTermImpliesConfigInTerm, OSM!CommitEntry, TypeOK
                    <5>. QED BY <1>ok, <3>7, <4>2, <4>3, <5>1 DEF OSM!CommitEntry, TypeOK
                <4>5. PICK n \in Q : currentTerm[n] >= configTerm[t] BY <4>q, <4>4, CommitEntryImpliesInActiveConfigSet DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. currentTerm[n] > currentTerm[p]
                    <5>1. currentTerm[n] > log[p][pLen] BY <1>ok, <4>q, <4>4, <4>5 DEF OSM!CommitEntry, Quorums, TypeOK
                    <5>. QED BY <4>q, <4>1, <5>1 DEF OSM!CommitEntry, Quorums, TypeOK
                <4>. QED BY <4>q, <4>1, <4>6 DEF OSM!CommitEntry, OSM!ImmediatelyCommitted, Quorums, TypeOK
            <3>. QED BY <3>8, <3>9
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, LogsLaterThanCommittedMustHaveCommitted
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            BY <2>1 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, OSM!UpdateTerms, OSM!UpdateTermsExpr,
                CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 9/1
\* finished 9/9
\* ReconfigImpliesCommitTermsSmallerOrEqual and ReconfigImpliesHasQuorumWithAllCommits
\* were likely the most work for this one
LEMMA ActiveConfigsOverlapWithCommittedEntryAndNext ==
ASSUME Ind, Next
PROVE ActiveConfigsOverlapWithCommittedEntry'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK p \in Server : OSM!ClientRequest(p) BY <2>1
            <3>3. ActiveConfigSet' = ActiveConfigSet /\ committed' = committed /\ config' = config
                BY <1>1, <3>2 DEF csmVars, OSM!ClientRequest, ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
            <3>4. TAKE c \in committed'
            <3>5. TAKE s \in ActiveConfigSet'
            <3>6. TAKE Q \in Quorums(config[s])'
            <3>7. c \in committed /\ s \in ActiveConfigSet /\ Q \in Quorums(config[s])
                BY <3>2, <3>3, <3>4, <3>5 DEF OSM!ClientRequest, Quorums, TypeOK
            <3>8. PICK n \in Q : InLog(c.entry, n) BY <3>1, <3>7 DEF Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
            <3>9. InLog(c.entry, n)' BY <3>2, <3>4, <3>6, <3>7, <3>8 DEF OSM!ClientRequest, Quorums, InLog, TypeOK
            <3>. QED BY <3>9 DEF InLog
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK s, t \in Server : OSM!GetEntries(s, t) BY <2>2
            <3>3. ActiveConfigSet' = ActiveConfigSet /\ committed' = committed /\ config' = config
                BY <1>1, <3>2 DEF csmVars, OSM!GetEntries, ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
            <3>4. TAKE c \in committed'
            <3>5. TAKE u \in ActiveConfigSet'
            <3>6. TAKE Q \in Quorums(config[u])'
            <3>7. c \in committed /\ u \in ActiveConfigSet /\ Q \in Quorums(config[u])
                BY <3>2, <3>3, <3>4, <3>5 DEF OSM!ClientRequest, Quorums, TypeOK
            <3>8. PICK n \in Q : InLog(c.entry, n) BY <3>1, <3>7 DEF Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
            <3>9. InLog(c.entry, n)' BY <3>2, <3>4, <3>6, <3>7, <3>8 DEF OSM!GetEntries, Quorums, InLog, TypeOK
            <3>. QED BY <3>9 DEF InLog
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK s, t \in Server : OSM!RollbackEntries(s, t) BY <2>3
            <3>3. ActiveConfigSet' = ActiveConfigSet /\ committed' = committed /\ config' = config
                BY <1>1, <3>2 DEF csmVars, OSM!RollbackEntries, ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
            <3>4. TAKE c \in committed'
            <3>5. TAKE u \in ActiveConfigSet'
            <3>6. TAKE Q \in Quorums(config[u])'
            <3>7. c \in committed /\ u \in ActiveConfigSet /\ Q \in Quorums(config[u])
                BY <3>2, <3>3, <3>4, <3>5 DEF OSM!RollbackEntries, Quorums, TypeOK
            <3>8. PICK n \in Q : InLog(c.entry, n) BY <3>1, <3>7 DEF Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
            <3>n. n \in Server BY <1>ok, <3>2, <3>5, <3>6, <3>8 DEF OSM!RollbackEntries,
                ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, Quorums, TypeOK
            <3>9. (n = s) => InLog(c.entry, n)'
                \* proof by contradiction.  if the committed entry is rolled back then it must have been the last entry of n's
                \* log before the rollback.  thus t must have the committed entry in its log because LastTerm(log[n]) < LastTerm(log[t]).
                \* however, LogMatching implies that n must be a prefix of t which is a contradiction.
                <4>1. SUFFICES ASSUME n = s, ~InLog(c.entry, n)'
                      PROVE FALSE OBVIOUS
                <4>2. Len(log[n]) = c.entry[1] /\ LastTerm(log[n]) = c.entry[2] BY <3>n, <3>2, <3>8, <4>1 DEF OSM!RollbackEntries, LastTerm, InLog, TypeOK
                <4>3. InLog(c.entry, t)
                    <5>1. \E i \in DOMAIN log[t] : log[t][i] > c.term
                        BY <3>2, <4>1, <4>2 DEF OSM!RollbackEntries, OSM!CanRollback, OSM!LastTerm, InLog, LastTerm, TypeOK, Ind, CommittedTermMatchesEntry
                    <5>2. c \in committed BY <3>2, <3>4, <4>1 DEF OSM!RollbackEntries, TypeOK
                    <5>3. Len(log[t]) >= c.entry[1] /\ log[t][c.entry[1]] = c.term
                        BY <4>1, <5>1, <5>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                    <5>. QED BY <3>2, <3>4, <4>1, <5>3 DEF OSM!RollbackEntries, Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero, InLog, TypeOK
                <4>4. log[t][c.entry[1]] = log[n][c.entry[1]] BY <1>ok, <4>2, <4>3 DEF LastTerm, InLog, TypeOK
                <4>5. Len(log[n]) <= Len(log[t]) /\ \A i \in DOMAIN log[n] : log[n][i] = log[t][i]
                    <5>.  DEFINE nLastIdx == Len(log[n])
                    <5>1. nLastIdx = c.entry[1] BY <4>2
                    <5>2. nLastIdx \in DOMAIN log[t] BY <4>3, <5>1 DEF Ind, CommittedEntryIndexesAreNonZero, InLog, TypeOK
                    <5>3. Len(log[n]) <= Len(log[t]) BY <5>1, <5>2
                    <5>4. log[n][nLastIdx] = log[t][nLastIdx] BY <5>1, <5>2, <4>4 DEF TypeOK
                    <5>5. EqualUpTo(log[n], log[t], nLastIdx) BY <3>n, <5>2, <5>3, <5>4 DEF Ind, LogMatching, EqualUpTo, TypeOK
                    <5>. QED BY <5>3, <5>5 DEF EqualUpTo
                <4>6. OSM!IsPrefix(log[n], log[t]) BY <4>5 DEF OSM!IsPrefix
                <4>. QED BY <3>2, <3>n, <4>1, <4>6 DEF OSM!RollbackEntries, OSM!CanRollback, OSM!IsPrefix, TypeOK
            <3>10. (n # s) => InLog(c.entry, n)' BY <3>2, <3>4, <3>6, <3>7, <3>8 DEF OSM!RollbackEntries, Quorums, InLog, TypeOK
            <3>. QED BY <3>9, <3>10 DEF InLog
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <2>4
            <3>3. PICK pQ \in Quorums(config[p]) : OSM!CommitEntry(p, pQ) BY <3>2, QuorumsIdentical DEF Ind
            <3>4. TAKE c \in committed'
            <3>5. TAKE s \in ActiveConfigSet'
            <3>6. TAKE sQ \in Quorums(config[s])'
            <3>7. s \in ActiveConfigSet /\ sQ \in Quorums(config[s])
                BY <1>1, <3>2 DEF csmVars, OSM!CommitEntry, ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, Quorums, TypeOK
            <3>8. CASE c \in committed
                BY <3>2, <3>7, <3>8 DEF OSM!CommitEntry, Ind, ActiveConfigsOverlapWithCommittedEntry, InLog, TypeOK
            <3>9. CASE c \notin committed
                <4>.  DEFINE ind == Len(log[p])
                <4>1. c.entry = <<ind, currentTerm[p]>> /\ c.term = currentTerm[p] BY <3>2, <3>9 DEF OSM!CommitEntry, TypeOK
                <4>2. \A t \in pQ :
                            /\ Len(log[t]) >= ind
                            /\ log[t][ind] = currentTerm[p]
                            /\ currentTerm[t] = currentTerm[p]
                    <5>1. OSM!ImmediatelyCommitted(<<ind,currentTerm[p]>>, pQ) BY <3>2, <3>3, <3>9 DEF OSM!CommitEntry, TypeOK
                    <5>. QED BY <5>1 DEF OSM!ImmediatelyCommitted, OSM!InLog, TypeOK
                <4>3. p \in ActiveConfigSet BY <3>2, <3>3, CommitImpliesInActiveConfigSet
                <4>4. PICK n \in sQ : n \in pQ BY <3>2, <3>3, <3>7, <4>3 DEF Ind, ActiveConfigsOverlap, QuorumsOverlap, Quorums, TypeOK
                <4>5. InLog(c.entry, n) BY <3>2, <3>3, <4>1, <4>2, <4>4 DEF OSM!CommitEntry, Quorums, InLog, TypeOK
                <4>. QED BY <3>2, <4>5 DEF OSM!CommitEntry, InLog, TypeOK
            <3>. QED BY <3>8, <3>9
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK p \in Server, newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>3. TAKE c \in committed'
            <3>4. TAKE s \in ActiveConfigSet'
            <3>5. c \in committed BY <1>2 DEF osmVars
            <3>6. s \in ActiveConfigSet BY <3>2, ReconfigImpliesSameActiveConfigSet DEF Ind
            <3>s. s \in Server BY <3>6 DEF ActiveConfigSet, ConfigDisabled
            <3>7. CASE s # p
                <4>1. \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c.entry, n)
                    BY <3>2, <3>5, <3>6, <3>7 DEF Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
                <4>. QED BY <1>2, <3>2, <3>7, <4>1, Z3 DEF osmVars, CSM!Reconfig, TypeOK, Quorums, InLog
            <3>8. CASE s = p
                <4>1. \A Q \in Quorums(newConfig) : \E n \in Q : InLog(c.entry, n)
                    BY <3>2, <3>5, <3>8, ReconfigImpliesHasQuorumWithAllCommits
                <4>. QED BY <1>ok, <1>2, <3>2, <3>8, <4>1 DEF osmVars, CSM!Reconfig, TypeOK, Quorums, InLog
            <3>. QED BY <3>7, <3>8
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK s,t \in Server : CSM!SendConfig(s, t) BY <2>2
            <3>3. TAKE c \in committed'
            <3>4. TAKE u \in ActiveConfigSet'
            <3>5. c \in committed BY <1>2 DEF osmVars
            <3>6. CASE u # t
                <4>1. u \in ActiveConfigSet BY <3>2, <3>4, <3>6, SendConfigActiveConfigSetIdenticalExceptRecipient DEF Ind
                <4>2. \A Q \in Quorums(config[u]) : \E n \in Q : InLog(c.entry, n)
                    BY <3>5, <4>1 DEF ActiveConfigSet, ConfigDisabled, Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
                <4>. QED BY <1>2, <3>2, <3>6, <4>2 DEF osmVars, CSM!SendConfig, InLog, TypeOK
            <3>7. CASE u = t
                <4>1. s \in ActiveConfigSet
                    BY <1>ok, <3>2, <3>4, <3>7 DEF CSM!SendConfig, CSM!IsNewerConfig, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK
                <4>2. \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c.entry, n)
                    BY <3>5, <4>1 DEF ActiveConfigSet, ConfigDisabled, Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
                <4>. QED BY <1>ok, <1>2, <3>2, <3>6, <4>2 DEF osmVars, CSM!SendConfig, InLog, TypeOK
            <3>. QED BY <3>6, <3>7
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>3. TAKE c \in committed'
            <3>4. TAKE s \in ActiveConfigSet'
            <3>5. c \in committed BY <3>2 DEF OSM!BecomeLeader
            <3>6. s \in ActiveConfigSet BY <3>2, BecomeLeaderActiveConfigSetIdentical DEF Ind
            <3>7. \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c.entry, n)
                BY <3>5, <3>6 DEF ActiveConfigSet, ConfigDisabled, Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
            <3>. QED BY <3>2, <3>5, <3>7 DEF OSM!BecomeLeader, CSM!BecomeLeader, ActiveConfigSet, ConfigDisabled, InLog, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A c \in committed' : \A s \in ActiveConfigSet' :
                            \A Q \in Quorums(config[s])' : \E n \in Q : InLog(c.entry, n)'
                  BY DEF ActiveConfigsOverlapWithCommittedEntry
            <3>2. PICK s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t) BY <2>2
            <3>3. TAKE c \in committed'
            <3>4. TAKE u \in ActiveConfigSet'
            <3>5. c \in committed BY <3>2 DEF OSM!UpdateTerms
            <3>6. u \in ActiveConfigSet BY <3>2 DEF OSM!UpdateTerms, CSM!UpdateTerms, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
            <3>7. \A Q \in Quorums(config[u]) : \E n \in Q : InLog(c.entry, n)
                BY <3>5, <3>6 DEF ActiveConfigSet, ConfigDisabled, Ind, ActiveConfigsOverlapWithCommittedEntry, TypeOK
            <3>. QED BY <3>2, <3>5, <3>7 DEF OSM!UpdateTerms, CSM!UpdateTerms, ActiveConfigSet, ConfigDisabled, InLog, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 9/10
\* finished 9/11
LEMMA NewerConfigsDisablePrimaryCommitsInOlderTermsAndNext ==
ASSUME Ind, Next
PROVE NewerConfigsDisablePrimaryCommitsInOlderTerms'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF csmVars, OSM!ClientRequest, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF csmVars, OSM!GetEntries, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF csmVars, OSM!RollbackEntries, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF csmVars, OSM!CommitEntry, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s,t \in Server :
                            (state'[t] = Primary /\ currentTerm'[t] < configTerm'[s]) =>
                                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t]
                  BY DEF NewerConfigsDisablePrimaryCommitsInOlderTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in Server
            <3>4. PICK p \in Server, newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>5. CASE t = p
                <4>1. \A u \in Server : currentTerm[p] >= configTerm[u] BY <3>4, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF Ind
                <4>2. \A u \in Server : currentTerm'[p] >= configTerm'[u] BY <1>ok, <3>4, <4>1 DEF CSM!Reconfig, TypeOK
                <4>. QED BY <1>2, <3>4, <3>5, <4>2 DEF osmVars, CSM!Reconfig, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
            <3>6. CASE t # p
                <4>1. SUFFICES ASSUME state'[t] = Primary, currentTerm'[t] < configTerm'[s]
                      PROVE \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t] OBVIOUS
                <4>2. state[t] = Primary BY <3>4, <4>1 DEF CSM!Reconfig
                <4>3. currentTerm[t] < configTerm[s] BY <3>4, <4>1, ReconfigImpliesConfigTermUnchanged DEF CSM!Reconfig, TypeOK
                <4>4. TAKE Q \in Quorums(config'[t])
                <4>5. Q \in Quorums(config[t]) BY <3>4, <3>6, <4>4 DEF CSM!Reconfig, Quorums, TypeOK
                <4>6. \E n \in Q : currentTerm[n] > currentTerm[t] BY <4>2, <4>3, <4>5 DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
                <4>. QED BY <3>4, <3>6, <4>5, <4>6 DEF CSM!Reconfig, Quorums, TypeOK
            <3>. QED BY <3>5, <3>6
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s,t \in Server :
                            (state'[t] = Primary /\ currentTerm'[t] < configTerm'[s]) =>
                                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t]
                  BY DEF NewerConfigsDisablePrimaryCommitsInOlderTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in Server
            <3>4. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>5. CASE t = p
                <4>1. \A u \in Server : currentTerm[p] >= configTerm[u] BY <3>4, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind
                <4>2. \A u \in Server : currentTerm'[p] >= configTerm'[u] BY <1>ok, <3>4, <4>1 DEF CSM!BecomeLeader, TypeOK
                <4>. QED BY <1>2, <3>4, <3>5, <4>2 DEF osmVars, CSM!BecomeLeader, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
            <3>6. CASE t # p
                <4>1. SUFFICES ASSUME state'[t] = Primary, currentTerm'[t] < configTerm'[s]
                      PROVE \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t] OBVIOUS
                <4>2. state[t] = Primary BY <1>ok, <3>4, <3>6, <4>1 DEF CSM!BecomeLeader, TypeOK
                <4>3. currentTerm[t] <= currentTerm[p]
                    BY <3>4, <3>6, <4>1, <4>2, ElectedLeadersCurrentTermGreaterThanConfigTerms, Zenon
                        DEF Ind, PrimaryConfigTermEqualToCurrentTerm, CSM!BecomeLeader, TypeOK
                \* took some time to find the optimal case split here
                <4>4. CASE t \in ActiveConfigSet
                    <5>1. PICK pQ \in Quorums(config[p]) : OSM!BecomeLeader(p, pQ) /\ CSM!BecomeLeader(p, pQ) BY <3>4
                    <5>2. config'[t] = config[t] BY <3>4, <3>6, <4>1, <5>1 DEF CSM!BecomeLeader, TypeOK
                    <5>t. t \notin pQ BY <3>4, <3>6, <4>1, <5>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader, TypeOK
                    <5>3. \A Q \in Quorums(config[t]) : Q \cap pQ # {}
                        BY <3>4, <4>4, <5>1, ElectedLeadersInActiveConfigSet DEF Ind, ActiveConfigsOverlap, QuorumsOverlap, Quorums, TypeOK
                    <5>4. \A u \in pQ : currentTerm'[u] > currentTerm[t]
                        BY <1>ok, <3>4, <4>3, <5>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF CSM!BecomeLeader, Quorums, TypeOK
                    <5>5. \A Q \in Quorums(config[t]) : \E u \in Q : currentTerm'[u] > currentTerm'[t]
                        <6>1. \A Q \in Quorums(config[t]) : \E u \in Q : u \in pQ BY <3>4, <5>1, <5>3 DEF Quorums, TypeOK
                        <6>2. \A Q \in Quorums(config[t]) : \E u \in Q : currentTerm'[u] > currentTerm[t]
                            BY <3>4, <5>1, <5>4, <6>1 DEF CSM!BecomeLeader, Quorums, TypeOK
                        <6>3. currentTerm'[t] = currentTerm[t] BY <3>4, <4>1, <5>1, <5>t DEF CSM!BecomeLeader, TypeOK
                        <6>. QED BY <3>4, <5>1, <6>2, <6>3 DEF Quorums, TypeOK
                    <5>. QED BY <3>4, <5>1, <5>2, <5>5, Zenon DEF CSM!BecomeLeader, Quorums, TypeOK
                <4>5. CASE t \notin ActiveConfigSet
                    <5>1. TAKE Q \in Quorums(config'[t])
                    <5>2. Q \in Quorums(config[t]) BY <3>4, <3>6, <4>1 DEF CSM!BecomeLeader, Quorums, TypeOK
                    <5>3. PICK n \in Q : currentTerm[t] < configTerm[n]
                        <6>1. PICK n \in Q : CSM!NewerConfig(CV(n), CV(t)) BY <4>5, <5>2 DEF ActiveConfigSet, ConfigDisabled, Quorums
                        <6>2. configTerm[t] < configTerm[n] BY <1>ok, <4>2, <5>2, <6>1, ConfigNewerThanPrimaryImpliesConfigTermIsNewer DEF Quorums, TypeOK
                        <6>. QED BY <4>2, <6>2 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                    <5>4. currentTerm[p] >= configTerm[n] BY <1>ok, <3>4, <5>2, <5>3, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Quorums, TypeOK
                    <5>5. currentTerm[p] > currentTerm[t] BY <1>ok, <3>4, <5>2, <5>3, <5>4 DEF CSM!BecomeLeader, Quorums, TypeOK
                    <5>6. PICK m \in Q : currentTerm[m] > currentTerm[t]
                        BY <4>2, <5>2, <5>3 DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, Quorums, TypeOK
                    <5>7. currentTerm[m] > currentTerm[t] BY <5>5, <5>6
                    <5>8. currentTerm'[m] >= currentTerm[m] BY <1>ok, <3>4, <5>2, <5>6 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
                    <5>9. currentTerm'[t] = currentTerm[t] BY <3>4, <3>6, <4>1, <5>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <1>ok, <3>4, <3>6, <5>2, <5>7, <5>8, <5>9 DEF CSM!BecomeLeader, Quorums, TypeOK
                <4>. QED BY <4>4, <4>5
            <3>. QED BY <3>5, <3>6
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s,t \in Server :
                            (state'[t] = Primary /\ currentTerm'[t] < configTerm'[s]) =>
                                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t]
                  BY DEF NewerConfigsDisablePrimaryCommitsInOlderTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in Server
            <3>4. SUFFICES ASSUME state'[t] = Primary, currentTerm'[t] < configTerm'[s]
                  PROVE \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] > currentTerm'[t] OBVIOUS
            <3>5. PICK u,v \in Server : OSM!UpdateTerms(u,v) /\ CSM!UpdateTerms(u,v) BY <2>2
            <3>6. t # v BY <1>ok, <3>4, <3>5, PrimaryAndSecondaryAreDifferent DEF CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
            <3>. QED BY <3>4, <3>5, <3>6, Z3 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

=============================================================================
