----------------------------- MODULE LeaderCompletenessLemmas -----------------------------

EXTENDS MongoRaftReconfig, Defs, Axioms, TypeOK, Lib, LeaderCompletenessLib

\* began: 8/29
\* finished 8/29
\* approx 3 min
LEMMA CommittedEntryIndexesAreNonZeroAndNext ==
ASSUME TypeOK, Ind, Next
PROVE CommittedEntryIndexesAreNonZero'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF OSM!RollbackEntries, Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
ASSUME TypeOK, Ind, Next
PROVE CommittedTermMatchesEntry'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, CommittedTermMatchesEntry, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, CommittedTermMatchesEntry, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF OSM!RollbackEntries, Ind, CommittedTermMatchesEntry, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
\* the toughest part was figuring out that TLAPS can't handle long files; i wasted
\* about 2-3 trying to figure out the induction.  in a nutshell, when the file was
\* too long, TLAPS couldn't prove:
\*  <n>m. TRUE BY Isa
\* I'm not sure if it's an issue with just isabelle + long files; either way I refactored
\* the project into separate files and everything works.
LEMMA LeaderCompletenessGeneralizedAndNext ==
ASSUME TypeOK, Ind, Next
PROVE LeaderCompletenessGeneralized'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3, PrimaryAndSecondaryAreDifferent, Z3 DEF OSM!RollbackEntries, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            <3>1. PICK p \in Server : \E Q \in OSM!QuorumsAt(p) : OSM!CommitEntry(p, Q) BY <2>4
            <3>2. \A s \in Server : currentTerm[p] >= configTerm[s]
                BY <3>1, QuorumsIdentical, CommitEntryImpliesCurrentTermGreaterThanConfigTerms DEF OSM!QuorumsAt
            <3>3. \A s \in Server : (state[s] = Primary /\ s # p) => currentTerm[s] < currentTerm[p]
                BY <3>1, <3>2 DEF OSM!CommitEntry, Ind, OnePrimaryPerTerm, PrimaryConfigTermEqualToCurrentTerm, TypeOK
            <3>. QED BY <3>1, <3>3 DEF OSM!CommitEntry, Ind, LeaderCompletenessGeneralized, InLog, OnePrimaryPerTerm, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A c \in committed : InLog(c.entry, p) BY <3>1, ElectedLeadersHaveAllCommits
            <3>3. \A c \in committed : InLog(c.entry, p)' BY <3>1, <3>2 DEF OSM!BecomeLeader, InLog, TypeOK
            <3>4. \A s \in Server : (state[s] = Primary /\ s # p) => (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))
                BY <3>1 DEF OSM!BecomeLeader, Ind, LeaderCompletenessGeneralized
            <3>5. \A s \in Server : (state'[s] = Primary /\ s # p) => (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))'
                BY <3>1, <3>4, PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader, InLog, TypeOK
            <3>. QED BY <3>1, <3>3, <3>5 DEF LeaderCompletenessGeneralized, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 9/11
\* finished 9/12
\* I decided to do this one last because I had a feeling it might be the toughest
\* turns out it wasn't too tough at all
LEMMA LogsLaterThanCommittedMustHaveCommittedAndNext ==
ASSUME TypeOK, Ind, Next
PROVE LogsLaterThanCommittedMustHaveCommitted'
PROOF
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
                    Ind, LogsLaterThanCommittedMustHaveCommitted, LeaderCompletenessGeneralized, CommittedEntryIndexesAreNonZero, CommittedTermMatchesEntry
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
                        <6>1. log[v][j] < log[v][i] BY <3>6, <3>7, <3>9, <5>1, <5>3, <5>5 DEF OSM!GetEntries, OSM!Empty, TypeOK
                        <6>2. j < i
                            \* why was this such a struggle??
                            <7>1. SUFFICES ASSUME j >= i
                                  PROVE FALSE BY <5>2, <5>5 DEF TypeOK
                            <7>2. log[v][j] >= log[v][i] BY <5>2, <5>5, <7>1 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
                            <7>. QED BY <3>7, <5>2, <5>5, <6>1, <7>2 DEF TypeOK
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
                    <5>1. log[s][j] < log[s][i] BY <3>6, <3>7, <3>9, <4>1, <4>2, <4>3 DEF OSM!RollbackEntries, TypeOK
                    <5>2. j < i
                        \* copy pasta job, may not have been as much of a struggle as above but its not worth figuring that out
                        <6>1. SUFFICES ASSUME j >= i
                              PROVE FALSE BY <4>1, <4>3 DEF TypeOK
                        <6>2. log[s][j] >= log[s][i] BY <4>1, <4>3, <6>1 DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK
                        <6>. QED BY <3>7, <4>1, <4>3, <5>1, <6>2 DEF OSM!RollbackEntries, TypeOK
                    <5>. QED BY <3>7, <3>9, <4>1, <4>3, <5>1, <5>2 DEF Ind, CommittedEntryIndexesAreNonZero, OSM!RollbackEntries, TypeOK
                <4>. QED BY <3>4, <3>7, <3>9, <4>2, <4>3, <4>4 DEF OSM!RollbackEntries, TypeOK
            <3>. QED BY <3>8, <3>9
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
            <3>7. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <2>4, QuorumsIdentical DEF OSM!QuorumsAt
            <3>8. CASE d \in committed
                <4>1. i \in DOMAIN log[s] BY <3>4, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>2. log[s][i] > d.term BY <3>4, <3>6, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>3. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term
                    BY <3>8, <4>1, <4>2 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                <4>. QED BY <3>7, <4>3 DEF OSM!CommitEntry, TypeOK
            <3>9. CASE d \notin committed
                \* interestingly enough, this case is not possible.  proof by contradiction
                <4>.  DEFINE pLen == Len(log[p])
                <4>q. PICK Q \in Quorums(config[p]) : OSM!CommitEntry(p, Q) BY <3>7
                <4>1. d = [entry |-> <<pLen, currentTerm[p]>>, term |-> currentTerm[p]] BY <3>7, <3>9 DEF OSM!CommitEntry, TypeOK
                <4>2. log[p][pLen] = d.term BY <3>7, <4>1 DEF OSM!CommitEntry, TypeOK
                <4>3. log[s][i] > d.term BY <3>4, <3>6, <3>7 DEF OSM!CommitEntry, TypeOK
                <4>4. PICK t \in Server : configTerm[t] > log[p][pLen]
                    <5>1. \E t \in Server : configTerm[t] >= log[s][i] BY <3>4, <3>7 DEF Ind, LogEntryInTermImpliesConfigInTerm, OSM!CommitEntry, TypeOK
                    <5>. QED BY <3>7, <4>2, <4>3, <5>1 DEF OSM!CommitEntry, TypeOK
                <4>5. PICK n \in Q : currentTerm[n] >= configTerm[t] BY <4>q, <4>4, CommitEntryImpliesInActiveConfigSet DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. currentTerm[n] > currentTerm[p]
                    <5>1. currentTerm[n] > log[p][pLen] BY <4>q, <4>4, <4>5 DEF OSM!CommitEntry, Quorums, TypeOK
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

=============================================================================
