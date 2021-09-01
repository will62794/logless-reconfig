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
            BY <2>3, PrimaryAndSecondaryAreDifferent DEF OSM!RollbackEntries, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
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

\* began: 9/1
LEMMA ActiveConfigsOverlapWithCommittedEntryAndNext ==
ASSUME TypeOK, Ind, Next
PROVE ActiveConfigsOverlapWithCommittedEntry'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            \* absolutely ridiculous that I need to spell this out
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
            \* thanks tlaps, can't believe i have to spell it out again
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
            <3>n. n \in Server BY <3>2, <3>5, <3>6, <3>8 DEF OSM!RollbackEntries,
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
                    <5>2. Len(log[t]) >= c.entry[1] /\ log[t][c.entry[1]] = c.term
                        BY <3>2, <3>4, <4>1, <5>1 DEF OSM!RollbackEntries, Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                    <5>. QED BY <3>2, <3>4, <4>1, <5>2 DEF OSM!RollbackEntries, Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero, InLog, TypeOK
                <4>4. log[t][c.entry[1]] = log[n][c.entry[1]] BY <4>2, <4>3 DEF LastTerm, InLog, TypeOK
                <4>5. Len(log[n]) <= Len(log[t]) /\ \A i \in DOMAIN log[n] : log[n][i] = log[t][i]
                    <5>1. Len(log[n]) <= Len(log[t])
                        <6>.  DEFINE nLastIdx == Len(log[n])
                        <6>1. nLastIdx = c.entry[1] BY <4>2
                        <6>2. nLastIdx \in DOMAIN log[t] BY <4>3, <6>1 DEF Ind, CommittedEntryIndexesAreNonZero, InLog, TypeOK
                        <6>. QED BY <6>1, <6>2 DEF TypeOK
                    <5>2. \A j \in Nat : (j > 0 /\ j < Len(log[n])) => log[n][j] = log[t][j]
                        BY <3>2, <3>n, <4>1, <4>2, <4>4, <5>1 DEF Ind, LogMatching, EqualUpTo, LastTerm, TypeOK
                    <5>. QED BY <3>2, <3>n, <4>1, <4>2, <4>3, <4>4, <5>1, <5>2 DEF InLog, TypeOK, InLog
                <4>6. OSM!IsPrefix(log[n], log[t]) BY <4>5 DEF OSM!IsPrefix
                <4>. QED BY <3>2, <3>n, <4>1, <4>6 DEF OSM!RollbackEntries, OSM!CanRollback, OSM!IsPrefix, TypeOK
            <3>10. (n # s) => InLog(c.entry, n)' BY <3>2, <3>4, <3>6, <3>7, <3>8 DEF OSM!RollbackEntries, Quorums, InLog, TypeOK
            <3>. QED BY <3>9, <3>10 DEF InLog
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


\* Template
(*
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next
*)

=============================================================================
