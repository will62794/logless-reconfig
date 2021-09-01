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
            <3>2. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <3>1
            <3>3. \A c \in committed : \E n \in Q : InLog(c.entry, n)
                BY <3>1, <3>2, ElectedLeadersInActiveConfigSet DEF Ind, ActiveConfigsOverlapWithCommittedEntry
            <3>4. \A c \in committed : InLog(c.entry, p)
                <4>1. TAKE c \in committed
                <4>2. PICK n \in Q : InLog(c.entry, n) BY <3>3
                <4>n. n \in Server
                <4>3. CASE LastTerm(log[p]) > LastTerm(log[n]) /\ Len(log[p]) >= Len(log[n])
                    <5>1. Len(log[n]) > 0
                        BY <4>2 DEF LastTerm, InLog, TypeOK \*Quorums, TypeOK, Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero
                    <5>2. LastTerm(log[n]) > 0
                        BY <3>1, <4>n, <4>1, <4>2, <5>1 DEF Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero, InLog, LastTerm, TypeOK
                    <5>3. \E i \in DOMAIN log[p] : log[p][i] > c.term
                        BY <3>2, <4>1, <4>2, <4>3, <5>1 DEF LastTerm, InLog, Quorums, TypeOK, OSM!BecomeLeader,
                            Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero
                    <5>. QED
                    \*BY <3>1, <4>1, <4>3 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, CommittedTermMatchesEntry, OSM!BecomeLeader, LastTerm, InLog, TypeOK
                <4>4. CASE LastTerm(log[p]) = LastTerm(log[n])
                <4>. QED
                
                (*\* at this point (after <4>2) it should suffices to assum that Len(log[n]) > 0
                <4>3. CASE LastTerm(log[p]) = LastTerm(log[n]) /\ Len(log[p]) >= Len(log[n])
                    <5>.  DEFINE nLen == Len(log[n])
                    <5>1. log[p][nLen] = log[n][nLen] \*BY <3>1, <3>2, <4>2, <4>3 DEF OSM!LastTerm, Ind, UniformLogEntriesInTerm, Quorums, TypeOK
                    <5>. QED
                    (*BY <3>1, <4>1, <4>2 DEF OSM!BecomeLeader, OSM!LastTerm, Ind, UniformLogEntriesInTerm,
                        CommittedTermMatchesEntry, LogMatching, EqualUpTo, InLog, TypeOK*)
                <4>4. CASE LastTerm(log[p]) > LastTerm(log[n])
                <4>. QED BY <3>1, <3>2, <4>2, <4>3, <4>4 DEF OSM!BecomeLeader, OSM!CanVoteForOplog, OSM!LastTerm, LastTerm, Quorums, TypeOK*)
            
                \*BY <3>1, <3>2, <3>3 DEF OSM!BecomeLeader, OSM!CanVoteForOplog, OSM!LastTerm, InLog, Quorums, TypeOK,
                \*    Ind, CommittedTermMatchesEntry, CommittedEntryIndexesAreNonZero
            <3>. QED BY <3>1, <3>4 DEF OSM!BecomeLeader, InLog, Ind, LeaderCompletenessGeneralized, TypeOK
            
            (*<3>2. \A s \in Server : currentTerm[p] >= configTerm[s]
                BY <3>1, QuorumsIdentical, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF OSM!QuorumsAt
            \*<3>3. \A s \in Server : (state[s] = Primary /\ s # p) => currentTerm[s] <= currentTerm[p]
            \*    BY <3>1, <3>2 DEF OSM!BecomeLeader, Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK
            <3>. QED*)
            \*BY <2>1, ElectedLeadersInActiveConfigSet DEF OSM!BecomeLeader, CSM!BecomeLeader, Quorums, CommittedEntryIndexesAreNonZero,
            \*    Ind, LeaderCompletenessGeneralized, ActiveConfigsOverlapWithCommittedEntry, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, Ind, LeaderCompletenessGeneralized, InLog, TypeOK
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
