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
