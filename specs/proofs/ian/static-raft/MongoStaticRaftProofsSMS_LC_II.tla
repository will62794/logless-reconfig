------------------- MODULE MongoStaticRaftProofsSMS_LC_II ------------------

EXTENDS MongoStaticRaft, MongoStaticRaftProofsLemmaBasic, MongoStaticRaftProofsLemmaSecondariesFollowPrimary,
        SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS

SMS_LC_II ==
    /\ LemmaSecondariesFollowPrimary
    /\ CommittedTermMatchesEntry
    /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
    /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    /\ LeaderCompletenessGeneralized
    /\ LogsEqualToCommittedMustHaveCommittedIfItFits
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ CommittedEntriesMustHaveQuorums


(* Helpers *)

THEOREM QuorumsAreNonempty ==
ASSUME TypeOK, AllConfigsAreServer,
       NEW s \in Server,
       NEW Q \in QuorumsAt(s)
PROVE Q # {}
PROOF
    <1>1. Cardinality(Server) >= 1
        BY ServerIsFinite, ServerIsNonempty, FS_CardinalityType, FS_EmptySet
    <1>2. IsFiniteSet(Q)
        BY ServerIsFinite, FS_Subset DEF QuorumsAt, Quorums, TypeOK
    <1>3. Cardinality(Q) * 2 > Cardinality(Server)
        BY <1>1 DEF QuorumsAt, Quorums, TypeOK, AllConfigsAreServer
    <1>4. Cardinality(Q) > 0
        BY <1>1, <1>2, <1>3, ServerIsFinite, FS_CardinalityType
    <1>. QED BY <1>4, FS_EmptySet

\* This is specific to RollbackEntries, at least until I need it for another case
THEOREM QuorumsHaveAtLeastTwoElements ==
ASSUME TypeOK, \E s,t \in Server : RollbackEntries(s,t),
       NEW Q \in Quorums(Server)
PROVE \E q1, q2 \in Q : q1 # q2
PROOF
    <1>1. \E q1,q2 \in Server : q1 # q2
        BY DEF RollbackEntries, CanRollback, LastTerm, TypeOK
    <1>2. Cardinality(Server) >= 2
        BY <1>1, ServerIsFinite, ServerIsNonempty, FS_CardinalityType, FS_EmptySet, FS_Singleton
    <1>. IsFiniteSet(Q)
        BY ServerIsFinite, FS_Subset DEF Quorums
    <1>3. Cardinality(Q) >= 2
        BY <1>2, ServerIsFinite, FS_CardinalityType DEF Quorums
    <1>. QED BY <1>3, FS_AddElement, FS_EmptySet


(* *AndNext *)

THEOREM CommittedTermMatchesEntryAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedTermMatchesEntry'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedTermMatchesEntry'
        <2>. QED BY DEF SMS_LC_II, CommittedTermMatchesEntry, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLensAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. QED BY AppendProperties DEF SMS_LC_II, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens, ClientRequest, TypeOK
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. QED BY DEF SMS_LC_II, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens, GetEntries, TypeOK
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. SUFFICES ASSUME \E s, t \in Server : RollbackEntries(s, t)
             PROVE \A c \in committed' : \E s \in Server : c.entry[1] <= Len(log'[s])
             BY DEF CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
        <2>. TAKE c \in committed'
        <2>. c \in committed
            BY DEF RollbackEntries
        <2>. PICK Q \in Quorums(Server) :
                \A q \in Q :
                    \E i \in DOMAIN log[q] : i = c.entry[1]
            BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
        <2>1. \E a,b \in Q : a # b
            BY QuorumsHaveAtLeastTwoElements
        <2>2. \A q \in Q : c.entry[1] <= Len(log[q])
            BY DEF TypeOK
        <2>. CASE \E q \in Q : \E t \in Server : RollbackEntries(q, t)
            <3>. PICK q1 \in Q : \E t \in Server : RollbackEntries(q1, t)
                OBVIOUS
            <3>. PICK q2 \in Q : q2 # q1
                BY <2>1
            <3>1. c.entry[1] <= Len(log'[q2])
                BY DEF RollbackEntries, TypeOK
            <3>2. q2 \in Server
                BY DEF Quorums
            <3>. QED BY <3>1, <3>2
        <2>. CASE \E s,t \in Server : RollbackEntries(s, t) /\ s \notin Q
            <3>. PICK q \in Q : \E s,t \in Server : RollbackEntries(s, t) /\ s # q
                BY <2>1
            <3>1. c.entry[1] <= Len(log'[q])
                BY DEF RollbackEntries, TypeOK
            <3>2. q \in Server
                BY DEF Quorums
            <3>. QED BY <3>1, <3>2
        <2>. QED OBVIOUS
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. QED BY AppendProperties DEF SMS_LC_II, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens, BecomeLeader, TypeOK
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. QED BY DEF SMS_LC_II, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens, CommitEntry, TypeOK
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
        <2>. QED BY DEF SMS_LC_II, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. SUFFICES ASSUME NEW s \in Server, ClientRequest(s)
             PROVE CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
             OBVIOUS
        <2>. LastTerm(log[s]) <= LastTerm(log'[s])
            BY DEF ClientRequest, LastTerm, TypeOK, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY DEF ClientRequest, SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, LastTerm, TypeOK
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. SUFFICES ASSUME \E s, t \in Server : GetEntries(s, t)
             PROVE \A c \in committed' : \E s \in Server : c.term <= LastTerm(log'[s])
             BY DEF CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
        <2>. TAKE c \in committed'
        <2>. c \in committed
            BY DEF GetEntries
        <2>. PICK s \in Server : c.term <= LastTerm(log[s])
            BY DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
        <2>1. LastTerm(log'[s]) >= LastTerm(log[s])
            <3>. CASE \E t \in Server : GetEntries(s, t)
                <4>. QED BY LemmaBasicAndNext, TermsOfEntriesGrowMonotonicallyAndNext, TypeOKAndNext
                    DEF GetEntries, LastTerm, TypeOK, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
            <3>. CASE \E t,u \in Server : GetEntries(u, t) /\ u # s
                <4>. QED BY DEF GetEntries, LastTerm, TypeOK, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
            <3>. QED OBVIOUS
        <2>. QED BY <2>1 DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, GetEntries, LastTerm, TypeOK
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. SUFFICES ASSUME \E s, t \in Server : RollbackEntries(s, t)
             PROVE \A c \in committed' : \E s \in Server : c.term <= LastTerm(log'[s])
             BY DEF CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
        <2>. TAKE c \in committed'
        <2>. c \in committed
            BY DEF RollbackEntries
        <2>. PICK Q \in Quorums(Server) :
                \A q \in Q :
                    \E i \in DOMAIN log[q] : log[q][i] = c.term
            BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
        <2>a. \A s \in Q : \A i \in DOMAIN log[s] : log[s][i] <= LastTerm(log[s])
            BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, Quorums, TypeOK
        
        <2>1. \E a,b \in Q : a # b
            BY QuorumsHaveAtLeastTwoElements
        <2>2. \A q \in Q : c.term <= LastTerm(log[q])
            BY <2>a DEF LastTerm, TypeOK
        <2>. CASE \E q \in Q : \E t \in Server : RollbackEntries(q, t)
            <3>. PICK q1 \in Q : \E t \in Server : RollbackEntries(q1, t)
                OBVIOUS
            <3>. PICK q2 \in Q : q2 # q1
                BY <2>1
            <3>1. c.term <= LastTerm(log'[q2])
                BY <2>a DEF RollbackEntries, LastTerm, TypeOK
            <3>2. q2 \in Server
                BY DEF Quorums
            <3>. QED BY <3>1, <3>2
        <2>. CASE \E s,t \in Server : RollbackEntries(s, t) /\ s \notin Q
            <3>. PICK q \in Q : \E s,t \in Server : RollbackEntries(s, t) /\ s # q
                BY <2>1
            <3>1. c.term <= LastTerm(log'[q])
                BY <2>a DEF RollbackEntries, LastTerm, TypeOK
            <3>2. q \in Server
                BY DEF Quorums
            <3>. QED BY <3>1, <3>2
        <2>. QED OBVIOUS
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. SUFFICES ASSUME NEW p \in Server, \E Q \in QuorumsAt(p) : BecomeLeader(p, Q)
             PROVE CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
             OBVIOUS
        <2>. \A s \in Server : currentTerm[p] >= LastTerm(log[s])
            BY ElectedLeadersHaveLatestTerm
                DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm, LastTerm, TypeOK
        <2>. QED BY DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, BecomeLeader, LastTerm, TypeOK
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. QED BY DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, CommitEntry, LastTerm, TypeOK
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
        <2>. QED BY DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LeaderCompletenessGeneralizedAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LeaderCompletenessGeneralized'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LeaderCompletenessGeneralized'
        <2>. SUFFICES ASSUME NEW p \in Server, ClientRequest(p)
             PROVE \A s \in Server : (state'[s] = Primary) => \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF LeaderCompletenessGeneralized
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state'[s] = Primary
             PROVE \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             OBVIOUS
        <2>. CASE currentTerm[s] >= currentTerm[p]
            <3>. QED BY DEF SMS_LC_II, LeaderCompletenessGeneralized, ClientRequest, TypeOK, InLog
        <2>. CASE currentTerm[s] < currentTerm[p]
            <3>. QED BY DEF SMS_LC_II, LeaderCompletenessGeneralized, ClientRequest, TypeOK, InLog
        <2>. QED BY DEF TypeOK
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LeaderCompletenessGeneralized'
        <2>. QED BY DEF GetEntries, SMS_LC_II, LeaderCompletenessGeneralized, InLog, TypeOK
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LeaderCompletenessGeneralized'
        \*<2>. QED BY DEF RollbackEntries, CanRollback, SMS_LC_II, LeaderCompletenessGeneralized, InLog, TypeOK
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LeaderCompletenessGeneralized'
        <2>. SUFFICES ASSUME NEW p \in Server, \E Q \in QuorumsAt(p) : BecomeLeader(p, Q)
             PROVE \A s \in Server : (state'[s] = Primary) => \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF LeaderCompletenessGeneralized
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state'[s] = Primary
             PROVE \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             OBVIOUS
        <2>. CASE s = p
            <3>. TAKE c \in committed'
            <3>. c \in committed
                BY DEF BecomeLeader
            <3>1. InLog(c.entry, s)
                <4>. PICK Q \in Quorums(Server) : \A q \in Q : InLog(c.entry, q)
                    BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
                \* s is also the largest primary and has a quorum of servers
                <4>. QED
            
                (*<4>. PICK i \in DOMAIN log[s] : log[s][i] >= c.term
                    <5>. CASE state[s] = Primary
                    <5>. CASE state[s] = Secondary
                    <5>. QED BY DEF TypeOK
                <4>. CASE log[s][i] = c.term
                <4>. CASE log[s][i] > c.term
                <4>. QED BY DEF TypeOK*)
            <3>. CASE LastTerm(log'[s]) = currentTerm[s] + 1
                <4>. (DOMAIN log[s]) \in SUBSET Nat /\ (DOMAIN log'[s]) \in SUBSET Nat
                    BY TypeOKAndNext DEF TypeOK
                <4>. \A i \in 1..Len(log[s]) : log[s][i] = log'[s][i]
                    BY AppendProperties DEF BecomeLeader, TypeOK
                <4>. QED BY <3>1 DEF LastTerm, BecomeLeader, TypeOK, InLog
            <3>. CASE UNCHANGED log
                <4>. QED BY <3>1 DEF BecomeLeader, TypeOK, InLog
            <3>. QED BY DEF BecomeLeader, LastTerm, TypeOK
        <2>. CASE s # p /\ state'[s] = Primary
            <3>. currentTerm[s] <= currentTerm[p]
                BY ElectedLeadersHaveLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary
            <3>. currentTerm'[s] < currentTerm'[p]
                BY LemmaSecondariesFollowPrimaryAndNext, LemmaBasicAndNext, OnePrimaryPerTermAndNext
                    DEF BecomeLeader, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm, TypeOK
            <3>. QED BY DEF SMS_LC_II, LeaderCompletenessGeneralized, BecomeLeader, TypeOK, InLog
        <2>. QED BY DEF BecomeLeader, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm, TypeOK
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LeaderCompletenessGeneralized'
        <2>. SUFFICES ASSUME NEW p \in Server, NEW Q \in QuorumsAt(p), CommitEntry(p, Q)
             PROVE \A s \in Server :
                        (state'[s] = Primary) => \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF LeaderCompletenessGeneralized
        <2>1. \A s \in Server : currentTerm[p] >= currentTerm[s]
            <3>1. state[p] = Primary
                BY DEF CommitEntry
            <3>. PICK lp \in Server :
                    /\ state[lp] = Primary
                    /\ \A u \in Server : currentTerm[lp] >= currentTerm[u]
                    /\ \E lQ \in QuorumsAt(lp) :
                          \A q \in lQ : currentTerm[q] = currentTerm[lp]
                BY <3>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary
            <3>. PICK lQ \in QuorumsAt(lp) : \A q \in lQ : currentTerm[q] = currentTerm[lp]
                OBVIOUS
            <3>2. \A q \in Q : currentTerm[q] = currentTerm[p]
                BY DEF CommitEntry, ImmediatelyCommitted
            <3>3. \E q \in lQ : q \in Q
                BY AllQuorumsOverlap DEF SMS_LC_II, LemmaSecondariesFollowPrimary
            <3>4. \A q \in lQ : currentTerm[q] = currentTerm[p]
                BY <3>2, <3>3
            <3>5. currentTerm[lp] = currentTerm[p]
                BY <3>4, QuorumsAreNonempty DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic
            <3>. QED BY <3>5 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state[s] = Primary
             PROVE \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF CommitEntry
        <2>. CASE s = p
            <3>. QED BY <2>1 DEF CommitEntry, TypeOK, InLog, SMS_LC_II, LeaderCompletenessGeneralized
        <2>. CASE s # p
            <3>. QED BY <2>1 DEF CommitEntry, TypeOK, InLog, SMS_LC_II, LeaderCompletenessGeneralized, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm
        <2>. QED OBVIOUS
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LeaderCompletenessGeneralized'
        <2>. QED BY PrimaryAndSecondaryAreDifferent DEF UpdateTerms, UpdateTermsExpr, SMS_LC_II, LeaderCompletenessGeneralized, InLog, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LogsEqualToCommittedMustHaveCommittedIfItFitsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LogsEqualToCommittedMustHaveCommittedIfItFits'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. QED BY DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LogsLaterThanCommittedMustHaveCommittedAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LogsLaterThanCommittedMustHaveCommitted'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LogsLaterThanCommittedMustHaveCommitted'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LogsLaterThanCommittedMustHaveCommitted'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LogsLaterThanCommittedMustHaveCommitted'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. QED BY DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntriesMustHaveQuorumsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntriesMustHaveQuorums'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntriesMustHaveQuorums'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntriesMustHaveQuorums'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntriesMustHaveQuorums'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntriesMustHaveQuorums'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntriesMustHaveQuorums'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntriesMustHaveQuorums'
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

-----------------------------------------------------------------------------------

(* Init => SMS_LC_II *)

THEOREM InitImpliesSMS_LC_II ==
ASSUME TRUE
PROVE Init => SMS_LC_II
BY InitImpliesLemmaSecondariesFollowPrimary
DEF Init, SMS_LC_II, 
    CommittedTermMatchesEntry, CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens,
    CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms, LeaderCompletenessGeneralized, 
    LogsEqualToCommittedMustHaveCommittedIfItFits, LogsLaterThanCommittedMustHaveCommitted,
    CommittedEntriesMustHaveQuorums

-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM SMS_LC_IIAndNext ==
ASSUME TypeOK, SMS_LC_II, Next
PROVE TypeOK' /\ SMS_LC_II'
PROOF BY InitImpliesSMS_LC_II, TypeOKAndNext,
         LemmaSecondariesFollowPrimaryAndNext,
         CommittedTermMatchesEntryAndNext,
         CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLensAndNext,
         CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext,
         LeaderCompletenessGeneralizedAndNext,
         LogsEqualToCommittedMustHaveCommittedIfItFitsAndNext,
         LogsLaterThanCommittedMustHaveCommittedAndNext,
         CommittedEntriesMustHaveQuorumsAndNext
      DEF SMS_LC_II

THEOREM SMS_LC_II_IsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => (TypeOK /\ SMS_LC_II)
      /\ (TypeOK /\ SMS_LC_II /\ Next) => (TypeOK /\ SMS_LC_II)'
PROOF BY InitImpliesTypeOK, InitImpliesSMS_LC_II, TypeOKAndNext, SMS_LC_IIAndNext

=============================================================================

