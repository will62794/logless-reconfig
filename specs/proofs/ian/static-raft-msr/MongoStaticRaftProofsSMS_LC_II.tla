------------------- MODULE MongoStaticRaftProofsSMS_LC_II ------------------

EXTENDS MongoStaticRaft, MongoStaticRaftProofsLemmaBasic, MongoStaticRaftProofsLemmaSecondariesFollowPrimary,
        SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS

SMS_LC_II ==
    /\ LemmaSecondariesFollowPrimary
    /\ PrimariesTermGreaterThanZero
    /\ CommitIndexGreaterThanZero
    /\ CommitTermGreaterThanZero
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

THEOREM GetEntriesFromLaterTerm ==
ASSUME TypeOK, LemmaBasic,
       NEW s \in Server, NEW t \in Server,
       GetEntries(s, t)
PROVE LastTerm(log[s]) <= LastTerm(log[t])
PROOF
    <1>. CASE Empty(log[s])
        <2>. QED BY DEF LastTerm, Empty, TypeOK
    <1>. CASE ~Empty(log[s])
        <2>. Len(log[s]) > 0
            BY DEF Empty
        <2>. DEFINE k == Len(log[s])
        <2>. k \in DOMAIN log[t]
            BY DEF GetEntries
        <2>. LastTerm(log[s]) = log[t][k]
            BY DEF GetEntries, LastTerm, TypeOK
        <2>. QED BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
    <1>. QED OBVIOUS

THEOREM CommittingImpliesLatestTerm ==
ASSUME TypeOK, LemmaBasic,
       NEW cp \in Server,
       NEW cQ \in QuorumsAt(cp)
PROVE CommitEntry(cp, cQ) => \A s \in Server : currentTerm[cp] >= currentTerm[s]
PROOF
    <1>. SUFFICES ASSUME CommitEntry(cp, cQ)
         PROVE \A t \in Server : currentTerm[cp] >= currentTerm[t]
         OBVIOUS
    <1>. PICK lp \in Server :
                /\ \A u \in Server : currentTerm[lp] >= currentTerm[u]
                /\ \E lQ \in QuorumsAt(lp) :
                        \A q \in lQ : currentTerm[q] = currentTerm[lp]
        BY DEF LemmaBasic, ExistsQuorumInLargestTerm
    <1>. PICK lQ \in QuorumsAt(lp) : \A q \in lQ : currentTerm[q] = currentTerm[lp]
        BY DEF LemmaBasic, ExistsQuorumInLargestTerm
    <1> PICK q \in Server : q \in cQ /\ q \in lQ
        BY AllQuorumsOverlap DEF QuorumsAt, Quorums, LemmaBasic, AllConfigsAreServer
    <1>1. currentTerm[q] = currentTerm[cp]
        BY DEF CommitEntry, ImmediatelyCommitted
    <1>2. currentTerm[q] = currentTerm[lp]
        OBVIOUS
    <1>. QED BY <1>1, <1>2

THEOREM CommitsMustBeSmallerThanOrEqualToLargestTerm ==
ASSUME TypeOK, SMS_LC_II
PROVE \A c \in committed : \E s \in Server : c.term <= currentTerm[s]
PROOF
    <1>. TAKE c \in committed
    <1>. PICK s \in Server : c.term <= LastTerm(log[s])
        BY DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    <1>. PICK t \in Server : LastTerm(log[s]) <= currentTerm[t]
        BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>. QED BY DEF LastTerm, TypeOK


(* *AndNext *)

THEOREM PrimariesTermGreaterThanZeroAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE PrimariesTermGreaterThanZero'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, BecomeLeader, TypeOK
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => PrimariesTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, PrimariesTermGreaterThanZero, UpdateTerms, UpdateTermsExpr, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommitIndexGreaterThanZeroAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommitIndexGreaterThanZero'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommitIndexGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommitTermGreaterThanZeroAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommitTermGreaterThanZero'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, PrimariesTermGreaterThanZero, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommitTermGreaterThanZero'
        <2>. QED BY DEF SMS_LC_II, CommitTermGreaterThanZero, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

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
                <4>. CASE Empty(log[s])
                    BY DEF Empty, GetEntries, LastTerm, TypeOK
                <4>. CASE ~Empty(log[s])
                    <5>tgm. TermsOfEntriesGrowMonotonically' /\ TypeOK'
                        BY LemmaBasicAndNext, TermsOfEntriesGrowMonotonicallyAndNext, TypeOKAndNext DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                    <5>. QED BY <5>tgm DEF TermsOfEntriesGrowMonotonically, GetEntries, LastTerm, TypeOK, Empty
                <4>. QED OBVIOUS
            <3>. CASE \E t,u \in Server : GetEntries(u, t) /\ u # s
                BY DEF GetEntries, LastTerm, TypeOK, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
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
        <2>. SUFFICES ASSUME \E s, t \in Server : RollbackEntries(s, t)
             PROVE \A s \in Server : (state'[s] = Primary) => \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF LeaderCompletenessGeneralized
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state[s] = Primary
             PROVE \A c \in committed' : (c.term <= currentTerm'[s]) => InLog(c.entry, s)'
             BY DEF RollbackEntries
        <2>. TAKE c \in committed'
        <2>. c \in committed
            BY DEF RollbackEntries
        <2>. SUFFICES ASSUME c.term <= currentTerm[s]
             PROVE InLog(c.entry, s)'
             BY DEF RollbackEntries
        <2>1. InLog(c.entry, s)
            BY DEF SMS_LC_II, LeaderCompletenessGeneralized
        
        \* to recap: s \in Server, c \in committed, c.term <= currentTerm[s]
        <2>. CASE \E t,u \in Server : RollbackEntries(u, t) /\ u # s
            <3>. QED BY DEF SMS_LC_II, LeaderCompletenessGeneralized, InLog, RollbackEntries, TypeOK
        <2>. CASE \E t \in Server : RollbackEntries(s, t)
            <3>. PICK t \in Server : RollbackEntries(s, t)
                OBVIOUS
            <3>1. LastTerm(log[s]) < LastTerm(log[t])
                BY DEF RollbackEntries, CanRollback
            <3>. CASE Len(log[s]) > Len(log[t])
                \* if c is in t's log then clearly we're not rolling back c
                <4>1. InLog(c.entry, t)
                    <5>. PICK i \in DOMAIN log[s] : i = c.entry[1] /\ log[s][i] = c.entry[2]
                        BY <2>1 DEF InLog
                    <5>1. log[s][i] < LastTerm(log[t])
                        \* ridiculous that I need to spell this out
                        <6>. log[s][i] <= LastTerm(log[s])
                            BY DEF LastTerm, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                        <6>. QED BY <3>1 DEF LastTerm, TypeOK
                    <5>2. c.term < LastTerm(log[t])
                        BY <5>1 DEF InLog, SMS_LC_II, CommittedTermMatchesEntry
                    <5>3. \E j \in DOMAIN log[t] : log[t][j] > c.term
                        BY <5>2 DEF LastTerm, TypeOK
                    <5>4. Len(log[t]) >= c.entry[1] /\ log[t][c.entry[1]] = c.term
                        BY <5>2, <5>3 DEF LastTerm, SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, TypeOK
                    <5>. QED BY <5>4 DEF InLog, SMS_LC_II, CommittedTermMatchesEntry
                <4>2. c.entry[1] <= Len(log[t])
                    BY <4>1 DEF InLog, TypeOK
                <4>3. Len(log[t]) <= Len(log'[s])
                    BY DEF RollbackEntries, CanRollback, TypeOK
                <4>4. c.entry[1] <= Len(log'[s])
                    BY <4>2, <4>3 DEF TypeOK
                <4>. QED BY <2>1, <4>4 DEF InLog, RollbackEntries
            <3>. CASE Len(log[s]) <= Len(log[t]) /\ LastTerm(log[s]) # LogTerm(t, Len(log[s]))
                \* if c is in t's log then we can't be rolling back c because: LastTerm(log[s]) # LogTerm(t, Len(log[s]))
                <4>1. InLog(c.entry, t)
                    <5>1. c.term <= LastTerm(log[t])
                        <6>. c.term <= LastTerm(log[s])
                            BY <2>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, InLog, CommittedTermMatchesEntry, LastTerm
                        <6>. QED BY <3>1 DEF LastTerm, TypeOK
                    <5>2. Len(log[t]) >= c.entry[1]
                        BY <2>1 DEF InLog
                    <5>. CASE c.term < LastTerm(log[t])
                        <6>. Len(log[t]) >= c.entry[1] /\ log[t][c.entry[1]] = c.term
                            BY DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, LastTerm, TypeOK
                        <6>. QED BY DEF SMS_LC_II, CommitIndexGreaterThanZero, CommittedTermMatchesEntry, InLog, TypeOK
                    <5>. CASE c.term = LastTerm(log[t])
                        <6>1. \E i \in DOMAIN log[t] : log[t][i] = c.term
                            BY <5>2 DEF SMS_LC_II, CommitIndexGreaterThanZero, LastTerm, TypeOK
                        <6>. log[t][c.entry[1]] = c.term
                            BY <5>2, <6>1 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, LastTerm, TypeOK
                        <6>. QED BY <5>2 DEF SMS_LC_II, CommitIndexGreaterThanZero, CommittedTermMatchesEntry, InLog, TypeOK
                    <5>. QED BY <5>1 DEF LastTerm, TypeOK
                <4>2. c.entry[1] # Len(log[s])
                    <5>. SUFFICES ASSUME c.entry[1] = Len(log[s])
                         PROVE FALSE
                         OBVIOUS
                    <5>1. LastTerm(log[s]) = LogTerm(s, c.entry[1])
                        BY DEF LastTerm, LogTerm, GetTerm
                    <5>2. LogTerm(t, Len(log[s])) = LogTerm(t, c.entry[1])
                        OBVIOUS
                    <5>3. LastTerm(log[s]) = LogTerm(t, Len(log[s]))
                        BY <5>1, <5>2, <2>1, <4>1 DEF InLog, LastTerm, LogTerm, GetTerm, TypeOK
                    <5>. QED BY <5>3
                <4>. QED BY <2>1, <4>2 DEF RollbackEntries, InLog, TypeOK
            <3>. QED BY DEF RollbackEntries, CanRollback
        <2>. QED OBVIOUS
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
                <4>. PICK cQ \in Quorums(Server) : \A q \in cQ : InLog(c.entry, q)
                    BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums, CommittedTermMatchesEntry, InLog
                <4>. PICK lQ \in QuorumsAt(s) : \A q \in lQ : CanVoteForOplog(q, s, currentTerm[s]+1)
                    BY DEF BecomeLeader
                <4>. PICK q \in cQ : q \in lQ
                    <5>. \E t \in Server : cQ \in QuorumsAt(t)
                        BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, AllConfigsAreServer, QuorumsAt
                    <5>. QED BY AllQuorumsOverlap DEF SMS_LC_II, LemmaSecondariesFollowPrimary
                <4>. PICK i \in DOMAIN log[q] : log[q][i] = c.term
                    BY DEF InLog, SMS_LC_II, CommittedTermMatchesEntry
                <4>. q \in Server
                    BY QuorumsAreServerSubsets
                <4>1. (LastTerm(log[s]) > c.term) => InLog(c.entry, s)
                    <5>. SUFFICES ASSUME LastTerm(log[s]) > c.term
                         PROVE InLog(c.entry, s)
                         OBVIOUS
                    <5>1. Len(log[s]) >= c.entry[1] /\ log[s][c.entry[1]] = c.term
                        BY DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, LastTerm, TypeOK
                    <5>2. c.entry[1] \in DOMAIN log[s]
                        BY <5>1, LenProperties DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
                    <5>. QED BY <5>1, <5>2 DEF InLog, SMS_LC_II, CommittedTermMatchesEntry
                <4>. CASE LastTerm(log[s]) > LastTerm(log[q])
                    <5>. LastTerm(log[s]) > c.term
                        BY DEF CanVoteForOplog, LastTerm, TypeOK,
                            SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>. QED BY <4>1
                <4>. CASE LastTerm(log[s]) = LastTerm(log[q]) /\ Len(log[s]) >= Len(log[q])
                    <5>1. LastTerm(log[s]) >= c.term
                        BY DEF CanVoteForOplog, LastTerm, TypeOK,
                            SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>. CASE LastTerm(log[s]) > c.term
                        BY <4>1
                    <5>. CASE LastTerm(log[s]) = c.term
                        <6>1. Len(log[s]) >= c.entry[1]
                            BY DEF InLog, TypeOK
                        <6>2. log[s][c.entry[1]] = c.term
                            BY <6>1 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, LastTerm, TypeOK
                        <6>3. c.entry[1] \in DOMAIN log[s]
                            BY <6>1, LenProperties DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
                        <6>. QED BY <6>2, <6>3 DEF InLog, SMS_LC_II, CommittedTermMatchesEntry
                    <5>. QED BY <5>1 DEF LastTerm, TypeOK
                <4>. QED BY DEF BecomeLeader, CanVoteForOplog
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
    
(* Another Helper *)
\* it may seem a bit weird (read: incorrect) to use an "AndNext" version of one of the properties of SMS_LC_II in the proof, however
\* we only use results here that have already been proved ABOVE so we do not run into a circular logic issue.  (also note that we only
\* make use of this theorem BELOW)
\* in particular, we make use of CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext here to prove a result that relies on this later
THEOREM CommitsMustBeSmallerThanOrEqualToLargestTermAndNext ==
ASSUME TypeOK, SMS_LC_II, Next
PROVE \A c \in committed' : \E s \in Server : c.term <= currentTerm'[s]
PROOF
    <1>. TAKE c \in committed'
    <1>. PICK s \in Server : c.term <= LastTerm(log'[s])
        BY CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    <1>. PICK t \in Server : LastTerm(log'[s]) <= currentTerm'[t]
        BY LemmaSecondariesFollowPrimaryAndNext, LemmaBasicAndNext, LogsMustBeSmallerThanOrEqualToLargestTermAndNext
            DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>. QED BY TypeOKAndNext DEF LastTerm, TypeOK
(******************)

THEOREM LogsEqualToCommittedMustHaveCommittedIfItFitsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LogsEqualToCommittedMustHaveCommittedIfItFits'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. SUFFICES ASSUME \E s \in Server : ClientRequest(s)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] = c.term) =>
                            \A d \in committed' :
                                (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             BY DEF LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] = c.term
             PROVE \A d \in committed' : (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>1. d \in committed
            BY DEF ClientRequest
        <2>. SUFFICES ASSUME d.term <= c.term /\ Len(log'[s]) >= d.entry[1]
             PROVE log'[s][d.entry[1]] = d.term
             OBVIOUS
             
        <2>. CASE \E t \in Server : ClientRequest(t) /\ t # s
            <3>. log'[s] = log[s] /\ UNCHANGED committed
                BY DEF ClientRequest, TypeOK
            <3>. QED BY DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. CASE ClientRequest(s)
            <3>1. state[s] = Primary /\ state'[s] = Primary
                BY DEF ClientRequest, TypeOK
            <3>2. d.term <= currentTerm[s]
                BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, ClientRequest, TypeOK
            <3>3. InLog(d.entry, s)
                BY <2>1, <3>1, <3>2 DEF SMS_LC_II, LeaderCompletenessGeneralized
            <3>. QED BY <3>3 DEF ClientRequest, TypeOK, InLog, SMS_LC_II, CommittedTermMatchesEntry
        <2>. QED OBVIOUS
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. SUFFICES ASSUME \E s, t \in Server : GetEntries(s, t)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] = c.term) =>
                            \A d \in committed' :
                                (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             BY DEF LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] = c.term
             PROVE \A d \in committed' : (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>1. d \in committed
            BY DEF GetEntries
        <2>. SUFFICES ASSUME d.term <= c.term /\ Len(log'[s]) >= d.entry[1]
             PROVE log'[s][d.entry[1]] = d.term
             OBVIOUS
        
        <2>. CASE \E t,u \in Server : GetEntries(u, t) /\ u # s
            <3>. log'[s] = log[s] /\ UNCHANGED committed
                BY DEF GetEntries, TypeOK
            <3>. QED BY DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. CASE \E t \in Server : GetEntries(s, t)
            \* the only way adding a new entry (via GetEntries) could violate LogsEqualToCommittedMustHaveCommittedIfItFits is if s receives an entry
            \* that has many commits between before it that aren't in s's log.  However "log[j][Len(log[i])] = log[i][Len(log[i])]" makes sure s receives
            \* a log that isn't committed much later.
            <3>. PICK t \in Server : GetEntries(s, t)
                OBVIOUS
            <3>1. d.entry[1] <= Len(log[t])
                BY DEF GetEntries, TypeOK
            <3>2. d.term <= LastTerm(log[t])
                <4>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                    OBVIOUS
                <4>. c.term <= LastTerm(log[t])
                    <5>. CASE i = Len(log'[s])
                        <6>1. Len(log[s])+1 = Len(log'[s])
                            BY DEF GetEntries, TypeOK
                        <6>2. i = IF Empty(log[s]) THEN 1 ELSE Len(log[s]) + 1
                            BY <6>1 DEF TypeOK, Empty
                        <6>3. log' = [log EXCEPT ![s] = Append(log[s], log[t][i])]
                            BY <6>2 DEF GetEntries, TypeOK
                        <6>4. log'[s][i] = log[t][i]
                            BY <6>3 DEF GetEntries, TypeOK
                        <6>5. log[t][i] <= LastTerm(log[t])
                            <7>. i \in DOMAIN log[t]
                                BY <6>2 DEF GetEntries, TypeOK
                            <7>. QED BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
                        <6>. QED BY <6>4, <6>5
                    <5>. CASE i < Len(log'[s])
                        <6>1. log'[s][i] = log[s][i]
                            BY DEF GetEntries, TypeOK
                        <6>2. c.term <= LastTerm(log[s])
                            BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK, GetEntries
                        <6>3. LastTerm(log[s]) <= LastTerm(log[t])
                            BY GetEntriesFromLaterTerm DEF LastTerm, TypeOK, SMS_LC_II, LemmaSecondariesFollowPrimary
                        <6>. QED BY <6>2, <6>3 DEF GetEntries, LastTerm, TypeOK
                    <5>. QED OBVIOUS
                <4>. QED BY TypeOKAndNext DEF LastTerm, TypeOK
            
            <3>. CASE Empty(log[s])
                <4>1. log[t][d.entry[1]] = d.term
                    <5>1. \E i \in DOMAIN log[t] : log[t][i] = c.term
                        BY DEF GetEntries, Empty
                    <5>2. d.term <= c.term
                        OBVIOUS
                    <5>3. c \in committed /\ d \in committed
                        BY DEF GetEntries
                    <5>. QED BY <5>1, <5>2, <5>3, <3>1 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                <4>. QED BY <4>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, Empty, TypeOK
            <3>. CASE ~Empty(log[s])
                <4>. CASE d.term <= LastTerm(log[s])
                    <5>1. Len(log[s])+1 >= d.entry[1]
                        BY DEF GetEntries, TypeOK
                    <5>. CASE Len(log[s])+1 > d.entry[1]
                        <6>1. Len(log'[s]) > d.entry[1]
                            BY DEF GetEntries, TypeOK
                        <6>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                            OBVIOUS
                        <6>. CASE i < Len(log'[s])
                            <7>1. log[s][d.entry[1]] = d.term
                                <8>1. i \in DOMAIN log[s]
                                    BY DEF GetEntries, TypeOK
                                <8>2. Len(log[s]) >= d.entry[1]
                                    BY DEF GetEntries, TypeOK
                                <8>3. log[s][i] = c.term
                                    BY <8>1 DEF GetEntries
                                <8>4. d.term <= c.term
                                    OBVIOUS
                                <8>5. Len(log[s]) >= d.entry[1]
                                    BY <8>2
                                <8>6. c \in committed /\ d \in committed
                                    BY DEF GetEntries
                                <8> QED BY <8>1, <8>3, <8>4, <8>5, <8>6 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, TypeOK
                            <7>. QED BY <2>1, <7>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, TypeOK
                        <6>. CASE i = Len(log'[s])
                            <7>1. log[t][i] = c.term
                                BY DEF GetEntries
                            <7>2. log[t][d.entry[1]] = d.term
                                BY <2>1, <3>1, <7>1 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, GetEntries, Empty, TypeOK
                            <7>. CASE Len(log'[s]) = d.entry[1]
                                <8>. QED BY <7>2 DEF GetEntries
                            <7>. CASE Len(log'[s]) > d.entry[1]
                                <8>. DEFINE k == Len(log[s])
                                <8>1. k >= d.entry[1]
                                    BY DEF GetEntries, TypeOK
                                <8>2. k \in DOMAIN log[s]
                                    BY DEF Empty
                                <8>3. d.term <= d.term
                                    BY <2>1 DEF TypeOK
                                <8>. CASE log[s][k] = d.term
                                    <9>1. log[s][d.entry[1]] = d.term
                                        BY <2>1, <8>1, <8>2, <8>3 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                                    <9>. QED BY <2>1, <9>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, TypeOK
                                <8>. CASE log[s][k] > d.term
                                    <9>1. log[s][d.entry[1]] = d.term
                                        BY <2>1, <8>1, <8>2, <8>3 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                                    <9>. QED BY <2>1, <9>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, TypeOK
                                <8>. QED BY <2>1 DEF SMS_LC_II, CommitTermGreaterThanZero, LastTerm, TypeOK, Empty
                            <7>. QED BY TypeOKAndNext DEF TypeOK
                        <6>. QED BY TypeOKAndNext DEF TypeOK
                    <5>. CASE Len(log[s])+1 = d.entry[1]
                        \* t transfers d to s
                        <6>. CASE d.term = LastTerm(log[t])
                            <7>1. \E i \in DOMAIN log[t] : log[t][i] = d.term
                                BY <2>1 DEF SMS_LC_II, CommitTermGreaterThanZero, LastTerm, TypeOK
                            <7>2. d.term <= d.term
                                BY <2>1 DEF TypeOK
                            <7>3. Len(log[t]) >= d.entry[1]
                                BY <3>1
                            <7>4. log[t][d.entry[1]] = d.term
                                BY <2>1, <7>1, <7>2, <7>3 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                            <7>. QED BY <7>4 DEF GetEntries
                        <6>. CASE d.term < LastTerm(log[t])
                            <7>1. \E i \in DOMAIN log[t] : log[t][i] > d.term
                                BY <2>1 DEF LastTerm, TypeOK
                            <7>2. d.term <= d.term
                                BY <2>1 DEF TypeOK
                            <7>3. log[t][d.entry[1]] = d.term
                                BY <2>1, <7>1, <7>2 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                            <7>. QED BY <7>3 DEF GetEntries
                        <6>. QED BY <2>1, <3>2 DEF LastTerm, TypeOK
                    <5>. CASE Len(log[s])+1 < d.entry[1]
                        \* proof by contradiction
                        <6>. QED BY <2>1, <5>1 DEF TypeOK
                    <5>. QED BY <2>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
                <4>. CASE d.term > LastTerm(log[s])
                    <5>1. \A i \in DOMAIN log[s] : log[s][i] # d.term
                        BY DEF LastTerm, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                    <5>2. \A i \in DOMAIN log[s] : log[s][i] # c.term
                        <6>1. c.term >= d.term /\ d.term > LastTerm(log[s])
                            OBVIOUS
                        <6>2. c.term > LastTerm(log[s])
                            BY <6>1 DEF LastTerm, TypeOK, GetEntries
                        <6>. QED BY <5>1, <6>2 DEF LastTerm, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                    <5>. DEFINE k == Len(log'[s])
                    <5>3. log'[s][k] = c.term
                        <6>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                            OBVIOUS
                        <6>1. i = Len(log'[s])
                            BY <5>2 DEF GetEntries
                        <6>. QED BY <6>1
                    <5>4. log[t][k] = c.term
                        BY <5>3 DEF GetEntries
                    <5>5. log[t][d.entry[1]] = d.term
                        <6>1. \E i \in DOMAIN log[t] : log[t][i] = c.term
                            BY <5>4 DEF GetEntries
                        <6>2. d.term <= c.term
                            OBVIOUS
                        <6>3. Len(log[t]) >= d.entry[1]
                            BY <3>1
                        <6>4. c \in committed /\ d \in committed
                            BY DEF GetEntries
                        <6>. QED BY <6>1, <6>2, <6>3, <6>4 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                        
                    \* the cases
                    <5>. CASE d.entry[1] > k
                        \* this is not possible because Len(log'[s]) >= d.entry[1]
                        <6>. QED BY TypeOKAndNext DEF TypeOK
                    <5>. CASE d.entry[1] = k
                        \* because of <5>5, it is clear that log'[s] has this from GetEntries
                        <6>. QED BY <5>5 DEF GetEntries, TypeOK
                    <5>. CASE d.entry[1] < k
                        \* this is not possible because: d.term > LastTerm(log[s]) = log[t][k-1] >= log[t][d.entry[1]] = d.term
                        <6>. LastTerm(log[s]) = log[t][k-1]
                            BY DEF LastTerm, GetEntries, Empty, TypeOK
                        <6>. log[t][k-1] >= log[t][d.entry[1]]
                            <7>. k-1 >= d.entry[1]
                                BY DEF GetEntries, TypeOK
                            <7>. k-1 \in DOMAIN log[t]
                                BY DEF Empty, GetEntries, TypeOK
                            <7>. d.entry[1] \in DOMAIN log[t]
                                BY <3>1 DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, TypeOK
                            <7>. QED BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                        <6>. QED BY <5>5 DEF TypeOK
                    <5>. QED BY TypeOKAndNext DEF TypeOK
                <4>. QED BY <2>1 DEF LastTerm, TypeOK
            <3>. QED OBVIOUS
        <2>. QED OBVIOUS
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. SUFFICES ASSUME \E s, t \in Server : RollbackEntries(s, t)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] = c.term) =>
                            \A d \in committed' :
                                (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             BY DEF LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] = c.term
             PROVE \A d \in committed' : (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>1. d \in committed
            BY DEF RollbackEntries
        <2>. SUFFICES ASSUME d.term <= c.term /\ Len(log'[s]) >= d.entry[1]
             PROVE log'[s][d.entry[1]] = d.term
             OBVIOUS
             
        <2>. CASE \E t,u \in Server : RollbackEntries(u, t) /\ u # s
            <3>. QED BY DEF RollbackEntries, SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. CASE \E t \in Server : RollbackEntries(s, t)
            <3>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                OBVIOUS
            <3>1. log[s][i] = c.term /\ i \in DOMAIN log[s]
                BY DEF RollbackEntries, TypeOK
            <3>2. d.term <= c.term
                OBVIOUS
            <3>3. Len(log[s]) >= d.entry[1]
                BY DEF RollbackEntries, TypeOK
            <3>4. c \in committed /\ d \in committed
                BY DEF RollbackEntries
            <3>5. log[s][d.entry[1]] = d.term
                BY <3>1, <3>2, <3>3, <3>4 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
            <3>. QED BY <3>5 DEF RollbackEntries, SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
        <2>. QED OBVIOUS
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. SUFFICES ASSUME \E p \in Server : \E Q \in QuorumsAt(p) : BecomeLeader(p, Q)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] = c.term) =>
                            \A d \in committed' :
                                (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             BY DEF LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] = c.term
             PROVE \A d \in committed' : (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>1. d \in committed
            BY DEF BecomeLeader
        <2>. SUFFICES ASSUME d.term <= c.term /\ Len(log'[s]) >= d.entry[1]
             PROVE log'[s][d.entry[1]] = d.term
             OBVIOUS
             
        <2>. CASE \E p \in Server : \E Q \in QuorumsAt(p) : BecomeLeader(p, Q) /\ p # s
            <3>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                OBVIOUS
            <3>1. log[s][i] = c.term /\ i \in DOMAIN log[s]
                BY DEF BecomeLeader, TypeOK
            <3>. QED BY <3>1 DEF BecomeLeader, SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, TypeOK
        <2>. CASE \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
            <3>. CASE UNCHANGED log
                <4>. QED BY DEF BecomeLeader, SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, TypeOK
            <3>. CASE log'[s] = Append(log[s], currentTerm[s]+1)
                <4>. DEFINE newTerm == currentTerm[s] + 1
                <4>1. c.term < newTerm
                    <5>1. c \in committed
                        BY DEF BecomeLeader
                    <5>. PICK t \in Server : c.term <= LastTerm(log[t])
                        BY <5>1 DEF SMS_LC_II, CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
                    <5>. PICK u \in Server : LastTerm(log[t]) <= currentTerm[u]
                        BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                    <5>2. currentTerm[u] < newTerm
                        BY ElectedLeadersHaveLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary, TypeOK
                    <5>. QED BY <5>2 DEF LastTerm, TypeOK
                <4>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                    OBVIOUS
                <4>2. i < Len(log'[s])
                    <5>1. TermsOfEntriesGrowMonotonically'
                        BY LemmaSecondariesFollowPrimaryAndNext, LemmaBasicAndNext, TermsOfEntriesGrowMonotonicallyAndNext
                            DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>. QED BY <4>1, <5>1 DEF TermsOfEntriesGrowMonotonically, TypeOK
                <4>3. i \in DOMAIN log[s] /\ log[s][i] = c.term
                    BY <4>2 DEF BecomeLeader, TypeOK
                <4>4. Len(log[s]) >= d.entry[1]
                    <5>. SUFFICES ASSUME d.entry[1] > Len(log[s])
                         PROVE FALSE
                         BY <2>1 DEF TypeOK
                    <5>a. d.entry[1] = Len(log'[s])
                        BY <2>1 DEF BecomeLeader, TypeOK
                    <5>. PICK cQ \in Quorums(Server) : \A q \in cQ :
                                \E j \in DOMAIN log[q] : log[q][j] = d.term /\ j = d.entry[1]
                        BY <2>1 DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
                    <5>. PICK lQ \in QuorumsAt(s) : BecomeLeader(s, lQ)
                        OBVIOUS
                    <5>. PICK t \in Server : t \in cQ /\ t \in lQ
                        BY AllQuorumsOverlap DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, AllConfigsAreServer, QuorumsAt, Quorums
                    <5>. PICK j \in DOMAIN log[t] : log[t][j] = d.term /\ j = d.entry[1]
                        OBVIOUS
                    <5>. CASE LastTerm(log[s]) > LastTerm(log[t])
                        <6>1a. d.term < LastTerm(log[s])
                            BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
                        <6>1. \E k \in DOMAIN log[s] : log[s][k] > d.term
                            BY <6>1a DEF LastTerm, TypeOK
                        <6>2. d.term <= d.term
                            BY DEF TypeOK
                        <6>3. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term
                            BY <2>1, <6>1, <6>2 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                        <6>. QED BY <6>3 DEF TypeOK
                    <5>. CASE LastTerm(log[s]) = LastTerm(log[t]) /\ Len(log[s]) >= Len(log[t])
                        \* proof by contradiction...in a proof by contraction.  how meta
                        <6>. Len(log[t]) > Len(log[s])
                            BY DEF TypeOK
                        <6>. QED OBVIOUS
                    <5>. QED BY DEF BecomeLeader, CanVoteForOplog
                <4>5. log[s][d.entry[1]] = d.term
                    BY <4>3, <4>4 DEF BecomeLeader, SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, TypeOK
                <4>6. d.entry[1] \in DOMAIN log[s]
                    BY <2>1, <4>4 DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
                <4>. QED BY <4>5, <4>6 DEF BecomeLeader, TypeOK
            <3>. QED BY DEF BecomeLeader, TypeOK
        <2>. QED OBVIOUS
    <1>5. (\E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. SUFFICES ASSUME \E p \in Server : \E Q \in QuorumsAt(p) : CommitEntry(p, Q)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] = c.term) =>
                            \A d \in committed' :
                                (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             BY DEF LogsEqualToCommittedMustHaveCommittedIfItFits
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] = c.term
             PROVE \A d \in committed' : (d.term <= c.term /\ Len(log'[s]) >= d.entry[1]) => log'[s][d.entry[1]] = d.term
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>. SUFFICES ASSUME d.term <= c.term /\ Len(log'[s]) >= d.entry[1]
             PROVE log'[s][d.entry[1]] = d.term
             OBVIOUS
             
        <2>. PICK p \in Server : \E Q \in QuorumsAt(p) : CommitEntry(p, Q)
            OBVIOUS
        <2>. DEFINE ind == Len(log[p])
        <2>. CASE d.entry[1] = ind
            <3>. CASE d.term = currentTerm[p]
                <4>1. log[p][d.entry[1]] = d.term
                    BY DEF CommitEntry
                <4>2. \A t \in Server : currentTerm[p] >= currentTerm[t]
                    BY CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary
                <4>. CASE state[s] = Primary
                    <5>1. currentTerm[s] >= c.term
                        BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, CommitEntry
                    <5>2. currentTerm[s] >= d.term
                        BY <5>1, TypeOKAndNext DEF TypeOK
                    <5>3. currentTerm[s] >= currentTerm[p]
                        BY <5>2
                    <5>4. s = p
                        BY <5>3, <4>2 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm, CommitEntry, TypeOK
                    <5>. QED
                        BY <5>4, <4>1 DEF CommitEntry
                <4>. CASE state[s] = Secondary
                    <5>1. c.term = currentTerm[p]
                        BY <4>2, CommitsMustBeSmallerThanOrEqualToLargestTermAndNext, TypeOKAndNext DEF CommitEntry, TypeOK
                    <5>2. LastTerm(log[s]) = currentTerm[p]
                        <6>. PICK i \in DOMAIN log'[s] : log'[s][i] = c.term
                            OBVIOUS
                        <6>1. i \in DOMAIN log[s] /\ log[s][i] = c.term
                            BY DEF CommitEntry
                        <6>2. LastTerm(log[s]) >= c.term
                            BY <6>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm
                        <6>3. LastTerm(log[s]) >= currentTerm[p]
                            BY <6>2, TypeOKAndNext DEF LastTerm, TypeOK
                        <6>4. LastTerm(log[s]) <= currentTerm[p]
                            <7>. PICK lt \in Server : LastTerm(log[s]) <= currentTerm[lt]
                                BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                            <7>1. currentTerm[lt] <= currentTerm[p]
                                BY CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary
                            <7>. QED BY <7>1 DEF LastTerm, TypeOK
                        <6>. QED BY <6>3, <6>4 DEF LastTerm, TypeOK
                    <5>3. Len(log[s]) = ind
                        <6>1. Len(log[s]) >= ind
                            BY DEF CommitEntry
                        <6>2. Len(log[s]) <= ind
                            <7>1. LastTerm(log[s]) >= currentTerm[s]
                                BY <5>2, CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary
                            <7>. CASE LastTerm(log[s]) = currentTerm[s]
                                <8>. CASE \E lp \in Server : state[lp] = Primary /\ currentTerm[lp] = currentTerm[s] /\ Len(log[lp]) >= Len(log[s])
                                    <9>. PICK lp \in Server : state[lp] = Primary /\ currentTerm[lp] = currentTerm[s] /\ Len(log[lp]) >= Len(log[s])
                                        OBVIOUS
                                    <9>1. currentTerm[p] = currentTerm[lp]
                                        BY <5>2
                                    <9>2. lp = p
                                        BY <9>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm, CommitEntry
                                    <9>. QED BY <9>2
                                <8>. CASE \E lp \in Server : currentTerm[lp] > currentTerm[s]
                                    \* impossible, proof by contradiction
                                    <9>. PICK lp \in Server : currentTerm[lp] > currentTerm[s]
                                        OBVIOUS
                                    <9>1. currentTerm[s] = currentTerm[p]
                                        BY <5>2 DEF LastTerm, TypeOK
                                    <9>2. currentTerm[lp] <= currentTerm[p]
                                        BY CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary, TypeOK
                                    <9>3. currentTerm[lp] <= currentTerm[s]
                                        BY <9>2, <9>1
                                    <9>. QED BY <9>3 DEF TypeOK
                                <8>. QED BY DEF SMS_LC_II, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm, CommitEntry
                            <7>. CASE LastTerm(log[s]) > currentTerm[s]
                                <8>. CASE \E lp \in Server : state[lp] = Primary /\ currentTerm[lp] = LastTerm(log[s]) /\ Len(log[lp]) >= Len(log[s])
                                    <9>. PICK lp \in Server : state[lp] = Primary /\ currentTerm[lp] = LastTerm(log[s]) /\ Len(log[lp]) >= Len(log[s])
                                        OBVIOUS
                                    <9>1. currentTerm[p] = currentTerm[lp]
                                        BY <5>2
                                    <9>2. lp = p
                                        BY <9>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, OnePrimaryPerTerm, CommitEntry
                                    <9>. QED BY <9>2
                                <8>. CASE \E lp \in Server : currentTerm[lp] > LastTerm(log[s])
                                    \* impossible, proof by contradiction
                                    <9>. PICK lp \in Server : currentTerm[lp] > LastTerm(log[s])
                                        OBVIOUS
                                    <9>1. LastTerm(log[s]) = currentTerm[p]
                                        BY <5>2
                                    <9>2. currentTerm[lp] <= currentTerm[p]
                                        BY CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary, TypeOK
                                    <9>3. currentTerm[lp] <= LastTerm(log[s])
                                        BY <9>2, <9>1
                                    <9>. QED BY <9>3 DEF LastTerm, TypeOK
                                <8>. QED BY PrimaryAndSecondaryAreDifferent
                                    DEF SMS_LC_II, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm, CommitEntry
                            <7>. QED BY <7>1 DEF LastTerm, TypeOK
                        <6>. QED BY <6>1, <6>2 DEF TypeOK
                    <5>. QED BY <5>2, <5>3 DEF LastTerm, CommitEntry
                <4>. QED BY DEF TypeOK
            <3>. CASE d.term # currentTerm[p]
                \* this case is impossible; proof by contradiction
                <4>1. d \in committed
                    BY DEF CommitEntry
                <4>. PICK prevQ \in Quorums(Server) : \A q \in prevQ : \E i \in DOMAIN log[q] : log[q][i] = d.term /\ i = d.entry[1]
                    BY <4>1 DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
                <4>. PICK nextQ \in QuorumsAt(p) : CommitEntry(p, nextQ)
                    OBVIOUS
                <4>. PICK q \in Server : q \in prevQ /\ q \in nextQ
                    BY AllQuorumsOverlap DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, AllConfigsAreServer, QuorumsAt, Quorums
                <4>2. InLog(<<ind,d.term>>, q)
                    BY <4>1 DEF InLog
                <4>3. InLog(<<ind, currentTerm[p]>>, q)
                    BY DEF CommitEntry, ImmediatelyCommitted
                <4>. QED BY <4>2, <4>3 DEF InLog, TypeOK
            <3>. QED OBVIOUS
        <2>. CASE d.entry[1] # ind
            <3>1. d \in committed
                BY DEF CommitEntry
            <3>2. \E i \in DOMAIN log[s] : log[s][i] >= d.term
                BY DEF CommitEntry
            <3>3. log[s][d.entry[1]] = d.term
                <4>. CASE \E i \in DOMAIN log[s] : log[s][i] = d.term
                    <5>1. d.term <= d.term
                        BY DEF TypeOK
                    <5>2. Len(log[s]) >= d.entry[1]
                        BY DEF CommitEntry, TypeOK
                    <5>. QED BY <3>1, <5>1, <5>2 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                <4>. CASE \E i \in DOMAIN log[s] : log[s][i] > d.term
                    <5>1. d.term <= d.term
                        BY <3>1 DEF TypeOK
                    <5>. QED BY <3>1, <5>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>. QED BY <3>1, <3>2 DEF TypeOK
            <3>. QED BY <3>3 DEF CommitEntry
        <2>. QED OBVIOUS
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LogsEqualToCommittedMustHaveCommittedIfItFits'
        <2>. QED BY DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LogsLaterThanCommittedMustHaveCommittedAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LogsLaterThanCommittedMustHaveCommitted'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. SUFFICES ASSUME \E s \in Server : ClientRequest(s)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] > c.term) =>
                            \A d \in committed' :
                                d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             BY DEF LogsLaterThanCommittedMustHaveCommitted
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>ccom. c \in committed
            BY DEF ClientRequest
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
             PROVE \A d \in committed' : d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>dcom. d \in committed
            BY DEF ClientRequest
        <2>. SUFFICES ASSUME d.term <= c.term
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             OBVIOUS
             
        <2>. CASE ~ClientRequest(s)
            BY DEF ClientRequest, SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>. CASE ClientRequest(s)
            <3>. CASE Empty(log[s])
                \* this is impossible, proof by contradiction
                <4>1. log'[s][1] = currentTerm[s]
                    BY DEF Empty, ClientRequest
                <4>2. log'[s][1] > c.term
                    BY DEF Empty, ClientRequest
                <4>3. currentTerm[s] > c.term
                    BY <4>1, <4>2, TypeOKAndNext DEF TypeOK
                <4>4. InLog(c.entry, s)
                    BY <4>3 DEF ClientRequest, SMS_LC_II, LeaderCompletenessGeneralized, TypeOK
                <4>. QED BY <4>3, <4>4 DEF InLog, Empty
            <3>. CASE \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i = Len(log'[s]) /\ ~Empty(log[s])
                <4>1. c.term < currentTerm[s]
                    <5>1. LastTerm(log'[s]) = currentTerm[s]
                        BY DEF ClientRequest, LastTerm, TypeOK
                    <5>2. LastTerm(log'[s]) > c.term
                        BY DEF LastTerm
                    <5>. QED BY <5>1, <5>2
                <4>2. InLog(d.entry, s)
                    BY <4>1 DEF SMS_LC_II, LeaderCompletenessGeneralized, ClientRequest, TypeOK
                <4>. QED BY <4>2 DEF InLog, ClientRequest, TypeOK, SMS_LC_II, CommittedTermMatchesEntry
            <3>. CASE \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i < Len(log'[s]) /\ ~Empty(log[s])
                <4>1. \E i \in DOMAIN log[s] : log[s][i] > c.term /\ i <= Len(log[s])
                    BY DEF ClientRequest, TypeOK
                <4>2. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                    BY <2>ccom, <2>dcom, <4>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>. QED BY <4>2 DEF ClientRequest, TypeOK, SMS_LC_II, CommitIndexGreaterThanZero
            <3>. QED BY TypeOKAndNext DEF Empty, TypeOK
        <2>. QED OBVIOUS
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. SUFFICES ASSUME \E s,t \in Server : GetEntries(s, t)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] > c.term) =>
                            \A d \in committed' :
                                d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             BY DEF LogsLaterThanCommittedMustHaveCommitted
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>ccom. c \in committed
            BY DEF GetEntries
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
             PROVE \A d \in committed' : d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>dcom. d \in committed
            BY DEF GetEntries
        <2>. SUFFICES ASSUME d.term <= c.term
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             OBVIOUS
             
        <2>. CASE \E t,u \in Server : GetEntries(u, t) /\ u # s
            <3>1. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                BY <2>ccom, <2>dcom DEF GetEntries, SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
            <3>. QED BY <3>1 DEF GetEntries, TypeOK
        <2>. CASE \E t \in Server : GetEntries(s, t)
            <3>. PICK t \in Server : GetEntries(s ,t)
                OBVIOUS
            <3>1. \/ Empty(log[s])
                  \/ \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i = Len(log'[s]) /\ ~Empty(log[s])
                  \/ \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i < Len(log'[s]) /\ ~Empty(log[s])
                BY TypeOKAndNext DEF SMS_LC_II, CommitIndexGreaterThanZero, Empty, TypeOK
            <3>. CASE Empty(log[s])
                <4>1. log[t][1] > c.term
                    BY DEF GetEntries, Empty
                <4>2. log[t][d.entry[1]] = d.term /\ Len(log[t]) >= d.entry[1]
                    <5>1. \E i \in DOMAIN log[t] : log[t][i] > c.term
                        BY <4>1 DEF GetEntries
                    <5>. QED BY <2>ccom, <2>dcom, <5>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>3. d.entry[1] = 1
                    <5>. SUFFICES ASSUME d.entry[1] > 1
                         PROVE FALSE
                         BY <2>dcom DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
                    <5>1. log[t][1] <= log[t][d.entry[1]]
                        BY <2>dcom, <4>2 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                    <5>2. log[t][d.entry[1]] <= c.term
                        BY <2>dcom, <4>2 DEF TypeOK
                    <5>3. log[t][1] <= c.term
                        BY <2>ccom, <2>dcom, <5>1, <5>2, <4>2 DEF TypeOK
                    <5>. QED BY <2>ccom, <4>1, <5>3 DEF GetEntries, TypeOK
                <4>. QED BY <2>dcom, <4>2, <4>3 DEF GetEntries, Empty, TypeOK
            <3>. CASE \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i = Len(log'[s]) /\ ~Empty(log[s])
                <4>. PICK i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i = Len(log'[s]) /\ ~Empty(log[s])
                    OBVIOUS
                <4>1. log[t][i] > c.term
                    BY DEF GetEntries
                <4>2. log[t][d.entry[1]] = d.term /\ Len(log[t]) >= d.entry[1]
                    BY <2>ccom, <2>dcom, <4>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, GetEntries
                <4>3. d.entry[1] <= i
                    <5>. SUFFICES ASSUME d.entry[1] > i
                         PROVE FALSE
                         BY <2>dcom DEF TypeOK
                    <5>1. log[t][i] <= log[t][d.entry[1]]
                        BY <2>dcom, <4>2 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
                    <5>2. log[t][d.entry[1]] <= c.term
                        BY <2>dcom, <4>2 DEF TypeOK
                    <5>3. log[t][i] <= c.term
                        BY <2>ccom, <2>dcom, <5>1, <5>2, <4>2 DEF TypeOK
                    <5>. QED BY <2>ccom, <4>1, <5>3 DEF GetEntries, TypeOK
                <4>. CASE d.entry[1] = i
                    BY <4>2 DEF GetEntries
                <4>. CASE d.entry[1] < i
                    <5>1. d.entry[1] > 0 /\ d.entry[1] <= Len(log[s])
                        BY <2>dcom DEF SMS_LC_II, CommitIndexGreaterThanZero, GetEntries, TypeOK
                    <5>2. d.entry[1] \in DOMAIN log[s]
                        BY <2>dcom, <5>1 DEF TypeOK
                    <5>. CASE d.entry[1] = Len(log[s])
                        BY <4>2, <5>2 DEF GetEntries, TypeOK
                    <5>. CASE d.entry[1] < Len(log[s])
                        <6>. CASE log[s][d.entry[1]] < d.term
                            \* impossible, proof by contradiction
                            <7>1. d.term < log'[s][i]
                                BY TypeOKAndNext DEF TypeOK
                            <7>2. log'[s][d.entry[1]] < d.term
                                BY <2>dcom, <5>2 DEF GetEntries, TypeOK
                            <7>3. d.term <= LastTerm(log[s])
                                <8>1. log[t][d.entry[1]] <= log[t][Len(log[s])]
                                    BY <4>2, <5>2 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, GetEntries, TypeOK
                                <8>2. d.term <= log[t][Len(log[s])]
                                    BY <8>1, <4>2
                                <8>. QED BY <8>2 DEF GetEntries, LastTerm, TypeOK
                            <7>. CASE d.term = LastTerm(log[s])
                                <8>1. \E j \in DOMAIN log[s] : log[s][j] = d.term
                                    BY <2>dcom DEF LastTerm, TypeOK
                                <8>2. d.term <= d.term /\ Len(log[s]) >= d.entry[1]
                                    BY <2>dcom, <5>1 DEF TypeOK
                                <8>3. log[s][d.entry[1]] = d.term
                                    BY <2>dcom, <8>1, <8>2 DEF SMS_LC_II, LogsEqualToCommittedMustHaveCommittedIfItFits
                                <8>. QED BY <8>3 DEF LastTerm, TypeOK
                            <7>. CASE d.term < LastTerm(log[s])
                                <8>1. \E j \in DOMAIN log[s] : log[s][j] > d.term
                                    BY <2>dcom DEF LastTerm, TypeOK
                                <8>2. d.term <= d.term
                                    BY <2>dcom DEF TypeOK
                                <8>3. log[s][d.entry[1]] = d.term
                                    BY <2>dcom, <8>1, <8>2 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                                <8>. QED BY <8>3, <5>2 DEF LastTerm, TypeOK
                            <7>. QED BY <2>dcom, <7>3 DEF LastTerm, TypeOK
                        <6>. CASE log[s][d.entry[1]] > d.term
                            \* impossible, proof by contradiction
                            \* based on <7>3 we could simply directly prove that log[s][d.entry[1]] = d.term, but that seems really
                            \* weird since there's a clear contradiction hanging around.  so we prove by contradiction, see <7>4
                            <7>1. d.entry[1] \in DOMAIN log[s] /\ log[s][d.entry[1]] > d.term /\ d.entry[1] <= Len(log[s])
                                BY <5>2
                            <7>2. d.term <= d.term
                                BY <2>dcom DEF TypeOK
                            <7>3. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                                BY <2>dcom, <7>1, <7>2 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                            <7>4. log[s][d.entry[1]] = d.term /\ log[s][d.entry[1]] > d.term
                                BY <7>3
                            <7>. QED BY <7>4
                        <6>. CASE log[s][d.entry[1]] = d.term
                            BY <5>2 DEF GetEntries, TypeOK
                        <6>. QED BY <2>dcom, <5>2 DEF TypeOK
                    <5>. QED BY <5>2 DEF TypeOK
                <4>. QED BY <2>dcom, <4>3 DEF TypeOK
            <3>. CASE \E i \in DOMAIN log'[s] : log'[s][i] > c.term /\ i < Len(log'[s]) /\ ~Empty(log[s])
                <4>1. \E i \in DOMAIN log[s] : log[s][i] > c.term /\ i <= Len(log[s])
                    BY DEF GetEntries, TypeOK
                <4>2. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                    BY <2>ccom, <2>dcom, <4>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>. QED BY <4>2 DEF GetEntries, TypeOK, SMS_LC_II, CommitIndexGreaterThanZero
            <3>. QED BY <3>1
        <2>. QED OBVIOUS
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. SUFFICES ASSUME \E s,t \in Server : RollbackEntries(s, t)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] > c.term) =>
                            \A d \in committed' :
                                d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             BY DEF LogsLaterThanCommittedMustHaveCommitted
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>ccom. c \in committed
            BY DEF RollbackEntries
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
             PROVE \A d \in committed' : d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>dcom. d \in committed
            BY DEF RollbackEntries
        <2>. SUFFICES ASSUME d.term <= c.term
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             OBVIOUS
        
        <2>1. Len(log[s]) >= d.entry[1] /\ log[s][d.entry[1]] = d.term
            <3>1. \E i \in DOMAIN log[s] : log[s][i] > c.term /\ d.term <= c.term
                BY DEF RollbackEntries
            <3>. QED BY <2>ccom, <2>dcom, <3>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
        <2>norol. CASE \E u,t \in Server : RollbackEntries(u, t) /\ u # s
            <3>. QED BY <2>1, <2>norol DEF RollbackEntries, TypeOK
        <2>. SUFFICES ASSUME \E t \in Server : RollbackEntries(s, t)
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             BY <2>norol
        
        <2>2. d.entry[1] \in DOMAIN log'[s]
            <3>1. d.entry[1] >= 1
                BY <2>dcom DEF SMS_LC_II, CommitIndexGreaterThanZero, TypeOK
            <3>2. d.entry[1] < Len(log[s])
                <4>. SUFFICES ASSUME d.entry[1] = Len(log[s])
                     PROVE FALSE
                     BY <2>dcom, <2>1 DEF TypeOK
                <4>. PICK t \in Server : RollbackEntries(s, t)
                    OBVIOUS
                <4>1. log[t][d.entry[1]] = d.term /\ Len(log[t]) >= d.entry[1]
                    <5>1. \E i \in DOMAIN log[t] : log[t][i] > c.term
                        <6>. PICK i \in DOMAIN log'[s] : log'[s][i] > c.term
                            OBVIOUS
                        <6>1. LastTerm(log[s]) >= log'[s][i]
                            BY DEF RollbackEntries, LastTerm, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically
                        <6>2. LastTerm(log[t]) > LastTerm(log[s]) /\ LastTerm(log[s]) >= log'[s][i] /\ log'[s][i] > c.term
                            BY <6>1 DEF RollbackEntries, CanRollback
                        <6>. QED BY <6>2, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>. QED BY <2>ccom, <2>dcom, <5>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>2. log[s][d.entry[1]] # log[t][d.entry[1]]
                    <5>1. Len(log[s]) <= Len(log[t]) /\ LastTerm(log[s]) # LogTerm(t, Len(log[s]))
                        BY <4>1 DEF RollbackEntries, CanRollback
                    <5>2. LastTerm(log[s]) # log[t][d.entry[1]]
                        BY <5>1 DEF LastTerm, LogTerm, GetTerm
                    <5>3. log[s][d.entry[1]] = LastTerm(log[s])
                        BY DEF LastTerm, RollbackEntries, CanRollback
                    <5>. QED BY <5>2, <5>3 DEF LastTerm, TypeOK
                <4>3. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                    <5>1. \E i \in DOMAIN log[s] : log[s][i] > c.term
                        BY DEF RollbackEntries, TypeOK
                    <5>. QED BY <2>ccom, <2>dcom, <5>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
                <4>4. log[s][d.entry[1]] = log[t][d.entry[1]]
                    BY <2>dcom, <4>1, <4>3 DEF TypeOK
                <4>. QED BY <4>2, <4>4
            <3>. QED BY <3>1, <3>2, <2>dcom DEF RollbackEntries, TypeOK
        <2>. QED BY <2>1, <2>2 DEF RollbackEntries, TypeOK
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. SUFFICES ASSUME \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] > c.term) =>
                            \A d \in committed' :
                                d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             BY DEF LogsLaterThanCommittedMustHaveCommitted
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>ccom. c \in committed
            BY DEF BecomeLeader
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
             PROVE \A d \in committed' : d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>dcom. d \in committed
            BY DEF BecomeLeader
        <2>. SUFFICES ASSUME d.term <= c.term
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             OBVIOUS
        
        <2>notbecome. CASE \E t \in Server : \E Q \in QuorumsAt(t) : BecomeLeader(t, Q) /\ t # s
            <3>1. log'[s] = log[s]
                BY <2>notbecome DEF BecomeLeader, TypeOK
            <3>2. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                BY <3>1 DEF BecomeLeader, SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, TypeOK
            <3>. QED BY <2>notbecome, <3>2 DEF BecomeLeader, TypeOK
        <2>. SUFFICES ASSUME \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             BY <2>notbecome
             
        \* while techncially sound, it would be cleaner to break the use of the "AndNext" theorems into separate
        \* helper theorems
        <2>1. InLog(d.entry, s)'
            \* we already proved this above so it's safe to use without getting into a circular logical flaw
            <3>1. LeaderCompletenessGeneralized'
                BY LeaderCompletenessGeneralizedAndNext DEF SMS_LC_II
            <3>2. d.term <= currentTerm'[s]
                <4>1. \A t \in Server : currentTerm[t] <= currentTerm[s]
                    BY ElectedLeadersHaveLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary
                <4>2. d.term <= currentTerm[s]
                    BY <2>dcom, <4>1, CommitsMustBeSmallerThanOrEqualToLargestTerm DEF TypeOK
                <4>3. currentTerm[s] <= currentTerm'[s]
                    BY DEF BecomeLeader, TypeOK
                <4>. QED BY <4>2, <4>3, TypeOKAndNext DEF TypeOK
            <3>. QED BY <3>1, <3>2 DEF LeaderCompletenessGeneralized, BecomeLeader
        <2>2. CommittedTermMatchesEntry'
            \* we already proved this above so it's safe to use without getting into a circular logical flaw
            BY CommittedTermMatchesEntryAndNext DEF SMS_LC_II
        <2>. QED BY <2>1, <2>2 DEF InLog, CommittedTermMatchesEntry
    <1>5. (\E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. SUFFICES ASSUME \E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
             PROVE \A s \in Server : \A c \in committed' :
                        (\E i \in DOMAIN log'[s] : log'[s][i] > c.term) =>
                            \A d \in committed' :
                                d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             BY DEF LogsLaterThanCommittedMustHaveCommitted
        <2>. TAKE s \in Server
        <2>. TAKE c \in committed'
        <2>. SUFFICES ASSUME \E i \in DOMAIN log'[s] : log'[s][i] > c.term
             PROVE \A d \in committed' : d.term <= c.term => (log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1])
             OBVIOUS
        <2>. TAKE d \in committed'
        <2>. SUFFICES ASSUME d.term <= c.term
             PROVE log'[s][d.entry[1]] = d.term /\ Len(log'[s]) >= d.entry[1]
             OBVIOUS
        
        <2>. PICK p \in Server : \E Q \in QuorumsAt(p) : CommitEntry(p, Q)
            OBVIOUS
        <2>. DEFINE ind == Len(log[p])
        <2>. CASE d \notin committed
            \* this isn't possible
            <3>. DEFINE newCommit == [entry |-> <<ind, currentTerm[p]>>, term |-> currentTerm[p]]
            <3>1. d = newCommit
                BY DEF CommitEntry
            <3>2. \A i \in DOMAIN log[s] : log[s][i] <= d.term
                <4>1. LastTerm(log[s]) <= currentTerm[p]
                    BY CommittingImpliesLatestTerm DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm, LastTerm, TypeOK
                <4>2. \A i \in DOMAIN log[s] : log[s][i] <= currentTerm[p]
                    BY <4>1 DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm, TypeOK
                <4>. QED BY <3>1, <4>2
            <3>3. \A i \in DOMAIN log'[s] : log'[s][i] <= c.term
                <4>1. \A i \in DOMAIN log'[s] : log'[s][i] <= d.term
                    BY <3>2 DEF CommitEntry
                <4>. QED BY <4>1, TypeOKAndNext DEF TypeOK
            <3>. QED BY <3>3, TypeOKAndNext DEF TypeOK
        <2>. CASE d \in committed
            <3>1. log[s][d.entry[1]] = d.term /\ Len(log[s]) >= d.entry[1]
                <4>1. \E i \in DOMAIN log[s] : log[s][i] > c.term
                    BY DEF CommitEntry
                <4>2. \E i \in DOMAIN log[s] : log[s][i] > d.term
                    BY <4>1, TypeOKAndNext DEF TypeOK
                <4>3. d \in committed /\ d.term <= d.term
                    BY DEF TypeOK
                <4>. QED BY <4>2, <4>3 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
            <3>. QED BY <3>1 DEF CommitEntry
        <2>. QED OBVIOUS
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LogsLaterThanCommittedMustHaveCommitted'
        <2>. QED BY DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntriesMustHaveQuorumsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntriesMustHaveQuorums'
PROOF
    <1>nd. (UNCHANGED committed /\ (\A s \in Server : \A i \in DOMAIN log[s] : Len(log[s]) <= Len(log'[s]) /\ log[s][i] = log'[s][i]))
            => CommittedEntriesMustHaveQuorums'
        <2>. SUFFICES ASSUME UNCHANGED committed /\ \A s \in Server : \A i \in DOMAIN log[s] : Len(log[s]) <= Len(log'[s]) /\ log[s][i] = log'[s][i]
             PROVE \A c \in committed' : \E Q \in Quorums(Server) :
                        \A q \in Q : \E i \in DOMAIN log'[q] : log'[q][i] = c.term /\ i = c.entry[1]
             BY DEF CommittedEntriesMustHaveQuorums
        <2>. TAKE c \in committed'
        <2>1. \E Q \in Quorums(Server) : \A q \in Q : \E i \in DOMAIN log[q] : log[q][i] = c.term /\ i = c.entry[1]
            BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
        <2>. PICK Q \in Quorums(Server) : \A q \in Q : \E i \in DOMAIN log[q] : log[q][i] = c.term /\ i = c.entry[1]
            BY <2>1
        <2>2. Q \in SUBSET Server
            BY DEF Quorums
        <2>3. \A q \in Q : \E i \in DOMAIN log'[q] : log'[q][i] = c.term /\ i = c.entry[1]
            BY <2>2
        <2>. QED BY <2>3
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntriesMustHaveQuorums'
        BY <1>nd DEF ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntriesMustHaveQuorums'
        BY <1>nd DEF GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntriesMustHaveQuorums'
        <2>. SUFFICES ASSUME \E s, t \in Server : RollbackEntries(s, t)
             PROVE \A c \in committed' : \E Q \in Quorums(Server) :
                        \A q \in Q : \E i \in DOMAIN log'[q] : log'[q][i] = c.term /\ i = c.entry[1]
             BY DEF CommittedEntriesMustHaveQuorums
        <2>. TAKE c \in committed'
        <2>1. c \in committed
            BY DEF RollbackEntries
            
        <2>. PICK s \in Server : \E t \in Server : RollbackEntries(s, t)
            OBVIOUS
        <2>. PICK t \in Server : RollbackEntries(s, t)
            OBVIOUS
        <2>2. c.term # LastTerm(log[s]) \/ c.entry[1] # Len(log[s])
            <3>. SUFFICES ASSUME c.term = LastTerm(log[s]) /\ c.entry[1] = Len(log[s])
                 PROVE FALSE
                 OBVIOUS
            <3>1. c.term < LastTerm(log[t])
                BY DEF RollbackEntries, CanRollback
            <3>2. Len(log[t]) >= c.entry[1] /\ log[t][c.entry[1]] = c.term
                <4>1. \E i \in DOMAIN log[t] : log[t][i] > c.term
                    BY <2>1, <3>1 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted, LastTerm, TypeOK
                <4>2. t \in Server /\ c \in committed /\ c.term <= c.term
                    BY <2>1 DEF TypeOK
                <4>. QED BY <4>1, <4>2 DEF SMS_LC_II, LogsLaterThanCommittedMustHaveCommitted
            <3>. CASE Len(log[s]) > Len(log[t])
                BY <3>1, <3>2 DEF TypeOK
            <3>. CASE Len(log[s]) <= Len(log[t]) /\ LastTerm(log[s]) # LogTerm(t, Len(log[s]))
                BY <3>2 DEF LastTerm, LogTerm, GetTerm, TypeOK
            <3>. QED BY DEF RollbackEntries, CanRollback
        <2>3. \E Q \in Quorums(Server) : \A q \in Q : \E i \in DOMAIN log[q] : log[q][i] = c.term /\ i = c.entry[1]
            BY <2>1 DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
        <2>. QED BY <2>2, <2>3 DEF RollbackEntries, LastTerm
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntriesMustHaveQuorums'
        <2>. SUFFICES ASSUME \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
             PROVE CommittedEntriesMustHaveQuorums'
             OBVIOUS
        <2>. PICK s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
            OBVIOUS
        <2>. DEFINE newTerm == currentTerm[s] + 1
        <2>. CASE log' = [log EXCEPT ![s] = Append(log[s], newTerm)]
            BY <1>nd DEF BecomeLeader, TypeOK
        <2>. CASE UNCHANGED log
            BY <1>nd DEF BecomeLeader
        <2>. QED BY DEF BecomeLeader
    <1>5. (\E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntriesMustHaveQuorums'
        <2>. SUFFICES ASSUME \E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)
             PROVE \A c \in committed' : \E Q \in Quorums(Server) :
                        \A q \in Q : \E i \in DOMAIN log'[q] : log'[q][i] = c.term /\ i = c.entry[1]
             BY DEF CommittedEntriesMustHaveQuorums
        <2>. TAKE c \in committed'
        <2>. PICK p \in Server : \E Q \in QuorumsAt(p) : CommitEntry(p, Q)
            OBVIOUS
        <2>. CASE c \in committed
            <3>1. \E Q \in Quorums(Server) :  \A q \in Q : \E i \in DOMAIN log[q] : log[q][i] = c.term /\ i = c.entry[1]
                BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
            <3>. QED BY <3>1 DEF CommitEntry
        <2>. CASE c \notin committed
            <3>. PICK Q \in QuorumsAt(p) : CommitEntry(p, Q)
                OBVIOUS
            <3>1. \A q \in Q : InLog(c.entry, q)
                BY DEF CommitEntry, ImmediatelyCommitted
            <3>2. Q \in Quorums(Server)
                BY DEF QuorumsAt, SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, AllConfigsAreServer
            <3>. QED BY <3>1, <3>2 DEF InLog, SMS_LC_II, CommittedTermMatchesEntry, CommitEntry
        <2>. QED OBVIOUS
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntriesMustHaveQuorums'
        BY <1>nd DEF UpdateTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

-----------------------------------------------------------------------------------

(* Init => SMS_LC_II *)

THEOREM InitImpliesSMS_LC_II ==
ASSUME TRUE
PROVE Init => SMS_LC_II
BY InitImpliesLemmaSecondariesFollowPrimary, PrimaryAndSecondaryAreDifferent
DEF Init, SMS_LC_II,
    LemmaSecondariesFollowPrimary,
    PrimariesTermGreaterThanZero,
    CommitIndexGreaterThanZero,
    CommitTermGreaterThanZero,
    CommittedTermMatchesEntry,
    CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens,
    CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms,
    LeaderCompletenessGeneralized,
    LogsEqualToCommittedMustHaveCommittedIfItFits,
    LogsLaterThanCommittedMustHaveCommitted,
    CommittedEntriesMustHaveQuorums

-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM SMS_LC_IIAndNext ==
ASSUME TypeOK, SMS_LC_II, Next
PROVE TypeOK' /\ SMS_LC_II'
PROOF BY InitImpliesSMS_LC_II, TypeOKAndNext,
         LemmaSecondariesFollowPrimaryAndNext,
         PrimariesTermGreaterThanZeroAndNext,
         CommitIndexGreaterThanZeroAndNext,
         CommitTermGreaterThanZeroAndNext,
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

-----------------------------------------------------------------------------------

\* the lengths I go to prove the obvious...
THEOREM NatPairNotEqual ==
ASSUME NEW p1 \in (Nat \times Nat),
       NEW p2 \in (Nat \times Nat)
PROVE p1 # p2 => (p1[1] # p2[1] \/ p1[2] # p2[2])
PROOF
    <1>. SUFFICES ASSUME p1 # p2
         PROVE p1[1] # p2[1] \/ p1[2] # p2[2]
         OBVIOUS
    <1>. PICK p1First \in Nat : \E p1Second \in Nat : p1 = <<p1First,p1Second>>
        OBVIOUS
    <1>. PICK p1Second \in Nat : p1 = <<p1First,p1Second>>
        OBVIOUS
    <1>. PICK p2First \in Nat : \E p2Second \in Nat : p2 = <<p2First,p2Second>>
        OBVIOUS
    <1>. PICK p2Second \in Nat : p2 = <<p2First,p2Second>>
        OBVIOUS
    <1>1. p1First # p2First \/ p1Second # p2Second
        OBVIOUS
    <1>2. <<p1First,p1Second>> \in Seq(Nat) /\ <<p2First,p2Second>> \in Seq(Nat)
        OBVIOUS
    <1>3. \E p1Seq \in Seq(Nat) : p1Seq = <<p1First,p1Second>>
        BY <1>2
    <1>4. \E p2Seq \in Seq(Nat) : p2Seq = <<p2First,p2Second>>
        BY <1>2
    <1>. QED BY <1>1, <1>3, <1>4

THEOREM SMS_LC_II_ImpliesSMS ==
ASSUME SMS_LC_II, TypeOK
PROVE StateMachineSafety
PROOF
    <1>. SUFFICES ASSUME \E c1,c2 \in committed : c1.entry[1] = c2.entry[1] /\ c1 # c2
         PROVE FALSE
         BY DEF StateMachineSafety
    <1>. PICK c1 \in committed : \E c2 \in committed : c1.entry[1] = c2.entry[1] /\ c1 # c2
        OBVIOUS
    <1>. PICK c2 \in committed : c1.entry[1] = c2.entry[1] /\ c1 # c2
        OBVIOUS
    <1>1. c1.term # c2.term
        <2>1. c1.entry \in (Nat \times Nat) /\ c2.entry \in (Nat \times Nat)
            BY DEF TypeOK
        <2>2. c1.term # c2.term \/ c1.entry # c2.entry
            BY DEF TypeOK
        <2>. QED BY <2>1, <2>2, NatPairNotEqual DEF SMS_LC_II, CommittedTermMatchesEntry
    <1>. PICK Q1 \in Quorums(Server) : \A q \in Q1 : \E i \in DOMAIN log[q] : log[q][i] = c1.term /\ i = c1.entry[1]
        BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
    <1>. PICK Q2 \in Quorums(Server) : \A q \in Q2 : \E i \in DOMAIN log[q] : log[q][i] = c2.term /\ i = c2.entry[1]
        BY DEF SMS_LC_II, CommittedEntriesMustHaveQuorums
    <1>2. \E q \in Server : q \in Q1 /\ q \in Q2
        <2>1. (\E s \in Server : Q1 \in QuorumsAt(s)) /\ (\E s \in Server : Q2 \in QuorumsAt(s))
            BY ServerIsNonempty DEF SMS_LC_II, LemmaSecondariesFollowPrimary, LemmaBasic, AllConfigsAreServer, Quorums, QuorumsAt
        <2>. QED BY <2>1, AllQuorumsOverlap DEF SMS_LC_II, LemmaSecondariesFollowPrimary, QuorumsAt, Quorums
    <1>. QED BY <1>1, <1>2

=============================================================================

