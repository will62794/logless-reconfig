------------------- MODULE MongoStaticRaftProofsSMS_LC_II ------------------

EXTENDS MongoStaticRaft, MongoStaticRaftProofsLemmaBasic, MongoStaticRaftProofsLemmaSecondariesFollowPrimary,
        SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS

SMS_LC_II ==
    /\ LemmaSecondariesFollowPrimary
    /\ CommittedTermMatchesEntry
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ LogsEqualToCommittedMustHaveCommittedIfItFits
    /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
    /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    /\ LeaderCompletenessGeneralized
    /\ CommittedEntriesMustHaveQuorums


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
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLensAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens'
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms'
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LeaderCompletenessGeneralizedAndNext ==
ASSUME SMS_LC_II, TypeOK, Next
PROVE LeaderCompletenessGeneralized'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LeaderCompletenessGeneralized'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LeaderCompletenessGeneralized'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LeaderCompletenessGeneralized'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LeaderCompletenessGeneralized'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LeaderCompletenessGeneralized'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LeaderCompletenessGeneralized'
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

(* Init => LemmaSecondariesFollowPrimary *)

THEOREM InitImpliesSMS_LC_II ==
ASSUME TRUE
PROVE Init => SMS_LC_II
(*PROOF
    <1>. Init => \A s \in Server : state[s] = Secondary
         BY DEF Init
    <1>. Init => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    <1>. Init => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
        BY DEF SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
    <1>1. QED BY InitImpliesLemmaBasic DEF LemmaSecondariesFollowPrimary*)

-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM SMS_LC_IIAndNext ==
ASSUME TypeOK, SMS_LC_II, Next
PROVE TypeOK' /\ SMS_LC_II'
PROOF BY InitImpliesSMS_LC_II, TypeOKAndNext,
         LemmaSecondariesFollowPrimaryAndNext,
         CommittedTermMatchesEntryAndNext,
         LogsLaterThanCommittedMustHaveCommittedAndNext,
         LogsEqualToCommittedMustHaveCommittedIfItFitsAndNext,
         CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLensAndNext,
         CommittedEntryTermMustBeSmallerThanOrEqualtoAllTermsAndNext,
         LeaderCompletenessGeneralizedAndNext,
         CommittedEntriesMustHaveQuorumsAndNext
      DEF SMS_LC_II

THEOREM SMS_LC_II_IsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => (TypeOK /\ SMS_LC_II)
      /\ (TypeOK /\ SMS_LC_II /\ Next) => (TypeOK /\ SMS_LC_II)'
PROOF BY InitImpliesTypeOK, InitImpliesSMS_LC_II, TypeOKAndNext, SMS_LC_IIAndNext

=============================================================================

