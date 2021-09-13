----------------------------- MODULE IndProof -----------------------------

EXTENDS MongoRaftReconfig, Defs, Axioms, TypeOK, ElectionSafetyLemmas, LogPropertiesLemmas,
        LeaderCompletenessLemmas, LeaderCompletenessLemmasCtd, Lib

LEMMA IndAndNext ==
ASSUME TypeOK, Ind, Next
PROVE Ind'
PROOF
    <1>1. OnePrimaryPerTerm' BY OnePrimaryPerTermAndNext
    <1>2. PrimaryConfigTermEqualToCurrentTerm' BY PrimaryConfigTermEqualToCurrentTermAndNext
    <1>3. ConfigVersionAndTermUnique' BY ConfigVersionAndTermUniqueAndNext
    <1>4. PrimaryInTermContainsNewestConfigOfTerm' BY PrimaryInTermContainsNewestConfigOfTermAndNext
    <1>5. ActiveConfigsOverlap' BY ActiveConfigsOverlapAndNext
    <1>6. ActiveConfigsSafeAtTerms' BY ActiveConfigsSafeAtTermsAndNext
    <1>7. LogMatching' BY LogMatchingAndNext
    <1>8. TermsOfEntriesGrowMonotonically' BY TermsOfEntriesGrowMonotonicallyAndNext
    <1>9. PrimaryHasEntriesItCreated' BY PrimaryHasEntriesItCreatedAndNext
    <1>10. CurrentTermAtLeastAsLargeAsLogTermsForPrimary' BY CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext
    <1>11. LogEntryInTermImpliesConfigInTerm' BY LogEntryInTermImpliesConfigInTermAndNext
    <1>12. UniformLogEntriesInTerm' BY UniformLogEntriesInTermAndNext
    <1>13. CommittedEntryIndexesAreNonZero' BY CommittedEntryIndexesAreNonZeroAndNext
    <1>14. CommittedTermMatchesEntry' BY CommittedTermMatchesEntryAndNext
    <1>15. LeaderCompletenessGeneralized' BY LeaderCompletenessGeneralizedAndNext
    <1>16. LogsLaterThanCommittedMustHaveCommitted' BY LogsLaterThanCommittedMustHaveCommittedAndNext
    <1>17. ActiveConfigsOverlapWithCommittedEntry' BY ActiveConfigsOverlapWithCommittedEntryAndNext
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms' BY NewerConfigsDisablePrimaryCommitsInOlderTermsAndNext
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
                <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18
          DEF Ind

--------------------------------------------------------------------------------

(* Overall Result *)

LEMMA InitImpliesInd ==
ASSUME Init
PROVE Ind
PROOF
    <1>1. OnePrimaryPerTerm
        BY PrimaryAndSecondaryAreDifferent DEF Init, OSM!Init, CSM!Init, OnePrimaryPerTerm
    <1>2. PrimaryConfigTermEqualToCurrentTerm
        BY DEF Init, OSM!Init, CSM!Init, PrimaryConfigTermEqualToCurrentTerm
    <1>3. ConfigVersionAndTermUnique
        BY DEF Init, OSM!Init, CSM!Init, ConfigVersionAndTermUnique
    <1>4. PrimaryInTermContainsNewestConfigOfTerm
        BY DEF Init, OSM!Init, CSM!Init, PrimaryInTermContainsNewestConfigOfTerm
    <1>5. ActiveConfigsOverlap
        BY ConfigQuorumsOverlap DEF Init, OSM!Init, CSM!Init, ActiveConfigsOverlap,
                QuorumsOverlap, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, Quorums, CV
    <1>6. ActiveConfigsSafeAtTerms
        BY QuorumsAreNonEmpty DEF Init, OSM!Init, CSM!Init, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, Quorums, CV
    <1>7. LogMatching
        BY DEF Init, OSM!Init, CSM!Init, LogMatching
    <1>8. TermsOfEntriesGrowMonotonically
        BY DEF Init, OSM!Init, CSM!Init, TermsOfEntriesGrowMonotonically
    <1>9. PrimaryHasEntriesItCreated
        BY DEF Init, OSM!Init, CSM!Init, PrimaryHasEntriesItCreated
    <1>10. CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        BY DEF Init, OSM!Init, CSM!Init, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>11. LogEntryInTermImpliesConfigInTerm
        BY DEF Init, OSM!Init, CSM!Init, LogEntryInTermImpliesConfigInTerm
    <1>12. UniformLogEntriesInTerm
        BY DEF Init, OSM!Init, CSM!Init, UniformLogEntriesInTerm
    <1>13. CommittedEntryIndexesAreNonZero
        BY DEF Init, OSM!Init, CSM!Init, CommittedEntryIndexesAreNonZero
    <1>14. CommittedTermMatchesEntry
        BY DEF Init, OSM!Init, CSM!Init, CommittedTermMatchesEntry
    <1>15. LeaderCompletenessGeneralized
        BY DEF Init, OSM!Init, CSM!Init, LeaderCompletenessGeneralized
    <1>16. LogsLaterThanCommittedMustHaveCommitted
        BY DEF Init, OSM!Init, CSM!Init, LogsLaterThanCommittedMustHaveCommitted
    <1>17. ActiveConfigsOverlapWithCommittedEntry
        BY DEF Init, OSM!Init, CSM!Init, ActiveConfigsOverlapWithCommittedEntry, InLog
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms
        BY DEF Init, OSM!Init, CSM!Init, NewerConfigsDisablePrimaryCommitsInOlderTerms
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
                <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18
          DEF Ind

THEOREM IndIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => Ind
      /\ (TypeOK /\ Ind /\ Next) => (TypeOK /\ Ind)'
PROOF BY InitImpliesTypeOK, InitImpliesInd, TypeOKAndNext, IndAndNext

=============================================================================
