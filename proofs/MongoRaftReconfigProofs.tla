----------------------------- MODULE MongoRaftReconfigProofs -----------------------------
\*
\* This module contains the top level statement of the theorems that establish the safety
\* properties of MongoRaftReconfig. Many of the detailed lemmas and proofs for
\* proving these theorems are delegated to auxiliary modules, which are imported by this
\* module.
\*

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, ElectionSafetyLemmas, LogLemmas,
        LeaderCompletenessLemmas, StateMachineSafetyLemmas, Lib, AuxLemmas

\*
\* Establishing the inductive invariant.
\*

LEMMA IndAndNext ==
ASSUME Ind, Next
PROVE Ind'
PROOF
    <1>1. TypeOK' BY TypeOKAndNext DEF Ind
    <1>2. OnePrimaryPerTerm' BY OnePrimaryPerTermAndNext
    <1>3. PrimaryConfigTermEqualToCurrentTerm' BY PrimaryConfigTermEqualToCurrentTermAndNext
    <1>4. ConfigVersionAndTermUnique' BY ConfigVersionAndTermUniqueAndNext
    <1>5. PrimaryInTermContainsNewestConfigOfTerm' BY PrimaryInTermContainsNewestConfigOfTermAndNext
    <1>6. ActiveConfigsOverlap' BY ActiveConfigsOverlapAndNext
    <1>7. ActiveConfigsSafeAtTerms' BY ActiveConfigsSafeAtTermsAndNext
    <1>8. LogMatching' BY LogMatchingAndNext
    <1>9. TermsOfEntriesGrowMonotonically' BY TermsOfEntriesGrowMonotonicallyAndNext
    <1>10. PrimaryHasEntriesItCreated' BY PrimaryHasEntriesItCreatedAndNext
    <1>11. CurrentTermAtLeastAsLargeAsLogTermsForPrimary' BY CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext
    <1>12. LogEntryInTermImpliesConfigInTerm' BY LogEntryInTermImpliesConfigInTermAndNext
    <1>13. UniformLogEntriesInTerm' BY UniformLogEntriesInTermAndNext
    <1>14. CommittedEntryIndexesAreNonZero' BY CommittedEntryIndexesAreNonZeroAndNext
    <1>15. CommittedTermMatchesEntry' BY CommittedTermMatchesEntryAndNext
    <1>16. LeaderCompleteness' BY LeaderCompletenessAndNext
    <1>17. LogsLaterThanCommittedMustHaveCommitted' BY LogsLaterThanCommittedMustHaveCommittedAndNext
    <1>18. ActiveConfigsOverlapWithCommittedEntry' BY ActiveConfigsOverlapWithCommittedEntryAndNext
    <1>19. NewerConfigsDisablePrimaryCommitsInOlderTerms' BY NewerConfigsDisablePrimaryCommitsInOlderTermsAndNext
    <1>20. ConfigsNonempty' BY ConfigsNonemptyAndNext
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
                <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20
          DEF Ind

LEMMA IndAndUnchanged ==
ASSUME Ind, UNCHANGED vars
PROVE Ind'
PROOF
    <1>.  USE DEF ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
    <1>1. TypeOK' BY DEF Ind, TypeOK, vars
    <1>2. OnePrimaryPerTerm' BY DEF Ind, OnePrimaryPerTerm, TypeOK, vars
    <1>3. PrimaryConfigTermEqualToCurrentTerm' BY DEF Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK, vars
    <1>4. ConfigVersionAndTermUnique' BY DEF Ind, ConfigVersionAndTermUnique, TypeOK, vars
    <1>5. PrimaryInTermContainsNewestConfigOfTerm' BY DEF Ind, PrimaryInTermContainsNewestConfigOfTerm, TypeOK, vars
    <1>6. ActiveConfigsOverlap' BY DEF Ind, ActiveConfigsOverlap, TypeOK, vars
    <1>7. ActiveConfigsSafeAtTerms' BY DEF Ind, ActiveConfigsSafeAtTerms, TypeOK, vars
    <1>8. LogMatching' BY DEF Ind, LogMatching, TypeOK, vars
    <1>9. TermsOfEntriesGrowMonotonically' BY DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK, vars
    <1>10. PrimaryHasEntriesItCreated' BY DEF Ind, PrimaryHasEntriesItCreated, InLog, TypeOK, vars
    <1>11. CurrentTermAtLeastAsLargeAsLogTermsForPrimary' BY DEF Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, TypeOK, vars
    <1>12. LogEntryInTermImpliesConfigInTerm' BY DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK, vars
    <1>13. UniformLogEntriesInTerm' BY DEF Ind, UniformLogEntriesInTerm, TypeOK, vars
    <1>14. CommittedEntryIndexesAreNonZero' BY DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK, vars
    <1>15. CommittedTermMatchesEntry' BY DEF Ind, CommittedTermMatchesEntry, TypeOK, vars
    <1>16. LeaderCompleteness' BY DEF Ind, LeaderCompleteness, InLog, TypeOK, vars
    <1>17. LogsLaterThanCommittedMustHaveCommitted' BY DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK, vars
    <1>18. ActiveConfigsOverlapWithCommittedEntry' BY DEF Ind, ActiveConfigsOverlapWithCommittedEntry, InLog, TypeOK, vars
    <1>19. NewerConfigsDisablePrimaryCommitsInOlderTerms' BY DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK, vars
    <1>20. ConfigsNonempty' BY DEF Ind, ConfigsNonempty, InLog, TypeOK, vars
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12,
                <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20
          DEF Ind

LEMMA InitImpliesInd ==
ASSUME Init
PROVE Ind
PROOF
    <1>1. TypeOK 
        BY DEF Init, OSM!Init, CSM!Init, TypeOK
    <1>2. OnePrimaryPerTerm
        BY PrimaryAndSecondaryAreDifferent DEF Init, OSM!Init, CSM!Init, OnePrimaryPerTerm
    <1>3. PrimaryConfigTermEqualToCurrentTerm
        BY DEF Init, OSM!Init, CSM!Init, PrimaryConfigTermEqualToCurrentTerm
    <1>4. ConfigVersionAndTermUnique
        BY DEF Init, OSM!Init, CSM!Init, ConfigVersionAndTermUnique
    <1>5. PrimaryInTermContainsNewestConfigOfTerm
        BY DEF Init, OSM!Init, CSM!Init, PrimaryInTermContainsNewestConfigOfTerm
    <1>6. ActiveConfigsOverlap
        BY ConfigQuorumsOverlap DEF Init, OSM!Init, CSM!Init, ActiveConfigsOverlap,
                QuorumsOverlap, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, Quorums, CV
    <1>7. ActiveConfigsSafeAtTerms
        BY QuorumsAreNonEmpty DEF Init, OSM!Init, CSM!Init, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, Quorums, CV
    <1>8. LogMatching
        BY DEF Init, OSM!Init, CSM!Init, LogMatching
    <1>9. TermsOfEntriesGrowMonotonically
        BY DEF Init, OSM!Init, CSM!Init, TermsOfEntriesGrowMonotonically
    <1>10. PrimaryHasEntriesItCreated
        BY DEF Init, OSM!Init, CSM!Init, PrimaryHasEntriesItCreated
    <1>11. CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        BY DEF Init, OSM!Init, CSM!Init, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>12. LogEntryInTermImpliesConfigInTerm
        BY DEF Init, OSM!Init, CSM!Init, LogEntryInTermImpliesConfigInTerm
    <1>13. UniformLogEntriesInTerm
        BY DEF Init, OSM!Init, CSM!Init, UniformLogEntriesInTerm
    <1>14. CommittedEntryIndexesAreNonZero
        BY DEF Init, OSM!Init, CSM!Init, CommittedEntryIndexesAreNonZero
    <1>15. CommittedTermMatchesEntry
        BY DEF Init, OSM!Init, CSM!Init, CommittedTermMatchesEntry
    <1>16. LeaderCompleteness
        BY DEF Init, OSM!Init, CSM!Init, LeaderCompleteness
    <1>17. LogsLaterThanCommittedMustHaveCommitted
        BY DEF Init, OSM!Init, CSM!Init, LogsLaterThanCommittedMustHaveCommitted
    <1>18. ActiveConfigsOverlapWithCommittedEntry
        BY DEF Init, OSM!Init, CSM!Init, ActiveConfigsOverlapWithCommittedEntry, InLog
    <1>19. NewerConfigsDisablePrimaryCommitsInOlderTerms
        BY DEF Init, OSM!Init, CSM!Init, NewerConfigsDisablePrimaryCommitsInOlderTerms
    <1>20. ConfigsNonempty
        BY DEF Init, OSM!Init, CSM!Init, ConfigsNonempty
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
                <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20
          DEF Ind

THEOREM IndIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => Ind
      /\ (Ind /\ [Next]_vars) => Ind'
PROOF BY InitImpliesTypeOK, InitImpliesInd, IndAndNext, IndAndUnchanged


\*
\* Establishing the safety properties of MongoRaftReconfig.
\*

MRRSpec == /\ TypeOK
           /\ Init
           /\ [][Next]_vars

LEMMA MRRImpliesInd ==
ASSUME TRUE
PROVE MRRSpec => []Ind
BY IndIsInductiveInvariant, PTL DEF MRRSpec

THEOREM MRRImpliesLeaderCompleteness ==
ASSUME TRUE
PROVE MRRSpec => []LeaderCompleteness
BY MRRImpliesInd, PTL DEF Ind

THEOREM MRRImpliesStateMachineSafety ==
ASSUME TRUE
PROVE MRRSpec => []StateMachineSafety
BY MRRImpliesInd, IndImpliesStateMachineSafety, PTL

=============================================================================
