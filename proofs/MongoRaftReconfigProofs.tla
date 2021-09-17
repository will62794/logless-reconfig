----------------------------- MODULE MongoRaftReconfigProofs -----------------------------
\*
\* This module contains the top level statement of the theorems that establish the safety
\* properties of MongoRaftReconfig. Many of the detailed lemmas and proofs for
\* proving these theorems are delegated to auxiliary modules, which are imported by this
\* module.
\*

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Axioms, TypeOK, ElectionSafetyLemmas, LogLemmas,
        LeaderCompletenessLemmas, Lib, AuxLemmas

\*
\* Establishing the inductive invariant.
\*

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
    <1>15. LeaderCompleteness' BY LeaderCompletenessAndNext
    <1>16. LogsLaterThanCommittedMustHaveCommitted' BY LogsLaterThanCommittedMustHaveCommittedAndNext
    <1>17. ActiveConfigsOverlapWithCommittedEntry' BY ActiveConfigsOverlapWithCommittedEntryAndNext
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms' BY NewerConfigsDisablePrimaryCommitsInOlderTermsAndNext
    <1>19. ConfigsNonempty' BY ConfigsNonemptyAndNext
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
                <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19
          DEF Ind

LEMMA IndAndUnchanged ==
ASSUME TypeOK, Ind, UNCHANGED vars
PROVE (TypeOK /\ Ind)'
PROOF
    <1>.  USE DEF ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
    <1>1. OnePrimaryPerTerm' BY DEF Ind, OnePrimaryPerTerm, TypeOK, vars
    <1>2. PrimaryConfigTermEqualToCurrentTerm' BY DEF Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK, vars
    <1>3. ConfigVersionAndTermUnique' BY DEF Ind, ConfigVersionAndTermUnique, TypeOK, vars
    <1>4. PrimaryInTermContainsNewestConfigOfTerm' BY DEF Ind, PrimaryInTermContainsNewestConfigOfTerm, TypeOK, vars
    <1>5. ActiveConfigsOverlap' BY DEF Ind, ActiveConfigsOverlap, TypeOK, vars
    <1>6. ActiveConfigsSafeAtTerms' BY DEF Ind, ActiveConfigsSafeAtTerms, TypeOK, vars
    <1>7. LogMatching' BY DEF Ind, LogMatching, TypeOK, vars
    <1>8. TermsOfEntriesGrowMonotonically' BY DEF Ind, TermsOfEntriesGrowMonotonically, TypeOK, vars
    <1>9. PrimaryHasEntriesItCreated' BY DEF Ind, PrimaryHasEntriesItCreated, InLog, TypeOK, vars
    <1>10. CurrentTermAtLeastAsLargeAsLogTermsForPrimary' BY DEF Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, TypeOK, vars
    <1>11. LogEntryInTermImpliesConfigInTerm' BY DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK, vars
    <1>12. UniformLogEntriesInTerm' BY DEF Ind, UniformLogEntriesInTerm, TypeOK, vars
    <1>13. CommittedEntryIndexesAreNonZero' BY DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK, vars
    <1>14. CommittedTermMatchesEntry' BY DEF Ind, CommittedTermMatchesEntry, TypeOK, vars
    <1>15. LeaderCompleteness' BY DEF Ind, LeaderCompleteness, InLog, TypeOK, vars
    <1>16. LogsLaterThanCommittedMustHaveCommitted' BY DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK, vars
    <1>17. ActiveConfigsOverlapWithCommittedEntry' BY DEF Ind, ActiveConfigsOverlapWithCommittedEntry, InLog, TypeOK, vars
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms' BY DEF Ind, NewerConfigsDisablePrimaryCommitsInOlderTerms, TypeOK, vars
    <1>19. ConfigsNonempty' BY DEF Ind, ConfigsNonempty, InLog, TypeOK, vars
    <1>20. TypeOK' BY DEF TypeOK, vars
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11,
                <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20
          DEF Ind

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
    <1>15. LeaderCompleteness
        BY DEF Init, OSM!Init, CSM!Init, LeaderCompleteness
    <1>16. LogsLaterThanCommittedMustHaveCommitted
        BY DEF Init, OSM!Init, CSM!Init, LogsLaterThanCommittedMustHaveCommitted
    <1>17. ActiveConfigsOverlapWithCommittedEntry
        BY DEF Init, OSM!Init, CSM!Init, ActiveConfigsOverlapWithCommittedEntry, InLog
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms
        BY DEF Init, OSM!Init, CSM!Init, NewerConfigsDisablePrimaryCommitsInOlderTerms
    <1>19. ConfigsNonempty
        BY DEF Init, OSM!Init, CSM!Init, ConfigsNonempty
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10,
                <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19
          DEF Ind

THEOREM IndIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => Ind
      /\ (TypeOK /\ Ind /\ [Next]_vars) => (TypeOK /\ Ind)'
PROOF BY InitImpliesTypeOK, InitImpliesInd, TypeOKAndNext, IndAndNext, IndAndUnchanged


\*
\* Establishing the safety properties of MongoRaftReconfig.
\*

MRRSpec == /\ TypeOK
           /\ Init
           /\ [][Next]_vars

LEMMA FS_InductionInServer == 
  ASSUME NEW S, IsFiniteSet(S), S \in SUBSET Server,
         NEW P(_), P({}),
         ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T,
         x \in Server, T \in SUBSET Server
         PROVE  P(T \cup {x})
  PROVE  P(S)
<1>.  DEFINE Q(n) == \A T : T \in SUBSET Server /\ IsFiniteSet(T) /\ Cardinality(T) = n => P(T)
<1>1. SUFFICES \A n \in Nat : Q(n)  BY FS_CardinalityType
<1>2. Q(0)  BY FS_EmptySet, Zenon
<1>3. ASSUME NEW n \in Nat, Q(n),
             NEW T, IsFiniteSet(T), Cardinality(T) = n+1,
             T \in SUBSET Server
      PROVE  P(T)
  <2>1. PICK x \in T : x \in Server  BY <1>3, FS_EmptySet
  <2>2. /\ IsFiniteSet(T \ {x})
        /\ Cardinality(T \ {x}) = n
    BY <1>3, FS_RemoveElement, Isa
  <2>3. P(T \ {x})  BY <1>3, <2>1, <2>2, Q(n)
  <2>4. P((T \ {x}) \cup {x})
    <3>1. T \in SUBSET Server BY <1>3
    <3>2. T = ((T \ {x}) \cup {x}) OBVIOUS
    <3>. QED BY <2>2, <2>3, Zenon, <3>1, <3>2
  <2>. QED  BY <2>4, Zenon
<1>4. QED  BY <1>2, <1>3, NatInduction, Isa

LEMMA NewerConfigImpliesNewerOrEqual ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       CSM!NewerConfig(CV(s), CV(t))
PROVE CSM!NewerOrEqualConfig(CV(s), CV(t))
BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA ServerHasLargestConfig ==
ASSUME TypeOK, Ind
PROVE \E s \in Server : \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))
PROOF
    <1>.  DEFINE P(S) == \/ S = {}
                         \/ \E s \in S : \A t \in S : CSM!NewerOrEqualConfig(CV(s), CV(t))
    <1>.  HIDE DEF P
    <1>1. P({}) BY DEF P
    <1>2. ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T, x \in Server, T \in SUBSET Server
          PROVE P(T \cup {x})
            <2>1. CASE T = {} BY <2>1 DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK, P
            <2>2. CASE T # {}
                <3>1. PICK s \in T : \A t \in T : CSM!NewerOrEqualConfig(CV(s), CV(t)) BY <1>2, <2>2 DEF P
                <3>2. CASE CSM!NewerOrEqualConfig(CV(s), CV(x)) BY <3>1, <3>2, NewerOrEqualConfigTransitivity DEF P
                <3>3. CASE ~CSM!NewerOrEqualConfig(CV(s), CV(x))
                    <4>1. CSM!NewerConfig(CV(x), CV(s)) BY <1>2, <3>3, NewerIsNotSymmetric
                    <4>2. \A t \in T : CSM!NewerOrEqualConfig(CV(x), CV(t))
                        BY <1>2, <3>1, <4>1, NewerConfigTransitivity, NewerConfigImpliesNewerOrEqual
                    <4>3. CSM!NewerOrEqualConfig(CV(x), CV(x)) BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
                    <4>. QED BY <4>2, <4>3 DEF P
                <3>. QED BY <3>2, <3>3, NewerIsNotSymmetric
            <2>. QED BY <2>1, <2>2
    <1>3. P(Server) BY <1>1, <1>2, ServerIsFinite, FS_InductionInServer, Isa
    <1>. QED BY <1>3, ServerIsNonempty DEF P

LEMMA ActiveConfigSetNonempty ==
ASSUME TypeOK, Ind
PROVE ActiveConfigSet # {}
PROOF
    <1>1. SUFFICES ASSUME \A s \in Server : ConfigDisabled(s)
                   PROVE FALSE BY DEF ActiveConfigSet
    <1>2. \A s \in Server : \A Q \in Quorums(config[s]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(s))
        BY <1>1 DEF ConfigDisabled
    <1>3. \A s \in Server : Quorums(config[s]) # {}
        <2>.  TAKE s \in Server
        <2>1. config[s] # {} BY DEF Ind, ConfigsNonempty
        <2>2. IsFiniteSet(config[s]) BY FS_Subset, ServerIsFinite DEF TypeOK
        <2>. QED BY <2>1, <2>2, QuorumsExistForNonEmptySets
    <1>. QED BY <1>2, <1>3, ServerHasLargestConfig, NewerIsNotSymmetric DEF Quorums, TypeOK

LEMMA CommitsAreLogEntries ==
ASSUME TypeOK, Ind
PROVE \A c \in committed : \E s \in Server : InLog(c.entry, s)
BY ActiveConfigSetNonempty DEF Ind, ActiveConfigsOverlapWithCommittedEntry, Quorums,
    ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA IndImpliesStateMachineSafety ==
ASSUME TypeOK, Ind
PROVE StateMachineSafety
PROOF
    <1>1. SUFFICES ASSUME TRUE
          PROVE \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)
          BY DEF StateMachineSafety
    <1>2. TAKE c1, c2 \in committed
    <1>3. SUFFICES ASSUME c1.entry[1] = c2.entry[1], c1 # c2
          PROVE FALSE OBVIOUS
    <1>4. c1.term # c2.term
        <2>1. SUFFICES ASSUME c1.term = c2.term
              PROVE FALSE OBVIOUS
        <2>2. c1.entry[2] = c2.entry[2] BY <2>1 DEF Ind, CommittedTermMatchesEntry
        <2>3. c1.entry[1] = c2.entry[1] BY <1>3
        <2>4. c1 = c2 BY <2>1, <2>2, <2>3, Z3 DEF TypeOK
        <2>. QED BY <1>3, <2>4
    <1>5. PICK s1 \in Server : InLog(c1.entry, s1) BY CommitsAreLogEntries
    <1>6. PICK s2 \in Server : InLog(c2.entry, s2) BY CommitsAreLogEntries
    <1>7. log[s1][c1.entry[1]] = c1.term BY <1>5 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
    <1>8. log[s2][c2.entry[1]] = c2.term BY <1>6 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
    <1>9. CASE c1.term > c2.term
        <2>1. \E i \in DOMAIN log[s1] : log[s1][i] = c1.term BY <1>5 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. \E i \in DOMAIN log[s1] : log[s1][i] > c2.term BY <1>9, <2>1 DEF TypeOK
        <2>3. Len(log[s1]) >= c2.entry[1] /\ log[s1][c2.entry[1]] = c2.term
            <3>1. c2.term <= c2.term BY DEF TypeOK
            <3>. QED BY <1>5, <2>2, <3>1 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>4. log[s1][c1.entry[1]] = c2.term BY <1>3, <2>3 DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>. QED BY <1>4, <1>7, <2>4 DEF TypeOK
    <1>10. CASE c1.term < c2.term
        <2>1. \E i \in DOMAIN log[s2] : log[s2][i] = c2.term BY <1>6 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. \E i \in DOMAIN log[s2] : log[s2][i] > c1.term BY <1>10, <2>1 DEF TypeOK
        <2>3. Len(log[s2]) >= c1.entry[1] /\ log[s2][c1.entry[1]] = c1.term
            <3>1. c1.term <= c1.term BY DEF TypeOK
            <3>. QED BY <1>6, <2>2, <3>1 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>4. log[s2][c2.entry[1]] = c1.term BY <1>3, <2>3 DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>. QED BY <1>4, <1>8, <2>4 DEF TypeOK
    <1>. QED BY <1>4, <1>9, <1>10 DEF TypeOK

\*
\* The main theorems establishing the high level safety properties of MongoRaftReconfig.
\*

LEMMA MRRImpliesInd ==
ASSUME TRUE
PROVE MRRSpec => [](TypeOK /\ Ind)
BY IndIsInductiveInvariant, PTL DEF MRRSpec

LEMMA MRRImpliesLeaderCompleteness ==
ASSUME TRUE
PROVE MRRSpec => []LeaderCompleteness
BY MRRImpliesInd, PTL DEF Ind

THEOREM MRRImpliesStateMachineSafety ==
ASSUME TRUE
PROVE MRRSpec => []StateMachineSafety
BY MRRImpliesInd, IndImpliesStateMachineSafety, PTL

-----------------------------------------------------------------------------

\*
\* Refinement proof of MongoRaftReconfig => MongoLoglessDynamicRaft.
\*
\* This proof is sufficient to establish that any properties of MongoLoglessDynamicRaft 
\* hold when operating as a subprotocol of MongoRaftReconfig.
\*

\* Create an instance of MongoLoglessDynamicRaft that uses a subset of the 
\* variables of MongoRaftReconfig.
IMLDR == INSTANCE MongoLoglessDynamicRaft WITH 
            currentTerm <- currentTerm,
            state <- state,
            configVersion <- configVersion,
            configTerm <- configTerm,
            config <- config


\* Prove that any step of MongoRaftReconfig is a valid step of MongoLoglessDynamicRaft. 
THEOREM MRRNextRefinesMLDRNext == [Next]_vars => [IMLDR!Next]_IMLDR!vars
    <1>a. SUFFICES ASSUME [Next]_vars PROVE [IMLDR!Next]_IMLDR!vars
            OBVIOUS
    <1>b. [IMLDR!Next]_IMLDR!vars
        <2>   USE DEF IMLDR!Next, IMLDR!vars
        <2>1. CASE (OSMNext /\ UNCHANGED csmVars)
            <3>1. CASE \E s \in Server : OSM!ClientRequest(s) /\ UNCHANGED csmVars 
                BY <3>1 DEF OSM!ClientRequest, csmVars
            <3>2. CASE \E s, t \in Server : OSM!GetEntries(s, t) /\ UNCHANGED csmVars
                BY <3>2 DEF OSM!GetEntries, csmVars
            <3>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t) /\ UNCHANGED csmVars
                BY <3>3 DEF OSM!RollbackEntries, csmVars
            <3>4. CASE \E s \in Server :  \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q) /\ UNCHANGED csmVars
                BY <3>4 DEF OSM!CommitEntry, csmVars
            <3>5. QED BY <2>1,<3>1,<3>2,<3>3,<3>4 DEF OSMNext
        <2>2. CASE CSMNext /\ UNCHANGED osmVars
            <3>1. CASE \E s \in Server, newConfig \in SUBSET Server : 
                    OplogCommitment(s) /\ CSM!Reconfig(s, newConfig) /\ UNCHANGED osmVars
                    BY <3>1 
                    DEF CSM!Reconfig, IMLDR!Reconfig, CSM!ConfigQuorumCheck, CSM!TermQuorumCheck, CSM!QuorumsOverlap,
                        IMLDR!ConfigQuorumCheck, IMLDR!TermQuorumCheck, IMLDR!QuorumsOverlap, CSM!Quorums, IMLDR!Quorums, 
                        Quorums, IMLDR!QuorumsAt, CSM!QuorumsAt, IsCommitted, osmVars, CSM!Cardinality, IMLDR!Cardinality
            <3>2. CASE \E s,t \in Server : CSM!SendConfig(s, t) /\ UNCHANGED osmVars
                    BY <3>2 DEF CSM!SendConfig, IMLDR!SendConfig, IMLDR!IsNewerConfig, CSM!IsNewerConfig                    
            <3>3. QED BY <2>2,<3>2,<3>1 DEF CSMNext, osmVars
        <2>3. CASE JointNext 
            <3>1. CASE \E i \in Server : \E Q \in Quorums(config[i]) : 
                            /\ OSM!BecomeLeader(i, Q)
                            /\ CSM!BecomeLeader(i, Q)
                    BY <3>1 
                    DEF CSM!BecomeLeader, IMLDR!BecomeLeader, CSM!CanVoteForConfig,
                        OSM!CanVoteForOplog, IMLDR!CanVoteForConfig,IMLDR!IsNewerOrEqualConfig,
                        CSM!IsNewerOrEqualConfig, IMLDR!IsNewerConfig, CSM!IsNewerConfig, OSM!LastTerm, Quorums, IMLDR!Quorums, 
                        IMLDR!Cardinality, Cardinality
            <3>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
                BY <3>2 DEF OSM!UpdateTerms, CSM!UpdateTerms,
                            IMLDR!UpdateTerms,
                            IMLDR!UpdateTermsExpr,
                            OSM!UpdateTermsExpr, CSM!UpdateTermsExpr     
            <3>3. QED BY <2>3, <3>1, <3>2 DEF JointNext 
        <2>4. CASE UNCHANGED vars BY <2>4 DEF vars, IMLDR!vars
        <2>5. QED BY <1>a,<2>1, <2>2,<2>3,<2>4 DEF Next
    <1>c. QED BY <1>b, <1>a


\* MongoRaftReconfig => MongoLoglessDynamicRaft
THEOREM MRRRefinesMLDR == Spec => IMLDR!Spec
    <1>1. Init => IMLDR!Init 
        BY DEF Init, OSM!Init, CSM!Init, IMLDR!Init
    <1>2. [Next]_vars => [IMLDR!Next]_IMLDR!vars BY MRRNextRefinesMLDRNext
    <1>3. QED BY <1>1, <1>2, PTL DEF Spec, IMLDR!Spec


\* Note: See https://github.com/tlaplus/Examples/blob/9d7de44a8a37e415c8ba6e24d167632d53c24176/specifications/Paxos/Voting.tla#L179-L198
\* for one example of a refinement proof in TLAPS.


=============================================================================
