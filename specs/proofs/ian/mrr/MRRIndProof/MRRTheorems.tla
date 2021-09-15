----------------------------- MODULE MRRTheorems -----------------------------

EXTENDS MongoRaftReconfig, Defs, IndProof, Axioms, TypeOK, ElectionSafetyLemmas, LogPropertiesLemmas,
        LeaderCompletenessLemmas, LeaderCompletenessLemmasCtd, Lib

MRRSpec == /\ TypeOK
           /\ Init
           /\ [][Next]_vars

LeaderCompleteness2 ==
    \A s \in Server :
        (state[s] = Primary) => (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

StateMachineSafety2 ==
    \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)

LEMMA MRRImpliesInd ==
ASSUME TRUE
PROVE MRRSpec => [](TypeOK /\ Ind)
BY IndIsInductiveInvariant, PTL DEF MRRSpec

LEMMA MRRImpliesLeaderCompletenessGeneralized ==
ASSUME TRUE
PROVE MRRSpec => []LeaderCompletenessGeneralized
BY MRRImpliesInd, PTL DEF Ind

THEOREM MRRImpliesLeaderCompleteness ==
ASSUME TRUE
PROVE MRRSpec => []LeaderCompleteness2
BY MRRImpliesLeaderCompletenessGeneralized DEF LeaderCompleteness2, LeaderCompletenessGeneralized, InLog, TypeOK

LEMMA ServerHasLargestConfig ==
ASSUME TypeOK, Ind
PROVE \E s \in Server : \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))

LEMMA ServerSubsetsHaveLargestConfig ==
ASSUME TypeOK, Ind,
       NEW conf \in SUBSET Server,
       conf # {}
PROVE \E s \in conf : \A t \in conf : CSM!NewerOrEqualConfig(CV(s), CV(t))

LEMMA ActiveConfigSetNonempty2 ==
ASSUME TypeOK, Ind
PROVE ActiveConfigSet # {}
PROOF
    <1>1. SUFFICES ASSUME \A s \in Server : ConfigDisabled(s)
                   PROVE FALSE BY DEF ActiveConfigSet
    <1>2. \A s \in Server : \A Q \in Quorums(config[s]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(s)) BY <1>1 DEF ConfigDisabled
    <1>3. \A s \in Server : Quorums(config[s]) # {}
        <2>.  TAKE s \in Server
        <2>1. config[s] # {} BY DEF Ind, ConfigsNonempty
        <2>2. IsFiniteSet(config[s]) BY FS_Subset, ServerIsFinite DEF TypeOK
        <2>. QED BY <2>1, <2>2, QuorumsExistForNonEmptySets
    <1>. QED BY <1>2, <1>3, ServerHasLargestConfig, NewerIsNotSymmetric DEF Quorums, TypeOK
                   
    \*<1>2. PICK s \in Server : ConfigDisabled(s) BY <1>1, ServerIsNonempty
    \*<1>3. \A Q \in Quorums(config[s]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(s)) BY <1>2 DEF ConfigDisabled
    \*<1>4. \A Q \in Quorums(config[s]) : (Q \in SUBSET Server /\ Q # {}) BY <1>3 DEF Quorums, TypeOK
    \*<1>4. \A Q \in Quorums(config[s]) : \E n \in Q : n # s BY <1>3 DEF CSM!NewerConfig, CV, TypeOK
    
    (*<1>5. Quorums(config[s]) # {}
        <2>1. config[s] # {} BY <1>4, ServerIsNonempty DEF Quorums, TypeOK
        <2>2. IsFiniteSet(config[s]) BY FS_Subset, ServerIsFinite DEF TypeOK
        <2>. QED BY <2>1, <2>2, QuorumsExistForNonEmptySets
    <1>6. \E n \in Server : CSM!NewerConfig(CV(n), CV(s)) BY <1>3, <1>4, <1>5 DEF Quorums, TypeOK
    <1>. QED*)

(*

LEMMA ActiveConfigSetNonempty2 ==
ASSUME TypeOK, Ind
PROVE ActiveConfigSet # {}
PROOF
    <1>1. SUFFICES ASSUME \A s \in Server : ConfigDisabled(s)
                   PROVE FALSE BY DEF ActiveConfigSet
    <1>2. PICK s \in Server : ConfigDisabled(s) BY <1>1, ServerIsNonempty
    <1>3. \A Q \in Quorums(config[s]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(s)) BY <1>2 DEF ConfigDisabled
    <1>4. \A Q \in Quorums(config[s]) : (Q \in SUBSET Server /\ Q # {}) BY <1>3 DEF Quorums, TypeOK
    <1>5. \A Q \in Quorums(config[s]) : \E t \in Q : \A n \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))
    <1>. QED*)

LEMMA CommitsAreLogEntries ==
ASSUME TypeOK, Ind
PROVE \A c \in committed : \E s \in Server : InLog(c.entry, s)
BY DEF Ind, ActiveConfigSetNonempty, ActiveConfigsOverlapWithCommittedEntry, Quorums,
    ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA IndImpliesStateMachineSafety ==
ASSUME TypeOK, Ind
PROVE StateMachineSafety2
PROOF
    <1>1. SUFFICES ASSUME TRUE
          PROVE \A c1, c2 \in committed : (c1.entry[1] = c2.entry[1]) => (c1 = c2)
          BY DEF StateMachineSafety2
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

THEOREM MRRImpliesStateMachineSafety ==
ASSUME TRUE
PROVE MRRSpec => []StateMachineSafety2
BY MRRImpliesInd, IndImpliesStateMachineSafety, PTL

(*PROOF
    <1>1. Init => Ind BY IndIsInductiveInvariant
    <1>2. Ind /\ TypeOK /\ [Next]_vars => (TypeOK /\ Ind)' BY IndIsInductiveInvariant
    <1>3. Ind => LeaderCompletenessGeneralized BY DEF Ind
    <1>. QED BY <1>1, <1>2, <1>3, PTL DEF MRRSpec*)

=============================================================================
