---- MODULE StateMachineSafetyLemmas ----
EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib

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
ASSUME Ind
PROVE \E s \in Server : \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))
PROOF
    <1>ok. TypeOK BY DEF Ind
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
                    <4>1. CSM!NewerConfig(CV(x), CV(s)) BY <1>ok, <1>2, <3>3, NewerIsNotSymmetric
                    <4>2. \A t \in T : CSM!NewerOrEqualConfig(CV(x), CV(t))
                        BY <1>ok, <1>2, <3>1, <4>1, NewerConfigTransitivity, NewerConfigImpliesNewerOrEqual
                    <4>3. CSM!NewerOrEqualConfig(CV(x), CV(x)) BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
                    <4>. QED BY <4>2, <4>3 DEF P
                <3>. QED BY <3>2, <3>3, NewerIsNotSymmetric
            <2>. QED BY <2>1, <2>2
    <1>3. P(Server) BY <1>1, <1>2, ServerIsFinite, FS_InductionInServer, Isa
    <1>. QED BY <1>3, ServerIsNonempty DEF P

LEMMA ActiveConfigSetNonempty ==
ASSUME Ind
PROVE ActiveConfigSet # {}
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. SUFFICES ASSUME \A s \in Server : ConfigDisabled(s)
                   PROVE FALSE BY DEF ActiveConfigSet
    <1>2. \A s \in Server : \A Q \in Quorums(config[s]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(s))
        BY <1>1 DEF ConfigDisabled
    <1>3. \A s \in Server : Quorums(config[s]) # {}
        <2>.  TAKE s \in Server
        <2>1. config[s] # {} BY DEF Ind, ConfigsNonempty
        <2>2. IsFiniteSet(config[s]) BY <1>ok, FS_Subset, ServerIsFinite DEF TypeOK
        <2>. QED BY <2>1, <2>2, QuorumsExistForNonEmptySets
    <1>. QED BY <1>ok, <1>2, <1>3, ServerHasLargestConfig, NewerIsNotSymmetric DEF Quorums, TypeOK

LEMMA CommitsAreLogEntries ==
ASSUME Ind
PROVE \A c \in committed : \E s \in Server : InLog(c.entry, s)
BY ActiveConfigSetNonempty DEF Ind, ActiveConfigsOverlapWithCommittedEntry, Quorums,
    ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA IndImpliesStateMachineSafety ==
ASSUME Ind
PROVE StateMachineSafety
PROOF
    <1>ok. TypeOK BY DEF Ind
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
        <2>4. c1 = c2 BY <1>ok, <2>1, <2>2, <2>3, Z3 DEF TypeOK
        <2>. QED BY <1>3, <2>4
    <1>5. PICK s1 \in Server : InLog(c1.entry, s1) BY CommitsAreLogEntries
    <1>6. PICK s2 \in Server : InLog(c2.entry, s2) BY CommitsAreLogEntries
    <1>7. log[s1][c1.entry[1]] = c1.term BY <1>5 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
    <1>8. log[s2][c2.entry[1]] = c2.term BY <1>6 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
    <1>9. CASE c1.term > c2.term
        <2>1. \E i \in DOMAIN log[s1] : log[s1][i] = c1.term BY <1>5 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. \E i \in DOMAIN log[s1] : log[s1][i] > c2.term BY <1>9, <2>1 DEF TypeOK
        <2>3. Len(log[s1]) >= c2.entry[1] /\ log[s1][c2.entry[1]] = c2.term
            <3>1. c2.term <= c2.term BY DEF Ind, TypeOK
            <3>. QED BY <1>5, <2>2, <3>1 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>4. log[s1][c1.entry[1]] = c2.term BY <1>3, <2>3 DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>. QED BY <1>4, <1>7, <2>4 DEF TypeOK
    <1>10. CASE c1.term < c2.term
        <2>1. \E i \in DOMAIN log[s2] : log[s2][i] = c2.term BY <1>6 DEF Ind, CommittedTermMatchesEntry, InLog, TypeOK
        <2>2. \E i \in DOMAIN log[s2] : log[s2][i] > c1.term BY <1>10, <2>1 DEF TypeOK
        <2>3. Len(log[s2]) >= c1.entry[1] /\ log[s2][c1.entry[1]] = c1.term
            <3>1. c1.term <= c1.term BY DEF Ind, TypeOK
            <3>. QED BY <1>6, <2>2, <3>1 DEF Ind, LogsLaterThanCommittedMustHaveCommitted, TypeOK
        <2>4. log[s2][c2.entry[1]] = c1.term BY <1>3, <2>3 DEF Ind, CommittedEntryIndexesAreNonZero, TypeOK
        <2>. QED BY <1>4, <1>8, <2>4 DEF TypeOK
    <1>. QED BY <1>4, <1>9, <1>10 DEF Ind, TypeOK
====