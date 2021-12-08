----------------------------- MODULE BasicQuorumsLib -----------------------------

EXTENDS SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS, MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions

LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorums(S) # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorums

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE Quorums(config[s]) \subseteq SUBSET Server
PROOF BY DEF Quorums, TypeOK

LEMMA StaticQuorumsOverlap ==
ASSUME NEW cfg \in SUBSET Server,
       NEW Q1 \in Quorums(cfg),
       NEW Q2 \in Quorums(cfg)
PROVE Q1 \cap Q2 # {}
PROOF
    <1>. IsFiniteSet(cfg)
        BY FS_Subset, ServerIsFinite
    <1>. IsFiniteSet(Q1) /\ IsFiniteSet(Q2)
        BY QuorumsAreServerSubsets, ServerIsFinite, FS_Subset DEF Quorums
    <1>. IsFiniteSet(Q1 \cap Q2)
        BY FS_Intersection
    <1>1. Q1 \in SUBSET cfg /\ Q2 \in SUBSET cfg
        BY QuorumsAreServerSubsets DEF Quorums, TypeOK
    <1>2. Cardinality(Q1) + Cardinality(Q2) <= Cardinality(cfg) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1 \cup Q2) = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
            BY FS_Union
        <2>2. Cardinality(Q1 \cup Q2) <= Cardinality(cfg)
            BY <1>1, FS_Subset, ServerIsFinite
        <2>3. QED BY <2>1, <2>2, FS_CardinalityType
    <1>3. Cardinality(Q1) + Cardinality(Q2) < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1) * 2 > Cardinality(cfg) /\ Cardinality(Q2) * 2 > Cardinality(cfg)
            BY <1>1 DEF Quorums, TypeOK
        <2>2. Cardinality(Q1) + Cardinality(Q2) > Cardinality(cfg)
            BY <2>1, FS_CardinalityType, ServerIsFinite
        <2>3. QED BY <2>2, <1>2, FS_CardinalityType
    <1>4. Cardinality(Q1 \cap Q2) > 0
        BY <1>3, FS_CardinalityType
    <1>5. QED BY <1>4, FS_EmptySet

COROLLARY ConfigQuorumsOverlap ==
ASSUME NEW cfg \in SUBSET Server
PROVE QuorumsOverlap(cfg, cfg)
PROOF BY StaticQuorumsOverlap DEF QuorumsOverlap

LEMMA QuorumsAreNonEmpty ==
ASSUME \/ config \in [Server -> SUBSET Server]
       \/ TypeOK,
       NEW s \in Server
PROVE \A Q \in Quorums(config[s]) : Q # {}
PROOF
    <1>. config \in [Server -> SUBSET Server] BY DEF TypeOK
    <1>. SUFFICES ASSUME \E Q \in Quorums(config[s]) : Q = {}
         PROVE FALSE OBVIOUS
    <1>. PICK Q \in Quorums(config[s]) : Q = {} OBVIOUS
    <1>1. Cardinality(Q) * 2 = 0
        <2>1. Cardinality(Q) = 0 BY FS_EmptySet
        <2>. QED BY <2>1, FS_CardinalityType
    <1>2. Cardinality(Q) * 2 > 0
        <2>1. Cardinality(config[s]) >= 0 /\ IsFiniteSet(config[s])
            BY ServerIsFinite, FS_CardinalityType, FS_Subset DEF Quorums
        <2>2. Cardinality(Q) * 2 > Cardinality(config[s]) BY <2>1, FS_CardinalityType DEF Quorums
        <2>3. IsFiniteSet(Q) BY ServerIsFinite, FS_Subset DEF Quorums
        <2>. QED BY <2>1, <2>2, <2>3, FS_CardinalityType
    <1>. QED BY <1>1, <1>2

=============================================================================
