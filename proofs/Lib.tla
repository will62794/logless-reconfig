----------------------------- MODULE Lib -----------------------------

EXTENDS SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS, MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK

LEMMA IsNewerOrEqualConfigTransitivity ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       CSM!IsNewerOrEqualConfig(s, t),
       CSM!IsNewerOrEqualConfig(t, u)
PROVE CSM!IsNewerOrEqualConfig(s, u)
PROOF BY DEF CSM!IsNewerOrEqualConfig, CSM!IsNewerConfig, TypeOK

LEMMA IsNewerConfigTransitivity ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       \/ CSM!IsNewerConfig(s, t) /\ CSM!IsNewerConfig(t, u)
       \/ CSM!IsNewerConfig(s, t) /\ CSM!IsNewerOrEqualConfig(t, u)
       \/ CSM!IsNewerOrEqualConfig(s, t) /\ CSM!IsNewerConfig(t, u)
PROVE CSM!IsNewerConfig(s, u)
PROOF BY DEF CSM!IsNewerOrEqualConfig, CSM!IsNewerConfig, TypeOK

LEMMA NewerOrEqualConfigTransitivity ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       CSM!NewerOrEqualConfig(CV(s), CV(t)),
       CSM!NewerOrEqualConfig(CV(t), CV(u))
PROVE CSM!NewerOrEqualConfig(CV(s), CV(u))
PROOF BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA NewerOrEqualConfigTransitivityAndNext ==
ASSUME TypeOK, Next,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       CSM!NewerOrEqualConfig(CV(s)', CV(t)'),
       CSM!NewerOrEqualConfig(CV(t)', CV(u))
PROVE CSM!NewerOrEqualConfig(CV(s)', CV(u))
PROOF BY TypeOKAndNext DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA NewerConfigTransitivity ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       \/ CSM!NewerConfig(CV(s), CV(t)) /\ CSM!NewerConfig(CV(t), CV(u))
       \/ CSM!NewerConfig(CV(s), CV(t)) /\ CSM!NewerOrEqualConfig(CV(t), CV(u))
       \/ CSM!NewerOrEqualConfig(CV(s), CV(t)) /\ CSM!NewerConfig(CV(t), CV(u))
PROVE CSM!NewerConfig(CV(s), CV(u))
PROOF BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA CVsFinite ==
ASSUME TypeOK
PROVE LET Op(x) == x \*configVersion[x]
          T == {Op(x) : x \in Server}
      IN  IsFiniteSet(T)
PROOF BY ServerIsFinite, FS_Image \*DEF TypeOK

LEMMA NewerConfigEquivalence ==
ASSUME NEW s \in Server,
       NEW t \in Server
PROVE CSM!IsNewerConfig(s, t) <=> CSM!NewerConfig(CV(s), CV(t))
BY DEF CSM!IsNewerConfig, CSM!NewerConfig, CV

LEMMA NewerOrEqualConfigEquivalence ==
ASSUME NEW s \in Server,
       NEW t \in Server
PROVE CSM!IsNewerOrEqualConfig(s, t) <=> CSM!NewerOrEqualConfig(CV(s), CV(t))
BY DEF CSM!IsNewerConfig, CSM!NewerConfig, CSM!IsNewerOrEqualConfig, CSM!NewerOrEqualConfig, CV

LEMMA NewerIsNotSymmetric ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server
PROVE /\ CSM!IsNewerConfig(s, t) <=> ~CSM!IsNewerOrEqualConfig(t, s)
      /\ CSM!NewerConfig(CV(s), CV(t)) <=> ~CSM!NewerOrEqualConfig(CV(t), CV(s))
BY DEF CSM!IsNewerConfig, CSM!IsNewerOrEqualConfig, CSM!NewerConfig, CSM!NewerOrEqualConfig, CV, TypeOK

LEMMA NewerIsNotSymmetricAndNext ==
ASSUME TypeOK, Next,
       NEW s \in Server,
       NEW t \in Server
PROVE /\ CSM!IsNewerConfig(s, t)' <=> ~CSM!IsNewerOrEqualConfig(t, s)'
      /\ CSM!NewerConfig(CV(s), CV(t))' <=> ~CSM!NewerOrEqualConfig(CV(t), CV(s))'
BY TypeOKAndNext DEF CSM!IsNewerConfig, CSM!IsNewerOrEqualConfig, CSM!NewerConfig, CSM!NewerOrEqualConfig, CV, TypeOK

LEMMA OlderIsNotSymmetric ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server
PROVE /\ CSM!IsNewerConfig(s, t) <=> OlderConfig(CV(t), CV(s))
      /\ CSM!NewerConfig(CV(s), CV(t)) <=> OlderConfig(CV(t), CV(s))
      /\ OlderConfig(CV(t), CV(s)) => CSM!IsNewerOrEqualConfig(s, t)
      /\ OlderConfig(CV(t), CV(s)) => CSM!NewerOrEqualConfig(CV(s), CV(t))
BY DEF OlderConfig, CSM!IsNewerConfig, CSM!IsNewerOrEqualConfig, CSM!NewerConfig, CSM!NewerOrEqualConfig, CV, TypeOK

LEMMA NewerIsNotReflexive ==
ASSUME TypeOK,
       NEW s \in Server
PROVE /\ ~CSM!IsNewerConfig(s, s)
      /\ ~CSM!NewerConfig(CV(s), CV(s))
BY DEF CSM!IsNewerConfig, CV, CSM!NewerConfig, TypeOK

LEMMA ReconfigImpliesConfigTermUnchanged ==
ASSUME Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE \A t \in Server : configTerm'[t] = configTerm[t]
PROOF
    <1>1. state[s] = Primary BY DEF CSM!Reconfig
    <1>2. configTerm[s] = currentTerm[s] BY <1>1 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
    <1>. QED BY <1>2 DEF CSM!Reconfig, Ind, TypeOK

LEMMA ReconfigImpliesNewerOrEqualConfig ==
ASSUME Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE /\ CSM!NewerConfig(CV(s)', CV(s))
      /\ \A t \in Server : t # s => CV(t)' = CV(t)
      /\ \A t \in Server : CSM!NewerOrEqualConfig(CV(t)', CV(t))
PROOF
    <1>1. CSM!NewerConfig(CV(s)', CV(s))
        <2>1. configVersion'[s] > configVersion[s] BY DEF CSM!Reconfig, Ind, TypeOK
        <2>. QED BY <2>1, ReconfigImpliesConfigTermUnchanged DEF CSM!NewerConfig, CV
    <1>2. \A t \in Server : t # s => CV(t)' = CV(t) BY DEF CSM!Reconfig, CV
    <1>3. \A t \in Server : CSM!NewerOrEqualConfig(CV(t)', CV(t)) BY <1>1, <1>2 DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
    <1>. QED BY <1>1, <1>2, <1>3

LEMMA SendConfigImpliesNewerOrEqualConfig ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       CSM!SendConfig(s, t)
PROVE /\ CSM!NewerConfig(CV(t)', CV(t))
      /\ \A u \in Server : u # t => CV(u)' = CV(u)
      /\ \A u \in Server : CSM!NewerOrEqualConfig(CV(u)', CV(u))
PROOF
    <1>1. CSM!NewerConfig(CV(t)', CV(t))
        <2>1. CSM!NewerConfig(CV(s), CV(t)) BY NewerConfigEquivalence DEF CSM!SendConfig, TypeOK
        <2>. QED BY <2>1 DEF CSM!SendConfig, CSM!NewerConfig, CV, TypeOK
    <1>2. \A u \in Server : u # t => CV(u)' = CV(u) BY DEF CSM!SendConfig, CV, TypeOK
    <1>3. \A u \in Server : CSM!NewerOrEqualConfig(CV(u)', CV(u)) BY <1>1, <1>2 DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3

LEMMA QuorumsOverlapIsCommutative ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> QuorumsOverlap(conf2,conf1)
PROOF
    <1>1. TAKE conf1, conf2 \in SUBSET Server
    <1>2. QuorumsOverlap(conf1,conf2) => QuorumsOverlap(conf2,conf1)
        <2>1. SUFFICES ASSUME QuorumsOverlap(conf1,conf2)
              PROVE QuorumsOverlap(conf2,conf1) OBVIOUS
        <2>2. \A qx \in Quorums(conf1), qy \in Quorums(conf2) : qx \cap qy # {} BY <2>1 DEF QuorumsOverlap
        <2>3. \A qy \in Quorums(conf2), qx \in Quorums(conf1) : qy \cap qx # {} BY <2>2
        <2>. QED BY <2>3 DEF QuorumsOverlap
    <1>3. QuorumsOverlap(conf2,conf1) => QuorumsOverlap(conf1,conf2)
        <2>1. SUFFICES ASSUME QuorumsOverlap(conf2,conf1)
              PROVE QuorumsOverlap(conf1,conf2) OBVIOUS
        <2>2. \A qx \in Quorums(conf2), qy \in Quorums(conf1) : qx \cap qy # {} BY <2>1 DEF QuorumsOverlap
        <2>3. \A qy \in Quorums(conf1), qx \in Quorums(conf2) : qy \cap qx # {} BY <2>2
        <2>. QED BY <2>3 DEF QuorumsOverlap
    <1>. QED BY <1>2, <1>3

LEMMA NewerOrEqualImpliesConfigTermGreaterThanOrEqual ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       CSM!NewerOrEqualConfig(CV(s), CV(t))
PROVE configTerm[s] >= configTerm[t]
PROOF BY DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK

LEMMA IsNewerOrEqualImpliesConfigTermGreaterThanOrEqual ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       CSM!IsNewerOrEqualConfig(s, t)
PROVE configTerm[s] >= configTerm[t]
PROOF BY DEF CSM!IsNewerOrEqualConfig, CSM!IsNewerConfig, TypeOK

LEMMA ElectedLeadersInActiveConfigSet ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       CSM!BecomeLeader(s, Q)
PROVE s \in ActiveConfigSet
PROOF
    <1>1. \A v \in Q : CSM!IsNewerOrEqualConfig(s, v) BY DEF CSM!BecomeLeader, CSM!CanVoteForConfig
    <1>2. \A v \in Q : CSM!NewerOrEqualConfig(CV(s), CV(v)) BY <1>1, NewerOrEqualConfigEquivalence DEF Quorums, TypeOK
    <1>3. \A v \in Q : ~CSM!NewerConfig(CV(v), CV(s)) BY <1>2, NewerIsNotSymmetric DEF Quorums, TypeOK
    <1>. QED BY <1>3 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK

LEMMA ElectedLeadersCurrentTermGreaterThanConfigTerms ==
ASSUME Ind,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       CSM!BecomeLeader(s, Q)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>. TAKE t \in Server
    <1>1. PICK n \in Q : currentTerm[n] >= configTerm[t] BY ElectedLeadersInActiveConfigSet DEF Ind, ActiveConfigsSafeAtTerms
    <1>2. currentTerm[s] >= currentTerm[n] BY <1>1 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, Ind, TypeOK
    <1>. QED BY <1>1, <1>2 DEF Quorums, Ind, TypeOK


LEMMA ReconfigImpliesInActiveConfigSet ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE s \in ActiveConfigSet
PROOF BY QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigQuorumCheck,
            ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK

LEMMA ReconfigImpliesCurrentTermGreaterThanConfigTerms ==
ASSUME Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>1. s \in ActiveConfigSet BY ReconfigImpliesInActiveConfigSet DEF Ind
    <1>2. TAKE t \in Server
    <1>3. PICK Q \in Quorums(config[s]) : \A n \in Q : currentTerm[n] = currentTerm[s]
        BY QuorumsIdentical DEF CSM!Reconfig, CSM!TermQuorumCheck, Ind
    <1>4. PICK n \in Q : currentTerm[n] >= configTerm[t] BY <1>1, <1>3 DEF Ind, ActiveConfigsSafeAtTerms
    <1>5. currentTerm[s] = currentTerm[n] BY <1>3
    <1>. QED BY <1>4, <1>5 DEF Quorums

COROLLARY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A n \in Server : configTerm[p] >= configTerm[n]
BY ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF CSM!Reconfig, Ind, PrimaryConfigTermEqualToCurrentTerm

LEMMA ReconfigImpliesSameActiveConfigSet ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A n \in ActiveConfigSet' : n \in ActiveConfigSet
    <4>ok. TypeOK BY DEF Ind
    <4>1. TAKE n \in ActiveConfigSet'
    <4>n. n \in Server BY <4>1 DEF ActiveConfigSet, ConfigDisabled, Quorums
    <4>2. PICK Q \in Quorums(config[n])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE n = p
        <5>1. \E nQ \in Quorums(config[n]) : \A q \in nQ : CV(n) = CV(q)
            BY <4>ok, QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigQuorumCheck, Quorums, CV
        <5>. QED BY <4>ok, <5>1 DEF ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, CSM!Reconfig, TypeOK
    <4>. CASE n # p
        <5>1. Q \in Quorums(config[n])
            <6>1. config[n] = config'[n] BY DEF CSM!Reconfig, TypeOK
            <6>. QED BY <4>2, <6>1 DEF Quorums
        <5>2. \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n))
            <6>1. p \notin Q
                <7>1. SUFFICES ASSUME p \in Q
                      PROVE FALSE OBVIOUS
                <7>2. currentTerm[p] >= configTerm[n] BY <4>n, ReconfigImpliesCurrentTermGreaterThanConfigTerms
                <7>3. configTerm[p] >= configTerm[n] BY <7>2 DEF CSM!Reconfig, Ind, PrimaryConfigTermEqualToCurrentTerm
                <7>. CASE configTerm[p] > configTerm[n]
                    <8>1. configTerm'[p] > configTerm'[n]
                        BY <4>n, <7>2 DEF CSM!Reconfig, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
                    <8>2. CSM!NewerConfig(CV(p), CV(n))' BY <4>n, <8>1 DEF CSM!Reconfig, CSM!NewerConfig, CV, TypeOK
                    <8>. QED BY <4>2, <7>1, <8>2
                <7>. CASE configTerm[p] = configTerm[n]
                    <8>1. configVersion[p] >= configVersion[n] BY <4>n DEF CSM!Reconfig, Ind, PrimaryInTermContainsNewestConfigOfTerm
                    <8>2. configVersion'[p] > configVersion'[n] BY <4>ok, <4>n, <8>1 DEF CSM!Reconfig, TypeOK
                    <8>3. CSM!NewerConfig(CV(p), CV(n))'
                        BY <4>n, <8>2 DEF CSM!Reconfig, CSM!NewerConfig, CV, Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK
                    <8>. QED BY <4>2, <7>1, <8>3
                <7>. QED BY <4>ok, <4>n, <7>3 DEF TypeOK
            <6>2. \A q \in Q : CV(q) = CV(q)' BY <4>2, <6>1 DEF CSM!Reconfig, CV, TypeOK
            <6>. QED BY <4>2, <6>2 DEF CSM!Reconfig, CSM!NewerConfig, CV
        <5>. QED BY <5>1, <5>2 DEF ActiveConfigSet, ConfigDisabled
    <4>. QED OBVIOUS

LEMMA NewerOrEqualConfigWithSameTermImpliesGreaterOrEqualVersion ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       CSM!NewerOrEqualConfig(CV(s), CV(t)),
       configTerm[s] = configTerm[t]
PROVE configVersion[s] >= configVersion[t]
PROOF
    <1>1. CASE CV(s) = CV(t) BY <1>1 DEF CSM!NewerOrEqualConfig, CV, TypeOK
    <1>2. CASE CV(s) # CV(t) BY <1>2 DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
    <1>. QED BY <1>1, <1>2

LEMMA ReconfigImpliesActiveConfigSetHaveSameConfig ==
ASSUME Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A s \in ActiveConfigSet' : config[s] = config[p]
PROOF
    <4>ok. TypeOK BY DEF Ind
    <4>. TAKE s \in ActiveConfigSet'
    <4>. s \in ActiveConfigSet BY ReconfigImpliesSameActiveConfigSet
    <4>. s \in Server BY DEF ActiveConfigSet, ConfigDisabled
    <4>1. PICK Q \in Quorums(config[s]) : \A n \in Q : ~CSM!NewerConfig(CV(n), CV(s)) BY DEF ActiveConfigSet, ConfigDisabled
    <4>2. PICK pQ \in Quorums(config[p]) : \A q \in pQ : CV(q) = CV(p)
        BY <4>ok, QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigQuorumCheck, CV, TypeOK
    <4>3. PICK q \in pQ : ~CSM!NewerConfig(CV(q), CV(s))
        BY <4>1, <4>2, ReconfigImpliesInActiveConfigSet DEF Ind, ActiveConfigsOverlap, QuorumsOverlap
    <4>4. CSM!NewerOrEqualConfig(CV(s), CV(q))
        BY <4>ok, <4>2, <4>3, NewerIsNotSymmetric, QuorumsAreNonEmpty DEF Quorums, TypeOK
    <4>5. configTerm[p] = configTerm[s]
        <5>1. configTerm[p] >= configTerm[s] BY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm
        <5>2. configTerm[s] >= configTerm[q]
            BY <4>ok, <4>4, NewerOrEqualImpliesConfigTermGreaterThanOrEqual DEF Quorums, TypeOK
        <5>. QED BY <4>ok, <4>2, <5>1, <5>2 DEF CV, TypeOK
    <4>6. configVersion[p] = configVersion[s]
        <5>1. configVersion[p] >= configVersion[s]
            BY <4>5 DEF CSM!Reconfig, Ind, PrimaryInTermContainsNewestConfigOfTerm, PrimaryConfigTermEqualToCurrentTerm
        <5>2. configVersion[s] >= configVersion[q]
            BY <4>ok, <4>2, <4>3, <4>4, <4>5, NewerOrEqualConfigWithSameTermImpliesGreaterOrEqualVersion DEF Quorums, CV, TypeOK
        <5>. QED BY <4>ok, <4>2, <5>1, <5>2 DEF CV, TypeOK
    <4>. QED BY <4>5, <4>6 DEF Ind, ConfigVersionAndTermUnique

LEMMA ConfigsIncreaseMonotonically ==
ASSUME Ind, Next
PROVE \A s \in Server : CSM!NewerOrEqualConfig(CV(s)', CV(s))
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        BY <1>1 DEF csmVars, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>ok, <2>1, ReconfigImpliesNewerOrEqualConfig
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>ok, <2>2, SendConfigImpliesNewerOrEqualConfig
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) BY <2>1
            <3>2. \A t \in Server : t # s => CV(t)' = CV(t) BY <3>1 DEF CSM!BecomeLeader, CV, TypeOK
            <3>3. CSM!NewerConfig(CV(s)', CV(s))
                <4>1. currentTerm[s] >= configTerm[s] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
                <4>2. configTerm'[s] > configTerm[s] BY <1>ok, <3>1, <4>1 DEF CSM!BecomeLeader, TypeOK
                <4>3. configVersion'[s] = configVersion[s] BY <3>1 DEF CSM!BecomeLeader
                <4>. QED BY <4>2, <4>3 DEF CSM!NewerConfig, CV, TypeOK
            <3>. QED BY <3>2, <3>3 DEF CSM!NewerOrEqualConfig
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF CSM!UpdateTerms, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

LEMMA SendConfigActiveConfigSetIdenticalExceptRecipient ==
ASSUME Ind, Next,
       NEW u \in Server,
       NEW v \in Server,
       CSM!SendConfig(u, v)
PROVE \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet
PROOF
    <4>ok. TypeOK BY DEF Ind
    <4>1. TAKE n \in ActiveConfigSet'
    <4>2. SUFFICES ASSUME n # v
          PROVE n \in ActiveConfigSet BY <4>1
    <4>3. PICK Q \in Quorums(config[n])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>4. n \in Server /\ Q \in SUBSET Server BY <4>ok, <4>1, <4>3, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
    <4>5. \A q \in Q : CSM!NewerOrEqualConfig(CV(n), CV(q))' BY <4>ok, <4>3, <4>4, NewerIsNotSymmetricAndNext
    <4>6. \A q \in Q : CSM!NewerOrEqualConfig(CV(q)', CV(q)) BY <4>ok, <4>4, SendConfigImpliesNewerOrEqualConfig
    <4>7. \A q \in Q : CSM!NewerOrEqualConfig(CV(n)', CV(q)) BY <4>ok, <4>4, <4>5, <4>6, NewerOrEqualConfigTransitivityAndNext
    <4>8. CV(n) = CV(n)' BY <4>2 DEF CSM!SendConfig, CV, TypeOK
    <4>9. \A q \in Q : CSM!NewerOrEqualConfig(CV(n), CV(q)) BY <4>7, <4>8
    <4>10. \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n)) BY <4>ok, <4>4, <4>9, NewerIsNotSymmetric
    <4>11. Q \in Quorums(config[n]) BY <4>2, <4>3, <4>4 DEF CSM!SendConfig, Quorums, TypeOK
    <4>. QED BY <4>10, <4>11 DEF ActiveConfigSet, ConfigDisabled

LEMMA BecomeLeaderActiveConfigSetIdentical ==
ASSUME Ind, Next,
       NEW p \in Server,
       \E Q \in Quorums(config[p]) : CSM!BecomeLeader(p, Q)
PROVE \A s \in ActiveConfigSet' : s \in ActiveConfigSet
PROOF
    <4>ok. TypeOK BY DEF Ind
    <4>2. TAKE s \in ActiveConfigSet'
    <4>. CASE s # p
        <5>2. PICK Q \in Quorums(config[s])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s))' BY <4>2 DEF ActiveConfigSet, ConfigDisabled
        <5>3. Q \in Quorums(config[s])' /\ \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s))' BY <5>2
        <5>4. s \in Server /\ Q \in SUBSET Server BY <4>ok, <4>2, <5>2, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
        <5>5. \A q \in Q : CSM!NewerOrEqualConfig(CV(s), CV(q))' BY <4>ok, <5>3, <5>4, NewerIsNotSymmetricAndNext
        <5>6. \A q \in Q : CSM!NewerOrEqualConfig(CV(q)', CV(q)) BY <5>4, ConfigsIncreaseMonotonically
        <5>7. \A q \in Q : CSM!NewerOrEqualConfig(CV(s)', CV(q)) BY <4>ok, <5>4, <5>5, <5>6, NewerOrEqualConfigTransitivityAndNext
        <5>8. CV(s) = CV(s)' BY DEF CSM!BecomeLeader, CV, TypeOK
        <5>9. \A q \in Q : CSM!NewerOrEqualConfig(CV(s), CV(q)) BY <5>7, <5>8
        <5>10. \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s)) BY <4>ok, <5>4, <5>9, NewerIsNotSymmetric
        <5>11. Q \in Quorums(config[s]) BY <5>2, <5>3, <5>4 DEF CSM!BecomeLeader, Quorums, TypeOK
        <5>. QED BY <5>10, <5>11 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE s = p BY <4>ok, ElectedLeadersInActiveConfigSet
    <4>. QED OBVIOUS

LEMMA EmptyIdentical ==
ASSUME TypeOK,
       NEW s \in Server
       \*NEW lg \in [Server -> Seq(Nat)]
PROVE Empty(log[s]) <=> OSM!Empty(log[s])
BY DEF OSM!Empty, Empty, TypeOK

LEMMA ConfigNewerThanPrimaryImpliesConfigTermIsNewer ==
ASSUME Ind,
       NEW s \in Server,
       NEW p \in Server,
       state[p] = Primary,
       CSM!NewerConfig(CV(s), CV(p))
PROVE configTerm[s] > configTerm[p]
BY DEF Ind, OnePrimaryPerTerm, PrimaryInTermContainsNewestConfigOfTerm, CSM!NewerConfig, CV, TypeOK

=============================================================================
