----------------------------- MODULE ElectionSafetyLemmas -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib, BasicQuorumsLib

\* approximately 1-2 dafter 3-4 weeks of prep work
\* completed 6/23
\* alt: started 8/13
\* alt: completed 8/16
LEMMA OnePrimaryPerTermAndNext ==
ASSUME Ind, Next
PROVE OnePrimaryPerTerm'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, OnePrimaryPerTerm
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, OnePrimaryPerTerm
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, OnePrimaryPerTerm
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, OnePrimaryPerTerm
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF OplogCommitment, CSM!Reconfig, Ind, OnePrimaryPerTerm
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF CSM!SendConfig, Ind, OnePrimaryPerTerm
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s \in Server : state'[s] = Primary =>
                             \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
                  BY DEF OnePrimaryPerTerm
            <3>2. TAKE s \in Server
            <3>3. SUFFICES ASSUME state'[s] = Primary
                  PROVE \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
                  BY <3>1
            <3>4. TAKE t \in Server
            <3>5. SUFFICES ASSUME state'[t] = Primary, currentTerm'[s] = currentTerm'[t], s # t
                  PROVE FALSE BY <3>3
            
            <3>6. \/ \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
                  \/ \E Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q)
                <4>a. SUFFICES ASSUME /\ ~\E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
                                      /\ ~\E Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q)
                      PROVE FALSE OBVIOUS
                <4>p. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
                <4>q. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <4>p
                <4>1. currentTerm[s] # currentTerm'[s] \/ currentTerm[t] # currentTerm'[t]
                    BY <2>1, <3>2, <3>3, <3>4, <3>5 DEF CSM!BecomeLeader, Ind, OnePrimaryPerTerm, TypeOK
                <4>2. s \in Q \/ t \in Q BY <4>q, <4>1 DEF CSM!BecomeLeader, TypeOK
                <4>3. s # p /\ t # p BY <4>a, <4>p DEF TypeOK
                <4>4. state'[s] = Secondary \/ state'[t] = Secondary BY <4>p, <4>q, <4>2, <4>3 DEF CSM!BecomeLeader, TypeOK
                <4>. QED BY <4>4, <3>3, <3>5, PrimaryAndSecondaryAreDifferent
            \* if s becomes leader then it's in the ActiveConfigSet, and thus \E n \in Q : currentTerm[n] > currentTerm[s], a contradiction
            <3>. CASE \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
                <4>1. PICK Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) OBVIOUS
                <4>2. currentTerm[t] > currentTerm[s]
                    <5>1. t \notin Q BY <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. currentTerm[t] = currentTerm'[t] BY <4>1, <5>1 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <1>ok, <5>2, <3>5 DEF CSM!BecomeLeader, TypeOK
                <4>3. currentTerm[t] = configTerm[t]
                    <5>1. t \notin Q BY <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. state[t] = Primary BY <1>ok, <5>1, <3>5 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                <4>4. s \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet DEF Ind
                <4>5. \E n \in Q : currentTerm[n] >= configTerm[t] BY <3>2, <4>1, <4>4 DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. \E n \in Q : currentTerm[n] > currentTerm[s] BY <1>ok, <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
                <4>. QED BY <1>ok, <3>2, <4>1, <4>6 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
            <3>. CASE \E Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q)
                <4>1. PICK Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q) OBVIOUS
                <4>2. currentTerm[s] > currentTerm[t]
                    <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. currentTerm[s] = currentTerm'[s] BY <4>1, <5>1 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <1>ok, <5>2, <3>5 DEF CSM!BecomeLeader, TypeOK
                <4>3. currentTerm[s] = configTerm[s]
                    <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. state[s] = Primary BY <1>ok, <5>1, <3>3, <3>5 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                <4>4. t \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet DEF Ind
                <4>5. \E n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <4>1, <4>4 DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. \E n \in Q : currentTerm[n] > currentTerm[t] BY <1>ok, <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
                <4>. QED BY <1>ok, <3>2, <4>1, <4>6 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
            <3>. QED BY <3>6
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            <3>. SUFFICES ASSUME TRUE
                 PROVE  \A s \in Server : state'[s] = Primary =>
                            \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
                 BY DEF OnePrimaryPerTerm
            <3>. TAKE s \in Server
            <3>. SUFFICES ASSUME state'[s] = Primary
                 PROVE \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t OBVIOUS
            <3>. TAKE t \in Server
            <3>. CASE \E u \in Server : OSM!UpdateTerms(u,t) /\ CSM!UpdateTerms(u,t)
                BY <1>ok, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK
            <3>. CASE ~(\E u \in Server : OSM!UpdateTerms(u,t) /\ CSM!UpdateTerms(u,t))
                <4>1. currentTerm'[s] = currentTerm[s] /\ state[s] = Primary
                    <5>1. ~(\E u \in Server : OSM!UpdateTerms(u,s) /\ CSM!UpdateTerms(u,s))
                        BY <1>ok, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                    <5>. QED BY <1>ok, <1>2, <2>2, <5>1 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                <4>2. currentTerm'[t] = currentTerm[t] /\ state'[t] = state[t]
                    BY <1>ok, <1>2, <2>2 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                <4>. QED BY <4>1, <4>2 DEF Ind, OnePrimaryPerTerm, TypeOK
            <3>. QED OBVIOUS
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next
    
\* approximately 30 min
\* completed 6/23
\* alt: no work needed
LEMMA PrimaryConfigTermEqualToCurrentTermAndNext ==
ASSUME Ind, Next
PROVE PrimaryConfigTermEqualToCurrentTerm'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF OplogCommitment, CSM!Reconfig, Ind, PrimaryConfigTermEqualToCurrentTerm
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, Ind, PrimaryConfigTermEqualToCurrentTerm
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A s \in Server : (state'[s] = Primary) => (configTerm'[s] = currentTerm'[s])
                 BY DEF PrimaryConfigTermEqualToCurrentTerm
            <3>. TAKE s \in Server
            <3>. SUFFICES ASSUME state'[s] = Primary
                 PROVE configTerm'[s] = currentTerm'[s] OBVIOUS
            <3>. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) OBVIOUS
            <3>. CASE p = s BY <1>ok DEF CSM!BecomeLeader, TypeOK, Quorums
            <3>. CASE p # s BY PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader, TypeOK, Quorums, Ind, PrimaryConfigTermEqualToCurrentTerm
            <3>. QED OBVIOUS
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* alt: began 8/16
\* alt: completed 8/16
\* approx: 1-2 hr
\* updated to more concise version later, 5 min
LEMMA ConfigVersionAndTermUniqueAndNext_BecomeLeader ==
ASSUME Ind, Next,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       OSM!BecomeLeader(s, Q),
       CSM!BecomeLeader(s, Q),
       NEW t \in Server,
       <<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>
PROVE config'[s] = config'[t]
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. \A n \in Server : currentTerm[s] >= configTerm[n] BY ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind
    <1>. QED BY <1>ok, <1>1, TypeOKAndNext DEF CSM!BecomeLeader, TypeOK

\* approx 1 day
\* completed 6/29
\* alt: only needed to update ConfigVersionAndTermUniqueAndNext_BecomeLeader
LEMMA ConfigVersionAndTermUniqueAndNext ==
ASSUME Ind, Next
PROVE ConfigVersionAndTermUnique'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, ConfigVersionAndTermUnique, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, ConfigVersionAndTermUnique, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, ConfigVersionAndTermUnique, csmVars
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, ConfigVersionAndTermUnique, csmVars
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>. PICK p \in Server : \E newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>1. state[p] = Primary BY DEF CSM!Reconfig
            <3>2. \A s \in Server : configTerm[s] = configTerm[p] => configVersion[s] <= configVersion[p] BY <3>1 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm
            <3>3. \A s \in Server : (s # p /\ configTerm[s] = configTerm[p]) => configVersion'[s] < configVersion'[p] BY <1>ok, <3>2 DEF CSM!Reconfig, TypeOK
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A s,t \in Server :
                            (<<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>) => config'[s] = config'[t]
                 BY DEF ConfigVersionAndTermUnique
            <3>. TAKE s,t \in Server
            <3>. SUFFICES ASSUME <<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>
                 PROVE config'[s] = config'[t] OBVIOUS
            <3>. CASE s = t OBVIOUS
            <3>. CASE s # t
                <4>1. s # p
                    <5>. SUFFICES ASSUME s = p
                         PROVE FALSE OBVIOUS
                    <5>1. configTerm[s] # configTerm[t] BY <3>3, TypeOKAndNext DEF TypeOK
                    <5>2. configTerm'[t] = configTerm[t] BY DEF CSM!Reconfig, TypeOK
                    <5>3. configTerm'[s] = configTerm[s] BY DEF CSM!Reconfig, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
                    <5>. QED BY <5>1, <5>2, <5>3
                <4>2. t # p BY <4>1, <3>3, TypeOKAndNext DEF CSM!Reconfig, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
                <4>. QED BY <4>1, <4>2 DEF CSM!Reconfig, TypeOK, Ind, ConfigVersionAndTermUnique
            <3>. QED OBVIOUS
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF CSM!SendConfig, Ind, ConfigVersionAndTermUnique, TypeOK
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A s,t \in Server :
                            (<<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>) => config'[s] = config'[t]
                 BY DEF ConfigVersionAndTermUnique
            <3>. TAKE s,t \in Server
            <3>. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>. CASE s = p \/ t = p BY ConfigVersionAndTermUniqueAndNext_BecomeLeader DEF ConfigVersionAndTermUnique
            <3>. CASE s # p /\ t # p BY DEF CSM!BecomeLeader, Ind, ConfigVersionAndTermUnique
            <3>. QED OBVIOUS
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK, Ind, ConfigVersionAndTermUnique
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* approx 1.5 days
\* completed 7/11
\* alt: completed 8/16
\* alt: approx 5 min
LEMMA PrimaryInTermContainsNewestConfigOfTermAndNext ==
ASSUME Ind, Next
PROVE PrimaryInTermContainsNewestConfigOfTerm'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A p,s \in Server : (state'[p] = Primary /\ configTerm'[s] = configTerm'[p]) => (configVersion'[p] >= configVersion'[s])
                 BY DEF PrimaryInTermContainsNewestConfigOfTerm
            <3>. TAKE p,s \in Server
            <3>. SUFFICES ASSUME state'[p] = Primary, configTerm'[s] = configTerm'[p]
                 PROVE configVersion'[p] >= configVersion'[s] OBVIOUS
                 
            <3>. PICK r \in Server, newConfig \in SUBSET Server : OplogCommitment(r) /\ CSM!Reconfig(r, newConfig) BY <2>1
            <3>. CASE p = r BY DEF CSM!Reconfig, Ind, PrimaryConfigTermEqualToCurrentTerm, PrimaryInTermContainsNewestConfigOfTerm, TypeOK
            <3>. CASE s = r BY DEF CSM!Reconfig, Ind, OnePrimaryPerTerm, PrimaryConfigTermEqualToCurrentTerm
            <3>. CASE p # r /\ s # r BY DEF CSM!Reconfig, Ind, PrimaryInTermContainsNewestConfigOfTerm
            <3>. QED OBVIOUS
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A p,s \in Server : (state'[p] = Primary /\ configTerm'[s] = configTerm'[p]) => (configVersion'[p] >= configVersion'[s])
                 BY DEF PrimaryInTermContainsNewestConfigOfTerm
            <3>. TAKE p,s \in Server
            <3>. SUFFICES ASSUME state'[p] = Primary, configTerm'[s] = configTerm'[p]
                 PROVE configVersion'[p] >= configVersion'[s] OBVIOUS
                 
            <3>. CASE \E t \in Server : CSM!SendConfig(t, s)
                <4>. PICK t \in Server : CSM!SendConfig(t, s) OBVIOUS
                <4>. CASE t # p
                    <5>1. configTerm'[p] = configTerm[p] /\ configTerm'[t] = configTerm[t] BY PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, TypeOK
                    <5>2. configTerm'[t] = configTerm'[s] BY <1>ok DEF CSM!SendConfig, TypeOK
                    <5>3. configTerm[p] = configTerm[t] BY <5>1, <5>2 DEF TypeOK
                    <5>4. configVersion[p] >= configVersion[t] BY <5>3 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm, CSM!SendConfig, TypeOK
                    <5>. QED BY <1>ok, <5>4 DEF CSM!SendConfig, TypeOK
                <4>. CASE t = p BY <1>ok DEF CSM!SendConfig, TypeOK
                <4>. QED OBVIOUS
            <3>. CASE ~(\E t \in Server : CSM!SendConfig(t, s))
                <4>1. configVersion'[s] = configVersion[s] /\ configTerm'[s] = configTerm[s] BY <2>2 DEF Ind, CSM!SendConfig, TypeOK
                <4>2. configVersion'[p] = configVersion[p] /\ configTerm'[p] = configTerm[p] BY <2>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, TypeOK
                <4>3. state[p] = Primary /\ configTerm[s] = configTerm[p] BY <2>2, <4>1, <4>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, TypeOK
                <4>4. configVersion[p] >= configVersion[s] BY <4>3 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm
                <4>. QED BY <4>1, <4>2, <4>4
            <3>. QED OBVIOUS
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) BY <2>1
            <3>2. \A t \in Server : currentTerm[s] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind
            <3>. QED BY <3>1, <3>2 DEF CSM!BecomeLeader, TypeOK, Ind, PrimaryInTermContainsNewestConfigOfTerm
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK, Ind, PrimaryInTermContainsNewestConfigOfTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


\* began: 8/16
\* finished: 8/24
LEMMA ActiveConfigsOverlapAndNext ==
ASSUME Ind, Next
PROVE ActiveConfigsOverlap'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, ActiveConfigsOverlap, csmVars,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, ActiveConfigsOverlap, csmVars,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, ActiveConfigsOverlap, csmVars,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, ActiveConfigsOverlap, csmVars,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>p. PICK p \in Server, newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>1. p \in ActiveConfigSet BY <3>p, ReconfigImpliesInActiveConfigSet DEF Ind
            <3>2. \A s \in ActiveConfigSet' : config[s] = config[p] BY <3>p, ReconfigImpliesActiveConfigSetHaveSameConfig DEF Ind
            <3>3. \A t \in ActiveConfigSet' : config'[t] = newConfig \/ config'[t] = config[p]
                BY <3>p, <3>2 DEF CSM!Reconfig, TypeOK
            <3>4. QuorumsOverlap(config[p], newConfig) BY <1>ok, <3>p, QuorumsOverlapIdentical DEF CSM!Reconfig, TypeOK
            <3>. QED BY <1>ok, <3>p, <3>3, <3>4, QuorumsOverlapIsCommutative, StaticQuorumsOverlap DEF ActiveConfigsOverlap, QuorumsOverlap, Quorums, TypeOK
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            <3>1. PICK u \in Server, v \in Server : CSM!SendConfig(u, v) BY <2>2
            <3>2. \A n \in Server : n # v => config[n] = config'[n] BY <3>1 DEF CSM!SendConfig, TypeOK
            <3>3. \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet BY <3>1, SendConfigActiveConfigSetIdenticalExceptRecipient DEF Ind
            <3>4. \A s,t \in ActiveConfigSet' : (s # v /\ t # v) => QuorumsOverlap(config[s], config[t])'
                <4>1. \A s,t \in ActiveConfigSet' : (s # v /\ t # v) => QuorumsOverlap(config[s], config[t]) BY <3>3 DEF Ind, ActiveConfigsOverlap
                <4>. QED BY <3>2, <4>1 DEF ActiveConfigSet, ConfigDisabled
            <3>5. \A s,t \in ActiveConfigSet' : (s = v /\ t # v) => QuorumsOverlap(config[s], config[t])'
                <4>1. TAKE s,t \in ActiveConfigSet'
                <4>2. SUFFICES ASSUME s = v, t # v
                      PROVE QuorumsOverlap(config[s], config[t])' OBVIOUS
                <4>. CASE u \in ActiveConfigSet'
                    <5>1. t \in ActiveConfigSet /\ u \in ActiveConfigSet BY <3>1, <3>3, <4>1, <4>2 DEF CSM!SendConfig, CSM!IsNewerConfig, TypeOK
                    <5>2. QuorumsOverlap(config[u], config[t]) BY <5>1, QuorumsOverlapIsCommutative DEF Ind, ActiveConfigsOverlap
                    <5>3. config'[t] = config[t] BY <3>1, <4>2 DEF CSM!SendConfig, TypeOK
                    <5>4. config'[s] = config[u] BY <1>ok, <3>1, <4>2, TypeOKAndNext DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <5>2, <5>3, <5>4
                <4>. CASE u \notin ActiveConfigSet'
                    BY <1>ok, <3>1, <4>1, <4>2 DEF CSM!SendConfig, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
                <4>. QED OBVIOUS
            <3>6. \A s,t \in ActiveConfigSet' : (s # v /\ t = v) => QuorumsOverlap(config[s], config[t])'
                BY <1>ok, <3>5, QuorumsOverlapIsCommutative, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, TypeOK
            <3>7. \A s,t \in ActiveConfigSet' : (s = v /\ t = v) => QuorumsOverlap(config[s], config[t])'
                BY <1>ok, StaticQuorumsOverlap, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, QuorumsOverlap, TypeOK
            <3>. QED BY <3>4, <3>5, <3>6, <3>7 DEF ActiveConfigsOverlap
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. \A s \in Server : Quorums(config'[s]) = Quorums(config[s]) BY <2>1 DEF CSM!BecomeLeader, Quorums
            <3>2. \A s,t \in Server : QuorumsOverlap(config[s],config[t]) <=> QuorumsOverlap(config[s],config[t])' BY <3>1 DEF QuorumsOverlap
            <3>3. \A s \in ActiveConfigSet' : s \in ActiveConfigSet BY <2>1, BecomeLeaderActiveConfigSetIdentical DEF Ind
            <3>. QED BY <3>2, <3>3 DEF Ind, ActiveConfigsOverlap, ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF CSM!UpdateTerms, Ind, ActiveConfigsOverlap,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/24
\* finished: 8/24
\* 1 long day (6 hrs?).  Having the lemmas generated from ActiveConfigsOverlapAndNext
\* for CSM!Reconfig and CSM!SendConfig really helped speed up this proof.
LEMMA ActiveConfigsSafeAtTermsAndNext ==
ASSUME Ind, Next
PROVE ActiveConfigsSafeAtTerms'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF csmVars, OSM!ClientRequest, Ind, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF csmVars, OSM!GetEntries, Ind, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF csmVars, OSM!RollbackEntries, Ind, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF csmVars, OSM!CommitEntry, Ind, ActiveConfigsSafeAtTerms,
                ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>p. PICK p \in Server, newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                    \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                  BY DEF ActiveConfigsSafeAtTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in ActiveConfigSet'
            <3>4. config[t] = config[p] BY <3>p, <3>3, ReconfigImpliesActiveConfigSetHaveSameConfig DEF Ind
            <3>5. CASE t # p
                <4>1. config'[t] = config[t] /\ config'[t] = config[p] BY <3>p, <3>4, <3>5 DEF CSM!Reconfig, TypeOK
                <4>2. PICK pQ \in Quorums(config[p]) : \A n \in pQ : currentTerm[n] = currentTerm[p]
                    BY <3>p, QuorumsIdentical DEF CSM!Reconfig, CSM!TermQuorumCheck, Ind
                <4>3. TAKE tQ \in Quorums(config'[t])
                <4>4. tQ \in Quorums(config[t]) BY <4>1, <4>3
                <4>5. QuorumsOverlap(config[t], config[p])
                    BY <3>3, ReconfigImpliesSameActiveConfigSet, <3>p, ReconfigImpliesInActiveConfigSet DEF Ind, ActiveConfigsOverlap
                <4>6. PICK n \in tQ : n \in pQ BY <4>2, <4>4, <4>5 DEF QuorumsOverlap
                <4>7. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>2, <4>6, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF Ind
                <4>8. currentTerm'[n] >= configTerm'[s]
                    BY <3>p, <3>2, <3>3, <4>4, <4>6, <4>7, ReconfigImpliesConfigTermUnchanged DEF CSM!Reconfig, Quorums, TypeOK
                <4>. QED BY <3>1, <3>2, <3>3, <4>3, <4>8
            <3>6. CASE t = p
                <4>1. PICK pQ \in Quorums(config[p]) : \A n \in pQ : currentTerm[n] = currentTerm[p]
                    BY <3>p, QuorumsIdentical DEF CSM!Reconfig, CSM!TermQuorumCheck, Ind
                <4>2. config'[t] = newConfig BY <1>ok, <3>p, <3>6 DEF CSM!Reconfig, TypeOK
                <4>3. TAKE tQ \in Quorums(config'[t])
                <4>4. QuorumsOverlap(config[p], newConfig) BY <1>ok, <3>p, <4>1, <4>2, <4>3, QuorumsOverlapIdentical DEF CSM!Reconfig, TypeOK
                <4>5. PICK n \in tQ : n \in pQ BY <4>1, <4>2, <4>3, <4>4 DEF QuorumsOverlap
                <4>6. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>1, <4>5, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF Ind
                <4>7. currentTerm'[n] >= configTerm'[s]
                    BY <3>p, <3>2, <3>3, <4>3, <4>5, <4>6, ReconfigImpliesConfigTermUnchanged DEF CSM!Reconfig, Quorums, TypeOK
                <4>. QED BY <3>1, <3>2, <3>3, <4>3, <4>7
            <3>. QED BY <3>5, <3>6
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            <3>1. PICK u,v \in Server : CSM!SendConfig(u, v) BY <2>2
            <3>2. SUFFICES ASSUME TRUE
                  PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                    \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                  BY DEF ActiveConfigsSafeAtTerms
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in ActiveConfigSet'
            <3>5. CASE t # v
                <4>1. t \in ActiveConfigSet BY <3>1, <3>4, <3>5, SendConfigActiveConfigSetIdenticalExceptRecipient DEF Ind
                <4>2. CASE s # v
                    <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s] BY <4>1 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>. QED BY <3>1, <3>5, <4>2, <5>1 DEF CSM!SendConfig, TypeOK
                <4>3. CASE s = v
                    <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[u] BY <3>1, <4>1 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>2. configTerm'[s] = configTerm[u] BY <1>ok, <3>1, <4>3 DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <3>1, <3>5, <4>2, <5>1, <5>2 DEF CSM!SendConfig, TypeOK
                <4>. QED BY <4>2, <4>3
            <3>6. CASE t = v
                <4>u. u # v BY <3>1 DEF CSM!SendConfig, CSM!IsNewerConfig, TypeOK
                <4>1. u \in ActiveConfigSet' BY <1>ok, <3>1, <3>6 DEF CSM!SendConfig, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
                <4>2. u \in ActiveConfigSet BY <3>1, <4>1, <4>u, SendConfigActiveConfigSetIdenticalExceptRecipient DEF Ind
                <4>3. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[s] BY <3>1, <4>2 DEF Ind, ActiveConfigsSafeAtTerms
                <4>4. config'[t] = config[u] BY <1>ok, <3>1, <3>6 DEF CSM!SendConfig, TypeOK
                <4>5. CASE s # v
                    <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                        BY <3>1, <4>u, <4>3, <4>5 DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <4>4, <5>1
                <4>6. CASE s = v
                    <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[u]
                        BY <3>1, <4>2 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>. QED BY <1>ok, <3>1, <4>4, <4>6, <5>1 DEF CSM!SendConfig, TypeOK
                <4>. QED BY <4>5, <4>6
            <3>. QED BY <3>5, <3>6
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>p. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>q. PICK pQ \in Quorums(config[p]) : OSM!BecomeLeader(p, pQ) /\ CSM!BecomeLeader(p, pQ) BY <3>p
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                    \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                  BY DEF ActiveConfigsSafeAtTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in ActiveConfigSet'
            <3>4. t \in ActiveConfigSet BY <2>1, <3>3, BecomeLeaderActiveConfigSetIdentical DEF TypeOK
            <3>5. TAKE Q \in Quorums(config'[t])
            <3>6. Q \in Quorums(config[t]) BY <2>1, <3>4, <3>5 DEF CSM!BecomeLeader, ActiveConfigSet, ConfigDisabled
            <3>7. PICK n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <3>4, <3>6 DEF Ind, ActiveConfigsSafeAtTerms
            <3>n. n \in Server BY <1>ok, <3>6, <3>7 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
            <3>8. CASE n \in pQ
                <4>1. currentTerm'[p] >= configTerm'[s]
                    <5>1. currentTerm[p] >= configTerm[s] BY <3>p, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
                    <5>2. CASE s # p
                        <6>1. configTerm'[s] = configTerm[s] BY <3>p, <5>2 DEF CSM!BecomeLeader, TypeOK
                        <6>2. currentTerm'[p] >= currentTerm[p] BY <1>ok, <3>p DEF CSM!BecomeLeader, TypeOK
                        <6>. QED BY <1>ok, <5>1, <6>1, <6>2, TypeOKAndNext DEF TypeOK
                    <5>3. CASE s = p BY <1>ok, <3>p, <5>3 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2, <5>3
                <4>2. currentTerm'[n] = currentTerm'[p] BY <1>ok, <3>p, <3>q, <3>8 DEF CSM!BecomeLeader, Quorums, TypeOK
                <4>. QED BY <3>7, <4>1, <4>2
            <3>9. CASE n \notin pQ
                <4>1. currentTerm'[n] = currentTerm[n] BY <3>p, <3>q, <3>n, <3>9 DEF CSM!BecomeLeader, TypeOK
                <4>2. CASE s # p BY <1>ok, <3>p, <3>7, <4>1, <4>2 DEF CSM!BecomeLeader, TypeOK
                <4>3. CASE s = p
                    <5>1. s \in ActiveConfigSet BY <3>p, <4>3, ElectedLeadersInActiveConfigSet DEF Ind
                    <5>2. QuorumsOverlap(config[t], config[s]) BY <3>4, <5>1 DEF Ind, ActiveConfigsOverlap
                    <5>3. PICK q \in pQ : q \in Q BY <3>6, <3>p, <3>q, <4>3, <5>2 DEF QuorumsOverlap
                    <5>4. currentTerm'[q] >= currentTerm'[s] \* their currentTerm's are equal because the update on q's
                                                             \* currentTerm is atomic (as well as p's)
                        BY <1>ok, <3>p, <3>q, <4>3, <5>3, TypeOKAndNext DEF CSM!BecomeLeader, Quorums, TypeOK
                    <5>5. currentTerm'[s] = configTerm'[s] BY <1>ok, <3>p, <4>3 DEF CSM!BecomeLeader, TypeOK
                    <5>6. q \in Server BY <1>ok, <3>4, <3>6, <5>3 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
                    <5>. QED BY <5>3, <5>4, <5>5, <5>6, TypeOKAndNext DEF TypeOK
                <4>. QED BY <4>2, <4>3
            <3>. QED BY <3>8, <3>9
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            <3>1. SUFFICES ASSUME TRUE
                  PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                    \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                  BY DEF ActiveConfigsSafeAtTerms
            <3>2. TAKE s \in Server
            <3>3. TAKE t \in ActiveConfigSet'
            <3>4. t \in ActiveConfigSet BY <2>2, <3>3 DEF CSM!UpdateTerms, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
            <3>5. t \in Server BY <3>4 DEF ActiveConfigSet, ConfigDisabled
            <3>6. TAKE Q \in Quorums(config'[t])
            <3>7. Q \in Quorums(config[t]) BY <2>2, <3>5, <3>6 DEF CSM!UpdateTerms, Quorums, TypeOK
            <3>8. PICK n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <3>4, <3>7 DEF Ind, ActiveConfigsSafeAtTerms
            <3>9. currentTerm'[n] >= currentTerm[n]
                <4>1. n \in Server BY <1>ok, <3>5, <3>7, <3>8 DEF Quorums, TypeOK
                <4>. QED BY <1>ok, <2>2, <4>1, TypeOKAndNext DEF CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
            <3>. QED BY <1>ok, <2>2, <3>5, <3>9, <3>8, <3>9, TypeOKAndNext DEF CSM!UpdateTerms, Quorums, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

=============================================================================
