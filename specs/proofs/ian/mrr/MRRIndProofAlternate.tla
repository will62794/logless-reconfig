----------------------------- MODULE MRRIndProofAlternate -----------------------------

EXTENDS MongoRaftReconfig, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS


InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is node i disabled due to a quorum of its config having moved to a newer config.
ConfigDisabled(i) == 
    \A Q \in Quorums(config[i]) : \E n \in Q : CSM!NewerConfig(CV(n), CV(i))

\* Does server s have the newest config.
NewestConfig(s) == \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))

\* Servers in the newest config.
ServersInNewestConfig == {s \in Server : NewestConfig(s)}

OlderConfig(ci, cj) == ~CSM!NewerOrEqualConfig(ci, cj) 

--------------------------------------------------------------------------------

\*
\* Establishing election safety under reconfiguration.
\*

OnePrimaryPerTerm ==
    \A s \in Server : state[s] = Primary =>
        \A t \in Server :
            (state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t

PrimaryConfigTermEqualToCurrentTerm == 
    \A s \in Server : (state[s] = Primary) => (configTerm[s] = currentTerm[s])

ConfigVersionAndTermUnique ==
    \A i,j \in Server :
        (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>> )=>
        config[i] = config[j]

PrimaryInTermContainsNewestConfigOfTerm == 
    \A p,s \in Server : 
        (state[p] = Primary /\ configTerm[s] = configTerm[p]) =>
            (configVersion[p] >= configVersion[s]) 

\* If config t has an older config than s, and their configs don't overlap, then
\* config t must be disabled based on config ordering.
NewerConfigDisablesOlderNonoverlappingConfigs == 
    \A s,t \in Server :
        (/\ OlderConfig(CV(t), CV(s)) 
         /\ ~QuorumsOverlap(config[t], config[s])) => ConfigDisabled(t)

\* If t has an older or equal config than s and it is not disabled by a newer
\* config, then its quorum must overlap with some node in the term of config s.
NewerConfigDisablesTermsOfOlderNonDisabledConfigs ==
    \A s,t \in Server :
        (/\ OlderConfig(CV(t), CV(s)) \/ (CV(t) = CV(s))
         /\ ~ConfigDisabled(t)) => 
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]


\*
\* Establishing log invariants.
\*

EqualUpTo(log1, log2, i) ==
    \*\A j \in 1..i : log1[j] = log2[j]
    \A j \in Nat : (j > 0 /\ j <= i) => log1[j] = log2[j]

\* This is a core property of Raft, but MongoStaticRaft does not satisfy this
LogMatching ==
    \A s,t \in Server :
        \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
            log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)

TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : i <= j => log[s][i] <= log[s][j]

\* If a log entry exists in term T and there is a primary in term T, then this
\* log entry should be present in that primary's log.
PrimaryHasEntriesItCreated == 
    \A i,j \in Server :
    (state[i] = Primary) => 
    \* Can't be that another node has an entry in this primary's term
    \* but the primary doesn't have it.
        ~(\E k \in DOMAIN log[j] :
            /\ log[j][k] = currentTerm[i]
            /\ ~InLog(<<k,log[j][k]>>, i))
    
\* A server's current term is always at least as large as the terms in its log.
\* This is LEMMA 6 from the Raft dissertation.
CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
    \A s \in Server : state[s] = Primary => (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* If a log entry in term T exists, there must have been an election in 
\* term T to create it, implying the existence of a config in term T or newer.
LogEntryInTermImpliesConfigInTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] :
    \E t \in Server : 
        configTerm[t] >= log[s][i]

\* If a log contains an entry in term T at index I such that
\* the entries at J < I are in a different term, then there must be
\* no other logs that contains entries in term T at indices J < I
UniformLogEntriesInTerm ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] : 
        (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => 
            (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)
    
\*
\* Basic type requirements of 'committed' variable.
\*

CommittedEntryIndexesAreNonZero == \A c \in committed : c.entry[1] # 0

\* Belongs in TypeOK, or considered a completely separate II
CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

\*
\* Establishing additional config related invariants that
\* help with leader completeness.
\*

\* For configs C=(v,t) and C'=(v+1,t), we know their quorums overlap, by explicit preconditions
\* of reconfiguration.
ConfigOverlapsWithDirectAncestor ==
    \A s,t \in Server :
        (/\ configVersion[s] = (configVersion[t] + 1)
         /\ configTerm[s] = configTerm[t]) => QuorumsOverlap(config[s], config[t])

NewestConfigHasLargestTerm == 
    \A s \in ServersInNewestConfig :
    \A t \in Server :
        currentTerm[t] <= configTerm[s]

\* The newest config should have some node that is currently primary or was
\* the newest primary (after stepping down). This node should be in its own config.
NewestConfigHasSomeNodeInConfig == 
    \A s \in ServersInNewestConfig : 
        (\E n \in config[s] :
            /\ n \in config[n]
            \* If this is node is or was primary in newest config,
            \* it's term should be the same as the term of the newest config.
            /\ currentTerm[n] = configTerm[s]
            /\ CV(n) = CV(s))

\* If two configs have the same version but different terms, one has a newer term,
\* then they either have the same member set or the older config is disabled. The 
\* latter is to address the case where these configs on divergent branches but have the
\* same version.
ConfigsWithSameVersionHaveSameMemberSet == 
    \A s,t \in Server : 
        (/\ configVersion[s] = configVersion[t]
         /\ configTerm[s] > configTerm[t]) => 
            \/ (config[s] = config[t])
            \/ ConfigDisabled(t)

\* If a config has been created in term T', then this must prevent any commits
\* in configs in terms < T. Note that only primary nodes can commit writes in a 
\* config.
CommitOfNewConfigPreventsCommitsInOldTerms == 
    \A s,t \in Server : 
        (/\ configTerm[t] < configTerm[s]
         /\ state[t] = Primary) =>
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]

\* 
\* Establishing leader completeness invariant.
\*

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderCompletenessGeneralized ==
    \A s \in Server : 
        (state[s] = Primary) =>
        (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

CommittedEntryIntersectsWithNewestConfig ==
    \A c \in committed :
    \A s \in ServersInNewestConfig :
        \A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n)

\* \* If a log entry is committed, then the quorums of every 
\* active config must overlap with some node that contains this log entry.
CommittedEntryIntersectsWithEveryActiveConfig ==
    \A c \in committed :
    \A s \in Server :
        ~ConfigDisabled(s) => (\A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n))


\* when a server's latest log term EXCEEDS a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log
LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
            \A d \in committed :
                d.term <= c.term => /\ Len(log[s]) >= d.entry[1]
                                    /\ log[s][d.entry[1]] = d.term
                                    
                                    
ActiveConfigSet == {s \in Server : ~ConfigDisabled(s)}

\* The quorums of all active configs overlap with each other. 
ActiveConfigsOverlap == 
    \A s,t \in ActiveConfigSet : QuorumsOverlap(config[s], config[t])

\* Every active config overlaps with some node in a term >=T for all elections
\* that occurred in term T (and exist in some config that is still around).
ActiveConfigsSafeAtTerms == 
    \A s \in Server : 
    \A t \in ActiveConfigSet :
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]

ActiveConfigsOverlapWithCommittedEntry == 
    \A c \in committed :
    \A s \in ActiveConfigSet :
        \A Q \in Quorums(config[s]) : \E n \in Q : InLog(c.entry, n)   

NewerConfigsDisablePrimaryCommitsInOlderTerms ==
    \A s,t \in Server : 
    (state[t] = Primary /\ currentTerm[t] < configTerm[s]) =>
        \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > currentTerm[t]

--------------------------------------------------------------------------------

\*IndAlt == 
Ind == 
    \*
    \* Establishing election safety under reconfiguration.
    \*
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigVersionAndTermUnique
    /\ PrimaryInTermContainsNewestConfigOfTerm
    \* (alternate)
    /\ ActiveConfigsOverlap
    /\ ActiveConfigsSafeAtTerms

    \*
    \* Establishing log invariants.
    \*
    /\ LogMatching
    /\ TermsOfEntriesGrowMonotonically
    /\ PrimaryHasEntriesItCreated
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ LogEntryInTermImpliesConfigInTerm
    /\ UniformLogEntriesInTerm

    \*
    \* Basic type requirements of 'committed' variable.
    \*
    /\ CommittedEntryIndexesAreNonZero
    /\ CommittedTermMatchesEntry

    \* (alternate)
    /\ LeaderCompletenessGeneralized
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ ActiveConfigsOverlapWithCommittedEntry
    /\ NewerConfigsDisablePrimaryCommitsInOlderTerms 

TypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq(Nat)]
    /\ config \in [Server -> SUBSET Server]
    /\ configVersion \in [Server -> Nat]
    /\ configTerm \in [Server -> Nat]
    \* For checking MongoRaftReconfig with logs.
    /\ committed \in SUBSET [ entry : Nat \X Nat, term : Nat ]
    /\ elections \in SUBSET [ leader : Server, term : Nat ]

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}

CVT(s) == <<configTerm[s], configVersion[s], currentTerm[s]>>

--------------------------------------------------------------------------------

(* TypeOK *)

LEMMA InitImpliesTypeOK ==
ASSUME Init
PROVE TypeOK
PROOF BY DEF TypeOK, Init, OSM!Init, CSM!Init

LEMMA TypeOKAndNext ==
ASSUME TypeOK, Next
PROVE TypeOK'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, TypeOK, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, TypeOK, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, TypeOK, csmVars
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, TypeOK, csmVars
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF OplogCommitment, CSM!Reconfig, TypeOK, osmVars
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF CSM!SendConfig, TypeOK, osmVars
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>. PICK s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
                BY <2>1
            <3>. CASE log' = [log EXCEPT ![s] = Append(log[s], currentTerm[s]+1)]
                BY <1>3, <2>1 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>. CASE UNCHANGED log
                BY <1>3, <2>1 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>. QED BY DEF OSM!BecomeLeader
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <1>3, <2>2 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


--------------------------------------------------------------------------------

LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorums(S) # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorums

\* this isn't true unless we add it to the II
LEMMA ConfigsAreNonempty ==
ASSUME TRUE
PROVE \A s \in Server : config[s] # {} /\ IsFiniteSet(config[s])

COROLLARY QuorumsExistsForServer ==
ASSUME NEW s \in Server
PROVE Quorums(config[s]) # {}
PROOF BY QuorumsExistForNonEmptySets, ConfigsAreNonempty

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE QuorumsAt(s) \subseteq SUBSET Server
PROOF BY DEF QuorumsAt, Quorums, TypeOK

LEMMA StaticQuorumsOverlap ==
ASSUME \*TypeOK,
       NEW cfg \in SUBSET Server,
       NEW Q1 \in Quorums(cfg),
       NEW Q2 \in Quorums(cfg)
PROVE Q1 \cap Q2 # {}
PROOF
    <1>. IsFiniteSet(cfg)
        BY FS_Subset, ServerIsFinite, ConfigsAreNonempty\* DEF TypeOK
    <1>. IsFiniteSet(Q1) /\ IsFiniteSet(Q2)
        BY QuorumsAreServerSubsets, ServerIsFinite, FS_Subset DEF Quorums
    <1>. IsFiniteSet(Q1 \cap Q2)
        BY FS_Intersection
    <1>1. Q1 \in SUBSET cfg /\ Q2 \in SUBSET cfg
        BY QuorumsAreServerSubsets DEF QuorumsAt, Quorums, TypeOK
    <1>2. Cardinality(Q1) + Cardinality(Q2) <= Cardinality(cfg) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1 \cup Q2) = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
            BY FS_Union
        <2>2. Cardinality(Q1 \cup Q2) <= Cardinality(cfg)
            BY <1>1, FS_Subset, ServerIsFinite
        <2>3. QED BY <2>1, <2>2, FS_CardinalityType
    <1>3. Cardinality(Q1) + Cardinality(Q2) < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1) * 2 > Cardinality(cfg) /\ Cardinality(Q2) * 2 > Cardinality(cfg)
            BY <1>1 DEF QuorumsAt, Quorums, TypeOK
        <2>2. Cardinality(Q1) + Cardinality(Q2) > Cardinality(cfg)
            BY <2>1, FS_CardinalityType, ServerIsFinite
        <2>3. QED BY <2>2, <1>2, FS_CardinalityType
    <1>4. Cardinality(Q1 \cap Q2) > 0
        BY <1>3, FS_CardinalityType
    <1>5. QED BY <1>4, FS_EmptySet

COROLLARY ConfigQuorumsOverlap ==
ASSUME \*TypeOK,
       NEW cfg \in SUBSET Server
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
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE \A t \in Server : configTerm'[t] = configTerm[t]
PROOF
    <1>1. state[s] = Primary BY DEF CSM!Reconfig
    <1>2. configTerm[s] = currentTerm[s] BY <1>1 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
    <1>. QED BY <1>2 DEF CSM!Reconfig, TypeOK

LEMMA ReconfigImpliesNewerOrEqualConfig ==
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE /\ CSM!NewerConfig(CV(s)', CV(s))
      /\ \A t \in Server : t # s => CV(t)' = CV(t)
      /\ \A t \in Server : CSM!NewerOrEqualConfig(CV(t)', CV(t))
PROOF
    <1>1. CSM!NewerConfig(CV(s)', CV(s))
        <2>1. configVersion'[s] > configVersion[s] BY DEF CSM!Reconfig, TypeOK
        <2>. QED BY <2>1, ReconfigImpliesConfigTermUnchanged DEF CSM!NewerConfig, CV, TypeOK
    <1>2. \A t \in Server : t # s => CV(t)' = CV(t) BY DEF CSM!Reconfig, CV, TypeOK
    <1>3. \A t \in Server : CSM!NewerOrEqualConfig(CV(t)', CV(t)) BY <1>1, <1>2 DEF CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
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

LEMMA QuorumsIdentical ==
ASSUME TypeOK
PROVE \A s \in Server : Quorums(config[s]) = CSM!Quorums(config[s])
        
LEMMA QuorumsOverlapIdentical ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> CSM!QuorumsOverlap(conf1,conf2)
\*PROOF BY QuorumsIdentical DEF QuorumsOverlap, CSM!QuorumsOverlap \*, Quorums, CSM!Quorums \*, TypeOK

LEMMA QuorumsOverlapIsCommutative ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> QuorumsOverlap(conf2,conf1)
\*PROOF BY DEF QuorumsOverlap, Quorums, TypeOK

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
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       CSM!BecomeLeader(s, Q)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>. TAKE t \in Server
    <1>1. PICK n \in Q : currentTerm[n] >= configTerm[t] BY ElectedLeadersInActiveConfigSet DEF Ind, ActiveConfigsSafeAtTerms
    <1>2. currentTerm[s] >= currentTerm[n] BY <1>1 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
    <1>. QED BY <1>1, <1>2 DEF Quorums, TypeOK

LEMMA ReconfigImpliesInActiveConfigSet ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE s \in ActiveConfigSet
PROOF BY QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt,
            ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, Quorums, TypeOK

LEMMA ReconfigImpliesCurrentTermGreaterThanConfigTerms ==
ASSUME TypeOK, Ind,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(s, newConfig)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>1. s \in ActiveConfigSet BY ReconfigImpliesInActiveConfigSet
    <1>2. TAKE t \in Server
    <1>3. PICK Q \in Quorums(config[s]) : \A n \in Q : currentTerm[n] = currentTerm[s]
        BY QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt
    <1>4. PICK n \in Q : currentTerm[n] >= configTerm[t] BY <1>1, <1>3 DEF Ind, ActiveConfigsSafeAtTerms
    <1>5. currentTerm[s] = currentTerm[n] BY <1>3
    <1>. QED BY <1>4, <1>5 DEF Quorums, TypeOK

COROLLARY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm ==
ASSUME TypeOK, Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A n \in Server : configTerm[p] >= configTerm[n]
BY ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF CSM!Reconfig, Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK

LEMMA ReconfigImpliesSameActiveConfigSet ==
ASSUME TypeOK, Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A n \in ActiveConfigSet' : n \in ActiveConfigSet
    <4>1. TAKE n \in ActiveConfigSet'
    <4>n. n \in Server BY <4>1 DEF ActiveConfigSet, ConfigDisabled, Quorums
    <4>2. PICK Q \in Quorums(config[n])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE n = p
        <5>1. \E nQ \in Quorums(config[n]) : \A q \in nQ : CV(n) = CV(q)
            BY QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt, Quorums, CV
        <5>. QED BY <5>1 DEF ActiveConfigSet, ConfigDisabled, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, CSM!Reconfig, TypeOK
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
                    <8>2. configVersion'[p] > configVersion'[n] BY <4>n, <8>1 DEF CSM!Reconfig, TypeOK
                    <8>3. CSM!NewerConfig(CV(p), CV(n))'
                        BY <4>n, <8>2 DEF CSM!Reconfig, CSM!NewerConfig, CV, Ind, PrimaryConfigTermEqualToCurrentTerm, TypeOK
                    <8>. QED BY <4>2, <7>1, <8>3
                <7>. QED BY <4>n, <7>3 DEF TypeOK
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
ASSUME TypeOK, Ind,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       CSM!Reconfig(p, newConfig)
PROVE \A s \in ActiveConfigSet' : config[s] = config[p]
PROOF
    <4>. TAKE s \in ActiveConfigSet'
    <4>. s \in ActiveConfigSet BY ReconfigImpliesSameActiveConfigSet
    <4>. s \in Server BY DEF ActiveConfigSet, ConfigDisabled
    <4>1. PICK Q \in Quorums(config[s]) : \A n \in Q : ~CSM!NewerConfig(CV(n), CV(s)) BY DEF ActiveConfigSet, ConfigDisabled
    <4>2. PICK pQ \in Quorums(config[p]) : \A q \in pQ : CVT(q) = CVT(p)
        BY QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt, CVT, TypeOK
    <4>3. PICK q \in pQ : ~CSM!NewerConfig(CV(q), CV(s))
        BY <4>1, <4>2, ReconfigImpliesInActiveConfigSet DEF Ind, ActiveConfigsOverlap, QuorumsOverlap
    <4>4. CSM!NewerOrEqualConfig(CV(s), CV(q))
        BY <4>2, <4>3, NewerIsNotSymmetric, QuorumsAreNonEmpty DEF Quorums, TypeOK
    <4>5. configTerm[p] = configTerm[s]
        <5>1. configTerm[p] >= configTerm[s] BY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm
        <5>2. configTerm[s] >= configTerm[q]
            BY <4>4, NewerOrEqualImpliesConfigTermGreaterThanOrEqual DEF Quorums, TypeOK
        <5>. QED BY <4>2, <5>1, <5>2 DEF CVT, TypeOK
    <4>6. configVersion[p] = configVersion[s]
        <5>1. configVersion[p] >= configVersion[s]
            BY <4>5 DEF CSM!Reconfig, Ind, PrimaryInTermContainsNewestConfigOfTerm, PrimaryConfigTermEqualToCurrentTerm
        <5>2. configVersion[s] >= configVersion[q]
            BY <4>2, <4>3, <4>4, <4>5, NewerOrEqualConfigWithSameTermImpliesGreaterOrEqualVersion DEF CVT, Quorums, TypeOK
        <5>. QED BY <4>2, <5>1, <5>2 DEF CVT, TypeOK
    <4>. QED BY <4>5, <4>6 DEF Ind, ConfigVersionAndTermUnique

LEMMA ConfigsIncreaseMonotonically ==
ASSUME TypeOK, Ind, Next
PROVE \A s \in Server : CSM!NewerOrEqualConfig(CV(s)', CV(s))
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        BY <1>1 DEF csmVars, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <2>1, ReconfigImpliesNewerOrEqualConfig
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <2>2, SendConfigImpliesNewerOrEqualConfig
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) BY <2>1
            <3>2. \A t \in Server : t # s => CV(t)' = CV(t) BY <3>1 DEF CSM!BecomeLeader, CV, TypeOK
            <3>3. CSM!NewerConfig(CV(s)', CV(s))
                <4>1. currentTerm[s] >= configTerm[s] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
                <4>2. configTerm'[s] > configTerm[s] BY <3>1, <4>1 DEF CSM!BecomeLeader, TypeOK
                <4>3. configVersion'[s] = configVersion[s] BY <3>1 DEF CSM!BecomeLeader
                <4>. QED BY <4>2, <4>3 DEF CSM!NewerConfig, CV, TypeOK
            <3>. QED BY <3>2, <3>3 DEF CSM!NewerOrEqualConfig
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF CSM!UpdateTerms, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

LEMMA SendConfigActiveConfigSetIdenticalExceptRecipient ==
ASSUME TypeOK, Ind, Next,
       NEW u \in Server,
       NEW v \in Server,
       CSM!SendConfig(u, v)
PROVE \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet
PROOF
    \* this took so much longer than it needed to...
    <4>1. TAKE n \in ActiveConfigSet'
    <4>2. SUFFICES ASSUME n # v
          PROVE n \in ActiveConfigSet BY <4>1
    <4>3. PICK Q \in Quorums(config[n])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>4. n \in Server /\ Q \in SUBSET Server BY <4>1, <4>3, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
    <4>5. \A q \in Q : CSM!NewerOrEqualConfig(CV(n), CV(q))' BY <4>3, <4>4, NewerIsNotSymmetricAndNext
    <4>6. \A q \in Q : CSM!NewerOrEqualConfig(CV(q)', CV(q)) BY <4>4, SendConfigImpliesNewerOrEqualConfig
    <4>7. \A q \in Q : CSM!NewerOrEqualConfig(CV(n)', CV(q)) BY <4>4, <4>5, <4>6, NewerOrEqualConfigTransitivityAndNext
    <4>8. CV(n) = CV(n)' BY <4>2 DEF CSM!SendConfig, CV, TypeOK
    <4>9. \A q \in Q : CSM!NewerOrEqualConfig(CV(n), CV(q)) BY <4>7, <4>8
    <4>10. \A q \in Q : ~CSM!NewerConfig(CV(q), CV(n)) BY <4>4, <4>9, NewerIsNotSymmetric
    <4>11. Q \in Quorums(config[n]) BY <4>2, <4>3, <4>4 DEF CSM!SendConfig, Quorums, TypeOK
    <4>. QED BY <4>10, <4>11 DEF ActiveConfigSet, ConfigDisabled

LEMMA BecomeLeaderActiveConfigSetIdentical ==
ASSUME TypeOK, Ind, Next,
       NEW p \in Server,
       \E Q \in Quorums(config[p]) : CSM!BecomeLeader(p, Q)
PROVE \A s \in ActiveConfigSet' : s \in ActiveConfigSet
PROOF
    <4>2. TAKE s \in ActiveConfigSet'
    <4>. CASE s # p
        <5>2. PICK Q \in Quorums(config[s])' : \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s))' BY <4>2 DEF ActiveConfigSet, ConfigDisabled
        <5>3. Q \in Quorums(config[s])' /\ \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s))' BY <5>2
        <5>4. s \in Server /\ Q \in SUBSET Server BY <4>2, <5>2, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
        <5>5. \A q \in Q : CSM!NewerOrEqualConfig(CV(s), CV(q))' BY <5>3, <5>4, NewerIsNotSymmetricAndNext
        <5>6. \A q \in Q : CSM!NewerOrEqualConfig(CV(q)', CV(q)) BY <5>4, ConfigsIncreaseMonotonically
        <5>7. \A q \in Q : CSM!NewerOrEqualConfig(CV(s)', CV(q)) BY <5>4, <5>5, <5>6, NewerOrEqualConfigTransitivityAndNext
        <5>8. CV(s) = CV(s)' BY DEF CSM!BecomeLeader, CV, TypeOK
        <5>9. \A q \in Q : CSM!NewerOrEqualConfig(CV(s), CV(q)) BY <5>7, <5>8
        <5>10. \A q \in Q : ~CSM!NewerConfig(CV(q), CV(s)) BY <5>4, <5>9, NewerIsNotSymmetric
        <5>11. Q \in Quorums(config[s]) BY <5>2, <5>3, <5>4 DEF CSM!BecomeLeader, Quorums, TypeOK
        <5>. QED BY <5>10, <5>11 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE s = p BY ElectedLeadersInActiveConfigSet
    <4>. QED OBVIOUS

LEMMA EmptyIdentical ==
ASSUME TypeOK,
       NEW s \in Server
       \*NEW lg \in [Server -> Seq(Nat)]
PROVE Empty(log[s]) <=> OSM!Empty(log[s])
BY DEF OSM!Empty, Empty, TypeOK

--------------------------------------------------------------------------------

(* IndAndNext *)

\* approximately 1-2 after 3-4 weeks of prep work
\* completed 6/23
\* alt: started 8/13
\* alt: completed 8/16
LEMMA OnePrimaryPerTermAndNext ==
ASSUME TypeOK, Ind, Next
PROVE OnePrimaryPerTerm'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, OnePrimaryPerTerm
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, OnePrimaryPerTerm
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, OnePrimaryPerTerm
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
                    <5>. QED BY <5>2, <3>5 DEF CSM!BecomeLeader, TypeOK
                <4>3. currentTerm[t] = configTerm[t]
                    <5>1. t \notin Q BY <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. state[t] = Primary BY <5>1, <3>5 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                <4>4. s \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet
                <4>5. \E n \in Q : currentTerm[n] >= configTerm[t] BY <3>2, <4>1, <4>4 DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. \E n \in Q : currentTerm[n] > currentTerm[s] BY <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
                <4>. QED BY <3>2, <4>1, <4>6 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
            \* basically a copy pasta job from the case above
            <3>. CASE \E Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q)
                <4>1. PICK Q \in Quorums(config[t]) : OSM!BecomeLeader(t, Q) /\ CSM!BecomeLeader(t, Q) OBVIOUS
                <4>2. currentTerm[s] > currentTerm[t]
                    <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. currentTerm[s] = currentTerm'[s] BY <4>1, <5>1 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2, <3>5 DEF CSM!BecomeLeader, TypeOK
                <4>3. currentTerm[s] = configTerm[s]
                    <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF CSM!BecomeLeader
                    <5>2. state[s] = Primary BY <5>1, <3>3, <3>5 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                <4>4. t \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet
                <4>5. \E n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <4>1, <4>4 DEF Ind, ActiveConfigsSafeAtTerms
                <4>6. \E n \in Q : currentTerm[n] > currentTerm[t] BY <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
                <4>. QED BY <3>2, <4>1, <4>6 DEF CSM!BecomeLeader, CSM!CanVoteForConfig, Quorums, TypeOK
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
                BY PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK
            <3>. CASE ~(\E u \in Server : OSM!UpdateTerms(u,t) /\ CSM!UpdateTerms(u,t))
                <4>1. currentTerm'[s] = currentTerm[s] /\ state[s] = Primary
                    <5>1. ~(\E u \in Server : OSM!UpdateTerms(u,s) /\ CSM!UpdateTerms(u,s))
                        BY PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                    <5>. QED BY <1>2, <2>2, <5>1 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                <4>2. currentTerm'[t] = currentTerm[t] /\ state'[t] = state[t]
                    BY <1>2, <2>2 DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
                <4>. QED BY <4>1, <4>2 DEF Ind, OnePrimaryPerTerm, TypeOK
            <3>. QED OBVIOUS
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next
    
\* approximately 30 min
\* completed 6/23
\* alt: no work needed
LEMMA PrimaryConfigTermEqualToCurrentTermAndNext ==
ASSUME TypeOK, Ind, Next
PROVE PrimaryConfigTermEqualToCurrentTerm'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, PrimaryConfigTermEqualToCurrentTerm, csmVars
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
            <3>. CASE p = s BY DEF CSM!BecomeLeader, TypeOK, Quorums
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
ASSUME TypeOK, Ind, Next,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       OSM!BecomeLeader(s, Q),
       CSM!BecomeLeader(s, Q),
       NEW t \in Server,
       <<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>
PROVE config'[s] = config'[t]
PROOF
    <1>1. \A n \in Server : currentTerm[s] >= configTerm[n] BY ElectedLeadersCurrentTermGreaterThanConfigTerms
    <1>. QED BY <1>1, TypeOKAndNext DEF CSM!BecomeLeader, TypeOK

\* approx 1 day
\* completed 6/29
\* alt: only needed to update ConfigVersionAndTermUniqueAndNext_BecomeLeader
LEMMA ConfigVersionAndTermUniqueAndNext ==
ASSUME TypeOK, Ind, Next
PROVE ConfigVersionAndTermUnique'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, ConfigVersionAndTermUnique, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, ConfigVersionAndTermUnique, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, ConfigVersionAndTermUnique, csmVars
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, ConfigVersionAndTermUnique, csmVars
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>. PICK p \in Server : \E newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>1. state[p] = Primary BY DEF CSM!Reconfig
            <3>2. \A s \in Server : configTerm[s] = configTerm[p] => configVersion[s] <= configVersion[p] BY <3>1 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm
            <3>3. \A s \in Server : (s # p /\ configTerm[s] = configTerm[p]) => configVersion'[s] < configVersion'[p] BY <3>2 DEF CSM!Reconfig, TypeOK
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
ASSUME TypeOK, Ind, Next
PROVE PrimaryInTermContainsNewestConfigOfTerm'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <1>1, <2>1 DEF OSM!ClientRequest, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <1>1, <2>2 DEF OSM!GetEntries, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF OSM!RollbackEntries, Ind, PrimaryInTermContainsNewestConfigOfTerm, csmVars
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
                    <5>2. configTerm'[t] = configTerm'[s] BY DEF CSM!SendConfig, TypeOK
                    <5>3. configTerm[p] = configTerm[t] BY <5>1, <5>2 DEF TypeOK
                    <5>4. configVersion[p] >= configVersion[t] BY <5>3 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm, CSM!SendConfig, TypeOK
                    <5>. QED BY <5>4 DEF CSM!SendConfig, TypeOK
                <4>. CASE t = p BY DEF CSM!SendConfig, TypeOK
                <4>. QED OBVIOUS
            <3>. CASE ~(\E t \in Server : CSM!SendConfig(t, s))
                <4>1. configVersion'[s] = configVersion[s] /\ configTerm'[s] = configTerm[s] BY <2>2 DEF CSM!SendConfig, TypeOK
                <4>2. configVersion'[p] = configVersion[p] /\ configTerm'[p] = configTerm[p] BY <2>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, TypeOK
                <4>3. state[p] = Primary /\ configTerm[s] = configTerm[p] BY <2>2, <4>1, <4>2, PrimaryAndSecondaryAreDifferent DEF CSM!SendConfig, TypeOK
                <4>4. configVersion[p] >= configVersion[s] BY <4>3 DEF Ind, PrimaryInTermContainsNewestConfigOfTerm
                <4>. QED BY <4>1, <4>2, <4>4
            <3>. QED OBVIOUS
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) BY <2>1
            <3>2. \A t \in Server : currentTerm[s] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
            <3>. QED BY <3>1, <3>2 DEF CSM!BecomeLeader, TypeOK, Ind, PrimaryInTermContainsNewestConfigOfTerm
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK, Ind, PrimaryInTermContainsNewestConfigOfTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


\* began: 8/16
\* finished: 8/24
LEMMA ActiveConfigsOverlapAndNext ==
ASSUME TypeOK, Ind, Next
PROVE ActiveConfigsOverlap'
PROOF
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
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF OSM!CommitEntry, Ind, ActiveConfigsOverlap, csmVars,
                QuorumsOverlap, Quorums, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            <3>p. PICK p \in Server, newConfig \in SUBSET Server : OplogCommitment(p) /\ CSM!Reconfig(p, newConfig) BY <2>1
            <3>1. p \in ActiveConfigSet BY <3>p, ReconfigImpliesInActiveConfigSet
            <3>2. \A s \in ActiveConfigSet' : config[s] = config[p] BY <3>p, ReconfigImpliesActiveConfigSetHaveSameConfig
            <3>3. \A t \in ActiveConfigSet' : config'[t] = newConfig \/ config'[t] = config[p]
                BY <3>p, <3>2 DEF CSM!Reconfig, TypeOK
            <3>4. QuorumsOverlap(config[p], newConfig) BY <3>p, QuorumsOverlapIdentical DEF CSM!Reconfig, TypeOK
            <3>. QED BY <3>p, <3>3, <3>4, QuorumsOverlapIsCommutative, StaticQuorumsOverlap DEF ActiveConfigsOverlap, QuorumsOverlap, Quorums, TypeOK
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            <3>1. PICK u \in Server, v \in Server : CSM!SendConfig(u, v) BY <2>2
            <3>2. \A n \in Server : n # v => config[n] = config'[n] BY <3>1 DEF CSM!SendConfig, TypeOK
            <3>3. \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet BY <3>1, SendConfigActiveConfigSetIdenticalExceptRecipient
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
                    <5>4. config'[s] = config[u] BY <3>1, <4>2, TypeOKAndNext DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <5>2, <5>3, <5>4
                <4>. CASE u \notin ActiveConfigSet'
                    BY <3>1, <4>1, <4>2 DEF CSM!SendConfig, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
                <4>. QED OBVIOUS
            <3>6. \A s,t \in ActiveConfigSet' : (s # v /\ t = v) => QuorumsOverlap(config[s], config[t])'
                BY <3>5, QuorumsOverlapIsCommutative, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, TypeOK
            <3>7. \A s,t \in ActiveConfigSet' : (s = v /\ t = v) => QuorumsOverlap(config[s], config[t])'
                BY StaticQuorumsOverlap, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, QuorumsOverlap, TypeOK
            <3>. QED BY <3>4, <3>5, <3>6, <3>7 DEF ActiveConfigsOverlap
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. \A s \in Server : Quorums(config'[s]) = Quorums(config[s]) BY <2>1 DEF CSM!BecomeLeader, Quorums
            <3>2. \A s,t \in Server : QuorumsOverlap(config[s],config[t]) <=> QuorumsOverlap(config[s],config[t])' BY <3>1 DEF QuorumsOverlap
            <3>3. \A s \in ActiveConfigSet' : s \in ActiveConfigSet BY <2>1, BecomeLeaderActiveConfigSetIdentical
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
ASSUME TypeOK, Ind, Next
PROVE ActiveConfigsSafeAtTerms'
PROOF
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
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
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
            <3>4. config[t] = config[p] BY <3>p, <3>3, ReconfigImpliesActiveConfigSetHaveSameConfig
            <3>5. CASE t # p
                <4>1. config'[t] = config[t] /\ config'[t] = config[p] BY <3>p, <3>4, <3>5 DEF CSM!Reconfig, TypeOK
                <4>2. PICK pQ \in Quorums(config[p]) : \A n \in pQ : CVT(n) = CVT(p)
                    BY <3>p, QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt, CVT
                <4>3. TAKE tQ \in Quorums(config'[t])
                <4>4. tQ \in Quorums(config[t]) BY <4>1, <4>3
                <4>5. QuorumsOverlap(config[t], config[p])
                    BY <3>3, ReconfigImpliesSameActiveConfigSet, <3>p, ReconfigImpliesInActiveConfigSet DEF Ind, ActiveConfigsOverlap
                <4>6. PICK n \in tQ : n \in pQ BY <4>2, <4>4, <4>5 DEF QuorumsOverlap
                <4>7. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>2, <4>6, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF CVT
                <4>8. currentTerm'[n] >= configTerm'[s]
                    BY <3>p, <3>2, <3>3, <4>4, <4>6, <4>7, ReconfigImpliesConfigTermUnchanged DEF CSM!Reconfig, Quorums, TypeOK
                <4>. QED BY <3>1, <3>2, <3>3, <4>3, <4>8
            <3>6. CASE t = p
                <4>1. PICK pQ \in Quorums(config[p]) : \A n \in pQ : CVT(n) = CVT(p)
                    BY <3>p, QuorumsIdentical DEF CSM!Reconfig, CSM!ConfigIsCommitted, CSM!QuorumsAt, CVT
                <4>2. config'[t] = newConfig BY <3>p, <3>6 DEF CSM!Reconfig, TypeOK
                <4>3. TAKE tQ \in Quorums(config'[t])
                <4>4. QuorumsOverlap(config[p], newConfig) BY <3>p, <4>1, <4>2, <4>3, QuorumsOverlapIdentical DEF CSM!Reconfig, TypeOK
                <4>5. PICK n \in tQ : n \in pQ BY <4>1, <4>2, <4>3, <4>4 DEF QuorumsOverlap
                <4>6. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>1, <4>5, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF CVT
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
                <4>1. t \in ActiveConfigSet BY <3>1, <3>4, <3>5, SendConfigActiveConfigSetIdenticalExceptRecipient
                <4>2. CASE s # v
                    <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s] BY <4>1 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>. QED BY <3>1, <3>5, <4>2, <5>1 DEF CSM!SendConfig, TypeOK
                <4>3. CASE s = v
                    <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[u] BY <3>1, <4>1 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>2. configTerm'[s] = configTerm[u] BY <3>1, <4>3 DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <3>1, <3>5, <4>2, <5>1, <5>2 DEF CSM!SendConfig, TypeOK
                <4>. QED BY <4>2, <4>3
            <3>6. CASE t = v
                <4>u. u # v BY <3>1 DEF CSM!SendConfig, CSM!IsNewerConfig, TypeOK
                <4>1. u \in ActiveConfigSet' BY <3>1, <3>6 DEF CSM!SendConfig, ActiveConfigSet, ConfigDisabled, CSM!NewerConfig, CV, TypeOK
                <4>2. u \in ActiveConfigSet BY <3>1, <4>1, <4>u, SendConfigActiveConfigSetIdenticalExceptRecipient
                <4>3. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[s] BY <3>1, <4>2 DEF Ind, ActiveConfigsSafeAtTerms
                <4>4. config'[t] = config[u] BY <3>1, <3>6 DEF CSM!SendConfig, TypeOK
                <4>5. CASE s # v
                    <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                        BY <3>1, <4>u, <4>3, <4>5 DEF CSM!SendConfig, TypeOK
                    <5>. QED BY <4>4, <5>1
                <4>6. CASE s = v
                    <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[u]
                        BY <3>1, <4>2 DEF Ind, ActiveConfigsSafeAtTerms
                    <5>. QED BY <3>1, <4>4, <4>6, <5>1 DEF CSM!SendConfig, TypeOK
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
            <3>4. t \in ActiveConfigSet BY <2>1, <3>3, BecomeLeaderActiveConfigSetIdentical
            <3>5. TAKE Q \in Quorums(config'[t])
            <3>6. Q \in Quorums(config[t]) BY <2>1, <3>4, <3>5 DEF CSM!BecomeLeader, ActiveConfigSet, ConfigDisabled
            <3>7. PICK n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <3>4, <3>6 DEF Ind, ActiveConfigsSafeAtTerms
            <3>n. n \in Server BY <3>6, <3>7 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
            <3>8. CASE n \in pQ
                <4>1. currentTerm'[p] >= configTerm'[s]
                    <5>1. currentTerm[p] >= configTerm[s] BY <3>p, ElectedLeadersCurrentTermGreaterThanConfigTerms
                    <5>2. CASE s # p
                        <6>1. configTerm'[s] = configTerm[s] BY <3>p, <5>2 DEF CSM!BecomeLeader, TypeOK
                        <6>2. currentTerm'[p] >= currentTerm[p] BY <3>p DEF CSM!BecomeLeader, TypeOK
                        <6>. QED BY <5>1, <6>1, <6>2, TypeOKAndNext DEF TypeOK
                    <5>3. CASE s = p BY <3>p, <5>3 DEF CSM!BecomeLeader, TypeOK
                    <5>. QED BY <5>2, <5>3
                <4>2. currentTerm'[n] = currentTerm'[p] BY <3>p, <3>q, <3>8 DEF CSM!BecomeLeader, Quorums, TypeOK
                <4>. QED BY <3>7, <4>1, <4>2
            <3>9. CASE n \notin pQ
                <4>1. currentTerm'[n] = currentTerm[n] BY <3>p, <3>q, <3>n, <3>9 DEF CSM!BecomeLeader, TypeOK
                <4>2. CASE s # p BY <3>p, <3>7, <4>1, <4>2 DEF CSM!BecomeLeader, TypeOK
                <4>3. CASE s = p
                    \* this case is very interesting because we rely on the currentTerm update \A q \in pQ, in particular
                    \* \A q \in pQ : q # p, I wouldn't expect the update on currentTerm to be atomic but it is in this
                    \* protocol.  see <5>4.
                    <5>1. s \in ActiveConfigSet BY <3>p, <4>3, ElectedLeadersInActiveConfigSet
                    <5>2. QuorumsOverlap(config[t], config[s]) BY <3>4, <5>1 DEF Ind, ActiveConfigsOverlap
                    <5>3. PICK q \in pQ : q \in Q BY <3>6, <3>p, <3>q, <4>3, <5>2 DEF QuorumsOverlap
                    <5>4. currentTerm'[q] >= currentTerm'[s] \* their currentTerm's are equal because the update on q's
                                                             \* currentTerm is atomic (as well as p's)
                        BY <3>p, <3>q, <4>3, <5>3, TypeOKAndNext DEF CSM!BecomeLeader, Quorums, TypeOK
                    <5>5. currentTerm'[s] = configTerm'[s] BY <3>p, <4>3 DEF CSM!BecomeLeader, TypeOK
                    <5>6. q \in Server BY <3>4, <3>6, <5>3 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
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
                <4>1. n \in Server BY <3>5, <3>7, <3>8 DEF Quorums, TypeOK
                <4>. QED BY <2>2, <4>1, TypeOKAndNext DEF CSM!UpdateTerms, CSM!UpdateTermsExpr, TypeOK
            <3>. QED BY <2>2, <3>5, <3>9, <3>8, <3>9, TypeOKAndNext DEF CSM!UpdateTerms, Quorums, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* 2-4 hours
LEMMA LogMatchingAndNext_ClientRequest ==
ASSUME TypeOK, Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       OSM!ClientRequest(s),
       s # t,
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <4>. SUFFICES ASSUME i > 1
         PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
         BY TypeOKAndNext DEF OSM!ClientRequest, TypeOK
    <4>1. log[s][i-1] = log'[s][i-1] BY DEF OSM!ClientRequest, TypeOK
    <4>2. log[t][i] = log'[t][i] BY DEF OSM!ClientRequest, TypeOK
    <4>3. CASE log[s][i-1] = log[t][i-1]
        BY <4>3 DEF Ind, LogMatching, EqualUpTo, OSM!ClientRequest, TypeOK
    <4>4. CASE log[s][i-1] # log[t][i-1]
        \* proof by contradiction, we will see that s is a primary without the log entries it created
        <5>1. Len(log[s]) = i-1
            <6>1. SUFFICES ASSUME Len(log[s]) # i-1
                  PROVE FALSE OBVIOUS
            <6>2. i-1 \in DOMAIN log[s] BY <4>4 DEF OSM!ClientRequest, TypeOK
            <6>3. Len(log[s]) > i-1 BY <4>4, <6>1, <6>2 DEF TypeOK
            <6>4. log[s][i] = log'[s][i] BY <6>3 DEF OSM!ClientRequest, TypeOK
            <6>5. log[s][i] = log[t][i] BY <4>2, <6>4 DEF TypeOK
            <6>6. log[s][i-1] = log[t][i-1]
                <7>1. i \in (DOMAIN log[s] \cap DOMAIN log[t]) BY <6>3 DEF OSM!ClientRequest, TypeOK
                <7>2. i-1 > 0 /\ i-1 <= i BY <6>3, TypeOKAndNext DEF OSM!ClientRequest, TypeOK
                <7>. QED BY <6>5, <7>1, <7>2 DEF Ind, LogMatching, EqualUpTo, TypeOK
            <6>. QED BY <4>4, <6>6 DEF TypeOK
        <5>2. log'[s][i] = currentTerm[s] BY <5>1 DEF OSM!ClientRequest
        <5>3. log[t][i] = currentTerm[s] BY <5>2 DEF OSM!ClientRequest
        <5>. QED BY <5>1, <5>3 DEF Ind, PrimaryHasEntriesItCreated, InLog, OSM!ClientRequest
    <4>. QED BY <4>3, <4>4

LEMMA LogMatchingAndNext_GetEntries ==
ASSUME TypeOK, Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       OSM!GetEntries(s, t),
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <1>1. TAKE j \in Nat
    <1>2. CASE j = i BY <1>2
    <1>3. CASE j < i
        <2>1. SUFFICES ASSUME ~Empty(log[s])
              PROVE (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
              BY DEF OSM!GetEntries, Empty, TypeOK
        <2>.  DEFINE sLastIdx == Len(log[s])
        <2>3. log[s][sLastIdx] = log[t][sLastIdx] BY <2>1, EmptyIdentical DEF OSM!GetEntries
        <2>4. j <= sLastIdx BY <1>3, <2>1 DEF OSM!GetEntries, Empty, TypeOK
        <2>. QED BY <1>1, <2>3, <2>4 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3 DEF OSM!GetEntries, TypeOK

LEMMA LogMatchingAndNext_GetEntriesOneOutside ==
ASSUME TypeOK, Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       NEW v \in Server,
       OSM!GetEntries(u, v),
       s # u, s # v,
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <1>1. TAKE j \in Nat
    <1>2. CASE j = i BY <1>2
    <1>3. CASE j < i
        <2>1. SUFFICES ASSUME ~Empty(log[s])
              PROVE (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
              BY DEF OSM!GetEntries, Empty, TypeOK
        <2>2. CASE t = u BY <1>1, <1>3, <2>1, <2>2 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, Empty, OSM!Empty, TypeOK
        <2>3. CASE t # u BY <1>1, <1>3, <2>1, <2>3 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, TypeOK
        <2>. QED BY <2>2, <2>3
    <1>. QED BY <1>1, <1>2, <1>3 DEF OSM!GetEntries, TypeOK

\* began: 8/26 (kinda on 8/24 at like 11pm but not really)
\* finished: 8/26
\* took a few hours, maybe 2-5
LEMMA LogMatchingAndNext ==
ASSUME TypeOK, Ind, Next
PROVE LogMatching'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME NEW s \in Server, NEW t \in Server,
                                  NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
                                  log'[s][i] = log'[t][i]
                  PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
                  BY DEF LogMatching, EqualUpTo
            <3>2. SUFFICES ASSUME i > 1
                  PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
                  BY <3>1, TypeOKAndNext DEF OSM!ClientRequest, TypeOK
            <3>3. CASE s = t BY <3>1, <3>2, <3>3 DEF OSM!ClientRequest, TypeOK
            <3>4. CASE OSM!ClientRequest(s) /\ s # t BY <3>1, <3>2, <3>4, LogMatchingAndNext_ClientRequest
            <3>5. CASE OSM!ClientRequest(t) /\ s # t BY <3>1, <3>2, <3>5, LogMatchingAndNext_ClientRequest
            <3>6. CASE ~OSM!ClientRequest(s) /\ ~OSM!ClientRequest(t) /\ s # t
                <4>1. log[s][i] = log[t][i] BY <2>1, <3>1, <3>6 DEF OSM!ClientRequest, TypeOK
                <4>2. i \in (DOMAIN log[s] \cap DOMAIN log[t]) BY <2>1, <3>1, <3>6 DEF OSM!ClientRequest, TypeOK
                <4>3. \A j \in Nat : (j > 0 /\ j <= i) => log[s][j] = log[t][j] BY <3>1, <4>1, <4>2 DEF Ind, LogMatching, EqualUpTo
                <4>. QED BY <2>1, <3>1, <3>6, <4>3 DEF OSM!ClientRequest, TypeOK
            <3>. QED BY <3>3, <3>4, <3>5, <3>6
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2, LogMatchingAndNext_GetEntries, LogMatchingAndNext_GetEntriesOneOutside DEF LogMatching, EqualUpTo
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF Ind, LogMatching, EqualUpTo, OSM!RollbackEntries, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            \* no idea why TLAPS needs me to break this out
            <3>1. UNCHANGED log BY <2>4 DEF OSM!CommitEntry, TypeOK
            <3>. QED BY <3>1 DEF Ind, LogMatching, EqualUpTo
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, LogMatching, EqualUpTo
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. CASE UNCHANGED log BY <3>2 DEF Ind, LogMatching, EqualUpTo
            <3>3. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                <4>1. \A t \in Server : t # p => (\A i \in DOMAIN log[t] : LastTerm(log'[p]) > log'[t][i])
                    <5>1. \A t \in Server : currentTerm[p] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
                    <5>2. \A t \in Server : \A i \in DOMAIN log[t] : currentTerm[p] >= log[t][i]
                        BY <3>1, <5>1 DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
                    <5>3. LastTerm(log'[p]) > currentTerm[p] BY <3>1, <3>3, <5>2, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>4. \A t \in Server : \A i \in DOMAIN log[t] : LastTerm(log'[p]) > log[t][i]
                        BY <3>1, <5>2, <5>3, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>. QED BY <3>1, <5>4, TypeOKAndNext DEF OSM!BecomeLeader, LastTerm, TypeOK
                <4>2. \A t \in Server : \A i \in DOMAIN log[t] : log'[t][i] = log[t][i] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2, TypeOKAndNext DEF Ind, LogMatching, EqualUpTo, OSM!BecomeLeader, LastTerm, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF Ind, LogMatching, EqualUpTo, OSM!UpdateTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/26
\* finished: 8/26
\* about 45 min
LEMMA TermsOfEntriesGrowMonotonicallyAndNext ==
ASSUME TypeOK, Ind, Next
PROVE TermsOfEntriesGrowMonotonically'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF Ind, TermsOfEntriesGrowMonotonically, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, OSM!ClientRequest, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK s \in Server, t \in Server : OSM!GetEntries(s, t) BY <2>2
            <3>.  DEFINE sLastIdx == Len(log'[s])
            <3>2. SUFFICES ASSUME sLastIdx > 1
                  PROVE TermsOfEntriesGrowMonotonically'
                  BY <3>1 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
            <3>3. log'[s][sLastIdx] >= log'[s][sLastIdx-1]
                <4>1. log'[s][sLastIdx] = log'[t][sLastIdx] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. log'[t][sLastIdx] = log[t][sLastIdx] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. log[t][sLastIdx] >= log[t][sLastIdx-1] BY <3>1, <3>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
                <4>4. log[t][sLastIdx-1] = log[s][sLastIdx-1] BY <3>1, <3>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>5. log'[s][sLastIdx-1] = log[s][sLastIdx-1] BY <3>1, <3>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>. QED BY <3>1, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5 DEF OSM!GetEntries, OSM!Empty, TypeOK
            <3>. QED BY <3>1, <3>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!RollbackEntries, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!CommitEntry, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, TermsOfEntriesGrowMonotonically
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. CASE UNCHANGED log BY <3>2 DEF Ind, TermsOfEntriesGrowMonotonically
            <3>3. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                <4>.  DEFINE pLastIdx == Len(log'[p])
                <4>1. \A i \in DOMAIN log'[p] : log'[p][pLastIdx] >= log'[p][i]
                    <5>1. \A t \in Server : currentTerm[p] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
                    <5>2. \A t \in Server : \A i \in DOMAIN log[t] : currentTerm[p] >= log[t][i]
                        BY <3>1, <5>1 DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
                    <5>3. LastTerm(log'[p]) > currentTerm[p] BY <3>1, <3>3, <5>2, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>4. \A i \in DOMAIN log[p] : log'[p][pLastIdx] > log[p][i] BY <3>1, <5>2, <5>3, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>5. \A i \in DOMAIN log'[p] : i < pLastIdx => log'[p][i] = log[p][i] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                    <5>. QED BY <3>1, <5>4, <5>5 DEF OSM!BecomeLeader, TypeOK
                <4>2. \A t \in Server : t # p => log'[t] = log[t] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <3>3, <4>1, <4>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!BecomeLeader, OSM!Empty, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!UpdateTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* never turned out to be useful.
LEMMA PrimaryHasEntriesItCreatedAlt ==
ASSUME TypeOK, PrimaryHasEntriesItCreated
PROVE \A s,t \in Server : state[s] = Primary
        => \A k \in DOMAIN log[t] : (log[t][k] = currentTerm[s]) => InLog(<<k,log[t][k]>>, s)
PROOF BY DEF TypeOK, PrimaryHasEntriesItCreated

\* began: 8/26
\* finished: 8/27
LEMMA PrimaryHasEntriesItCreatedAndNext ==
ASSUME TypeOK, Ind, Next
PROVE PrimaryHasEntriesItCreated'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. CASE ~OSM!ClientRequest(s)
                <4>1. state[s] = Primary BY <2>1, <3>1, <3>2 DEF OSM!ClientRequest, TypeOK
                <4>2. CASE ~OSM!ClientRequest(t)
                    <5>1. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <2>1, <3>1, <3>2, <4>2 DEF OSM!ClientRequest, InLog, TypeOK
                    <5>2. k \in DOMAIN log[t] BY <2>1, <3>1, <3>2, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>. QED BY <3>1, <4>1, <5>1, <5>2 DEF Ind, PrimaryHasEntriesItCreated, InLog, TypeOK
                <4>3. CASE OSM!ClientRequest(t)
                    <5>1. CASE k = Len(log'[t])
                        <6>1. currentTerm[s] = currentTerm[t] BY <3>1, <3>2, <4>3, <5>1 DEF OSM!ClientRequest, TypeOK
                        <6>2. s # t BY <3>2, <4>3 DEF OSM!ClientRequest, TypeOK
                        <6>3. state[s] = Primary /\ state[t] = Primary BY <4>1, <4>3 DEF OSM!ClientRequest
                        <6>. QED BY <6>1, <6>2, <6>3 DEF Ind, OnePrimaryPerTerm
                    <5>2. CASE k < Len(log'[t])
                        <6>1. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                            BY <3>1, <3>2, <4>3, <5>2 DEF OSM!ClientRequest, InLog, TypeOK
                        <6>2. k \in DOMAIN log[t] BY <3>1, <4>3, <5>2 DEF OSM!ClientRequest, TypeOK
                        <6>. QED BY <3>1, <4>1, <6>1, <6>2 DEF Ind, PrimaryHasEntriesItCreated, TypeOK
                    <5>. QED BY <3>1, <5>1, <5>2 DEF OSM!ClientRequest, TypeOK
                <4>. QED BY <4>2, <4>3
            <3>3. CASE OSM!ClientRequest(s)
                <4>1. SUFFICES ASSUME s # t
                      PROVE FALSE BY <3>1, <3>3 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>2. k \in DOMAIN log[t] BY <3>1, <3>3, <4>1 DEF OSM!ClientRequest, TypeOK
                <4>3. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                    BY <3>1, <3>3, <4>1 DEF OSM!ClientRequest, InLog, TypeOK
                <4>. QED BY <3>1, <3>3, <4>1, <4>2, <4>3 DEF Ind, PrimaryHasEntriesItCreated, InLog, OSM!ClientRequest, TypeOK
            <3>. QED BY <3>2, <3>3
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. SUFFICES ASSUME s # t
                  PROVE FALSE BY <3>1 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>3. PICK u,v \in Server : OSM!GetEntries(u, v) BY <2>2
            <3>4. CASE t = u
                <4>1. CASE k = Len(log'[t])
                    <5>1. k \in DOMAIN log[v] BY <3>1, <3>3, <3>4 DEF OSM!GetEntries, TypeOK
                    <5>2. log[v][k] = currentTerm[s] /\ ~InLog(<<k,log[v][k]>>, s)
                        BY <3>1, <3>3, <3>4, <4>1 DEF OSM!GetEntries, OSM!Empty, InLog, TypeOK
                    <5>. QED BY <3>1, <3>2, <3>3, <5>1, <5>2 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>2. CASE k < Len(log'[t])
                    <5>1. k \in DOMAIN log[t] BY <3>1, <3>3, <4>2 DEF OSM!GetEntries, TypeOK
                    <5>2. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <3>1, <3>3, <3>4, <4>2 DEF OSM!GetEntries, OSM!Empty, InLog, TypeOK
                    <5>. QED BY <3>1, <3>2, <3>3, <5>1, <5>2 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>. QED BY <3>1, <3>3, <3>4, <4>1, <4>2 DEF OSM!GetEntries, TypeOK
            <3>5. CASE t # u BY <3>1, <3>2, <3>3, <3>5 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>. QED BY <3>4, <3>5
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. PICK u, v \in Server : OSM!RollbackEntries(u, v) BY <2>3
            <3>3. s # u BY <3>1, <3>2, PrimaryAndSecondaryAreDifferent DEF OSM!RollbackEntries, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF OSM!RollbackEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A s \in Server : \A i \in DOMAIN log[s] : \E t \in Server : configTerm[t] >= log[s][i] BY DEF Ind, LogEntryInTermImpliesConfigInTerm
            <3>3. \A s \in Server : \A i \in DOMAIN log[s] : currentTerm[p] >= log[s][i] BY <3>1, <3>2, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
            <3>4. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>5. SUFFICES ASSUME s # t
                  PROVE FALSE BY <3>1, <3>4 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>6. CASE t # p BY <3>1, <3>3, <3>4, <3>6 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>7. CASE t = p
                <4>q. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <3>1
                <4>1. s \notin Q BY <3>1, <3>4, <3>5, <3>7, <4>q, PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader, TypeOK
                <4>2. CASE k = Len(log'[p]) /\ log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    <5>1. currentTerm'[s] = currentTerm[p] + 1 BY <3>1, <3>4, <3>7, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>2. currentTerm[s] =  currentTerm[p] + 1 BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <5>1 DEF OSM!BecomeLeader, TypeOK
                    <5>3. state[s] = Primary BY <3>1, <3>4, <3>5, <3>7 DEF OSM!BecomeLeader, TypeOK
                    <5>4. configTerm[s] = currentTerm[p] + 1 BY <5>2, <5>3 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                    <5>. QED BY <3>1, <5>4, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
                <4>3. CASE k < Len(log'[t]) \/ UNCHANGED log
                    <5>1. currentTerm[s] = currentTerm'[s] BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <4>3 DEF OSM!BecomeLeader, TypeOK
                    <5>2. k \in DOMAIN log[t] BY <3>1, <3>4, <3>7, <4>3 DEF OSM!BecomeLeader, TypeOK
                    <5>3. log[t][k] = log'[t][k]
                        \* truly obnoxious that I need to split this one up
                        <6>1. CASE UNCHANGED log BY <6>1, <3>1, <3>4, <3>5, <3>7, <4>3 DEF OSM!BecomeLeader, TypeOK
                        <6>2. CASE k < Len(log'[t]) /\ log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                            BY <3>1, <3>4, <3>5, <3>7, <4>3, <6>2 DEF OSM!BecomeLeader, TypeOK
                        <6>. QED BY <3>1, <3>7, <4>3, <6>1, <6>2 DEF OSM!BecomeLeader, TypeOK
                    <5>4. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <4>3, <5>3 DEF OSM!BecomeLeader, InLog, TypeOK
                    <5>. QED BY <3>1, <3>4, <5>2, <5>4 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>. QED BY <3>1, <3>4, <3>7, <4>2, <4>3 DEF OSM!BecomeLeader, TypeOK
            <3>. QED BY <3>6, <3>7
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* finished: 8/27
\* approx 20 min
LEMMA CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext ==
ASSUME TypeOK, Ind, Next
PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!GetEntries, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3, PrimaryAndSecondaryAreDifferent DEF OSM!RollbackEntries, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            \* the result is obvious for any server not becoming the new leader
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A i \in DOMAIN log[p] : currentTerm[p] >= log[p][i]
                BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
            <3>3. \A i \in DOMAIN log'[p] : currentTerm'[p] >= log'[p][i]
                <4>1. CASE UNCHANGED log BY <3>1, <3>2, <4>1 DEF OSM!BecomeLeader, TypeOK
                <4>2. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    <5>1. \A i \in DOMAIN log'[p] : i = Len(log'[p]) => log'[p][i] = currentTerm'[p] BY <3>1, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>2. \A i \in DOMAIN log'[p] : i < Len(log'[p]) => log'[p][i] = log[p][i] BY <3>1, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>3. \A i \in DOMAIN log'[p] : i < Len(log'[p]) => log'[p][i] <= currentTerm'[p] BY <3>1, <3>2, <5>2 DEF OSM!BecomeLeader, TypeOK
                    <5>. QED BY <3>1, <3>2, <5>1, <5>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2 DEF OSM!BecomeLeader, TypeOK
            <3>. QED BY <3>1, <3>3, PrimaryAndSecondaryAreDifferent DEF Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* finished: 8/27
\* approx 3 hours
LEMMA LogEntryInTermImpliesConfigInTermAndNext ==
ASSUME TypeOK, Ind, Next
PROVE LogEntryInTermImpliesConfigInTerm'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. PICK s \in Server : OSM!ClientRequest(s) BY <2>1
            <3>2. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => configTerm'[s] = log'[s][i]
                BY <1>1, <3>1 DEF csmVars, OSM!ClientRequest, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
            <3>3. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => configTerm[s] >= log[s][i]
                BY <3>1 DEF OSM!ClientRequest, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, PrimaryConfigTermEqualToCurrentTerm
            <3>4. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => configTerm'[s] >= log'[s][i]
                BY <1>1, <3>1, <3>3 DEF csmVars, OSM!ClientRequest, TypeOK
            <3>. QED BY <1>1, <3>1, <3>2, <3>4 DEF csmVars, OSM!ClientRequest, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK s,t \in Server : OSM!GetEntries(s, t) BY <2>2
            <3>2. \A i \in DOMAIN log'[s] : i <= Len(log'[s]) => \E u \in Server : configTerm'[u] >= log'[s][i]
                <4>1. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => \E u \in Server : configTerm[u] >= log[s][i]
                    \* absolutely ridiculous that i need to spell this out
                    <5>1. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => s \in Server /\ i \in DOMAIN log[s]
                        BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                    <5>. QED BY <3>1, <5>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                <4>2. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => log[t][i] = log'[s][i] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => \E u \in Server : configTerm[u] >= log'[s][i]
                    BY <3>1, <4>2 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                <4>. QED BY <1>1, <3>1, <4>1, <4>3, TypeOKAndNext DEF csmVars, OSM!GetEntries, OSM!Empty, TypeOK
            <3>3. \A u \in Server : u # s => \A i \in DOMAIN log'[u] : \E v \in Server : configTerm'[v] >= log'[u][i]
                BY <1>1, <3>1 DEF csmVars, OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
            <3>. QED BY <3>2, <3>3 DEF LogEntryInTermImpliesConfigInTerm
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF csmVars, OSM!RollbackEntries, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF csmVars, OSM!CommitEntry, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1, ConfigsIncreaseMonotonically DEF osmVars, CSM!Reconfig, TypeOK,
                Ind, LogEntryInTermImpliesConfigInTerm, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2, ConfigsIncreaseMonotonically DEF osmVars, CSM!SendConfig, TypeOK,
                Ind, LogEntryInTermImpliesConfigInTerm, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A s \in Server : \A i \in DOMAIN log[s] : currentTerm[p] >= log[s][i]
                BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
            <3>3. \A s \in Server : s # p => \A i \in DOMAIN log'[s] : currentTerm'[p] >= log'[s][i]
                BY <3>1, <3>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>4. \A i \in DOMAIN log'[p] : currentTerm'[p] >= log'[p][i]
                <4>1. CASE UNCHANGED log
                    <5>1. currentTerm'[p] >= currentTerm[p]
                        BY <3>1, ConfigsIncreaseMonotonically DEF OSM!BecomeLeader, CSM!BecomeLeader, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
                    <5>. QED BY <3>1, <3>2, <4>1, <5>1 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
                <4>2. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    BY <3>1, <3>2, <4>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>. QED BY <3>1, <3>3, <3>4 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK, LogEntryInTermImpliesConfigInTerm
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, CSM!UpdateTerms, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* UniformLogEntriesInTerm notes:
\* DEF boundary == an index i in a server s' log where log[s][i] # log[s][i-1]
\* DEF local boundary == a boundary for a single server
\* DEF global boundary == a boundary for all servers
\* UniformLogEntriesInTerm in a nutshell:
\*   for all local log term boundaries, the boundary is in fact global
\* 
LEMMA UniformLogEntriesInTermAndNext ==
ASSUME TypeOK, Ind, Next
PROVE UniformLogEntriesInTerm'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. PICK p \in Server : OSM!ClientRequest(p) BY <2>1
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            \* this is unneeded, but it helps me to clearly see the proof goal
            \* after DeMorgan'ing the 2nd part of the 'implies' we see the local (s) to global (\A t) boundary stipulation
            <3>f. SUFFICES ASSUME TRUE
                  \*PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)'
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            
            \* this proof really ought to be cleaned up.  here's a first attempt..
            (*
            <3>6. \A u \in Server : (u # p) => log'[u] = log[u] BY <3>1 DEF OSM!ClientRequest, TypeOK
            <3>7. \A j \in DOMAIN log'[p] : (j < Len(log'[p])) => log[p][j] = log'[p][j] BY <3>1 DEF OSM!ClientRequest, TypeOK
            <3>8. log'[p][Len(log'[p])] = currentTerm[p] BY <3>1 DEF OSM!ClientRequest, TypeOK
            <3>9. \A u \in Server : ~\E k \in DOMAIN log[u] : log[u][k] = currentTerm[p] /\ ~InLog(<<k,log[u][k]>>, p)
                BY <3>1 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>. QED BY <3>1, <3>6, <3>7, <3>8, <3>9 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm, InLog*)
            
            <3>6. CASE s = p
                <4>1. CASE i = Len(log'[p])
                    <5>1. SUFFICES ASSUME (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])',
                                          NEW k \in DOMAIN log'[t], log'[t][k] = log'[s][i], k < i
                          PROVE FALSE OBVIOUS
                    \*<5>2. SUFFICES ASSUME p # t
                    \*      PROVE FALSE BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, TypeOK
                    <5>2. k \in DOMAIN log[t] BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, TypeOK
                    <5>3. log[t][k] = currentTerm[p] BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, TypeOK
                    <5>4. ~InLog(<<k, log[t][k]>>, p) BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, InLog, TypeOK
                    <5>. QED BY <3>1, <3>4, <5>2, <5>3, <5>4 DEF Ind, PrimaryHasEntriesItCreated, OSM!ClientRequest, InLog, TypeOK
                <4>2. CASE i < Len(log'[p])
                    <5>1. i \in DOMAIN log[p] BY <3>1, <3>5, <3>6, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>2. log[p][i] = log'[p][i] BY <3>1, <3>5, <3>6, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>3. (\A j \in DOMAIN log[p] : (j < i) => log[p][j] # log[p][i]) => (~\E k \in DOMAIN log[t] : log[t][k] = log[p][i] /\ k < i)
                        BY <3>1, <3>5, <3>6, <4>2, <5>1, <5>2 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
                    <5>i. (DOMAIN log'[p] \cap DOMAIN log[p]) = DOMAIN log[p] BY <3>1 DEF OSM!ClientRequest, TypeOK
                    <5>4. \A j \in DOMAIN log'[p] : (j < i) => j \in DOMAIN log[p] BY <3>1, <3>6, <4>2, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>5. \A j \in DOMAIN log[p] : (j < i) => log[p][j] = log'[p][j] BY <3>1, <3>6, <4>2, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>6. (\A j \in DOMAIN log[p] : (j < i) => log[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>1, <5>3 DEF OSM!ClientRequest, TypeOK
                    <5>7. (\A j \in DOMAIN log[p] : (j < i) => log'[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>4, <5>5, <5>6 DEF OSM!ClientRequest, TypeOK
                    <5>8. (\A j \in DOMAIN log'[p] : (j < i) => log'[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>7, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>. QED BY <3>1, <3>5, <3>6, <4>2, <5>8 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
                <4>. QED BY <3>1, <3>5, <3>6, <4>1, <4>2 DEF OSM!ClientRequest, TypeOK
            <3>7. CASE t = p
                <4>1. SUFFICES ASSUME t # s
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>2. log'[s] = log[s] BY <3>1, <3>7, <4>1 DEF OSM!ClientRequest, TypeOK
                <4>3. \A j \in DOMAIN log'[t] : (j < Len(log'[t])) => log[t][j] = log'[t][j] BY <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>4. log'[t][Len(log'[t])] = currentTerm[t] BY <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>5. \A u \in Server : ~\E k \in DOMAIN log[u] : log[u][k] = currentTerm[t] /\ ~InLog(<<k,log[u][k]>>, t)
                    BY <3>1, <3>7, <4>4 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>. QED BY <3>1, <3>7, <4>1, <4>2, <4>3, <4>4, <4>5 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm, InLog
            <3>8. CASE s # p /\ t # p BY <3>1, <3>8 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK u, v \in Server : OSM!GetEntries(u, v) BY <2>2
            <3>.  DEFINE sLastIdx == Len(log'[u])
            <3>m. log'[u] = SubSeq(log[v], 1, sLastIdx) BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogMatching, EqualUpTo
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            <3>f. SUFFICES ASSUME TRUE
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            <3>6. CASE s = u
                <4>1. SUFFICES ASSUME s # t
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. \A j \in DOMAIN log[v] : (j < i) => (j \in DOMAIN log'[s] /\ log[s][j] = log'[s][j])
                    BY <3>1, <3>m, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. (\A j \in DOMAIN log'[s] : (j < i) => log'[s][j] # log'[s][i]) => (\A j \in DOMAIN log[v] : (j < i) => log[v][j] # log[v][i])
                    \* why do i have to spell this out?  because TLAPS is stupid
                    <5>1. \A j \in DOMAIN log[v] : (j < i) => (j \in DOMAIN log'[s]) BY <4>2
                    <5>. QED BY <3>1, <3>m, <3>6, <4>1, <5>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>4. (\A j \in DOMAIN log[v] : (j < i) => log[v][j] # log[v][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i])
                    BY <3>1, <3>3, <3>4, <3>5, <3>6, <4>2 DEF OSM!GetEntries, OSM!Empty, Ind, UniformLogEntriesInTerm, TypeOK
                <4>5. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                    <5>1. SUFFICES ASSUME \A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i]
                          PROVE (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])' OBVIOUS
                    <5>2. log'[t] = log[t] BY <3>1, <3>6, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>3. log'[v] = log[v] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>4. log'[v][i] = log'[s][i] BY <3>1, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogMatching, EqualUpTo
                    <5>. QED BY <5>1, <5>2, <5>3, <5>4 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>. QED BY <4>3, <4>4, <4>5 DEF TypeOK
            <3>7. CASE t = u
                <4>1. SUFFICES ASSUME s # t
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>7 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1 DEF Ind, UniformLogEntriesInTerm, OSM!GetEntries, OSM!Empty, TypeOK
                <4>4. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log'[t][j] # log'[s][i])
                    BY <3>1, <3>5, <3>7, <4>1, <4>3 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>.  DEFINE tLastIdx == Len(log'[t])
                <4>5. log'[t][tLastIdx] = log[v][tLastIdx]
                    BY <3>1, <3>5, <3>7, <4>1, <4>3 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>6. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (tLastIdx < i => log[v][tLastIdx] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
                <4>. QED BY <3>1, <3>5, <3>7, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
            <3>8. CASE s # u /\ t # u BY <3>1, <3>8 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. PICK u, v \in Server : OSM!RollbackEntries(u, v) BY <2>3
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            <3>f. SUFFICES ASSUME TRUE
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            <3>6. CASE s = u
                <4>a. SUFFICES ASSUME t # s
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK
                <4>1. \A j \in DOMAIN log'[s] : j \in DOMAIN log[s] /\ log'[s][j] = log[s][j]
                    BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK
                <4>2. \A j \in DOMAIN log[s] : (j < i) => (j \in DOMAIN log'[s] /\ log'[s][j] = log[s][j])
                    BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK
                <4>3. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])
                    BY <3>5, <4>1, <4>2
                <4>4. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])
                    BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK, Ind, UniformLogEntriesInTerm
                <4>5. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                    BY <3>1, <3>5, <3>6, <4>a DEF OSM!RollbackEntries, TypeOK
                <4>. QED BY <4>1, <4>2, <4>3, <4>4, <4>5
            <3>7. CASE t = u
                \* i think if i included the def of OSM!CanRollback, OSM!LastTerm, OSM!LogTerm, OSM!GetTerm then i wouldn't need LogMatching
                BY <3>1, <3>5, <3>7 DEF OSM!RollbackEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm, LogMatching, EqualUpTo
            <3>8. CASE s # u /\ t # u BY <3>1, <3>8 DEF OSM!RollbackEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, UniformLogEntriesInTerm
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, UniformLogEntriesInTerm
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, TypeOK, Ind, UniformLogEntriesInTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next


\* Template
(*
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
        <2>4. CASE \E s \in Server : \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q)
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next
*)


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
    <1>13. CommittedEntryIndexesAreNonZero'
    <1>14. CommittedTermMatchesEntry'
    <1>15. LeaderCompletenessGeneralized'
    <1>16. LogsLaterThanCommittedMustHaveCommitted'
    <1>17. ActiveConfigsOverlapWithCommittedEntry'
    <1>18. NewerConfigsDisablePrimaryCommitsInOlderTerms'
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

