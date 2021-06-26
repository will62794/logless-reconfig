----------------------------- MODULE MRRIndProof -----------------------------

EXTENDS MongoRaftReconfig, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS

(* Log Matching *)

EqualUpTo(log1, log2, i) ==
    \A j \in 1..i : log1[j] = log2[j]

\* This is a core property of Raft, but MongoStaticRaft does not satisfy this
LogMatching ==
    \A s,t \in Server :
        \A i \in (DOMAIN log[s] \cap DOMAIN log[t]) :
            log[s][i] = log[t][i] => EqualUpTo(log[s],log[t],i)


--------------------------------------------------------------------------------

(* SMS_LC_II Helpers *)

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

\* The set of all quorums in a given set.

ExistsPrimary == \E s \in Server : state[s] = Primary


(* LemmaBasic Properties *)

AllConfigsAreServer ==
    \A s \in Server : config[s] = Server

\* A server's current term is always at least as large as the terms in its log.
\* This is LEMMA 6 from the Raft dissertation.
CurrentTermAtLeastAsLargeAsLogTermsForPrimary ==
    \A s \in Server : state[s] = Primary => (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* The terms of entries grow monotonically in each log.
\* This is LEMMA 7 from the Raft dissertation.
TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : i <= j => log[s][i] <= log[s][j]

OnePrimaryPerTerm ==
    \A s \in Server : state[s] = Primary =>
        \A t \in Server :
            (state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t

ExistsQuorumInLargestTerm ==
  \E s \in Server :
       /\ ExistsPrimary => state[s] = Primary
       /\ \A u \in Server : currentTerm[s] >= currentTerm[u]
       /\ \E Q \in QuorumsAt(s) :
             \A q \in Q : currentTerm[q] = currentTerm[s]

LogsMustBeSmallerThanOrEqualToLargestTerm ==
    \A s \in Server : \E t \in Server : LastTerm(log[s]) <= currentTerm[t]


(* LemmaSecondariesFollowPrimary *)

SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm ==
    \A s \in Server :
        (state[s] = Secondary /\ LastTerm(log[s]) = currentTerm[s]) =>
           \/ \E p \in Server :
                  /\ state[p] = Primary
                  /\ currentTerm[p] = currentTerm[s] \* different from exceeds
                  /\ LastTerm(log[p]) >= LastTerm(log[s])
                  /\ Len(log[p]) >= Len(log[s])
           \/ \E p \in Server :
                  /\ state[p] = Primary
                  /\ currentTerm[p] > currentTerm[s] \* different from exceeds
           \/ \A t \in Server : state[t] = Secondary

SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm ==
    \A s \in Server :
        (state[s] = Secondary /\ LastTerm(log[s]) > currentTerm[s]) =>
           \/ \E p \in Server :
                  /\ state[p] = Primary
                  /\ currentTerm[p] = LastTerm(log[s]) \* different from matches
                  /\ LastTerm(log[p]) >= LastTerm(log[s])
                  /\ Len(log[p]) >= Len(log[s])
           \/ \E p \in Server :
                  /\ state[p] = Primary
                  /\ currentTerm[p] > LastTerm(log[s]) \* different from matches
           \/ \A t \in Server : state[t] = Secondary


(* SMS_LC_II *)

\* Belongs in TypeOK, or considered a completely separate II
CommittedTermMatchesEntry ==
    \A c \in committed : c.term = c.entry[2]

\* when a server's latest log term EXCEEDS a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log
LogsLaterThanCommittedMustHaveCommitted ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) =>
            \A d \in committed :
                d.term <= c.term => /\ Len(log[s]) >= d.entry[1]
                                    /\ log[s][d.entry[1]] = d.term

\* when a server's latest log term is EQUAL to a committed entry c's term, ALL commits
\* with terms before or equal to c's must be in the server's log (if the entry fits)
LogsEqualToCommittedMustHaveCommittedIfItFits ==
    \A s \in Server : \A c \in committed :
        (\E i \in DOMAIN log[s] : log[s][i] = c.term) =>
            \A d \in committed :
                (d.term <= c.term /\ Len(log[s]) >= d.entry[1]) =>
                      log[s][d.entry[1]] = d.term


CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens ==
    \A s \in Server :
        LET MaxLgLen == Max({ Len(log[t]) : t \in config[s] })
        IN \A c \in committed : c.entry[1] <= MaxLgLen

CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms ==
    \A s \in Server :
        LET MaxLogTerm == Max({ LastTerm(log[t]) : t \in config[s] })
        IN \A c \in committed : c.term <= MaxLogTerm

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderCompletenessGeneralized ==
    \A s \in Server :
        (state[s] = Primary) =>
        (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

\* Basically the definition of committed--committed entries must appear on a quorum of
\* servers in a server's config
CommittedEntriesMustHaveQuorums ==
    \A c \in committed :
        \A s \in Server :
            \E Q \in Quorums(config[s]) : \A q \in Q :
                \E i \in DOMAIN log[q] :
                    /\ log[q][i] = c.term
                    /\ i = c.entry[1]

\* \* Is node i electable in term T
Electable(i) == \E Q \in QuorumsAt(i) : ENABLED JointBecomeLeader(i, Q)
ElectableInQ(i, Q) == ENABLED JointBecomeLeader(i, Q)


\* \*TODO: Generalize ExistsQuorumInLargestTerm to avoid reliance on quorum definition.
ElectionDisablesLesserOrEqualTerms ==
    \A i,j \in Server :
        \* TODO: Generalize notion of "electable in term" rather than
        \* hard-coding (currentTerm + 1)
        ((state[i] = Primary) /\ (currentTerm[j] + 1) <= currentTerm[i]) => ~Electable(j)

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

\*
\* Reconfiguration stuff.
\*

\* Can someone get elected in config c.
ActiveConfig(v,t) ==
    \E i \in Server :
        /\ configVersion[i] = v
        /\ configTerm[i] = t
        /\ Electable(i)

QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

PrimaryConfigTermEqualToCurrentTerm ==
    \A s \in Server : (state[s] = Primary) => (configTerm[s] = currentTerm[s])

ConfigsNonEmpty ==
    \A s \in Server : config[s] # {}

\* (version, term) pair uniquely identifies a configuration.
ConfigVersionAndTermUnique ==
    \A i,j \in Server :
        (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>> )=>
        config[i] = config[j]

ActiveConfigsInSameTermOverlap ==
    \A i,j \in Server :
        (\*/\ configTerm[i] = configTerm[j]
         /\ ActiveConfig(configVersion[i], configTerm[i])
         /\ ActiveConfig(configVersion[j], configTerm[j])) =>
         QuorumsOverlap(config[i], config[j])

\* If a config exists in term T, there must be some node with a current term
\* of that config or newer.
ConfigInTermImpliesSomeNodeInThatTerm ==
    \A s \in Server : \E t \in config[s] : currentTerm[t] >= configTerm[s]

ConfigInTermDisablesAllOlderConfigsWithDifferingMemberSets ==
    \A s,t \in Server :
    ( /\ configTerm[t] < configTerm[s]
      /\ QuorumsOverlap(config[s], config[t])) => ~ActiveConfig(configVersion[t], configTerm[t])

\* If a config C=(v,t) exists, then there must have been an election
\* in term T in the original config of this term, and those terms must
\* have been propagated on a quorum through configs, so any quorum must
\* overlap with some node in this term.
ConfigInTermImpliesQuorumOfConfigInTerm ==
    \A s \in Server :
    \A Q \in Quorums(config[s]) :
    \E n \in Q : currentTerm[n] >= configTerm[s]

\* For configs C=(v,t) and C'=(v+1,t), we know their quorums overlap, by explicit preconditions
\* of reconfiguration.
ConfigOverlapsWithDirectAncestor ==
    \A s,t \in Server :
        (/\ configVersion[s] = (configVersion[t] + 1)
         /\ configTerm[s] = configTerm[t]) => QuorumsOverlap(config[s], config[t])

\* A reconfig on step up from C=(v,t) to C'=(v,t+1) does not change the config
\* member set.
ElectionReconfigDoesntChangeMemberSet ==
    \A s,t \in Server :
        (/\ configVersion[s] = configVersion[t]
         /\ configTerm[s] = (configTerm[t] + 1)) => config[s] = config[t]


\* If there is a primary in some term, it should be the only one who can create configs
\* in that term, so it should have the newest config in that term.
PrimaryInTermContainsNewestConfigOfTerm ==
    \A i,j \in Server :
    (state[i] = Primary /\ configTerm[j] = currentTerm[i]) =>
    (configVersion[j] <= configVersion[i])

\* If a config C=(v,t) exists and there is another config C=(v',t') with t' < t, and the
\* quorums of C and C' don't overlap, then there must be some committed config in t that overlaps
\* with C.
ConfigInTermNewerThanNonoverlappingImpliesCommittmentInTerm ==
    \A s,t \in Server :
        \* (configTerm[s] > configTerm[t] /\ ~QuorumsOverlap(config[s], config[t])) =>
        (configTerm[s] > configTerm[t] /\ config[s] # config[t]) =>
        \A Q \in Quorums(config[t]) : \E n \in Q :
            \/ configTerm[n] > configTerm[t]
            \/ configVersion[n] > configVersion[t]

ConfigInTermPreventsOlderConfigs ==
    \A s,t \in Server :
        /\ (/\ configTerm[t] < configTerm[s]
            /\ ~QuorumsOverlap(config[s], config[t])) =>
            (\A Q \in Quorums(config[t]) :
             \E n \in Q :
                \/ CSM!NewerConfig(<<configVersion[n], configTerm[n]>>,
                                <<configVersion[t],configTerm[t]>>))


CommittedEntryIndexesAreNonZero == \A c \in committed : c.entry[1] # 0

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

\* \* If a log entry is committed, then the quorums of every
\* active config must overlap with some node that contains this log entry.
CommittedEntryIntersectsWithEveryActiveConfig ==
    \A c \in committed :
    \A s \in Server :
        ~ConfigDisabled(s) => (\A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n))

CommittedEntryInTermIntersectsNewerConfigs ==
    \A c \in committed :
    \A s \in Server :
        (configTerm[s] >= c.term) =>
        (\A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n))

PrimaryMustBeInOwnConfig ==
    \A s \in Server : (state[s] = Primary) => s \in config[s]

\* If a log entry in term T exists, there must have been an election in
\* term T to create it, implying the existence of a config in term T or newer.
LogEntryInTermImpliesConfigInTerm ==
    \A s \in Server :
    \A i \in DOMAIN log[s] :
    \E t \in Server :
        configTerm[t] >= log[s][i]

CommittedEntryIntersectsAnyQuorumOfNewestConfig ==
    \A c \in committed :
    \A s \in Server :
    (\A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))) =>
        \A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n)

\* LogEntryInTermImpliesElectionInTerm ==

\* If a log contains an entry in term T at index I such that
\* the entries at J < I are in a different term, then there must be
\* no other logs that contains entries in term T at indices J < I
UniformLogEntriesInTerm ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] :
        (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
            (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)


\* It cannot be the case that all nodes are not members of their own configs.
SomeActiveConfig == \E s \in Server : s \in config[s]

NewestConfigIsActive ==
    \A s \in Server :
    (\A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))) =>
        \E n \in config[s] : Electable(n)

\* NewestConfigContainsCommittedEntry ==
NewestConfigHasQuorumWithCommittedEntry ==
    \A c \in committed :
    \A s \in ServersInNewestConfig :
        \E Q \in Quorums(config[s]) :
        \A n \in Q : InLog(c.entry, n)


\* The newest config should have some node that is currently primary or was
\* the newest primary (after stepping down). This node should be in its own config.
NewestConfigHasSomeNodeInConfig ==
    \A s \in ServersInNewestConfig :
        (\E n \in config[s] : n \in config[n]
            \* If this is node is or was primary in newest config,
            \* it's term should be the same as the term of the newest config.
            /\ currentTerm[n] = configTerm[s]
            /\ CV(n) = CV(s))

\* The newest config should have some node that is currently primary or was
\* the newest primary (after stepping down). This node should have all committed
\* entries in its log and should be a part of its own config.
NewestConfigHasSomeNodeInConfigWithCommittedEntry ==
    \A s \in ServersInNewestConfig :
        (\E n \in config[s] :
            /\ \A c \in committed : InLog(c.entry, n)
            /\ n \in config[n]
            \* If this is node is or was primary in newest config,
            \* it's term should be the same as the term of the newest config.
            /\ currentTerm[n] = configTerm[s]
            /\ CV(n) = CV(s)

            \* Can't be that another node has an entry in this node's term
            \* but this primary (or past primary) doesn't have it.
            /\ \A j \in Server :
                ~(\E k \in DOMAIN log[j] :
                    /\ log[j][k] = currentTerm[n]
                    /\ ~InLog(<<k,log[j][k]>>, n))
            )

NewestConfigHasLargestTerm ==
    \A s \in ServersInNewestConfig :
    \A t \in Server :
        currentTerm[t] <= configTerm[s]


CommittedEntryIntersectsWithNewestConfig ==
    \A c \in committed :
    \A s \in ServersInNewestConfig :
        \A Q \in QuorumsAt(s) : \E n \in Q : InLog(c.entry, n)

LogEntryOnQuorumInTermImpliesFutureLeadersHaveIt ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] :
        (/\ state[s] = Primary
         /\ \E Q \in Quorums(config[s]) :
            \A n \in Q :
                /\ InLog(<<i,log[s][i]>>, n)
                /\ currentTerm[n] = currentTerm[s]
                /\ log[s][i] = currentTerm[s]) =>
        (~(/\ Electable(t)
           /\ currentTerm[t] >= currentTerm[s]
           /\ ~InLog(<<i,log[s][i]>>, t)))

NewestConfigHasAPrimary ==
    \/ \A s \in Server : configTerm[s] = 0 \* initial state.
    \/ \E s \in ServersInNewestConfig : state[s] = Primary


\* If a config has been created in term T', then this must prevent any commits
\* in configs in terms < T. Note that only primary nodes can commit writes in a
\* config.
CommitOfNewConfigPreventsCommitsInOldTerms ==
    \A s,t \in Server :
        (/\ configTerm[t] < configTerm[s]
         /\ state[t] = Primary) =>
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]

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

ViewNoElections == <<currentTerm, state, log, configVersion, configTerm, config, log, committed>>


Ind ==
    \*
    \* Establishing election safety under reconfiguration.
    \*
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigVersionAndTermUnique
    /\ PrimaryInTermContainsNewestConfigOfTerm
    /\ NewerConfigDisablesOlderNonoverlappingConfigs
    /\ NewerConfigDisablesTermsOfOlderNonDisabledConfigs

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

    \*
    \* Establishing additional config related invariants that
    \* help with leader completeness.
    \*
    /\ ConfigOverlapsWithDirectAncestor
    /\ NewestConfigHasLargestTerm
    /\ NewestConfigHasSomeNodeInConfig
    /\ ConfigsWithSameVersionHaveSameMemberSet
    /\ CommitOfNewConfigPreventsCommitsInOldTerms

    \*
    \* Establishing leader completeness invariant.
    \*
    /\ LeaderCompletenessGeneralized
    /\ CommittedEntryIntersectsWithNewestConfig
    /\ CommittedEntryIntersectsWithEveryActiveConfig
    /\ LogsLaterThanCommittedMustHaveCommitted


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

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE QuorumsAt(s) \subseteq SUBSET Server
PROOF BY DEF QuorumsAt, Quorums, TypeOK

LEMMA StaticQuorumsOverlap ==
ASSUME TypeOK,
       NEW cfg \in SUBSET Server,
       NEW Q1 \in Quorums(cfg),
       NEW Q2 \in Quorums(cfg)
PROVE Q1 \cap Q2 # {}
PROOF
    <1>. IsFiniteSet(cfg)
        BY FS_Subset, ServerIsFinite DEF TypeOK
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
ASSUME TypeOK,
       NEW cfg \in SUBSET Server
PROVE QuorumsOverlap(cfg, cfg)
PROOF BY StaticQuorumsOverlap DEF QuorumsOverlap

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

LEMMA ExistsMaxInNatSet ==
ASSUME NEW S \in SUBSET Nat,
       IsFiniteSet(S), S # {}
PROVE \E m \in S : \A x \in S : m >= x

LEMMA CVsFinite ==
ASSUME TypeOK
PROVE LET Op(x) == x \*configVersion[x]
          T == {Op(x) : x \in Server}
      IN  IsFiniteSet(T)
PROOF BY ServerIsFinite, FS_Image \*DEF TypeOK

LEMMA ExistsServerWithMaxConfigVersion ==
ASSUME TypeOK
PROVE \E s \in Server : \A t \in Server : configVersion[s] >= configVersion[t]
PROOF
    <1>. DEFINE allConfigVersions == {configVersion[s] : s \in Server}
    <1>. DEFINE configVersionOp(s) == configVersion[s]
    <1>. DEFINE allConfigVersionsAlt == {configVersionOp(s) : s \in Server}
    <1>1c. IsFiniteSet(allConfigVersions) BY ServerIsFinite, FS_SameCardinalityBij , FS_Bijection, FS_Image DEF TypeOK
    <1>1b. IsFiniteSet(allConfigVersions) \*BY ServerIsFinite, FS_Image DEF TypeOK
        <2>1. allConfigVersions \in SUBSET Nat BY DEF TypeOK
        <2>. DEFINE P(s) == configVersion[s]
        <2>2. Cardinality({P(s) : s \in Server}) <= Cardinality(Server) BY ServerIsFinite, FS_Image \*, \*AllProversT(100) \*BY ServerIsFinite, FS_Image DEF TypeOK
        <2>. QED \*BY <2>1, ServerIsFinite, FS_Image, FS_Subset
    \*<1>a. allConfigVersions \in SUBSET Nat BY DEF TypeOK
    <1>. DEFINE maxSet == {x \in allConfigVersions : \A y \in allConfigVersions : x >= y}
    <1>. DEFINE maxCV == CHOOSE x \in maxSet : TRUE \*Max(allConfigVersions)
    <1>1. allConfigVersions # {} BY ServerIsNonempty
    <1>b. \A x \in allConfigVersions : x \in Nat BY DEF TypeOK
    \*<1>c. \E x \in allConfigVersions : x \in Nat BY DEF TypeOK
    <1>d. maxCV \in allConfigVersions BY <1>1
    <1>e. maxCV \in Nat BY <1>b, <1>d \*DEF Max
    <1>mse. maxSet # {} BY <1>1, <1>1b, <1>b, ExistsMaxInNatSet DEF TypeOK \*BY <1>1 DEF TypeOK
    <1>z. maxCV \in maxSet BY <1>mse
    <1>h. \A y \in allConfigVersions : maxCV >= y BY <1>z

    <1>. PICK s \in Server : configVersion[s] = maxCV BY <1>1
    <1>2. \A t \in Server : configVersion[s] >= configVersion[t] BY <1>h
    <1>. QED BY <1>2

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
PROVE CSM!IsNewerConfig(s, t) <=> ~CSM!IsNewerOrEqualConfig(t, s)
BY DEF CSM!IsNewerConfig, CSM!IsNewerOrEqualConfig, TypeOK

LEMMA ServersInNewestConfigNotEmpty ==
ASSUME TypeOK
PROVE ServersInNewestConfig # {}
PROOF
    <1>. SUFFICES ASSUME \A s \in Server : \E t \in Server : ~CSM!NewerOrEqualConfig(CV(s), CV(t))
         PROVE FALSE
         BY DEF ServersInNewestConfig, NewestConfig
    <1>1. \A s \in Server : \E t \in Server : CSM!IsNewerConfig(t, s) BY NewerOrEqualConfigEquivalence, NewerIsNotSymmetric
    \*<1>. PICK s \in Server : TRUE BY ServerIsNonempty
    \*<1>. PICK t \in Server : ~CSM!NewerOrEqualConfig(CV(s), CV(t)) OBVIOUS

    <1>. DEFINE NewerConfigsOf(s) == {t \in Server : CSM!IsNewerConfig(t, s)}
    <1>2. \A s \in Server : NewerConfigsOf(s) # {} BY <1>1
    <1>. DEFINE necs == UNION {NewerConfigsOf(s) : s \in Server}
    \*<1>3. \A s \in Server : \A t \in NewerConfigsOf(s) : t \in necs OBVIOUS
    <1>3. necs # {} BY <1>2, ServerIsNonempty
    <1>a. \A s \in necs : \E t \in Server : CSM!IsNewerConfig(s, t) OBVIOUS

    <1>. TRUE
    <1>. QED

LEMMA ElectedLeadersHaveLatestTerm ==
ASSUME TypeOK, Ind,
       NEW p \in Server,
       NEW Q \in QuorumsAt(p),
       OSM!BecomeLeader(p, Q),
       CSM!BecomeLeader(p, Q)
PROVE \A s \in Server : currentTerm[p] >= currentTerm[s]
PROOF
    <1>. PICK nc \in ServersInNewestConfig : TRUE BY ServersInNewestConfigNotEmpty
    <1>1. OlderConfig(CV(p), CV(nc)) \/ (CV(p) = CV(nc))
        <2>1. CSM!NewerOrEqualConfig(CV(nc), CV(p)) BY DEF ServersInNewestConfig, NewestConfig
        <2>2. CSM!NewerConfig(CV(nc), CV(p)) \/ CV(nc) = CV(p) BY <2>1 DEF CSM!NewerOrEqualConfig
        <2>3. CSM!NewerConfig(CV(nc), CV(p)) => OlderConfig(CV(p), CV(nc)) BY DEF CSM!NewerConfig, OlderConfig, CSM!NewerOrEqualConfig, CV, TypeOK, ServersInNewestConfig
        <2>. QED BY <2>2, <2>3
    <1>. CASE ConfigDisabled(p)
        \* contradiction, can't become leader
        <2>. PICK s \in Q : CSM!NewerConfig(CV(s), CV(p)) BY DEF ConfigDisabled, QuorumsAt
        <2>1. CSM!IsNewerOrEqualConfig(p, s) BY DEF CSM!BecomeLeader, CSM!CanVoteForConfig
        <2>2. CSM!IsNewerConfig(s, p) BY NewerConfigEquivalence, QuorumsAreServerSubsets
        <2>. QED BY <2>1, <2>2, NewerIsNotSymmetric, QuorumsAreServerSubsets
    <1>. CASE ~ConfigDisabled(p)
        <2>. PICK s \in Q : currentTerm[s] >= configTerm[nc]
            BY <1>1 DEF Ind, NewerConfigDisablesTermsOfOlderNonDisabledConfigs, ServersInNewestConfig, QuorumsAt
        <2>1. \A t \in Server : currentTerm[s] >= currentTerm[t]
            <3>1. \A t \in Server : configTerm[nc] >= currentTerm[t] BY DEF Ind, NewestConfigHasLargestTerm
            <3>. QED BY <3>1 DEF TypeOK, ServersInNewestConfig, QuorumsAt, Quorums
        <2>2. \A t \in Q : currentTerm[p] >= currentTerm[t] BY DEF OSM!BecomeLeader, OSM!CanVoteForOplog, QuorumsAt, Quorums, TypeOK
        <2>. QED BY <2>1, <2>2 DEF QuorumsAt, Quorums, TypeOK
    <1>. QED OBVIOUS

LEMMA BecomeLeaderQuorumsInLargestTerm ==
ASSUME TypeOK, Ind,
       NEW p \in Server,
       NEW Q \in QuorumsAt(p),
       OSM!BecomeLeader(p, Q),
       CSM!BecomeLeader(p, Q)
PROVE \A s \in Q : \A t \in Server : t \notin Q => currentTerm'[s] > currentTerm'[t]
PROOF
    <1>. TAKE s \in Q
    <1>. TAKE t \in Server
    <1>. SUFFICES ASSUME t \notin Q
         PROVE currentTerm'[s] > currentTerm'[t] OBVIOUS
    <1>1. currentTerm[p] >= currentTerm[t] BY ElectedLeadersHaveLatestTerm
    <1>2. currentTerm'[p] > currentTerm[t] BY <1>1 DEF OSM!BecomeLeader, TypeOK
    <1>. QED BY <1>2 DEF OSM!BecomeLeader, TypeOK, QuorumsAt, Quorums

--------------------------------------------------------------------------------

(* IndAndNext *)

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
            <3>. SUFFICES ASSUME TRUE
                 PROVE \A s \in Server : state'[s] = Primary =>
                            \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
                 BY DEF OnePrimaryPerTerm
            <3>. TAKE s \in Server
            <3>. CASE \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
                <4>. PICK Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q) OBVIOUS
                <4>1. \A t \in Server : currentTerm'[s] > currentTerm'[t] \/ state'[t] # Primary \/ t = s
                    <5>1. \A t \in Server : currentTerm[s] >= currentTerm[t] BY ElectedLeadersHaveLatestTerm DEF QuorumsAt
                    <5>2. \A t \in Server : t \notin Q => currentTerm'[s] > currentTerm'[t] BY <5>1 DEF OSM!BecomeLeader, TypeOK
                    <5>3. \A t \in Q : t # s => state'[t] # Primary BY PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader, TypeOK, QuorumsAt, Quorums
                    <5>. QED BY <5>2, <5>3 DEF QuorumsAt, Quorums
                <4>2. \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t BY <4>1, TypeOKAndNext DEF TypeOK
                <4>3. state'[s] = Primary BY DEF OSM!BecomeLeader
                <4>. QED BY <4>2, <4>3 DEF OnePrimaryPerTerm
            <3>. CASE ~(\E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q))
                <4>. PICK p \in Server : p # s /\ \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
                <4>. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) OBVIOUS
                <4>. CASE s \in Q BY PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader \* s won't be primary
                <4>. CASE s \notin Q
                    <5>. SUFFICES ASSUME state'[s] = Primary
                         PROVE \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t OBVIOUS
                    <5>. TAKE t \in Server
                    <5>. CASE t \in Q
                        <6>1. currentTerm'[s] < currentTerm'[t] BY BecomeLeaderQuorumsInLargestTerm DEF QuorumsAt
                        <6>. QED BY <6>1, TypeOKAndNext DEF TypeOK
                    <5>. CASE t \notin Q BY DEF OSM!BecomeLeader, Ind, OnePrimaryPerTerm
                    <5>. QED OBVIOUS
                <4>. QED OBVIOUS
            <3>. QED OBVIOUS
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

LEMMA IndAndNext ==
ASSUME TypeOK, Ind, Next
PROVE Ind'
PROOF
    <1>1. OnePrimaryPerTerm'
        BY OnePrimaryPerTermAndNext
    <1>2. PrimaryConfigTermEqualToCurrentTerm'
    <1>3. ConfigVersionAndTermUnique'
    <1>4. PrimaryInTermContainsNewestConfigOfTerm'
    <1>5. NewerConfigDisablesOlderNonoverlappingConfigs'
    <1>6. NewerConfigDisablesTermsOfOlderNonDisabledConfigs'
    <1>7. LogMatching'
    <1>8. TermsOfEntriesGrowMonotonically'
    <1>9. PrimaryHasEntriesItCreated'
    <1>10. CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
    <1>11. LogEntryInTermImpliesConfigInTerm'
    <1>12. UniformLogEntriesInTerm'
    <1>13. CommittedEntryIndexesAreNonZero'
    <1>14. CommittedTermMatchesEntry'
    <1>15. ConfigOverlapsWithDirectAncestor'
    <1>16. NewestConfigHasLargestTerm'
    <1>17. NewestConfigHasSomeNodeInConfig'
    <1>18. ConfigsWithSameVersionHaveSameMemberSet'
    <1>19. CommitOfNewConfigPreventsCommitsInOldTerms'
    <1>20. LeaderCompletenessGeneralized'
    <1>21. CommittedEntryIntersectsWithNewestConfig'
    <1>22. CommittedEntryIntersectsWithEveryActiveConfig'
    <1>23. LogsLaterThanCommittedMustHaveCommitted'
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
                <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17,
                <1>18, <1>19, <1>20, <1>21, <1>22, <1>23
          DEF Ind

--------------------------------------------------------------------------------

(* Overall Result *)

LEMMA QuorumsAreNonEmpty ==
ASSUME config \in [Server -> SUBSET Server], \* from TypeOK
       NEW s \in Server
PROVE \A Q \in Quorums(config[s]) : Q # {}
PROOF
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
    <1>5. NewerConfigDisablesOlderNonoverlappingConfigs
        BY DEF Init, OSM!Init, CSM!Init, NewerConfigDisablesOlderNonoverlappingConfigs,
                OlderConfig, CSM!NewerOrEqualConfig, ConfigDisabled, CSM!NewerConfig, CSM!IsNewerConfig, QuorumsOverlap, Quorums, CV
    <1>6. NewerConfigDisablesTermsOfOlderNonDisabledConfigs
        <2>. SUFFICES ASSUME TRUE
             PROVE \A s,t \in Server : \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]
             BY DEF NewerConfigDisablesTermsOfOlderNonDisabledConfigs
        <2>. TAKE s \in Server
        <2>. TAKE t \in Server
        <2>. TAKE Q \in Quorums(config[t])
        <2>1. Q # {} BY QuorumsAreNonEmpty DEF Init, OSM!Init, CSM!Init
        <2>2. \A q \in Q : currentTerm[q] >= configTerm[s]
            BY DEF Init, OSM!Init, CSM!Init, Quorums
        <2>. QED BY <2>1, <2>2
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
    <1>15. ConfigOverlapsWithDirectAncestor
        BY DEF Init, OSM!Init, CSM!Init, ConfigOverlapsWithDirectAncestor
    <1>16. NewestConfigHasLargestTerm
        BY DEF Init, OSM!Init, CSM!Init, NewestConfigHasLargestTerm, ServersInNewestConfig
    <1>17. NewestConfigHasSomeNodeInConfig
        BY DEF Init, OSM!Init, CSM!Init, NewestConfigHasSomeNodeInConfig, ServersInNewestConfig, CV
    <1>18. ConfigsWithSameVersionHaveSameMemberSet
        BY DEF Init, OSM!Init, CSM!Init, ConfigsWithSameVersionHaveSameMemberSet
    <1>19. CommitOfNewConfigPreventsCommitsInOldTerms
        BY DEF Init, OSM!Init, CSM!Init, CommitOfNewConfigPreventsCommitsInOldTerms
    <1>20. LeaderCompletenessGeneralized
        BY DEF Init, OSM!Init, CSM!Init, LeaderCompletenessGeneralized
    <1>21. CommittedEntryIntersectsWithNewestConfig
        BY DEF Init, OSM!Init, CSM!Init, CommittedEntryIntersectsWithNewestConfig
    <1>22. CommittedEntryIntersectsWithEveryActiveConfig
        BY DEF Init, OSM!Init, CSM!Init, CommittedEntryIntersectsWithEveryActiveConfig
    <1>23. LogsLaterThanCommittedMustHaveCommitted
        BY DEF Init, OSM!Init, CSM!Init, LogsLaterThanCommittedMustHaveCommitted
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
                <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17,
                <1>18, <1>19, <1>20, <1>21, <1>22, <1>23
          DEF Ind

THEOREM IndIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => Ind
      /\ (TypeOK /\ Ind /\ Next) => (TypeOK /\ Ind)'
PROOF BY InitImpliesTypeOK, InitImpliesInd, TypeOKAndNext, IndAndNext

=============================================================================

