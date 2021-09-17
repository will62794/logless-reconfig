----------------------------- MODULE MongoRaftReconfigProofs -----------------------------

\*
\* MongoDB replication protocol that allows for logless, dynamic reconfiguration.
\*

EXTENDS MongoRaftReconfig, Randomization

CONSTANT MaxLogLen
CONSTANT MaxTerm
CONSTANT MaxConfigVersion
CONSTANT NumRandSubsets

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
                    /\ configVersion[s] <= MaxConfigVersion

Symmetry == Permutations(Server)

(***************************************************************************)
(* Proving an inductive invariant.  (experimental)                         *)
(***************************************************************************)

SeqOf(set, n) == 
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

BoundedSeq(S, n) ==
  (***************************************************************************)
  (* An alias for SeqOf to make the connection to Sequences!Seq, which is    *)
  (* the unbounded version of BoundedSeq.                                    *)
  (***************************************************************************)
  SeqOf(S, n)


\* Note from Randomization.tla
(***************************************************************************)
(* RandomSetOfSubsets(k, n, S) equals a pseudo-randomly chosen set of      *)
(* subsets of S -- that is, a randomly chosen subset of SUBSET S .  Thus,  *)
(* each element T of this set is a subset of S.  Each such T is chosen so  *)
(* that each element of S has a probability n / Cardinality(S) of being in *)
(* T.  Thus, the average number of elements in each chosen subset T is n.  *)
(* The set RandomSetOfSubsets(k, n, S) is obtained by making k such        *)
(* choices of T .  Because this can produce duplicate choices, the number  *)
(* of elements T in this set may be less than k.  The average number of    *)
(* elements in RandomSetOfSubsets(k, n, S) seems to be difficult to        *)
(* compute in general.  However, there is very little variation in the     *)
(* actual number of elements in the chosen set for fixed values of k, n,   *)
(* and Cardinality(S).  You can therefore use the operator                 *)
(* TestRandomSetOfSubsets defined below to find out approximately how      *)
(* close to k the cardinality of the chosen set of subsets is.             *)
(***************************************************************************)


BoundedSeqFin(S) == BoundedSeq(S, MaxLogLen)
NatFinite == 0..3
PositiveNat == 1..3

ConfigType == [Server -> SUBSET Server]

ElectionType == [ leader : Server, 
                  term   : Nat ]

--------------------------------------------------------------------------------

\* Is log entry e = <<index, term>> in the log of node 'i'.
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
    \A j \in 1..i : log1[j] = log2[j]

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

--------------------------------------------------------------------------------

ViewNoElections == <<currentTerm, state, log, configVersion, configTerm, config, log, committed>>

CommittedType == 
    [ entry  : (0..MaxLogLen) \X (0..MaxTerm),
      term   : 0..MaxTerm ]

kNumSubsets == 3
nAvgSubsetSize == 2

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])
    /\ state \in RandomSubset(NumRandSubsets, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(NumRandSubsets, [Server -> Seq(0..MaxLogLen)])
    /\ config \in RandomSubset(NumRandSubsets, [Server -> SUBSET Server])
    /\ configVersion \in RandomSubset(NumRandSubsets, [Server -> 0..MaxConfigVersion])
    /\ configTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])
    \* For checking MongoRaftReconfig with logs.
    /\ committed \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, CommittedType)
    /\ elections = {}

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

IInit == 
    /\ TypeOKRandom
    /\ Ind


\* Must check that the initial states satisfy the inductive invariant.
Initiation == (Init => Ind)

--------------------------------------------------------------------------------

CSMBecomeLeaderPrec(s, Q) ==
    LET newTerm == currentTerm[s] + 1 IN
    /\ s \in config[s]
    /\ s \in Q
    /\ \A v \in Q : CSM!CanVoteForConfig(v, s, newTerm)

OSMBecomeLeaderPrec(s, Q) ==
    LET newTerm == currentTerm[s] + 1 IN
    /\ s \in Q
    /\ \A v \in Q : OSM!CanVoteForOplog(v, s, newTerm)

BecomeLeaderPrec(s, Q) == OSMBecomeLeaderPrec(s, Q) \/ CSMBecomeLeaderPrec(s, Q)

EProp ==
    \A s \in Server :
        (\E Q \in QuorumsAt(s) : CSMBecomeLeaderPrec(s, Q)) =>
            \A t \in Server :
                /\ currentTerm[s] >= currentTerm[t]
                \*/\ configTerm[s] >= configTerm[t] \/ configVersion[s] >= configVersion[t]
                \*/\ CSM!IsNewerOrEqualConfig(s, t)

FProp ==
    \A s \in Server : s \in config[s] =>
        \E Q \in QuorumsAt(s) :
            \A q \in Q : \A t \in config[s]: currentTerm[q] >= currentTerm[t]

\*GProp ==
    \*\A s \in ServersInNewestConfig :
        \*\A t \in Server : c

GProp ==
    \A s,t \in Server :
        (configVersion[s] > configVersion[t]) => (configTerm[s] > configTerm[t])

=============================================================================
