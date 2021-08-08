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


(*
TypeOK == 
    /\ currentTerm \in SUBSET [Server -> Nat]
    /\ state \in SUBSET [Server -> {Secondary, Primary}]
    /\ log \in SUBSET [Server -> Seq(PositiveNat)]
    /\ config = [i \in Server |-> Server]
    /\ elections = {}
    /\ committed \in SUBSET CommittedType
*)

\*
\* Correctness properties
\*


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

MaxConfigId == CHOOSE s \in Server : \A t \in Server : CSM!NewerOrEqualConfig(CV(s), CV(t))

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

\* Alternate form stated in terms of the maximum (i.e.) newest config in the system.
NewerConfigDisablesTermsOfOlderNonDisabledConfigs_Alt ==
    \A t \in Server : 
        ( /\ OlderConfig(CV(t), CV(MaxConfigId)) \/ (CV(t) = CV(MaxConfigId)) 
          /\ ~ConfigDisabled(t) ) =>
            \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[MaxConfigId]


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

CommittedType == 
    [ entry  : (0..MaxLogLen) \X (0..MaxTerm),
      term   : 0..MaxTerm ]

\*
\* Parameters for selecting subsets of 'committed' variable type below. For a
\* set S, calling RandomSetOfSubsets(k, n, S) produces a randomly chosen subset
\* of SUBSET S. Thus, each element T of the set is a subset of S. The goal is to
\* output a set of size k (i.e containing k subsets of S), but the output may be 
\* of size less than k. The average number of elements in each chosen subset T is n. 
\* For example:
\*
\* (tla+) RandomSetOfSubsets(3, 2, {1,2,3,4})
\* {{3}, {1, 2}, {2, 3, 4}}
\*
\* (tla+) RandomSetOfSubsets(4, 2, {1,2,3,4})
\* {{1}, {1, 3}, {1, 2, 3}, {1, 2, 4}}
\*
\* (tla+) RandomSetOfSubsets(5, 2, {1,2,3,4})
\* {{4}, {1, 4}, {3, 4}, {1, 2, 4}, {1, 2, 3, 4}}
\*

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

ConfigsGrowMonotonically == [][\A s \in Server : CSM!NewerOrEqualConfig(CV(s)', CV(s))]_vars
CurrentTermsGTEConfigTerms == \A s \in Server : currentTerm[s] >= configTerm[s]

\* If a server is currently primary in term T in config (v,T), then all older configs
\* in term T that do not overlap with (v,T) must be disabled.
I1 == 
    \A s,t \in Server :
        (\*/\ state[s] = Primary 
         /\ OlderConfig(CV(t), CV(s))
        \*  /\ configTerm[t] = configTerm[s]
        \*  /\ configVersion[t] < configVersion[s]
         /\ ~QuorumsOverlap(config[t], config[s]) 
         /\ config[t] # {} 
         /\ config[s] # {}) => ConfigDisabled(t)

\* If a server is currently primary in term T in config (v, T), then all configs
\* in the same term that overlap with it must intersect with some node in term >= T.

\* All non disabled configs in a given term must overlap with some node in term >= T (?)
I1a == 
    \A s \in Server :
        ~ConfigDisabled(s) => 
        \A Q \in Quorums(config[s]) : \E n \in Q : currentTerm[n] >= configTerm[s]

\* For any config in term T, all of its quorums should overlap with some node in term >= T.
I1b ==
    \A s \in Server : 
    \A Q \in Quorums(config[s]) : \E n \in Q : currentTerm[n] >= configTerm[s]


\* If a node is currently primary in term T, then all configs in lesser terms should
\* be either (a) disabled or (b) prevented from becoming committed.
I2 == 
    \A s,t \in Server :
        (\*/\ state[s] = Primary
         /\ configTerm[t] < configTerm[s]) =>
          \/ ConfigDisabled(t)
          \/ \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]


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

Ind ==
    \*
    \* Establishing election safety under reconfiguration.
    \*
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigVersionAndTermUnique
    /\ PrimaryInTermContainsNewestConfigOfTerm

    \* (original)
    /\ NewerConfigDisablesOlderNonoverlappingConfigs
    /\ NewerConfigDisablesTermsOfOlderNonDisabledConfigs

    \* (alternate)
    \* /\ ActiveConfigsOverlap
    \* /\ ActiveConfigsSafeAtTerms

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

    \* (original)

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


    \* (alternate)

    \* /\ LeaderCompletenessGeneralized
    \* /\ LogsLaterThanCommittedMustHaveCommitted
    \* /\ ActiveConfigsOverlapWithCommittedEntry
    \* /\ NewerConfigsDisablePrimaryCommitsInOlderTerms






\* SMS_LC_II
\* 
\* /\ CommittedEntryIndexesAreNonZero
\* /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
\* /\ TermsOfEntriesGrowMonotonically
\* /\ ExistsQuorumInLargestTerm
\* /\ LogsMustBeSmallerThanOrEqualToLargestTerm
\* /\ AllConfigsAreServer
\* /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
\* /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
\* /\ CommittedTermMatchesEntry
\* /\ LogsLaterThanCommittedMustHaveCommitted
\* /\ LogsEqualToCommittedMustHaveCommittedIfItFits
\* /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
\* /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
\* /\ LeaderCompletenessGeneralized
\* /\ CommittedEntriesMustHaveQuorums


IInit == 
    /\ TypeOKRandom
    /\ Ind


\* Must check that the initial states satisfy the inductive invariant.
Initiation == (Init => Ind)

\*
\* DEBUGGING
\*

StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(log[s]) \o " " \o
    ToString(config[s]) \o " (" \o ToString(configVersion[s]) \o "," \o ToString(configTerm[s]) \o ")"

ServerPair == Server \X Server
Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        \* elections |-> elections,
        \* config |-> config,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)],
        committed |-> committed,
        activeConfigs |-> ActiveConfigSet,
        \* activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])],
        newestConfig |-> {<<config[s],CV(s)>> : s \in ServersInNewestConfig}
        \* configChains |-> [<<s,t>> \in ServerPair |-> ConfigChains(s,t)]
    ]


=============================================================================
