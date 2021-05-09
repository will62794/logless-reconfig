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

CommittedType == 
    [ entry  : PositiveNat \times PositiveNat,
      term : Nat]

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

\* \*TODO: Generalize ExistsQuorumInLargestTerm to avoid reliance on quorum definition.
ElectionDisablesLesserOrEqualTerms == 
    \A i,j \in Server : 
        \* TODO: Generalize notion of "electable in term" rather than
        \* hard-coding (currentTerm + 1)
        ((state[i] = Primary) /\ (currentTerm[j] + 1) <= currentTerm[i]) => ~Electable(j)

\* \* If a log entry exists in term T, then an election must have occurred in term T, 
\* \* and so all future elections in terms <= T must be disabled. 
\* LogEntryInTermDisablesLesserOrEqualTerms == 
\*     \A i,j \in Server :
\*     \A term \in Range(log[i]) : 
\*     \A leqT \in 1..term : ~Electable(j, leqT)

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
    
\* ElectableNodesHaveCommittedEntries ==
\*     \A i \in Server :
\*     \A c \in committed :
\*         Electable(i, currentTerm[i] + 1) => 
\*         \E Q \in QuorumsAt(i) : \A n \in Q : InLog(c.entry, n)


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

\* If two configs have the same version but one has a newer term,
\* then they either have the same member set or the config in the lesser
\* term is disabled.
ConfigsWithSameVersionHaveSameMemberSetOrDisable == 
    \A s,t \in Server : 
        (/\ configTerm[s] > configTerm[t]
         /\ configVersion[s] = configVersion[t]) => 
            \/ (config[s] = config[t])
            \/ \A Q \in Quorums(config[t]) : \E n \in Q :
                CSM!NewerConfig(<<configVersion[n], configTerm[n]>>,<<configVersion[t], configTerm[t]>>) 

ConfigSeparationImpliesPreviousCommit ==
    \A s,t \in Server :
        \* If config version and config term differ b/w two configs,
        \* they must have been separated by a commit of the newer term in
        \* the original config.
        (/\ configTerm[s] > configTerm[t] 
         /\ configVersion[s] > configVersion[t]
        \*  /\ ~QuorumsOverlap(config[s], config[t])
         /\ config[s] # config[t]) =>
         \E Q \in Quorums(config[t]) : \A n \in Q : configTerm[n] >= configTerm[s]

\* If a config C=(v,t) exists, then there must have been an election
\* in term T in the original config of this term, and those terms must 
\* have been propagated on a quorum through configs, so any quorum must
\* overlap with some node in this term.
ConfigInTermImpliesQuorumOfConfigInTerm ==
    \A s \in Server : 
    \A Q \in Quorums(config[s]) :
    \E n \in Q : currentTerm[n] >= configTerm[s]


\* \* A chain of non-empty config member sets between config[t] and config[s], inclusive of t and non-inclusive of s
\* \* where each config in the chain has pairwise quorum overlap and differs by a version of 1.
\* ConfigChains(s,t) == 
\*     IF (configVersion[s] >= configVersion[t] + 1 /\ configTerm[s] = configTerm[t]) THEN
\*     {chain \in [(configVersion[t]..(configVersion[s]-1)) -> SUBSET Server] :
\*             \* Config t starts the chain.
\*             /\ chain[configVersion[t]] = config[t]
\*             \* Last config in chain overlaps with config s.
\*             /\ QuorumsOverlap(chain[configVersion[s]-1], config[s])
\*             \* The configs in between satisfy pairwise quorum overlap.
\*             /\ \A vx,vy \in DOMAIN chain : 
\*                 /\ chain[vx] # {}
\*                 /\ chain[vy] # {}
\*                 /\ (vx = (vy + 1)) => QuorumsOverlap(chain[vx], chain[vy])
\*             /\ \A vx \in DOMAIN chain:
\*                 \E Q \in Quorums(chain[vx]) : 
\*                 \A n \in Q : 
\*                     CSM!NewerOrEqualConfig(<<configVersion[n], configTerm[n]>>, <<vx, configTerm[s]>>)
\*         }
\*     ELSE {}

\* If a config C=(v,t) and C'=(v',t) both exist with v' >= v+1, then there must have been a parent
\* of C' that was committed before C' came into existence.
ConfigSameTermAncestorMustBeCommitted == 
    \A s,t \in Server :
        (/\ configVersion[s] >= configVersion[t] + 1
         /\ configTerm[s] = configTerm[t]) =>
         \* If these configs differ by 1 or more reconfig edges, then there must exist
         \* a chain of configs between them that are all committed and have pairwise
         \* quorum overlap.
         (\E chain \in [(configVersion[t]..(configVersion[s]-1)) -> SUBSET Server] :
            \* Config t starts the chain.
            /\ chain[configVersion[t]] = config[t]
            \* Last config in chain overlaps with config s.
            /\ QuorumsOverlap(chain[configVersion[s]-1], config[s])
            \* The configs in between satisfy pairwise quorum overlap.
            /\ \A vx,vy \in DOMAIN chain : 
                /\ chain[vx] # {}
                /\ chain[vy] # {}
                /\ (vx = (vy + 1)) => QuorumsOverlap(chain[vx], chain[vy])
            /\ \A vx \in DOMAIN chain:
                \E Q \in Quorums(chain[vx]) : 
                \A n \in Q : 
                    CSM!NewerOrEqualConfig(<<configVersion[n], configTerm[n]>>, <<vx, configTerm[s]>>))


\* If a config C=(v,t) and C'=(v',t') with v > v' and t' > t, there must be a chain
\* of configs between C and C' with some committed config in there.

\* If two configs have different terms, then there are two cases:
\* (I)  one is an ancestor of the other.
\* (II) they are siblings of each other.
\*
\* In case I, there must be a linear chain of configs from C to C', respecting
\* the rules of reconfig/election edges.
\* In case II, there must be a common ancestor config Ca such that there is a path
\* from Ca to both C and C' respecting the election edge rule.
ConfigDiffTermAndVersionAncestorMustBeCommitted == 
    \A s,t \in Server :
        (\*/\ configVersion[s] > configVersion[t]
         /\ configTerm[s] > configTerm[t]) =>

        LET versionDomain == (configVersion[t]..configVersion[s])
            termDomain    == (configTerm[t]..configTerm[s]) IN
        \* CASE I (one is descendant of other)
         (\E chain \in [(versionDomain \X termDomain) -> SUBSET Server] :
            \* /\ \E branch \in DOMAIN chain :
            \*     /\ branch[2] = configTerm[s]
            \*      \* election edges doesn't change config.
            \*     /\ chain[<<branch[1]-1,branch[2]>>] = chain[branch]
            \* Config t starts the chain.
            /\ chain[<<configVersion[t], configTerm[t]>>] = config[t]
            \* Max config in chain overlaps with config s.
            /\ LET maxcv == CHOOSE cvx \in DOMAIN chain : \A cvy \in DOMAIN chain : CSM!NewerOrEqualConfig(cvx, cvy) IN 
               QuorumsOverlap(chain[maxcv], config[s])
            \* The configs in between satisfy pairwise quorum overlap.
            /\ \A vtx,vty \in DOMAIN chain : 
                /\ chain[vtx] # {}
                /\ chain[vty] # {}
                /\ (vtx[1] = (vty[1] + 1) /\ vtx[2] = vty[2]) => QuorumsOverlap(chain[vtx], chain[vty])
                /\ (vtx[1] = vty[1] /\ vtx[2] > vty[2]) => chain[vtx] = chain[vty]
            /\ \A vtx,vty \in DOMAIN chain :
                \* If this is a reconfig edge in the chain, then the parent must be committed.
                (vtx[2] = vtx[2] /\ vtx[1] > vty[1]) =>
                    (\E Q \in Quorums(chain[vtx]) : 
                     \A n \in Q : 
                        CSM!NewerOrEqualConfig(<<configVersion[n], configTerm[n]>>, vtx)))


        \* \* CASE II (siblings)
        \* \E commonAncestor :


        \*  LET versionDomain == (configVersion[t]..configVersion[s])
        \*      termDomain    == (configTerm[t]..configTerm[s]) IN

        \* \* Either C' is an ancestor of C or C and C' are siblings.
        \*  (\E chain \in [(versionDomain \X termDomain) -> SUBSET Server] :
        \*     \* /\ \E branch \in DOMAIN chain :
        \*     \*     /\ branch[2] = configTerm[s]
        \*     \*      \* election edges doesn't change config.
        \*     \*     /\ chain[<<branch[1]-1,branch[2]>>] = chain[branch]
        \*     \* Config t starts the chain.
        \*     /\ chain[<<configVersion[t], configTerm[t]>>] = config[t]
        \*     \* Last config in chain overlaps with config s.
        \*     /\ QuorumsOverlap(chain[<<configVersion[s]-1, configTerm[s]>>], config[s])
        \*     \* The configs in between satisfy pairwise quorum overlap.
        \*     /\ \A vtx,vty \in DOMAIN chain : 
        \*         /\ chain[vtx] # {}
        \*         /\ chain[vty] # {}
        \*         /\ (vtx[1] = (vty[1] + 1) /\ vtx[2] = vty[2]) => QuorumsOverlap(chain[vtx], chain[vty])
        \*         /\ (vtx[1] = vty[1] /\ vtx[2] > vty[2]) => chain[vtx] = chain[vty]
        \*     /\ \A vtx \in DOMAIN chain:
        \*         \E Q \in Quorums(chain[vtx]) : 
        \*         \A n \in Q : 
        \*             CSM!NewerOrEqualConfig(<<configVersion[n], configTerm[n]>>, vtx))



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

\* ConfigInNewerTermNewerDisablesOlderConfigs ==
\*     \A s,t \in Server :
\*         (configTerm[s] > configTerm[t] /\ ~QuorumsOverlap(config[s], config[t])) =>
\*         \A Q \in Quorums(config[t]) : \E n \in Q : 
\*             \/ currentTerm[n] >= configTerm[s]
            \* \/ configTerm[n] > configTerm[t]
            \* \/ configVersion[n] > configVersion[t]


ConfigInTermPreventsOlderConfigs == 
    \A s,t \in Server :
        /\ (/\ configTerm[t] < configTerm[s]
            /\ ~QuorumsOverlap(config[s], config[t])) => 
            (\A Q \in Quorums(config[t]) : 
             \E n \in Q : 
                \/ CSM!NewerConfig(<<configVersion[n], configTerm[n]>>,
                                <<configVersion[t],configTerm[t]>>))

ViewNoElections == <<currentTerm, state, log, configVersion, configTerm, config, log, committed>>

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])
    /\ state \in RandomSubset(NumRandSubsets, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(NumRandSubsets, [Server -> Seq(0..MaxLogLen)])
    /\ config \in RandomSubset(NumRandSubsets, [Server -> SUBSET Server])
    /\ configVersion \in RandomSubset(NumRandSubsets, [Server -> 0..MaxConfigVersion])
    /\ configTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])
    /\ elections = {}
    \* /\ committed \in RandomSetOfSubsets(NumRandSubsets, 1, CommittedType)
    /\ committed = {}

Ind ==
    \* Establishing config safety.
    /\ OnePrimaryPerTerm
    /\ PrimaryConfigTermEqualToCurrentTerm
    /\ ConfigsNonEmpty

    \* Establish basic, intra-term config safety.
    /\ ConfigVersionAndTermUnique
    /\ ConfigSameTermAncestorMustBeCommitted
    /\ ConfigOverlapsWithDirectAncestor
    /\ PrimaryInTermContainsNewestConfigOfTerm

    \* Establish inter-term config safety.
    /\ ConfigInTermImpliesQuorumOfConfigInTerm
    /\ ConfigsWithSameVersionHaveSameMemberSetOrDisable
    /\ ConfigInTermPreventsOlderConfigs


    


    \*
    \* LEMMA Basic
    \*
    \* /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    \* /\ TermsOfEntriesGrowMonotonically
    \* /\ ExistsQuorumInLargestTerm \* quorum based.
    \* /\ ElectionDisablesLesserOrEqualTerms
    \* /\ LogEntryInTermDisablesLesserOrEqualTerms

    \* /\ LogsMustBeSmallerThanOrEqualToLargestTerm
    \* /\ PrimaryHasEntriesItCreated

    \*
    \* LEMMA Reconfigs.
    \*


    \* /\ ElectionReconfigDoesntChangeMemberSet
    \* /\ ConfigDiffTermAndVersionAncestorMustBeCommitted
    \* /\ ConfigInTermNewerThanNonoverlappingImpliesCommittmentInTerm
    \* /\ ConfigInNewerTermNewerDisablesOlderConfigs


    \* /\ ConfigInTermImpliesSomeNodeInThatTerm
    \* /\ ConfigVersionAndTermUnique
    \* /\ ActiveConfigsInSameTermOverlap
    \* /\ PrimaryInTermContainsNewestConfigOfTerm
    \* /\ ConfigsWithSameVersionHaveSameMemberSet
    \* /\ ConfigSeparationImpliesPreviousCommit
    \* /\ ConfigInTermImpliesQuorumOfConfigInTerm
    \* /\ ConfigInTermDisablesAllOlderConfigsWithDifferingMemberSets

    \*
    \* LEMMA Extra
    \*
    \* /\ CommittedTermMatchesEntry
    \* /\ LogsLaterThanCommittedMustHaveCommitted
    \* /\ LogsEqualToCommittedMustHaveCommittedIfItFits
    \* \* /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
    \* \* /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    \* /\ LeaderCompletenessGeneralized

    \* /\ ElectableNodesHaveCommittedEntrielslss
    \* /\ CommittedEntriesMustHaveQuorums \* quorum based.

IInit == 
    /\ TypeOKRandom
    /\ Ind


\*
\* DEBUGGING
\*

\* Alias == 
\*     [
\*         state |-> state,
\*         config |-> config,
\*         configVersion |-> configVersion,
\*         configTerm |-> configTerm,
\*         currentTerm |-> currentTerm,
\*         committed |-> committed,
\*         log |-> log,
\*         activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])]
\*     ]


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
        \* committed |-> committed,
        \* config |-> config,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)],
        activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])]
        \* configChains |-> [<<s,t>> \in ServerPair |-> ConfigChains(s,t)]
    ]


=============================================================================
