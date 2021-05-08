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
\* Electable(i, T) == \E Q \in QuorumsAt(i) : ENABLED BecomeLeader(i, Q, T)

\* \*TODO: Generalize ExistsQuorumInLargestTerm to avoid reliance on quorum definition.
\* ElectionDisablesLesserOrEqualTerms == 
\*     \A i,j \in Server : 
\*         (state[i] = Primary) => 
\*         (\A leqT \in 1..currentTerm[i] : ~Electable(j, leqT))

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


TypeOKRandom == 
    /\ currentTerm \in RandomSubset(NumRandSubsets, [Server -> Nat])
    /\ state \in RandomSubset(NumRandSubsets, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(NumRandSubsets, [Server -> Seq(PositiveNat)])
    /\ config \in RandomSubset(NumRandSubsets, [Server -> SUBSET Server])
    /\ configVersion \in RandomSubset(NumRandSubsets, [Server -> PositiveNat])
    /\ configTerm \in RandomSubset(NumRandSubsets, [Server -> PositiveNat])
    /\ elections = {}
    /\ committed \in RandomSetOfSubsets(NumRandSubsets, 1, CommittedType)


Ind ==
    \*
    \* LEMMA Basic
    \*
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ TermsOfEntriesGrowMonotonically
    /\ OnePrimaryPerTerm
    \* /\ ExistsQuorumInLargestTerm \* quorum based.

    \* /\ ElectionDisablesLesserOrEqualTerms
    \* /\ LogEntryInTermDisablesLesserOrEqualTerms

    /\ LogsMustBeSmallerThanOrEqualToLargestTerm
    /\ AllConfigsAreServer
    /\ PrimaryHasEntriesItCreated

    \*
    \* LEMMA Secondaries Follow Primary.
    \*
    \* /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    \* /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm  

    \*
    \* LEMMA Extra
    \*
    /\ CommittedTermMatchesEntry
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ LogsEqualToCommittedMustHaveCommittedIfItFits
    /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
    /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    /\ LeaderCompletenessGeneralized

    \* /\ ElectableNodesHaveCommittedEntrielslss
    /\ CommittedEntriesMustHaveQuorums \* quorum based.

IInit == 
    /\ TypeOKRandom
    /\ Ind


=============================================================================
