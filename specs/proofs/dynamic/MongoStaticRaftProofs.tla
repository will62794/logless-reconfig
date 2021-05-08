----------------------------- MODULE MongoStaticRaftProofs -----------------------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, Randomization

CONSTANT MaxLogLen
CONSTANT MaxTerm
CONSTANT NumRandSubsets

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

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

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(NumRandSubsets, [Server -> Nat])
    /\ state \in RandomSubset(NumRandSubsets, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(NumRandSubsets, [Server -> Seq(PositiveNat)])

    \* Make config constant for all nodes.
    /\ config = [i \in Server |-> Server]
    \*/\ config \in RandomSubset(10, ConfigType)
    \*/\ config = [i \in Server |-> RandomSubset(2, Server)]
    (* To make config = subset of Server work we need
        1. s \in Server : t \in config[s]
        2. \A s \in Server : s \in config[s] (note this means not all configs are the same)
        3. servers not in the same config can't interact with each other.  need to confirm this
            is how Raft does it.
    *)

    \*/\ elections \in RandomSetOfSubsets(15, 1, ElectionType)
    /\ elections = {}
    /\ committed \in RandomSetOfSubsets(NumRandSubsets, 1, CommittedType)

-------------------------------------------------------------------------------------

\* Adding log matching is a whole different direction

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is node i electable in term T
Electable(i, T) == \E Q \in QuorumsAt(i) : ENABLED BecomeLeader(i, Q, T)

\*TODO: Generalize ExistsQuorumInLargestTerm to avoid reliance on quorum definition.
ElectionDisablesLesserOrEqualTerms == 
    \A i,j \in Server : 
        (state[i] = Primary) => 
        (\A leqT \in 1..currentTerm[i] : ~Electable(j, leqT))

\* If a log entry exists in term T, then an election must have occurred in term T, 
\* and so all future elections in terms <= T must be disabled. 
LogEntryInTermDisablesLesserOrEqualTerms == 
    \A i,j \in Server :
    \A term \in Range(log[i]) : 
    \A leqT \in 1..term : ~Electable(j, leqT)

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
    
ElectableNodesHaveCommittedEntries ==
    \A i \in Server :
    \A c \in committed :
        Electable(i, currentTerm[i] + 1) => 
        \E Q \in QuorumsAt(i) : \A n \in Q : InLog(c.entry, n)

LemmaBasic == TRUE
\*     /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
\*     /\ TermsOfEntriesGrowMonotonically
\*     /\ OnePrimaryPerTerm

\*     \* /\ ExistsQuorumInLargestTerm \* quorum based.
\*     /\ ElectionDisablesLesserOrEqualTerms
\*     /\ LogEntryInTermDisablesLesserOrEqualTerms

\*     /\ LogsMustBeSmallerThanOrEqualToLargestTerm
\*     /\ AllConfigsAreServer

\*     /\ PrimaryHasEntriesItCreated

LemmaSecondariesFollowPrimary == TRUE
\*     /\ LemmaBasic
\*     /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
\*     /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm

SMS_LC_II ==
    \*
    \* LEMMA Basic
    \*
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ TermsOfEntriesGrowMonotonically
    /\ OnePrimaryPerTerm
    \* /\ ExistsQuorumInLargestTerm \* quorum based.
    /\ ElectionDisablesLesserOrEqualTerms
    /\ LogEntryInTermDisablesLesserOrEqualTerms
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

    \* /\ ElectableNodesHaveCommittedEntries
    /\ CommittedEntriesMustHaveQuorums \* quorum based.


CONSTANT n1
CONSTANT n2
CONSTANT n3

N1 == {n1}
N2 == {n2}
N3 == {n3}
InitDebug == 
    /\ currentTerm = [i \in N1 |-> 1] @@ [i \in N2 |-> 3] @@ [i \in N3 |-> 3]
    /\ state       = [i \in N1 |-> Secondary] @@ [i \in N2 |-> Secondary] @@ [i \in N3 |-> Primary]
    /\ log = [i \in N1 |-> <<1, 2>>] @@ [i \in N2 |-> <<2>>] @@ [i \in N3 |-> <<2,3>>]
    /\ \E initConfig \in SUBSET Server : 
        /\ initConfig # {} \* configs should be non-empty.
        /\ config = [i \in Server |-> initConfig]
        /\ \A i \in Server : config[i] = Server
    /\ elections = {}
    /\ committed = {[term |-> 2, entry |-> <<1, 2>>]}

IInit_StateMachineSafetyNew ==  
    /\ TypeOKRandom 
    /\ SMS_LC_II 
    \*/\ LemmaSecondariesFollowPrimary
    \*/\ LemmaBasic

INext_StateMachineSafety == Next


THEOREM InitImpliesLemmaBasic ==
ASSUME TRUE
PROVE Init => LemmaBasic 
PROOF BY DEF Init, LemmaBasic


Alias == 
    [
        state |-> state,
        log |-> log,
        config |-> config,
        currentTerm |-> currentTerm,
        committed |-> committed,
        electable |-> [s \in (Server) |-> Electable(s, currentTerm[s]+1)]
    ]

=============================================================================
