----------------------------- MODULE MongoStaticRaftProofs -----------------------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, Randomization

CONSTANT MaxLogLen
CONSTANT MaxTerm
CONSTANT NumRandSubsets

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

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

LemmaBasic ==
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ TermsOfEntriesGrowMonotonically
    /\ OnePrimaryPerTerm
    /\ ExistsQuorumInLargestTerm
    /\ LogsMustBeSmallerThanOrEqualToLargestTerm
    /\ AllConfigsAreServer

LemmaSecondariesFollowPrimary ==
    /\ LemmaBasic
    /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm

SMS_LC_II ==
    /\ LemmaSecondariesFollowPrimary
    /\ CommitIndexGreaterThanZero
    /\ CommittedTermMatchesEntry
    /\ CommittedEntryIndMustBeSmallerThanOrEqualtoAllLogLens
    /\ CommittedEntryTermMustBeSmallerThanOrEqualtoAllTerms
    /\ LeaderCompletenessGeneralized
    /\ LogsEqualToCommittedMustHaveCommittedIfItFits
    /\ LogsLaterThanCommittedMustHaveCommitted
    /\ CommittedEntriesMustHaveQuorums
    /\ StateMachineSafety


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

=============================================================================
