----------------------------- MODULE MongoWeakRaftProofs -----------------------------

\* Proving inductive invariance for dynamic Raft reconfiguration. (experimental)

EXTENDS MongoWeakRaft, Randomization

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

ElectionType == [ leader : Server, 
                  term   : Nat, 
                  quorum : SUBSET Server]

CommittedType == 
    [ entry  : PositiveNat \times PositiveNat,
      quorum : SUBSET Server,
      term : Nat]

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(10, [Server -> Nat])
    /\ state \in RandomSubset(15, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(30, [Server -> Seq(PositiveNat)])
    \* Make config constant for all nodes.
    /\ config = [i \in Server |-> Server]
    \* /\ elections \in RandomSetOfSubsets(15, 1, ElectionType)
    /\ elections = {}
    /\ committed \in RandomSetOfSubsets(15, 1, CommittedType)

\* Condition that all nodes have the same config. For these proofs we assume this,
\* which essentially makes the protocol we're proving MongoStaticRaft.
StricterQuorumCondition == \A s \in Server : config[s] = Server
NextStrict == Next /\ StricterQuorumCondition'

-------------------------------------------------------------------------------------

(*** ElectionSafety ***)

\* If a node has been elected in term T, all nodes in its quorum must have reached term T or greater.
ElectionImpliesQuorumInTerm == 
    \A e \in elections : \A s \in e.quorum : currentTerm[s] >= e.term

\* An election quorum must be from the set of valid quorums.
ElectionQuorumsValid == 
    \A e \in elections : e.quorum \in Quorums(Server)

\* Prove ElectionSafety inductively.
ElectionSafetyInd == 
    /\ ElectionSafety
    /\ ElectionImpliesQuorumInTerm
    /\ ElectionQuorumsValid

\* Check inductive invariance.
IInit_ElectionSafety ==  TypeOKRandom /\ StricterQuorumCondition /\ ElectionSafetyInd
INext_ElectionSafety == NextStrict

-------------------------------------------------------------------------------------

(*** LogMatching ***)

\* Inductive invariant.
LogMatchingInd == 
    /\ LogMatching

\* Check inductive invariance.
IInit_LogMatching ==  
    /\ TypeOKRandom 
    /\ StricterQuorumCondition 
    /\ ElectionSafety \* we assume that this invariant holds.
    /\ LogMatchingInd

INext_LogMatching == NextStrict

-------------------------------------------------------------------------------------

(*** StateMachineSafety ***)

\* If a log entry is committed by a quorum Q, it must be present in the log of each node
\* in Q.
CommittedEntryPresentInLogs == 
    \A c \in committed : \A s \in c.quorum : InLog(c.entry, s)

\* A node must have committed a log entry using some quorum of the global config.
CommitMustUseValidQuorum == 
    \A c \in committed : c.quorum \in Quorums(Server)


\* If a node is currently primary in term T, an election in term T must have been recorded.
PrimaryNodeImpliesElectionRecorded == 
    \A s \in Server : state[s] = Primary => (\E e \in elections : 
                                                /\ e.term = currentTerm[s]
                                                /\ e.leader = s)

\* A server's current term is always at least as large as the terms in its log.
\* This is LEMMA 6 from the Raft dissertation.
CurrentTermAtLeastAsLargeAsLogTerms == 
    \A s \in Server : \A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i]

\* The terms of entries grow monotonically in each log.
\* This is LEMMA 7 from the Raft dissertation.
TermsOfEntriesGrowMonotonically ==
    \A s \in Server : \A i \in 1..(Len(log[s])-1) : log[s][i] <= log[s][i+1] 

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderLogContainsPastCommittedEntries ==
    \A s \in Server : 
        (state[s] = Primary) =>
            (\A c \in committed : c.term < currentTerm[s] => InLog(c.entry, s))


\* If a log entry in term T exists, it must have been created by a leader in term T. So
\* an election in term T must exist.
LogEntryInTermImpliesElectionInTerm == 
    \A s \in Server : \A i \in DOMAIN log[s] : (\E e \in elections : e.term = log[s][i])

\* Inductive invariant.
StateMachineSafetyInd == 
    /\ StateMachineSafety
    /\ CommittedEntryPresentInLogs
    /\ CommitMustUseValidQuorum
    /\ LeaderLogContainsPastCommittedEntries
    /\ CurrentTermAtLeastAsLargeAsLogTerms
    /\ TermsOfEntriesGrowMonotonically

    \* Election related invariants.
    \* /\ PrimaryNodeImpliesElectionRecorded
    \* /\ ElectionImpliesQuorumInTerm
    \* /\ LogEntryInTermImpliesElectionInTerm

\* Assumptions or previously proven invariants that we use to help make
\* inductive proof easier. These follow from the rule that, if Inv1, Inv2, etc. is known to hold,
\* then it suffices to show that Inv1 /\ Inv2 /\ IndInv /\ Next => IndInv' for the
\* inductive step.
Assumptions == 
    /\ ElectionSafety
    /\ LogMatching
    /\ ElectionQuorumsValid

IInit_StateMachineSafety ==  
    /\ TypeOKRandom 
    /\ StricterQuorumCondition 
    /\ Assumptions
    /\ StateMachineSafetyInd

INext_StateMachineSafety == NextStrict

\*
\* For easier error diagnosis.
\*
StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "--------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(log[s])

Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        elections |-> elections,
        committed |-> committed,
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)]
    ]

=============================================================================