----------------------------- MODULE MongoDynamicRaftProofs -----------------------------

\* Proving inductive invariance for dynamic Raft reconfiguration. (experimental)

EXTENDS MongoDynamicRaft, Randomization

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
    /\ currentTerm \in RandomSubset(7, [Server -> Nat])
    /\ state \in RandomSubset(5, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(5, [Server -> Seq(PositiveNat)])
    /\ config \in RandomSubset(5, [Server -> SUBSET Server])
    /\ configLog \in RandomSubset(5, [Server -> Seq(SUBSET Server)])
    /\ committed \in RandomSetOfSubsets(5, 1, CommittedType)
    /\ elections \in RandomSetOfSubsets(5, 1, ElectionType)

-------------------------------------------------------------------------------------

\* The newest config log entry on a node is equivalent to its current config.
LatestConfigLogEntryMatchesConfig == 
    \A s \in Server : (configLog[s] # <<>>) => configLog[s][Len(configLog[s])] = config[s]

\* Assume this for now to prevent out of bounds errors. We could prove it separately.
LogAndConfigLogSameLengths ==
    \A s \in Server : Len(log[s]) = Len(configLog[s])

\* Inductive invariant.
WeakQuorumConditionInd == 
    /\ MWR!WeakQuorumCondition

\* Assumed or previously proved invariants that we use to make the inductive step
\* simpler.
Assumptions == 
    /\ LogAndConfigLogSameLengths 
    /\ LatestConfigLogEntryMatchesConfig
    /\ LogMatching
    /\ StateMachineSafety

IInit ==  
    /\ TypeOKRandom 
    /\ Assumptions
    /\ WeakQuorumConditionInd

INext == Next


=============================================================================