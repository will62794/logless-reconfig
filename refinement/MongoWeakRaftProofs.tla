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
    /\ state \in RandomSubset(8, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(7, [Server -> Seq(PositiveNat)])
    \* Make config constant for all nodes.
    /\ config = [i \in Server |-> Server]
    /\ committed \in RandomSetOfSubsets(6, 1, CommittedType)
    /\ elections \in RandomSetOfSubsets(6, 1, ElectionType)

\* Condition that all nodes have the same config.
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

\* If a node is primary, it must contain all committed entries from previous terms in its log.
LeaderLogContainsPastCommittedEntries ==
    \A s \in Server : 
        (state[s] = Primary) =>
            (\A c \in committed : c.term < currentTerm[s] => InLog(c.entry, s))

\* Inductive invariant.
StateMachineSafetyInd == 
    /\ StateMachineSafety
    /\ CommittedEntryPresentInLogs
    /\ CommitMustUseValidQuorum
    /\ PrimaryNodeImpliesElectionRecorded
    /\ LeaderLogContainsPastCommittedEntries

IInit_StateMachineSafety ==  
    /\ TypeOKRandom 
    /\ StricterQuorumCondition 
    /\ LogMatching \* assume this invariant holds.
    /\ StateMachineSafetyInd

INext_StateMachineSafety == NextStrict


=============================================================================