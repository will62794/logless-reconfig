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

ElectionType == [ leader : Server, 
                  term   : Nat, 
                  quorum : SUBSET Server]

CommittedType == 
    [ entry  : Nat \times Nat,
      quorum : SUBSET Server]

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(5, [Server -> Nat])
    /\ state \in RandomSubset(5, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(5, [Server -> Seq([term  : Nat])])
    /\ config \in RandomSubset(1, [Server -> SUBSET Server])
    /\ committed \in RandomSetOfSubsets(5, 1, CommittedType)
    /\ elections \in RandomSetOfSubsets(5, 1, ElectionType)

\* \*
\* \* Decompose the inductive invariant into subcomponents for easier reasoning.
\* \*

\* \* If you are a primary, a quorum should have voted for you, so are in your term or greater.
\* PrimaryHasQuorumInConfigInTermOrGreater == 
\*     \A s \in Server : (state[s] = Primary) => 
\*         (\E voters \in Quorums(config[s]) : 
\*          (\A v \in voters : currentTerm[v] >= currentTerm[s]))

\* \* If you are a primary, a quorum should have voted for you, so a quorum in the config that 
\* \* you were elected in should have your term or greater.
\* PrimaryHasQuorumInElectionConfigInTermOrGreater == 
\*     \A e \in elections : 
\*        (\E voters \in Quorums(e.config.m) : 
\*          (\A v \in voters : currentTerm[v] >= e.term))

\* \* If you are a primary, a quorum should have voted for you, so a quorum in your election config should 
\* \* have configs the same or newer than the config you got elected in.
\* \*PrimaryHasQuorumInElectionConfigInConfigOrNewer == 
\* \*    \A e \in elections : 
\* \*       (\E voters \in Quorums(e.config) : 
\* \*         (\A v \in voters : 
\* \*            \/ configTerm[e.leader] >= e.configTerm
\* \*            \/ /\ configTerm[e.leader] = e.configTerm
\* \*               /\ configVersion[e.leader] >= e.configVersion))

\* PrimaryConfigsMonotonic == 
\*     \A e \in elections : 
\*         \/ configTerm[e.leader] >= e.config.t
\*         \/ /\ configTerm[e.leader] = e.config.t
\*            /\ configVersion[e.leader] >= e.config.v
        
\* \* The config term of a primary should be equal to its current term.
\* PrimarysCurrentConfigIsInOwnTerm == 
\*     \A s \in Server : (state[s] = Primary) => (configTerm[s] = currentTerm[s])

\* ConfigTermNotGreaterThanCurrentTerm == 
\*     \A s \in Server : configTerm[s] <= currentTerm[s]

\* \* A primary's current config has at least one member.
\* \* This should be true since a primary cannot remove itself from its config. 
\* PrimaryConfigHasAtLeastOneMember == \A s \in Server : state[s] = Primary => config[s] # {}

\* PrimaryElectionRecorded == 
\*     \A s \in Server : 
\*     (state[s] = Primary) => 
\*         \E e \in elections : 
\*             /\ e.leader = s 
\*             /\ e.term = currentTerm[s]


\* \* If a config C exists, then it must have been created via some reconfig or it is the initial config.
\* ConfigExistenceImpliesReconfigOccurred == 
\*     \A s \in Server :
\*         \* Has a config created by a reconfig.
\*         \/ (\E rc \in reconfigs : 
\*              /\ rc.new.m = config[s]
\*              /\ rc.new.v = configVersion[s]
\*              /\ rc.new.t = configTerm[s])
\*         \* Has the initial config.
\*         \/ /\ configVersion[s] = 0
\*            /\ configTerm[s] = 0      

\* \* If we moved to config C, then the parent of C must have been committed.
\* \* TODO.
\* ReconfigRequiresParentWasCommitted == 
\*     \A rc \in reconfigs:
\*     \E configQuorum \in Quorums(rc.old.m) :
\*     \* Config should have been committed by a quorum,
\*     \* so this quorum should have this config or a newer one. 
\*     \A s \in configQuorum :
\*         NewerOrEqualConfig(<<configVersion[s], configTerm[s]>>,
\*                            <<rc.old.v, rc.old.t>>)
                           
\* \* Reconfigs that are not step up reconfigs cannot change config term. 
\* NormalReconfigsDoNotChangeConfigTerm == 
\*     \A rc \in reconfigs : 
\*         \/ rc.new.t = rc.old.t
\*         \* Step up reconfigs are the only case where version is not incremented.
\*         \/ /\ rc.new.t > rc.new.t
\*            /\ rc.new.v = rc.old.v

\* \* If all nodes are in the initial config <<0, 0>>, then they should all have the same config i.e.
\* \* we always start out in a static config.
\* AllNodesInInitialConfigImpliesAllNodesHaveSameConfig == 
\*     (\A s \in Server : configVersion[s] = 0 /\ configTerm[s] = 0) =>
\*     (\A s,t \in Server : config[s] = config[t])

\* \* Inductive invariant for proving election safety.
\* \* TODO: More work to expand this to handle safety under reconfigurations.
\* ElectionSafetyInd == 
\*     /\ ElectionSafety
\*     /\ PrimaryHasQuorumInElectionConfigInTermOrGreater
\*     /\ PrimaryConfigsMonotonic
\*     /\ PrimarysCurrentConfigIsInOwnTerm
\*     /\ PrimaryConfigHasAtLeastOneMember
\*     /\ PrimaryElectionRecorded
    (*/\ ConfigTermNotGreaterThanCurrentTerm
    /\ ConfigExistenceImpliesReconfigOccurred
    /\ ReconfigRequiresParentWasCommitted*)
    
    \* /\ AllNodesInInitialConfigImpliesAllNodesHaveSameConfig
    \* /\ NormalReconfigsDoNotChangeConfigTerm

StateMachineSafetyInd == 
    /\ StateMachineSafety

\* All nodes have the same config.
StricterQuorumCondition == \A s \in Server : config[s] = Server
\* NextStrict == Next /\ StrictQuorumCondition'
NextStrict == Next /\ StricterQuorumCondition'

IndInv == StateMachineSafetyInd
IInit ==  TypeOKRandom /\ StricterQuorumCondition /\ IndInv
INext == NextStrict


=============================================================================