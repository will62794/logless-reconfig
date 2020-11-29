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

\* All logs start out with an initial entry in term 0, which all store
\* the same, initial config.
AllLogsStartWithInitConfig == 
    \A s,t \in Server : 
        /\ Len(log[s]) > 0
        /\ Len(log[t]) > 0
        /\ log[s][1] = 0 
        /\ log[t][1] = 0
        /\ configLog[s][1] = configLog[t][1]

\* Assume this for now to prevent out of bounds errors. We could prove it separately.
LogAndConfigLogSameLengths ==
    \A s \in Server : Len(log[s]) = Len(configLog[s])

\* We encode certain assumptions into this TypeOK definition that we 
\* deem to be relatively trivial. Encoding them into the TypeOK definition
\* appears to significantly increase state generation performance when 
\* checking inductive invariance, since we aren't generating tons of invalid states 
\* only to throw them away.
TypeOKRandom == 
    /\ currentTerm \in RandomSubset(10, [Server -> Nat])
    /\ state \in RandomSubset(8, [Server -> {Secondary, Primary}])
    \* We assume that all logs start out with the same '0' entry.
    /\ \E mLog \in RandomSubset(15, [Server -> Seq(PositiveNat)]) :
        log = [i \in Server |-> <<0>> \o mLog[i]]
    \* We assume that the configLog is a function of the 'log' i.e. it
    \* has the same length on every node, but with different entries.
    /\ \E cLog \in RandomSubset(15, [Server -> Seq(SUBSET Server)]) : 
       \E initConfig \in SUBSET Server :
        configLog = [i \in Server |-> <<initConfig>> \o cLog[i]]
    /\ LogAndConfigLogSameLengths
    /\ AllLogsStartWithInitConfig
    \* We also assume that the current config on every node is the last entry
    \* of the configLog on each node.
    /\ config = [i \in Server |-> configLog[i][Len(configLog[i])]]
    \* /\ config \in RandomSubset(10, [Server -> SUBSET Server])
    /\ committed \in RandomSetOfSubsets(10, 1, CommittedType)
    /\ elections = {} \*\in RandomSetOfSubsets(15, 1, ElectionType)

-------------------------------------------------------------------------------------

\* The newest config log entry on a node is equivalent to its current config.
LatestConfigLogEntryMatchesConfig == 
    \A s \in Server : 
        \/ configLog[s] = <<>> /\ log[s] = <<>>
        \/ configLog[s] # <<>> /\ configLog[s][Len(configLog[s])] = config[s]

MSRProofs == INSTANCE MongoStaticRaftProofs
    WITH MaxTerm <- MaxTerm,
         MaxLogLen <- MaxLogLen,
         MaxConfigVersion <- MaxConfigVersion,
         Server <- Server,
         Secondary <- Secondary,
         Primary <- Primary,
         Nil <- Nil,
         currentTerm <- currentTerm,
         state <- state,
         config <- config,
         elections <- elections,
         committed <- committed

CommittedEntryPresentInLogs == MSRProofs!CommittedEntryPresentInLogs
CommitMustUseValidQuorum == MSRProofs!CommitMustUseValidQuorum
LeaderLogContainsPastCommittedEntries == MSRProofs!LeaderLogContainsPastCommittedEntries
CurrentTermAtLeastAsLargeAsLogTerms == MSRProofs!CurrentTermAtLeastAsLargeAsLogTerms
TermsOfEntriesGrowMonotonically == MSRProofs!TermsOfEntriesGrowMonotonically
PrimaryImpliesQuorumInTerm == MSRProofs!PrimaryImpliesQuorumInTerm
LogEntryInTermImpliesElectionInTerm == MSRProofs!LogEntryInTermImpliesElectionInTerm
NewerLogMustContainPastCommittedEntries == MSRProofs!NewerLogMustContainPastCommittedEntries
CommittedEntriesAreInTermOfLeader == MSRProofs!CommittedEntriesAreInTermOfLeader
LogEntryInTermMustExistInACurrentPrimaryLog == MSRProofs!LogEntryInTermMustExistInACurrentPrimaryLog

\* Inductive invariant.
WeakQuorumConditionInd == 
    MSRProofs!StateMachineSafetyInd
    \* /\ MWR!WeakQuorumCondition

\* Assumed or previously proved invariants that we use to make the inductive step
\* simpler.
Assumptions == 
    /\ LogAndConfigLogSameLengths 
    /\ LatestConfigLogEntryMatchesConfig
    /\ AllLogsStartWithInitConfig
    \* /\ LogMatching
    \* /\ MSRProofs!StateMachineSafetyInd

IInit ==  
    /\ TypeOKRandom 
    /\ Assumptions
    /\ WeakQuorumConditionInd

INext == Next

\* For easier error diagnosis.
Alias == MSRProofs!Alias


=============================================================================