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
PositiveNat == {n \in Nat : n > 0}

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

\* The newest config log entry on a node is equivalent to its current config.
LatestConfigLogEntryMatchesConfig == 
    \A s \in Server : 
        \/ configLog[s] = <<>> /\ log[s] = <<>>
        \/ configLog[s] # <<>> /\ configLog[s][Len(configLog[s])] = config[s]

\* We encode certain assumptions into this TypeOK definition that we 
\* deem to be relatively trivial. Encoding them into the TypeOK definition
\* appears to significantly increase state generation performance when 
\* checking inductive invariance, since we aren't generating tons of invalid states 
\* only to throw them away.
TypeOKRandom == 
    /\ currentTerm \in RandomSubset(12, [Server -> Nat])
    /\ state \in RandomSubset(8, [Server -> {Secondary, Primary}])


    \* Both the main 'log' and the 'configLog' are the same length. We assume this.
    \* So, for state generation, we give the model checker some help by 
    \* making them have the same length by construction, rather than generating
    \* a bunch of random states and picking the valid ones. The rough idea is:
    \* 1. Generate a random initial 'log' state, which sets the lengths for each log.
    \* 2. Generate a random function mapping from positions in the 'log' to configs (i.e. SUBSET Server)
    \* 3. Generate each configLog deterministically from the function generated in (2).

    \* We assume that all logs start out with the same '0' entry.
    /\ \E mLog \in RandomSubset(12, [Server -> Seq(PositiveNat)]) :
        log = [i \in Server |-> <<0>> \o mLog[i]]

    \* Random element from the set of functions that map from <<s,i>> indexes to configs
    /\ LET ServerIndPairs == UNION {{<<s,i>> : i \in DOMAIN log[s]} : s \in Server} IN 
        \E cLogMap \in RandomSubset(12, [ServerIndPairs -> SUBSET Server]) :
        \E initConfig \in SUBSET Server :
        \* configLog at server 's'.
        LET ConfigLogAt(serv) == 
            (LET domain == {si[2] : si \in {p \in ServerIndPairs : p[1]=serv}} IN 
            [ind \in domain |-> 
                IF ind = 1 THEN initConfig 
                ELSE cLogMap[<<serv,ind>>]]) IN
        configLog = [s \in Server |-> ConfigLogAt(s)]
    
    \* \E cLog \in RandomSubset(165, [Server -> Seq({sub \in SUBSET Server : sub # {}})]) : 
    \*    \E initConfig \in SUBSET Server :
    \*     configLog = [i \in Server |-> <<initConfig>> \o cLog[i]]
    \* We also assume that the current config on every node is the last entry
    \* of the configLog on each node.
    /\ config = [i \in Server |-> configLog[i][Len(configLog[i])]]
    \* /\ config \in RandomSubset(10, [Server -> SUBSET Server])
    /\ committed \in RandomSetOfSubsets(10, 1, CommittedType)
    /\ elections = {} \*\in RandomSetOfSubsets(15, 1, ElectionType)

-------------------------------------------------------------------------------------

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

CommitMustUseValidQuorum == \* MSRProofs!CommitMustUseValidQuorum
    \A c \in committed : c.quorum # {} \* a quorum can be any non-empty subset of servers.
    
LeaderLogContainsPastCommittedEntries == MSRProofs!LeaderLogContainsPastCommittedEntries
CurrentTermAtLeastAsLargeAsLogTerms == MSRProofs!CurrentTermAtLeastAsLargeAsLogTerms
TermsOfEntriesGrowMonotonically == MSRProofs!TermsOfEntriesGrowMonotonically
PrimaryImpliesQuorumInTerm == MSRProofs!PrimaryImpliesQuorumInTerm
\* LogEntryInTermImpliesElectionInTerm == MSRProofs!LogEntryInTermImpliesElectionInTerm
NewerLogMustContainPastCommittedEntries == MSRProofs!NewerLogMustContainPastCommittedEntries
CommittedEntriesAreInTermOfLeader == MSRProofs!CommittedEntriesAreInTermOfLeader
LogEntryInTermMustExistInACurrentPrimaryLog == MSRProofs!LogEntryInTermMustExistInACurrentPrimaryLog
PresentElectionSafety == MSRProofs!PresentElectionSafety

ConfigsNonEmpty == 
    \A s \in Server : 
        /\ config[s] # {}
        /\ \A i \in DOMAIN configLog[s] : configLog[s][i] # {}

\* Commit quorums cannot be empty.
ValidCommitQuorums ==
    \A c \in committed : c.quorum # {}


\* Does there exist quorum of nodes in the node set 'S' that have all reached term
\* >= 't'.
QuorumAtTerm(S, t) == \E Q \in Quorums(S) : \A s \in Q : currentTerm[s] >= t 

ReconfigPairsInLog(s) == 
    {LET inew == (iold + 1) IN
     [  oldEntry |-> <<iold,log[s][iold]>>,
        newEntry |-> <<inew,log[s][inew]>>,
        configOld |-> configLog[s][iold],
        configNew |-> configLog[s][inew]] : 
        iold \in 1..(Len(log[s])-1)}

\* If we look at all logs in the system and look at every adjacent pair of
\* entries, each of these should correspond to a reconfig, either by Reconfig
\* action or a BecomeLeader action.
ReconfigPairsAll == UNION {ReconfigPairsInLog(s) : s \in Server}

\* Step up reconfigs change the term.
IsStepUpReconfig(rc) == rc.oldEntry[2] # rc.newEntry[2]

\* Normal reconfigs do not change the term.
IsNormalReconfig(rc) == rc.oldEntry[2] = rc.newEntry[2]

\* If current config exists, its parent must be committed.
ReconfigImpliesParentCommitted == 
    \A rc \in ReconfigPairsAll :
    \* If the terms are the same, this is a reconfig, so the old
    \* config must be committed.
    (rc.oldEntry[2] = rc.newEntry[2]) => \E c \in committed : c.entry = rc.oldEntry

\* If a step up reconfig log entry exists, then it must have been the result of an election, so a quorum
\* in the config of the election must have term >=T.
StepUpReconfigImpliesQuorumInTermFromElection == 
    \A rc \in ReconfigPairsAll :
    LET oldTerm == rc.oldEntry[2]
        newTerm == rc.newEntry[2] IN
    oldTerm # newTerm => QuorumAtTerm(rc.configOld, newTerm)

\* If a log entry E exists for a reconfig, then its parent (the previous log entry) must be committed.
ReconfigLogEntryImpliesParentCommitted == 
    \A s \in Server :
    \* Ignore the first element of each log.
    \A i \in ((DOMAIN log[s]) \ {1}) : 
        LET iPar == (i-1) IN
        \* Reconfig log entry is one with same term.
        (log[s][i] = log[s][iPar]) => (\E c \in committed : c.entry = <<iPar, log[s][iPar]>>)


\* If a config is committed, all ancestors are deactivated.
\* TODO?

\* Gives the index of the newest log entry in log[s] that is in a term less than T.
\* If there is no such entry, will return 1. Assumes monotonicity of terms in log.
LatestEntryBeforeTerm(s, T) == 
    LET indicesBeforeTerm == {i \in DOMAIN log[s] : log[s][i] < T} IN 
    IF indicesBeforeTerm # {} THEN Max(indicesBeforeTerm) ELSE 1

\* If a node 'i' is currently primary, we can determine what config it was elected in
\* by looking at its newest log entry index that is not in its own term. Assumes 's'
\* is currently primary.
ElectionLogIndex(s) == 
    LET nonTermInds == {i \in DOMAIN log[s] : log[s][i] < currentTerm[s]} IN
    IF nonTermInds = {} THEN -1 ELSE Max(nonTermInds)

\* Once a primary is elected, it should only append entries (i.e. reconfigs) to its log.
\* So, all commtited entries written in this primary's term must have a quorum of nodes in term >=T
\* since the primary must have been elected in a config prior to this sequence of log entries. Also,
\* the first entry before these entries must have been the one the primary was elected in, so it must
\* also have a quorum in term >= T.
ConfigsCommittedByPrimaryMustHaveQuorumAtTerm == 
    \A s \in Server : (state[s] = Primary) =>
    \A i \in DOMAIN log[s] : 
        \* All committed log entries written by this primary should have a quorum
        \* of nodes in their config with term >= T.
        (\/ (log[s][i] = currentTerm[s] /\ \E c \in committed : c.entry = <<i, log[s][i]>>) 
         \/ i = ElectionLogIndex(s)) =>
         QuorumAtTerm(configLog[s][i], currentTerm[s])

\* If a log entry exists in term T, it must have been created by a primary in term T,
\* which implies there must have been a successful election in term T. The primary of term
\* T must have been elected, though, in a config from an older term e.g. in this log
\*
\* <<0,1,1,1,2,2,2>>
\*
\* The existence of any of the entries in term T imply that the leader of term 2 must have
\* been elected in config/entry <<index=4,term=1>>. So, there must be a quorum of nodes in
\* config at <<4,1>> that have term >= T. For a log entry <<i,T>>, the election of the leader 
\* in term T must have occurred in the latest log entry in a term < T.
LogEntryInTermImpliesElectionInTerm == 
    \A s \in Server :
    \* Don't consider the initial log entry since no election created it.
    \A i \in ((DOMAIN log[s]) \ {1}) : 
        \* Look for the newest log entry in an earlier term. The election for the
        \* term of the current entry have must occurred in that entry's config.
        LET electionInd == LatestEntryBeforeTerm(s, log[s][i]) IN
        QuorumAtTerm(configLog[s][electionInd], log[s][i])

\* A node that is currently primary must be inside its own current config.
PrimaryMustBeInOwnConfig ==
    \A s \in Server : state[s] = Primary => s \in config[s]

\* For any config, its quorums must overlap with its parent.
ConfigAndParentQuorumsOverlap == 
    \A rc \in ReconfigPairsAll : QuorumsOverlap(rc.configOld, rc.configNew)

StepUpReconfigsCannotChangeConfig == 
    \A rc \in ReconfigPairsAll : IsStepUpReconfig(rc) => (rc.configOld = rc.configNew)

\* Inductive invariant.
DynamicRaftInd == 
    /\ StateMachineSafety

    /\ CommittedEntryPresentInLogs
    /\ LeaderLogContainsPastCommittedEntries
    /\ NewerLogMustContainPastCommittedEntries
    /\ CommittedEntriesAreInTermOfLeader

    /\ PresentElectionSafety
    /\ CurrentTermAtLeastAsLargeAsLogTerms
    /\ TermsOfEntriesGrowMonotonically
    /\ LogEntryInTermMustExistInACurrentPrimaryLog

    /\ LogEntryInTermImpliesElectionInTerm
    /\ ReconfigLogEntryImpliesParentCommitted
    /\ ConfigsCommittedByPrimaryMustHaveQuorumAtTerm
    /\ StepUpReconfigsCannotChangeConfig


\* Assumed or previously proved invariants that we use to make the inductive step
\* simpler.
Assumptions == 
    /\ LogAndConfigLogSameLengths 
    /\ LatestConfigLogEntryMatchesConfig
    /\ AllLogsStartWithInitConfig
    \* Basic, config related assumptions.
    /\ ConfigsNonEmpty
    /\ ValidCommitQuorums
    /\ PrimaryMustBeInOwnConfig 
    /\ ConfigAndParentQuorumsOverlap
  

IInit ==  
    /\ TypeOKRandom 
    \* /\ PrintT(<<LogAndConfigLogSameLengths,LatestConfigLogEntryMatchesConfig,AllLogsStartWithInitConfig>>)
    /\ Assumptions
    /\ DynamicRaftInd

INext == Next

\*
\* For easier error diagnosis.
\*
StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(log[s]) \o " " \o ToString(configLog[s])

Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        elections |-> elections,
        committed |-> committed,
        config |-> config,
        configLog |-> configLog,
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)],
        reconfigs |-> ReconfigPairsAll,
        electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
    ]


=============================================================================