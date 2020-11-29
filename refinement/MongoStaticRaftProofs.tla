----------------------------- MODULE MongoStaticRaftProofs -----------------------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, Randomization

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

\* Re-define some things locally for convenience.
Quorums(S) == MWR!Quorums(S)
InLog(e,i) == MWR!InLog(e,i)
LastTerm(l) == MWR!LastTerm(l)

ElectionType == [ leader : Server, 
                  term   : Nat, 
                  quorum : SUBSET Server]

CommittedType == 
    [ entry  : PositiveNat \times PositiveNat,
      quorum : SUBSET Server,
      term : Nat]

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(20, [Server -> Nat])
    /\ state \in RandomSubset(20, [Server -> {Secondary, Primary}])
    /\ log \in RandomSubset(30, [Server -> Seq(PositiveNat)])
    \* Make config constant for all nodes.
    /\ config = [i \in Server |-> Server]
    \* /\ elections \in RandomSetOfSubsets(15, 1, ElectionType)
    /\ elections = {}
    /\ committed \in RandomSetOfSubsets(20, 1, CommittedType)

\* Condition that all nodes have the same config. For these proofs we assume this,
\* which essentially makes the protocol we're proving MongoStaticRaft.
\* StricterQuorumCondition == \A s \in Server : config[s] = Server
\* NextStrict == Next /\ StricterQuorumCondition'
\* SpecStricterQuorums ==   Init /\ [][Next /\ StricterQuorumCondition']_vars

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
IInit_ElectionSafety ==  TypeOKRandom /\ ElectionSafetyInd
INext_ElectionSafety == Next

-------------------------------------------------------------------------------------

(*** LogMatching ***)

\* Inductive invariant.
LogMatchingInd == 
    /\ MWR!LogMatching

\* Check inductive invariance.
IInit_LogMatching ==  
    /\ TypeOKRandom 
    /\ ElectionSafety \* we assume that this invariant holds.
    /\ LogMatchingInd

INext_LogMatching == Next

-------------------------------------------------------------------------------------

(*** StateMachineSafety ***)

\* Election safety holds in the current state.
PresentElectionSafety == 
    \A s,t \in Server : 
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ s # t) => currentTerm[s] # currentTerm[t]

\* If a primary exists in term T, it implies a quorum of node reached term >= T.
PrimaryImpliesQuorumInTerm == 
    \A s \in Server : 
        (state[s] = Primary) => 
        \E Q \in MWR!QuorumsAt(s) : \A q \in Q : currentTerm[q] >= currentTerm[s]

\* If a log entry is committed by a quorum Q, it must be present in the log of each node
\* in Q.
CommittedEntryPresentInLogs == 
    \A c \in committed : \A s \in c.quorum : MWR!InLog(c.entry, s)

\* A node must have committed a log entry using some quorum of the global config.
CommitMustUseValidQuorum == 
    \A c \in committed : c.quorum \in MWR!Quorums(Server)


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
        (\A c \in committed : c.term <= currentTerm[s] => InLog(c.entry, s))

\* If a log entry in term T exists, it must have been created by a leader in term T. So,
\* there must exist a quorum in terms >= T since an election must have occurred in T.
LogEntryInTermImpliesElectionInTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] : 
    (\E Q \in Quorums(Server) : \A q \in Q : currentTerm[q] >= log[s][i])



\* Could a node with log 'li' cast a vote for a node with log 'lj'.
LogCouldVote(li, lj) == 
    \/ LastTerm(lj) > LastTerm(li)
    \/ /\ LastTerm(lj) = LastTerm(li)
           /\ Len(lj) >= Len(li)

\* If a node is currently primary, it means that it must have won election with the log it
\* had at the time it was elected, which is its current log ignoring any entries  
\* in its current term.
CurrentPrimaryImpliesWinningLog == 
    \A s \in Server :
    (state[s] = Primary) => 
    (\E Q \in Quorums(Server) : \A q \in Q : 
        \* Consider the other log but without any entries >= T, since we expect
        \* those could have only been created after this election occurred.
        LET logAtElection == SelectSeq(log[s], LAMBDA e : e # currentTerm[s])
            otherLog == SelectSeq(log[q], LAMBDA e : e < currentTerm[s]) IN
        LogCouldVote(otherLog, logAtElection))

\* If a node's log contains an entry in term U, it must contain all entries committed in terms
\* T < U.
NewerLogMustContainPastCommittedEntries == 
    \A s \in Server : 
    \A c \in committed : 
        (\E i \in DOMAIN log[s] : log[s][i] > c.term) => InLog(c.entry, s)

CommittedEntriesAreInTermOfLeader == 
    \A c \in committed : c.term = c.entry[2]

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) == 
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

\* If a particular log entry E exists with term T, it must have been created
\* uniquely by some primary, since we know there can only be 1 primary per term.
\* This means that any log that exists with entries in term T must be a prefix
\* of this log.
LogEntryIsUniqueToPrimaryCreator == 
    \* If two nodes both have a log entry in term T, then one must be a prefix of the other.
    \A s,t \in Server :
        (\E i \in DOMAIN log[s] : \E j \in DOMAIN log[t] : log[s][i] = log[t][j]) =>
            \/ IsPrefix(log[s], log[t]) 
            \/ IsPrefix(log[t], log[s])

\* If there exists a log entry in term T, and there exists a node that is 
\* currently primary in term T, then the entry must exist in that node's log.
LogEntryInTermMustExistInACurrentPrimaryLog == 
    \A s \in Server :
    \A i \in DOMAIN log[s] : 
        \A t \in Server : 
        (state[t] = Primary /\ currentTerm[t] = log[s][i]) => InLog(<<i, log[s][i]>>, t)

\*
\* The inductive invariant.
\*
StateMachineSafetyInd == 
    /\ StateMachineSafety
    /\ CommittedEntryPresentInLogs
    /\ CommitMustUseValidQuorum
    /\ LeaderLogContainsPastCommittedEntries
    /\ CurrentTermAtLeastAsLargeAsLogTerms
    /\ TermsOfEntriesGrowMonotonically
    /\ PrimaryImpliesQuorumInTerm
    /\ LogEntryInTermImpliesElectionInTerm
    /\ NewerLogMustContainPastCommittedEntries
    /\ CommittedEntriesAreInTermOfLeader
    /\ LogEntryInTermMustExistInACurrentPrimaryLog

\* Assumptions or previously proven invariants that we use to help make
\* inductive proof easier. These follow from the rule that, if Inv1, Inv2, etc. is known to hold,
\* then it suffices to show that Inv1 /\ Inv2 /\ IndInv /\ Next => IndInv' for the
\* inductive step.
Assumptions == 
    /\ PresentElectionSafety
    /\ MWR!LogMatching

IInit_StateMachineSafety ==  
    /\ TypeOKRandom 
    /\ Assumptions
    /\ StateMachineSafetyInd

INext_StateMachineSafety == Next

-------------------------------------------------------------------------------------

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