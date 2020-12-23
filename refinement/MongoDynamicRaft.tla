---- MODULE MongoDynamicRaft ----
\* Dynamic Raft protocol that allows ops to change quorum definition on nodes.

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE config

VARIABLE configLog \* shadow of 'log' variable which stores config at a log index.

\* Implementation variable stored to support rolling back to the initial config.
\* TODO: Can hopefully get rid of this eventually by abstracting away rollback.
VARIABLE initConfig 

VARIABLE elections
VARIABLE committed

serverVars == <<currentTerm, state, log>>
vars == <<currentTerm, state, log, elections, committed, config, configLog, initConfig>>

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

MWR == INSTANCE MongoWeakRaft 
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

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
QuorumsAt(i) == Quorums(config[i])
    
\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]
   
\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk
    
-------------------------------------------------------------------------------------------

(***************************************************************************)
(* Next state actions.                                                     *)
(***************************************************************************)

\* Exchange terms between two nodes and step down the primary if needed.
UpdateTerms(i, j) ==
    \* Update terms of sender and receiver i.e. to simulate an RPC request and response (heartbeat).
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* May update state of sender or receiver.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Secondary ELSE state[j],
                              ![i] = IF currentTerm[i] < currentTerm[j] THEN Secondary ELSE state[i] ]

UpdateTermsOnNodes(i, j) == /\ UpdateTerms(i, j)

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ configLog' = [configLog EXCEPT ![i] = SubSeq(configLog[i], 1, Len(configLog[i])-1)]
    \* Roll back your config state as well. If we are rolling back our only log entry,
    \* then go back to the initial config.
    /\ config' = [config EXCEPT ![i] = 
                    IF Len(log[i]) = 1 THEN initConfig
                    ELSE configLog[i][Len(configLog[i])-1]]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<elections, committed, initConfig>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
              \* We also propagate the config via logs.
              /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], configLog[j][newEntryIndex])]
              /\ config' = [config EXCEPT ![i] = configLog[j][newEntryIndex]]
    /\ UpdateTerms(i, j)

    /\ UNCHANGED <<elections, committed, initConfig>>

\* Is the last log entry of node 'i' currently committed.
LastIsCommitted(i) == 
    \/ Len(log[i]) = 0 \* consider an empty log as being committed.
    \/ /\ Len(log[i]) > 0
       /\ \E c \in committed : 
            c.entry = <<Len(log[i]), log[i][Len(log[i])]>>

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log. It also executes a reconfig.                                                         
ClientRequest(i, newConfig) ==
    \* Make sure the current log entry is committed before reconfiguring.
    /\ LastIsCommitted(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig \* don't remove yourself from config.
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], newConfig)]
    /\ MWR!ClientRequest(i)
    /\ UNCHANGED <<initConfig>>

BecomeLeader(i, voteQuorum) == 
    /\ MWR!BecomeLeader(i, voteQuorum)
    \* Must write a no-op on step up so that it must be committed before a config change can occur.
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i] + 1)]
    \* The config does not change but we write a dummy log entry.
    /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], config[i])]
    /\ UNCHANGED <<config, initConfig>>   

CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ \A s \in commitQuorum :
        /\ Len(log[s]) >= ind
        /\ log[s][ind] = log[i][ind]        \* they have the entry.
        /\ currentTerm[s] = currentTerm[i]  \* they are in the same term.
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c.entry = <<ind, currentTerm[i]>>
    /\ committed' = committed \cup
            {[ entry  |-> <<ind, currentTerm[i]>>,
               quorum |-> commitQuorum,
               term  |-> currentTerm[i]]}
    /\ UNCHANGED <<currentTerm, state, log, elections, config, configLog, initConfig>>

\* Is node 'i' currently electable with quorum 'q'.
Electable(i, q) == ENABLED BecomeLeader(i, q)


Init ==
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ \E initCfg \in SUBSET Server : 
        /\ initCfg # {}
        /\ config = [i \in Server |-> initCfg]
        /\ configLog = [i \in Server |-> <<>>]
        \* Save the initial config in case of rollback.
        /\ initConfig = initCfg
    /\ elections = {}
    /\ committed = {}


\* Defined separately to improve error reporting when model checking.
BecomeLeaderAction == \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
CommitEntryAction == \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)

Next == 
    \/ \E s \in Server : \E newConfig \in SUBSET Server : ClientRequest(s, newConfig)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ BecomeLeaderAction
    \/ CommitEntryAction

Spec == Init /\ [][Next]_vars

MSWR == INSTANCE MongoSafeWeakRaft 
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

MSWLR == INSTANCE MongoSafeWeakLockstepRaft 
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

ElectionSafety == MWR!ElectionSafety
LeaderCompleteness == MWR!LeaderCompleteness
LogMatching == MWR!LogMatching

\* Variant of LogMatching property that also takes into account the values in the 'configLog'.
LogMatchingWithConfigs == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        /\ (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.
        /\ (SubSeq(configLog[s],1,i) = SubSeq(configLog[t],1,i))\* configLog values must match.


StateMachineSafety == MWR!StateMachineSafety
WeakQuorumCondition == MSWR!WeakQuorumCondition
StrictQuorumCondition == MWR!StrictQuorumCondition

LockstepCondition == MSWLR!LockstepCondition

\* Reconfig history edges in the log of node 's'.
ReconfigEdges(s) == {[old |-> [m |-> configLog[s][k], i |-> k+1, t |-> log[s][k] ], 
                      new |-> [m |-> configLog[s][k+1], i |-> k+1, t |-> log[s][k+1]]] : k \in 1..(Len(log[s])-1)}

\* The configuration history structure.
ConfigHistoryEdges == UNION {ReconfigEdges(s) : s \in Server}    
ConfigHistoryNodes == UNION {{rc.old, rc.new} : rc \in ConfigHistoryEdges}

AllConfigs == UNION {Range(configLog[s]) : s \in Server}

\* Set of all paths in the history graph.
Paths == {p \in Seq(ConfigHistoryNodes) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : [old |-> p[i], new |-> p[i+1]] \in ConfigHistoryEdges}

\* Is there a path from config ci to cj in the history.
Path(ci, cj) == \E p \in Paths : p[1] = ci /\ p[Len(p)] = cj

\* Is config ci an ancestor of cj.
Ancestor(ci, cj) == Path(ci, cj)

\* Is config ci a descendant of cj.
Descendant(ci, cj) == Path(cj, ci)

\* Is config ci a sibling of cj i.e. are they on different branches with a common
\* ancestor.
Sibling(ci, cj) == 
    /\ \E a \in ConfigHistoryNodes : Ancestor(a, ci) /\ Ancestor(a, cj)
    /\ ~Ancestor(ci, cj)
    /\ ~Ancestor(cj, ci)

\* Takes a path and returns the set of edges making up that path.
EdgesInPath(p) == {[old |-> p[i], new |-> p[i+1]] : i \in 1..(Len(p)-1)}

\* Compares to see if it1=<<index1,term1>> is newer than it2=<<index2,term2>>
NewerIndTerm(it1,it2) == 
    \/ (it1[2] = it2[2] /\ it1[1] > it2[1])
    \/ it1[2] > it2[2]

\* The newest common ancestor between two nodes. Assume ci and cj are siblings.
NewestCommonAncestor(ci, cj) ==
    LET commonAncestors == {c \in ConfigHistoryNodes : Ancestor(c, ci) /\ Ancestor(c, cj)} IN
    CHOOSE newestCA \in commonAncestors :
        \A otherCA \in commonAncestors : 
            /\ (otherCA # newestCA) => NewerIndTerm(<<newestCA.i,newestCA.t>>, <<otherCA.i,otherCA.t>>)

\* Returns the number of reconfig edges in the given path 'p'.
NReconfigs(p) == 
    \* Edges where terms don't change are considered 'reconfig' edges.
    Cardinality({e \in EdgesInPath(p) : e = e[2][2]})

\* A config is deactivated if it is prevented from holding elections now or in the future.
\* That is, no quorum in the config could hold a successful election.
Deactivated(c) == 
    \A Q \in Quorums(c.m) : \E s \in Q : NewerIndTerm(<<Len(log[s]),log[s][Len(log[s])]>>, <<c.i,c.t>>)

\* If two configs C1, C2 on sibling branches have non overlapping quorums,
\* one of them must be committed and one of them must be deactivated.
NonOverlappingSiblingConfigsMutuallyExclusiveCommit == 
    \A c1, c2 \in ConfigHistoryNodes :
    (/\ Sibling(c1,c2) 
     /\ ~QuorumsOverlap(c1.m, c2.m)) => 
        \E c \in committed : 
        LET nca == NewestCommonAncestor(c1, c2) IN
            \/ (c.entry = <<c1.i,c1.t>>) \/ \A x \in Range(Path(nca, c2)) : Deactivated(x)
            \/ (c.entry = <<c2.i,c2.t>>) \/ \A x \in Range(Path(nca, c1)) : Deactivated(x)

\*
\* Refinement definitions.
\*

THEOREM MDRRefinesMWR == Spec => MWR!Spec
THEOREM MDRWeakQuorumCondition == Spec => []MSWR!WeakQuorumCondition

RefinesMongoWeakRaft == MWR!Spec
RefinesMongoSafeWeakRaft == MSWR!Spec
RefinesMongoSafeWeakLockstepRaft == MSWLR!Spec

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

ServerSymmetry == Permutations(Server)

SeqOf(set, n) == 
  UNION {[1..m -> set] : m \in 0..n}

BoundedSeq(S) == SeqOf(S, Max(Nat))

\* For debugging.
Alias == 
    [
        currentTerm |-> currentTerm,
        state |-> state,
        log |-> log,
        elections |-> elections,
        committed |-> committed,
        config |-> config,
        configLog |-> configLog,
        reconfigs |-> ConfigHistoryEdges
    ]

=============================================================================
