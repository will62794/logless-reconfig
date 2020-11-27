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

VARIABLE elections
VARIABLE committed

serverVars == <<currentTerm, state, log>>
vars == <<currentTerm, state, log, elections, committed, config, configLog>>

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
    \* Roll back your config state as well.
    /\ config' = [config EXCEPT ![i] = configLog[i-1]]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<elections, committed>>

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
              /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], configLog[j][newEntryIndex])]
    /\ UpdateTerms(i, j)
    \* We also propagate the config via logs. Conceptually, the current config is determined by the 
    \* last log entry, so we can just update the config on the receiving node directly to the config
    \* of the sender.
    /\ config' = [config EXCEPT ![j] = config[i]]
    /\ UNCHANGED <<elections, committed>>

\* Is the last log entry of node 'i' currently committed.
LastIsCommitted(i) == 
    \/ Len(log[i]) = 0 \* consider an empty log as being committed.
    \/ /\ Len(log[i]) > 0
       /\ \E c \in committed : 
            c.entry = <<Len(log[i]), log[i][Len(log[i])]>>

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log. It also executes a reconfig.                                                         
ClientRequest(i, newConfig) ==
    /\ state[i] = Primary
    \* Make sure the current log entry is committed before reconfiguring.
    /\ LastIsCommitted(i)
    /\ QuorumsOverlap(config[i], newConfig)
    /\ i \in newConfig \* don't remove yourself from config.
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ config' = [config EXCEPT ![i] = newConfig]
    /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], newConfig)]
    /\ UNCHANGED <<currentTerm, state, elections, committed>>

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ elections' = elections \cup 
        {[ leader  |-> i, 
            term   |-> newTerm, 
            quorum |-> voteQuorum]}
    \* Write a new no-op on step up that must be committed before a config change can occur.
    /\ log' = [log EXCEPT ![i] = Append(log[i], newTerm)]
    \* The config does not change but we write a dummy log entry.
    /\ configLog' = [configLog EXCEPT ![i] = Append(configLog[i], config[i])]
    /\ UNCHANGED <<committed, config>>   

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
    /\ UNCHANGED <<currentTerm, state, log, elections, config, configLog>>

\* Is node 'i' currently electable with quorum 'q'.
Electable(i, q) == ENABLED BecomeLeader(i, q)

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

Init ==
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    \* Let every log start with an entry representing the initial config.
    /\ log = [i \in Server |-> <<0>>]
    /\ \E initConfig \in SUBSET Server : 
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]
        /\ configLog = [i \in Server |-> <<initConfig>>]
    /\ elections = {}
    /\ committed = {}


\* Defined separately to improve error reporting when model checking.
BecomeLeaderAction == \E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
CommitEntryAction == \E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)

Next == 
    \/ \E s \in Server : \E newConfig \in SUBSET Server : ClientRequest(s, newConfig)
    \/ \E s, t \in Server : GetEntries(s, t)
    \* \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ BecomeLeaderAction
    \/ CommitEntryAction

Spec == Init /\ [][Next]_vars

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

ElectionSafety == MWR!ElectionSafety
LogMatching == MWR!LogMatching
StateMachineSafety == MWR!StateMachineSafety

-------------------------------------------------------------------------------------------

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

ServerSymmetry == Permutations(Server)

=============================================================================
