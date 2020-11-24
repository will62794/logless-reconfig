----------------------------- MODULE StaticRaft -----------------------------

\* Logless, Static Raft specification, with no reconfig.

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary

(***************************************************************************)
(* Replication related variables.                                          *)
(***************************************************************************)

VARIABLE currentTerm
VARIABLE state
VARIABLE configVersion
VARIABLE configTerm

serverVars == <<currentTerm, state>>
configVars == <<configVersion, configTerm>>
vars == <<serverVars, configVersion, configTerm>>

(***************************************************************************)
(* Helper operators.                                                       *)
(***************************************************************************)

\* The set of all quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* QuorumsAt(i) == Quorums(Server)
QuorumsAt(i) == SUBSET Server

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is the config of node i considered 'newer' than the config of node j. This is the condition for
\* node j to accept the config of node i.
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] >= configVersion[j]

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerConfig(ci, cj) ==
    \* Compare configTerm first.
    \/ ci[2] > cj[2] 
    \* Compare configVersion if terms are equal.
    \/ /\ ci[2] = cj[2]
       /\ ci[1] > cj[1]  

\* Compares two configs given as <<configVersion, configTerm>> tuples.
NewerOrEqualConfig(ci, cj) == NewerConfig(ci, cj) \/ ci = cj
       
\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteFor(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerConfig(j, i)
    
\* Do all quorums of set x and set y share at least one overlapping node.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}
    
ConfigQuorumCheck(self, s) == 
    \* Equal configs.
    \/ (/\ configVersion[self] = configVersion[s]
        /\ configTerm[self] = configTerm[s])
    \/ IsNewerConfig(s, self)

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
                            /\ UNCHANGED <<configVars>>

\* Node 'i' automatically becomes a leader, if eligible.
BecomeLeader(i, voteQuorum) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteFor(v, i, newTerm)
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ configTerm' = [configTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<configVersion>>

\* Did a node talked to a quorum as primary.
TermQuorumCheck(self, s) == currentTerm[self] >= currentTerm[s]

\* A reconfig occurs on node i. The node must currently be a leader.
Reconfig(i, newConfig) ==
    (* PRE *)
    /\ state[i] = Primary
    (* POST *)
    /\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i]]
    /\ configVersion' = [configVersion EXCEPT ![i] = configVersion[i] + 1]
    /\ UNCHANGED <<serverVars>>

\* Node i sends its current config to node j.
SendConfig(i, j) ==
    (* PRE *)
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    (* POST *)
    /\ UpdateTerms(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]

(***************************************************************************)
(* Spec definition                                                         *)
(***************************************************************************)
InitConfigConstraint(c) == TRUE
InitConfigMaxSizeOnly(c) == c = Server
Init ==
    \* Server variables.
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ configVersion =  [i \in Server |-> 0]
    /\ configTerm    =  [i \in Server |-> 0]

Next ==
    \/ \E s \in Server : \E voters \in QuorumsAt(s) : BecomeLeader(s, voters)
    \/ \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
    \/ \E s,t \in Server : SendConfig(s, t)
    \/ \E s, t \in Server : UpdateTermsOnNodes(s, t)

Spec == Init /\ [][Next]_vars

ElectionSafety == \A x,y \in Server : 
    (/\ (state[x] = Primary) /\ (state[y] = Primary) 
     /\  currentTerm[x] = currentTerm[y]) => (x = y)
-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* State Constraint. Used for model checking only.                                                *)
(**************************************************************************************************)

CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

=============================================================================