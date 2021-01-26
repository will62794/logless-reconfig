# January 25, 2021

Working on defining the refinement mapping between MongoLoglessDynamicRaft and MongoSafeWeakRaft. Noticed a quirk of how `IsNewerConfig` is defined, which allows configs to be >= i.e.
```tla
IsNewerConfig(i, j) ==
    \/ configTerm[i] > configTerm[j]
    \/ /\ configTerm[i] = configTerm[j]
       /\ configVersion[i] >= configVersion[j]
```
If we change this to be strictly greater than, it appears to create a liveness issue i.e. the protocol deadlocks in all initial states. Would like to understand why this is occurring. It seems like it may have to do with the fact that `SendConfig` implicitly allows for term updates if `IsNewerConfig` allows the action to be taken even when configs are equal:
```tla
SendConfig(i, j) ==
    (* PRE *)
    /\ state[j] = Secondary
    /\ IsNewerConfig(i, j)
    (* POST *)
    /\ UpdateTerms(i, j)
    /\ configVersion' = [configVersion EXCEPT ![j] = configVersion[i]]
    /\ configTerm' = [configTerm EXCEPT ![j] = configTerm[i]]
    /\ config' = [config EXCEPT ![j] = config[i]]
```
Turns out it was actually due to the definition of `CanVoteForConfig`, which limited candidates to only vote for those in strictly newer configs:
```tla
CanVoteForConfig(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerConfig(j, i)
```

Outstanding question: does `SendConfig` need to update terms of each nodes for safety, or is it only needed for a liveness condition?

To define the refinement mapping from *MongoLoglessDynamicRaft* to *MongoSafeWeakRaft*, I have defined *MongoLoglessDynamicRaftRefinement*, which extends *MongoLoglessDynamicRaft* to include auxiliary variables for defining this refinement mapping. We can check the refinement *MongoLoglessDynamicRaft => MongoSafeWeakRaft* using this spec, in addition to checking that the *WeakQuorumCondition* holds, which can be simply checked as an invariant.

Considering utilize the *TermSafetyCondition* directly instead of using the more concrete *WeakQuorumCondition*. I have given an initial TLA+ definition here:

```tla
\* Term Safety Condition

\* If an election has occurred in term T, no other elections can ever occur in term T.
T1 == \A e1,e2 \in elections : (e1.term = e2.term) => (e1.leader = e2.leader)

\* If an election has occurred in term T, no primary can ever commit in a term < T.
T2 == \A e \in elections : \A s \in Server : 
        (state[s] = Primary /\ currentTerm[s] < e.term) => \A Q \in MWR!QuorumsAt(s) : ~ENABLED MWR!CommitEntry(s, Q)

\* If an entry E has been committed in term T, any leader in term > T will contain the entry in its log.
T3 == \A s \in Server : \A c \in committed :
        (state[s]=Primary /\ c.term < currentTerm[s]) => MWR!InLog(c.entry, s)
```