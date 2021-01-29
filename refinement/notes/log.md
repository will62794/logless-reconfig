# 2021-01-25

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

# 2021-01-29

### Soundness of our Specification Abstractions

In a fail-stop, asynchronous, message passing system model, nodes communicated by sending messages over the network, and nodes can fail by stopping at any time. This gives basic fundamental events of this model, where message drops and duplication are also considered. We can assume a 'network' variables that contains the set of outstanding messages that have not yet been delivered:

- SendMsg(m): place a message 'm' in 'network'
- RecvMsg(m): message 'm' is processed and removed from 'network'.
- DropMsg(m): message 'm' is removed from 'network' without being processed.
- DuplicateMsg(m): a copy of 'm' is added to 'network'.
- Fail(i): node 'i' stops sending or receiving any messages.
- Recover(i): node 'i' begins sending and receiving messages again.

**Node Failures**

If a node fails and recovers at some later point, this should be equivalent to a behavior where the node simply did not send or receive any message, which is always possible in our non-deterministic specification. If too many nodes stay permanently failed, this obviously presents liveness issues, but we are focused on safety verification. As far as 

**Message Loss**

If a node A sends a message to node B in an asynchronous network, this message could be lost. If the sending of a message does not modify any local state of node A, though (i.e. it only modifies the network), then this (Send, Drop) pair of events is as if they never occurred at all i.e. it has no effect on the local states of nodes, which is what matters for safety. That is, it's equivalent to the node having never sent its message at all, which a scenario clearly covered by our specification. Message loss is important to consider when reasoning about liveness, but we are concerned with safety.

**Stale Messages**

The other difference is that our specification models message transmission synchronously i.e. there is no separation between a 'Send' and 'Receive' event. In the fully asynchronous model, this means that a node may be able to receive a stale message i.e. one from arbitrarily far back in the past, though our specification can't represent this. Is this important? TODO: Something about monotonicity?????

In our spec, SendConfig/BecomeLeader are the two actions that model message send/receipt. Let's examine SendConfig. We know that for SendConfig, nodes will only accept configurations newer than their own. Messages coming from arbitrarily far back in the past could be modeled in our spec by nodes that are indefinitely stale i.e. they have become "partitioned" and haven't updated their state in arbitrarily long. I think this should be sufficient in our model to capture these "stale" messages cases. 

**Message Duplication**

Can be modeled as equivalent to the spec just trying to execute the same action more than once? Idempotency should be ensured by the preconditions of the actions?



**Atomic Elections**

The BecomeLeader action is modeled as a single atomic action, rather than a round of separate vote requests and responses. How does this affect soundness? It does model the case of two concurrent primaries, but it doesn't model the case of two  elections happening concurrently. If two elections were happening concurrently in two non overlapping configs, this could be a problem? 

```
|------| E1
    |------| E2
```
What happens if two elections overlap?



