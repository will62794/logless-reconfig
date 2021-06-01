## 2021-01-25

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

## 2021-01-29

### Soundness of our Specification Abstractions

In a fail-stop, asynchronous, message passing system model, nodes communicate by sending messages over the network, and nodes can fail by stopping at any time. The basic, defining characteristics of this model include the following:

- Node failure
- Message loss/duplication
- Message Delay (Asynchrony)

Let's consider how each of these aspects affect reasoning about correctness and verification of a system and how it's treated in our abstract TLA+ specs.

**Node Failure**

If a node fails and recovers at some later point, this should be equivalent to a behavior where the node simply did not send or receive any message for some period of time, which is always possible in the non-deterministic specification i.e. the model checker will always explore behaviors where a certain node is "unscheduled" (doesn't execute any actions) for an arbitrary period of time. If too many nodes stay permanently failed, this obviously presents liveness issues, but we are focused on safety verification.

**Message Loss**

If a node A sends a message to node B in an asynchronous network, this message could be lost. If the sending of a message does not modify any local state of node A, though (i.e. it only modifies the network), then this (send, drop) pair of events are effectively nilpotent i.e they have no effect on the state of nodes, which is what matters for safety. That is, it's equivalent to the node having never sent a message at all, which are scenarios that are covered by the model checker i.e. it just chooses not to schedule a certain action. Message loss is important to consider when reasoning about liveness/progress, but we are concerned with safety.

**Message Duplication**

If the network can spontaneously duplicate messages, does this present any fundamentally new considerations for modeling/verification? It seems like message duplication would about checking idempotency issues i.e. if a node processing the same message would lead to bugs. It seems like this idempotency is sort of implicitly verified in our specs simply by action preconditions i.e. if an action precondition is "not idempotent" meaning it could allow the same action A to occur twice in a row, the model checker would exercise this case, in behaviors where such actions occur repeatedly. Could think about this more but it doesn't feel too problematic.

**Message Delay (Asynchrony)**

A big difference is that our specification models message transmission synchronously i.e. there is no separation between a 'send' and 'receive' event. In the fully asynchronous model, this means that a node may be able to receive a stale message i.e. one from arbitrarily far back in the past, though our specification doesn't model this explicitly through an async network. represent this. But, our models should actually exercise cases where nodes can hear about arbitrarily stale information e.g. if there is some node that is "partitioned" (conceptually), and it's state has not been updated in many transitions. At a later time, it could then try to communicate with another node, which would seem to be nearly equivalent to the case of a stale message hanging around in the network indefinitely and being delivered at a later time.

Is this important? TODO: Something about monotonicity?????

In our spec, SendConfig/BecomeLeader are the two actions that model message send/receipt. Let's examine SendConfig. We know that for SendConfig, nodes will only accept configurations newer than their own. Messages coming from arbitrarily far back in the past could be modeled in our spec by nodes that are indefinitely stale i.e. they have become "partitioned" and haven't updated their state in arbitrarily long. I think this should be sufficient in our model to capture these "stale" messages cases. 

**Atomic Elections**

The BecomeLeader action is modeled as a single atomic action, rather than a round of separate vote requests and responses. How does this affect soundness? It does model the case of two concurrent primaries, but it doesn't model the case of two  elections happening concurrently. If two elections were happening concurrently in two non overlapping configs, this could be a problem? 

```
|------| E1
    |------| E2
```
What happens if two elections overlap?

## 2021-05-31

Stavros' summary of today's discussion and current progress:

1. we have two protocols, which i will call MongoStaticRaftWithOutLogMatching (MSR) and MongoStaticRaftWithLogMatching (MSRLM)
2. we have a property which i will call Ian's Inductive Invariant (I3)
3. Ian has proven that I3 is indeed an inductive invariant for MSR
4. Ian will also prove that I3 is an inductive invariant for MSRLM
5. we have two safety properties, which I will call StateMachineSafety (SMS), and LogMatchingSafety (LMS)
6. Ian believes that I3 implies SMS and is in the process of proving that
7. Ian believes that I3 does not imply LMS
8. we have another protocol called MongoRaftReconfig (MRR) 
9. we have another property, which i will call Will's Inductive Invariant (W2)
10. we believe that W2 is an inductive invariant for MRR but this remains to be shown
11. we also believe that W2 implies SMS but this also remains to be seen
12. it seems that W2 implies LMS because LMS is one of the conjuncts of W2 

Ian will now prioritize 4 and 6, and then start with 10, 11, 12.



