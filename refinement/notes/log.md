# December 8, 2020

If a node was elected in term T in the past, what durable evidence is there of such an election? If there are a quorum of nodes in term≥ T, this doesn't guarantee that an election actually succeeded in term T. If there exists a log entry in term T, however, this does guarantee that some leader was elected in T since they must have written down that log entry. So, if a log entry exists in term T, then the protocol must be safe against future leaders getting elected in term T again.

Does satisfaction of the WeakQuorumCondition by MongoDynamicRaft rely on many other invariants of the protocol? Is the inductive invariant as complex as the one needed to show StateMachineSafety? The WeakQuorumCondition for elections alone also rely on correctness of the state machine? So it relies on the WeakQuorumCondition for commitment too?

What aspects of the inductive invariant for the static protocol don't depend on strict quorum overlap condition?

# December 9, 2020

How hard is it to prove that MongoDynamicRaft upholds the WeakQuorumCondition?

*WeakElectionQuorumCondition*: Current electable nodes must overlap with past election quorums.
*WeakCommitQuorumCondition*: Current electable nodes must overlap with previously committed entries.

To show WeakElectionQuorumCondition we must have to show that whenever quorums (i.e. configs) change, the property is still satisfied. Does showing this depend on the state machine operating correctly, though?

Inductive step:

```tla
(WeakElectionQuorumCondition /\ WeakCommitQuorumCondition /\ Next) =>
(WeakElectionQuorumCondition' /\ WeakCommitQuorumCondition')
```

If both conditions hold currently, then we know the system operated as a safe MongoWeakRaft machine? It must have satisfied:

- LogMatching
- ElectionSafety
- LeaderCompleteness
- StateMachineSafety

among other properties and invariants about logs/states that are not directly dependent on strict quorum overlap.


# December 14, 2020

The *MongoStaticRaft* protocol behaves "safely". That is, it satisfies the 9 key safety lemmas provided in the original Raft proof, which includes the high level *StateMachineSafety* property. We let *StaticRaftSafety* be the property that represents the conjunction of these 9 abstract safety properties. We can, however, define a more general protocol than MongoStaticRaft that satisfies this same definition of safety but doesn't rely on the strict assumption that any two quorums overlap. We will call this protocol *MongoSafeWeakRaft*. Before defining it, though, we first define an even weaker protocol called *MongoWeakRaft*. This is a variant of *MongoStaticRaft* that allows configurations on nodes to change arbitrarily. That is, no restrictions are placed on when configurations can change. This protocol is unsafe, but we will use it as a starting point to define the abstract, safe protocol *MongoSafeWeakRaft*.

To develop *MongoSafeWeakRaft* we can start from the definition of *StaticRaftSafety* and try to abstract the conditions necessary for satisfying these properties, without a reliance on quorum overlap. Quorum for elections and commitment in *MongoStaticRaft* must overlap, which servers to ensure the following properties:

1. If an election has occurred in term T, this prevents future elections in term T.
2. If an election has occurred in term T, it prevents entries from becoming committed in terms < T in the future.
3. If a leader is elected in term T, it must contain all entries committed in previous terms.

*MongoStaticRaft* relies on quorum overlap to enforce these conditions and satisfiy *StaticRaftSafety*, but when viewed in the abstract, these conditions don't inherently depend on the quorums used by the protocol. We can refer to these conditions collectively as the *WeakQuorumCondition*. Then, we claim that if *MongoWeakRaft* is modified to satisfy these 3 conditions, this should be sufficient to satisfy *StaticRaftSafety*. This is how we define *MongoSafeWeakRaft* i.e. it is directly defined as 

```
MongoSafeWeakRaft == MongoWeakRaft /\ []WeakQuorumCondition
```
We can now alternatively consider the definition of a "safe" Raft protocol as one that implements/refines the *MongoSafeWeakRaft* protocol. 

Our next goal is then to show that *MongoDynamicRaft* is actually a "safe" Raft protocol i.e. it is a refinement of *MongoSafeWeakRaft*. We can do this by showing that it is a refinement of *MongoWeakRaft*, and then showing that it satisfies *[]WeakQuorumCondition*. This demonstrates that

```
(1) MongoDynamicRaft => MongoWeakRaft
(2) MongoDynamicRaft => []WeakQuorumCondition
```
which is sufficient to show that
```
(3) MongoDynamicRaft => MongoWeakRaft /\ []WeakQuorumCondition
(4) MongoDynamicRaft => MongoSafeWeakRaft
(5) MongoDynamicRaft => StaticRaftSafety
```
To prove (2) inductively, we can assume that the protocol refined *MongoWeakRaft* up the current state and that it satisfied *WeakQuorumCondition* up the current state, which means we can assume *StaticRaftSafety* as part of our inductive hypothesis. Then, we just need to prove that in the next state, *WeakQuorumCondition* is maintained by the *MongoDynamicRaft* protocol.



