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