# Safety of MongoDB Logless Reconfig Protocol

The standard MongoDB replication protocol without reconfiguration is referred to as the *MongoStaticRaft* protocol. This protocol is safe, which was proven in the original [Raft dissertation proof](raft-dissertation-proof.pdf). We can define a Raft like protocol as *safe* if it satisfies the 9 key safety lemmas proven in the original proof. A formal inductive invariant wasn't given in the proof, but we can consider these lemmas as sufficient for defining an abstract meaning of safety for a Raft protocol. We let *StaticRaftSafety* be a property that is the conjunction of these 9 proof lemmas, which includes the high level *StateMachineSafety* property. The safety of *MongoStaticRaft* relies on the assumption that any two quorums must overlap. We can, however, define a more general protocol that still satisfies the same definition of safety i.e. one that still satisfies *StaticRaftSafety*, without reliance on quorum overlap. We will call this protocol *MongoSafeWeakRaft*.  Before defining this protocol, we define an even weaker protocol, which we call *MongoWeakRaft*. This is protocol is built by starting with *MongoStaticRaft* and allowing configurations on nodes to change arbitrarily, so that all assumptions about quorums used by different nodes are broken. Formally, we can *MongoStaticRaft* in terms of *MongoWeakRaft*, which is how it is specified. These are the formal specifications for the protocols and properties we have defined so far:

- [MongoWeakRaft](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoWeakRaft.tla)
- [MongoStaticRaft](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoStaticRaft.tla)
- [StateMachineSafety](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoWeakRaft.tla#L261-L263) (high level safety property)

The *MongoWeakRaft* protocol is unsafe, since it gets rid of any quorum assumptions, but we can use it as a basis for defining our safe protocol *MongoSafeWeakRaft*. To develop this safe protocol, we can look at the safety properties included in *StaticRaftSafety* and try to abstract the conditions necessary for guaranteeing these properties without relying on quorum overlap. In the static protocol, quorum overlap is ultimately required to satisfy the following high level conditions:

1. If an election has occurred in term T, it prevents future elections in term T.
2. If an election has occurred in term T, it prevents entries from becoming committed in terms < T in the future.
3. If a leader is elected in term T, it must contain all entries committed in previous terms.

*MongoStaticRaft* relies on quorum overlap to enforce these conditions, but they don't inherently depend on quorums. We can refer to these conditions collectively as the *WeakQuorumCondition*. We claim that if *MongoWeakRaft* is modified to satisfy these 3 conditions, this is sufficient for it to satisfy *StaticRaftSafety*. This is how we define *MongoSafeWeakRaft* i.e. we first define *[WeakQuorumCondition](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoSafeWeakRaft.tla#L40-L56)* precisely, and then define *[MongoSafeWeakRaft](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoSafeWeakRaft.tla#L58-L67)* in terms of *MongoWeakRaft* and *WeakQuorumCondition*. Having defined *MongoSafeWeakRaft*, we can alternatively consider this protocol as an asbtract definition of "safety" for other Raft-like protocols. That is, any protocol that implements the *MongoSafeWeakRaft* specification is considered *safe*.

Finally, we want to show that *MongoDynamicRaft*, which is a log-based Raft protocol that allows for reconfiguration, is *safe*, which we can do by showing that it is a refinement of *MongoSafeWeakRaft*. We can do this by showing first that it is a refinement of *MongoWeakRaft* and then showing that it satisfies the *WeakQuorumCondition*. That is, we want to show:

```
MongoSafeWeakRaft!Spec => MongoWeakRaft!Spec    (refinement)
MongoSafeWeakRaft!Spec => []WeakQuorumCondition (invariance)
```
If we first prove the refinement statement, then we can prove the invariance property inductively, by assuming that the *WeakQuorumCondition* held in every state up to the current state. If we've proved refinement already, then we also know that the protocol operated "safely" up to this point i.e. it implemented *MongoSafeWeakRaft* up to the current state. Then, we just need to prove that *WeakQuorumCondition* holds in the next state.This allows our induction hypothesis to assume the standard safety properties about the static Raft protocol, though, which helps us to prove the invariant i.e. if our *MongoDynamicRaft* protocol has operated as a *MongoSafeWeakRaft* system up to the current state, it will continue to do so in the next state.

-----------

## Composition

The new, logless MongoDB reconfiguration protocol, which is specified in [`MongoRaftReconfig`](../MongoRaftReconfig.tla), extends `MongoStaticRaft` to allow for reconfiguration changes. Ultimately, our goal is to verify that `MongoRaftReconfig` satisfies the same safety property as the static protocol. That is, we want to verify [`MongoRaftReconfigSafety`](../MongoRaftReconfig.tla#L103). At a high level, the `MongoRaftReconfig` protocol is a composition of two conceptually distinct Raft state machines. We refer to these as the *oplog state machine (OSM)* and the *config state machine (CSM)*. The former is responsible for managing user data and the latter responsible for managing configuration state of the replica set. Both state machines run their protocols independently, but synchronize on some actions, and share some state. The CSM runs a protocol described by the specification [`MongoLoglessDynamicRaft`](../MongoLoglessDynamicRaft.tla), which is a variant of the static protocol that allows for operations of the state machine to change the definition of a quorum. The OSM runs the `MongoStaticRaft` protocol. `MongoRaftReconfig` is a composition of these two protocols, and each sub protocol (the OSM and CSM) operates over a subset of [common, global variables](../MongoRaftReconfig.tla#L16-L23). The protocols do share some state, related to terms and elections, so the composition is not fully asynchronous. They synchronize on the election action i.e. both protocol must take an election step jointly. This composition is expressed formally in the [specification](../MongoRaftReconfig.tla#L75-L94) of `MongoRaftReconfig`.

To summarize the above protocols:
- `MongoStaticRaft`: The standard, static MongoDB Raft replication protocol where configurations are fixed. Safety of this protocol has already been proven.
- `MongoLoglessDynamicRaft`: An extended form of the static  protocol where state machine operations are allowed to change the quorum definition on different nodes.
- `MongoRaftReconfig`: the complete, new MongoDB replication protocol which allows for dynamic reconfiguration. It is built as a composition of `MongoStaticRaft`, used by the OSM, and `MongoLoglessDynamicRaft`, used by the CSM. Establishing safety of this protocol is our main goal.

## Verifying *MongoLoglessDynamicRaft*

In order to verify that `MongoRaftReconfig` behaves safely , we ultimately need to ensure that the OSM, which we consider as the "externally visible" state machine, 
operates safely when composed with the CSM. In order to do this, however, we first need to ensure that the CSM behaves correctly i.e. we need to establish that `MongoLoglessDynamicRaft` is safe. `MongoLoglessDynamicRaft` is based on the `MongoStaticRaft` protocol, but it breaks some key assumptions necessary for ensuring safety of the static protocol. Thus, it is not a direct implementation of the `MongoStaticRaft` protocol, so it does not inherit its safety properties directly. Specifically, the static protocol assumes that every node starts out with a common, fixed configuration (a subset of server nodes) that never changes. The dynamic protocol, however, allows the configuration stored on different nodes to change over time. Additionally, `MongoLoglessDynamicRaft` does not store an explicit log of operations i.e. it optimizes them away. To make reasoning more straightforward, we define a version of this protocol that keeps an explicit log, which we specify as `MongoDynamicRaft`. For reasoning we consider the `MongoDynamicRaft` protocol, and eventually show that `MongoLoglessDynamicRaft` is a refinement of `MongoDynamicRaft`.

Our main goal is to show that `MongoDynamicRaft` satisfies the `StateMachineSafety` property. To do this, we start by looking at how this protocol relates to the static version of the protocol. 





## The Oplog State Machine

Once we have shown that the CSM is safe, we can then show that the OSM behaves correctly when composed with the CSM. Since elections are shared between the OSM and CSM, we already know that the election related condition of `WeakQuorumCondition` holds for the `MongoRaftReconfig` spec, but we will need to show the log related condition holds. Since we know that the CSM operates as a correct Raft state machine, and we know that a committed log entry must be committed in a current config before a reconfig is allowed, we should be able to show this fairly easily, by reasoning over the history of configs in the CSM.

### Protocols Overview and Refinements

![](refinements.png)

- `MongoWeakRaft` - A very general, weak protocol that places no restrictions on quorums used by nodes.
- `MongoStaticRaft` - The existing replication protocol used by MongoDB that is based on Raft. It does not allow for dynamic reconfiguration and it satisfies all the same safety properties as standard Raft, as described in the Raft dissertation. It implements `MongoWeakRaft` and should satisfy `StrictQuorumCondition`.
- `MongoLockstepWeakRaft` - Weak quorum protocol but requires a log entry be committed in a node's own quorum before writing a new entry.
- `MongoDynamicRaft` - A variant of `MongoStaticRaft` that allows for state machine operations to modify the configuration. This protocol keeps an explicit log and is closest to the Raft dissertation reconfig algorithm.
- `MongoLoglessDynamicRaft` - A variant of `MongoDynamicRaft` that optimizes away the log, and only stores the latest config on each node. The goal is to have this refine `MongoDynamicRaft`.
- `MongoRaftReconfig` - The new MongoDB protocol that allows for dynamic reconfiguration. Behaves as a composition of `MongoLoglessDynamicRaft` which runs the CSM and `MongoStaticRaft` which runs the OSM.