# MongoDB Logless Reconfig Protocol: Safety Proof Outline

## Overview

The new, logless MongoDB reconfiguration protocol, extends the existing static Raft protocol to allow for dynamic reconfiguration. This protocol is referred to as *MongoRaftReconfig.*

 <!-- which is specified in [`MongoRaftReconfig`](../MongoRaftReconfig.tla), extends `MongoStaticRaft` to allow for reconfiguration changes.  -->

<!-- Ultimately, our goal is to verify that `MongoRaftReconfig` satisfies the same safety property as the static protocol. That is, we want to verify [`MongoRaftReconfigSafety`](../MongoRaftReconfig.tla#L103).  -->

At a high level, the *[MongoRaftReconfig](https://github.com/will62794/logless-reconfig/blob/a26545cb9d0a093ee24bd07d822f5535b865d370/refinement/MongoRaftReconfig.tla)* protocol is a composition of two conceptually distinct Raft state machines. We refer to these as the *oplog state machine (OSM)* and the *config state machine (CSM)*. The former is responsible for managing user data and the latter responsible for managing configuration state of the replica set. Both state machines run their protocols independently, but synchronize on some actions, and share some state. The CSM runs the *[MongoLoglessDynamicRaft](https://github.com/will62794/logless-reconfig/blob/a26545cb9d0a093ee24bd07d822f5535b865d370/refinement/MongoLoglessDynamicRaft.tla)* protocol, and the OSM runs the *[MongoStaticRaft](https://github.com/will62794/logless-reconfig/blob/a26545cb9d0a093ee24bd07d822f5535b865d370/refinement/MongoStaticRaft.tla)* protocol. MongoRaftReconfig is a composition of these two protocols, and each sub protocol (the OSM and CSM) operates over a subset of [common, global variables](https://github.com/will62794/logless-reconfig/blob/9c83df264e41cd6b51f1e9ed9c6d64a4deb300bd/refinement/MongoRaftReconfig.tla#L16-L23). The protocols do share some state, related to terms and elections, so the composition is not fully asynchronous. They synchronize on the election action i.e. both protocol must take an election step jointly. This composition is expressed formally in the [MongoRaftReconfig specification](https://github.com/will62794/logless-reconfig/blob/a26545cb9d0a093ee24bd07d822f5535b865d370/refinement/MongoRaftReconfig.tla#L80-L123). Ultimately, we want to verify that the *MongoRaftReconfig* satisfies the same high level safety properties as the static Raft protocol.

## The Config State Machine

In order to verify that MongoRaftReconfig behaves safely , we ultimately need to ensure that the OSM, which we consider as the "externally visible" state machine, 
operates safely when composed with the CSM. In order to do this, however, we first need to ensure that the CSM behaves correctly i.e. we need to establish that *MongoLoglessDynamicRaft* is safe. To analyze its correctness we reason about a higher level, log-based version of the protocol, which we refer to as *MongoDynamicRaft*. We first demonstrate the correctness of this higher level protocol and then show that *MongoLoglessDynamicRaft* is a refinement of it. This allows us to demonstrate safety of the logless protocol more easily, since we can reason directly about the history of log operations. We start by abstracting the safety conditions satisfied by *MongoStaticRaft* to make them applicable to *MongoDynamicRaft*.

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