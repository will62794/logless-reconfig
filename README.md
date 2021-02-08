
# MongoDB's Logless Dynamic Reconfiguration Protocol: TLA+ Specifications


This repository contains TLA+ specifications for defining and verifying various aspects of the logless dynamic reconfiguration protocol used in the MongoDB replication system, which is referred to as *MongoRaftReconfig*. [*MongoRaftReconfig*](specs/MongoRaftReconfig.tla) is specified as a composition of two subprotocols, [*MongoStaticRaft*](specs/MongoStaticRaft.tla) and [*MongoLoglessDynamicRaft*](specs/MongoLoglessDynamicRaft.tla). The *MongoStaticRaft* protocol is responsible for managing the oplog, which handles user database operations, while *MongoLoglessDynamicRaft* is responsible for managing the configuration state of the replica set in a separate, logless replicated state machine.

<!-- Below is an overview of the specifications included in this directory and what they are used for.

This repository includes a TLA+ specification of the logless dynamic reconfiguration protocol for Raft based replication systems, along with models for checking various correctness properties of the protocol with TLC. -->

<!-- # Overview

- [MongoRaftReconfig.tla](MongoRaftReconfig.tla): The logless dynamic reconfiguration protocol for the MongoDB replication system. It is specified as a composition of two subprotocols, MongoStaticRaft and MongoLoglessDynamicRaft.
- [MongoStaticRaft.tla](MongoStaticRaft.tla): The static MongoDB replication protocol, without dynamic reconfiguration.
- [MongoLoglessDynamicRaft.tla](MongoLoglessDynamicRaft.tla): A logless variant of MongoDB's replication protocol that allows for dynamic reconfiguration.
- [MongoSafeWeakRaft.tla](MongoSafeWeakRaft.tla): An abstract, safe version of the MongoDB replication protocol that does not depend on strict quorum overlap.
- [MongoLoglessDynamicRaftRefinement](MongoLoglessDynamicRaftRefinement.tla): Used for defining a refinement mapping from MongoLoglessDynamicRaft to MongoSafeWeakRaft It extends MongoLoglessDynamicRaft with auxiliary variables that are necessary to define this mapping. -->

## Model Checking 

Correctness properties of the protocol can be verified with the TLC model checker. run model checking with TLC, it is assumed that the `tla2tools.jar` is installed and accessible on your `CLASSPATH`. You can download the latest version of the TLA+ tools [here](https://github.com/tlaplus/tlaplus/releases).

To check the `ElectionSafety` property:
```
$ java tlc2.TLC -workers auto -config models/ElectionSafety.cfg MCLoglessReconfig.tla
```
To check the `NeverRollbackCommitted` property:
```
$ java tlc2.TLC -workers auto -config models/NeverRollbackCommitted.cfg MCLoglessReconfig.tla
```





