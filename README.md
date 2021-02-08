
# Logless Dynamic Reconfiguration in MongoDB: TLA+ Specifications


This repository contains TLA+ specifications for defining and verifying various aspects of the logless dynamic reconfiguration protocol used in the MongoDB replication system. The protocol, which is defined in the [*MongoRaftReconfig.tla*](specs/MongoRaftReconfig.tla) specification, extends the static MongoDB replication protocol to allow for dynamic membership changes. *MongoRaftReconfig* is formally specified as a composition of two subprotocols, [*MongoStaticRaft.tla*](specs/MongoStaticRaft.tla) and [*MongoLoglessDynamicRaft.tla*](specs/MongoLoglessDynamicRaft.tla). *MongoStaticRaft* protocol is responsible for managing the oplog, which handles user database operations, while *MongoLoglessDynamicRaft* is responsible for managing the configuration state of the replica set in a separate, logless replicated state machine.

## Checking Safety Properties

Safety properties of *MongoRaftReconfig* and *MongoLoglessDynamicRaft* can be verified by checking finite instances of the protocols using the TLC model checker. The key high level safety property of both protocols is the *StateMachineSafety* property.

In order to install TLC locally, you can execute the following commands:

```
cd specs
./setup_tlc.sh
```
which will download a fixed version of the `tla2tools.jar` to the current directory. To check the `StateMachineSafety` property for `MongoRaftReconfig`, execute
```
./checkmodel.sh models/MCMongoRaftReconfig_4Servers-L2-T2-CV3.cfg MCMongoRaftReconfig 1
```
and for `MongoLoglessDynamicRaft`:
```
./checkmodel.sh models/MCMongoLoglessDynamicRaftRefinement-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaftRefinement 1
```

The `./checkmodel.sh <config_file> <spec_name> <worker_count` script runs the given specification and configuration with the given TLC worker count, and save the results of the execution, along with auxiliary information about the run into a timestamped file in `specs/notes/tlc-results`. Complete verification of the above models may take several minutes or several hours depending on the speed of your machine. 

 <!-- ## Checking Refinement

 You can also verify certain refinements with TLC, to provide additional confidence in the relationships between the protocols defined in this repository. One important refinement relationship is that `MongoRaftReconfig => MongoLoglessDynamicRaft`. This can be verified by running the following model:

 ```

 ``` -->





