
# TLA+ Specification of Logless Dynamic Reconfiguration in MongoDB

This repository contains TLA+ specifications for the logless dynamic reconfiguration protocol used in the MongoDB replication system. The protocol, which is specified in the [`MongoRaftReconfig`](specs/MongoRaftReconfig.tla) specification, extends the static MongoDB replication protocol to allow for dynamic membership changes. `MongoRaftReconfig` is formally specified as a composition of two subprotocols, [`MongoStaticRaft`](specs/MongoStaticRaft.tla) and [`MongoLoglessDynamicRaft`](specs/MongoLoglessDynamicRaft.tla). The former is responsible for managing the oplog, which handles user database operations, while the latter manages the configuration state of the replica set in a separate, logless replicated state machine.

## Checking Properties with TLC

The correctness properties of `MongoRaftReconfig` and `MongoLoglessDynamicRaft` can be verified by checking finite instances of the protocols using the TLC model checker. The key high level safety property of both protocols is the `StateMachineSafety` property.

In order to download TLC to run model checking, you can first change to the `specs` sub-directory, and then execute the following script:

```
./download_tlc.sh
```
which will download a pinned version of `tla2tools.jar` to the current directory. To check a model contained in the `specs/models` subdirectory, you can execute the following 
```
./checkmodel.sh <config_file> <spec_name> <worker_count>
```
This will run the specification `<spec_name>.tla` with TLC configuration `models/<config_file>` with `<worker_count>` TLC worker threads. It will save the results of the execution, along with auxiliary information about the run, into a timestamped file in `specs/tlc-results`. 

<!-- For example, to verify the `StateMachineSafety` property of `MongoRaftReconfig` and `MongoLoglessDynamicRaft`, respectively, you can run the following models:

```bash
./checkmodel.sh models/MCMongoRaftReconfig_4Servers-L2-T2-CV3.cfg MCMongoRaftReconfig 1
```

```bash
./checkmodel.sh models/MCMongoLoglessDynamicRaftAux-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaftAux 1
```
Complete verification for these models may take several minutes or hours depending on the speed of your machine.  -->

 <!-- ## Checking Refinement

 You can also verify certain refinements with TLC, to provide additional confidence in the relationships between the protocols defined in this repository. One important refinement relationship is that `MongoRaftReconfig => MongoLoglessDynamicRaft`. This can be verified by running the following model:

 ```

 ``` -->





