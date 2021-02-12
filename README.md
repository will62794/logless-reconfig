
# TLA+ Specification of Logless Dynamic Reconfiguration in MongoDB

This repository contains TLA+ specifications for the logless dynamic reconfiguration protocol used in the MongoDB replication system. The protocol, which is specified in the [`MongoRaftReconfig`](specs/MongoRaftReconfig.tla) specification, extends the static MongoDB replication protocol to allow for dynamic reconfiguration. It is formally specified as a composition of two subprotocols, [`MongoStaticRaft`](specs/MongoStaticRaft.tla) and [`MongoLoglessDynamicRaft`](specs/MongoLoglessDynamicRaft.tla). The former is responsible for managing the oplog, which handles user database operations, while the latter manages the configuration state of the replica set in a separate, logless replicated state machine.

## Checking Properties with TLC

Correctness properties of the protocol can be verified with the TLC model checker. In order to download TLC to run model checking, you can run the following:

```
cd specs
./download_tlc.sh
```
which will download a pinned version of `tla2tools.jar` to the current directory. To check a model, you can execute the following from inside the `specs` directory:
```
./checkmodel.sh <config_file> <spec_name> <worker_count>
```
This will run the specification `<spec_name>.tla` with TLC configuration file `<config_file>` and `<worker_count>` TLC worker threads. It will save the results of the execution, along with auxiliary information about the run, into a timestamped file in `specs/tlc-results`. 

For example, to verify safety properties of `MongoRaftReconfig` and `MongoLoglessDynamicRaft` using a single TLC worker, you can run the following from inside the `specs` directory:

```bash
./checkmodel.sh models/MCMongoRaftReconfig_4Servers-L2-T2-CV3.cfg MCMongoRaftReconfig 1
./checkmodel.sh models/MCMongoLoglessDynamicRaftAux-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaftAux 1
```
These models impose state constraints on both protocols to make the reachable state space finite. Complete verification time, however, will vary depending on the speed of your machine.




