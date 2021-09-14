
# Formal Verification of Logless Reconfiguration in MongoDB

This repository contains TLA+ forma specification of *MongoRaftReconfig*, the logless dynamic reconfiguration protocol used in the MongoDB replication system. 

<!-- TODO: Include these sentences once TLAPS proofs are organized. -->
<!-- It also includes a formally stated inductive invariant for establishing its high level safety properties along with a machine checked TLAPS proof of these safety proofs. -->

The overall reconfiguration protocol is defined in the [*MongoRaftReconfig*](specs/MongoRaftReconfig.tla) TLA+ specification. The protocol is formally described as the composition of two subprotocols: (1) [*MongoStaticRaft*](specs/MongoStaticRaft.tla), the static MongoDB replication protocol, and (2) [*MongoLoglessDynamicRaft*](specs/MongoLoglessDynamicRaft.tla), which manages the configuration state of the replica set in a separate, logless replicated state machine. Our specifications are written at a deliberately high level of abstraction, ignoring some lower level details of the protocol and system model. In practice,
we have found the abstraction level of our specifications most useful for understanding
and communicating the essential behaviors and safety characteristics of the protocol, while
also serving to make automated verification via model checking more feasible.


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
./checkmodel.sh models/MCMongoLoglessDynamicRaft-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaft 1
```
These models impose state constraints on both protocols to make the reachable state space finite. Complete verification time, however, will vary depending on the speed of your machine.

<!-- TODO -->
<!-- ## Inductive Invariant and TLAPS Proofs -->





