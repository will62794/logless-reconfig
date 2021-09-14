
# Formal Verification of Logless Reconfiguration in MongoDB

This repository contains the TLA+ formal specification of *MongoRaftReconfig*, a novel logless dynamic reconfiguration protocol designed for and implemented in the MongoDB replication system.

<!-- TODO: Include these sentences once TLAPS proofs are organized. -->
<!-- It also includes a formally stated inductive invariant for establishing its high level safety properties along with a machine checked TLAPS proof of these safety proofs. -->

The overall reconfiguration protocol is defined in the [MongoRaftReconfig](specs/MongoRaftReconfig.tla) TLA+ specification. The protocol is formally described as the composition of two subprotocols: (1) [MongoStaticRaft](specs/MongoStaticRaft.tla), the static MongoDB replication protocol, and (2) [MongoLoglessDynamicRaft](specs/MongoLoglessDynamicRaft.tla), which manages the configuration state of the replica set in a separate, logless replicated state machine. Our specifications are written at a deliberately high level of abstraction, ignoring some lower level details of the protocol and system model. In practice,
we have found the abstraction level of our specifications most useful for understanding
and communicating the essential behaviors and safety characteristics of the protocol, while
also serving to make automated verification via model checking more feasible.


## Model Checking

Safety properties of finite instances of *MongoRaftReconfig* can be verified using the TLC model checker. To check a model, you can execute the following:
```
./modelcheck.sh <config_file> <spec_name> <tlc_worker_count>
```
This will save the results of the execution, along with auxiliary information about the run, into a timestamped file in `tlc-results`. For example, to verify safety properties of `MongoRaftReconfig` and `MongoLoglessDynamicRaft` with 4 TLC workers, you can run the following commands:

```bash
# Check MongoRaftReconfig.
./modelcheck.sh models/MCMongoRaftReconfig_4Servers-L2-T2-CV3.cfg MCMongoRaftReconfig 4
# Check MongoLoglessDynamicRaft.
./modelcheck.sh models/MCMongoLoglessDynamicRaft-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaft 4
```
These models impose state constraints on both protocols to make the reachable state space finite. Complete verification time, however, will vary depending on the speed of your machine.

<!-- TODO -->
<!-- ## Inductive Invariant and TLAPS Proofs -->





