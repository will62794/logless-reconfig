
# Formal Verification of Logless Reconfiguration in MongoDB

This repository contains a TLA+ formal specification of *MongoRaftReconfig*, a novel logless dynamic reconfiguration protocol designed for and implemented in the MongoDB distributed replication system. It also includes a formally stated inductive invariant for establishing its high level safety properties along with a machine checked TLAPS safety proof.

The overall reconfiguration protocol is defined in the [MongoRaftReconfig](specs/MongoRaftReconfig.tla) TLA+ specification. The protocol is formally described as the composition of two subprotocols: (1) [MongoStaticRaft](specs/MongoStaticRaft.tla), the static MongoDB replication protocol, and (2) [MongoLoglessDynamicRaft](specs/MongoLoglessDynamicRaft.tla), which manages the configuration state of the replica set in a separate, logless replicated state machine. Note that our specifications are written at a deliberately high level of abstraction, ignoring some lower level details of the protocol and system model. In practice,
we have found this abstraction level most useful for understanding
and communicating the essential behaviors and safety characteristics of the protocol, while
also serving to make automated verification via model checking more feasible.


## Model Checking

Safety properties of finite instances of *MongoRaftReconfig* can be verified using the TLC model checker. To check a model, you can execute the following:
```
./modelcheck.sh <config_file> <spec_name> <tlc_worker_count>
```
This will save the results of the execution, along with auxiliary information about the run, into a timestamped file in [`tlc-results`](tlc-results). For example, to verify safety properties of MongoRaftReconfig and MongoLoglessDynamicRaft with 4 TLC workers, you can run the following commands:

```bash
# Check MongoRaftReconfig.
./modelcheck.sh models/MCMongoRaftReconfig_4Servers-L2-T2-CV3.cfg MCMongoRaftReconfig 4
# Check MongoLoglessDynamicRaft.
./modelcheck.sh models/MCMongoLoglessDynamicRaft-4Servers-T4-CV4.cfg MCMongoLoglessDynamicRaft 4
```
These models impose state constraints on both protocols to make the reachable state space finite. Complete verification time, however, will vary depending on the speed of your local machine.

## Inductive Invariant and TLAPS Safety Proofs

TLAPS proofs of the safety properties of MongoRaftReconfig are provided in the [`proofs`](proofs) sub-directory. This includes a [formal inductive invariant](https://github.com/will62794/logless-reconfig/blob/3fe9ef6801c579774149b9dc8122023f738ab9b5/proofs/Defs.tla#L226-L260) for establishing safety. Information on how to inspect and check these proofs using the TLA+ proof system is provided in the README present in the [`proofs`](proofs) sub-directory.



