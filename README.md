
# Logless Dynamic Reconfiguration

This repository includes a TLA+ specification of the logless dynamic reconfiguration protocol for Raft based replication systems, along with models for checking various correctness properties of the protocol with TLC.

## Model Checking 

To run model checking with TLC, it is assumed that the `tla2tools.jar` is installed and accessible on your `CLASSPATH`. You can download the latest version of the TLA+ tools [here](https://github.com/tlaplus/tlaplus/releases).

To check the `ElectionSafety` property:
```
$ java tlc2.TLC -workers auto -config models/ElectionSafety.cfg MCLoglessReconfig.tla
```
To check the `NeverRollbackCommitted` property:
```
$ java tlc2.TLC -workers auto -config models/NeverRollbackCommitted.cfg MCLoglessReconfig.tla
```