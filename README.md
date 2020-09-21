
# Logless Dynamic Reconfiguration

Formal specification of logless dynamic reconfiguration for Raft based replication systems.

## Model Checking 

To check the `ElectionSafety` property
```
$ alias tlc="java -cp <path to tla2tools.jar> tlc2.TLC"
$ tlc -workers auto -config models/ElectionSafety.cfg MCLoglessReconfig.tla
```