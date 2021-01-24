# TLC Model Checking Results Log

## January 24, 2021

**Git Revision**: [2b8d52](https://github.com/will62794/logless-reconfig/tree/2b8d52841a9035c1ed2e60d4297490fbdc6d6b6a)

**Platform**:
- MacBook (Retina, 12-inch, Early 2015)
- OSX 10.14.6
- 1.1 GHz Intel Core M
- 8 GB 1600 MHz DDR3

**Spec**: [MCMongoRaftReconfig.tla](https://github.com/will62794/logless-reconfig/blob/2b8d52841a9035c1ed2e60d4297490fbdc6d6b6a/refinement/MCMongoRaftReconfig.tla)

**Config**: [MCMongoRaftReconfig.cfg](https://github.com/will62794/logless-reconfig/blob/2b8d52841a9035c1ed2e60d4297490fbdc6d6b6a/refinement/MCMongoRaftReconfig.cfg)
```
SPECIFICATION Spec
CONSTANTS 
Nil = Nil
Server = {n1, n2, n3, n4}
Secondary = Secondary
Primary = Primary
MaxLogLen = 2
MaxTerm = 2
MaxConfigVersion = 2
CONSTRAINT StateConstraint
INVARIANT StateMachineSafety
SYMMETRY ServerSymmetry
VIEW stateView
```
**Output**:
```
$ java -cp tla2tools.jar tlc2.TLC -workers auto MCMongoRaftReconfig
TLC2 Version 2.15 of Day Month 20?? (rev: 5753be0)
Running breadth-first search Model-Checking with fp 97 and seed 5695211682645891496 with 4 workers on 4 cores with 1820MB heap and 64MB offheap memory (Mac OS X 10.14.6 x86_64, Oracle Corporation 1.8.0_45 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /Users/willyschultz/Desktop/scratch/logless-reconfig/refinement/MCMongoRaftReconfig.tla
Parsing file /private/var/folders/3r/r01znwx909gbm97mrz12n8k80000gn/T/TLC.tla
Parsing file /Users/willyschultz/Desktop/scratch/logless-reconfig/refinement/MongoRaftReconfig.tla
Parsing file /private/var/folders/3r/r01znwx909gbm97mrz12n8k80000gn/T/Naturals.tla
Parsing file /private/var/folders/3r/r01znwx909gbm97mrz12n8k80000gn/T/Integers.tla
Parsing file /private/var/folders/3r/r01znwx909gbm97mrz12n8k80000gn/T/FiniteSets.tla
Parsing file /private/var/folders/3r/r01znwx909gbm97mrz12n8k80000gn/T/Sequences.tla
Parsing file /Users/willyschultz/Desktop/scratch/logless-reconfig/refinement/MongoLoglessDynamicRaft.tla
Parsing file /Users/willyschultz/Desktop/scratch/logless-reconfig/refinement/MongoStaticRaft.tla
Parsing file /Users/willyschultz/Desktop/scratch/logless-reconfig/refinement/MongoWeakRaft.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module MongoLoglessDynamicRaft
Semantic processing of module MongoWeakRaft
Semantic processing of module MongoStaticRaft
Semantic processing of module MongoRaftReconfig
Semantic processing of module MCMongoRaftReconfig
Starting... (2021-01-23 18:36:11)
Computing initial states...
Computed 2 initial states...
Computed 4 initial states...
Computed 8 initial states...
Finished computing initial states: 15 states generated, with 4 of them distinct at 2021-01-23 18:36:11.
... 
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 7.8E-5
  based on the actual fingerprints:  val = 3.7E-6
204317671 states generated, 7279918 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 29.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 26 and the 95th percentile is 4).
Finished in 16h 56min at (2021-01-24 11:32:57)
```