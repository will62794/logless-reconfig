## TLC Model Checking Log

### Nov. 19, 2019

- Reporter: Will Schultz
- Invariants: `ActiveConfigsOverlap` and `ElectionSafety`
- Server = {n1, n2, n3, n4}
- MaxLogLen = 0
- MaxTerm = 3
- MaxConfigVersion = 3
- Symmetry: `ServerSymmetry`
- 11 TLC workers on Ubuntu 16.10 workstation.
- Error: No violation found.
- Model checking time: 07s
- Total states generated: 692,798
- Distinct states found: 31,362
- Max throughput: N/A

### Nov. 19, 2019

- Reporter: Will Schultz
- Invariants: `ActiveConfigsOverlap` and `ElectionSafety`
- Server = {n1, n2, n3, n4, n5}
- MaxLogLen = 0
- MaxTerm = 3
- MaxConfigVersion = 3
- Symmetry: `ServerSymmetry`
- 11 TLC workers on Ubuntu 16.10 workstation.
- Error: No violation found.
- Model checking time: 09min 28s
- Total states generated: 21,995,773
- Distinct states found: 647,596
- Max throughput: 2,427,575 s/min

### Nov. 20, 2019

- Reporter: Will Schultz
- Invariants: `ElectionSafety`
- Server = {n1, n2, n3, n4, n5, n6}
- MaxLogLen = 0
- MaxTerm = 3
- MaxConfigVersion = 3
- Symmetry: `ServerSymmetry`
- 11 TLC workers on Ubuntu 16.10 workstation.
- Error: No violation found.
- Model checking time: 07h 55min
- Total states generated: 483,637,661
- Distinct states found: 9,983,421
- Max throughput: 1,273,251 s/min

### Nov. 20, 2019

To do a sanity check, I checked a model on the latest [revision](https://github.com/will62794/mongo-repl-reconfig/blob/1803cce1286dc476efbfcfb97380e6d455b04a00/MongoReplReconfig.tla) with the [ConfigIsSafe](https://github.com/will62794/mongo-repl-reconfig/blob/1803cce1286dc476efbfcfb97380e6d455b04a00/MongoReplReconfig.tla#L270) precondition entirely disabled i.e. I commented it out. The model checker still passed on a 3 node model when checking ElectionSafety. I believe this is due to a bug in the [definition](https://github.com/will62794/mongo-repl-reconfig/blob/1803cce1286dc476efbfcfb97380e6d455b04a00/MongoReplReconfig.tla#L90) of `AliveNodes`, where it quantifies over the set `Server` instead of the given set. This may have caused the pre-condition for the Reconfig action to be too strong, causing the model explore a smaller state space than we expected. If I comment out the `AliveNodes` [precondition](https://github.com/will62794/mongo-repl-reconfig/blob/1803cce1286dc476efbfcfb97380e6d455b04a00/MongoReplReconfig.tla#L275) in addition to disabling `ConfigIsSafe`, the model checker immediately finds a violation.

- Reporter: Will Schultz
- Invariants: `ElectionSafety`
- Server = {n1, n2, n3}
- MaxLogLen = 2
- MaxTerm = 3
- MaxConfigVersion = 3
- Symmetry: `ServerSymmetry`
- 11 TLC workers on Ubuntu 16.10 workstation.
- Error: No violation found.
- Model checking time: 01min 56s
- Total states generated: 46,866,046
- Distinct states found: 3,547,079
- Max throughput: 24,606,593 s/min

### Nov. 20, 2019

I tried to resolve the problem mentioned above with `AliveNodes` by f[ixing its definition](https://github.com/will62794/mongo-repl-reconfig/commit/75c4407258ef63b982ac5ea45c120330b19125df). I can now confirm that with the fixed definition, removing the `ConfigIsSafe` definition entirely on a 3 node model will cause the model checker to quickly find a violation. Running the spec on this [revision](https://github.com/will62794/mongo-repl-reconfig/blob/75c4407258ef63b982ac5ea45c120330b19125df/MongoReplReconfig.tla), the model checker finds an ElectionSafety violation in under a second with a 3 node model with no logs. This seems to confirm that the definition of `AliveNodes` was causing the problem. I will run larger models with the fixed definition to make sure it wasn't masking any bugs.

### Nov. 20, 2019

Ran a 5 node model on this [revision](https://github.com/will62794/mongo-repl-reconfig/tree/c66da514c1eac158d46b6becb7d18f643ca7538f) after fixing the definition of `AliveNodes`. TLC reported no violation of ElectionSafety.

- Reporter: Will Schultz
- Invariants: `ElectionSafety`
- Server = {n1, n2, n3, n4, n5}
- MaxLogLen = 0
- MaxTerm = 3
- MaxConfigVersion = 3
- Symmetry: `ServerSymmetry`
- 11 TLC workers on Ubuntu 16.10 workstation.
- Error: No violation found.
- Model checking time: 02h 06min
- Total states generated: 520,720,228
- Distinct states found: 13,935,343
- Max throughput: 4,647,994 s/min
