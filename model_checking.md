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
