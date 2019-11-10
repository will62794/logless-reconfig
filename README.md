
### Overview

Modeling reconfiguration in MongoDB replication protocol.

### Model Checking

`models/election_safety`: Contains models that check ElectionSafety invariant with varying versions of the protocol. Each model enables/disables different pre-conditions in the definition of 'ConfigIsSafe'. Tries to demonstrate the minimum necessary rules of the protocol required to satisfy election safey i.e. no two leaders elected in the same term.

`models/never_rollback_committed`: Contains models that check NeverRollbackCommitted property with varying versions of the protocol. Each model enables/disables different pre-conditions in the definition of 'ConfigIsSafe'. Tries to demonstrate the rules needed for protocol to satisfy NeverRollbackCommitted, independently of ElectionSafety.