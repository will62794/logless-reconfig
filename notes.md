Want counterexamples to demonstrate the role of each pre-condition for determining a config is "safe". When a config is "safe" this means a node is allowed to install a new config.

Config Safety Checks:
- Term Quorum Check
- Config Quorum Check
- Op Committed in Config


ELECTION SAFETY

The 'TermQuorumCheck' and 'ConfigQuorumCheck' are important for enforcing election safety i.e. at most one leader per term. If you only do the 'ConfigQuorumCheck', then you guarantee that at least a quorum of nodes in config Ci have received that config or a newer one. This should mean that a config prior to Ci should no longer be able to independently form a quorum in that config, because a quorum have moved to the new Ci. If you only do 'TermQuorumCheck' this is also not safe. Together they enforce election safety, though.

LEADER COMPLETENESS


### Model Checking

`models/election_safety`: Contains models that check ElectionSafety invariant with varying versions of the protocol. Each model enables/disables different pre-conditions in the definition of 'ConfigIsSafe'. Demonstrates the minimum necessary rules of the protocol required to satisfy election safey i.e. no two leaders elected in the same term.

`models/never_rollback_committed`: Contains models that check NeverRollbackCommitted property with varying versions of the protocol. Each model enables/disables different pre-conditions in the definition of 'ConfigIsSafe'. Demonstrates the rules neeeded for protocol to satisfy NeverRollbackCommitted, independently of ElectionSafety.