---- MODULE MCLoglessReconfig ----
EXTENDS LoglessReconfig, TLC

\* Optimized versions of the operators for recording history variables. These
\* allow for significant state space reduction in cases where parts of a particular
\* history variable are not needed.
RecordReconfigDisabled(rc) == reconfigs
RecordElectionCompact(e) == elections \cup {[leader |-> e.leader, term |-> e.term]}

\* For declaring the set of servers as a symmetry set.
ServerSymmetry == Permutations(Server)

====