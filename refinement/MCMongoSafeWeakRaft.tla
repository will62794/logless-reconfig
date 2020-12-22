---- MODULE MCMongoSafeWeakRaft ----
EXTENDS MongoSafeWeakRaft,TLC

\* Re-defined locally for convenience.
ElectionSafety == MWR!ElectionSafety
LeaderCompleteness == MWR!LeaderCompleteness
StateMachineSafety == MWR!StateMachineSafety

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
BoundedSeq(S) == SeqOf(S, MaxLogLen)

\* Invariant stating that StateMachineSafety holds in every next state.
OneStepStateMachineSafety == [][StateMachineSafety']_vars

\*
\* Theoretically, it is valid in TLA+ to write the following formula:
\*      
\*  Init /\ [][Next]_vars /\ []WeakQuorumCondition
\* 
\* but the TLC  model checker will not interpret it correctly, so we need to use the 
\* protocol definition that inserts these conditions directly in the initial and transition 
\* predicate directly.
\*
MCSpec == Init /\ [][Next]_vars


====