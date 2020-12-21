---- MODULE MCMongoSafeWeakLockstepRaft ----
EXTENDS MongoSafeWeakLockstepRaft, TLC

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
BoundedSeq(S) == SeqOf(S, MaxLogLen)

\* For debugging.
Alias == 
    [
        currentTerm |-> currentTerm,
        state |-> state,
        log |-> log,
        elections |-> elections,
        committed |-> committed,
        config |-> config,
        historyEdges |-> HistoryEdges
    ]

\*
\* Theoretically, it is valid in TLA+ to write the following formula:
\*      
\*  Init /\ [][Next]_vars /\ []LockstepCondition
\* 
\* but the TLC  model checker will not interpret it correctly, so we need to use the 
\* protocol definition that inserts these conditions directly in the initial and transition 
\* predicate directly.
\*
MCSpec == Init /\ [][Next]_vars

====