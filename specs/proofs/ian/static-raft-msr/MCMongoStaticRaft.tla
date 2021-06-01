---- MODULE MCMongoStaticRaft ----
EXTENDS TLC, MongoStaticRaft

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen

\* State Constraint. Used for model checking only.                                                *)
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

stateView == <<currentTerm, state, log, config, committed>>

\* For easier error diagnosis
Alias == 
    [
        currentTerm |-> currentTerm,
        state |-> state,
        log |-> log,
        config |-> config,
        elections |-> elections,
        committed |-> committed
    ]
====