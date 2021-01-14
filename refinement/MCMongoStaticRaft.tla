---- MODULE MCMongoStaticRaft ----
EXTENDS TLC, MongoStaticRaft

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

\* State Constraint. Used for model checking only.                                                *)
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

\* For easier error diagnosis
Alias == 
    [
        currentTerm |-> currentTerm,
        state |-> state,
        log |-> log,
        config |-> config,
        elections |-> elections,
        committed |-> committed,
        futureCommitted |-> {e \in MWR!LogEntriesAll : MWR!IsFutureCommitted(e)}
    ]
====