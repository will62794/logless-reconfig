---- MODULE MCLoglessDynamicRaft ----
EXTENDS TLC, MongoLoglessDynamicRaft

\* State Constraint. Used for model checking only.                                                *)
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm
====