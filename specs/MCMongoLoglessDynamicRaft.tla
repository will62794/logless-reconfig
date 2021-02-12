---- MODULE MCMongoLoglessDynamicRaft ----
EXTENDS TLC, MongoLoglessDynamicRaft

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxConfigVersion

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

ServerSymmetry == Permutations(Server)
====