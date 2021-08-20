---- MODULE MCMongoLoglessDynamicRaft ----
EXTENDS TLC, MongoLoglessDynamicRaft

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxConfigVersion

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

ServerSymmetry == Permutations(Server)

OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)
====