---- MODULE MCMongoRaftReconfig ----
EXTENDS TLC, MongoRaftReconfig

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm

ServerSymmetry == Permutations(Server)
====