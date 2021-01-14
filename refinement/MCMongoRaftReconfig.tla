---- MODULE MCMongoRaftReconfig ----
EXTENDS TLC, MongoRaftReconfig

\* For model checking.
CONSTANTS MaxTerm, MaxLogLen, MaxConfigVersion

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
                    /\ configVersion[s] <= MaxConfigVersion

ServerSymmetry == Permutations(Server)

\* If we are not checking a property that depends on the 'elections' history 
\* variable, we can project it out.
stateView == <<currentTerm,state,log,configVersion,configTerm,config,committed>>

====