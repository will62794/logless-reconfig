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

\* For checking that MongoRaftReconfig => MongoLoglessDynamicRaft i.e.
\* that MongoLoglessDynamicRaft operating in composition with MongoStaticRaft
\* only restricts its behaviors, but does not augment them.
MLDR == INSTANCE MongoLoglessDynamicRaft
        WITH currentTerm <- currentTerm,
             state <- state,
             configVersion <- configVersion,
             configTerm <- configTerm,
             config <- config

RefinesMLDR == MLDR!Spec

\* If we are not checking a property that depends on the 'elections' history 
\* variable, we can project it out.
viewNoElections == <<currentTerm,state,log,configVersion,configTerm,config,committed>>

====