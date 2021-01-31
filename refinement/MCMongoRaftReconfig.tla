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

\*
\* For easier debugging.
\*

StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(log[s]) \o " " \o
    ToString(config[s]) \o " (" \o ToString(configVersion[s]) \o "," \o ToString(configTerm[s]) \o ")"

Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        \* elections |-> elections,
        committed |-> committed,
        \* config |-> config,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)]

    ]

====