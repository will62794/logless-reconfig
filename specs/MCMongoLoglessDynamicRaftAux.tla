---- MODULE MCMongoLoglessDynamicRaftAux ----
EXTENDS TLC, MongoLoglessDynamicRaftAux

CONSTANTS MaxTerm, MaxConfigVersion

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

ServerSymmetry == Permutations(Server)

ViewNoLog == <<currentTerm, state, configVersion, configTerm, config, committedConfigs>>

\*
\* For easier debugging.
\*

StateStr(st) == 
    IF st = Primary THEN "P" ELSE "S"

ServerStr(s) == 
    IF s = Nil THEN "----------------------------" ELSE
    "t" \o ToString(currentTerm[s]) \o " " \o StateStr(state[s]) \o " " \o
    ToString(config[s]) \o " (" \o ToString(configVersion[s]) \o "," \o ToString(configTerm[s]) \o ")"

Alias == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        log |-> log,
        \* config |-> config,
        committedConfigs |-> committedConfigs,
        \* config |-> config,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)]

    ]

====