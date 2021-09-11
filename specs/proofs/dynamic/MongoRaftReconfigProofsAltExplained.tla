---- MODULE MongoRaftReconfigProofsAltExplained ----
EXTENDS TLC, MongoRaftReconfigProofs

\* For checking 1-step induction counterexamples.
VARIABLE depth

PrimaryServers == {s \in Server : state[s] = Primary}
NewestTerm == Max({currentTerm[s] : s \in PrimaryServers})

OnlyPrimaryInNewestTermCanExecuteReconfig == 
    \A s \in Server : 
    \A cfg \in SUBSET Server :
        (state[s] = Primary /\ ENABLED CSM!Reconfig(s, cfg)) => (currentTerm[s] = NewestTerm)

ReconfigAllowedImpliesActiveConfigsHaveSameMemberSet == 
    \A s \in Server :
    \A cfg \in SUBSET Server :
        (state[s] = Primary /\  ENABLED CSM!Reconfig(s, cfg)) => 
        (\A ni,nj \in ActiveConfigSet : config[ni] = config[nj])

TermsOfElectableServersGreaterThanCurrentConfigTerm == 
    \A s \in Server : 
    \A Q \in Quorums(config[s]) :
    \* Electable server must get elected in a term > than its current config term.
    (ENABLED JointBecomeLeader(s, Q)) => (currentTerm[s] + 1) > configTerm[s]

ReconfigAllowedOnPrimaryImpliesAllOtherPrimariesCannotReconfig ==
    \A s \in Server : \A t \in Server \ {s} :
    \A ca, cb \in SUBSET Server :
         (ENABLED CSM!Reconfig(s, ca)) => 
        ~(ENABLED CSM!Reconfig(t, cb))

ElectableServerRequiresAllActiveConfigsHaveSameMemberSet ==
    \A s \in Server :
    \A Q \in Quorums(config[s]) : 
    (ENABLED JointBecomeLeader(s, Q)) =>
    (\A ni,nj \in ActiveConfigSet : config[ni] = config[nj])

IndAlt2 ==
    \* /\ OnePrimaryPerTerm
    \* /\ ActiveConfigsSafeAtTerms
    \* /\ PrimaryConfigTermEqualToCurrentTerm
    \* /\ OnlyPrimaryInNewestTermCanExecuteReconfig
    \* /\ ActiveConfigsOverlap
    /\ ReconfigAllowedImpliesActiveConfigsHaveSameMemberSet
    /\ ReconfigAllowedOnPrimaryImpliesAllOtherPrimariesCannotReconfig
    \* /\ ElectableServerRequiresAllActiveConfigsHaveSameMemberSet
    \* /\ TermsOfElectableServersGreaterThanCurrentConfigTerm

IInitAlt2 ==     
    /\ TypeOKRandom
    /\ depth = 1
    /\ IndAlt2

INextAlt2 ==
    /\ NextVerbose
    /\ depth = 1
    /\ depth' = depth + 1

AliasLocal == 
    [
        \* currentTerm |-> currentTerm,
        \* state |-> state,
        \* log |-> log,
        \* config |-> config,
        \* config |-> config,
        depth |-> depth,
        \* reconfigs |-> ReconfigPairsAll,
        \* electionLogIndexes |-> [s \in Server |-> ElectionLogIndex(s)]
        \* latestBeforeTerm |-> [s \in Server |-> [ i \in ((DOMAIN log[s]) \{1}) |-> LatestEntryBeforeTerm(s, log[s][i])]]
        nodes |-> [i \in Server \cup {Nil} |-> ServerStr(i)],
        committed |-> committed,
        activeConfigs |-> ActiveConfigSet,
        \* activeConfig |-> [s \in Server |-> ActiveConfig(configVersion[s], configTerm[s])],
        newestConfig |-> {<<config[s],CV(s)>> : s \in ServersInNewestConfig}
        \* configChains |-> [<<s,t>> \in ServerPair |-> ConfigChains(s,t)]
    ]

========