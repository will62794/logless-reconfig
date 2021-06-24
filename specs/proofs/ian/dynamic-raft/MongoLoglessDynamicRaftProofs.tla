---------------------- MODULE MongoLoglessDynamicRaftProofs ---------------------

\*
\* MongoDB replication protocol that allows for logless, dynamic reconfiguration.
\*

EXTENDS MongoLoglessDynamicRaft, Randomization

CONSTANT MaxTerm
CONSTANT MaxConfigVersion
CONSTANT NumRandSubsets

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ configVersion[s] <= MaxConfigVersion

Symmetry == Permutations(Server)

SeqOf(set, n) == 
  UNION {[1..m -> set] : m \in 0..n}

BoundedSeq(S, n) ==
  SeqOf(S, n)


NatFinite == 0..3
PositiveNat == 1..3

ConfigType == [Server -> SUBSET Server]

ElectionType == [ leader : Server, 
                  term   : Nat ]

kNumSubsets == 3
nAvgSubsetSize == 2

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])
    /\ state \in RandomSubset(NumRandSubsets, [Server -> {Secondary, Primary}])
    /\ config \in RandomSubset(NumRandSubsets, [Server -> SUBSET Server])
    /\ configVersion \in RandomSubset(NumRandSubsets, [Server -> 0..MaxConfigVersion])
    /\ configTerm \in RandomSubset(NumRandSubsets, [Server -> 0..MaxTerm])

--------------------------------------------------------------------------------

(* Graveyard *)

(*
NewerVersionImpliesNewerTerm ==
    \A s,t \in Server :
        (configVersion[s] > configVersion[t]) => (configTerm[s] >= configTerm[t])

PrimariesLeadConfigVersionOld ==
    \A s \in Server : state[s] = Primary
        => \A t \in Server : configTerm[s] = configTerm[t]
            => configVersion[s] >= configVersion[t]

PrimariesLeadConfigTermOld ==
    \A s \in Server : state[s] = Primary
        => \A t \in Server : currentTerm[s] >= currentTerm[t]
            => configTerm[s] >= configTerm[t]

PrimariesLeadConfigTerm ==
    \A s,t \in Server :
        (state[s] = Primary /\ currentTerm[s] >= currentTerm[t]) => configTerm[s] >= configTerm[t]

LargestMustHaveQuorumOld ==
    \A s \in Server :
        (\A t \in Server : currentTerm[s] >= currentTerm[t])
            => \E Q \in {conf \in SUBSET config[s] : 2*(Cardinality(conf)+1) > Cardinality(config[s])} :
                  \A t \in Q : currentTerm[t] = currentTerm[s]

BecomeLeaderImpliesSameConfig ==
    \A s,t \in Server :
        (/\ (\E Q \in QuorumsAt(s) : BecomeLeaderPrecondition(s, Q))
         /\ (\E Q \in QuorumsAt(t) : BecomeLeaderPrecondition(t, Q))) => configTerm[s] = configTerm[t]

TriangleIneqConfSize ==
    \A s \in Server :
        CanBecomeLeader(s) =>
            \A t,u \in config[s] : (s # t /\ t # u /\ s # u) =>
                Cardinality(config[s]) <= Cardinality(config[t]) + Cardinality(config[u])

SymmetricDiffOne(conf1, conf2) ==
    \E s \in Server :
        \/ conf1 \cup {s} = conf2
        \/ conf2 \cup {s} = conf1

*)
--------------------------------------------------------------------------------

AbsValue(x) == IF x > 0 THEN x ELSE -x

ExistsPrimary == \E s \in Server : state[s] = Primary

\* (configVersion, term) pair of node i.
CV(i) == <<configVersion[i], configTerm[i]>>

\* Is node i disabled due to a quorum of its config having moved to a newer config.
\* the consequence here is that i CANNOT be elected in its current form
ConfigDisabled(i) == 
    \A Q \in Quorums(config[i]) : \E n \in Q : NewerConfig(CV(n), CV(i))

\* lets us drop one req; that s is primary
ConfigIsCommittedMinReq(s) ==
    /\ configTerm[s] = currentTerm[s]
    /\ \E Q \in QuorumsAt(s) :
          \A t \in Q :
              /\ configVersion[s] = configVersion[t]
              /\ configTerm[s] = configTerm[t]
              /\ currentTerm[t] = currentTerm[s]

BecomeLeaderPrecondition(s, Q) ==
    /\ s \in config[s]
    /\ s \in Q
    /\ \A t \in Q : CanVoteForConfig(t, s, currentTerm[s]+1)

latestTerm ==
    CHOOSE s \in Server :
        \A t \in Server : currentTerm[s] >= currentTerm[t]

latestConfig ==
    CHOOSE s \in Server :
        \A t \in Server : IsNewerOrEqualConfig(s, t)

BecomeLeaderPrecondition2(s, t, Q) ==
    /\ t \in config[s]
    /\ t \in Q
    \* the following two are a tailored version of CanVoteForConfig
    /\ \A q \in Q : currentTerm[q] <= currentTerm[t]
    /\ \A q \in Q : IsNewerOrEqualConfig(s, q)

CanBecomeLeader(s) == \E Q \in QuorumsAt(s) : BecomeLeaderPrecondition(s, Q)

--------------------------------------------------------------------------------

(* Ind properties *)

\* TypeOK style reqs
\* some of these are kind of cheating, but whatever

NonzeroVarsImpliesExistsPrimary ==
    (\E s \in Server : currentTerm[s] > 0 \/ configTerm[s] > 0 \/ configVersion[s] > 1)
        => (\E s \in Server : state[s] = Primary)

ConfigVersionGreaterThanZero ==
    \A s \in Server : configVersion[s] > 0

NonemptyConfig ==
    \A s \in Server : config[s] # {}

ExistsPrimaryImpliesNonZeroTerm ==
    \A s \in Server : state[s] = Primary => currentTerm[s] > 0

\*

PrimariesMustBeInTheirConfig ==
    \A s \in Server : state[s] = Primary => s \in config[s]

PrimariesConfigTermEqualsCurrentTerm ==
    \A s \in Server : state[s] = Primary => configTerm[s] = currentTerm[s]

OnePrimaryPerTerm ==
    \A s \in Server : state[s] = Primary =>
        \A t \in Server :
            (state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t

ConfigVersionAndTermUnique ==
    \A s,t \in Server :
        (configVersion[s] = configVersion[t] /\ configTerm[s] = configTerm[t])
            => (config[s] = config[t])

\* the abs value doesnt add anything because of ConfigVersionAndTermUnique
ConfigOverlapsWithDirectAncestor ==
    \A s,t \in Server :
        (AbsValue(configVersion[s] - configVersion[t]) <= 1 /\ configTerm[s] = configTerm[t])
            => QuorumsOverlap(config[s], config[t])

ExistsLargestTerm ==
    \E s \in Server :
        \A t \in Server:
            /\ ExistsPrimary => state[s] = Primary
            /\ currentTerm[s] >= currentTerm[t]
            /\ configTerm[s] >= configTerm[t]

\* In order to initiate a reconfig, a server must have its config committed, therefore disabling
\* the previous config.  Thus a config from two versions ago must necessarily be disabled.
ConfigDisabledByVersion ==
    \A s,t \in Server :
        (configVersion[s] >= configVersion[t] + 2) => ConfigDisabled(t)

\* generalization of (configVersion[s] > configVersion[t] /\ ConfigIsCommitted(s)) => ConfigDisabled(t)
ConfigDisabledByCommit ==
    \A s,t \in Server :
        /\ (configVersion[s] > configVersion[t] /\ ConfigIsCommittedMinReq(s)) => ConfigDisabled(t)
        /\ (IsNewerConfig(s, t) /\ ConfigIsCommittedMinReq(s)) => ConfigDisabled(t)

\* this clearly holds for configTerm[s] >= configTerm[t] too
OnlyLatestPrimaryCanReconfig ==
    \A s \in Server :
        (\E conf \in SUBSET Server : ENABLED Reconfig(s, conf))
            => \A t \in Server : currentTerm[s] >= currentTerm[t]

\* might be the same as? (\E Q \in QuorumsAt(s) : ENABLED BecomeLeader(s, Q))
OnlyLatestPrimaryCanBecomeLeader ==
    \A s \in Server :
        (\E Q \in QuorumsAt(s) : BecomeLeaderPrecondition(s, Q))
            => \A t \in Server : currentTerm[s] >= currentTerm[t]

\* If two configs have the same version but different terms, one has a newer term,
\* then they either have the same member set or the older config is disabled. The 
\* latter is to address the case where these configs on divergent branches but have the
\* same version.
ConfigsWithSameVersionHaveSameMemberSet == 
    \A s,t \in Server :
        (configVersion[s] = configVersion[t] /\ configTerm[s] > configTerm[t])
            => (config[s] = config[t]) \/ ConfigDisabled(t)

PrimariesLeadConfigVersion ==
    \A s,t \in Server :
        (state[s] = Primary /\ configTerm[s] = configTerm[t]) => configVersion[s] >= configVersion[t]

LargestMustHaveQuorum ==
    \A s \in Server :
        (state[s] = Primary /\ \A t \in Server : currentTerm[s] >= currentTerm[t])
            => LET possiblePrevConfigs == {conf \in SUBSET Server : QuorumsOverlap(config[s],conf)}
               IN  \E conf \in possiblePrevConfigs :
                      \E Q \in Quorums(conf) : \A t \in Q : currentTerm[t] = currentTerm[s]

SendConfigBecomeLeaderSafety ==
    \A s \in Server :
        \A t \in config[s] :
            (state[t] = Secondary /\ IsNewerConfig(s, t))
                \* if s sends its config to t and t can become leader then it must be the case
                \* that t is in the latest term
                => \/ currentTerm[t] = currentTerm[latestTerm]
                   \/ ~(\E Q \in Quorums(config[s]) : BecomeLeaderPrecondition2(s, t, Q))

ConfigsMustHaveQuorumOverlap ==
    \A s \in Server :
        \E t \in Server : QuorumsOverlap(config[s], config[t])

\* If a config has been created in term T', then this must prevent any commits
\* in configs in terms < T. Note that only primary nodes can commit writes in a 
\* config.
CommitOfNewConfigPreventsCommitsInOldTerms == 
    \A s,t \in Server : 
        (configTerm[t] < configTerm[s] /\ state[t] = Primary)
            => \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] > configTerm[t]
               \*\A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s]

ServerQuorumsMustHaveLatestTerm ==
    \A s \in Server :
        config[s] \in Quorums(Server)
            => \/ \E t \in config[s] :
                  \A u \in Server : currentTerm[t] >= currentTerm[u]
               \/ ConfigDisabled(s)

OnlySelfInSingletonConfigCanBecomeLeader ==
    \A s \in Server :
        config[s] = {s} => (\A t \in Server : CanBecomeLeader(t) => t = s)

SingletonsRestriction2 ==
    \A s,t \in Server :
        (config[s] = {t} /\ IsNewerConfig(s,t))
            => (\A u \in Server : CanBecomeLeader(u) => u = t)

BecomeLeaderConfigsOverlap ==
    \A s,t \in Server :
        (CanBecomeLeader(s) /\ CanBecomeLeader(t))
            => QuorumsOverlap(config[s], config[t])

\* technically true but weakens the II
LatestTermImpliesLaterConfig ==
    \E r \in Server : state[r] = Primary =>
      (LET p == CHOOSE s \in Server : (state[s] = Primary /\ \A t \in Server : currentTerm[s] >= currentTerm[t])
       IN
       \A s \in Server :
           (\A u \in Server : currentTerm[s] >= currentTerm[u])
               => \A t \in Server :
                   (currentTerm[t] < currentTerm[s] /\ IsNewerConfig(t, s)) => QuorumsOverlap(config[p], config[t]))

\* for the toplogically inclined, S and T "separate" Server
DifferentConfigsAlwaysSeparateServer ==
    \A s,t \in Server : IsNewerConfig(s, t)
        => \E S,T \in SUBSET Server :
              /\ S \cup T = Server
              /\ S \cap T = {}
              /\ s \in S
              /\ t \in T
              /\ \A u \in S : IsNewerConfig(u, t)
              /\ \A u \in T : IsNewerConfig(s, u)
              \*/\ \A u \in S : IsNewerOrEqualConfig(u, s)
              \*/\ \A u \in T : IsNewerOrEqualConfig(t, u)

\* doesn't work
AdjacentConfigsOverlap ==
    \A s,t \in Server :
        (\E S,T \in SUBSET Server :
            /\ S \cup T = Server
            /\ S \cap T = {}
            /\ s \in S
            /\ t \in T
            /\ \A u \in S : IsNewerOrEqualConfig(u, s)
            /\ \A u \in T : IsNewerOrEqualConfig(t, u))
          => QuorumsOverlap(config[s], config[t])

--------------------------------------------------------------------------------

Ind ==
    /\ NonzeroVarsImpliesExistsPrimary
    /\ ConfigVersionGreaterThanZero
    /\ NonemptyConfig
    /\ ExistsPrimaryImpliesNonZeroTerm

    /\ PrimariesMustBeInTheirConfig
    /\ PrimariesConfigTermEqualsCurrentTerm
    /\ OnePrimaryPerTerm
    /\ ConfigVersionAndTermUnique
    /\ ConfigOverlapsWithDirectAncestor
    /\ ExistsLargestTerm
    /\ ConfigDisabledByVersion
    /\ ConfigDisabledByCommit
    /\ OnlyLatestPrimaryCanReconfig
    /\ OnlyLatestPrimaryCanBecomeLeader
    /\ ConfigsWithSameVersionHaveSameMemberSet
    /\ PrimariesLeadConfigVersion
    /\ LargestMustHaveQuorum
    /\ SendConfigBecomeLeaderSafety
    /\ ConfigsMustHaveQuorumOverlap
    /\ CommitOfNewConfigPreventsCommitsInOldTerms
    /\ ServerQuorumsMustHaveLatestTerm
    /\ OnlySelfInSingletonConfigCanBecomeLeader
    /\ SingletonsRestriction2
    /\ BecomeLeaderConfigsOverlap
    /\ DifferentConfigsAlwaysSeparateServer

CONSTANT n1,n2,n3
CounterExample ==
    /\ state = (n1 :> Primary @@ n2 :> Secondary @@ n3 :> Primary)
    /\ config = (n1 :> {n1, n3} @@ n2 :> {n1, n2, n3} @@ n3 :> {n1, n3})
    /\ currentTerm = (n1 :> 2 @@ n2 :> 1 @@ n3 :> 3)
    /\ configVersion = (n1 :> 2 @@ n2 :> 1 @@ n3 :> 2)
    /\ configTerm = (n1 :> 2 @@ n2 :> 3 @@ n3 :> 3)

IInit == 
    /\ TypeOKRandom
    \*/\ CounterExample
    /\ Ind
(*
IInit == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ configVersion =  [i \in Server |-> 1]
    /\ configTerm    =  [i \in Server |-> 0]
    /\ \E initConfig \in SUBSET Server :
        /\ initConfig # {}
        /\ config = [i \in Server |-> initConfig]
    /\ Ind
*)



\* Must check that the initial states satisfy the inductive invariant.
Initiation == (Init => Ind)

=============================================================================
