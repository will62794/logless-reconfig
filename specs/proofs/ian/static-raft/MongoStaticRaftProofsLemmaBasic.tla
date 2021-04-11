------------------------- MODULE MongoStaticRaftProofsLemmaBasic -------------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, SequenceTheorems, FunctionTheorems, FiniteSetTheorems

CONSTANT MaxLogLen
CONSTANT MaxTerm
CONSTANT NumRandSubsets

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

TypeOK == 
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> Seq(Nat)]
    /\ config \in [Server -> SUBSET Server]
    /\ elections \in SUBSET [ leader : Server, term : Nat ]
    /\ committed \in SUBSET [ entry : Nat \times Nat, term : Nat]

-------------------------------------------------------------------------------------

\* Adding log matching is a whole different direction

LemmaBasic ==
    /\ CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    /\ TermsOfEntriesGrowMonotonically
    /\ OnePrimaryPerTerm
    /\ NonZeroLogsImplyExistsPrimary
    /\ AllSecondariesImplyInitialState 
    /\ LargestPrimaryMustHaveAQuorumInTerm
    /\ LogsMustBeSmallerThanOrEqualToLargestTerm
    /\ AllConfigsAreServer

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)

THEOREM EXCEPT_Eq ==
ASSUME NEW f,
       NEW k \in DOMAIN f, NEW u
PROVE [f EXCEPT![k] = u][k] = u
PROOF OBVIOUS

THEOREM EXCEPT_Neq ==
ASSUME NEW f, NEW k, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE \A i \in DOMAIN g : i # k => g[i] = f[i]
PROOF OBVIOUS

THEOREM EXCEPT_Domain ==
ASSUME NEW f, NEW k \in DOMAIN f, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE DOMAIN g = DOMAIN f
PROOF OBVIOUS

THEOREM FuncDomRangeForGeneral ==
ASSUME NEW Dom1, NEW Rng1,
       NEW Dom2, NEW Rng2,
       NEW f \in [Dom1 -> Rng1]
PROVE (DOMAIN f = Dom2 /\ Range(f) \in SUBSET Rng2) => f \in [Dom2 -> Rng2]
PROOF BY DEF Range

THEOREM FuncDomRangeForIndividual ==
ASSUME NEW Dom1, NEW Rng1(_),
       NEW Dom2, NEW Rng2,
       NEW f, f = [x \in Dom1 |-> Rng1(x)]
PROVE (DOMAIN f = Dom2 /\ Range(f) \in SUBSET Rng2) => f \in [Dom2 -> Rng2]
PROOF BY DEF Range

THEOREM AppendDomain ==
ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
PROVE /\ DOMAIN Append(seq, elt) = DOMAIN seq \cup {Len(Append(seq, elt))}
      /\ DOMAIN Append(seq, elt) = DOMAIN seq \cup {Len(seq)+1}
PROOF BY AppendProperties

THEOREM AppendedLogTypeOK ==
ASSUME NEW log1 \in [Server -> Seq(Nat)],
       NEW s \in Server, NEW n \in Nat,
       NEW log2, log2 = [log1 EXCEPT ![s] = Append(log1[s], n)]
PROVE log2 \in [Server -> Seq(Nat)]
PROOF
    <1>1. DOMAIN log2 = Server
        BY EXCEPT_Domain
    <1>2. Range(log2) \in SUBSET Seq(Nat)
        <2>. Append(log1[s], n) \in Seq(Nat)
            BY AppendProperties
        <2>1. \A u \in Server : u # s => log2[u] \in Seq(Nat)
            BY EXCEPT_Neq
        <2>2. \A u \in Server : u = s => log2[u] \in Seq(Nat)
            BY EXCEPT_Eq
        <2>3. QED BY <2>1, <2>2 DEF Range
    <1>3. QED BY <1>1, <1>2

THEOREM AppendedCurrentTermTypeOK ==
ASSUME TypeOK,
       NEW log1 \in [Server -> Seq(Nat)],
       NEW s \in Server,
       NEW log2, log2 = [log1 EXCEPT ![s] = Append(log1[s], currentTerm[s])]
PROVE log2 \in [Server -> Seq(Nat)]
PROOF
    <1>1. currentTerm[s] \in Nat
        BY DEF TypeOK
    <1>2. QED BY AppendedLogTypeOK, <1>1

THEOREM QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE QuorumsAt(s) \subseteq SUBSET Server
PROOF BY DEF QuorumsAt, Quorums, TypeOK

THEOREM AllQuorumsOverlap ==
ASSUME TypeOK, LemmaBasic,
       NEW s1 \in Server, NEW s2 \in Server,
       NEW Q1 \in QuorumsAt(s1),
       NEW Q2 \in QuorumsAt(s2)
PROVE Q1 \cap Q2 # {}
PROOF
    <1>. IsFiniteSet(Q1) /\ IsFiniteSet(Q2)
        BY QuorumsAreServerSubsets, ServerIsFinite, FS_Subset
    <1>. IsFiniteSet(Q1 \cap Q2) /\ IsFiniteSet(Server)
        BY FS_Intersection, ServerIsFinite
    <1>1. Q1 \in SUBSET Server /\ Q2 \in SUBSET Server
        BY QuorumsAreServerSubsets DEF LemmaBasic, AllConfigsAreServer
    <1>2. Cardinality(Q1) + Cardinality(Q2) <= Cardinality(Server) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1 \cup Q2) = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
            BY FS_Union
        <2>2. Cardinality(Q1 \cup Q2) <= Cardinality(Server)
            BY <1>1, FS_Subset, ServerIsFinite
        <2>3. QED BY <2>1, <2>2, FS_CardinalityType
    <1>3. Cardinality(Q1) + Cardinality(Q2) < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1) * 2 > Cardinality(Server) /\ Cardinality(Q2) * 2 > Cardinality(Server)
            BY <1>1 DEF LemmaBasic, AllConfigsAreServer, QuorumsAt, Quorums
        <2>2. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server)
            BY <2>1, FS_CardinalityType, ServerIsFinite
        <2>3. QED BY <2>2, <1>2, FS_CardinalityType
    <1>4. Cardinality(Q1 \cap Q2) > 0
        BY <1>3, FS_CardinalityType
    <1>5. QED BY <1>4, FS_EmptySet

THEOREM ElectedLeadersHaveLatestTerm ==
ASSUME TypeOK, LemmaBasic,
       NEW p \in Server,
       NEW Q \in QuorumsAt(p)
PROVE BecomeLeader(p, Q) => \A t \in Server : currentTerm[p] >= currentTerm[t]
PROOF
    <1>. SUFFICES ASSUME BecomeLeader(p, Q)
         PROVE \A t \in Server : currentTerm[p] >= currentTerm[t]
         OBVIOUS
    <1>. CASE \E s \in Server : state[s] = Primary
        <2>. PICK lp \in Server :
                    /\ state[lp] = Primary
                    /\ \A u \in Server : currentTerm[lp] >= currentTerm[u]
                    /\ \E lQ \in QuorumsAt(lp) :
                            \A q \in lQ : currentTerm[q] = currentTerm[lp]
            BY DEF LemmaBasic, LargestPrimaryMustHaveAQuorumInTerm
        <2>. PICK lQ \in QuorumsAt(lp) : \A q \in lQ : currentTerm[q] = currentTerm[lp]
            BY DEF LemmaBasic, LargestPrimaryMustHaveAQuorumInTerm
        <2>. SUFFICES ASSUME currentTerm[p] < currentTerm[lp]
             PROVE FALSE
             BY DEF TypeOK
        <2>1. \A q \in lQ : currentTerm[p] < currentTerm[q]
            OBVIOUS
        <2>2. \A q \in Q : currentTerm[p] >= currentTerm[q]
            <3>1. \A q \in Q : currentTerm[p]+1 > currentTerm[q]
                BY DEF BecomeLeader, CanVoteForOplog
            <3>2. QED BY <3>1, QuorumsAreServerSubsets DEF TypeOK
        <2>3. Q \cap lQ # {}
            BY AllQuorumsOverlap
        <2>4. QED BY <2>1, <2>2, <2>3, QuorumsAreServerSubsets DEF TypeOK
    <1>. CASE \A s \in Server : state[s] = Secondary
        <2>1. \A s \in Server : currentTerm[s] = 0
            BY DEF LemmaBasic, AllSecondariesImplyInitialState
        <2>2. QED BY <2>1 DEF TypeOK
    <1>1. QED BY PrimaryAndSecondaryAreDifferent DEF TypeOK




(* LemmaBasic /\ TypeOK /\ Next => LemmaBasic *)

THEOREM TypeOKAndNext ==
ASSUME TypeOK, Next
PROVE TypeOK'
PROOF
    <1>. SUFFICES ASSUME TypeOK, Next
         PROVE TypeOK'
         PROOF OBVIOUS
    <1>1. (\E s \in Server : ClientRequest(s)) => TypeOK'
        BY AppendedCurrentTermTypeOK DEF ClientRequest, TypeOK
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => TypeOK'
        BY AppendedCurrentTermTypeOK DEF GetEntries, TypeOK
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => TypeOK'
        BY AppendedCurrentTermTypeOK DEF RollbackEntries, TypeOK
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => TypeOK'
        <2>. SUFFICES ASSUME (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q))
             PROVE TypeOK'
             OBVIOUS
        <2>. PICK s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
             OBVIOUS
        <2>. PICK Q \in QuorumsAt(s) : BecomeLeader(s, Q)
             OBVIOUS
        <2>1. currentTerm' \in [Server -> Nat]
            <3>1. currentTerm' = [t \in Server |-> IF t \in Q THEN currentTerm[s]+1 ELSE currentTerm[t]]
                BY DEF BecomeLeader
            <3>2. DOMAIN currentTerm' = Server
                BY <3>1
            <3>3. Range(currentTerm') \in SUBSET Nat
                BY <3>1 DEF Range, TypeOK
            <3>4. QED BY <3>1, <3>2, <3>3 DEF Range
        <2>2. state' \in [Server -> {Secondary, Primary}]
            <3>. DEFINE P(t) == IF t = s THEN Primary ELSE IF t \in Q THEN Secondary ELSE state[t]
            <3>1. state' = [t \in Server |-> P(t)]
                BY DEF BecomeLeader
            <3>2. DOMAIN state' = Server
                BY <3>1
            <3>3. Range(state') \in SUBSET {Secondary, Primary}
                <4>1. Range(state') = { state'[t] : t \in Server }
                    BY <3>2 DEF Range
                <4>2. Range(state') = { P(t) : t \in Server }
                    BY <3>1, <4>1
                <4>3. { P(t) : t \in Server } \in SUBSET {Secondary, Primary}
                    BY DEF TypeOK
                <4>4. QED BY <4>2, <4>3
            <3>4. QED BY <3>1, <3>2, <3>3 DEF Range
        <2>3. elections' \in SUBSET [ leader : Server, term : Nat ]
            BY DEF BecomeLeader, TypeOK
        <2>4. log' \in [Server -> Seq(Nat)]
            <3>1. currentTerm[s] + 1 \in Nat
                BY DEF TypeOK
            <3>2. QED BY <3>1, AppendedLogTypeOK DEF BecomeLeader, TypeOK
        <2>5. QED BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TypeOK'
        BY DEF CommitEntry, TypeOK
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TypeOK'
        <2>. SUFFICES ASSUME (\E s,t \in Server : UpdateTerms(s, t))
             PROVE TypeOK'
             PROOF OBVIOUS
        <2>. PICK s,t \in Server : UpdateTerms(s, t)
             OBVIOUS
        <2>1. currentTerm' \in [Server -> Nat]
            <3>. currentTerm' = [currentTerm EXCEPT ![t] = currentTerm[s]]
                BY DEF UpdateTerms, UpdateTermsExpr
            <3>1. DOMAIN currentTerm' = Server
                BY EXCEPT_Domain DEF TypeOK
            <3>2. Range(currentTerm') \in SUBSET Nat
                BY DEF TypeOK, Range
            <3>3. QED BY <3>1, <3>2 DEF Range
        <2>2. state' \in [Server -> {Secondary, Primary}]
            <3>. state' = [state EXCEPT ![t] = Secondary]
                BY DEF UpdateTerms, UpdateTermsExpr
            <3>1. DOMAIN state' = Server
                BY DEF TypeOK
            <3>2. Range(state') \in SUBSET {Secondary, Primary}
                BY DEF TypeOK, Range
            <3>6. QED
                BY <3>1, <3>2 DEF Range
        <2>3. QED BY <2>1, <2>2 DEF TypeOK, UpdateTerms, UpdateTermsExpr
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM LemmaBasic /\ TypeOK /\ Next => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
PROOF
    <1>. SUFFICES ASSUME LemmaBasic, TypeOK, Next
         PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
         OBVIOUS
    <1>. TypeOK'
        BY TypeOKAndNext
    <1>1. (\E s \in Server : ClientRequest(s)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        <2>. SUFFICES ASSUME \E s \in Server : ClientRequest(s)
             PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
             OBVIOUS
        <2>. PICK s \in Server : ClientRequest(s)
             OBVIOUS
        <2>1. \A t \in Server : t = s => \A i \in DOMAIN log'[t] : currentTerm'[t] >= log'[t][i]
            <3>1. \A i \in 1..Len(log[s]) : currentTerm[s] >= log'[s][i]
                BY AppendProperties DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, ClientRequest
            <3>2. currentTerm[s] >= log'[s][Len(log[s])+1]
                BY AppendProperties, EXCEPT_Eq DEF ClientRequest, TypeOK
            <3>3. QED BY <3>1, <3>2 DEF ClientRequest
        <2>2. \A t \in Server : (state'[t] = Primary /\ t # s) => \A i \in DOMAIN log'[t] : currentTerm'[t] >= log'[t][i]
            BY EXCEPT_Neq DEF ClientRequest, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, TypeOK
        <2>3. QED BY <2>1, <2>2 DEF CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        <2>. SUFFICES ASSUME (\E s, t \in Server : GetEntries(s, t))
             PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
             OBVIOUS
        <2>. PICK s \in Server : \E t \in Server : GetEntries(s, t)
            OBVIOUS
        <2>1. state'[s] = Primary => (\A i \in DOMAIN log'[s] : currentTerm'[s] >= log'[s][i])
            <3>1. state'[s] = Secondary
                BY DEF GetEntries
            <3>2. QED BY <3>1, PrimaryAndSecondaryAreDifferent
        <2>2. \A u \in Server : (u # s /\ state'[u] = Primary) => (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
            <3>. SUFFICES ASSUME NEW u \in Server, (u # s /\ state'[u] = Primary)
                 PROVE (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
                 OBVIOUS
            <3>1. log'[u] = log[u]
                BY EXCEPT_Neq DEF GetEntries
            <3>2. UNCHANGED state /\ UNCHANGED currentTerm
                BY DEF GetEntries
            <3>3. state[u] = Primary => (\A i \in DOMAIN log[u] : currentTerm[u] >= log[u][i])
                BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
            <3>4. QED BY <3>1, <3>2, <3>3
        <2>3. QED BY <2>1, <2>2 DEF CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        <2>. SUFFICES ASSUME NEW s \in Server, \E t \in Server : RollbackEntries(s, t)
             PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
             OBVIOUS
        <2>. UNCHANGED state /\ UNCHANGED currentTerm
            BY DEF RollbackEntries
        <2>1. state'[s] = Primary => \A i \in DOMAIN log'[s] : currentTerm'[s] >= log'[s][i]
            <3>. SUFFICES ASSUME state'[s] = Primary
                 PROVE \A i \in DOMAIN log'[s] : currentTerm'[s] >= log'[s][i]
                 OBVIOUS
            <3>. state[s] = Primary
                BY DEF RollbackEntries
            <3>1. log'[s] = SubSeq(log[s], 1, Len(log[s])-1)
                BY EXCEPT_Eq DEF RollbackEntries, TypeOK
            <3>2. \A i \in 1..Len(log[s])-1 : log'[s][i] = log[s][i]
                BY <3>1, SubSeqProperties
            <3>3. DOMAIN log'[s] = 1..Len(log[s])-1
                BY <3>1, SubSeqProperties
            <3>4. \A i \in DOMAIN log'[s] : log'[s][i] = log[s][i]
                BY <3>2, <3>3
            <3>5. \A i \in DOMAIN log'[s] : currentTerm'[s] >= log[s][i]
                BY <3>1, SubSeqProperties DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
            <3>6. QED BY <3>4, <3>5 DEF TypeOK
        <2>2. \A t \in Server : (t # s /\ state'[t] = Primary) => \A i \in DOMAIN log'[t] : currentTerm'[t] >= log'[t][i]
            <3>. SUFFICES ASSUME NEW t \in Server, t # s, state'[t] = Primary
                 PROVE \A i \in DOMAIN log'[t] : currentTerm'[t] >= log'[t][i]
                 OBVIOUS
            <3>1. log'[t] = log[t]
                BY EXCEPT_Neq DEF RollbackEntries
            <3>2. QED BY <3>1 DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>3. QED BY <2>1, <2>2 DEF CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        <2>. SUFFICES ASSUME (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q))
             PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
             OBVIOUS
        <2>. PICK p \in Server : \E Q \in QuorumsAt(p) : BecomeLeader(p, Q)
            OBVIOUS
        <2>. PICK Q \in QuorumsAt(p) : BecomeLeader(p, Q)
            OBVIOUS
        <2>. \A u \in Server : u # p => log'[u] = log[u]
            BY EXCEPT_Neq DEF BecomeLeader, TypeOK
        <2>1. state'[p] = Primary => (\A i \in DOMAIN log'[p] : currentTerm'[p] >= log'[p][i])
            <3>. state'[p] = Primary
                BY DEF BecomeLeader
            <3>. DEFINE AllTerms == {currentTerm[i] : i \in Server}
            <3>. DEFINE MaxAllTerms == Max(AllTerms)
            <3>1. currentTerm'[p] = currentTerm[p]+1
                BY DEF BecomeLeader
            <3>5. currentTerm'[p] > LastTerm(log[p])
                <4>1. \A u \in Server : currentTerm[p] >= currentTerm[u]
                    BY ElectedLeadersHaveLatestTerm
                <4>2. \A t \in Server : LastTerm(log[t]) <= MaxAllTerms
                    BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                <4>3. \A t \in Server : currentTerm[p] >= LastTerm(log[t])
                    BY <4>1, <4>2 DEF Max
                <4>4. currentTerm'[p] > LastTerm(log[p])
                    BY <3>1, <4>3 DEF TypeOK, LastTerm
                <4>5. QED BY <4>4
            <3>6. \A i \in DOMAIN log[p] : currentTerm'[p] > log[p][i]
                <4>1. \A i \in DOMAIN log[p] : LastTerm(log[p]) >= log[p][i]
                    BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm
                <4>2. QED BY <3>5, <4>1 DEF LastTerm, TypeOK
            <3>. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                <4>1. log'[p] = Append(log[p], currentTerm[p]+1)
                    BY EXCEPT_Eq DEF BecomeLeader, TypeOK
                <4>2. \A i \in DOMAIN log'[p] : i = Len(log'[p]) => currentTerm'[p] >= log'[p][i]
                    BY <3>1, <4>1, AppendProperties DEF TypeOK
                <4>3. \A i \in DOMAIN log'[p] : i < Len(log'[p]) => currentTerm'[p] >= log'[p][i]
                    BY <3>6, <4>1, AppendProperties DEF TypeOK
                <4>4. QED BY <4>2, <4>3
            <3>. CASE UNCHANGED log
                <4>1. QED BY <3>6 DEF TypeOK
            <3>9. QED BY DEF BecomeLeader
        <2>2. \A u \in Q : (u # p /\ state'[u] = Primary) => (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
            <3>. SUFFICES ASSUME NEW u \in Q, (u # p /\ state'[u] = Primary)
                 PROVE FALSE
                 OBVIOUS
            <3>1. state'[u] = Secondary
                BY QuorumsAreServerSubsets DEF BecomeLeader
            <3>2. QED BY <3>1, PrimaryAndSecondaryAreDifferent
        <2>3. \A u \in Server : (u \notin Q /\ state'[u] = Primary) => (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
            <3>. SUFFICES ASSUME NEW u \in Server, (u \notin Q /\ state'[u] = Primary)
                 PROVE (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
                 OBVIOUS
            <3>1. state'[u] = state[u] /\ currentTerm'[u] = currentTerm[u]
                BY DEF BecomeLeader
            <3>2. \A i \in DOMAIN log[u] : currentTerm[u] >= log[u][i]
                <4>1. state[u] = Primary
                    BY <3>1
                <4>2. QED BY <4>1 DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
            <3>3. p \in Q
                BY DEF BecomeLeader
            <3>20 QED BY <3>1, <3>2, <3>3
        <2>4. QED BY <2>1, <2>2, <2>3 DEF CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        BY DEF LemmaBasic, CommitEntry, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
        <2>. SUFFICES ASSUME (\E s,t \in Server : UpdateTerms(s, t))
             PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
             OBVIOUS
        <2>. PICK t \in Server : \E s \in Server : UpdateTerms(s, t)
            OBVIOUS
        <2>1. state'[t] = Primary => (\A i \in DOMAIN log'[t] : currentTerm'[t] >= log'[t][i])
            BY EXCEPT_Eq, PrimaryAndSecondaryAreDifferent DEF UpdateTerms, UpdateTermsExpr, TypeOK
        <2>2. \A u \in Server : (u # t /\ state'[u] = Primary) => (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
            <3>. SUFFICES ASSUME NEW u \in Server, (u # t /\ state'[u] = Primary)
                 PROVE (\A i \in DOMAIN log'[u] : currentTerm'[u] >= log'[u][i])
                 OBVIOUS
            <3>1. state'[u] = state[u] /\ currentTerm'[u] = currentTerm[u]
                BY EXCEPT_Neq DEF UpdateTerms, UpdateTermsExpr
            <3>2. UNCHANGED log
                BY DEF UpdateTerms, UpdateTermsExpr
            <3>3. state[u] = Primary => (\A i \in DOMAIN log[u] : currentTerm[u] >= log[u][i])
                BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
            <3>4. QED BY <3>1, <3>2, <3>3
        <2>3. QED BY <2>1, <2>2 DEF CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


THEOREM AppendLogProperties ==
ASSUME TypeOK, Next, LemmaBasic,
       NEW s \in Server, NEW newEntry,
       log'[s] = Append(log[s], newEntry),
       \A i \in DOMAIN log[s] : log[s][i] <= newEntry
PROVE \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
PROOF
    <1>. DEFINE k == Len(log'[s])
    <1>1. \A i,j \in DOMAIN log[s] : (i <= j) => (log'[s][i] <= log'[s][j])
        <2>1. \A i,j \in DOMAIN log[s] : (i <= j) => (log'[s][i] = log[s][i])
            BY AppendProperties
        <2>2. QED BY <2>1 DEF LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK
    <1>2. \A i \in DOMAIN log'[s] : (i <= k) => (log'[s][i] <= log'[s][k])
        <2>1. \A i \in DOMAIN log'[s] : i = k => log'[s][i] <= newEntry
            BY TypeOKAndNext DEF TypeOK
        <2>2. log'[s][k] = newEntry
            BY AppendProperties
        <2>3. QED BY <2>1, <2>2
    <1>3. QED BY <1>1, <1>2, AppendDomain

THEOREM LemmaBasic /\ TypeOK /\ Next => TermsOfEntriesGrowMonotonically'
PROOF
    <1>. SUFFICES ASSUME LemmaBasic, TypeOK, Next
         PROVE TermsOfEntriesGrowMonotonically'
         PROOF OBVIOUS
    <1>. \A s \in Server : log'[s] = log[s] => \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
        BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically
    <1>. UNCHANGED log => TermsOfEntriesGrowMonotonically'
        BY DEF TermsOfEntriesGrowMonotonically
    <1>1. (\E s \in Server : ClientRequest(s)) => TermsOfEntriesGrowMonotonically'
        <2>. SUFFICES ASSUME NEW s \in Server, ClientRequest(s)
             PROVE TermsOfEntriesGrowMonotonically'
             OBVIOUS
        <2>. state[s] = Primary
            BY DEF ClientRequest
        <2>1. \A t \in Server : t # s => log'[t] = log[t]
            BY EXCEPT_Neq DEF ClientRequest
        <2>2. \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
            <3>1. log'[s] = Append(log[s], currentTerm[s])
                BY EXCEPT_Eq DEF ClientRequest, TypeOK
            <3>2. \A i \in DOMAIN log[s] : log[s][i] <= currentTerm[s]
                BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
            <3>3. QED BY <3>1, <3>2, AppendLogProperties
        <2>3. QED BY <2>1, <2>2 DEF TermsOfEntriesGrowMonotonically
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => TermsOfEntriesGrowMonotonically'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW p \in Server, GetEntries(s, p)
             PROVE TermsOfEntriesGrowMonotonically'
             OBVIOUS
        <2>1. \A t \in Server : t # s => log'[t] = log[t]
            BY EXCEPT_Neq DEF GetEntries
        <2>2. \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
            <3>. DEFINE newEntryIndex == IF Empty(log[s]) THEN 1 ELSE Len(log[s]) + 1
            <3>. DEFINE newEntry == log[p][newEntryIndex]
            <3>. \A i \in DOMAIN log[s] : i <= newEntryIndex
                BY LenProperties DEF Empty
            <3>. newEntryIndex \in DOMAIN log[p]
                BY DEF GetEntries
            <3>1. log'[s] = Append(log[s], newEntry)
                BY EXCEPT_Eq DEF GetEntries, TypeOK
            <3>2. \A i \in DOMAIN log[s] : log[s][i] <= newEntry
                <4>. CASE Empty(log[s])
                    <5>1. QED BY DEF Empty
                <4>. CASE ~Empty(log[s])
                    <5>. DEFINE k == Len(log[s])
                    <5>1. \A i \in DOMAIN log[p] : (i <= newEntryIndex) => (log[p][i] <= newEntry)
                        BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>2. log[s][Len(log[s])] = log[p][Len(log[s])]
                        BY DEF GetEntries
                    <5>3. \A i \in DOMAIN log[s] : (i <= k) => log[s][i] <= log[s][k]
                        BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>4. QED BY <5>1, <5>2, <5>3 DEF TypeOK
                <4>1. QED OBVIOUS
            <3>3. QED BY <3>1, <3>2, AppendLogProperties
        <2>3. QED BY <2>1, <2>2 DEF TermsOfEntriesGrowMonotonically
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => TermsOfEntriesGrowMonotonically'
        <2>. SUFFICES ASSUME NEW s \in Server, \E t \in Server : RollbackEntries(s, t)
             PROVE TermsOfEntriesGrowMonotonically'
             OBVIOUS
        <2>1. \A t \in Server : t # s => log'[t] = log[t]
            BY EXCEPT_Neq DEF RollbackEntries, TypeOK
        <2>2. \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
            <3>. \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])
                BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically
            <3>. log'[s] = SubSeq(log[s], 1, Len(log[s])-1)
                BY EXCEPT_Eq DEF RollbackEntries, TypeOK
            <3>1. QED BY SubSeqProperties
        <2>3. QED BY <2>1, <2>2 DEF TermsOfEntriesGrowMonotonically
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => TermsOfEntriesGrowMonotonically'
        <2>. SUFFICES ASSUME NEW s \in Server, \E Q \in QuorumsAt(s) : BecomeLeader(s, Q) 
             PROVE TermsOfEntriesGrowMonotonically'
             OBVIOUS
        <2>1. \A t \in Server : t # s => log'[t] = log[t]
            BY EXCEPT_Neq DEF BecomeLeader, TypeOK
        <2>2. \A i,j \in DOMAIN log'[s] : (i <= j) => (log'[s][i] <= log'[s][j])
            <3>. CASE UNCHANGED log
                <4>1. QED OBVIOUS
            <3>. CASE log' = [log EXCEPT ![s] = Append(log[s], currentTerm[s]+1)]
                <4>. log'[s] = Append(log[s], currentTerm[s]+1)
                    BY EXCEPT_Eq DEF TypeOK
                <4>. DEFINE AllTerms == {currentTerm[i] : i \in Server}
                <4>1. currentTerm[s] = Max(AllTerms)
                    BY ElectedLeadersHaveLatestTerm DEF Max
                <4>2. LastTerm(log[s]) <= currentTerm[s]
                    BY <4>1 DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                <4>3. \A i \in DOMAIN log[s] : log[s][i] <= currentTerm[s] + 1
                    <5>1. \A i \in DOMAIN log[s] : log[s][i] <= LastTerm(log[s])
                        BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm
                    <5>2. QED BY <4>2, <5>1 DEF TypeOK, LastTerm
                <4>4. QED BY <4>3, AppendLogProperties
            <3>1. QED BY DEF BecomeLeader
        <2>3 QED BY <2>1, <2>2 DEF TermsOfEntriesGrowMonotonically
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TermsOfEntriesGrowMonotonically'
        BY DEF CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TermsOfEntriesGrowMonotonically'
        BY DEF UpdateTerms
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


THEOREM LemmaBasic /\ TypeOK /\ Next => OnePrimaryPerTerm'
PROOF
    <1>. SUFFICES ASSUME LemmaBasic, TypeOK, Next
         PROVE OnePrimaryPerTerm'
         PROOF OBVIOUS
    <1>1. (\E s \in Server : ClientRequest(s)) => OnePrimaryPerTerm'
        BY DEF ClientRequest, LemmaBasic, OnePrimaryPerTerm
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => OnePrimaryPerTerm'
        BY DEF GetEntries, LemmaBasic, OnePrimaryPerTerm
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => OnePrimaryPerTerm'
        BY DEF RollbackEntries, LemmaBasic, OnePrimaryPerTerm
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => OnePrimaryPerTerm'
        <2>. SUFFICES ASSUME NEW p \in Server, NEW Q \in QuorumsAt(p), BecomeLeader(p, Q)
             PROVE OnePrimaryPerTerm'
             OBVIOUS
        <2>. \A t \in Server : currentTerm[p] >= currentTerm[t]
            BY ElectedLeadersHaveLatestTerm
        <2>. state'[p] = Primary
            BY DEF BecomeLeader
        <2>1. \A s \in Q : state'[s] = Primary =>
                \A t \in Server :
                    (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
            <3>1. \A q \in Q : q # p => state'[q] = Secondary
                BY QuorumsAreServerSubsets DEF BecomeLeader
            <3>2. \A q \in Q : state'[q] = Primary => q = p
                BY <3>1, PrimaryAndSecondaryAreDifferent
            <3>3. \A u \in Server : u \notin Q => currentTerm'[u] # currentTerm'[p]
                <4>1. currentTerm'[p] = currentTerm[p] + 1
                    BY DEF BecomeLeader
                <4>2. \A u \in Server : u \notin Q => currentTerm'[u] = currentTerm[u]
                    BY DEF BecomeLeader
                <4>3. QED BY <4>1, <4>2 DEF TypeOK
            <3>4. QED BY <3>2, <3>3
        <2>2. \A s \in Server : (state'[s] = Primary /\ s \notin Q) =>
                \A t \in Server : t \notin Q =>
                    ((state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t)
            <3>. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary, s \notin Q,
                                 NEW t \in Server, state'[t] = Primary, t \notin Q,
                                 currentTerm'[t] = currentTerm'[s]
                 PROVE s = t
                 OBVIOUS
            <3>. state'[s] = state[s] /\ currentTerm[s] = currentTerm'[s]
                BY DEF BecomeLeader
            <3>. state'[t] = state[t] /\ currentTerm[t] = currentTerm'[t]
                BY DEF BecomeLeader
            <3>1. \A u \in Server : (state[u] = Primary /\ u \notin Q) =>
                    ((state[s] = Primary /\ currentTerm[s] = currentTerm[u]) => s = u)
                BY DEF LemmaBasic, OnePrimaryPerTerm
            <3>2. QED BY <3>1
        <2>3. QED BY <2>1, <2>2, QuorumsAreServerSubsets DEF OnePrimaryPerTerm
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => OnePrimaryPerTerm'
        BY DEF CommitEntry, LemmaBasic, OnePrimaryPerTerm
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => OnePrimaryPerTerm'
        <2>. SUFFICES ASSUME NEW t \in Server, \E s \in Server : UpdateTerms(s, t)
             PROVE OnePrimaryPerTerm'
             OBVIOUS
        <2>1. \A s \in Server : s # t =>
                    (state'[s] = Primary => \A u \in Server : u # t =>
                        ((state'[u] = Primary /\ currentTerm'[s] = currentTerm'[u]) => s = u))
            <3>. \A s \in Server : s # t => (state'[s] = state[s] /\ currentTerm'[s] = currentTerm[s])
                BY EXCEPT_Neq DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>1. QED BY DEF LemmaBasic, OnePrimaryPerTerm
        <2>2. \A s \in Server : s = t =>
                    (state'[s] = Primary => \A u \in Server :
                        (state'[u] = Primary /\ currentTerm'[s] = currentTerm'[u]) => s = u)
            <3>. state'[t] = Secondary
                BY EXCEPT_Eq DEF UpdateTerms, UpdateTermsExpr,  TypeOK
            <3>1. QED BY PrimaryAndSecondaryAreDifferent
        <2>3. QED BY <2>1, <2>2 DEF OnePrimaryPerTerm
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next



THEOREM LemmaBasic /\ TypeOK /\ Next => NonZeroLogsImplyExistsPrimary'
PROOF
    <1>. SUFFICES ASSUME LemmaBasic, TypeOK, Next
         PROVE NonZeroLogsImplyExistsPrimary'
         PROOF OBVIOUS
    <1>1. (\E s \in Server : ClientRequest(s)) => NonZeroLogsImplyExistsPrimary'
        BY DEF ClientRequest, NonZeroLogsImplyExistsPrimary
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => NonZeroLogsImplyExistsPrimary'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, GetEntries(s, t)
             PROVE NonZeroLogsImplyExistsPrimary'
             OBVIOUS
        <2>. Len(log[t]) > Len(log[s])
            BY DEF GetEntries
        <2>1. Len(log[t]) > 0
            BY LenProperties
        <2>2. \E u \in Server : state[u] = Primary
            BY <2>1 DEF LemmaBasic, NonZeroLogsImplyExistsPrimary
        <2>3. QED BY <2>2 DEF GetEntries, NonZeroLogsImplyExistsPrimary
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => NonZeroLogsImplyExistsPrimary'
        <2>. SUFFICES ASSUME NEW s \in Server, \E t \in Server : RollbackEntries(s, t)
             PROVE NonZeroLogsImplyExistsPrimary'
             OBVIOUS
        <2>1. Len(log[s]) > 0
            BY DEF RollbackEntries, CanRollback
        <2>2. \E u \in Server : state[u] = Primary
            BY <2>1 DEF LemmaBasic, NonZeroLogsImplyExistsPrimary
        <2>3. QED BY <2>2 DEF RollbackEntries, NonZeroLogsImplyExistsPrimary
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => NonZeroLogsImplyExistsPrimary'
        BY DEF BecomeLeader, NonZeroLogsImplyExistsPrimary
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => NonZeroLogsImplyExistsPrimary'
        BY DEF CommitEntry, NonZeroLogsImplyExistsPrimary
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => NonZeroLogsImplyExistsPrimary'
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


(* Template

THEOREM LemmaBasic /\ TypeOK /\ Next => TypeOK'
PROOF
    <1>. SUFFICES ASSUME LemmaBasic, TypeOK, Next
         PROVE TypeOK'
         PROOF OBVIOUS
    <1>1. (\E s \in Server : ClientRequest(s)) => TypeOK'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => TypeOK'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => TypeOK'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => TypeOK'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TypeOK'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TypeOK'
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next
*)

-----------------------------------------------------------------------------------

(* Init => *)

THEOREM Init => TypeOK
PROOF BY DEF Init, TypeOK

THEOREM Init => LemmaBasic
PROOF
    <1> SUFFICES ASSUME Init
        PROVE LemmaBasic
        PROOF OBVIOUS
    <1>1. CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        BY DEF Init, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>2. TermsOfEntriesGrowMonotonically
        BY DEF Init, TermsOfEntriesGrowMonotonically
    <1>3. OnePrimaryPerTerm
        BY PrimaryAndSecondaryAreDifferent DEF Init, OnePrimaryPerTerm
    <1>4. NonZeroLogsImplyExistsPrimary
        BY DEF Init, NonZeroLogsImplyExistsPrimary
    <1>5. AllSecondariesImplyInitialState
        BY DEF Init, AllSecondariesImplyInitialState
    <1>6. LargestPrimaryMustHaveAQuorumInTerm
        BY PrimaryAndSecondaryAreDifferent DEF Init, LargestPrimaryMustHaveAQuorumInTerm
    <1>7. LogsMustBeSmallerThanOrEqualToLargestTerm
        BY DEF Init, Max, LastTerm, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>8. AllConfigsAreServer
        BY DEF Init, AllConfigsAreServer
    <1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF LemmaBasic

=============================================================================

