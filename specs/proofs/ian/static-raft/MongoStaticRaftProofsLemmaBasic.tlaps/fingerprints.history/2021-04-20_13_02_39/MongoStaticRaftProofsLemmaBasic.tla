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
    /\ ExistsQuorumInLargestTerm
    /\ LogsMustBeSmallerThanOrEqualToLargestTerm
    /\ AllConfigsAreServer

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}

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

THEOREM QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorums(S) # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorums

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
    <1>. PICK lp \in Server :
                /\ \A u \in Server : currentTerm[lp] >= currentTerm[u]
                /\ \E lQ \in QuorumsAt(lp) :
                        \A q \in lQ : currentTerm[q] = currentTerm[lp]
        BY DEF LemmaBasic, ExistsQuorumInLargestTerm
    <1>. PICK lQ \in QuorumsAt(lp) : \A q \in lQ : currentTerm[q] = currentTerm[lp]
        BY DEF LemmaBasic, ExistsQuorumInLargestTerm
    <1>. SUFFICES ASSUME currentTerm[p] < currentTerm[lp]
         PROVE FALSE
         BY DEF TypeOK
    <1>1. \A q \in lQ : currentTerm[p] < currentTerm[q]
        OBVIOUS
    <1>2. \A q \in Q : currentTerm[p] >= currentTerm[q]
        <2>. \A q \in Q : currentTerm[p]+1 > currentTerm[q]
            BY DEF BecomeLeader, CanVoteForOplog
        <2>1. QED BY QuorumsAreServerSubsets DEF TypeOK
    <1>3. Q \cap lQ # {}
        BY AllQuorumsOverlap
    <1>4. QED BY <1>1, <1>2, <1>3, QuorumsAreServerSubsets DEF TypeOK

THEOREM AllLogsSmallerOrEqToElectedLeadersTerm ==
ASSUME TypeOK, LemmaBasic,
       NEW p \in Server, NEW Q \in QuorumsAt(p), BecomeLeader(p, Q)
PROVE \A s \in Server : LastTerm(log[s]) <= currentTerm[p]
PROOF
    <1>. \A s \in Server : currentTerm[p] >= currentTerm[s]
        BY ElectedLeadersHaveLatestTerm
    <1>1. QED
        BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm, LastTerm, TypeOK


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

THEOREM CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
PROOF
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
            <3>. DEFINE MaxAllTerms == currentTerm[p]
            <3>1. currentTerm'[p] = currentTerm[p]+1
                BY DEF BecomeLeader
            <3>5. currentTerm'[p] > LastTerm(log[p])
                <4>1. \A u \in Server : currentTerm[p] >= currentTerm[u]
                    BY ElectedLeadersHaveLatestTerm
                <4>2. \A t \in Server : LastTerm(log[t]) <= MaxAllTerms
                    BY AllLogsSmallerOrEqToElectedLeadersTerm
                <4>3. \A t \in Server : currentTerm[p] >= LastTerm(log[t])
                    BY <4>1, <4>2
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

THEOREM TermsOfEntriesGrowMonotonicallyAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE TermsOfEntriesGrowMonotonically'
PROOF
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
                <4>1. LastTerm(log[s]) <= currentTerm[s]
                    BY AllLogsSmallerOrEqToElectedLeadersTerm
                <4>2. \A i \in DOMAIN log[s] : log[s][i] <= currentTerm[s] + 1
                    <5>1. \A i \in DOMAIN log[s] : log[s][i] <= LastTerm(log[s])
                        BY DEF LemmaBasic, TermsOfEntriesGrowMonotonically, LastTerm
                    <5>2. QED BY <4>1, <5>1 DEF TypeOK, LastTerm
                <4>3. QED BY <4>2, AppendLogProperties
            <3>1. QED BY DEF BecomeLeader
        <2>3 QED BY <2>1, <2>2 DEF TermsOfEntriesGrowMonotonically
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TermsOfEntriesGrowMonotonically'
        BY DEF CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TermsOfEntriesGrowMonotonically'
        BY DEF UpdateTerms
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


THEOREM OnePrimaryPerTermAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE OnePrimaryPerTerm'
PROOF
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



THEOREM RollbackImpliesDifferentServers ==
ASSUME TypeOK,
       NEW s \in Server, NEW t \in Server,
       RollbackEntries(s, t)
PROVE s # t
PROOF
    <1>1. LastTerm(log[s]) < LastTerm(log[t])
        BY DEF RollbackEntries, CanRollback
    <1>2. log[s] # log[t]
        <2>. Len(log[t]) > 0
            BY DEF RollbackEntries, CanRollback, LastTerm, TypeOK
        <2>. CASE Len(log[s]) = 0
            <3>1. QED OBVIOUS
        <2>. CASE Len(log[s]) > 0
            <3>1. LastTerm(log[s]) = log[s][Len(log[s])]
                BY DEF RollbackEntries, CanRollback, LastTerm
            <3>2. LastTerm(log[t]) = log[t][Len(log[t])]
                BY DEF RollbackEntries, CanRollback, LastTerm
            <3>. DEFINE i == Len(log[s])
            <3>3. \/ Len(log[t]) # Len(log[s])
                  \/ /\ i = Len(log[t])
                     /\ log[s][i] # log[t][i]
                BY <1>1, <3>1, <3>2 DEF LastTerm, TypeOK
            <3>4. QED BY <3>3
        <2>1. QED OBVIOUS
    <1>3. QED BY <1>2



THEOREM ExistsQuorumInLargestTermAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE ExistsQuorumInLargestTerm'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => ExistsQuorumInLargestTerm'
        BY DEF ClientRequest, LemmaBasic, QuorumsAt, Quorums, ExistsQuorumInLargestTerm, ExistsPrimary
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => ExistsQuorumInLargestTerm'
        BY DEF GetEntries, LemmaBasic, QuorumsAt, Quorums, ExistsQuorumInLargestTerm, ExistsPrimary
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => ExistsQuorumInLargestTerm'
        BY DEF RollbackEntries, LemmaBasic, QuorumsAt, Quorums, ExistsQuorumInLargestTerm, ExistsPrimary
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => ExistsQuorumInLargestTerm'
        <2>. SUFFICES ASSUME NEW p \in Server, NEW Q \in QuorumsAt(p), BecomeLeader(p, Q)
             PROVE ExistsQuorumInLargestTerm'
             OBVIOUS
        <2>1. state'[p] = Primary
            BY DEF BecomeLeader
        <2>2. \A u \in Server : currentTerm'[p] >= currentTerm'[u]
            BY ElectedLeadersHaveLatestTerm DEF BecomeLeader, TypeOK
        <2>3. \A q \in Q : currentTerm'[q] = currentTerm'[p]
            BY QuorumsAreServerSubsets DEF BecomeLeader, TypeOK
        <2>4. QED
            BY <2>1, <2>2, <2>3 DEF ExistsQuorumInLargestTerm, BecomeLeader, QuorumsAt, Quorums
    <1>5. (\E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => ExistsQuorumInLargestTerm'
        BY DEF CommitEntry, LemmaBasic, QuorumsAt, Quorums, ExistsQuorumInLargestTerm, ExistsPrimary
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => ExistsQuorumInLargestTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, UpdateTerms(s, t)
             PROVE ExistsQuorumInLargestTerm'
             OBVIOUS
        <2>. CASE ExistsPrimary
            <3>. PICK p \in Server :
                         /\ state[p] = Primary
                         /\ \A u \in Server : currentTerm[p] >= currentTerm[u]
                         /\ \E Q \in QuorumsAt(p) :
                               \A q \in Q : currentTerm[q] = currentTerm[p]
                BY DEF LemmaBasic, ExistsQuorumInLargestTerm
            <3>. PICK Q \in QuorumsAt(p) : \A q \in Q : currentTerm[q] = currentTerm[p]
                OBVIOUS
            \* Believe me, it's all necessary.  and ridiculous...
            <3>1. /\ p \in Server
                  /\ ExistsPrimary' => state'[p] = Primary
                  /\ \A u \in Server : currentTerm'[p] >= currentTerm'[u]
                  /\ \E Qp \in QuorumsAt(p) :
                      \A q \in Qp : currentTerm'[q] = currentTerm'[p]
                <4>. state'[p] = Primary
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>. \A u \in Server : currentTerm'[p] >= currentTerm'[u]
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>. \A q \in Q : currentTerm'[q] = currentTerm'[p]
                    <5>. currentTerm'[p] = currentTerm[p]
                        BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                    <5>1. QED BY QuorumsAreServerSubsets DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>1. QED OBVIOUS
            <3>2. \E a \in Server :
                    /\ ExistsPrimary' => state'[a] = Primary
                    /\ \A u \in Server : currentTerm'[a] >= currentTerm'[u]
                    /\ \E Qp \in (QuorumsAt(a))' :
                        \A q \in Qp : currentTerm'[q] = currentTerm'[a]
                <4>. \E Qp \in (QuorumsAt(p))' : TRUE
                    BY QuorumsAreServerSubsets DEF QuorumsAt, Quorums, UpdateTerms, UpdateTermsExpr, TypeOK
                <4>1. QED BY <3>1, QuorumsAreServerSubsets DEF QuorumsAt, Quorums, UpdateTerms, UpdateTermsExpr
            <3>3. QED BY <3>2 DEF ExistsQuorumInLargestTerm
        <2>. CASE ~ExistsPrimary
            <3>. ~(ExistsPrimary')
                <4>. \A u \in Server : state[u] = Secondary
                    BY PrimaryAndSecondaryAreDifferent DEF TypeOK, ExistsPrimary
                <4>. \A u \in Server : state'[u] = Secondary
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>1. QED BY DEF ExistsPrimary
            <3>. PICK p \in Server :
                         /\ \A u \in Server : currentTerm[p] >= currentTerm[u]
                         /\ \E Q \in QuorumsAt(p) :
                               \A q \in Q : currentTerm[q] = currentTerm[p]
                BY DEF LemmaBasic, ExistsQuorumInLargestTerm
            <3>. PICK Q \in QuorumsAt(p) : \A q \in Q : currentTerm[q] = currentTerm[p]
                OBVIOUS
            <3>1. /\ p \in Server
                  /\ ExistsPrimary' => state'[p] = Primary
                  /\ \A u \in Server : currentTerm'[p] >= currentTerm'[u]
                  /\ \E Qp \in QuorumsAt(p) :
                      \A q \in Qp : currentTerm'[q] = currentTerm'[p]
                <4>. \A u \in Server : currentTerm'[p] >= currentTerm'[u]
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>. \A q \in Q : currentTerm'[q] = currentTerm'[p]
                    <5>. currentTerm'[p] = currentTerm[p]
                        BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                    <5>1. QED BY QuorumsAreServerSubsets DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>1. QED OBVIOUS
            <3>2. \E a \in Server :
                    /\ ExistsPrimary' => state'[a] = Primary
                    /\ \A u \in Server : currentTerm'[a] >= currentTerm'[u]
                    /\ \E Qp \in (QuorumsAt(a))' :
                        \A q \in Qp : currentTerm'[q] = currentTerm'[a]
                <4>. \E Qp \in (QuorumsAt(p))' : TRUE
                    BY QuorumsAreServerSubsets DEF QuorumsAt, Quorums, UpdateTerms, UpdateTermsExpr, TypeOK
                <4>1. QED BY <3>1, QuorumsAreServerSubsets DEF QuorumsAt, Quorums, UpdateTerms, UpdateTermsExpr
            <3>3. QED BY <3>2 DEF ExistsQuorumInLargestTerm
        <2>1. QED BY DEF ExistsQuorumInLargestTerm \*PrimaryAndSecondaryAreDifferent DEF ExistsPrimary, ExistsQuorumInLargestTerm
            \*BY QuorumsExistForNonEmptySets DEF UpdateTerms, UpdateTermsExpr, QuorumsAt, Quorums, TypeOK, ExistsQuorumInLargestTerm, ExistsPrimary
            
            
        (* 
        
            <3>. p # t
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
        <2>. CASE \E u \in Server : state[u] = Server
            <3>. state[p] = Primary
                BY DEF LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary
            <3>. state'[p] = Primary /\ currentTerm'[p] = currentTerm[p]
                BY DEF UpdateTerms, UpdateTermsExpr
            <3>. \A u \in Server : currentTerm'[p] >= currentTerm'[u]
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>. \A q \in Q : currentTerm'[q] = currentTerm'[p]
                <4>. t \notin Q
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK, ExistsQuorumInLargestTerm
                <4>1. QED BY DEF UpdateTerms, UpdateTermsExpr
            <3>1. QED BY DEF UpdateTerms, QuorumsAt, Quorums, ExistsQuorumInLargestTerm
        <2>. CASE \A u \in Server : state[u] = Secondary
        <2>1. QED BY PrimaryAndSecondaryAreDifferent DEF TypeOK*)
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next



THEOREM AppendLogIsSafe ==
ASSUME TypeOK, Next, LemmaBasic,
       NEW s \in Server, NEW newEntry,
       log' = [log EXCEPT ![s] = Append(log[s], newEntry)],
       currentTerm' = currentTerm
PROVE (\E t \in Server : currentTerm[t] >= newEntry) => LogsMustBeSmallerThanOrEqualToLargestTerm'
PROOF
    <1>. SUFFICES ASSUME NEW t \in Server, currentTerm[t] >= newEntry
         PROVE \A u \in Server : \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
         BY DEF LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>. TAKE u \in Server
    <1>. PICK v \in Server : LastTerm(log[u]) <= currentTerm[v]
        BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>. CASE u = s
        <2>. LastTerm(log'[u]) <= currentTerm[t]
            BY DEF LastTerm, TypeOK
        <2>1. QED OBVIOUS
    <1>. CASE u # s
        <2>. LastTerm(log'[u]) = LastTerm(log[u])
            BY DEF LastTerm, TypeOK
        <2>1. QED OBVIOUS
    <1>1. QED OBVIOUS

THEOREM LogsMustBeSmallerThanOrEqualToLargestTermAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE LogsMustBeSmallerThanOrEqualToLargestTerm'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, ClientRequest(s)
             PROVE LogsMustBeSmallerThanOrEqualToLargestTerm'
             OBVIOUS
        <2>. DEFINE newEntry == currentTerm[s]
        <2>1. log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
            BY DEF ClientRequest
        <2>2. currentTerm[s] >= newEntry
            BY DEF TypeOK
        <2>3. currentTerm' = currentTerm
            BY DEF ClientRequest
        <2>4. QED BY <2>1, <2>2, <2>3, AppendLogIsSafe DEF TypeOK
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        \* very messy, could use some clean up
        <2>. SUFFICES ASSUME NEW s \in Server, NEW p \in Server, GetEntries(s, p)
             PROVE \A u \in Server : \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
             BY DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>1. LastTerm(log'[s]) <= LastTerm(log[p])
            <3>. DEFINE idx == IF Empty(log[s]) THEN 1 ELSE Len(log[s]) + 1
            <3>. idx = Len(log[s]) + 1
                BY DEF Empty
            <3>. idx = Len(log'[s])
                BY AppendProperties DEF GetEntries, TypeOK
            <3>1. log'[s][idx] = log[p][idx]
                BY AppendProperties DEF GetEntries, TypeOK
            <3>2. LastTerm(log'[s]) = log[p][idx]
                BY <3>1 DEF LastTerm
            <3>3. log[p][idx] <= LastTerm(log[p])
                <4>. idx <= Len(log[p])
                    BY DEF GetEntries, TypeOK
                <4>1. QED BY <3>2, LenProperties DEF LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK, LastTerm
            <3>4. QED BY <3>2, <3>3 DEF TypeOK
        <2>. PICK t \in Server : LastTerm(log[p]) <= currentTerm[t]
            BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>4. LastTerm(log'[s]) <= currentTerm'[t]
            <3>1. LastTerm(log'[s]) <= LastTerm(log'[p])
                BY <2>1 DEF GetEntries, TypeOK
            <3>2. LastTerm(log'[p]) <= currentTerm'[t]
                BY DEF GetEntries, TypeOK
            <3>3. QED BY <3>1, <3>2, TypeOKAndNext DEF TypeOK, LastTerm
        <2>7. \A u \in Server : u # s => \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
            <3>. \A u \in Server : u # s => log'[u] = log[u]
                BY DEF GetEntries, TypeOK
            <3>1. \A u \in Server : currentTerm'[u] = currentTerm[u]
                BY DEF GetEntries, TypeOK
            <3>. TAKE u \in Server
            <3>2. PICK v \in Server : LastTerm(log[u]) <= currentTerm[v]
                BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
            <3>3. QED BY <3>1, <3>2 DEF TypeOK
        <2>8. QED
            BY <2>4, <2>7 DEF LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, \E t \in Server : RollbackEntries(s, t)
             PROVE \A u \in Server : \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
             BY DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. TAKE t \in Server
        <2>. PICK p \in Server : LastTerm(log[t]) <= currentTerm[p]
            BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. currentTerm'[p] = currentTerm[p]
            BY DEF RollbackEntries, TypeOK
        <2>1. t # s => LastTerm(log'[t]) <= currentTerm'[p]
            <3>. t # s => LastTerm(log'[t]) = LastTerm(log[t])
                BY DEF RollbackEntries, LastTerm
            <3>1. QED BY DEF RollbackEntries
        <2>2. t = s => LastTerm(log'[t]) <= currentTerm'[p]
            <3>. CASE log'[t] = <<>>
                <4>. LastTerm(log'[t]) = 0
                    BY DEF LastTerm
                <4>1. QED BY DEF RollbackEntries, TypeOK
            <3>. CASE log'[t] # <<>>
                <4>. \A i \in DOMAIN log'[t] : log'[t][i] = log[t][i]
                    BY DEF RollbackEntries
                <4>. \A i \in DOMAIN log'[t] : log[t][i] <= LastTerm(log[t])
                    BY DEF RollbackEntries, LastTerm, LemmaBasic, TermsOfEntriesGrowMonotonically
                <4>. LastTerm(log'[t]) <= LastTerm(log[t])
                    BY DEF LastTerm
                <4>1. QED BY TypeOKAndNext DEF LastTerm, TypeOK
            <3>1. QED OBVIOUS
        <2>3. QED BY <2>1, <2>2
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        <2>. SUFFICES ASSUME NEW p \in Server, \E Q \in QuorumsAt(p) : BecomeLeader(p, Q)
             PROVE \A u \in Server : \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
             BY DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. \A s \in Server : currentTerm[p] >= currentTerm[s]
            BY ElectedLeadersHaveLatestTerm
        <2>. currentTerm'[p] = currentTerm[p] + 1
            BY DEF BecomeLeader
        <2>. TAKE s \in Server
        <2>. PICK t \in Server : LastTerm(log[s]) <= currentTerm[t]
            BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>1. LastTerm(log[s]) <= currentTerm[p]
            BY DEF TypeOK, LastTerm
        <2>. CASE s # p \/ UNCHANGED log
            <3>. LastTerm(log'[s]) = LastTerm(log[s])
                BY DEF BecomeLeader, LastTerm, TypeOK
            <3>1. QED BY <2>1 DEF TypeOK, LastTerm
        <2>. CASE s = p /\ log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
            <3>. log'[p] = Append(log[p], currentTerm'[p])
                BY DEF TypeOK
            <3>1. LastTerm(log'[p]) <= currentTerm'[p]
                BY AppendProperties DEF LastTerm, TypeOK
            <3>2. QED BY <3>1
        <2>2. QED BY DEF BecomeLeader
    <1>5. (\E s \in Server : \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        BY DEF CommitEntry, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => LogsMustBeSmallerThanOrEqualToLargestTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, UpdateTerms(s, t)
             PROVE \A u \in Server : \E v \in Server : LastTerm(log'[u]) <= currentTerm'[v]
             BY DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. TAKE u \in Server
        <2>. LastTerm(log'[u]) = LastTerm(log[u])
            BY DEF UpdateTerms, LastTerm
        <2>. PICK p \in Server : LastTerm(log[u]) <= currentTerm[p]
            BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. CASE p = t
            <3>1. currentTerm[p] < currentTerm'[p]
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>2. LastTerm(log[u]) <= currentTerm'[p]
                BY <3>1, TypeOKAndNext DEF TypeOK, LastTerm
            <3>3. QED BY <3>2 DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>. CASE p # t
            <3>1. currentTerm'[p] = currentTerm[p]
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>2. QED BY <3>1 DEF LogsMustBeSmallerThanOrEqualToLargestTerm
        <2>1. QED OBVIOUS
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next



THEOREM AllConfigsAreServerAndNext ==
ASSUME LemmaBasic, TypeOK, Next
PROVE AllConfigsAreServer'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => AllConfigsAreServer'
        BY DEF LemmaBasic, AllConfigsAreServer, UpdateTerms
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

-----------------------------------------------------------------------------------

(* Init => *)

THEOREM InitImpliesTypeOK ==
ASSUME TRUE
PROVE Init => TypeOK
PROOF BY DEF Init, TypeOK

THEOREM InitImpliesLemmaBasic ==
ASSUME TRUE
PROVE Init => LemmaBasic
PROOF
    <1> SUFFICES ASSUME Init
        PROVE LemmaBasic
        PROOF OBVIOUS
    <1>. AllConfigsAreServer
        BY DEF Init, AllConfigsAreServer
    <1>. CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        BY DEF Init, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
    <1>. TermsOfEntriesGrowMonotonically
        BY DEF Init, TermsOfEntriesGrowMonotonically
    <1>. OnePrimaryPerTerm
        BY PrimaryAndSecondaryAreDifferent DEF Init, OnePrimaryPerTerm
    <1>. ExistsQuorumInLargestTerm
        <2>. ~ExistsPrimary
            BY PrimaryAndSecondaryAreDifferent DEF ExistsPrimary, Init
        <2>. \A s \in Server : currentTerm[s] = 0
            BY DEF Init
        <2>. \A s \in Server : \A Q \in QuorumsAt(s) : \A t \in Q : currentTerm[s] = currentTerm[t]
            BY QuorumsAreServerSubsets, InitImpliesTypeOK
        <2>. \E s \in Server : QuorumsAt(s) # {}
            BY ServerIsFinite, ServerIsNonempty, QuorumsExistForNonEmptySets DEF AllConfigsAreServer, QuorumsAt
        <2>1. QED
            BY DEF Init, ExistsQuorumInLargestTerm
    <1>. LogsMustBeSmallerThanOrEqualToLargestTerm
        BY DEF Init, Max, LastTerm, LogsMustBeSmallerThanOrEqualToLargestTerm
    <1>1. QED BY DEF LemmaBasic


-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM LemmaBasicAndNext ==
ASSUME TypeOK, LemmaBasic, Next
PROVE TypeOK' /\ LemmaBasic'
PROOF BY InitImpliesTypeOK, InitImpliesLemmaBasic, TypeOKAndNext,
         CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext,
         TermsOfEntriesGrowMonotonicallyAndNext,
         OnePrimaryPerTermAndNext,
         ExistsQuorumInLargestTermAndNext,
         LogsMustBeSmallerThanOrEqualToLargestTermAndNext,
         AllConfigsAreServerAndNext
      DEF LemmaBasic

THEOREM LemmaBasicIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => (TypeOK /\ LemmaBasic)
      /\ (TypeOK /\ LemmaBasic /\ Next) => (TypeOK /\ LemmaBasic)'
PROOF BY InitImpliesTypeOK, InitImpliesLemmaBasic, TypeOKAndNext, LemmaBasicAndNext

=============================================================================

