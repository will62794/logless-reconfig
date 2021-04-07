------------------------- MODULE MongoStaticRaftProofsLemmaBasic -------------------

\* Finding inductive invariants for MongoStaticRaft protocol.

EXTENDS MongoStaticRaft, SequenceTheorems, FunctionTheorems

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

THEOREM EXCEPT_Eq ==
ASSUME NEW f, NEW k, NEW u
PROVE [f EXCEPT![k] = u][k] = u
OMITTED

THEOREM EXCEPT_Neq ==
ASSUME NEW f, NEW k, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE \A i \in DOMAIN g : i # k => g[i] = f[i]
PROOF OMITTED

THEOREM EXCEPT_Domain ==
ASSUME NEW f, NEW k, NEW u,
       NEW g, g = [f EXCEPT![k] = u]
PROVE DOMAIN g = DOMAIN f
PROOF OMITTED

THEOREM FuncSetDef ==
ASSUME NEW f, NEW Dom, NEW Rnge,
       Dom = DOMAIN f
PROVE (\A x \in Dom : f[x] \in Rnge) <=> f \in [Dom -> Rnge]
PROOF
    <1>1. (\A x \in Dom : f[x] \in Rnge) => f \in [Dom -> Rnge]
        <2>. SUFFICES ASSUME \A x \in Dom : f[x] \in Rnge
             PROVE f \in [Dom -> Rnge]
             OBVIOUS
        <2>1. Rnge \subseteq Range(f)
            BY DEF Range
        <2>20. QED
    <1>2. f \in [Dom -> Rnge] => (\A x \in Dom : f[x] \in Rnge)
    <1>3. QED
        BY <1>1, <1>2

THEOREM AppendedLogTypeOK ==
ASSUME NEW log1 \in [Server -> Seq(Nat)],
       NEW s \in Server, NEW n \in Nat,
       NEW log2, log2 =  [log1 EXCEPT ![s] = Append(log1[s], n)]
PROVE log2 \in [Server -> Seq(Nat)]
PROOF
    <1>1. Append(log1[s], n) \in Seq(Nat)
        BY AppendProperties
    <1>2. \A u \in Server : u # s => log2[u] \in Seq(Nat)
        BY <1>1, EXCEPT_Neq
    <1>3. \A u \in Server : u = s => log2[u] \in Seq(Nat)
        BY <1>1, EXCEPT_Eq
    <1>4. DOMAIN log2 = Server
        BY EXCEPT_Domain
        
    <1>5. log1 \in Surjection(Server, Range(log1))
        BY Fun_RangeProperties
    <1>6. Range(log1) \in SUBSET Seq(Nat)
        BY Fun_RangeProperties
    <1>7. Range(log2) \in SUBSET Seq(Nat)
        BY <1>2, <1>3 DEF Range
    <1>50. QED
        BY <1>4, <1>7 \*<1>2, <1>3, <1>4, FuncSetDef

THEOREM AppendedCurrentTermTypeOK ==
ASSUME TypeOK,
       NEW log1 \in [Server -> Seq(Nat)],
       NEW s \in Server,
       NEW log2, log2 =  [log1 EXCEPT ![s] = Append(log1[s], currentTerm[s])]
PROVE log2 \in [Server -> Seq(Nat)]
PROOF
    <1>1. currentTerm[s] \in Nat
        BY DEF TypeOK
    <1>2. QED
        BY AppendedLogTypeOK, <1>1

THEOREM FuncDomain ==
ASSUME NEW Dom, NEW Rng(_),
       NEW f, f = [x \in Dom |-> Rng(x)]
PROVE Dom = DOMAIN f
PROOF OMITTED

THEOREM FuncDomainRangeDef ==
ASSUME NEW Dom, NEW Rng, NEW f
PROVE f \in [Dom -> Rng] <=> (DOMAIN(f) = Dom /\ Range(f) \in SUBSET Rng)
PROOF OMITTED

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary

THEOREM LemmaBasic /\ TypeOK /\ Next => CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
PROOF OMITTED

THEOREM TypeOK /\ Next => TypeOK'
PROOF
    <1> SUFFICES ASSUME TypeOK, Next
        PROVE TypeOK'
        PROOF OBVIOUS
    <1>1. (\E s \in Server : ClientRequest(s)) => TypeOK'
        <2> SUFFICES ASSUME (\E s \in Server : ClientRequest(s))
            PROVE TypeOK'
            PROOF OBVIOUS
        <2>1. log' \in [Server -> Seq(Nat)]
            BY AppendedCurrentTermTypeOK DEF ClientRequest, TypeOK
        <2>2. QED
            BY <2>1 DEF TypeOK, ClientRequest
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => TypeOK'
        <2> SUFFICES ASSUME (\E s, t \in Server : GetEntries(s, t))
            PROVE TypeOK'
            PROOF OBVIOUS
        <2>1. log' \in [Server -> Seq(Nat)]
            BY AppendedCurrentTermTypeOK DEF GetEntries, TypeOK
        <2>2. QED
            BY <2>1 DEF TypeOK, GetEntries
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => TypeOK'
        <2> SUFFICES ASSUME (\E s, t \in Server : RollbackEntries(s, t))
            PROVE TypeOK'
            PROOF OBVIOUS
        <2>1. log' \in [Server -> Seq(Nat)]
            BY AppendedCurrentTermTypeOK DEF RollbackEntries, TypeOK
        <2>2. QED
            BY <2>1 DEF TypeOK, RollbackEntries
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => TypeOK'
        <2>. SUFFICES ASSUME (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q))
             PROVE TypeOK'
             PROOF OBVIOUS
        <2>. PICK s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
            OBVIOUS
        <2>1. currentTerm' \in [Server -> Nat]
            <3> SUFFICES ASSUME \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)
                PROVE currentTerm' \in [Server -> Nat]
                PROOF OBVIOUS
            <3>2. PICK Q \in QuorumsAt(s) : BecomeLeader(s, Q)
                OBVIOUS
            <3>3. currentTerm' = [t \in Server |-> IF t \in Q THEN currentTerm[s]+1 ELSE currentTerm[t]]
                BY <3>2 DEF BecomeLeader
            <3>4. \A t \in Server : currentTerm'[t] \in Nat
                BY <3>3 DEF TypeOK
            <3>5. QED
                BY <3>3, <3>4, FuncSetDef
        <2>2. state' \in [Server -> {Secondary, Primary}]
            <3>2. PICK Q \in QuorumsAt(s) : BecomeLeader(s, Q)
                OBVIOUS
            <3>. DEFINE P(t) == IF t = s THEN Primary ELSE IF t \in Q THEN Secondary ELSE state[t]
            <3>4. state' = [t \in Server |-> P(t)]
                BY <3>2 DEF BecomeLeader
            <3>5. DOMAIN state' = Server
                BY <3>4, FuncDomain
            <3>6. Range(state') = { state'[t] : t \in Server }
                BY <3>5 DEF Range
            <3>7. Range(state') = { P(t) : t \in Server }
                BY <3>4, <3>6
            <3>8. { P(t) : t \in Server } \in SUBSET {Secondary, Primary}
                BY DEF TypeOK
            <3>9. Range(state') \in SUBSET {Secondary, Primary}
                BY <3>7, <3>8
            <3>10. QED
                BY <3>5, <3>9, FuncDomainRangeDef
        <2>3. elections' \in SUBSET [ leader : Server, term : Nat ]
            <3>1. elections' = elections \cup {[ leader |-> s, term |-> currentTerm[s]+1 ]}
                BY DEF BecomeLeader
            <3>3. QED
                BY <3>1 DEF TypeOK
        <2>4. log' \in [Server -> Seq(Nat)]
            <3>2. currentTerm[s] + 1 \in Nat
                BY DEF TypeOK
            <3>3. QED
                BY <3>2, AppendedLogTypeOK DEF BecomeLeader, TypeOK
        <2>5. QED
            BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK, BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TypeOK'
        <2> SUFFICES ASSUME (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q))
            PROVE TypeOK'
            PROOF OBVIOUS
        <2>1. committed' \in SUBSET [ entry : Nat \times Nat, term : Nat]
            BY DEF CommitEntry, TypeOK
        <2>2. QED BY <2>1 DEF TypeOK, CommitEntry
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TypeOK'
        <2> SUFFICES ASSUME (\E s,t \in Server : UpdateTerms(s, t))
            PROVE TypeOK'
            PROOF OBVIOUS
        <2>1. currentTerm' \in [Server -> Nat]
            <3> SUFFICES ASSUME \E s,t \in Server : UpdateTerms(s, t)
                PROVE currentTerm' \in [Server -> Nat]
                PROOF OBVIOUS
            <3>1. PICK s,t \in Server : currentTerm' = [currentTerm EXCEPT ![t] = currentTerm[s]]
                BY DEF UpdateTerms, UpdateTermsExpr
            <3>2. \A u \in Server : currentTerm[u] \in Nat
                BY DEF TypeOK
            <3>3. \A u \in Server : u # t => currentTerm'[u] \in Nat
                BY <3>1, <3>2, EXCEPT_Neq
            <3>4. currentTerm'[t] \in Nat
                BY <3>1, <3>2, EXCEPT_Eq
            <3>5. \A u \in Server : currentTerm'[u] \in Nat
                BY <3>3, <3>4
            <3>6. DOMAIN currentTerm' = Server
                BY <3>1, EXCEPT_Domain DEF TypeOK
            <3>20. QED
                BY <3>5, <3>6, FuncSetDef
        <2>2. state' \in [Server -> {Secondary, Primary}]
            <3>1. PICK s,t \in Server : UpdateTerms(s, t)
                OBVIOUS
            <3>2. state' = [state EXCEPT ![t] = Secondary]
                BY <3>1 DEF UpdateTerms, UpdateTermsExpr
            <3>3. \A u \in Server : u # t => state'[u] \in {Secondary, Primary}
                BY <3>2, EXCEPT_Neq DEF TypeOK
            <3>4. \A u \in Server : u = t => state'[u] \in {Secondary, Primary}
                BY <3>2, EXCEPT_Eq
            <3>5. DOMAIN state' = Server
                BY <3>2, EXCEPT_Domain DEF TypeOK
            <3>6. QED
                BY FuncSetDef, <3>3, <3>4, <3>5
        <2>3. QED BY <2>1, <2>2 DEF TypeOK, UpdateTerms, UpdateTermsExpr
    <1>7. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

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
    <1>8. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF LemmaBasic

=============================================================================

