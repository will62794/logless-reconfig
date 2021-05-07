------------------- MODULE MongoStaticRaftProofsLemmaSecondariesFollowPrimary ---------------

EXTENDS MongoStaticRaft, MongoStaticRaftProofsLemmaBasic, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, TLAPS


LemmaSecondariesFollowPrimary ==
    /\ LemmaBasic
    /\ SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    /\ SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm


THEOREM GtImpliesGorT ==
ASSUME NEW a \in Nat, NEW b \in Nat
PROVE a >= b <=> (a = b \/ a > b)
OBVIOUS


THEOREM SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTermAndNext ==
ASSUME LemmaSecondariesFollowPrimary, TypeOK, Next
PROVE SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
PROOF
    <1>. LemmaBasic
        BY DEF LemmaSecondariesFollowPrimary
    <1>. DEFINE C1(s, p) ==
          /\ state[p] = Primary
          /\ currentTerm[p] = currentTerm[s]
          /\ LastTerm(log[p]) >= LastTerm(log[s])
          /\ Len(log[p]) >= Len(log[s])
    <1>. DEFINE C2(s, p) ==
          /\ state[p] = Primary
          /\ currentTerm[p] > currentTerm[s]
    <1>. DEFINE C3 == \A t \in Server : state[t] = Secondary
    <1>. DEFINE Reqs(s) ==
            (state[s] = Secondary /\ LastTerm(log[s]) = currentTerm[s]) =>
               \/ \E p \in Server : C1(s,p)
               \/ \E p \in Server : C2(s,p)
               \/ C3
    <1>1. (\E s \in Server : ClientRequest(s)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        <2>. SUFFICES ASSUME \E s \in Server : ClientRequest(s)
             PROVE \A s \in Server : (Reqs(s))'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. ~(\A t \in Server : state[t] = Secondary)
            BY PrimaryAndSecondaryAreDifferent DEF ClientRequest
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state'[s] = Secondary, LastTerm(log'[s]) = currentTerm'[s]
             PROVE \E p \in Server : (C1(s,p))' \/ (C2(s,p))'
             BY DEF Reqs
        <2>. CASE state[s] = Secondary /\ LastTerm(log[s]) = currentTerm[s]
            <3>. CASE \E p \in Server : C1(s,p)
                <4>. PICK p \in Server : C1(s,p)
                    OBVIOUS
                <4>. state'[p] = Primary /\ currentTerm'[p] = currentTerm'[s]
                    BY DEF C1, ClientRequest
                <4>. LastTerm(log'[p]) >= LastTerm(log'[s])
                    BY DEF C1, ClientRequest, LastTerm, TypeOK
                <4>. Len(log'[p]) >= Len(log'[s])
                    BY AppendProperties DEF C1, ClientRequest, LastTerm, TypeOK
                <4>1. QED BY DEF C1
            <3>. CASE \E p \in Server : C2(s,p)
                <4>. PICK p \in Server : C2(s,p)
                    OBVIOUS
                <4>. state'[p] = Primary
                    BY DEF C2, ClientRequest
                <4>. currentTerm'[p] > currentTerm'[s]
                    BY DEF C2, ClientRequest, LastTerm, TypeOK
                <4>1. QED BY DEF C2
            <3>1. QED BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. CASE state[s] = Primary \/ ~(LastTerm(log[s]) = currentTerm[s])
            BY PrimaryAndSecondaryAreDifferent DEF ClientRequest
        <2>1. QED BY PrimaryAndSecondaryAreDifferent DEF TypeOK, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, GetEntries(s, t)
             PROVE \A u \in Server : Reqs(u)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. TAKE u \in Server
        <2>. SUFFICES ASSUME state'[u] = Secondary, LastTerm(log'[u]) = currentTerm'[u]
             PROVE (\E p \in Server : C1(u,p)' \/ C2(u,p)') \/ C3'
             BY DEF Reqs
        <2>. SUFFICES ASSUME ~C3
             PROVE \E p \in Server : C1(u,p)' \/ C2(u,p)'
             BY DEF GetEntries, C3
        \* cases
        <2>. CASE u # s
            <3>. state[u] = Secondary
                BY DEF GetEntries
            <3>. CASE LastTerm(log[u]) # currentTerm[u]
                <4>1. QED BY DEF GetEntries
            <3>. CASE \E p \in Server : C1(u,p)
                <4>1. QED BY PrimaryAndSecondaryAreDifferent DEF GetEntries, C1
            <3>. CASE \E p \in Server : C2(u,p)
                <4>1. QED BY DEF GetEntries, C2
            <3>1. QED BY DEF C1, C2, C3, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. CASE u = s
            \* p is the largest primary
            <3>. PICK p \in Server :
                    /\ state[p] = Primary
                    /\ \A v \in Server : currentTerm[p] >= currentTerm[v]
                BY DEF C3, LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary, TypeOK
            <3>. CASE currentTerm[u] < currentTerm[p]
                <4>1. QED BY DEF GetEntries
            <3>. CASE currentTerm[u] = currentTerm[p]
                <4>. LastTerm(log[t]) = currentTerm[p]
                    <5>. DEFINE k == IF Empty(log[s]) THEN 1 ELSE Len(log[s]) + 1
                    <5>. log[t][k] = LastTerm(log'[u])
                        BY DEF GetEntries, LastTerm, TypeOK
                    <5>. currentTerm[p] = LastTerm(log'[u])
                        BY DEF GetEntries
                    <5>. LastTerm(log[t]) >= currentTerm[p]
                        BY DEF LastTerm, LemmaBasic, TermsOfEntriesGrowMonotonically, TypeOK, GetEntries
                    <5>1. QED BY DEF LastTerm, TypeOK, LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                \* the case where t is in the largest term
                <4>. CASE currentTerm[t] = currentTerm[p]
                    \* because there's at most one primary per term, t is either equal to p or a secondary
                    <5>. CASE state[t] = Secondary
                        \* in this case it turns out that t satisfies SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm so we
                        \* can leverage these properties for proving SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
                        <6>. LastTerm(log[t]) = currentTerm[t]
                            OBVIOUS
                        <6>. LastTerm(log[p]) >= LastTerm(log[t]) /\ Len(log[p]) >= Len(log[t])
                            BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm, TypeOK, LemmaBasic, OnePrimaryPerTerm
                        <6>1. QED BY DEF GetEntries, LastTerm
                    <5>. CASE t = p
                        <6>1. QED BY DEF GetEntries, LastTerm
                    <5>1. QED BY DEF LemmaBasic, OnePrimaryPerTerm, TypeOK
                \* the case where t is in a smaller term
                <4>. CASE currentTerm[t] < currentTerm[p]
                    <5>. CASE state[t] = Primary
                        \* this scenario is impossible
                        <6>1. QED BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, LastTerm, TypeOK
                    <5>. CASE state[t] = Secondary
                        \* SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm comes to the rescue
                        <6>1. QED BY DEF GetEntries, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
                    <5>1. QED BY DEF TypeOK
                <4>1. QED BY DEF TypeOK
            <3>1. QED BY DEF TypeOK
        <2>1. QED OBVIOUS
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, RollbackEntries(s, t)
             PROVE \A u \in Server : Reqs(u)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. TAKE u \in Server
        <2>. SUFFICES ASSUME state'[u] = Secondary, LastTerm(log'[u]) = currentTerm'[u]
             PROVE (\E p \in Server : C1(u,p)' \/ C2(u,p)') \/ C3'
             BY DEF Reqs
        <2>. SUFFICES ASSUME ~C3
             PROVE \E p \in Server : C1(u,p)' \/ C2(u,p)'
             BY DEF RollbackEntries, C3
        
        <2>. state[u] = Secondary
            BY PrimaryAndSecondaryAreDifferent DEF RollbackEntries
        <2>. CASE u # s
            \* relies on the primary from SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
            <3>. LastTerm(log[u]) = currentTerm[u]
                BY DEF LastTerm, RollbackEntries, TypeOK
            <3>. PICK p \in Server : C1(u,p) \/ C2(u,p)
                BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
            <3>. CASE state[s] = Secondary
                <4>. QED BY DEF RollbackEntries, TypeOK, LastTerm
            <3>. CASE state[s] = Primary
                <4>. CASE C1(u,p)
                    <5>. CASE s # p
                        <6>. QED BY DEF RollbackEntries
                    <5>. CASE s = p
                        <6>. LastTerm(log[p]) >= LastTerm(log[u])
                            OBVIOUS
                        <6>. LastTerm(log[t]) > LastTerm(log[p])
                            BY DEF RollbackEntries, CanRollback
                        <6>. PICK lt \in Server : LastTerm(log[t]) <= currentTerm[lt]
                            BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                        <6>. PICK lp \in Server : state[lp] = Primary /\ (\A v \in Server : currentTerm[lp] >= currentTerm[v]) \*/\ currentTerm[lp] >= currentTerm[lt]
                            BY DEF LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary
                        <6>. currentTerm[p] >= LastTerm(log[p])
                            BY DEF LastTerm, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
                        <6>. CASE lp # p
                            \* if lp # p then lp is a primary in a higher term than u
                            <7>. currentTerm[lp] > currentTerm[p]
                                BY DEF TypeOK, LemmaBasic, OnePrimaryPerTerm
                            <7>. currentTerm[lp] > currentTerm[u]
                                OBVIOUS
                            <7>. QED BY DEF RollbackEntries
                        <6>. CASE lp = p
                            \* this case is impossible, so we prove by contradiction
                            <7>. currentTerm[p] = currentTerm[u]
                                OBVIOUS
                            <7>. currentTerm[p] >= LastTerm(log[p])
                                BY DEF LastTerm, LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
                            <7>. LastTerm(log[t]) > currentTerm[p]
                                BY DEF LastTerm, TypeOK
                            <7>. \A v \in Server : LastTerm(log[v]) <= currentTerm[p]
                                BY DEF TypeOK, LastTerm
                            <7>. QED BY DEF TypeOK, LastTerm
                        <6>. QED OBVIOUS
                    <5>. QED OBVIOUS
                <4>. CASE C2(u,p)
                    <5>. QED BY DEF RollbackEntries
                <4>. QED OBVIOUS
            <3>. QED BY DEF TypeOK
        <2>. CASE u = s
            \* relies on the largest primary
            <4>. PICK p \in Server :
                    /\ state[p] = Primary
                    /\ \A v \in Server : currentTerm[p] >= currentTerm[v]
                BY DEF C3, LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary, TypeOK
            <4>. CASE currentTerm[u] < currentTerm[p]
                <5>1. QED BY DEF RollbackEntries
            <4>. CASE currentTerm[u] = currentTerm[p]
                \* fairly ridiculous that I need to spell this out
                <5>. Len(log[u]) = 1 \/ Len(log[u]) > 1
                    <6>. Len(log[u]) \in Nat
                        BY LenProperties
                    <6>. Len(log[u]) >= 1
                        BY DEF RollbackEntries, CanRollback
                    <6>. QED BY GtImpliesGorT
                <5>. CASE Len(log[u]) > 1
                    \* SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm is true for this case
                    <6>. DEFINE k == Len(log[u]) - 1
                    <6>. log[u][k] = LastTerm(log'[u])
                        BY TypeOKAndNext DEF LastTerm, RollbackEntries, TypeOK
                    <6>. log[u][k] = currentTerm[p]
                        BY DEF RollbackEntries
                    <6>. LastTerm(log[u]) = currentTerm[p]
                        <7>. LastTerm(log[u]) >= log[u][k]
                            BY DEF LastTerm, LemmaBasic, TermsOfEntriesGrowMonotonically
                        <7>. LastTerm(log[u]) <= currentTerm[p]
                            <8>. PICK lt \in Server :  LastTerm(log[u]) <= currentTerm[lt]
                                BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                            <8>. currentTerm[lt] <= currentTerm[p]
                                OBVIOUS
                            <8>. QED BY DEF LastTerm, TypeOK
                        <7>. QED BY DEF LastTerm, TypeOK
                    <6>. PICK pu \in Server : C1(u,pu) \/ C2(u,pu)
                        BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
                    <6>. log'[pu] = log[pu]
                        BY DEF RollbackEntries, TypeOK
                    <6>. QED BY DEF RollbackEntries, LastTerm, TypeOK
                <5>. CASE Len(log[u]) = 1
                    <6>. Len(log'[u]) = 0
                        BY DEF RollbackEntries, TypeOK
                    <6>. LastTerm(log'[p]) >= LastTerm(log'[u]) /\ Len(log'[p]) >= Len(log'[u])
                        BY TypeOKAndNext DEF TypeOK, LastTerm
                    <6>. QED BY DEF RollbackEntries
                <5>. QED OBVIOUS
            <4>. QED BY DEF TypeOK
        <2>. QED OBVIOUS
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        <2>. SUFFICES ASSUME NEW p \in Server, NEW Q \in QuorumsAt(p), BecomeLeader(p, Q)
             PROVE \A s \in Server : Reqs(s)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. \A t \in Server : currentTerm[p] >= currentTerm[t]
            BY ElectedLeadersHaveLatestTerm
        <2>. TAKE s \in Server
        <2>. CASE s \notin Q
            <3>. \A t \in Server : t \notin Q => currentTerm'[p] > currentTerm'[t]
                BY DEF BecomeLeader, TypeOK
            <3>. state'[p] = Primary
                BY DEF BecomeLeader
            <3>. QED OBVIOUS
        <2>. CASE s = p
            <3>. QED BY DEF BecomeLeader, TypeOK
        <2>. CASE s \in Q /\ s # p
            <3>. state'[s] = Secondary
                BY DEF BecomeLeader, TypeOK
            <3>. LastTerm(log[s]) <= currentTerm[p]
                BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm, LastTerm, TypeOK
            <3>. QED BY DEF BecomeLeader, TypeOK
        <2>. QED BY DEF BecomeLeader
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        BY DEF CommitEntry, TypeOK, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm'
        <2>. SUFFICES ASSUME NEW s \in Server, NEW t \in Server, UpdateTerms(s, t)
             PROVE \A u \in Server : Reqs(u)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        <2>. TAKE u \in Server
        <2>. SUFFICES ASSUME state'[u] = Secondary, LastTerm(log'[u]) = currentTerm'[u]
             PROVE (\E p \in Server : C1(u,p)' \/ C2(u,p)') \/ C3'
             BY DEF Reqs
        <2>. SUFFICES ASSUME ~C3
             PROVE (\E p \in Server : C1(u,p)' \/ C2(u,p)') \/ C3'
             BY DEF UpdateTerms, UpdateTermsExpr
        
        <2>. CASE u # t
            <3>. LastTerm(log[u]) = currentTerm[u]
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK, LastTerm
            <3>. state[u] = Secondary
                BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>. PICK p \in Server : C1(u,p) \/ C2(u,p)
                BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
            <3>. CASE p # t
                <4>. QED BY DEF UpdateTerms, UpdateTermsExpr
            <3>. CASE p = t
                <4>. PICK lp \in Server : state[lp] = Primary /\ currentTerm[lp] >= currentTerm[s]
                    BY DEF LemmaBasic, ExistsQuorumInLargestTerm, ExistsPrimary
                <4>. currentTerm[lp] > currentTerm[u]
                    BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>. QED BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
            <3>. QED OBVIOUS
        <2>. CASE u = t
            <3>. CASE ExistsPrimary'
                <4>. ExistsPrimary
                    BY DEF UpdateTerms, UpdateTermsExpr, ExistsPrimary, TypeOK
                <4>. PICK p \in Server :
                        /\ state[p] = Primary
                        /\ \A v \in Server : currentTerm[p] >= currentTerm[v]
                        /\ \E Q \in QuorumsAt(p) : \A q \in Q : currentTerm[q] = currentTerm[p]
                    BY DEF LemmaBasic, ExistsQuorumInLargestTerm
                <4>. CASE currentTerm[s] # currentTerm[p]
                    <5>. QED BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                <4>. CASE currentTerm[s] = currentTerm[p]
                    <5>. LastTerm(log[u]) = currentTerm[p]
                        BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                    <5>. LastTerm(log[u]) > currentTerm[u]
                        BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                    <5>. state[u] = Secondary
                        BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, LastTerm, TypeOK
                    <5>. DEFINE E1(ss,pp) == 
                          /\ state[pp] = Primary
                          /\ currentTerm[pp] = LastTerm(log[ss])
                          /\ LastTerm(log[pp]) >= LastTerm(log[ss])
                          /\ Len(log[pp]) >= Len(log[ss])
                    <5>. DEFINE E2(ss,pp) ==
                          /\ state[pp] = Primary
                          /\ currentTerm[pp] > LastTerm(log[ss])
                    <5>. state[u] = Secondary /\ LastTerm(log[u]) > currentTerm[u]
                        OBVIOUS
                    <5>. PICK lp \in Server : E1(u,lp) \/ E2(u,lp)
                        BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm, ExistsPrimary
                    <5>. CASE E1(u,lp)
                        <6>. QED BY DEF UpdateTerms, UpdateTermsExpr, TypeOK
                    <5>. CASE E2(u,lp)
                        \* this case isn't possible
                        <6>. QED BY DEF LastTerm, TypeOK
                    <5>. QED OBVIOUS
                <4>. QED OBVIOUS
            <3>. CASE ~ExistsPrimary'
                <4>. QED BY PrimaryAndSecondaryAreDifferent, TypeOKAndNext DEF ExistsPrimary, TypeOK
            <3>. QED OBVIOUS
        <2>. QED OBVIOUS
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTermAndNext ==
ASSUME LemmaSecondariesFollowPrimary, TypeOK, Next
PROVE SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
PROOF
    <1>. LemmaBasic
        BY DEF LemmaSecondariesFollowPrimary
    <1>. DEFINE E1(s,p) ==
                  /\ state[p] = Primary
                  /\ currentTerm[p] = LastTerm(log[s]) \* different from matches
                  /\ LastTerm(log[p]) >= LastTerm(log[s])
                  /\ Len(log[p]) >= Len(log[s])
    <1>. DEFINE E2(s,p) ==
                  /\ state[p] = Primary
                  /\ currentTerm[p] > LastTerm(log[s])
    <1>. DEFINE E3 == \A t \in Server : state[t] = Secondary
    <1>. DEFINE Reqs(s) ==
            (state[s] = Secondary /\ LastTerm(log[s]) > currentTerm[s]) =>
               \/ \E p \in Server : E1(s,p)
               \/ \E p \in Server : E2(s,p)
               \/ E3
    <1>1. (\E s \in Server : ClientRequest(s)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
        <2>. SUFFICES ASSUME \E s \in Server : ClientRequest(s)
             PROVE \A s \in Server : Reqs(s)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state'[s] = Secondary, LastTerm(log'[s]) > currentTerm'[s], ~E3
             PROVE (\E p \in Server : E1(s,p)' \/ E2(s,p)') \/ E3'
             BY DEF Reqs, ClientRequest
        <2>. PICK p \in Server : E1(s,p) \/ E2(s,p)
            BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm, ClientRequest, TypeOK
        <2>. CASE E1(s,p)
            <3>. SUFFICES ASSUME ClientRequest(p)
                 PROVE (\E r \in Server : E1(s,r)' \/ E2(s,r)') \/ E3'
                 BY DEF ClientRequest, TypeOK
            <3>. LastTerm(log'[p]) >= LastTerm(log[p])
                <4>. CASE Len(log[p]) = 0
                    <5>. QED BY TypeOKAndNext DEF TypeOK, LastTerm
                <4>. CASE Len(log[p]) > 0
                    <5>. Len(log'[p]) > 1
                        BY DEF ClientRequest, TypeOK
                    <5>. DEFINE k == Len(log'[p])
                    <5>. log'[p][k-1] = LastTerm(log[p])
                        BY DEF ClientRequest, LastTerm, TypeOK
                    <5>. log'[p][k] >= log'[p][k-1]
                        BY LemmaBasicAndNext, TermsOfEntriesGrowMonotonicallyAndNext DEF LemmaBasic, TermsOfEntriesGrowMonotonically
                    <5>. QED BY DEF LastTerm, TypeOK
                <4>. QED BY DEF TypeOK
            <3>. QED BY DEF ClientRequest, LastTerm, TypeOK
        <2>. CASE E2(s,p)
            <3>. QED BY DEF ClientRequest, TypeOK
        <2>. QED OBVIOUS
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
        <2>. SUFFICES ASSUME \E s,t \in Server : GetEntries(s, t)
             PROVE \A s \in Server : Reqs(s)'
             BY DEF SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
        <2>. TAKE s \in Server
        <2>. SUFFICES ASSUME state'[s] = Secondary, LastTerm(log'[s]) > currentTerm'[s], ~E3
             PROVE (\E p \in Server : E1(s,p)' \/ E2(s,p)') \/ E3'
             BY DEF Reqs, GetEntries
        <2>. state[s] = Secondary
            BY DEF GetEntries
        
        <2>. CASE \E t \in Server : GetEntries(s, t)
            (*<3>. PICK p \in Server : state'[p] = Primary /\ (\A u \in Server : currentTerm'[p] >= currentTerm'[u])
                BY LemmaBasicAndNext, ExistsQuorumInLargestTermAndNext, TypeOKAndNext
                    DEF LemmaBasic, ExistsQuorumInLargestTerm, TypeOK, GetEntries, ExistsPrimary*)
            <3>. PICK p \in Server : state[p] = Primary /\ (\A u \in Server : currentTerm[p] >= currentTerm[u])
                BY DEF LemmaBasic, ExistsQuorumInLargestTerm, TypeOK, ExistsPrimary
            <3>. state'[p] = Primary /\ (\A u \in Server : currentTerm'[p] >= currentTerm'[u])
                BY DEF GetEntries, TypeOK
            <3>. CASE currentTerm'[p] > LastTerm(log'[s])
                <4>. QED OBVIOUS
            <3>. CASE currentTerm'[p] = LastTerm(log'[s])
                <4>. PICK t \in Server : GetEntries(s, t)
                    OBVIOUS
                <4>. DEFINE k == IF Empty(log[s]) THEN 1 ELSE Len(log[s]) + 1
                <4>. LastTerm(log[t]) = currentTerm[p]
                    <5>. LastTerm(log'[s]) = log[t][k]
                        BY DEF GetEntries, LastTerm, TypeOK
                    <5>. currentTerm[p] = currentTerm'[p]
                        BY DEF GetEntries
                    <5>. LastTerm(log[t]) >= log[t][k]
                        BY DEF LastTerm, LemmaBasic, TermsOfEntriesGrowMonotonically, GetEntries, Empty, TypeOK
                    <5>. LastTerm(log[t]) >= currentTerm[p]
                        BY DEF TypeOK
                    <5>. QED BY DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm, LastTerm, TypeOK
                <4>1. LastTerm(log'[s]) = LastTerm(log[t])
                    BY DEF LastTerm, LemmaBasic, TermsOfEntriesGrowMonotonically, GetEntries, TypeOK
                <4>. CASE state[t] = Primary
                    <5>. t = p
                        BY DEF LemmaBasic, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, OnePrimaryPerTerm, LastTerm, TypeOK
                    <5>. E1(s,p)' \* for some reason TLAPS needs this to be 2 steps
                        BY DEF GetEntries, LastTerm, TypeOK
                    <5>. QED OBVIOUS
                <4>. CASE state[t] = Secondary
                    <5>. CASE currentTerm[t] = currentTerm[p]
                        <6>. DEFINE C1(ss, pp) ==
                              /\ state[pp] = Primary
                              /\ currentTerm[pp] = currentTerm[ss]
                              /\ LastTerm(log[pp]) >= LastTerm(log[ss])
                              /\ Len(log[pp]) >= Len(log[ss])
                        <6>. LastTerm(log[t]) = currentTerm[t]
                            BY DEF LastTerm
                        <6>. C1(t,p)
                            <7>. PICK lp \in Server : C1(t,lp)
                                BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm, TypeOK
                            <7>. p = lp
                                BY DEF LemmaBasic, OnePrimaryPerTerm
                            <7>. QED OBVIOUS
                        <6>. E1(s,p)' \* 2 steps again...
                            BY <4>1 DEF GetEntries
                        <6>. QED OBVIOUS
                    <5>. CASE currentTerm[t] < currentTerm[p]
                        <6>. LastTerm(log[t]) > currentTerm[t]
                            BY DEF LastTerm
                        <6>. PICK lp \in Server : E1(t,lp) \/ E2(t,lp)
                            BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
                        <6>. CASE E1(t,lp)
                            <7>. E1(s,lp)' \* for some reason TLAPS needs this to be 2 steps
                                BY DEF GetEntries, LastTerm, TypeOK
                            <7>. QED OBVIOUS
                        <6>. CASE E2(t,lp)
                            <7>. QED BY DEF GetEntries
                        <6>. QED OBVIOUS
                    <5>. QED BY DEF TypeOK
                <4>. QED BY DEF TypeOK
            <3>. CASE currentTerm'[p] < LastTerm(log'[s])
                \* this is impossible, proof by contradiction
                <4>. currentTerm'[p] >= LastTerm(log'[s])
                    <5>. \A t \in Server : \E lp \in Server : LastTerm(log'[t]) <= currentTerm'[lp]
                        BY LemmaBasicAndNext, LogsMustBeSmallerThanOrEqualToLargestTermAndNext
                            DEF LemmaBasic, LogsMustBeSmallerThanOrEqualToLargestTerm
                    <5>. \A t \in Server : currentTerm'[p] >= currentTerm'[t]
                        OBVIOUS
                    <5>. QED BY TypeOKAndNext DEF LastTerm, TypeOK
                <4>. QED BY TypeOKAndNext DEF LastTerm, TypeOK
            <3>. QED BY TypeOKAndNext DEF LastTerm, TypeOK
        <2>. CASE \E t,u \in Server : GetEntries(u, t) /\ u # s
            <3>. CASE LastTerm(log[s]) > currentTerm[s]
                <4>. CASE \E p \in Server : E1(s,p)
                    <5>. PICK p \in Server : E1(s,p)
                        OBVIOUS
                    <5>. E1(s,p)' \* for some reason TLAPS needs this to be 2 steps
                        BY DEF GetEntries, LastTerm, TypeOK
                    <5>. QED OBVIOUS
                <4>. CASE \E p \in Server : E2(s,p)
                    <5>. QED BY DEF GetEntries, LastTerm, TypeOK
                <4>. QED BY DEF LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
            <3>. CASE LastTerm(log[s]) <= currentTerm[s]
                <4>. QED BY DEF GetEntries, LastTerm, TypeOK
            <3>. QED BY DEF LastTerm, TypeOK
        <2>. QED OBVIOUS
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
        BY DEF CommitEntry, TypeOK, LemmaSecondariesFollowPrimary, SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm'
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


(* Template
THEOREM LemmaBasic /\ TypeOK /\ Next => TypeOK'
PROOF
    <1>1. (\E s \in Server : ClientRequest(s)) => TypeOK'
    <1>2. (\E s, t \in Server : GetEntries(s, t)) => TypeOK'
    <1>3. (\E s, t \in Server : RollbackEntries(s, t)) => TypeOK'
    <1>4. (\E s \in Server : \E Q \in QuorumsAt(s) : BecomeLeader(s, Q)) => TypeOK'
    <1>5. (\E s \in Server :  \E Q \in QuorumsAt(s) : CommitEntry(s, Q)) => TypeOK'
    <1>6. (\E s,t \in Server : UpdateTerms(s, t)) => TypeOK'
    <1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next
*)

-----------------------------------------------------------------------------------

(* Init => LemmaSecondariesFollowPrimary *)

THEOREM InitImpliesLemmaSecondariesFollowPrimary ==
ASSUME TRUE
PROVE Init => LemmaSecondariesFollowPrimary
PROOF
    <1>. Init => \A s \in Server : state[s] = Secondary
         BY DEF Init
    <1>. Init => SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
        BY DEF SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTerm
    <1>. Init => SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
        BY DEF SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTerm
    <1>1. QED BY InitImpliesLemmaBasic DEF LemmaSecondariesFollowPrimary

-----------------------------------------------------------------------------------

(* Overall Result *)

THEOREM LemmaSecondariesFollowPrimaryAndNext ==
ASSUME TypeOK, LemmaSecondariesFollowPrimary, Next
PROVE TypeOK' /\ LemmaSecondariesFollowPrimary'
PROOF BY InitImpliesLemmaSecondariesFollowPrimary, TypeOKAndNext,
         LemmaBasicAndNext,
         SecondariesMustFollowPrimariesWhenLogTermMatchesCurrentTermAndNext,
         SecondariesMustFollowPrimariesWhenLogTermExceedsCurrentTermAndNext
      DEF LemmaSecondariesFollowPrimary

THEOREM LemmaSecondariesFollowPrimaryIsInductiveInvariant ==
ASSUME TRUE
PROVE /\ Init => (TypeOK /\ LemmaSecondariesFollowPrimary)
      /\ (TypeOK /\ LemmaSecondariesFollowPrimary /\ Next) => (TypeOK /\ LemmaSecondariesFollowPrimary)'
PROOF BY InitImpliesTypeOK, InitImpliesLemmaSecondariesFollowPrimary, TypeOKAndNext, LemmaSecondariesFollowPrimaryAndNext

=============================================================================

