----------------------------- MODULE LogLemmas -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib

\* 2-4 hours
LEMMA LogMatchingAndNext_ClientRequest ==
ASSUME Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       OSM!ClientRequest(s),
       s # t,
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <4>ok. TypeOK BY DEF Ind
    <4>. SUFFICES ASSUME i > 1
         PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
         BY <4>ok, TypeOKAndNext DEF OSM!ClientRequest, TypeOK
    <4>1. log[s][i-1] = log'[s][i-1] BY DEF OSM!ClientRequest, TypeOK
    <4>2. log[t][i] = log'[t][i] BY DEF OSM!ClientRequest, TypeOK
    <4>3. CASE log[s][i-1] = log[t][i-1]
        BY <4>3 DEF Ind, LogMatching, EqualUpTo, OSM!ClientRequest, TypeOK
    <4>4. CASE log[s][i-1] # log[t][i-1]
        \* proof by contradiction, we will see that s is a primary without the log entries it created
        <5>1. Len(log[s]) = i-1
            <6>1. SUFFICES ASSUME Len(log[s]) # i-1
                  PROVE FALSE OBVIOUS
            <6>2. i-1 \in DOMAIN log[s] BY <4>4 DEF OSM!ClientRequest, TypeOK
            <6>3. Len(log[s]) > i-1 BY <4>4, <6>1, <6>2 DEF TypeOK
            <6>4. log[s][i] = log'[s][i] BY <6>3 DEF OSM!ClientRequest, TypeOK
            <6>5. log[s][i] = log[t][i] BY <4>2, <6>4 DEF TypeOK
            <6>6. log[s][i-1] = log[t][i-1]
                <7>1. i \in (DOMAIN log[s] \cap DOMAIN log[t]) BY <6>3 DEF OSM!ClientRequest, TypeOK
                <7>2. i-1 > 0 /\ i-1 <= i BY <6>3, TypeOKAndNext DEF OSM!ClientRequest, TypeOK
                <7>. QED BY <6>5, <7>1, <7>2 DEF Ind, LogMatching, EqualUpTo, TypeOK
            <6>. QED BY <4>4, <6>6 DEF TypeOK
        <5>2. log'[s][i] = currentTerm[s] BY <5>1 DEF OSM!ClientRequest
        <5>3. log[t][i] = currentTerm[s] BY <5>2 DEF OSM!ClientRequest
        <5>. QED BY <5>1, <5>3 DEF Ind, PrimaryHasEntriesItCreated, InLog, OSM!ClientRequest
    <4>. QED BY <4>3, <4>4

LEMMA LogMatchingAndNext_GetEntries ==
ASSUME Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       OSM!GetEntries(s, t),
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <1>1. TAKE j \in Nat
    <1>2. CASE j = i BY <1>2
    <1>3. CASE j < i
        <2>1. SUFFICES ASSUME ~Empty(log[s])
              PROVE (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
              BY DEF OSM!GetEntries, Empty, TypeOK
        <2>.  DEFINE sLastIdx == Len(log[s])
        <2>3. log[s][sLastIdx] = log[t][sLastIdx] BY <2>1, EmptyIdentical DEF OSM!GetEntries, Ind
        <2>4. j <= sLastIdx BY <1>3, <2>1 DEF OSM!GetEntries, Empty, TypeOK
        <2>. QED BY <1>1, <2>3, <2>4 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3 DEF OSM!GetEntries, TypeOK

LEMMA LogMatchingAndNext_GetEntriesOneOutside ==
ASSUME Ind, Next,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       NEW v \in Server,
       OSM!GetEntries(u, v),
       s # u, s # v,
       NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
       log'[s][i] = log'[t][i]
PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. TAKE j \in Nat
    <1>2. CASE j = i BY <1>2
    <1>3. CASE j < i
        <2>1. SUFFICES ASSUME ~Empty(log[s])
              PROVE (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
              BY DEF OSM!GetEntries, Empty, TypeOK
        <2>2. CASE t = u BY <1>1, <1>3, <2>1, <2>2 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, Empty, OSM!Empty, TypeOK
        <2>3. CASE t # u BY <1>1, <1>3, <2>1, <2>3 DEF Ind, LogMatching, EqualUpTo, OSM!GetEntries, TypeOK
        <2>. QED BY <2>2, <2>3
    <1>. QED BY <1>ok, <1>1, <1>2, <1>3 DEF OSM!GetEntries, TypeOK

\* began: 8/26
\* finished: 8/26
\* took a few hours, maybe 2-5
LEMMA LogMatchingAndNext ==
ASSUME Ind, Next
PROVE LogMatching'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME NEW s \in Server, NEW t \in Server,
                                  NEW i \in (DOMAIN log[s] \cap DOMAIN log[t])',
                                  log'[s][i] = log'[t][i]
                  PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
                  BY DEF LogMatching, EqualUpTo
            <3>2. SUFFICES ASSUME i > 1
                  PROVE \A j \in Nat : (j > 0 /\ j <= i) => log'[s][j] = log'[t][j]
                  BY <1>ok, <3>1, TypeOKAndNext DEF OSM!ClientRequest, TypeOK
            <3>3. CASE s = t BY <3>1, <3>2, <3>3 DEF OSM!ClientRequest, TypeOK
            <3>4. CASE OSM!ClientRequest(s) /\ s # t BY <3>1, <3>2, <3>4, LogMatchingAndNext_ClientRequest
            <3>5. CASE OSM!ClientRequest(t) /\ s # t BY <3>1, <3>2, <3>5, LogMatchingAndNext_ClientRequest
            <3>6. CASE ~OSM!ClientRequest(s) /\ ~OSM!ClientRequest(t) /\ s # t
                <4>1. log[s][i] = log[t][i] BY <1>ok, <2>1, <3>1, <3>6 DEF OSM!ClientRequest, TypeOK
                <4>2. i \in (DOMAIN log[s] \cap DOMAIN log[t]) BY <1>ok, <2>1, <3>1, <3>6 DEF OSM!ClientRequest, TypeOK
                <4>3. \A j \in Nat : (j > 0 /\ j <= i) => log[s][j] = log[t][j] BY <3>1, <4>1, <4>2 DEF Ind, LogMatching, EqualUpTo
                <4>. QED BY <2>1, <3>1, <3>6, <4>3 DEF OSM!ClientRequest, TypeOK
            <3>. QED BY <3>3, <3>4, <3>5, <3>6
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2, LogMatchingAndNext_GetEntries, LogMatchingAndNext_GetEntriesOneOutside DEF LogMatching, EqualUpTo
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF Ind, LogMatching, EqualUpTo, OSM!RollbackEntries, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            <3>1. UNCHANGED log BY <2>4 DEF OSM!CommitEntry, TypeOK
            <3>. QED BY <3>1 DEF Ind, LogMatching, EqualUpTo
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, LogMatching, EqualUpTo
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. CASE UNCHANGED log BY <3>2 DEF Ind, LogMatching, EqualUpTo
            <3>3. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                <4>1. \A t \in Server : t # p => (\A i \in DOMAIN log[t] : LastTerm(log'[p]) > log'[t][i])
                    <5>1. \A t \in Server : currentTerm[p] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind
                    <5>2. \A t \in Server : \A i \in DOMAIN log[t] : currentTerm[p] >= log[t][i]
                        BY <3>1, <5>1 DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
                    <5>3. LastTerm(log'[p]) > currentTerm[p] BY <1>ok, <3>1, <3>3, <5>2, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>4. \A t \in Server : \A i \in DOMAIN log[t] : LastTerm(log'[p]) > log[t][i]
                        BY <1>ok, <3>1, <5>2, <5>3, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>. QED BY <3>1, <5>4, TypeOKAndNext DEF OSM!BecomeLeader, LastTerm, TypeOK
                <4>2. \A t \in Server : \A i \in DOMAIN log[t] : log'[t][i] = log[t][i] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2, TypeOKAndNext DEF Ind, LogMatching, EqualUpTo, OSM!BecomeLeader, LastTerm, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF Ind, LogMatching, EqualUpTo, OSM!UpdateTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/26
\* finished: 8/26
\* about 45 min
LEMMA TermsOfEntriesGrowMonotonicallyAndNext ==
ASSUME Ind, Next
PROVE TermsOfEntriesGrowMonotonically'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF Ind, TermsOfEntriesGrowMonotonically, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, OSM!ClientRequest, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK s \in Server, t \in Server : OSM!GetEntries(s, t) BY <2>2
            <3>.  DEFINE sLastIdx == Len(log'[s])
            <3>2. SUFFICES ASSUME sLastIdx > 1
                  PROVE TermsOfEntriesGrowMonotonically'
                  BY <3>1 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
            <3>3. log'[s][sLastIdx] >= log'[s][sLastIdx-1]
                <4>1. log'[s][sLastIdx] = log'[t][sLastIdx] BY <1>ok, <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. log'[t][sLastIdx] = log[t][sLastIdx] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. log[t][sLastIdx] >= log[t][sLastIdx-1] BY <3>1, <3>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
                <4>4. log[t][sLastIdx-1] = log[s][sLastIdx-1] BY <1>ok, <3>1, <3>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>5. log'[s][sLastIdx-1] = log[s][sLastIdx-1] BY <3>1, <3>2 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>. QED BY <3>1, <3>2, <4>1, <4>2, <4>3, <4>4, <4>5 DEF OSM!GetEntries, OSM!Empty, TypeOK
            <3>. QED BY <3>1, <3>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!GetEntries, OSM!Empty, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!RollbackEntries, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!CommitEntry, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, TermsOfEntriesGrowMonotonically
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. CASE UNCHANGED log BY <3>2 DEF Ind, TermsOfEntriesGrowMonotonically
            <3>3. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                <4>.  DEFINE pLastIdx == Len(log'[p])
                <4>1. \A i \in DOMAIN log'[p] : log'[p][pLastIdx] >= log'[p][i]
                    <5>1. \A t \in Server : currentTerm[p] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind
                    <5>2. \A t \in Server : \A i \in DOMAIN log[t] : currentTerm[p] >= log[t][i]
                        BY <3>1, <5>1 DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
                    <5>3. LastTerm(log'[p]) > currentTerm[p] BY <1>ok, <3>1, <3>3, <5>2, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>4. \A i \in DOMAIN log[p] : log'[p][pLastIdx] > log[p][i] BY <1>ok, <3>1, <5>2, <5>3, TypeOKAndNext DEF LastTerm, TypeOK
                    <5>5. \A i \in DOMAIN log'[p] : i < pLastIdx => log'[p][i] = log[p][i] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                    <5>. QED BY <3>1, <5>4, <5>5 DEF OSM!BecomeLeader, TypeOK
                <4>2. \A t \in Server : t # p => log'[t] = log[t] BY <3>1, <3>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <3>3, <4>1, <4>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!BecomeLeader, OSM!Empty, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF Ind, TermsOfEntriesGrowMonotonically, OSM!UpdateTerms, TypeOK
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/26
\* finished: 8/27
LEMMA PrimaryHasEntriesItCreatedAndNext ==
ASSUME Ind, Next
PROVE PrimaryHasEntriesItCreated'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. CASE ~OSM!ClientRequest(s)
                <4>1. state[s] = Primary BY <2>1, <3>1, <3>2 DEF OSM!ClientRequest, TypeOK
                <4>2. CASE ~OSM!ClientRequest(t)
                    <5>1. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <1>ok, <2>1, <3>1, <3>2, <4>2 DEF OSM!ClientRequest, InLog, TypeOK
                    <5>2. k \in DOMAIN log[t] BY <1>ok, <2>1, <3>1, <3>2, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>. QED BY <3>1, <4>1, <5>1, <5>2 DEF Ind, PrimaryHasEntriesItCreated, InLog, TypeOK
                <4>3. CASE OSM!ClientRequest(t)
                    <5>1. CASE k = Len(log'[t])
                        <6>1. currentTerm[s] = currentTerm[t] BY <1>ok, <3>1, <3>2, <4>3, <5>1 DEF OSM!ClientRequest, TypeOK
                        <6>2. s # t BY <3>2, <4>3 DEF OSM!ClientRequest, TypeOK
                        <6>3. state[s] = Primary /\ state[t] = Primary BY <4>1, <4>3 DEF OSM!ClientRequest
                        <6>. QED BY <6>1, <6>2, <6>3 DEF Ind, OnePrimaryPerTerm
                    <5>2. CASE k < Len(log'[t])
                        <6>1. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                            BY <3>1, <3>2, <4>3, <5>2 DEF OSM!ClientRequest, InLog, TypeOK
                        <6>2. k \in DOMAIN log[t] BY <3>1, <4>3, <5>2 DEF OSM!ClientRequest, TypeOK
                        <6>. QED BY <3>1, <4>1, <6>1, <6>2 DEF Ind, PrimaryHasEntriesItCreated, TypeOK
                    <5>. QED BY <3>1, <5>1, <5>2 DEF OSM!ClientRequest, TypeOK
                <4>. QED BY <4>2, <4>3
            <3>3. CASE OSM!ClientRequest(s)
                <4>1. SUFFICES ASSUME s # t
                      PROVE FALSE BY <3>1, <3>3 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>2. k \in DOMAIN log[t] BY <3>1, <3>3, <4>1 DEF OSM!ClientRequest, TypeOK
                <4>3. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                    BY <3>1, <3>3, <4>1 DEF OSM!ClientRequest, InLog, TypeOK
                <4>. QED BY <3>1, <3>3, <4>1, <4>2, <4>3 DEF Ind, PrimaryHasEntriesItCreated, InLog, OSM!ClientRequest, TypeOK
            <3>. QED BY <3>2, <3>3
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. SUFFICES ASSUME s # t
                  PROVE FALSE BY <3>1 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>3. PICK u,v \in Server : OSM!GetEntries(u, v) BY <2>2
            <3>4. CASE t = u
                <4>1. CASE k = Len(log'[t])
                    <5>1. k \in DOMAIN log[v] BY <3>1, <3>3, <3>4 DEF OSM!GetEntries, TypeOK
                    <5>2. log[v][k] = currentTerm[s] /\ ~InLog(<<k,log[v][k]>>, s)
                        BY <3>1, <3>3, <3>4, <4>1 DEF OSM!GetEntries, OSM!Empty, InLog, TypeOK
                    <5>. QED BY <3>1, <3>2, <3>3, <5>1, <5>2 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>2. CASE k < Len(log'[t])
                    <5>1. k \in DOMAIN log[t] BY <3>1, <3>3, <4>2 DEF OSM!GetEntries, TypeOK
                    <5>2. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <3>1, <3>3, <3>4, <4>2 DEF OSM!GetEntries, OSM!Empty, InLog, TypeOK
                    <5>. QED BY <3>1, <3>2, <3>3, <5>1, <5>2 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>. QED BY <3>1, <3>3, <3>4, <4>1, <4>2 DEF OSM!GetEntries, TypeOK
            <3>5. CASE t # u BY <3>1, <3>2, <3>3, <3>5 DEF OSM!GetEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>. QED BY <3>4, <3>5
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>2. PICK u, v \in Server : OSM!RollbackEntries(u, v) BY <2>3
            <3>3. s # u BY <3>1, <3>2, PrimaryAndSecondaryAreDifferent DEF OSM!RollbackEntries, TypeOK
            <3>. QED BY <3>1, <3>2, <3>3 DEF OSM!RollbackEntries, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A s \in Server : \A i \in DOMAIN log[s] : \E t \in Server : configTerm[t] >= log[s][i] BY DEF Ind, LogEntryInTermImpliesConfigInTerm
            <3>3. \A s \in Server : \A i \in DOMAIN log[s] : currentTerm[p] >= log[s][i] BY <1>ok, <3>1, <3>2, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
            <3>4. SUFFICES ASSUME NEW s \in Server, state'[s] = Primary,
                                  NEW t \in Server,
                                  NEW k \in DOMAIN log'[t], log'[t][k] = currentTerm'[s], ~InLog(<<k,log[t][k]>>, s)'
                  PROVE FALSE BY DEF PrimaryHasEntriesItCreated
            <3>5. SUFFICES ASSUME s # t
                  PROVE FALSE BY <3>1, <3>4 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>6. CASE t # p BY <3>1, <3>3, <3>4, <3>6 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
            <3>7. CASE t = p
                <4>q. PICK Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <3>1
                <4>1. s \notin Q BY <3>1, <3>4, <3>5, <3>7, <4>q, PrimaryAndSecondaryAreDifferent DEF OSM!BecomeLeader, TypeOK
                <4>2. CASE k = Len(log'[p]) /\ log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    <5>1. currentTerm'[s] = currentTerm[p] + 1 BY <1>ok, <3>1, <3>4, <3>7, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>2. currentTerm[s] =  currentTerm[p] + 1 BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <5>1 DEF OSM!BecomeLeader, TypeOK
                    <5>3. state[s] = Primary BY <1>ok, <3>1, <3>4, <3>5, <3>7 DEF OSM!BecomeLeader, TypeOK
                    <5>4. configTerm[s] = currentTerm[p] + 1 BY <5>2, <5>3 DEF Ind, PrimaryConfigTermEqualToCurrentTerm
                    <5>. QED BY <1>ok, <3>1, <5>4, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
                <4>3. CASE k < Len(log'[t]) \/ UNCHANGED log
                    <5>1. currentTerm[s] = currentTerm'[s] BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <4>3 DEF OSM!BecomeLeader, TypeOK
                    <5>2. k \in DOMAIN log[t] BY <3>1, <3>4, <3>7, <4>3 DEF OSM!BecomeLeader, TypeOK
                    <5>3. log[t][k] = log'[t][k]
                        <6>1. CASE UNCHANGED log BY <6>1, <3>1, <3>4, <3>5, <3>7, <4>3 DEF OSM!BecomeLeader, TypeOK
                        <6>2. CASE k < Len(log'[t]) /\ log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                            BY <3>1, <3>4, <3>5, <3>7, <4>3, <6>2 DEF OSM!BecomeLeader, TypeOK
                        <6>. QED BY <3>1, <3>7, <4>3, <6>1, <6>2 DEF OSM!BecomeLeader, TypeOK
                    <5>4. log[t][k] = currentTerm[s] /\ ~InLog(<<k,log[t][k]>>, s)
                        BY <3>1, <3>4, <3>5, <3>7, <4>q, <4>1, <4>3, <5>3 DEF OSM!BecomeLeader, InLog, TypeOK
                    <5>. QED BY <3>1, <3>4, <5>2, <5>4 DEF OSM!BecomeLeader, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>. QED BY <3>1, <3>4, <3>7, <4>2, <4>3 DEF OSM!BecomeLeader, TypeOK
            <3>. QED BY <3>6, <3>7
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* finished: 8/27
\* approx 20 min
LEMMA CurrentTermAtLeastAsLargeAsLogTermsForPrimaryAndNext ==
ASSUME Ind, Next
PROVE CurrentTermAtLeastAsLargeAsLogTermsForPrimary'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!GetEntries, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3, PrimaryAndSecondaryAreDifferent DEF OSM!RollbackEntries, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF osmVars, CSM!Reconfig, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF osmVars, CSM!SendConfig, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            \* the result is obvious for any server not becoming the new leader
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A i \in DOMAIN log[p] : currentTerm[p] >= log[p][i]
                BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
            <3>3. \A i \in DOMAIN log'[p] : currentTerm'[p] >= log'[p][i]
                <4>1. CASE UNCHANGED log BY <1>ok, <3>1, <3>2, <4>1 DEF OSM!BecomeLeader, TypeOK
                <4>2. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    <5>1. \A i \in DOMAIN log'[p] : i = Len(log'[p]) => log'[p][i] = currentTerm'[p] BY <1>ok, <3>1, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>2. \A i \in DOMAIN log'[p] : i < Len(log'[p]) => log'[p][i] = log[p][i] BY <3>1, <4>2 DEF OSM!BecomeLeader, TypeOK
                    <5>3. \A i \in DOMAIN log'[p] : i < Len(log'[p]) => log'[p][i] <= currentTerm'[p] BY <1>ok, <3>1, <3>2, <5>2 DEF OSM!BecomeLeader, TypeOK
                    <5>. QED BY <1>ok, <3>1, <3>2, <5>1, <5>3 DEF OSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2 DEF OSM!BecomeLeader, TypeOK
            <3>. QED BY <3>1, <3>3, PrimaryAndSecondaryAreDifferent DEF Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, OSM!BecomeLeader, TypeOK
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2, PrimaryAndSecondaryAreDifferent DEF OSM!UpdateTerms, OSM!UpdateTermsExpr, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* finished: 8/27
\* approx 3 hours
LEMMA LogEntryInTermImpliesConfigInTermAndNext ==
ASSUME Ind, Next
PROVE LogEntryInTermImpliesConfigInTerm'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. PICK s \in Server : OSM!ClientRequest(s) BY <2>1
            <3>2. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => configTerm'[s] = log'[s][i]
                BY <1>1, <3>1 DEF csmVars, OSM!ClientRequest, TypeOK, Ind, PrimaryConfigTermEqualToCurrentTerm
            <3>3. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => configTerm[s] >= log[s][i]
                BY <3>1 DEF OSM!ClientRequest, TypeOK, Ind, CurrentTermAtLeastAsLargeAsLogTermsForPrimary, PrimaryConfigTermEqualToCurrentTerm
            <3>4. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => configTerm'[s] >= log'[s][i]
                BY <1>1, <3>1, <3>3 DEF csmVars, OSM!ClientRequest, TypeOK
            <3>. QED BY <1>1, <3>1, <3>2, <3>4 DEF csmVars, OSM!ClientRequest, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK s,t \in Server : OSM!GetEntries(s, t) BY <2>2
            <3>2. \A i \in DOMAIN log'[s] : i <= Len(log'[s]) => \E u \in Server : configTerm'[u] >= log'[s][i]
                <4>1. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => \E u \in Server : configTerm[u] >= log[s][i]
                    <5>1. \A i \in DOMAIN log'[s] : i < Len(log'[s]) => s \in Server /\ i \in DOMAIN log[s]
                        BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                    <5>. QED BY <3>1, <5>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                <4>2. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => log[t][i] = log'[s][i] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. \A i \in DOMAIN log'[s] : i = Len(log'[s]) => \E u \in Server : configTerm[u] >= log'[s][i]
                    BY <3>1, <4>2 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
                <4>. QED BY <1>1, <3>1, <4>1, <4>3, TypeOKAndNext DEF csmVars, OSM!GetEntries, OSM!Empty, TypeOK
            <3>3. \A u \in Server : u # s => \A i \in DOMAIN log'[u] : \E v \in Server : configTerm'[v] >= log'[u][i]
                BY <1>1, <3>1 DEF csmVars, OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
            <3>. QED BY <3>2, <3>3 DEF LogEntryInTermImpliesConfigInTerm
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <1>1, <2>3 DEF csmVars, OSM!RollbackEntries, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <1>1, <2>4 DEF csmVars, OSM!CommitEntry, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1, ConfigsIncreaseMonotonically DEF osmVars, CSM!Reconfig, TypeOK,
                Ind, LogEntryInTermImpliesConfigInTerm, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2, ConfigsIncreaseMonotonically DEF osmVars, CSM!SendConfig, TypeOK,
                Ind, LogEntryInTermImpliesConfigInTerm, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            <3>1. PICK p \in Server : \E Q \in Quorums(config[p]) : OSM!BecomeLeader(p, Q) /\ CSM!BecomeLeader(p, Q) BY <2>1
            <3>2. \A s \in Server : \A i \in DOMAIN log[s] : currentTerm[p] >= log[s][i]
                BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF Ind, LogEntryInTermImpliesConfigInTerm, TypeOK
            <3>3. \A s \in Server : s # p => \A i \in DOMAIN log'[s] : currentTerm'[p] >= log'[s][i]
                BY <1>ok, <3>1, <3>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>4. \A i \in DOMAIN log'[p] : currentTerm'[p] >= log'[p][i]
                <4>1. CASE UNCHANGED log
                    <5>1. currentTerm'[p] >= currentTerm[p]
                        BY <1>ok, <3>1, ConfigsIncreaseMonotonically DEF OSM!BecomeLeader, CSM!BecomeLeader, CSM!NewerOrEqualConfig, CSM!NewerConfig, CV, TypeOK
                    <5>. QED BY <1>ok, <3>1, <3>2, <4>1, <5>1 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
                <4>2. CASE log' = [log EXCEPT ![p] = Append(log[p], currentTerm[p]+1)]
                    BY <1>ok, <3>1, <3>2, <4>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
                <4>. QED BY <3>1, <4>1, <4>2 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK
            <3>. QED BY <1>ok, <3>1, <3>3, <3>4 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK, LogEntryInTermImpliesConfigInTerm
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, CSM!UpdateTerms, TypeOK, Ind, LogEntryInTermImpliesConfigInTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

\* began: 8/27
\* finished: 8/29
\* UniformLogEntriesInTerm notes:
\* DEF boundary == an index i in a server s' log where log[s][i] # log[s][i-1]
\* DEF local boundary == a boundary for a single server
\* DEF global boundary == a boundary for all servers
\* UniformLogEntriesInTerm in a nutshell:
\*   for all local log term boundaries, the boundary is in fact global
\* 
LEMMA UniformLogEntriesInTermAndNext ==
ASSUME Ind, Next
PROVE UniformLogEntriesInTerm'
PROOF
    <1>ok. TypeOK BY DEF Ind
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            <3>1. PICK p \in Server : OSM!ClientRequest(p) BY <2>1
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            \* this is unneeded, but it helps me to clearly see the proof goal
            \* after DeMorgan'ing the 2nd part of the 'implies' we see the local (s) to global (\A t) boundary stipulation
            <3>f. SUFFICES ASSUME TRUE
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            <3>6. CASE s = p
                <4>1. CASE i = Len(log'[p])
                    <5>1. SUFFICES ASSUME (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])',
                                          NEW k \in DOMAIN log'[t], log'[t][k] = log'[s][i], k < i
                          PROVE FALSE OBVIOUS
                    <5>2. k \in DOMAIN log[t] BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, TypeOK
                    <5>3. log[t][k] = currentTerm[p] BY <1>ok, <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, TypeOK
                    <5>4. ~InLog(<<k, log[t][k]>>, p) BY <3>1, <3>6, <4>1, <5>1 DEF OSM!ClientRequest, InLog, TypeOK
                    <5>. QED BY <3>1, <3>4, <5>2, <5>3, <5>4 DEF Ind, PrimaryHasEntriesItCreated, OSM!ClientRequest, InLog, TypeOK
                <4>2. CASE i < Len(log'[p])
                    <5>1. i \in DOMAIN log[p] BY <3>1, <3>5, <3>6, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>2. log[p][i] = log'[p][i] BY <3>1, <3>5, <3>6, <4>2 DEF OSM!ClientRequest, TypeOK
                    <5>3. (\A j \in DOMAIN log[p] : (j < i) => log[p][j] # log[p][i]) => (~\E k \in DOMAIN log[t] : log[t][k] = log[p][i] /\ k < i)
                        BY <3>1, <3>5, <3>6, <4>2, <5>1, <5>2 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
                    <5>i. (DOMAIN log'[p] \cap DOMAIN log[p]) = DOMAIN log[p] BY <3>1 DEF OSM!ClientRequest, TypeOK
                    <5>4. \A j \in DOMAIN log'[p] : (j < i) => j \in DOMAIN log[p] BY <3>1, <3>6, <4>2, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>5. \A j \in DOMAIN log[p] : (j < i) => log[p][j] = log'[p][j] BY <3>1, <3>6, <4>2, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>6. (\A j \in DOMAIN log[p] : (j < i) => log[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>1, <5>3 DEF OSM!ClientRequest, TypeOK
                    <5>7. (\A j \in DOMAIN log[p] : (j < i) => log'[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>4, <5>5, <5>6 DEF OSM!ClientRequest, TypeOK
                    <5>8. (\A j \in DOMAIN log'[p] : (j < i) => log'[p][j] # log'[p][i]) => (~\E k \in DOMAIN log'[t] : log'[t][k] = log'[p][i] /\ k < i)
                        BY <3>1, <5>7, <5>i DEF OSM!ClientRequest, TypeOK
                    <5>. QED BY <3>1, <3>5, <3>6, <4>2, <5>8 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
                <4>. QED BY <3>1, <3>5, <3>6, <4>1, <4>2 DEF OSM!ClientRequest, TypeOK
            <3>7. CASE t = p
                <4>1. SUFFICES ASSUME t # s
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>2. log'[s] = log[s] BY <3>1, <3>7, <4>1 DEF OSM!ClientRequest, TypeOK
                <4>3. \A j \in DOMAIN log'[t] : (j < Len(log'[t])) => log[t][j] = log'[t][j] BY <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>4. log'[t][Len(log'[t])] = currentTerm[t] BY <1>ok, <3>1, <3>7 DEF OSM!ClientRequest, TypeOK
                <4>5. \A u \in Server : ~\E k \in DOMAIN log[u] : log[u][k] = currentTerm[t] /\ ~InLog(<<k,log[u][k]>>, t)
                    BY <3>1, <3>7, <4>4 DEF OSM!ClientRequest, TypeOK, Ind, PrimaryHasEntriesItCreated, InLog
                <4>6. SUFFICES ASSUME (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])'
                      PROVE (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])' OBVIOUS
                \* splitting into cases helps tlaps
                <4>7. CASE i = Len(log'[s])
                    BY <3>1, <3>7, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm, InLog
                <4>8. CASE i < Len(log'[s])
                    BY <3>1, <3>7, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>8 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm, InLog
                <4>. QED BY <3>1, <3>5, <3>7, <4>7, <4>8 DEF OSM!ClientRequest, TypeOK
            <3>8. CASE s # p /\ t # p BY <3>1, <3>8 DEF OSM!ClientRequest, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            <3>1. PICK u, v \in Server : OSM!GetEntries(u, v) BY <2>2
            <3>.  DEFINE uLastIdx == Len(log'[u])
            <3>m. log'[u] = SubSeq(log[v], 1, uLastIdx) BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogMatching, EqualUpTo
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            <3>f. SUFFICES ASSUME TRUE
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            <3>6. CASE s = u
                <4>1. SUFFICES ASSUME s # t
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. \A j \in DOMAIN log[v] : (j < i) => (j \in DOMAIN log'[s] /\ log[s][j] = log'[s][j])
                    BY <3>1, <3>m, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. (\A j \in DOMAIN log'[s] : (j < i) => log'[s][j] # log'[s][i]) => (\A j \in DOMAIN log[v] : (j < i) => log[v][j] # log[v][i])
                    <5>1. \A j \in DOMAIN log[v] : (j < i) => (j \in DOMAIN log'[s]) BY <4>2
                    <5>2. \A j \in DOMAIN log'[s] : (j \in DOMAIN log[v] /\ log[v][j] = log'[s][j]) BY <3>1, <3>m, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>. QED BY <5>1, <5>2
                <4>4. (\A j \in DOMAIN log[v] : (j < i) => log[v][j] # log[v][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i])
                    <5>1. i \in DOMAIN log[v] BY <3>1, <3>5, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>. QED BY <3>6, <4>2, <5>1 DEF Ind, UniformLogEntriesInTerm
                <4>5. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                    <5>1. SUFFICES ASSUME \A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[v][i]
                          PROVE (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])' OBVIOUS
                    <5>2. log'[t] = log[t] BY <3>1, <3>6, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>3. log'[v] = log[v] BY <3>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                    <5>4. log'[v][i] = log'[s][i] BY <3>1, <3>6 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, LogMatching, EqualUpTo
                    <5>. QED BY <5>1, <5>2, <5>3, <5>4 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>. QED BY <4>3, <4>4, <4>5 DEF TypeOK
            <3>7. CASE t = u
                <4>1. SUFFICES ASSUME s # t
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>7 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>2. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>3. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1 DEF Ind, UniformLogEntriesInTerm, OSM!GetEntries, OSM!Empty, TypeOK
                <4>4. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log'[t][j] # log'[s][i])
                    BY <3>1, <3>5, <3>7, <4>1, <4>3 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>.  DEFINE tLastIdx == Len(log'[t])
                <4>5. log'[t][tLastIdx] = log[v][tLastIdx]
                    BY <1>ok, <3>1, <3>5, <3>7, <4>1, <4>3 DEF OSM!GetEntries, OSM!Empty, TypeOK
                <4>6. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (tLastIdx < i => log[v][tLastIdx] # log[s][i])
                    BY <3>1, <3>5, <3>7, <4>1, Z3 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
                <4>. QED BY <3>1, <3>5, <3>7, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF OSM!GetEntries, OSM!Empty, TypeOK
            <3>8. CASE s # u /\ t # u BY <3>1, <3>8 DEF OSM!GetEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            <3>1. PICK u, v \in Server : OSM!RollbackEntries(u, v) BY <2>3
            <3>2. SUFFICES ASSUME TRUE
                  PROVE (\A s,t \in Server : \A i \in DOMAIN log[s] :
                            (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) =>
                                (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i))'
                  BY DEF UniformLogEntriesInTerm
            <3>3. TAKE s \in Server
            <3>4. TAKE t \in Server
            <3>5. TAKE i \in DOMAIN log'[s]
            <3>f. SUFFICES ASSUME TRUE
                  PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                  OBVIOUS
            <3>6. CASE s = u
                <4>a. SUFFICES ASSUME t # s
                      PROVE (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                      BY <3>1, <3>5, <3>6, Z3 DEF OSM!RollbackEntries, TypeOK
                <4>1. \A j \in DOMAIN log'[s] : j \in DOMAIN log[s] /\ log'[s][j] = log[s][j]
                    BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK
                <4>2. \A j \in DOMAIN log[s] : (j < i) => (j \in DOMAIN log'[s] /\ log'[s][j] = log[s][j])
                    BY <3>1, <3>5, <3>6 DEF OSM!RollbackEntries, TypeOK
                <4>3. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])' => (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])
                    BY <3>5, <4>1, <4>2
                <4>4. (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])
                    <5>1. i \in DOMAIN log[s] BY <3>1, <3>5 DEF OSM!RollbackEntries, TypeOK
                    <5>. QED BY <3>6, <5>1 DEF Ind, UniformLogEntriesInTerm
                <4>5. (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]) => (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])'
                    BY <3>1, <3>5, <3>6, <4>a DEF OSM!RollbackEntries, TypeOK
                <4>. QED BY <4>1, <4>2, <4>3, <4>4, <4>5
            <3>7. CASE t = u
                <4>1. SUFFICES ASSUME (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i])'
                      PROVE (\A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i])' OBVIOUS
                <4>2. \A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i] BY <3>1, <3>7, <4>1 DEF Ind, OSM!RollbackEntries, OSM!Empty, TypeOK
                <4>3. \A j \in DOMAIN log[t] : (j < i) => log[t][j] # log[s][i]
                    BY <3>1, <3>7, <4>2 DEF Ind, UniformLogEntriesInTerm, OSM!RollbackEntries, OSM!Empty
                <4>. QED BY <3>1, <3>7, <4>3 DEF OSM!RollbackEntries, OSM!Empty, TypeOK
            <3>8. CASE s # u /\ t # u BY <3>1, <3>8 DEF OSM!RollbackEntries, OSM!Empty, TypeOK, Ind, UniformLogEntriesInTerm
            <3>. QED BY <3>6, <3>7, <3>8
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, TypeOK, Ind, UniformLogEntriesInTerm
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        BY <1>2 DEF osmVars, Ind, UniformLogEntriesInTerm
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            BY <2>1 DEF OSM!BecomeLeader, CSM!BecomeLeader, TypeOK, Ind, UniformLogEntriesInTerm
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, TypeOK, Ind, UniformLogEntriesInTerm
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

=============================================================================
