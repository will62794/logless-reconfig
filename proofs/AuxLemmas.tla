----------------------------- MODULE AuxLemmas -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv, Assumptions, TypeOK, Lib

\* began: 9/14
\* finished: 9/14
\* approx 2 min
LEMMA ConfigsNonemptyAndNext ==
ASSUME Ind, Next
PROVE ConfigsNonempty'
PROOF
    <1>1. CASE OSMNext /\ UNCHANGED csmVars
        <2>1. CASE \E s \in Server : OSM!ClientRequest(s)
            BY <2>1 DEF OSM!ClientRequest, Ind, ConfigsNonempty, TypeOK
        <2>2. CASE \E s, t \in Server : OSM!GetEntries(s, t)
            BY <2>2 DEF OSM!GetEntries, Ind, ConfigsNonempty, TypeOK
        <2>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t)
            BY <2>3 DEF OSM!RollbackEntries, Ind, ConfigsNonempty, TypeOK
        <2>4. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!CommitEntry(s, Q)
            BY <2>4 DEF OSM!CommitEntry, Ind, ConfigsNonempty, TypeOK
        <2>. QED BY <1>1, <2>1, <2>2, <2>3, <2>4 DEF OSMNext
    <1>2. CASE CSMNext /\ UNCHANGED osmVars
        <2>1. CASE \E s \in Server, newConfig \in SUBSET Server : OplogCommitment(s) /\ CSM!Reconfig(s, newConfig)
            BY <1>2, <2>1 DEF OplogCommitment, CSM!Reconfig, Ind, ConfigsNonempty
        <2>2. CASE \E s,t \in Server : CSM!SendConfig(s, t)
            BY <1>2, <2>2 DEF CSM!SendConfig, Ind, ConfigsNonempty
        <2>. QED BY <1>2, <2>1, <2>2 DEF CSMNext
    <1>3. CASE JointNext
        <2>1. CASE \E s \in Server : \E Q \in Quorums(config[s]) : OSM!BecomeLeader(s, Q) /\ CSM!BecomeLeader(s, Q)
            BY <2>1 DEF OSM!BecomeLeader, Ind, ConfigsNonempty
        <2>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
            BY <2>2 DEF OSM!UpdateTerms, Ind, ConfigsNonempty
        <2>. QED BY <1>3, <2>1, <2>2 DEF JointNext
    <1>. QED BY <1>1, <1>2, <1>3 DEF Next

=============================================================================
