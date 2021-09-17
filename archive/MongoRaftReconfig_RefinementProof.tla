----------------------------- MODULE MongoRaftReconfig_RefinementProof -----------------------------

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, TLAPS, MongoRaftReconfig

\*
\* Refinement proof of MongoRaftReconfig => MongoLoglessDynamicRaft.
\*
\* This proof is sufficient to establish that any properties of MongoLoglessDynamicRaft 
\* hold when operating as a subprotocol of MongoRaftReconfig.
\*

\* Create an instance of MongoLoglessDynamicRaft that uses a subset of the 
\* variables of MongoRaftReconfig.
IMLDR == INSTANCE MongoLoglessDynamicRaft WITH 
            currentTerm <- currentTerm,
            state <- state,
            configVersion <- configVersion,
            configTerm <- configTerm,
            config <- config


\* Prove that any step of MongoRaftReconfig is a valid step of MongoLoglessDynamicRaft. 
THEOREM MRRNextRefinesMLDRNext == [Next]_vars => [IMLDR!Next]_IMLDR!vars
    <1>a. SUFFICES ASSUME [Next]_vars PROVE [IMLDR!Next]_IMLDR!vars
            OBVIOUS
    <1>b. [IMLDR!Next]_IMLDR!vars
        <2>   USE DEF IMLDR!Next, IMLDR!vars
        <2>1. CASE (OSMNext /\ UNCHANGED csmVars)
            <3>1. CASE \E s \in Server : OSM!ClientRequest(s) /\ UNCHANGED csmVars 
                BY <3>1 DEF OSM!ClientRequest, csmVars
            <3>2. CASE \E s, t \in Server : OSM!GetEntries(s, t) /\ UNCHANGED csmVars
                BY <3>2 DEF OSM!GetEntries, csmVars
            <3>3. CASE \E s, t \in Server : OSM!RollbackEntries(s, t) /\ UNCHANGED csmVars
                BY <3>3 DEF OSM!RollbackEntries, csmVars
            <3>4. CASE \E s \in Server :  \E Q \in OSM!QuorumsAt(s) : OSM!CommitEntry(s, Q) /\ UNCHANGED csmVars
                BY <3>4 DEF OSM!CommitEntry, csmVars
            <3>5. QED BY <2>1,<3>1,<3>2,<3>3,<3>4 DEF OSMNext
        <2>2. CASE CSMNext /\ UNCHANGED osmVars
            <3>1. CASE \E s \in Server, newConfig \in SUBSET Server : 
                    OplogCommitment(s) /\ CSM!Reconfig(s, newConfig) /\ UNCHANGED osmVars
                    BY <3>1 
                    DEF CSM!Reconfig, IMLDR!Reconfig, CSM!ConfigQuorumCheck, CSM!TermQuorumCheck, CSM!QuorumsOverlap,
                        IMLDR!ConfigQuorumCheck, IMLDR!TermQuorumCheck, IMLDR!QuorumsOverlap, CSM!Quorums, IMLDR!Quorums, 
                        Quorums, IMLDR!QuorumsAt, CSM!QuorumsAt, IsCommitted, osmVars, CSM!Cardinality, IMLDR!Cardinality
            <3>2. CASE \E s,t \in Server : CSM!SendConfig(s, t) /\ UNCHANGED osmVars
                    BY <3>2 DEF CSM!SendConfig, IMLDR!SendConfig, IMLDR!IsNewerConfig, CSM!IsNewerConfig                    
            <3>3. QED BY <2>2,<3>2,<3>1 DEF CSMNext, osmVars
        <2>3. CASE JointNext 
            <3>1. CASE \E i \in Server : \E Q \in Quorums(config[i]) : 
                            /\ OSM!BecomeLeader(i, Q)
                            /\ CSM!BecomeLeader(i, Q)
                    BY <3>1 
                    DEF CSM!BecomeLeader, IMLDR!BecomeLeader, CSM!CanVoteForConfig,
                        OSM!CanVoteForOplog, IMLDR!CanVoteForConfig,IMLDR!IsNewerOrEqualConfig,
                        CSM!IsNewerOrEqualConfig, IMLDR!IsNewerConfig, CSM!IsNewerConfig, OSM!LastTerm, Quorums, IMLDR!Quorums, 
                        IMLDR!Cardinality, Cardinality
            <3>2. CASE \E s,t \in Server : OSM!UpdateTerms(s,t) /\ CSM!UpdateTerms(s,t)
                BY <3>2 DEF OSM!UpdateTerms, CSM!UpdateTerms,
                            IMLDR!UpdateTerms,
                            IMLDR!UpdateTermsExpr,
                            OSM!UpdateTermsExpr, CSM!UpdateTermsExpr     
            <3>3. QED BY <2>3, <3>1, <3>2 DEF JointNext 
        <2>4. CASE UNCHANGED vars BY <2>4 DEF vars, IMLDR!vars
        <2>5. QED BY <1>a,<2>1, <2>2,<2>3,<2>4 DEF Next
    <1>c. QED BY <1>b, <1>a


\* MongoRaftReconfig => MongoLoglessDynamicRaft
THEOREM MRRRefinesMLDR == Spec => IMLDR!Spec
    <1>1. Init => IMLDR!Init 
        BY DEF Init, OSM!Init, CSM!Init, IMLDR!Init
    <1>2. [Next]_vars => [IMLDR!Next]_IMLDR!vars BY MRRNextRefinesMLDRNext
    <1>3. QED BY <1>1, <1>2, PTL DEF Spec, IMLDR!Spec


\* Note: See https://github.com/tlaplus/Examples/blob/9d7de44a8a37e415c8ba6e24d167632d53c24176/specifications/Paxos/Voting.tla#L179-L198
\* for one example of a refinement proof in TLAPS.

=============================================================================
