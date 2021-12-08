----------------------------- MODULE Assumptions -----------------------------
EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv

\*
\* Some very basic assumptions/lemmas that are necessary for reasoning about the protocol.
\*

ASSUME PrimaryAndSecondaryAreDifferent == Primary # Secondary
ASSUME ServerIsFinite == IsFiniteSet(Server)
ASSUME ServerIsNonempty == Server # {}

LEMMA QuorumsIdentical ==
ASSUME TypeOK
PROVE
    \A s \in Server : 
        /\ Quorums(config[s]) = CSM!Quorums(config[s])
        /\ Quorums(config[s]) = OSM!Quorums(config[s])
    BY ServerIsFinite DEF TypeOK,Quorums,CSM!Quorums,OSM!Quorums,Cardinality,CSM!Cardinality,OSM!Cardinality
   
LEMMA QuorumsOverlapIdentical ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> CSM!QuorumsOverlap(conf1,conf2)
    BY ServerIsFinite DEF TypeOK, Quorums, 
        OSM!QuorumsOverlap,CSM!QuorumsOverlap,QuorumsOverlap,OSM!Quorums,
        CSM!Quorums,Cardinality,CSM!Cardinality,OSM!Cardinality

=============================================================================
