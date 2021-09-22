----------------------------- MODULE Axioms -----------------------------

EXTENDS MongoRaftReconfig, MongoRaftReconfigIndInv

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}

LEMMA ConfigsAreFinite ==
ASSUME TRUE
PROVE \A s \in Server : IsFiniteSet(config[s])

LEMMA QuorumsIdentical ==
ASSUME TypeOK
PROVE \A s \in Server :
            /\ Quorums(config[s]) = CSM!Quorums(config[s])
            /\ Quorums(config[s]) = OSM!Quorums(config[s])
        
LEMMA QuorumsOverlapIdentical ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> CSM!QuorumsOverlap(conf1,conf2)

=============================================================================
