----------------------------- MODULE Axioms -----------------------------

EXTENDS MongoRaftReconfig

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}
\*AXIOM ServersAreEqual == Server = CSM!currentTerm

LEMMA ConfigsAreFinite ==
ASSUME TRUE
PROVE \A s \in Server : IsFiniteSet(config[s])

=============================================================================
