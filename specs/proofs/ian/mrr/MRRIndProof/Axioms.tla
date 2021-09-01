----------------------------- MODULE Axioms -----------------------------

EXTENDS MongoRaftReconfig

AXIOM PrimaryAndSecondaryAreDifferent == Primary # Secondary
AXIOM ServerIsFinite == IsFiniteSet(Server)
AXIOM ServerIsNonempty == Server # {}

=============================================================================
