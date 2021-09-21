#!/bin/sh
#
# Count lines of code in TLAPS proofs, excluding comments.
#

function prooflines {
    cat proofs/AuxLemmas.tla \
        proofs/Axioms.tla \
        proofs/BasicQuorumsLib.tla \
        proofs/ElectionSafetyLemmas.tla \
        proofs/LeaderCompletenessLemmas.tla \
        proofs/LeaderCompletenessLib.tla \
        proofs/Lib.tla \
        proofs/LogLemmas.tla \
        proofs/MongoRaftReconfigIndInv.tla \
        proofs/MongoRaftReconfigProofs.tla \
        proofs/StateMachineSafetyLemmas.tla \
        MongoRaftReconfig.tla \
        MongoLoglessDynamicRaft.tla \
        MongoStaticRaft.tla
}

# cd proofs
echo "Count lines of non-comment code in TLAPS proofs:"
prooflines | grep -v "\*" | wc -l

echo "Count lines of non-comment code for inductive invariant:"
cat proofs/MongoRaftReconfigIndInv.tla | grep -v "\*" | wc -l

echo "Count lines of non-comment code for protocol spec:"
cat MongoRaftReconfig.tla MongoLoglessDynamicRaft.tla MongoStaticRaft.tla | grep -v "\*" | wc -l

echo "Count LEMMA statements in TLAPS proofs:"
prooflines | grep "LEMMA" | wc -l

echo "Count THEOREM statements in TLAPS proofs:"
prooflines | grep "THEOREM" | wc -l
    