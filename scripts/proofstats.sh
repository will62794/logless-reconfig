#!/bin/sh
#
# Count lines of code in TLAPS proofs, excluding comments.
#

function prooflines {
    cat AuxLemmas.tla \
        Axioms.tla \
        BasicQuorumsLib.tla \
        ElectionSafetyLemmas.tla \
        LeaderCompletenessLemmas.tla \
        LeaderCompletenessLib.tla \
        Lib.tla \
        LogLemmas.tla \
        MongoRaftReconfigIndInv.tla \
        MongoRaftReconfigProofs.tla \
        StateMachineSafetyLemmas.tla 
}

cd proofs
echo "Count lines of non-comment code in TLAPS proofs:"
prooflines | grep -v "\*" | wc -l

echo "Count LEMMA statements in TLAPS proofs:"
prooflines | grep "LEMMA" | wc -l

echo "Count THEOREM statements in TLAPS proofs:"
prooflines | grep "THEOREM" | wc -l
    