#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

tlapm --stretch 2 -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ IndProof.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LeaderCompletenessLib.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ Lib.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ LogPropertiesLemmas.tla
tlapm --stretch 2 -v --cleanfp --timing -I ../ MRRTheorems.tla
