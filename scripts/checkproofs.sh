#!/bin/sh

#
# Check all TLAPS proofs for establishing safety of MongoRaftReconfig.
#

tlapm -v --cleanfp --timing -I ../ AuxLemmas.tla
tlapm -v --cleanfp --timing -I ../ BasicQuorumsLib.tla
tlapm -v --cleanfp --timing -I ../ ElectionSafetyLemmas.tla
tlapm -v --cleanfp --timing -I ../ IndProof.tla
tlapm -v --cleanfp --timing -I ../ LeaderCompletenessLemmas.tla
tlapm -v --cleanfp --timing -I ../ LeaderCompletenessLemmasCtd.tla
tlapm -v --cleanfp --timing -I ../ Lib.tla
tlapm -v --cleanfp --timing -I ../ LogPropertiesLemmas.tla
tlapm -v --cleanfp --timing -I ../ MRRTheorems.tla
